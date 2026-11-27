//! Walking a compilation and laying out the assembly it becomes.
//!
//! The order of the work is forced by the format. A `MethodDef` row stores the
//! address of its body, so the bodies have to exist before the rows; a body
//! refers to methods by token, so the tokens have to exist before the bodies.
//! The way out is to predict: rows are handed out in a fixed order, so a
//! token can be computed from a position before anything is written. The
//! planning pass does that, the generation pass emits IL against the predicted
//! tokens, and the writing pass adds the rows in exactly the predicted order.

use std::collections::HashMap;

use rustlyn_semantics::{
    Binder, BoundAttribute, BoundBody, BoundExpression, BoundExpressionKind, BoundStatement,
    Compilation, ConstantValue, LocalId, Modifiers, RefKind, SpecialConstant, SpecialType,
    SymbolId, SymbolKind, Type, TypeKind,
};

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use crate::codegen::BodyEmitter;
use crate::il::{Instruction, InstructionStream, Token, method_body};
use crate::metadata::{
    Metadata, field_attributes, method_attributes, method_impl, param_attributes, table,
    type_attributes,
};
use crate::pe::{PeLayout, il_rva, runtime_config};
use crate::references::References;
use crate::resources::Resource;
use crate::signature::{
    ElementType, SigType, field_signature, generic_method_signature, local_signature,
    method_signature, method_spec_signature, property_signature, type_def_or_ref, vararg_signature,
};

/// Why an assembly could not be produced.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EmitError {
    pub message: String,
}

impl EmitError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl std::fmt::Display for EmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for EmitError {}

/// How much of a compilation this backend can turn into IL.
///
/// `emit` stops at the first thing it cannot do, because an assembly with a
/// hole in it is not an assembly. Planning a road to compiling something the
/// size of Roslyn needs the other answer: how many bodies come out, and what
/// the rest are waiting on. A ranked list of reasons is worth more than a
/// list of features sorted by guesswork — the same argument the binder sweep
/// makes, for the half of the compiler the binder sweep says nothing about.
#[derive(Clone, Debug, Default)]
pub struct Coverage {
    /// One entry per body the backend was asked for.
    pub bodies: Vec<CoverageEntry>,
}

/// One method body, and whether it came out.
#[derive(Clone, Debug)]
pub struct CoverageEntry {
    /// The file the body was written in, where it was written in one: a
    /// synthesized member belongs to whichever file its type does, and a type
    /// the plan refused has no one body to point at.
    pub tree: Option<usize>,
    pub method: String,
    /// Why it did not come out, or `None` where it did.
    pub failure: Option<String>,
}

impl Coverage {
    /// How many bodies came out.
    #[must_use]
    pub fn emitted(&self) -> usize {
        self.bodies
            .iter()
            .filter(|entry| entry.failure.is_none())
            .count()
    }
}

/// A finished assembly and the file the host needs beside it.
#[derive(Clone, Debug)]
pub struct Emitted {
    pub assembly: Vec<u8>,
    pub runtime_config: String,
}

/// What a method in the plan is.
#[derive(Clone, Debug)]
pub(crate) enum MethodSource {
    /// A method, constructor or local body declared in the source.
    Declared(SymbolId),
    /// The parameterless constructor a class gets when it declares none.
    DefaultConstructor,
    /// The class constructor that runs the static field initializers.
    StaticConstructor,
    /// `get_X` for a property: either its body, or a read of its backing
    /// field when the property is automatic.
    PropertyGetter { property: SymbolId, backing: bool },
    /// `set_X` for an automatic property.
    PropertySetter { property: SymbolId },
    /// A private method that implements an interface member by calling the
    /// public one that answers it implicitly, where the two signatures differ
    /// only in what the runtime alone cares about: an `in` parameter under a
    /// `modreq(InAttribute)` on the interface's side and not on the class's,
    /// or a `ref readonly` return under another assembly's `InAttribute`.
    /// The runtime matches an implementation by its exact signature, so
    /// Roslyn writes this and a `MethodImpl` row naming it; its signature is
    /// `member`'s, the interface's. In a generic class the call names the
    /// method on the class's own construction, `implementation` being that
    /// method, since a `MethodDef` of a generic type cannot be called
    /// directly.
    Forwarding {
        target: Token,
        member: SymbolId,
        implementation: Option<SymbolId>,
    },
    /// A private method that implements an interface member the class lists
    /// by calling the member of a base class that C# picks to answer it,
    /// where the runtime would not look there itself (see
    /// [`Emitter::plan_inherited_forwarders`]). `setter` says which accessor
    /// where `implementation` is a property; the token is looked up when the
    /// body is written, the base class being planned perhaps after the class.
    InheritedForwarding {
        implementation: SymbolId,
        setter: Option<bool>,
        member: SymbolId,
        /// The base class the implementation is reached through, where it
        /// is a construction: `Base<!0>` under `SubSubT<T>`.
        through: Option<Type>,
    },
    /// A lambda, which becomes a method of its own: the CLI has no lambdas,
    /// only methods and the delegates that point at them.
    Lambda { owner: SymbolId, index: usize },
    /// A local function, whose body was bound inside the method that holds
    /// it — which is the only way a local of that method is in scope inside
    /// it. The index is into that body's list of them.
    LocalFunction { owner: SymbolId, index: usize },
    /// The constructor of a display class, which does nothing but chain to
    /// `object`.
    DisplayConstructor,
    /// The class constructor of a `<>c`, which makes its one instance.
    SingletonStaticConstructor,
    /// A record's positional constructor, which fills the properties its
    /// parameters named.
    RecordConstructor(SymbolId),
    /// One of the members the language gives a record: what it does comes
    /// from what the record holds.
    RecordMember(SymbolId),
    /// `Equals(Base)` in a record derived from another record: a sealed
    /// override that hands over to `Equals(object)`. It has no symbol, since
    /// nothing may call it but through the base's.
    RecordBaseEquals,
    /// The constructor of a state machine, which records the state it starts
    /// in and the thread that made it.
    IteratorConstructor(MachineKey),
    /// The body the source wrote, as the state machine runs it.
    IteratorMoveNext(MachineKey),
    /// `Current`, typed or as an `object`.
    IteratorCurrent(MachineKey, bool),
    /// `GetEnumerator`, typed or untyped.
    IteratorGetEnumerator(MachineKey, bool),
    /// `Dispose`, which runs the `finally`s a walk stopped in the middle of.
    IteratorDispose(MachineKey),
    /// `Reset`, which an iterator never supports.
    IteratorReset,
    /// The method the source wrote, which now makes a state machine and hands
    /// it back.
    IteratorStart(MachineKey),
    /// The constructor of an `async` machine, which chains to `object`.
    AsyncConstructor,
    /// The body of an `async` method, as its machine runs it.
    AsyncMoveNext(MachineKey),
    /// `IAsyncStateMachine.SetStateMachine`, which a class-based machine has
    /// nothing to do in.
    AsyncSetStateMachine,
    /// The `<Main>` that starts an assembly whose `Main` is `async`: it calls
    /// `Main` and waits on the task it gives back (§7.1).
    AsyncMain(SymbolId),
    /// `add_E` or `remove_E` of a field-like event: the language's accessors
    /// around the delegate field, which combine or remove a handler.
    EventAccessor { event: SymbolId, add: bool },
    /// The `async` method the source wrote, which now makes a machine, starts
    /// it, and hands back the builder's task.
    AsyncStart(MachineKey),
    /// The constructor of an `async` iterator's machine: the state it
    /// starts in, the thread that made it, and a builder of its own.
    AsyncIteratorConstructor(MachineKey),
    /// `IAsyncEnumerable<T>.GetAsyncEnumerator`, which hands back the machine
    /// itself for the first walk on the thread that made it, and a fresh one
    /// for any other — each started from what the method was called with.
    AsyncIteratorGetEnumerator(MachineKey),
    /// `IAsyncEnumerator<T>.MoveNextAsync`, which runs the body up to its
    /// next `yield return` or its end, and says which through the promise.
    AsyncIteratorMoveNext(MachineKey),
    /// `IAsyncEnumerator<T>.Current`: what the last `yield return` gave.
    AsyncIteratorCurrent(MachineKey),
    /// A member of `IValueTaskSource<bool>` or `IValueTaskSource`, which the
    /// machine answers by handing it on to its promise.
    AsyncIteratorPromise(MachineKey, PromiseCall),
    /// `IAsyncDisposable.DisposeAsync`, which resumes the body in dispose
    /// mode, to run the `finally`s it stopped inside and nothing else.
    AsyncIteratorDispose(MachineKey),
}

impl MethodSource {
    /// The member the source declared that this method is, whatever its
    /// body became: an iterator and an `async` method are still the method
    /// written, with its attributes and its `this` parameter.
    pub(crate) fn written_member(&self) -> Option<SymbolId> {
        match self {
            Self::Declared(symbol)
            | Self::IteratorStart(MachineKey::Member(symbol))
            | Self::AsyncStart(MachineKey::Member(symbol)) => Some(*symbol),
            _ => None,
        }
    }
}

/// Which member of `IValueTaskSource<bool>` and `IValueTaskSource` an
/// `async` iterator's machine hands on to its promise.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PromiseCall {
    /// `bool IValueTaskSource<bool>.GetResult(short)`.
    GetResult,
    /// `void IValueTaskSource.GetResult(short)`, which drops the `bool`.
    GetResultVoid,
    /// `GetStatus(short)`, the same for both.
    GetStatus,
    /// `OnCompleted(Action<object>, object, short, flags)`, the same for both.
    OnCompleted,
}

/// One parameter of a planned method.
///
/// A synthesised accessor has a parameter that no symbol stands behind, so the
/// plan carries the name and type rather than looking them up again.
/// Whose body a state machine runs: a member's, or a lambda's or a local
/// function's written inside one.
///
/// A closure has no symbol of its own to hang a machine on — a lambda has
/// none at all, and a local function's body is bound on the member's table —
/// so a machine is named by the member and the closure's place in it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum MachineKey {
    Member(SymbolId),
    Lambda { owner: SymbolId, index: usize },
    Function { owner: SymbolId, index: usize },
}

impl MachineKey {
    /// The member whose body the machine's statements were bound in.
    pub(crate) fn owner(self) -> SymbolId {
        match self {
            Self::Member(owner) | Self::Lambda { owner, .. } | Self::Function { owner, .. } => {
                owner
            }
        }
    }
}

/// Where the method a closure became lives, which is what its state machine
/// has to know to reach `this` and to name itself.
#[derive(Clone, Debug)]
pub(crate) struct ClosureHost {
    /// Whether the method has a `this` at all.
    pub(crate) instance: bool,
    /// The display class or state machine the method is a member of, where it
    /// is one: `this` there is that object, and the machine keeps it under a
    /// signature rather than a type, since nothing in the source names it.
    pub(crate) hosted: Option<SigType>,
}

#[derive(Clone, Debug)]
pub(crate) struct ParameterPlan {
    pub(crate) symbol: Option<SymbolId>,
    pub(crate) name: String,
    pub(crate) ty: Type,
    /// Whether it is passed by reference where no parameter symbol says so.
    ///
    /// A lambda's parameters are locals rather than parameter symbols, so a
    /// `ref` on the delegate it answers to has nowhere else to live.
    pub(crate) by_ref: bool,
}

/// Which of the four members the runtime gives a multi-dimensional array.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ArrayMember {
    Constructor,
    Get,
    Set,
    Address,
}

#[derive(Clone, Debug)]
pub(crate) struct MethodPlan {
    pub(crate) source: MethodSource,
    pub(crate) token: Token,
    pub(crate) name: String,
    pub(crate) flags: u16,
    pub(crate) instance: bool,
    pub(crate) return_type: Type,
    pub(crate) parameters: Vec<ParameterPlan>,
    /// The method's own type parameters, which become `GenericParam` rows and
    /// the `GENERIC` bit in its signature.
    pub(crate) type_parameters: Vec<SymbolId>,
    /// How the body is provided; zero means the IL blob provides it.
    pub(crate) impl_flags: u16,
    /// A signature written out rather than derived from the plan, for the one
    /// method whose parameters C# cannot spell: a delegate's constructor takes
    /// a `native int`.
    pub(crate) signature: Option<Vec<u8>>,
}

#[derive(Clone, Debug)]
pub(crate) struct FieldPlan {
    pub(crate) token: Token,
    pub(crate) name: String,
    pub(crate) ty: Type,
    pub(crate) flags: u16,
    /// The property this field backs, for an automatic property.
    pub(crate) symbol: Option<SymbolId>,
    /// The value of a `const` field or an enum member, which metadata stores
    /// rather than the field storing it.
    pub(crate) constant: Option<ConstantValue>,
    /// The signature written instead of the type's, for a field whose type
    /// has no name in the source: a state machine's `<>4__this` where `this`
    /// is a display class.
    pub(crate) sig: Option<SigType>,
}

/// A field-like event: the delegate field it keeps, and the two accessor
/// methods that the `Event` row points at.
#[derive(Clone, Debug)]
pub(crate) struct EventPlan {
    pub(crate) symbol: SymbolId,
    pub(crate) name: String,
    pub(crate) ty: Type,
    pub(crate) add: Token,
    pub(crate) remove: Token,
}

/// A property, which in metadata is two methods and a row saying so.
#[derive(Clone, Debug)]
pub(crate) struct PropertyPlan {
    /// The property declared in the source, whose attributes go on the row.
    pub(crate) symbol: Option<SymbolId>,
    pub(crate) name: String,
    pub(crate) ty: Type,
    pub(crate) instance: bool,
    /// An indexer's arguments; empty for a named property.
    pub(crate) parameters: Vec<Type>,
    pub(crate) getter: Option<Token>,
    pub(crate) setter: Option<Token>,
}

#[derive(Clone, Debug)]
pub(crate) struct TypePlan {
    /// The type this plan is for. A display class has no symbol of its own —
    /// nothing in the source declares one — so it carries the type it is
    /// nested in here and says what it really is in `display`.
    pub(crate) symbol: SymbolId,
    pub(crate) token: Token,
    pub(crate) fields: Vec<FieldPlan>,
    pub(crate) methods: Vec<MethodPlan>,
    pub(crate) properties: Vec<PropertyPlan>,
    /// Set when this plan is a display class rather than a declared type.
    pub(crate) display: Option<SymbolId>,
    /// Set when this plan is the state machine a member's `yield`s made, or
    /// the member whose closure's `await`s made one: the member is where the
    /// machine's type parameters come from.
    pub(crate) iterator: Option<SymbolId>,
    /// Set when this plan is an `async` machine, and whose.
    pub(crate) machine: Option<MachineKey>,
    /// Set when this plan is the display class of one lambda of the member
    /// rather than of the member: the lambda's index.
    pub(crate) nested: Option<Closure>,
}

/// A closure of a member that a display class can belong to: one of its
/// lambdas, or one of its local functions, by index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Closure {
    Lambda(usize),
    Function(usize),
    /// The body of a loop, by the span the class covers: a fresh instance
    /// each time round, which is what C# promises a variable declared in
    /// the body and captured by a closure.
    Scope(TextSpan),
}

impl std::fmt::Display for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Lambda(index) => write!(f, "{index}"),
            Self::Function(index) => write!(f, "f{index}"),
            Self::Scope(span) => write!(f, "s{}", span.start()),
        }
    }
}

/// The class that holds what a lambda captured.
///
/// A captured variable has to outlive the method that declared it: the
/// delegate can be called after the method returned. So the variable stops
/// being a local and becomes a field of an object the method makes on entry,
/// and the lambda becomes a method of that object. Roslyn calls it a display
/// class, and so does this.
#[derive(Clone, Debug, Default)]
pub(crate) struct DisplayView {
    pub(crate) constructor: Token,
    /// A field per captured local, and per captured parameter.
    pub(crate) locals: HashMap<LocalId, Token>,
    pub(crate) parameters: HashMap<SymbolId, Token>,
    /// `<>4__this`, where a lambda reads `this` as well as something else.
    pub(crate) this: Option<Token>,
    /// The lambdas that became methods of it.
    pub(crate) methods: HashMap<usize, Token>,
    /// The local functions that became methods of it, because they read
    /// something of the method that holds them.
    pub(crate) local_functions: HashMap<SymbolId, Token>,
    /// `CS$<>8__locals`: the member's display class, where this is the class
    /// of one lambda of the member and its lambdas read the member's
    /// variables too.
    pub(crate) parent: Option<Token>,
}

#[derive(Clone, Debug)]
pub(crate) struct DisplayClass {
    /// How the class is named in a signature, as the method that makes one
    /// names it. Inside a generic type or a generic method the class is
    /// generic itself — it holds values of those parameters — so that is a
    /// construction rather than a bare name.
    pub(crate) sig: SigType,
    /// The members as the class's own methods reach them: definitions, which
    /// inside the type resolve against whatever it was constructed with.
    pub(crate) inside: DisplayView,
    /// The same members as the method that made the class reaches them:
    /// `MemberRef`s under the construction it named.
    pub(crate) outside: DisplayView,
    /// The class as its own members name it: every parameter its own, `!n`.
    pub(crate) inner_sig: SigType,
    /// Whose class `CS$<>8__locals` points at, where this is a nested class:
    /// the closure around it that has one, or the member's class if `None`.
    pub(crate) parent_closure: Option<Closure>,
    /// The type parameters the class declares, in order: the enclosing
    /// type's, the member's, then those of the local functions around the
    /// closure it was made for. Empty where the class is a state machine.
    pub(crate) generics: Vec<SymbolId>,
}

/// A display class whose members still have to be named under the
/// construction it sits in.
///
/// Everything about them is known while planning; what they *resolve to* is
/// not. A field of type `ObjectPool<T>` names a type that may not have been
/// given a token yet, and a signature built then says `TypeRef` where the
/// definition says `TypeDef` — two blobs for one member, and the call finds
/// nothing. So the names and types are kept and the tokens made once every
/// type has one.
struct PendingDisplay {
    owner: SymbolId,
    token: Token,
    /// How many parameters the enclosing type gave it.
    arity: usize,
    /// How many the method that makes one gave it, after those.
    own: usize,
    /// The closure this is the class of, where it is one closure's rather
    /// than the member's.
    nested: Option<Closure>,
    /// Whether the method that makes one is itself a member of a display
    /// class, which names the method's parameters as its own, `!n`.
    hosted: bool,
    /// The member's display class, as a field of this one names it.
    parent: Option<SigType>,
    /// Where the class declares more than the enclosing type's and the
    /// member's parameters — a nested class inside a generic local function
    /// holds values of that function's too — every parameter it declares,
    /// and how the method that makes one names its construction.
    generics: Option<(Vec<SymbolId>, Vec<SigType>)>,
    locals: Vec<(LocalId, String, Type)>,
    parameters: Vec<(SymbolId, String, Type)>,
    this: Option<Type>,
    methods: Vec<(usize, String, Type, Vec<Type>)>,
    /// The same for the local functions that became methods of it, which are
    /// named by their symbol rather than by a position.
    functions: Vec<(SymbolId, String, Type, Vec<Type>)>,
}

/// A member that says, in its own name, which interface member it stands in
/// for.
///
/// C# writes it as `string IFormattable.ToString(string, IFormatProvider)`,
/// and the member is reachable only through the interface. Metadata says none
/// of that in the name: a `MethodImpl` row names the body and the declaration
/// it answers, and that row is the whole of it.
struct ExplicitImpl {
    /// The type the row belongs to.
    class: Token,
    /// The `MethodDef` of what was written.
    body: Token,
    /// What it stands in for.
    declaration: Declaration,
}

/// The interface member an explicit implementation answers, named the way it
/// will have to be looked up once every type has a token.
enum Declaration {
    Method {
        member: SymbolId,
        interface: Type,
    },
    Accessor {
        property: SymbolId,
        interface: Type,
        setter: bool,
    },
    /// A method of a base class in this assembly, overridden by a body whose
    /// signature differs from it: `Derived.<Clone>$` returns `Derived` where
    /// `Base.<Clone>$` returns `Base`, and only a `MethodImpl` row can say the
    /// one overrides the other.
    Override {
        member: SymbolId,
        /// The base as this class derives from it: `A<int>` for `B1 : A<int>`,
        /// whose `<Clone>$` is a member of that construction.
        through: Type,
    },
}

/// The state every part of emission shares.
pub(crate) struct Emitter<'a> {
    pub(crate) compilation: &'a Compilation,
    pub(crate) binder: Binder<'a>,
    pub(crate) metadata: Metadata,
    pub(crate) references: References,
    /// The `TypeDef` token of each type the assembly defines.
    pub(crate) types: HashMap<SymbolId, Token>,
    /// The field-like events of each type, for its `Event` rows.
    events_of: HashMap<SymbolId, Vec<EventPlan>>,
    /// Every type the assembly *will* define, known before any of them has a
    /// token. Whether a nested type is named as a construction depends on
    /// this, and planning would otherwise get a different answer for a type
    /// depending on whether its turn had come round yet.
    defining: std::collections::HashSet<SymbolId>,
    /// The metadata name of each type the compilation synthesized while
    /// binding — `<>f__AnonymousDelegate0` — which is handed out only once
    /// every body has asked for what it needs.
    synthesized_names: HashMap<SymbolId, String>,
    /// The `MethodDef` token of each method it defines.
    pub(crate) methods: HashMap<SymbolId, Token>,
    /// The name a method is defined under where it is not the symbol's own:
    /// a local function is `<Owner>g__name`, and a `MemberRef` naming it
    /// through a construction has to spell that.
    pub(crate) emitted_names: HashMap<SymbolId, String>,
    /// The same for a lambda's method, by the member it was written in and
    /// its index there: `<M>b__0_1` names it wherever it is reached from.
    pub(crate) lambda_names: HashMap<(SymbolId, usize), String>,
    /// The lambdas that went to their type's `<>c`, and where they are.
    pub(crate) singleton_lambdas: HashMap<(SymbolId, usize), crate::singleton::SingletonLambda>,
    /// Every `<>c`, by its `TypeDef` token.
    pub(crate) singleton_types: HashMap<Token, crate::singleton::Singleton>,
    /// The lambdas of the type being planned that go to its `<>c`.
    pub(crate) singleton_candidates: Vec<(SymbolId, usize)>,
    /// The parameters of `Invoke` each of a delegate's `BeginInvoke` and
    /// `EndInvoke` repeats, by the `MethodDef` token of the method, which
    /// carry the originals' attributes over.
    pub(crate) cloned_parameters: HashMap<Token, Vec<SymbolId>>,
    /// The `#nullable` directives of each tree, where it has any.
    pub(crate) nullable_contexts: Vec<Option<rustlyn_semantics::NullableContexts>>,
    /// Whether nullable metadata is written, decided once the rows are.
    pub(crate) nullable_on: bool,
    /// Each state machine's name, known before its row is written: the
    /// method that makes one names it in `[AsyncStateMachine(typeof(...))]`.
    pub(crate) machine_type_names: HashMap<MachineKey, String>,
    /// Each type's own nullable context, once worked out.
    pub(crate) nullable_type_contexts: HashMap<SymbolId, Option<u8>>,
    pub(crate) pending_singletons: Vec<crate::singleton::PendingSingleton>,
    /// The `Field` token of each field it defines, and of the backing field of
    /// each automatic property.
    pub(crate) fields: HashMap<SymbolId, Token>,
    /// `get_X` and `set_X` for each property.
    pub(crate) getters: HashMap<SymbolId, Token>,
    pub(crate) setters: HashMap<SymbolId, Token>,
    /// The synthesised constructor of each delegate type, which no symbol
    /// stands behind because no source writes one.
    pub(crate) constructors: HashMap<SymbolId, Token>,
    /// Bound bodies, kept so that planning and emitting see the same tree.
    bodies: HashMap<SymbolId, Option<std::sync::Arc<BoundBody>>>,
    /// The bodies being bound on other threads while the plan is made.
    ahead: Option<Ahead>,
    /// The method each lambda became, by the member it was written in and its
    /// place in that member's list.
    pub(crate) lambdas: HashMap<(SymbolId, usize), Token>,
    /// The display class of each member whose lambdas capture something.
    pub(crate) displays: HashMap<SymbolId, DisplayClass>,
    /// The display class of one lambda of a member, by the member and the
    /// lambda: made when the lambda runs, for what closures inside it
    /// capture of its parameters and locals.
    pub(crate) nested_displays: HashMap<(SymbolId, Closure), DisplayClass>,
    /// The `FixedElementField` and element type of every `fixed` buffer
    /// field, by the field.
    pub(crate) fixed_buffers: HashMap<SymbolId, (Token, Type)>,
    /// The struct planned for each `fixed` buffer, by its type token: what
    /// it is called and how many bytes it is.
    fixed_buffer_types: HashMap<Token, (String, u32)>,
    /// The state machine each iterator member became.
    pub(crate) iterators: HashMap<MachineKey, crate::iterator::IteratorPlan>,
    /// The interface rows those machines still need written.
    pub(crate) iterator_impls: Vec<crate::iterator::IteratorImpls>,
    /// The machines whose outward-facing members still need naming.
    pub(crate) iterator_pending: Vec<crate::iterator::PendingIterator>,
    /// The state machine each `async` member became.
    pub(crate) asyncs: HashMap<MachineKey, crate::async_machine::AsyncPlan>,
    /// The `async` machines whose members still need naming.
    pub(crate) async_pending: Vec<crate::async_machine::PendingAsync>,
    /// Each `async` body with its `await`s moved out, or why that could not
    /// be done.
    pub(crate) async_bodies: HashMap<MachineKey, Result<BoundBody, String>>,
    /// Where each lambda and local function's method lives, by the machine
    /// it would be the start of.
    pub(crate) closure_hosts: HashMap<MachineKey, ClosureHost>,
    /// The closures that became `async` machines, in planning order.
    pub(crate) async_closures: Vec<MachineKey>,
    /// The closures that became iterators, in planning order.
    pub(crate) iterator_closures: Vec<MachineKey>,
    /// Display classes whose members are named once every type has a token.
    display_pending: Vec<PendingDisplay>,
    /// Every interface a class, or anything deriving from it, has to answer
    /// for. A member that answers one of them is virtual whatever it wrote.
    answering: HashMap<SymbolId, Vec<Type>>,
    /// The enclosing method's type parameters that each method the compiler
    /// made carries, by that method's token.
    ///
    /// A call to one names them: the method is generic even though nothing in
    /// the source wrote a type parameter on it.
    pub(crate) inherited_generics: HashMap<Token, Vec<SymbolId>>,
    /// The type parameters of the generic local functions a lambda of a
    /// display class sits in, which its method declares as its own.
    pub(crate) lambda_generics: HashMap<(SymbolId, usize), Vec<SymbolId>>,
    /// The type parameters the method being written declares, in order.
    ///
    /// A lambda or a local function written in a generic method becomes a
    /// method of its own, and the enclosing method's parameters are copied
    /// onto it: from inside, `!!0` is the first of *that* list.
    pub(crate) method_generics: Vec<SymbolId>,
    /// The type parameters the type currently being written declares, where
    /// it is one the compiler made. A display class over a generic method
    /// declares that method's parameters as its own, so inside it they are
    /// the type's — `!0` and not `!!0` — and a signature has to say so.
    pub(crate) display_generics: Vec<SymbolId>,
    /// Every `string IFormattable.ToString(...)` met, kept until the plan is
    /// complete: the interface it names may be planned after the type that
    /// implements it, so the token it needs does not exist yet.
    explicit_impls: Vec<ExplicitImpl>,
    /// The bodies that override with a narrower return type (C# 9), which
    /// carry `[PreserveBaseOverrides]`: an override of one of them further
    /// down then answers the base's slot too.
    covariant_bodies: std::collections::HashSet<Token>,
    /// Whether a type the plan cannot make is skipped rather than fatal.
    ///
    /// An assembly with a hole in it is not an assembly, so `emit` stops.
    /// Measuring how much of a project comes out has to keep going, or the
    /// answer is always the first thing in the way.
    pub(crate) lenient: bool,
    /// The `<Module>..cctor` that calls each `[ModuleInitializer]` method,
    /// where the compilation has any: its token, the methods it calls in
    /// lexical order, and where its body starts once generated.
    module_constructor: Option<(Token, Vec<SymbolId>, u32)>,
    /// The types skipped that way, with the reason.
    pub(crate) skipped: Vec<(String, String)>,
    /// The classes holding the call sites of `dynamic` operations, made as
    /// the bodies that need them are emitted, each with the type it is
    /// nested in and its name.
    pub(crate) dynamic_containers: Vec<(TypePlan, crate::dynamic::SiteRow)>,
    /// The class the body being emitted keeps its sites in, once it has one.
    pub(crate) dynamic_current: crate::dynamic::SiteContainer,
    /// The type the body being emitted belongs to.
    pub(crate) dynamic_enclosing: Option<SymbolId>,
    /// Each site class's row, by its token: the type it is nested in and
    /// its name.
    pub(crate) dynamic_rows: HashMap<Token, crate::dynamic::SiteRow>,
    /// The bytes block-initialized arrays are copied out of, as the image
    /// holds them, each blob eight-byte aligned.
    pub(crate) mapped_data: Vec<u8>,
    /// The field each such blob is, by the SHA-256 of its bytes.
    pub(crate) array_data: HashMap<[u8; 32], Token>,
    /// `<PrivateImplementationDetails>` (no size) and the structs of each
    /// size nested in it, by token.
    array_data_types: HashMap<Token, Option<u32>>,
    /// Where each blob's field starts in `mapped_data`.
    array_data_offsets: Vec<(Token, u32)>,
    /// The delegate types made for sites that pass something by reference,
    /// by the signature of their `Invoke`.
    pub(crate) site_delegates: HashMap<Vec<u8>, (SigType, Token)>,
    /// The next `TypeDef` and `Field` rows, once the plan has handed out
    /// its own.
    pub(crate) next_type: u32,
    pub(crate) next_field: u32,
    /// The structs an editor's build gives a tail, by qualified name, and
    /// whether the tail has slots for references (`IncrementalOptions`).
    pub(crate) struct_tails: HashMap<String, bool>,
    /// The program's own `InAttribute`, if it declares one, as of how many
    /// types were planned when it was looked for: a search of every type's
    /// name, which every `in` parameter and `ref readonly` return asks.
    own_in_attribute: Option<(usize, Option<SymbolId>)>,
    /// A getter-only automatic property also gets an internal setter, of
    /// its backing field: a patch to a constructor that sets the property
    /// calls it, where only the class's own constructor could have.
    getter_only_setters: bool,
    pub(crate) next_method: u32,
}

/// Compiles a whole compilation into one assembly.
///
/// # Errors
///
/// Returns the first construct met that this backend does not emit yet, or the
/// reason no entry point could be found.
pub fn emit(compilation: &Compilation, name: &str) -> Result<Emitted, EmitError> {
    emit_with_resources(compilation, name, &[])
}

/// Lays the resources out the way the runtime reads them: each one is its
/// length and then its bytes, on an eight-byte boundary, and the manifest
/// names each by its offset into the whole (§II.24.3.4).
fn embed_resources(metadata: &mut Metadata, resources: &[Resource]) -> Vec<u8> {
    let mut blob = Vec::new();
    for resource in resources {
        while blob.len() % 8 != 0 {
            blob.push(0);
        }
        metadata.add_manifest_resource(blob.len() as u32, &resource.name);
        blob.extend_from_slice(&(resource.data.len() as u32).to_le_bytes());
        blob.extend_from_slice(&resource.data);
    }
    blob
}

/// Compiles a whole compilation into one assembly with these resources
/// embedded in it.
///
/// # Errors
///
/// As for [`emit`].
pub fn emit_with_resources(
    compilation: &Compilation,
    name: &str,
    resources: &[Resource],
) -> Result<Emitted, EmitError> {
    emit_assembly(compilation, name, resources, false, None)
}

/// Compiles a whole compilation into an assembly that starts at the `Main`
/// of the type named (csc's `/main:`, Roslyn's `MainTypeName`), where more
/// than one type has one — or top-level statements beside a `Main`.
///
/// # Errors
///
/// As for [`emit`], and where the type has no `Main` to start at.
pub fn emit_with_main_type(
    compilation: &Compilation,
    name: &str,
    main_type: &str,
) -> Result<Emitted, EmitError> {
    emit_assembly(compilation, name, &[], false, Some(main_type))
}

/// Compiles a whole compilation into a library: an assembly with no entry
/// point, for other assemblies to reference.
///
/// # Errors
///
/// Returns the first construct met that this backend does not emit yet.
pub fn emit_library(compilation: &Compilation, name: &str) -> Result<Emitted, EmitError> {
    emit_assembly(compilation, name, &[], true, None)
}

fn emit_assembly(
    compilation: &Compilation,
    name: &str,
    resources: &[Resource],
    library: bool,
    main_type: Option<&str>,
) -> Result<Emitted, EmitError> {
    // Lowering and generating code walk each body as deep as it nests.
    rustlyn_semantics::parallel::deep(|| {
        emit_assembly_here(compilation, name, resources, library, main_type)
    })
}

fn emit_assembly_here(
    compilation: &Compilation,
    name: &str,
    resources: &[Resource],
    library: bool,
    main_type: Option<&str>,
) -> Result<Emitted, EmitError> {
    let mut emitter = Emitter::new(compilation, name, false);

    let planning = rustlyn_semantics::timing::phase("plan");
    let plans = emitter.plan()?;
    drop(planning);
    let generating = rustlyn_semantics::timing::phase("generate");
    let (il, mut bodies) = emitter.generate(&plans)?;
    drop(generating);
    let _writing = rustlyn_semantics::timing::phase("write");
    let mut plans = plans;
    emitter.take_site_containers(&mut plans, &mut bodies);
    let entry_point = if library {
        Token(0)
    } else {
        emitter.entry_point(&plans, main_type)?
    };
    emitter.write_rows(&plans, &bodies)?;
    // Every body of the compilation is in there, and freeing tens of
    // thousands of trees takes long enough to be worth doing beside the
    // rest rather than before it.
    let bodies_bound = std::mem::take(&mut emitter.bodies);
    std::thread::spawn(move || drop(bodies_bound));

    let resources = embed_resources(&mut emitter.metadata, resources);
    let metadata = emitter.metadata.write(il_rva(emitter.mapped_data.len()));
    let assembly = crate::pe::write(&PeLayout {
        data: emitter.mapped_data.clone(),
        il,
        resources,
        metadata,
        entry_point: entry_point.0,
    });
    Ok(Emitted {
        assembly,
        runtime_config: runtime_config(emitter.references.framework_major()),
    })
}

/// The body of a method a survey could not write: it throws, saying which.
///
/// `ldstr <name>; newobj NotImplementedException(string); throw`, so that
/// running the assembly says which of the two it met — a body this backend
/// could not write, and which one, or a bug in one it could. `ldnull; throw`
/// would say `NullReferenceException`, which is exactly what a real mistake
/// looks like; and a message beats a stack frame, which the JIT is free to
/// fold into whatever called it.
fn stub_body(constructor: Token, name: Token) -> Vec<u8> {
    let mut code = vec![0x72];
    code.extend_from_slice(&name.0.to_le_bytes());
    code.push(0x73);
    code.extend_from_slice(&constructor.0.to_le_bytes());
    code.push(0x7A);
    // A tiny header carries the code size in its top six bits.
    let mut body = vec![0x02 | ((code.len() as u8) << 2)];
    body.extend_from_slice(&code);
    body
}

/// Emits the whole compilation, writing a throwing body where one cannot be
/// written, and says which those were.
///
/// This is for looking at an assembly that does not compile yet: everything
/// but the bodies that failed is real, so the rows, the signatures and the
/// layout can be read back and checked.
///
/// # Errors
///
/// Returns an error when the plan itself cannot be made.
pub fn survey(
    compilation: &Compilation,
    name: &str,
) -> Result<(Emitted, Vec<(String, String)>), EmitError> {
    survey_with_resources(compilation, name, &[])
}

/// A survey whose assembly carries these resources.
///
/// # Errors
///
/// As for [`survey`].
pub fn survey_with_resources(
    compilation: &Compilation,
    name: &str,
    resources: &[Resource],
) -> Result<(Emitted, Vec<(String, String)>), EmitError> {
    let mut emitter = Emitter::new(compilation, name, true);

    let planning = rustlyn_semantics::timing::phase("plan");
    let plans = emitter.plan()?;
    drop(planning);
    let generating = rustlyn_semantics::timing::phase("generate");
    let (il, mut bodies) = emitter.generate(&plans)?;
    drop(generating);
    let _writing = rustlyn_semantics::timing::phase("write");
    let mut plans = plans;
    emitter.take_site_containers(&mut plans, &mut bodies);
    // A library has no entry point, and a survey is of a library.
    let entry_point = emitter.entry_point(&plans, None).unwrap_or(Token(0));
    emitter.write_rows(&plans, &bodies)?;
    // Every body of the compilation is in there, and freeing tens of
    // thousands of trees takes long enough to be worth doing beside the
    // rest rather than before it.
    let bodies_bound = std::mem::take(&mut emitter.bodies);
    std::thread::spawn(move || drop(bodies_bound));

    let resources = embed_resources(&mut emitter.metadata, resources);
    let metadata = emitter.metadata.write(il_rva(emitter.mapped_data.len()));
    let assembly = crate::pe::write(&PeLayout {
        data: emitter.mapped_data.clone(),
        il,
        resources,
        metadata,
        entry_point: entry_point.0,
    });
    Ok((
        Emitted {
            assembly,
            runtime_config: runtime_config(emitter.references.framework_major()),
        },
        std::mem::take(&mut emitter.skipped),
    ))
}

/// A survey kept in memory after it is written, so that a change to a few
/// method bodies writes the assembly again without generating the others.
///
/// Every token stays where the first build put it: a changed body goes after
/// all the others, its row is pointed at it, and whatever new references it
/// makes are added after the rows already there. That holds only while the
/// declarations are the same — the same members, and in each changed body
/// the same lambdas, local functions and state machines the plan made
/// classes and methods for — so the caller rebuilds from scratch otherwise.
pub struct Incremental<'a> {
    emitter: Emitter<'a>,
    plans: Vec<TypePlan>,
    il: Vec<u8>,
    entry_point: Token,
}

impl std::fmt::Debug for Incremental<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Incremental")
            .field("types", &self.plans.len())
            .field("il_bytes", &self.il.len())
            .finish_non_exhaustive()
    }
}

/// What [`Incremental::rebuild`] did.
#[derive(Debug)]
pub struct Rebuilt {
    pub assembly: Vec<u8>,
    /// Methods whose bodies were generated again: a member's own, its
    /// lambdas' and local functions', its state machine's.
    pub bodies: usize,
    /// How many bytes of IL the changed bodies added; the bodies they
    /// replace stay behind, pointed at by nothing.
    pub appended_bytes: usize,
}

/// What [`incremental`] gives: the build kept for the next one, the
/// assembly, and the bodies written as throwing stubs, as [`survey`] says.
pub type Started<'a> = (Incremental<'a>, Emitted, Vec<(String, String)>);

/// Surveys the compilation as [`survey`] does and keeps what is needed to
/// write it again after a change.
///
/// # Errors
///
/// As for [`survey`].
pub fn incremental<'a>(compilation: &'a Compilation, name: &str) -> Result<Started<'a>, EmitError> {
    incremental_with(compilation, name, IncrementalOptions::default())
}

/// How [`incremental_with`] builds the assembly it keeps.
#[derive(Clone, Debug, Default)]
pub struct IncrementalOptions {
    /// An editor's build that hot patches will reach into: every member is
    /// opened to the assembly (see `Metadata::widen_for_patches`), so that a
    /// patch assembly the build names in an `InternalsVisibleTo` can read and
    /// call what the patched method could.
    pub widen_for_patches: bool,
    /// The structs given a tail — a last field, `__pilotTail`, of
    /// `PilotTail.Tail` where the bool says it holds references and of
    /// `PilotTail.ValueTail` where not — by qualified name: room for the
    /// fields an edit adds to a struct, which a loaded struct cannot grow.
    /// The compilation has to declare the two tail types.
    pub struct_tails: HashMap<String, bool>,
}

/// [`incremental`], built as the options say.
///
/// # Errors
///
/// As for [`survey`].
pub fn incremental_with<'a>(
    compilation: &'a Compilation,
    name: &str,
    options: IncrementalOptions,
) -> Result<Started<'a>, EmitError> {
    let mut emitter = Emitter::new(compilation, name, true);
    emitter.struct_tails = options.struct_tails.clone();
    emitter.getter_only_setters = options.widen_for_patches;
    let planning = rustlyn_semantics::timing::phase("plan");
    let plans = emitter.plan()?;
    drop(planning);
    let generating = rustlyn_semantics::timing::phase("generate");
    let (il, mut bodies) = emitter.generate(&plans)?;
    drop(generating);
    let _writing = rustlyn_semantics::timing::phase("write");
    let mut plans = plans;
    emitter.take_site_containers(&mut plans, &mut bodies);
    let entry_point = emitter.entry_point(&plans, None).unwrap_or(Token(0));
    emitter.write_rows(&plans, &bodies)?;
    if options.widen_for_patches {
        let unity_owned = emitter.unity_object_fields();
        emitter.metadata.widen_for_patches(&unity_owned);
    }
    let bodies_bound = std::mem::take(&mut emitter.bodies);
    std::thread::spawn(move || drop(bodies_bound));

    let metadata = emitter.metadata.write(il_rva(emitter.mapped_data.len()));
    let assembly = crate::pe::write(&PeLayout {
        data: emitter.mapped_data.clone(),
        il: il.clone(),
        resources: Vec::new(),
        metadata,
        entry_point: entry_point.0,
    });
    let skipped = std::mem::take(&mut emitter.skipped);
    let emitted = Emitted {
        assembly,
        runtime_config: runtime_config(emitter.references.framework_major()),
    };
    let kept = Incremental {
        emitter,
        plans,
        il,
        entry_point,
    };
    Ok((kept, emitted, skipped))
}

impl Emitter<'_> {
    /// The rows of the instance fields of Unity objects — `MonoBehaviour`s,
    /// `ScriptableObject`s — whose `initonly` an editor's build keeps: Unity
    /// writes what such an object holds when it reloads, and reads it back
    /// expecting the fields it wrote, as csc's build has them.
    fn unity_object_fields(&self) -> std::collections::HashSet<u32> {
        let symbols = self.compilation.symbols();
        let binder = Binder::new(self.compilation);
        let mut unity = HashMap::new();
        let mut is_unity = |ty: SymbolId| -> bool {
            *unity.entry(ty).or_insert_with(|| {
                let mut current = Some(ty);
                for _ in 0..32 {
                    let Some(id) = current else { return false };
                    if symbols.qualified_name(id) == "UnityEngine.Object" {
                        return true;
                    }
                    current = match binder.base_class_of(id) {
                        Some(Type::Named { symbol, .. }) => Some(symbol),
                        _ => None,
                    };
                }
                false
            })
        };
        self.fields
            .iter()
            .filter(|(field, _)| symbols.get(**field).container.is_some_and(&mut is_unity))
            .map(|(_, token)| token.0 & 0x00FF_FFFF)
            .collect()
    }
}

impl<'a> Incremental<'a> {
    /// Writes the assembly again for `compilation`, which differs from the
    /// one before only inside the bodies of `changed`.
    ///
    /// # Errors
    ///
    /// When a changed body needs something the plan did not make for it — a
    /// `dynamic` call site's container — and so only a full build will do.
    pub fn rebuild(
        &mut self,
        compilation: &'a Compilation,
        changed: &[SymbolId],
    ) -> Result<Rebuilt, EmitError> {
        let emitter = &mut self.emitter;
        emitter.compilation = compilation;
        emitter.binder = Binder::new(compilation);
        for symbol in changed {
            emitter.bodies.remove(symbol);
        }
        let belongs = |source: &MethodSource| match source {
            MethodSource::Declared(symbol) => changed.contains(symbol),
            MethodSource::Lambda { owner, .. } | MethodSource::LocalFunction { owner, .. } => {
                changed.contains(owner)
            }
            MethodSource::IteratorMoveNext(key)
            | MethodSource::IteratorStart(key)
            | MethodSource::IteratorDispose(key)
            | MethodSource::AsyncMoveNext(key)
            | MethodSource::AsyncStart(key)
            | MethodSource::AsyncIteratorMoveNext(key)
            | MethodSource::AsyncIteratorDispose(key) => changed.contains(&key.owner()),
            _ => false,
        };
        let mut bodies = 0;
        let mut appended_bytes = 0;
        for plan in &self.plans {
            if !plan.methods.iter().any(|method| belongs(&method.source)) {
                continue;
            }
            emitter.display_generics = emitter.display_parameters(plan);
            for method in &plan.methods {
                if !belongs(&method.source)
                    || method.flags & method_attributes::ABSTRACT != 0
                    || method.impl_flags & method_impl::RUNTIME != 0
                {
                    continue;
                }
                emitter.method_generics = method.type_parameters.clone();
                emitter.dynamic_enclosing = Some(plan.symbol);
                emitter.dynamic_current = crate::dynamic::SiteContainer::default();
                let body = match BodyEmitter::emit(emitter, plan, method) {
                    Ok(body) => body,
                    Err(error) => {
                        let owner = compilation.symbols().qualified_name(plan.symbol);
                        emitter
                            .skipped
                            .push((format!("{owner}.{}", method.name), error.message.clone()));
                        let constructor = emitter.not_implemented();
                        let said = emitter.metadata.user_string(&format!(
                            "{owner}.{} is not emitted: {}",
                            method.name, error.message
                        ));
                        stub_body(constructor, said)
                    }
                };
                while !self.il.len().is_multiple_of(4) {
                    self.il.push(0);
                }
                appended_bytes += body.len();
                emitter
                    .metadata
                    .set_method_body(method.token, self.il.len() as u32);
                self.il.extend_from_slice(&body);
                bodies += 1;
            }
        }
        emitter.method_generics = Vec::new();
        emitter.display_generics = Vec::new();
        if !emitter.dynamic_containers.is_empty() {
            return Err(EmitError::new(
                "a changed body made a `dynamic` call site the plan has no class for",
            ));
        }
        let metadata = emitter.metadata.write(il_rva(emitter.mapped_data.len()));
        let assembly = crate::pe::write(&PeLayout {
            data: emitter.mapped_data.clone(),
            il: self.il.clone(),
            resources: Vec::new(),
            metadata,
            entry_point: self.entry_point.0,
        });
        Ok(Rebuilt {
            assembly,
            bodies,
            appended_bytes,
        })
    }
}

/// Tries every method body in the compilation and says which ones came out.
///
/// # Errors
///
/// Returns an error only when the plan itself cannot be made — when nothing
/// can be attempted at all. A body that fails is counted, not returned.
pub fn coverage(compilation: &Compilation, name: &str) -> Result<Coverage, EmitError> {
    let mut emitter = Emitter::new(compilation, name, true);

    let plans = emitter.plan()?;
    let mut coverage = Coverage::default();
    for plan in &plans {
        // Which file the type was written in: a body belongs to it even when
        // the body itself is one the compiler wrote.
        let tree = emitter
            .compilation
            .declaration_nodes(plan.symbol)
            .first()
            .map(|(tree, _)| *tree);
        for method in &plan.methods {
            // Abstract, or provided by the runtime: there is no body to emit
            // and nothing to count.
            if method.flags & method_attributes::ABSTRACT != 0
                || method.flags & method_attributes::PINVOKE_IMPL != 0
                || method.impl_flags & method_impl::RUNTIME != 0
            {
                continue;
            }
            let owner = emitter.compilation.symbols().qualified_name(plan.symbol);
            let failure = BodyEmitter::emit(&mut emitter, plan, method)
                .err()
                .map(|error| error.message);
            coverage.bodies.push(CoverageEntry {
                tree,
                method: format!("{owner}.{}", method.name),
                failure,
            });
        }
    }
    // A type the plan could not make has bodies too, and leaving them out
    // would flatter the count.
    for (name, reason) in std::mem::take(&mut emitter.skipped) {
        coverage.bodies.push(CoverageEntry {
            tree: None,
            method: name,
            failure: Some(reason),
        });
    }
    Ok(coverage)
}

impl<'a> Emitter<'a> {
    /// An emitter that has planned nothing yet. `lenient` writes a throwing
    /// body where one cannot be written instead of failing the compile.
    fn new(compilation: &'a Compilation, name: &str, lenient: bool) -> Self {
        Emitter {
            compilation,
            binder: Binder::new(compilation),
            metadata: Metadata::new(&format!("{name}.dll"), name),
            references: References::new(compilation),
            types: HashMap::new(),
            events_of: HashMap::new(),
            defining: std::collections::HashSet::new(),
            synthesized_names: HashMap::new(),
            methods: HashMap::new(),
            emitted_names: HashMap::new(),
            lambda_names: HashMap::new(),
            singleton_lambdas: HashMap::new(),
            singleton_types: HashMap::new(),
            singleton_candidates: Vec::new(),
            cloned_parameters: HashMap::new(),
            nullable_contexts: crate::nullable::contexts_of(compilation),
            nullable_on: false,
            machine_type_names: HashMap::new(),
            nullable_type_contexts: HashMap::new(),
            pending_singletons: Vec::new(),
            fields: HashMap::new(),
            getters: HashMap::new(),
            setters: HashMap::new(),
            constructors: HashMap::new(),
            bodies: HashMap::new(),
            ahead: None,
            lambdas: HashMap::new(),
            displays: HashMap::new(),
            iterators: HashMap::new(),
            iterator_impls: Vec::new(),
            iterator_pending: Vec::new(),
            asyncs: HashMap::new(),
            async_pending: Vec::new(),
            async_bodies: HashMap::new(),
            explicit_impls: Vec::new(),
            covariant_bodies: std::collections::HashSet::new(),
            display_pending: Vec::new(),
            closure_hosts: HashMap::new(),
            nested_displays: HashMap::new(),
            fixed_buffers: HashMap::new(),
            fixed_buffer_types: HashMap::new(),
            async_closures: Vec::new(),
            iterator_closures: Vec::new(),
            answering: HashMap::new(),
            inherited_generics: HashMap::new(),
            lambda_generics: HashMap::new(),
            method_generics: Vec::new(),
            display_generics: Vec::new(),
            lenient,
            module_constructor: None,
            skipped: Vec::new(),
            dynamic_containers: Vec::new(),
            dynamic_current: crate::dynamic::SiteContainer::default(),
            dynamic_enclosing: None,
            dynamic_rows: HashMap::new(),
            mapped_data: Vec::new(),
            array_data: HashMap::new(),
            array_data_types: HashMap::new(),
            array_data_offsets: Vec::new(),
            site_delegates: HashMap::new(),
            next_type: 0,
            next_field: 0,
            struct_tails: HashMap::new(),
            own_in_attribute: None,
            getter_only_setters: false,
            next_method: 0,
        }
    }
}

impl Emitter<'_> {
    /// Decides what the assembly will contain and what token each part gets.
    fn plan(&mut self) -> Result<Vec<TypePlan>, EmitError> {
        let user_types = self.user_types();
        let owners = self.owners_of_bodies(&user_types);
        let slots: std::sync::Arc<[BodySlot]> = owners.iter().map(|_| BodySlot::new()).collect();
        let next = std::sync::atomic::AtomicUsize::new(0);
        let compilation = self.compilation;
        std::thread::scope(|scope| {
            // Every core binds, in the order the plan will ask; this thread
            // plans, waiting only where it catches up with them.
            // Each on the largest stack there is room for; the plan waits
            // on what they bind, so one of them at least has to start.
            let mut started = 0;
            for _ in 0..rustlyn_semantics::parallel::threads() {
                let (owners, next) = (&owners, &next);
                let thread = rustlyn_semantics::parallel::spawn_scoped(
                    scope,
                    rustlyn_semantics::parallel::STACK,
                    || {
                        let slots = std::sync::Arc::clone(&slots);
                        move || {
                            let binder = Binder::new(compilation);
                            loop {
                                let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                                let Some(&owner) = owners.get(index) else {
                                    break;
                                };
                                // A body whose binding panics is bound again
                                // where it is asked for, and panics there.
                                let bound =
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        bind_body_with(compilation, &binder, owner)
                                            .map(|body| spilled_with(compilation, slimmed(body)))
                                    }));
                                let _ = slots[index]
                                    .set(bound.ok().map(|body| body.map(std::sync::Arc::new)));
                            }
                        }
                    },
                );
                if thread.is_none() {
                    break;
                }
                started += 1;
            }
            assert!(started > 0, "a binding thread should start");
            self.ahead = Some(Ahead {
                index: owners
                    .iter()
                    .enumerate()
                    .map(|(index, owner)| (*owner, index))
                    .collect(),
                slots: std::sync::Arc::clone(&slots),
            });
            let planned = self.plan_types(user_types);
            // The bodies the plan did not ask for are the generator's.
            self.finish_binding();
            let mut planned = planned?;
            self.plan_array_data(&mut planned);
            Ok(planned)
        })
    }

    /// `<PrivateImplementationDetails>`, with a field for every distinct
    /// blob an array initializer of the bound bodies is copied out of
    /// (`RuntimeHelpers.InitializeArray`), named by the blob's SHA-256 as
    /// Roslyn names it, and a struct of each blob size to type them.
    ///
    /// Planned once every body is bound and before any is generated, so the
    /// fields are one run of rows; a body that makes an array the scan did
    /// not see — lowering writes some — fills it element by element.
    fn plan_array_data(&mut self, plans: &mut Vec<TypePlan>) {
        let Some(symbol) = plans.first().map(|plan| plan.symbol) else {
            return;
        };
        let mut blobs: std::collections::BTreeMap<[u8; 32], Vec<u8>> =
            std::collections::BTreeMap::new();
        for body in self.bodies.values().flatten() {
            body.each_expression(&mut |expression| {
                if let BoundExpressionKind::ArrayCreation {
                    element,
                    lengths,
                    elements,
                } = &expression.kind
                    && let Some(data) = self.array_block_data(element, lengths, elements)
                {
                    blobs
                        .entry(rustlyn_semantics::sha256(&data))
                        .or_insert(data);
                }
            });
        }
        if blobs.is_empty() {
            return;
        }
        let details = Token::new(table::TYPE_DEF, self.next_type);
        self.next_type += 1;
        self.array_data_types.insert(details, None);
        // The structs in the order of their names, as Roslyn has them; a
        // blob of one, two, four or eight bytes is typed as the integer that
        // size instead.
        let mut sizes: Vec<u32> = blobs
            .values()
            .map(|data| data.len() as u32)
            .filter(|size| primitive_of_size(*size).is_none())
            .collect();
        sizes.sort_by_key(|size| array_data_type_name(*size));
        sizes.dedup();
        let mut size_types = HashMap::new();
        let mut nested = Vec::new();
        for size in sizes {
            let token = Token::new(table::TYPE_DEF, self.next_type);
            self.next_type += 1;
            self.array_data_types.insert(token, Some(size));
            size_types.insert(size, token);
            nested.push(token);
        }
        let mut fields = Vec::new();
        for (hash, data) in blobs {
            let token = Token::new(table::FIELD, self.next_field);
            self.next_field += 1;
            while !self.mapped_data.len().is_multiple_of(8) {
                self.mapped_data.push(0);
            }
            self.array_data_offsets
                .push((token, self.mapped_data.len() as u32));
            let size = data.len() as u32;
            let sig = primitive_of_size(size).map_or_else(
                || SigType::Named {
                    value_type: true,
                    coded: type_def_or_ref(0, size_types[&size].0 & 0x00FF_FFFF),
                },
                SigType::Primitive,
            );
            self.mapped_data.extend_from_slice(&data);
            self.array_data.insert(hash, token);
            fields.push(FieldPlan {
                token,
                name: hash.iter().map(|byte| format!("{byte:02X}")).collect(),
                ty: Type::Error,
                flags: field_attributes::ASSEMBLY
                    | field_attributes::STATIC
                    | field_attributes::INIT_ONLY
                    | field_attributes::HAS_FIELD_RVA,
                symbol: None,
                constant: None,
                sig: Some(sig),
            });
        }
        let empty = |token| TypePlan {
            symbol,
            token,
            fields: Vec::new(),
            methods: Vec::new(),
            properties: Vec::new(),
            display: None,
            iterator: None,
            machine: None,
            nested: None,
        };
        let mut outer = empty(details);
        outer.fields = fields;
        plans.push(outer);
        plans.extend(nested.into_iter().map(empty));
    }

    /// The bytes `new T[] { ... }` is filled with, where `InitializeArray`
    /// may copy them in: a one-dimensional array of a primitive type, every
    /// element a constant and more than two of them not zero (Roslyn's
    /// `ShouldEmitBlockInitializer`).
    pub(crate) fn array_block_data(
        &self,
        element: &Type,
        lengths: &[BoundExpression],
        elements: &[BoundExpression],
    ) -> Option<Vec<u8>> {
        use SpecialType as S;
        // An enum's elements are its underlying type's, as Roslyn copies
        // them.
        let stored = match element.symbol() {
            Some(symbol)
                if self.compilation.symbols().get(symbol).type_kind() == Some(TypeKind::Enum) =>
            {
                self.enum_underlying(symbol)
            }
            _ => element.clone(),
        };
        let special = self.special_type_of(&stored)?;
        let width = match special {
            S::Boolean | S::SByte | S::Byte => 1,
            S::Int16 | S::UInt16 | S::Char => 2,
            S::Int32 | S::UInt32 | S::Single => 4,
            S::Int64 | S::UInt64 | S::Double => 8,
            _ => return None,
        };
        match lengths {
            [] => {}
            [length] => {
                if self.binder.folded(length) != Some(ConstantValue::Int32(elements.len() as i32)) {
                    return None;
                }
            }
            _ => return None,
        }
        let mut data = Vec::with_capacity(elements.len() * width);
        let mut written = 0;
        for value in elements {
            let constant = self.binder.folded(value)?;
            let bytes = element_bytes(special, &constant)?;
            if bytes.iter().any(|byte| *byte != 0) {
                written += 1;
            }
            data.extend_from_slice(&bytes);
        }
        (written > 2).then_some(data)
    }

    /// The field an array's block initializer is copied out of, where the
    /// plan made one for these bytes.
    pub(crate) fn array_block_field(
        &self,
        element: &Type,
        lengths: &[BoundExpression],
        elements: &[BoundExpression],
    ) -> Option<Token> {
        let data = self.array_block_data(element, lengths, elements)?;
        self.array_data
            .get(&rustlyn_semantics::sha256(&data))
            .copied()
    }

    /// `RuntimeHelpers.InitializeArray(Array, RuntimeFieldHandle)`.
    pub(crate) fn initialize_array(&mut self) -> Token {
        let array = self
            .references
            .type_ref_coded(&mut self.metadata, "System.Array");
        let handle = self
            .references
            .type_ref_coded(&mut self.metadata, "System.RuntimeFieldHandle");
        let signature = method_signature(
            false,
            &SigType::Primitive(ElementType::Void),
            &[
                SigType::Named {
                    value_type: false,
                    coded: array,
                },
                SigType::Named {
                    value_type: true,
                    coded: handle,
                },
            ],
        );
        self.references.member_ref(
            &mut self.metadata,
            "System.Runtime.CompilerServices.RuntimeHelpers",
            "InitializeArray",
            &signature,
        )
    }

    /// Every type the source declares, in the order they are planned.
    fn user_types(&self) -> Vec<SymbolId> {
        self.compilation
            .all_types()
            .filter(|symbol| !self.compilation.is_from_corlib(symbol.id))
            .map(|symbol| symbol.id)
            .collect()
    }

    /// Decides what the assembly will contain and what token each part gets.
    fn plan_types(&mut self, user_types: Vec<SymbolId>) -> Result<Vec<TypePlan>, EmitError> {
        let symbols = self.compilation.symbols();
        // Row 1 of `TypeDef` is always `<Module>`, the pseudo-type that owns
        // anything declared outside a class.
        let mut next_type = 2u32;
        let mut next_method = 1u32;
        let mut next_field = 1u32;
        let mut plans = Vec::new();

        self.defining = user_types.iter().copied().collect();
        self.answering = self.interfaces_to_answer();

        // `<Module>`'s class constructor, when there are initializers for it
        // to call, is the first `MethodDef`: `<Module>` is the first type.
        let initializers = self.module_initializers(&user_types);
        if !initializers.is_empty() {
            self.module_constructor = Some((Token::new(table::METHOD_DEF, 1), initializers, 0));
            next_method = 2;
        }

        for symbol in user_types {
            let detail = symbols.get(symbol);
            // Every kind of type a declaration can be is emitted; a symbol
            // with no kind at all is a namespace or a type parameter, which
            // no `TypeDef` stands for.
            let Some(type_kind) = detail.type_kind() else {
                continue;
            };
            let interface = type_kind == TypeKind::Interface;

            let token = Token::new(table::TYPE_DEF, next_type);
            next_type += 1;
            self.types.insert(symbol, token);

            if type_kind == TypeKind::Enum {
                plans.push(self.plan_enum(symbol, token, &mut next_field)?);
                continue;
            }
            if type_kind == TypeKind::Delegate {
                plans.push(self.plan_delegate(symbol, token, &mut next_method)?);
                continue;
            }

            let mut fields = Vec::new();
            let mut methods = Vec::new();
            let mut properties = Vec::new();
            let mut has_constructor = false;
            let mut has_static_initializer = false;
            let mut declared_static_constructor = false;
            // Members whose lambdas might need somewhere to keep a capture.
            let mut capturing: Vec<SymbolId> = Vec::new();
            // The structs behind the type's `fixed` buffers, nested in it,
            // by the buffer field each is for.
            let mut buffers: Vec<(SymbolId, TypePlan)> = Vec::new();

            for member in self.members_in_emitted_order(symbol) {
                let detail = symbols.get(member);
                match detail.kind {
                    // `event EventHandler E;` in an interface is two abstract
                    // accessors and an `Event` row: an interface has no
                    // instance storage to keep a delegate in.
                    SymbolKind::Event
                        if interface
                            && !detail.modifiers.contains(Modifiers::STATIC)
                            && self.is_field_like_event(member) =>
                    {
                        methods.extend(self.plan_event_accessors(member, &mut next_method));
                    }
                    // An event with `add` and `remove` blocks is its two
                    // accessors and an `Event` row, and no field — in an
                    // interface as anywhere else.
                    SymbolKind::Event if !self.is_field_like_event(member) => {
                        methods.extend(self.plan_declared_event(member, &mut next_method));
                        let accessors: Vec<SymbolId> = symbols
                            .get(member)
                            .as_event()
                            .map(|detail| detail.adder.into_iter().chain(detail.remover).collect())
                            .unwrap_or_default();
                        for accessor in accessors {
                            methods.extend(self.plan_lambdas(accessor, &mut next_method)?);
                            methods.extend(self.plan_local_functions(accessor, &mut next_method)?);
                            capturing.push(accessor);
                        }
                    }
                    // A field-like event is a field of its delegate type, with
                    // the accessors the language adds around it planned below
                    // it: within its type it is read and written as the field.
                    SymbolKind::Field | SymbolKind::Event => {
                        let token = Token::new(table::FIELD, next_field);
                        next_field += 1;
                        self.fields.insert(member, token);
                        let is_static = detail.modifiers.contains(Modifiers::STATIC)
                            || detail.modifiers.contains(Modifiers::CONST);
                        // A `decimal` has no literal form in metadata,
                        // whatever its value folded to.
                        let constant = self.binder.constant_value(member).filter(|_| {
                            self.special_type_of(&self.type_of(member))
                                != Some(SpecialType::Decimal)
                        });
                        // The field behind a field-like event is private, as
                        // Roslyn makes it: only the declaring type and the
                        // types inside it use the event as its field, and
                        // `x.E += h` anywhere else calls `add_E`. A public
                        // one was a delegate field every serializer that
                        // reads public fields — Odin's, Json.NET's — took.
                        let field_like_event =
                            detail.kind == SymbolKind::Event && self.is_field_like_event(member);
                        let mut flags = if field_like_event {
                            field_flags(rustlyn_semantics::Accessibility::Private, is_static)
                        } else {
                            field_flags(detail.accessibility, is_static)
                        };
                        if constant.is_some() {
                            // A `const` has no storage: the value lives in
                            // metadata, so the field is a literal and nothing
                            // has to run to give it its value.
                            flags |= field_attributes::LITERAL | field_attributes::HAS_DEFAULT;
                        } else if (detail.modifiers.contains(Modifiers::READONLY)
                            || detail.modifiers.contains(Modifiers::CONST))
                            && detail.kind == SymbolKind::Field
                        {
                            // A `const decimal` has no literal form in
                            // metadata either: it is a static field its
                            // class constructor fills, and says what it
                            // holds in a `[DecimalConstant]`.
                            // `readonly` is `initonly`: a reader of the
                            // metadata sees the promise the source made.
                            flags |= field_attributes::INIT_ONLY;
                        }
                        if constant.is_none()
                            && is_static
                            && (detail.as_field().is_some_and(|field| field.has_initializer)
                                || self.event_has_initializer(member))
                        {
                            has_static_initializer = true;
                        }
                        // `fixed byte Buffer[256]` is a field of a struct
                        // made for it, 256 bytes long, holding one `byte`.
                        let sig = if detail.modifiers.contains(Modifiers::FIXED) {
                            let plan = self.plan_fixed_buffer(member, symbol, &mut next_type)?;
                            let sig = SigType::Named {
                                value_type: true,
                                coded: type_def_or_ref(0, plan.token.0 & 0x00FF_FFFF),
                            };
                            buffers.push((member, plan));
                            Some(sig)
                        } else {
                            None
                        };
                        fields.push(FieldPlan {
                            token,
                            name: detail.name.clone(),
                            ty: self.type_of(member),
                            flags,
                            symbol: Some(member),
                            constant,
                            sig,
                        });
                        if field_like_event {
                            methods.extend(self.plan_event_accessors(member, &mut next_method));
                        }
                        // `Func<int, int> f = x => x * 2;` writes a lambda in
                        // an initializer, and that is a method too — planned
                        // under the field, which is the body it was written
                        // in, not under the constructor it ends up running in.
                        methods.extend(self.plan_lambdas(member, &mut next_method)?);
                        methods.extend(self.plan_local_functions(member, &mut next_method)?);
                        // A lambda in the initializer with a lambda inside it
                        // that captures its parameter needs a class for that
                        // parameter, planned with the field's other closures.
                        if self.body_of(member).is_some_and(|body| {
                            !body.lambdas.is_empty() || !body.local_functions.is_empty()
                        }) {
                            capturing.push(member);
                        }
                    }
                    SymbolKind::Property => {
                        // `static int X { get; } = 5;` needs a class
                        // constructor as much as a static field with an
                        // initializer does.
                        if detail.modifiers.contains(Modifiers::STATIC)
                            && self
                                .body_of(member)
                                .is_some_and(|body| !body.statements.is_empty())
                        {
                            has_static_initializer = true;
                        }
                        let plan = self.plan_property(
                            member,
                            &mut next_field,
                            &mut next_method,
                            interface,
                        )?;
                        fields.extend(plan.0);
                        methods.extend(plan.1);
                        properties.push(plan.2);
                        // An accessor body is a body like any other: it may
                        // write a lambda or a local function, and each of
                        // those is a method that needs planning. A `=> e`
                        // property is one body under the property itself; a
                        // `{ get { ... } }` is one body per accessor, and
                        // that is where what is written in it belongs.
                        for owner in std::iter::once(member)
                            .chain(self.accessors_of(member))
                            .collect::<Vec<_>>()
                        {
                            methods.extend(self.plan_lambdas(owner, &mut next_method)?);
                            methods.extend(self.plan_local_functions(owner, &mut next_method)?);
                            capturing.push(owner);
                        }
                    }
                    SymbolKind::Method => {
                        if detail.name == ".ctor" {
                            has_constructor = true;
                        }
                        // A type that writes its own class constructor gets no
                        // second one: the field initializers are emitted into
                        // the one it wrote, ahead of what it wrote.
                        if detail.name == ".cctor" {
                            declared_static_constructor = true;
                        }
                        let token = Token::new(table::METHOD_DEF, next_method);
                        let Some(plan) = self.plan_method(member, token, interface)? else {
                            continue;
                        };
                        next_method += 1;
                        self.methods.insert(member, token);
                        // `async Task Main()` cannot start the runtime, which
                        // wants a `void` or an `int` back: a `<Main>` beside
                        // it calls it and waits on the task, as Roslyn's does.
                        let async_main =
                            if (plan.name == "Main" || plan.name == "<Main>$") && !plan.instance {
                                self.awaited_main_result(&plan.return_type)
                            } else {
                                None
                            };
                        let main_parameters = plan.parameters.clone();
                        methods.push(plan);
                        if let Some(result) = async_main {
                            let token = Token::new(table::METHOD_DEF, next_method);
                            next_method += 1;
                            methods.push(MethodPlan {
                                source: MethodSource::AsyncMain(member),
                                token,
                                name: "<Main>".to_string(),
                                flags: method_attributes::PRIVATE | method_attributes::STATIC,
                                instance: false,
                                return_type: result,
                                parameters: main_parameters,
                                type_parameters: Vec::new(),
                                impl_flags: 0,
                                signature: None,
                            });
                        }
                        // A lambda in the body is a method of its own, and its
                        // row comes right after the method it was written in.
                        methods.extend(self.plan_lambdas(member, &mut next_method)?);
                        methods.extend(self.plan_local_functions(member, &mut next_method)?);
                        capturing.push(member);
                    }
                    _ => {}
                }
            }

            // An editor's build gives the struct its tail, after every
            // field it declares: written into the metadata rather than the
            // source, so the trees are the files as they are.
            if let Some(&references) = self.struct_tails.get(&symbols.qualified_name(symbol))
                && symbols.get(symbol).type_kind() == Some(rustlyn_semantics::TypeKind::Struct)
                && let Some(tail) = self.compilation.type_by_metadata_name(if references {
                    "PilotTail.Tail"
                } else {
                    "PilotTail.ValueTail"
                })
            {
                let token = Token::new(table::FIELD, next_field);
                next_field += 1;
                // Kept out of what Unity writes of an object when it reloads
                // (`[NonSerialized]`); `readonly` where the struct is.
                let mut flags =
                    field_flags(rustlyn_semantics::Accessibility::Internal, false) | 0x0080;
                if symbols.get(symbol).modifiers.contains(Modifiers::READONLY) {
                    flags |= field_attributes::INIT_ONLY;
                }
                fields.push(FieldPlan {
                    token,
                    name: "__pilotTail".to_string(),
                    ty: Type::Named {
                        symbol: tail,
                        type_arguments: Vec::new(),
                    },
                    flags,
                    symbol: None,
                    constant: None,
                    sig: None,
                });
            }

            if !interface {
                methods.extend(self.plan_forwarders(symbol, token, &mut next_method));
                methods.extend(self.plan_inherited_forwarders(symbol, token, &mut next_method));
            }

            // An interface has no constructor to synthesise. Neither does a
            // struct: the runtime zeroes a value type, and `new S()` is
            // `initobj` rather than a call.
            if !has_constructor
                && !interface
                && !matches!(type_kind, TypeKind::Struct | TypeKind::RecordStruct)
            {
                let token = Token::new(table::METHOD_DEF, next_method);
                next_method += 1;
                methods.push(MethodPlan {
                    source: MethodSource::DefaultConstructor,
                    token,
                    name: ".ctor".to_string(),
                    flags: method_attributes::PUBLIC
                        | method_attributes::SPECIAL_NAME
                        | method_attributes::RT_SPECIAL_NAME,
                    instance: true,
                    return_type: Type::Void,
                    parameters: Vec::new(),
                    type_parameters: Vec::new(),
                    impl_flags: 0,
                    signature: None,
                });
            }
            // A record derived from another overrides the base's
            // `Equals(Base)`, so that comparing through the base still
            // compares as the derived record does.
            if let Some(base) = self.record_base(symbol) {
                let token = Token::new(table::METHOD_DEF, next_method);
                next_method += 1;
                let boolean = self
                    .compilation
                    .special_type(SpecialType::Boolean)
                    .map_or(Type::Error, Type::named);
                methods.push(MethodPlan {
                    source: MethodSource::RecordBaseEquals,
                    token,
                    name: "Equals".to_string(),
                    flags: method_attributes::PUBLIC
                        | method_attributes::VIRTUAL
                        | method_attributes::FINAL
                        | method_attributes::HIDE_BY_SIG,
                    instance: true,
                    return_type: boolean,
                    parameters: vec![ParameterPlan {
                        symbol: None,
                        name: "other".to_string(),
                        ty: base,
                        by_ref: false,
                    }],
                    type_parameters: Vec::new(),
                    impl_flags: 0,
                    signature: None,
                });
            }
            if has_static_initializer && !declared_static_constructor {
                let token = Token::new(table::METHOD_DEF, next_method);
                next_method += 1;
                methods.push(MethodPlan {
                    source: MethodSource::StaticConstructor,
                    token,
                    name: ".cctor".to_string(),
                    flags: method_attributes::PRIVATE
                        | method_attributes::STATIC
                        | method_attributes::SPECIAL_NAME
                        | method_attributes::RT_SPECIAL_NAME,
                    instance: false,
                    return_type: Type::Void,
                    parameters: Vec::new(),
                    type_parameters: Vec::new(),
                    impl_flags: 0,
                    signature: None,
                });
            }

            plans.push(TypePlan {
                symbol,
                token,
                fields,
                methods,
                properties,
                display: None,
                iterator: None,
                machine: None,
                nested: None,
            });
            // Their type tokens were handed out while the fields were
            // planned, right after the type's own; their one field each comes
            // after all of the type's fields, which a `FieldList` needs
            // contiguous.
            for (field, mut plan) in buffers {
                let element_field = Token::new(table::FIELD, next_field);
                next_field += 1;
                plan.fields[0].token = element_field;
                self.fixed_buffers
                    .insert(field, (element_field, plan.fields[0].ty.clone()));
                plans.push(plan);
            }

            // A display class is nested in the type whose member made it, and
            // its rows come after that type's, which is the order its token
            // was handed out in.
            for (counter, member) in capturing.into_iter().enumerate() {
                // A member with a `yield` in it becomes a class of its own,
                // nested in the same place a display class would be — and it
                // is the display class for the lambdas written in it.
                if let Some(element) = self.iterated_element(MachineKey::Member(member))
                    && self.iterator_refusal(MachineKey::Member(member)).is_none()
                    && let Some(plan) = self.plan_iterator(
                        MachineKey::Member(member),
                        symbol,
                        element,
                        &mut next_type,
                        &mut next_field,
                        &mut next_method,
                    )?
                {
                    plans.push(plan);
                }
                // And so does an `async` member: its `await`s make it a class
                // driven by a builder.
                if self.is_async_method(member)
                    && self.async_refusal(MachineKey::Member(member)).is_none()
                    && let Some(plan) = self.plan_async(
                        MachineKey::Member(member),
                        symbol,
                        &mut next_type,
                        &mut next_field,
                        &mut next_method,
                    )?
                {
                    plans.push(plan);
                }
                if let Some(plan) = self.plan_display_class(
                    member,
                    symbol,
                    counter,
                    &mut next_type,
                    &mut next_field,
                    &mut next_method,
                )? {
                    plans.push(plan);
                }
                // A lambda whose variables a closure inside it captures gets
                // a display class of its own, nested beside the member's.
                for outer in self.nested_display_owners(member) {
                    let counters = (next_type, next_field, next_method);
                    match self.plan_nested_display(
                        member,
                        outer,
                        symbol,
                        &mut next_type,
                        &mut next_field,
                        &mut next_method,
                    ) {
                        Ok(Some(plan)) => plans.push(plan),
                        Ok(None) => {}
                        // A survey leaves out a class it cannot make, with
                        // the rows it had counted on; the closures that
                        // needed it come out as throwing stubs.
                        Err(error) if self.lenient => {
                            (next_type, next_field, next_method) = counters;
                            let owner = symbols.qualified_name(member);
                            self.skipped
                                .push((format!("{owner} (closure class)"), error.message));
                        }
                        Err(error) => return Err(error),
                    }
                }
                self.name_scope_fields(member, &mut plans);
                // An `async` lambda or local function of the member is a
                // machine of its own, made by the method the closure became;
                // so is a local function with a `yield` in it.
                let closures: Vec<MachineKey> = self
                    .iterator_closures
                    .iter()
                    .copied()
                    .filter(|key| key.owner() == member)
                    .collect();
                for key in closures {
                    if let Some(element) = self.iterated_element(key)
                        && let Some(plan) = self.plan_iterator(
                            key,
                            symbol,
                            element,
                            &mut next_type,
                            &mut next_field,
                            &mut next_method,
                        )?
                    {
                        plans.push(plan);
                    }
                }
                let closures: Vec<MachineKey> = self
                    .async_closures
                    .iter()
                    .copied()
                    .filter(|key| key.owner() == member)
                    .collect();
                for key in closures {
                    if let Some(plan) = self.plan_async(
                        key,
                        symbol,
                        &mut next_type,
                        &mut next_field,
                        &mut next_method,
                    )? {
                        plans.push(plan);
                    }
                }
            }
            // The lambdas of the type that capture nothing share its `<>c`,
            // nested after everything else the type's members made.
            let shared = std::mem::take(&mut self.singleton_candidates);
            if let Some(plan) = self.plan_singleton(
                symbol,
                shared,
                &mut next_type,
                &mut next_field,
                &mut next_method,
            )? {
                plans.push(plan);
            }
        }

        // The delegate types the bodies needed synthesized (§10.7.3 of C#
        // 10): once every body has been bound the list is complete, and the
        // indexed names can be handed out in source order.
        self.finish_binding();
        for (symbol, name) in self.compilation.anonymous_delegates() {
            let token = Token::new(table::TYPE_DEF, next_type);
            next_type += 1;
            self.types.insert(symbol, token);
            self.defining.insert(symbol);
            let arity = symbols
                .get(symbol)
                .as_named_type()
                .map_or(0, |detail| detail.arity);
            let name = if arity > 0 {
                format!("{name}`{arity}")
            } else {
                name
            };
            self.synthesized_names.insert(symbol, name);
            plans.push(self.plan_delegate(symbol, token, &mut next_method)?);
        }

        if plans.is_empty() {
            return Err(EmitError::new("the compilation declares no types to emit"));
        }
        // Whatever a body makes as it is emitted comes after these.
        self.next_type = next_type;
        self.next_field = next_field;
        self.next_method = next_method;
        // Every type has a token now, which is what naming the members of a
        // display class inside a generic one was waiting for.
        self.restate_iterator_signatures(&mut plans)?;
        self.resolve_display_members()?;
        self.resolve_singleton_members()?;
        self.resolve_iterator_members()?;
        self.resolve_async_members()?;
        Ok(plans)
    }

    /// An enum is a value type with one instance field for the storage and one
    /// literal field per member.
    ///
    /// The storage field's name is fixed: the runtime looks for `value__`, and
    /// an enum without it does not load.
    /// A delegate, which has no IL at all.
    ///
    /// Its constructor takes a target and a function pointer and its `Invoke`
    /// is the signature the source wrote — and the runtime writes both bodies,
    /// which is what `MethodImplAttributes.Runtime` says. Emitting IL for
    /// either would be wrong rather than merely unnecessary.
    fn plan_delegate(
        &mut self,
        symbol: SymbolId,
        token: Token,
        next_method: &mut u32,
    ) -> Result<TypePlan, EmitError> {
        let symbols = self.compilation.symbols();
        let invoke = symbols
            .lookup(symbol, "Invoke")
            .first()
            .copied()
            .ok_or_else(|| EmitError::new("a delegate with no `Invoke`"))?;
        let parameters = symbols
            .get(invoke)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        let return_type = self.type_of(invoke);

        let runtime = method_attributes::PUBLIC | method_attributes::HIDE_BY_SIG;
        let mut methods = Vec::new();

        // `.ctor(object target, native int method)`, which no source writes.
        let constructor = Token::new(table::METHOD_DEF, *next_method);
        *next_method += 1;
        self.constructors.insert(symbol, constructor);
        methods.push(MethodPlan {
            source: MethodSource::DefaultConstructor,
            token: constructor,
            name: ".ctor".to_string(),
            flags: runtime | method_attributes::SPECIAL_NAME | method_attributes::RT_SPECIAL_NAME,
            instance: true,
            return_type: Type::Void,
            parameters: vec![
                ParameterPlan {
                    by_ref: false,
                    symbol: None,
                    name: "object".to_string(),
                    ty: Type::Void,
                },
                ParameterPlan {
                    by_ref: false,
                    symbol: None,
                    name: "method".to_string(),
                    ty: Type::Void,
                },
            ],
            type_parameters: Vec::new(),
            impl_flags: method_impl::RUNTIME,
            signature: Some(delegate_constructor_signature()),
        });

        let invoke_token = Token::new(table::METHOD_DEF, *next_method);
        *next_method += 1;
        self.methods.insert(invoke, invoke_token);
        methods.push(MethodPlan {
            source: MethodSource::Declared(invoke),
            token: invoke_token,
            name: "Invoke".to_string(),
            flags: runtime | method_attributes::VIRTUAL | method_attributes::NEW_SLOT,
            instance: true,
            return_type,
            parameters: parameters
                .into_iter()
                .map(|parameter| ParameterPlan {
                    by_ref: false,
                    symbol: Some(parameter),
                    name: symbols.get(parameter).name.clone(),
                    ty: self.type_of(parameter),
                })
                .collect(),
            type_parameters: Vec::new(),
            impl_flags: method_impl::RUNTIME,
            signature: None,
        });

        // `BeginInvoke` and `EndInvoke`, which every delegate `csc` writes
        // has, and which reflection lists: the arguments and a callback and
        // state, and the `ref` and `out` ones and the `IAsyncResult`.
        let named = |name: &str| {
            self.compilation
                .type_by_metadata_name(name)
                .map(Type::named)
        };
        if let (Some(callback), Some(result), Some(object)) = (
            named("System.AsyncCallback"),
            named("System.IAsyncResult"),
            named("System.Object"),
        ) {
            let symbols = self.compilation.symbols();
            let parameters = symbols
                .get(invoke)
                .as_method()
                .map(|detail| detail.parameters.clone())
                .unwrap_or_default();
            let plan_of = |this: &Self, parameter: SymbolId| ParameterPlan {
                by_ref: this.is_by_reference(Some(parameter)),
                symbol: None,
                name: symbols.get(parameter).name.clone(),
                ty: this.type_of(parameter),
            };
            let mut begin: Vec<ParameterPlan> = parameters
                .iter()
                .map(|parameter| plan_of(self, *parameter))
                .collect();
            begin.push(ParameterPlan {
                by_ref: false,
                symbol: None,
                name: "callback".to_string(),
                ty: callback,
            });
            begin.push(ParameterPlan {
                by_ref: false,
                symbol: None,
                name: "object".to_string(),
                ty: object,
            });
            let mut end: Vec<ParameterPlan> = parameters
                .iter()
                .filter(|parameter| self.is_by_reference(Some(**parameter)))
                .map(|parameter| plan_of(self, *parameter))
                .collect();
            end.push(ParameterPlan {
                by_ref: false,
                symbol: None,
                name: "result".to_string(),
                ty: result.clone(),
            });
            let return_type = self.type_of(invoke);
            let by_reference: Vec<SymbolId> = parameters
                .iter()
                .copied()
                .filter(|parameter| self.is_by_reference(Some(*parameter)))
                .collect();
            for (name, parameters, returns, originals) in [
                ("BeginInvoke", begin, result, parameters.clone()),
                ("EndInvoke", end, return_type, by_reference),
            ] {
                let token = Token::new(table::METHOD_DEF, *next_method);
                *next_method += 1;
                self.cloned_parameters.insert(token, originals);
                methods.push(MethodPlan {
                    source: MethodSource::DefaultConstructor,
                    token,
                    name: name.to_string(),
                    flags: runtime | method_attributes::VIRTUAL | method_attributes::NEW_SLOT,
                    instance: true,
                    return_type: returns,
                    parameters,
                    type_parameters: Vec::new(),
                    impl_flags: method_impl::RUNTIME,
                    signature: None,
                });
            }
        }

        Ok(TypePlan {
            symbol,
            token,
            fields: Vec::new(),
            methods,
            properties: Vec::new(),
            display: None,
            iterator: None,
            machine: None,
            nested: None,
        })
    }

    /// One method per lambda in a member's body that captures nothing.
    ///
    /// The CLI has no lambdas: what a delegate points at is an ordinary
    /// method, with an unspeakable name so that nothing in C# can collide
    /// with it. A lambda that captures nothing is static; one that reads only
    /// `this` is an instance method of the same type, which is what `ldftn`
    /// over `this` then makes a delegate of. One that captures a variable
    /// needs somewhere for that variable to live, and is left to
    /// [`Self::plan_display_class`].
    /// Plans the local functions written inside a member.
    ///
    /// A local function is a method of the type in metadata, with a name no
    /// C# identifier can collide with, because the CLI has nothing smaller
    /// than a method and nowhere to put one but a type. One that reads
    /// anything of the method around it is not planned here at all: it
    /// becomes a method of that method's display class, where what it reads
    /// lives.
    fn plan_local_functions(
        &mut self,
        owner: SymbolId,
        next_method: &mut u32,
    ) -> Result<Vec<MethodPlan>, EmitError> {
        let Some(body) = self.body_of(owner) else {
            return Ok(Vec::new());
        };
        if body.local_functions.is_empty() {
            return Ok(Vec::new());
        }
        // With a display class or a machine the local functions live there;
        // an `extern` one has no body to move and stays a static method of
        // the type.
        let hosted_elsewhere = self.needs_display(owner, &body) || self.becomes_machine(owner);
        let symbols = self.compilation.symbols();
        let owner_name = symbols.get(owner).name.clone();
        // A local function written in a generic method is a method of the
        // type, where the method's parameters mean nothing: it declares them
        // itself, and every call names them.
        let owner_generics = self.enclosing_method_generics(owner);
        // An instance local function can reach `this`; a `static` one cannot.
        let owner_instance = !symbols.get(owner).modifiers.contains(Modifiers::STATIC);
        let spans: Vec<Option<TextSpan>> = body
            .local_functions
            .iter()
            .map(|function| self.function_span(function))
            .collect();
        let mut plans = Vec::new();
        for (index, function) in body.local_functions.iter().enumerate() {
            if hosted_elsewhere && self.dll_import(function.symbol).is_none() {
                continue;
            }
            // A local function inside a generic local function can name that
            // one's parameters too, and declares them after the method's.
            let mut inherited = owner_generics.clone();
            let mut enclosing: Vec<(TextSpan, usize)> = spans
                .iter()
                .enumerate()
                .filter_map(|(other, span)| {
                    let (span, own) = ((*span)?, spans[index]?);
                    (other != index
                        && span.start() <= own.start()
                        && own.end() <= span.end()
                        && span != own)
                        .then_some((span, other))
                })
                .collect();
            enclosing.sort_by_key(|(span, _)| std::cmp::Reverse(span.length()));
            for (_, other) in enclosing {
                inherited.extend(
                    self.compilation
                        .symbols()
                        .get(body.local_functions[other].symbol)
                        .as_method()
                        .map(|detail| detail.type_parameters.clone())
                        .unwrap_or_default(),
                );
            }
            // An instance local function is one written in an instance method
            // without `static`: whether it *reads* `this` is not the question,
            // because the call site passes it either way.
            let instance = owner_instance
                && !self
                    .compilation
                    .symbols()
                    .get(function.symbol)
                    .modifiers
                    .contains(Modifiers::STATIC);
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.methods.insert(function.symbol, token);
            if !inherited.is_empty() {
                self.inherited_generics.insert(token, inherited.clone());
            }
            let mut plan = self.plan_local_function(
                owner,
                index,
                function,
                token,
                instance,
                None,
                &owner_name,
            )?;
            let mut all = inherited.clone();
            all.extend(plan.type_parameters.iter().copied());
            plan.type_parameters = all;
            plans.push(plan);
        }
        Ok(plans)
    }

    /// The plan for one local function, wherever it ends up living.
    #[allow(clippy::too_many_arguments)]
    fn plan_local_function(
        &mut self,
        owner: SymbolId,
        index: usize,
        function: &rustlyn_semantics::BoundLocalFunction,
        token: Token,
        instance: bool,
        hosted: Option<SigType>,
        owner_name: &str,
    ) -> Result<MethodPlan, EmitError> {
        let symbols = self.compilation.symbols();
        let detail = symbols
            .get(function.symbol)
            .as_method()
            .ok_or_else(|| EmitError::new("a local function without method detail"))?;
        let parameters = detail.parameters.clone();
        let type_parameters = detail.type_parameters.clone();
        let name = match self.body_of(owner) {
            Some(body) => self.local_function_name(&body, owner, index, hosted.is_some()),
            None => format!("<{owner_name}>g__{}", symbols.get(function.symbol).name),
        };
        self.emitted_names.insert(function.symbol, name.clone());
        let key = MachineKey::Function { owner, index };
        // An `extern` local function is a static method of the type with an
        // unmanaged body, whatever else the member's closures became.
        let import = self.dll_import(function.symbol);
        let instance = instance && import.is_none();
        let mut impl_flags = 0;
        let mut flags = method_attributes::PRIVATE
            | method_attributes::HIDE_BY_SIG
            | if instance {
                0
            } else {
                method_attributes::STATIC
            };
        if let Some(import) = import {
            flags |= method_attributes::PINVOKE_IMPL;
            impl_flags |= method_impl::PRESERVE_SIG;
            self.note_pinvoke(token, import);
        }
        let source = self.closure_source(key, instance, hosted);
        Ok(MethodPlan {
            source,
            token,
            name,
            flags,
            instance,
            return_type: self.type_of(function.symbol),
            parameters: parameters
                .into_iter()
                .map(|symbol| ParameterPlan {
                    by_ref: false,
                    symbol: Some(symbol),
                    name: self.compilation.symbols().get(symbol).name.clone(),
                    ty: self.type_of(symbol),
                })
                .collect(),
            type_parameters,
            impl_flags,
            signature: None,
        })
    }

    /// The primitive a constant of `ty` is stored as: the type itself, an
    /// enum's underlying type, or what is inside a nullable.
    fn constant_width(&self, ty: &Type) -> Option<SpecialType> {
        let ty = self.nullable_underlying(ty).unwrap_or_else(|| ty.clone());
        let ty = match ty.symbol() {
            Some(symbol)
                if self.compilation.symbols().get(symbol).type_kind() == Some(TypeKind::Enum) =>
            {
                self.enum_underlying(symbol)
            }
            _ => ty,
        };
        self.special_type_of(&ty)
    }

    /// What a method's `Param` rows say beyond the name: `out`, and for an
    /// optional parameter its default, which is what a caller in another
    /// assembly — or reflection asking `HasDefaultValue` — reads.
    fn write_parameter_rows(
        &mut self,
        method: Token,
        parameters: &[ParameterPlan],
        nullable: Option<&crate::nullable::NullableShape>,
    ) -> Result<(), EmitError> {
        for (index, parameter) in parameters.iter().enumerate() {
            // A setter's `value` has no symbol, and its property's type.
            if parameter.symbol.is_none()
                && let Some(shape) = nullable
                && let Some(flags) = shape.parameters.get(index)
            {
                let param = self.metadata.param_token(method, index);
                self.mark_nullable(((param.0 & 0x00FF_FFFF) << 5) | 4, flags, shape.effective);
            }
            let Some(symbol) = parameter.symbol else {
                continue;
            };
            let symbols = self.compilation.symbols();
            let Some(detail) = symbols.get(symbol).as_parameter() else {
                continue;
            };
            // `[Optional]` alone makes a parameter optional with no value
            // of its own; `= value` and `[DefaultParameterValue(value)]`
            // give it one.
            let optional = detail.has_default;
            // A `decimal` or `DateTime` default is no constant metadata can
            // hold: it goes in a `[DecimalConstant]` or `[DateTimeConstant]`
            // instead (the latter only ever written by hand).
            let special = if optional {
                self.binder.special_constant(symbol)
            } else {
                None
            };
            let has_default = optional
                && special.is_none()
                && self.binder.parameter_default_syntax(symbol).is_some();
            let mut flags = self.written_direction(symbol);
            match detail.ref_kind {
                RefKind::Out => flags |= param_attributes::OUT,
                RefKind::In => flags |= param_attributes::IN,
                _ => {}
            }
            if optional {
                flags |= param_attributes::OPTIONAL;
            }
            if has_default {
                flags |= param_attributes::HAS_DEFAULT;
            }
            let param = self.metadata.param_token(method, index);
            let by_ref = detail.ref_kind != RefKind::None;
            // A `HasCustomAttribute` parent tagged 4 is a `Param`. What the
            // language says of a parameter comes before what the source
            // wrote, in Roslyn's order.
            let parent = ((param.0 & 0x00FF_FFFF) << 5) | 4;
            if detail.is_params {
                self.mark_with(parent, params_attribute(&parameter.ty));
            }
            if let Some(value @ SpecialConstant::Decimal { .. }) = special
                && self.attribute_on(symbol, "DecimalConstant").is_none()
            {
                self.mark_special_constant(parent, value);
            }
            self.mark_dynamic(parent, &parameter.ty, by_ref);
            self.mark_tuple_names(parent, &parameter.ty);
            // `in` is a `ref` marked read-only, which is how another
            // compiler tells it apart; `ref readonly` says so with an
            // attribute of its own.
            if detail.ref_readonly {
                self.mark_with(
                    parent,
                    "System.Runtime.CompilerServices.RequiresLocationAttribute",
                );
            } else if detail.ref_kind == RefKind::In {
                self.mark_with(
                    parent,
                    "System.Runtime.CompilerServices.IsReadOnlyAttribute",
                );
            }
            if let Some(shape) = nullable
                && let Some(flags) = shape.parameters.get(index)
            {
                self.mark_nullable(parent, flags, shape.effective);
            }
            self.write_custom_attributes(parent, symbol, AttributeTarget::Parameter)?;
            if flags == 0 {
                continue;
            }
            self.metadata.set_param_flags(param, flags);
            if has_default {
                // A default that is no constant — `default(CancellationToken)`
                // — is recorded as a null, which is what csc writes for it.
                let special = self.constant_width(&parameter.ty);
                let (element, value) = match self.binder.parameter_default(symbol) {
                    Some(constant) => encode_constant_as(&constant, special),
                    None => encode_constant(&ConstantValue::Null),
                };
                self.metadata.add_param_constant(param, element, &value);
            }
        }
        Ok(())
    }

    /// The `In` and `Out` flags `[In]` and `[Out]` written on a parameter
    /// set, and `Optional` for `[Optional]`, bound to be sure of what they
    /// name.
    fn written_parameter_flags(&mut self, parameter: SymbolId) -> u16 {
        let mut flags = 0;
        for (tree, span) in self.compilation.declaration_nodes(parameter).to_vec() {
            let Some(node) = self
                .compilation
                .trees()
                .get(tree)
                .and_then(|tree| tree.root().find_node(span))
            else {
                continue;
            };
            for attribute in attributes_for(&node, AttributeTarget::Parameter) {
                let Some(ty) = self
                    .binder
                    .bind_attribute(tree, &node, &attribute)
                    .and_then(|bound| bound.ty.symbol())
                else {
                    continue;
                };
                flags |= match self.compilation.symbols().qualified_name(ty).as_str() {
                    "System.Runtime.InteropServices.InAttribute" => param_attributes::IN,
                    "System.Runtime.InteropServices.OutAttribute" => param_attributes::OUT,
                    "System.Runtime.InteropServices.OptionalAttribute" => {
                        param_attributes::OPTIONAL
                    }
                    _ => 0,
                };
            }
        }
        flags
    }

    /// What `[In]` and `[Out]` on a parameter set (Roslyn's `IsMetadataIn`
    /// and `IsMetadataOut` add them to what `in` and `out` do).
    fn written_direction(&mut self, parameter: SymbolId) -> u16 {
        self.written_parameter_flags(parameter) & (param_attributes::IN | param_attributes::OUT)
    }

    /// `BeginInvoke`'s and `EndInvoke`'s parameters are `Invoke`'s cloned
    /// (Roslyn's `SourceDelegateClonedParameterSymbolForBeginAndEndInvoke`):
    /// the original's attributes, `[In]`, `[Out]` and marshalling, but only
    /// `[Optional]` makes one optional, only `[DefaultParameterValue]` gives
    /// it a default, and none is `params`.
    fn write_cloned_parameter_rows(
        &mut self,
        method: Token,
        originals: &[SymbolId],
    ) -> Result<(), EmitError> {
        for (index, &symbol) in originals.iter().enumerate() {
            let Some(ref_kind) = self
                .compilation
                .symbols()
                .get(symbol)
                .as_parameter()
                .map(|detail| detail.ref_kind)
            else {
                continue;
            };
            let mut flags = self.written_parameter_flags(symbol);
            match ref_kind {
                RefKind::Out => flags |= param_attributes::OUT,
                RefKind::In => flags |= param_attributes::IN,
                _ => {}
            }
            let attributed =
                self.binder
                    .parameter_default_syntax(symbol)
                    .is_some_and(|(_, node, _)| {
                        node.child_of_kind(SyntaxKind::EqualsValueClause).is_none()
                    });
            if attributed {
                flags |= param_attributes::HAS_DEFAULT;
            }
            let ty = self.type_of(symbol);
            let param = self.metadata.param_token(method, index);
            let parent = ((param.0 & 0x00FF_FFFF) << 5) | 4;
            self.mark_dynamic(parent, &ty, ref_kind != RefKind::None);
            self.mark_tuple_names(parent, &ty);
            self.write_custom_attributes(parent, symbol, AttributeTarget::Parameter)?;
            if flags == 0 {
                continue;
            }
            self.metadata.set_param_flags(param, flags);
            if attributed {
                let width = self.constant_width(&ty);
                let (element, value) = match self.binder.parameter_default(symbol) {
                    Some(constant) => encode_constant_as(&constant, width),
                    None => encode_constant(&ConstantValue::Null),
                };
                self.metadata.add_param_constant(param, element, &value);
            }
        }
        Ok(())
    }

    /// A type's members in the order their rows are written.
    ///
    /// Roslyn sorts a type's members by where they are written. The members
    /// a record gets from the language have no place of their own and sort
    /// after all that do, the last made first — except `EqualityContract`,
    /// which stands at the record's name, ahead of its positional members.
    fn members_in_emitted_order(&self, ty: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let members = symbols.get(ty).members.clone();
        if !matches!(
            symbols.get(ty).type_kind(),
            Some(TypeKind::Record | TypeKind::RecordStruct)
        ) {
            return members;
        }
        let language = |member: &SymbolId| {
            symbols.get(*member).as_method().is_some_and(|detail| {
                detail.method_kind == rustlyn_semantics::MethodKind::RecordSynthesized
                    || (symbols.get(*member).name == ".ctor"
                        && detail.parameters.len() == 1
                        && symbols
                            .get(detail.parameters[0])
                            .as_parameter()
                            .is_some_and(|parameter| {
                                parameter.synthesized
                                    == Some(rustlyn_semantics::SynthesizedType::Containing)
                            }))
            })
        };
        let contract = |member: &SymbolId| {
            symbols.get(*member).as_property().is_some_and(|detail| {
                detail.synthesized == Some(rustlyn_semantics::SynthesizedType::SystemType)
            })
        };
        let (made, written): (Vec<SymbolId>, Vec<SymbolId>) =
            members.into_iter().partition(|member| language(member));
        let (contracts, mut written): (Vec<SymbolId>, Vec<SymbolId>) =
            written.into_iter().partition(|member| contract(member));
        // After the constructor the parameter list declares, where there
        // is one.
        let at = written
            .iter()
            .position(|member| {
                symbols.get(*member).name == ".ctor"
                    && symbols
                        .get(*member)
                        .as_method()
                        .is_some_and(|detail| !detail.parameters.is_empty())
                    && self.is_record_constructor(*member)
            })
            .map_or(0, |at| at + 1);
        for (offset, contract) in contracts.into_iter().enumerate() {
            written.insert(at + offset, contract);
        }
        written.extend(made.into_iter().rev());
        written
    }

    /// The attributes of a type's own row, in the order Roslyn writes them:
    /// what its base names that metadata cannot say, its nullable context,
    /// `[Extension]` for a class of extension methods, `[IsByRefLike]` for
    /// a `ref struct` with the markers that keep an older compiler off it,
    /// `[IsReadOnly]` for a `readonly struct`, `[DefaultMember]` for a type
    /// with an indexer, `[RequiredMember]` for one with `required` members,
    /// and then what the source wrote.
    fn write_type_attributes(&mut self, plan: &TypePlan, token: Token) -> Result<(), EmitError> {
        // A `HasCustomAttribute` parent tagged 3 is a `TypeDef`.
        let parent = ((token.0 & 0x00FF_FFFF) << 5) | 3;
        let ty = plan.symbol;
        // An anonymous type or delegate is the language's, and says only
        // that.
        if self.is_synthesized_type(ty) {
            self.mark_compiler_generated(token);
            return Ok(());
        }
        if let Some(base) = self.base_class_type(ty) {
            self.mark_dynamic(parent, &base, false);
            self.mark_tuple_names(parent, &base);
        }
        if self.nullable_on {
            self.mark_type_nullable(ty, parent);
        }
        let has_extensions = plan.methods.iter().any(|method| {
            method
                .source
                .written_member()
                .is_some_and(|symbol| self.is_extension_method(symbol))
        });
        if has_extensions {
            self.mark_extension(parent);
        }
        // Nothing in the flags says `ref struct`: the runtime reads
        // `IsByRefLikeAttribute` and refuses a type holding a `Span<T>` in a
        // field without it. A compiler from before C# 7.2 would not know to
        // keep one on the stack, and is kept away by an error.
        let symbols = self.compilation.symbols();
        let ref_like = symbols
            .get(ty)
            .as_named_type()
            .is_some_and(|detail| detail.ref_like);
        if ref_like {
            self.mark_by_ref_like(token);
            if self.attribute_on(ty, "Obsolete").is_none() {
                self.mark_obsolete_error(
                    parent,
                    "Types with embedded references are not supported in this version of your compiler.",
                );
            }
            self.mark_compiler_feature_required(parent, "RefStructs");
        }
        // `readonly struct` is an attribute too, which is how another
        // assembly learns that calling a member cannot change the value.
        let symbol = self.compilation.symbols().get(ty);
        if symbol.modifiers.contains(Modifiers::READONLY)
            && matches!(
                symbol.type_kind(),
                Some(TypeKind::Struct | TypeKind::RecordStruct)
            )
        {
            self.mark_with(
                parent,
                "System.Runtime.CompilerServices.IsReadOnlyAttribute",
            );
        }
        // A type with an indexer says which of its properties that is with
        // `[DefaultMember("Item")]`: reflection, the runtime binder and
        // another compiler all find it that way.
        let indexer = plan.properties.iter().find(|property| {
            property.symbol.is_some_and(|symbol| {
                self.compilation
                    .symbols()
                    .get(symbol)
                    .as_property()
                    .is_some_and(|detail| detail.is_indexer)
            })
        });
        if let Some(indexer) = indexer
            && self.attribute_on(ty, "DefaultMember").is_none()
        {
            let name = indexer.name.clone();
            self.mark_default_member(parent, &name);
        }
        if self.declares_required_members(ty) {
            self.mark_with(
                parent,
                "System.Runtime.CompilerServices.RequiredMemberAttribute",
            );
        }
        self.write_custom_attributes(parent, ty, AttributeTarget::Type)
    }

    /// `[CompilerGenerated]` on a type the language made: a closure's
    /// class, a state machine, a class of call sites.
    pub(crate) fn mark_compiler_generated(&mut self, token: Token) {
        // A `HasCustomAttribute` parent tagged 3 is a `TypeDef`.
        self.mark_with(
            ((token.0 & 0x00FF_FFFF) << 5) | 3,
            "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
        );
    }

    /// Whether a type is one the language made for `new { ... }`.
    pub(crate) fn is_anonymous_type(&self, ty: SymbolId) -> bool {
        self.compilation
            .symbols()
            .get(ty)
            .as_named_type()
            .is_some_and(|detail| detail.anonymous)
    }

    /// Whether a type is one the language made for an anonymous object or
    /// for a lambda with no delegate type to go to.
    pub(crate) fn is_synthesized_type(&self, ty: SymbolId) -> bool {
        self.synthesized_names.contains_key(&ty)
            || self
                .compilation
                .symbols()
                .get(ty)
                .as_named_type()
                .is_some_and(|detail| detail.anonymous)
    }

    /// Whether a type declares a `required` field or property of its own.
    fn declares_required_members(&self, ty: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        symbols.get(ty).members.iter().any(|member| {
            matches!(
                symbols.get(*member).kind,
                SymbolKind::Field | SymbolKind::Property
            ) && symbols.get(*member).modifiers.contains(Modifiers::REQUIRED)
        })
    }

    /// Whether a type or any type it derives from declares `required`
    /// members, which every constructor that does not set them all has to
    /// be kept from an older compiler for.
    fn has_any_required_members(&self, ty: SymbolId) -> bool {
        let mut current = Some(ty);
        let mut depth = 0;
        while let Some(ty) = current {
            if self.declares_required_members(ty) {
                return true;
            }
            depth += 1;
            if depth > 64 {
                return false;
            }
            current = self.binder.base_types_of(ty).into_iter().find_map(|base| {
                base.symbol().filter(|symbol| {
                    matches!(
                        self.compilation.symbols().get(*symbol).type_kind(),
                        Some(TypeKind::Class | TypeKind::Record)
                    )
                })
            });
        }
        false
    }

    /// `[Obsolete(message, true)]`: an error to use, which is how a
    /// compiler that does not know a feature is kept from what needs it.
    fn mark_obsolete_error(&mut self, parent: u32, message: &str) {
        let string = SigType::Primitive(ElementType::String);
        let boolean = SigType::Primitive(ElementType::Boolean);
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.ObsoleteAttribute",
            ".ctor",
            &method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[string, boolean],
            ),
        );
        let mut blob = vec![0x01, 0x00];
        ser_string(&mut blob, Some(message));
        blob.push(0x01);
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// `[CompilerFeatureRequired(feature)]`, which a compiler that knows it
    /// reads past and one that does not refuses.
    fn mark_compiler_feature_required(&mut self, parent: u32, feature: &str) {
        const REQUIRED: &str = "System.Runtime.CompilerServices.CompilerFeatureRequiredAttribute";
        if self.compilation.type_by_metadata_name(REQUIRED).is_none() {
            return;
        }
        let string = SigType::Primitive(ElementType::String);
        let constructor = self.references.member_ref(
            &mut self.metadata,
            REQUIRED,
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[string]),
        );
        let mut blob = vec![0x01, 0x00];
        ser_string(&mut blob, Some(feature));
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// The attributes of a method's own row, in the order Roslyn writes
    /// them: `[IsReadOnly]` for a `readonly` member of a struct, its
    /// `[NullableContext]`, the state machine its body became, the marks of
    /// what the language wrote rather than the source, `[Extension]`, and
    /// then what the source wrote.
    fn write_method_attributes(
        &mut self,
        ty: SymbolId,
        method: &MethodPlan,
        token: Token,
        declared_type: bool,
        shape: Option<&crate::nullable::NullableShape>,
    ) -> Result<(), EmitError> {
        // A `HasCustomAttribute` parent tagged 0 is a `MethodDef`.
        let parent = (token.0 & 0x00FF_FFFF) << 5;
        // An anonymous type's members are hidden from the debugger's
        // stepping, its properties' getters left as they are.
        if self.is_anonymous_type(ty) {
            if !matches!(method.source, MethodSource::PropertyGetter { .. }) {
                self.mark_with(parent, "System.Diagnostics.DebuggerHiddenAttribute");
            }
            return Ok(());
        }
        // What a state machine does for the runtime rather than for the
        // body is hidden from the debugger's stepping: all but `MoveNext`.
        if matches!(
            method.source,
            MethodSource::IteratorConstructor(_)
                | MethodSource::IteratorCurrent(..)
                | MethodSource::IteratorGetEnumerator(..)
                | MethodSource::IteratorDispose(_)
                | MethodSource::IteratorReset
                | MethodSource::AsyncSetStateMachine
                | MethodSource::AsyncIteratorConstructor(_)
                | MethodSource::AsyncIteratorGetEnumerator(_)
                | MethodSource::AsyncIteratorMoveNext(_)
                | MethodSource::AsyncIteratorCurrent(_)
                | MethodSource::AsyncIteratorPromise(..)
                | MethodSource::AsyncIteratorDispose(_)
        ) {
            self.mark_with(parent, "System.Diagnostics.DebuggerHiddenAttribute");
        }
        if self.covariant_bodies.contains(&token) {
            self.mark_with(
                parent,
                "System.Runtime.CompilerServices.PreserveBaseOverridesAttribute",
            );
        }
        let written = method.source.written_member();
        if let Some(symbol) = written
            && self
                .compilation
                .symbols()
                .get(symbol)
                .modifiers
                .contains(Modifiers::READONLY)
        {
            self.mark_with(
                parent,
                "System.Runtime.CompilerServices.IsReadOnlyAttribute",
            );
        }
        if let Some(value) = shape.and_then(|shape| shape.context) {
            self.mark_nullable_context(parent, value);
        }
        if let MethodSource::IteratorStart(key) | MethodSource::AsyncStart(key) = method.source {
            self.mark_state_machine(
                parent,
                key,
                matches!(method.source, MethodSource::AsyncStart(_)),
            );
        }
        // What the language writes itself: an automatic property's
        // accessors, a field-like event's, a record's members, and a lambda
        // or a local function that became a method of the program's own
        // type.
        let closure = matches!(
            method.source,
            MethodSource::Lambda { .. }
                | MethodSource::LocalFunction { .. }
                | MethodSource::IteratorStart(
                    MachineKey::Lambda { .. } | MachineKey::Function { .. }
                )
                | MethodSource::AsyncStart(MachineKey::Lambda { .. } | MachineKey::Function { .. })
        );
        let made = (declared_type && closure)
            || matches!(
                method.source,
                MethodSource::PropertyGetter { backing: true, .. }
                    | MethodSource::PropertySetter { .. }
                    | MethodSource::EventAccessor { .. }
                    | MethodSource::RecordMember(_)
                    | MethodSource::RecordBaseEquals
            );
        if made {
            self.mark_with(
                parent,
                "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
            );
        }
        // A constructor of a type with `required` members that does not
        // say it sets them all is kept from a compiler that would not make
        // its callers set them.
        let constructor = match method.source {
            MethodSource::Declared(symbol) | MethodSource::RecordConstructor(symbol) => {
                let symbols = self.compilation.symbols();
                (symbols.get(symbol).name == ".ctor"
                    && !symbols.get(symbol).modifiers.contains(Modifiers::STATIC))
                .then_some(Some(symbol))
            }
            MethodSource::DefaultConstructor
                if declared_type
                    && method.name == ".ctor"
                    && self.compilation.symbols().get(ty).type_kind()
                        != Some(TypeKind::Delegate) =>
            {
                Some(None)
            }
            _ => None,
        };
        if let Some(symbol) = constructor
            && self.has_any_required_members(ty)
            && symbol
                .is_none_or(|symbol| self.attribute_on(symbol, "SetsRequiredMembers").is_none())
        {
            if symbol.is_none_or(|symbol| self.attribute_on(symbol, "Obsolete").is_none()) {
                self.mark_obsolete_error(
                    parent,
                    "Constructors of types with required members are not supported in this version of your compiler.",
                );
            }
            self.mark_compiler_feature_required(parent, "RequiredMembers");
        }
        if let Some(symbol) = written {
            if self.is_extension_method(symbol) {
                self.mark_extension(parent);
            }
            self.write_custom_attributes(parent, symbol, AttributeTarget::Method)?;
        }
        // `[Tag] void Local() { }` says it on the method the function became.
        if let Some(function) = self.local_function_of(&method.source) {
            self.write_custom_attributes(parent, function, AttributeTarget::Method)?;
        }
        if let MethodSource::Lambda { owner, index }
        | MethodSource::AsyncStart(MachineKey::Lambda { owner, index }) = method.source
        {
            self.write_lambda_attributes(token, owner, index)?;
        }
        Ok(())
    }

    /// The local function a method was made from, whether its body stayed
    /// one or started a state machine.
    fn local_function_of(&mut self, source: &MethodSource) -> Option<SymbolId> {
        let (MethodSource::LocalFunction { owner, index }
        | MethodSource::IteratorStart(MachineKey::Function { owner, index })
        | MethodSource::AsyncStart(MachineKey::Function { owner, index })) = *source
        else {
            return None;
        };
        self.body_of(owner).and_then(|body| {
            body.local_functions
                .get(index)
                .map(|function| function.symbol)
        })
    }

    /// `[IteratorStateMachine(typeof(M))]`, `[AsyncStateMachine(...)]` or
    /// `[AsyncIteratorStateMachine(...)]` on the method a machine was made
    /// for, naming the machine as an open type.
    fn mark_state_machine(&mut self, parent: u32, key: MachineKey, asynchronous: bool) {
        let Some(name) = self.machine_type_names.get(&key).cloned() else {
            return;
        };
        let attribute = if !asynchronous {
            "System.Runtime.CompilerServices.IteratorStateMachineAttribute"
        } else if self.asyncs.get(&key).is_some_and(|plan| {
            matches!(plan.kind, crate::async_machine::AsyncKind::Iterator { .. })
        }) {
            "System.Runtime.CompilerServices.AsyncIteratorStateMachineAttribute"
        } else {
            "System.Runtime.CompilerServices.AsyncStateMachineAttribute"
        };
        if self.compilation.type_by_metadata_name(attribute).is_none() {
            return;
        }
        // The machine is nested in the type the method belongs to.
        let Some(enclosing) = self
            .enclosing_type(key.owner())
            .and_then(|ty| self.serialized_type_name(&Type::named(ty)))
        else {
            return;
        };
        let system_type = SigType::Named {
            value_type: false,
            coded: self
                .references
                .type_ref_coded(&mut self.metadata, "System.Type"),
        };
        let constructor = self.references.member_ref(
            &mut self.metadata,
            attribute,
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[system_type]),
        );
        let mut blob = vec![0x01, 0x00];
        ser_string(&mut blob, Some(&format!("{enclosing}+{name}")));
        blob.extend_from_slice(&[0x00, 0x00]);
        // A `CustomAttributeType` tagged 3 is a `MemberRef`.
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// `params` on a lambda's parameter, which has no symbol to say so: the
    /// same attribute a method's gets, read off the syntax.
    fn mark_lambda_params(&mut self, method: Token, owner: SymbolId, index: usize) {
        let Some(body) = self.body_of(owner) else {
            return;
        };
        let Some(lambda) = body.lambdas.get(index) else {
            return;
        };
        let Some(&(tree, _)) = self.compilation.declaration_nodes(owner).first() else {
            return;
        };
        let Some(root) = self.compilation.trees().get(tree).map(|tree| tree.root()) else {
            return;
        };
        for (position, local) in lambda.parameters.iter().enumerate() {
            let local = &body.locals[local.0 as usize];
            let is_params = root
                .find_node(local.span)
                .and_then(|node| {
                    std::iter::once(node.clone())
                        .chain(node.ancestors())
                        .find(|it| it.kind() == SyntaxKind::Parameter)
                })
                .is_some_and(|parameter| {
                    parameter
                        .child_tokens()
                        .any(|token| token.kind() == SyntaxKind::ParamsKeyword)
                });
            if is_params {
                let param = self.metadata.param_token(method, position);
                self.mark_with(
                    ((param.0 & 0x00FF_FFFF) << 5) | 4,
                    params_attribute(&local.ty),
                );
            }
        }
    }

    /// Where a lambda was written: its tree and its syntax.
    pub(crate) fn lambda_node(
        &mut self,
        owner: SymbolId,
        index: usize,
    ) -> Option<(usize, SyntaxNode)> {
        let span = self.body_of(owner)?.lambdas.get(index)?.span;
        let &(tree, _) = self.compilation.declaration_nodes(owner).first()?;
        let node = self
            .compilation
            .trees()
            .get(tree)?
            .root()
            .find_node(span)
            .filter(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::ParenthesizedLambdaExpression | SyntaxKind::SimpleLambdaExpression
                )
            })?;
        Some((tree, node))
    }

    /// The attributes written on a lambda (C# 10) and on its parameters,
    /// which go on the method it became and on that method's `Param` rows.
    fn write_lambda_attributes(
        &mut self,
        method: Token,
        owner: SymbolId,
        index: usize,
    ) -> Result<(), EmitError> {
        let Some((tree, node)) = self.lambda_node(owner, index) else {
            return Ok(());
        };
        self.write_attribute_lists(
            (method.0 & 0x00FF_FFFF) << 5,
            tree,
            &node,
            AttributeTarget::Method,
        )?;
        let parameters: Vec<SyntaxNode> = node
            .child_of_kind(SyntaxKind::ParameterList)
            .map(|list| {
                list.children()
                    .filter(|child| child.kind() == SyntaxKind::Parameter)
                    .collect()
            })
            .unwrap_or_default();
        for (position, parameter) in parameters.iter().enumerate() {
            if attributes_for(parameter, AttributeTarget::Parameter).is_empty() {
                continue;
            }
            let param = self.metadata.param_token(method, position);
            self.write_attribute_lists(
                ((param.0 & 0x00FF_FFFF) << 5) | 4,
                tree,
                parameter,
                AttributeTarget::Parameter,
            )?;
        }
        Ok(())
    }

    /// Writes the custom attributes a declaration carries onto its row.
    ///
    /// §II.22.10: each is the constructor it calls and a blob of what it was
    /// given (§II.23.3). Whatever cannot be written — an argument that is no
    /// constant, a constructor this assembly cannot name — is left off
    /// rather than written wrong.
    fn write_custom_attributes(
        &mut self,
        parent: u32,
        symbol: SymbolId,
        target: AttributeTarget,
    ) -> Result<(), EmitError> {
        // Every declaration of a partial type may carry attributes, and so
        // may the declaring part of a partial method.
        let mut declarations = self.compilation.declaration_nodes(symbol).to_vec();
        if matches!(target, AttributeTarget::Method | AttributeTarget::Return) {
            declarations.extend(self.declaring_partial_parts(symbol));
        }
        for (tree, span) in declarations {
            let Some(node) = self
                .compilation
                .trees()
                .get(tree)
                .and_then(|tree| tree.root().find_node(span))
            else {
                continue;
            };
            self.write_attribute_lists(parent, tree, &node, target)?;
        }
        Ok(())
    }

    /// The method, where any of its declarations says `[return: ...]`.
    fn has_return_attributes(&self, method: SymbolId) -> Option<SymbolId> {
        let mut declarations = self.compilation.declaration_nodes(method).to_vec();
        declarations.extend(self.declaring_partial_parts(method));
        declarations
            .into_iter()
            .any(|(tree, span)| {
                self.compilation
                    .trees()
                    .get(tree)
                    .and_then(|tree| tree.root().find_node(span))
                    .is_some_and(|node| !attributes_for(&node, AttributeTarget::Return).is_empty())
            })
            .then_some(method)
    }

    /// The bodiless declaring part of a partial method, whose symbol the
    /// implementing part took over: its attributes are the method's too.
    fn declaring_partial_parts(&self, method: SymbolId) -> Vec<(usize, TextSpan)> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(method);
        if !symbol.modifiers.contains(Modifiers::PARTIAL) {
            return Vec::new();
        }
        let Some(container) = symbol.container else {
            return Vec::new();
        };
        let count = symbol
            .as_method()
            .map_or(0, |detail| detail.parameters.len());
        let mut parts = Vec::new();
        for (tree, span) in self.compilation.declaration_nodes(container).to_vec() {
            let Some(node) = self
                .compilation
                .trees()
                .get(tree)
                .and_then(|tree| tree.root().find_node(span))
            else {
                continue;
            };
            for member in node.children() {
                if member.kind() != SyntaxKind::MethodDeclaration
                    || member.child_of_kind(SyntaxKind::Block).is_some()
                    || member
                        .child_of_kind(SyntaxKind::ArrowExpressionClause)
                        .is_some()
                {
                    continue;
                }
                let partial = member
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::PartialKeyword);
                let named = member.child_tokens().any(|token| {
                    token.kind() == SyntaxKind::IdentifierToken && token.value_text() == symbol.name
                });
                let parameters =
                    member
                        .child_of_kind(SyntaxKind::ParameterList)
                        .map_or(0, |list| {
                            list.children()
                                .filter(|child| child.kind() == SyntaxKind::Parameter)
                                .count()
                        });
                if partial && named && parameters == count {
                    parts.push((tree, member.span()));
                }
            }
        }
        parts
    }

    fn write_attribute_lists(
        &mut self,
        parent: u32,
        tree: usize,
        node: &SyntaxNode,
        target: AttributeTarget,
    ) -> Result<(), EmitError> {
        let lists = attributes_for(node, target);
        // What goes on a property's field is a field's attribute from here.
        let target = match target {
            AttributeTarget::PropertyField => AttributeTarget::Field,
            other => other,
        };
        for attribute in lists {
            let Some(bound) = self.binder.bind_attribute(tree, node, &attribute) else {
                continue;
            };
            let Some(constructor) = bound.constructor else {
                continue;
            };
            let Some(attribute_type) = bound.ty.symbol() else {
                continue;
            };
            let pseudo = self.is_pseudo_attribute(attribute_type, target);
            if pseudo {
                self.apply_pseudo_attribute(attribute_type, parent, &bound, target);
            }
            if pseudo || self.conditioned_out(attribute_type, tree, attribute.span().start()) {
                continue;
            }
            // `[Attr<string>("a")]` names the constructor of the
            // construction, which is a member of a `TypeSpec`.
            let constructed = matches!(&bound.ty, Type::Named { type_arguments, .. } if !type_arguments.is_empty());
            let token = if constructed {
                Some(self.member_of_constructed(constructor, &bound.ty)?)
            } else {
                self.attribute_constructor(constructor)
            };
            let Some(token) = token else {
                continue;
            };
            let Some(value) = self.encode_attribute(constructor, &bound)? else {
                continue;
            };
            // A `CustomAttributeType` tagged 2 is a `MethodDef` and tagged 3
            // a `MemberRef`.
            let tag = if token.0 >> 24 == u32::from(table::METHOD_DEF) {
                2
            } else {
                3
            };
            self.metadata.add_custom_attribute(
                parent,
                ((token.0 & 0x00FF_FFFF) << 3) | tag,
                &value,
            );
        }
        Ok(())
    }

    /// The attributes on a type parameter, `class C<[A] T>`, which go on its
    /// `GenericParam` row once the table is sorted and the row is known.
    fn write_type_parameter_attributes(
        &mut self,
        owner: u32,
        number: u16,
        parameter: SymbolId,
    ) -> Result<(), EmitError> {
        for (tree, span) in self.compilation.declaration_nodes(parameter).to_vec() {
            let Some(node) = self
                .compilation
                .trees()
                .get(tree)
                .and_then(|tree| tree.root().find_node(span))
            else {
                continue;
            };
            if attributes_for(&node, AttributeTarget::TypeParameter).is_empty() {
                continue;
            }
            let parent = self.metadata.generic_param_parent(owner, number);
            self.write_attribute_lists(parent, tree, &node, AttributeTarget::TypeParameter)?;
        }
        Ok(())
    }

    /// The `MethodImplAttributes` the source asks for on the method a plan
    /// writes: `[MethodImpl]` on a method, an accessor, a local function or
    /// a lambda, and `[PreserveSig]`.
    fn written_impl_flags(&mut self, source: &MethodSource) -> u16 {
        let mut nodes: Vec<(usize, SyntaxNode)> = Vec::new();
        let at = |this: &Self, symbol: SymbolId, nodes: &mut Vec<(usize, SyntaxNode)>| {
            let mut declarations = this.compilation.declaration_nodes(symbol).to_vec();
            declarations.extend(this.declaring_partial_parts(symbol));
            for (tree, span) in declarations {
                if let Some(node) = this
                    .compilation
                    .trees()
                    .get(tree)
                    .and_then(|tree| tree.root().find_node(span))
                {
                    nodes.push((tree, node));
                }
            }
        };
        match source {
            MethodSource::Declared(symbol) => at(self, *symbol, &mut nodes),
            MethodSource::LocalFunction { owner, index } => {
                if let Some(function) = self
                    .body_of(*owner)
                    .and_then(|body| body.local_functions.get(*index).map(|it| it.symbol))
                {
                    at(self, function, &mut nodes);
                }
            }
            MethodSource::Lambda { owner, index } => {
                nodes.extend(self.lambda_node(*owner, *index));
            }
            // An automatic property's accessors have no symbols of their
            // own, only their syntax inside the property's.
            MethodSource::PropertyGetter { property, .. }
            | MethodSource::PropertySetter { property } => {
                let getter = matches!(source, MethodSource::PropertyGetter { .. });
                let &(tree, _) = match self.compilation.declaration_nodes(*property).first() {
                    Some(declaration) => declaration,
                    None => return 0,
                };
                if let Some(accessor) = self
                    .compilation
                    .declaration_node(*property)
                    .and_then(|node| node.child_of_kind(SyntaxKind::AccessorList))
                    .and_then(|list| {
                        list.children().find(|accessor| {
                            if getter {
                                accessor.kind() == SyntaxKind::GetAccessorDeclaration
                            } else {
                                matches!(
                                    accessor.kind(),
                                    SyntaxKind::SetAccessorDeclaration
                                        | SyntaxKind::InitAccessorDeclaration
                                )
                            }
                        })
                    })
                {
                    nodes.push((tree, accessor));
                }
            }
            _ => {}
        }
        let mut flags = 0u16;
        for (tree, node) in nodes {
            for attribute in attributes_for(&node, AttributeTarget::Method) {
                let Some(bound) = self.binder.bind_attribute(tree, &node, &attribute) else {
                    continue;
                };
                let Some(ty) = bound.ty.symbol() else {
                    continue;
                };
                let name = self.compilation.symbols().qualified_name(ty);
                match name.as_str() {
                    // The options less the two bits only `MethodCodeType`
                    // may set (Roslyn's `DecodeMethodImplAttribute`).
                    "System.Runtime.CompilerServices.MethodImplAttribute" => {
                        if let Some(ConstantValue::Int32(options)) = bound
                            .arguments
                            .first()
                            .and_then(|value| self.binder.folded(value))
                        {
                            flags |= (options & !3) as u16;
                        }
                        for (member, value) in &bound.named {
                            if self.compilation.symbols().get(*member).name == "MethodCodeType"
                                && let Some(ConstantValue::Int32(code @ 0..=3)) =
                                    self.binder.folded(value)
                            {
                                flags |= code as u16;
                            }
                        }
                    }
                    "System.Runtime.InteropServices.PreserveSigAttribute" => {
                        flags |= method_impl::PRESERVE_SIG;
                    }
                    _ => {}
                }
            }
        }
        flags
    }

    /// The native type `[MarshalAs]` describes (§II.23.4), as Roslyn's
    /// `MarshalAsAttributeDecoder` reads the attribute and its metadata
    /// writer lays the descriptor out. `None` where the attribute is one
    /// Roslyn rejects: a `ByValArray` anywhere but on a field, a
    /// `CustomMarshaler` with no marshaller, a named argument the kind
    /// takes none of.
    fn marshal_descriptor(&mut self, bound: &BoundAttribute, field: bool) -> Option<Vec<u8>> {
        const MAX: i64 = 0x1FFF_FFFF;
        let integer = |value: Option<ConstantValue>| -> Option<i64> {
            match value? {
                ConstantValue::Int32(value) => Some(i64::from(value)),
                _ => None,
            }
        };
        let kind = integer(self.binder.folded(bound.arguments.first()?))?;
        let mut named: Vec<(String, &BoundExpression)> = Vec::new();
        for (member, value) in &bound.named {
            named.push((self.compilation.symbols().get(*member).name.clone(), value));
        }
        let mut out = Vec::new();
        let compress = |out: &mut Vec<u8>, value: i64| {
            crate::signature::compress(out, value as u32);
        };
        if !(0..=MAX).contains(&kind) {
            return None;
        }
        compress(&mut out, kind);
        match kind {
            // `CustomMarshaler`: an empty GUID and native type name, then the
            // marshaller, by name or by type, and the cookie.
            0x2C => {
                let mut marshaller: Option<Option<String>> = None;
                let mut by_type: Option<Option<String>> = None;
                let mut cookie = None;
                for (name, value) in &named {
                    match name.as_str() {
                        "MarshalType" => marshaller = Some(self.folded_string(value)?),
                        "MarshalTypeRef" => {
                            by_type = Some(match &written_value(value).kind {
                                BoundExpressionKind::TypeOf(ty) => {
                                    Some(self.serialized_type_name(ty)?)
                                }
                                _ => None,
                            });
                        }
                        "MarshalCookie" => cookie = self.folded_string(value)?,
                        _ => {}
                    }
                }
                out.extend([0, 0]);
                match marshaller.or(by_type)? {
                    Some(name) => ser_string(&mut out, Some(&name)),
                    None => out.push(0),
                }
                match cookie {
                    Some(cookie) => ser_string(&mut out, Some(&cookie)),
                    None => out.push(0),
                }
            }
            // `Interface`, `IDispatch`, `IUnknown`: the parameter the IID is
            // in, where one is named.
            0x1C | 0x1A | 0x19 => {
                for (name, value) in &named {
                    if name == "IidParameterIndex" {
                        let index = integer(self.binder.folded(value))?;
                        if !(0..=MAX).contains(&index) {
                            return None;
                        }
                        compress(&mut out, index);
                    }
                }
            }
            // `LPArray` and, on a field only, `ByValArray`.
            0x2A | 0x1E => {
                let fixed = kind == 0x1E;
                if fixed && !field {
                    return None;
                }
                let mut element = None;
                let mut count = None;
                let mut parameter = None;
                for (name, value) in &named {
                    match name.as_str() {
                        "ArraySubType" => {
                            let sub = integer(self.binder.folded(value))?;
                            if !fixed && sub == 0x2C || !(0..=MAX).contains(&sub) {
                                return None;
                            }
                            element = Some(sub);
                        }
                        "SizeConst" => {
                            let size = integer(self.binder.folded(value))?;
                            if !(0..=MAX).contains(&size) {
                                return None;
                            }
                            count = Some(size);
                        }
                        "SizeParamIndex" if !fixed => {
                            let index = integer(self.binder.folded(value))?;
                            if index < 0 {
                                return None;
                            }
                            parameter = Some(index);
                        }
                        "SizeParamIndex" | "SafeArraySubType" => return None,
                        _ => {}
                    }
                }
                if fixed {
                    // A `ByValArray` with no `SizeConst` is one element long
                    // (CS9125 warns).
                    compress(&mut out, count.unwrap_or(1));
                    if let Some(element) = element {
                        compress(&mut out, element);
                    }
                } else {
                    compress(&mut out, element.unwrap_or(0x50));
                    match (parameter, count) {
                        (Some(parameter), count) => {
                            compress(&mut out, parameter);
                            if let Some(count) = count {
                                compress(&mut out, count);
                                out.push(1);
                            }
                        }
                        (None, Some(count)) => {
                            out.push(0);
                            compress(&mut out, count);
                            out.push(0);
                        }
                        (None, None) => {}
                    }
                }
            }
            // `SafeArray`: the variant type of its elements, and the type of
            // a user-defined one, which only `VT_DISPATCH`, `VT_UNKNOWN` and
            // `VT_RECORD` take.
            0x1D => {
                let mut variant = None;
                let mut user_defined = None;
                for (name, value) in &named {
                    match name.as_str() {
                        "SafeArraySubType" => {
                            let sub = integer(self.binder.folded(value))?;
                            if !(0..=MAX).contains(&sub) {
                                return None;
                            }
                            variant = Some(sub);
                        }
                        "SafeArrayUserDefinedSubType" => {
                            user_defined = Some(match &written_value(value).kind {
                                BoundExpressionKind::TypeOf(ty) => Some(ty.clone()),
                                _ => None,
                            });
                        }
                        "ArraySubType" | "SizeConst" | "SizeParamIndex" => return None,
                        _ => {}
                    }
                }
                let user_defined = match variant {
                    Some(9 | 13 | 36) => user_defined.flatten(),
                    Some(_) if user_defined.is_some() => return None,
                    _ => None,
                };
                if let Some(variant) = variant {
                    compress(&mut out, variant);
                    if let Some(ty) = user_defined {
                        let name = self.serialized_type_name(&ty)?;
                        ser_string(&mut out, Some(&name));
                    }
                }
            }
            // `ByValTStr`, on a field only: its length, which must be given.
            0x17 => {
                if !field {
                    return None;
                }
                let mut count = None;
                for (name, value) in &named {
                    match name.as_str() {
                        "SizeConst" => {
                            let size = integer(self.binder.folded(value))?;
                            if !(0..=MAX).contains(&size) {
                                return None;
                            }
                            count = Some(size);
                        }
                        "ArraySubType" | "SizeParamIndex" => return None,
                        _ => {}
                    }
                }
                compress(&mut out, count?);
            }
            // `VBByRefStr`, anywhere but on a field.
            0x22 if field => return None,
            _ => {}
        }
        Some(out)
    }

    /// A `string` constant, `None` inside for `null`; `None` for no
    /// constant at all.
    fn folded_string(&self, value: &BoundExpression) -> Option<Option<String>> {
        match self.binder.folded(value)? {
            ConstantValue::String(text) => Some(Some(text)),
            ConstantValue::Null => Some(None),
            _ => None,
        }
    }

    /// The token of an attribute's constructor: the definition where the
    /// attribute class is declared here, a reference where it is not.
    fn attribute_constructor(&mut self, constructor: SymbolId) -> Option<Token> {
        if let Some(token) = self.methods.get(&constructor) {
            return Some(*token);
        }
        if self.compilation.is_from_corlib(constructor) {
            return self.corlib_member(constructor).ok();
        }
        None
    }

    /// Whether an attribute is one metadata has a bit, a column or a row
    /// for instead of a `CustomAttribute` row (§II.21.2) where it is written
    /// — `[StructLayout]` is a `ClassLayout` row, `[MethodImpl]` is in
    /// `ImplFlags`, `[AssemblyVersion]` is the `Assembly` row's version —
    /// and writing it as an attribute as well would be wrong. What is left
    /// out depends on what the attribute is on, as Roslyn's
    /// `ShouldEmitAttribute` has it. `[ThreadStatic]` and `[IsByRefLike]`
    /// are real attributes that the emitter already writes where it needs
    /// them.
    fn is_pseudo_attribute(&self, attribute_type: SymbolId, target: AttributeTarget) -> bool {
        let name = self.compilation.symbols().qualified_name(attribute_type);
        let name = name.as_str();
        const SPECIAL_NAME: &str = "System.Runtime.CompilerServices.SpecialNameAttribute";
        const MARSHAL_AS: &str = "System.Runtime.InteropServices.MarshalAsAttribute";
        match target {
            AttributeTarget::Assembly => matches!(
                name,
                "System.Reflection.AssemblyCultureAttribute"
                    | "System.Reflection.AssemblyVersionAttribute"
                    | "System.Reflection.AssemblyFlagsAttribute"
                    | "System.Reflection.AssemblyAlgorithmIdAttribute"
                    | "System.Runtime.CompilerServices.TypeForwardedToAttribute"
            ),
            AttributeTarget::Event => name == SPECIAL_NAME,
            AttributeTarget::Field | AttributeTarget::PropertyField => matches!(
                name,
                SPECIAL_NAME
                    | MARSHAL_AS
                    | "System.NonSerializedAttribute"
                    | "System.Runtime.InteropServices.FieldOffsetAttribute"
                    | "System.ThreadStaticAttribute"
            ),
            AttributeTarget::Method => matches!(
                name,
                SPECIAL_NAME
                    | "System.Runtime.CompilerServices.MethodImplAttribute"
                    | "System.Runtime.InteropServices.DllImportAttribute"
                    | "System.Runtime.InteropServices.PreserveSigAttribute"
                    | "System.Security.DynamicSecurityMethodAttribute"
            ),
            AttributeTarget::Return => name == MARSHAL_AS,
            AttributeTarget::Type => matches!(
                name,
                SPECIAL_NAME
                    | "System.Runtime.InteropServices.ComImportAttribute"
                    | "System.SerializableAttribute"
                    | "System.Runtime.InteropServices.StructLayoutAttribute"
                    | "System.Runtime.InteropServices.WindowsRuntime.WindowsRuntimeImportAttribute"
                    | "System.Runtime.CompilerServices.IsByRefLikeAttribute"
            ),
            AttributeTarget::Parameter => matches!(
                name,
                MARSHAL_AS
                    | "System.Runtime.InteropServices.OptionalAttribute"
                    | "System.Runtime.InteropServices.DefaultParameterValueAttribute"
                    | "System.Runtime.InteropServices.InAttribute"
                    | "System.Runtime.InteropServices.OutAttribute"
            ),
            AttributeTarget::Property => matches!(
                name,
                SPECIAL_NAME
                    | "System.Runtime.CompilerServices.IndexerNameAttribute"
                    | "System.Diagnostics.CodeAnalysis.DisallowNullAttribute"
                    | "System.Diagnostics.CodeAnalysis.AllowNullAttribute"
                    | "System.Diagnostics.CodeAnalysis.MaybeNullAttribute"
                    | "System.Diagnostics.CodeAnalysis.NotNullAttribute"
            ),
            AttributeTarget::TypeParameter => false,
        }
    }

    /// The attributes Roslyn puts on every assembly it writes, after
    /// `[Extension]` and before what the source wrote, unless the source
    /// wrote them itself: `[CompilationRelaxations(NoStringInterning)]`,
    /// `[RuntimeCompatibility(WrapNonExceptionThrows = true)]` — which is
    /// what makes `catch (Exception)` catch a thrown string — and
    /// `[Debuggable]`, which turns the JIT's optimizations off for a debug
    /// build.
    fn mark_assembly_relaxations(&mut self) {
        let written = self.written_assembly_attributes();
        let exists =
            |this: &Self, name: &str| this.compilation.type_by_metadata_name(name).is_some();
        let void = SigType::Primitive(ElementType::Void);
        const RELAXATIONS: &str = "System.Runtime.CompilerServices.CompilationRelaxationsAttribute";
        if !written.contains(RELAXATIONS) && exists(self, RELAXATIONS) {
            let constructor = self.references.member_ref(
                &mut self.metadata,
                RELAXATIONS,
                ".ctor",
                &method_signature(true, &void, &[SigType::Primitive(ElementType::I4)]),
            );
            // `CompilationRelaxations.NoStringInterning`.
            let mut blob = vec![0x01, 0x00];
            blob.extend_from_slice(&8i32.to_le_bytes());
            blob.extend_from_slice(&[0x00, 0x00]);
            self.metadata.add_custom_attribute(
                (1 << 5) | 14,
                ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
                &blob,
            );
        }
        const COMPATIBILITY: &str = "System.Runtime.CompilerServices.RuntimeCompatibilityAttribute";
        if !written.contains(COMPATIBILITY) && exists(self, COMPATIBILITY) {
            let constructor = self.references.member_ref(
                &mut self.metadata,
                COMPATIBILITY,
                ".ctor",
                &method_signature(true, &void, &[]),
            );
            // One named argument: the property (0x54) `WrapNonExceptionThrows`,
            // a `bool` (0x02), true.
            let mut blob = vec![0x01, 0x00, 0x01, 0x00, 0x54, 0x02];
            ser_string(&mut blob, Some("WrapNonExceptionThrows"));
            blob.push(0x01);
            self.metadata.add_custom_attribute(
                (1 << 5) | 14,
                ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
                &blob,
            );
        }
        const DEBUGGABLE: &str = "System.Diagnostics.DebuggableAttribute";
        if !written.contains(DEBUGGABLE) && exists(self, DEBUGGABLE) {
            let modes = self.references.type_ref_coded(
                &mut self.metadata,
                "System.Diagnostics.DebuggableAttribute+DebuggingModes",
            );
            let constructor = self.references.member_ref(
                &mut self.metadata,
                DEBUGGABLE,
                ".ctor",
                &method_signature(
                    true,
                    &void,
                    &[SigType::Named {
                        value_type: true,
                        coded: modes,
                    }],
                ),
            );
            // `IgnoreSymbolStoreSequencePoints`, and for a debug build
            // `Default | DisableOptimizations | EnableEditAndContinue`.
            let mode: i32 = if self.compilation.options().optimize {
                2
            } else {
                2 | 1 | 256 | 4
            };
            let mut blob = vec![0x01, 0x00];
            blob.extend_from_slice(&mode.to_le_bytes());
            blob.extend_from_slice(&[0x00, 0x00]);
            self.metadata.add_custom_attribute(
                (1 << 5) | 14,
                ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
                &blob,
            );
        }
    }

    /// The types of the attributes the source writes on the assembly.
    fn written_assembly_attributes(&mut self) -> std::collections::HashSet<String> {
        let mut written = std::collections::HashSet::new();
        for tree in 0..self.compilation.trees().len() {
            let Some(root) = self.compilation.trees().get(tree).map(|tree| tree.root()) else {
                continue;
            };
            for attribute in attributes_for(&root, AttributeTarget::Assembly) {
                if let Some(ty) = self
                    .binder
                    .bind_attribute(tree, &root, &attribute)
                    .and_then(|bound| bound.ty.symbol())
                {
                    written.insert(self.compilation.symbols().qualified_name(ty));
                }
            }
        }
        written
    }

    /// What a pseudo-attribute writes in place of a `CustomAttribute` row,
    /// where the row it is on says nothing of it already: a flag, a
    /// `FieldMarshal` row, a column of the `Assembly` row.
    fn apply_pseudo_attribute(
        &mut self,
        attribute_type: SymbolId,
        parent: u32,
        bound: &BoundAttribute,
        target: AttributeTarget,
    ) {
        let name = self.compilation.symbols().qualified_name(attribute_type);
        let first = bound
            .arguments
            .first()
            .and_then(|value| self.binder.folded(value));
        // The `HasCustomAttribute` tag says which table the row is in.
        let tag = parent & 0x1F;
        match name.as_str() {
            "System.Runtime.InteropServices.MarshalAsAttribute" => {
                if let Some(descriptor) =
                    self.marshal_descriptor(bound, target == AttributeTarget::Field)
                {
                    self.metadata.add_field_marshal(parent, &descriptor);
                }
            }
            // `SpecialName` is its own bit in each table's flags.
            "System.Runtime.CompilerServices.SpecialNameAttribute" => {
                let flag = match tag {
                    0 => u32::from(method_attributes::SPECIAL_NAME),
                    1 => u32::from(field_attributes::SPECIAL_NAME),
                    3 => 0x0400,
                    9 | 10 => 0x0200,
                    _ => 0,
                };
                self.metadata.add_row_flags(parent, flag);
            }
            "System.NonSerializedAttribute" if tag == 1 => {
                self.metadata.add_row_flags(parent, 0x0080);
            }
            "System.SerializableAttribute" if tag == 3 => {
                self.metadata
                    .add_row_flags(parent, type_attributes::SERIALIZABLE);
            }
            // "1.2" is 1.2.0.0; a `*` is a number of the clock's, which a
            // reproducible build has none of.
            "System.Reflection.AssemblyVersionAttribute" => {
                if let Some(ConstantValue::String(text)) = first {
                    let parts: Vec<Option<u16>> =
                        text.split('.').map(|part| part.parse().ok()).collect();
                    if (1..=4).contains(&parts.len()) && parts.iter().all(Option::is_some) {
                        let mut version = [0u16; 4];
                        for (at, part) in parts.into_iter().enumerate() {
                            version[at] = part.unwrap_or(0);
                        }
                        self.metadata.set_assembly_version(version);
                    }
                }
            }
            "System.Reflection.AssemblyCultureAttribute" => {
                if let Some(ConstantValue::String(culture)) = first {
                    self.metadata.set_assembly_culture(&culture);
                }
            }
            "System.Reflection.AssemblyFlagsAttribute" => match first {
                Some(ConstantValue::Int32(flags)) => self.metadata.set_assembly_flags(flags as u32),
                Some(ConstantValue::UInt32(flags)) => self.metadata.set_assembly_flags(flags),
                _ => {}
            },
            "System.Reflection.AssemblyAlgorithmIdAttribute" => match first {
                Some(ConstantValue::Int32(algorithm)) => {
                    self.metadata.set_hash_algorithm(algorithm as u32);
                }
                Some(ConstantValue::UInt32(algorithm)) => {
                    self.metadata.set_hash_algorithm(algorithm);
                }
                _ => {}
            },
            _ => {}
        }
    }

    /// The methods `[ModuleInitializer]` marks, in the order Roslyn calls
    /// them: lexically, file by file. An attribute a `[Conditional]` on its
    /// class leaves out marks nothing; one on the method does not matter,
    /// since the call is the compiler's and not the source's.
    fn module_initializers(&self, user_types: &[SymbolId]) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let mut found = Vec::new();
        for ty in user_types {
            for member in &symbols.get(*ty).members {
                if symbols.get(*member).kind != SymbolKind::Method {
                    continue;
                }
                // The declaring part of a partial method may be what carries
                // the attribute.
                let mut parts = self.compilation.declaration_nodes(*member).to_vec();
                parts.extend(self.declaring_partial_parts(*member));
                for (tree, span) in parts {
                    let Some(node) = self
                        .compilation
                        .trees()
                        .get(tree)
                        .and_then(|tree| tree.root().find_node(span))
                    else {
                        continue;
                    };
                    let marked = attributes_for(&node, AttributeTarget::Method)
                        .iter()
                        .any(|attribute| {
                            self.binder
                                .bind_attribute(tree, &node, attribute)
                                .and_then(|bound| bound.ty.symbol())
                                .is_some_and(|ty| {
                                    symbols.qualified_name(ty)
                                        == "System.Runtime.CompilerServices.ModuleInitializerAttribute"
                                })
                        });
                    if marked {
                        found.push(((tree, span.start()), *member));
                        break;
                    }
                }
            }
        }
        found.sort_by_key(|(at, _)| *at);
        found.into_iter().map(|(_, member)| member).collect()
    }

    /// Whether a `[Conditional("X")]` on the attribute class leaves the
    /// attribute at `position` out of this file, `X` not being defined there
    /// (§22.5.3).
    fn conditioned_out(&self, attribute_type: SymbolId, tree: usize, position: u32) -> bool {
        let Some(conditions) = self.binder.conditional_symbols(attribute_type) else {
            return false;
        };
        let Some(tree) = self.compilation.trees().get(tree) else {
            return false;
        };
        !conditions
            .iter()
            .any(|condition| tree.is_defined_at(condition, position))
    }

    /// The blob of an attribute's arguments (§II.23.3): the prolog, one
    /// fixed argument per constructor parameter, and the named ones after a
    /// count. `None` where an argument is nothing the blob can hold.
    fn encode_attribute(
        &mut self,
        constructor: SymbolId,
        bound: &BoundAttribute,
    ) -> Result<Option<Vec<u8>>, EmitError> {
        // A generic attribute's parameters are of its construction's types.
        let substitution: HashMap<SymbolId, Type> = match &bound.ty {
            Type::Named {
                symbol,
                type_arguments,
            } if !type_arguments.is_empty() => self
                .compilation
                .symbols()
                .get(*symbol)
                .as_named_type()
                .map(|detail| {
                    detail
                        .type_parameters
                        .iter()
                        .copied()
                        .zip(type_arguments.iter().cloned())
                        .collect()
                })
                .unwrap_or_default(),
            _ => HashMap::new(),
        };
        let parameters: Vec<(Type, bool)> = {
            let symbols = self.compilation.symbols();
            let Some(detail) = symbols.get(constructor).as_method() else {
                return Ok(None);
            };
            detail
                .parameters
                .iter()
                .map(|parameter| {
                    (
                        self.type_of(*parameter).substitute(&substitution),
                        symbols
                            .get(*parameter)
                            .as_parameter()
                            .is_some_and(|detail| detail.is_params),
                    )
                })
                .collect()
        };
        let mut out = vec![0x01, 0x00];
        for (index, (ty, is_params)) in parameters.iter().enumerate() {
            // `[A(1, 2, 3)]` on a `params int[]` is one array argument. An
            // array or a `null` in its place is the normal form: `[A(null)]`
            // passes no array at all, as a call does.
            let packed = *is_params
                && !(bound.arguments.len() == parameters.len()
                    && bound.arguments.get(index).is_some_and(|argument| {
                        matches!(argument.ty, Type::Array { .. })
                            || matches!(written_value(argument).ty, Type::Null)
                    }));
            if packed {
                let Type::Array { element, .. } = ty else {
                    return Ok(None);
                };
                let rest = &bound.arguments[index.min(bound.arguments.len())..];
                out.extend((rest.len() as u32).to_le_bytes());
                for argument in rest {
                    if !self.encode_argument(&mut out, element, argument)? {
                        return Ok(None);
                    }
                }
                break;
            }
            let Some(argument) = bound.arguments.get(index) else {
                return Ok(None);
            };
            if !self.encode_argument(&mut out, ty, argument)? {
                return Ok(None);
            }
        }
        let Ok(count) = u16::try_from(bound.named.len()) else {
            return Ok(None);
        };
        out.extend(count.to_le_bytes());
        for (member, value) in &bound.named {
            let (kind, name) = {
                let symbol = self.compilation.symbols().get(*member);
                (symbol.kind, symbol.name.clone())
            };
            out.push(if kind == SymbolKind::Field {
                0x53
            } else {
                0x54
            });
            let ty = self.type_of(*member).substitute(&substitution);
            if !self.encode_element_type(&mut out, &ty)? {
                return Ok(None);
            }
            ser_string(&mut out, Some(&name));
            if !self.encode_argument(&mut out, &ty, value)? {
                return Ok(None);
            }
        }
        Ok(Some(out))
    }

    /// One argument of an attribute, as the type of the parameter it is for
    /// says it is written (§II.23.3): a constant in its width, a string or a
    /// type as a serialized string, an array as a count and its elements, and
    /// an `object` as the written value's own type followed by the value.
    /// `false` where the argument is none of these.
    fn encode_argument(
        &mut self,
        out: &mut Vec<u8>,
        ty: &Type,
        argument: &BoundExpression,
    ) -> Result<bool, EmitError> {
        let written = written_value(argument);
        let special = self.special_type_of(ty);
        if special == Some(SpecialType::Object) {
            // A null boxed is written as a null string.
            if matches!(written.ty, Type::Null) {
                out.extend([0x0E, 0xFF]);
                return Ok(true);
            }
            let inner = written.ty.clone();
            let before = out.len();
            if !self.encode_element_type(out, &inner)? {
                // `default(B<delegate*<void>[]>)` is a null of a type no blob
                // can name: it is written as the null any `object` can hold.
                let null_default = matches!(written.kind, BoundExpressionKind::Default(_))
                    && written.ty.is_reference_type(self.compilation.symbols());
                if null_default || matches!(self.binder.folded(written), Some(ConstantValue::Null))
                {
                    out.truncate(before);
                    out.extend([0x0E, 0xFF]);
                    return Ok(true);
                }
                return Ok(false);
            }
            return self.encode_argument(out, &inner, written);
        }
        if special == Some(SpecialType::String) {
            return Ok(match self.binder.folded(argument) {
                Some(ConstantValue::String(text)) => {
                    ser_string(out, Some(&text));
                    true
                }
                Some(ConstantValue::Null) => {
                    ser_string(out, None);
                    true
                }
                _ => false,
            });
        }
        if self.is_system_type(ty) {
            return Ok(match &written.kind {
                BoundExpressionKind::TypeOf(named) => match self.serialized_type_name(named) {
                    Some(name) => {
                        ser_string(out, Some(&name));
                        true
                    }
                    None => false,
                },
                _ if matches!(written.ty, Type::Null) => {
                    ser_string(out, None);
                    true
                }
                _ => false,
            });
        }
        if let Type::Array { element, .. } = ty {
            return match &written.kind {
                BoundExpressionKind::ArrayCreation { elements, .. } => {
                    out.extend((elements.len() as u32).to_le_bytes());
                    for value in elements {
                        if !self.encode_argument(out, element, value)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ if matches!(written.ty, Type::Null) => {
                    out.extend(u32::MAX.to_le_bytes());
                    Ok(true)
                }
                _ => Ok(false),
            };
        }
        // A number, a `bool`, a `char` or an enum member: the constant in the
        // width of the parameter's type, an enum's being its underlying one.
        let Some(width) = self.constant_width(ty) else {
            return Ok(false);
        };
        if matches!(
            width,
            SpecialType::Decimal | SpecialType::Object | SpecialType::Void
        ) {
            return Ok(false);
        }
        let Some(constant) = self
            .binder
            .folded(argument)
            .or_else(|| self.binder.folded(written))
        else {
            return Ok(false);
        };
        if matches!(constant, ConstantValue::Null | ConstantValue::String(_)) {
            return Ok(false);
        }
        let (_, bytes) = encode_constant_as(&constant, Some(width));
        out.extend(bytes);
        Ok(true)
    }

    /// The `FieldOrPropType` of a named argument, or of a value boxed into
    /// an `object` (§II.23.3): an element type for the primitives, `0x50`
    /// for `System.Type`, `0x51` for `object`, `0x1D` and the element for an
    /// array, and `0x55` and the enum's name for an enum.
    fn encode_element_type(&mut self, out: &mut Vec<u8>, ty: &Type) -> Result<bool, EmitError> {
        if let Some(special) = self.special_type_of(ty) {
            let element = match special {
                SpecialType::Boolean => 0x02,
                SpecialType::Char => 0x03,
                SpecialType::SByte => 0x04,
                SpecialType::Byte => 0x05,
                SpecialType::Int16 => 0x06,
                SpecialType::UInt16 => 0x07,
                SpecialType::Int32 => 0x08,
                SpecialType::UInt32 => 0x09,
                SpecialType::Int64 => 0x0A,
                SpecialType::UInt64 => 0x0B,
                SpecialType::Single => 0x0C,
                SpecialType::Double => 0x0D,
                SpecialType::String => 0x0E,
                SpecialType::Object => 0x51,
                SpecialType::Decimal | SpecialType::Void => return Ok(false),
            };
            out.push(element);
            return Ok(true);
        }
        if self.is_system_type(ty) {
            out.push(0x50);
            return Ok(true);
        }
        if let Type::Array { element, rank: 1 } = ty {
            out.push(0x1D);
            return self.encode_element_type(out, element);
        }
        if let Some(symbol) = ty.symbol()
            && self.compilation.symbols().get(symbol).type_kind() == Some(TypeKind::Enum)
        {
            let Some(name) = self.serialized_type_name(ty) else {
                return Ok(false);
            };
            out.push(0x55);
            ser_string(out, Some(&name));
            return Ok(true);
        }
        Ok(false)
    }

    fn is_system_type(&self, ty: &Type) -> bool {
        ty.symbol().is_some_and(|symbol| {
            self.compilation.symbols().qualified_name(symbol) == "System.Type"
        })
    }

    /// A type as an attribute blob names it (§II.23.3): `Ns.Outer+Inner`1`,
    /// with type arguments in brackets and `[]` after an array. A type of
    /// this assembly or of the core library needs no assembly name, which is
    /// where nearly every type an attribute names comes from.
    fn serialized_type_name(&self, ty: &Type) -> Option<String> {
        let mut name = self.unqualified_serialized_name(ty)?;
        // A type of another assembly names it, as Roslyn's
        // `TypeNameSerializer` writes it for every one — the core library's
        // too: `System.Int32*` alone is looked for here first, and a program
        // that declares a `System.Int32` of its own would find that.
        if let Some(reference) = self.home_assembly(ty) {
            let [major, minor, build, revision] = reference.version;
            let token = if crate::references::is_framework(&reference.name) {
                "b03f5f7f11d50a3a"
            } else {
                "null"
            };
            name.push_str(&format!(
                ", {}, Version={major}.{minor}.{build}.{revision}, Culture=neutral, \
                 PublicKeyToken={token}",
                reference.name
            ));
        }
        Some(name)
    }

    /// The assembly a type written in an attribute comes from: an array's or
    /// a pointer's element's, and a construction's definition's.
    fn home_assembly(&self, ty: &Type) -> Option<rustlyn_semantics::Reference> {
        match ty {
            Type::Named { symbol, .. } => self.compilation.assembly_of(*symbol).cloned(),
            Type::Array { element, .. } | Type::Pointer(element) => self.home_assembly(element),
            _ => None,
        }
    }

    fn unqualified_serialized_name(&self, ty: &Type) -> Option<String> {
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let symbols = self.compilation.symbols();
                let mut name = String::new();
                let mut chain = Vec::new();
                let mut current = Some(*symbol);
                while let Some(id) = current {
                    let node = symbols.get(id);
                    if node.kind != SymbolKind::NamedType {
                        let namespace = symbols.qualified_name(id);
                        if !namespace.is_empty() {
                            name.push_str(&namespace);
                            name.push('.');
                        }
                        break;
                    }
                    chain.push(self.compilation.metadata_name_of(id));
                    current = node.container;
                }
                chain.reverse();
                name.push_str(&chain.join("+"));
                if !type_arguments.is_empty() {
                    let mut written = Vec::with_capacity(type_arguments.len());
                    for argument in type_arguments {
                        written.push(format!("[{}]", self.serialized_type_name(argument)?));
                    }
                    name.push('[');
                    name.push_str(&written.join(","));
                    name.push(']');
                }
                Some(name)
            }
            Type::Array { element, rank } => {
                let mut name = self.unqualified_serialized_name(element)?;
                name.push('[');
                name.push_str(&",".repeat(rank.saturating_sub(1)));
                name.push(']');
                Some(name)
            }
            Type::Pointer(element) => {
                Some(format!("{}*", self.unqualified_serialized_name(element)?))
            }
            _ => None,
        }
    }

    /// The struct a `fixed` buffer field is of: `<Name>e__FixedBuffer`, one
    /// `FixedElementField` of the element type, and a fixed size of the whole
    /// buffer (§23.8.2), which is what lets `fixed (byte* p = state.Buffer)`
    /// pin the first element and step through the rest.
    fn plan_fixed_buffer(
        &mut self,
        field: SymbolId,
        enclosing: SymbolId,
        next_type: &mut u32,
    ) -> Result<TypePlan, EmitError> {
        let symbols = self.compilation.symbols();
        let name = symbols.get(field).name.clone();
        let element = self.type_of(field);
        let element_size = element
            .symbol()
            .and_then(|symbol| self.special_of(symbol))
            .and_then(|special| match special {
                SpecialType::Byte | SpecialType::SByte | SpecialType::Boolean => Some(1),
                SpecialType::Int16 | SpecialType::UInt16 | SpecialType::Char => Some(2),
                SpecialType::Int32 | SpecialType::UInt32 | SpecialType::Single => Some(4),
                SpecialType::Int64 | SpecialType::UInt64 | SpecialType::Double => Some(8),
                _ => None,
            })
            .ok_or_else(|| {
                EmitError::new(format!(
                    "the `fixed` buffer `{}` has an element type this backend cannot size",
                    symbols.qualified_name(field)
                ))
            })?;
        let length = self.binder.fixed_buffer_length(field).ok_or_else(|| {
            EmitError::new(format!(
                "the `fixed` buffer `{}` has no constant length",
                symbols.qualified_name(field)
            ))
        })?;
        let size = u32::try_from(length * element_size).map_err(|_| {
            EmitError::new(format!(
                "the `fixed` buffer `{}` is too large",
                symbols.qualified_name(field)
            ))
        })?;
        let token = Token::new(table::TYPE_DEF, *next_type);
        *next_type += 1;
        self.fixed_buffer_types
            .insert(token, (format!("<{name}>e__FixedBuffer"), size));
        Ok(TypePlan {
            symbol: enclosing,
            token,
            fields: vec![FieldPlan {
                // Numbered once the type's own fields all are.
                token: Token::new(table::FIELD, 0),
                name: "FixedElementField".to_string(),
                ty: element,
                flags: field_attributes::PUBLIC,
                symbol: None,
                constant: None,
                sig: None,
            }],
            methods: Vec::new(),
            properties: Vec::new(),
            display: None,
            iterator: None,
            machine: None,
            nested: None,
        })
    }

    fn plan_lambdas(
        &mut self,
        owner: SymbolId,
        next_method: &mut u32,
    ) -> Result<Vec<MethodPlan>, EmitError> {
        let Some(body) = self.body_of(owner) else {
            return Ok(Vec::new());
        };
        // A lambda in a member that becomes a state machine is a method of
        // the machine, planned with it; one in a member that gets a display
        // class is a method of that class, or of a nested one, planned
        // there — a copy on the type would never be called, and its frame
        // would be set up as if it were.
        let is_field = self.compilation.symbols().get(owner).kind == SymbolKind::Field;
        if self.becomes_machine(owner) || (self.needs_display(owner, &body) && !is_field) {
            return Ok(Vec::new());
        }
        // A lambda written in a generic method is the same story as a local
        // function: it becomes a method of the type, and the method's own
        // parameters are not in scope there unless it declares them.
        let inherited = self.enclosing_method_generics(owner);
        // A static member has no `this` for a lambda to close over, whatever
        // the binder made of the body.
        let owner_instance = !self
            .compilation
            .symbols()
            .get(owner)
            .modifiers
            .contains(Modifiers::STATIC);
        let mut plans = Vec::new();
        for (index, lambda) in body.lambdas.iter().enumerate() {
            if captures_a_variable(lambda) {
                continue;
            }
            if self.goes_to_singleton(&body, owner, index) {
                self.singleton_candidates.push((owner, index));
                continue;
            }
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.lambdas.insert((owner, index), token);
            // Inside a generic local function the lambda reads its type
            // parameters too, and declares them after the method's.
            let mut inherited = inherited.clone();
            inherited.extend(self.function_generics_around(&body, lambda.span));
            if !inherited.is_empty() {
                self.inherited_generics.insert(token, inherited.clone());
            }
            let lambda_name = self.lambda_method_name(&body, owner, index, false);
            self.lambda_names
                .insert((owner, index), lambda_name.clone());
            let instance = lambda.captures_this && owner_instance;
            let source = self.closure_source(MachineKey::Lambda { owner, index }, instance, None);
            plans.push(MethodPlan {
                source,
                token,
                // The name a C# compiler gives one: unspeakable, so nothing
                // written in C# can collide with it.
                name: lambda_name,
                flags: method_attributes::PRIVATE
                    | method_attributes::HIDE_BY_SIG
                    | if instance {
                        0
                    } else {
                        method_attributes::STATIC
                    },
                instance,
                return_type: lambda_return(lambda),
                parameters: lambda
                    .parameters
                    .iter()
                    .map(|local| ParameterPlan {
                        by_ref: body.locals[local.0 as usize].by_ref,
                        symbol: None,
                        name: body.locals[local.0 as usize].name.clone(),
                        ty: body.locals[local.0 as usize].ty.clone(),
                    })
                    .collect(),
                type_parameters: inherited.clone(),
                impl_flags: 0,
                signature: None,
            });
        }
        Ok(plans)
    }

    /// What the method a closure became is the source of: the closure's
    /// body, or — for an `async` one a machine can be built for — the start
    /// of that machine. Where the method lives is remembered either way, for
    /// the machine to find `this` by.
    pub(crate) fn closure_source(
        &mut self,
        key: MachineKey,
        instance: bool,
        hosted: Option<SigType>,
    ) -> MethodSource {
        self.closure_hosts
            .insert(key, ClosureHost { instance, hosted });
        if self.iterated_element(key).is_some() && self.iterator_refusal(key).is_none() {
            self.iterator_closures.push(key);
            return MethodSource::IteratorStart(key);
        }
        if self.is_async_closure(key) && self.async_refusal(key).is_none() {
            self.async_closures.push(key);
            return MethodSource::AsyncStart(key);
        }
        match key {
            MachineKey::Lambda { owner, index } => MethodSource::Lambda { owner, index },
            MachineKey::Function { owner, index } => MethodSource::LocalFunction { owner, index },
            MachineKey::Member(member) => MethodSource::Declared(member),
        }
    }

    /// Whether a member's closures live in a display class of its own.
    ///
    /// A member of an interface with an `out` or `in` type parameter keeps
    /// every local function and every closure over `this` there too, even
    /// where nothing else is captured: the runtime checks the variance of
    /// every method of such an interface, private ones included, and `T1
    /// local(T1 x)` in `I1<out T1>` would take a `T1` in (Roslyn's
    /// `GetEnclosingVariantInterface`). A class has no variance to check.
    fn needs_display(&self, owner: SymbolId, body: &rustlyn_semantics::BoundBody) -> bool {
        needs_display(body)
            || ((!body.local_functions.is_empty()
                || body.lambdas.iter().any(|lambda| lambda.captures_this))
                && self.in_variant_interface(owner))
    }

    /// Whether a member belongs to an interface with a variant type
    /// parameter, or to an interface nested in one.
    fn in_variant_interface(&self, member: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let mut current = self.enclosing_type(member);
        while let Some(ty) = current {
            if symbols.get(ty).type_kind() != Some(TypeKind::Interface) {
                return false;
            }
            let variant = symbols.get(ty).as_named_type().is_some_and(|detail| {
                detail.type_parameters.iter().any(|parameter| {
                    symbols
                        .get(*parameter)
                        .as_type_parameter()
                        .is_some_and(|detail| detail.variance != rustlyn_semantics::Variance::None)
                })
            });
            if variant {
                return true;
            }
            current = symbols
                .get(ty)
                .container
                .filter(|outer| symbols.get(*outer).kind == SymbolKind::NamedType);
        }
        false
    }

    /// Whether a member's body is rewritten into a state machine: an
    /// iterator's or an `async` method's, where the rewrite is built for it.
    pub(crate) fn becomes_machine(&mut self, member: SymbolId) -> bool {
        (self.iterated_element(MachineKey::Member(member)).is_some()
            && self.iterator_refusal(MachineKey::Member(member)).is_none())
            || (self.is_async_method(member)
                && self.async_refusal(MachineKey::Member(member)).is_none())
    }

    /// Makes a state machine the display class of the member it was made
    /// from: every lambda and local function of the body becomes a method of
    /// the machine, and what they capture is read from the fields the machine
    /// already keeps the locals, the parameters and `this` in.
    ///
    /// A machine in a generic type or method is generic itself, and then its
    /// members are named under a construction once every type has a token,
    /// exactly as a display class's are.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn attach_closures(
        &mut self,
        owner: SymbolId,
        plan: &mut TypePlan,
        sig: SigType,
        view: DisplayView,
        arity: usize,
        own: usize,
        next_field: &mut u32,
        next_method: &mut u32,
    ) -> Result<(), EmitError> {
        let Some(body) = self.body_of(owner) else {
            return Ok(());
        };
        if body.lambdas.is_empty() && body.local_functions.is_empty() {
            return Ok(());
        }
        let owner_name = self.compilation.symbols().get(owner).name.clone();
        // A closure written inside a lambda that gets a class of its own
        // lives there, not here.
        let nested = self.nested_display_owners(owner);
        let nested_spans: Vec<TextSpan> = nested
            .iter()
            .filter_map(|outer| self.closure_span(&body, *outer))
            .collect();
        let in_a_nested = |span: TextSpan| {
            nested_spans
                .iter()
                .any(|outer| *outer != span && within(span, *outer))
        };
        // A lambda's parameters are locals of the body too, and the machine
        // has a field for every local — but a parameter is what the lambda
        // is called with, not something kept across a suspension, and the
        // lambda's method reads it from its argument slot.
        let mut view = view;
        for lambda in &body.lambdas {
            for parameter in &lambda.parameters {
                view.locals.remove(parameter);
            }
        }
        // The machine holds the member's parameters; a parameter of a local
        // function that a closure inside it captures — a function nested in
        // the local function, a lambda in it — has to be held too, and gets
        // a field of its own.
        let mut foreign: Vec<SymbolId> = Vec::new();
        let captured_parameters = body
            .lambdas
            .iter()
            .flat_map(|lambda| lambda.captured_parameters.iter().copied())
            .chain(
                body.local_functions
                    .iter()
                    .flat_map(|function| function.captured_parameters.iter().copied()),
            );
        for parameter in captured_parameters {
            if !view.parameters.contains_key(&parameter) && !foreign.contains(&parameter) {
                foreign.push(parameter);
            }
        }
        let mut pending = PendingDisplay {
            owner,
            token: plan.token,
            arity,
            own,
            nested: None,
            hosted: false,
            parent: None,
            generics: None,
            locals: Vec::new(),
            parameters: Vec::new(),
            this: None,
            methods: Vec::new(),
            functions: Vec::new(),
        };
        for (number, parameter) in foreign.iter().enumerate() {
            let name = format!(
                "<{}>P__{number}",
                self.compilation.symbols().get(*parameter).name
            );
            let ty = self.type_of(*parameter);
            let token = Token::new(table::FIELD, *next_field);
            *next_field += 1;
            plan.fields.push(FieldPlan {
                token,
                name: name.clone(),
                ty: ty.clone(),
                flags: field_attributes::PUBLIC,
                symbol: None,
                constant: None,
                sig: None,
            });
            view.parameters.insert(*parameter, token);
            pending.parameters.push((*parameter, name, ty));
        }
        let mut display = DisplayClass {
            inner_sig: sig.clone(),
            sig,
            inside: view.clone(),
            outside: view,
            parent_closure: None,
            generics: Vec::new(),
        };
        for (index, lambda) in body.lambdas.iter().enumerate() {
            if in_a_nested(lambda.span) {
                continue;
            }
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            let name = self.lambda_method_name(&body, owner, index, true);
            self.lambda_names.insert((owner, index), name.clone());
            // A lambda inside a generic local function names that function's
            // parameters, and declares them as its own.
            let function_generics = self.function_generics_around(&body, lambda.span);
            if !function_generics.is_empty() {
                self.lambda_generics
                    .insert((owner, index), function_generics.clone());
            }
            self.lambdas.insert((owner, index), method);
            display.inside.methods.insert(index, method);
            display.outside.methods.insert(index, method);
            pending.methods.push((
                index,
                name.clone(),
                lambda_return(lambda),
                lambda
                    .parameters
                    .iter()
                    .map(|local| {
                        let local = &body.locals[local.0 as usize];
                        // A `ref` parameter is a reference in the signature the
                        // definition is written with, and the reference to the
                        // member has to say the same.
                        if local.by_ref {
                            Type::ByRef(Box::new(local.ty.clone()))
                        } else {
                            local.ty.clone()
                        }
                    })
                    .collect(),
            ));
            let source = self.closure_source(
                MachineKey::Lambda { owner, index },
                true,
                Some(display.sig.clone()),
            );
            plan.methods.push(MethodPlan {
                source,
                token: method,
                name,
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                instance: true,
                return_type: lambda_return(lambda),
                parameters: lambda
                    .parameters
                    .iter()
                    .map(|local| ParameterPlan {
                        by_ref: body.locals[local.0 as usize].by_ref,
                        symbol: None,
                        name: body.locals[local.0 as usize].name.clone(),
                        ty: body.locals[local.0 as usize].ty.clone(),
                    })
                    .collect(),
                type_parameters: function_generics.clone(),
                impl_flags: 0,
                signature: None,
            });
        }
        for (index, function) in body.local_functions.iter().enumerate() {
            if self.function_span(function).is_some_and(in_a_nested)
                || self.dll_import(function.symbol).is_some()
            {
                continue;
            }
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.methods.insert(function.symbol, method);
            display
                .inside
                .local_functions
                .insert(function.symbol, method);
            display
                .outside
                .local_functions
                .insert(function.symbol, method);
            let function_plan = self.plan_local_function(
                owner,
                index,
                function,
                method,
                true,
                Some(display.sig.clone()),
                &owner_name,
            )?;
            pending.functions.push((
                function.symbol,
                function_plan.name.clone(),
                function_plan.return_type.clone(),
                function_plan
                    .parameters
                    .iter()
                    .map(|it| self.pending_parameter_type(it))
                    .collect(),
            ));
            plan.methods.push(MethodPlan {
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                ..function_plan
            });
        }
        self.displays.insert(owner, display);
        if arity > 0 || own > 0 {
            self.display_pending.push(pending);
        }
        Ok(())
    }

    /// Renames the fields a machine's lambdas read, once the machine's own
    /// members are named under its construction.
    ///
    /// A machine in a generic type or method is registered as its lambdas'
    /// display class while it is planned, with definition tokens; inside a
    /// generic type those name nothing the runtime will load through, and
    /// the `MemberRef`s made afterwards have to take their place.
    /// Gives the `<>8__s…` fields of the member's `async` machine their
    /// types: the loop-body classes were planned after the machine, so the
    /// machine's plan named them with a placeholder until now.
    fn name_scope_fields(&mut self, member: SymbolId, plans: &mut [TypePlan]) {
        for plan in plans.iter_mut() {
            let Some(key) = plan.machine.filter(|key| key.owner() == member) else {
                continue;
            };
            let Some(scopes) = self.asyncs.get(&key).map(|plan| plan.scopes.clone()) else {
                continue;
            };
            for (span, token) in scopes {
                let Some(sig) = self
                    .nested_displays
                    .get(&(member, Closure::Scope(span)))
                    .map(|display| display.inner_sig.clone())
                else {
                    continue;
                };
                if let Some(field) = plan.fields.iter_mut().find(|field| field.token == token) {
                    field.sig = Some(sig);
                }
            }
        }
    }

    pub(crate) fn refresh_machine_display(
        &mut self,
        owner: SymbolId,
        constructor: Token,
        locals: &HashMap<LocalId, Token>,
        parameters: &HashMap<SymbolId, Token>,
        this: Option<Token>,
    ) {
        let lambda_parameters: Vec<LocalId> = self
            .body_of(owner)
            .map(|body| {
                body.lambdas
                    .iter()
                    .flat_map(|lambda| lambda.parameters.iter().copied())
                    .collect()
            })
            .unwrap_or_default();
        let Some(display) = self.displays.get_mut(&owner) else {
            return;
        };
        for view in [&mut display.inside, &mut display.outside] {
            view.constructor = constructor;
            view.locals = locals.clone();
            for parameter in &lambda_parameters {
                view.locals.remove(parameter);
            }
            // A parameter of a local function that a closure captured has
            // a field the machine's plan knows nothing of: it stays.
            let mut merged = parameters.clone();
            for (parameter, token) in &view.parameters {
                merged.entry(*parameter).or_insert(*token);
            }
            view.parameters = merged;
            view.this = this;
        }
    }

    /// The type parameters the method holding a lambda or a local function
    /// declares, which a method made for one has to declare too.
    /// The type parameters of every local function of a body that holds
    /// `span`, outermost first.
    pub(crate) fn function_generics_around(
        &self,
        body: &BoundBody,
        span: TextSpan,
    ) -> Vec<SymbolId> {
        let mut around: Vec<(TextSpan, SymbolId)> = body
            .local_functions
            .iter()
            .filter_map(|function| {
                let at = self.function_span(function)?;
                (at.start() <= span.start() && span.end() <= at.end() && at != span)
                    .then_some((at, function.symbol))
            })
            .collect();
        around.sort_by_key(|(at, _)| std::cmp::Reverse(at.length()));
        around
            .into_iter()
            .flat_map(|(_, symbol)| {
                self.compilation
                    .symbols()
                    .get(symbol)
                    .as_method()
                    .map(|detail| detail.type_parameters.clone())
                    .unwrap_or_default()
            })
            .collect()
    }

    fn enclosing_method_generics(&self, owner: SymbolId) -> Vec<SymbolId> {
        self.compilation
            .symbols()
            .get(owner)
            .as_method()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default()
    }

    /// The class that holds what a member's lambdas captured.
    ///
    /// One per member rather than one per scope, which is simpler and right
    /// wherever C# shares the variable. It differs for a `foreach` variable,
    /// which C# makes fresh each iteration; the interpreter shares its frame
    /// and so agrees with this rather than with C#.
    fn plan_display_class(
        &mut self,
        owner: SymbolId,
        enclosing: SymbolId,
        counter: usize,
        next_type: &mut u32,
        next_field: &mut u32,
        next_method: &mut u32,
    ) -> Result<Option<TypePlan>, EmitError> {
        let Some(body) = self.body_of(owner) else {
            return Ok(None);
        };
        // A state machine is its own display class: its lambdas are methods
        // of it, and what they capture is already in its fields. A field
        // initializer has no variables of its own to keep, and no method of
        // its own to make a class in: its closures capture at most each
        // other's parameters, which nested classes hold.
        // A field initializer that declares a variable a lambda captures —
        // `F = Take(out var x) && Run(() => x)` — does need one, made in
        // the constructor that runs the initializer.
        let captures_own_local = body
            .lambdas
            .iter()
            .any(|lambda| !lambda.captured.is_empty());
        if !self.needs_display(owner, &body)
            || self.becomes_machine(owner)
            || (matches!(
                self.compilation.symbols().get(owner).kind,
                SymbolKind::Field | SymbolKind::Property
            ) && !captures_own_local)
        {
            return Ok(None);
        }
        // Every lambda of the member becomes a method of the class, not only
        // the ones that captured: one that captured nothing is still written
        // inside a method whose locals now live here, and a lambda inside a
        // local function reads them through the same fields. The exception
        // is a closure written inside a lambda that gets a class of its own:
        // that class is where it lives.
        let nested = self.nested_display_owners(owner);
        let nested_spans: Vec<TextSpan> = nested
            .iter()
            .filter_map(|outer| self.closure_span(&body, *outer))
            .collect();
        // Strictly inside: the owner of a nested class is not inside its
        // own class.
        let in_a_nested = |span: TextSpan| {
            nested_spans
                .iter()
                .any(|outer| *outer != span && within(span, *outer))
        };
        let nested_functions: Vec<SymbolId> = nested
            .iter()
            .filter_map(|outer| match outer {
                Closure::Function(index) => Some(body.local_functions[*index].symbol),
                Closure::Lambda(_) | Closure::Scope(_) => None,
            })
            .collect();
        // One that captures nothing at all goes to the type's `<>c`, as it
        // would from a member with no class.
        let mut capturing: Vec<usize> = Vec::new();
        for index in 0..body.lambdas.len() {
            if in_a_nested(body.lambdas[index].span) {
                continue;
            }
            if self.goes_to_singleton(&body, owner, index) {
                self.singleton_candidates.push((owner, index));
            } else {
                capturing.push(index);
            }
        }
        let functions: Vec<usize> = (0..body.local_functions.len())
            .filter(|index| {
                !self
                    .function_span(&body.local_functions[*index])
                    .is_some_and(in_a_nested)
                    && self
                        .dll_import(body.local_functions[*index].symbol)
                        .is_none()
            })
            .collect();

        // Every capture of every lambda goes in one class, so that two lambdas
        // over the same variable share it — which is what C# promises. A
        // variable declared inside a lambda with a class of its own lives
        // there instead.
        let mut locals: Vec<LocalId> = Vec::new();
        let mut parameters: Vec<SymbolId> = Vec::new();
        let mut needs_this = false;
        let mut take = |lambda_locals: &[LocalId],
                        lambda_parameters: &[SymbolId],
                        this: bool,
                        locals: &mut Vec<LocalId>,
                        parameters: &mut Vec<SymbolId>| {
            for local in lambda_locals {
                if !locals.contains(local) && !in_a_nested(body.locals[local.0 as usize].span) {
                    locals.push(*local);
                }
            }
            for parameter in lambda_parameters {
                // A parameter of a local function with a class of its own
                // lives in that class.
                let of_nested = self
                    .compilation
                    .symbols()
                    .get(*parameter)
                    .container
                    .is_some_and(|container| nested_functions.contains(&container));
                if !parameters.contains(parameter) && !of_nested {
                    parameters.push(*parameter);
                }
            }
            needs_this |= this;
        };
        for index in &capturing {
            let lambda = &body.lambdas[*index];
            take(
                &lambda.captured,
                &lambda.captured_parameters,
                lambda.captures_this,
                &mut locals,
                &mut parameters,
            );
        }
        for index in &functions {
            let function = &body.local_functions[*index];
            take(
                &function.captured,
                &function.captured_parameters,
                function.captures_this,
                &mut locals,
                &mut parameters,
            );
        }
        // A closure inside a nested class may still read the member's
        // variables and `this`: it reaches them through the class's parent,
        // which is this one, so they have to be here too.
        for span in nested_spans.iter().copied() {
            for lambda in body
                .lambdas
                .iter()
                .filter(|lambda| within(lambda.span, span))
            {
                take(
                    &lambda.captured,
                    &lambda.captured_parameters,
                    lambda.captures_this,
                    &mut locals,
                    &mut parameters,
                );
            }
            for function in &body.local_functions {
                if self
                    .function_span(function)
                    .is_some_and(|it| within(it, span))
                {
                    take(
                        &function.captured,
                        &function.captured_parameters,
                        function.captures_this,
                        &mut locals,
                        &mut parameters,
                    );
                }
            }
        }

        let token = Token::new(table::TYPE_DEF, *next_type);
        *next_type += 1;
        let symbols = self.compilation.symbols();
        let owner_name = symbols.get(owner).name.clone();

        // A display class inside `Pool<T>` carries `T` as a parameter of its
        // own: the locals it holds are of that type, and there is no naming
        // them otherwise.
        let inherited = self
            .compilation
            .symbols()
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        // A lambda in `Held<T>(T value)` captures a value of the method's own
        // `T`, and a field has to name it: the class declares it too, after
        // whatever the enclosing type gave it.
        let own = self
            .compilation
            .symbols()
            .get(owner)
            .as_method()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        let coded = type_def_or_ref(0, token.0 & 0x00FF_FFFF);
        let sig = if inherited.is_empty() && own.is_empty() {
            SigType::Named {
                value_type: false,
                coded,
            }
        } else {
            SigType::Constructed {
                value_type: false,
                coded,
                // As the method that makes one names it: the enclosing type's
                // parameters are the type's, and its own are the method's.
                arguments: (0..inherited.len() as u32)
                    .map(SigType::TypeParameter)
                    .chain((0..own.len() as u32).map(SigType::MethodTypeParameter))
                    .collect(),
            }
        };
        let mut pending = PendingDisplay {
            owner,
            token,
            arity: inherited.len(),
            own: own.len(),
            nested: None,
            hosted: false,
            parent: None,
            generics: None,
            locals: Vec::new(),
            parameters: Vec::new(),
            this: None,
            methods: Vec::new(),
            functions: Vec::new(),
        };

        let mut fields = Vec::new();
        let inner_sig = if inherited.is_empty() && own.is_empty() {
            sig.clone()
        } else {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..(inherited.len() + own.len()) as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            }
        };
        let mut display = DisplayClass {
            sig,
            inside: DisplayView::default(),
            outside: DisplayView::default(),
            inner_sig,
            parent_closure: None,
            generics: inherited.iter().chain(own.iter()).copied().collect(),
        };
        let mut field = |fields: &mut Vec<FieldPlan>, name: String, ty: Type| {
            let token = Token::new(table::FIELD, *next_field);
            *next_field += 1;
            fields.push(FieldPlan {
                token,
                name,
                ty,
                flags: field_attributes::PUBLIC,
                symbol: None,
                constant: None,
                sig: None,
            });
            token
        };
        for local in &locals {
            let symbol = &body.locals[local.0 as usize];
            let (name, ty) = (symbol.name.clone(), symbol.ty.clone());
            let token = field(&mut fields, name.clone(), ty.clone());
            display.inside.locals.insert(*local, token);
            display.outside.locals.insert(*local, token);
            pending.locals.push((*local, name, ty));
        }
        for parameter in &parameters {
            let name = self.compilation.symbols().get(*parameter).name.clone();
            let ty = self.type_of(*parameter);
            let token = field(&mut fields, name.clone(), ty.clone());
            display.inside.parameters.insert(*parameter, token);
            display.outside.parameters.insert(*parameter, token);
            pending.parameters.push((*parameter, name, ty));
        }
        if needs_this {
            let ty = self.binder.self_type(enclosing);
            let token = field(&mut fields, "<>4__this".to_string(), ty.clone());
            display.inside.this = Some(token);
            display.outside.this = Some(token);
            pending.this = Some(ty);
        }

        let mut methods = Vec::new();
        let constructor = Token::new(table::METHOD_DEF, *next_method);
        *next_method += 1;
        display.inside.constructor = constructor;
        display.outside.constructor = constructor;
        methods.push(MethodPlan {
            source: MethodSource::DisplayConstructor,
            token: constructor,
            name: ".ctor".to_string(),
            flags: method_attributes::PUBLIC
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
                | method_attributes::RT_SPECIAL_NAME,
            instance: true,
            return_type: Type::Void,
            parameters: Vec::new(),
            type_parameters: Vec::new(),
            impl_flags: 0,
            signature: None,
        });

        for index in capturing {
            let lambda = &body.lambdas[index];
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            let name = self.lambda_method_name(&body, owner, index, true);
            self.lambda_names.insert((owner, index), name.clone());
            // A lambda inside a generic local function names that function's
            // parameters, and declares them as its own.
            let function_generics = self.function_generics_around(&body, lambda.span);
            if !function_generics.is_empty() {
                self.lambda_generics
                    .insert((owner, index), function_generics.clone());
            }
            self.lambdas.insert((owner, index), method);
            display.inside.methods.insert(index, method);
            display.outside.methods.insert(index, method);
            pending.methods.push((
                index,
                name.clone(),
                lambda_return(lambda),
                lambda
                    .parameters
                    .iter()
                    .map(|local| {
                        let local = &body.locals[local.0 as usize];
                        // A `ref` parameter is a reference in the signature the
                        // definition is written with, and the reference to the
                        // member has to say the same.
                        if local.by_ref {
                            Type::ByRef(Box::new(local.ty.clone()))
                        } else {
                            local.ty.clone()
                        }
                    })
                    .collect(),
            ));
            let source = self.closure_source(
                MachineKey::Lambda { owner, index },
                true,
                Some(display.inner_sig.clone()),
            );
            methods.push(MethodPlan {
                source,
                token: method,
                name,
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                instance: true,
                return_type: lambda_return(lambda),
                parameters: lambda
                    .parameters
                    .iter()
                    .map(|local| ParameterPlan {
                        by_ref: body.locals[local.0 as usize].by_ref,
                        symbol: None,
                        name: body.locals[local.0 as usize].name.clone(),
                        ty: body.locals[local.0 as usize].ty.clone(),
                    })
                    .collect(),
                type_parameters: function_generics.clone(),
                impl_flags: 0,
                signature: None,
            });
        }

        // A local function of the member is a method of the class too: what
        // it reads of the method around it is in these fields, and reaching
        // them is the whole reason the class exists.
        for index in functions {
            let function = &body.local_functions[index];
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.methods.insert(function.symbol, method);
            display
                .inside
                .local_functions
                .insert(function.symbol, method);
            display
                .outside
                .local_functions
                .insert(function.symbol, method);
            let mut plan = self.plan_local_function(
                owner,
                index,
                function,
                method,
                true,
                Some(display.inner_sig.clone()),
                &owner_name,
            )?;
            self.declare_functions_around(&body, function, method, &display.generics, &mut plan);
            pending.functions.push((
                function.symbol,
                plan.name.clone(),
                plan.return_type.clone(),
                plan.parameters
                    .iter()
                    .map(|it| self.pending_parameter_type(it))
                    .collect(),
            ));
            methods.push(MethodPlan {
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                ..plan
            });
        }

        self.displays.insert(owner, display);
        if pending.arity > 0 || pending.own > 0 {
            self.display_pending.push(pending);
        }
        let _ = counter;
        Ok(Some(TypePlan {
            symbol: enclosing,
            token,
            fields,
            methods,
            properties: Vec::new(),
            display: Some(owner),
            iterator: None,
            machine: None,
            nested: None,
        }))
    }

    /// The lambdas of a member whose parameters or locals a closure inside
    /// them captures. `a => b => a + b` has the inner lambda reading `a`,
    /// which the outer one is called with afresh each time: it needs a class
    /// of its own, made when it runs, the way the member's is made when the
    /// member runs.
    pub(crate) fn nested_display_owners(&mut self, owner: SymbolId) -> Vec<Closure> {
        let Some(body) = self.body_of(owner) else {
            return Vec::new();
        };
        // An iterator's `MoveNext` keeps no local alive across a `yield`,
        // and has no field for a class made each time round either; an
        // `async` machine keeps one (`<>8__s…`), so its loops get theirs.
        let is_iterator = self.iterated_element(MachineKey::Member(owner)).is_some()
            && self.iterator_refusal(MachineKey::Member(owner)).is_none();
        let symbols = self.compilation.symbols();
        let declared_inside =
            |local: &LocalId, span: TextSpan| within(body.locals[local.0 as usize].span, span);
        // Whether any closure written inside `span`, other than the owner
        // itself, captures a local declared there or a parameter of
        // `function`.
        let captured_inside = |span: TextSpan, function: Option<SymbolId>| {
            body.lambdas.iter().any(|lambda| {
                lambda.span != span
                    && within(lambda.span, span)
                    && (lambda
                        .captured
                        .iter()
                        .any(|local| declared_inside(local, span))
                        || lambda.captured_parameters.iter().any(|parameter| {
                            function.is_some() && symbols.get(*parameter).container == function
                        }))
            }) || body.local_functions.iter().any(|inner| {
                let inner_span = self.function_span(inner);
                inner_span.is_some_and(|it| it != span && within(it, span))
                    && (inner
                        .captured
                        .iter()
                        .any(|local| declared_inside(local, span))
                        || inner.captured_parameters.iter().any(|parameter| {
                            function.is_some() && symbols.get(*parameter).container == function
                        }))
            })
        };
        let mut owners: Vec<Closure> = (0..body.lambdas.len())
            .filter(|outer| captured_inside(body.lambdas[*outer].span, None))
            .map(Closure::Lambda)
            .collect();
        // A local function whose own variables a closure inside it captures
        // needs a class per call, the way a lambda does: it may be running
        // several times at once — recursively — and each call's variables
        // are its own.
        owners.extend(
            (0..body.local_functions.len())
                .filter(|index| {
                    let function = &body.local_functions[*index];
                    self.function_span(function)
                        .is_some_and(|span| captured_inside(span, Some(function.symbol)))
                })
                .map(Closure::Function),
        );
        // A loop body whose variables a closure captures gets a class made
        // afresh each time round (§12.19.6 for `foreach`; a `for` shares its
        // own variables and keeps only the body's here). One level only for
        // now: a loop inside another owner, or holding one, keeps the
        // member's class.
        if !is_iterator {
            let mut scopes = Vec::new();
            for statement in &body.statements {
                loop_scopes(statement, &mut scopes);
            }
            for lambda in &body.lambdas {
                loop_scopes(&lambda.body, &mut scopes);
            }
            for function in &body.local_functions {
                loop_scopes(&function.body, &mut scopes);
            }
            let other_spans: Vec<TextSpan> = owners
                .iter()
                .filter_map(|outer| self.closure_span(&body, *outer))
                .collect();
            let candidates: Vec<TextSpan> = scopes
                .iter()
                .copied()
                .filter(|span| captured_inside(*span, None))
                .collect();
            for span in &candidates {
                let overlaps = |other: &TextSpan| {
                    *other != *span && (within(*other, *span) || within(*span, *other))
                };
                if other_spans.iter().any(overlaps) || candidates.iter().any(overlaps) {
                    continue;
                }
                owners.push(Closure::Scope(*span));
            }
        }
        // Outer closures first: a nested class is parented to the class of
        // the closure around it, which has to be planned before it.
        owners.sort_by_key(|closure| {
            let span = self.closure_span(&body, *closure);
            (
                span.map_or(0, TextSpan::start),
                std::cmp::Reverse(span.map_or(0, TextSpan::length)),
            )
        });
        owners
    }

    /// Where a closure was written: a lambda's span, or a local function's.
    fn closure_span(
        &self,
        body: &rustlyn_semantics::BoundBody,
        closure: Closure,
    ) -> Option<TextSpan> {
        match closure {
            Closure::Lambda(index) => body.lambdas.get(index).map(|lambda| lambda.span),
            Closure::Function(index) => body
                .local_functions
                .get(index)
                .and_then(|function| self.function_span(function)),
            Closure::Scope(span) => Some(span),
        }
    }

    /// Where a local function was written.
    fn function_span(&self, function: &rustlyn_semantics::BoundLocalFunction) -> Option<TextSpan> {
        self.compilation
            .declaration_node(function.symbol)
            .map(|node| node.span())
    }

    /// A local function inside a generic local function names that one's
    /// parameters too. As a method of a closure class it declares them in
    /// front of its own, unless the class declares them already, and every
    /// call names them.
    fn declare_functions_around(
        &mut self,
        body: &rustlyn_semantics::BoundBody,
        function: &rustlyn_semantics::BoundLocalFunction,
        method: Token,
        declared: &[SymbolId],
        plan: &mut MethodPlan,
    ) {
        let Some(span) = self.function_span(function) else {
            return;
        };
        let around: Vec<SymbolId> = self
            .function_generics_around(body, span)
            .into_iter()
            .filter(|parameter| !declared.contains(parameter))
            .collect();
        if around.is_empty() {
            return;
        }
        self.inherited_generics.insert(method, around.clone());
        let mut all = around;
        all.extend(plan.type_parameters.iter().copied());
        plan.type_parameters = all;
    }

    /// The number Roslyn gives each lambda and local function of a body:
    /// those written directly in a scope first, in order, then those inside
    /// each of them (`VisitNestedFunctions` over its scope tree).
    pub(crate) fn closure_ordinal(
        &self,
        body: &rustlyn_semantics::BoundBody,
        closure: Closure,
    ) -> usize {
        let closures: Vec<(Closure, TextSpan)> = (0..body.lambdas.len())
            .map(Closure::Lambda)
            .chain((0..body.local_functions.len()).map(Closure::Function))
            .filter_map(|closure| Some((closure, self.closure_span(body, closure)?)))
            .collect();
        let parent = |span: TextSpan| {
            closures
                .iter()
                .filter(|(_, outer)| *outer != span && within(span, *outer))
                .min_by_key(|(_, outer)| outer.length())
                .map(|(_, outer)| *outer)
        };
        // Each closure's parent once, and the closures by parent: a method
        // with hundreds of lambdas asked this for each of them.
        let mut by_parent: HashMap<Option<TextSpan>, Vec<(Closure, TextSpan)>> = HashMap::new();
        for &(closure, span) in &closures {
            by_parent
                .entry(parent(span))
                .or_default()
                .push((closure, span));
        }
        let mut order: Vec<Closure> = Vec::new();
        let mut pending: Vec<Option<TextSpan>> = vec![None];
        while let Some(scope) = pending.pop() {
            let mut children: Vec<(Closure, TextSpan)> =
                by_parent.get(&scope).cloned().unwrap_or_default();
            children.sort_by_key(|(_, span)| span.start());
            order.extend(children.iter().map(|(closure, _)| *closure));
            // Depth first, in order: the stack takes them reversed.
            pending.extend(children.iter().rev().map(|(_, span)| Some(*span)));
        }
        order
            .iter()
            .position(|it| *it == closure)
            .unwrap_or(order.len())
    }

    /// How a member is named in the names of what its body is lowered to:
    /// an accessor's body is its property's here, and a field's initializer
    /// runs in a constructor.
    fn closure_owner_name(&self, owner: SymbolId) -> String {
        let symbol = self.compilation.symbols().get(owner);
        match symbol.kind {
            SymbolKind::Field if symbol.modifiers.contains(Modifiers::STATIC) => {
                ".cctor".to_string()
            }
            SymbolKind::Field => ".ctor".to_string(),
            _ => self.metadata_method_name(owner),
        }
    }

    /// The name a method is defined under: its own, or for an explicit
    /// implementation the interface's in front of it as Roslyn writes it —
    /// `System.IDisposable.Dispose`, `N.I.get_P` for an accessor of `N.I.P`.
    /// A property stands for its getter, whose body a `=> e` is.
    pub(crate) fn metadata_method_name(&self, member: SymbolId) -> String {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let bare = |name: &str| name.rsplit('.').next().unwrap_or_default().to_string();
        let explicit = |of: SymbolId| {
            (!symbols.get(of).modifiers.contains(Modifiers::STATIC))
                .then(|| self.explicit_interface(of))
                .flatten()
                .map(|interface| self.explicit_prefix(&interface))
        };
        match symbol.kind {
            SymbolKind::Property => match explicit(member) {
                Some(prefix) => format!("{prefix}.get_{}", bare(&symbol.name)),
                None => format!("get_{}", symbol.name),
            },
            _ => {
                // An accessor is named `get_`, `set_`, `add_` or `remove_`
                // and its property's or event's name.
                if let Some(container) = symbol.container
                    && matches!(
                        symbols.get(container).kind,
                        SymbolKind::Property | SymbolKind::Event
                    )
                {
                    if let Some(prefix) = explicit(container)
                        && let Some((kind, _)) = symbol.name.split_once('_')
                    {
                        return format!("{prefix}.{kind}_{}", bare(&symbols.get(container).name));
                    }
                    return symbol.name.clone();
                }
                match explicit(member) {
                    Some(prefix) => format!("{prefix}.{}", bare(&symbol.name)),
                    None => symbol.name.clone(),
                }
            }
        }
    }

    /// The name of a lambda's method (Roslyn's `MakeLambdaMethodName`):
    /// `<M>b__0_1`, the member's number and the lambda's, where it is a
    /// method of the type or of the shared `<>c`, and `<M>b__1` in a class
    /// made for the member alone.
    pub(crate) fn lambda_method_name(
        &self,
        body: &rustlyn_semantics::BoundBody,
        owner: SymbolId,
        index: usize,
        in_display: bool,
    ) -> String {
        let ordinal = self.closure_ordinal(body, Closure::Lambda(index));
        let name = self.closure_owner_name(owner);
        if in_display {
            format!("<{name}>b__{ordinal}")
        } else {
            format!("<{name}>b__{}_{ordinal}", self.method_ordinal(owner))
        }
    }

    /// The same for a local function (`MakeLocalFunctionName`): `<M>g__F|0_1`.
    pub(crate) fn local_function_name(
        &self,
        body: &rustlyn_semantics::BoundBody,
        owner: SymbolId,
        index: usize,
        in_display: bool,
    ) -> String {
        let ordinal = self.closure_ordinal(body, Closure::Function(index));
        let name = self.closure_owner_name(owner);
        let function = &self
            .compilation
            .symbols()
            .get(body.local_functions[index].symbol)
            .name;
        if in_display {
            format!("<{name}>g__{function}|{ordinal}")
        } else {
            format!(
                "<{name}>g__{function}|{}_{ordinal}",
                self.method_ordinal(owner)
            )
        }
    }

    /// The member number of the method a body is compiled as. Roslyn
    /// compiles a field's initializer into each constructor and numbers its
    /// lambdas by the constructor's; here it is compiled once, and takes the
    /// field's own number, which no other member's names can collide with.
    pub(crate) fn method_ordinal(&self, owner: SymbolId) -> usize {
        self.member_ordinal(owner)
    }

    /// Where a member stands among its type's members, the way Roslyn numbers
    /// them for the names of what the compiler makes from its body
    /// (`<M>b__0_1`, `<M>g__F|0_0`, `<>c__DisplayClass0_0`): in the order
    /// they were written, accessors and backing fields counted, and the
    /// constructor the language supplies first.
    pub(crate) fn member_ordinal(&self, member: SymbolId) -> usize {
        let symbols = self.compilation.symbols();
        // An accessor's body is bound as its property's, and a field's
        // initializer runs in a constructor: the member itself stands in.
        let Some(container) = symbols.get(member).container else {
            return 0;
        };
        // An accessor is counted with its property or event: the rows of
        // the property, its backing field, then `get` before `set`.
        if matches!(
            symbols.get(container).kind,
            SymbolKind::Property | SymbolKind::Event
        ) {
            let is_second = symbols.get(member).name.starts_with("set_")
                || symbols.get(member).name.starts_with("remove_");
            let first_exists = symbols
                .get(container)
                .as_property()
                .is_none_or(|detail| detail.has_get);
            return self.member_ordinal(container) + usize::from(is_second && first_exists);
        }
        let ty = container;
        let position = |symbol: SymbolId| {
            symbols
                .get(symbol)
                .locations
                .first()
                .map_or((usize::MAX, 0), |location| {
                    (location.tree, location.span.start() as usize)
                })
        };
        // Where each member sorts, how many rows it stands for, and where
        // among them the body is: an accessor after its property and its
        // backing field.
        let mut entries: Vec<((usize, usize), SymbolId, usize, usize)> = Vec::new();
        for &id in &symbols.get(ty).members {
            let symbol = symbols.get(id);
            if symbol.kind == SymbolKind::TypeParameter {
                continue;
            }
            let count = match &symbol.detail {
                rustlyn_semantics::Detail::Property(detail) => {
                    let auto = detail.getter.is_none()
                        && detail.setter.is_none()
                        && !symbol.modifiers.contains(Modifiers::ABSTRACT)
                        && !symbol.modifiers.contains(Modifiers::EXTERN)
                        && symbols.get(ty).type_kind() != Some(TypeKind::Interface)
                        && self.compilation.declaration_node(id).is_some_and(|node| {
                            node.descendants().any(|accessor| {
                                matches!(
                                    accessor.kind(),
                                    SyntaxKind::GetAccessorDeclaration
                                        | SyntaxKind::SetAccessorDeclaration
                                        | SyntaxKind::InitAccessorDeclaration
                                ) && accessor.child_of_kind(SyntaxKind::Block).is_none()
                                    && accessor
                                        .child_of_kind(SyntaxKind::ArrowExpressionClause)
                                        .is_none()
                            })
                        });
                    let backing = usize::from(auto || detail.backing_field.is_some());
                    entries.push((
                        position(id),
                        id,
                        1 + backing
                            + usize::from(detail.has_get)
                            + usize::from(detail.has_set || detail.has_init),
                        1 + backing,
                    ));
                    continue;
                }
                rustlyn_semantics::Detail::Event(_) => {
                    entries.push((position(id), id, 3, 1));
                    continue;
                }
                // The constructor nobody wrote has no place in the source,
                // and sorts after everything that has one.
                rustlyn_semantics::Detail::Method(detail)
                    if detail.method_kind == rustlyn_semantics::MethodKind::Constructor
                        && self.compilation.declaration_node(id).is_none_or(|node| {
                            node.kind() != SyntaxKind::ConstructorDeclaration
                        }) =>
                {
                    entries.push(((usize::MAX, usize::MAX), id, 1, 0));
                    continue;
                }
                _ => 1,
            };
            entries.push((position(id), id, count, 0));
        }
        entries.sort_by_key(|(at, _, _, _)| *at);
        let mut ordinal = 0;
        for (_, id, count, offset) in entries {
            if id == member {
                return ordinal + offset;
            }
            ordinal += count;
        }
        ordinal
    }

    /// The type parameters the code that makes a nested closure class can
    /// name: those its class declares, and those its method declares.
    ///
    /// A lambda's or a local function's class is made on entry to it; a
    /// loop body's by the closure the loop is written in, or by the member
    /// itself where it is written in none.
    fn maker_generics(
        &self,
        owner: SymbolId,
        body: &rustlyn_semantics::BoundBody,
        outer: Closure,
        enclosing: SymbolId,
        machine: bool,
    ) -> (Vec<SymbolId>, Vec<SymbolId>) {
        let symbols = self.compilation.symbols();
        let maker = match outer {
            Closure::Lambda(_) | Closure::Function(_) => Some(outer),
            Closure::Scope(span) => {
                let lambdas = (0..body.lambdas.len()).map(Closure::Lambda);
                let functions = (0..body.local_functions.len()).map(Closure::Function);
                lambdas
                    .chain(functions)
                    .filter_map(|closure| Some((closure, self.closure_span(body, closure)?)))
                    .filter(|(_, at)| *at != span && within(span, *at))
                    .min_by_key(|(_, at)| at.length())
                    .map(|(closure, _)| closure)
            }
        };
        let type_generics = symbols
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        match maker {
            Some(Closure::Lambda(index)) => {
                let own = self
                    .lambda_generics
                    .get(&(owner, index))
                    .cloned()
                    .unwrap_or_default();
                match self.home_of_lambda(owner, index) {
                    Some(home) if !home.generics.is_empty() => (home.generics, own),
                    _ => {
                        let mut method = self.enclosing_method_generics(owner);
                        method.extend(own);
                        (type_generics, method)
                    }
                }
            }
            Some(Closure::Function(index)) => {
                let symbol = body.local_functions[index].symbol;
                let own = symbols
                    .get(symbol)
                    .as_method()
                    .map(|detail| detail.type_parameters.clone())
                    .unwrap_or_default();
                match self.home_of_function(owner, symbol) {
                    Some(home) if !home.generics.is_empty() => (home.generics, own),
                    _ => {
                        let mut method = self
                            .methods
                            .get(&symbol)
                            .and_then(|token| self.inherited_generics.get(token))
                            .cloned()
                            .unwrap_or_default();
                        method.extend(own);
                        (type_generics, method)
                    }
                }
            }
            // The member itself makes the class — unless it became a state
            // machine, whose `MoveNext` does, declaring nothing of its own:
            // there the member's parameters are the machine's, after the
            // type's, as the machine declares them.
            _ if machine => {
                let mut all = type_generics;
                all.extend(self.enclosing_method_generics(owner));
                (all, Vec::new())
            }
            _ => (type_generics, self.enclosing_method_generics(owner)),
        }
    }

    /// Plans the display class of one lambda of a member: the class its
    /// parameters and locals live in when a closure inside it captures them,
    /// with the closures as its methods and the member's class as its parent.
    #[allow(clippy::too_many_arguments)]
    fn plan_nested_display(
        &mut self,
        owner: SymbolId,
        outer: Closure,
        enclosing: SymbolId,
        next_type: &mut u32,
        next_field: &mut u32,
        next_method: &mut u32,
    ) -> Result<Option<TypePlan>, EmitError> {
        let Some(body) = self.body_of(owner) else {
            return Ok(None);
        };
        let Some(span) = self.closure_span(&body, outer) else {
            return Ok(None);
        };
        // The function whose class this is, whose parameters its closures
        // may capture.
        let owning_function = match outer {
            Closure::Function(index) => Some(body.local_functions[index].symbol),
            Closure::Lambda(_) | Closure::Scope(_) => None,
        };
        // A closure inside this one that has a class of its own keeps its
        // variables and its closures there: `x => y => z => x + y + z`
        // holds `y` in the middle lambda's class alone, and `z` is a method
        // of that class, reaching `x` through its parent.
        let inner: Vec<TextSpan> = self
            .nested_display_owners(owner)
            .into_iter()
            .filter(|closure| *closure != outer)
            .filter_map(|closure| self.closure_span(&body, closure))
            .filter(|it| *it != span && within(*it, span))
            .collect();
        // Strictly inside: the inner closure itself is a method of this
        // class, and only what it holds is not.
        let in_inner = |at: TextSpan| inner.iter().any(|it| at != *it && within(at, *it));
        let lambdas: Vec<usize> = (0..body.lambdas.len())
            .filter(|index| {
                outer != Closure::Lambda(*index)
                    && within(body.lambdas[*index].span, span)
                    && !in_inner(body.lambdas[*index].span)
            })
            .collect();
        let functions: Vec<usize> = (0..body.local_functions.len())
            .filter(|index| {
                outer != Closure::Function(*index)
                    && self
                        .function_span(&body.local_functions[*index])
                        .is_some_and(|it| within(it, span) && !in_inner(it))
                    && self
                        .dll_import(body.local_functions[*index].symbol)
                        .is_none()
            })
            .collect();
        let mut locals: Vec<LocalId> = Vec::new();
        let mut parameters: Vec<SymbolId> = Vec::new();
        let mut captures_this = false;
        {
            let symbols = self.compilation.symbols();
            let mut take = |captured: &[LocalId], captured_parameters: &[SymbolId], this: bool| {
                for local in captured {
                    let at = body.locals[local.0 as usize].span;
                    if within(at, span) && !in_inner(at) && !locals.contains(local) {
                        locals.push(*local);
                    }
                }
                for parameter in captured_parameters {
                    if owning_function.is_some()
                        && symbols.get(*parameter).container == owning_function
                        && !parameters.contains(parameter)
                    {
                        parameters.push(*parameter);
                    }
                }
                captures_this |= this;
            };
            for index in &lambdas {
                let lambda = &body.lambdas[*index];
                take(
                    &lambda.captured,
                    &lambda.captured_parameters,
                    lambda.captures_this,
                );
            }
            for index in &functions {
                let function = &body.local_functions[*index];
                take(
                    &function.captured,
                    &function.captured_parameters,
                    function.captures_this,
                );
            }
        }
        // The parent is the class the closure around this one has, where it
        // has one — `x => y => z => x + y + z` keeps `y` in a class whose
        // parent holds `x` — and the member's class otherwise: the outer
        // lambda is a method of it, and what the closures read of the member
        // is there. Without either, `this` is kept here.
        let enclosing_owner = self
            .nested_display_owners(owner)
            .into_iter()
            .filter(|closure| *closure != outer)
            .filter_map(|closure| self.closure_span(&body, closure).map(|it| (closure, it)))
            .filter(|(_, it)| *it != span && within(span, *it))
            .max_by_key(|(_, it)| it.start())
            .map(|(closure, _)| closure);
        // The member's class is the parent only where the outer closure is
        // a method of it: a lambda that captured nothing is a method of the
        // type, and has no class of the member's to hand down.
        let hosted_by_member = match outer {
            Closure::Lambda(index) => self
                .displays
                .get(&owner)
                .is_some_and(|display| display.inside.methods.contains_key(&index)),
            Closure::Function(index) => {
                let symbol = body.local_functions[index].symbol;
                self.displays
                    .get(&owner)
                    .is_some_and(|display| display.inside.local_functions.contains_key(&symbol))
            }
            Closure::Scope(_) => true,
        };
        let parent = enclosing_owner
            .and_then(|closure| self.nested_displays.get(&(owner, closure)).cloned())
            .or_else(|| {
                hosted_by_member
                    .then(|| self.displays.get(&owner).cloned())
                    .flatten()
            });
        let needs_this = parent.is_none() && captures_this;

        let token = Token::new(table::TYPE_DEF, *next_type);
        *next_type += 1;
        let symbols = self.compilation.symbols();
        let owner_name = symbols.get(owner).name.clone();
        let inherited = symbols
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        let own = symbols
            .get(owner)
            .as_method()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        // Inside a generic local function the class holds values of that
        // function's parameters — and of those of the functions around it —
        // and declares them after the member's: `L<T2>(T2 t2)` whose `t2` a
        // closure captures keeps it in a field of type `T2`.
        let mut extra = self.function_generics_around(&body, span);
        if let Some(function) = owning_function {
            extra.extend(
                symbols
                    .get(function)
                    .as_method()
                    .map(|detail| detail.type_parameters.clone())
                    .unwrap_or_default(),
            );
        }
        let generics: Vec<SymbolId> = inherited
            .iter()
            .chain(own.iter())
            .chain(extra.iter())
            .copied()
            .collect();
        let coded = type_def_or_ref(0, token.0 & 0x00FF_FFFF);
        let generic = !generics.is_empty();
        let inner_sig = if generic {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..generics.len() as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            }
        } else {
            SigType::Named {
                value_type: false,
                coded,
            }
        };
        // The class is made by the code of the closure it belongs to — for a
        // loop body, of the closure the loop is written in, or the member —
        // and that code names each parameter the way its own method does:
        // one its class declares is `!n`, one the method declares is `!!n`.
        let hosted = parent.is_some();
        let machine = self.becomes_machine(owner);
        let (maker_class, maker_method) =
            self.maker_generics(owner, &body, outer, enclosing, machine);
        let outer_arguments: Vec<SigType> = generics
            .iter()
            .map(|parameter| {
                if let Some(at) = maker_class.iter().position(|it| it == parameter) {
                    Ok(SigType::TypeParameter(at as u32))
                } else if let Some(at) = maker_method.iter().position(|it| it == parameter) {
                    Ok(SigType::MethodTypeParameter(at as u32))
                } else {
                    Err(EmitError::new(format!(
                        "a closure class over `{}`, which the code that makes it cannot name",
                        self.compilation.symbols().get(*parameter).name
                    )))
                }
            })
            .collect::<Result<_, _>>()?;
        let sig = if generic {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: outer_arguments.clone(),
            }
        } else {
            inner_sig.clone()
        };
        let mut pending = PendingDisplay {
            owner,
            token,
            arity: inherited.len(),
            own: own.len(),
            nested: Some(outer),
            hosted,
            parent: parent.as_ref().map(|it| it.inner_sig.clone()),
            generics: Some((generics.clone(), outer_arguments)),
            locals: Vec::new(),
            parameters: Vec::new(),
            this: None,
            methods: Vec::new(),
            functions: Vec::new(),
        };
        let mut fields = Vec::new();
        let mut display = DisplayClass {
            sig,
            inside: DisplayView::default(),
            outside: DisplayView::default(),
            inner_sig: inner_sig.clone(),
            parent_closure: enclosing_owner,
            generics,
        };
        let mut field =
            |fields: &mut Vec<FieldPlan>, name: String, ty: Type, sig: Option<SigType>| {
                let token = Token::new(table::FIELD, *next_field);
                *next_field += 1;
                fields.push(FieldPlan {
                    token,
                    name,
                    ty,
                    flags: field_attributes::PUBLIC,
                    symbol: None,
                    constant: None,
                    sig,
                });
                token
            };
        for local in &locals {
            let symbol = &body.locals[local.0 as usize];
            let (name, ty) = (symbol.name.clone(), symbol.ty.clone());
            let token = field(&mut fields, name.clone(), ty.clone(), None);
            display.inside.locals.insert(*local, token);
            display.outside.locals.insert(*local, token);
            pending.locals.push((*local, name, ty));
        }
        for parameter in &parameters {
            let name = self.compilation.symbols().get(*parameter).name.clone();
            let ty = self.type_of(*parameter);
            let token = field(&mut fields, name.clone(), ty.clone(), None);
            display.inside.parameters.insert(*parameter, token);
            display.outside.parameters.insert(*parameter, token);
            pending.parameters.push((*parameter, name, ty));
        }
        if needs_this {
            let ty = self.binder.self_type(enclosing);
            let token = field(&mut fields, "<>4__this".to_string(), ty.clone(), None);
            display.inside.this = Some(token);
            display.outside.this = Some(token);
            pending.this = Some(ty);
        }
        if let Some(parent) = &parent {
            let token = field(
                &mut fields,
                "CS$<>8__locals".to_string(),
                Type::Error,
                Some(parent.inner_sig.clone()),
            );
            display.inside.parent = Some(token);
            display.outside.parent = Some(token);
        }

        let mut methods = Vec::new();
        let constructor = Token::new(table::METHOD_DEF, *next_method);
        *next_method += 1;
        display.inside.constructor = constructor;
        display.outside.constructor = constructor;
        methods.push(MethodPlan {
            source: MethodSource::DisplayConstructor,
            token: constructor,
            name: ".ctor".to_string(),
            flags: method_attributes::PUBLIC
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
                | method_attributes::RT_SPECIAL_NAME,
            instance: true,
            return_type: Type::Void,
            parameters: Vec::new(),
            type_parameters: Vec::new(),
            impl_flags: 0,
            signature: None,
        });
        for index in lambdas {
            let lambda = &body.lambdas[index];
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            let name = self.lambda_method_name(&body, owner, index, true);
            self.lambda_names.insert((owner, index), name.clone());
            // A lambda inside a generic local function names that function's
            // parameters, and declares them as its own.
            let function_generics = self.function_generics_around(&body, lambda.span);
            if !function_generics.is_empty() {
                self.lambda_generics
                    .insert((owner, index), function_generics.clone());
            }
            self.lambdas.insert((owner, index), method);
            display.inside.methods.insert(index, method);
            display.outside.methods.insert(index, method);
            pending.methods.push((
                index,
                name.clone(),
                lambda_return(lambda),
                lambda
                    .parameters
                    .iter()
                    .map(|local| {
                        let local = &body.locals[local.0 as usize];
                        // A `ref` parameter is a reference in the signature the
                        // definition is written with, and the reference to the
                        // member has to say the same.
                        if local.by_ref {
                            Type::ByRef(Box::new(local.ty.clone()))
                        } else {
                            local.ty.clone()
                        }
                    })
                    .collect(),
            ));
            let source = self.closure_source(
                MachineKey::Lambda { owner, index },
                true,
                Some(display.inner_sig.clone()),
            );
            methods.push(MethodPlan {
                source,
                token: method,
                name,
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                instance: true,
                return_type: lambda_return(lambda),
                parameters: lambda
                    .parameters
                    .iter()
                    .map(|local| ParameterPlan {
                        by_ref: body.locals[local.0 as usize].by_ref,
                        symbol: None,
                        name: body.locals[local.0 as usize].name.clone(),
                        ty: body.locals[local.0 as usize].ty.clone(),
                    })
                    .collect(),
                type_parameters: function_generics.clone(),
                impl_flags: 0,
                signature: None,
            });
        }
        for index in functions {
            let function = &body.local_functions[index];
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.methods.insert(function.symbol, method);
            display
                .inside
                .local_functions
                .insert(function.symbol, method);
            display
                .outside
                .local_functions
                .insert(function.symbol, method);
            let mut plan = self.plan_local_function(
                owner,
                index,
                function,
                method,
                true,
                Some(display.inner_sig.clone()),
                &owner_name,
            )?;
            self.declare_functions_around(&body, function, method, &display.generics, &mut plan);
            pending.functions.push((
                function.symbol,
                plan.name.clone(),
                plan.return_type.clone(),
                plan.parameters
                    .iter()
                    .map(|it| self.pending_parameter_type(it))
                    .collect(),
            ));
            methods.push(MethodPlan {
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                ..plan
            });
        }
        self.nested_displays.insert((owner, outer), display);
        if generic {
            self.display_pending.push(pending);
        }
        Ok(Some(TypePlan {
            symbol: enclosing,
            token,
            fields,
            methods,
            properties: Vec::new(),
            display: Some(owner),
            iterator: None,
            machine: None,
            nested: Some(outer),
        }))
    }

    /// Names every member of every display class that sits in a generic type,
    /// now that every type has a token.
    ///
    /// A `MemberRef` under a `TypeSpec` is the only way to reach one, and its
    /// signature has to be the same blob the definition was written with. A
    /// signature built while planning is not: a field of type
    /// `ObjectPool<T>` names a type that may not have had a token yet, and
    /// what came out said `TypeRef` where the definition says `TypeDef`.
    /// The display class a lambda's method is a member of, if any: the
    /// member's, or that of the lambda it was written inside.
    pub(crate) fn home_of_lambda(&self, owner: SymbolId, index: usize) -> Option<DisplayClass> {
        if let Some(display) = self.displays.get(&owner)
            && display.inside.methods.contains_key(&index)
        {
            return Some(display.clone());
        }
        self.nested_displays
            .iter()
            .find(|((held_by, _), display)| {
                *held_by == owner && display.inside.methods.contains_key(&index)
            })
            .map(|(_, display)| display.clone())
    }

    /// The same for a local function.
    pub(crate) fn home_of_function(
        &self,
        owner: SymbolId,
        symbol: SymbolId,
    ) -> Option<DisplayClass> {
        if let Some(display) = self.displays.get(&owner)
            && display.inside.local_functions.contains_key(&symbol)
        {
            return Some(display.clone());
        }
        self.nested_displays
            .iter()
            .find(|((held_by, _), display)| {
                *held_by == owner && display.inside.local_functions.contains_key(&symbol)
            })
            .map(|(_, display)| display.clone())
    }

    /// The member's display class, or one of its lambdas' by index.
    fn display_at_mut(&mut self, at: (SymbolId, Option<Closure>)) -> Option<&mut DisplayClass> {
        match at {
            (owner, None) => self.displays.get_mut(&owner),
            (owner, Some(outer)) => self.nested_displays.get_mut(&(owner, outer)),
        }
    }

    fn resolve_display_members(&mut self) -> Result<(), EmitError> {
        for pending in std::mem::take(&mut self.display_pending) {
            let (declared, made_as) = pending.generics.clone().unwrap_or_else(|| {
                let made_as = if pending.hosted {
                    (0..(pending.arity + pending.own) as u32)
                        .map(SigType::TypeParameter)
                        .collect()
                } else {
                    (0..pending.arity as u32)
                        .map(SigType::TypeParameter)
                        .chain((0..pending.own as u32).map(SigType::MethodTypeParameter))
                        .collect()
                };
                (
                    self.display_generics_of(pending.owner, pending.arity),
                    made_as,
                )
            });
            let count = if pending.generics.is_some() {
                declared.len()
            } else {
                pending.arity + pending.own
            };
            let sig = SigType::Constructed {
                value_type: false,
                coded: type_def_or_ref(0, pending.token.0 & 0x00FF_FFFF),
                arguments: made_as,
            };
            let mut blob = Vec::new();
            sig.write(&mut blob);
            let outer = self.references.type_spec(&mut self.metadata, &blob);
            // Inside the class its own parameters are what name it, and a
            // member of a generic type is reached through a construction even
            // from within it: `!0` there, whatever the caller wrote.
            let inner = SigType::Constructed {
                value_type: false,
                coded: type_def_or_ref(0, pending.token.0 & 0x00FF_FFFF),
                arguments: (0..count as u32).map(SigType::TypeParameter).collect(),
            };
            let mut blob = Vec::new();
            inner.write(&mut blob);
            let inner = self.references.type_spec(&mut self.metadata, &blob);

            // A `MemberRef` under a `TypeSpec` carries the *definition's*
            // signature (§II.22.25): `!0` where the construction says what it
            // is. So the members below are written as the class names them,
            // whichever construction they hang off.
            self.display_generics = declared;
            let at = (pending.owner, pending.nested);

            for (local, name, ty) in &pending.locals {
                let token = self.display_field(outer, name, ty)?;
                let held = self.display_field(inner, name, ty)?;
                if let Some(display) = self.display_at_mut(at) {
                    display.outside.locals.insert(*local, token);
                    display.inside.locals.insert(*local, held);
                }
            }
            for (parameter, name, ty) in &pending.parameters {
                let token = self.display_field(outer, name, ty)?;
                let held = self.display_field(inner, name, ty)?;
                if let Some(display) = self.display_at_mut(at) {
                    display.outside.parameters.insert(*parameter, token);
                    display.inside.parameters.insert(*parameter, held);
                }
            }
            if let Some(ty) = &pending.this {
                let token = self.display_field(outer, "<>4__this", ty)?;
                let held = self.display_field(inner, "<>4__this", ty)?;
                if let Some(display) = self.display_at_mut(at) {
                    display.outside.this = Some(token);
                    display.inside.this = Some(held);
                }
            }
            if let Some(parent) = &pending.parent {
                let token = self.display_field_sig(outer, "CS$<>8__locals", parent);
                let held = self.display_field_sig(inner, "CS$<>8__locals", parent);
                if let Some(display) = self.display_at_mut(at) {
                    display.outside.parent = Some(token);
                    display.inside.parent = Some(held);
                }
            }

            let signature = method_signature(true, &SigType::Primitive(ElementType::Void), &[]);
            let constructor =
                self.references
                    .member_of_spec(&mut self.metadata, outer, ".ctor", &signature);
            let held_constructor =
                self.references
                    .member_of_spec(&mut self.metadata, inner, ".ctor", &signature);
            for (index, name, returns, parameters) in &pending.methods {
                let own = self
                    .lambda_generics
                    .get(&(pending.owner, *index))
                    .cloned()
                    .unwrap_or_default();
                let outer_method_generics =
                    std::mem::replace(&mut self.method_generics, own.clone());
                let returns = self.sig_type(returns)?;
                let mut written = Vec::with_capacity(parameters.len());
                for parameter in parameters {
                    written.push(self.sig_type(parameter)?);
                }
                self.method_generics = outer_method_generics;
                let signature =
                    generic_method_signature(true, own.len() as u32, &returns, &written);
                let token =
                    self.references
                        .member_of_spec(&mut self.metadata, outer, name, &signature);
                let held =
                    self.references
                        .member_of_spec(&mut self.metadata, inner, name, &signature);
                self.lambdas.insert((pending.owner, *index), token);
                if let Some(display) = self.display_at_mut(at) {
                    display.outside.methods.insert(*index, token);
                    display.inside.methods.insert(*index, held);
                }
            }
            for (symbol, name, returns, parameters) in &pending.functions {
                // A generic local function is named by the generic signature
                // it is defined with: its own parameters are `!!n` there,
                // after those of the functions around it that it declares.
                let around = self
                    .methods
                    .get(symbol)
                    .and_then(|token| self.inherited_generics.get(token))
                    .cloned()
                    .unwrap_or_default();
                let mut own = around.clone();
                own.extend(
                    self.compilation
                        .symbols()
                        .get(*symbol)
                        .as_method()
                        .map(|detail| detail.type_parameters.clone())
                        .unwrap_or_default(),
                );
                let outer_method_generics =
                    std::mem::replace(&mut self.method_generics, own.clone());
                let returns = self.sig_type(returns)?;
                let mut written = Vec::with_capacity(parameters.len());
                for parameter in parameters {
                    written.push(self.sig_type(parameter)?);
                }
                self.method_generics = outer_method_generics;
                let signature =
                    generic_method_signature(true, own.len() as u32, &returns, &written);
                let token =
                    self.references
                        .member_of_spec(&mut self.metadata, outer, name, &signature);
                let held =
                    self.references
                        .member_of_spec(&mut self.metadata, inner, name, &signature);
                self.methods.insert(*symbol, token);
                if !around.is_empty() {
                    self.inherited_generics.insert(token, around.clone());
                    self.inherited_generics.insert(held, around);
                }
                if let Some(display) = self.display_at_mut(at) {
                    display.outside.local_functions.insert(*symbol, token);
                    display.inside.local_functions.insert(*symbol, held);
                }
            }
            if let Some(display) = self.display_at_mut(at) {
                display.outside.constructor = constructor;
                display.inside.constructor = held_constructor;
            }
            self.display_generics = Vec::new();
        }
        Ok(())
    }

    /// One field of a display class, named under the construction it sits in.
    pub(crate) fn display_field(
        &mut self,
        spec: Token,
        name: &str,
        ty: &Type,
    ) -> Result<Token, EmitError> {
        let written = self.sig_type(ty)?;
        let signature = field_signature(&written);
        Ok(self
            .references
            .member_of_spec(&mut self.metadata, spec, name, &signature))
    }

    /// The attribute called `name` (with or without the `Attribute` suffix)
    /// written on a symbol's declaration, if any.
    fn attribute_on(&self, symbol: SymbolId, name: &str) -> Option<rustlyn_syntax::SyntaxNode> {
        let node = self.compilation.declaration_node(symbol)?;
        // A field's attributes sit on the declaration statement around the
        // declarator, not on the declarator itself.
        let holder: rustlyn_syntax::SyntaxNode = if node.kind() == SyntaxKind::VariableDeclarator {
            node.parent()
                .and_then(|declaration| declaration.parent())?
                .clone()
        } else {
            node.clone()
        };
        let long = format!("{name}Attribute");
        holder
            .children()
            .filter(|child| child.kind() == SyntaxKind::AttributeList)
            .flat_map(|list| list.children().collect::<Vec<_>>())
            .filter(|child| child.kind() == SyntaxKind::Attribute)
            .find(|attribute| {
                attribute
                    .children()
                    .next()
                    .and_then(|written| last_identifier(&written))
                    .is_some_and(|written| written == name || written == long)
            })
    }

    /// An attribute written on any declaration of `symbol`, bound: the
    /// arguments it was given are constants folded, whatever expression
    /// spelled them — `Size = 4 * sizeof(byte)`, `FieldOffset(Header.Size)`.
    fn bound_attribute_on(&self, symbol: SymbolId, name: &str) -> Option<BoundAttribute> {
        let long = format!("{name}Attribute");
        for &(tree, span) in self.compilation.declaration_nodes(symbol) {
            let Some(node) = self
                .compilation
                .trees()
                .get(tree)
                .and_then(|syntax| syntax.root().find_node(span))
            else {
                continue;
            };
            // A field's attributes sit on the declaration statement around
            // the declarator, not on the declarator itself.
            let holder = if node.kind() == SyntaxKind::VariableDeclarator {
                match node.parent().and_then(|declaration| declaration.parent()) {
                    Some(holder) => holder.clone(),
                    None => continue,
                }
            } else {
                node
            };
            let attribute = holder
                .children()
                .filter(|child| child.kind() == SyntaxKind::AttributeList)
                .flat_map(|list| list.children().collect::<Vec<_>>())
                .filter(|child| child.kind() == SyntaxKind::Attribute)
                .find(|attribute| {
                    attribute
                        .children()
                        .next()
                        .and_then(|written| last_identifier(&written))
                        .is_some_and(|written| written == name || written == long)
                });
            if let Some(attribute) = attribute {
                return self.binder.bind_attribute(tree, &holder, &attribute);
            }
        }
        None
    }

    /// What `[StructLayout(LayoutKind.Explicit, Size = 1, Pack = 4)]` on a
    /// struct says, where it is written.
    fn struct_layout(&self, ty: SymbolId) -> Option<StructLayout> {
        let attribute = self.bound_attribute_on(ty, "StructLayout")?;
        let mut layout = StructLayout {
            // `LayoutKind.Explicit` is 2 (§II.10.1.2).
            explicit: attribute
                .arguments
                .first()
                .and_then(|kind| folded_integer(self.binder.folded(kind)))
                == Some(2),
            ..StructLayout::default()
        };
        for (member, value) in &attribute.named {
            let number = folded_integer(self.binder.folded(value))
                .and_then(|number| u32::try_from(number).ok());
            match self.compilation.symbols().get(*member).name.as_str() {
                "Size" => layout.size = number,
                "Pack" => layout.pack = number.and_then(|pack| u16::try_from(pack).ok()),
                _ => {}
            }
        }
        Some(layout)
    }

    /// The `n` of `[FieldOffset(n)]` on a field, where it is written.
    fn field_offset(&self, field: SymbolId) -> Option<u32> {
        let attribute = self.bound_attribute_on(field, "FieldOffset")?;
        folded_integer(self.binder.folded(attribute.arguments.first()?))
            .and_then(|offset| u32::try_from(offset).ok())
    }

    /// What `[DllImport]` on an `extern` method says: the library, the entry
    /// point and the mapping flags, read off the attribute as written.
    ///
    /// `EntryPoint` defaults to the method's name; the calling convention is
    /// `Winapi` unless said otherwise; `CharSet`, `SetLastError` and
    /// `ExactSpelling` each set their bit (§II.23.1.8).
    pub(crate) fn dll_import(&self, method: SymbolId) -> Option<DllImport> {
        let symbols = self.compilation.symbols();
        if !symbols.get(method).modifiers.contains(Modifiers::EXTERN) {
            return None;
        }
        let node = self.compilation.declaration_node(method)?;
        let attribute = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::AttributeList)
            .flat_map(|list| list.children().collect::<Vec<_>>())
            .filter(|child| child.kind() == SyntaxKind::Attribute)
            .find(|attribute| {
                attribute
                    .children()
                    .next()
                    .and_then(|name| last_identifier(&name))
                    .is_some_and(|name| name == "DllImport" || name == "DllImportAttribute")
            })?;
        let arguments = attribute.child_of_kind(SyntaxKind::AttributeArgumentList)?;
        let mut library = None;
        let mut entry = symbols.get(method).name.clone();
        let mut flags: u16 = 0x0100;
        for argument in arguments
            .children()
            .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
        {
            let named = argument
                .child_of_kind(SyntaxKind::NameEquals)
                .and_then(|name| last_identifier(&name));
            let Some(value) = argument
                .children()
                .find(|child| child.kind().is_expression())
            else {
                continue;
            };
            let text = || {
                value
                    .child_tokens()
                    .next()
                    .map(|token| token.value_text().trim_matches('"').to_string())
            };
            match named.as_deref() {
                None => library = text(),
                Some("EntryPoint") => {
                    if let Some(name) = text() {
                        entry = name;
                    }
                }
                Some("CharSet") => {
                    flags |= match last_identifier(&value).as_deref() {
                        Some("Ansi") => 0x0002,
                        Some("Unicode") => 0x0004,
                        Some("Auto") => 0x0006,
                        _ => 0,
                    }
                }
                Some("CallingConvention") => {
                    flags = (flags & !0x0700)
                        | match last_identifier(&value).as_deref() {
                            Some("Cdecl") => 0x0200,
                            Some("StdCall") => 0x0300,
                            Some("ThisCall") => 0x0400,
                            Some("FastCall") => 0x0500,
                            _ => 0x0100,
                        };
                }
                Some("SetLastError") if value.kind() == SyntaxKind::TrueLiteralExpression => {
                    flags |= 0x0040;
                }
                Some("ExactSpelling") if value.kind() == SyntaxKind::TrueLiteralExpression => {
                    flags |= 0x0001;
                }
                _ => {}
            }
        }
        Some(DllImport {
            library: library?,
            entry,
            flags,
        })
    }

    /// Writes the rows that give a method its unmanaged body.
    fn note_pinvoke(&mut self, method: Token, import: DllImport) {
        let module = self.metadata.add_module_ref(&import.library);
        self.metadata
            .add_impl_map(import.flags, method, &import.entry, module);
    }

    /// The same, for a field whose type is only a signature.
    pub(crate) fn display_field_sig(&mut self, spec: Token, name: &str, sig: &SigType) -> Token {
        let signature = field_signature(sig);
        self.references
            .member_of_spec(&mut self.metadata, spec, name, &signature)
    }

    fn plan_enum(
        &mut self,
        symbol: SymbolId,
        token: Token,
        next_field: &mut u32,
    ) -> Result<TypePlan, EmitError> {
        let underlying = self.enum_underlying(symbol);
        let mut fields = vec![FieldPlan {
            token: Token::new(table::FIELD, *next_field),
            name: "value__".to_string(),
            ty: underlying,
            flags: field_attributes::PUBLIC
                | field_attributes::SPECIAL_NAME
                | field_attributes::RT_SPECIAL_NAME,
            symbol: None,
            constant: None,
            sig: None,
        }];
        *next_field += 1;

        let symbols = self.compilation.symbols();
        for member in symbols.get(symbol).members.clone() {
            if self.compilation.symbols().get(member).kind != SymbolKind::Field {
                continue;
            }
            let field = Token::new(table::FIELD, *next_field);
            *next_field += 1;
            self.fields.insert(member, field);
            let constant = match self.binder.constant_value(member) {
                Some(constant) => constant,
                None => {
                    let name = self.compilation.symbols().qualified_name(member);
                    let message = format!("the enum member `{name}` has no constant value");
                    if !self.lenient {
                        return Err(EmitError::new(message));
                    }
                    self.skipped.push((name, message));
                    ConstantValue::Int32(0)
                }
            };
            fields.push(FieldPlan {
                token: field,
                name: self.compilation.symbols().get(member).name.clone(),
                // A member's type is the enum, not the storage underneath it.
                ty: Type::named(symbol),
                flags: field_attributes::PUBLIC
                    | field_attributes::STATIC
                    | field_attributes::LITERAL
                    | field_attributes::HAS_DEFAULT,
                symbol: Some(member),
                constant: Some(constant),
                sig: None,
            });
        }

        Ok(TypePlan {
            symbol,
            token,
            fields,
            methods: Vec::new(),
            properties: Vec::new(),
            display: None,
            iterator: None,
            machine: None,
            nested: None,
        })
    }

    /// The type an enum stores its values in, which is `int` unless it says.
    pub(crate) fn enum_underlying(&self, symbol: SymbolId) -> Type {
        let mut sink = rustlyn_semantics::Diagnostics::new();
        let symbols = self.compilation.symbols();
        if let Some(reference) = symbols
            .get(symbol)
            .as_named_type()
            .and_then(|detail| detail.enum_underlying)
        {
            return self.binder.resolve_type_ref(reference, &mut sink);
        }
        // An enum read out of metadata says what it is made of through its
        // `value__` field: `EventKeywords` is a `long`, and a constant of it
        // has to be loaded as one.
        if let Some(storage) = symbols.lookup(symbol, "value__").first().copied() {
            let ty = self.type_of(storage);
            if !ty.is_error() {
                return ty;
            }
        }
        self.compilation
            .special_type(SpecialType::Int32)
            .map_or(Type::Error, Type::named)
    }

    /// A property becomes a pair of methods, and an automatic one also becomes
    /// a field for them to work on.
    /// The accessor symbols a property declares, where it declares them.
    ///
    /// A `{ get { ... } }` accessor is a member with a body of its own; a
    /// `=> e` property has none, and its body is the property's.
    fn accessors_of(&self, property: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let Some(detail) = symbols.get(property).as_property() else {
            return Vec::new();
        };
        [detail.getter, detail.setter]
            .into_iter()
            .flatten()
            .collect()
    }

    /// Whether an event was written as a field — `public event Action E;` —
    /// rather than with `add` and `remove` blocks of its own.
    /// Whether a field-like event was written with a value: `event Action E
    /// = Handler;` stores it in its field as a field initializer would.
    pub(crate) fn event_has_initializer(&self, event: SymbolId) -> bool {
        self.compilation.symbols().get(event).kind == SymbolKind::Event
            && self
                .compilation
                .declaration_node(event)
                .is_some_and(|node| {
                    node.kind() == SyntaxKind::VariableDeclarator
                        && node.child_of_kind(SyntaxKind::EqualsValueClause).is_some()
                })
    }

    pub(crate) fn is_field_like_event(&self, event: SymbolId) -> bool {
        self.compilation
            .declaration_node(event)
            .is_some_and(|node| node.kind() == SyntaxKind::VariableDeclarator)
    }

    /// The `add_E` and `remove_E` a field-like event gets (§15.8.2): public
    /// as the event is, virtual where an interface's event is being
    /// implemented, and each taking the handler as `value`.
    fn plan_event_accessors(&mut self, event: SymbolId, next_method: &mut u32) -> Vec<MethodPlan> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(event);
        let name = symbol.name.clone();
        let ty = self.type_of(event);
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        let flags = self.event_accessor_flags(event);
        let container = symbol.container;
        // The accessors' symbols, which a `+=` from another type calls: their
        // tokens go on the map every call goes through.
        let (adder, remover) = symbol
            .as_event()
            .map_or((None, None), |detail| (detail.adder, detail.remover));
        let mut plans = Vec::with_capacity(2);
        let mut tokens = Vec::with_capacity(2);
        for (add, accessor) in [(true, adder), (false, remover)] {
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            tokens.push(token);
            let value = accessor.and_then(|accessor| {
                symbols
                    .get(accessor)
                    .as_method()
                    .and_then(|detail| detail.parameters.first().copied())
            });
            if let Some(accessor) = accessor {
                self.methods.insert(accessor, token);
            }
            plans.push(MethodPlan {
                source: MethodSource::EventAccessor { event, add },
                token,
                name: format!("{}_{name}", if add { "add" } else { "remove" }),
                flags,
                instance,
                return_type: Type::Void,
                parameters: vec![ParameterPlan {
                    symbol: value,
                    name: "value".to_string(),
                    ty: ty.clone(),
                    by_ref: false,
                }],
                type_parameters: Vec::new(),
                impl_flags: 0,
                signature: None,
            });
        }
        if let Some(container) = container {
            self.events_of
                .entry(container)
                .or_default()
                .push(EventPlan {
                    symbol: event,
                    name,
                    ty,
                    add: tokens[0],
                    remove: tokens[1],
                });
        }
        plans
    }

    /// The `add_E` or `remove_E` synthesized for a field-like event.
    pub(crate) fn event_accessor(&self, event: SymbolId, add: bool) -> Option<Token> {
        let container = self.compilation.symbols().get(event).container?;
        self.events_of
            .get(&container)?
            .iter()
            .find(|plan| plan.symbol == event)
            .map(|plan| if add { plan.add } else { plan.remove })
    }

    /// The flags both accessors of an event carry: as accessible as the
    /// event, virtual where an interface's event is being implemented.
    fn event_accessor_flags(&self, event: SymbolId) -> u16 {
        let symbol = self.compilation.symbols().get(event);
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        if instance && self.declared_in_interface(event) {
            return self.interface_member_flags(event, symbol.accessibility, false)
                | method_attributes::SPECIAL_NAME;
        }
        let mut flags = method_flags(symbol.accessibility, instance, symbol.modifiers)
            | method_attributes::SPECIAL_NAME
            | method_attributes::HIDE_BY_SIG;
        if instance && self.implements_an_interface_event(event) {
            flags |= implementing_flags(symbol.modifiers);
        }
        flags
    }

    /// The accessors an event wrote as `add { }` and `remove { }` blocks:
    /// declared methods with bodies of their own, planned here so that the
    /// `Event` row can name them.
    fn plan_declared_event(&mut self, event: SymbolId, next_method: &mut u32) -> Vec<MethodPlan> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(event);
        let name = symbol.name.clone();
        let ty = self.type_of(event);
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        let mut flags = self.event_accessor_flags(event);
        let container = symbol.container;
        let Some(detail) = symbol.as_event() else {
            return Vec::new();
        };
        let (Some(adder), Some(remover)) = (detail.adder, detail.remover) else {
            return Vec::new();
        };
        // `event EventHandler I.E { add { } remove { } }` implements the
        // interface's accessors explicitly: private, sealed, named
        // `I.add_E`, and tied to them by `MethodImpl` rows.
        let explicit = instance
            .then(|| self.explicit_interface(event))
            .flatten()
            .and_then(|interface| {
                let declared = self.interface_event(event, &interface)?;
                Some((interface, declared))
            });
        let (prefix, bare) = match &explicit {
            Some((interface, _)) => (
                format!("{}.", self.explicit_prefix(interface)),
                name.rsplit('.').next().unwrap_or_default().to_string(),
            ),
            None => (String::new(), name.clone()),
        };
        let name = format!("{prefix}{bare}");
        if explicit.is_some() && self.declared_in_interface(event) {
            flags = self.interface_member_flags(event, symbol.accessibility, true)
                | method_attributes::SPECIAL_NAME;
        } else if explicit.is_some() {
            flags = method_attributes::PRIVATE
                | method_attributes::FINAL
                | method_attributes::VIRTUAL
                | method_attributes::NEW_SLOT
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME;
        }
        let mut plans = Vec::with_capacity(2);
        let mut tokens = Vec::with_capacity(2);
        for (add, accessor) in [(true, adder), (false, remover)] {
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            tokens.push(token);
            self.methods.insert(accessor, token);
            let value = symbols
                .get(accessor)
                .as_method()
                .and_then(|detail| detail.parameters.first().copied());
            if let Some((interface, declared)) = &explicit
                && let Some(class) = container.and_then(|container| self.types.get(&container))
            {
                let answered = if add { declared.0 } else { declared.1 };
                self.explicit_impls.push(ExplicitImpl {
                    class: *class,
                    body: token,
                    declaration: Declaration::Method {
                        member: answered,
                        interface: interface.clone(),
                    },
                });
            }
            plans.push(MethodPlan {
                source: MethodSource::Declared(accessor),
                token,
                name: format!("{prefix}{}_{bare}", if add { "add" } else { "remove" }),
                flags,
                instance,
                return_type: Type::Void,
                parameters: vec![ParameterPlan {
                    symbol: value,
                    name: "value".to_string(),
                    ty: ty.clone(),
                    by_ref: false,
                }],
                type_parameters: Vec::new(),
                impl_flags: 0,
                signature: None,
            });
        }
        if let Some(container) = container {
            self.events_of
                .entry(container)
                .or_default()
                .push(EventPlan {
                    symbol: event,
                    name,
                    ty,
                    add: tokens[0],
                    remove: tokens[1],
                });
        }
        plans
    }

    /// The accessors of the interface event an explicit implementation
    /// answers: `I.E` answers `I`'s `E`.
    fn interface_event(&self, event: SymbolId, interface: &Type) -> Option<(SymbolId, SymbolId)> {
        let symbols = self.compilation.symbols();
        let declared = interface.symbol()?;
        let name = symbols.get(event).name.clone();
        let bare = name.rsplit('.').next()?;
        let found = symbols
            .lookup(declared, bare)
            .iter()
            .copied()
            .find(|candidate| symbols.get(*candidate).kind == SymbolKind::Event)?;
        let detail = symbols.get(found).as_event()?;
        Some((detail.adder?, detail.remover?))
    }

    /// Whether an event answers for one an interface of its type declares.
    fn implements_an_interface_event(&self, event: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(event).container else {
            return false;
        };
        let name = symbols.get(event).name.clone();
        self.answering
            .get(&container)
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter_map(|interface| interface.symbol())
            .any(|interface| {
                symbols.lookup(interface, &name).iter().any(|candidate| {
                    symbols.get(*candidate).kind == SymbolKind::Event
                        && self.is_interface_slot(*candidate)
                })
            })
    }

    /// Remembers that a static method implements a `static abstract` (or
    /// `static virtual`) member of an interface its type has.
    ///
    /// `operator +` on `Duration` answers for `IAdditionOperators<Duration,
    /// Duration, Duration>.op_Addition`, and a static method has no virtual
    /// slot to be found through: a `MethodImpl` row is the only way the
    /// runtime can pair the two (§II.22.27).
    fn note_static_implementations(&mut self, method: SymbolId, body: Token) {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(method).container else {
            return;
        };
        let Some(class) = self.types.get(&container).copied() else {
            return;
        };
        let interfaces = self.answering.get(&container).cloned().unwrap_or_default();
        let own: Vec<Type> = symbols
            .get(method)
            .as_method()
            .map(|detail| {
                detail
                    .parameters
                    .iter()
                    .map(|parameter| self.type_of(*parameter))
                    .collect()
            })
            .unwrap_or_default();
        for interface in interfaces {
            let Some(declared) = self.interface_member(method, &interface) else {
                continue;
            };
            // `LocalDate` implements `IAdditionOperators<LocalDate, Period,
            // LocalDate>` and `IAdditionOperators<LocalDate, LocalTime,
            // LocalDateTime>` both: the operator whose parameters are the
            // construction's is the one that answers for it.
            let declared_parameters: Vec<Type> = symbols
                .get(declared)
                .as_method()
                .map(|detail| {
                    detail
                        .parameters
                        .iter()
                        .map(|parameter| self.member_type(*parameter, &interface))
                        .collect()
                })
                .unwrap_or_default();
            if declared_parameters != own {
                continue;
            }
            let modifiers = symbols.get(declared).modifiers;
            if !modifiers.contains(Modifiers::STATIC)
                || !(modifiers.contains(Modifiers::ABSTRACT)
                    || modifiers.contains(Modifiers::VIRTUAL))
            {
                continue;
            }
            self.explicit_impls.push(ExplicitImpl {
                class,
                body,
                declaration: Declaration::Method {
                    member: declared,
                    interface,
                },
            });
        }
    }

    /// The same for a static property: `Period.AdditiveIdentity` answers for
    /// `IAdditiveIdentity<Period, Period>.AdditiveIdentity`, accessor by
    /// accessor.
    fn note_static_property_implementations(
        &mut self,
        property: SymbolId,
        body: Token,
        setter: bool,
    ) {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(property).container else {
            return;
        };
        let Some(class) = self.types.get(&container).copied() else {
            return;
        };
        let own = self.type_of(property);
        let interfaces = self.answering.get(&container).cloned().unwrap_or_default();
        for interface in interfaces {
            let Some(declared) = self.interface_member(property, &interface) else {
                continue;
            };
            // A property read from metadata says `static abstract` on its
            // accessors, not on itself. One written in an interface has the
            // accessor symbol only where it was given a body, so that the
            // property says whether it has the accessor at all.
            let Some(detail) = symbols.get(declared).as_property() else {
                continue;
            };
            if !(if setter {
                detail.has_set
            } else {
                detail.has_get
            }) {
                continue;
            }
            let accessor = if setter { detail.setter } else { detail.getter };
            let has = |flag: Modifiers| {
                accessor.is_some_and(|accessor| symbols.get(accessor).modifiers.contains(flag))
                    || symbols.get(declared).modifiers.contains(flag)
            };
            if !has(Modifiers::STATIC)
                || !(has(Modifiers::ABSTRACT) || has(Modifiers::VIRTUAL))
                || self.member_type(declared, &interface) != own
            {
                continue;
            }
            self.explicit_impls.push(ExplicitImpl {
                class,
                body,
                declaration: Declaration::Accessor {
                    property: declared,
                    interface,
                    setter,
                },
            });
        }
    }

    /// The same, for the body emitter.
    pub(crate) fn is_extension_method_symbol(&self, method: SymbolId) -> bool {
        self.is_extension_method(method)
    }

    /// Whether a method is an extension method: one written with `this` on
    /// its first parameter.
    fn is_extension_method(&self, method: SymbolId) -> bool {
        self.compilation
            .symbols()
            .get(method)
            .as_method()
            .is_some_and(|detail| detail.is_extension)
    }

    /// Writes the `[Extension]` the compiler puts on an extension method, on
    /// its class and on its assembly (§C.4): the source never writes it, and
    /// another compilation finds the method as an extension by nothing else.
    /// `[DebuggerBrowsable(DebuggerBrowsableState.Never)]`, which a debug
    /// build puts on the fields the language adds.
    fn mark_debugger_browsable_never(&mut self, parent: u32) {
        const BROWSABLE: &str = "System.Diagnostics.DebuggerBrowsableAttribute";
        if self.compilation.type_by_metadata_name(BROWSABLE).is_none() {
            return;
        }
        let state = SigType::Named {
            value_type: true,
            coded: self.references.type_ref_coded(
                &mut self.metadata,
                "System.Diagnostics.DebuggerBrowsableState",
            ),
        };
        let constructor = self.references.member_ref(
            &mut self.metadata,
            BROWSABLE,
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[state]),
        );
        // `DebuggerBrowsableState.Never` is 0.
        self.metadata.add_custom_attribute(
            parent,
            ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
            &[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        );
    }

    fn mark_extension(&mut self, parent: u32) {
        self.mark_with(parent, "System.Runtime.CompilerServices.ExtensionAttribute");
    }

    /// `[Dynamic]` on a row whose type says `dynamic` somewhere, which is how
    /// another compiler learns that the `object` in the signature was one:
    /// one flag per type in the type, in pre-order, after one for a `ref`.
    fn mark_dynamic(&mut self, parent: u32, ty: &Type, by_ref: bool) {
        if !crate::dynamic::mentions_dynamic_type(ty) {
            return;
        }
        let mut flags = Vec::new();
        if by_ref {
            flags.push(false);
        }
        crate::dynamic::dynamic_flags(ty.value(), &mut flags);
        let bool_array = SigType::Array(Box::new(SigType::Primitive(ElementType::Boolean)));
        let (parameters, blob) = if flags == [true] {
            (Vec::new(), vec![0x01, 0x00, 0x00, 0x00])
        } else {
            let mut blob = vec![0x01, 0x00];
            blob.extend_from_slice(&(flags.len() as u32).to_le_bytes());
            blob.extend(flags.iter().map(|flag| u8::from(*flag)));
            blob.extend_from_slice(&[0x00, 0x00]);
            (vec![bool_array], blob)
        };
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.Runtime.CompilerServices.DynamicAttribute",
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &parameters),
        );
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// `[TupleElementNames]` on a row whose type has a named tuple in it: the
    /// names the metadata type `ValueTuple<...>` cannot carry, one per element
    /// of every tuple in the type in pre-order, null where one has none.
    fn mark_tuple_names(&mut self, parent: u32, ty: &Type) {
        let names = tuple_names(ty.value());
        if names.is_empty() {
            return;
        }
        let strings = SigType::Array(Box::new(SigType::Primitive(ElementType::String)));
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.Runtime.CompilerServices.TupleElementNamesAttribute",
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[strings]),
        );
        let mut blob = vec![0x01, 0x00];
        blob.extend_from_slice(&(names.len() as u32).to_le_bytes());
        for name in &names {
            match name {
                // A null string is the one byte 0xFF (§II.23.3).
                None => blob.push(0xFF),
                Some(name) => {
                    crate::signature::compress(&mut blob, name.len() as u32);
                    blob.extend_from_slice(name.as_bytes());
                }
            }
        }
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// `[FixedBuffer(typeof(T), length)]` on a `fixed` buffer field's row.
    fn mark_fixed_buffer(&mut self, parent: u32, field: SymbolId) {
        let element = self.type_of(field);
        let (Some(name), Some(length)) = (
            self.serialized_type_name(&element),
            self.binder.fixed_buffer_length(field),
        ) else {
            return;
        };
        let system_type = SigType::Named {
            value_type: false,
            coded: self
                .references
                .type_ref_coded(&mut self.metadata, "System.Type"),
        };
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.Runtime.CompilerServices.FixedBufferAttribute",
            ".ctor",
            &method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[system_type, SigType::Primitive(ElementType::I4)],
            ),
        );
        let mut blob = vec![0x01, 0x00];
        crate::signature::compress(&mut blob, name.len() as u32);
        blob.extend_from_slice(name.as_bytes());
        blob.extend_from_slice(&(length as i32).to_le_bytes());
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// `[DefaultMember(name)]` on a type's row.
    fn mark_default_member(&mut self, parent: u32, name: &str) {
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.Reflection.DefaultMemberAttribute",
            ".ctor",
            &method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[SigType::Primitive(ElementType::String)],
            ),
        );
        // The prolog, the string as a length and its UTF-8, and no named
        // arguments.
        let mut blob = vec![0x01, 0x00];
        crate::signature::compress(&mut blob, name.len() as u32);
        blob.extend_from_slice(name.as_bytes());
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// Writes an attribute with a parameterless constructor on a row: the
    /// ones the compiler adds on its own, such as `[ParamArray]` on a
    /// `params` parameter, which is how another compilation knows it is one.
    /// Writes a `decimal` or `DateTime` constant as the attribute that holds
    /// one: `[DecimalConstant(scale, sign, hi, mid, lo)]` with the unsigned
    /// constructor, or `[DateTimeConstant(ticks)]`.
    fn mark_special_constant(&mut self, parent: u32, value: SpecialConstant) {
        let (name, parameters, arguments): (&str, Vec<SigType>, Vec<u8>) = match value {
            SpecialConstant::Decimal {
                scale,
                negative,
                hi,
                mid,
                lo,
            } => {
                // The sign is the top bit of the byte, as `decimal` keeps it.
                let mut arguments = vec![scale, if negative { 0x80 } else { 0 }];
                for word in [hi, mid, lo] {
                    arguments.extend_from_slice(&word.to_le_bytes());
                }
                (
                    "System.Runtime.CompilerServices.DecimalConstantAttribute",
                    vec![
                        SigType::Primitive(ElementType::U1),
                        SigType::Primitive(ElementType::U1),
                        SigType::Primitive(ElementType::U4),
                        SigType::Primitive(ElementType::U4),
                        SigType::Primitive(ElementType::U4),
                    ],
                    arguments,
                )
            }
            SpecialConstant::DateTime(ticks) => (
                "System.Runtime.CompilerServices.DateTimeConstantAttribute",
                vec![SigType::Primitive(ElementType::I8)],
                ticks.to_le_bytes().to_vec(),
            ),
        };
        let constructor = self.references.member_ref(
            &mut self.metadata,
            name,
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &parameters),
        );
        let mut blob = vec![0x01, 0x00];
        blob.extend_from_slice(&arguments);
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    fn mark_with(&mut self, parent: u32, qualified_type: &str) {
        let constructor = self.references.member_ref(
            &mut self.metadata,
            qualified_type,
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[]),
        );
        // A `CustomAttributeType` tagged 3 is a `MemberRef`.
        self.metadata.add_custom_attribute(
            parent,
            ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
            &[0x01, 0x00, 0x00, 0x00],
        );
    }

    fn plan_property(
        &mut self,
        property: SymbolId,
        next_field: &mut u32,
        next_method: &mut u32,
        interface: bool,
    ) -> Result<(Vec<FieldPlan>, Vec<MethodPlan>, PropertyPlan), EmitError> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(property);
        let detail = symbol
            .as_property()
            .ok_or_else(|| EmitError::new("a property symbol without property detail"))?;
        let is_indexer = detail.is_indexer;
        // An extension block's accessors declare the block's type
        // parameters as their own.
        let generics = detail.extension_generics.clone();
        let (declared_getter, declared_setter) = (detail.getter, detail.setter);
        let arguments = detail.parameters.clone();
        // An indexer has no name of its own in metadata; it is called `Item`
        // by convention, and `DefaultMemberAttribute` on the type is what says
        // so. We do not write attributes, so a C# consumer would not see the
        // indexer syntax — but the accessors are there and callable, which is
        // what our own IL uses.
        // An override of an indexer read from metadata is named as that one
        // is: `get_P` answers `get_P`, and a `get_Item` beside it would
        // override nothing.
        let overridden_name = (is_indexer && symbol.modifiers.contains(Modifiers::OVERRIDE))
            .then(|| self.overridden_member(property))
            .flatten()
            .filter(|base| self.compilation.is_from_metadata(*base))
            .and_then(|base| {
                let base = symbols.get(base).as_property()?;
                let accessor = base.getter.or(base.setter)?;
                let name = &symbols.get(accessor).name;
                name.strip_prefix("get_")
                    .or_else(|| name.strip_prefix("set_"))
                    .map(str::to_string)
            });
        let name = if let Some(name) = overridden_name {
            name
        } else if is_indexer {
            // `[IndexerName("Chars")]` names it otherwise, a constant
            // expression included.
            self.binder.indexer_metadata_name(property)
        } else {
            symbol.name.clone()
        };
        let ty = self.type_of(property);
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        let accessibility = symbol.accessibility;
        let (has_get, declared_set) = (detail.has_get, detail.has_set || detail.has_init);
        // `int X { get; }` written in an interface, or after `abstract`, has
        // no body and no field: it *looks* automatic, because an automatic
        // property is written the same way. What tells them apart is where it
        // sits, not how it reads.
        let abstract_property = instance
            && (symbol.modifiers.contains(Modifiers::ABSTRACT)
                || (interface
                    && self
                        .compilation
                        .interface_member_modifiers(property)
                        .contains(Modifiers::ABSTRACT)));
        let automatic = !is_indexer
            && !abstract_property
            && !(interface && instance)
            && self.binder.is_automatic_property(property);
        // The flags both accessors carry. An interface member's are what
        // C# 8 makes of what it wrote; a member that implements an interface
        // property has to be virtual too, or the interface's call reaches
        // nothing, and final so that nothing can override it out from under
        // the interface.
        let explicit = instance
            .then(|| self.explicit_interface(property))
            .flatten();
        // An explicit implementation's property is `N.I.P` and its accessors
        // `N.I.get_P`, the interface written as Roslyn writes it.
        let (name, accessor_prefix, accessor_base) = match &explicit {
            Some(declared) => {
                let prefix = format!("{}.", self.explicit_prefix(declared));
                let bare = name.rsplit('.').next().unwrap_or_default().to_string();
                (format!("{prefix}{bare}"), prefix, bare)
            }
            None => (name.clone(), String::new(), name),
        };
        // An accessor of an interface's property that narrowed itself —
        // `private set { }` — is narrowed out of the slot as well.
        let interface_accessor = |own: Option<rustlyn_semantics::Accessibility>| {
            self.interface_member_flags(property, own.unwrap_or(accessibility), explicit.is_some())
                | method_attributes::SPECIAL_NAME
        };
        let accessor_flags = if interface && instance {
            interface_accessor(None)
        } else if explicit.is_some() {
            method_attributes::PRIVATE
                | method_attributes::FINAL
                | method_attributes::VIRTUAL
                | method_attributes::NEW_SLOT
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
        } else {
            // A record's `EqualityContract` is `virtual` or `override` by
            // what the record's base is.
            let modifiers =
                if detail.synthesized == Some(rustlyn_semantics::SynthesizedType::SystemType) {
                    {
                        let mut modifiers = symbol.modifiers;
                        modifiers.insert(self.record_member_modifiers(property));
                        modifiers
                    }
                } else {
                    symbol.modifiers
                };
            let mut flags =
                method_flags(accessibility, instance, modifiers) | method_attributes::SPECIAL_NAME;
            if detail.synthesized == Some(rustlyn_semantics::SynthesizedType::SystemType) {
                flags |= method_attributes::HIDE_BY_SIG;
            }
            if instance && self.implements_an_interface_property(property) {
                flags |= implementing_flags(modifiers);
            }
            flags
        };
        let no_body = accessor_flags & method_attributes::ABSTRACT != 0;
        // For patches: `int X { get; }` set from a patched constructor.
        let opened_setter = self.getter_only_setters
            && automatic
            && has_get
            && !declared_set
            && !interface
            && explicit.is_none()
            && ![Modifiers::VIRTUAL, Modifiers::OVERRIDE, Modifiers::ABSTRACT]
                .iter()
                .any(|modifier| symbol.modifiers.contains(*modifier));
        let has_set = declared_set || opened_setter;
        let (get_flags, set_flags) = if interface && instance {
            (
                interface_accessor(detail.get_accessibility),
                interface_accessor(detail.set_accessibility),
            )
        } else {
            (
                narrowed(accessor_flags, detail.get_accessibility, explicit.is_some()),
                narrowed(accessor_flags, detail.set_accessibility, explicit.is_some()),
            )
        };

        let mut parameters = Vec::with_capacity(arguments.len());
        for argument in &arguments {
            parameters.push(ParameterPlan {
                by_ref: false,
                symbol: Some(*argument),
                name: symbols.get(*argument).name.clone(),
                ty: self.type_of(*argument),
            });
        }
        let parameter_types: Vec<Type> = parameters
            .iter()
            .map(|parameter| parameter.ty.clone())
            .collect();

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        if automatic {
            let token = Token::new(table::FIELD, *next_field);
            *next_field += 1;
            self.fields.insert(property, token);
            // A property nothing can set but a constructor or an `init` is
            // backed by a `readonly` field, as Roslyn makes it.
            let readonly = !detail.has_set;
            fields.push(FieldPlan {
                token,
                // The name a C# compiler gives a backing field: unspeakable in
                // C#, so nothing can collide with it.
                name: self.backing_field_name(property),
                ty: ty.clone(),
                flags: field_attributes::PRIVATE
                    | if instance {
                        0
                    } else {
                        field_attributes::STATIC
                    }
                    | if readonly {
                        field_attributes::INIT_ONLY
                    } else {
                        0
                    },
                // The property itself stands behind the field: `public int
                // X { get; } = 5;` writes the 5 into it, and the initializer
                // is under the property rather than under any field symbol.
                symbol: Some(property),
                constant: None,
                sig: None,
            });
        }

        // `get; set { field = value; }` has a getter with no body and a
        // field the binder declared for it: the getter reads that.
        let field_backed =
            detail.backing_field.is_some() && !self.binder.declaration_has_arrow_body(property);
        if has_get {
            // Three shapes, in order: a declared `get { ... }`, an
            // expression-bodied property (whose own declaration is the
            // getter), and an automatic property (a read of the field).
            let source = match (
                automatic || (field_backed && declared_getter.is_none()),
                declared_getter,
            ) {
                (true, _) => MethodSource::PropertyGetter {
                    property,
                    backing: true,
                },
                // A getter with a `yield` in it starts a state machine, the
                // way a method with one does.
                (false, Some(getter))
                    if self.iterated_element(MachineKey::Member(getter)).is_some()
                        && self.iterator_refusal(MachineKey::Member(getter)).is_none() =>
                {
                    MethodSource::IteratorStart(MachineKey::Member(getter))
                }
                (false, Some(getter)) => MethodSource::Declared(getter),
                // `EqualityContract => typeof(R)`, which nothing wrote.
                (false, None)
                    if detail.synthesized
                        == Some(rustlyn_semantics::SynthesizedType::SystemType) =>
                {
                    MethodSource::RecordMember(property)
                }
                (false, None) => MethodSource::PropertyGetter {
                    property,
                    backing: false,
                },
            };
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.getters.insert(property, token);
            if let Some(declared) = &explicit {
                let declared = declared.clone();
                self.note_explicit(property, token, &declared, Some(false));
            }
            self.note_renamed_accessor_override(
                property,
                token,
                false,
                &format!("{accessor_prefix}get_{accessor_base}"),
            );
            let get_flags = if instance
                && !interface
                && explicit.is_none()
                && self.note_covariant_override(property, token, true)
            {
                get_flags | method_attributes::NEW_SLOT
            } else {
                get_flags
            };
            if !instance && !interface && explicit.is_none() {
                self.note_static_property_implementations(property, token, false);
            }
            methods.push(MethodPlan {
                source,
                token,
                name: format!("{accessor_prefix}get_{accessor_base}"),
                flags: get_flags,
                instance,
                return_type: ty.clone(),
                parameters: parameters.clone(),
                type_parameters: generics.clone(),
                impl_flags: 0,
                signature: None,
            });
        }
        if has_set {
            let source = match (
                automatic || no_body || (field_backed && declared_setter.is_none()),
                declared_setter,
            ) {
                (true, _) => MethodSource::PropertySetter { property },
                (false, Some(setter)) => MethodSource::Declared(setter),
                (false, None) => {
                    return Err(EmitError::new(format!(
                        "cannot emit the setter of `{}` yet: it has no body to emit",
                        symbols.qualified_name(property)
                    )));
                }
            };
            // The value comes last, after an indexer's arguments. Where an
            // accessor was declared it owns a `value` symbol; the synthesised
            // one has none, so the plan carries the name and type instead.
            let mut setter_parameters = parameters.clone();
            setter_parameters.push(ParameterPlan {
                by_ref: false,
                symbol: declared_setter.and_then(|setter| {
                    symbols
                        .get(setter)
                        .as_method()
                        .and_then(|detail| detail.parameters.last().copied())
                }),
                name: "value".to_string(),
                ty: ty.clone(),
            });
            let token = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.setters.insert(property, token);
            if let Some(declared) = &explicit {
                let declared = declared.clone();
                self.note_explicit(property, token, &declared, Some(true));
            }
            self.note_renamed_accessor_override(
                property,
                token,
                true,
                &format!("{accessor_prefix}set_{accessor_base}"),
            );
            if !instance && !interface && explicit.is_none() {
                self.note_static_property_implementations(property, token, true);
            }
            methods.push(MethodPlan {
                source,
                token,
                name: format!("{accessor_prefix}set_{accessor_base}"),
                flags: if opened_setter {
                    method_attributes::ASSEMBLY
                        | method_attributes::HIDE_BY_SIG
                        | method_attributes::SPECIAL_NAME
                        | if instance {
                            0
                        } else {
                            method_attributes::STATIC
                        }
                } else {
                    set_flags
                },
                instance,
                return_type: Type::Void,
                parameters: setter_parameters,
                type_parameters: generics.clone(),
                impl_flags: 0,
                signature: None,
            });
        }

        Ok((
            fields,
            methods,
            PropertyPlan {
                symbol: Some(property),
                name,
                ty,
                instance,
                parameters: parameter_types,
                getter: self.getters.get(&property).copied(),
                setter: self.setters.get(&property).copied(),
            },
        ))
    }

    fn plan_method(
        &mut self,
        method: SymbolId,
        token: Token,
        interface: bool,
    ) -> Result<Option<MethodPlan>, EmitError> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(method);
        let detail = symbol
            .as_method()
            .ok_or_else(|| EmitError::new("a method symbol without method detail"))?;
        // A class constructor is a constructor too: its name is reserved, it
        // returns nothing, and the runtime finds it by the two name flags
        // rather than by the name alone.
        let class_constructor = symbol.name == ".cctor";
        let constructor = symbol.name == ".ctor" || class_constructor;
        let synthesized = detail.method_kind == rustlyn_semantics::MethodKind::RecordSynthesized;
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        // A record over one whose `ToString` is sealed writes none of its
        // own (C# 10): the base's is the record's.
        if synthesized
            && symbol.name == "ToString"
            && detail.parameters.is_empty()
            && symbol
                .container
                .is_some_and(|record| self.base_seals_to_string(record))
        {
            return Ok(None);
        }
        // A record's own members are `virtual` or `override` by what the
        // record and its base are, which the declaration could not know.
        let modifiers = if synthesized {
            let mut modifiers = symbol.modifiers;
            modifiers.insert(self.record_member_modifiers(method));
            modifiers
        } else {
            symbol.modifiers
        };
        let mut flags = method_flags(symbol.accessibility, instance, modifiers);
        if synthesized && instance {
            flags |= method_attributes::HIDE_BY_SIG;
        }
        // An operator is a method with a special name: `op_Addition` is how
        // `+` is found, and the flag is what says the name means that.
        if matches!(
            detail.method_kind,
            rustlyn_semantics::MethodKind::Operator | rustlyn_semantics::MethodKind::Conversion
        ) {
            flags |= method_attributes::SPECIAL_NAME;
        }
        // A method that implements an interface member has to sit in a slot
        // of its own and may not be overridden out of it, or the interface's
        // call would reach something else.
        let explicit = instance.then(|| self.explicit_interface(method)).flatten();
        // A member of an interface is what C# 8 makes of what it wrote: a
        // slot of the interface's, abstract or with a body, or a method of
        // its own that nothing overrides.
        if interface && instance {
            flags = self.interface_member_flags(method, symbol.accessibility, explicit.is_some());
        } else if explicit.is_some() {
            // An explicit implementation is private, sealed and in a slot of
            // its own: nothing may call it by name and nothing may override
            // it. The `MethodImpl` row is what connects it to the interface —
            // the name does not.
            flags = method_attributes::PRIVATE
                | method_attributes::FINAL
                | method_attributes::VIRTUAL
                | method_attributes::NEW_SLOT
                | method_attributes::HIDE_BY_SIG;
        } else if !interface
            && instance
            && self.implements_an_interface_member(method)
            && !self.needs_forwarder(method)
        {
            flags |= implementing_flags(modifiers);
        }
        if synthesized && !instance {
            flags |= method_attributes::SPECIAL_NAME | method_attributes::HIDE_BY_SIG;
        }
        if constructor {
            flags |= method_attributes::SPECIAL_NAME | method_attributes::RT_SPECIAL_NAME;
        }
        // `[DllImport] static extern` has no body: its rows say which
        // library and entry point stand in for one.
        let mut impl_flags = 0;
        if let Some(import) = self.dll_import(method) {
            flags |= method_attributes::PINVOKE_IMPL;
            impl_flags |= method_impl::PRESERVE_SIG;
            self.note_pinvoke(token, import);
        }
        // A record's own members have symbols but no source: what they do
        // comes from what the record holds.
        // A method with a `yield` in it does not run its own body: it makes
        // the state machine that will, and hands it back.
        let iterates = !synthesized
            && !constructor
            && self.iterated_element(MachineKey::Member(method)).is_some()
            && self.iterator_refusal(MachineKey::Member(method)).is_none();
        // An `async` method does not run its own body either: it makes the
        // machine that will, starts it, and hands back the task.
        let awaits = !synthesized
            && !constructor
            && !iterates
            && self.is_async_method(method)
            && self.async_refusal(MachineKey::Member(method)).is_none();
        let source = if synthesized {
            MethodSource::RecordMember(method)
        } else if constructor && self.is_record_constructor(method) {
            MethodSource::RecordConstructor(method)
        } else if iterates {
            MethodSource::IteratorStart(MachineKey::Member(method))
        } else if awaits {
            MethodSource::AsyncStart(MachineKey::Member(method))
        } else {
            MethodSource::Declared(method)
        };
        if class_constructor {
            flags = method_attributes::PRIVATE
                | method_attributes::STATIC
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
                | method_attributes::RT_SPECIAL_NAME;
        }
        // An explicit implementation is named for the interface as Roslyn
        // writes it: `I<System.Int32[,][]>.Goo` for `I<int[][,]>.Goo`.
        let name = match &explicit {
            Some(declared) => format!(
                "{}.{}",
                self.explicit_prefix(declared),
                symbol.name.rsplit('.').next().unwrap_or_default()
            ),
            None => symbol.name.clone(),
        };
        let parameters: Vec<ParameterPlan> = detail
            .parameters
            .clone()
            .into_iter()
            .map(|symbol| ParameterPlan {
                by_ref: false,
                symbol: Some(symbol),
                name: symbols.get(symbol).name.clone(),
                ty: self.type_of(symbol),
            })
            .collect();
        let type_parameters = detail.type_parameters.clone();
        let return_type = if constructor {
            Type::Void
        } else {
            self.type_of(method)
        };
        if !instance && !interface && !constructor && explicit.is_none() {
            self.note_static_implementations(method, token);
        }
        let has_explicit = explicit.is_some();
        if let Some(declared) = explicit {
            self.note_explicit(method, token, &declared, None);
        }
        if synthesized && symbol.name == "<Clone>$" {
            self.note_clone_override(method, token);
        }
        // An override that returns a narrower type is another method to the
        // runtime, which matches by signature: it takes a slot of its own
        // and names the one it overrides.
        let covariant = !interface
            && instance
            && !has_explicit
            && !synthesized
            && self.note_covariant_override(method, token, false);
        if covariant {
            flags |= method_attributes::NEW_SLOT;
        }
        // An override the runtime would put into another method's slot takes
        // a slot of its own and names the one it overrides.
        if !covariant
            && !interface
            && instance
            && !has_explicit
            && !synthesized
            && let Some(overridden) = self.overridden_method(method)
            && let Some(owner) = self.compilation.symbols().get(overridden).container
            && self
                .compilation
                .symbols()
                .get(owner)
                .as_named_type()
                .is_some_and(|detail| detail.type_parameters.is_empty())
            && self.override_is_hidden(method, overridden)
            && let Some(class) = self
                .compilation
                .symbols()
                .get(method)
                .container
                .and_then(|container| self.types.get(&container).copied())
        {
            flags |= method_attributes::NEW_SLOT;
            self.explicit_impls.push(ExplicitImpl {
                class,
                body: token,
                declaration: Declaration::Override {
                    member: overridden,
                    through: Type::named(owner),
                },
            });
        }
        Ok(Some(MethodPlan {
            source,
            token,
            name,
            flags,
            instance,
            return_type,
            parameters,
            type_parameters,
            impl_flags,
            signature: None,
        }))
    }

    /// The flags of an instance member of an interface, or of one of its
    /// accessors, from what C# 8 makes of its modifiers.
    ///
    /// `void M();` is a slot with nothing in it and `void M() { }` a slot
    /// with a body — `newslot virtual`, and `abstract` for the first — while
    /// `sealed`, `private` and partial methods are plain instance methods no
    /// class can answer for. An `internal` or `private protected` slot is
    /// `strict`, so that only who can see it may fill it. An explicit
    /// implementation, `void I1.M() { }` in an interface deriving from `I1`,
    /// is private and final, and takes no slot of its own: it fills `I1`'s,
    /// through its `MethodImpl` row, and `abstract void I1.M();` empties it
    /// again.
    fn interface_member_flags(
        &self,
        member: SymbolId,
        accessibility: rustlyn_semantics::Accessibility,
        explicit: bool,
    ) -> u16 {
        use rustlyn_semantics::Accessibility as A;
        let modifiers = self.compilation.interface_member_modifiers(member);
        if explicit {
            return method_attributes::PRIVATE
                | method_attributes::HIDE_BY_SIG
                | method_attributes::VIRTUAL
                | method_attributes::FINAL
                | if modifiers.contains(Modifiers::ABSTRACT) {
                    method_attributes::ABSTRACT
                } else {
                    0
                };
        }
        // A private accessor of a virtual property is no slot either.
        let modifiers = if accessibility == A::Private {
            Modifiers::from_bits(modifiers.bits() & !Modifiers::VIRTUAL.bits())
        } else {
            modifiers
        };
        let mut flags =
            method_flags(accessibility, true, modifiers) | method_attributes::HIDE_BY_SIG;
        if flags & method_attributes::VIRTUAL != 0
            && flags & method_attributes::FINAL == 0
            && matches!(accessibility, A::Internal | A::ProtectedAndInternal)
        {
            flags |= method_attributes::STRICT;
        }
        flags
    }

    /// Whether a member belongs to an interface.
    fn declared_in_interface(&self, member: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        symbols
            .get(member)
            .container
            .is_some_and(|owner| symbols.get(owner).type_kind() == Some(TypeKind::Interface))
    }

    /// Whether a constructor is a record's positional one: it has parameters
    /// and no body, because the language rather than the source wrote it.
    fn is_record_constructor(&self, constructor: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        // An anonymous type's constructor fills its properties from its
        // parameters the way a record's positional one does.
        symbols.get(constructor).container.is_some_and(|container| {
            matches!(
                symbols.get(container).type_kind(),
                Some(TypeKind::Record | TypeKind::RecordStruct)
            ) || symbols
                .get(container)
                .as_named_type()
                .is_some_and(|detail| detail.anonymous)
        }) && self
            .compilation
            .declaration_node(constructor)
            .is_none_or(|node| node.kind() != SyntaxKind::ConstructorDeclaration)
    }

    /// Emits every body, returning the IL blob and where each body starts.
    fn generate(&mut self, plans: &[TypePlan]) -> Result<(Vec<u8>, Vec<Vec<u32>>), EmitError> {
        let mut il = Vec::new();
        let mut offsets = Vec::new();
        // `<Module>..cctor` calls the initializers one after another, and
        // does nothing else (§II.10.5.3.1: the runtime runs it before
        // anything else in the module is touched).
        if let Some((_, initializers, _)) = self.module_constructor.clone() {
            let mut stream = InstructionStream::new();
            for initializer in initializers {
                let Some(token) = self.methods.get(&initializer).copied() else {
                    continue;
                };
                stream.call_effect(Instruction::Call(token), 0, 0);
            }
            il = self.finish_body(stream, &[]);
        }
        for plan in plans {
            self.display_generics = self.display_parameters(plan);
            let mut type_offsets = Vec::new();
            for method in &plan.methods {
                // Abstract, or provided by the runtime: either way there is no
                // IL, and the row's RVA is zero.
                if method.flags & method_attributes::ABSTRACT != 0
                    || method.flags & method_attributes::PINVOKE_IMPL != 0
                    || method.impl_flags & method_impl::RUNTIME != 0
                {
                    type_offsets.push(u32::MAX);
                    continue;
                }
                self.method_generics = method.type_parameters.clone();
                self.dynamic_enclosing = Some(plan.symbol);
                self.dynamic_current = crate::dynamic::SiteContainer::default();
                let body = match BodyEmitter::emit(self, plan, method) {
                    Ok(body) => body,
                    // A body that cannot be written is fatal to a compile and
                    // not to a *survey* of one: the assembly is made with the
                    // method throwing where its code would have been, so that
                    // everything else about it can still be looked at.
                    Err(error) if self.lenient => {
                        let owner = self.compilation.symbols().qualified_name(plan.symbol);
                        self.skipped
                            .push((format!("{owner}.{}", method.name), error.message.clone()));
                        let constructor = self.not_implemented();
                        let said = self.metadata.user_string(&format!(
                            "{owner}.{} is not emitted: {}",
                            method.name, error.message
                        ));
                        stub_body(constructor, said)
                    }
                    Err(error) => return Err(error),
                };
                // A fat header has to start on a four-byte boundary.
                while il.len() % 4 != 0 {
                    il.push(0);
                }
                type_offsets.push(il.len() as u32);
                il.extend_from_slice(&body);
            }
            offsets.push(type_offsets);
        }
        self.method_generics = Vec::new();
        self.display_generics = Vec::new();
        Ok((il, offsets))
    }

    /// The type parameters a class the compiler made declares: the enclosing
    /// type's, then those of the method it was made for.
    fn display_generics_of(&self, owner: SymbolId, arity: usize) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let mut all = symbols
            .get(owner)
            .container
            .and_then(|container| symbols.get(container).as_named_type())
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        all.truncate(arity);
        all.extend(
            symbols
                .get(owner)
                .as_method()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default(),
        );
        all
    }

    /// The type parameters a plan's type declares, where the compiler made it.
    pub(crate) fn display_parameters(&mut self, plan: &TypePlan) -> Vec<SymbolId> {
        let Some(owner) = plan.display.or(plan.iterator) else {
            return Vec::new();
        };
        // A display class knows what it declares.
        if plan.display.is_some() && plan.machine.is_none() {
            let display = match plan.nested {
                None => self.displays.get(&owner),
                Some(outer) => self.nested_displays.get(&(owner, outer)),
            };
            if let Some(display) = display.filter(|display| !display.generics.is_empty()) {
                return display.generics.clone();
            }
        }
        // A local function's machine declares the function's own after them.
        let function = plan
            .machine
            .map(|key| self.function_generics(key))
            .unwrap_or_default();
        let symbols = self.compilation.symbols();
        let mut all = symbols
            .get(plan.symbol)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        all.extend(
            symbols
                .get(owner)
                .as_method()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default(),
        );
        all.extend(function);
        all
    }

    /// Adds the rows, in the order the plan predicted their tokens from.
    /// Adds the classes the `dynamic` operations made while their bodies
    /// were emitted to the plan, after everything planned before.
    /// A row of `<PrivateImplementationDetails>` (`None`) or of the struct
    /// of one blob size nested in it.
    fn write_array_data_type(
        &mut self,
        plan: &TypePlan,
        size: Option<u32>,
        type_offsets: &[u32],
    ) -> Result<(), EmitError> {
        let Some(size) = size else {
            let object = self
                .references
                .type_ref_coded(&mut self.metadata, "System.Object");
            let token = self.metadata.add_type_def(
                type_attributes::SEALED | type_attributes::AUTO_LAYOUT_ANSI_CLASS,
                "",
                "<PrivateImplementationDetails>",
                object,
            );
            predicted(token, plan.token, "<PrivateImplementationDetails>")?;
            self.mark_compiler_generated(token);
            self.write_members(plan, type_offsets)?;
            for (field, offset) in self.array_data_offsets.clone() {
                self.metadata
                    .add_field_rva(field, crate::pe::data_rva(offset));
            }
            return Ok(());
        };
        let value_type = self
            .references
            .type_ref_coded(&mut self.metadata, "System.ValueType");
        let token = self.metadata.add_type_def(
            type_attributes::NESTED_ASSEMBLY
                | type_attributes::EXPLICIT_LAYOUT
                | type_attributes::SEALED,
            "",
            &array_data_type_name(size),
            value_type,
        );
        predicted(token, plan.token, "a struct of array data")?;
        if let Some((details, _)) = self
            .array_data_types
            .iter()
            .find(|(_, size)| size.is_none())
        {
            self.metadata.add_nested_class(token, *details);
        }
        self.metadata.add_class_layout(token, 1, size);
        Ok(())
    }

    fn take_site_containers(&mut self, plans: &mut Vec<TypePlan>, offsets: &mut Vec<Vec<u32>>) {
        for (plan, row) in std::mem::take(&mut self.dynamic_containers) {
            self.dynamic_rows.insert(plan.token, row);
            offsets.push(vec![u32::MAX; plan.methods.len()]);
            plans.push(plan);
        }
    }

    fn write_rows(&mut self, plans: &[TypePlan], offsets: &[Vec<u32>]) -> Result<(), EmitError> {
        self.nullable_on = self.nullable_wanted();
        for plan in plans {
            if let Some(key) = plan.machine {
                let name = self.machine_type_name(key, plan);
                self.machine_type_names.insert(key, name);
            }
        }
        // Every type has its token by now, which is what naming the interface
        // member of an explicit implementation was waiting for.
        self.write_method_impls()?;
        // `<Module>` has to be the first row of `TypeDef`, and extends nothing.
        self.metadata.add_type_def(0, "", "<Module>", 0);
        if let Some((token, _, offset)) = self.module_constructor.clone() {
            let signature = method_signature(false, &SigType::Primitive(ElementType::Void), &[]);
            let written = self.metadata.add_method(
                method_attributes::PRIVATE
                    | method_attributes::STATIC
                    | method_attributes::HIDE_BY_SIG
                    | method_attributes::SPECIAL_NAME
                    | method_attributes::RT_SPECIAL_NAME,
                0,
                ".cctor",
                &signature,
                Some(offset),
                &[],
            );
            predicted(written, token, ".cctor")?;
        }
        // `[assembly: X]` goes on the one `Assembly` row, which is a
        // `HasCustomAttribute` parent tagged 14.
        let has_extensions = plans.iter().any(|plan| {
            plan.methods.iter().any(|method| {
                method
                    .source
                    .written_member()
                    .is_some_and(|symbol| self.is_extension_method(symbol))
            })
        });
        if has_extensions {
            self.mark_extension((1 << 5) | 14);
        }
        self.mark_assembly_relaxations();
        // C# 11 and later say which rules for `ref` safety a module was
        // compiled under, on the `Module` row (tagged 7): another compilation
        // reads its signatures by them.
        if self
            .compilation
            .language_version()
            .at_least(rustlyn_syntax::LanguageVersion::CSharp11)
            && self
                .compilation
                .type_by_metadata_name("System.Runtime.CompilerServices.RefSafetyRulesAttribute")
                .is_some()
        {
            let constructor = self.references.member_ref(
                &mut self.metadata,
                "System.Runtime.CompilerServices.RefSafetyRulesAttribute",
                ".ctor",
                &method_signature(
                    true,
                    &SigType::Primitive(ElementType::Void),
                    &[SigType::Primitive(ElementType::I4)],
                ),
            );
            let mut blob = vec![0x01, 0x00];
            blob.extend_from_slice(&11i32.to_le_bytes());
            blob.extend_from_slice(&[0x00, 0x00]);
            self.metadata.add_custom_attribute(
                (1 << 5) | 7,
                ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
                &blob,
            );
        }
        for tree in 0..self.compilation.trees().len() {
            let Some(root) = self.compilation.trees().get(tree).map(|tree| tree.root()) else {
                continue;
            };
            self.write_attribute_lists((1 << 5) | 14, tree, &root, AttributeTarget::Assembly)?;
        }

        for (plan, type_offsets) in plans.iter().zip(offsets) {
            // `<PrivateImplementationDetails>`, holding the blobs array
            // initializers are copied out of, and a struct of each blob size.
            if let Some(size) = self.array_data_types.get(&plan.token).copied() {
                self.write_array_data_type(plan, size, type_offsets)?;
                continue;
            }
            // The class a body keeps its `dynamic` call sites in: static,
            // nested in the type the body belongs to, fields and nothing else.
            if let Some(crate::dynamic::SiteRow::Delegate(name)) =
                self.dynamic_rows.get(&plan.token).cloned()
            {
                let base = self
                    .references
                    .type_ref_coded(&mut self.metadata, "System.MulticastDelegate");
                let token = self.metadata.add_type_def(
                    type_attributes::SEALED | type_attributes::AUTO_LAYOUT_ANSI_CLASS,
                    "",
                    &name,
                    base,
                );
                predicted(token, plan.token, "a delegate of call sites")?;
                self.mark_compiler_generated(token);
                self.write_members(plan, type_offsets)?;
                continue;
            }
            if let Some(crate::dynamic::SiteRow::Container {
                enclosing,
                name,
                arity,
            }) = self.dynamic_rows.get(&plan.token).cloned()
            {
                let object = self
                    .references
                    .type_ref_coded(&mut self.metadata, "System.Object");
                let token = self.metadata.add_type_def(
                    type_attributes::NESTED_PRIVATE
                        | type_attributes::ABSTRACT
                        | type_attributes::SEALED
                        | type_attributes::BEFORE_FIELD_INIT,
                    "",
                    &name,
                    object,
                );
                predicted(token, plan.token, "a class of call sites")?;
                self.metadata.add_nested_class(token, enclosing);
                self.mark_compiler_generated(token);
                // A `TypeOrMethodDef` owner tagged 0 is a `TypeDef`.
                let owner = (token.0 & 0x00FF_FFFF) << 1;
                for number in 0..arity {
                    self.metadata
                        .add_generic_param(number as u16, 0, owner, &format!("T{number}"));
                }
                self.write_members(plan, type_offsets)?;
                continue;
            }
            // The struct behind a `fixed` buffer: nested in the type that
            // declares the buffer, laid out sequentially at the size the
            // buffer is.
            if let Some((name, size)) = self.fixed_buffer_types.get(&plan.token).cloned() {
                let value_type = self
                    .references
                    .type_ref_coded(&mut self.metadata, "System.ValueType");
                let token = self.metadata.add_type_def(
                    type_attributes::NESTED_PUBLIC
                        | type_attributes::SEALED
                        | type_attributes::SEQUENTIAL_LAYOUT
                        | type_attributes::BEFORE_FIELD_INIT,
                    "",
                    &name,
                    value_type,
                );
                predicted(token, plan.token, "a fixed buffer")?;
                if let Some(enclosing) = self.types.get(&plan.symbol).copied() {
                    self.metadata.add_nested_class(token, enclosing);
                }
                // The language's, and holding what no reference may point
                // into, which the runtime is told not to let one.
                self.mark_compiler_generated(token);
                self.mark_with(
                    ((token.0 & 0x00FF_FFFF) << 5) | 3,
                    "System.Runtime.CompilerServices.UnsafeValueTypeAttribute",
                );
                self.metadata.add_class_layout(token, 0, size);
                self.write_members(plan, type_offsets)?;
                continue;
            }
            // A display class is not a declared type: it is nested in the one
            // whose member made it, extends `object`, and is as unspeakable as
            // the methods it holds.
            if let Some(key) = plan.machine {
                if self.asyncs.contains_key(&key) {
                    self.write_async_type(plan, key, type_offsets)?;
                } else {
                    self.write_iterator_type(plan, key, type_offsets)?;
                }
                continue;
            }
            if let Some(singleton) = self.singleton_types.get(&plan.token).copied() {
                self.write_singleton_type(plan, singleton.enclosing, type_offsets)?;
                continue;
            }
            if let Some(owner) = plan.display {
                // `<>c__DisplayClass0_1`: the member's number, and the class's
                // among the member's — its own first, then the nested ones
                // outermost first.
                let method = self.method_ordinal(owner);
                let closure = match plan.nested {
                    None => 0,
                    Some(outer) => {
                        usize::from(self.displays.contains_key(&owner))
                            + self
                                .nested_display_owners(owner)
                                .iter()
                                .position(|it| *it == outer)
                                .unwrap_or(0)
                    }
                };
                let name = format!("<>c__DisplayClass{method}_{closure}");
                let object = self
                    .references
                    .type_ref_coded(&mut self.metadata, "System.Object");
                let token = self.metadata.add_type_def(
                    type_attributes::NESTED_PRIVATE
                        | type_attributes::SEALED
                        | type_attributes::BEFORE_FIELD_INIT,
                    "",
                    &name,
                    object,
                );
                predicted(token, plan.token, "a display class")?;
                if let Some(enclosing) = self.types.get(&plan.symbol).copied() {
                    self.metadata.add_nested_class(token, enclosing);
                }
                self.mark_compiler_generated(token);
                // A display class inside a generic type declares that type's
                // parameters as its own, the way any nested type does, and one
                // over a generic method declares that method's after them: the
                // values it holds are of those types.
                let inherited = self.display_parameters(plan);
                let owner = (token.0 & 0x00FF_FFFF) << 1;
                // The constraints below are written in terms of the class's
                // own parameters, so those have to be in force first: `where
                // T : IResult<TMember>` on a method names `!!1`, and on the
                // class made over it the same constraint names `!1`.
                self.display_generics = inherited.clone();
                for (number, parameter) in inherited.iter().enumerate() {
                    let name = self.compilation.symbols().get(*parameter).name.clone();
                    // The same constraints the enclosing type wrote: the class
                    // holds values of that parameter, and a construction of it
                    // has to be one the enclosing type would accept.
                    let flags =
                        generic_param_flags(self.compilation.symbols(), *parameter) & !0x0003u16;
                    self.metadata
                        .add_generic_param(number as u16, flags, owner, &name);
                    self.write_constraints(owner, number as u16, *parameter)?;
                }
                // The class's own parameters are what its members name, so
                // a signature written here says `!0` where the method that
                // makes one says `!!0`.
                self.display_generics = inherited;
                let written = self.write_members(plan, type_offsets);
                self.display_generics = Vec::new();
                written?;
                continue;
            }
            let symbols = self.compilation.symbols();
            let symbol = symbols.get(plan.symbol);
            let namespace = namespace_of(self.compilation, plan.symbol);
            let kind = symbol.type_kind();
            let interface = kind == Some(TypeKind::Interface);
            let enumeration = kind == Some(TypeKind::Enum);
            // An interface extends nothing: what it lists are interfaces, and
            // those are rows of their own.
            let value_type = matches!(kind, Some(TypeKind::Struct | TypeKind::RecordStruct));
            let extends = if interface {
                0
            } else if enumeration {
                self.references
                    .type_ref_coded(&mut self.metadata, "System.Enum")
            } else if value_type {
                self.references
                    .type_ref_coded(&mut self.metadata, "System.ValueType")
            } else {
                self.base_type_coded(plan.symbol)?
            };
            let mut flags = type_attributes::AUTO_LAYOUT_ANSI_CLASS;
            // `beforefieldinit` says the runtime may run the class
            // constructor whenever it likes before the first static field is
            // read. A type that *wrote* one means it to run at a point it can
            // reason about, so the flag is not theirs to have (§II.10.5.3.3).
            let declares_static_constructor = self
                .compilation
                .symbols()
                .get(plan.symbol)
                .members
                .iter()
                .any(|member| {
                    let symbol = self.compilation.symbols().get(*member);
                    symbol.name == ".cctor"
                });
            if interface {
                flags |= type_attributes::INTERFACE | type_attributes::ABSTRACT;
                // An interface's static fields are initialised as a class's
                // are (C# 8), and the flag means the same for them.
                if !declares_static_constructor {
                    flags |= type_attributes::BEFORE_FIELD_INIT;
                }
            } else if enumeration || kind == Some(TypeKind::Delegate) {
                // The runtime refuses a delegate that is not sealed: it writes
                // the bodies, so nothing may derive from one and change them.
                flags |= type_attributes::SEALED;
            } else if value_type {
                // A struct cannot be derived from, and its fields are laid out
                // in the order they were written, which is what C# promises —
                // unless `[StructLayout(LayoutKind.Explicit)]` puts each where
                // its `[FieldOffset]` says.
                flags |= type_attributes::SEALED;
                flags |= match self.struct_layout(plan.symbol) {
                    Some(layout) if layout.explicit => type_attributes::EXPLICIT_LAYOUT,
                    _ => type_attributes::SEQUENTIAL_LAYOUT,
                };
                if !declares_static_constructor {
                    flags |= type_attributes::BEFORE_FIELD_INIT;
                }
            } else if !declares_static_constructor {
                flags |= type_attributes::BEFORE_FIELD_INIT;
            }
            // A nested type's visibility is a different set of values, and
            // the table is the only thing that says where it sits: its own row
            // carries no namespace and only the simple name.
            let enclosing = self
                .compilation
                .symbols()
                .get(plan.symbol)
                .container
                .filter(|container| {
                    self.compilation.symbols().get(*container).kind == SymbolKind::NamedType
                })
                .and_then(|container| self.types.get(&container).copied());
            let symbol = self.compilation.symbols().get(plan.symbol);
            if enclosing.is_some() {
                flags |= nested_visibility(symbol.accessibility);
            } else if symbol.accessibility == rustlyn_semantics::Accessibility::Public {
                flags |= type_attributes::PUBLIC;
            }
            if symbol.modifiers.contains(Modifiers::ABSTRACT) {
                flags |= type_attributes::ABSTRACT;
            }
            if symbol.modifiers.contains(Modifiers::SEALED) {
                flags |= type_attributes::SEALED;
            }
            // A static class is both in metadata: nothing may make one, and
            // nothing may derive from it (§II.10.1.4), which is also how
            // another compiler knows it is static.
            if symbol.modifiers.contains(Modifiers::STATIC)
                && symbol.type_kind() == Some(TypeKind::Class)
            {
                flags |= type_attributes::ABSTRACT | type_attributes::SEALED;
            }
            if self.binder.is_com_import(plan.symbol) {
                flags |= type_attributes::IMPORT;
            }
            // `Box<T>` is `Box`1` in metadata: the arity is part of the name,
            // which is how two types of the same name are told apart.
            let name = self
                .synthesized_names
                .get(&plan.symbol)
                .cloned()
                .unwrap_or_else(|| self.compilation.metadata_name_of(plan.symbol));
            let parameters: Vec<SymbolId> = symbol
                .as_named_type()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            let token = self
                .metadata
                .add_type_def(flags, &namespace, &name, extends);
            predicted(token, plan.token, &name)?;
            if let Some(enclosing) = enclosing {
                self.metadata.add_nested_class(token, enclosing);
            }
            // The type's own attributes go on its row and on no other plan
            // that carries its symbol — a display class or a buffer struct
            // — which is what comparing the tokens rules out.
            if self.types.get(&plan.symbol) == Some(&plan.token) {
                self.write_type_attributes(plan, token)?;
            }
            // `[StructLayout(..., Size = 1, Pack = 4)]` is a row of its own,
            // and so is each `[FieldOffset(n)]`.
            let layout = self.struct_layout(plan.symbol);
            if let Some(layout) = &layout
                && (layout.size.is_some() || layout.pack.is_some())
            {
                self.metadata.add_class_layout(
                    token,
                    layout.pack.unwrap_or(0),
                    layout.size.unwrap_or(0),
                );
            }
            // A struct with no instance field is one byte, and says so where
            // no `[StructLayout]` says otherwise, as Roslyn has it: the
            // tag components of an ECS are thousands of them.
            if layout.is_none()
                && self.types.get(&plan.symbol) == Some(&plan.token)
                && matches!(
                    self.compilation.symbols().get(plan.symbol).type_kind(),
                    Some(TypeKind::Struct | TypeKind::RecordStruct)
                )
                && plan
                    .fields
                    .iter()
                    .all(|field| field.flags & field_attributes::STATIC != 0)
            {
                self.metadata.add_class_layout(token, 0, 1);
            }
            for field in &plan.fields {
                if let Some(member) = field.symbol
                    && self.compilation.symbols().get(member).kind == SymbolKind::Field
                    && let Some(offset) = self.field_offset(member)
                {
                    self.metadata.add_field_layout(field.token, offset);
                }
            }
            // A `TypeOrMethodDef` owner tagged 0 is a `TypeDef`.
            let owner = (token.0 & 0x00FF_FFFF) << 1;
            let own_type = self.types.get(&plan.symbol) == Some(&plan.token);
            let context = if self.nullable_on && own_type {
                self.type_effective_context(plan.symbol)
            } else {
                None
            };
            for (number, parameter) in parameters.iter().enumerate() {
                let name = self.compilation.symbols().get(*parameter).name.clone();
                let flags = generic_param_flags(self.compilation.symbols(), *parameter);
                self.metadata
                    .add_generic_param(number as u16, flags, owner, &name);
                let written = self.write_constraints(owner, number as u16, *parameter)?;
                if self.nullable_on && own_type {
                    self.mark_type_parameter_nullable(
                        owner,
                        number as u16,
                        *parameter,
                        &written,
                        context,
                    );
                }
                self.write_type_parameter_attributes(owner, number as u16, *parameter)?;
            }

            // The interfaces a type implements are rows of their own; a base
            // class is a column, an interface is not.
            // What the base class and the interfaces name that metadata
            // types cannot say — `Base<(int x, int y)>`'s element names, a
            // `dynamic` type argument — goes on the type's row and on each
            // `InterfaceImpl` row, where another compilation looks for it.
            for interface in self.implemented_interfaces(plan.symbol) {
                let coded = self.type_coded(&interface)?;
                let row = self.metadata.add_interface_impl(token, coded);
                self.mark_dynamic((row << 5) | 5, &interface, false);
                self.mark_tuple_names((row << 5) | 5, &interface);
                if self.nullable_on && own_type {
                    let flags = self.interface_flags(plan.symbol, &interface);
                    self.mark_nullable((row << 5) | 5, &flags, context);
                }
            }

            self.write_members(plan, type_offsets)?;
        }
        Ok(())
    }

    /// The fields, properties and methods of one planned type.
    pub(crate) fn write_members(
        &mut self,
        plan: &TypePlan,
        type_offsets: &[u32],
    ) -> Result<(), EmitError> {
        {
            let token = plan.token;
            // The context the type's members are read in, where it is a
            // type the program declared and nullable metadata is written.
            let nullable = (self.nullable_on && self.types.get(&plan.symbol) == Some(&plan.token))
                .then(|| self.type_effective_context(plan.symbol));
            // A lambda or a local function in a class made for the type's
            // closures is read in the type's context too; nothing else such
            // a class holds carries annotations.
            let closures = (self.nullable_on && !self.synthesized_names.contains_key(&plan.symbol))
                .then(|| self.type_effective_context(plan.symbol));
            for field in &plan.fields {
                let signature = {
                    let ty = match &field.sig {
                        Some(sig) => sig.clone(),
                        None => self.sig_type(&field.ty)?,
                    };
                    field_signature(&ty)
                };
                let token = self
                    .metadata
                    .add_field(field.flags, &field.name, &signature);
                predicted(token, field.token, &field.name)?;
                // A `HasCustomAttribute` parent tagged 1 is a `Field`. What
                // the language says of a field comes before what the source
                // wrote, in Roslyn's order.
                let parent = ((token.0 & 0x00FF_FFFF) << 5) | 1;
                // `dynamic` is `object` with a `[Dynamic]` saying which.
                if field.symbol.is_some() && field.sig.is_none() {
                    self.mark_dynamic(parent, &field.ty, false);
                    self.mark_tuple_names(parent, &field.ty);
                }
                // The field behind a property or an event is of its type.
                if let Some(context) = nullable
                    && let Some(symbol) = field.symbol
                {
                    let flags = self.symbol_flags(symbol);
                    self.mark_nullable(parent, &flags, context);
                }
                if let Some(constant) = &field.constant {
                    let special = self.constant_width(&field.ty);
                    let (element, value) = encode_constant_as(constant, special);
                    self.metadata.add_constant(token, element, &value);
                }
                if field.constant.is_none()
                    && let Some(symbol) = field.symbol
                    && self
                        .compilation
                        .symbols()
                        .get(symbol)
                        .modifiers
                        .contains(Modifiers::CONST)
                    && let Some(parts) = self.decimal_constant(symbol, 0)
                {
                    self.mark_decimal_constant(parent, parts);
                }
                // `fixed int x[10]` says what it is with `[FixedBuffer]`: the
                // element type and the length, which is all another
                // compilation has to read it back as a buffer by.
                if let Some(symbol) = field.symbol
                    && self.fixed_buffers.contains_key(&symbol)
                {
                    self.mark_fixed_buffer(parent, symbol);
                }
                if let Some(symbol) = field.symbol
                    && self.compilation.symbols().get(symbol).kind == SymbolKind::Field
                    && self
                        .compilation
                        .symbols()
                        .get(symbol)
                        .modifiers
                        .contains(Modifiers::REQUIRED)
                {
                    self.mark_with(
                        parent,
                        "System.Runtime.CompilerServices.RequiredMemberAttribute",
                    );
                }
                // The field behind an automatic property or a field-like
                // event is the language's, and says so; a debug build hides
                // it from the debugger's view too.
                if self.is_anonymous_type(plan.symbol) {
                    // An anonymous type's fields are hidden from the
                    // debugger's view in every build, and say nothing more.
                    self.mark_debugger_browsable_never(parent);
                } else if let Some(symbol) = field.symbol
                    && matches!(
                        self.compilation.symbols().get(symbol).kind,
                        SymbolKind::Property | SymbolKind::Event
                    )
                {
                    self.mark_with(
                        parent,
                        "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
                    );
                    if !self.compilation.options().optimize {
                        self.mark_debugger_browsable_never(parent);
                    }
                }
                // The field a property backs carries the property's symbol:
                // the property's attributes are the property's, but for
                // those written `field:` — `[field: SerializeField]`, which
                // Unity serializes the field by.
                if let Some(symbol) = field.symbol {
                    match self.compilation.symbols().get(symbol).kind {
                        SymbolKind::Field => {
                            self.write_custom_attributes(parent, symbol, AttributeTarget::Field)?;
                        }
                        SymbolKind::Property => {
                            self.write_custom_attributes(
                                parent,
                                symbol,
                                AttributeTarget::PropertyField,
                            )?;
                        }
                        _ => {}
                    }
                }
                // `[ThreadStatic]` is read by the runtime itself: without the
                // attribute in metadata a per-thread field is one field for
                // every thread.
                if let Some(symbol) = field.symbol
                    && self.compilation.symbols().get(symbol).kind == SymbolKind::Field
                    && self.attribute_on(symbol, "ThreadStatic").is_some()
                {
                    self.mark_thread_static(token);
                }
            }

            // A property's rows say that two methods belong together; the
            // methods themselves are added below like any other.
            if !plan.properties.is_empty() {
                self.metadata.add_property_map(token);
                for property in &plan.properties.clone() {
                    let mut ty = self.sig_type(&property.ty)?;
                    if let Some(symbol) = property.symbol {
                        ty = self.returned_sig(symbol, ty);
                    }
                    let symbols = self.compilation.symbols();
                    let declared = property
                        .symbol
                        .and_then(|symbol| symbols.get(symbol).as_property())
                        .map(|detail| detail.parameters.clone())
                        .unwrap_or_default();
                    let mut parameters = Vec::with_capacity(property.parameters.len());
                    for (at, parameter) in property.parameters.iter().enumerate() {
                        let ty = self.sig_type(parameter)?;
                        parameters.push(match declared.get(at) {
                            Some(symbol) => self.parameter_sig(*symbol, ty),
                            None => ty,
                        });
                    }
                    let signature = property_signature(property.instance, &ty, &parameters);
                    let token = self.metadata.add_property(
                        &property.name,
                        &signature,
                        property.getter,
                        property.setter,
                    );
                    // A `HasCustomAttribute` parent tagged 9 is a `Property`.
                    self.mark_dynamic(((token.0 & 0x00FF_FFFF) << 5) | 9, &property.ty, false);
                    self.mark_tuple_names(((token.0 & 0x00FF_FFFF) << 5) | 9, &property.ty);
                    if let Some(context) = nullable
                        && let Some(symbol) = property.symbol
                    {
                        let flags = self.symbol_flags(symbol);
                        self.mark_nullable(((token.0 & 0x00FF_FFFF) << 5) | 9, &flags, context);
                    }
                    if let Some(symbol) = property.symbol {
                        let parent = ((token.0 & 0x00FF_FFFF) << 5) | 9;
                        let symbols = self.compilation.symbols();
                        if symbols.get(symbol).modifiers.contains(Modifiers::REQUIRED) {
                            self.mark_with(
                                parent,
                                "System.Runtime.CompilerServices.RequiredMemberAttribute",
                            );
                        }
                        // A record's `EqualityContract` is the language's.
                        if symbols.get(symbol).as_property().is_some_and(|detail| {
                            detail.synthesized
                                == Some(rustlyn_semantics::SynthesizedType::SystemType)
                        }) {
                            self.mark_with(
                                parent,
                                "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
                            );
                        }
                    }
                    if let Some(symbol) = property.symbol {
                        self.write_custom_attributes(
                            ((token.0 & 0x00FF_FFFF) << 5) | 9,
                            symbol,
                            AttributeTarget::Property,
                        )?;
                    }
                }
            }

            // The type's events: an `EventMap` row opening its run, and one
            // `Event` row per event naming its accessors.
            if self.types.get(&plan.symbol) == Some(&plan.token)
                && let Some(events) = self.events_of.get(&plan.symbol).cloned()
                && !events.is_empty()
            {
                self.metadata.add_event_map(plan.token);
                for event in events {
                    let event_type = self.type_token(&event.ty)?;
                    let tag = match (event_type.0 >> 24) as u8 {
                        table::TYPE_DEF => 0,
                        table::TYPE_REF => 1,
                        _ => 2,
                    };
                    let row = self.metadata.add_event(
                        &event.name,
                        type_def_or_ref(tag, event_type.0 & 0x00FF_FFFF),
                        Some(event.add),
                        Some(event.remove),
                    );
                    // A `HasCustomAttribute` parent tagged 10 is an `Event`.
                    self.mark_dynamic(((row.0 & 0x00FF_FFFF) << 5) | 10, &event.ty, false);
                    self.mark_tuple_names(((row.0 & 0x00FF_FFFF) << 5) | 10, &event.ty);
                    if let Some(context) = nullable {
                        let flags = self.symbol_flags(event.symbol);
                        self.mark_nullable(((row.0 & 0x00FF_FFFF) << 5) | 10, &flags, context);
                    }
                    self.write_custom_attributes(
                        ((row.0 & 0x00FF_FFFF) << 5) | 10,
                        event.symbol,
                        AttributeTarget::Event,
                    )?;
                }
            }

            // A type the program declared, rather than one made for it.
            let declared_type = self.types.get(&plan.symbol) == Some(&plan.token);
            for (method, offset) in plan.methods.iter().zip(type_offsets) {
                self.method_generics = method.type_parameters.clone();
                let signature = self.method_signature_of(method)?;
                // A partial method's parameters are named in metadata as its
                // declaring part wrote them.
                let declared: Vec<Option<String>> = match method.source {
                    MethodSource::Declared(symbol) => {
                        let symbols = self.compilation.symbols();
                        symbols
                            .get(symbol)
                            .as_method()
                            .map(|detail| {
                                detail
                                    .parameters
                                    .iter()
                                    .map(|parameter| {
                                        symbols
                                            .get(*parameter)
                                            .as_parameter()
                                            .and_then(|detail| detail.declared_name.clone())
                                    })
                                    .collect()
                            })
                            .unwrap_or_default()
                    }
                    _ => Vec::new(),
                };
                let names: Vec<String> = method
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(index, parameter)| {
                        declared
                            .get(index)
                            .cloned()
                            .flatten()
                            .unwrap_or_else(|| parameter.name.clone())
                    })
                    .collect();
                let body = (*offset != u32::MAX).then_some(*offset);
                let written = self.written_impl_flags(&method.source);
                // Every method C# writes hides by signature, never by name
                // (Roslyn's `HidesBaseMethodsByName` is false for all).
                let token = self.metadata.add_method(
                    method.flags | method_attributes::HIDE_BY_SIG,
                    method.impl_flags
                        | written
                        | if self.lenient && method.impl_flags & method_impl::RUNTIME == 0 {
                            method_impl::NO_INLINING
                        } else {
                            0
                        },
                    &method.name,
                    &signature,
                    body,
                    &names,
                );
                predicted(token, method.token, &method.name)?;
                let shape = if nullable.is_some() || closures.is_some() {
                    self.method_nullable_shape(plan.symbol, method)
                } else {
                    None
                };
                let nullable_return = shape
                    .as_ref()
                    .filter(|shape| Self::nullable_needed(&shape.returns, shape.effective));
                let return_attributes = match method.source {
                    MethodSource::Declared(symbol) => self.has_return_attributes(symbol),
                    _ => self
                        .local_function_of(&method.source)
                        .and_then(|function| self.has_return_attributes(function)),
                };
                // `[return: A] x => x` says it on the lambda.
                let lambda_returns = match method.source {
                    MethodSource::Lambda { owner, index }
                    | MethodSource::AsyncStart(MachineKey::Lambda { owner, index }) => {
                        self.lambda_node(owner, index).filter(|(_, node)| {
                            !attributes_for(node, AttributeTarget::Return).is_empty()
                        })
                    }
                    _ => None,
                };
                // A `ref readonly` return is marked read-only on the return's
                // row, as an `in` parameter is on its own.
                let readonly_return = match method.source {
                    MethodSource::PropertyGetter { property, .. } => self
                        .compilation
                        .symbols()
                        .get(property)
                        .as_property()
                        .is_some_and(|detail| detail.returns_readonly),
                    _ => method.source.written_member().is_some_and(|symbol| {
                        let symbols = self.compilation.symbols();
                        match symbols.get(symbol).container.map(|c| symbols.get(c).kind) {
                            Some(SymbolKind::Property) => {
                                symbols
                                    .get(symbols.get(symbol).container.unwrap_or(symbol))
                                    .as_property()
                                    .is_some_and(|detail| detail.returns_readonly)
                                    && symbols.get(symbol).name.starts_with("get_")
                            }
                            _ => symbols
                                .get(symbol)
                                .as_method()
                                .is_some_and(|detail| detail.returns_readonly),
                        }
                    }),
                };
                if crate::dynamic::mentions_dynamic_type(&method.return_type)
                    || !tuple_names(&method.return_type).is_empty()
                    || return_attributes.is_some()
                    || lambda_returns.is_some()
                    || nullable_return.is_some()
                    || readonly_return
                {
                    let returns = self.metadata.add_return_param(token);
                    let parent = ((returns.0 & 0x00FF_FFFF) << 5) | 4;
                    if readonly_return {
                        self.mark_with(
                            parent,
                            "System.Runtime.CompilerServices.IsReadOnlyAttribute",
                        );
                    }
                    self.mark_dynamic(parent, &method.return_type, false);
                    self.mark_tuple_names(parent, &method.return_type);
                    if let Some(shape) = nullable_return {
                        self.mark_nullable(parent, &shape.returns, shape.effective);
                    }
                    if let Some(symbol) = return_attributes {
                        self.write_custom_attributes(parent, symbol, AttributeTarget::Return)?;
                    }
                    if let Some((tree, node)) = lambda_returns {
                        self.write_attribute_lists(parent, tree, &node, AttributeTarget::Return)?;
                    }
                }
                // After the return's row, which goes ahead of the parameters'
                // and would move any row an attribute was put on before it.
                self.write_method_attributes(
                    plan.symbol,
                    method,
                    token,
                    declared_type,
                    shape.as_ref(),
                )?;
                self.write_parameter_rows(token, &method.parameters, shape.as_ref())?;
                if let Some(originals) = self.cloned_parameters.get(&token).cloned() {
                    self.write_cloned_parameter_rows(token, &originals)?;
                }
                if let MethodSource::Lambda { owner, index } = method.source {
                    self.mark_lambda_params(token, owner, index);
                }

                // A `TypeOrMethodDef` owner tagged 1 is a `MethodDef`.
                let owner = ((token.0 & 0x00FF_FFFF) << 1) | 1;
                // C# forbids an override from restating the constraints it
                // inherits, so the source says nothing and the row would be
                // weaker than the one it overrides — which the runtime
                // refuses. They come from the method being overridden.
                let inherited_from = match method.source {
                    MethodSource::Declared(symbol) => self
                        .overridden_method(symbol)
                        .and_then(|base| self.compilation.symbols().get(base).as_method())
                        .map(|detail| detail.type_parameters.clone()),
                    _ => None,
                };
                for (number, own) in method.type_parameters.clone().iter().enumerate() {
                    let parameter = &inherited_from
                        .as_ref()
                        .and_then(|list| list.get(number).copied())
                        .unwrap_or(*own);
                    let symbol = self.compilation.symbols().get(*parameter);
                    let name = symbol
                        .as_type_parameter()
                        .and_then(|detail| detail.declared_name.clone())
                        .unwrap_or_else(|| symbol.name.clone());
                    // A method's own type parameter is never variant; its
                    // constraints are its own like any other's.
                    let flags =
                        generic_param_flags(self.compilation.symbols(), *parameter) & !0x0003u16;
                    self.metadata
                        .add_generic_param(number as u16, flags, owner, &name);
                    // The constraint types are the overridden method's said
                    // in this one's terms: its `T` is what this class says
                    // the base class's `T` is.
                    let written = self.write_constraints(owner, number as u16, *own)?;
                    if let Some(shape) = &shape {
                        self.mark_type_parameter_nullable(
                            owner,
                            number as u16,
                            *own,
                            &written,
                            shape.effective,
                        );
                    }
                    self.write_type_parameter_attributes(owner, number as u16, *own)?;
                }
                self.method_generics = Vec::new();
            }
        }
        Ok(())
    }

    /// What an `async Main` hands the runtime once its task is waited on:
    /// nothing for a `Task`, the `T` of a `Task<T>`, and `None` for a `Main`
    /// that is not `async` at all.
    fn awaited_main_result(&self, returns: &Type) -> Option<Type> {
        let Type::Named {
            symbol,
            type_arguments,
        } = returns
        else {
            return None;
        };
        match self.compilation.symbols().qualified_name(*symbol).as_str() {
            "System.Threading.Tasks.Task" => Some(Type::Void),
            "System.Threading.Tasks.Task`1" => type_arguments.first().cloned(),
            _ => None,
        }
    }

    /// The token of the method the runtime starts at.
    fn entry_point(&self, plans: &[TypePlan], main_type: Option<&str>) -> Result<Token, EmitError> {
        // Top-level statements are the entry point, whatever else is called
        // `Main` (which the language warns about and ignores); an `async`
        // one starts at the `<Main>` around it. A main type named looks in
        // that type alone, top-level statements or not.
        let symbols = self.compilation.symbols();
        let in_main_type = |plan: &&TypePlan| {
            main_type.is_none_or(|wanted| {
                plan.display.is_none()
                    && plan.iterator.is_none()
                    && plan.machine.is_none()
                    && !self.singleton_types.contains_key(&plan.token)
                    && symbols.qualified_name(plan.symbol) == wanted
            })
        };
        let methods = || {
            plans
                .iter()
                .filter(in_main_type)
                .flat_map(|plan| &plan.methods)
        };
        // A `Main` of the type named wins over the statements beside it.
        let named_main = main_type.is_some()
            && methods().any(|method| {
                matches!(method.source, MethodSource::Declared(_)) && method.name == "Main"
            });
        let top_level = methods()
            .find(|method| match method.source {
                MethodSource::AsyncMain(member) => symbols.get(member).name == "<Main>$",
                _ => false,
            })
            .or_else(|| methods().find(|method| method.name == "<Main>$"))
            .filter(|_| !named_main);
        if let Some(method) = top_level {
            return Ok(method.token);
        }
        // What Roslyn's `FindEntryPoint` accepts: a static `Main`, not
        // generic and in no generic type, taking nothing or a `string[]` and
        // giving back nothing or an `int`. An `async` one (through the
        // `<Main>` around it) counts only where no synchronous one does.
        // `/main:T` looks only at the `Main` methods of `T`.
        let main_type = self.compilation.options().main_type_name.as_deref();
        let in_main_type = |member: SymbolId| {
            main_type.is_none_or(|name| {
                symbols
                    .get(member)
                    .container
                    .is_some_and(|container| symbols.qualified_name(container) == name)
            })
        };
        let mut synchronous = Vec::new();
        let mut asynchronous = Vec::new();
        for method in methods() {
            match method.source {
                MethodSource::AsyncMain(member) | MethodSource::Declared(member)
                    if !in_main_type(member) => {}
                MethodSource::AsyncMain(member) if self.is_entry_point_candidate(member) => {
                    if self.is_entry_point_result(&method.return_type) {
                        asynchronous.push(method.token);
                    }
                }
                MethodSource::Declared(member)
                    if method.name == "Main"
                        && !method.instance
                        && self.is_entry_point_candidate(member)
                        && self.is_entry_point_result(&method.return_type) =>
                {
                    synchronous.push(method.token);
                }
                _ => {}
            }
        }
        let found = if synchronous.is_empty() {
            asynchronous
        } else {
            synchronous
        };
        match found.as_slice() {
            [] => Err(EmitError::new("no static `Main` to start at")),
            [one] => Ok(*one),
            _ => Err(EmitError::new(
                "more than one static `Main`; an assembly may have only one entry point",
            )),
        }
    }

    /// Whether an entry point may give this back: nothing, or an `int`.
    fn is_entry_point_result(&self, returns: &Type) -> bool {
        matches!(returns, Type::Void) || self.special_type_of(returns) == Some(SpecialType::Int32)
    }

    /// Whether a method called `Main` may start the program, before its
    /// return type is looked at: static, not generic and in no generic type,
    /// and taking nothing or one `string[]`.
    fn is_entry_point_candidate(&self, member: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        if symbol.name != "Main" || !symbol.modifiers.contains(Modifiers::STATIC) {
            return false;
        }
        let Some(detail) = symbol.as_method() else {
            return false;
        };
        if !detail.type_parameters.is_empty() {
            return false;
        }
        let mut container = symbol.container;
        while let Some(outer) = container {
            let outer_symbol = symbols.get(outer);
            if outer_symbol
                .as_named_type()
                .is_some_and(|ty| !ty.type_parameters.is_empty())
            {
                return false;
            }
            container = outer_symbol.container;
        }
        match detail.parameters.as_slice() {
            [] => true,
            [parameter] => match self.type_of(*parameter) {
                Type::Array { element, rank: 1 } => {
                    self.special_type_of(&element) == Some(SpecialType::String)
                        && !self.is_by_reference(Some(*parameter))
                }
                _ => false,
            },
            _ => false,
        }
    }

    // -- types and signatures ---------------------------------------------

    pub(crate) fn type_of(&self, symbol: SymbolId) -> Type {
        let mut sink = rustlyn_semantics::Diagnostics::new();
        self.binder.type_of(symbol, &mut sink)
    }

    /// A member's type as the receiver's construction says it is.
    pub(crate) fn member_type(&self, member: SymbolId, receiver: &Type) -> Type {
        // A member the receiver inherits is written in its base's terms, as
        // the receiver constructs that base: `Value` of an `S0<T>` read on
        // an `S1 : S0<object>` is an `object`.
        let through = self.through(member, Some(receiver));
        let receiver = through.as_ref().unwrap_or(receiver);
        self.type_of(member)
            .substitute(&self.binder.type_substitution(receiver))
    }

    /// What a `T?` holds, where the type is one.
    pub(crate) fn nullable_underlying(&self, ty: &Type) -> Option<Type> {
        self.binder.nullable_underlying(ty)
    }

    /// A parameterless member of `Nullable<T>`, through the construction: its
    /// `HasValue` and `GetValueOrDefault` are what a pattern on a `T?` asks.
    pub(crate) fn nullable_member(&mut self, ty: &Type, name: &str) -> Result<Token, EmitError> {
        let spec = self.type_token(ty)?;
        let returns = if name == "get_HasValue" {
            SigType::Primitive(ElementType::Boolean)
        } else {
            SigType::TypeParameter(0)
        };
        let signature = method_signature(true, &returns, &[]);
        Ok(self
            .references
            .member_of_spec(&mut self.metadata, spec, name, &signature))
    }

    /// A member of a construction, named the way §II.22.25 says: a
    /// `MemberRef` under the `TypeSpec`, carrying the definition's signature.
    ///
    /// For a member of a type this assembly does not define, where there is
    /// no symbol to ask — a base constructor is found by name and arity, not
    /// by lookup.
    pub(crate) fn member_of_type(
        &mut self,
        ty: &Type,
        name: &str,
        signature: &[u8],
    ) -> Result<Token, EmitError> {
        let spec = self.type_token(ty)?;
        Ok(self
            .references
            .member_of_spec(&mut self.metadata, spec, name, signature))
    }

    /// `Nullable<T>::.ctor(T)`, which is what putting a value into a `T?` is.
    pub(crate) fn nullable_constructor(&mut self, ty: &Type) -> Result<Token, EmitError> {
        let spec = self.type_token(ty)?;
        let signature = method_signature(
            true,
            &SigType::Primitive(ElementType::Void),
            &[SigType::TypeParameter(0)],
        );
        Ok(self
            .references
            .member_of_spec(&mut self.metadata, spec, ".ctor", &signature))
    }

    /// The `ItemN` field of a tuple, as a `MemberRef` under its `TypeSpec`.
    /// The fields read, in order, to reach element `index` of a tuple: its
    /// `Item{n}`, or — past the seventh element — `Rest`, and then the
    /// element's field in the tuple nested there, and so on.
    pub(crate) fn tuple_field(&mut self, ty: &Type, index: usize) -> Result<Vec<Token>, EmitError> {
        let mut chain = Vec::new();
        let mut current = ty.clone();
        let mut index = index;
        loop {
            let spec = self.type_token(&current)?;
            if index < 7 {
                let signature = field_signature(&SigType::TypeParameter(index as u32));
                chain.push(self.references.member_of_spec(
                    &mut self.metadata,
                    spec,
                    &format!("Item{}", index + 1),
                    &signature,
                ));
                return Ok(chain);
            }
            let signature = field_signature(&SigType::TypeParameter(7));
            chain.push(self.references.member_of_spec(
                &mut self.metadata,
                spec,
                "Rest",
                &signature,
            ));
            current = match &current {
                Type::Tuple(elements) if elements.len() > 7 => Type::Tuple(elements[7..].to_vec()),
                Type::Named { type_arguments, .. } if type_arguments.len() == 8 => {
                    type_arguments[7].clone()
                }
                other => {
                    return Err(EmitError::new(format!(
                        "element {} of a tuple of type `{}` is out of its range",
                        index + 1,
                        other.display(self.compilation.symbols())
                    )));
                }
            };
            index -= 7;
        }
    }

    /// Whether a method is the implementation of a member of an interface the
    /// type implements.
    ///
    /// C# matches them by name and signature, with no `override` to say so,
    /// which is why this has to be worked out rather than read off.
    fn implements_an_interface_member(&self, method: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(method).container else {
            return false;
        };
        let Some(detail) = symbols.get(method).as_method() else {
            return false;
        };
        let name = symbols.get(method).name.clone();
        let arity = detail.parameters.len();
        self.answering
            .get(&container)
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter_map(|interface| interface.symbol())
            .any(|interface| {
                symbols.lookup(interface, &name).iter().any(|candidate| {
                    self.is_interface_slot(*candidate)
                        && symbols
                            .get(*candidate)
                            .as_method()
                            .is_some_and(|member| member.parameters.len() == arity)
                })
            })
    }

    /// Whether a member of an interface is a slot a class can fill: not
    /// static, and neither `sealed` nor `private` (C# 8), which makes it a
    /// method of the interface's own that no class answers for. What a
    /// referenced interface declares is taken as a slot.
    fn is_interface_slot(&self, member: SymbolId) -> bool {
        let modifiers = self.compilation.interface_member_modifiers(member);
        !modifiers.contains(Modifiers::STATIC)
            && (self.compilation.is_from_metadata(member)
                || modifiers.contains(Modifiers::VIRTUAL)
                || modifiers.contains(Modifiers::ABSTRACT))
    }

    /// How Roslyn writes an interface in the name of a member that
    /// implements it explicitly: namespace-qualified, the type arguments the
    /// same way with no space between them, and an array's ranks in the
    /// order the runtime reads them.
    pub(crate) fn explicit_prefix(&self, ty: &Type) -> String {
        let symbols = self.compilation.symbols();
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let qualified = symbols.qualified_name(*symbol);
                let bare = match qualified.rsplit_once('`') {
                    Some((name, arity)) if arity.chars().all(|c| c.is_ascii_digit()) => {
                        name.to_string()
                    }
                    _ => qualified,
                };
                if type_arguments.is_empty() {
                    bare
                } else {
                    let arguments: Vec<String> = type_arguments
                        .iter()
                        .map(|argument| self.explicit_prefix(argument))
                        .collect();
                    format!("{bare}<{}>", arguments.join(","))
                }
            }
            Type::Array { .. } => {
                let mut ranks = Vec::new();
                let mut element = ty;
                while let Type::Array {
                    element: inner,
                    rank,
                } = element
                {
                    ranks.push(*rank);
                    element = inner;
                }
                let mut text = self.explicit_prefix(element);
                for rank in ranks.iter().rev() {
                    text.push('[');
                    text.push_str(&",".repeat(rank.saturating_sub(1)));
                    text.push(']');
                }
                text
            }
            Type::Pointer(inner) => format!("{}*", self.explicit_prefix(inner)),
            Type::TypeParameter(symbol) => symbols.get(*symbol).name.clone(),
            other => other.display(symbols),
        }
    }

    /// The interface a member names in front of itself, where it names one
    /// (see [`Binder::explicit_interface`]): it has to be resolved here
    /// because nothing downstream can get back to the syntax that said
    /// which one.
    fn explicit_interface(&self, member: SymbolId) -> Option<Type> {
        self.binder.explicit_interface(member)
    }

    /// The member of `interface` that an explicit implementation answers.
    ///
    /// The symbol's own name carries the interface in front of it, which is
    /// what keeps `IFormattable.ToString` from colliding with `ToString`; the
    /// interface's member goes by the bare name.
    fn interface_member(&self, member: SymbolId, interface: &Type) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let declared = interface.symbol()?;
        let symbol = symbols.get(member);
        let bare = symbol.name.rsplit('.').next()?.to_string();
        let kind = symbol.kind;
        let candidates: Vec<SymbolId> = symbols
            .lookup(declared, &bare)
            .iter()
            .copied()
            .filter(|candidate| {
                symbols.get(*candidate).kind == kind && self.same_signature(member, *candidate)
            })
            .collect();
        // Overloads the construction makes alike — `long Method(T x)` and
        // `int Method(U x)` of an `I1<int, int>`, or `Method(ref T x)` and
        // `Method(U x)` — are told apart by what each takes and gives back
        // once the construction has said what `T` and `U` are.
        candidates
            .iter()
            .copied()
            .find(|candidate| self.answers_exactly(member, *candidate, interface))
            .or_else(|| candidates.first().copied())
    }

    /// Whether an implementation takes and gives back exactly what an
    /// interface member does through `interface`, `ref` and all.
    fn answers_exactly(&self, member: SymbolId, declared: SymbolId, interface: &Type) -> bool {
        self.answers_exactly_through(member, None, declared, interface)
    }

    /// The same, for a member read through a construction of its class.
    fn answers_exactly_through(
        &self,
        member: SymbolId,
        through: Option<&Type>,
        declared: SymbolId,
        interface: &Type,
    ) -> bool {
        let seen = |member: SymbolId| match through {
            Some(base) => self.member_type(member, base),
            None => self.type_of(member),
        };
        let symbols = self.compilation.symbols();
        let parameters = |member: SymbolId| -> Vec<SymbolId> {
            let symbol = symbols.get(member);
            symbol
                .as_method()
                .map(|detail| detail.parameters.clone())
                .or_else(|| symbol.as_property().map(|detail| detail.parameters.clone()))
                .unwrap_or_default()
        };
        let ref_kind = |parameter: SymbolId| {
            symbols
                .get(parameter)
                .as_parameter()
                .map(|detail| detail.ref_kind)
        };
        let (mine, theirs) = (parameters(member), parameters(declared));
        seen(member) == self.member_type(declared, interface)
            && mine.len() == theirs.len()
            && mine.iter().zip(&theirs).all(|(mine, theirs)| {
                ref_kind(*mine) == ref_kind(*theirs)
                    && seen(*mine) == self.member_type(*theirs, interface)
            })
    }

    /// Whether two members could be the same member of the same type.
    ///
    /// Name and arity are not enough: `ISymbol` declares `Accept` three times
    /// over, and picking the first leaves the runtime comparing a body to the
    /// wrong declaration. Two type parameters, or a type parameter and
    /// anything, are treated as matching — the interface's side is written in
    /// terms of parameters the implementation has already chosen for.
    fn same_signature(&self, left: SymbolId, right: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let shape = |member: SymbolId| -> Option<(usize, Vec<SymbolId>)> {
            let symbol = symbols.get(member);
            match symbol.kind {
                SymbolKind::Method => symbol
                    .as_method()
                    .map(|detail| (detail.type_parameters.len(), detail.parameters.clone())),
                _ => symbol
                    .as_property()
                    .map(|detail| (0, detail.parameters.clone())),
            }
        };
        let (Some((left_arity, left_parameters)), Some((right_arity, right_parameters))) =
            (shape(left), shape(right))
        else {
            return false;
        };
        left_arity == right_arity
            && left_parameters.len() == right_parameters.len()
            && left_parameters
                .iter()
                .zip(&right_parameters)
                .all(|(left, right)| same_shape(&self.type_of(*left), &self.type_of(*right)))
    }

    /// Remembers that a body explicitly implements an interface member, to be
    /// turned into a `MethodImpl` row once every type has its token.
    ///
    /// `setter` says which accessor, where the member is a property; a method
    /// passes `None`.
    fn note_explicit(
        &mut self,
        member: SymbolId,
        body: Token,
        interface: &Type,
        setter: Option<bool>,
    ) {
        let Some(declared) = self.interface_member(member, interface) else {
            return;
        };
        let Some(container) = self.compilation.symbols().get(member).container else {
            return;
        };
        let Some(class) = self.types.get(&container).copied() else {
            return;
        };
        let declaration = match setter {
            None => Declaration::Method {
                member: declared,
                interface: interface.clone(),
            },
            Some(setter) => Declaration::Accessor {
                property: declared,
                interface: interface.clone(),
                setter,
            },
        };
        self.explicit_impls.push(ExplicitImpl {
            class,
            body,
            declaration,
        });
    }

    /// The accessor read from metadata that an accessor of an overriding
    /// property overrides, where it carries custom modifiers.
    fn overridden_metadata_accessor(&self, source: &MethodSource) -> Option<SymbolId> {
        let (property, setter) = match source {
            MethodSource::PropertyGetter { property, .. } => (*property, false),
            MethodSource::PropertySetter { property } => (*property, true),
            _ => return None,
        };
        let symbols = self.compilation.symbols();
        if !symbols
            .get(property)
            .modifiers
            .contains(Modifiers::OVERRIDE)
        {
            return None;
        }
        let overridden = self.overridden_member(property)?;
        if !self.compilation.is_from_metadata(overridden) {
            return None;
        }
        let accessor = symbols
            .get(overridden)
            .as_property()
            .and_then(|detail| if setter { detail.setter } else { detail.getter })?;
        let modified = |symbol: SymbolId| {
            self.compilation
                .metadata_modifiers(symbol)
                .is_some_and(|modifiers| !modifiers.is_empty())
        };
        (modified(accessor)
            || symbols
                .get(accessor)
                .as_method()
                .is_some_and(|detail| detail.parameters.iter().any(|p| modified(*p))))
        .then_some(accessor)
    }

    /// Ties an accessor of an overriding property to the one it overrides
    /// where metadata named that one otherwise: `get_P` answers a base's
    /// `GetProperty2` only through a `MethodImpl` row, the runtime matching
    /// by name.
    fn note_renamed_accessor_override(
        &mut self,
        property: SymbolId,
        body: Token,
        setter: bool,
        name: &str,
    ) {
        let symbols = self.compilation.symbols();
        if !symbols
            .get(property)
            .modifiers
            .contains(Modifiers::OVERRIDE)
        {
            return;
        }
        let Some(overridden) = self.overridden_member(property) else {
            return;
        };
        if !self.compilation.is_from_metadata(overridden) {
            return;
        }
        let Some(accessor) = symbols
            .get(overridden)
            .as_property()
            .and_then(|detail| if setter { detail.setter } else { detail.getter })
        else {
            return;
        };
        // Or where its signature carries custom modifiers this one's does
        // not: the runtime compares those too.
        let modified = |symbol: SymbolId| {
            self.compilation
                .metadata_modifiers(symbol)
                .is_some_and(|modifiers| !modifiers.is_empty())
        };
        let carries_modifiers = modified(accessor)
            || symbols
                .get(accessor)
                .as_method()
                .is_some_and(|detail| detail.parameters.iter().any(|p| modified(*p)));
        if symbols.get(accessor).name == name && !carries_modifiers {
            return;
        }
        let (Some(container), Some(owner)) = (
            symbols.get(property).container,
            symbols.get(overridden).container,
        ) else {
            return;
        };
        let Some(class) = self.types.get(&container).copied() else {
            return;
        };
        let through = self
            .binder
            .constructed_from(&self.binder.self_type(container), owner)
            .unwrap_or_else(|| Type::named(owner));
        self.explicit_impls.push(ExplicitImpl {
            class,
            body,
            declaration: Declaration::Override {
                member: accessor,
                through,
            },
        });
    }

    /// Remembers that a method, or a property's getter, overrides one whose
    /// return type is wider than its own (C# 9), and says whether it does.
    ///
    /// `override string M()` over `object M()` is no override to the runtime,
    /// which matches by name and signature: the `MethodImpl` row is what
    /// puts the body in the base's slot, and `[PreserveBaseOverrides]` what
    /// keeps a further override in it.
    fn note_covariant_override(&mut self, member: SymbolId, body: Token, getter: bool) -> bool {
        let Some(overridden) = self.overridden_member(member) else {
            return false;
        };
        let symbols = self.compilation.symbols();
        let (Some(container), Some(owner)) = (
            symbols.get(member).container,
            symbols.get(overridden).container,
        ) else {
            return false;
        };
        if symbols.get(overridden).kind != symbols.get(member).kind {
            return false;
        }
        // What the base returns as this class derives from it: `T Get()` of
        // a `GB<T>` is an `A Get()` to `GD : GB<A>`, and of a generic method
        // with this one's type parameters in place of its own.
        let mut theirs = self.member_type(overridden, &self.binder.self_type(container));
        if let (Some(base), Some(own)) = (
            symbols.get(overridden).as_method(),
            symbols.get(member).as_method(),
        ) {
            let renamed: HashMap<SymbolId, Type> = base
                .type_parameters
                .iter()
                .zip(&own.type_parameters)
                .map(|(theirs, ours)| (*theirs, Type::TypeParameter(*ours)))
                .collect();
            theirs = theirs.substitute(&renamed);
        }
        if same_return(&self.type_of(member), &theirs) {
            return false;
        }
        let Some(class) = self.types.get(&container).copied() else {
            return false;
        };
        let through = self
            .binder
            .constructed_from(&self.binder.self_type(container), owner)
            .unwrap_or_else(|| Type::named(owner));
        let declaration = if getter {
            Declaration::Accessor {
                property: overridden,
                interface: through,
                setter: false,
            }
        } else {
            Declaration::Override {
                member: overridden,
                through,
            }
        };
        self.explicit_impls.push(ExplicitImpl {
            class,
            body,
            declaration,
        });
        self.covariant_bodies.insert(body);
        true
    }

    /// Remembers that a record's `<Clone>$` overrides its base record's.
    ///
    /// Each returns its own type, so by name and signature they are two
    /// methods; the `MethodImpl` row is what makes `derived with { }` copy a
    /// derived record as itself, whatever the receiver's static type.
    fn note_clone_override(&mut self, clone: SymbolId, body: Token) {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(clone).container else {
            return;
        };
        let Some(class) = self.types.get(&container).copied() else {
            return;
        };
        let overridden = self
            .binder
            .base_types_of(container)
            .into_iter()
            // A referenced record is a class to metadata, and its `<Clone>$`
            // is what says it is a record.
            .filter(|base| {
                base.symbol().is_some_and(|base| {
                    symbols.get(base).type_kind() == Some(TypeKind::Record)
                        || !symbols.lookup(base, "<Clone>$").is_empty()
                })
            })
            .find_map(|base| {
                symbols
                    .lookup(base.symbol()?, "<Clone>$")
                    .iter()
                    .copied()
                    .find(|member| symbols.get(*member).kind == SymbolKind::Method)
                    .map(|member| (member, base))
            });
        if let Some((member, through)) = overridden {
            self.explicit_impls.push(ExplicitImpl {
                class,
                body,
                declaration: Declaration::Override { member, through },
            });
        }
    }

    /// Turns every explicit implementation met while planning into a
    /// `MethodImpl` row, now that every type has its token.
    fn write_method_impls(&mut self) -> Result<(), EmitError> {
        for pending in std::mem::take(&mut self.explicit_impls) {
            let declaration = match &pending.declaration {
                Declaration::Method { member, interface } => {
                    self.declared_method_token(*member, interface)
                }
                Declaration::Accessor {
                    property,
                    interface,
                    setter,
                } => self.property_accessor(*property, Some(interface), *setter),
                // Through a constructed base the method is a `MemberRef`
                // under the `TypeSpec`, as any member of `A<int>` is.
                Declaration::Override { member, through } if self.is_constructed(through) => {
                    self.member_of_constructed(*member, through)
                }
                // A referenced record's `<Clone>$` is a reference like any
                // other member of that assembly.
                Declaration::Override { member, .. }
                    if !self.methods.contains_key(member)
                        && self.compilation.is_from_metadata(*member) =>
                {
                    self.corlib_member(*member)
                }
                Declaration::Override { member, .. } => {
                    self.methods.get(member).copied().ok_or_else(|| {
                        EmitError::new(format!(
                            "cannot reference the overridden method `{}`",
                            self.compilation.symbols().qualified_name(*member)
                        ))
                    })
                }
            };
            // A survey writes what it can: an interface member that cannot be
            // named leaves the row out, which loads and fails later, rather
            // than stopping the whole assembly.
            let declaration = match declaration {
                Ok(token) => token,
                Err(error) if self.lenient => {
                    self.skipped
                        .push(("an explicit implementation".to_string(), error.message));
                    continue;
                }
                Err(error) => return Err(error),
            };
            let body = method_def_or_ref(pending.body);
            let declaration = method_def_or_ref(declaration);
            self.metadata
                .add_method_impl(pending.class, body, declaration);
        }
        Ok(())
    }

    /// The token that names a method of an interface: the definition where the
    /// interface is its own type, and a `MemberRef` under a `TypeSpec` where
    /// it is a construction.
    fn declared_method_token(
        &mut self,
        member: SymbolId,
        interface: &Type,
    ) -> Result<Token, EmitError> {
        if self.is_constructed(interface) {
            return self.member_of_constructed(member, interface);
        }
        if let Some(token) = self.methods.get(&member) {
            return Ok(*token);
        }
        if self.compilation.is_from_corlib(member) {
            return self.corlib_member(member);
        }
        Err(EmitError::new(format!(
            "cannot name `{}` to implement it explicitly",
            self.compilation.symbols().qualified_name(member)
        )))
    }

    /// The method an `override` answers, found in the nearest base class that
    /// declares one of the same name and shape.
    fn overridden_method(&self, method: SymbolId) -> Option<SymbolId> {
        self.overridden_member(method)
    }

    /// The method or property an `override` answers, found in the nearest
    /// base class that declares one of the same name and shape.
    fn overridden_member(&self, method: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        if !symbols.get(method).modifiers.contains(Modifiers::OVERRIDE) {
            return None;
        }
        let name = symbols.get(method).name.clone();
        let base_of = |symbol: SymbolId| {
            self.binder
                .base_types_of(symbol)
                .into_iter()
                .find_map(|base| {
                    base.symbol().filter(|found| {
                        symbols.get(*found).type_kind() != Some(TypeKind::Interface)
                    })
                })
        };
        let mut current = base_of(symbols.get(method).container?);
        let mut depth = 0;
        while let Some(at) = current {
            if depth > 16 {
                return None;
            }
            // A base's private member is no one's to override: `private new
            // string P` in between is passed over for the `P` beyond it.
            if let Some(found) = symbols.lookup(at, &name).iter().copied().find(|candidate| {
                symbols.get(*candidate).accessibility != rustlyn_semantics::Accessibility::Private
                    && self.same_signature(method, *candidate)
                    && (self.same_ref_kinds(method, *candidate)
                        || self.compilation.is_from_metadata(*candidate))
                    && self.same_modifiers(method, *candidate)
            }) {
                return Some(found);
            }
            depth += 1;
            current = base_of(at);
        }
        None
    }

    /// Whether two methods take each parameter the same way: `ref` and
    /// `out` are one thing in metadata but two in C#, where an override
    /// has to match the one it overrides.
    fn same_ref_kinds(&self, left: SymbolId, right: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let kinds = |member: SymbolId| -> Vec<rustlyn_semantics::RefKind> {
            symbols
                .get(member)
                .as_method()
                .map(|detail| {
                    detail
                        .parameters
                        .iter()
                        .map(|parameter| {
                            symbols
                                .get(*parameter)
                                .as_parameter()
                                .map(|parameter| parameter.ref_kind)
                                .unwrap_or_default()
                        })
                        .collect()
                })
                .unwrap_or_default()
        };
        kinds(left) == kinds(right)
    }

    /// Whether an override has to name what it overrides: a class between
    /// the two declares a virtual method metadata cannot tell apart from it
    /// (`M(out int)` hiding `M(ref int)`), and the runtime, matching by name
    /// and signature, would otherwise put the body in that method's slot.
    fn override_is_hidden(&self, method: SymbolId, overridden: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let name = symbols.get(method).name.clone();
        let Some(target) = symbols.get(overridden).container else {
            return false;
        };
        let base_of = |symbol: SymbolId| {
            self.binder
                .base_types_of(symbol)
                .into_iter()
                .find_map(|base| {
                    base.symbol().filter(|found| {
                        symbols.get(*found).type_kind() != Some(TypeKind::Interface)
                    })
                })
        };
        let Some(container) = symbols.get(method).container else {
            return false;
        };
        let mut current = base_of(container);
        let mut depth = 0;
        while let Some(at) = current {
            if at == target || depth > 16 {
                return false;
            }
            let hides = symbols.lookup(at, &name).iter().any(|candidate| {
                *candidate != overridden
                    && symbols.get(*candidate).kind == SymbolKind::Method
                    && (symbols
                        .get(*candidate)
                        .modifiers
                        .contains(Modifiers::VIRTUAL)
                        || symbols
                            .get(*candidate)
                            .modifiers
                            .contains(Modifiers::ABSTRACT)
                        || symbols
                            .get(*candidate)
                            .modifiers
                            .contains(Modifiers::OVERRIDE))
                    && self.same_signature(method, *candidate)
                    && !self.same_ref_kinds(method, *candidate)
            });
            // A virtual property's accessor is a method to the runtime,
            // though not to C#: `C.get_P()` overriding `A.get_P()` passes
            // `B.P`'s getter on the way, and would land in its slot.
            let accessor_hides = name.strip_prefix("get_").is_some_and(|property| {
                symbols.lookup(at, property).iter().any(|candidate| {
                    let symbol = symbols.get(*candidate);
                    symbol.kind == SymbolKind::Property
                        && [Modifiers::VIRTUAL, Modifiers::ABSTRACT, Modifiers::OVERRIDE]
                            .into_iter()
                            .any(|modifier| symbol.modifiers.contains(modifier))
                        && symbol.as_property().is_some_and(|detail| detail.has_get)
                        && self.same_signature(method, *candidate)
                        && same_shape(&self.type_of(method), &self.type_of(*candidate))
                })
            });
            if hides || accessor_hides {
                return true;
            }
            depth += 1;
            current = base_of(at);
        }
        false
    }

    /// Whether a property of this name (or, for an indexer, of this arity)
    /// is declared by an interface the containing type implements.
    ///
    /// The accessors are what metadata matches, and they only count as an
    /// implementation if they are virtual — so the property has to be looked
    /// up as a property, by the name it was written with.
    fn implements_an_interface_property(&self, property: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(property).container else {
            return false;
        };
        let Some(detail) = symbols.get(property).as_property() else {
            return false;
        };
        let name = symbols.get(property).name.clone();
        let (is_indexer, arity) = (detail.is_indexer, detail.parameters.len());
        self.answering
            .get(&container)
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .filter_map(|interface| interface.symbol())
            .any(|interface| {
                symbols.lookup(interface, &name).iter().any(|candidate| {
                    self.is_interface_slot(*candidate)
                        && symbols.get(*candidate).as_property().is_some_and(|member| {
                            member.is_indexer == is_indexer && member.parameters.len() == arity
                        })
                })
            })
    }

    /// Every interface each class has to answer for, its own and the ones
    /// anything deriving from it lists.
    ///
    /// `CommonEmbeddedMember` lists only `IEmbeddedDefinition`, which says
    /// nothing about `IsEncDeleted` — but `EmbeddedField` derives from it and
    /// lists `IFieldDefinition`, which does, and the member answering that is
    /// the base class's. Leaving it non-virtual leaves the derived type's
    /// interface slot empty, and the runtime refuses to load the type with
    /// "does not have an implementation".
    fn interfaces_to_answer(&self) -> HashMap<SymbolId, Vec<Type>> {
        let symbols = self.compilation.symbols();
        let mut answering: HashMap<SymbolId, Vec<Type>> = HashMap::new();
        for symbol in self.defining.iter().copied() {
            if symbols
                .get(symbol)
                .type_kind()
                .is_none_or(|kind| kind == TypeKind::Interface)
            {
                continue;
            }
            let interfaces = self.inherited_interfaces(symbol);
            if interfaces.is_empty() {
                continue;
            }
            // The member that answers can be anywhere up the chain, so every
            // class above this one has to know what is asked of it.
            let mut current = Some(symbol);
            let mut seen = std::collections::HashSet::new();
            while let Some(at) = current.filter(|at| seen.insert(*at)) {
                let held = answering.entry(at).or_default();
                for interface in &interfaces {
                    if !held.contains(interface) {
                        held.push(interface.clone());
                    }
                }
                current = self.base_class(at);
            }
        }
        answering
    }

    /// The class a class derives from, where this assembly declares it.
    fn base_class(&self, symbol: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        self.binder
            .base_types_of(symbol)
            .into_iter()
            .filter_map(|base| base.symbol())
            .find(|base| symbols.get(*base).type_kind() != Some(TypeKind::Interface))
    }

    /// Every interface a type has to answer for: the ones it lists, the ones
    /// those inherit, and the ones its base classes list.
    ///
    /// `Count` on a type that says only `IImmutableDictionary<K, V>` still
    /// implements `IReadOnlyCollection<KeyValuePair<K, V>>.Count`, three
    /// interfaces up. Looking only at what the type wrote leaves the accessor
    /// non-virtual, and the interface's call reaches nothing.
    fn inherited_interfaces(&self, symbol: SymbolId) -> Vec<Type> {
        let symbols = self.compilation.symbols();
        let mut found = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut pending = vec![Type::named(symbol)];
        let mut visited = std::collections::HashSet::new();
        while let Some(current) = pending.pop() {
            let Some(current_symbol) = current.symbol() else {
                continue;
            };
            if !visited.insert(current.clone()) {
                continue;
            }
            // What an interface inherits is written in its own parameters:
            // `IComparisonOperators<Money, Money, bool>` inherits
            // `IEqualityOperators<TSelf, TOther, TResult>`, which is
            // `IEqualityOperators<Money, Money, bool>` here, and a
            // `MethodImpl` naming the definition's form would not match.
            let substitution = self.binder.type_substitution(&current);
            for base in self.binder.base_types_of(current_symbol) {
                let base = base.substitute(&substitution);
                let Some(declared) = base.symbol() else {
                    continue;
                };
                if symbols.get(declared).type_kind() == Some(TypeKind::Interface)
                    && seen.insert(base.clone())
                {
                    found.push(base.clone());
                }
                pending.push(base);
            }
        }
        found
    }

    /// The interfaces a type lists among its base types.
    ///
    /// Every interface the type lists and every one those inherit, as `csc`
    /// writes the rows: `class Y : X, I2` with `I2 : I1` implements `I1`
    /// afresh, and a public `goo` of `Y` then answers `I1.goo` in place of
    /// what `X` mapped it to.
    pub(crate) fn implemented_interfaces(&self, symbol: SymbolId) -> Vec<Type> {
        // The interfaces the type lists and every interface those extend,
        // depth first in declaration order, each once — Roslyn's
        // `CalculateInterfacesToEmit`. A class that lists `I2 : I1` over a
        // base that implements `I1` implements `I1` anew, and the runtime
        // only maps `I1` to its methods if the row says so.
        let mut found = Vec::new();
        self.visit_interfaces(symbol, &HashMap::new(), &mut found, 0);
        found
    }

    fn visit_interfaces(
        &self,
        symbol: SymbolId,
        substitution: &HashMap<SymbolId, Type>,
        found: &mut Vec<Type>,
        depth: usize,
    ) {
        if depth > 32 {
            return;
        }
        let symbols = self.compilation.symbols();
        for base in self.binder.base_types_of(symbol) {
            let Some(interface) = base
                .symbol()
                .filter(|base| symbols.get(*base).type_kind() == Some(TypeKind::Interface))
            else {
                continue;
            };
            let base = base.substitute(substitution);
            if found.contains(&base) {
                continue;
            }
            found.push(base.clone());
            let parameters = symbols
                .get(interface)
                .as_named_type()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            let arguments = match &base {
                Type::Named { type_arguments, .. } => type_arguments.clone(),
                _ => Vec::new(),
            };
            let inner: HashMap<SymbolId, Type> = parameters.into_iter().zip(arguments).collect();
            self.visit_interfaces(interface, &inner, found, depth + 1);
        }
    }

    /// The `GenericParamConstraint` rows of one type parameter.
    ///
    /// `where T : Base` and `where T : IComparable<T>` are the same table; the
    /// `class`, `struct` and `new()` constraints are flags rather than rows.
    /// Writes a type parameter's constraint rows, and says for each which
    /// syntax wrote it (none for one an override inherits).
    pub(crate) fn write_constraints(
        &mut self,
        owner: u32,
        number: u16,
        parameter: SymbolId,
    ) -> Result<Vec<Option<rustlyn_semantics::TypeSyntaxRef>>, EmitError> {
        let mut written = Vec::new();
        let references = self
            .compilation
            .symbols()
            .get(parameter)
            .as_type_parameter()
            .map(|detail| detail.constraints.clone())
            .unwrap_or_default();
        // An override writes no constraints and has the overridden
        // method's, which the runtime checks it restates: in terms of the
        // override's own type parameters and of what its class says the
        // base class's are.
        if references.is_empty()
            && let Some(inherited) = self.inherited_constraints(parameter)
        {
            for ty in inherited {
                let coded = self.type_coded(&ty)?;
                self.metadata
                    .add_generic_param_constraint(owner, number, coded);
                written.push(None);
            }
            return Ok(written);
        }
        for reference in references {
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let ty = self.binder.resolve_type_ref(reference, &mut sink);
            if matches!(ty, Type::Error) {
                continue;
            }
            let coded = self.type_coded(&ty)?;
            self.metadata
                .add_generic_param_constraint(owner, number, coded);
            written.push(Some(reference));
        }
        Ok(written)
    }

    /// The constraints an override's type parameter has from the method it
    /// overrides, substituted into the override's terms.
    fn inherited_constraints(&self, parameter: SymbolId) -> Option<Vec<Type>> {
        let overridden = self.binder.overridden_type_parameter(parameter)?;
        let symbols = self.compilation.symbols();
        let method = symbols.get(parameter).container?;
        let base_method = symbols.get(overridden).container?;
        let base_type = symbols.get(base_method).container?;
        let own_type = symbols.get(method).container?;
        let mut substitution = std::collections::HashMap::new();
        let own = symbols.get(method).as_method()?.type_parameters.clone();
        let theirs = symbols
            .get(base_method)
            .as_method()?
            .type_parameters
            .clone();
        for (their, mine) in theirs.iter().zip(&own) {
            substitution.insert(*their, Type::TypeParameter(*mine));
        }
        let construction = self
            .own_construction(own_type)
            .unwrap_or(Type::named(own_type));
        if let Some(Type::Named { type_arguments, .. }) =
            self.binder.constructed_from(&construction, base_type)
            && let Some(detail) = symbols.get(base_type).as_named_type()
        {
            for (their, argument) in detail.type_parameters.iter().zip(type_arguments) {
                substitution.insert(*their, argument);
            }
        }
        let inherited = self.binder.base_types_of(overridden);
        Some(
            inherited
                .iter()
                .filter(|ty| !ty.is_error())
                .map(|ty| ty.substitute(&substitution))
                .collect(),
        )
    }

    /// The `TypeDefOrRef` coded index of what a type extends.
    /// The class a class names as its base, as written: `Base<(int x, int
    /// y)>`, names and all.
    fn base_class_type(&self, symbol: SymbolId) -> Option<Type> {
        let symbols = self.compilation.symbols();
        if !matches!(
            symbols.get(symbol).type_kind(),
            Some(TypeKind::Class | TypeKind::Record)
        ) {
            return None;
        }
        self.binder.base_types_of(symbol).into_iter().find(|base| {
            base.symbol().is_some_and(|base| {
                matches!(
                    symbols.get(base).type_kind(),
                    Some(TypeKind::Class | TypeKind::Record)
                )
            })
        })
    }

    fn base_type_coded(&mut self, symbol: SymbolId) -> Result<u32, EmitError> {
        let symbols = self.compilation.symbols();
        // A delegate declares no base at all; metadata gives it one.
        if symbols.get(symbol).type_kind() == Some(TypeKind::Delegate) {
            return Ok(self
                .references
                .type_ref_coded(&mut self.metadata, "System.MulticastDelegate"));
        }
        let bases = self.binder.base_types_of(symbol);
        let symbols = self.compilation.symbols();
        // A record is a class too: `record Derived : Base` extends `Base`,
        // and saying `object` instead lays the fields out as if the base
        // had none.
        for base in bases {
            if let Some(base_symbol) = base.symbol()
                && matches!(
                    symbols.get(base_symbol).type_kind(),
                    Some(TypeKind::Class | TypeKind::Record)
                )
            {
                return self.type_coded(&base);
            }
        }
        Ok(self
            .references
            .type_ref_coded(&mut self.metadata, "System.Object"))
    }

    /// Where a type's *definition* lives, ignoring any construction of it.
    fn definition_coded(&mut self, symbol: SymbolId) -> Result<u32, EmitError> {
        if let Some(token) = self.types.get(&symbol) {
            return Ok(type_def_or_ref(0, token.0 & 0x00FF_FFFF));
        }
        let token = self.referenced_type(symbol);
        Ok(type_def_or_ref(1, token.0 & 0x00FF_FFFF))
    }

    /// The `TypeRef` for a type this assembly does not define, into the
    /// assembly it was read from: a library's own `InAttribute` is not the
    /// framework's, however alike their names.
    pub(crate) fn referenced_type(&mut self, symbol: SymbolId) -> Token {
        let name = self.compilation.symbols().metadata_qualified_name(symbol);
        match self.compilation.assembly_of(symbol) {
            Some(home) => {
                let home = home.clone();
                self.references
                    .type_ref_in(&mut self.metadata, &home, &name)
            }
            None => self.references.type_ref(&mut self.metadata, &name),
        }
    }

    /// Which of its type's parameters a type parameter is, by position.
    /// Which of its owner's parameters a type parameter is, and whether the
    /// owner is a method.
    ///
    /// A type's and a method's are numbered separately — `!0` and `!!0` are
    /// different things — so the answer has to say which kind it found.
    fn type_parameter_index(&self, parameter: SymbolId) -> Option<(u32, bool)> {
        // Inside a class the compiler made over a generic method, the
        // method's parameters are the class's own.
        if let Some(at) = self
            .display_generics
            .iter()
            .position(|candidate| *candidate == parameter)
        {
            return Some((at as u32, false));
        }
        let symbols = self.compilation.symbols();
        let container = symbols.get(parameter).container?;
        let position = |parameters: &[SymbolId]| {
            parameters
                .iter()
                .position(|candidate| *candidate == parameter)
                .map(|index| index as u32)
        };
        if let Some(detail) = symbols.get(container).as_named_type() {
            return position(&detail.type_parameters).map(|index| (index, false));
        }
        // What the method being written declares wins over what the symbol's
        // own container says: a local function carries its enclosing method's
        // parameters in front of its own, and `!!0` there is the first of the
        // list that was emitted.
        if let Some(at) = position(&self.method_generics) {
            return Some((at, true));
        }
        let detail = symbols.get(container).as_method()?;
        position(&detail.type_parameters).map(|index| (index, true))
    }

    pub(crate) fn is_value_type_symbol(&self, symbol: SymbolId) -> bool {
        matches!(
            self.compilation.symbols().get(symbol).type_kind(),
            Some(TypeKind::Struct | TypeKind::Enum | TypeKind::RecordStruct)
        )
    }

    /// The `TypeDefOrRef` coded index of a type, defining or referencing it as
    /// needed.
    pub(crate) fn type_coded(&mut self, ty: &Type) -> Result<u32, EmitError> {
        let ty = &self.completed(ty);
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                if !type_arguments.is_empty() {
                    // A `TypeDefOrRef` tagged 2 is a `TypeSpec`.
                    let token = self.type_token(ty)?;
                    return Ok(type_def_or_ref(2, token.0 & 0x00FF_FFFF));
                }
                self.definition_coded(*symbol)
            }
            // `where TDerived : TBase` names a type parameter, which no
            // `TypeDef` or `TypeRef` stands for: it is a `TypeSpec` holding
            // `!0` or `!!0` like any other use of one.
            Type::TypeParameter(_) | Type::FunctionPointer(_) | Type::Pointer(_) => {
                let token = self.type_token(ty)?;
                Ok(type_def_or_ref(2, token.0 & 0x00FF_FFFF))
            }
            Type::Array { .. } | Type::Null => Ok(self
                .references
                .type_ref_coded(&mut self.metadata, "System.Object")),
            other if self.lenient => {
                let _ = other;
                Ok(self
                    .references
                    .type_ref_coded(&mut self.metadata, "System.Object"))
            }
            other => Err(EmitError::new(format!(
                "cannot emit a token for the type `{}`",
                other.display(self.compilation.symbols())
            ))),
        }
    }

    /// The token an instruction such as `box` or `newarr` needs for a type.
    ///
    /// A constructed type has no definition to point at, so it gets a
    /// `TypeSpec`: a row that is nothing but the signature of the shape.
    pub(crate) fn type_token(&mut self, ty: &Type) -> Result<Token, EmitError> {
        let ty = &self.completed(ty);
        match ty {
            Type::Dynamic => Ok(self
                .references
                .type_ref(&mut self.metadata, "System.Object")),
            Type::TypeParameter(_) => {
                let mut blob = Vec::new();
                self.sig_type(ty)?.write(&mut blob);
                Ok(self.references.type_spec(&mut self.metadata, &blob))
            }
            // A tuple is a construction like any other, spelled differently.
            Type::Named { type_arguments, .. } if !type_arguments.is_empty() => {
                let mut blob = Vec::new();
                self.sig_type(ty)?.write(&mut blob);
                Ok(self.references.type_spec(&mut self.metadata, &blob))
            }
            // `T[]` and `(int, string)` have no row of their own either: a
            // `TypeSpec` is a signature blob standing where a type goes.
            Type::Tuple(_)
            | Type::Array { .. }
            | Type::ByRef(_)
            | Type::Pointer(_)
            | Type::FunctionPointer(_) => {
                let mut blob = Vec::new();
                self.sig_type(ty)?.write(&mut blob);
                Ok(self.references.type_spec(&mut self.metadata, &blob))
            }
            Type::Named { symbol, .. } => {
                if let Some(token) = self.types.get(symbol) {
                    return Ok(*token);
                }
                Ok(self.referenced_type(*symbol))
            }
            // `typeof(void)` is `System.Void`.
            Type::Void => Ok(self.references.type_ref(&mut self.metadata, "System.Void")),
            other if self.lenient => {
                let _ = other;
                Ok(self
                    .references
                    .type_ref(&mut self.metadata, "System.Object"))
            }
            other => Err(EmitError::new(format!(
                "cannot emit a token for the type `{}`",
                other.display(self.compilation.symbols())
            ))),
        }
    }

    /// The row a named type is defined by (or referenced through), which is
    /// what `typeof` of an unbound generic type loads.
    pub(crate) fn definition_token(&mut self, symbol: SymbolId) -> Token {
        if let Some(token) = self.types.get(&symbol) {
            return *token;
        }
        self.referenced_type(symbol)
    }

    /// How a type is spelled inside a signature blob.
    pub(crate) fn sig_type(&mut self, ty: &Type) -> Result<SigType, EmitError> {
        let ty = &self.completed(ty);
        match ty {
            Type::Void => Ok(SigType::Primitive(ElementType::Void)),
            // `null` has no type of its own; where one is needed it is
            // whatever reference type the context wanted, and `object` is the
            // only safe answer here.
            Type::Null => Ok(SigType::Primitive(ElementType::Object)),
            // `dynamic` is `object` to the runtime; only the operations on it
            // are different.
            Type::Dynamic => Ok(SigType::Primitive(ElementType::Object)),
            Type::Array { element, rank } => {
                let element = Box::new(self.sig_type(element)?);
                // `T[]` is a vector, which the format spells on its own; `T[,]`
                // is an array with a shape, and the shape is a rank and the
                // bounds nobody writes.
                Ok(if *rank == 1 {
                    SigType::Array(element)
                } else {
                    SigType::MultiArray(element, *rank as u32)
                })
            }
            // A signature never names a type parameter: `Box<T>.Get` returns
            // `!0`, and what `!0` is depends on the construction the caller
            // wrote rather than on anything the definition can say.
            Type::TypeParameter(symbol) => match self.type_parameter_index(*symbol) {
                Some((index, false)) => Ok(SigType::TypeParameter(index)),
                Some((index, true)) => Ok(SigType::MethodTypeParameter(index)),
                None => Err(EmitError::new(format!(
                    "the type parameter `{}` belongs to nothing this can index",
                    self.compilation.symbols().get(*symbol).name
                ))),
            },
            Type::Named {
                symbol,
                type_arguments,
            } => {
                if !type_arguments.is_empty() {
                    let mut arguments = Vec::with_capacity(type_arguments.len());
                    for argument in type_arguments {
                        arguments.push(self.sig_type(argument)?);
                    }
                    let value_type = self.is_value_type_symbol(*symbol);
                    let coded = self.definition_coded(*symbol)?;
                    return Ok(SigType::Constructed {
                        value_type,
                        coded,
                        arguments,
                    });
                }
                if let Some(primitive) = self.primitive_of(*symbol) {
                    return Ok(SigType::Primitive(primitive));
                }
                // An enum is a value type too: its storage is an integer, but
                // its identity in a signature is the type itself.
                let value_type = matches!(
                    self.compilation.symbols().get(*symbol).type_kind(),
                    Some(TypeKind::Struct | TypeKind::Enum | TypeKind::RecordStruct)
                );
                Ok(SigType::Named {
                    value_type,
                    coded: self.type_coded(ty)?,
                })
            }
            // A `ref` local holds where something is rather than what it
            // holds, and its entry in the local signature says so. A `ref`
            // parameter is wrapped where the signature is built, because
            // whether it is one is a flag on the parameter and not part of
            // the type it was declared with.
            Type::ByRef(inner) => Ok(SigType::ByRef(Box::new(self.sig_type(inner)?))),
            // `void*` is a pointer to nothing in particular, which the format
            // spells the same way as any other pointer.
            Type::Pointer(inner) => Ok(SigType::Pointer(Box::new(self.sig_type(inner)?))),
            Type::FunctionPointer(pointer) => self.function_pointer_sig(pointer),
            // `(int, string)` is a `ValueTuple<int, string>`: the language
            // spells it one way and the runtime knows only the other, and the
            // element names are for the reader alone.
            Type::Tuple(elements) => {
                // Past seven the rest nest in an eighth `TRest` (§8.3.11).
                let (head, rest) = if elements.len() > 7 {
                    (&elements[..7], Some(Type::Tuple(elements[7..].to_vec())))
                } else {
                    (&elements[..], None)
                };
                let ty = self.tuple_as_named(head.len() + usize::from(rest.is_some()))?;
                let mut arguments = Vec::with_capacity(head.len() + 1);
                for element in head {
                    arguments.push(self.sig_type(&element.ty)?);
                }
                if let Some(rest) = rest {
                    arguments.push(self.sig_type(&rest)?);
                }
                Ok(SigType::Constructed {
                    value_type: true,
                    coded: self.definition_coded(ty)?,
                    arguments,
                })
            }
            // A survey wants an assembly out the other end, so a type it
            // cannot spell becomes `object`: the row is there, the shape is
            // wrong, and everything around it can still be read back.
            other if self.lenient => {
                let _ = other;
                Ok(SigType::Primitive(ElementType::Object))
            }
            other => Err(EmitError::new(format!(
                "cannot emit the type `{}` yet",
                other.display(self.compilation.symbols())
            ))),
        }
    }

    /// The constructor of the `ValueTuple` a tuple expression makes.
    ///
    /// Its parameters are the tuple's own type arguments, spelled `!0`, `!1`
    /// and so on: a `MemberRef` under a `TypeSpec` says what the definition
    /// looks like, and the `TypeSpec` says what it was constructed with.
    pub(crate) fn tuple_constructor(&mut self, ty: &Type) -> Result<Token, EmitError> {
        // `(a, b).ToString()` has a receiver the binder already reads as the
        // `ValueTuple<...>` underneath: the same constructor, named the same
        // way.
        let width = match ty {
            // Eight and up: seven elements and the nested rest.
            Type::Tuple(elements) => elements.len().min(8),
            Type::Named {
                symbol,
                type_arguments,
            } if !type_arguments.is_empty()
                && self.compilation.symbols().get(*symbol).name == "ValueTuple" =>
            {
                type_arguments.len()
            }
            _ => {
                return Err(EmitError::new(
                    "a tuple expression whose type is not a tuple",
                ));
            }
        };
        let spec = self.type_token(ty)?;
        let parameters: Vec<SigType> = (0..width)
            .map(|index| SigType::TypeParameter(index as u32))
            .collect();
        let signature = method_signature(true, &SigType::Primitive(ElementType::Void), &parameters);
        Ok(self
            .references
            .member_of_spec(&mut self.metadata, spec, ".ctor", &signature))
    }

    /// The `ValueTuple` of the given width, which is what a tuple really is.
    pub(crate) fn tuple_as_named(&self, width: usize) -> Result<SymbolId, EmitError> {
        // Eight and up nest: the eighth element of a `ValueTuple`8` is itself
        // a tuple of the rest. Saying so beats emitting seven and dropping the
        // others.
        if width > 8 {
            return Err(EmitError::new(format!(
                "a tuple of {width} elements: past seven they nest, eight at most"
            )));
        }
        let name = format!("System.ValueTuple`{width}");
        self.compilation
            .type_by_metadata_name(&name)
            .ok_or_else(|| {
                EmitError::new(format!("cannot emit a tuple: `{name}` is not referenced"))
            })
    }

    /// The element type a language keyword maps onto, if the symbol is one of
    /// the types the runtime treats specially.
    pub(crate) fn primitive_of(&self, symbol: SymbolId) -> Option<ElementType> {
        // `IntPtr` is `native int` in a signature and nothing else: a
        // reference that spells it as a value type names a member that does
        // not exist, which is what `IntPtr.Zero` came back as.
        match self.compilation.symbols().qualified_name(symbol).as_str() {
            "System.IntPtr" => return Some(ElementType::I),
            "System.UIntPtr" => return Some(ElementType::U),
            // `typedref` likewise: `SetValueDirect(TypedReference, object)`
            // spells it with an element type of its own.
            "System.TypedReference" => return Some(ElementType::TypedByRef),
            _ => {}
        }
        let special = self.special_of(symbol)?;
        Some(match special {
            SpecialType::Void => ElementType::Void,
            SpecialType::Boolean => ElementType::Boolean,
            SpecialType::Char => ElementType::Char,
            SpecialType::SByte => ElementType::I1,
            SpecialType::Byte => ElementType::U1,
            SpecialType::Int16 => ElementType::I2,
            SpecialType::UInt16 => ElementType::U2,
            SpecialType::Int32 => ElementType::I4,
            SpecialType::UInt32 => ElementType::U4,
            SpecialType::Int64 => ElementType::I8,
            SpecialType::UInt64 => ElementType::U8,
            SpecialType::Single => ElementType::R4,
            SpecialType::Double => ElementType::R8,
            SpecialType::String => ElementType::String,
            SpecialType::Object => ElementType::Object,
            SpecialType::Decimal => return None,
        })
    }

    /// Which special type a symbol is, if any.
    pub(crate) fn special_of(&self, symbol: SymbolId) -> Option<SpecialType> {
        SpecialType::ALL
            .iter()
            .copied()
            .find(|special| self.compilation.special_type(*special) == Some(symbol))
    }

    pub(crate) fn special_type_of(&self, ty: &Type) -> Option<SpecialType> {
        ty.symbol().and_then(|symbol| self.special_of(symbol))
    }

    /// Whether values of a type are copied rather than referred to, which is
    /// what decides whether a call needs the value or its address.
    pub(crate) fn is_value_type(&self, ty: &Type) -> bool {
        !ty.is_reference_type(self.compilation.symbols())
            && !matches!(ty, Type::Array { .. } | Type::Null | Type::Error)
    }

    /// The constant a field holds, for the fields that hold one rather than
    /// storing one.
    pub(crate) fn constant_of(&self, field: SymbolId) -> Option<ConstantValue> {
        self.binder.constant_value(field)
    }

    /// A planned parameter's type as a member reference has to write it: a
    /// `ref` parameter is a reference, exactly as the definition says.
    fn pending_parameter_type(&self, parameter: &ParameterPlan) -> Type {
        if parameter.by_ref || self.is_by_reference(parameter.symbol) {
            Type::ByRef(Box::new(parameter.ty.clone()))
        } else {
            parameter.ty.clone()
        }
    }

    /// The method or property a planned method declares the signature of,
    /// where the source wrote one: an accessor's return is its property's.
    fn declared_member(&self, source: &MethodSource) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        match source {
            MethodSource::Declared(member) => {
                let container = symbols.get(*member).container?;
                Some(
                    if symbols.get(*member).kind == SymbolKind::Method
                        && symbols.get(container).kind == SymbolKind::Property
                    {
                        container
                    } else {
                        *member
                    },
                )
            }
            MethodSource::PropertyGetter { property, .. } => Some(*property),
            MethodSource::Forwarding { member, .. }
            | MethodSource::InheritedForwarding { member, .. } => Some(*member),
            _ => None,
        }
    }

    fn method_signature_of(&mut self, plan: &MethodPlan) -> Result<Vec<u8>, EmitError> {
        if let Some(signature) = &plan.signature {
            return Ok(signature.clone());
        }
        // An accessor of a property that overrides one read from metadata
        // repeats the custom modifiers that one's accessor carries: the
        // runtime matches the override, or its `MethodImpl`, by them.
        if let Some(base) = self.overridden_metadata_accessor(&plan.source) {
            let modifiers = |emitter: &Self, symbol: SymbolId| {
                emitter
                    .compilation
                    .metadata_modifiers(symbol)
                    .map(<[_]>::to_vec)
                    .unwrap_or_default()
            };
            let returns = self.sig_type(&plan.return_type)?;
            let returned = modifiers(self, base);
            let return_type = self.with_modifiers(returns, &returned);
            let base_parameters = member_parameters(self.compilation.symbols(), base)
                .map(<[SymbolId]>::to_vec)
                .unwrap_or_default();
            let mut parameters = Vec::new();
            for (at, parameter) in plan.parameters.clone().iter().enumerate() {
                let ty = self.sig_type(&parameter.ty)?;
                let written = base_parameters
                    .get(at)
                    .map(|base| modifiers(self, *base))
                    .unwrap_or_default();
                parameters.push(self.with_modifiers(ty, &written));
            }
            return Ok(generic_method_signature(
                plan.instance,
                plan.type_parameters.len() as u32,
                &return_type,
                &parameters,
            ));
        }
        let mut return_type = self.sig_type(&plan.return_type)?;
        // `ref readonly T` comes back under a `modreq(InAttribute)`.
        if let Some(member) = self.declared_member(&plan.source) {
            return_type = self.returned_sig(member, return_type);
        }
        let mut parameters = Vec::new();
        for parameter in &plan.parameters.clone() {
            let ty = self.sig_type(&parameter.ty)?;
            // `ref` and `out` are the same thing to the runtime: a reference.
            // Which one it was is a promise the compiler checked, and the
            // `Out` flag on the row is all that is left of it.
            parameters.push(match parameter.symbol {
                Some(symbol) if self.is_by_reference(Some(symbol)) => {
                    self.parameter_sig(symbol, ty)
                }
                _ if parameter.by_ref => SigType::ByRef(Box::new(ty)),
                // A value parameter may still carry a `modopt` its base's has.
                Some(symbol) => self.parameter_sig(symbol, ty),
                None => ty,
            });
        }
        if let Some(member) = self.declared_member(&plan.source)
            && self
                .compilation
                .symbols()
                .get(member)
                .as_method()
                .is_some_and(|detail| detail.is_vararg)
        {
            return Ok(vararg_signature(
                plan.instance,
                &return_type,
                &parameters,
                &[],
            ));
        }
        Ok(generic_method_signature(
            plan.instance,
            plan.type_parameters.len() as u32,
            &return_type,
            &parameters,
        ))
    }

    /// The token for a member reached through a constructed type.
    ///
    /// `Box<int>.Get` has no definition of its own — only `Box`1.Get` does —
    /// so it is a `MemberRef` whose parent is the construction. Its signature
    /// is the *definition's*, with `!0` where the parameter goes: the
    /// arguments are already in the parent, and repeating them there would
    /// name a member that does not exist.
    pub(crate) fn member_of_constructed(
        &mut self,
        member: SymbolId,
        receiver: &Type,
    ) -> Result<Token, EmitError> {
        let spec = self.type_token(receiver)?;
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let mut name = self
            .emitted_names
            .get(&member)
            .cloned()
            .unwrap_or_else(|| symbol.name.clone());
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);

        let signature = match symbol.kind {
            SymbolKind::Field | SymbolKind::Event => {
                let ty = self.type_of(member);
                let ty = self.sig_type(&ty)?;
                field_signature(&ty)
            }
            // A property stands for the field behind it here: `Holder<T>.
            // Default { get; } = ...` writes the backing field of that
            // construction, and the accessors are reached another way.
            SymbolKind::Property => {
                name = self.backing_field_name(member);
                let ty = self.type_of(member);
                let ty = self.sig_type(&ty)?;
                field_signature(&ty)
            }
            _ => {
                let detail = symbol
                    .as_method()
                    .ok_or_else(|| EmitError::new("a member that is neither field nor method"))?;
                let parameters = detail.parameters.clone();
                // A local function made for a generic method carries that
                // method's parameters in front of its own, and a reference
                // to it has to say so too.
                let inherited = self
                    .methods
                    .get(&member)
                    .and_then(|token| self.inherited_generics.get(token))
                    .cloned()
                    .unwrap_or_default();
                let arity = (detail.type_parameters.len() + inherited.len()) as u32;
                let return_type = if name == ".ctor" {
                    SigType::Primitive(ElementType::Void)
                } else {
                    let ty = self.type_of(member);
                    let returns = self.sig_type(&ty)?;
                    self.returned_sig(member, returns)
                };
                let mut types = Vec::with_capacity(parameters.len());
                for parameter in parameters {
                    let ty = self.type_of(parameter);
                    let ty = self.sig_type(&ty)?;
                    types.push(self.parameter_sig(parameter, ty));
                }
                // A generic method reached through a constructed type keeps
                // its own arity: `Pair<int, string>.With<C>` is still one
                // method with one type parameter of its own.
                generic_method_signature(instance, arity, &return_type, &types)
            }
        };
        // A receiver that is not a construction after all — a task-like
        // type's builder from another assembly, `MyTaskBuilder` beside
        // `MyTaskBuilder<T>` — is a `TypeRef`, and the reference's parent
        // has to be tagged as one: tagged as a `TypeSpec`, the row it names
        // is one that is not there.
        let token = if spec.0 >> 24 == u32::from(table::TYPE_REF) {
            self.references
                .member_ref_on(&mut self.metadata, spec, &name, &signature)
        } else {
            self.references
                .member_of_spec(&mut self.metadata, spec, &name, &signature)
        };
        // The instantiation a call makes of the reference has to carry the
        // inherited parameters, the way one of the definition does.
        if let Some(inherited) = self
            .methods
            .get(&member)
            .and_then(|definition| self.inherited_generics.get(definition))
            .cloned()
            && !inherited.is_empty()
        {
            self.inherited_generics.insert(token, inherited);
        }
        Ok(token)
    }

    /// The token a call to a varargs method uses: a `MemberRef` under the
    /// method's own definition whose signature adds, past a sentinel, the
    /// types of what this call passes to its `__arglist` (§II.23.2.2).
    pub(crate) fn vararg_call_site(
        &mut self,
        method: SymbolId,
        extra: &[(Type, bool)],
    ) -> Result<Token, EmitError> {
        let definition = *self
            .methods
            .get(&method)
            .ok_or_else(|| EmitError::new("a varargs method of another assembly"))?;
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(method);
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        let detail = symbol
            .as_method()
            .ok_or_else(|| EmitError::new("a varargs call to no method"))?;
        let constructor = matches!(
            detail.method_kind,
            rustlyn_semantics::MethodKind::Constructor
        );
        let parameters = detail.parameters.clone();
        let name = if constructor {
            ".ctor".to_string()
        } else {
            self.emitted_names
                .get(&method)
                .cloned()
                .unwrap_or_else(|| symbol.name.clone())
        };
        let return_type = if constructor {
            SigType::Primitive(ElementType::Void)
        } else {
            let ty = self.type_of(method);
            let returns = self.sig_type(&ty)?;
            self.returned_sig(method, returns)
        };
        let mut fixed = Vec::with_capacity(parameters.len());
        for parameter in parameters {
            let ty = self.type_of(parameter);
            let ty = self.sig_type(&ty)?;
            fixed.push(self.parameter_sig(parameter, ty));
        }
        let mut extras = Vec::with_capacity(extra.len());
        for (ty, by_ref) in extra {
            let ty = self.sig_type(ty)?;
            extras.push(if *by_ref {
                SigType::ByRef(Box::new(ty))
            } else {
                ty
            });
        }
        let signature = vararg_signature(instance, &return_type, &fixed, &extras);
        // A `MemberRefParent` tagged 3 is a `MethodDef`, which is what a
        // call site of a varargs method in this module names.
        let parent = ((definition.0 & 0x00FF_FFFF) << 3) | 3;
        Ok(self.metadata.add_member_ref(parent, &name, &signature))
    }

    /// The token a call to a generic method uses.
    ///
    /// `Echo<int>` has no definition of its own — only `Echo<T>` does — so the
    /// call goes through a `MethodSpec`: the definition, plus the list of
    /// types the call settled on. The definition's own signature keeps `!!0`,
    /// because what `!!0` is comes from here.
    pub(crate) fn method_instantiation(
        &mut self,
        method: Token,
        type_arguments: &[Type],
    ) -> Result<Token, EmitError> {
        let mut arguments = Vec::with_capacity(type_arguments.len());
        for argument in type_arguments {
            arguments.push(self.sig_type(argument)?);
        }
        let signature = method_spec_signature(&arguments);
        // A `MethodDefOrRef` tagged 0 is a `MethodDef` and 1 is a `MemberRef`.
        let tag = u32::from(method.0 >> 24 == u32::from(table::MEMBER_REF));
        let coded = ((method.0 & 0x00FF_FFFF) << 1) | tag;
        Ok(self.metadata.add_method_spec(coded, &signature))
    }

    /// Says in metadata that a type is a `ref struct`.
    ///
    /// §II.22.10: a custom attribute is the constructor it calls and the
    /// arguments it was given; a constructor taking nothing is the prolog
    /// `0x0001` and a count of zero named arguments, and nothing else.
    /// Writes `[ThreadStatic]` on a field, which is what makes the runtime
    /// give each thread its own.
    fn mark_thread_static(&mut self, field: Token) {
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.ThreadStaticAttribute",
            ".ctor",
            &method_signature(true, &SigType::Primitive(ElementType::Void), &[]),
        );
        // A `HasCustomAttribute` parent tagged 1 is a `Field`, and a
        // `CustomAttributeType` tagged 3 is a `MemberRef`.
        self.metadata.add_custom_attribute(
            ((field.0 & 0x00FF_FFFF) << 5) | 1,
            ((constructor.0 & 0x00FF_FFFF) << 3) | 3,
            &[0x01, 0x00, 0x00, 0x00],
        );
    }

    /// `[DecimalConstant(scale, sign, hi, mid, lo)]` on a `const decimal`
    /// field or a `decimal` parameter's default: what it holds, which only
    /// the attribute can say.
    fn mark_decimal_constant(&mut self, parent: u32, parts: DecimalParts) {
        let byte = SigType::Primitive(ElementType::U1);
        let word = SigType::Primitive(ElementType::U4);
        let constructor = self.references.member_ref(
            &mut self.metadata,
            "System.Runtime.CompilerServices.DecimalConstantAttribute",
            ".ctor",
            &method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[byte.clone(), byte, word.clone(), word.clone(), word],
            ),
        );
        let mut blob = vec![
            0x01,
            0x00,
            parts.scale,
            if parts.negative { 0x80 } else { 0 },
        ];
        blob.extend_from_slice(&parts.hi.to_le_bytes());
        blob.extend_from_slice(&parts.mid.to_le_bytes());
        blob.extend_from_slice(&parts.lo.to_le_bytes());
        blob.extend_from_slice(&[0x00, 0x00]);
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }

    /// The value of a `const decimal` field, from its initializer: a
    /// literal (made with `decimal`'s five-part constructor), a whole
    /// number, another such constant, one of `decimal`'s own, or the
    /// negation of any of them. `None` where it is anything else.
    fn decimal_constant(&mut self, field: SymbolId, depth: usize) -> Option<DecimalParts> {
        let symbols = self.compilation.symbols();
        let container = symbols.get(field).container?;
        if self.special_of(container) == Some(rustlyn_semantics::SpecialType::Decimal) {
            let max = DecimalParts {
                lo: u32::MAX,
                mid: u32::MAX,
                hi: u32::MAX,
                negative: false,
                scale: 0,
            };
            let one = DecimalParts {
                lo: 1,
                mid: 0,
                hi: 0,
                negative: false,
                scale: 0,
            };
            return Some(match symbols.get(field).name.as_str() {
                "MaxValue" => max,
                "MinValue" => DecimalParts {
                    negative: true,
                    ..max
                },
                "One" => one,
                "MinusOne" => DecimalParts {
                    negative: true,
                    ..one
                },
                "Zero" => DecimalParts { lo: 0, ..one },
                _ => return None,
            });
        }
        if depth > 32 {
            return None;
        }
        let body = self.body_of(field)?;
        let value = crate::codegen::first_returned_value(&body)?;
        self.decimal_value(&value, depth)
    }

    fn decimal_value(&mut self, value: &BoundExpression, depth: usize) -> Option<DecimalParts> {
        // An integer constant of any type, however it is written —
        // `ulong.MaxValue`, `'a' + 1`, `(short)-3` — is a whole number.
        if self.special_type_of(&value.ty) != Some(rustlyn_semantics::SpecialType::Decimal)
            && let Some(constant) = self.binder.folded(value)
        {
            let whole = match constant {
                ConstantValue::Int32(value) => i128::from(value),
                ConstantValue::UInt32(value) => i128::from(value),
                ConstantValue::Int64(value) => i128::from(value),
                ConstantValue::UInt64(value) => i128::from(value),
                ConstantValue::Char(value) => i128::from(u32::from(value)),
                _ => return self.decimal_value_of_kind(value, depth),
            };
            let magnitude = whole.unsigned_abs();
            return Some(DecimalParts {
                lo: magnitude as u32,
                mid: (magnitude >> 32) as u32,
                hi: 0,
                negative: whole < 0,
                scale: 0,
            });
        }
        self.decimal_value_of_kind(value, depth)
    }

    fn decimal_value_of_kind(
        &mut self,
        value: &BoundExpression,
        depth: usize,
    ) -> Option<DecimalParts> {
        match &value.kind {
            BoundExpressionKind::Conversion { operand, .. } => self.decimal_value(operand, depth),
            BoundExpressionKind::Literal(constant) => {
                let (negative, magnitude) = match *constant {
                    ConstantValue::Int32(value) => (value < 0, u64::from(value.unsigned_abs())),
                    ConstantValue::Int64(value) => (value < 0, value.unsigned_abs()),
                    ConstantValue::UInt32(value) => (false, u64::from(value)),
                    ConstantValue::UInt64(value) => (false, value),
                    ConstantValue::Char(value) => (false, u64::from(u32::from(value))),
                    _ => return None,
                };
                Some(DecimalParts {
                    lo: magnitude as u32,
                    mid: (magnitude >> 32) as u32,
                    hi: 0,
                    negative,
                    scale: 0,
                })
            }
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } if arguments.len() == 5 && initializers.is_empty() => {
                let word = |argument: &BoundExpression| match argument.constant() {
                    Some(ConstantValue::Int32(value)) => Some(*value as u32),
                    Some(ConstantValue::UInt32(value)) => Some(*value),
                    _ => None,
                };
                let negative = match arguments[3].constant() {
                    Some(ConstantValue::Boolean(value)) => *value,
                    _ => return None,
                };
                Some(DecimalParts {
                    lo: word(&arguments[0])?,
                    mid: word(&arguments[1])?,
                    hi: word(&arguments[2])?,
                    negative,
                    scale: u8::try_from(word(&arguments[4])?).ok()?,
                })
            }
            BoundExpressionKind::Unary {
                operator: rustlyn_semantics::UnaryOperator::Minus,
                operand,
            } => {
                let parts = self.decimal_value(operand, depth)?;
                Some(DecimalParts {
                    negative: !parts.negative,
                    ..parts
                })
            }
            BoundExpressionKind::Unary {
                operator: rustlyn_semantics::UnaryOperator::Plus,
                operand,
            } => self.decimal_value(operand, depth),
            BoundExpressionKind::Field { field, .. } => self.decimal_constant(*field, depth + 1),
            _ => None,
        }
    }

    fn mark_by_ref_like(&mut self, token: Token) {
        // A `HasCustomAttribute` parent tagged 3 is a `TypeDef`.
        self.mark_with(
            ((token.0 & 0x00FF_FFFF) << 5) | 3,
            "System.Runtime.CompilerServices.IsByRefLikeAttribute",
        );
    }

    /// Refuses a static member of a generic type.
    ///
    /// `Table<string>.Kind` is a member of a *construction*, and the CLI has
    /// no way to name one without saying which: the token would have to be a
    /// `MemberRef` under a `TypeSpec`. The bound tree drops the construction
    /// for a static access — a static member has no receiver to carry it — so
    /// the information is not here to emit. Saying so beats emitting
    /// `Table`1::get_Kind`, which loads but throws the moment it is called.
    pub(crate) fn check_not_static_generic(&self, member: SymbolId) -> Result<(), EmitError> {
        let symbols = self.compilation.symbols();
        // Not `arity`: a type that writes no parameters of its own is still
        // generic in metadata when it is nested in one that does, and a
        // static member of it needs a construction just the same.
        let generic = symbols
            .get(member)
            .container
            .is_some_and(|container| self.own_construction(container).is_some());
        if generic {
            return Err(EmitError::new(format!(
                "cannot emit the static member `{}` of a generic type yet",
                symbols.qualified_name(member)
            )));
        }
        Ok(())
    }

    /// Whether calling a member leaves the value it is called on as it was:
    /// a `readonly` member, a member of a `readonly struct`, or a property
    /// whose getter is `readonly`.
    pub(crate) fn is_readonly_member(&self, member: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        if symbol.modifiers.contains(Modifiers::READONLY) {
            return true;
        }
        // An automatic getter never writes; a getter read from metadata says
        // what it promises with the attribute the loader turned into this.
        if let Some(detail) = symbol.as_property() {
            if detail
                .getter
                .is_some_and(|getter| symbols.get(getter).modifiers.contains(Modifiers::READONLY))
            {
                return true;
            }
            if !self.compilation.is_from_metadata(member)
                && self.binder.is_automatic_property(member)
            {
                return true;
            }
        }
        let mut container = symbol.container;
        while let Some(at) = container {
            let owner = symbols.get(at);
            if owner.kind == SymbolKind::NamedType {
                return owner.modifiers.contains(Modifiers::READONLY)
                    // An enum has no fields of its own to write.
                    || owner.type_kind() == Some(TypeKind::Enum);
            }
            container = owner.container;
        }
        false
    }

    /// Whether a parameter is `ref` or `out`.
    pub(crate) fn is_by_reference(&self, parameter: Option<SymbolId>) -> bool {
        parameter.is_some_and(|symbol| {
            self.compilation
                .symbols()
                .get(symbol)
                .as_parameter()
                .is_some_and(|detail| {
                    // `in` is a reference too: `in T` is `T&` that the callee
                    // promises not to write through, and the promise is the
                    // compiler's to keep, not the runtime's.
                    detail.ref_kind != rustlyn_semantics::RefKind::None
                })
        })
    }

    /// A nested type of a generic type, named the way a signature has to name
    /// it.
    ///
    /// The declaration pass already gives such a type the enclosing
    /// parameters as its own — `Holder<T>.Walker` declares `T` — because the
    /// CLI has no notion of an enclosing scope. What the *source* writes is
    /// the difference: `Walker`, written inside `Holder<T>`, means
    /// `Holder`1/Walker<!0>`, and the argument has to be in the signature
    /// even though nobody wrote it. The missing arguments are always the
    /// leading ones, and inside the enclosing type they are its own
    /// parameters, which is the only place such a name can be written.
    pub(crate) fn completed(&self, ty: &Type) -> Type {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return ty.clone();
        };
        // Only for a type this assembly defines. A nested type of a referenced
        // assembly is named through its enclosing *construction* —
        // `List<string>.Enumerator` — and the binder does not keep which one,
        // so spelling a parameter here would put `!0` where no `!0` exists.
        if !self.defining.contains(symbol) {
            return ty.clone();
        }
        let declared = self
            .compilation
            .symbols()
            .get(*symbol)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        if type_arguments.len() >= declared.len() {
            return ty.clone();
        }
        let missing = declared.len() - type_arguments.len();
        let mut arguments: Vec<Type> = declared[..missing]
            .iter()
            .copied()
            .map(Type::TypeParameter)
            .collect();
        arguments.extend(type_arguments.iter().cloned());
        Type::Named {
            symbol: *symbol,
            type_arguments: arguments,
        }
    }

    /// The named type a member belongs to.
    ///
    /// Not always its container: an accessor belongs to the property, which
    /// belongs to the type, and a lambda's method to whatever held the lambda.
    pub(crate) fn enclosing_type(&self, member: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let mut current = symbols.get(member).container;
        while let Some(id) = current {
            if symbols.get(id).kind == rustlyn_semantics::SymbolKind::NamedType {
                return Some(id);
            }
            current = symbols.get(id).container;
        }
        None
    }

    /// The type as its own members name it: `Pool<!0>` inside `Pool<T>`.
    ///
    /// `None` where the type is not generic and names itself. A member of a
    /// generic type has no definition of its own to point at — everything
    /// about it depends on the construction — so anything naming one from
    /// inside has to go through a `TypeSpec`.
    pub(crate) fn own_construction(&self, symbol: SymbolId) -> Option<Type> {
        let parameters = self
            .compilation
            .symbols()
            .get(symbol)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        (!parameters.is_empty()).then(|| Type::Named {
            symbol,
            type_arguments: parameters.into_iter().map(Type::TypeParameter).collect(),
        })
    }

    /// The construction a member has to be named through.
    ///
    /// A member inherited from a generic base belongs to *that construction*:
    /// `Counter : Visitor<int, string>` calls `Visitor<int, string>::Visit`,
    /// The construction a member has to be named through.
    ///
    /// A member inherited from a generic base belongs to *that construction*:
    /// `Counter : Visitor<int, string>` calls `Visitor<int, string>::Visit`,
    /// and the open definition's method is not one the runtime can call. The
    /// receiver's own type says nothing — it has no type arguments — so the
    /// chain up to the declaring type is what answers.
    pub(crate) fn through(&self, member: SymbolId, receiver: Option<&Type>) -> Option<Type> {
        let receiver = receiver?;
        // A tuple's members are the `ValueTuple<...>`'s, reached through
        // that construction: `Item2` of a `(int?, string)` is a `string`
        // only there.
        let named;
        let receiver = match receiver {
            Type::Tuple(elements) => {
                let symbol = self.tuple_as_named(elements.len()).ok()?;
                named = Type::Named {
                    symbol,
                    type_arguments: elements.iter().map(|element| element.ty.clone()).collect(),
                };
                &named
            }
            other => other,
        };
        let symbols = self.compilation.symbols();
        let mut current = symbols.get(member).container;
        while let Some(id) = current {
            if symbols.get(id).kind == rustlyn_semantics::SymbolKind::NamedType {
                break;
            }
            current = symbols.get(id).container;
        }
        // A member the receiver's own type declares is named through the
        // receiver; one it inherited belongs to the base *as this receiver
        // constructs it*, and saying otherwise names a member the base has
        // and the derived type does not — `CachingBase<Entry<TKey,
        // TValue>>.mask` is not a member of what derives from it.
        let Some(container) = current.filter(|container| receiver.symbol() != Some(*container))
        else {
            return self.is_constructed(receiver).then(|| receiver.clone());
        };
        let constructed = self.binder.constructed_from(receiver, container)?;
        self.is_constructed(&constructed).then_some(constructed)
    }

    /// Whether a type is a construction of a generic definition, which is what
    /// makes its members need a `MemberRef` rather than their definitions.
    pub(crate) fn is_constructed(&self, ty: &Type) -> bool {
        // A nested type of a generic type is a construction too, even where
        // the source wrote no arguments at all.
        matches!(self.completed(ty), Type::Named { type_arguments, .. } if !type_arguments.is_empty())
    }

    /// The accessor a property or an indexer is read or written through.
    ///
    /// The CLI has no properties: `list[0]` and `point.X` both reach ordinary
    /// methods, and the only question is which token names them. That depends
    /// on the receiver, not on the declaration: `Cell<int>.get_Value` and
    /// `Cell<string>.get_Value` are one definition and two members, so a
    /// constructed receiver takes a `MemberRef` under a `TypeSpec` carrying
    /// the *definition's* signature — `!0`, whose meaning comes from the
    /// construction — while anything else can name the method directly.
    ///
    /// An indexer's name comes from the type's `DefaultMember` attribute:
    /// `Item` nearly everywhere, `Chars` on `System.String`.
    /// The getter a read of a property calls through a receiver of this
    /// type: an extension block's instantiated for it.
    pub(crate) fn read_accessor(
        &mut self,
        property: SymbolId,
        receiver: Option<&Type>,
    ) -> Result<Token, EmitError> {
        match receiver {
            Some(receiver) if self.is_extension_property(property) => {
                self.place_accessor(property, None, Some(receiver), false)
            }
            _ => self.property_accessor(property, receiver, false),
        }
    }

    /// An accessor as a place calls it: an extension block's (C# 14),
    /// instantiated for the receiver where the block is generic, or any
    /// other property's through its receiver's type.
    pub(crate) fn place_accessor(
        &mut self,
        property: SymbolId,
        receiver_type: Option<&Type>,
        extension_receiver: Option<&Type>,
        setter: bool,
    ) -> Result<Token, EmitError> {
        let Some(receiver) = extension_receiver else {
            return self.property_accessor(property, receiver_type, setter);
        };
        let token = self.property_accessor(property, None, setter)?;
        let (generics, first) = {
            let symbols = self.compilation.symbols();
            let Some(detail) = symbols.get(property).as_property() else {
                return Ok(token);
            };
            (
                detail.extension_generics.clone(),
                detail.parameters.first().copied(),
            )
        };
        if generics.is_empty() {
            return Ok(token);
        }
        let mut inferred = HashMap::new();
        if let Some(first) = first {
            let pattern = self.type_of(first);
            // A receiver that only converts to the parameter's type — an
            // array for an `IEnumerable<T>`, a `List<int>` for an
            // `IReadOnlyList<T>` — says what `T` is through the
            // construction of that type it reaches.
            let actual = match (&pattern, receiver) {
                (Type::Named { symbol, .. }, receiver) if receiver.symbol() != Some(*symbol) => {
                    let span_element = match receiver {
                        Type::Array {
                            element: given,
                            rank: 1,
                        } if self.binder.span_parts(&pattern).is_some() => Some(Type::Named {
                            symbol: *symbol,
                            type_arguments: vec![(**given).clone()],
                        }),
                        _ => None,
                    };
                    span_element
                        .or_else(|| self.binder.constructed_from(receiver, *symbol))
                        .unwrap_or_else(|| receiver.clone())
                }
                _ => receiver.clone(),
            };
            unify(&pattern, &actual, &mut inferred);
        }
        let arguments: Vec<Type> = generics
            .iter()
            .map(|parameter| inferred.get(parameter).cloned().unwrap_or(Type::Error))
            .collect();
        self.method_instantiation(token, &arguments)
    }

    /// The name of an automatic property's field: `<X>k__BackingField`, or
    /// `<X>i__Field` for an anonymous type's.
    pub(crate) fn backing_field_name(&self, property: SymbolId) -> String {
        let symbols = self.compilation.symbols();
        let name = &symbols.get(property).name;
        let anonymous = symbols
            .get(property)
            .container
            .and_then(|container| symbols.get(container).as_named_type())
            .is_some_and(|detail| detail.anonymous);
        if anonymous {
            format!("<{name}>i__Field")
        } else {
            format!("<{name}>k__BackingField")
        }
    }

    /// Whether a property is an extension block's (C# 14) instance one:
    /// static in metadata, with the receiver as its first parameter.
    pub(crate) fn is_extension_property(&self, member: SymbolId) -> bool {
        self.compilation
            .symbols()
            .get(member)
            .as_property()
            .is_some_and(|detail| detail.extended.is_some() && !detail.parameters.is_empty())
    }

    pub(crate) fn property_accessor(
        &mut self,
        property: SymbolId,
        receiver: Option<&Type>,
        setter: bool,
    ) -> Result<Token, EmitError> {
        let token = self.declared_property_accessor(property, receiver, setter)?;
        // A static member of a generic extension block, reached through the
        // type that says what the block's type parameters are:
        // `C<int>.P` for `extension<T>(C<T>)`.
        let instantiation = receiver.and_then(|receiver| {
            let detail = self.compilation.symbols().get(property).as_property()?;
            let extended = detail.extended?;
            (detail.parameters.is_empty() && !detail.extension_generics.is_empty()).then(|| {
                (
                    extended,
                    detail.extension_generics.clone(),
                    receiver.clone(),
                )
            })
        });
        let Some((extended, generics, receiver)) = instantiation else {
            return Ok(token);
        };
        let mut sink = rustlyn_semantics::Diagnostics::new();
        let pattern = self.binder.resolve_type_ref(extended, &mut sink);
        let mut inferred = HashMap::new();
        let actual = match &pattern {
            Type::Named { symbol, .. } if receiver.symbol() != Some(*symbol) => self
                .binder
                .constructed_from(&receiver, *symbol)
                .unwrap_or(receiver),
            _ => receiver,
        };
        unify(&pattern, &actual, &mut inferred);
        let arguments: Vec<Type> = generics
            .iter()
            .map(|parameter| inferred.get(parameter).cloned().unwrap_or(Type::Error))
            .collect();
        self.method_instantiation(token, &arguments)
    }

    fn declared_property_accessor(
        &mut self,
        property: SymbolId,
        receiver: Option<&Type>,
        setter: bool,
    ) -> Result<Token, EmitError> {
        // An extension block's accessor belongs to the static class that
        // declared it, whatever the receiver.
        let receiver = if self
            .compilation
            .symbols()
            .get(property)
            .as_property()
            .is_some_and(|detail| detail.extended.is_some())
        {
            None
        } else {
            receiver
        };
        let original_receiver = receiver.cloned();
        // A property the receiver inherited belongs to the base as this
        // receiver constructs it: `CachingBase<Entry<TKey, TValue>>.Entries`
        // is not a member of the type that derives from it.
        let through = self.through(property, receiver);
        // A property inherited from a type that is not a construction —
        // `IsEmpty` of the plain `IConstantValueSet` read through an
        // `IConstantValueSet<int>` — is its definition's, not a member of
        // the receiver's type.
        let inherited = receiver.is_some_and(|receiver| {
            receiver.symbol().is_some() && self.enclosing_type(property) != receiver.symbol()
        });
        let receiver = through.as_ref().or(if inherited { None } else { receiver });
        let constructed = receiver.is_some_and(|receiver| self.is_constructed(receiver));
        if receiver.is_none() {
            self.check_not_static_generic(property)?;
        }
        if !constructed {
            let planned = if setter {
                self.setters.get(&property)
            } else {
                self.getters.get(&property)
            };
            if let Some(token) = planned {
                return Ok(*token);
            }
        }

        let symbols = self.compilation.symbols();
        let symbol = symbols.get(property);
        let container = symbol
            .container
            .ok_or_else(|| EmitError::new("a property with no container"))?;
        let qualified = symbols.metadata_qualified_name(container);
        let detail = symbol
            .as_property()
            .ok_or_else(|| EmitError::new("a property symbol without property detail"))?;
        let (is_indexer, parameter_symbols) = (detail.is_indexer, detail.parameters.clone());
        let present = if setter {
            detail.has_set || detail.has_init
        } else {
            detail.has_get
        };
        let display = if is_indexer {
            format!("{qualified}.this[]")
        } else {
            format!("{qualified}.{}", symbol.name)
        };
        // An override that writes only a getter still has the setter it
        // overrides: `b.Property1++` through it calls the base's.
        if !present
            && symbol.modifiers.contains(Modifiers::OVERRIDE)
            && let Some(overridden) = self.overridden_method(property)
            && overridden != property
        {
            return self.property_accessor(overridden, original_receiver.as_ref(), setter);
        }
        if !present {
            return Err(EmitError::new(format!(
                "`{display}` has no {} to call",
                if setter { "setter" } else { "getter" }
            )));
        }
        // A property declared here whose accessor was never planned is one
        // `plan_property` refused; saying so beats referencing a method that
        // is not in the assembly. A constructed receiver comes through here
        // too, and its accessor *is* planned — it just needs a `MemberRef`
        // rather than the definition's token.
        let planned = if setter {
            self.setters.contains_key(&property)
        } else {
            self.getters.contains_key(&property)
        };
        if !self.compilation.is_from_corlib(property) && !planned {
            return Err(EmitError::new(format!("cannot emit `{display}` yet")));
        }

        // A property this assembly did not declare has its accessors as
        // symbols already, under their real names: `StringBuilder`'s indexer
        // is reached through `get_Chars`, because the type said so with
        // `[IndexerName]`, and nothing but the row itself knows that.
        let declared_accessor = self
            .compilation
            .is_from_metadata(property)
            .then(|| {
                symbols
                    .get(property)
                    .as_property()
                    .and_then(|detail| if setter { detail.setter } else { detail.getter })
            })
            .flatten();
        let name = if let Some(accessor) = declared_accessor {
            symbols.get(accessor).name.clone()
        } else if is_indexer {
            format!(
                "{}_{}",
                if setter { "set" } else { "get" },
                default_member_name(&qualified)
            )
        } else {
            format!(
                "{}_{}",
                if setter { "set" } else { "get" },
                symbols.get(property).name
            )
        };
        let instance = !symbols.get(property).modifiers.contains(Modifiers::STATIC);

        let element = self.type_of(property);
        let element = self.sig_type(&element)?;
        let mut parameters = Vec::with_capacity(parameter_symbols.len() + 1);
        let read = self.returned_sig(property, element.clone());
        for parameter in parameter_symbols {
            let ty = self.type_of(parameter);
            let ty = self.sig_type(&ty)?;
            parameters.push(self.parameter_sig(parameter, ty));
        }
        let signature = if setter {
            // A setter takes the value last, after any arguments.
            parameters.push(element);
            method_signature(
                instance,
                &SigType::Primitive(ElementType::Void),
                &parameters,
            )
        } else {
            method_signature(instance, &read, &parameters)
        };

        if constructed {
            let receiver = receiver.ok_or_else(|| EmitError::new("a constructed nothing"))?;
            let spec = self.type_token(receiver)?;
            return Ok(self
                .references
                .member_of_spec(&mut self.metadata, spec, &name, &signature));
        }
        let parent = self.referenced_type(container);
        Ok(self
            .references
            .member_ref_on(&mut self.metadata, parent, &name, &signature))
    }

    /// The token for a member of the core library, resolved against the real
    /// framework by name and signature.
    pub(crate) fn corlib_member(&mut self, method: SymbolId) -> Result<Token, EmitError> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(method);
        let mut container = symbol
            .container
            .ok_or_else(|| EmitError::new("a core library member with no container"))?;
        // An accessor read from metadata hangs off its property or event;
        // the type that declares it is the one the reference names.
        if matches!(
            symbols.get(container).kind,
            SymbolKind::Property | SymbolKind::Event
        ) && let Some(declaring) = symbols.get(container).container
        {
            container = declaring;
        }
        let name = symbol.name.clone();
        let instance = !symbol.modifiers.contains(Modifiers::STATIC);
        let detail = symbol
            .as_method()
            .ok_or_else(|| EmitError::new("a core library member that is not a method"))?;
        let parameter_symbols = detail.parameters.clone();
        let arity = detail.type_parameters.len() as u32;

        let return_type = if name == ".ctor" {
            SigType::Primitive(ElementType::Void)
        } else {
            let ty = self.type_of(method);
            let returns = self.sig_type(&ty)?;
            self.returned_sig(method, returns)
        };
        let mut parameters = Vec::new();
        for parameter in parameter_symbols {
            let ty = self.type_of(parameter);
            let ty = self.sig_type(&ty)?;
            parameters.push(self.parameter_sig(parameter, ty));
        }
        // A generic method's reference carries its own arity and spells its
        // type parameters as `!!0`: the `MethodSpec` that says what they are
        // is a separate row, and this one has to match the definition.
        let signature = generic_method_signature(instance, arity, &return_type, &parameters);
        let parent = self.referenced_type(container);
        Ok(self
            .references
            .member_ref_on(&mut self.metadata, parent, &name, &signature))
    }

    /// A `MemberRef` for a field of a type this assembly does not define.
    ///
    /// `int.MaxValue` and `string.Empty` are ordinary static fields of
    /// ordinary framework types, and nothing else is needed to reach one.
    pub(crate) fn referenced_field(&mut self, field: SymbolId) -> Result<Token, EmitError> {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(field);
        let container = symbol
            .container
            .ok_or_else(|| EmitError::new("a referenced field with no container"))?;
        let name = symbol.name.clone();
        // A `fixed` buffer's type is its element's to C#, and the struct made
        // for it to the runtime.
        let ty = match self.compilation.metadata_fixed_buffer(field) {
            Some(buffer) => Type::named(buffer),
            None => self.type_of(field),
        };
        let ty = self.sig_type(&ty)?;
        let signature = field_signature(&ty);
        let parent = self.referenced_type(container);
        Ok(self
            .references
            .member_ref_on(&mut self.metadata, parent, &name, &signature))
    }

    /// The one field of the struct a `fixed` buffer field is of, whose
    /// address is the buffer's first element's: defined here for a buffer
    /// declared here, and a reference for one read from another assembly.
    pub(crate) fn fixed_element_field(
        &mut self,
        field: SymbolId,
    ) -> Result<Option<Token>, EmitError> {
        if let Some((token, _)) = self.fixed_buffers.get(&field) {
            return Ok(Some(*token));
        }
        let Some(buffer) = self.compilation.metadata_fixed_buffer(field) else {
            return Ok(None);
        };
        let element = self.type_of(field);
        let element_sig = self.sig_type(&element)?;
        let parent = self.referenced_type(buffer);
        let token = self.references.member_ref_on(
            &mut self.metadata,
            parent,
            "FixedElementField",
            &field_signature(&element_sig),
        );
        self.fixed_buffers.insert(field, (token, element));
        Ok(Some(token))
    }

    /// A member of the framework named directly, for the helpers a lowering
    /// needs that no source ever mentions.
    pub(crate) fn framework_member(
        &mut self,
        qualified_type: &str,
        name: &str,
        instance: bool,
        return_type: &SigType,
        parameters: &[SigType],
    ) -> Token {
        let signature = method_signature(instance, return_type, parameters);
        self.references
            .member_ref(&mut self.metadata, qualified_type, name, &signature)
    }

    /// `System.Activator.CreateInstance<T>()`, instantiated for one type.
    ///
    /// `new T()` on a type parameter has no constructor to call: which one it
    /// would be is not known until the method is instantiated, so the runtime
    /// is asked to find it. This is what `where T : new()` compiles to, and
    /// the reason the constraint is needed at all.
    pub(crate) fn activator_create(&mut self, ty: &Type) -> Result<Token, EmitError> {
        let signature = generic_method_signature(false, 1, &SigType::MethodTypeParameter(0), &[]);
        let member = self.references.member_ref(
            &mut self.metadata,
            "System.Activator",
            "CreateInstance",
            &signature,
        );
        self.method_instantiation(member, std::slice::from_ref(ty))
    }

    /// A parameter's type as a signature spells it: `ref`, `out` and `in` are
    /// references, and an `in` one is under a `modreq(InAttribute)` where its
    /// member's signature carries one.
    pub(crate) fn parameter_sig(&mut self, parameter: SymbolId, ty: SigType) -> SigType {
        // A parameter read from metadata, or one of an override of such a
        // member, carries exactly the modifiers written there.
        if let Some(modifiers) = self.written_modifiers(parameter, 0) {
            let ty = if self.is_by_reference(Some(parameter)) {
                SigType::ByRef(Box::new(ty))
            } else {
                ty
            };
            return self.with_modifiers(ty, &modifiers);
        }
        if !self.is_by_reference(Some(parameter)) {
            return ty;
        }
        let reference = SigType::ByRef(Box::new(ty));
        if !self.in_modifier(parameter, 0) {
            return reference;
        }
        let modifier = self.in_attribute_coded(parameter);
        SigType::Required {
            modifier,
            inner: Box::new(reference),
        }
    }

    /// A function pointer's signature as a type: `ref`, `in` and `out` are
    /// references, the last two under the `modreq` that tells them apart
    /// (`InAttribute`, `OutAttribute`), and a convention beyond what the
    /// calling convention byte can say is a `modopt(CallConv*)` on the return.
    pub(crate) fn function_pointer_sig(
        &mut self,
        pointer: &rustlyn_semantics::FunctionPointer,
    ) -> Result<SigType, EmitError> {
        let (returns, parameters) = self.function_pointer_parts(pointer)?;
        Ok(SigType::FunctionPointer {
            convention: pointer.convention,
            returns: Box::new(returns),
            parameters,
        })
    }

    /// The return type and the parameter types a function pointer's
    /// signature spells, as [`Self::function_pointer_sig`] writes them.
    pub(crate) fn function_pointer_parts(
        &mut self,
        pointer: &rustlyn_semantics::FunctionPointer,
    ) -> Result<(SigType, Vec<SigType>), EmitError> {
        let mut returns = self.sig_type(&pointer.returns)?;
        returns = self.by_reference_sig(pointer.returns_ref, returns);
        for name in pointer.modifiers.iter().rev() {
            let modifier = self.references.type_ref_coded(
                &mut self.metadata,
                &format!("System.Runtime.CompilerServices.CallConv{name}"),
            );
            returns = SigType::Optional {
                modifier,
                inner: Box::new(returns),
            };
        }
        let mut parameters = Vec::with_capacity(pointer.parameters.len());
        for (kind, ty) in &pointer.parameters {
            let ty = self.sig_type(ty)?;
            parameters.push(self.by_reference_sig(*kind, ty));
        }
        Ok((returns, parameters))
    }

    /// A type as a function pointer's parameter or return spells it for
    /// one `ref` kind.
    fn by_reference_sig(&mut self, kind: RefKind, ty: SigType) -> SigType {
        let modifier = match kind {
            RefKind::None => return ty,
            RefKind::Ref => return SigType::ByRef(Box::new(ty)),
            RefKind::In => "System.Runtime.InteropServices.InAttribute",
            RefKind::Out => "System.Runtime.InteropServices.OutAttribute",
        };
        SigType::Required {
            modifier: self.references.type_ref_coded(&mut self.metadata, modifier),
            inner: Box::new(SigType::ByRef(Box::new(ty))),
        }
    }

    /// The `InAttribute` a `modreq` on a parameter or on a member's return
    /// names: for a member read from metadata, whichever its signature named;
    /// for one of this assembly's, its own `InAttribute` where it declares
    /// one, as it is for Roslyn, and the framework's otherwise.
    pub(crate) fn in_attribute_coded(&mut self, symbol: SymbolId) -> u32 {
        const NAME: &str = "System.Runtime.InteropServices.InAttribute";
        if let Some(modifier) = self.compilation.metadata_modifier_type(symbol) {
            return type_def_or_ref(1, self.referenced_type(modifier).0 & 0x00FF_FFFF);
        }
        if !self.compilation.is_from_metadata(symbol)
            && let Some(own) = self.own_in_attribute()
            && let Some(token) = self.types.get(&own).copied()
        {
            return type_def_or_ref(0, token.0 & 0x00FF_FFFF);
        }
        self.references.type_ref_coded(&mut self.metadata, NAME)
    }

    /// The `InAttribute` the program declares itself, if any.
    fn own_in_attribute(&mut self) -> Option<SymbolId> {
        const NAME: &str = "System.Runtime.InteropServices.InAttribute";
        if let Some((count, own)) = self.own_in_attribute
            && count == self.types.len()
        {
            return own;
        }
        let symbols = self.compilation.symbols();
        let own = self
            .types
            .keys()
            .copied()
            .find(|ty| symbols.metadata_qualified_name(*ty) == NAME);
        self.own_in_attribute = Some((self.types.len(), own));
        own
    }

    /// The `InAttribute` a member's `modreq`s name: the one its metadata
    /// signature has, this compilation's own where it declares one, or the
    /// framework's.
    fn in_attribute_type(&self, symbol: SymbolId) -> Option<SymbolId> {
        const NAME: &str = "System.Runtime.InteropServices.InAttribute";
        if let Some(modifier) = self.compilation.metadata_modifier_type(symbol) {
            return Some(modifier);
        }
        let symbols = self.compilation.symbols();
        if !self.compilation.is_from_metadata(symbol)
            && let Some(own) = self
                .types
                .keys()
                .find(|ty| symbols.metadata_qualified_name(**ty) == NAME)
        {
            return Some(*own);
        }
        self.compilation.type_by_metadata_name(NAME)
    }

    /// Whether an `in` parameter's reference is under a `modreq(InAttribute)`.
    ///
    /// C# writes the modifier where the caller cannot know which body it
    /// reaches — on a virtual or abstract member, an interface's, a
    /// delegate's `Invoke` — and an override or an explicit implementation
    /// copies whatever the member it answers has, so that the runtime sees
    /// the same signature on both. A member read from metadata has what its
    /// signature says.
    fn in_modifier(&self, parameter: SymbolId, depth: usize) -> bool {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(parameter);
        if symbol
            .as_parameter()
            .is_none_or(|detail| detail.ref_kind != RefKind::In)
        {
            return false;
        }
        if self.compilation.is_from_metadata(parameter) {
            return self.compilation.metadata_in_modifier(parameter);
        }
        let Some(owner) = symbol.container else {
            return false;
        };
        let owner_symbol = symbols.get(owner);
        let parameters = match (owner_symbol.as_method(), owner_symbol.as_property()) {
            (Some(detail), _) => &detail.parameters,
            (_, Some(detail)) => &detail.parameters,
            _ => return false,
        };
        let Some(position) = parameters.iter().position(|each| *each == parameter) else {
            return false;
        };
        if depth < 16
            && let Some(answered) = self.answered_member(owner)
        {
            let answered_symbol = symbols.get(answered);
            let answered_parameters =
                match (answered_symbol.as_method(), answered_symbol.as_property()) {
                    (Some(detail), _) => &detail.parameters,
                    (_, Some(detail)) => &detail.parameters,
                    _ => return false,
                };
            return answered_parameters
                .get(position)
                .is_some_and(|base| self.in_modifier(*base, depth + 1));
        }
        let container = owner_symbol
            .container
            .map(|container| symbols.get(container));
        let kind = container.and_then(|container| container.type_kind());
        let modifiers = owner_symbol.modifiers;
        kind == Some(TypeKind::Delegate)
            || modifiers.contains(Modifiers::VIRTUAL)
            || modifiers.contains(Modifiers::ABSTRACT)
            || (kind == Some(TypeKind::Interface)
                && !modifiers.contains(Modifiers::STATIC)
                && !modifiers.contains(Modifiers::SEALED)
                && owner_symbol.accessibility != rustlyn_semantics::Accessibility::Private)
    }

    /// The custom modifiers a signature position has to carry as metadata
    /// wrote them: a parameter's or a member's return, read from an assembly
    /// — or, for a member of this one, the ones of the member it overrides
    /// or implements, which Roslyn copies so that the runtime sees one
    /// signature on both sides.
    fn written_modifiers(
        &self,
        symbol: SymbolId,
        depth: usize,
    ) -> Option<Vec<rustlyn_semantics::SignatureModifier>> {
        if self.compilation.is_from_metadata(symbol) {
            return self
                .compilation
                .metadata_modifiers(symbol)
                .map(<[_]>::to_vec);
        }
        if depth >= 16 {
            return None;
        }
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        if found.kind == SymbolKind::Parameter {
            let owner = found.container?;
            let position = member_parameters(symbols, owner)?
                .iter()
                .position(|each| *each == symbol)?;
            let answered = self.answered_member(owner)?;
            let base = *member_parameters(symbols, answered)?.get(position)?;
            return self.written_modifiers(base, depth + 1);
        }
        let answered = self.answered_member(symbol)?;
        self.written_modifiers(answered, depth + 1)
    }

    /// Whether two members read from metadata carry the same custom
    /// modifiers throughout their signatures: the runtime matches an
    /// override by them, and one that differs only there is a new slot.
    fn same_modifiers(&self, first: SymbolId, second: SymbolId) -> bool {
        let compilation = self.compilation;
        if !compilation.is_from_metadata(first) || !compilation.is_from_metadata(second) {
            return true;
        }
        let symbols = compilation.symbols();
        let written = |symbol: SymbolId| compilation.metadata_modifiers(symbol).unwrap_or(&[]);
        written(first) == written(second)
            && match (
                member_parameters(symbols, first),
                member_parameters(symbols, second),
            ) {
                (Some(ours), Some(theirs)) => ours
                    .iter()
                    .zip(theirs)
                    .all(|(ours, theirs)| written(*ours) == written(*theirs)),
                _ => true,
            }
    }

    /// A type under the modifiers given, the first outermost.
    fn with_modifiers(
        &mut self,
        mut ty: SigType,
        modifiers: &[rustlyn_semantics::SignatureModifier],
    ) -> SigType {
        for modifier in modifiers.iter().rev() {
            let token = match &modifier.assembly {
                Some(home) => self
                    .references
                    .type_ref_in(&mut self.metadata, home, &modifier.name),
                None => self.references.type_ref(&mut self.metadata, &modifier.name),
            };
            let coded = type_def_or_ref(1, token.0 & 0x00FF_FFFF);
            ty = if modifier.required {
                SigType::Required {
                    modifier: coded,
                    inner: Box::new(ty),
                }
            } else {
                SigType::Optional {
                    modifier: coded,
                    inner: Box::new(ty),
                }
            };
        }
        ty
    }

    /// Whether two parameter lists differ in their `in` modifiers: one is
    /// under a `modreq(InAttribute)` where the other is not, or each names
    /// another assembly's `InAttribute`.
    fn in_modifiers_differ(&self, left: &[SymbolId], right: &[SymbolId]) -> bool {
        left.len() == right.len()
            && left.iter().zip(right).any(|(left, right)| {
                let (on_left, on_right) = (self.in_modifier(*left, 0), self.in_modifier(*right, 0));
                on_left != on_right
                    || (on_left && self.in_attribute_type(*left) != self.in_attribute_type(*right))
            })
    }

    /// Whether two members return `ref readonly` under different
    /// `InAttribute`s.
    fn return_modifier_differs(&self, left: SymbolId, right: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let readonly = |member: SymbolId| {
            let symbol = symbols.get(member);
            symbol
                .as_method()
                .is_some_and(|detail| detail.returns_readonly)
                || symbol
                    .as_property()
                    .is_some_and(|detail| detail.returns_readonly)
        };
        readonly(left)
            && readonly(right)
            && self.in_attribute_type(left) != self.in_attribute_type(right)
    }

    /// Whether a method that implements an interface member implicitly is
    /// answered through a forwarding method (see [`MethodSource::Forwarding`]):
    /// it is then a method of its own and not the slot, as Roslyn writes it.
    fn needs_forwarder(&self, method: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let Some(class) = symbols.get(method).container else {
            return false;
        };
        let Some(found) = symbols.get(method).as_method() else {
            return false;
        };
        if !found.type_parameters.is_empty() {
            return false;
        }
        let name = symbols.get(method).name.clone();
        let explicit = format!(".{name}");
        if symbols
            .get(class)
            .members
            .iter()
            .any(|other| symbols.get(*other).name.ends_with(&explicit))
        {
            return false;
        }
        self.implemented_interfaces(class)
            .iter()
            .filter_map(Type::symbol)
            .any(|interface| {
                symbols.get(interface).members.iter().any(|member| {
                    let symbol = symbols.get(*member);
                    symbol.kind == SymbolKind::Method
                        && symbol.name == name
                        && !symbol.modifiers.contains(Modifiers::STATIC)
                        && self.same_signature(method, *member)
                        && symbol.as_method().is_some_and(|wanted| {
                            self.in_modifiers_differ(&wanted.parameters, &found.parameters)
                                || self.return_modifier_differs(*member, method)
                        })
                })
            })
    }

    /// The methods that answer an interface member for the member of this
    /// type that implements it implicitly, where the two signatures differ
    /// in their `in` modifiers (see [`MethodSource::Forwarding`]).
    fn plan_forwarders(
        &mut self,
        class: SymbolId,
        class_token: Token,
        next_method: &mut u32,
    ) -> Vec<MethodPlan> {
        let symbols = self.compilation.symbols();
        // A generic class calls its own method through the construction the
        // body names (`R<!0>::Search`), which the forwarder of a method
        // knows how to write; an accessor's is not written yet.
        let generic = symbols
            .get(class)
            .as_named_type()
            .is_some_and(|detail| !detail.type_parameters.is_empty());
        // Every interface the class implements, those its interfaces extend
        // among them, each once and constructed as the class sees it:
        // `IIdx<!0>` under `R<T> : IDb<T>`, not `IDb`'s own `IIdx<T>`.
        let interfaces = self.implemented_interfaces(class);
        let differs = |this: &Self, left: &[SymbolId], right: &[SymbolId]| {
            this.in_modifiers_differ(left, right)
        };
        let return_differs = |this: &Self, left: SymbolId, right: SymbolId| {
            this.return_modifier_differs(left, right)
        };
        let mut plans = Vec::new();
        for interface in interfaces {
            let Some(declared) = interface.symbol() else {
                continue;
            };
            let prefix = symbols.get(declared).name.clone();
            for member in symbols.get(declared).members.clone() {
                let symbol = symbols.get(member);
                if symbol.modifiers.contains(Modifiers::STATIC) {
                    continue;
                }
                // Written explicitly, the member is answered already.
                let explicit = format!(".{}", symbol.name);
                if symbols
                    .get(class)
                    .members
                    .iter()
                    .any(|other| symbols.get(*other).name.ends_with(&explicit))
                {
                    continue;
                }
                let Some(implementation) = symbols
                    .lookup(class, &symbol.name)
                    .iter()
                    .copied()
                    .find(|candidate| {
                        symbols.get(*candidate).kind == symbol.kind
                            && !symbols
                                .get(*candidate)
                                .modifiers
                                .contains(Modifiers::STATIC)
                            && self.same_signature(*candidate, member)
                    })
                else {
                    continue;
                };
                match symbol.kind {
                    SymbolKind::Method => {
                        let (Some(wanted), Some(found)) =
                            (symbol.as_method(), symbols.get(implementation).as_method())
                        else {
                            continue;
                        };
                        if !found.type_parameters.is_empty()
                            || !(differs(self, &wanted.parameters, &found.parameters)
                                || return_differs(self, member, implementation))
                        {
                            continue;
                        }
                        let Some(target) = self.methods.get(&implementation).copied() else {
                            continue;
                        };
                        let parameters = wanted
                            .parameters
                            .iter()
                            .zip(&found.parameters)
                            .map(|(wanted, found)| ParameterPlan {
                                symbol: Some(*wanted),
                                name: symbols.get(*found).name.clone(),
                                ty: self.type_of(*found),
                                by_ref: false,
                            })
                            .collect();
                        let token = Token::new(table::METHOD_DEF, *next_method);
                        *next_method += 1;
                        plans.push(MethodPlan {
                            source: MethodSource::Forwarding {
                                target,
                                member,
                                implementation: generic.then_some(implementation),
                            },
                            token,
                            name: format!("{prefix}.{}", symbol.name),
                            flags: method_attributes::PRIVATE
                                | method_attributes::FINAL
                                | method_attributes::VIRTUAL
                                | method_attributes::NEW_SLOT
                                | method_attributes::HIDE_BY_SIG,
                            instance: true,
                            return_type: self.type_of(implementation),
                            parameters,
                            type_parameters: Vec::new(),
                            impl_flags: 0,
                            signature: None,
                        });
                        self.explicit_impls.push(ExplicitImpl {
                            class: class_token,
                            body: token,
                            declaration: Declaration::Method {
                                member,
                                interface: interface.clone(),
                            },
                        });
                    }
                    SymbolKind::Property if !generic => {
                        let (Some(wanted), Some(found)) = (
                            symbol.as_property(),
                            symbols.get(implementation).as_property(),
                        ) else {
                            continue;
                        };
                        if !differs(self, &wanted.parameters, &found.parameters)
                            && !return_differs(self, member, implementation)
                        {
                            continue;
                        }
                        let ty = self.type_of(implementation);
                        let name = if wanted.is_indexer {
                            "Item".to_string()
                        } else {
                            symbol.name.clone()
                        };
                        for (setter, present, accessors) in [
                            (false, wanted.has_get, &self.getters),
                            (true, wanted.has_set || wanted.has_init, &self.setters),
                        ] {
                            let Some(target) = accessors.get(&implementation).copied() else {
                                continue;
                            };
                            if !present {
                                continue;
                            }
                            let mut parameters: Vec<ParameterPlan> = wanted
                                .parameters
                                .iter()
                                .zip(&found.parameters)
                                .map(|(wanted, found)| ParameterPlan {
                                    symbol: Some(*wanted),
                                    name: symbols.get(*found).name.clone(),
                                    ty: self.type_of(*found),
                                    by_ref: false,
                                })
                                .collect();
                            if setter {
                                parameters.push(ParameterPlan {
                                    symbol: None,
                                    name: "value".to_string(),
                                    ty: ty.clone(),
                                    by_ref: false,
                                });
                            }
                            let token = Token::new(table::METHOD_DEF, *next_method);
                            *next_method += 1;
                            plans.push(MethodPlan {
                                source: MethodSource::Forwarding {
                                    target,
                                    member,
                                    implementation: None,
                                },
                                token,
                                name: format!(
                                    "{prefix}.{}_{name}",
                                    if setter { "set" } else { "get" }
                                ),
                                flags: method_attributes::PRIVATE
                                    | method_attributes::FINAL
                                    | method_attributes::VIRTUAL
                                    | method_attributes::NEW_SLOT
                                    | method_attributes::HIDE_BY_SIG,
                                instance: true,
                                return_type: if setter { Type::Void } else { ty.clone() },
                                parameters,
                                type_parameters: Vec::new(),
                                impl_flags: 0,
                                signature: None,
                            });
                            self.explicit_impls.push(ExplicitImpl {
                                class: class_token,
                                body: token,
                                declaration: Declaration::Accessor {
                                    property: member,
                                    interface: interface.clone(),
                                    setter,
                                },
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
        plans
    }

    /// The methods that implement an interface member a class lists by
    /// calling the member of a base class C# picks for it, where the runtime
    /// would pick another (Roslyn's `SynthesizeInterfaceMemberImplementation`).
    ///
    /// `class Derived3 : Derived, Interface` with `Derived : Base` and `Base :
    /// Interface` implementing `Method` explicitly: C# looks for `Method` in
    /// `Derived3`, then in `Derived`, and takes `Derived.Method`. The runtime
    /// looks for an implementation in a class that lists the interface, and
    /// in the classes above one only up to the first that lists it too:
    /// `Derived` does not, and its base does, so `Derived3` would keep
    /// `Base`'s mapping. Roslyn writes `Interface.Method` on `Derived3`,
    /// private and final, calling `Derived.Method`, and ties it to the
    /// interface's with a `MethodImpl` row. A base class that lists the
    /// interface itself, or none of whose bases does, is one the runtime
    /// finds on its own, its method made virtual for it — where the method
    /// is this assembly's to make so: `class C : LibBase, IFoo` over a
    /// referenced `LibBase` whose `Foo` is not virtual gets `IFoo.Foo` too.
    fn plan_inherited_forwarders(
        &mut self,
        class: SymbolId,
        class_token: Token,
        next_method: &mut u32,
    ) -> Vec<MethodPlan> {
        let symbols = self.compilation.symbols();
        let generic = |symbol: SymbolId| {
            symbols
                .get(symbol)
                .as_named_type()
                .is_some_and(|detail| !detail.type_parameters.is_empty())
        };
        // The names the class answers under itself, an explicit
        // implementation's without the interface in front.
        let own: std::collections::HashSet<(SymbolKind, &str)> = symbols
            .get(class)
            .members
            .iter()
            .map(|member| {
                let found = symbols.get(*member);
                (
                    found.kind,
                    found.name.rsplit('.').next().unwrap_or(&found.name),
                )
            })
            .collect();
        let mut plans = Vec::new();
        for interface in self.implemented_interfaces(class) {
            let Some(declared) = interface.symbol() else {
                continue;
            };
            let prefix = self.explicit_prefix(&interface);
            for member in symbols.get(declared).members.clone() {
                let symbol = symbols.get(member);
                let method = symbol.as_method().is_some_and(|detail| {
                    detail.method_kind == rustlyn_semantics::MethodKind::Ordinary
                        && detail.type_parameters.is_empty()
                });
                if !(method || symbol.kind == SymbolKind::Property)
                    || !self.is_interface_slot(member)
                {
                    continue;
                }
                let own_type = self.binder.self_type(class);
                // What the class writes itself answers first, and the
                // runtime finds that without help — unless its signature
                // carries custom modifiers the interface's does not, which
                // the runtime compares too: `override T vMeth(T)` over a
                // base's `modopt(IsConst)` answers `I<T>.vMeth` only through
                // a method written for it (Roslyn's forwarding method).
                let (implementation, through) =
                    if own.contains(&(symbol.kind, symbol.name.as_str())) {
                        let written = (symbol.kind == SymbolKind::Method)
                            .then(|| {
                                symbols.lookup(class, &symbol.name).iter().copied().find(
                                    |candidate| {
                                        symbols.get(*candidate).kind == SymbolKind::Method
                                            && self.same_signature(*candidate, member)
                                    },
                                )
                            })
                            .flatten();
                        match written {
                            Some(written)
                                if self.carries_modifiers(written)
                                    && !self.carries_modifiers(member) =>
                            {
                                (written, generic(class).then(|| own_type.clone()))
                            }
                            _ => continue,
                        }
                    } else {
                        // The member C# finds, class by class up the chain: a
                        // public one of the same name and signature. A class
                        // that lists the interface itself answers for it as C#
                        // would, explicit implementations and all — which a
                        // referenced class keeps private, out of sight — and the
                        // runtime hands its mapping down: past it there is
                        // nothing to write.
                        let mut current = self.base_class(class);
                        let mut answer = None;
                        let mut through = None;
                        while let Some(at) = current {
                            if self.implemented_interfaces(at).contains(&interface) {
                                break;
                            }
                            // A generic base is reached as the class constructs
                            // it: `Base<T>.Meth` answers `I<T>.Meth` under
                            // `SubSubT<T>`.
                            let constructed = generic(at)
                                .then(|| self.binder.constructed_from(&own_type, at))
                                .flatten();
                            through = constructed.clone();
                            answer = symbols.lookup(at, &symbol.name).iter().copied().find(
                                |candidate| {
                                    let found = symbols.get(*candidate);
                                    found.kind == symbol.kind
                                        && self.accessibility_of(*candidate)
                                            == rustlyn_semantics::Accessibility::Public
                                        && !found.modifiers.contains(Modifiers::STATIC)
                                        && found
                                            .as_method()
                                            .is_none_or(|detail| detail.type_parameters.is_empty())
                                        && self.same_signature(*candidate, member)
                                        && self.answers_exactly_through(
                                            *candidate,
                                            constructed.as_ref(),
                                            member,
                                            &interface,
                                        )
                                },
                            );
                            if answer.is_some() {
                                break;
                            }
                            current = self.base_class(at);
                        }
                        let (Some(implementation), Some(owner)) = (answer, current) else {
                            continue;
                        };
                        // Where the runtime looks anyway — for an override,
                        // where it looks for the method overridden — the method
                        // only has to be virtual: this assembly's is made so for
                        // the class that lists the interface, and a referenced
                        // one has to be so already.
                        let mut looked_at = Some((implementation, owner));
                        let mut found_anyway = false;
                        while let Some((method, owner)) = looked_at {
                            let lists = self.implemented_interfaces(owner).contains(&interface);
                            let above = self.base_class(owner).is_some_and(|base| {
                                self.inherited_interfaces(base).contains(&interface)
                            });
                            if lists || !above {
                                found_anyway = !self.compilation.is_from_metadata(implementation)
                                    || self.virtual_in_metadata(implementation);
                                break;
                            }
                            looked_at = self
                                .overridden_member(method)
                                .and_then(|base| Some((base, symbols.get(base).container?)));
                        }
                        if found_anyway {
                            continue;
                        }
                        (implementation, through)
                    };
                let parameters_of = |member: SymbolId| -> Vec<SymbolId> {
                    let symbol = symbols.get(member);
                    symbol
                        .as_method()
                        .map(|detail| detail.parameters.clone())
                        .or_else(|| symbol.as_property().map(|detail| detail.parameters.clone()))
                        .unwrap_or_default()
                };
                let (wanted, found) = (parameters_of(member), parameters_of(implementation));
                let seen = |member: SymbolId| match &through {
                    Some(base) => self.member_type(member, base),
                    None => self.type_of(member),
                };
                let parameters: Vec<ParameterPlan> = wanted
                    .iter()
                    .zip(&found)
                    .map(|(wanted, found)| ParameterPlan {
                        symbol: Some(*wanted),
                        name: symbols.get(*found).name.clone(),
                        ty: seen(*found),
                        by_ref: false,
                    })
                    .collect();
                let ty = seen(implementation);
                let flags = method_attributes::PRIVATE
                    | method_attributes::FINAL
                    | method_attributes::VIRTUAL
                    | method_attributes::NEW_SLOT
                    | method_attributes::HIDE_BY_SIG;
                let accessors: Vec<(Option<bool>, String)> = match symbol.as_property() {
                    None => vec![(None, format!("{prefix}.{}", symbol.name))],
                    Some(property) => {
                        let name = if property.is_indexer {
                            "Item".to_string()
                        } else {
                            symbol.name.clone()
                        };
                        [
                            (false, property.has_get),
                            (true, property.has_set || property.has_init),
                        ]
                        .into_iter()
                        .filter(|(_, present)| *present)
                        .map(|(setter, _)| {
                            let verb = if setter { "set" } else { "get" };
                            (Some(setter), format!("{prefix}.{verb}_{name}"))
                        })
                        .collect()
                    }
                };
                for (setter, name) in accessors {
                    let token = Token::new(table::METHOD_DEF, *next_method);
                    *next_method += 1;
                    let mut parameters = parameters.clone();
                    if setter == Some(true) {
                        parameters.push(ParameterPlan {
                            symbol: None,
                            name: "value".to_string(),
                            ty: ty.clone(),
                            by_ref: false,
                        });
                    }
                    plans.push(MethodPlan {
                        source: MethodSource::InheritedForwarding {
                            implementation,
                            setter,
                            member,
                            through: through.clone(),
                        },
                        token,
                        name,
                        flags,
                        instance: true,
                        return_type: if setter == Some(true) {
                            Type::Void
                        } else {
                            ty.clone()
                        },
                        parameters,
                        type_parameters: Vec::new(),
                        impl_flags: 0,
                        signature: None,
                    });
                    self.explicit_impls.push(ExplicitImpl {
                        class: class_token,
                        body: token,
                        declaration: match setter {
                            None => Declaration::Method {
                                member,
                                interface: interface.clone(),
                            },
                            Some(setter) => Declaration::Accessor {
                                property: member,
                                interface: interface.clone(),
                                setter,
                            },
                        },
                    });
                }
            }
        }
        plans
    }

    /// Whether a method's signature carries custom modifiers: its own, read
    /// from metadata, or — for an override — the ones it repeats from the
    /// metadata method it overrides.
    fn carries_modifiers(&self, method: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let mut current = Some(method);
        let mut depth = 0;
        while let Some(at) = current {
            if self.compilation.is_from_metadata(at) {
                let modified = |symbol: SymbolId| {
                    self.compilation
                        .metadata_modifiers(symbol)
                        .is_some_and(|modifiers| !modifiers.is_empty())
                };
                return modified(at)
                    || symbols
                        .get(at)
                        .as_method()
                        .is_some_and(|detail| detail.parameters.iter().any(|p| modified(*p)));
            }
            depth += 1;
            if depth > 16 {
                return false;
            }
            current = self.overridden_member(at);
        }
        false
    }

    /// Whether a class up the chain from a record seals `ToString`.
    fn base_seals_to_string(&self, record: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let mut current = self.base_class(record);
        let mut depth = 0;
        while let Some(at) = current {
            if let Some(found) = symbols
                .lookup(at, "ToString")
                .iter()
                .copied()
                .find(|member| {
                    symbols
                        .get(*member)
                        .as_method()
                        .is_some_and(|detail| detail.parameters.is_empty())
                })
            {
                return symbols.get(found).modifiers.contains(Modifiers::SEALED);
            }
            depth += 1;
            if depth > 32 {
                return false;
            }
            current = self.base_class(at);
        }
        false
    }

    /// How widely a member can be seen, a property or an event read from
    /// metadata by its accessors, which is where metadata says it.
    fn accessibility_of(&self, member: SymbolId) -> rustlyn_semantics::Accessibility {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        if symbol.accessibility != rustlyn_semantics::Accessibility::NotApplicable {
            return symbol.accessibility;
        }
        self.accessors_of_member(member)
            .into_iter()
            .map(|accessor| symbols.get(accessor).accessibility)
            .max()
            .unwrap_or(symbol.accessibility)
    }

    /// Whether a member read from metadata takes a virtual slot: a
    /// property or an event by its accessors.
    fn virtual_in_metadata(&self, member: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let is_virtual = |member: SymbolId| {
            let modifiers = symbols.get(member).modifiers;
            modifiers.contains(Modifiers::VIRTUAL)
                || modifiers.contains(Modifiers::ABSTRACT)
                || modifiers.contains(Modifiers::OVERRIDE)
        };
        match symbols.get(member).kind {
            SymbolKind::Method => is_virtual(member),
            _ => {
                let accessors = self.accessors_of_member(member);
                !accessors.is_empty() && accessors.into_iter().all(is_virtual)
            }
        }
    }

    /// The accessor methods of a property or an event, where it has
    /// symbols for them.
    fn accessors_of_member(&self, member: SymbolId) -> Vec<SymbolId> {
        let symbol = self.compilation.symbols().get(member);
        match (symbol.as_property(), symbol.as_event()) {
            (Some(property), _) => [property.getter, property.setter]
                .into_iter()
                .flatten()
                .collect(),
            (_, Some(event)) => [event.adder, event.remover].into_iter().flatten().collect(),
            _ => Vec::new(),
        }
    }

    /// The member an override or an explicit interface implementation
    /// answers, whose signature it has to repeat.
    fn answered_member(&self, member: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        if symbols.get(member).modifiers.contains(Modifiers::OVERRIDE) {
            return self.overridden_member(member);
        }
        let interface = self.explicit_interface(member)?;
        self.interface_member(member, &interface)
    }

    /// A return type as a reference to the method has to spell it.
    ///
    /// `ref readonly T` is `T&` under a `modreq` naming `InAttribute`: the
    /// modifier is part of what the runtime matches on, so a reference that
    /// leaves it out names a method that does not exist.
    fn returned_sig(&mut self, member: SymbolId, returns: SigType) -> SigType {
        if let Some(modifiers) = self.written_modifiers(member, 0) {
            return self.with_modifiers(returns, &modifiers);
        }
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let readonly = symbol
            .as_method()
            .is_some_and(|detail| detail.returns_readonly)
            || symbol
                .as_property()
                .is_some_and(|detail| detail.returns_readonly);
        if !readonly {
            return returns;
        }
        let modifier = self.in_attribute_coded(member);
        SigType::Required {
            modifier,
            inner: Box::new(returns),
        }
    }

    /// One of the members the runtime supplies for `int[,]`.
    ///
    /// An array of more than one dimension has no `ldelem` of its own: §I.8.9.1
    /// says the runtime gives every such type a `.ctor`, a `Get`, a `Set` and
    /// an `Address`, and a `TypeSpec` holding the array's signature is what
    /// they hang off. `which` is which of those; the rank says how many
    /// indices it takes.
    pub(crate) fn array_member(
        &mut self,
        array: &Type,
        which: ArrayMember,
        rank: usize,
        element: &Type,
    ) -> Result<Token, EmitError> {
        let element = self.sig_type(element)?;
        let index = SigType::Primitive(ElementType::I4);
        let mut parameters = vec![index; rank];
        let (name, returns) = match which {
            ArrayMember::Constructor => (".ctor", SigType::Primitive(ElementType::Void)),
            ArrayMember::Get => ("Get", element),
            ArrayMember::Set => {
                parameters.push(element);
                ("Set", SigType::Primitive(ElementType::Void))
            }
            ArrayMember::Address => ("Address", SigType::ByRef(Box::new(element))),
        };
        let signature = method_signature(true, &returns, &parameters);
        let spec = self.type_token(array)?;
        Ok(self
            .references
            .member_of_spec(&mut self.metadata, spec, name, &signature))
    }

    /// `NotImplementedException()`, which every stubbed body throws.
    pub(crate) fn not_implemented(&mut self) -> Token {
        let signature = method_signature(
            true,
            &SigType::Primitive(ElementType::Void),
            &[SigType::Primitive(ElementType::String)],
        );
        self.references.member_ref(
            &mut self.metadata,
            "System.NotImplementedException",
            ".ctor",
            &signature,
        )
    }

    /// Wraps a finished instruction stream in a method body.
    pub(crate) fn finish_body(
        &mut self,
        mut stream: InstructionStream,
        locals: &[SigType],
    ) -> Vec<u8> {
        // A method may not end on an instruction that falls through, even
        // one nothing reaches: dead code after the last `return` still gets
        // a `ret` to land on, which the JIT never imports.
        if !stream.ends_flow() || stream.last_falls_through() {
            stream.emit(Instruction::Ret);
        }
        let (code, max_stack, regions) = stream.finish();
        let signature = (!locals.is_empty())
            .then(|| self.metadata.add_stand_alone_sig(&local_signature(locals)));
        method_body(&code, max_stack, signature, &regions)
    }

    /// A copy of the bound body of a member's declaration, if it has one,
    /// for a caller that changes it. Copying a body costs about what binding
    /// it did: a caller that only reads it wants [`Self::body_of`].
    ///
    /// Cached, and not only for speed: planning a method's lambdas and then
    /// emitting them has to see the same tree, and binding twice would give
    /// two trees with two sets of indices. The plan binds every body of the
    /// compilation up front, on every core ([`Self::plan`]), so this is where
    /// they are kept until emitted.
    pub(crate) fn bound_body(&mut self, symbol: SymbolId) -> Option<BoundBody> {
        self.body_of(symbol).map(|body| BoundBody::clone(&body))
    }

    /// The bound body of a member's declaration, shared rather than copied:
    /// for a caller that only reads it, which is most of them.
    pub(crate) fn body_of(&mut self, symbol: SymbolId) -> Option<std::sync::Arc<BoundBody>> {
        if let Some(body) = self.bodies.get(&symbol) {
            return body.clone();
        }
        if let Some(ahead) = &self.ahead
            && let Some(&index) = ahead.index.get(&symbol)
            && let Some(bound) = ahead.slots[index].wait()
        {
            let bound = bound.clone();
            self.bodies.insert(symbol, bound.clone());
            return bound;
        }
        let bound = self
            .bind_body(symbol)
            .map(|body| std::sync::Arc::new(self.spilled(body)));
        self.bodies.insert(symbol, bound.clone());
        bound
    }

    /// A body with every loop inside an expression moved out ahead of the
    /// statement that holds it, where it has any. One that cannot be moved
    /// is left for the backend to emit in place, or refuse.
    pub(crate) fn spilled(&self, body: BoundBody) -> BoundBody {
        spilled_with(self.compilation, body)
    }

    /// Every member of these types that has a body of its own for the plan
    /// and the bodies to ask for: the members, and the accessors of their
    /// properties and events.
    fn owners_of_bodies(&self, types: &[SymbolId]) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let mut owners = Vec::new();
        for &ty in types {
            // An enum's members are constants and a delegate's are the
            // runtime's: neither has a body to bind.
            if matches!(
                symbols.get(ty).type_kind(),
                Some(TypeKind::Enum | TypeKind::Delegate) | None
            ) {
                continue;
            }
            for &member in &symbols.get(ty).members {
                let detail = symbols.get(member);
                match detail.kind {
                    SymbolKind::Field | SymbolKind::Method => owners.push(member),
                    SymbolKind::Property => {
                        owners.push(member);
                        owners.extend(self.accessors_of(member));
                    }
                    SymbolKind::Event => {
                        // An event with `add` and `remove` blocks is bound
                        // accessor by accessor; one written as a field is
                        // bound for its initializer.
                        if self.is_field_like_event(member) {
                            owners.push(member);
                        }
                        if let Some(event) = detail.as_event() {
                            owners.extend(event.adder.into_iter().chain(event.remover));
                        }
                    }
                    _ => {}
                }
            }
        }
        owners
    }

    /// Waits for every body being bound ahead, and keeps them all.
    ///
    /// Bodies are independent of one another once the declarations are
    /// done: what one binding learns and keeps — a base type, a constant, a
    /// conversion — is a property of the compilation that every other
    /// binding would have learned the same, so the order they are bound in
    /// does not show in what comes out.
    fn finish_binding(&mut self) {
        let Some(ahead) = self.ahead.take() else {
            return;
        };
        let mut owners: Vec<(SymbolId, usize)> = ahead.index.into_iter().collect();
        owners.sort_unstable_by_key(|(_, index)| *index);
        for (owner, index) in owners {
            if self.bodies.contains_key(&owner) {
                continue;
            }
            let bound = match ahead.slots[index].wait() {
                Some(bound) => bound.clone(),
                None => self
                    .bind_body(owner)
                    .map(|body| std::sync::Arc::new(self.spilled(body))),
            };
            self.bodies.insert(owner, bound);
        }
    }

    /// The `: base(...)` a type's default constructor needs, where the base
    /// takes only arguments it fills itself.
    pub(crate) fn implicit_base_initializer(&self, symbol: SymbolId) -> Option<BoundStatement> {
        let (tree, span) = *self.compilation.declaration_nodes(symbol).first()?;
        let node = self.compilation.trees().get(tree)?.root().find_node(span)?;
        rustlyn_semantics::BodyBinder::implicit_base_initializer(&self.binder, tree, &node)
    }

    fn bind_body(&self, symbol: SymbolId) -> Option<BoundBody> {
        bind_body_with(self.compilation, &self.binder, symbol)
    }
}

/// A bound body as the backend keeps it: without what only an editor asks a
/// body — what each name refers to, which symbol each token settled on, the
/// diagnostics — and with the type of an expression kept only for the
/// lambdas, which is all emitting reads. Every body of a compilation is held
/// until it is emitted, and those tables are most of one.
fn slimmed(mut body: BoundBody) -> BoundBody {
    body.references = std::collections::HashMap::new();
    body.symbols = std::collections::HashMap::new();
    body.diagnostics = rustlyn_semantics::Diagnostics::new();
    let spans: std::collections::HashSet<TextSpan> =
        body.lambdas.iter().map(|lambda| lambda.span).collect();
    body.types.retain(|span, _| spans.contains(span));
    body.types.shrink_to_fit();
    body
}

/// [`Emitter::spilled`], for a thread that has only the compilation.
fn spilled_with(compilation: &Compilation, body: BoundBody) -> BoundBody {
    if !crate::async_machine::body_has_spill_sequences(&body) {
        return body;
    }
    let special = |which| {
        compilation
            .special_type(which)
            .map_or(Type::Error, Type::named)
    };
    let boolean = special(rustlyn_semantics::SpecialType::Boolean);
    let integer = special(rustlyn_semantics::SpecialType::Int32);
    crate::async_machine::spill_sequences(body.clone(), boolean, integer, compilation.symbols())
        .unwrap_or(body)
}

/// The bound body of a member's declaration, if it has one.
fn bind_body_with(
    compilation: &Compilation,
    binder: &Binder<'_>,
    symbol: SymbolId,
) -> Option<BoundBody> {
    let (tree, span) = *compilation.declaration_nodes(symbol).first()?;
    let node = compilation.trees().get(tree)?.root().find_node(span)?;
    Some(rustlyn_semantics::BodyBinder::bind_member(
        binder, tree, &node,
    ))
}

/// One body being bound ahead: `None` inside where its binding panicked.
type BodySlot = std::sync::OnceLock<Option<Option<std::sync::Arc<BoundBody>>>>;

/// The bodies being bound on other threads, by the member each is for.
#[derive(Debug)]
struct Ahead {
    index: HashMap<SymbolId, usize>,
    slots: std::sync::Arc<[BodySlot]>,
}

/// The name a type's indexer accessors are built from.
///
/// `DefaultMember` is an attribute on the type, and the core library here does
/// not carry attributes, so the one type whose answer is not `Item` is named
/// outright. Getting this wrong is a `MissingMethodException` at run time
/// rather than anything the writer would notice.
/// A `decimal` as its constructor and `[DecimalConstant]` take it apart: a
/// 96-bit whole number, a sign and how many of its digits are decimals.
#[derive(Clone, Copy)]
pub(crate) struct DecimalParts {
    lo: u32,
    mid: u32,
    hi: u32,
    negative: bool,
    scale: u8,
}

/// `void .ctor(object, native int)`, the constructor every delegate has and no
/// source writes.
pub(crate) fn delegate_constructor_signature() -> Vec<u8> {
    method_signature(
        true,
        &SigType::Primitive(ElementType::Void),
        &[
            SigType::Primitive(ElementType::Object),
            SigType::Primitive(ElementType::I),
        ],
    )
}

fn default_member_name(qualified_type: &str) -> &'static str {
    match qualified_type {
        "System.String" => "Chars",
        _ => "Item",
    }
}

fn namespace_of(compilation: &Compilation, symbol: SymbolId) -> String {
    let symbols = compilation.symbols();
    let mut parts = Vec::new();
    let mut current = symbols.get(symbol).container;
    while let Some(container) = current {
        let parent = symbols.get(container);
        if parent.kind != SymbolKind::Namespace || parent.name.is_empty() {
            break;
        }
        parts.push(parent.name.clone());
        current = parent.container;
    }
    parts.reverse();
    parts.join(".")
}

/// How a nested type's accessibility is spelled in `TypeAttributes`.
fn nested_visibility(accessibility: rustlyn_semantics::Accessibility) -> u32 {
    use rustlyn_semantics::Accessibility as A;
    match accessibility {
        A::Public => type_attributes::NESTED_PUBLIC,
        A::Protected => type_attributes::NESTED_FAMILY,
        A::ProtectedOrInternal => type_attributes::NESTED_FAM_OR_ASSEM,
        A::ProtectedAndInternal => type_attributes::NESTED_FAM_AND_ASSEM,
        A::Internal => type_attributes::NESTED_ASSEMBLY,
        // A member of a type is private unless it says otherwise, and a nested
        // type is a member.
        _ => type_attributes::NESTED_PRIVATE,
    }
}

/// Accessor flags with the visibility an accessor narrowed itself to, where
/// the source wrote one and the accessor is free to have its own.
fn narrowed(
    flags: u16,
    accessibility: Option<rustlyn_semantics::Accessibility>,
    fixed: bool,
) -> u16 {
    use rustlyn_semantics::Accessibility as A;
    let Some(accessibility) = accessibility else {
        return flags;
    };
    if fixed {
        return flags;
    }
    let visibility = match accessibility {
        A::Public => method_attributes::PUBLIC,
        A::Protected => method_attributes::FAMILY,
        A::ProtectedOrInternal => method_attributes::FAM_OR_ASSEM,
        A::ProtectedAndInternal => method_attributes::FAM_AND_ASSEM,
        A::Internal => method_attributes::ASSEMBLY,
        _ => method_attributes::PRIVATE,
    };
    (flags & !0x0007) | visibility
}

fn field_flags(accessibility: rustlyn_semantics::Accessibility, is_static: bool) -> u16 {
    use rustlyn_semantics::Accessibility as A;
    let visibility = match accessibility {
        A::Public => field_attributes::PUBLIC,
        A::Protected => field_attributes::FAMILY,
        A::ProtectedOrInternal => field_attributes::FAM_OR_ASSEM,
        A::ProtectedAndInternal => field_attributes::FAM_AND_ASSEM,
        A::Internal => field_attributes::ASSEMBLY,
        _ => field_attributes::PRIVATE,
    };
    visibility
        | if is_static {
            field_attributes::STATIC
        } else {
            0
        }
}

/// What a member that implements an interface member needs beyond what it
/// asked for.
///
/// It has to be virtual, or the interface's call reaches nothing. A member the
/// source left plain also gets a slot of its own and is sealed into it, so
/// that nothing can override it out from under the interface. A member the
/// source already made `virtual`, `abstract` or `override` is meant to be
/// overridden, and already has the slot it should have: sealing that one is
/// what the runtime rejects the moment a derived type overrides it.
fn implementing_flags(modifiers: Modifiers) -> u16 {
    let overridable = modifiers.contains(Modifiers::VIRTUAL)
        || modifiers.contains(Modifiers::ABSTRACT)
        || modifiers.contains(Modifiers::OVERRIDE);
    method_attributes::VIRTUAL
        | method_attributes::HIDE_BY_SIG
        | if overridable {
            0
        } else {
            method_attributes::NEW_SLOT | method_attributes::FINAL
        }
}

/// What each type parameter in `pattern` stands for, read off `actual`:
/// `List<T>` against `List<int>` says `T` is `int`.
fn unify(pattern: &Type, actual: &Type, out: &mut HashMap<SymbolId, Type>) {
    match (pattern, actual) {
        (Type::TypeParameter(parameter), _) => {
            out.entry(*parameter).or_insert_with(|| actual.clone());
        }
        (
            Type::Named {
                type_arguments: left,
                ..
            },
            Type::Named {
                type_arguments: right,
                ..
            },
        ) => {
            for (left, right) in left.iter().zip(right) {
                unify(left, right, out);
            }
        }
        (Type::Array { element: left, .. }, Type::Array { element: right, .. })
        | (Type::ByRef(left), Type::ByRef(right))
        | (Type::Pointer(left), Type::Pointer(right)) => unify(left, right, out),
        (_, Type::ByRef(right)) => unify(pattern, right, out),
        _ => {}
    }
}

/// Whether an override returns what the method it overrides does, as far as
/// the runtime can tell: `dynamic` is `object`, and a tuple is its elements
/// whatever they are called.
fn same_return(left: &Type, right: &Type) -> bool {
    match (left, right) {
        (Type::Dynamic, Type::Named { type_arguments, .. })
        | (Type::Named { type_arguments, .. }, Type::Dynamic) => type_arguments.is_empty(),
        (
            Type::Named {
                symbol: left,
                type_arguments: left_arguments,
            },
            Type::Named {
                symbol: right,
                type_arguments: right_arguments,
            },
        ) => {
            left == right
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| same_return(left, right))
        }
        (Type::Tuple(left), Type::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| same_return(&left.ty, &right.ty))
        }
        (
            Type::Array {
                element: left,
                rank: left_rank,
            },
            Type::Array {
                element: right,
                rank: right_rank,
            },
        ) => left_rank == right_rank && same_return(left, right),
        (Type::ByRef(left), Type::ByRef(right)) | (Type::Pointer(left), Type::Pointer(right)) => {
            same_return(left, right)
        }
        (left, right) => left == right,
    }
}

/// Whether two types could be the same type once a construction is put
/// through.
///
/// A type parameter stands for whatever the construction put there, so it
/// matches anything; everything else has to agree on what it is made of.
fn same_shape(left: &Type, right: &Type) -> bool {
    match (left, right) {
        (Type::TypeParameter(_), _) | (_, Type::TypeParameter(_)) => true,
        // `dynamic` is `object` in a signature: an override may say either.
        (Type::Dynamic, Type::Named { type_arguments, .. })
        | (Type::Named { type_arguments, .. }, Type::Dynamic) => type_arguments.is_empty(),
        (Type::Named { symbol: left, .. }, Type::Named { symbol: right, .. }) => left == right,
        (
            Type::Array {
                element: left,
                rank: left_rank,
            },
            Type::Array {
                element: right,
                rank: right_rank,
            },
        ) => left_rank == right_rank && same_shape(left, right),
        (Type::ByRef(left), Type::ByRef(right)) | (Type::Pointer(left), Type::Pointer(right)) => {
            same_shape(left, right)
        }
        (left, right) => left == right,
    }
}

/// Checks that a row landed where planning said it would.
///
/// Every token in every body was worked out before a single row existed, from
/// the order the rows would be added in. A row that lands somewhere else makes
/// every token naming it point at something different — silently, and at
/// nothing the assembly itself can be checked against. This is the one place
/// the prediction can still be tested against the answer.
pub(crate) fn predicted(actual: Token, planned: Token, what: &str) -> Result<(), EmitError> {
    if actual == planned {
        return Ok(());
    }
    Err(EmitError::new(format!(
        "`{what}` was planned as {:#010x} and written as {:#010x}: \
         every token naming it points at something else",
        planned.0, actual.0
    )))
}

/// A `MethodDefOrRef` coded index: the row, with a bit saying which table.
fn method_def_or_ref(token: Token) -> u32 {
    let tag = u32::from(token.0 >> 24 == u32::from(table::MEMBER_REF));
    ((token.0 & 0x00FF_FFFF) << 1) | tag
}

fn method_flags(
    accessibility: rustlyn_semantics::Accessibility,
    instance: bool,
    modifiers: Modifiers,
) -> u16 {
    use rustlyn_semantics::Accessibility as A;
    // `internal` is not `private`: the whole assembly can reach it, and the
    // runtime refuses the call when the row says otherwise.
    let mut flags = match accessibility {
        A::Public => method_attributes::PUBLIC,
        A::Protected => method_attributes::FAMILY,
        A::ProtectedOrInternal => method_attributes::FAM_OR_ASSEM,
        A::ProtectedAndInternal => method_attributes::FAM_AND_ASSEM,
        A::Internal => method_attributes::ASSEMBLY,
        _ => method_attributes::PRIVATE,
    };
    if !instance {
        flags |= method_attributes::STATIC;
    }
    // A method that can be overridden gets a slot; one that overrides reuses
    // the slot its base declared, so it must *not* ask for a new one. An
    // `abstract override` does both at once — it says the derived type must
    // answer again for a slot that already exists — and asking for a new slot
    // there leaves the old one unimplemented forever. A `static abstract` or
    // `static virtual` member of an interface is virtual with no slot of an
    // instance's to take, and csc writes it without `newslot`.
    if modifiers.contains(Modifiers::VIRTUAL)
        || modifiers.contains(Modifiers::ABSTRACT)
        || modifiers.contains(Modifiers::OVERRIDE)
    {
        flags |= method_attributes::VIRTUAL;
    }
    if (modifiers.contains(Modifiers::VIRTUAL) || modifiers.contains(Modifiers::ABSTRACT))
        && !modifiers.contains(Modifiers::OVERRIDE)
        && instance
    {
        flags |= method_attributes::NEW_SLOT;
    }
    if modifiers.contains(Modifiers::ABSTRACT) {
        flags |= method_attributes::ABSTRACT;
    }
    if modifiers.contains(Modifiers::SEALED) {
        flags |= method_attributes::FINAL;
    }
    flags
}

/// A constant as the `Constant` table stores it: the element type it is, and
/// the value in the little-endian form §II.22.9 lays down.
/// A constant encoded at the width its declared type has: `const byte B = 7`
/// and `byte small = 7` are a `U1` in metadata, whatever the folder held it
/// in, and reflection hands back exactly that type.
fn encode_constant_as(value: &ConstantValue, special: Option<SpecialType>) -> (u8, Vec<u8>) {
    use crate::signature::ElementType;
    let integer = match value {
        ConstantValue::Int32(value) => Some(i64::from(*value)),
        ConstantValue::UInt32(value) => Some(i64::from(*value)),
        ConstantValue::Int64(value) => Some(*value),
        ConstantValue::UInt64(value) => Some(*value as i64),
        ConstantValue::Char(value) => Some(i64::from(u32::from(*value))),
        ConstantValue::Boolean(value) => Some(i64::from(*value)),
        _ => None,
    };
    match (special, integer) {
        (Some(SpecialType::Byte), Some(value)) => (ElementType::U1 as u8, vec![value as u8]),
        (Some(SpecialType::SByte), Some(value)) => (ElementType::I1 as u8, vec![value as i8 as u8]),
        (Some(SpecialType::Int16), Some(value)) => {
            (ElementType::I2 as u8, (value as i16).to_le_bytes().to_vec())
        }
        (Some(SpecialType::UInt16), Some(value)) => {
            (ElementType::U2 as u8, (value as u16).to_le_bytes().to_vec())
        }
        (Some(SpecialType::Char), Some(value)) => (
            ElementType::Char as u8,
            (value as u16).to_le_bytes().to_vec(),
        ),
        (Some(SpecialType::Boolean), Some(value)) => {
            (ElementType::Boolean as u8, vec![u8::from(value != 0)])
        }
        (Some(SpecialType::Int32), Some(value)) => {
            (ElementType::I4 as u8, (value as i32).to_le_bytes().to_vec())
        }
        (Some(SpecialType::UInt32), Some(value)) => {
            (ElementType::U4 as u8, (value as u32).to_le_bytes().to_vec())
        }
        (Some(SpecialType::Int64), Some(value)) => {
            (ElementType::I8 as u8, value.to_le_bytes().to_vec())
        }
        (Some(SpecialType::UInt64), Some(value)) => {
            (ElementType::U8 as u8, (value as u64).to_le_bytes().to_vec())
        }
        // `[CallerLineNumber] float line` is given an `int`, which is
        // written as the `float` it becomes, not as its bits.
        (Some(SpecialType::Single | SpecialType::Double), _) => {
            let number = match value {
                ConstantValue::UInt64(value) => *value as f64,
                ConstantValue::Single(value) => f64::from(*value),
                ConstantValue::Double(value) => *value,
                _ => match integer {
                    Some(value) => value as f64,
                    None => return encode_constant(value),
                },
            };
            if special == Some(SpecialType::Single) {
                // A `float` constant is kept as one: widening it and
                // narrowing it back gives the same bits.
                let single = match value {
                    ConstantValue::Single(value) => *value,
                    ConstantValue::UInt64(value) => *value as f32,
                    ConstantValue::Int64(value) => *value as f32,
                    _ => number as f32,
                };
                (ElementType::R4 as u8, single.to_le_bytes().to_vec())
            } else {
                (ElementType::R8 as u8, number.to_le_bytes().to_vec())
            }
        }
        _ => encode_constant(value),
    }
}

fn encode_constant(value: &ConstantValue) -> (u8, Vec<u8>) {
    use crate::signature::ElementType;
    match value {
        ConstantValue::Boolean(value) => (ElementType::Boolean as u8, vec![u8::from(*value)]),
        ConstantValue::Char(value) => (
            ElementType::Char as u8,
            (*value as u16).to_le_bytes().to_vec(),
        ),
        ConstantValue::Int32(value) => (ElementType::I4 as u8, value.to_le_bytes().to_vec()),
        ConstantValue::UInt32(value) => (ElementType::U4 as u8, value.to_le_bytes().to_vec()),
        ConstantValue::Int64(value) => (ElementType::I8 as u8, value.to_le_bytes().to_vec()),
        ConstantValue::UInt64(value) => (ElementType::U8 as u8, value.to_le_bytes().to_vec()),
        ConstantValue::Single(value) => (ElementType::R4 as u8, value.to_le_bytes().to_vec()),
        ConstantValue::Double(value) => (ElementType::R8 as u8, value.to_le_bytes().to_vec()),
        ConstantValue::String(text) => (
            ElementType::String as u8,
            text.encode_utf16().flat_map(u16::to_le_bytes).collect(),
        ),
        // A null constant is stored as a zero of pointer width.
        ConstantValue::Null => (0x12, vec![0; 4]),
    }
}

/// Whether a lambda reads a variable from around it, which is what needs a
/// display class. Reading `this` alone does not: the delegate can be made over
/// `this` itself.
/// The `GenericParamAttributes` bits a type parameter's variance sets.
/// The `GenericParamAttributes` of §II.23.1.7: the variance in the low two
/// bits, and `class`, `struct` and `new()` in the three above them.
///
/// The runtime checks every construction against these. `where T : class` is
/// what makes `Interlocked.CompareExchange<T>` callable with it, and without
/// the bit the call is refused where the source says it is fine.
pub(crate) fn generic_param_flags(
    symbols: &rustlyn_semantics::Symbols,
    parameter: SymbolId,
) -> u16 {
    let Some(detail) = symbols.get(parameter).as_type_parameter() else {
        return 0;
    };
    let variance = match detail.variance {
        rustlyn_semantics::Variance::Out => 1,
        rustlyn_semantics::Variance::In => 2,
        rustlyn_semantics::Variance::None => 0,
    };
    variance
        | if detail.reference_type { 0x0004 } else { 0 }
        | if detail.value_type { 0x0008 } else { 0 }
        // `allows ref struct` is `AllowByRefLike`.
        | if detail.allows_ref_struct { 0x0020 } else { 0 }
        | if detail.constructor || detail.value_type {
            // A `struct` constraint implies a parameterless constructor, and
            // the runtime expects the bit to say so.
            0x0010
        } else {
            0
        }
}

/// The integer a blob of one, two, four or eight bytes is typed as.
const fn primitive_of_size(size: u32) -> Option<ElementType> {
    match size {
        1 => Some(ElementType::U1),
        2 => Some(ElementType::I2),
        4 => Some(ElementType::I4),
        8 => Some(ElementType::I8),
        _ => None,
    }
}

/// The name of the struct a blob of `size` bytes is typed as.
fn array_data_type_name(size: u32) -> String {
    format!("__StaticArrayInitTypeSize={size}")
}

/// An element of a block-initialized array as the bytes it is stored as,
/// little-endian, converted to the element's type where the constant is of
/// another.
fn element_bytes(special: SpecialType, constant: &ConstantValue) -> Option<Vec<u8>> {
    use SpecialType as S;
    let integer = match constant {
        ConstantValue::Boolean(value) => Some(i128::from(*value)),
        ConstantValue::Char(value) => Some(i128::from(u32::from(*value))),
        ConstantValue::Int32(value) => Some(i128::from(*value)),
        ConstantValue::UInt32(value) => Some(i128::from(*value)),
        ConstantValue::Int64(value) => Some(i128::from(*value)),
        ConstantValue::UInt64(value) => Some(i128::from(*value)),
        _ => None,
    };
    let real = match constant {
        ConstantValue::Single(value) => Some(f64::from(*value)),
        ConstantValue::Double(value) => Some(*value),
        _ => integer.map(|value| value as f64),
    };
    Some(match special {
        S::Boolean => match constant {
            ConstantValue::Boolean(value) => vec![u8::from(*value)],
            _ => return None,
        },
        S::SByte | S::Byte => vec![integer? as u8],
        S::Int16 | S::UInt16 | S::Char => (integer? as u16).to_le_bytes().to_vec(),
        S::Int32 | S::UInt32 => (integer? as u32).to_le_bytes().to_vec(),
        S::Int64 | S::UInt64 => (integer? as u64).to_le_bytes().to_vec(),
        S::Single => match constant {
            ConstantValue::Single(value) => value.to_le_bytes().to_vec(),
            _ => (real? as f32).to_le_bytes().to_vec(),
        },
        S::Double => real?.to_le_bytes().to_vec(),
        _ => return None,
    })
}

/// An integral constant as a number: a layout's size or an offset written
/// as an `int`, or an enum's member folded to what it holds.
fn folded_integer(value: Option<ConstantValue>) -> Option<i64> {
    Some(match value? {
        ConstantValue::Int32(value) => i64::from(value),
        ConstantValue::UInt32(value) => i64::from(value),
        ConstantValue::Int64(value) => value,
        _ => return None,
    })
}

/// What a `[StructLayout]` says.
#[derive(Clone, Copy, Debug, Default)]
struct StructLayout {
    explicit: bool,
    size: Option<u32>,
    pack: Option<u16>,
}

/// What a `[DllImport]` says.
#[derive(Clone, Debug)]
pub(crate) struct DllImport {
    pub(crate) library: String,
    pub(crate) entry: String,
    pub(crate) flags: u16,
}

/// The last identifier of a name: `CharSet.Unicode` gives `Unicode`, and
/// `DllImport` itself.
fn last_identifier(node: &rustlyn_syntax::SyntaxNode) -> Option<String> {
    let mut last = None;
    for token in node.descendant_tokens() {
        if token.kind() == SyntaxKind::IdentifierToken {
            last = Some(token.value_text().to_string());
        }
    }
    last
}

/// Whether one span lies inside another.
/// The span a loop's per-iteration class covers: what C# makes fresh each
/// time round. That is the whole statement for a `foreach`, whose variable
/// is fresh, and for a `while` or a `do`, whose condition's variables are
/// (`while (Try(out var x))`); a `for` shares what its initializers declare
/// and nothing else, so its class starts at the condition.
pub(crate) fn loop_scope(statement: &BoundStatement) -> Option<TextSpan> {
    use rustlyn_semantics::BoundStatementKind as S;
    match &statement.kind {
        S::ForEach { .. } | S::While { .. } | S::DoWhile { .. } => Some(statement.span),
        S::For {
            condition,
            incrementors,
            body,
            ..
        } => {
            let start = condition
                .iter()
                .chain(incrementors)
                .map(|expression| expression.span.start())
                .chain(std::iter::once(body.span.start()))
                .min()
                .unwrap_or(body.span.start());
            Some(TextSpan::new(start, body.span.end() - start))
        }
        _ => None,
    }
}

/// The spans every loop's per-iteration class would cover, as
/// [`loop_scope`] says.
fn loop_scopes(statement: &BoundStatement, out: &mut Vec<TextSpan>) {
    use rustlyn_semantics::BoundStatementKind as S;
    match &statement.kind {
        S::ForEach { body, .. }
        | S::While { body, .. }
        | S::DoWhile { body, .. }
        | S::For { body, .. } => {
            out.extend(loop_scope(statement));
            loop_scopes(body, out);
        }
        S::Block(statements) => {
            for inner in statements {
                loop_scopes(inner, out);
            }
        }
        S::If {
            consequence,
            alternative,
            ..
        } => {
            loop_scopes(consequence, out);
            if let Some(alternative) = alternative {
                loop_scopes(alternative, out);
            }
        }
        S::Using { body, .. } | S::Lock { body, .. } | S::Fixed { body, .. } => {
            loop_scopes(body, out);
        }
        S::Switch { sections, .. } => {
            for section in sections {
                for inner in &section.statements {
                    loop_scopes(inner, out);
                }
            }
        }
        S::Try {
            body,
            catches,
            finally,
        } => {
            loop_scopes(body, out);
            for catch in catches {
                loop_scopes(&catch.body, out);
            }
            if let Some(finally) = finally {
                loop_scopes(finally, out);
            }
        }
        _ => {}
    }
}

/// The attribute `params` is written as: `ParamArrayAttribute` on an
/// array, `ParamCollectionAttribute` on any other collection (C# 13).
fn params_attribute(ty: &Type) -> &'static str {
    if matches!(ty, Type::Array { .. }) {
        "System.ParamArrayAttribute"
    } else {
        "System.Runtime.CompilerServices.ParamCollectionAttribute"
    }
}

pub(crate) fn within(inner: TextSpan, outer: TextSpan) -> bool {
    inner.start() >= outer.start() && inner.end() <= outer.end()
}

/// What the method a lambda becomes returns: the task an `async` lambda's
/// delegate gets, not the value its `return`s give.
pub(crate) fn lambda_return(lambda: &rustlyn_semantics::BoundLambda) -> Type {
    lambda
        .task_type
        .clone()
        .unwrap_or_else(|| lambda.return_type.clone())
}

fn captures_a_variable(lambda: &rustlyn_semantics::BoundLambda) -> bool {
    !lambda.captured.is_empty() || !lambda.captured_parameters.is_empty()
}

/// Whether a local function reads anything of the method that holds it.
///
/// `this` alone is not a reason for a display class: a local function that
/// reads only `this` can be an instance method of the type, which is where
/// `this` already is.
fn captures_a_variable_too(function: &rustlyn_semantics::BoundLocalFunction) -> bool {
    !function.captured.is_empty() || !function.captured_parameters.is_empty()
}

/// Whether a body needs somewhere to keep what was captured out of it.
///
/// One display class serves the whole member: every lambda and every local
/// function of it becomes a method of that class, so that a lambda written
/// inside a local function reaches the same fields as one written beside it.
fn needs_display(body: &rustlyn_semantics::BoundBody) -> bool {
    body.lambdas.iter().any(captures_a_variable)
        || body.local_functions.iter().any(captures_a_variable_too)
}

/// Which row of a declaration an attribute list is for.
///
/// A list with no target goes on the declaration's own row; `[return: X]`
/// and the like name another, and `[assembly: X]` sits in a file with no
/// declaration around it at all (§22.3).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AttributeTarget {
    Type,
    Method,
    Field,
    Property,
    Parameter,
    Event,
    Assembly,
    /// `[return: A]`, which goes on the method's parameter row numbered 0.
    Return,
    /// `class C<[A] T>`, on the parameter's `GenericParam` row.
    TypeParameter,
    /// `[field: A] int P { get; set; }`: on the field an automatic property
    /// keeps its value in — only what says `field:`, the rest being the
    /// property's.
    PropertyField,
}

impl AttributeTarget {
    /// The word an attribute target specifier uses for this row.
    const fn word(self) -> &'static str {
        match self {
            Self::Type => "type",
            Self::Method => "method",
            Self::Field => "field",
            Self::Property => "property",
            Self::Parameter => "param",
            Self::Event => "event",
            Self::Assembly => "assembly",
            Self::Return => "return",
            Self::TypeParameter => "typevar",
            Self::PropertyField => "field",
        }
    }
}

/// The attributes written on a declaration that go on one of its rows.
fn attributes_for(node: &SyntaxNode, target: AttributeTarget) -> Vec<SyntaxNode> {
    // A field's attributes sit on the declaration statement around the
    // declarator, not on the declarator itself.
    let holder = if node.kind() == SyntaxKind::VariableDeclarator {
        match node.parent().and_then(|declaration| declaration.parent()) {
            Some(holder) => holder.clone(),
            None => return Vec::new(),
        }
    } else {
        node.clone()
    };
    let mut found = Vec::new();
    for list in holder
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
    {
        let specifier = list
            .child_of_kind(SyntaxKind::AttributeTargetSpecifier)
            .map(|specifier| {
                specifier
                    .text()
                    .trim()
                    .trim_end_matches(':')
                    .trim()
                    .to_string()
            });
        let applies = match &specifier {
            None => !matches!(
                target,
                AttributeTarget::Assembly
                    | AttributeTarget::Return
                    | AttributeTarget::PropertyField
            ),
            Some(word) => word == target.word(),
        };
        if !applies {
            continue;
        }
        found.extend(
            list.children()
                .filter(|child| child.kind() == SyntaxKind::Attribute),
        );
    }
    found
}

/// The value an argument was written as, under whatever conversion the
/// binder put on it: the blob holds `1` as the `long` the parameter is, and
/// a value boxed into an `object` as itself.
fn written_value(value: &BoundExpression) -> &BoundExpression {
    match &value.kind {
        BoundExpressionKind::Conversion { operand, .. } => written_value(operand),
        _ => value,
    }
}

/// A `SerString` (§II.23.3): a null is `0xFF`, and anything else its UTF-8
/// length compressed and then the bytes.
fn ser_string(out: &mut Vec<u8>, text: Option<&str>) {
    match text {
        None => out.push(0xFF),
        Some(text) => {
            crate::signature::compress(out, text.len() as u32);
            out.extend_from_slice(text.as_bytes());
        }
    }
}

/// The element names of every tuple in a type, in pre-order, or nothing if
/// none of them is named.
fn tuple_names(ty: &Type) -> Vec<Option<String>> {
    fn walk(ty: &Type, names: &mut Vec<Option<String>>) {
        match ty {
            Type::Tuple(elements) => {
                names.extend(elements.iter().map(|element| element.name.clone()));
                for element in elements {
                    walk(&element.ty, names);
                }
            }
            Type::Named { type_arguments, .. } => {
                for argument in type_arguments {
                    walk(argument, names);
                }
            }
            Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
                walk(element, names);
            }
            _ => {}
        }
    }
    let mut names = Vec::new();
    walk(ty, &mut names);
    if names.iter().all(Option::is_none) {
        return Vec::new();
    }
    names
}

/// The parameters of a method or of an indexer.
fn member_parameters(
    symbols: &rustlyn_semantics::Symbols,
    member: SymbolId,
) -> Option<&[SymbolId]> {
    let symbol = symbols.get(member);
    symbol
        .as_method()
        .map(|detail| detail.parameters.as_slice())
        .or_else(|| {
            symbol
                .as_property()
                .map(|detail| detail.parameters.as_slice())
        })
}
