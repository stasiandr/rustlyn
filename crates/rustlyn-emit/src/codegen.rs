//! Lowering one bound body to IL.
//!
//! The bound tree says what the program means; this says how a stack machine
//! carries it out. Two jobs live here that a tree-walking interpreter never
//! has to do. Everything that reads *and* writes a location — a compound
//! assignment, `++`, `foreach` — has to evaluate the location's parts exactly
//! once, so those parts go into temporary locals and are pushed again from
//! there; and `&&`, `||`, `?:` and `??` have to be turned into branches,
//! because the stack machine has no short-circuiting operator.

use std::collections::HashMap;
use std::sync::Arc;

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundCatch, BoundEnumeration, BoundExpression, BoundExpressionKind,
    BoundListPattern, BoundPattern, BoundPatternKind, BoundRecursivePattern, BoundStatement,
    BoundStatementKind, BoundSwitchArm, BoundSwitchLabel, BoundSwitchSection, BoundUsingResource,
    ConstantValue, ConversionKind, IncrementOperator, LocalId, Modifiers, RefKind, SpecialType,
    SymbolId, SymbolKind, Symbols, Type, TypeKind, UnaryOperator,
};
use rustlyn_syntax::SyntaxKind;
use rustlyn_text::TextSpan;

use crate::emitter::{
    ArrayMember, Closure, DisplayClass, DisplayView, EmitError, Emitter, MachineKey, MethodPlan,
    MethodSource, ParameterPlan, TypePlan,
};
use crate::il::{
    ExceptionRegion, HandlerKind, IndirectKind, Instruction, InstructionStream, Label, Token,
};
use crate::iterator::IteratorRun;
use crate::signature::{
    ElementType, SigType, generic_method_signature, method_signature, standalone_method_signature,
};

/// A place a value can be read from and written to.
///
/// The parts a place needs on the stack are evaluated once into temporaries,
/// so that `a[f()] += 1` calls `f` once, as C# requires.
#[derive(Clone, Debug)]
pub(crate) enum Place {
    Local(u16),
    Argument(u16),
    StaticField(Token),
    Field {
        receiver: u16,
        token: Token,
    },
    /// A field of a value type. The receiver is an address rather than a
    /// value, because storing into a copy would throw the store away, and the
    /// address is re-pushed rather than parked because a local cannot hold a
    /// managed pointer without a by-ref signature.
    ValueField {
        address: Address,
        token: Token,
    },
    Element {
        array: u16,
        index: u16,
        element: Token,
        /// What the array holds, which says which `stelem` writes it.
        element_type: Type,
    },
    /// An element of an array with more than one dimension, which the runtime
    /// reaches through `Get` and `Set` rather than through an opcode.
    MultiElement {
        array: u16,
        indices: Vec<u16>,
        get: Token,
        set: Token,
    },
    /// A variable a lambda captured, which now lives in the display class.
    Captured {
        holder: Holder,
        token: Token,
    },
    /// What a `ref` or `out` parameter points at.
    Indirect {
        argument: u16,
        kind: IndirectKind,
    },
    /// The same for a `ref` local, whose slot holds the address.
    IndirectLocal {
        slot: u16,
        kind: IndirectKind,
    },
    /// A property or an indexer, which is a property that takes arguments.
    ///
    /// The accessors are resolved when the place is read or written rather
    /// than when it is formed, because which token names them depends on the
    /// receiver — and because a read-only property should say it has no setter
    /// only when something tries to write to it.
    Property {
        receiver: Option<Receiver>,
        arguments: Vec<u16>,
        /// Which of the arguments an `in` parameter takes by address: the
        /// slot holds the value, and its address is what is pushed.
        by_address: Vec<bool>,
        property: SymbolId,
        receiver_type: Option<Type>,
        /// Set where the property has no setter and its getter hands back a
        /// reference: `array[i] = v` on a `ref T this[int]` writes through
        /// what the getter returns, because that *is* where the value lives.
        through: Option<IndirectKind>,
        /// Written through `base.`, whose accessors are called and never
        /// dispatched.
        direct: bool,
        /// The receiver's type where the property is an extension block's
        /// (C# 14): what a generic block's accessors are instantiated for.
        extension_receiver: Option<Type>,
    },
}

/// What a property's receiver is, once it has been evaluated once.
///
/// A reference type is copied into a slot, and copying a reference costs
/// nothing and points at the same object. A value type cannot be copied —
/// writing to the copy would throw the write away — so where it has an
/// address that address is kept instead.
#[derive(Clone, Debug)]
pub(crate) enum Receiver {
    Slot(u16),
    At(Address),
    /// A value-type variable an extension block's accessor takes by value:
    /// read from where it lives at each call, as Roslyn does, so that an
    /// accessor sees what the one before it left there.
    ValueAt(Address, IndirectKind),
    /// `this` or `base` of a class: pushed as the argument it is, since a
    /// protected member of the base may only be reached through `this`
    /// itself, and a copy in a slot is not that to the verifier.
    This,
}

/// Somewhere whose address can be taken again as often as it is needed,
/// because taking it has no effect of its own.
#[derive(Clone, Debug)]
pub(crate) enum Address {
    Local(u16),
    Argument(u16),
    /// `this` inside a value type's method, which is already an address.
    This,
    /// An argument that already holds an address: a `ref` or `out` parameter.
    Held(u16),
    /// A local that already holds one: a `ref` local.
    HeldLocal(u16),
    StaticField(Token),
    /// A field of something that has an address: `a.b.c = 1` writes through
    /// the address of `a.b`, which is the address of `a` and a `ldflda`.
    Field(Box<Address>, Token),
    /// A `ref` field of something that has an address, which holds one:
    /// the field is loaded, not its address taken.
    HeldField(Box<Address>, Token),
}

/// Where the object an object or collection initializer is working on lives.
///
/// A reference type is the value already on the stack, duplicated once per
/// initializer. A value type has no reference to duplicate, so it waits in a
/// local and the members are written through that local's address.
#[derive(Clone, Copy, Debug)]
enum Created {
    Stack,
    Local(u16),
    /// A reference held in a slot rather than on the stack: an initializer
    /// that calls through a `dynamic` site has the site under it there.
    Held(u16),
}

pub(crate) struct BodyEmitter<'a, 'b> {
    pub(crate) emitter: &'a mut Emitter<'b>,
    /// The bound body: shared with the emitter's cache rather than copied,
    /// since a closure's method is emitted against the whole of the member
    /// it was written in.
    pub(crate) body: Arc<BoundBody>,
    /// Which statements are the method's: see [`Statements`].
    statements: Statements,
    pub(crate) stream: InstructionStream,
    /// Where the object an initializer is initializing can be found,
    /// innermost last.
    creating: Vec<Created>,
    /// A variable of a type parameter an indexer is being reached through,
    /// and the local holding the address of the receiver kept for it: the
    /// `Length` or `Count` an `Index` counts back from is read through the
    /// same receiver (`item[^F(ref item)]` on a class reads the instance
    /// `item` held first).
    counted: Option<(BoundExpressionKind, u16)>,
    /// The locals holding the receivers of the `?.` expressions being
    /// emitted, innermost last.
    accessing: Vec<u16>,
    /// Which of those hold a reference to the receiver rather than the
    /// receiver itself: a `T` that may be a struct is reached where it lives.
    accessing_by_reference: Vec<bool>,
    /// The signature of every local slot, including the temporaries added
    /// while lowering.
    pub(crate) locals: Vec<SigType>,
    /// Which locals hold an address rather than a value.
    by_ref_locals: Vec<bool>,
    /// Where the declared locals' slots begin: zero, except while a field
    /// initializer's body is emitted inside a constructor.
    local_base: u16,
    /// The reads one match shares across its patterns, where there is a
    /// match being emitted.
    pattern_share: Option<PatternShare>,
    /// The label each `goto` target name stands for.
    pub(crate) labels: HashMap<String, Label>,
    /// The slot holding each loop scope's class, by the scope's span, made
    /// once per body however many times the loop is entered.
    scope_slots: HashMap<TextSpan, u16>,
    /// The type of every local slot, for the places that need more than the
    /// signature.
    pub(crate) local_types: Vec<Type>,
    /// Where `break` goes, innermost last, with the protected-region depth the
    /// target sits at. A loop and a `switch` both push here; only a loop
    /// pushes a `continue` target as well, which is what makes `continue`
    /// inside a `switch` reach the loop around it.
    breaks: Vec<(Label, usize)>,
    continues: Vec<(Label, usize)>,
    /// Where each section of the switches being emitted begins, innermost
    /// last, so that `goto case` has somewhere to jump to.
    cases: Vec<CaseTargets>,
    /// How many `try` regions enclose the cursor. Leaving one needs `leave`
    /// rather than `br`, and the depth is what says whether a jump leaves one.
    pub(crate) protected: usize,
    /// The single exit a method with a `finally` gets: `return` inside a
    /// protected region cannot return, it has to leave to here.
    pub(crate) exit: Option<(Label, Option<u16>)>,
    pub(crate) parameters: Vec<ParameterPlan>,
    pub(crate) instance: bool,
    /// Whether the method belongs to a value type, which is what makes
    /// `this` an address rather than a reference.
    in_value_type: bool,
    /// The type being emitted, as its own methods see it.
    pub(crate) self_type: Type,
    /// The member whose body this is, which is how a lambda inside it finds
    /// the method it was planned as.
    pub(crate) owner: Option<SymbolId>,
    /// Where to find the display class holding this member's captures, when
    /// there is one. The method that made it keeps it in a local; a lambda
    /// that became one of its methods *is* it.
    pub(crate) display: Option<(DisplayClass, DisplayAt)>,
    /// The display class of the member around a closure, as the closure's
    /// own state machine reaches it: held in a slot, loaded from the
    /// machine's `<>4__this` when `MoveNext` starts. The machine's own
    /// fields are `display`; what the closure captured of the member is
    /// here.
    pub(crate) captures: Vec<(DisplayView, Holder)>,
    /// How many of `captures` were there when the body started: the rest
    /// are the classes of loop bodies entered since, innermost last, and
    /// inside such a body its class is where a variable is — before the
    /// body's own class, which a machine hoists every local into too.
    pub(crate) setup_captures: usize,
    /// Whether the display classes being set up leave `this` out for now:
    /// a constructor makes them before its initializer runs, when there is
    /// no object yet to put in them.
    defer_this: bool,
    /// Whether the expression being emitted is inside a `checked` region:
    /// its arithmetic and narrowings then trap on overflow.
    pub(crate) checked: bool,
    /// Set just before the addition of a `p[i]` is emitted, which is never
    /// checked; taken by that addition.
    element_access: bool,
    /// The slots `stackalloc`s made ahead of their statement were kept in,
    /// by where they stand.
    hoisted_stackallocs: HashMap<TextSpan, u16>,
    /// How each slot in `captures` is filled when the body starts: from a
    /// field of `this`, or from a field of a slot filled before it.
    pub(crate) capture_loads: Vec<(CaptureSource, u16)>,
    /// The state machine being emitted, when this body is one's `MoveNext`.
    pub(crate) iterator: Option<crate::iterator::IteratorRun>,
    /// The `async` machine being emitted, when this body is one's `MoveNext`.
    pub(crate) async_run: Option<crate::async_machine::AsyncRun>,
    /// What both kinds of machine share while `MoveNext` is emitted: the
    /// suspensions, the regions and the dispatches between them.
    pub(crate) machine: Option<crate::async_machine::MachineRun>,
    /// Where the `try` around the whole of an `async` `MoveNext` begins.
    pub(crate) async_try_start: Option<Label>,
}

/// What holds a captured variable's field: the display class the body has
/// (`this` or a local, per `DisplayAt`), or the member's display class held
/// in a slot by a closure's machine.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Holder {
    Display,
    Slot(u16),
    /// A field of `this`: the class a loop body of an `async` machine makes
    /// each time round, which `MoveNext` keeps on the machine.
    ThisField(Token),
}

/// A captured variable: the object holding it, and its field.
#[derive(Clone, Copy, Debug)]
struct Capture {
    holder: Holder,
    token: Token,
}

/// Where a display class held in a slot is loaded from when the body starts.
#[derive(Clone, Copy, Debug)]
pub(crate) enum CaptureSource {
    /// A field of `this`: a machine's `<>4__this`, or a nested class's
    /// parent.
    ThisField(Token),
    /// A field of a class already loaded into a slot: the parent of the
    /// class a machine's `<>4__this` holds.
    SlotField(u16, Token),
}

/// One step from the value a match is on to a value a pattern reads.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum PathStep {
    Element(usize),
    Member(SymbolId),
}

/// What one match (an `is`, a `switch` statement or expression) reads more
/// than once — the same property in two arms, the same tuple element in two
/// alternatives of an `or` — and so reads once (as Roslyn's decision DAG
/// does): each such read is kept in a slot, with a flag saying whether it
/// has happened yet.
#[derive(Default)]
struct PatternShare {
    /// Where each slot a pattern tests came from.
    paths: HashMap<u16, Vec<PathStep>>,
    /// The flag of each read that is shared, set to false at the start.
    flags: HashMap<Vec<PathStep>, u16>,
    /// The slot a shared read is kept in, once it has a type.
    values: HashMap<Vec<PathStep>, u16>,
}

/// Counts the reads a pattern makes, by where they read from, with the
/// order each place was first read in.
fn count_pattern_reads(
    pattern: &BoundPattern,
    path: &[PathStep],
    counts: &mut HashMap<Vec<PathStep>, (usize, usize)>,
) {
    match &pattern.kind {
        BoundPatternKind::Recursive(recursive) => {
            for (member, inner) in &recursive.properties {
                let mut next = path.to_vec();
                next.push(PathStep::Member(*member));
                let first = counts.len();
                counts.entry(next.clone()).or_insert((0, first)).0 += 1;
                count_pattern_reads(inner, &next, counts);
            }
            if recursive.deconstruct.is_none() {
                for (index, inner) in recursive.positional.iter().enumerate() {
                    let mut next = path.to_vec();
                    next.push(PathStep::Element(index));
                    let first = counts.len();
                    counts.entry(next.clone()).or_insert((0, first)).0 += 1;
                    count_pattern_reads(inner, &next, counts);
                }
            }
        }
        BoundPatternKind::And(left, right) | BoundPatternKind::Or(left, right) => {
            count_pattern_reads(left, path, counts);
            count_pattern_reads(right, path, counts);
        }
        BoundPatternKind::Not(inner) => count_pattern_reads(inner, path, counts),
        _ => {}
    }
}

/// Where the display class instance is reached from.
#[derive(Clone, Copy, Debug)]
pub(crate) enum DisplayAt {
    Local(u16),
    This,
}

/// The labels of one switch's sections, by the constant that reaches them.
#[derive(Default)]
struct CaseTargets {
    values: Vec<((Type, ConstantValue), Label)>,
    default: Option<Label>,
    /// How deep in protected regions the switch itself is, so a jump out of a
    /// `try` inside it leaves the region rather than branching out of it.
    depth: usize,
}

impl<'a, 'b> BodyEmitter<'a, 'b> {
    /// Emits the body of one planned method.
    pub(crate) fn emit(
        emitter: &'a mut Emitter<'b>,
        plan: &TypePlan,
        method: &MethodPlan,
    ) -> Result<Vec<u8>, EmitError> {
        let body: Arc<BoundBody> = match &method.source {
            MethodSource::Declared(symbol) => emitter.body_of(*symbol).unwrap_or_default(),
            MethodSource::PropertyGetter {
                property,
                backing: false,
            } => emitter.body_of(*property).unwrap_or_default(),
            // A lambda is emitted against the body it was written in: its
            // locals are on that member's table, because that is where the
            // binder put them.
            MethodSource::Lambda { owner, .. } | MethodSource::LocalFunction { owner, .. } => {
                emitter.body_of(*owner).unwrap_or_default()
            }
            // The body the source wrote now runs inside `MoveNext`, and its
            // locals live in the machine's fields rather than in slots.
            MethodSource::IteratorMoveNext(key) => {
                Arc::new(emitter.machine_body(*key).unwrap_or_default())
            }
            // The same for an `async` method, with every `await` already
            // moved to a statement of its own.
            MethodSource::AsyncMoveNext(key) => {
                Arc::new(emitter.async_body(*key).unwrap_or_default())
            }
            // A positional constructor has no block, but `record Derived(int
            // X) : Base(X)` chains, and the chain is bound from the parameter
            // list that declares it.
            MethodSource::RecordConstructor(constructor) => {
                emitter.body_of(*constructor).unwrap_or_default()
            }
            _ => Arc::default(),
        };
        // A lambda's statements are its own, not the member's.
        let statements = match &method.source {
            MethodSource::Lambda { index, .. } => {
                // A lambda converted to `Expression<TDelegate>` is described
                // where it is written and never called as a method: the
                // method it was planned as only has to be a valid one.
                let lambda = body.lambdas.get(*index);
                let is_tree = lambda.is_some_and(|lambda| {
                    body.types.get(&lambda.span).is_some_and(|ty| {
                        matches!(ty, Type::Named { symbol, type_arguments }
                            if type_arguments.len() == 1
                                && emitter.compilation.symbols().qualified_name(*symbol)
                                    == "System.Linq.Expressions.Expression`1")
                    })
                });
                Statements::Own(match lambda {
                    Some(lambda) if is_tree => vec![BoundStatement::new(
                        BoundStatementKind::Throw(Some(BoundExpression::new(
                            BoundExpressionKind::Literal(ConstantValue::Null),
                            Type::Null,
                            lambda.span,
                        ))),
                        lambda.span,
                    )],
                    Some(lambda) => vec![lambda.body.clone()],
                    None => Vec::new(),
                })
            }
            // The same for a local function: its statements are its own, and
            // the locals it shares with the method that holds it are the
            // table it was bound against.
            MethodSource::LocalFunction { index, .. } => Statements::Own(
                body.local_functions
                    .get(*index)
                    .map(|function| vec![function.body.clone()])
                    .unwrap_or_default(),
            ),
            MethodSource::Declared(symbol) => destructor_statements(emitter, *symbol, &body)
                .map_or(Statements::Body, Statements::Own),
            _ => Statements::Body,
        };

        let mut locals = Vec::new();
        let mut local_types = Vec::new();
        let by_ref_locals: Vec<bool> = body.locals.iter().map(|local| local.by_ref).collect();
        for local in &body.locals {
            // The locals of a body are one table, shared with the lambdas and
            // the local functions bound inside it. A generic local function's
            // own `T` is not nameable from the method that holds it — `!!0` in
            // a method declaring no type parameters is not a signature the
            // runtime will read — and the slot is not one this method touches.
            // The type parameters this body may name: the method's own, and
            // whatever the type being written declares — a display class or a
            // state machine over a generic method declares that method's.
            let mut nameable = method.type_parameters.clone();
            nameable.extend(emitter.display_generics.iter().copied());
            let signature =
                if foreign_parameter(emitter.compilation.symbols(), &local.ty, &nameable) {
                    SigType::Primitive(ElementType::Object)
                } else {
                    emitter.sig_type(&local.ty).map_err(|error| {
                        EmitError::new(format!(
                            "in `{}`: the local `{}` cannot be emitted: {error}",
                            method.name, local.name
                        ))
                    })?
                };
            // A `ref` local's slot holds an address, and its signature has to
            // say so: `T&`, not `T`.
            locals.push(if local.by_ref {
                SigType::ByRef(Box::new(signature))
            } else {
                signature
            });
            local_types.push(local.ty.clone());
        }

        // A `finally` anywhere means every `return` has to leave to one exit,
        // so the exit is set up before anything is emitted.
        // An `async` machine's `MoveNext` has an exit of its own, outside
        // the `try` around the whole body.
        let needs_exit = !matches!(
            method.source,
            MethodSource::AsyncMoveNext(_) | MethodSource::IteratorMoveNext(_)
        ) && match &statements {
            Statements::Own(own) => own.iter().any(has_finally),
            _ => body.statements.iter().any(has_finally),
        };
        let in_value_type = emitter.is_value_type(&Type::named(plan.symbol));
        let self_type = emitter.binder.self_type(plan.symbol);
        let check_overflow = emitter.compilation.options().check_overflow;

        let owner = match &method.source {
            MethodSource::Declared(symbol) => Some(*symbol),
            MethodSource::PropertyGetter { property, .. }
            | MethodSource::PropertySetter { property } => Some(*property),
            MethodSource::Lambda { owner, .. } | MethodSource::LocalFunction { owner, .. } => {
                Some(*owner)
            }
            // A machine's `MoveNext` is the member's body, lambdas and all;
            // the method that makes the machine is the member itself.
            MethodSource::IteratorMoveNext(key)
            | MethodSource::IteratorStart(key)
            | MethodSource::AsyncMoveNext(key)
            | MethodSource::AsyncStart(key) => Some(key.owner()),
            // A positional constructor's parameter list is its body: the
            // arguments to the base are bound there, lambdas and all.
            MethodSource::RecordConstructor(constructor) => Some(*constructor),
            _ => None,
        };
        let mut this = Self {
            emitter,
            body,
            statements,
            stream: InstructionStream::new(),
            creating: Vec::new(),
            counted: None,
            accessing: Vec::new(),
            accessing_by_reference: Vec::new(),
            locals,
            by_ref_locals,
            local_base: 0,
            pattern_share: None,
            labels: HashMap::new(),
            scope_slots: HashMap::new(),
            setup_captures: 0,
            defer_this: false,
            // `/checked` makes the code outside any `checked`/`unchecked`
            // region checked.
            checked: check_overflow,
            element_access: false,
            hoisted_stackallocs: HashMap::new(),
            local_types,
            breaks: Vec::new(),
            cases: Vec::new(),
            continues: Vec::new(),
            protected: 0,
            exit: None,
            parameters: method.parameters.clone(),
            instance: method.instance,
            in_value_type,
            self_type,
            owner,
            display: None,
            captures: Vec::new(),
            capture_loads: Vec::new(),
            iterator: None,
            async_run: None,
            machine: None,
            async_try_start: None,
        };
        // The display class a closure's method is a member of, where it is
        // one: the member's, or that of the lambda it was written inside.
        let home = match &method.source {
            MethodSource::Lambda { owner, index }
            | MethodSource::AsyncStart(MachineKey::Lambda { owner, index })
            | MethodSource::AsyncMoveNext(MachineKey::Lambda { owner, index }) => {
                this.emitter.home_of_lambda(*owner, *index)
            }
            MethodSource::LocalFunction { owner, index }
            | MethodSource::AsyncStart(MachineKey::Function { owner, index })
            | MethodSource::AsyncMoveNext(MachineKey::Function { owner, index })
            | MethodSource::IteratorStart(MachineKey::Function { owner, index })
            | MethodSource::IteratorMoveNext(MachineKey::Function { owner, index }) => {
                let symbol = this
                    .emitter
                    .body_of(*owner)
                    .and_then(|body| body.local_functions.get(*index).map(|it| it.symbol));
                symbol.and_then(|symbol| this.emitter.home_of_function(*owner, symbol))
            }
            _ => None,
        };
        // A lambda that became a method of the display class reaches it as
        // `this`; the method that made it keeps it in a local of its own.
        let in_a_local = |this: &mut Self, display: DisplayClass| {
            let slot = this.locals.len() as u16;
            this.locals.push(display.sig.clone());
            this.local_types.push(Type::Error);
            Some((display, DisplayAt::Local(slot)))
        };
        let members = owner.and_then(|owner| this.emitter.displays.get(&owner).cloned());
        this.display = match &method.source {
            // A method of `<>c` reads nothing of the member's.
            MethodSource::Lambda { owner, index }
                if this
                    .emitter
                    .singleton_lambdas
                    .contains_key(&(*owner, *index)) =>
            {
                None
            }
            MethodSource::Lambda { .. } | MethodSource::LocalFunction { .. } => {
                match home.clone() {
                    Some(display) => Some((display, DisplayAt::This)),
                    None => members.and_then(|display| in_a_local(&mut this, display)),
                }
            }
            // A state machine is its own display class, reached as `this`
            // from its `MoveNext`; the method that makes one has nothing to
            // reach — the machine is made and filled by hand.
            MethodSource::IteratorMoveNext(MachineKey::Member(_))
            | MethodSource::AsyncMoveNext(MachineKey::Member(_)) => {
                members.map(|display| (display, DisplayAt::This))
            }
            // A closure's machine is not the class the closure lived in:
            // the machine keeps that class in `<>4__this`, reached from a
            // slot while `MoveNext` runs.
            MethodSource::AsyncMoveNext(key) | MethodSource::IteratorMoveNext(key) => {
                if let Some(display) = home.clone() {
                    let held = match &method.source {
                        MethodSource::AsyncMoveNext(_) => {
                            this.emitter.asyncs.get(key).and_then(|plan| plan.this)
                        }
                        _ => this.emitter.iterators.get(key).and_then(|plan| plan.this),
                    };
                    let slot = this.locals.len() as u16;
                    this.locals.push(display.inner_sig.clone());
                    this.local_types.push(Type::Error);
                    if let Some(field) = held {
                        this.capture_loads
                            .push((CaptureSource::ThisField(field), slot));
                    }
                    // The class the closure lived in may itself sit inside
                    // another's, and that one inside the member's: each is a
                    // field of the one below it.
                    let mut current = display.clone();
                    let mut below = slot;
                    while let Some(field) = current.inside.parent {
                        let parent = match current.parent_closure {
                            Some(closure) => owner.and_then(|owner| {
                                this.emitter.nested_displays.get(&(owner, closure)).cloned()
                            }),
                            None => {
                                owner.and_then(|owner| this.emitter.displays.get(&owner).cloned())
                            }
                        };
                        let Some(parent) = parent else {
                            break;
                        };
                        let outer = this.locals.len() as u16;
                        this.locals.push(parent.inner_sig.clone());
                        this.local_types.push(Type::Error);
                        this.capture_loads
                            .push((CaptureSource::SlotField(below, field), outer));
                        this.captures
                            .push((parent.inside.clone(), Holder::Slot(outer)));
                        below = outer;
                        current = parent;
                    }
                    this.captures
                        .insert(0, (display.inside.clone(), Holder::Slot(slot)));
                }
                None
            }
            // The method that makes a closure's machine is the closure's own
            // method: `this` where the closure lives in a class.
            MethodSource::AsyncStart(key) | MethodSource::IteratorStart(key)
                if !matches!(key, MachineKey::Member(_)) =>
            {
                home.clone().map(|display| (display, DisplayAt::This))
            }
            MethodSource::IteratorStart(_) | MethodSource::AsyncStart(_) => None,
            _ => members.and_then(|display| in_a_local(&mut this, display)),
        };
        // `a => b => a + b`: the outer lambda makes the class its `a` lives
        // in when it runs, and keeps it in a slot; the inner lambda, a method
        // of that class, reaches the member's class through the parent field.
        let mut owned: Option<(DisplayClass, u16)> = None;
        let own_closure = match &method.source {
            MethodSource::Lambda { owner, index } => Some((*owner, Closure::Lambda(*index))),
            MethodSource::LocalFunction { owner, index } => {
                Some((*owner, Closure::Function(*index)))
            }
            _ => None,
        };
        if let Some(key) = own_closure
            && let Some(display) = this.emitter.nested_displays.get(&key).cloned()
        {
            let slot = this.locals.len() as u16;
            this.locals.push(display.sig.clone());
            this.local_types.push(Type::Error);
            this.captures
                .push((display.outside.clone(), Holder::Slot(slot)));
            owned = Some((display, slot));
        }
        match &method.source {
            MethodSource::AsyncMoveNext(MachineKey::Lambda { owner, index })
                if this
                    .emitter
                    .nested_displays
                    .contains_key(&(*owner, Closure::Lambda(*index))) =>
            {
                return Err(EmitError::new(
                    "an `async` lambda whose variables a lambda inside it captures is not built \
                     yet",
                ));
            }
            MethodSource::AsyncMoveNext(MachineKey::Function { owner, index })
            | MethodSource::IteratorMoveNext(MachineKey::Function { owner, index })
                if this
                    .emitter
                    .nested_displays
                    .contains_key(&(*owner, Closure::Function(*index))) =>
            {
                return Err(EmitError::new(
                    "a local function machine whose variables a closure inside it captures is \
                     not built yet",
                ));
            }
            _ => {}
        }
        // A nested class's parent, and its parent's parent, up to the
        // member's class: each is loaded into a slot from the one below, so
        // that `z` in `x => y => z => x + y + z` reads `x` two classes up.
        if matches!(
            method.source,
            MethodSource::Lambda { .. } | MethodSource::LocalFunction { .. }
        ) && let Some(display) = &home
        {
            let mut current = display.clone();
            let mut below: Option<u16> = None;
            while let Some(field) = current.inside.parent {
                let parent = match current.parent_closure {
                    Some(closure) => owner.and_then(|owner| {
                        this.emitter.nested_displays.get(&(owner, closure)).cloned()
                    }),
                    None => owner.and_then(|owner| this.emitter.displays.get(&owner).cloned()),
                };
                let Some(parent) = parent else {
                    return Err(EmitError::new(
                        "a display class with a parent the member lacks",
                    ));
                };
                let slot = this.locals.len() as u16;
                this.locals.push(parent.inner_sig.clone());
                this.local_types.push(Type::Error);
                this.captures
                    .push((parent.inside.clone(), Holder::Slot(slot)));
                this.capture_loads.push((
                    match below {
                        None => CaptureSource::ThisField(field),
                        Some(from) => CaptureSource::SlotField(from, field),
                    },
                    slot,
                ));
                below = Some(slot);
                current = parent;
            }
        }
        // A state machine reads the method's arguments, its locals and its
        // `this` out of its own fields, which is what a display class already
        // does — so it is one, reached as `this`. A machine with lambdas in it
        // is registered as one already, with the lambdas as its methods.
        if let MethodSource::IteratorMoveNext(key) = &method.source {
            let Some(iterator) = this.emitter.iterators.get(key).cloned() else {
                return Err(EmitError::new("a state machine with no plan"));
            };
            if this.display.is_none() {
                this.display = Some((
                    DisplayClass {
                        sig: iterator.sig.clone(),
                        inner_sig: iterator.sig.clone(),
                        parent_closure: None,
                        generics: Vec::new(),
                        inside: DisplayView {
                            constructor: iterator.constructor,
                            locals: iterator.locals.clone(),
                            parameters: iterator.parameters.clone(),
                            // A hosted closure's `<>4__this` is the display
                            // class, not what the body calls `this`.
                            this: if iterator.hosted { None } else { iterator.this },
                            ..DisplayView::default()
                        },
                        outside: DisplayView::default(),
                    },
                    DisplayAt::This,
                ));
            }
            let yielded = this.stream.label();
            let done = this.stream.label();
            this.iterator = Some(IteratorRun {
                plan: iterator,
                yielded,
                done,
            });
        }
        // A constructor makes its display class once the object exists:
        // storing `this` anywhere before the base constructor has run is
        // not something the verifier allows.
        let constructor =
            matches!(&method.source, MethodSource::Declared(_)) && method.name == ".ctor";
        if !constructor {
            this.emit_frame_setup(owned.as_ref())?;
        }
        this.setup_captures = this.captures.len();
        this.emit_move_next_dispatch()?;
        if needs_exit {
            let label = this.stream.label();
            let slot = match &method.return_type {
                Type::Void => None,
                ty => Some(this.temporary(ty)?),
            };
            this.exit = Some((label, slot));
        }
        if let MethodSource::AsyncMoveNext(key) = &method.source {
            this.begin_async_move_next(*key)?;
        }

        match &method.source {
            MethodSource::DefaultConstructor => {
                this.emit_instance_initializers(plan)?;
                this.emit_implicit_base_constructor(plan)?;
            }
            MethodSource::Declared(_) if method.name == ".ctor" => {
                // `: this(Get(out var x), () => x)` captures a variable the
                // constructor initializer declares, and the class holding it
                // has to exist before that call. It can, where it does not
                // hold `this`: nothing about it needs the object made yet.
                let early = this
                    .display
                    .as_ref()
                    .is_some_and(|(display, _)| display.outside.this.is_none())
                    && owned
                        .as_ref()
                        .is_none_or(|(display, _)| display.outside.this.is_none());
                if early {
                    this.emit_frame_setup(owned.as_ref())?;
                }
                this.emit_parameter_captures(plan)?;
                let statements = this.take_statements();
                let initializer = statements
                    .iter()
                    .find_map(|statement| match &statement.kind {
                        BoundStatementKind::ConstructorInitializer {
                            constructor,
                            arguments,
                            chains_to_this,
                        } => Some((*constructor, arguments.clone(), *chains_to_this)),
                        _ => None,
                    });
                // A constructor that chains to another of its own type leaves
                // the field initializers to that one; running them twice would
                // undo whatever it did.
                // `A(string x) : this(() => x)` hands the initializer a lambda
                // over a parameter, so the class holding it has to exist
                // first. Where the class holds no `this` nothing stops it
                // being made before the object is.
                let early =
                    initializer.is_some() && matches!(this.display, Some((_, DisplayAt::Local(_))));
                if early {
                    this.defer_this = true;
                    let made = this.emit_frame_setup(owned.as_ref());
                    this.defer_this = false;
                    made?;
                }
                match initializer {
                    // A struct's `: this()` reaching the constructor nobody
                    // wrote zeroes the fields and runs no initializer, so
                    // this constructor runs them after it (C# 10).
                    Some((None, arguments, true)) => {
                        this.emit_constructor_call(plan, None, &arguments)?;
                        this.emit_instance_initializers(plan)?;
                    }
                    Some((constructor, arguments, chains_to_this)) => {
                        if !chains_to_this {
                            this.emit_instance_initializers(plan)?;
                        }
                        this.emit_constructor_call(plan, constructor, &arguments)?;
                        // A struct's `: this()` that no constructor answers
                        // only zeroes the fields; the initializers are still
                        // this constructor's to run, after it.
                        if chains_to_this && constructor.is_none() {
                            this.emit_instance_initializers(plan)?;
                        }
                    }
                    None => {
                        this.emit_instance_initializers(plan)?;
                        this.emit_implicit_base_constructor(plan)?;
                    }
                }
                if early {
                    // The object exists now, and goes where the classes
                    // made above were waiting for it.
                    if let Some((display, DisplayAt::Local(slot))) = this.display.clone()
                        && let Some(field) = display.outside.this
                    {
                        this.stream.emit(Instruction::LoadLocal(slot));
                        this.push_this_value()?;
                        this.stream.emit(Instruction::StoreField(field));
                    }
                    if let Some((display, slot)) = owned.as_ref()
                        && let Some(field) = display.outside.this
                    {
                        this.stream.emit(Instruction::LoadLocal(*slot));
                        this.push_this_value()?;
                        this.stream.emit(Instruction::StoreField(field));
                    }
                } else {
                    this.emit_frame_setup(owned.as_ref())?;
                }
                for statement in &statements {
                    if matches!(
                        statement.kind,
                        BoundStatementKind::ConstructorInitializer { .. }
                    ) {
                        continue;
                    }
                    this.emit_statement(statement)?;
                }
            }
            MethodSource::StaticConstructor => this.emit_static_initializers(plan)?,
            // `this` and every argument, as they came, to the member that
            // answers for this one.
            MethodSource::Forwarding {
                target,
                implementation,
                ..
            } => {
                let target = match implementation {
                    Some(implementation) => {
                        let own = this.emitter.own_construction(plan.symbol);
                        this.method_token_on(*implementation, own.as_ref())?
                    }
                    None => *target,
                };
                let arguments = method.parameters.len();
                for position in 0..=arguments {
                    this.stream.emit(Instruction::LoadArgument(position as u16));
                }
                let pushes = usize::from(!matches!(method.return_type, Type::Void));
                this.stream
                    .call_effect(Instruction::Call(target), arguments + 1, pushes);
            }
            // The same, to a base class's member: through its slot where it
            // has one, so that what overrides it further down answers.
            MethodSource::InheritedForwarding {
                implementation,
                setter,
                through,
                ..
            } => {
                // A referenced class's property has symbols for its accessors,
                // which say what metadata says of each; this assembly's
                // accessors are rows planned beside the property.
                let accessor = setter.and_then(|setter| {
                    let property = this
                        .emitter
                        .compilation
                        .symbols()
                        .get(*implementation)
                        .as_property()?;
                    if setter {
                        property.setter
                    } else {
                        property.getter
                    }
                });
                let target = match setter {
                    None => this.method_token_on(*implementation, through.as_ref())?,
                    Some(setter) => {
                        let planned = if *setter {
                            &this.emitter.setters
                        } else {
                            &this.emitter.getters
                        };
                        match (planned.get(implementation).copied(), accessor) {
                            (Some(token), _) => token,
                            (None, Some(accessor)) => this.method_token(accessor)?,
                            (None, None) => {
                                return Err(EmitError::new(format!(
                                    "cannot reference an accessor of `{}`",
                                    this.emitter
                                        .compilation
                                        .symbols()
                                        .qualified_name(*implementation)
                                )));
                            }
                        }
                    }
                };
                let symbols = this.emitter.compilation.symbols();
                let mut modifiers = symbols.get(*implementation).modifiers;
                if let Some(accessor) = accessor {
                    modifiers.insert(symbols.get(accessor).modifiers);
                }
                let overridable = !modifiers.contains(Modifiers::SEALED)
                    && (modifiers.contains(Modifiers::VIRTUAL)
                        || modifiers.contains(Modifiers::ABSTRACT)
                        || modifiers.contains(Modifiers::OVERRIDE));
                let arguments = method.parameters.len();
                for position in 0..=arguments {
                    this.stream.emit(Instruction::LoadArgument(position as u16));
                }
                let pushes = usize::from(!matches!(method.return_type, Type::Void));
                let call = if overridable {
                    Instruction::CallVirtual(target)
                } else {
                    Instruction::Call(target)
                };
                this.stream.call_effect(call, arguments + 1, pushes);
            }
            // A written class constructor runs the field initializers first:
            // C# says they happen before its body, and there is only one
            // `.cctor` for both.
            MethodSource::Declared(_) if method.name == ".cctor" => {
                this.emit_static_initializers(plan)?;
                let statements = this.take_statements();
                for statement in &statements {
                    this.emit_statement(statement)?;
                }
            }
            MethodSource::RecordConstructor(constructor) => {
                this.emit_record_constructor(plan, *constructor)?;
            }
            MethodSource::RecordMember(method) => this.emit_record_member(plan, *method)?,
            MethodSource::RecordBaseEquals => this.emit_record_base_equals(plan)?,
            MethodSource::DisplayConstructor => {
                // A display class holds captures and nothing else; its
                // constructor only has to chain to `object`.
                let object = this.emitter.framework_member(
                    "System.Object",
                    ".ctor",
                    true,
                    &SigType::Primitive(ElementType::Void),
                    &[],
                );
                this.stream.emit(Instruction::LoadArgument(0));
                this.stream.call_effect(Instruction::Call(object), 1, 0);
            }
            MethodSource::SingletonStaticConstructor => {
                // `<>9 = new <>c();`
                let singleton = this
                    .emitter
                    .singleton_types
                    .get(&plan.token)
                    .copied()
                    .ok_or_else(|| EmitError::new("a `<>c` with no plan"))?;
                this.stream
                    .call_effect(Instruction::NewObject(singleton.constructor), 0, 1);
                this.stream
                    .emit(Instruction::StoreStaticField(singleton.instance));
            }
            MethodSource::AsyncStart(key) => this.emit_async_start(*key)?,
            MethodSource::AsyncConstructor => this.emit_async_constructor(),
            MethodSource::AsyncIteratorConstructor(key) => {
                this.emit_async_iterator_constructor(*key)?;
            }
            MethodSource::AsyncIteratorGetEnumerator(key) => {
                this.emit_async_iterator_get_enumerator(*key)?;
            }
            MethodSource::AsyncIteratorMoveNext(key) => {
                this.emit_async_iterator_move_next(*key)?;
            }
            MethodSource::AsyncIteratorCurrent(key) => this.emit_async_iterator_current(*key)?,
            MethodSource::AsyncIteratorPromise(key, call) => this.emit_promise_call(*key, *call)?,
            MethodSource::AsyncIteratorDispose(key) => this.emit_async_iterator_dispose(*key)?,
            MethodSource::AsyncSetStateMachine => this.stream.emit(Instruction::Ret),
            MethodSource::AsyncMain(main) => this.emit_async_main(*main)?,
            MethodSource::EventAccessor { event, add } => this.emit_event_accessor(*event, *add)?,
            MethodSource::AsyncMoveNext(_) => {
                let statements = this.take_statements();
                for statement in &statements {
                    this.emit_statement(statement)?;
                }
                this.end_async_move_next()?;
            }
            MethodSource::IteratorConstructor(owner) => this.emit_iterator_constructor(*owner)?,
            MethodSource::IteratorCurrent(owner, boxed) => {
                this.emit_iterator_current(*owner, *boxed)?;
            }
            MethodSource::IteratorGetEnumerator(owner, untyped) => {
                this.emit_iterator_get_enumerator(*owner, *untyped)?;
            }
            MethodSource::IteratorDispose(owner) => this.emit_iterator_dispose(*owner)?,
            MethodSource::IteratorMoveNext(_) => {
                let statements = this.take_statements();
                for statement in &statements {
                    this.emit_statement(statement)?;
                }
                this.end_iterator_move_next();
            }
            MethodSource::IteratorReset => this.emit_iterator_reset(),
            MethodSource::IteratorStart(owner) => this.emit_iterator_start(*owner)?,
            MethodSource::PropertyGetter {
                property,
                backing: true,
            } => this.emit_backing_field_read(plan, *property)?,
            MethodSource::PropertySetter { property } => {
                this.emit_backing_field_write(plan, *property)?;
            }
            MethodSource::Lambda { index, .. } => {
                // The lambda's parameters are locals of the member it was
                // written in, so its body reads them with `ldloc`. Copying the
                // arguments into those slots up front is the whole difference,
                // and the JIT elides it.
                let parameters = this
                    .body
                    .lambdas
                    .get(*index)
                    .map(|lambda| lambda.parameters.clone())
                    .unwrap_or_default();
                let base = u16::from(method.instance);
                for (position, local) in parameters.iter().enumerate() {
                    // A parameter an inner lambda captures lives in the
                    // class made above, and is written there.
                    this.begin_store(*local);
                    this.stream
                        .emit(Instruction::LoadArgument(position as u16 + base));
                    this.end_store(*local);
                }
                let statements = this.take_statements();
                for statement in &statements {
                    this.emit_statement(statement)?;
                }
            }
            _ => {
                let statements = this.take_statements();
                for statement in &statements {
                    this.emit_statement(statement)?;
                }
            }
        }

        if let Some((label, slot)) = this.exit {
            this.stream.mark(label);
            if let Some(slot) = slot {
                this.stream.emit(Instruction::LoadLocal(slot));
            }
            this.stream.emit(Instruction::Ret);
        }

        // The end of a method that returns a value is a place the language
        // proved nothing reaches — an exhaustive `switch` over a tuple with a
        // `return` in every case — and this backend's plainer reckoning
        // sometimes cannot. A `ret` there would have nothing to return and
        // the JIT would refuse the whole method; a throw is what an
        // unreachable place costs.
        if !matches!(method.return_type, Type::Void) && this.stream.end_depth() == Some(0) {
            let message = this
                .emitter
                .metadata
                .user_string("the end of a method that returns a value was reached");
            let constructor = this.emitter.not_implemented();
            this.stream.emit(Instruction::LoadString(message));
            this.stream
                .call_effect(Instruction::NewObject(constructor), 1, 1);
            this.stream.emit(Instruction::Throw);
        }
        let BodyEmitter {
            emitter,
            stream,
            locals,
            ..
        } = this;
        Ok(emitter.finish_body(stream, &locals))
    }

    // -- constructors ------------------------------------------------------

    /// The base constructor call for a constructor that wrote no `: base(...)`:
    /// the base may take arguments it fills itself, and then the constructor
    /// — written or not — still has to pass them.
    pub(crate) fn emit_implicit_base_constructor(
        &mut self,
        plan: &TypePlan,
    ) -> Result<(), EmitError> {
        let chained = self
            .emitter
            .implicit_base_initializer(plan.symbol)
            .and_then(|statement| match statement.kind {
                BoundStatementKind::ConstructorInitializer {
                    constructor: Some(constructor),
                    arguments,
                    ..
                } => Some((constructor, arguments)),
                _ => None,
            });
        match chained {
            Some((constructor, arguments)) => {
                self.emit_constructor_call(plan, Some(constructor), &arguments)
            }
            None => self.emit_base_constructor(plan),
        }
    }

    /// `ldarg.0; call <base>::.ctor()`, which every constructor needs and none
    /// of them writes.
    pub(crate) fn emit_base_constructor(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        // A value type has no base constructor to chain to: `ValueType` and
        // `Object` have one apiece and neither may be called, because there
        // is no object to call it on.
        if self.in_value_type {
            return Ok(());
        }
        let bases = self.emitter.binder.base_types_of(plan.symbol);
        let symbols = self.emitter.compilation.symbols();
        let base = bases.into_iter().find(|base| {
            base.symbol().is_some_and(|symbol| {
                matches!(
                    symbols.get(symbol).type_kind(),
                    Some(rustlyn_semantics::TypeKind::Class | rustlyn_semantics::TypeKind::Record)
                )
            })
        });

        let token = match base.as_ref().and_then(Type::symbol) {
            Some(symbol) if self.emitter.types.contains_key(&symbol) => {
                // A base in this assembly: find its parameterless constructor.
                let symbols = self.emitter.compilation.symbols();
                let constructor = symbols.lookup(symbol, ".ctor").iter().copied().find(|id| {
                    symbols
                        .get(*id)
                        .as_method()
                        .is_some_and(|method| method.parameters.is_empty())
                });
                let Some(constructor) = constructor else {
                    return Err(EmitError::new(format!(
                        "the base type `{}` has no parameterless constructor to chain to",
                        symbols.qualified_name(symbol)
                    )));
                };
                // `class Counter : Visitor<int, string>` chains to the
                // constructor of *that construction*: the open definition's
                // is not a method the runtime can call.
                let base = base.clone().unwrap_or_else(|| Type::named(symbol));
                self.method_token_on(constructor, Some(&base))?
            }
            Some(symbol) => {
                // `SymbolEqualityComparer : EqualityComparer<Symbol>` chains
                // to the constructor of *that construction* even where the
                // base is a framework type: the open definition's is not a
                // method the runtime can call.
                let base = base.clone().unwrap_or_else(|| Type::named(symbol));
                if self.emitter.is_constructed(&base) {
                    let signature =
                        method_signature(true, &SigType::Primitive(ElementType::Void), &[]);
                    self.emitter.member_of_type(&base, ".ctor", &signature)?
                } else {
                    let parent = self.emitter.referenced_type(symbol);
                    let signature =
                        method_signature(true, &SigType::Primitive(ElementType::Void), &[]);
                    self.emitter.references.member_ref_on(
                        &mut self.emitter.metadata,
                        parent,
                        ".ctor",
                        &signature,
                    )
                }
            }
            None => self.emitter.framework_member(
                "System.Object",
                ".ctor",
                true,
                &SigType::Primitive(ElementType::Void),
                &[],
            ),
        };

        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::Call(token), 1, 0);
        Ok(())
    }

    /// `ldarg.0; <arguments>; call <constructor>`, for a written `: base(...)`
    /// or `: this(...)`.
    /// The `: base(...)` the body was bound with, where it wrote one whose
    /// constructor was found.
    pub(crate) fn chained_constructor(&self) -> Option<(SymbolId, Vec<BoundExpression>)> {
        self.current_statements()
            .iter()
            .find_map(|statement| match &statement.kind {
                BoundStatementKind::ConstructorInitializer {
                    constructor: Some(constructor),
                    arguments,
                    chains_to_this: false,
                } => Some((*constructor, arguments.clone())),
                _ => None,
            })
    }

    pub(crate) fn emit_constructor_call(
        &mut self,
        plan: &TypePlan,
        constructor: Option<SymbolId>,
        arguments: &[BoundExpression],
    ) -> Result<(), EmitError> {
        let Some(constructor) = constructor else {
            // A struct's `: this()` is the constructor nobody wrote: the
            // fields start at zero, and zeroing them is the whole of it.
            let ty = self.emitter.binder.self_type(plan.symbol);
            if self.emitter.is_value_type(&ty) {
                let token = self.emitter.type_token(&ty)?;
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::InitObject(token));
                return Ok(());
            }
            return Err(EmitError::new(
                "no constructor was resolved for the constructor initializer",
            ));
        };
        self.stream.emit(Instruction::LoadArgument(0));
        for argument in arguments {
            self.emit_expression(argument, true)?;
        }
        // `: base(x)` where the base is a construction calls *that
        // construction's* constructor; the open definition's is not a method
        // the runtime can call.
        let owner = self
            .emitter
            .compilation
            .symbols()
            .get(constructor)
            .container
            .and_then(|owner| {
                let ty = self.emitter.binder.self_type(plan.symbol);
                self.emitter.binder.constructed_from(&ty, owner)
            });
        let token = self.method_token_on(constructor, owner.as_ref())?;
        self.stream
            .call_effect(Instruction::Call(token), arguments.len() + 1, 0);
        Ok(())
    }

    /// `this.<x>P = x` for each primary constructor parameter a member reads,
    /// before anything else runs: an initializer may already call a method
    /// that reads it.
    pub(crate) fn emit_parameter_captures(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let Some(owner) = self.owner else {
            return Ok(());
        };
        if symbols
            .get(plan.symbol)
            .as_named_type()
            .and_then(|detail| detail.primary_constructor)
            != Some(owner)
        {
            return Ok(());
        }
        let parameters = symbols
            .get(owner)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        for (position, parameter) in parameters.into_iter().enumerate() {
            let Some(field) = symbols
                .get(parameter)
                .as_parameter()
                .and_then(|detail| detail.captured)
            else {
                continue;
            };
            // Through the construction, as every field of a generic type is.
            let receiver = self.emitter.binder.self_type(plan.symbol);
            let token = self.field_token_on(field, Some(&receiver))?;
            self.stream.emit(Instruction::LoadArgument(0));
            self.load_parameter_value(parameter, position)?;
            self.stream.emit(Instruction::StoreField(token));
        }
        Ok(())
    }

    /// The value of parameter `position` of the method being written: an
    /// `in` one (`record R(in int P)`) is a reference, read through.
    pub(crate) fn load_parameter_value(
        &mut self,
        parameter: SymbolId,
        position: usize,
    ) -> Result<(), EmitError> {
        self.stream
            .emit(Instruction::LoadArgument(position as u16 + 1));
        let symbols = self.emitter.compilation.symbols();
        let by_reference = symbols
            .get(parameter)
            .as_parameter()
            .is_some_and(|detail| detail.ref_kind != RefKind::None);
        if by_reference {
            let ty = self.emitter.type_of(parameter);
            let kind = self.indirect_kind(&ty)?;
            self.stream.emit(Instruction::LoadIndirect(kind));
        }
        Ok(())
    }

    pub(crate) fn emit_instance_initializers(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        // A record's copy constructor, written or not, copies what the
        // initializers would have set; it runs none of them (Roslyn's
        // `IncludeFieldInitializersInBody`).
        if self.is_record_copy_constructor() {
            return Ok(());
        }
        self.emit_field_initializers(plan, false)
    }

    /// Whether the body being emitted is a record class's copy constructor:
    /// an instance constructor taking one of the record by value.
    fn is_record_copy_constructor(&self) -> bool {
        let Some(owner) = self.owner else {
            return false;
        };
        let symbols = self.emitter.compilation.symbols();
        let symbol = symbols.get(owner);
        let Some(detail) = symbol.as_method() else {
            return false;
        };
        let Some(record) = symbol.container else {
            return false;
        };
        symbol.name == ".ctor"
            && !symbol.modifiers.contains(Modifiers::STATIC)
            && symbols.get(record).type_kind() == Some(TypeKind::Record)
            && matches!(&detail.parameters[..], [parameter]
                if symbols.get(*parameter).as_parameter().is_some_and(|parameter| {
                    parameter.ref_kind == rustlyn_semantics::RefKind::None
                })
                    && self.emitter.type_of(*parameter).symbol() == Some(record))
    }

    fn emit_static_initializers(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        self.emit_field_initializers(plan, true)
    }

    fn emit_field_initializers(&mut self, plan: &TypePlan, statics: bool) -> Result<(), EmitError> {
        for field in plan.fields.clone() {
            let Some(symbol) = field.symbol else { continue };
            let detail = self.emitter.compilation.symbols().get(symbol);
            // A field with an initializer, or the property an automatic one
            // stands behind: `int X { get; } = 5;` has its 5 under the
            // property, and the field it writes has no symbol of its own.
            // A field-like event with an initializer stores it in its
            // field the same way.
            let written = detail.as_field().is_some_and(|f| f.has_initializer)
                || detail.kind == SymbolKind::Property
                || self.emitter.event_has_initializer(symbol);
            if !written {
                continue;
            }
            // A `const` has no storage to store into: its row is a literal
            // and its value is already in metadata. Writing to it produces a
            // `stsfld` the runtime refuses, and every read of it was folded
            // to the value anyway.
            if field.constant.is_some() {
                continue;
            }
            let is_static = detail.modifiers.contains(Modifiers::STATIC)
                || detail.modifiers.contains(Modifiers::CONST);
            if is_static != statics {
                continue;
            }
            let Some(body) = self.emitter.body_of(symbol) else {
                continue;
            };
            let Some(value) = first_returned_value(&body) else {
                continue;
            };
            // The initializer is the field's body, and a lambda in it was
            // planned under the field: while it is being emitted, the field
            // is what owns what is written there.
            // Its locals — `out var` and patterns declare them — are slots
            // of the constructor it runs in, after the constructor's own.
            let base = self.locals.len() as u16;
            let mut by_ref = Vec::with_capacity(body.locals.len());
            // A local function's own `T` in a lambda of the initializer is not
            // nameable from the constructor, as in any other body: the slot is
            // not one it touches.
            let nameable: Vec<SymbolId> = self.emitter.display_generics.to_vec();
            for local in &body.locals {
                let signature = if foreign_parameter(
                    self.emitter.compilation.symbols(),
                    &local.ty,
                    &nameable,
                ) {
                    SigType::Primitive(ElementType::Object)
                } else {
                    self.emitter.sig_type(&local.ty)?
                };
                self.locals.push(if local.by_ref {
                    SigType::ByRef(Box::new(signature))
                } else {
                    signature
                });
                self.local_types.push(local.ty.clone());
                by_ref.push(local.by_ref);
            }
            let outer_base = std::mem::replace(&mut self.local_base, base);
            let outer_by_ref = std::mem::replace(&mut self.by_ref_locals, by_ref);
            let outer = std::mem::replace(&mut self.body, body);
            let outer_statements = std::mem::replace(&mut self.statements, Statements::Body);
            let outer_owner = self.owner.replace(symbol);
            // A lambda capturing a variable the initializer declares has a
            // class of the initializer's own, made here and nowhere else.
            let own_display = self.emitter.displays.get(&symbol).cloned().map(|display| {
                let slot = self.locals.len() as u16;
                self.locals.push(display.sig.clone());
                self.local_types.push(Type::Error);
                (display, DisplayAt::Local(slot))
            });
            let has_own_display = own_display.is_some();
            let outer_display = if has_own_display {
                Some(std::mem::replace(&mut self.display, own_display))
            } else {
                None
            };
            let outer_captures = if has_own_display {
                let setup = std::mem::replace(&mut self.setup_captures, 0);
                Some((std::mem::take(&mut self.captures), setup))
            } else {
                None
            };
            if has_own_display {
                self.emit_display_prologue()?;
            }
            // A field of a generic type is named through the construction
            // wherever it is reached, and an initializer is no exception: a
            // `stsfld` on the definition and a `ldsfld` through `Box<!0>` are
            // two different statics to the runtime, so the one the
            // initializer writes would never be the one anything reads.
            let receiver = self.emitter.binder.self_type(plan.symbol);
            let token = self.field_token_on(symbol, Some(&receiver))?;
            if !statics {
                self.hoist_stackallocs_in(&value, true)?;
                self.stream.emit(Instruction::LoadArgument(0));
            }
            self.emit_expression(&value, true)?;
            self.stream.emit(if statics {
                Instruction::StoreStaticField(token)
            } else {
                Instruction::StoreField(token)
            });
            self.body = outer;
            self.statements = outer_statements;
            self.owner = outer_owner;
            self.local_base = outer_base;
            self.by_ref_locals = outer_by_ref;
            if let Some(display) = outer_display {
                self.display = display;
            }
            if let Some((captures, setup)) = outer_captures {
                self.captures = captures;
                self.setup_captures = setup;
            }
        }
        Ok(())
    }

    /// A local slot of a type the body did not declare, for a synthesised
    /// member that needs one.
    pub(crate) fn add_local(&mut self, ty: &Type) -> Result<u16, EmitError> {
        self.temporary(ty)
    }

    pub(crate) fn backing_field(
        &mut self,
        plan: &TypePlan,
        property: SymbolId,
    ) -> Result<Token, EmitError> {
        // `get; set { field = value; }` (C# 14) reads the field the binder
        // declared for `field`, which is a field of the type like any other.
        let declared = self
            .emitter
            .compilation
            .symbols()
            .get(property)
            .as_property()
            .and_then(|detail| detail.backing_field);
        let field = match declared {
            Some(field) if !self.emitter.fields.contains_key(&property) => field,
            _ => property,
        };
        if !self.emitter.fields.contains_key(&field) {
            return Err(EmitError::new(format!(
                "the property `{}` has no backing field",
                self.emitter
                    .compilation
                    .symbols()
                    .qualified_name(plan.symbol)
            )));
        }
        // The field of a generic type is named through the construction
        // wherever it is reached — the initializer writes `Holder<!0>`'s, and
        // the accessor has to read the same one.
        let receiver = self.emitter.binder.self_type(plan.symbol);
        self.field_token_on(field, Some(&receiver))
    }

    fn emit_backing_field_read(
        &mut self,
        plan: &TypePlan,
        property: SymbolId,
    ) -> Result<(), EmitError> {
        let token = self.backing_field(plan, property)?;
        if self.instance {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(token));
        } else {
            self.stream.emit(Instruction::LoadStaticField(token));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    fn emit_backing_field_write(
        &mut self,
        plan: &TypePlan,
        property: SymbolId,
    ) -> Result<(), EmitError> {
        let token = self.backing_field(plan, property)?;
        if self.instance {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.emit(Instruction::StoreField(token));
        } else {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::StoreStaticField(token));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    // -- statements --------------------------------------------------------

    fn emit_statement(&mut self, statement: &BoundStatement) -> Result<(), EmitError> {
        // A `stackalloc` inside the statement is made first, the operand of
        // an `await` included: `localloc` wants nothing else on the stack.
        self.hoist_stackallocs(statement)?;
        // In a machine's `MoveNext`, a statement that is an `await` is a
        // place the machine can stop at.
        if self.emit_await_statement(statement)? {
            return Ok(());
        }
        match &statement.kind {
            BoundStatementKind::Block(statements) => {
                for inner in statements {
                    self.emit_statement(inner)?;
                }
                self.clear_hoisted(statements)?;
            }
            BoundStatementKind::Empty => {}
            BoundStatementKind::LocalDeclaration { local, initializer } => {
                if let Some(value) = initializer {
                    // A captured variable is not a local any more: even its
                    // declaration writes the display class's field.
                    match self.captured_local(*local) {
                        // `localloc` wants nothing else on the stack, so a
                        // `stackalloc` is made before the class holding the
                        // variable is pushed.
                        Some(capture) if contains_stackalloc(value) => {
                            let slot = self.temporary(&value.ty)?;
                            self.emit_expression(value, true)?;
                            self.stream.emit(Instruction::StoreLocal(slot));
                            self.push_holder(capture.holder);
                            self.stream.emit(Instruction::LoadLocal(slot));
                            self.stream.emit(Instruction::StoreField(capture.token));
                        }
                        Some(capture) => {
                            self.push_holder(capture.holder);
                            self.emit_expression(value, true)?;
                            self.stream.emit(Instruction::StoreField(capture.token));
                        }
                        // A `ref` local is given a place, not a value: what
                        // goes in the slot is the address.
                        None if self.is_by_ref_local(*local) => {
                            match &value.kind {
                                BoundExpressionKind::RefArgument { operand, .. } => {
                                    self.emit_reference(operand)?;
                                }
                                _ => self.emit_reference(value)?,
                            }
                            self.stream.emit(Instruction::StoreLocal(self.slot(local)));
                        }
                        None => {
                            self.emit_expression(value, true)?;
                            self.stream.emit(Instruction::StoreLocal(self.slot(local)));
                        }
                    }
                }
            }
            BoundStatementKind::Expression(value) => self.emit_expression(value, false)?,
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                let otherwise = self.stream.label();
                self.emit_branch_if_false(condition, otherwise)?;
                self.emit_statement(consequence)?;
                match alternative {
                    Some(alternative) => {
                        let end = self.stream.label();
                        // `if (c) return a; else return b;` has nothing to
                        // jump past the `else` from, and a `ret` after the
                        // whole thing would have nothing on the stack.
                        if self.stream.end_reachable() {
                            self.stream.emit(Instruction::Branch(end));
                        }
                        self.stream.mark(otherwise);
                        self.emit_statement(alternative)?;
                        self.stream.mark(end);
                    }
                    None => self.stream.mark(otherwise),
                }
            }
            BoundStatementKind::While { condition, body } => {
                let head = self.stream.label();
                let end = self.stream.label();
                self.stream.mark(head);
                // The condition's variables are fresh each time round, as
                // the body's are: the class is made before the condition.
                let scope = self.enter_scope(statement.span)?;
                self.emit_branch_if_false(condition, end)?;
                self.enter_loop(end, head);
                self.emit_statement(body)?;
                self.leave_scope(scope);
                self.leave_loop();
                // A body that always returns or throws has no way back up.
                if self.stream.end_reachable() {
                    self.stream.emit(Instruction::Branch(head));
                }
                self.stream.mark(end);
            }
            BoundStatementKind::DoWhile { body, condition } => {
                let head = self.stream.label();
                let again = self.stream.label();
                let end = self.stream.label();
                self.stream.mark(head);
                self.enter_loop(end, again);
                let scope = self.enter_scope(statement.span)?;
                self.emit_statement(body)?;
                self.leave_loop();
                self.stream.mark(again);
                self.emit_branch_if_true(condition, head)?;
                self.leave_scope(scope);
                self.stream.mark(end);
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                for initializer in initializers {
                    self.emit_statement(initializer)?;
                }
                let head = self.stream.label();
                let step = self.stream.label();
                let end = self.stream.label();
                self.stream.mark(head);
                // What the condition and the incrementors declare is fresh
                // each time round, as the body's variables are.
                let scope = match crate::emitter::loop_scope(statement) {
                    Some(span) => self.enter_scope(span)?,
                    None => false,
                };
                if let Some(condition) = condition {
                    self.emit_branch_if_false(condition, end)?;
                }
                self.enter_loop(end, step);
                self.emit_statement(body)?;
                self.leave_loop();
                self.stream.mark(step);
                for incrementor in incrementors {
                    self.emit_expression(incrementor, false)?;
                }
                self.leave_scope(scope);
                self.stream.emit(Instruction::Branch(head));
                self.stream.mark(end);
            }
            BoundStatementKind::ForEach {
                local,
                collection,
                body,
                enumeration,
                walk,
                dimensions,
            } => match (enumeration, walk) {
                (Some(enumeration), _) => {
                    self.emit_enumeration(*local, collection, body, enumeration, statement.span)?
                }
                (None, Some((array, _))) if !dimensions.is_empty() => {
                    self.emit_foreach_dimensions(
                        *local,
                        collection,
                        body,
                        *array,
                        dimensions,
                        statement.span,
                    )?;
                }
                (None, Some((array, index))) => {
                    self.emit_foreach(*local, collection, body, *array, *index, statement.span)?;
                }
                (None, None) => {
                    return Err(EmitError::new(
                        "cannot emit `foreach` over anything but an array yet",
                    ));
                }
            },
            BoundStatementKind::YieldReturn(value) if self.async_run.is_some() => {
                self.emit_async_yield_return(value)?;
            }
            BoundStatementKind::YieldReturn(value) => self.emit_yield_return(value)?,
            BoundStatementKind::YieldBreak => self.emit_yield_break(),
            // A `return;` in an iterator says the same thing `yield break`
            // does: there is nothing more.
            BoundStatementKind::Return(None) if self.iterator.is_some() => self.emit_yield_break(),
            BoundStatementKind::Return(value) => match self.exit {
                // A method with a `finally` has one exit, because `ret` may
                // not run from inside a protected region: the value is parked
                // and the region left, and the real `ret` waits at the end.
                Some((label, slot)) => {
                    if let Some(value) = value {
                        self.emit_returned(value)?;
                        if let Some(slot) = slot {
                            self.stream.emit(Instruction::StoreLocal(slot));
                        }
                    }
                    self.emit_jump(label, 0);
                }
                None => {
                    if let Some(value) = value {
                        self.emit_returned(value)?;
                    }
                    self.stream.emit(Instruction::Ret);
                }
            },
            // A label is a place in the body that a `goto` anywhere in it can
            // jump to, forwards or back. Both sides ask for the same label by
            // name, and whichever comes first is the one that makes it.
            BoundStatementKind::Label(name) => {
                let label = self.named_label(name);
                self.stream.mark(label);
            }
            BoundStatementKind::Goto(name) => {
                let label = self.named_label(name);
                // Leaving a `try` is a `leave`, exactly as `break` out of one
                // is: a label outside the region cannot be branched to.
                self.emit_jump(label, 0);
            }
            BoundStatementKind::Break(outward) => {
                let (target, depth) = *self
                    .breaks
                    .iter()
                    .rev()
                    .nth(*outward)
                    .ok_or_else(|| EmitError::new("`break` outside a loop or `switch`"))?;
                self.emit_jump(target, depth);
            }
            BoundStatementKind::Continue(outward) => {
                let (target, depth) = *self
                    .continues
                    .iter()
                    .rev()
                    .nth(*outward)
                    .ok_or_else(|| EmitError::new("`continue` outside a loop"))?;
                self.emit_jump(target, depth);
            }
            BoundStatementKind::GotoCase(value) => {
                let targets = self
                    .cases
                    .last()
                    .ok_or_else(|| EmitError::new("`goto case` outside a `switch`"))?;
                let target = match value {
                    Some(value) => targets
                        .values
                        .iter()
                        .find(|(key, _)| key == value)
                        .map(|(_, label)| *label),
                    None => targets.default,
                };
                let depth = targets.depth;
                let target = target.ok_or_else(|| {
                    EmitError::new("`goto case` names a label this `switch` does not have")
                })?;
                self.emit_jump(target, depth);
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => self.emit_switch_statement(governing, sections)?,
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => self.emit_try(body, catches, finally.as_deref())?,
            BoundStatementKind::Using { resources, body } => {
                self.emit_using(resources, body)?;
            }
            BoundStatementKind::Lock {
                value,
                held,
                taken,
                body,
            } => {
                self.emit_lock(value, *held, *taken, body)?;
            }
            BoundStatementKind::Fixed { declarations, body } => {
                self.emit_fixed(declarations, body)?;
            }
            BoundStatementKind::Throw(Some(value)) => {
                self.emit_expression(value, true)?;
                self.stream.emit(Instruction::Throw);
            }
            // A bare `throw;` in a `catch`: the exception carries on with the
            // stack trace it already had, which `throw e;` would throw away.
            BoundStatementKind::Throw(None) => {
                self.stream.emit(Instruction::Rethrow);
            }
            BoundStatementKind::ConstructorInitializer { .. } => {
                return Err(EmitError::new(
                    "a constructor initializer outside a constructor",
                ));
            }
            BoundStatementKind::Unsupported(kind) => {
                return Err(EmitError::new(format!("cannot emit `{kind:?}` yet")));
            }
        }
        Ok(())
    }

    /// `foreach` over an array, lowered to the index loop it is.
    fn emit_foreach(
        &mut self,
        local: LocalId,
        collection: &BoundExpression,
        body: &BoundStatement,
        array: LocalId,
        index: LocalId,
        scope_span: TextSpan,
    ) -> Result<(), EmitError> {
        let Type::Array { element, .. } = collection.ty.clone() else {
            return Err(EmitError::new(
                "cannot emit `foreach` over anything but an array yet",
            ));
        };
        let element_token = self.emitter.type_token(&element)?;

        self.begin_store(array);
        self.emit_expression(collection, true)?;
        self.end_store(array);
        self.begin_store(index);
        self.stream.emit(Instruction::LoadInt32(0));
        self.end_store(index);

        let head = self.stream.label();
        let step = self.stream.label();
        let end = self.stream.label();
        self.stream.mark(head);
        self.load_local(index);
        self.load_local(array);
        self.stream.emit(Instruction::LoadLength);
        self.stream.emit(Instruction::ConvertI4);
        self.stream.emit(Instruction::CompareLess);
        self.stream.emit(Instruction::BranchIfFalse(end));

        let scope = self.enter_scope(scope_span)?;
        self.begin_store(local);
        self.load_local(array);
        self.load_local(index);
        self.load_element(&element, element_token);
        self.end_store(local);

        self.enter_loop(end, step);
        self.emit_statement(body)?;
        self.leave_loop();
        self.leave_scope(scope);

        self.stream.mark(step);
        self.begin_store(index);
        self.load_local(index);
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::Add);
        self.end_store(index);
        self.stream.emit(Instruction::Branch(head));
        self.stream.mark(end);
        Ok(())
    }

    /// `foreach` over an array of more than one dimension, lowered as
    /// Roslyn lowers it: the upper bound of every dimension read first, then
    /// a loop per dimension from its lower bound, the innermost reading the
    /// element with the array's `Get`.
    fn emit_foreach_dimensions(
        &mut self,
        local: LocalId,
        collection: &BoundExpression,
        body: &BoundStatement,
        array: LocalId,
        dimensions: &[(LocalId, LocalId)],
        scope_span: TextSpan,
    ) -> Result<(), EmitError> {
        let Type::Array { element, .. } = self.emitter.completed(&collection.ty) else {
            return Err(EmitError::new("a multi-dimensional walk over no array"));
        };
        let int = SigType::Primitive(ElementType::I4);
        let upper_bound = self.emitter.framework_member(
            "System.Array",
            "GetUpperBound",
            true,
            &int,
            std::slice::from_ref(&int),
        );
        let lower_bound = self.emitter.framework_member(
            "System.Array",
            "GetLowerBound",
            true,
            &int,
            std::slice::from_ref(&int),
        );
        let get = self.array_member(collection, ArrayMember::Get, &element)?;

        self.begin_store(array);
        self.emit_expression(collection, true)?;
        self.end_store(array);
        for (dimension, (_, upper)) in dimensions.iter().enumerate() {
            self.begin_store(*upper);
            self.load_local(array);
            self.stream.emit(Instruction::LoadInt32(dimension as i32));
            self.stream
                .call_effect(Instruction::CallVirtual(upper_bound), 2, 1);
            self.end_store(*upper);
        }
        let end = self.stream.label();
        // Each dimension's loop: where it tests, and where it steps.
        let mut heads = Vec::new();
        for (dimension, (index, upper)) in dimensions.iter().enumerate() {
            self.begin_store(*index);
            self.load_local(array);
            self.stream.emit(Instruction::LoadInt32(dimension as i32));
            self.stream
                .call_effect(Instruction::CallVirtual(lower_bound), 2, 1);
            self.end_store(*index);
            let head = self.stream.label();
            let step = self.stream.label();
            // The test of an outer loop failing ends the loop around it,
            // which for the outermost is the end of the walk.
            let done = heads.last().map_or(end, |(_, outer_step, _)| *outer_step);
            self.stream.mark(head);
            self.load_local(*index);
            self.load_local(*upper);
            self.stream.emit(Instruction::CompareGreater);
            self.stream.emit(Instruction::BranchIfTrue(done));
            heads.push((head, step, *index));
        }

        let innermost_step = heads.last().map_or(end, |(_, step, _)| *step);
        let scope = self.enter_scope(scope_span)?;
        self.begin_store(local);
        self.load_local(array);
        for (index, _) in dimensions {
            self.load_local(*index);
        }
        self.stream
            .call_effect(Instruction::Call(get), dimensions.len() + 1, 1);
        self.convert_iterated(&element, local)?;
        self.end_store(local);
        self.enter_loop(end, innermost_step);
        self.emit_statement(body)?;
        self.leave_loop();
        self.leave_scope(scope);

        // Stepping a dimension is followed by its test; one that is done
        // steps the dimension around it.
        for (head, step, index) in heads.into_iter().rev() {
            self.stream.mark(step);
            self.begin_store(index);
            self.load_local(index);
            self.stream.emit(Instruction::LoadInt32(1));
            self.stream.emit(Instruction::Add);
            self.end_store(index);
            self.stream.emit(Instruction::Branch(head));
        }
        self.stream.mark(end);
        Ok(())
    }

    /// Pushes the enumerator a `foreach` is walking with, as what the call
    /// on it needs: a reference, or the address of the struct it is.
    fn push_enumerator(&mut self, local: LocalId, held: Option<Capture>, by_value: bool) {
        match held {
            Some(capture) => {
                self.push_holder(capture.holder);
                self.stream.emit(if by_value {
                    Instruction::LoadFieldAddress(capture.token)
                } else {
                    Instruction::LoadField(capture.token)
                });
            }
            None => {
                let slot = self.slot(local);
                self.stream.emit(if by_value {
                    Instruction::LoadLocalAddress(slot)
                } else {
                    Instruction::LoadLocal(slot)
                });
            }
        }
    }

    /// Reads a declared local, wherever it turned out to live.
    pub(crate) fn load_local(&mut self, local: LocalId) {
        match self.captured_local(local) {
            Some(capture) => {
                self.push_holder(capture.holder);
                self.stream.emit(Instruction::LoadField(capture.token));
            }
            None => self.stream.emit(Instruction::LoadLocal(self.slot(local))),
        }
    }

    /// Pushes the address of a local: of its slot, or of the field a display
    /// class or a state machine keeps it in.
    pub(crate) fn load_local_address(&mut self, local: LocalId) {
        match self.captured_local(local) {
            Some(capture) => {
                self.push_holder(capture.holder);
                self.stream
                    .emit(Instruction::LoadFieldAddress(capture.token));
            }
            None => self
                .stream
                .emit(Instruction::LoadLocalAddress(self.slot(local))),
        }
    }

    /// Pushes whatever has to go under the value a local is about to be given.
    ///
    /// A slot takes nothing; a field takes the object it belongs to, and it
    /// has to be on the stack before the value is.
    pub(crate) fn begin_store(&mut self, local: LocalId) {
        if let Some(capture) = self.captured_local(local) {
            self.push_holder(capture.holder);
        }
    }

    /// Stores into it, the value being on the stack.
    pub(crate) fn end_store(&mut self, local: LocalId) {
        match self.captured_local(local) {
            Some(capture) => self.stream.emit(Instruction::StoreField(capture.token)),
            None => self.stream.emit(Instruction::StoreLocal(self.slot(local))),
        }
    }

    /// `foreach` over anything that is not an array, which is a `while` around
    /// an enumerator with a `finally` that disposes it.
    ///
    /// The `finally` is not decoration: the loop can be left by `break`, by
    /// `return` or by an exception, and C# promises the enumerator is disposed
    /// however it goes.
    fn emit_enumeration(
        &mut self,
        local: LocalId,
        collection: &BoundExpression,
        body: &BoundStatement,
        enumeration: &BoundEnumeration,
        scope_span: TextSpan,
    ) -> Result<(), EmitError> {
        let slot = self.slot(enumeration.enumerator);
        let get_enumerator = match &enumeration.extension {
            Some(type_arguments) => {
                let token = self.method_token_on(enumeration.get_enumerator, None)?;
                self.instantiated(token, type_arguments)?
            }
            None => self.method_token_on(
                enumeration.get_enumerator,
                Some(&enumeration.collection_type),
            )?,
        };
        let move_next =
            self.method_token_on(enumeration.move_next, Some(&enumeration.move_next_type))?;
        let current = self.emitter.property_accessor(
            enumeration.current,
            Some(&enumeration.current_type),
            false,
        )?;

        // `List<T>.GetEnumerator` gives back a *struct*, and the whole point
        // of that struct is that iterating a list allocates nothing. A value
        // type has no vtable to dispatch through and no reference to load: its
        // methods are called on its address, directly.
        // An enumerator of a type parameter — `allows ref struct` makes one
        // possible — is called through `constrained.` on its address, which
        // is right whatever the type argument turns out to be.
        let constrained = match &enumeration.enumerator_type {
            Type::TypeParameter(_) => Some(self.emitter.type_token(&enumeration.enumerator_type)?),
            _ => None,
        };
        let by_value =
            constrained.is_some() || self.emitter.is_value_type(&enumeration.enumerator_type);
        let held = self.captured_local(enumeration.enumerator);
        let invoke = |token| {
            if by_value && constrained.is_none() {
                Instruction::Call(token)
            } else {
                Instruction::CallVirtual(token)
            }
        };

        // The collection can be a struct too — `foreach` over an
        // `ImmutableArray<T>` is the ordinary case — and a struct's method is
        // called on its address rather than dispatched through a vtable it
        // does not have.
        // An extension `GetEnumerator` takes the collection as its argument,
        // by value; a member is called on it.
        // A `this in C` or `this ref C` takes the collection's address.
        let this_by_reference = enumeration.extension.is_some()
            && self
                .emitter
                .compilation
                .symbols()
                .get(enumeration.get_enumerator)
                .as_method()
                .and_then(|detail| detail.parameters.first().copied())
                .and_then(|first| {
                    self.emitter
                        .compilation
                        .symbols()
                        .get(first)
                        .as_parameter()
                        .map(|detail| detail.ref_kind)
                })
                .is_some_and(|kind| kind != rustlyn_semantics::RefKind::None);
        if enumeration.extension.is_some() {
            if this_by_reference {
                self.emit_reference(collection)?;
            } else {
                self.emit_expression(collection, true)?;
                if !matches!(enumeration.extension_this, Type::Void) {
                    self.emit_value_conversion(&collection.ty, &enumeration.extension_this)?;
                }
            }
            for argument in &enumeration.extension_arguments {
                self.emit_expression(argument, true)?;
            }
            self.stream.call_effect(
                Instruction::Call(get_enumerator),
                1 + enumeration.extension_arguments.len(),
                1,
            );
        } else {
            self.emit_member_receiver(collection, enumeration.get_enumerator)?;
            let call =
                self.receiver_call(collection, enumeration.get_enumerator, get_enumerator)?;
            self.stream.call_effect(call, 1, 1);
        }
        // A `GetEnumerator` that returns a reference hands over the variable;
        // the loop walks a copy of what is there.
        if matches!(
            self.emitter.type_of(enumeration.get_enumerator),
            Type::ByRef(_)
        ) {
            let kind = self.indirect_kind(&enumeration.enumerator_type)?;
            self.stream.emit(Instruction::LoadIndirect(kind));
        }
        match held {
            // The enumerator has to be stored before anything is pushed for
            // the object it belongs to, so it goes into a slot first and is
            // copied across.
            Some(capture) => {
                let parked = self.temporary(&enumeration.enumerator_type)?;
                self.stream.emit(Instruction::StoreLocal(parked));
                self.push_holder(capture.holder);
                self.stream.emit(Instruction::LoadLocal(parked));
                self.stream.emit(Instruction::StoreField(capture.token));
            }
            None => self.stream.emit(Instruction::StoreLocal(slot)),
        }

        let end = self.stream.label();
        let try_start = self.stream.label();
        let try_end = self.stream.label();
        let disposes = enumeration.dispose.is_some();
        if disposes {
            self.protected += 1;
            self.emit_region_entry(&[try_start])?;
        }

        let head = self.stream.label();
        let step = self.stream.label();
        let done = self.stream.label();
        self.stream.mark(head);
        self.push_enumerator(enumeration.enumerator, held, by_value);
        if let Some(ty) = constrained {
            self.stream.emit(Instruction::Constrained(ty));
        }
        self.stream.call_effect(invoke(move_next), 1, 1);
        self.stream.emit(Instruction::BranchIfFalse(done));

        let scope = self.enter_scope(scope_span)?;
        self.begin_store(local);
        self.push_enumerator(enumeration.enumerator, held, by_value);
        if let Some(ty) = constrained {
            self.stream.emit(Instruction::Constrained(ty));
        }
        self.stream.call_effect(invoke(current), 1, 1);
        // `foreach (ref var x in c)` keeps the reference `Current` hands back.
        if !self.is_by_ref_local(local) {
            self.read_through_reference(enumeration.current, &enumeration.element_type)?;
            self.convert_iterated(&enumeration.element_type.clone(), local)?;
        }
        self.end_store(local);

        // `continue` goes back to `MoveNext`, which is the loop head: there is
        // no step to run in between.
        self.enter_loop(done, step);
        self.emit_statement(body)?;
        self.leave_loop();
        self.leave_scope(scope);
        self.stream.mark(step);
        self.stream.emit(Instruction::Branch(head));
        self.stream.mark(done);

        if disposes {
            self.emit_region_exit();
            self.protected -= 1;
            self.stream.emit(Instruction::Leave(end));
            self.stream.mark(try_end);

            let handler_start = self.stream.label();
            let handler_end = self.stream.label();
            self.stream.mark(handler_start);
            let suspended = self.begin_guarded_finally();
            self.emit_dispose_of(slot, held, enumeration)?;
            self.end_guarded_finally(suspended);
            self.stream.emit(Instruction::EndFinally);
            self.stream.mark(handler_end);
            self.stream.region(ExceptionRegion {
                kind: HandlerKind::Finally,
                try_start,
                try_end,
                handler_start,
                handler_end,
            });
        }
        self.stream.mark(end);
        Ok(())
    }

    /// Brings an element just read off a collection to the type the loop
    /// variable was declared with: `foreach (INamedTypeDefinition t in
    /// typeDefs)` over `ITypeDefinition`s casts each one (§13.9.5), and
    /// `foreach (int n in objects)` unboxes.
    fn convert_iterated(&mut self, from: &Type, local: LocalId) -> Result<(), EmitError> {
        let to = self.local_types[local.0 as usize].clone();
        if to == *from || to.is_error() || from.is_error() {
            return Ok(());
        }
        let symbols = self.emitter.compilation.symbols();
        let is_reference = |ty: &Type| {
            !matches!(ty, Type::TypeParameter(_))
                && (ty.is_reference_type(symbols) || matches!(ty, Type::Array { .. }))
        };
        match (is_reference(from), is_reference(&to)) {
            (true, true) => {
                if !self.emitter.binder.converts_implicitly(from, &to) {
                    let token = self.emitter.type_token(&to)?;
                    self.stream.emit(Instruction::CastClass(token));
                }
            }
            (true, false) => {
                let token = self.emitter.type_token(&to)?;
                self.stream.emit(Instruction::UnboxAny(token));
            }
            (false, true) => self.box_if_needed(from)?,
            (false, false) => {
                if self.numeric_kind(from).is_some() && self.numeric_kind(&to).is_some() {
                    self.convert_number_from(from, &to)?;
                } else if matches!(from, Type::TypeParameter(_))
                    || matches!(to, Type::TypeParameter(_))
                {
                    self.box_if_needed(from)?;
                    let token = self.emitter.type_token(&to)?;
                    self.stream.emit(Instruction::UnboxAny(token));
                }
            }
        }
        Ok(())
    }

    /// Disposes an enumerator, skipping one that was never made. `held` is
    /// the field it lives in where it is not in its slot: a machine keeps an
    /// enumerator a `yield` or an `await` comes between the uses of.
    fn emit_dispose_of(
        &mut self,
        slot: u16,
        held: Option<Capture>,
        enumeration: &BoundEnumeration,
    ) -> Result<(), EmitError> {
        let (Some(dispose), Some(through)) = (enumeration.dispose, &enumeration.dispose_type)
        else {
            return Ok(());
        };
        let token = self.method_token_on(dispose, Some(through))?;
        let value_type = self.emitter.is_value_type(&enumeration.enumerator_type);
        let skip = self.stream.label();
        if value_type {
            // A struct enumerator is never null and is called on its address
            // (in the machine's field, where one keeps it); a `ref struct`'s
            // own `Dispose` is given the defaults it takes.
            match held {
                Some(capture) => {
                    self.push_holder(capture.holder);
                    self.stream
                        .emit(Instruction::LoadFieldAddress(capture.token));
                }
                None => self.stream.emit(Instruction::LoadLocalAddress(slot)),
            }
            if !enumeration.dispose_arguments.is_empty() {
                for argument in &enumeration.dispose_arguments {
                    self.emit_expression(argument, true)?;
                }
                self.stream.call_effect(
                    Instruction::Call(token),
                    1 + enumeration.dispose_arguments.len(),
                    0,
                );
                return Ok(());
            }
            self.emit_struct_dispose(dispose, token, &enumeration.enumerator_type)?;
            return Ok(());
        }
        // One read out of its field, and the slot for it read from then on.
        let slot = match held {
            Some(capture) => {
                let parked = self.temporary(&enumeration.enumerator_type)?;
                self.push_holder(capture.holder);
                self.stream.emit(Instruction::LoadField(capture.token));
                self.stream.emit(Instruction::StoreLocal(parked));
                parked
            }
            None => slot,
        };
        if enumeration.dispose_checked {
            // `(enumerator as IDisposable)?.Dispose()`: the type did not
            // promise one, the value may have one anyway.
            let disposable = self.emitter.type_token(through)?;
            let held = self.temporary(through)?;
            self.stream.emit(Instruction::LoadLocal(slot));
            self.stream.emit(Instruction::IsInstance(disposable));
            self.stream.emit(Instruction::StoreLocal(held));
            self.stream.emit(Instruction::LoadLocal(held));
            self.stream.emit(Instruction::BranchIfFalse(skip));
            self.stream.emit(Instruction::LoadLocal(held));
            self.stream
                .call_effect(Instruction::CallVirtual(token), 1, 0);
            self.stream.mark(skip);
            return Ok(());
        }
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream.emit(Instruction::BranchIfFalse(skip));
        self.stream.emit(Instruction::LoadLocal(slot));
        self.stream
            .call_effect(Instruction::CallVirtual(token), 1, 0);
        self.stream.mark(skip);
        Ok(())
    }

    /// Branches when a condition is false, folding the comparison into the
    /// branch where it can.
    fn emit_branch_if_false(
        &mut self,
        condition: &BoundExpression,
        target: Label,
    ) -> Result<(), EmitError> {
        // `while (true)` tests nothing: a branch on a constant would make
        // the verifier see a way out of the loop that is not there, and
        // want a return past it.
        match constant_condition(condition) {
            Some(true) => return Ok(()),
            Some(false) => {
                self.stream.emit(Instruction::Branch(target));
                return Ok(());
            }
            None => {}
        }
        self.emit_expression(condition, true)?;
        self.stream.emit(Instruction::BranchIfFalse(target));
        Ok(())
    }

    fn emit_branch_if_true(
        &mut self,
        condition: &BoundExpression,
        target: Label,
    ) -> Result<(), EmitError> {
        match constant_condition(condition) {
            Some(false) => return Ok(()),
            Some(true) => {
                self.stream.emit(Instruction::Branch(target));
                return Ok(());
            }
            None => {}
        }
        self.emit_expression(condition, true)?;
        self.stream.emit(Instruction::BranchIfTrue(target));
        Ok(())
    }

    fn enter_loop(&mut self, on_break: Label, on_continue: Label) {
        self.breaks.push((on_break, self.protected));
        self.continues.push((on_continue, self.protected));
    }

    fn leave_loop(&mut self) {
        self.breaks.pop();
        self.continues.pop();
    }

    /// Jumps to `target`, which sits at protected-region depth `depth`.
    ///
    /// A plain branch may not cross out of a `try`; `leave` is the instruction
    /// that may, and it empties the evaluation stack on the way.
    /// Boxes what is on the stack where it is not already a reference.
    fn box_if_a_value(&mut self, ty: &Type) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        // A type parameter is boxed whatever it turns out to be: the
        // verifier has no `isinst` or `brtrue` on a `T`, and the box is
        // nothing at run time where `T` is a reference type.
        if !matches!(ty, Type::TypeParameter(_))
            && (ty.is_reference_type(symbols) || matches!(ty, Type::Array { .. } | Type::Null))
        {
            return Ok(());
        }
        let token = self.emitter.type_token(ty)?;
        self.stream.emit(Instruction::Box(token));
        Ok(())
    }

    /// The label a name stands for, made the first time the name is asked
    /// about — which may be the `goto` rather than the label itself.
    fn named_label(&mut self, name: &str) -> Label {
        if let Some(label) = self.labels.get(name) {
            return *label;
        }
        let label = self.stream.label();
        self.labels.insert(name.to_string(), label);
        label
    }

    pub(crate) fn emit_jump(&mut self, target: Label, depth: usize) {
        self.stream.emit(if self.protected > depth {
            Instruction::Leave(target)
        } else {
            Instruction::Branch(target)
        });
    }

    // -- receivers ---------------------------------------------------------

    /// Pushes what an instance call needs as its receiver.
    ///
    /// A reference type is passed as the reference it is; a value type has to
    /// be passed by address, or the method would work on a copy and its
    /// changes would go nowhere.
    /// The receiver of a call to `member`: as `emit_receiver` pushes it, or
    /// as the value it is where the member is an extension block's
    /// property, whose receiver is an argument like any other.
    fn emit_receiver_for(
        &mut self,
        receiver: &BoundExpression,
        member: SymbolId,
    ) -> Result<(), EmitError> {
        if self.emitter.is_extension_property(member) {
            let parameter = self
                .emitter
                .compilation
                .symbols()
                .get(member)
                .as_property()
                .and_then(|detail| detail.parameters.first().copied());
            // `extension(ref S s)` takes where the receiver is.
            if self.emitter.is_by_reference(parameter) {
                let held = self.address_receiver(receiver)?;
                self.push_property_receiver(Some(&held), None);
                return Ok(());
            }
            let taken = parameter.map_or_else(|| receiver.ty.clone(), |p| self.emitter.type_of(p));
            self.emit_value_of(receiver)?;
            if !self.emitter.is_value_type(&taken) && self.emitter.is_value_type(&receiver.ty) {
                self.box_if_needed(&receiver.ty)?;
            }
            return Ok(());
        }
        self.emit_receiver(receiver)
    }

    fn emit_receiver(&mut self, receiver: &BoundExpression) -> Result<(), EmitError> {
        // A call on a type parameter goes through `constrained.`, which reads
        // a *pointer* to the receiver whatever the parameter turns out to be:
        // pushing the value there and calling through it is how `T.GetHashCode()`
        // reads protected memory.
        if !self.emitter.is_value_type(&receiver.ty)
            && !matches!(receiver.ty, Type::TypeParameter(_))
        {
            return self.emit_expression(receiver, true);
        }
        // A `readonly` field is called on a copy outside its constructor
        // (§15.5.3): the verifier refuses its address there, and the
        // language promises the call cannot change it.
        // `int.MaxValue.ToString()`: a constant has no storage to address,
        // however much it looks like a field.
        let constant = self.emitter.binder.folded(receiver).is_some();
        // `x[0].ToString()` on a `T[]` is called through `readonly.
        // ldelema`, as Roslyn's constrained receivers are: a `T[]` that is
        // an `ApplicationException[]` seen as an `Exception[]` fails the
        // type check a plain `ldelema !T` makes.
        if matches!(receiver.ty, Type::TypeParameter(_))
            && matches!(&receiver.kind, BoundExpressionKind::ArrayAccess { indices, .. } if !indices.is_empty())
        {
            return self.emit_readonly_reference(receiver);
        }
        if !constant && !self.readonly_field_outside_constructor(receiver) {
            if let Some(address) = self.address_of(receiver)? {
                self.push_address(address);
                return Ok(());
            }
            if self.lives_somewhere(receiver) {
                return self.emit_reference(receiver);
            }
        }
        // Anything else is a value with nowhere of its own to live, so it
        // gets a slot to be addressed in.
        let slot = self.temporary(&receiver.ty)?;
        self.emit_expression(receiver, true)?;
        self.stream.emit(Instruction::StoreLocal(slot));
        self.stream.emit(Instruction::LoadLocalAddress(slot));
        Ok(())
    }

    /// What a `return` hands back: `return ref x` from a `ref readonly`
    /// member is a reference nothing will write through.
    fn emit_returned(&mut self, value: &BoundExpression) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let readonly = self.owner.is_some_and(|owner| {
            symbols
                .get(owner)
                .as_method()
                .is_some_and(|detail| detail.returns_readonly)
                || symbols
                    .get(owner)
                    .as_property()
                    .is_some_and(|detail| detail.returns_readonly)
        });
        match &value.kind {
            BoundExpressionKind::RefArgument { operand, .. }
                if readonly && self.iterator.is_none() && self.async_run.is_none() =>
            {
                self.emit_readonly_reference(operand)
            }
            _ => self.emit_expression(value, true),
        }
    }

    /// The address of a variable that will only be read through: an
    /// element of an array of references is reached with `readonly.
    /// ldelema`, which a `string[]` seen as an `object[]` passes where the
    /// plain `ldelema object` would throw (§III.2.3).
    fn emit_readonly_reference(&mut self, target: &BoundExpression) -> Result<(), EmitError> {
        // `M(Kind.Stop)` to an `in` parameter: a constant looks like a field
        // and has no storage (`ldsflda` of a literal field is a
        // `MissingFieldException`), so it is held in a slot and the slot is
        // handed on, as any value with nowhere to live is.
        if self.emitter.binder.folded(target).is_some() {
            let slot = self.temporary(&target.ty)?;
            self.emit_expression(target, true)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.stream.emit(Instruction::LoadLocalAddress(slot));
            return Ok(());
        }
        if let BoundExpressionKind::ArrayAccess { array, indices } = &target.kind
            && indices.len() == 1
            && (matches!(target.ty, Type::TypeParameter(_))
                || !self.emitter.is_value_type(&target.ty))
        {
            self.emit_expression(array, true)?;
            let element = self.emitter.type_token(&target.ty)?;
            self.emit_single_index(indices)?;
            self.stream.emit(Instruction::Readonly);
            self.stream.emit(Instruction::LoadElementAddress(element));
            return Ok(());
        }
        // `readonly.` may come before the `Address` of a rectangular array
        // too (§III.2.3), and skips its type check the same way: a `T[,]`
        // that is a `string[,]` seen as an `object[,]`.
        if let BoundExpressionKind::ArrayAccess { array, indices } = &target.kind
            && indices.len() > 1
            && matches!(target.ty, Type::TypeParameter(_))
        {
            self.emit_expression(array, true)?;
            let address = self.array_member(array, ArrayMember::Address, &target.ty)?;
            for index in indices {
                self.emit_expression(index, true)?;
            }
            self.stream.emit(Instruction::Readonly);
            self.stream
                .call_effect(Instruction::Call(address), indices.len() + 1, 1);
            return Ok(());
        }
        self.emit_reference(target)
    }

    /// Whether an expression is a call, a property or an indexer that hands
    /// back a reference, which `emit_reference` leaves as it stands.
    fn returns_reference(&self, value: &BoundExpression) -> bool {
        match &value.kind {
            BoundExpressionKind::Call { method, .. } => {
                matches!(self.emitter.type_of(*method), Type::ByRef(_))
            }
            BoundExpressionKind::IndexerAccess { indexer, .. } => {
                matches!(self.emitter.type_of(*indexer), Type::ByRef(_))
            }
            BoundExpressionKind::Property { property, .. } => {
                matches!(self.emitter.type_of(*property), Type::ByRef(_))
            }
            _ => false,
        }
    }

    /// The receiver of a call to `member`, copied first where it is a
    /// variable nothing may write through and the member does not promise to
    /// leave it alone: an `in` parameter, or `this` in a `readonly` member
    /// (§16.4.12). The call then changes the copy, as the language says.
    fn emit_member_receiver(
        &mut self,
        receiver: &BoundExpression,
        member: SymbolId,
    ) -> Result<(), EmitError> {
        if self.emitter.is_extension_property(member) {
            return self.emit_receiver_for(receiver, member);
        }
        // A type parameter may be a struct, and gets the same copy unless
        // it is known to be a class.
        let may_be_struct = match &receiver.ty {
            Type::TypeParameter(_) => !receiver
                .ty
                .is_reference_type(self.emitter.compilation.symbols()),
            ty => self.emitter.is_value_type(ty),
        };
        if may_be_struct
            && self.is_readonly_variable(receiver)
            && !self.emitter.is_readonly_member(member)
        {
            let slot = self.temporary(&receiver.ty)?;
            self.emit_expression(receiver, true)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.stream.emit(Instruction::LoadLocalAddress(slot));
            return Ok(());
        }
        self.emit_receiver(receiver)
    }

    /// Whether an expression is a local the code may not assign, which a
    /// `using` or a `foreach` declares.
    fn is_readonly_local(&self, value: &BoundExpression) -> bool {
        matches!(value.kind, BoundExpressionKind::Local(local)
            if self.body.locals.get(local.0 as usize).is_some_and(|slot| !slot.by_ref && slot.readonly))
    }

    /// Whether an expression is a variable of a value type that the code
    /// may read but not write: an `in` parameter, or `this` in a `readonly`
    /// member.
    fn is_readonly_variable(&self, value: &BoundExpression) -> bool {
        let symbols = self.emitter.compilation.symbols();
        match &value.kind {
            BoundExpressionKind::Parameter(parameter) => {
                self.captured_parameter(*parameter).is_none()
                    && symbols
                        .get(*parameter)
                        .as_parameter()
                        .is_some_and(|detail| detail.ref_kind == rustlyn_semantics::RefKind::In)
            }
            BoundExpressionKind::This => self.owner.is_some_and(|owner| {
                let mut member = owner;
                // An accessor is `readonly` where its property is.
                loop {
                    if symbols.get(member).modifiers.contains(Modifiers::READONLY) {
                        return true;
                    }
                    match symbols.get(member).container {
                        Some(container) if symbols.get(container).kind == SymbolKind::Property => {
                            member = container;
                        }
                        _ => return false,
                    }
                }
            }),
            // What a `ref readonly` field refers to is only read through it,
            // and a struct's field is as read-only as the struct. A struct in
            // a `using` or `foreach` variable is written by what is called
            // on it, as in any local, and only its fields are read-only
            // (Roslyn's `NeedsByValueFieldAccess`).
            BoundExpressionKind::Field { field, receiver } => {
                (self.is_ref_field(*field)
                    && self.emitter.compilation.is_ref_readonly_field(*field))
                    || (!self.is_ref_field(*field)
                        && receiver.as_deref().is_some_and(|receiver| {
                            self.emitter.is_value_type(&receiver.ty)
                                && (self.is_readonly_variable(receiver)
                                    || self.is_readonly_local(receiver))
                        }))
            }
            // `c ? ref a : ref ro` is as read-only as its more read-only
            // branch: a call on it works on a copy.
            BoundExpressionKind::Conditional {
                consequence,
                alternative,
                ..
            } => [consequence, alternative]
                .iter()
                .any(|branch| match &branch.kind {
                    BoundExpressionKind::RefArgument { operand, .. } => {
                        self.is_readonly_variable(operand)
                    }
                    _ => false,
                }),
            // So is what a `ref readonly` local refers to.
            BoundExpressionKind::Local(local) => self
                .body
                .locals
                .get(local.0 as usize)
                .is_some_and(|slot| slot.by_ref && slot.readonly_ref),
            // And `r = ref x` on one.
            BoundExpressionKind::Assignment {
                target,
                value: from,
            } => self.rebinds(target, from) && self.is_readonly_variable(target),
            // So is what a `ref readonly` return hands back.
            BoundExpressionKind::Call { method, .. } => {
                self.returns_reference(value)
                    && symbols
                        .get(*method)
                        .as_method()
                        .is_some_and(|detail| detail.returns_readonly)
            }
            BoundExpressionKind::IndexerAccess {
                indexer: property, ..
            }
            | BoundExpressionKind::Property { property, .. } => {
                self.returns_reference(value)
                    && symbols
                        .get(*property)
                        .as_property()
                        .is_some_and(|detail| detail.returns_readonly)
            }
            _ => false,
        }
    }

    /// Makes, ahead of a statement, each `stackalloc` that stands inside a
    /// larger expression of it: `localloc` wants nothing else on the stack,
    /// and `F(x, stackalloc int[2])` would have `x` there. Each is kept in a
    /// slot, which the expression then reads where the `stackalloc` was.
    fn hoist_stackallocs(&mut self, statement: &BoundStatement) -> Result<(), EmitError> {
        if self.body.nested_stackallocs.is_empty() {
            return Ok(());
        }
        let root = match &statement.kind {
            BoundStatementKind::Expression(value)
            | BoundStatementKind::Return(Some(value))
            | BoundStatementKind::LocalDeclaration {
                initializer: Some(value),
                ..
            } => value,
            _ => return Ok(()),
        };
        self.hoist_stackallocs_in(root, false)
    }

    /// The same for an expression, the whole of it included where something
    /// is pushed before it: a field initializer's `this`.
    fn hoist_stackallocs_in(
        &mut self,
        root: &BoundExpression,
        with_root: bool,
    ) -> Result<(), EmitError> {
        if self.body.nested_stackallocs.is_empty() {
            return Ok(());
        }
        let span = root.span;
        let nested: Vec<TextSpan> = self
            .body
            .nested_stackallocs
            .iter()
            .copied()
            .filter(|at| {
                span.start() <= at.start() && at.end() <= span.end() && (with_root || *at != span)
            })
            .collect();
        if nested.is_empty() {
            return Ok(());
        }
        let mut copy = root.clone();
        let mut found = Vec::new();
        collect_stackallocs(&mut copy, &nested, &mut found);
        for stackalloc in found {
            let slot = self.temporary(&stackalloc.ty)?;
            self.emit_expression(&stackalloc, true)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.hoisted_stackallocs.insert(stackalloc.span, slot);
        }
        Ok(())
    }

    /// Whether a field is declared `ref`, and so holds a reference.
    fn is_ref_field(&self, field: SymbolId) -> bool {
        self.emitter.compilation.symbols().get(field).kind == rustlyn_semantics::SymbolKind::Field
            && matches!(self.emitter.type_of(field), Type::ByRef(_))
    }

    /// Whether an expression is a `fixed` buffer field, whose address is
    /// the pointer the language reads it as.
    fn is_fixed_buffer(&self, value: &BoundExpression) -> bool {
        matches!(&value.kind, BoundExpressionKind::Field { field, .. }
            if self.emitter.fixed_buffers.contains_key(field)
                || self.emitter.compilation.metadata_fixed_buffer(*field).is_some())
    }

    /// Whether `value` reads a `readonly` field from anywhere but a
    /// constructor of the type declaring it.
    fn readonly_field_outside_constructor(&self, value: &BoundExpression) -> bool {
        let BoundExpressionKind::Field { field, .. } = &value.kind else {
            return false;
        };
        let symbols = self.emitter.compilation.symbols();
        if !symbols.get(*field).modifiers.contains(Modifiers::READONLY) {
            return false;
        }
        let in_constructor = self.owner.is_some_and(|owner| {
            let name = symbols.get(owner).name.as_str();
            (name == ".ctor" || name == ".cctor")
                && self.emitter.enclosing_type(owner) == self.emitter.enclosing_type(*field)
        });
        !in_constructor
    }

    /// Whether a value has a place of its own that can be addressed, without
    /// that place being an `Address`.
    ///
    /// A value type in a field of an object, or in an array, is reached by
    /// one `ldflda` or `ldelema` off what holds it. Copying it into a slot
    /// instead would throw away whatever is written to it —
    /// `TextWindow.AdvanceChar()` would advance a copy, and the lexer would
    /// never move.
    fn lives_somewhere(&self, value: &BoundExpression) -> bool {
        match &value.kind {
            BoundExpressionKind::Field { receiver, .. } => receiver
                .as_deref()
                .is_some_and(|value| !is_type_name(value)),
            // `__refvalue(r, T)` is the variable `r` refers to.
            BoundExpressionKind::ArrayAccess { .. }
            | BoundExpressionKind::Dereference { .. }
            | BoundExpressionKind::RefValue(_) => true,
            // `c ? ref a : ref b` is one of two variables, whichever it is —
            // unless either is a `readonly` field, which a call may only see
            // a copy of.
            BoundExpressionKind::Conditional {
                consequence,
                alternative,
                ..
            } => [consequence, alternative]
                .iter()
                .all(|branch| match &branch.kind {
                    BoundExpressionKind::RefArgument { operand, .. } => {
                        !self.readonly_field_outside_constructor(operand)
                    }
                    _ => false,
                }),
            // A captured variable is a field of the display class, which is
            // somewhere of its own as much as any other field is.
            BoundExpressionKind::Local(local) => self.captured_local(*local).is_some(),
            BoundExpressionKind::Parameter(symbol) => self.captured_parameter(*symbol).is_some(),
            BoundExpressionKind::Assignment {
                target,
                value: from,
            } => self.rebinds(target, from),
            // What comes before the last step of a sequence is done for what
            // it does, and the last is the variable: the receiver an
            // interpolated string handler was made with is kept in a local
            // first, and the call reaches the local (or, through a `ref`
            // local, the variable it was).
            BoundExpressionKind::Sequence(steps) => steps.last().is_some_and(|last| {
                matches!(
                    last.kind,
                    BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
                ) || self.lives_somewhere(last)
            }),
            // A call that returns a reference hands back where the value is.
            _ => self.returns_reference(value),
        }
    }

    /// Whether `target = value` points a `ref` local or parameter at another
    /// variable rather than writing through it.
    fn rebinds(&self, target: &BoundExpression, value: &BoundExpression) -> bool {
        matches!(value.kind, BoundExpressionKind::RefArgument { .. })
            && match &target.kind {
                BoundExpressionKind::Local(local) => self.is_by_ref_local(*local),
                BoundExpressionKind::Parameter(symbol) => {
                    self.is_by_reference(*symbol) && self.captured_parameter(*symbol).is_none()
                }
                _ => false,
            }
    }

    /// Where a value lives, when it lives somewhere that can be addressed.
    fn address_of(&mut self, expression: &BoundExpression) -> Result<Option<Address>, EmitError> {
        Ok(match &expression.kind {
            // A captured variable has no slot to take the address of: it is a
            // field, and `emit_reference` is what reaches one.
            BoundExpressionKind::Local(local) if self.captured_local(*local).is_some() => None,
            BoundExpressionKind::Parameter(symbol)
                if self.captured_parameter(*symbol).is_some() =>
            {
                None
            }
            BoundExpressionKind::Local(local) => Some(if self.is_by_ref_local(*local) {
                Address::HeldLocal(self.slot(local))
            } else {
                Address::Local(self.slot(local))
            }),
            BoundExpressionKind::Parameter(symbol) => {
                let index = self.argument_index(*symbol)?;
                // A `ref` parameter is already an address; taking its address
                // again would point at the reference rather than through it.
                Some(if self.is_by_reference(*symbol) {
                    Address::Held(index)
                } else {
                    Address::Argument(index)
                })
            }
            // A struct's `this` a state machine keeps is a field of the
            // machine — `ldarg.0` is the machine — and `emit_reference` is
            // what reaches it.
            BoundExpressionKind::This if self.captured_this().is_some() => None,
            // Inside a value type's method `this` is already a pointer.
            BoundExpressionKind::This if self.instance && self.in_value_type => Some(Address::This),
            // A value type being initialized waits in a local exactly so that
            // its members have somewhere to be written.
            BoundExpressionKind::CreatedObject => match self.creating.last() {
                Some(Created::Local(slot)) => Some(Address::Local(*slot)),
                _ => None,
            },
            // The receiver of a `?.` held by reference is reached where it is.
            BoundExpressionKind::AccessedValue
                if self.accessing_by_reference.last().copied().unwrap_or(false) =>
            {
                self.accessing.last().map(|slot| Address::HeldLocal(*slot))
            }
            // A `const` has no storage to point at: its value is loaded and
            // held somewhere that has.
            BoundExpressionKind::Field {
                receiver: None,
                field,
            } if self.emitter.constant_of(*field).is_none() => {
                Some(Address::StaticField(self.field_token(*field)?))
            }
            // `a.b.c` writes through the address of `a.b`, which is the
            // address of `a` and one `ldflda` — as long as `a.b` is a value
            // type, since a field of a reference is reached from the
            // reference itself.
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                field,
            } if self.emitter.is_value_type(&receiver.ty) => {
                let token = self.field_token_on(*field, Some(&receiver.ty))?;
                let held = self.is_ref_field(*field);
                self.address_of(receiver)?.map(|base| {
                    if held {
                        Address::HeldField(Box::new(base), token)
                    } else {
                        Address::Field(Box::new(base), token)
                    }
                })
            }
            _ => None,
        })
    }

    fn push_address(&mut self, address: Address) {
        let instruction = match address {
            Address::Local(slot) => Instruction::LoadLocalAddress(slot),
            Address::Argument(index) => Instruction::LoadArgumentAddress(index),
            Address::Held(index) => Instruction::LoadArgument(index),
            Address::HeldLocal(slot) => Instruction::LoadLocal(slot),
            Address::This => Instruction::LoadArgument(0),
            Address::StaticField(token) => Instruction::LoadStaticFieldAddress(token),
            Address::Field(base, token) => {
                self.push_address(*base);
                Instruction::LoadFieldAddress(token)
            }
            Address::HeldField(base, token) => {
                self.push_address(*base);
                Instruction::LoadField(token)
            }
        };
        self.stream.emit(instruction);
    }

    // -- patterns ----------------------------------------------------------

    /// The constant a `case` label compares with, which a `goto case`
    /// names: its own, or — on a union (C# 15) — the one it compares what
    /// the union holds with, `null` where it asks whether it holds anything.
    /// It comes with the type it is tested in (`Binder::case_key`), which is
    /// how the `goto case` names it too.
    fn case_key(&self, pattern: &BoundPattern, input: &Type) -> Option<(Type, ConstantValue)> {
        match &pattern.kind {
            BoundPatternKind::Constant(value) => self.emitter.binder.case_key(value, input),
            BoundPatternKind::UnionCase { inner, .. } => self.case_key(inner, input),
            BoundPatternKind::Or(left, _) => self.case_key(left, input),
            BoundPatternKind::Recursive(recursive)
                if recursive.properties.len() == 1
                    && recursive.positional.is_empty()
                    && recursive.local.is_none() =>
            {
                let (member, inner) = &recursive.properties[0];
                if self.emitter.compilation.symbols().get(*member).name == "HasValue" {
                    Some((Type::Null, ConstantValue::Null))
                } else {
                    self.case_key(inner, input)
                }
            }
            _ => None,
        }
    }

    /// Emits the test a pattern performs against a value already in `slot`.
    ///
    /// The code falls through when the pattern matched, with whatever it binds
    /// stored, and branches to `on_fail` when it did not. Everything else
    /// about patterns follows from that one shape: `and` chains two tests with
    /// the same failure label, `or` gives the first its own, and `not` swaps
    /// the two exits.
    ///
    /// The value lives in a local rather than on the stack because a pattern
    /// reads it more than once — a type test and then a comparison — and a
    /// stack machine cannot read a value twice without copying it each time.
    fn emit_pattern_test(
        &mut self,
        slot: u16,
        input: &Type,
        pattern: &BoundPattern,
        on_fail: Label,
    ) -> Result<(), EmitError> {
        match &pattern.kind {
            BoundPatternKind::Discard => {}
            BoundPatternKind::Var { local } => {
                self.begin_store(*local);
                self.stream.emit(Instruction::LoadLocal(slot));
                self.end_store(*local);
            }
            // `span is "str"`: the span goes where the binder's
            // `SequenceEqual` reads it from, and the call has to say yes.
            BoundPatternKind::SpanString { local, test } => {
                self.begin_store(*local);
                self.stream.emit(Instruction::LoadLocal(slot));
                self.end_store(*local);
                self.emit_expression(test, true)?;
                self.stream.emit(Instruction::BranchIfFalse(on_fail));
            }
            // `var (a, b)`: the value, or what a `T?` holds, goes into the
            // local the deconstruction reads from.
            BoundPatternKind::VarDeconstruct {
                ty,
                local,
                deconstruction,
            } => {
                self.emit_type_test(slot, input, ty, on_fail)?;
                self.emit_narrowed(slot, input, ty)?;
                self.store_top(*local)?;
                self.emit_expression(deconstruction, false)?;
            }
            BoundPatternKind::Type(target) => {
                self.emit_type_test(slot, input, target, on_fail)?;
            }
            BoundPatternKind::Recursive(recursive) => {
                self.emit_recursive_test(slot, input, recursive, on_fail)?;
            }
            BoundPatternKind::List(list) => {
                self.emit_list_test(slot, input, list, on_fail)?;
            }
            BoundPatternKind::Declaration { ty, local } => {
                self.emit_type_test(slot, input, ty, on_fail)?;
                if let Some(local) = local {
                    self.emit_narrowed(slot, input, ty)?;
                    self.store_top(*local)?;
                }
            }
            BoundPatternKind::Constant(value) => {
                // `case null:` is a null check and nothing else; a `null` has
                // no type to test against.
                // A named constant that is `null` is one too.
                if matches!(value.constant(), Some(ConstantValue::Null))
                    || matches!(self.emitter.binder.folded(value), Some(ConstantValue::Null))
                {
                    // A `T?` has no null to branch on: `brtrue` on a struct
                    // is not a program, and what is being asked is whether it
                    // holds anything.
                    if self.emitter.nullable_underlying(input).is_some() {
                        let has_value = self.emitter.nullable_member(input, "get_HasValue")?;
                        self.stream.emit(Instruction::LoadLocalAddress(slot));
                        self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                        self.stream.emit(Instruction::BranchIfTrue(on_fail));
                        return Ok(());
                    }
                    self.stream.emit(Instruction::LoadLocal(slot));
                    // `value is null` on a `T` boxes it: the verifier has
                    // no branch on a `T`, and a struct boxes to something
                    // that is never null, which is the right answer.
                    if matches!(input, Type::TypeParameter(_)) {
                        let token = self.emitter.type_token(input)?;
                        self.stream.emit(Instruction::Box(token));
                    }
                    self.stream.emit(Instruction::BranchIfTrue(on_fail));
                    return Ok(());
                }
                // `case 1:` on a `long?` asks whether there is a value, and
                // then compares it: the constant is one of the `long` inside.
                if let Some(inner) = self.emitter.nullable_underlying(input)
                    && self.numeric_kind(&inner).is_some()
                    && self.numeric_kind(&value.ty).is_some()
                {
                    self.emit_type_test(slot, input, &inner, on_fail)?;
                    self.emit_narrowed(slot, input, &inner)?;
                    let held = self.temporary(&inner)?;
                    self.stream.emit(Instruction::StoreLocal(held));
                    return self.emit_pattern_test(held, &inner, pattern, on_fail);
                }
                // `case 0:` on a `byte` is a comparison of numbers, not a
                // question about whether the byte is an `int`: the constant
                // takes the input's type (§12.2.3), and the values meet on
                // the stack as whatever the input is.
                if let Some(input_kind) = self.numeric_kind(input)
                    && self.numeric_kind(&value.ty).is_some()
                    && input != &value.ty
                {
                    self.stream.emit(Instruction::LoadLocal(slot));
                    self.emit_expression(value, true)?;
                    self.widen_to(input_kind);
                    self.stream.emit(Instruction::CompareEqual);
                    self.stream.emit(Instruction::BranchIfFalse(on_fail));
                    return Ok(());
                }
                // `case 6:` on an `nint` is the constant as a native integer.
                if input != &value.ty
                    && input
                        .symbol()
                        .and_then(|symbol| self.emitter.primitive_of(symbol))
                        .is_some_and(|element| matches!(element, ElementType::I | ElementType::U))
                    && let Some(constant) = self.emitter.binder.folded(value)
                    && self.numeric_kind(&value.ty).is_some()
                {
                    self.stream.emit(Instruction::LoadLocal(slot));
                    self.emit_constant(&constant, input)?;
                    self.stream.emit(Instruction::CompareEqual);
                    self.stream.emit(Instruction::BranchIfFalse(on_fail));
                    return Ok(());
                }
                self.emit_type_test(slot, input, &value.ty, on_fail)?;
                self.emit_narrowed(slot, input, &value.ty)?;
                // `d is double.NaN` asks `double.IsNaN(d)`: no NaN is equal
                // to anything, itself included.
                let nan = match self.emitter.binder.folded(value) {
                    Some(ConstantValue::Double(number)) if number.is_nan() => {
                        Some(("System.Double", ElementType::R8))
                    }
                    Some(ConstantValue::Single(number)) if number.is_nan() => {
                        Some(("System.Single", ElementType::R4))
                    }
                    _ => None,
                };
                if let Some((owner, element)) = nan {
                    let is_nan = self.emitter.framework_member(
                        owner,
                        "IsNaN",
                        false,
                        &SigType::Primitive(ElementType::Boolean),
                        &[SigType::Primitive(element)],
                    );
                    self.stream.call_effect(Instruction::Call(is_nan), 1, 1);
                    self.stream.emit(Instruction::BranchIfFalse(on_fail));
                    return Ok(());
                }
                self.emit_expression(value, true)?;
                // `case 1.5m:` compares decimals through `op_Equality`.
                if self.is_decimal(&value.ty) {
                    self.emit_decimal_operator(BinaryOperator::Equality)?;
                    self.stream.emit(Instruction::BranchIfFalse(on_fail));
                    return Ok(());
                }
                if self.is_string(&value.ty) {
                    let string = SigType::Primitive(ElementType::String);
                    let equality = self.emitter.framework_member(
                        "System.String",
                        "op_Equality",
                        false,
                        &SigType::Primitive(ElementType::Boolean),
                        &[string.clone(), string],
                    );
                    self.stream.call_effect(Instruction::Call(equality), 2, 1);
                } else {
                    self.stream.emit(Instruction::CompareEqual);
                }
                self.stream.emit(Instruction::BranchIfFalse(on_fail));
            }
            BoundPatternKind::Relational { operator, value } => {
                // As for a constant: `> 0` on an `int?` compares the `int`
                // inside, where there is one.
                if let Some(inner) = self.emitter.nullable_underlying(input)
                    && self.numeric_kind(&inner).is_some()
                    && self.numeric_kind(&value.ty).is_some()
                {
                    self.emit_type_test(slot, input, &inner, on_fail)?;
                    self.emit_narrowed(slot, input, &inner)?;
                    let held = self.temporary(&inner)?;
                    self.stream.emit(Instruction::StoreLocal(held));
                    return self.emit_pattern_test(held, &inner, pattern, on_fail);
                }
                // As for a constant: `> 0` on a `byte` compares bytes.
                let compared = match self.numeric_kind(input) {
                    Some(input_kind)
                        if self.numeric_kind(&value.ty).is_some() && input != &value.ty =>
                    {
                        self.stream.emit(Instruction::LoadLocal(slot));
                        self.emit_expression(value, true)?;
                        self.widen_to(input_kind);
                        input.clone()
                    }
                    _ => {
                        self.emit_type_test(slot, input, &value.ty, on_fail)?;
                        self.emit_narrowed(slot, input, &value.ty)?;
                        self.emit_expression(value, true)?;
                        value.ty.clone()
                    }
                };
                // `<= 60.000m` compares decimals, which is `System.Decimal`'s
                // `op_LessThanOrEqual` and not an instruction.
                if self.is_decimal(&compared) {
                    self.emit_decimal_operator(*operator)?;
                    self.stream.emit(Instruction::BranchIfFalse(on_fail));
                    return Ok(());
                }
                let unsigned = self.is_unsigned(&compared);
                let floating = matches!(
                    self.emitter.special_type_of(&compared),
                    Some(SpecialType::Single | SpecialType::Double)
                );
                match operator {
                    BinaryOperator::LessThan => self.stream.emit(less_than(unsigned)),
                    BinaryOperator::GreaterThan => self.stream.emit(greater_than(unsigned)),
                    BinaryOperator::LessThanOrEqual => {
                        self.stream.emit(greater_than(unsigned || floating));
                        self.negate();
                    }
                    BinaryOperator::GreaterThanOrEqual => {
                        self.stream.emit(less_than(unsigned || floating));
                        self.negate();
                    }
                    BinaryOperator::Equality => self.stream.emit(Instruction::CompareEqual),
                    BinaryOperator::Inequality => {
                        self.stream.emit(Instruction::CompareEqual);
                        self.negate();
                    }
                    other => {
                        return Err(EmitError::new(format!(
                            "`{other:?}` is not a relational pattern operator"
                        )));
                    }
                }
                self.stream.emit(Instruction::BranchIfFalse(on_fail));
            }
            // What the left established is what the right is matched
            // against: after `S1` on an `object`, the right reads an `S1`.
            BoundPatternKind::And(left, right) => {
                self.emit_pattern_test(slot, input, left, on_fail)?;
                let narrowed = match &left.kind {
                    BoundPatternKind::Type(ty) | BoundPatternKind::Declaration { ty, .. } => {
                        Some(ty.clone())
                    }
                    BoundPatternKind::Recursive(recursive) => recursive.ty.clone(),
                    _ => None,
                }
                .filter(|ty| ty != input && !ty.is_error());
                match narrowed {
                    Some(ty) => {
                        let held = self.temporary(&ty)?;
                        self.emit_narrowed(slot, input, &ty)?;
                        self.stream.emit(Instruction::StoreLocal(held));
                        self.note_path(held, slot, None);
                        self.emit_pattern_test(held, &ty, right, on_fail)?;
                    }
                    None => self.emit_pattern_test(slot, input, right, on_fail)?,
                }
            }
            BoundPatternKind::Or(left, right) => {
                let second = self.stream.label();
                let matched = self.stream.label();
                self.emit_pattern_test(slot, input, left, second)?;
                self.stream.emit(Instruction::Branch(matched));
                self.stream.mark(second);
                self.emit_pattern_test(slot, input, right, on_fail)?;
                self.stream.mark(matched);
            }
            // `u is int n` on a union with a `TryGetValue(out int)`: the
            // call says whether it holds one and hands it over, and the
            // pattern goes on against what it handed over. The union in a
            // `U?` is reached first, and a class union that is null holds
            // nothing.
            BoundPatternKind::UnionCase {
                try_get_value,
                ty,
                inner,
            } => {
                let (matched, slot) = match self.emitter.nullable_underlying(input) {
                    Some(union) => {
                        self.emit_type_test(slot, input, &union, on_fail)?;
                        let held = self.temporary(&union)?;
                        self.emit_narrowed(slot, input, &union)?;
                        self.stream.emit(Instruction::StoreLocal(held));
                        (union, held)
                    }
                    None => {
                        if !self.emitter.is_value_type(input) {
                            self.stream.emit(Instruction::LoadLocal(slot));
                            self.stream.emit(Instruction::BranchIfFalse(on_fail));
                        }
                        (input.clone(), slot)
                    }
                };
                let receiver = BoundExpression::new(
                    BoundExpressionKind::Local(LocalId(u32::from(slot))),
                    matched.clone(),
                    TextSpan::new(0, 0),
                );
                self.emit_receiver_for(&receiver, *try_get_value)?;
                let held = self.temporary(ty)?;
                self.stream.emit(Instruction::LoadLocalAddress(held));
                let token = self.method_token_on(*try_get_value, Some(&matched))?;
                let instruction = self.receiver_call(&receiver, *try_get_value, token)?;
                self.stream.call_effect(instruction, 2, 1);
                self.stream.emit(Instruction::BranchIfFalse(on_fail));
                self.emit_pattern_test(held, ty, inner, on_fail)?;
            }
            BoundPatternKind::Not(inner) => {
                // The two exits swap: falling through means the inner pattern
                // failed, which is what `not` wanted.
                let failed = self.stream.label();
                self.emit_pattern_test(slot, input, inner, failed)?;
                self.stream.emit(Instruction::Branch(on_fail));
                self.stream.mark(failed);
            }
            BoundPatternKind::Unsupported(kind) => {
                return Err(EmitError::new(format!(
                    "cannot emit the pattern `{kind:?}` yet"
                )));
            }
        }
        Ok(())
    }

    /// Branches to `on_fail` unless the value in `slot` is of `target`.
    fn emit_type_test(
        &mut self,
        slot: u16,
        input: &Type,
        target: &Type,
        on_fail: Label,
    ) -> Result<(), EmitError> {
        if input == target || target.is_error() {
            // The static type already says so — but `null` is a value of every
            // reference type and matches no type pattern, so a reference is
            // still worth one test. Without it `expression is ExpressionSyntax
            // found` is true for a null, and the loop reading it never ends.
            if !target.is_error()
                && input.is_reference_type(self.emitter.compilation.symbols())
                && !matches!(input, Type::Pointer(_))
            {
                self.stream.emit(Instruction::LoadLocal(slot));
                self.stream.emit(Instruction::BranchIfFalse(on_fail));
            }
            // A `T` may be a reference, and a null one matches no type
            // pattern either: boxed, a value is never null and a null
            // reference stays one.
            if !target.is_error() && matches!(input, Type::TypeParameter(_)) {
                let token = self.emitter.type_token(input)?;
                self.stream.emit(Instruction::LoadLocal(slot));
                self.stream.emit(Instruction::Box(token));
                self.stream.emit(Instruction::BranchIfFalse(on_fail));
            }
            return Ok(());
        }
        // A `T?` holding a `T` is what `HasValue` answers; `isinst` would be
        // asking the wrong question of the wrong thing.
        if self.emitter.nullable_underlying(input).as_ref() == Some(target) {
            let token = self.emitter.nullable_member(input, "get_HasValue")?;
            self.stream.emit(Instruction::LoadLocalAddress(slot));
            self.stream.call_effect(Instruction::Call(token), 1, 1);
            self.stream.emit(Instruction::BranchIfFalse(on_fail));
            return Ok(());
        }
        // `isinst` answers about a reference, so a value has to be a boxed
        // one first. `t is IFoo` on a struct and on an unconstrained `T` are
        // both this: box, then ask. The box is what the runtime compares
        // against, and boxing a `T` that turns out to be a reference type is
        // the identity.
        let token = self.emitter.type_token(target)?;
        self.stream.emit(Instruction::LoadLocal(slot));
        self.box_if_a_value(input)?;
        self.stream.emit(Instruction::IsInstance(token));
        self.stream.emit(Instruction::BranchIfFalse(on_fail));
        Ok(())
    }

    /// `v is [1, var x, ..]`: how many elements, then each one in turn.
    ///
    /// The length is read once into a slot of its own, because every test
    /// after the first reads it again — and the ones written after a `..`
    /// count back from it.
    fn emit_list_test(
        &mut self,
        slot: u16,
        input: &Type,
        pattern: &BoundListPattern,
        on_fail: Label,
    ) -> Result<(), EmitError> {
        // Nothing is a list of anything when it is null, and `Length` on one
        // would throw rather than answer.
        let matched = if pattern.matched == *input {
            slot
        } else {
            self.emit_type_test(slot, input, &pattern.matched, on_fail)?;
            let narrowed = self.temporary(&pattern.matched)?;
            self.emit_narrowed(slot, input, &pattern.matched)?;
            self.stream.emit(Instruction::StoreLocal(narrowed));
            narrowed
        };
        if !self.emitter.is_value_type(&pattern.matched) {
            self.stream.emit(Instruction::LoadLocal(matched));
            self.stream.emit(Instruction::BranchIfFalse(on_fail));
        }

        // `[..]` asks nothing but that there is a list: a count is never
        // negative (Roslyn assumes as much), so it is not even read.
        let listed = pattern.before.len() + pattern.after.len();
        if listed == 0 && pattern.slice && pattern.slice_pattern.is_none() {
            if let Some(local) = pattern.local {
                self.begin_store(local);
                self.stream.emit(Instruction::LoadLocal(matched));
                self.end_store(local);
            }
            return Ok(());
        }
        let counted = self.temporary(&self.int_type())?;
        match pattern.length {
            None => {
                self.stream.emit(Instruction::LoadLocal(matched));
                self.stream.emit(Instruction::LoadLength);
                self.stream.emit(Instruction::ConvertI4);
            }
            Some(length) => {
                let token =
                    self.emitter
                        .property_accessor(length, Some(&pattern.matched), false)?;
                self.push_matched(matched, &pattern.matched);
                let reached = self.reading_member(length);
                let call = self.receiver_call_on(&pattern.matched, reached, token)?;
                self.stream.call_effect(call, 1, 1);
            }
        }
        self.stream.emit(Instruction::StoreLocal(counted));

        self.stream.emit(Instruction::LoadLocal(counted));
        self.stream.emit(Instruction::LoadInt32(listed as i32));
        if pattern.slice {
            // `[a, .., z]` wants at least the two that were written.
            self.stream.emit(Instruction::CompareLess);
            self.stream.emit(Instruction::BranchIfTrue(on_fail));
        } else {
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::BranchIfFalse(on_fail));
        }

        // An indexer taking an `Index` is given the ones the binder made;
        // one taking an `int` is given the number.
        let mut indexes = pattern.indexes.iter();
        for (at, element) in pattern.before.iter().enumerate() {
            let index = indexes.next();
            if index.is_none() {
                self.stream.emit(Instruction::LoadInt32(at as i32));
            }
            self.emit_element_test(matched, index, element, pattern, on_fail)?;
        }
        // `.. p` cuts the slice out of the list the binder named, whose
        // count it needs for a `Slice(start, length)`.
        if let Some(slice) = &pattern.slice_pattern {
            self.begin_store(slice.list);
            self.stream.emit(Instruction::LoadLocal(matched));
            self.end_store(slice.list);
            self.begin_store(slice.count);
            self.stream.emit(Instruction::LoadLocal(counted));
            self.end_store(slice.count);
            self.emit_expression(&slice.value, true)?;
            let held = self.temporary(&slice.value.ty)?;
            self.stream.emit(Instruction::StoreLocal(held));
            // A slice is taken to be something (Roslyn's DAG assumes a
            // slice evaluation non-null): `.. {}` tests nothing, even where
            // `Slice` hands back `null`.
            match &slice.pattern.kind {
                BoundPatternKind::Recursive(recursive)
                    if recursive.properties.is_empty()
                        && recursive.positional.is_empty()
                        && recursive.deconstruct.is_none()
                        && recursive.ty.as_ref().is_none_or(|ty| *ty == slice.value.ty) =>
                {
                    if let Some(local) = recursive.local {
                        self.begin_store(local);
                        self.stream.emit(Instruction::LoadLocal(held));
                        self.end_store(local);
                    }
                }
                _ => self.emit_pattern_test(held, &slice.value.ty, &slice.pattern, on_fail)?,
            }
        }
        // What was written after the `..` counts back from the end, because
        // how many the slice swallowed is not known until run time.
        for (at, element) in pattern.after.iter().enumerate() {
            let index = indexes.next();
            if index.is_none() {
                let back = (pattern.after.len() - at) as i32;
                self.stream.emit(Instruction::LoadLocal(counted));
                self.stream.emit(Instruction::LoadInt32(back));
                self.stream.emit(Instruction::Subtract);
            }
            self.emit_element_test(matched, index, element, pattern, on_fail)?;
        }
        if let Some(local) = pattern.local {
            self.begin_store(local);
            self.stream.emit(Instruction::LoadLocal(matched));
            self.end_store(local);
        }
        Ok(())
    }

    /// One element of a list pattern, read with the `Index` given or, where
    /// there is none, with the `int` already on the stack.
    fn emit_element_test(
        &mut self,
        matched: u16,
        given: Option<&BoundExpression>,
        element: &BoundPattern,
        pattern: &BoundListPattern,
        on_fail: Label,
    ) -> Result<(), EmitError> {
        let index = match given {
            Some(given) => {
                self.emit_expression(given, true)?;
                self.temporary(&given.ty)?
            }
            None => self.temporary(&self.int_type())?,
        };
        self.stream.emit(Instruction::StoreLocal(index));
        let held = self.temporary(&pattern.element)?;
        match pattern.indexer {
            None => {
                let token = self.emitter.type_token(&pattern.element)?;
                self.stream.emit(Instruction::LoadLocal(matched));
                self.stream.emit(Instruction::LoadLocal(index));
                self.load_element(&pattern.element, token);
            }
            Some(indexer) => {
                // `this[int]` is a property; `get_Item` is the method behind
                // it, and either may be what the lookup found.
                let token = match self.emitter.compilation.symbols().get(indexer).kind {
                    SymbolKind::Property => {
                        self.emitter
                            .property_accessor(indexer, Some(&pattern.matched), false)?
                    }
                    _ => self.method_token_on(indexer, Some(&pattern.matched))?,
                };
                self.push_matched(matched, &pattern.matched);
                self.stream.emit(Instruction::LoadLocal(index));
                let reached = self.reading_member(indexer);
                let call = self.receiver_call_on(&pattern.matched, reached, token)?;
                self.stream.call_effect(call, 2, 1);
                // `span[i]` is a `ref readonly char`: what the pattern
                // compares is the character, not where it is.
                self.read_through_reference(indexer, &pattern.element)?;
            }
        }
        self.stream.emit(Instruction::StoreLocal(held));
        self.emit_pattern_test(held, &pattern.element, element, on_fail)
    }

    /// Pushes the value a list pattern reads its members on, as the call
    /// needs it: a struct by address, anything else as the reference it is.
    fn push_matched(&mut self, slot: u16, ty: &Type) {
        self.stream.emit(if self.emitter.is_value_type(ty) {
            Instruction::LoadLocalAddress(slot)
        } else {
            Instruction::LoadLocal(slot)
        });
    }

    /// The method a member is read through, which for a property is its
    /// getter: whether the call is virtual is the getter's to say.
    fn reading_member(&self, member: SymbolId) -> SymbolId {
        let symbols = self.emitter.compilation.symbols();
        if symbols.get(member).kind != SymbolKind::Property {
            return member;
        }
        symbols
            .get(member)
            .as_property()
            .and_then(|detail| detail.getter)
            .unwrap_or(member)
    }

    /// The instruction a call on a value of that type uses.
    fn receiver_call_on(
        &mut self,
        ty: &Type,
        method: SymbolId,
        token: Token,
    ) -> Result<Instruction, EmitError> {
        let receiver = BoundExpression::new(
            BoundExpressionKind::Unsupported(SyntaxKind::None),
            ty.clone(),
            TextSpan::default(),
        );
        self.receiver_call(&receiver, method, token)
    }

    /// Pushes the value in `slot` as `target`, the test having already passed.    /// Pushes the value in `slot` as `target`, the test having already passed.
    /// `Shape { Width: > 2 }` and `p is (1, var b)`.
    ///
    /// The type test comes first and narrows what everything inside is read
    /// on; then each member is read into a slot of its own and matched, and
    /// each part the value is taken apart into likewise. Every failure jumps
    /// to the same place, which is what makes the whole thing one test.
    /// Starts a match on the value in `slot` against these patterns: the
    /// reads more than one of them makes are found, and each gets a flag
    /// that is cleared here. What was being shared before is handed back,
    /// for [`end_match`](Self::end_match) to put back.
    fn begin_match(
        &mut self,
        slot: u16,
        patterns: &[&BoundPattern],
    ) -> Result<Option<PatternShare>, EmitError> {
        let mut counts = HashMap::new();
        for pattern in patterns {
            count_pattern_reads(pattern, &[], &mut counts);
        }
        let mut share = PatternShare::default();
        share.paths.insert(slot, Vec::new());
        let boolean = self
            .emitter
            .compilation
            .special_type(SpecialType::Boolean)
            .map_or(Type::Error, Type::named);
        let mut shared: Vec<(Vec<PathStep>, usize)> = counts
            .into_iter()
            .filter(|(_, (count, _))| *count > 1)
            .map(|(path, (_, first))| (path, first))
            .collect();
        // Shallower reads first, and among those the one read first: the
        // flags are slots, and their numbering must not be a hash's order.
        shared.sort_by_key(|(path, first)| (path.len(), *first));
        for (path, _) in shared {
            let flag = self.temporary(&boolean)?;
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::StoreLocal(flag));
            share.flags.insert(path, flag);
        }
        Ok(self.pattern_share.replace(share))
    }

    fn end_match(&mut self, outer: Option<PatternShare>) {
        self.pattern_share = outer;
    }

    /// Where a slot a pattern tests came from, where a match is tracking it.
    fn path_of(&self, slot: u16) -> Option<Vec<PathStep>> {
        self.pattern_share.as_ref()?.paths.get(&slot).cloned()
    }

    /// Notes that `slot` holds what `from` does, narrowed or read further by
    /// `step`.
    fn note_path(&mut self, slot: u16, from: u16, step: Option<PathStep>) {
        let Some(mut path) = self.path_of(from) else {
            return;
        };
        path.extend(step);
        if let Some(share) = self.pattern_share.as_mut() {
            share.paths.insert(slot, path);
        }
    }

    /// Reads a part of the value in `from` into a slot, through `emit`: once
    /// per match where the match reads it more than once, and every time
    /// otherwise.
    fn read_part(
        &mut self,
        from: u16,
        step: PathStep,
        ty: &Type,
        emit: impl FnOnce(&mut Self) -> Result<(), EmitError>,
    ) -> Result<u16, EmitError> {
        let path = self.path_of(from).map(|mut path| {
            path.push(step.clone());
            path
        });
        let flag = path.as_ref().and_then(|path| {
            self.pattern_share
                .as_ref()
                .and_then(|share| share.flags.get(path).copied())
        });
        let (Some(path), Some(flag)) = (path, flag) else {
            let held = self.temporary(ty)?;
            emit(self)?;
            self.stream.emit(Instruction::StoreLocal(held));
            self.note_path(held, from, Some(step));
            return Ok(held);
        };
        let existing = self
            .pattern_share
            .as_ref()
            .and_then(|share| share.values.get(&path).copied());
        let held = match existing {
            Some(held) => held,
            None => {
                let held = self.temporary(ty)?;
                if let Some(share) = self.pattern_share.as_mut() {
                    share.values.insert(path.clone(), held);
                }
                held
            }
        };
        let done = self.stream.label();
        self.stream.emit(Instruction::LoadLocal(flag));
        self.stream.emit(Instruction::BranchIfTrue(done));
        emit(self)?;
        self.stream.emit(Instruction::StoreLocal(held));
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::StoreLocal(flag));
        self.stream.mark(done);
        if let Some(share) = self.pattern_share.as_mut() {
            share.paths.insert(held, path);
        }
        Ok(held)
    }

    fn emit_recursive_test(
        &mut self,
        slot: u16,
        input: &Type,
        pattern: &BoundRecursivePattern,
        on_fail: Label,
    ) -> Result<(), EmitError> {
        // What the parts are read on: the written type where there was one.
        let (matched, slot) = match &pattern.ty {
            Some(ty) if ty != input => {
                self.emit_type_test(slot, input, ty, on_fail)?;
                let narrowed = self.temporary(ty)?;
                self.emit_narrowed(slot, input, ty)?;
                self.stream.emit(Instruction::StoreLocal(narrowed));
                self.note_path(narrowed, slot, None);
                (ty.clone(), narrowed)
            }
            // `{ X: 1 }` with nothing written in front still fails on a null:
            // there is nothing to read `X` off.
            _ => {
                if !self.emitter.is_value_type(input) {
                    self.stream.emit(Instruction::LoadLocal(slot));
                    self.stream.emit(Instruction::BranchIfFalse(on_fail));
                }
                (input.clone(), slot)
            }
        };

        for (member, inner) in &pattern.properties {
            let member_type = self.emitter.member_type(*member, &matched);
            let held = self.read_part(slot, PathStep::Member(*member), &member_type, |this| {
                this.emit_member_read(slot, &matched, *member)
            })?;
            self.emit_pattern_test(held, &member_type, inner, on_fail)?;
        }

        if !pattern.positional.is_empty() {
            let parts = self.emit_taken_apart(slot, &matched, pattern)?;
            for ((held, ty), inner) in parts.into_iter().zip(&pattern.positional) {
                self.emit_pattern_test(held, &ty, inner, on_fail)?;
            }
        }

        if let Some(local) = pattern.local {
            self.begin_store(local);
            self.stream.emit(Instruction::LoadLocal(slot));
            self.end_store(local);
        }
        Ok(())
    }

    /// The slots a positional pattern's parts end up in.
    fn emit_taken_apart(
        &mut self,
        slot: u16,
        matched: &Type,
        pattern: &BoundRecursivePattern,
    ) -> Result<Vec<(u16, Type)>, EmitError> {
        // A tuple is taken apart by reading its fields; anything else by
        // calling the `Deconstruct` the binder picked, with a slot per `out`.
        let Some(deconstruct) = pattern.deconstruct else {
            let Type::Tuple(elements) = matched else {
                return Err(EmitError::new(
                    "a positional pattern on something with no `Deconstruct`",
                ));
            };
            let mut parts = Vec::with_capacity(elements.len());
            for (index, element) in elements.iter().enumerate() {
                let chain = self.emitter.tuple_field(matched, index)?;
                let held = self.read_part(slot, PathStep::Element(index), &element.ty, |this| {
                    this.stream.emit(Instruction::LoadLocal(slot));
                    for token in chain {
                        this.stream.emit(Instruction::LoadField(token));
                    }
                    Ok(())
                })?;
                parts.push((held, element.ty.clone()));
            }
            return Ok(parts);
        };

        let (parameters, extension) = self
            .emitter
            .compilation
            .symbols()
            .get(deconstruct)
            .as_method()
            .map(|detail| (detail.parameters.clone(), detail.is_extension))
            .unwrap_or_default();
        // An extension `Deconstruct` takes the value as its first argument
        // and the parts after it.
        if extension && let Some((_, outs)) = parameters.split_first() {
            let mut parts = Vec::with_capacity(outs.len());
            self.stream.emit(Instruction::LoadLocal(slot));
            for parameter in outs {
                let ty = self.emitter.member_type(*parameter, matched);
                let held = self.temporary(&ty)?;
                self.stream.emit(Instruction::LoadLocalAddress(held));
                parts.push((held, ty));
            }
            let token = self.method_token(deconstruct)?;
            self.stream
                .call_effect(Instruction::Call(token), parameters.len(), 0);
            return Ok(parts);
        }
        let mut parts = Vec::with_capacity(parameters.len());
        let receiver = BoundExpression::new(
            BoundExpressionKind::Local(LocalId(u32::from(slot))),
            matched.clone(),
            TextSpan::new(0, 0),
        );
        self.emit_receiver(&receiver)?;
        for parameter in &parameters {
            let ty = self.emitter.member_type(*parameter, matched);
            let held = self.temporary(&ty)?;
            self.stream.emit(Instruction::LoadLocalAddress(held));
            parts.push((held, ty));
        }
        let token = self.method_token_on(deconstruct, Some(matched))?;
        let instruction = self.receiver_call(&receiver, deconstruct, token)?;
        self.stream
            .call_effect(instruction, parameters.len() + 1, 0);
        Ok(parts)
    }

    /// Reads a field or a property off a value in a slot.
    fn emit_member_read(
        &mut self,
        slot: u16,
        matched: &Type,
        member: SymbolId,
    ) -> Result<(), EmitError> {
        let receiver = BoundExpression::new(
            BoundExpressionKind::Local(LocalId(u32::from(slot))),
            matched.clone(),
            TextSpan::new(0, 0),
        );
        let symbols = self.emitter.compilation.symbols();
        match symbols.get(member).kind {
            SymbolKind::Field => {
                self.emit_expression(&receiver, true)?;
                let token = self.field_token_on(member, Some(matched))?;
                self.stream.emit(Instruction::LoadField(token));
                Ok(())
            }
            _ => {
                let getter = self.emitter.read_accessor(member, Some(matched))?;
                self.emit_receiver_for(&receiver, member)?;
                let instruction = self.receiver_call(&receiver, member, getter)?;
                self.stream.call_effect(instruction, 1, 1);
                Ok(())
            }
        }
    }

    fn emit_narrowed(&mut self, slot: u16, input: &Type, target: &Type) -> Result<(), EmitError> {
        if self.emitter.nullable_underlying(input).as_ref() == Some(target) {
            let token = self.emitter.nullable_member(input, "GetValueOrDefault")?;
            self.stream.emit(Instruction::LoadLocalAddress(slot));
            self.stream.call_effect(Instruction::Call(token), 1, 1);
            return Ok(());
        }
        self.stream.emit(Instruction::LoadLocal(slot));
        if input != target && !target.is_error() {
            // What was tested was the box, so that is what is narrowed.
            self.box_if_a_value(input)?;
            // `unbox.any` unboxes a value type and behaves as `castclass` on a
            // reference one, so one instruction covers both.
            let token = self.emitter.type_token(target)?;
            self.stream.emit(Instruction::UnboxAny(token));
        }
        Ok(())
    }

    /// The pattern of an arm or a label, with its `when` clause.
    fn emit_arm_test(
        &mut self,
        slot: u16,
        input: &Type,
        pattern: &BoundPattern,
        when: Option<&BoundExpression>,
        on_fail: Label,
    ) -> Result<(), EmitError> {
        self.emit_pattern_test(slot, input, pattern, on_fail)?;
        if let Some(when) = when {
            self.emit_expression(when, true)?;
            self.stream.emit(Instruction::BranchIfFalse(on_fail));
        }
        Ok(())
    }

    // -- switch ------------------------------------------------------------

    fn emit_switch_statement(
        &mut self,
        governing: &BoundExpression,
        sections: &[BoundSwitchSection],
    ) -> Result<(), EmitError> {
        let slot = self.temporary(&governing.ty)?;
        self.emit_expression(governing, true)?;
        self.stream.emit(Instruction::StoreLocal(slot));
        let patterns: Vec<&BoundPattern> = sections
            .iter()
            .flat_map(|section| &section.labels)
            .filter_map(|label| match label {
                BoundSwitchLabel::Case(case) => Some(&case.pattern),
                BoundSwitchLabel::Default => None,
            })
            .collect();
        let outer = self.begin_match(slot, &patterns)?;

        let end = self.stream.label();
        let bodies: Vec<Label> = sections.iter().map(|_| self.stream.label()).collect();
        let mut default = None;
        // What `goto case` can name: the constant each section answers to, and
        // where the `default` section begins.
        let mut targets = CaseTargets {
            depth: self.protected,
            ..CaseTargets::default()
        };

        // Every test comes first, in source order, and jumps to the body it
        // belongs to; `default` is where the last test falls through to.
        for (section, body) in sections.iter().zip(&bodies) {
            for label in &section.labels {
                match label {
                    BoundSwitchLabel::Default => {
                        default = Some(*body);
                        targets.default = Some(*body);
                    }
                    BoundSwitchLabel::Case(case) => {
                        if let Some(key) = self.case_key(&case.pattern, &governing.ty) {
                            targets.values.push((key, *body));
                        }
                        let next = self.stream.label();
                        self.emit_arm_test(
                            slot,
                            &governing.ty,
                            &case.pattern,
                            case.when.as_ref(),
                            next,
                        )?;
                        self.stream.emit(Instruction::Branch(*body));
                        self.stream.mark(next);
                    }
                }
            }
        }
        self.stream
            .emit(Instruction::Branch(default.unwrap_or(end)));
        self.end_match(outer);

        self.breaks.push((end, self.protected));
        self.cases.push(targets);
        for (section, body) in sections.iter().zip(&bodies) {
            self.stream.mark(*body);
            for statement in &section.statements {
                self.emit_statement(statement)?;
            }
        }
        self.cases.pop();
        self.breaks.pop();
        self.stream.mark(end);
        Ok(())
    }

    fn emit_switch_expression(
        &mut self,
        governing: &BoundExpression,
        arms: &[BoundSwitchArm],
        ty: &Type,
    ) -> Result<(), EmitError> {
        let slot = self.temporary(&governing.ty)?;
        self.emit_expression(governing, true)?;
        self.stream.emit(Instruction::StoreLocal(slot));

        let result = self.temporary(ty)?;
        let end = self.stream.label();
        let patterns: Vec<&BoundPattern> = arms.iter().map(|arm| &arm.pattern).collect();
        let outer = self.begin_match(slot, &patterns)?;
        for arm in arms {
            let next = self.stream.label();
            self.emit_arm_test(slot, &governing.ty, &arm.pattern, arm.when.as_ref(), next)?;
            // The arm's value is not part of the match: a pattern in it is
            // a match of its own.
            let within = self.pattern_share.take();
            self.emit_expression(&arm.value, true)?;
            self.pattern_share = within;
            self.stream.emit(Instruction::StoreLocal(result));
            self.stream.emit(Instruction::Branch(end));
            self.stream.mark(next);
        }

        self.end_match(outer);
        // Falling off the end means no arm matched, which is what the runtime
        // has an exception for; `csc` throws the same one — the program's
        // own, where it declares one, as for every type the language names.
        let exception =
            self.source_constructor("System.Runtime.CompilerServices.SwitchExpressionException")?;
        let exception = match exception {
            Some(token) => token,
            None => self.emitter.framework_member(
                "System.Runtime.CompilerServices.SwitchExpressionException",
                ".ctor",
                true,
                &SigType::Primitive(ElementType::Void),
                &[],
            ),
        };
        self.stream
            .call_effect(Instruction::NewObject(exception), 0, 1);
        self.stream.emit(Instruction::Throw);

        self.stream.mark(end);
        self.stream.emit(Instruction::LoadLocal(result));
        Ok(())
    }

    // -- try ---------------------------------------------------------------

    /// `try`/`catch`/`finally`, as the nested regions the runtime wants.
    ///
    /// A clause with both catches and a `finally` is two regions, not one: the
    /// catches guard the body, and the `finally` guards the body *and* the
    /// catches, because it has to run however the whole thing is left.
    fn emit_try(
        &mut self,
        body: &BoundStatement,
        catches: &[BoundCatch],
        finally: Option<&BoundStatement>,
    ) -> Result<(), EmitError> {
        let end = self.stream.label();
        let outer_start = self.stream.label();
        let inner_start = self.stream.label();
        let inner_end = self.stream.label();

        self.protected += 1;
        self.emit_region_entry(&[outer_start, inner_start])?;
        self.emit_statement(body)?;
        self.emit_region_exit();
        self.protected -= 1;
        self.stream.emit(Instruction::Leave(end));
        self.stream.mark(inner_end);

        for catch in catches {
            let region = self.emit_catch(catch, inner_start, inner_end, end)?;
            self.stream.region(region);
        }

        if let Some(finally) = finally {
            let outer_end = self.stream.label();
            let handler_start = self.stream.label();
            let handler_end = self.stream.label();
            self.stream.mark(outer_end);
            self.stream.mark(handler_start);
            let suspended = self.begin_guarded_finally();
            self.protected += 1;
            self.emit_statement(finally)?;
            self.protected -= 1;
            self.end_guarded_finally(suspended);
            self.stream.emit(Instruction::EndFinally);
            self.stream.mark(handler_end);
            self.stream.region(ExceptionRegion {
                kind: HandlerKind::Finally,
                try_start: outer_start,
                try_end: outer_end,
                handler_start,
                handler_end,
            });
        }

        self.stream.mark(end);
        Ok(())
    }

    /// `using`, which is the `try`/`finally` it has always been.
    ///
    /// Several resources nest rather than sharing one region, so the second is
    /// disposed before the first however the block is left — which is the
    /// order C# promises and the order nesting gives for nothing.
    fn emit_using(
        &mut self,
        resources: &[BoundUsingResource],
        body: &BoundStatement,
    ) -> Result<(), EmitError> {
        let Some((first, rest)) = resources.split_first() else {
            return self.emit_statement(body);
        };

        self.begin_store(first.local);
        self.emit_expression(&first.value, true)?;
        self.end_store(first.local);

        let end = self.stream.label();
        let try_start = self.stream.label();
        let try_end = self.stream.label();
        self.protected += 1;
        self.emit_region_entry(&[try_start])?;
        if rest.is_empty() {
            self.emit_statement(body)?;
        } else {
            self.emit_using(rest, body)?;
        }
        self.emit_region_exit();
        self.protected -= 1;
        self.stream.emit(Instruction::Leave(end));
        self.stream.mark(try_end);

        let handler_start = self.stream.label();
        let handler_end = self.stream.label();
        self.stream.mark(handler_start);
        let suspended = self.begin_guarded_finally();
        self.emit_dispose(first)?;
        self.end_guarded_finally(suspended);
        self.stream.emit(Instruction::EndFinally);
        self.stream.mark(handler_end);
        self.stream.region(ExceptionRegion {
            kind: HandlerKind::Finally,
            try_start,
            try_end,
            handler_start,
            handler_end,
        });
        self.stream.mark(end);
        Ok(())
    }

    /// `lock (o) { ... }`, which C# spells out as a `try`/`finally` around
    /// `Monitor.Enter` and `Monitor.Exit`.
    ///
    /// The object is held in a local so that the `finally` unlocks the very
    /// one that was locked, whatever the expression would say by then, and a
    /// `bool` records whether `Enter` got that far: an exception between
    /// taking the lock and entering the `try` would otherwise leave the
    /// `finally` unlocking something it never locked.
    fn emit_lock(
        &mut self,
        value: &BoundExpression,
        held: LocalId,
        taken: LocalId,
        body: &BoundStatement,
    ) -> Result<(), EmitError> {
        let object = SigType::Primitive(ElementType::Object);
        let boolean = SigType::Primitive(ElementType::Boolean);
        let enter = self.emitter.framework_member(
            "System.Threading.Monitor",
            "Enter",
            false,
            &SigType::Primitive(ElementType::Void),
            &[object.clone(), SigType::ByRef(Box::new(boolean))],
        );
        let exit = self.emitter.framework_member(
            "System.Threading.Monitor",
            "Exit",
            false,
            &SigType::Primitive(ElementType::Void),
            &[object],
        );

        self.begin_store(held);
        self.emit_expression(value, true)?;
        self.end_store(held);
        self.begin_store(taken);
        self.stream.emit(Instruction::LoadInt32(0));
        self.end_store(taken);

        let end = self.stream.label();
        let try_start = self.stream.label();
        let try_end = self.stream.label();
        self.protected += 1;
        self.emit_region_entry(&[try_start])?;
        self.load_local(held);
        self.load_local_address(taken);
        self.stream.call_effect(Instruction::Call(enter), 2, 0);
        self.emit_statement(body)?;
        self.emit_region_exit();
        self.protected -= 1;
        self.stream.emit(Instruction::Leave(end));
        self.stream.mark(try_end);

        let handler_start = self.stream.label();
        let handler_end = self.stream.label();
        self.stream.mark(handler_start);
        let suspended = self.begin_guarded_finally();
        let unlocked = self.stream.label();
        self.load_local(taken);
        self.stream.emit(Instruction::BranchIfFalse(unlocked));
        self.load_local(held);
        self.stream.call_effect(Instruction::Call(exit), 1, 0);
        self.stream.mark(unlocked);
        self.end_guarded_finally(suspended);
        self.stream.emit(Instruction::EndFinally);
        self.stream.mark(handler_end);
        self.stream.region(ExceptionRegion {
            kind: HandlerKind::Finally,
            try_start,
            try_end,
            handler_start,
            handler_end,
        });
        self.stream.mark(end);
        Ok(())
    }

    fn emit_dispose(&mut self, resource: &BoundUsingResource) -> Result<(), EmitError> {
        // `using (null)` holds nothing, and there is nothing to dispose; a
        // `dynamic` resource is disposed as the `IDisposable` the resource
        // after it converted it to.
        let declared = self
            .body
            .locals
            .get(resource.local.0 as usize)
            .map_or_else(|| resource.value.ty.clone(), |local| local.ty.clone());
        if resource.dispose.is_none()
            && (matches!(resource.value.ty, Type::Null) || matches!(declared, Type::Dynamic))
        {
            return Ok(());
        }
        let Some(dispose) = resource.dispose else {
            return Err(EmitError::new(format!(
                "`using` needs a `Dispose` on `{}`",
                resource
                    .value
                    .ty
                    .display(self.emitter.compilation.symbols())
            )));
        };
        let local = resource.local;
        // `if (r.HasValue) r.GetValueOrDefault().Dispose();` for a `T?`,
        // whose `T` is disposed from a copy, the way Roslyn writes it.
        if let Some(inside) = self.emitter.binder.nullable_underlying(&declared) {
            let has_value = self.emitter.nullable_member(&declared, "get_HasValue")?;
            let get = self
                .emitter
                .nullable_member(&declared, "GetValueOrDefault")?;
            let token = self.method_token_on(dispose, Some(&inside))?;
            let skip = self.stream.label();
            let copy = self.temporary(&inside)?;
            self.load_local_address(local);
            self.stream.call_effect(Instruction::Call(has_value), 1, 1);
            self.stream.emit(Instruction::BranchIfFalse(skip));
            self.load_local_address(local);
            self.stream.call_effect(Instruction::Call(get), 1, 1);
            self.stream.emit(Instruction::StoreLocal(copy));
            self.stream.emit(Instruction::LoadLocalAddress(copy));
            self.emit_struct_dispose(dispose, token, &inside)?;
            self.stream.mark(skip);
            return Ok(());
        }
        // A type parameter may be a struct or a class: it is compared with
        // `null` boxed — a struct never is — and called through a
        // `constrained.` call on its address, which suits both.
        if let Type::TypeParameter(_) = &declared {
            let token = self.method_token_on(dispose, Some(&declared))?;
            let constraint = self.emitter.type_token(&declared)?;
            let skip = self.stream.label();
            let symbols = self.emitter.compilation.symbols();
            let never_null = matches!(&declared, Type::TypeParameter(parameter)
                if symbols
                    .get(*parameter)
                    .as_type_parameter()
                    .is_some_and(|detail| detail.value_type));
            if !never_null {
                self.load_local(local);
                self.stream.emit(Instruction::Box(constraint));
                self.stream.emit(Instruction::BranchIfFalse(skip));
            }
            self.load_local_address(local);
            self.stream.emit(Instruction::Constrained(constraint));
            self.stream
                .call_effect(Instruction::CallVirtual(token), 1, 0);
            self.stream.mark(skip);
            return Ok(());
        }
        let token = self.method_token_on(dispose, Some(&resource.value.ty))?;
        // A reference that was never assigned is not disposed; a value type
        // cannot be null, so it has nothing to check — and its method is
        // called on its address rather than dispatched through a vtable it
        // does not have.
        let value_type = self.emitter.is_value_type(&resource.value.ty);
        if value_type {
            self.load_local_address(local);
            self.emit_struct_dispose(dispose, token, &resource.value.ty)?;
            return Ok(());
        }
        let skip = self.stream.label();
        self.load_local(local);
        self.stream.emit(Instruction::BranchIfFalse(skip));
        self.load_local(local);
        self.stream
            .call_effect(Instruction::CallVirtual(token), 1, 0);
        self.stream.mark(skip);
        Ok(())
    }

    /// Calls `Dispose` on a struct whose address is on the stack.
    ///
    /// A `Dispose` the struct implements explicitly is the interface's method
    /// (`ReadOnlySpan<T>.Enumerator` has only that one), reached through the
    /// struct with a `constrained.` call rather than by boxing it — which a
    /// `ref struct` could not survive anyway.
    fn emit_struct_dispose(
        &mut self,
        dispose: SymbolId,
        token: Token,
        ty: &Type,
    ) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let through_interface = symbols.get(dispose).container.is_some_and(|container| {
            symbols.get(container).type_kind() == Some(TypeKind::Interface)
        });
        if through_interface {
            let constraint = self.emitter.type_token(ty)?;
            self.stream.emit(Instruction::Constrained(constraint));
            self.stream
                .call_effect(Instruction::CallVirtual(token), 1, 0);
        } else {
            self.stream.call_effect(Instruction::Call(token), 1, 0);
        }
        Ok(())
    }

    /// Stores the exception on the stack into the `catch` variable, which a
    /// lambda or a state machine may have moved into a field: the object the
    /// field belongs to has to go under the value, so the value waits in a
    /// slot.
    fn store_caught(&mut self, local: LocalId) -> Result<(), EmitError> {
        self.store_top(local)
    }

    /// Stores the value on the stack into a local, wherever the local lives:
    /// a slot, or a field of a display class or a state machine. A pattern
    /// variable declared in an iterator is one of the latter, and writing
    /// the slot it would otherwise have had leaves the field empty.
    fn store_top(&mut self, local: LocalId) -> Result<(), EmitError> {
        match self.captured_local(local) {
            Some(capture) => {
                let ty = self.local_types[local.0 as usize].clone();
                let parked = self.temporary(&ty)?;
                self.stream.emit(Instruction::StoreLocal(parked));
                self.push_holder(capture.holder);
                self.stream.emit(Instruction::LoadLocal(parked));
                self.stream.emit(Instruction::StoreField(capture.token));
            }
            None => self.stream.emit(Instruction::StoreLocal(self.slot(local))),
        }
        Ok(())
    }

    fn emit_catch(
        &mut self,
        catch: &BoundCatch,
        try_start: Label,
        try_end: Label,
        end: Label,
    ) -> Result<ExceptionRegion, EmitError> {
        let token = self.emitter.type_token(&catch.exception_type)?;
        let local = catch.local;

        // A `when` clause becomes a filter, which the runtime runs with the
        // exception on the stack before it unwinds anything.
        let kind = match &catch.filter {
            None => HandlerKind::Catch(token),
            Some(condition) => {
                let filter_start = self.stream.label();
                let keep = self.stream.label();
                let decided = self.stream.label();
                self.stream.mark(filter_start);
                self.stream.emit(Instruction::IsInstance(token));
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::BranchIfTrue(keep));
                // Not the right type: answer no without running the condition.
                self.stream.emit(Instruction::Pop);
                self.stream.emit(Instruction::LoadInt32(0));
                self.stream.emit(Instruction::Branch(decided));
                self.stream.mark(keep);
                match local {
                    Some(local) => self.store_caught(local)?,
                    None => self.stream.emit(Instruction::Pop),
                }
                self.emit_expression(condition, true)?;
                self.stream.mark(decided);
                self.stream.emit(Instruction::EndFilter);
                HandlerKind::Filter(filter_start)
            }
        };

        let handler_start = self.stream.label();
        let handler_end = self.stream.label();
        self.stream.mark(handler_start);
        // The handler is entered with the exception pushed. A filter has
        // already stored it, so there it is only in the way.
        match (local, &catch.filter) {
            (_, Some(_)) => self.stream.emit(Instruction::Pop),
            (Some(local), None) => self.store_caught(local)?,
            (None, None) => self.stream.emit(Instruction::Pop),
        }
        self.protected += 1;
        self.emit_statement(&catch.body)?;
        self.protected -= 1;
        self.stream.emit(Instruction::Leave(end));
        self.stream.mark(handler_end);

        Ok(ExceptionRegion {
            kind,
            try_start,
            try_end,
            handler_start,
            handler_end,
        })
    }

    // -- expressions -------------------------------------------------------

    /// Emits an expression, leaving exactly one value on the stack when `used`
    /// and none otherwise.
    pub(crate) fn emit_expression(
        &mut self,
        expression: &BoundExpression,
        used: bool,
    ) -> Result<(), EmitError> {
        // `checked` and `unchecked` are regions of the source: the innermost
        // one around the expression says how its arithmetic overflows.
        if self.body.checked_regions.is_empty() {
            return self.emit_expression_in(expression, used);
        }
        let was = self.checked;
        let span = expression.span;
        if let Some((_, checked)) = self
            .body
            .checked_regions
            .iter()
            .filter(|(region, _)| region.start() <= span.start() && span.end() <= region.end())
            .min_by_key(|(region, _)| region.length())
        {
            self.checked = *checked;
        }
        let result = self.emit_expression_in(expression, used);
        self.checked = was;
        result
    }

    fn emit_expression_in(
        &mut self,
        expression: &BoundExpression,
        used: bool,
    ) -> Result<(), EmitError> {
        match &expression.kind {
            BoundExpressionKind::Assignment { target, value } => {
                return self.emit_assignment(target, value, used);
            }
            BoundExpressionKind::EventAssignment {
                receiver,
                event,
                add,
                handler,
            } => {
                return self.emit_event_assignment(receiver.as_deref(), *event, *add, handler);
            }
            BoundExpressionKind::CompoundAssignment {
                target,
                operator,
                value,
            } => {
                return self.emit_compound_assignment(
                    target,
                    *operator,
                    value,
                    &expression.ty,
                    used,
                );
            }
            BoundExpressionKind::Increment {
                target,
                operator,
                prefix,
                method,
            } => {
                return self.emit_increment(
                    target,
                    *operator,
                    *prefix,
                    *method,
                    &expression.ty,
                    used,
                );
            }
            // A call the runtime binds is told whether its value is wanted.
            BoundExpressionKind::Dynamic(dynamic) => {
                if self.emit_dynamic(dynamic, &expression.ty, used)? && !used {
                    self.stream.emit(Instruction::Pop);
                }
                return Ok(());
            }
            // A `?.` whose value nothing reads is an `if` around the access:
            // there is no `T?` to make, which matters where the access gives
            // a `ref struct` that no `Nullable<T>` can hold.
            BoundExpressionKind::ConditionalAccess { .. } if !used => {
                let discarded =
                    BoundExpression::new(expression.kind.clone(), Type::Void, expression.span);
                self.emit_value(&discarded)?;
                return Ok(());
            }
            _ => {}
        }

        let pushed = self.emit_value(expression)?;
        match (pushed, used) {
            (true, false) => self.stream.emit(Instruction::Pop),
            (false, true) => {
                return Err(EmitError::new(
                    "an expression of type `void` was used as a value",
                ));
            }
            _ => {}
        }
        Ok(())
    }

    /// Emits an expression for its value. Returns whether anything was pushed,
    /// which is false only for a call that returns `void`.
    fn emit_value(&mut self, expression: &BoundExpression) -> Result<bool, EmitError> {
        // A constant expression is its value (§12.23): `0.0 / 0.0` is loaded
        // as the NaN it folds to, not divided at run time.
        if matches!(
            expression.kind,
            BoundExpressionKind::Binary { .. } | BoundExpressionKind::Unary { .. }
        ) && matches!(
            self.emitter.special_type_of(&expression.ty),
            Some(
                SpecialType::Boolean
                    | SpecialType::Char
                    | SpecialType::SByte
                    | SpecialType::Byte
                    | SpecialType::Int16
                    | SpecialType::UInt16
                    | SpecialType::Int32
                    | SpecialType::UInt32
                    | SpecialType::Int64
                    | SpecialType::UInt64
                    | SpecialType::Single
                    | SpecialType::Double
                    | SpecialType::String
            )
        ) && let Some(value) = self.emitter.binder.folded(expression)
        {
            self.emit_constant(&value, &expression.ty)?;
            return Ok(true);
        }
        // So is a floating constant cast to an integer: `(int)3.7` is 3,
        // and one its type has no room for — `unchecked((int)1e10)` — is the
        // zero it folds to, where the conversion left to run gives whatever
        // the processor or the runtime's version gives.
        if let BoundExpressionKind::Conversion { operand, .. } = &expression.kind
            && matches!(
                self.emitter.special_type_of(&expression.ty),
                Some(
                    SpecialType::Char
                        | SpecialType::SByte
                        | SpecialType::Byte
                        | SpecialType::Int16
                        | SpecialType::UInt16
                        | SpecialType::Int32
                        | SpecialType::UInt32
                        | SpecialType::Int64
                        | SpecialType::UInt64
                )
            )
            && matches!(
                self.emitter.binder.folded(operand),
                Some(ConstantValue::Single(_) | ConstantValue::Double(_))
            )
            && let Some(value) = self.emitter.binder.folded(expression)
        {
            self.emit_constant(&value, &expression.ty)?;
            return Ok(true);
        }
        match &expression.kind {
            // `__arglist` in a varargs method: the handle on what it was
            // given past its parameters.
            BoundExpressionKind::ArgListHandle => {
                self.stream.emit(Instruction::ArgList);
            }
            BoundExpressionKind::ArgList(_) => {
                return Err(EmitError::new(
                    "`__arglist(...)` is only an argument to a varargs method",
                ));
            }
            BoundExpressionKind::Literal(value) => {
                self.emit_constant(value, &expression.ty)?;
            }
            // A captured variable stopped being a local: it lives in the
            // display class, and every read of it is a field read.
            // A `ref` local holds an address: reading the name reads through
            // it.
            BoundExpressionKind::Local(local) if self.is_by_ref_local(*local) => {
                let kind = self.indirect_kind(&expression.ty)?;
                self.stream.emit(Instruction::LoadLocal(self.slot(local)));
                self.stream.emit(Instruction::LoadIndirect(kind));
            }
            BoundExpressionKind::Local(local) => match self.captured_local(*local) {
                Some(capture) => {
                    self.push_holder(capture.holder);
                    self.stream.emit(Instruction::LoadField(capture.token));
                }
                None => self.stream.emit(Instruction::LoadLocal(self.slot(local))),
            },
            BoundExpressionKind::Parameter(symbol) => match self.captured_parameter(*symbol) {
                Some(capture) => {
                    self.push_holder(capture.holder);
                    self.stream.emit(Instruction::LoadField(capture.token));
                }
                None => {
                    let index = self.argument_index(*symbol)?;
                    self.stream.emit(Instruction::LoadArgument(index));
                    // A `ref` parameter holds an address; reading it reads
                    // what that address points at.
                    if self.is_by_reference(*symbol) {
                        let kind = self.indirect_kind(&expression.ty)?;
                        self.stream.emit(Instruction::LoadIndirect(kind));
                    }
                }
            },
            BoundExpressionKind::This | BoundExpressionKind::Base => match self.captured_this() {
                Some(capture) => {
                    self.push_holder(capture.holder);
                    self.stream.emit(Instruction::LoadField(capture.token));
                }
                None => {
                    self.stream.emit(Instruction::LoadArgument(0));
                    // Inside a value type's method `this` is an address, and
                    // what is wanted here is the value: `new Enumerator(this)`
                    // passes what the struct holds, not where it is. `base`
                    // there is `ValueType`, which the struct is only boxed.
                    if self.instance && self.in_value_type {
                        if matches!(expression.kind, BoundExpressionKind::Base) {
                            let own = self.self_type.clone();
                            let token = self.emitter.type_token(&own)?;
                            self.stream
                                .emit(Instruction::LoadIndirect(IndirectKind::Object(token)));
                            self.stream.emit(Instruction::Box(token));
                        } else {
                            let kind = self.indirect_kind(&expression.ty)?;
                            self.stream.emit(Instruction::LoadIndirect(kind));
                        }
                    }
                }
            },
            BoundExpressionKind::Field { receiver, field } => {
                // A `const` field and an enum member have no storage to read:
                // the value is in metadata, and the code carries it directly.
                if let Some(constant) = self.emitter.constant_of(*field) {
                    self.emit_constant(&constant, &expression.ty)?;
                    return Ok(true);
                }
                let token =
                    self.field_token_on(*field, receiver.as_deref().map(|value| &value.ty))?;
                match receiver.as_deref().filter(|value| !is_type_name(value)) {
                    Some(receiver) => {
                        self.emit_expression(receiver, true)?;
                        // A field of a `T : class` is read off the boxed
                        // value, which is the value itself at run time.
                        if matches!(receiver.ty, Type::TypeParameter(_)) {
                            self.box_if_needed(&receiver.ty)?;
                        }
                        self.stream.emit(Instruction::LoadField(token));
                    }
                    None => self.stream.emit(Instruction::LoadStaticField(token)),
                }
                // A `ref` field holds a reference, and reading the field
                // reads what that points at.
                if self.is_ref_field(*field) {
                    let kind = self.indirect_kind(&expression.ty)?;
                    self.stream.emit(Instruction::LoadIndirect(kind));
                }
            }
            BoundExpressionKind::Property { receiver, property } => {
                // `T.Zero` where `T : INumberBase<T>`: the interface's static
                // abstract getter, reached through the type parameter.
                let declared_getter = {
                    let symbols = self.emitter.compilation.symbols();
                    symbols
                        .get(*property)
                        .as_property()
                        .and_then(|detail| detail.getter)
                };
                if receiver.as_deref().is_none_or(is_type_name)
                    && let Some(getter) = declared_getter
                    && let Some((parameter, construction)) = self.static_abstract_constraint(getter)
                {
                    let token = self.constraint_member(getter, &construction)?;
                    let constraint = self.emitter.type_token(&Type::TypeParameter(parameter))?;
                    self.stream.emit(Instruction::Constrained(constraint));
                    self.stream.call_effect(Instruction::Call(token), 0, 1);
                    self.read_through_reference(*property, &expression.ty)?;
                    return Ok(true);
                }
                let getter = self
                    .emitter
                    .read_accessor(*property, receiver.as_ref().map(|receiver| &receiver.ty))?;
                if let Some(receiver) = receiver.as_deref().filter(|value| !is_type_name(value)) {
                    match self.counted_through(receiver, *property) {
                        Some(slot) => self.push_address(Address::HeldLocal(slot)),
                        None => self.emit_member_receiver(receiver, *property)?,
                    }
                    let instruction = self.receiver_call(receiver, *property, getter)?;
                    self.stream.call_effect(instruction, 1, 1);
                } else {
                    self.stream.call_effect(Instruction::Call(getter), 0, 1);
                }
                self.read_through_reference(*property, &expression.ty)?;
            }
            // `ref x` pushes where `x` is, not what it holds; `in x` a
            // reference nothing will write through.
            BoundExpressionKind::RefArgument { operand, kind } => {
                if *kind == rustlyn_semantics::RefKind::In {
                    self.emit_readonly_reference(operand)?;
                } else {
                    self.emit_reference(operand)?;
                }
            }
            // It never comes back, so whatever wanted a value here is
            // unreachable — which IL agrees with, and why saying a value was
            // pushed costs nothing: the depths are worked out by walking from
            // the places control can actually arrive, and none of them is
            // after a `throw`.
            BoundExpressionKind::Throw(thrown) => {
                match thrown {
                    Some(thrown) => {
                        self.emit_expression(thrown, true)?;
                        self.stream.emit(Instruction::Throw);
                    }
                    None => self.stream.emit(Instruction::Rethrow),
                }
                return Ok(true);
            }
            // `(a, b)` is a `ValueTuple<A, B>` made of the two values, and the
            // constructor takes them in order.
            BoundExpressionKind::TupleCreation(values) => {
                self.emit_tuple_creation(values, &expression.ty)?;
            }
            // Each in order; only the last leaves anything behind, and where
            // nothing wanted a value none of them does.
            BoundExpressionKind::Sequence(steps) => {
                let Some((last, rest)) = steps.split_last() else {
                    return Ok(false);
                };
                // Everything before the last is done for what it does; the
                // last is what the sequence *is*, so its value is the whole
                // sequence's. An assignment can be the last one — taking a
                // tuple apart ends in one — and assignments are emitted
                // before this path rather than in it.
                for step in rest {
                    self.emit_expression(step, false)?;
                }
                let wanted = !matches!(last.ty, Type::Void);
                self.emit_expression(last, wanted)?;
                return Ok(wanted);
            }
            // What the spiller did not move out of the expression can still
            // run in place where nothing is on the stack beneath it: `var x
            // = [..items]` walks `items` with the stack empty.
            BoundExpressionKind::SpillSequence { statements, value } => {
                if self.stream.end_depth() != Some(0) {
                    return Err(EmitError::new(
                        "a loop inside an expression that has values beneath it on the stack",
                    ));
                }
                for statement in statements {
                    self.emit_statement(statement)?;
                }
                let wanted = !matches!(value.ty, Type::Void);
                self.emit_expression(value, wanted)?;
                return Ok(wanted);
            }
            BoundExpressionKind::SizeOf(ty) => {
                let token = self.emitter.type_token(ty)?;
                self.stream.emit(Instruction::SizeOf(token));
            }
            // `*p` reads through the pointer.
            BoundExpressionKind::Dereference { operand } => {
                self.element_access = is_element_access(expression);
                self.emit_expression(operand, true)?;
                self.element_access = false;
                let kind = self.indirect_kind(&expression.ty)?;
                self.stream.emit(Instruction::LoadIndirect(kind));
            }
            // `&x` is the variable's address as an unmanaged pointer. A
            // `fixed` buffer's may be in something the collector moves, and
            // stays a managed one until it is stored somewhere, as Roslyn
            // leaves it.
            BoundExpressionKind::AddressOf { operand } => {
                self.emit_reference(operand)?;
                if !self.is_fixed_buffer(operand) {
                    self.stream.emit(Instruction::ConvertU);
                }
            }
            BoundExpressionKind::StackAlloc { .. }
                if self.hoisted_stackallocs.contains_key(&expression.span) =>
            {
                let slot = self.hoisted_stackallocs[&expression.span];
                self.stream.emit(Instruction::LoadLocal(slot));
            }
            BoundExpressionKind::StackAlloc {
                element,
                count,
                elements,
                span,
            } => {
                self.emit_stackalloc(element, count, elements, span.as_ref())?;
            }
            BoundExpressionKind::Await { .. } => {
                // The method was refused a state machine, or the `await` is
                // somewhere the rewrite did not reach; the reason says which.
                let refusal = self
                    .owner
                    .and_then(|owner| self.emitter.async_refusal(MachineKey::Member(owner)));
                return Err(EmitError::new(refusal.unwrap_or_else(|| {
                    format!(
                        "an `await` in a position the state machine does not reach{}",
                        self.at(expression.span)
                    )
                })));
            }
            BoundExpressionKind::MethodGroup { .. } => {
                return Err(EmitError::new(format!(
                    "a method group is not a value until it is converted to a delegate{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::UnboundLambda(_) => {
                return Err(EmitError::new(format!(
                    "a lambda has no type until it is converted to a delegate{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::UnboundCollection(_) => {
                return Err(EmitError::new(format!(
                    "a collection expression has no type until something says what it is{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::UnboundCreation(_) => {
                return Err(EmitError::new(format!(
                    "`new(...)` has no type until something says what is being made{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::UnboundConditional(_) => {
                return Err(EmitError::new(format!(
                    "`c ? a : b` has no type until something says what its branches are{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::UnboundSwitch(_) => {
                return Err(EmitError::new(format!(
                    "a `switch` expression has no type until something says what its arms are{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::Lambda(index) => {
                if self.is_expression_tree_type(&expression.ty) {
                    self.emit_expression_tree(&expression.ty, *index)?;
                } else {
                    self.emit_lambda(&expression.ty, *index)?;
                }
            }
            BoundExpressionKind::DelegateCreation {
                method,
                receiver,
                virtual_dispatch,
                type_arguments,
            } => {
                self.emit_delegate_creation(
                    &expression.ty,
                    *method,
                    receiver.as_deref(),
                    *virtual_dispatch,
                    type_arguments,
                )?;
            }
            BoundExpressionKind::Call {
                receiver,
                method,
                type_arguments,
                arguments,
                virtual_call,
            } => {
                return self.emit_call(&CallSite {
                    receiver: receiver.as_deref(),
                    method: *method,
                    type_arguments,
                    arguments,
                    virtual_call: *virtual_call,
                    result: &expression.ty,
                    read: true,
                });
            }
            // `&M` is the method's address, which is all a function pointer
            // holds.
            BoundExpressionKind::MethodAddress {
                method,
                type_arguments,
            } => {
                let token = self.method_token(*method)?;
                let token = self.instantiated(token, type_arguments)?;
                self.stream.emit(Instruction::LoadFunction(token));
            }
            BoundExpressionKind::FunctionPointerCall { pointer, arguments } => {
                return self.emit_function_pointer_call(pointer, arguments, &expression.ty, true);
            }
            // `a?.B` evaluates `a` once — that is the whole reason it exists
            // rather than `a == null ? null : a.B` — so it goes into a local
            // that the access inside reads.
            BoundExpressionKind::ConditionalAccess { receiver, access } => {
                let missing = self.stream.label();
                let end = self.stream.label();
                // `x[0]?.Dispose()` on a `T` that may be a struct calls the
                // element, not a copy of it; one that turns out a class is
                // read once and tested for null (as `csc` does it).
                // A `readonly` field is read, not reached: what is called on
                // it works on a copy, outside a constructor.
                let by_reference = match &receiver.ty {
                    Type::TypeParameter(parameter) => {
                        !self.is_a_struct_parameter(*parameter)
                            && !receiver
                                .ty
                                .is_reference_type(self.emitter.compilation.symbols())
                            && !self.readonly_field_outside_constructor(receiver)
                            && (self.address_of(receiver)?.is_some()
                                || self.lives_somewhere(receiver))
                    }
                    _ => false,
                };
                if by_reference {
                    let Receiver::At(Address::HeldLocal(held)) =
                        self.property_receiver(receiver)?
                    else {
                        return Err(EmitError::new("a `?.` receiver with nowhere to live"));
                    };
                    let token = self.emitter.type_token(&receiver.ty)?;
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream
                        .emit(Instruction::LoadIndirect(IndirectKind::Object(token)));
                    self.stream.emit(Instruction::Box(token));
                    self.stream.emit(Instruction::BranchIfFalse(missing));
                    self.accessing.push(held);
                    self.accessing_by_reference.push(true);
                    let void = matches!(expression.ty, Type::Void);
                    let result = self.emit_expression(access, !void);
                    self.accessing.pop();
                    self.accessing_by_reference.pop();
                    result?;
                    if !void
                        && self
                            .emitter
                            .nullable_underlying(&expression.ty)
                            .is_some_and(|inner| inner == access.ty)
                    {
                        let constructor = self.emitter.nullable_constructor(&expression.ty)?;
                        self.stream
                            .call_effect(Instruction::NewObject(constructor), 1, 1);
                    }
                    self.stream.emit(Instruction::Branch(end));
                    self.stream.mark(missing);
                    if !void {
                        self.emit_default(&expression.ty)?;
                    }
                    self.stream.mark(end);
                    return Ok(!void);
                }
                let slot = self.temporary(&receiver.ty)?;
                self.emit_expression(receiver, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                // A `T?` has no null to branch on: it is asked whether it
                // holds anything, and what the access reaches is the value
                // inside rather than the `T?` around it.
                let reached = match self.emitter.nullable_underlying(&receiver.ty) {
                    Some(inner) => {
                        let has_value =
                            self.emitter.nullable_member(&receiver.ty, "get_HasValue")?;
                        self.stream.emit(Instruction::LoadLocalAddress(slot));
                        self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                        self.stream.emit(Instruction::BranchIfFalse(missing));
                        let value = self
                            .emitter
                            .nullable_member(&receiver.ty, "GetValueOrDefault")?;
                        let held = self.temporary(&inner)?;
                        self.stream.emit(Instruction::LoadLocalAddress(slot));
                        self.stream.call_effect(Instruction::Call(value), 1, 1);
                        self.stream.emit(Instruction::StoreLocal(held));
                        held
                    }
                    None => {
                        self.stream.emit(Instruction::LoadLocal(slot));
                        // A `T` has no null to branch on either until it is
                        // boxed, which is nothing at run time where `T` is a
                        // reference and a real box — never null — where it
                        // is a value.
                        if matches!(receiver.ty, Type::TypeParameter(_)) {
                            let token = self.emitter.type_token(&receiver.ty)?;
                            self.stream.emit(Instruction::Box(token));
                        }
                        self.stream.emit(Instruction::BranchIfFalse(missing));
                        slot
                    }
                };
                self.accessing.push(reached);
                self.accessing_by_reference.push(false);
                let void = matches!(expression.ty, Type::Void);
                let result = self.emit_expression(access, !void);
                self.accessing.pop();
                self.accessing_by_reference.pop();
                result?;
                // A value type read through `?.` is handed back as a `T?`,
                // so the value that was just computed has to be put into one.
                if !void
                    && self
                        .emitter
                        .nullable_underlying(&expression.ty)
                        .is_some_and(|inner| inner == access.ty)
                {
                    let constructor = self.emitter.nullable_constructor(&expression.ty)?;
                    self.stream
                        .call_effect(Instruction::NewObject(constructor), 1, 1);
                }
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(missing);
                if !void {
                    // A null receiver gives the default: `null` for a
                    // reference, and — where C# would give a `T?` — the zero
                    // of the value type, which this compiler does not wrap.
                    self.emit_default(&expression.ty)?;
                }
                self.stream.mark(end);
                return Ok(!void);
            }
            BoundExpressionKind::AccessedValue => {
                let slot = *self
                    .accessing
                    .last()
                    .ok_or_else(|| EmitError::new("a `?.` access with no receiver"))?;
                self.stream.emit(Instruction::LoadLocal(slot));
                if self.accessing_by_reference.last().copied().unwrap_or(false) {
                    let kind = self.indirect_kind(&expression.ty)?;
                    self.stream.emit(Instruction::LoadIndirect(kind));
                }
            }
            BoundExpressionKind::ObjectCreation {
                constructor,
                arguments,
                initializers,
            } => {
                // `new T()` on a type parameter: which constructor that is
                // depends on what `T` turns out to be, and only the runtime
                // knows. So too for a `where T : struct`, whose struct may
                // declare a parameterless constructor (C# 10) that zeroing it
                // would not run — Roslyn's `MakeNewT` asks the runtime always.
                if arguments.is_empty() && matches!(expression.ty, Type::TypeParameter(_)) {
                    let token = self.emitter.activator_create(&expression.ty)?;
                    self.stream.call_effect(Instruction::Call(token), 0, 1);
                    self.emit_initializers(initializers, &expression.ty)?;
                    return Ok(true);
                }
                // A value type with no arguments is not constructed, it is
                // zeroed; the runtime provides that and no method exists —
                // unless the struct wrote a parameterless constructor of its
                // own (C# 10), which is then the one to call.
                if arguments.is_empty()
                    && constructor.is_none()
                    && self.emitter.is_value_type(&expression.ty)
                {
                    self.emit_default(&expression.ty)?;
                    self.emit_initializers(initializers, &expression.ty)?;
                    return Ok(true);
                }
                let constructor = constructor.ok_or_else(|| {
                    EmitError::new(format!(
                        "no constructor was resolved for `new {}`",
                        expression.ty.display(self.emitter.compilation.symbols())
                    ))
                })?;
                // A `decimal` zero with no scale is written without its
                // sign, as Roslyn writes one (`decimal.Zero`): `-(decimal.Zero)`
                // folds to a `-0` only a constant operation on it can tell
                // from `0`, and one written out as a value is `0`.
                let unsigned_zero = arguments.len() == 5
                    && self.is_decimal(&expression.ty)
                    && arguments.iter().enumerate().all(|(at, argument)| {
                        matches!(
                            (at, &argument.kind),
                            (
                                0..=2 | 4,
                                BoundExpressionKind::Literal(ConstantValue::Int32(0))
                            ) | (3, BoundExpressionKind::Literal(ConstantValue::Boolean(_)))
                        )
                    });
                for (at, argument) in arguments.iter().enumerate() {
                    if unsigned_zero && at == 3 {
                        self.stream.emit(Instruction::LoadInt32(0));
                        continue;
                    }
                    self.emit_expression(argument, true)?;
                }
                let token = self.method_token_on(constructor, Some(&expression.ty))?;
                self.stream
                    .call_effect(Instruction::NewObject(token), arguments.len(), 1);
                self.emit_initializers(initializers, &expression.ty)?;
            }
            // The object an initializer is initializing: a reference is the
            // one already on the stack, and a value type is a local whose
            // address the members are written through.
            BoundExpressionKind::CreatedObject => match self.creating.last() {
                // A `T` is reached as a value, which the member access boxes:
                // its members are its constraint class's.
                Some(Created::Local(slot)) if matches!(expression.ty, Type::TypeParameter(_)) => {
                    self.stream.emit(Instruction::LoadLocal(*slot));
                }
                Some(Created::Local(slot)) => {
                    self.stream.emit(Instruction::LoadLocalAddress(*slot));
                }
                Some(Created::Held(slot)) => self.stream.emit(Instruction::LoadLocal(*slot)),
                _ => self.stream.emit(Instruction::Dup),
            },
            BoundExpressionKind::ArrayCreation {
                element,
                lengths,
                elements,
            } => self.emit_array_creation(element, lengths, elements)?,
            BoundExpressionKind::ArrayAccess { array, indices } => {
                self.emit_expression(array, true)?;
                if indices.len() > 1 {
                    let get = self.array_member(array, ArrayMember::Get, &expression.ty)?;
                    for index in indices {
                        self.emit_expression(index, true)?;
                    }
                    self.stream
                        .call_effect(Instruction::Call(get), indices.len() + 1, 1);
                } else {
                    let element = self.emitter.type_token(&expression.ty)?;
                    self.emit_single_index(indices)?;
                    self.load_element(&expression.ty, element);
                }
            }
            BoundExpressionKind::ArrayLength { array } => {
                self.emit_expression(array, true)?;
                // `ldlen` reads a vector; a `string[,]` answers `Length`
                // through `System.Array`, as any array may.
                if matches!(array.ty, Type::Array { rank, .. } if rank > 1) {
                    let int = SigType::Primitive(ElementType::I4);
                    let length = self.emitter.framework_member(
                        "System.Array",
                        "get_Length",
                        true,
                        &int,
                        &[],
                    );
                    self.stream
                        .call_effect(Instruction::CallVirtual(length), 1, 1);
                    return Ok(true);
                }
                self.stream.emit(Instruction::LoadLength);
                self.stream.emit(Instruction::ConvertI4);
            }
            BoundExpressionKind::Binary {
                operator,
                left,
                right,
            } => self.emit_binary(*operator, left, right, &expression.ty)?,
            // A unary operator on a `T?` is lifted (§12.4.8): nothing in,
            // nothing out, and otherwise the operator on what is inside,
            // wrapped again.
            BoundExpressionKind::Unary { operator, operand }
                if self.emitter.nullable_underlying(&operand.ty).is_some()
                    && self.emitter.nullable_underlying(&expression.ty).is_some() =>
            {
                let inner = self
                    .emitter
                    .nullable_underlying(&operand.ty)
                    .unwrap_or(Type::Error);
                let slot = self.temporary(&operand.ty)?;
                let has_value = self.emitter.nullable_member(&operand.ty, "get_HasValue")?;
                let value = self
                    .emitter
                    .nullable_member(&operand.ty, "GetValueOrDefault")?;
                let constructor = self.emitter.nullable_constructor(&expression.ty)?;
                let (missing, end) = (self.stream.label(), self.stream.label());
                self.emit_expression(operand, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                self.stream.emit(Instruction::LoadLocalAddress(slot));
                self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                self.stream.emit(Instruction::BranchIfFalse(missing));
                self.stream.emit(Instruction::LoadLocalAddress(slot));
                self.stream.call_effect(Instruction::Call(value), 1, 1);
                match operator {
                    UnaryOperator::Plus => {}
                    UnaryOperator::Minus if self.is_decimal(&inner) => {
                        let decimal = self.decimal_sig();
                        let token = self.emitter.framework_member(
                            "System.Decimal",
                            "op_UnaryNegation",
                            false,
                            &decimal,
                            std::slice::from_ref(&decimal),
                        );
                        self.stream.call_effect(Instruction::Call(token), 1, 1);
                    }
                    UnaryOperator::Minus => self.stream.emit(Instruction::Negate),
                    UnaryOperator::BitwiseNot => self.stream.emit(Instruction::Not),
                    UnaryOperator::LogicalNot => {
                        self.stream.emit(Instruction::LoadInt32(0));
                        self.stream.emit(Instruction::CompareEqual);
                    }
                }
                self.stream
                    .call_effect(Instruction::NewObject(constructor), 1, 1);
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(missing);
                self.emit_default(&expression.ty)?;
                self.stream.mark(end);
            }
            BoundExpressionKind::Unary { operator, operand } => {
                // `-x` in a `checked` region is `0 - x`, so that negating
                // the smallest value traps rather than giving it back.
                let checked_negation = *operator == UnaryOperator::Minus
                    && self.checked
                    && matches!(
                        self.integer_special(&operand.ty),
                        Some(SpecialType::Int32 | SpecialType::Int64)
                    );
                if checked_negation {
                    if self.integer_special(&operand.ty) == Some(SpecialType::Int64) {
                        self.stream.emit(Instruction::LoadInt64(0));
                    } else {
                        self.stream.emit(Instruction::LoadInt32(0));
                    }
                }
                self.emit_expression(operand, true)?;
                match operator {
                    UnaryOperator::Plus => {}
                    UnaryOperator::Minus if checked_negation => {
                        self.stream.emit(Instruction::SubtractOvf);
                    }
                    UnaryOperator::Minus if self.is_decimal(&operand.ty) => {
                        let decimal = self.decimal_sig();
                        let token = self.emitter.framework_member(
                            "System.Decimal",
                            "op_UnaryNegation",
                            false,
                            &decimal,
                            std::slice::from_ref(&decimal),
                        );
                        self.stream.call_effect(Instruction::Call(token), 1, 1);
                    }
                    UnaryOperator::Minus => self.stream.emit(Instruction::Negate),
                    UnaryOperator::BitwiseNot => {
                        self.stream.emit(Instruction::Not);
                        // `~e` on a `ushort` enum is a `ushort` enum: the bits
                        // above it, which `not` just set, are not its.
                        if self.is_enum(&operand.ty) {
                            match self.integer_special(&operand.ty) {
                                Some(SpecialType::SByte) => {
                                    self.stream.emit(Instruction::ConvertI1)
                                }
                                Some(SpecialType::Byte) => self.stream.emit(Instruction::ConvertU1),
                                Some(SpecialType::Int16) => {
                                    self.stream.emit(Instruction::ConvertI2)
                                }
                                Some(SpecialType::UInt16) => {
                                    self.stream.emit(Instruction::ConvertU2);
                                }
                                _ => {}
                            }
                        }
                    }
                    UnaryOperator::LogicalNot => {
                        self.stream.emit(Instruction::LoadInt32(0));
                        self.stream.emit(Instruction::CompareEqual);
                    }
                }
            }
            // Laid out as Roslyn does: the branch goes to the consequence,
            // and the alternative falls through, which is how readers of
            // the IL (decompilers among them) tell the two sides apart.
            // `c ? ref a : ref b` read for its value reads whichever
            // variable was chosen.
            BoundExpressionKind::Conditional {
                consequence,
                alternative,
                ..
            } if is_ref_branch(consequence) && is_ref_branch(alternative) => {
                self.emit_reference(expression)?;
                let kind = self.indirect_kind(&expression.ty)?;
                self.stream.emit(Instruction::LoadIndirect(kind));
            }
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                let taken = self.stream.label();
                let end = self.stream.label();
                self.emit_branch_if_true(condition, taken)?;
                self.emit_expression(alternative, true)?;
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(taken);
                self.emit_expression(consequence, true)?;
                self.stream.mark(end);
            }
            BoundExpressionKind::Conversion {
                operand,
                conversion,
                ..
            } => self.emit_conversion(operand, *conversion, &expression.ty)?,
            // The binder joins every interpolated string once its body is
            // bound; one met here is one no body binding saw.
            BoundExpressionKind::InterpolatedString(parts) => {
                self.emit_interpolated_string(parts)?;
            }
            // `{x,5:N2}` is `string.Format("{0,5:N2}", (object)x)`.
            BoundExpressionKind::StringInsert {
                value,
                alignment,
                format,
            } => {
                let string = SigType::Primitive(ElementType::String);
                let object = SigType::Primitive(ElementType::Object);
                let clauses = rustlyn_semantics::composite_clauses(*alignment, format.as_deref());
                let composite = self
                    .emitter
                    .metadata
                    .user_string(&format!("{{0{clauses}}}"));
                self.stream.emit(Instruction::LoadString(composite));
                self.emit_expression(value, true)?;
                self.box_if_needed(&value.ty)?;
                let call = self.emitter.framework_member(
                    "System.String",
                    "Format",
                    false,
                    &string,
                    &[string.clone(), object],
                );
                self.stream.call_effect(Instruction::Call(call), 2, 1);
            }
            BoundExpressionKind::Switch { governing, arms } => {
                self.emit_switch_expression(governing, arms, &expression.ty)?;
            }
            BoundExpressionKind::IsPattern { operand, pattern } => {
                let slot = self.temporary(&operand.ty)?;
                self.emit_expression(operand, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                let failed = self.stream.label();
                let end = self.stream.label();
                let outer = self.begin_match(slot, &[pattern])?;
                self.emit_pattern_test(slot, &operand.ty, pattern, failed)?;
                self.end_match(outer);
                self.stream.emit(Instruction::LoadInt32(1));
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(failed);
                self.stream.emit(Instruction::LoadInt32(0));
                self.stream.mark(end);
            }
            BoundExpressionKind::TypeTest { operand, target } => {
                // A value that is never null is of its own type, and a `ref
                // struct`, which does not box, is of no other: both answers
                // are known without a test (Roslyn's constant results).
                let symbols = self.emitter.compilation.symbols();
                let never_null = match &operand.ty {
                    Type::TypeParameter(parameter) => symbols
                        .get(*parameter)
                        .as_type_parameter()
                        .is_some_and(|detail| detail.value_type),
                    ty => {
                        self.emitter.is_value_type(ty)
                            && self.emitter.nullable_underlying(ty).is_none()
                    }
                };
                let ref_like = operand.ty.symbol().is_some_and(|symbol| {
                    symbols
                        .get(symbol)
                        .as_named_type()
                        .is_some_and(|detail| detail.ref_like)
                });
                if (never_null && operand.ty == *target) || ref_like {
                    self.emit_expression(operand, false)?;
                    self.stream
                        .emit(Instruction::LoadInt32(i32::from(operand.ty == *target)));
                    return Ok(true);
                }
                let token = self.emitter.type_token(target)?;
                self.emit_expression(operand, true)?;
                // `isinst` asks about a reference, so a value is boxed first:
                // `square is IShape` and `t is IShape` for an unconstrained
                // `T` are both that.
                self.box_if_a_value(&operand.ty)?;
                self.stream.emit(Instruction::IsInstance(token));
                // A `T` that allows a `ref struct` may be boxed only where a
                // branch reads the test at once, which the runtime accepts
                // for a type argument that does not box.
                if matches!(operand.ty, Type::TypeParameter(_)) {
                    let (yes, end) = (self.stream.label(), self.stream.label());
                    self.stream.emit(Instruction::BranchIfTrue(yes));
                    self.stream.emit(Instruction::LoadInt32(0));
                    self.stream.emit(Instruction::Branch(end));
                    self.stream.mark(yes);
                    self.stream.emit(Instruction::LoadInt32(1));
                    self.stream.mark(end);
                } else {
                    self.stream.emit(Instruction::LoadNull);
                    self.stream.emit(Instruction::CompareGreaterUnsigned);
                }
            }
            BoundExpressionKind::TryCast { operand, target } => {
                let token = self.emitter.type_token(target)?;
                self.emit_expression(operand, true)?;
                self.box_if_a_value(&operand.ty)?;
                self.stream.emit(Instruction::IsInstance(token));
                // `x as T` gives a `T`, and `isinst` gives the boxed form of
                // one: unboxing takes it back, which is nothing at run time
                // for the reference type `T` has to be. `x as S?` is the
                // same: `isinst` leaves a boxed `S` or null, and `unbox.any
                // S?` makes the `S?` either way.
                if matches!(target, Type::TypeParameter(_))
                    || self.emitter.nullable_underlying(target).is_some()
                {
                    self.stream.emit(Instruction::UnboxAny(token));
                }
            }
            BoundExpressionKind::TypeOf(target) => {
                // `typeof(List<>)` names the definition itself, with no
                // arguments at all: its own row, not a construction.
                // Only a type with parameters of its own can be unbound: one
                // nested in a generic type and named without arguments is the
                // construction the code it is in sees.
                let token = match target {
                    Type::Named {
                        symbol,
                        type_arguments,
                    } if type_arguments.is_empty() && self.declares_own_parameters(*symbol) => {
                        self.emitter.definition_token(*symbol)
                    }
                    // `typeof(C<>.E)` is the nested type of the unbound
                    // `C<>`: it carries `C`'s parameter and was given no
                    // argument for it, and it is the definition too.
                    Type::Named {
                        symbol,
                        type_arguments,
                    } if type_arguments.iter().all(Type::is_error)
                        && self
                            .emitter
                            .compilation
                            .symbols()
                            .get(*symbol)
                            .as_named_type()
                            .is_some_and(|detail| !detail.type_parameters.is_empty()) =>
                    {
                        self.emitter.definition_token(*symbol)
                    }
                    _ => self.emitter.type_token(target)?,
                };
                self.stream.emit(Instruction::LoadToken(token));
                self.emit_type_from_handle();
            }
            // `__makeref(x)` is `x`'s address with its type.
            BoundExpressionKind::MakeRef(operand) => {
                self.emit_reference(operand)?;
                let token = self.emitter.type_token(&operand.ty)?;
                self.stream.emit(Instruction::MakeRefAny(token));
            }
            // `__refvalue(r, T)` read as a value: the address `r` holds, if
            // it holds a `T`, and what is there.
            BoundExpressionKind::RefValue(operand) => {
                self.emit_expression(operand, true)?;
                let token = self.emitter.type_token(&expression.ty)?;
                self.stream.emit(Instruction::RefAnyValue(token));
                let kind = self.indirect_kind(&expression.ty)?;
                self.stream.emit(Instruction::LoadIndirect(kind));
            }
            BoundExpressionKind::RefType(operand) => {
                self.emit_expression(operand, true)?;
                self.stream.emit(Instruction::RefAnyType);
                self.emit_type_from_handle();
            }
            BoundExpressionKind::Default(ty) => self.emit_default(ty)?,
            BoundExpressionKind::Dynamic(dynamic) => {
                return self.emit_dynamic(dynamic, &expression.ty, true);
            }
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => {
                let getter = self.emitter.read_accessor(*indexer, Some(&receiver.ty))?;
                // A struct's indexer takes the address of its receiver and is
                // called directly: `callvirt` on a value is not IL at all.
                // A variable of a `T` that may be a class is kept as it was
                // before the arguments ran, as a call's receiver is.
                let kept = if self.generic_variable(receiver)
                    && !arguments.iter().all(safe_after_receiver)
                    && !self.emitter.is_extension_property(*indexer)
                {
                    match self.property_receiver(receiver)? {
                        Receiver::At(Address::HeldLocal(slot)) => {
                            self.push_address(Address::HeldLocal(slot));
                            Some(slot)
                        }
                        other => {
                            self.push_property_receiver(Some(&other), Some(&receiver.ty));
                            None
                        }
                    }
                } else {
                    self.emit_member_receiver(receiver, *indexer)?;
                    None
                };
                let outer = self.counted.take();
                self.counted = kept.map(|slot| (receiver.kind.clone(), slot));
                for argument in arguments {
                    self.emit_expression(argument, true)?;
                }
                self.counted = outer;
                let instruction = self.receiver_call(receiver, *indexer, getter)?;
                self.stream.call_effect(instruction, 1 + arguments.len(), 1);
                self.read_through_reference(*indexer, &expression.ty)?;
            }
            BoundExpressionKind::With {
                receiver,
                initializers,
            } => self.emit_with(receiver, initializers, &expression.ty)?,
            BoundExpressionKind::TypeExpression(symbol)
            | BoundExpressionKind::NamespaceExpression(symbol) => {
                return Err(EmitError::new(format!(
                    "a type or namespace name was used as a value: `{}`{}",
                    self.emitter.compilation.symbols().qualified_name(*symbol),
                    self.at(expression.span),
                )));
            }
            BoundExpressionKind::Error => {
                return Err(EmitError::new(format!(
                    "the body has an expression that did not bind{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::Unsupported(kind) => {
                // The type is worth saying: a collection expression that could
                // not be built is a different gap for every collection, and a
                // sweep that lumps them together cannot say which to write.
                let ty = expression.ty.display(self.emitter.compilation.symbols());
                return Err(EmitError::new(format!(
                    "cannot emit `{kind:?}` as `{ty}` yet{}",
                    self.at(expression.span)
                )));
            }
            BoundExpressionKind::Assignment { .. }
            | BoundExpressionKind::EventAssignment { .. }
            | BoundExpressionKind::CompoundAssignment { .. }
            | BoundExpressionKind::Increment { .. } => {
                unreachable!("handled before the value path")
            }
        }
        Ok(true)
    }

    fn emit_constant(&mut self, value: &ConstantValue, ty: &Type) -> Result<(), EmitError> {
        // `const long Mask = 0x1F` holds the literal as written, which is an
        // `int`; what is loaded is a value of the constant's type, or an
        // `and` on it has one side of each width.
        let integer = match value {
            ConstantValue::Int32(value) => Some(i64::from(*value)),
            ConstantValue::UInt32(value) => Some(i64::from(*value)),
            ConstantValue::Int64(value) => Some(*value),
            ConstantValue::UInt64(value) => Some(*value as i64),
            ConstantValue::Char(value) => Some(i64::from(*value as u32)),
            _ => None,
        };
        let special = self.emitter.special_type_of(ty).or_else(|| {
            ty.symbol()
                .filter(|symbol| {
                    self.emitter.compilation.symbols().get(*symbol).type_kind()
                        == Some(rustlyn_semantics::TypeKind::Enum)
                })
                .and_then(|symbol| {
                    self.emitter
                        .special_type_of(&self.emitter.enum_underlying(symbol))
                })
        });
        // A `decimal` that an integer constant stands for (`const decimal c =
        // 'b'`) is loaded as the integer it holds, as its own type, and
        // converted: nothing else puts a `decimal` on the stack.
        if special == Some(SpecialType::Decimal) {
            let element = match value {
                ConstantValue::Int32(_) => Some(ElementType::I4),
                ConstantValue::UInt32(_) => Some(ElementType::U4),
                ConstantValue::Int64(_) => Some(ElementType::I8),
                ConstantValue::UInt64(_) => Some(ElementType::U8),
                ConstantValue::Char(_) => Some(ElementType::Char),
                _ => None,
            };
            if let Some(element) = element {
                match value {
                    ConstantValue::Int32(value) => self.stream.emit(Instruction::LoadInt32(*value)),
                    ConstantValue::UInt32(value) => {
                        self.stream.emit(Instruction::LoadInt32(*value as i32));
                    }
                    ConstantValue::Char(value) => {
                        self.stream.emit(Instruction::LoadInt32(*value as i32));
                    }
                    _ => self
                        .stream
                        .emit(Instruction::LoadInt64(integer.unwrap_or_default())),
                }
                let decimal = self.decimal_sig();
                let token = self.emitter.framework_member(
                    "System.Decimal",
                    "op_Implicit",
                    false,
                    &decimal,
                    &[SigType::Primitive(element)],
                );
                self.stream.call_effect(Instruction::Call(token), 1, 1);
                return Ok(());
            }
        }
        // A native integer is loaded as the narrowest constant that holds
        // it and widened the way its signedness says: `uint.MaxValue` as an
        // `nuint` is zero-extended, not the `-1` an `i4` would sign-extend to.
        if let Some(integer) = integer
            && let Some(native) = ty
                .symbol()
                .and_then(|symbol| self.emitter.primitive_of(symbol))
                .filter(|element| matches!(element, ElementType::I | ElementType::U))
        {
            let unsigned = native == ElementType::U;
            let narrow = if unsigned {
                u32::try_from(integer).ok().map(|value| value as i32)
            } else {
                i32::try_from(integer).ok()
            };
            match narrow {
                Some(value) => self.stream.emit(Instruction::LoadInt32(value)),
                None => self.stream.emit(Instruction::LoadInt64(integer)),
            }
            self.stream.emit(if unsigned {
                Instruction::ConvertU
            } else {
                Instruction::ConvertI
            });
            return Ok(());
        }
        if let Some(integer) = integer {
            match special {
                Some(SpecialType::Int64 | SpecialType::UInt64) => {
                    self.stream.emit(Instruction::LoadInt64(integer));
                    return Ok(());
                }
                Some(SpecialType::Single) => {
                    self.stream.emit(Instruction::LoadFloat32(integer as f32));
                    return Ok(());
                }
                Some(SpecialType::Double) => {
                    self.stream.emit(Instruction::LoadFloat64(integer as f64));
                    return Ok(());
                }
                _ => {}
            }
        }
        match value {
            ConstantValue::Null => self.stream.emit(Instruction::LoadNull),
            ConstantValue::Boolean(value) => {
                self.stream.emit(Instruction::LoadInt32(i32::from(*value)));
            }
            ConstantValue::Char(value) => {
                self.stream.emit(Instruction::LoadInt32(*value as i32));
            }
            ConstantValue::Int32(value) => self.stream.emit(Instruction::LoadInt32(*value)),
            ConstantValue::UInt32(value) => {
                self.stream.emit(Instruction::LoadInt32(*value as i32));
            }
            ConstantValue::Int64(value) => self.stream.emit(Instruction::LoadInt64(*value)),
            ConstantValue::UInt64(value) => {
                self.stream.emit(Instruction::LoadInt64(*value as i64));
            }
            ConstantValue::Single(value) => self.stream.emit(Instruction::LoadFloat32(*value)),
            ConstantValue::Double(value) => self.stream.emit(Instruction::LoadFloat64(*value)),
            ConstantValue::String(text) => {
                let token = self.emitter.metadata.user_string(text);
                self.stream.emit(Instruction::LoadString(token));
            }
        }
        let _ = ty;
        Ok(())
    }

    /// Whether a type parameter was written `where T : struct`.
    fn is_a_struct_parameter(&self, parameter: SymbolId) -> bool {
        self.emitter
            .compilation
            .symbols()
            .get(parameter)
            .as_type_parameter()
            .is_some_and(|detail| detail.value_type)
    }

    fn emit_default(&mut self, ty: &Type) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        if ty.is_reference_type(symbols) || matches!(ty, Type::Array { .. } | Type::Null) {
            self.stream.emit(Instruction::LoadNull);
            return Ok(());
        }
        match self.emitter.special_type_of(ty) {
            Some(SpecialType::Int64 | SpecialType::UInt64) => {
                self.stream.emit(Instruction::LoadInt64(0));
            }
            Some(SpecialType::Single) => self.stream.emit(Instruction::LoadFloat32(0.0)),
            Some(SpecialType::Double) => self.stream.emit(Instruction::LoadFloat64(0.0)),
            Some(
                SpecialType::Boolean
                | SpecialType::Char
                | SpecialType::SByte
                | SpecialType::Byte
                | SpecialType::Int16
                | SpecialType::UInt16
                | SpecialType::Int32
                | SpecialType::UInt32,
            ) => self.stream.emit(Instruction::LoadInt32(0)),
            _ => {
                // A struct with no literal form — `decimal` among them: zero
                // a slot and read it back.
                let slot = self.temporary(ty)?;
                let token = self.emitter.type_token(ty)?;
                self.stream.emit(Instruction::LoadLocalAddress(slot));
                self.stream.emit(Instruction::InitObject(token));
                self.stream.emit(Instruction::LoadLocal(slot));
            }
        }
        Ok(())
    }

    fn emit_array_creation(
        &mut self,
        element: &Type,
        lengths: &[BoundExpression],
        elements: &[BoundExpression],
    ) -> Result<(), EmitError> {
        let token = self.emitter.type_token(element)?;
        match lengths.len() {
            0 => self
                .stream
                .emit(Instruction::LoadInt32(elements.len() as i32)),
            1 => {
                self.emit_expression(&lengths[0], true)?;
                self.narrow_index(&lengths[0].ty);
            }
            rank => {
                // `new int[2, 3]` is a `newobj` on a constructor the runtime
                // supplies, not a `newarr`: the shape is part of the type.
                let array = Type::Array {
                    element: Box::new(element.clone()),
                    rank,
                };
                let constructor =
                    self.emitter
                        .array_member(&array, ArrayMember::Constructor, rank, element)?;
                for length in lengths {
                    self.emit_expression(length, true)?;
                }
                self.stream
                    .call_effect(Instruction::NewObject(constructor), rank, 1);
                if elements.is_empty() {
                    return Ok(());
                }
                // `{ { 1, 2 }, { 3, 4 } }` was flattened across the rows, so
                // each value's indices are its position taken apart by the
                // sizes the nesting gave.
                let sizes: Option<Vec<usize>> = lengths.iter().map(Self::constant_length).collect();
                let Some(sizes) = sizes else {
                    return Err(EmitError::new(
                        "an array of more than one dimension filled in by an                          initializer whose sizes are not constants",
                    ));
                };
                let set = self
                    .emitter
                    .array_member(&array, ArrayMember::Set, rank, element)?;
                for (at, value) in elements.iter().enumerate() {
                    self.stream.emit(Instruction::Dup);
                    let mut rest = at;
                    let mut indices = vec![0usize; rank];
                    for (index, size) in indices.iter_mut().zip(&sizes).rev() {
                        let size = (*size).max(1);
                        *index = rest % size;
                        rest /= size;
                    }
                    for index in indices {
                        self.stream.emit(Instruction::LoadInt32(index as i32));
                    }
                    self.emit_expression(value, true)?;
                    self.stream.call_effect(Instruction::Call(set), rank + 2, 0);
                }
                return Ok(());
            }
        }
        self.stream.emit(Instruction::NewArray(token));
        // All of it constants: copied in at once out of the bytes the image
        // holds for it (`RuntimeHelpers.InitializeArray`), rather than an
        // instruction per element — four million of them made a method of
        // thirty-six megabytes for the JIT to read.
        if let Some(field) = self.emitter.array_block_field(element, lengths, elements) {
            let initialize = self.emitter.initialize_array();
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadToken(field));
            self.stream.call_effect(Instruction::Call(initialize), 2, 0);
            return Ok(());
        }
        for (index, value) in elements.iter().enumerate() {
            // A new array is all zeros already, as Roslyn leaves it.
            if self.is_zero_element(element, value) {
                continue;
            }
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(index as i32));
            self.emit_expression(value, true)?;
            self.store_element(element, token);
        }
        Ok(())
    }

    /// Whether an element of an array initializer is a constant the array
    /// already holds when made: zero of a number, `false`, `'\0'`, or `null`
    /// of a reference.
    fn is_zero_element(&self, element: &Type, value: &BoundExpression) -> bool {
        use rustlyn_semantics::SpecialType as S;
        let Some(constant) = self.emitter.binder.folded(value) else {
            return false;
        };
        let symbols = self.emitter.compilation.symbols();
        match constant {
            ConstantValue::Null => element.is_reference_type(symbols),
            ConstantValue::Boolean(value) => {
                !value && self.emitter.special_type_of(element) == Some(S::Boolean)
            }
            ConstantValue::Char(value) => {
                value == '\0' && self.emitter.special_type_of(element) == Some(S::Char)
            }
            ConstantValue::Int32(0)
            | ConstantValue::UInt32(0)
            | ConstantValue::Int64(0)
            | ConstantValue::UInt64(0) => matches!(
                self.emitter.special_type_of(element),
                Some(
                    S::SByte
                        | S::Byte
                        | S::Int16
                        | S::UInt16
                        | S::Char
                        | S::Int32
                        | S::UInt32
                        | S::Int64
                        | S::UInt64
                )
            ),
            ConstantValue::Single(value) => {
                value.to_bits() == 0 && self.emitter.special_type_of(element) == Some(S::Single)
            }
            ConstantValue::Double(value) => {
                value.to_bits() == 0 && self.emitter.special_type_of(element) == Some(S::Double)
            }
            _ => false,
        }
    }

    /// `Get`, `Set` or `Address` of the array an expression has the type of.
    fn array_member(
        &mut self,
        array: &BoundExpression,
        which: ArrayMember,
        element: &Type,
    ) -> Result<Token, EmitError> {
        let ty = self.emitter.completed(&array.ty);
        let Type::Array { rank, .. } = &ty else {
            return Err(EmitError::new(
                "an access with several indices on something that is not an array",
            ));
        };
        let rank = *rank;
        self.emitter.array_member(&ty, which, rank, element)
    }

    /// The element types of a tuple type, written or read out of metadata.
    fn tuple_element_types(&self, ty: &Type) -> Option<Vec<Type>> {
        match ty {
            Type::Tuple(elements) => {
                Some(elements.iter().map(|element| element.ty.clone()).collect())
            }
            Type::Named {
                symbol,
                type_arguments,
            } if !type_arguments.is_empty() => {
                let symbols = self.emitter.compilation.symbols();
                if symbols.get(*symbol).name != "ValueTuple" {
                    return None;
                }
                // Past seven the rest nest, and a `ValueTuple<…, ValueTuple<…>>`
                // has the elements of both.
                let mut elements = type_arguments.clone();
                if elements.len() == 8
                    && let Some(more) = self.tuple_element_types(&elements[7])
                {
                    elements.pop();
                    elements.extend(more);
                }
                Some(elements)
            }
            _ => None,
        }
    }

    /// The tuple nested as the rest of a long one: its elements past the
    /// seventh.
    fn tuple_rest(ty: &Type) -> Option<Type> {
        match ty {
            Type::Tuple(elements) if elements.len() > 7 => {
                Some(Type::Tuple(elements[7..].to_vec()))
            }
            Type::Named { type_arguments, .. } if type_arguments.len() == 8 => {
                Some(type_arguments[7].clone())
            }
            _ => None,
        }
    }

    /// Makes a tuple of `count` elements that are on the stack in order: the
    /// innermost rest first, from the last of them, and then each tuple
    /// around it from its seven and the one it holds.
    fn emit_tuple_constructors(&mut self, ty: &Type, count: usize) -> Result<(), EmitError> {
        let mut nested = vec![ty.clone()];
        let mut remaining = count;
        while remaining > 7 {
            let Some(rest) = nested.last().and_then(Self::tuple_rest) else {
                return Err(EmitError::new("a long tuple whose type is not a tuple"));
            };
            nested.push(rest);
            remaining -= 7;
        }
        let mut width = remaining;
        for current in nested.iter().rev() {
            let token = self.emitter.tuple_constructor(current)?;
            self.stream
                .call_effect(Instruction::NewObject(token), width, 1);
            width = 8;
        }
        Ok(())
    }

    /// Converts the value on the stack from one type to another by the
    /// language's own conversions: a box, an unbox, a cast, or a numeric
    /// widening or narrowing.
    fn emit_value_conversion(&mut self, from: &Type, to: &Type) -> Result<(), EmitError> {
        // `x ?? throw ...`: a `throw` has no type, and leaves nothing to
        // convert.
        if from == to || to.is_error() || from.is_error() || matches!(from, Type::Null) {
            return Ok(());
        }
        let symbols = self.emitter.compilation.symbols();
        // A type parameter goes through a box either way: boxing is nothing
        // where it is a reference type, and `unbox.any` gives it back.
        if matches!(to, Type::TypeParameter(_)) {
            self.box_if_needed(from)?;
            let token = self.emitter.type_token(to)?;
            self.stream.emit(Instruction::UnboxAny(token));
            return Ok(());
        }
        let from_value = !from.is_reference_type(symbols) || matches!(from, Type::TypeParameter(_));
        let to_value = !to.is_reference_type(symbols);
        match (from_value, to_value) {
            (true, false) => self.box_if_needed(from)?,
            (false, true) => {
                let token = self.emitter.type_token(to)?;
                self.stream.emit(Instruction::UnboxAny(token));
            }
            (true, true) => {
                if self.emitter.nullable_underlying(to).is_some()
                    && self.emitter.nullable_underlying(from).is_none()
                {
                    let constructor = self.emitter.nullable_constructor(to)?;
                    self.stream
                        .call_effect(Instruction::NewObject(constructor), 1, 1);
                } else if matches!(from, Type::TypeParameter(_)) {
                    self.box_if_needed(from)?;
                    let token = self.emitter.type_token(to)?;
                    self.stream.emit(Instruction::UnboxAny(token));
                } else {
                    self.convert_number_from(from, to)?;
                }
            }
            (false, false) => {
                if !self.emitter.binder.converts_implicitly(from, to) {
                    let token = self.emitter.type_token(to)?;
                    self.stream.emit(Instruction::CastClass(token));
                }
            }
        }
        Ok(())
    }

    /// `ldelem` in the form the element asks for, as [`Self::store_element`]
    /// does for `stelem`: `ldelem.u2` for a `char`, and the token form for
    /// anything the verifier does not hold to a primitive's own.
    fn load_element(&mut self, element: &Type, token: Token) {
        use rustlyn_semantics::SpecialType as S;
        let symbols = self.emitter.compilation.symbols();
        let instruction = match self.emitter.special_type_of(element) {
            Some(S::Boolean | S::Byte) => Instruction::LoadElementU1,
            Some(S::SByte) => Instruction::LoadElementI1,
            Some(S::Int16) => Instruction::LoadElementI2,
            Some(S::UInt16 | S::Char) => Instruction::LoadElementU2,
            Some(S::Int32) => Instruction::LoadElementI4,
            Some(S::UInt32) => Instruction::LoadElementU4,
            Some(S::Int64 | S::UInt64) => Instruction::LoadElementI8,
            Some(S::Single) => Instruction::LoadElementR4,
            Some(S::Double) => Instruction::LoadElementR8,
            Some(S::String | S::Object) => Instruction::LoadElementRef,
            _ if !matches!(element, Type::TypeParameter(_))
                && element.is_reference_type(symbols) =>
            {
                Instruction::LoadElementRef
            }
            _ => Instruction::LoadElement(token),
        };
        self.stream.emit(instruction);
    }

    /// `stelem` in the form the element asks for: a primitive has its own
    /// — `stelem.i2` for a `char` — and the verifier holds an array of
    /// them to it; anything else goes by its token.
    fn store_element(&mut self, element: &Type, token: Token) {
        use rustlyn_semantics::SpecialType as S;
        let instruction = match self.emitter.special_type_of(element) {
            Some(S::Boolean | S::SByte | S::Byte) => Instruction::StoreElementI1,
            Some(S::Int16 | S::UInt16 | S::Char) => Instruction::StoreElementI2,
            Some(S::Int32 | S::UInt32) => Instruction::StoreElementI4,
            Some(S::Int64 | S::UInt64) => Instruction::StoreElementI8,
            Some(S::Single) => Instruction::StoreElementR4,
            Some(S::Double) => Instruction::StoreElementR8,
            _ => Instruction::StoreElement(token),
        };
        self.stream.emit(instruction);
    }

    fn emit_single_index(&mut self, indices: &[BoundExpression]) -> Result<(), EmitError> {
        match indices {
            [index] => {
                self.emit_expression(index, true)?;
                self.narrow_index(&index.ty);
                Ok(())
            }
            _ => Err(EmitError::new(
                "cannot emit an array access with more than one index yet",
            )),
        }
    }

    /// An array is indexed and sized by an `int` or a native `int`: a `long`
    /// or `ulong` written there — `labels[i]` for a `ulong i` — becomes a
    /// native one first, which is what the language's conversion does.
    fn narrow_index(&mut self, ty: &Type) {
        if matches!(
            self.emitter.special_type_of(ty),
            Some(SpecialType::Int64 | SpecialType::UInt64)
        ) {
            self.stream.emit(Instruction::ConvertI);
        }
    }

    /// A bound expression named by its shape, for a message about one met
    /// somewhere a backend did not expect it.
    fn describe_kind(kind: &BoundExpressionKind) -> String {
        match kind {
            BoundExpressionKind::Unsupported(written) => format!("`{written:?}`"),
            other => {
                let text = format!("{other:?}");
                let end = text.find(['(', ' ', '{']).unwrap_or(text.len());
                format!("`{}`", &text[..end])
            }
        }
    }

    /// The length a dimension was given, where it was given a constant one.
    fn constant_length(length: &BoundExpression) -> Option<usize> {
        match &length.kind {
            BoundExpressionKind::Literal(ConstantValue::Int32(value)) => {
                usize::try_from(*value).ok()
            }
            _ => None,
        }
    }

    /// How a call on a receiver is made.
    ///
    /// A struct's methods cannot be overridden, and what a call on one takes
    /// is an address rather than an object: `callvirt` on that is not valid
    /// IL. A type parameter is the exception, and the whole point of
    /// `constrained.` — there only the runtime knows, from the type argument
    /// the call was instantiated with, whether the address holds an object to
    /// dereference or a value to box.
    fn receiver_call(
        &mut self,
        receiver: &BoundExpression,
        method: SymbolId,
        token: Token,
    ) -> Result<Instruction, EmitError> {
        // `base.MetadataName` names the base's accessor and means that one:
        // dispatching it would land back on the override that asked. An
        // extension block's property is a static method taking the receiver.
        if matches!(receiver.kind, BoundExpressionKind::Base)
            || self.emitter.is_extension_property(method)
            || self.is_base_of(receiver)
        {
            return Ok(Instruction::Call(token));
        }
        if !matches!(receiver.ty, Type::TypeParameter(_))
            && !self.emitter.is_value_type(&receiver.ty)
        {
            return Ok(Instruction::CallVirtual(token));
        }
        // A struct's own methods cannot be overridden, so a call to one is
        // direct and takes the address the receiver was given. Reaching a
        // method the struct did *not* declare — `object.ToString()` — is the
        // same question a type parameter asks, and has the same answer.
        // A local function or a lambda of the struct is the struct's own
        // method too, although its container is the method it was written
        // in.
        let declared_here = !matches!(receiver.ty, Type::TypeParameter(_))
            && self.emitter.enclosing_type(method) == receiver.ty.symbol();
        if declared_here {
            return Ok(Instruction::Call(token));
        }
        let constraint = self.emitter.type_token(&receiver.ty)?;
        self.stream.emit(Instruction::Constrained(constraint));
        Ok(Instruction::CallVirtual(token))
    }

    /// Whether the receiver is `PilotRuntime.Base.Of<T>(instance)`: what a hot
    /// patch writes for `base`, from outside the class that said it. The
    /// patch is a static method of a class of its own, where C# has no way
    /// to call the base's implementation of a virtual member; the call on
    /// this receiver is made as `base` would make it, directly.
    fn is_base_of(&self, receiver: &BoundExpression) -> bool {
        let BoundExpressionKind::Call { method, .. } = &receiver.kind else {
            return false;
        };
        let symbols = self.emitter.compilation.symbols();
        let symbol = symbols.get(*method);
        symbol.name == "Of"
            && symbol
                .container
                .is_some_and(|holder| symbols.qualified_name(holder) == "PilotRuntime.Base")
    }

    /// With the address of a receiver of a type parameter on the stack:
    /// where the type turns out to be a class, swaps it for the address of
    /// a copy, so that what the arguments write to the variable does not
    /// change which instance is called. The test is on `default(T)`, which
    /// is null only for a class, and which the JIT folds.
    fn clone_if_reference_type(&mut self, ty: &Type) -> Result<(), EmitError> {
        let token = self.emitter.type_token(ty)?;
        let done = self.stream.label();
        let default = self.temporary(ty)?;
        self.stream.emit(Instruction::LoadLocalAddress(default));
        self.stream.emit(Instruction::InitObject(token));
        self.stream.emit(Instruction::LoadLocal(default));
        self.stream.emit(Instruction::Box(token));
        self.stream.emit(Instruction::BranchIfTrue(done));
        let copy = self.temporary(ty)?;
        self.stream
            .emit(Instruction::LoadIndirect(IndirectKind::Object(token)));
        self.stream.emit(Instruction::StoreLocal(copy));
        self.stream.emit(Instruction::LoadLocalAddress(copy));
        self.stream.mark(done);
        Ok(())
    }

    /// `Type.GetTypeFromHandle` on the handle on the stack.
    fn emit_type_from_handle(&mut self) {
        let handle = SigType::Named {
            value_type: true,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeTypeHandle"),
        };
        let ty = SigType::Named {
            value_type: false,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.Type"),
        };
        let member = self.emitter.framework_member(
            "System.Type",
            "GetTypeFromHandle",
            false,
            &ty,
            &[handle],
        );
        self.stream.call_effect(Instruction::Call(member), 1, 1);
    }

    /// `f(a, b)` through a function pointer: the arguments, then the pointer,
    /// then `calli` with the pointer's own signature (§III.3.20). The pointer
    /// is evaluated first, as C# says, so where reading it again could see
    /// something else it waits in a temporary.
    fn emit_function_pointer_call(
        &mut self,
        pointer: &BoundExpression,
        arguments: &[BoundExpression],
        result: &Type,
        read: bool,
    ) -> Result<bool, EmitError> {
        let Type::FunctionPointer(signature) = pointer.ty.value() else {
            return Err(EmitError::new(
                "a call through something that is no function pointer",
            ));
        };
        let signature = signature.clone();
        let stable = matches!(
            pointer.kind,
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
        ) && arguments.is_empty();
        let saved = if stable {
            None
        } else {
            self.emit_expression(pointer, true)?;
            let slot = self.temporary(&pointer.ty)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            Some(slot)
        };
        for argument in arguments {
            self.emit_expression(argument, true)?;
        }
        match saved {
            Some(slot) => self.stream.emit(Instruction::LoadLocal(slot)),
            None => self.emit_expression(pointer, true)?,
        }
        let (returns, parameters) = self.emitter.function_pointer_parts(&signature)?;
        let blob = standalone_method_signature(signature.convention, &returns, &parameters);
        let token = self.emitter.metadata.add_stand_alone_sig(&blob);
        let returns_void =
            matches!(signature.returns, Type::Void) && signature.returns_ref == RefKind::None;
        self.stream.call_effect(
            Instruction::CallIndirect(token),
            arguments.len() + 1,
            usize::from(!returns_void),
        );
        if read && signature.returns_ref != RefKind::None {
            let kind = self.indirect_kind(result)?;
            self.stream.emit(Instruction::LoadIndirect(kind));
        }
        Ok(!returns_void)
    }

    fn emit_call(&mut self, call: &CallSite<'_>) -> Result<bool, EmitError> {
        let &CallSite {
            receiver,
            method,
            type_arguments,
            arguments,
            virtual_call,
            result,
            read,
        } = call;
        // `Holder<int>.Echo(7)` has a receiver that is a type rather than a
        // value: it is there to say which construction the member belongs to —
        // which the token below needs — and nothing is pushed for it.
        // A local function that lives in the display class is an instance
        // method of it, and whatever the call site named as a receiver is not
        // what it is called on: the class is where what it reads lives.
        let display_receiver = self.in_display(method);
        let value_receiver = receiver
            .filter(|receiver| !is_type_name(receiver))
            .filter(|_| display_receiver.is_none());
        // A receiver of a type parameter is reached through its address, and
        // an argument may write the variable before the call: `item.M(F(ref
        // item))` calls `M` on the instance `item` held when the call began.
        // A `T : class` is called on its value, boxed; any other `T` on a copy
        // where it turns out to be a class (Roslyn's
        // `emitGenericReceiverCloneIfNecessary`).
        let mut boxed_reference = false;
        if let Some(receiver) = value_receiver {
            let generic = matches!(receiver.ty, Type::TypeParameter(parameter)
                    if !self
                        .emitter
                        .compilation
                        .symbols()
                        .get(parameter)
                        .as_type_parameter()
                        .is_some_and(|detail| detail.value_type))
                && !self.emitter.is_extension_property(method)
                && !arguments.iter().all(safe_after_receiver);
            if generic && self.emitter.binder.held_by_reference(&receiver.ty) {
                self.emit_expression(receiver, true)?;
                let token = self.emitter.type_token(&receiver.ty)?;
                self.stream.emit(Instruction::Box(token));
                boxed_reference = true;
            } else {
                self.emit_member_receiver(receiver, method)?;
                if generic {
                    self.clone_if_reference_type(&receiver.ty)?;
                }
            }
        }
        if let Some(holder) = display_receiver {
            self.push_holder(holder);
        }
        // What an `__arglist(...)` passes goes on the stack after the fixed
        // arguments, each as the type it has, and the call site's signature
        // says which types those are.
        let mut extra: Option<Vec<(Type, bool)>> = None;
        for argument in arguments {
            if let BoundExpressionKind::ArgList(values) = &argument.kind {
                let mut types = Vec::with_capacity(values.len());
                for value in values {
                    match &value.kind {
                        BoundExpressionKind::RefArgument { operand, .. } => {
                            self.emit_reference(operand)?;
                            types.push((value.ty.clone(), true));
                        }
                        _ => {
                            self.emit_expression(value, true)?;
                            types.push((value.ty.clone(), false));
                        }
                    }
                }
                extra = Some(types);
                continue;
            }
            self.emit_expression(argument, true)?;
        }
        // A static member of a generic type has no receiver to say which
        // construction it belongs to, so the call reads it off what goes in
        // and what comes out instead.
        let standing_in = if receiver.is_none() {
            self.static_container(method, arguments, result)
        } else {
            None
        };
        // `a + b` on a `T : IAdditionOperators<T, T, T>` calls the
        // interface's static abstract operator through the type parameter:
        // `constrained. !!T` and then the member of the constraint's
        // construction (§III.2.1), which is the only way to reach a static
        // virtual member.
        let constrained_static = if receiver.is_none_or(is_type_name) {
            self.static_abstract_constraint(method)
        } else {
            None
        };
        let through = receiver.map(|value| &value.ty).or(standing_in.as_ref());
        let token = if let Some((_, construction)) = &constrained_static {
            self.constraint_member(method, construction)?
        } else if display_receiver.is_some() {
            match self.display_function_token(method) {
                Some(token) => token,
                None => self.method_token(method)?,
            }
        } else {
            self.method_token_on(method, through)?
        };
        if let Some((parameter, _)) = &constrained_static {
            let constraint = self.emitter.type_token(&Type::TypeParameter(*parameter))?;
            self.stream.emit(Instruction::Constrained(constraint));
        }
        // A generic method is called through the instantiation the binder
        // inferred, never through the definition. A lambda or a local
        // function made for a generic method declares that method's
        // parameters too, and they come first.
        let token = match &extra {
            Some(types) => self.emitter.vararg_call_site(method, types)?,
            None => self.instantiated(token, type_arguments)?,
        };
        let returns_void = matches!(self.emitter.type_of(method), Type::Void);
        let pops = arguments.len() + extra.as_ref().map_or(0, Vec::len)
            - usize::from(extra.is_some())
            + usize::from(value_receiver.is_some())
            + usize::from(display_receiver.is_some());
        let pushes = usize::from(!returns_void);
        // A call on a value type that reaches a method the value type did not
        // declare — `marks.HasFlag(other)`, `point.ToString()` — is given an
        // address where the method wants an object, whether or not the method
        // is virtual. `constrained.` is what turns the one into the other.
        let by_address = value_receiver.filter(|receiver| {
            matches!(receiver.ty, Type::TypeParameter(_))
                || self.emitter.is_value_type(&receiver.ty)
        });
        let instruction = if boxed_reference {
            Instruction::CallVirtual(token)
        } else {
            match value_receiver.filter(|_| virtual_call).or(by_address) {
                Some(receiver) => self.receiver_call(receiver, method, token)?,
                None => Instruction::Call(token),
            }
        };
        self.stream.call_effect(instruction, pops, pushes);
        // A method that returns by reference hands back where the value is.
        // Reading the call as a value reads through that; `ref M()` wants the
        // reference as it stands, and asks for it with `read` false.
        if read && matches!(self.emitter.type_of(method), Type::ByRef(_)) {
            let kind = self.indirect_kind(result)?;
            self.stream.emit(Instruction::LoadIndirect(kind));
        }
        Ok(!returns_void)
    }

    /// A delegate: a target and the address of a method, handed to the
    /// constructor the runtime writes.
    ///
    /// A static method has no target, so `null` goes in its place. `ldvirtftn`
    /// rather than `ldftn` when the target is virtual, because the delegate
    /// has to remember the override the *receiver* provides, not the one its
    /// static type names — and that is why the receiver is duplicated: the
    /// constructor wants it too.
    fn emit_delegate_creation(
        &mut self,
        delegate_type: &Type,
        method: SymbolId,
        receiver: Option<&BoundExpression>,
        virtual_dispatch: bool,
        type_arguments: &[Type],
    ) -> Result<(), EmitError> {
        // A local function that lives in the display class is an instance
        // method of it, whatever the source wrote: a delegate to it closes
        // over the class, not over what the call site named — and never over
        // a null, which a `static` local function would otherwise get.
        if let Some(holder) = self.in_display(method) {
            let target = match self.display_function_token(method) {
                Some(token) => token,
                None => self.method_token(method)?,
            };
            let target = self.instantiated(target, type_arguments)?;
            let constructor = self.delegate_constructor(delegate_type)?;
            self.push_holder(holder);
            self.stream.emit(Instruction::LoadFunction(target));
            self.stream
                .call_effect(Instruction::NewObject(constructor), 2, 1);
            return Ok(());
        }
        let target = self.method_token_on(method, receiver.map(|value| &value.ty))?;
        let target = self.instantiated(target, type_arguments)?;
        let constructor = self.delegate_constructor(delegate_type)?;

        // A type where a receiver would be says which construction a static
        // method belongs to — the token above needed it — and is nothing to
        // push: the delegate's target is `null` like any static method's.
        match receiver.filter(|receiver| !is_type_name(receiver)) {
            Some(receiver) => {
                self.emit_expression(receiver, true)?;
                // A delegate's target is an object: a struct's method is
                // called on a boxed copy, as `new(this, ..., RegisterOutput)`
                // in a `readonly struct` does.
                self.box_if_a_value(&receiver.ty)?;
                // `base.F` names the base's method itself, never what an
                // override of it would dispatch to.
                let through_base = matches!(receiver.kind, BoundExpressionKind::Base);
                if virtual_dispatch && !through_base {
                    self.stream.emit(Instruction::Dup);
                    self.stream.emit(Instruction::LoadVirtualFunction(target));
                } else {
                    self.stream.emit(Instruction::LoadFunction(target));
                }
            }
            None => {
                self.stream.emit(Instruction::LoadNull);
                self.stream.emit(Instruction::LoadFunction(target));
            }
        }
        self.stream
            .call_effect(Instruction::NewObject(constructor), 2, 1);
        Ok(())
    }

    /// What a body does before its first statement: makes the display
    /// class the method owns, if any, and loads what the closures capture.
    /// The start of a loop body that has a class of its own: a fresh
    /// instance, linked to the member's class where there is one, and its
    /// fields in view for the body. `true` when there was such a class.
    fn enter_scope(&mut self, span: TextSpan) -> Result<bool, EmitError> {
        let Some(owner) = self.owner else {
            return Ok(false);
        };
        let Some(display) = self
            .emitter
            .nested_displays
            .get(&(owner, Closure::Scope(span)))
            .cloned()
        else {
            return Ok(false);
        };
        // In an `async` machine the class lives in a field of the machine,
        // since a local would not outlive an `await` in the loop; anywhere
        // else a local of the method is where it goes.
        let held = match self
            .async_run
            .as_ref()
            .and_then(|run| run.plan.scopes.get(&span).copied())
        {
            Some(field) => Holder::ThisField(field),
            None => Holder::Slot(match self.scope_slots.get(&span) {
                Some(slot) => *slot,
                None => {
                    let slot = self.locals.len() as u16;
                    self.locals.push(display.sig.clone());
                    self.local_types.push(Type::Error);
                    self.scope_slots.insert(span, slot);
                    slot
                }
            }),
        };
        if let Holder::ThisField(_) = held {
            self.stream.emit(Instruction::LoadArgument(0));
        }
        self.stream
            .call_effect(Instruction::NewObject(display.outside.constructor), 0, 1);
        match held {
            Holder::ThisField(field) => self.stream.emit(Instruction::StoreField(field)),
            Holder::Slot(slot) => self.stream.emit(Instruction::StoreLocal(slot)),
            Holder::Display => unreachable!("a loop body's class is never the body's own"),
        }
        if let Some(field) = display.outside.parent {
            self.push_holder(held);
            self.push_display();
            self.stream.emit(Instruction::StoreField(field));
        }
        if let Some(field) = display.outside.this {
            self.push_holder(held);
            self.push_this_value()?;
            self.stream.emit(Instruction::StoreField(field));
        }
        self.captures.push((display.outside.clone(), held));
        Ok(true)
    }

    fn leave_scope(&mut self, entered: bool) {
        if entered {
            self.captures.pop();
        }
    }

    fn emit_frame_setup(
        &mut self,
        owned: Option<&(crate::emitter::DisplayClass, u16)>,
    ) -> Result<(), EmitError> {
        self.emit_display_prologue()?;
        if let Some((display, slot)) = owned {
            let slot = *slot;
            self.stream
                .call_effect(Instruction::NewObject(display.outside.constructor), 0, 1);
            self.stream.emit(Instruction::StoreLocal(slot));
            if let Some(field) = display.outside.parent {
                self.stream.emit(Instruction::LoadLocal(slot));
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::StoreField(field));
            }
            if let Some(field) = display.outside.this
                && !self.defer_this
            {
                self.stream.emit(Instruction::LoadLocal(slot));
                self.push_this_value()?;
                self.stream.emit(Instruction::StoreField(field));
            }
            // A local function's parameters that its closures capture move
            // into the class the moment it starts, and the body reads them
            // there from then on.
            for (parameter, field) in by_declaration(&display.outside.parameters) {
                let Ok(index) = self.argument_index(parameter) else {
                    continue;
                };
                self.stream.emit(Instruction::LoadLocal(slot));
                self.stream.emit(Instruction::LoadArgument(index));
                self.stream.emit(Instruction::StoreField(field));
            }
        }
        self.emit_capture_loads();
        Ok(())
    }

    /// Makes the display class and fills in what it can at method entry.
    ///
    /// A captured parameter and `this` are known the moment the method starts,
    /// so they are copied in here; a captured local is assigned through the
    /// class from then on, so there is nothing to copy.
    fn emit_display_prologue(&mut self) -> Result<(), EmitError> {
        let Some((display, at)) = self.display.clone() else {
            return Ok(());
        };
        // A local function that became a method of the class is handed the
        // class itself, and its own parameters still have to go in: a lambda
        // written inside it reads them from there, as it reads everything.
        let DisplayAt::Local(slot) = at else {
            for (parameter, field) in by_declaration(&display.inside.parameters) {
                let Ok(index) = self.argument_index(parameter) else {
                    continue;
                };
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::LoadArgument(index));
                self.stream.emit(Instruction::StoreField(field));
            }
            return Ok(());
        };
        self.stream
            .call_effect(Instruction::NewObject(display.outside.constructor), 0, 1);
        self.stream.emit(Instruction::StoreLocal(slot));

        for (parameter, field) in by_declaration(&display.outside.parameters) {
            let Some(index) = self.argument_index(parameter).ok() else {
                continue;
            };
            self.stream.emit(Instruction::LoadLocal(slot));
            self.stream.emit(Instruction::LoadArgument(index));
            self.stream.emit(Instruction::StoreField(field));
        }
        if let Some(field) = display.outside.this
            && !self.defer_this
        {
            self.stream.emit(Instruction::LoadLocal(slot));
            self.push_this_value()?;
            self.stream.emit(Instruction::StoreField(field));
        }
        Ok(())
    }

    /// The members of the display class as the method being emitted reaches
    /// them: its own methods name definitions, and the method that made it
    /// names them under the construction it wrote.
    fn display_view(&self) -> Option<&crate::emitter::DisplayView> {
        match self.display.as_ref()? {
            (display, DisplayAt::This) => Some(&display.inside),
            (display, DisplayAt::Local(_)) => Some(&display.outside),
        }
    }

    /// Pushes the display class instance.
    fn push_display(&mut self) {
        match self.display {
            Some((_, DisplayAt::Local(slot))) => {
                self.stream.emit(Instruction::LoadLocal(slot));
            }
            Some((_, DisplayAt::This)) => self.stream.emit(Instruction::LoadArgument(0)),
            None => {}
        }
    }

    /// The holder and field of a captured local, for an expression tree to
    /// read it through.
    pub(crate) fn captured_local_public(&self, local: LocalId) -> Option<(Holder, Token)> {
        self.captured_local(local)
            .map(|capture| (capture.holder, capture.token))
    }

    /// The same for a captured parameter.
    pub(crate) fn captured_parameter_public(&self, parameter: SymbolId) -> Option<(Holder, Token)> {
        self.captured_parameter(parameter)
            .map(|capture| (capture.holder, capture.token))
    }

    pub(crate) fn push_holder_public(&mut self, holder: Holder) {
        self.push_holder(holder);
    }

    /// Pushes whatever holds a captured variable's field.
    fn push_holder(&mut self, holder: Holder) {
        match holder {
            Holder::Display => self.push_display(),
            Holder::Slot(slot) => self.stream.emit(Instruction::LoadLocal(slot)),
            Holder::ThisField(field) => {
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::LoadField(field));
            }
        }
    }

    /// The capture `find` names, looked for where the innermost variable
    /// wins: the loop-body classes entered so far (innermost first), then
    /// the class the body has, then what was in view when the body started
    /// (the closest first).
    fn find_capture(&self, find: impl Fn(&DisplayView) -> Option<Token>) -> Option<Capture> {
        let (setup, entered) = self.captures.split_at(self.setup_captures);
        entered
            .iter()
            .rev()
            .find_map(|(view, holder)| {
                find(view).map(|token| Capture {
                    holder: *holder,
                    token,
                })
            })
            .or_else(|| {
                self.display_view().and_then(|view| {
                    find(view).map(|token| Capture {
                        holder: Holder::Display,
                        token,
                    })
                })
            })
            .or_else(|| {
                setup.iter().find_map(|(view, holder)| {
                    find(view).map(|token| Capture {
                        holder: *holder,
                        token,
                    })
                })
            })
    }

    /// `<>4__this`, when the method being emitted reaches `this` through the
    /// display class rather than as an argument. Only a lambda does: the
    /// method that made the display class still has its own `this`. A
    /// closure's machine reaches it through the member's display class.
    fn captured_this(&self) -> Option<Capture> {
        if let Some((display, DisplayAt::This)) = self.display.as_ref()
            && let Some(token) = display.inside.this
        {
            return Some(Capture {
                holder: Holder::Display,
                token,
            });
        }
        self.captures.iter().find_map(|(view, holder)| {
            view.this.map(|token| Capture {
                holder: *holder,
                token,
            })
        })
    }

    /// Fills the slots the captured classes are read from, in the order
    /// they were asked for: each is loaded from `this` or from a slot filled
    /// before it.
    fn emit_capture_loads(&mut self) {
        for (source, slot) in std::mem::take(&mut self.capture_loads) {
            match source {
                CaptureSource::ThisField(field) => {
                    self.stream.emit(Instruction::LoadArgument(0));
                    self.stream.emit(Instruction::LoadField(field));
                }
                CaptureSource::SlotField(from, field) => {
                    self.stream.emit(Instruction::LoadLocal(from));
                    self.stream.emit(Instruction::LoadField(field));
                }
            }
            self.stream.emit(Instruction::StoreLocal(slot));
        }
    }

    /// The field a captured local lives in, if it is captured at all: in the
    /// display class this body has, or in the member's that a closure's
    /// machine holds.
    fn captured_local(&self, local: LocalId) -> Option<Capture> {
        self.find_capture(|view| view.locals.get(&local).copied())
    }

    /// Whether a member is a local function that became a method of the
    /// display class this body already has, and what holds that class.
    /// The token a local function that lives in a display class is called
    /// by from here: from inside the class it is the member of `Display<!0>`,
    /// from the method that made the class the member of `Display<!!0>`, and
    /// from a closure holding the class in a slot whatever that view says.
    /// The two differ only for a generic method, and the wrong one names a
    /// method type variable where the caller declares none.
    fn display_function_token(&self, member: SymbolId) -> Option<Token> {
        if let Some((display, at)) = self.display.as_ref() {
            let view = match at {
                DisplayAt::This => &display.inside,
                DisplayAt::Local(_) => &display.outside,
            };
            if let Some(token) = view.local_functions.get(&member) {
                return Some(*token);
            }
        }
        self.captures
            .iter()
            .find_map(|(view, _)| view.local_functions.get(&member).copied())
    }

    fn in_display(&self, member: SymbolId) -> Option<Holder> {
        let here = self.display.as_ref().is_some_and(|(display, at)| match at {
            DisplayAt::This => display.inside.local_functions.contains_key(&member),
            DisplayAt::Local(_) => display.outside.local_functions.contains_key(&member),
        });
        if here {
            return Some(Holder::Display);
        }
        self.captures.iter().find_map(|(view, holder)| {
            view.local_functions
                .contains_key(&member)
                .then_some(*holder)
        })
    }

    /// The same for a captured parameter.
    fn captured_parameter(&self, parameter: SymbolId) -> Option<Capture> {
        self.find_capture(|view| view.parameters.get(&parameter).copied())
    }

    /// The address of a variable, for passing it by reference.
    ///
    /// C# only lets a variable be passed this way, and this is why: a
    /// reference has to point at somewhere that stays put, and the address of
    /// a value on the stack would not.
    pub(crate) fn emit_reference(&mut self, target: &BoundExpression) -> Result<(), EmitError> {
        match &target.kind {
            // `*p` is a place whose address is `p` itself.
            BoundExpressionKind::Dereference { operand } => {
                self.emit_expression(operand, true)?;
            }
            // A value type being initialized is a local, and a `ref this`
            // extension `Add` is handed that local's address.
            BoundExpressionKind::CreatedObject
                if matches!(self.creating.last(), Some(Created::Local(_))) =>
            {
                if let Some(Created::Local(slot)) = self.creating.last() {
                    self.stream.emit(Instruction::LoadLocalAddress(*slot));
                }
            }
            // `ref x` names the place `x` is, which is what is wanted here.
            BoundExpressionKind::RefArgument { operand, .. } => {
                self.emit_reference(operand)?;
            }
            // `r = ref x` is a variable too: the one `r` now refers to.
            BoundExpressionKind::Assignment {
                target: rebound,
                value,
            } if self.rebinds(rebound, value) => {
                self.emit_expression(value, true)?;
                self.stream.emit(Instruction::Dup);
                match &rebound.kind {
                    BoundExpressionKind::Local(local) => {
                        self.stream.emit(Instruction::StoreLocal(local.0 as u16));
                    }
                    BoundExpressionKind::Parameter(symbol) => {
                        let index = self.argument_index(*symbol)?;
                        self.stream.emit(Instruction::StoreArgument(index));
                    }
                    _ => unreachable!("rebinds only takes a local or a parameter"),
                }
            }
            // `c ? ref a : ref b` is one of two places, and which one is
            // decided here rather than by copying either.
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } if is_ref_branch(consequence) && is_ref_branch(alternative) => {
                let taken = self.stream.label();
                let end = self.stream.label();
                self.emit_branch_if_true(condition, taken)?;
                self.emit_reference(alternative)?;
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(taken);
                self.emit_reference(consequence)?;
                self.stream.mark(end);
            }
            BoundExpressionKind::Local(local) => {
                // A captured variable lives in the display class, so its
                // address is the address of a field.
                if let Some(capture) = self.captured_local(*local) {
                    self.push_holder(capture.holder);
                    self.stream
                        .emit(Instruction::LoadFieldAddress(capture.token));
                } else if self.is_by_ref_local(*local) {
                    // A `ref` local already holds a reference: passing it on
                    // passes the same one, and taking its address again would
                    // point at the slot holding the reference.
                    self.stream.emit(Instruction::LoadLocal(self.slot(local)));
                } else {
                    self.stream
                        .emit(Instruction::LoadLocalAddress(self.slot(local)));
                }
            }
            // A struct's `this` kept in `<>4__this` is that field, written in
            // place: `this.F = 1` in an `async` struct method changes the
            // machine's copy (C# gives the method a copy of `this`).
            BoundExpressionKind::This if let Some(capture) = self.captured_this() => {
                self.push_holder(capture.holder);
                self.stream
                    .emit(Instruction::LoadFieldAddress(capture.token));
            }
            BoundExpressionKind::Parameter(symbol) => {
                if let Some(capture) = self.captured_parameter(*symbol) {
                    self.push_holder(capture.holder);
                    self.stream
                        .emit(Instruction::LoadFieldAddress(capture.token));
                } else if self.is_by_reference(*symbol) {
                    // Already a reference: passing it on passes the same one.
                    let index = self.argument_index(*symbol)?;
                    self.stream.emit(Instruction::LoadArgument(index));
                } else {
                    let index = self.argument_index(*symbol)?;
                    self.stream.emit(Instruction::LoadArgumentAddress(index));
                }
            }
            // A `ref` field's value is the reference: the variable is where
            // it points, not the field.
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                field,
            } if self.is_ref_field(*field) => {
                let token = self.field_token_on(*field, Some(&receiver.ty))?;
                self.emit_receiver(receiver)?;
                self.stream.emit(Instruction::LoadField(token));
            }
            BoundExpressionKind::Field { receiver, field } => {
                let token = self.field_token_on(*field, receiver.as_deref().map(|it| &it.ty))?;
                // A `fixed` buffer's address is its first element's, the one
                // field of the struct made for it.
                let element = self.emitter.fixed_element_field(*field)?;
                match receiver.as_deref().filter(|value| !is_type_name(value)) {
                    // A field reached through a `T` is a field of the class
                    // `T` is constrained to, so the receiver is a reference:
                    // `ldflda` wants that reference, not the address of the
                    // slot holding it, which is what `constrained.` wants.
                    Some(receiver) if matches!(receiver.ty, Type::TypeParameter(_)) => {
                        self.emit_expression(receiver, true)?;
                        self.box_if_needed(&receiver.ty)?;
                        self.stream.emit(Instruction::LoadFieldAddress(token));
                    }
                    // A buffer in a `readonly` field is still reached in
                    // place: its elements are read through the pointer, and
                    // a copy would be read instead of the buffer.
                    Some(receiver)
                        if element.is_some()
                            && self.emitter.is_value_type(&receiver.ty)
                            && self.lives_somewhere(receiver) =>
                    {
                        self.emit_reference(receiver)?;
                        self.stream.emit(Instruction::LoadFieldAddress(token));
                    }
                    // `M().f` where `M` returns a reference is a field of the
                    // variable it refers to, and `in` hands on that field
                    // itself, not a copy.
                    Some(receiver)
                        if self.emitter.is_value_type(&receiver.ty)
                            && self.returns_reference(receiver) =>
                    {
                        self.emit_reference(receiver)?;
                        self.stream.emit(Instruction::LoadFieldAddress(token));
                    }
                    Some(receiver) => {
                        self.emit_receiver(receiver)?;
                        self.stream.emit(Instruction::LoadFieldAddress(token));
                    }
                    None => self.stream.emit(Instruction::LoadStaticFieldAddress(token)),
                }
                if let Some(element) = element {
                    self.stream.emit(Instruction::LoadFieldAddress(element));
                }
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                self.emit_expression(array, true)?;
                if indices.len() > 1 {
                    let address = self.array_member(array, ArrayMember::Address, &target.ty)?;
                    for index in indices {
                        self.emit_expression(index, true)?;
                    }
                    self.stream
                        .call_effect(Instruction::Call(address), indices.len() + 1, 1);
                } else {
                    let element = self.emitter.type_token(&target.ty)?;
                    self.emit_single_index(indices)?;
                    self.stream.emit(Instruction::LoadElementAddress(element));
                }
            }
            BoundExpressionKind::FunctionPointerCall { pointer, arguments }
                if matches!(&pointer.ty, Type::FunctionPointer(signature)
                    if signature.returns_ref != RefKind::None) =>
            {
                self.emit_function_pointer_call(pointer, arguments, &target.ty, false)?;
            }
            // `__refvalue(r, T)` is a variable: the address `r` holds.
            BoundExpressionKind::RefValue(operand) => {
                self.emit_expression(operand, true)?;
                let token = self.emitter.type_token(&target.ty)?;
                self.stream.emit(Instruction::RefAnyValue(token));
            }
            // A method that returns by reference hands back the reference
            // itself: the call *is* the address, and there is nothing here to
            // take the address of.
            BoundExpressionKind::Call {
                receiver,
                method,
                type_arguments,
                arguments,
                virtual_call,
            } if matches!(self.emitter.type_of(*method), Type::ByRef(_)) => {
                let returned = self.emitter.type_of(*method).value().clone();
                self.emit_call(&CallSite {
                    receiver: receiver.as_deref(),
                    method: *method,
                    type_arguments,
                    arguments,
                    virtual_call: *virtual_call,
                    result: &returned,
                    read: false,
                })?;
            }
            // `ref buckets[i]` on a `ref T this[int]` is the reference the
            // getter hands back, kept as it stands rather than read through
            // and copied into a slot — a write through it has to land in the
            // collection.
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } if matches!(self.emitter.type_of(*indexer), Type::ByRef(_)) => {
                let getter = self
                    .emitter
                    .property_accessor(*indexer, Some(&receiver.ty), false)?;
                self.emit_receiver_for(receiver, *indexer)?;
                for argument in arguments {
                    self.emit_expression(argument, true)?;
                }
                let instruction = self.receiver_call(receiver, *indexer, getter)?;
                self.stream.call_effect(instruction, 1 + arguments.len(), 1);
            }
            BoundExpressionKind::Property { receiver, property }
                if matches!(self.emitter.type_of(*property), Type::ByRef(_)) =>
            {
                let getter = self.emitter.property_accessor(
                    *property,
                    receiver.as_ref().map(|receiver| &receiver.ty),
                    false,
                )?;
                match receiver.as_deref().filter(|value| !is_type_name(value)) {
                    Some(receiver) => {
                        self.emit_receiver_for(receiver, *property)?;
                        let instruction = self.receiver_call(receiver, *property, getter)?;
                        self.stream.call_effect(instruction, 1, 1);
                    }
                    None => self.stream.call_effect(Instruction::Call(getter), 0, 1),
                }
            }
            // What comes before the last step is done for what it does; the
            // last is the variable.
            BoundExpressionKind::Sequence(steps) if !steps.is_empty() => {
                let (last, rest) = steps.split_last().expect("not empty");
                for step in rest {
                    self.emit_expression(step, false)?;
                }
                self.emit_reference(last)?;
            }
            // Inside a value type `this` is already the address of the
            // value, and `ref this` is that address.
            BoundExpressionKind::This if self.instance && self.in_value_type => {
                self.stream.emit(Instruction::LoadArgument(0));
            }
            _ => {
                // A value that is not a variable has no address of its own,
                // and calling a struct's method on one still needs somewhere
                // to point: `(flag ? a : b).ToString()` computes a value, and
                // a local is where it goes so that there is something to take
                // the address of. C# spills the same way, and the binder is
                // what refuses a `ref` argument that is not a variable.
                let slot = self.temporary(&target.ty)?;
                self.emit_expression(target, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                self.stream.emit(Instruction::LoadLocalAddress(slot));
            }
        }
        Ok(())
    }

    /// Whether a parameter of the method being emitted holds an address, in
    /// which case reading it means reading through it. `in` does as much as
    /// `ref` and `out` do: what it promises is that nothing writes back.
    fn is_by_reference(&self, parameter: SymbolId) -> bool {
        self.emitter.is_by_reference(Some(parameter))
    }

    /// The width a reference to this type is read and written at.
    /// `this` as a value: the argument itself in a class, and what the
    /// argument points at in a struct, whose `this` is an address. A state
    /// machine or display class made inside a struct keeps a copy.
    pub(crate) fn push_this_value(&mut self) -> Result<(), EmitError> {
        self.stream.emit(Instruction::LoadArgument(0));
        if self.instance && self.in_value_type {
            let ty = self.self_type.clone();
            let kind = self.indirect_kind(&ty)?;
            self.stream.emit(Instruction::LoadIndirect(kind));
        }
        Ok(())
    }

    pub(crate) fn indirect_kind(&mut self, ty: &Type) -> Result<IndirectKind, EmitError> {
        use rustlyn_semantics::SpecialType as S;
        if let Some(special) = self.emitter.special_type_of(ty) {
            return Ok(match special {
                // A `bool` is read as the unsigned byte it is, as `csc`
                // reads it: sign-extended, 0xFF would be -1 and not equal to
                // the same `true` read any other way.
                S::SByte => IndirectKind::I1,
                S::Boolean | S::Byte => IndirectKind::U1,
                S::Int16 => IndirectKind::I2,
                S::UInt16 | S::Char => IndirectKind::U2,
                S::Int32 | S::UInt32 => IndirectKind::I4,
                S::Int64 | S::UInt64 => IndirectKind::I8,
                S::Single => IndirectKind::R4,
                S::Double => IndirectKind::R8,
                // `decimal`, `IntPtr` and the other special structs are
                // copied whole like any struct; `object` and `string` are
                // references.
                _ if self.emitter.is_value_type(ty) => {
                    IndirectKind::Object(self.emitter.type_token(ty)?)
                }
                _ => IndirectKind::Ref,
            });
        }
        if self.emitter.is_value_type(ty) {
            // A struct is copied whole, which needs its token.
            return Ok(IndirectKind::Object(self.emitter.type_token(ty)?));
        }
        Ok(IndirectKind::Ref)
    }

    /// A delegate over the method a lambda became.
    ///
    /// Which is all a lambda is in the CLI: a method with an unspeakable name,
    /// and a delegate pointing at it. One that captures nothing needs no
    /// target at all.
    fn emit_lambda(&mut self, delegate_type: &Type, index: usize) -> Result<(), EmitError> {
        let owner = self
            .owner
            .ok_or_else(|| EmitError::new("a lambda outside any member"))?;
        let captures_this = self.instance
            && self
                .body
                .lambdas
                .get(index)
                .is_some_and(|lambda| lambda.captures_this);
        let target = *self.emitter.lambdas.get(&(owner, index)).ok_or_else(|| {
            EmitError::new(format!(
                "cannot emit lambda {index} of `{}`: it was planned nowhere",
                self.emitter.compilation.symbols().qualified_name(owner)
            ))
        })?;
        let constructor = self.delegate_constructor(delegate_type)?;

        // One that captures nothing is a method of the type's `<>c`, and its
        // delegate is made once and kept:
        // `<>9__0_1 ?? (<>9__0_1 = new D(<>9.<M>b__0_1))`.
        if let Some(shared) = self.emitter.singleton_lambdas.get(&(owner, index)).copied() {
            let made = self.stream.label();
            self.stream.emit(Instruction::LoadStaticField(shared.cache));
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::BranchIfTrue(made));
            self.stream.emit(Instruction::Pop);
            self.stream
                .emit(Instruction::LoadStaticField(shared.instance));
            self.stream.emit(Instruction::LoadFunction(shared.method));
            self.stream
                .call_effect(Instruction::NewObject(constructor), 2, 1);
            self.stream.emit(Instruction::Dup);
            self.stream
                .emit(Instruction::StoreStaticField(shared.cache));
            self.stream.mark(made);
            return Ok(());
        }

        // A lambda that captures is a method of the display class, so that is
        // what the delegate is made over — named through the view the method
        // being emitted has of it. From inside the class its parameters are
        // its own, `!0`; from the method that makes one they are that
        // method's, `!!0`, and neither name means anything in the other
        // place.
        let held = self
            .display
            .as_ref()
            .and_then(|(display, at)| match at {
                DisplayAt::This => display.inside.methods.get(&index).copied(),
                DisplayAt::Local(_) => display.outside.methods.get(&index).copied(),
            })
            .map(|token| (Holder::Display, token))
            .or_else(|| {
                self.captures.iter().find_map(|(view, holder)| {
                    view.methods.get(&index).map(|token| (*holder, *token))
                })
            });
        if let Some((holder, _)) = held {
            self.push_holder(holder);
        } else if captures_this {
            // Inside a closure's machine `this` is the machine; what the
            // lambda closes over is what the body calls `this`.
            match self.captured_this() {
                Some(capture) => {
                    self.push_holder(capture.holder);
                    self.stream.emit(Instruction::LoadField(capture.token));
                }
                None => self.stream.emit(Instruction::LoadArgument(0)),
            }
        } else {
            self.stream.emit(Instruction::LoadNull);
        }
        let target = match held {
            // A lambda inside a generic local function is a generic method
            // of the class, named through the function's parameters as the
            // code making the delegate sees them.
            Some((_, token)) => match self.emitter.lambda_generics.get(&(owner, index)).cloned() {
                Some(generics) => {
                    let all: Vec<Type> = generics.into_iter().map(Type::TypeParameter).collect();
                    self.emitter.method_instantiation(token, &all)?
                }
                None => token,
            },
            None => {
                // A lambda made for a generic method carries that method's
                // parameters, and is named through an instantiation of them
                // whether it is reached as the definition or through the
                // type's own construction.
                let inherited = self
                    .emitter
                    .inherited_generics
                    .get(&target)
                    .cloned()
                    .unwrap_or_default();
                let named = self.through_own_construction(target, index)?;
                if inherited.is_empty() {
                    named
                } else {
                    let all: Vec<Type> = inherited.into_iter().map(Type::TypeParameter).collect();
                    self.emitter.method_instantiation(named, &all)?
                }
            }
        };
        self.stream.emit(Instruction::LoadFunction(target));
        self.stream
            .call_effect(Instruction::NewObject(constructor), 2, 1);
        Ok(())
    }

    /// The token naming a lambda's method from inside the type that holds it.
    ///
    /// A lambda written in `Pool<T>` becomes a method of `Pool<T>`, and there
    /// is no such method until `T` is something: `ldftn` on the definition
    /// loads a pointer the runtime refuses to call. It has to go through a
    /// `MemberRef` under `Pool<!0>`, which is the same method said the way
    /// the CLI can say it.
    fn through_own_construction(
        &mut self,
        target: Token,
        index: usize,
    ) -> Result<Token, EmitError> {
        // A lambda that captures is a method of the display class, which is
        // named elsewhere.
        if self.display.as_ref().is_some_and(|(display, at)| match at {
            DisplayAt::This => display.inside.methods.contains_key(&index),
            DisplayAt::Local(_) => display.outside.methods.contains_key(&index),
        }) {
            return Ok(target);
        }
        let Some(owner) = self.owner else {
            return Ok(target);
        };
        let Some(container) = self.emitter.enclosing_type(owner) else {
            return Ok(target);
        };
        let Some(construction) = self.emitter.own_construction(container) else {
            return Ok(target);
        };
        let Some(lambda) = self.body.lambdas.get(index) else {
            return Ok(target);
        };
        let instance = lambda.captures_this;
        let name = self
            .emitter
            .lambda_names
            .get(&(owner, index))
            .cloned()
            .ok_or_else(|| EmitError::new("a lambda with no method planned"))?;
        // An `async` lambda's method returns the task, whatever its body
        // returns: the reference has to say what the definition says.
        let returns = lambda
            .task_type
            .clone()
            .unwrap_or_else(|| lambda.return_type.clone());
        let parameters: Vec<(Type, bool)> = lambda
            .parameters
            .iter()
            .map(|local| {
                let slot = &self.body.locals[local.0 as usize];
                (slot.ty.clone(), slot.by_ref)
            })
            .collect();
        let returns = self.emitter.sig_type(&returns)?;
        let mut written = Vec::with_capacity(parameters.len());
        for (parameter, by_ref) in &parameters {
            let ty = self.emitter.sig_type(parameter)?;
            written.push(if *by_ref {
                SigType::ByRef(Box::new(ty))
            } else {
                ty
            });
        }
        // The definition declares the enclosing method's type parameters as
        // its own, and a reference to it has to say how many.
        let arity = self
            .emitter
            .inherited_generics
            .get(&target)
            .map_or(0, |inherited| inherited.len() as u32);
        let signature = generic_method_signature(instance, arity, &returns, &written);
        let spec = self.emitter.type_token(&construction)?;
        Ok(self.emitter.references.member_of_spec(
            &mut self.emitter.metadata,
            spec,
            &name,
            &signature,
        ))
    }

    /// The `.ctor(object, native int)` of a delegate type.
    fn delegate_constructor(&mut self, delegate_type: &Type) -> Result<Token, EmitError> {
        let symbol = delegate_type
            .symbol()
            .ok_or_else(|| EmitError::new("a delegate creation with no delegate type"))?;
        // Every delegate's constructor takes the same two arguments, and no
        // source anywhere writes one: the runtime supplies the body. So the
        // reference can be written out from nothing but the type — which is
        // the only way to name it when the type is a construction, because
        // then there is no definition to point at.
        let constructed = self.emitter.is_constructed(delegate_type);
        if let Some(token) = self.emitter.constructors.get(&symbol)
            && !constructed
        {
            return Ok(*token);
        }
        if self.emitter.compilation.is_from_corlib(symbol) || constructed {
            let signature = method_signature(
                true,
                &SigType::Primitive(ElementType::Void),
                &[
                    SigType::Primitive(ElementType::Object),
                    SigType::Primitive(ElementType::I),
                ],
            );
            if constructed {
                let spec = self.emitter.type_token(delegate_type)?;
                return Ok(self.emitter.references.member_of_spec(
                    &mut self.emitter.metadata,
                    spec,
                    ".ctor",
                    &signature,
                ));
            }
            let parent = self.emitter.referenced_type(symbol);
            return Ok(self.emitter.references.member_ref_on(
                &mut self.emitter.metadata,
                parent,
                ".ctor",
                &signature,
            ));
        }
        Err(EmitError::new(format!(
            "cannot make a `{}`: it is not a delegate",
            delegate_type.display(self.emitter.compilation.symbols())
        )))
    }

    /// `$"a{b}"` becomes `String.Concat(object[])`, which is what `csc` emits
    /// once there is more than one hole and what always behaves the same.
    fn emit_interpolated_string(&mut self, parts: &[BoundExpression]) -> Result<(), EmitError> {
        let object = SigType::Primitive(ElementType::Object);
        let object_token = self
            .emitter
            .references
            .type_ref(&mut self.emitter.metadata, "System.Object");

        self.stream.emit(Instruction::LoadInt32(parts.len() as i32));
        self.stream.emit(Instruction::NewArray(object_token));
        for (index, part) in parts.iter().enumerate() {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(index as i32));
            // A hole written with no alignment or format is its value; one
            // with either is the string `string.Format` makes of it.
            match &part.kind {
                BoundExpressionKind::StringInsert {
                    value,
                    alignment: None,
                    format: None,
                } => {
                    self.emit_expression(value, true)?;
                    self.box_if_needed(&value.ty)?;
                }
                _ => self.emit_expression(part, true)?,
            }
            self.stream.emit(Instruction::StoreElementRef);
        }
        let concat = self.emitter.framework_member(
            "System.String",
            "Concat",
            false,
            &SigType::Primitive(ElementType::String),
            &[SigType::Array(Box::new(object))],
        );
        self.stream.call_effect(Instruction::Call(concat), 1, 1);
        Ok(())
    }

    /// `receiver with { X = 1 }`: a copy of the receiver, and then the
    /// initializer run against the copy.
    ///
    /// Loading a struct or a tuple *is* copying it. A record class copies
    /// itself through its `<Clone>$`, called virtually so that a derived
    /// record copies as what it is; anything else has no copy to make and is
    /// refused.
    fn emit_with(
        &mut self,
        receiver: &BoundExpression,
        initializers: &[BoundExpression],
        ty: &Type,
    ) -> Result<(), EmitError> {
        self.emit_expression(receiver, true)?;
        if !self.emitter.is_value_type(ty) {
            let symbols = self.emitter.compilation.symbols();
            let clone = ty
                .symbol()
                .and_then(|symbol| {
                    symbols
                        .lookup(symbol, "<Clone>$")
                        .iter()
                        .copied()
                        .find(|member| symbols.get(*member).kind == SymbolKind::Method)
                })
                .ok_or_else(|| {
                    EmitError::new(format!(
                        "cannot emit `with` on `{}`: it is not a record",
                        ty.display(symbols)
                    ))
                })?;
            let token = self.method_token_on(clone, Some(ty))?;
            self.stream
                .call_effect(Instruction::CallVirtual(token), 1, 1);
        }
        self.emit_initializers(initializers, ty)
    }

    /// Runs an object or collection initializer against the value the
    /// expression just left on the stack.
    ///
    /// For a reference type each one starts by duplicating it — that is what
    /// `CreatedObject` becomes — and leaves nothing behind, so the new object
    /// is still on top when they are done. A value type has no reference to
    /// duplicate: it goes into a local, the members are written through that
    /// local's address, and the finished value is loaded back.
    fn emit_initializers(
        &mut self,
        initializers: &[BoundExpression],
        ty: &Type,
    ) -> Result<(), EmitError> {
        if initializers.is_empty() {
            return Ok(());
        }
        if self.emitter.is_value_type(ty) {
            let slot = self.temporary(ty)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.creating.push(Created::Local(slot));
            let result = self.emit_each_initializer(initializers);
            self.creating.pop();
            result?;
            self.stream.emit(Instruction::LoadLocal(slot));
            return Ok(());
        }
        if initializers.iter().any(mentions_dynamic) {
            let slot = self.temporary(ty)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.creating.push(Created::Held(slot));
            let result = self.emit_each_initializer(initializers);
            self.creating.pop();
            result?;
            self.stream.emit(Instruction::LoadLocal(slot));
            return Ok(());
        }
        self.creating.push(Created::Stack);
        let result = self.emit_each_initializer(initializers);
        self.creating.pop();
        result
    }

    fn emit_each_initializer(&mut self, initializers: &[BoundExpression]) -> Result<(), EmitError> {
        for initializer in initializers {
            self.emit_expression(initializer, false)?;
        }
        Ok(())
    }

    /// Boxes a value type on its way into something that holds references.
    pub(crate) fn box_if_needed(&mut self, ty: &Type) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        // A type parameter boxes whatever its constraints say: the box is
        // the identity where `T` turns out to be a reference type.
        if !matches!(ty, Type::TypeParameter(_))
            && (ty.is_reference_type(symbols) || matches!(ty, Type::Array { .. } | Type::Null))
        {
            return Ok(());
        }
        let token = self.emitter.type_token(ty)?;
        self.stream.emit(Instruction::Box(token));
        Ok(())
    }

    fn emit_conversion(
        &mut self,
        operand: &BoundExpression,
        conversion: ConversionKind,
        target: &Type,
    ) -> Result<(), EmitError> {
        // `null` given to a value type is that type's default — the empty
        // `Nullable<T>`, nearly always. A struct is not a reference, and
        // `ldnull` where one is wanted is not a program: a runtime meeting it
        // does not refuse the body, it falls over compiling it.
        let symbols = self.emitter.compilation.symbols();
        if matches!(operand.ty, Type::Null)
            && !matches!(target, Type::Null | Type::Error | Type::Array { .. })
            && !target.is_reference_type(symbols)
        {
            return self.emit_default(target);
        }
        // A null pointer is the address zero, not a null reference: `ldnull`
        // where an `int*` is wanted is a program the runtime refuses.
        if matches!(operand.ty, Type::Null)
            && matches!(target, Type::Pointer(_) | Type::FunctionPointer(_))
        {
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::ConvertU);
            return Ok(());
        }
        self.emit_expression(operand, true)?;
        match conversion {
            ConversionKind::Identity | ConversionKind::ImplicitReference => {}
            ConversionKind::Numeric => self.convert_number_from(&operand.ty, target)?,
            ConversionKind::Boxing => self.box_if_needed(&operand.ty)?,
            // A tuple into a tuple of other element types: each element is
            // read off the one made, converted, and a new one is made of them.
            ConversionKind::TupleElements => {
                let (Some(from_elements), Some(to_elements)) = (
                    self.tuple_element_types(&operand.ty),
                    self.tuple_element_types(target),
                ) else {
                    return Err(EmitError::new("a tuple conversion between non-tuples"));
                };
                let held = self.temporary(&operand.ty)?;
                self.stream.emit(Instruction::StoreLocal(held));
                for (index, (from, to)) in from_elements.iter().zip(&to_elements).enumerate() {
                    let chain = self.emitter.tuple_field(&operand.ty, index)?;
                    self.stream.emit(Instruction::LoadLocal(held));
                    for field in chain {
                        self.stream.emit(Instruction::LoadField(field));
                    }
                    self.emit_value_conversion(from, to)?;
                }
                self.emit_tuple_constructors(target, to_elements.len())?;
            }
            ConversionKind::Unboxing => {
                // `(T)i` on an `int` is `box int32; unbox.any !!T`, as `(int)t`
                // on a `T` is `box !!T; unbox.any int32`: a value of either
                // side is boxed first, and a reference is one already.
                self.box_if_needed(&operand.ty)?;
                let token = self.emitter.type_token(target)?;
                self.stream.emit(Instruction::UnboxAny(token));
            }
            ConversionKind::ExplicitReference => {
                let token = self.emitter.type_token(target)?;
                self.stream.emit(Instruction::CastClass(token));
            }
            // `int` into an `int?` makes one holding the value; back out of
            // it reads the value, and `Value` is what throws where there is
            // nothing in it.
            ConversionKind::NullableWrap => {
                // `3` into a `byte?` is a `byte` first: what goes into the
                // constructor has to be the type it takes.
                // `(IntPtr?)aFloat` is a native integer first, which only
                // the conversion from the operand's own type knows to make.
                if let Some(inner) = self.emitter.nullable_underlying(target)
                    && inner != operand.ty
                {
                    self.convert_number_from(&operand.ty, &inner)?;
                }
                let token = self.emitter.nullable_constructor(target)?;
                self.stream.call_effect(Instruction::NewObject(token), 1, 1);
            }
            ConversionKind::NullableUnwrap => {
                let held = self.temporary(&operand.ty)?;
                self.stream.emit(Instruction::StoreLocal(held));
                self.stream.emit(Instruction::LoadLocalAddress(held));
                let token = self.emitter.nullable_member(&operand.ty, "get_Value")?;
                self.stream.call_effect(Instruction::Call(token), 1, 1);
            }
            // `byte?` into an `int?`: what is inside converts, and where
            // there is nothing inside the answer is a null `int?`.
            ConversionKind::NullableLift => {
                let held = self.temporary(&operand.ty)?;
                self.stream.emit(Instruction::StoreLocal(held));
                let has_value = self.emitter.nullable_member(&operand.ty, "get_HasValue")?;
                let value = self
                    .emitter
                    .nullable_member(&operand.ty, "GetValueOrDefault")?;
                let (missing, end) = (self.stream.label(), self.stream.label());
                self.stream.emit(Instruction::LoadLocalAddress(held));
                self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                self.stream.emit(Instruction::BranchIfFalse(missing));
                self.stream.emit(Instruction::LoadLocalAddress(held));
                self.stream.call_effect(Instruction::Call(value), 1, 1);
                let inner = self
                    .emitter
                    .nullable_underlying(target)
                    .unwrap_or_else(|| target.clone());
                self.convert_number(&inner);
                let token = self.emitter.nullable_constructor(target)?;
                self.stream.call_effect(Instruction::NewObject(token), 1, 1);
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(missing);
                self.emit_default(target)?;
                self.stream.mark(end);
            }
        }
        Ok(())
    }

    /// The instruction that turns the number on the stack into this type.
    ///
    /// Nothing at all where the type is not a number: a `bool` is already an
    /// `i4`, and everything else was never a numeric conversion.
    /// The primitive a numeric type is, an enum by what is underneath it.
    fn integer_special(&self, ty: &Type) -> Option<SpecialType> {
        self.emitter.special_type_of(ty).or_else(|| {
            ty.symbol()
                .filter(|symbol| {
                    self.emitter.compilation.symbols().get(*symbol).type_kind()
                        == Some(rustlyn_semantics::TypeKind::Enum)
                })
                .and_then(|symbol| {
                    self.emitter
                        .special_type_of(&self.emitter.enum_underlying(symbol))
                })
        })
    }

    fn convert_number(&mut self, target: &Type) {
        // An enum converts as the integer underneath it does: `(Kind)aLong`
        // narrows to the enum's `int`.
        let special = self.emitter.special_type_of(target).or_else(|| {
            target
                .symbol()
                .filter(|symbol| {
                    self.emitter.compilation.symbols().get(*symbol).type_kind()
                        == Some(rustlyn_semantics::TypeKind::Enum)
                })
                .and_then(|symbol| {
                    self.emitter
                        .special_type_of(&self.emitter.enum_underlying(symbol))
                })
        });
        // In a `checked` region the narrowing traps; the value on the stack
        // came out of an operation on signed integers, which is what the
        // signed forms expect.
        if self.checked
            && let Some(instruction) = self.checked_conversion(target, false)
        {
            self.stream.emit(instruction);
            return;
        }
        let instruction = match special {
            Some(SpecialType::SByte) => Instruction::ConvertI1,
            Some(SpecialType::Byte) => Instruction::ConvertU1,
            Some(SpecialType::Int16) => Instruction::ConvertI2,
            Some(SpecialType::UInt16 | SpecialType::Char) => Instruction::ConvertU2,
            Some(SpecialType::Int32) => Instruction::ConvertI4,
            Some(SpecialType::UInt32) => Instruction::ConvertU4,
            Some(SpecialType::Int64) => Instruction::ConvertI8,
            Some(SpecialType::UInt64) => Instruction::ConvertU8,
            Some(SpecialType::Single) => Instruction::ConvertR4,
            Some(SpecialType::Double) => Instruction::ConvertR8,
            // A number into a pointer is a native integer; a pointer into
            // another pointer is nothing at all.
            None if matches!(target, Type::Pointer(_) | Type::FunctionPointer(_)) => {
                Instruction::ConvertU
            }
            _ => return,
        };
        self.stream.emit(instruction);
    }

    fn emit_binary(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        result: &Type,
    ) -> Result<(), EmitError> {
        // `d1 + d2` combines two delegates and `d1 - d2` takes one out of the
        // other: `Delegate.Combine` and `Delegate.Remove`, cast back.
        let is_delegate = result.symbol().is_some_and(|symbol| {
            self.emitter.compilation.symbols().get(symbol).type_kind() == Some(TypeKind::Delegate)
        });
        if is_delegate && matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract) {
            self.emit_expression(left, true)?;
            self.emit_expression(right, true)?;
            return self.emit_binary_instruction(operator, result, &right.ty);
        }
        // `t == null` on a `T` boxes it, and a `T` that allows a `ref
        // struct` may be boxed only where a branch reads the box at once.
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) {
            let null = |side: &BoundExpression| match &side.kind {
                BoundExpressionKind::Conversion { operand, .. } => {
                    matches!(operand.ty, Type::Null)
                }
                BoundExpressionKind::Literal(ConstantValue::Null) => true,
                // `null` given the type of the `T` it is compared with.
                BoundExpressionKind::Default(Type::TypeParameter(_)) => true,
                _ => matches!(side.ty, Type::Null),
            };
            let operand = if null(right) && !null(left) {
                boxed_type_parameter(left)
            } else if null(left) && !null(right) {
                boxed_type_parameter(right)
            } else {
                None
            };
            if let Some(operand) = operand {
                let token = self.emitter.type_token(&operand.ty)?;
                self.emit_expression(operand, true)?;
                self.stream.emit(Instruction::Box(token));
                let (present, end) = (self.stream.label(), self.stream.label());
                self.stream.emit(Instruction::BranchIfTrue(present));
                let equal = matches!(operator, BinaryOperator::Equality);
                self.stream.emit(Instruction::LoadInt32(i32::from(equal)));
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(present);
                self.stream.emit(Instruction::LoadInt32(i32::from(!equal)));
                self.stream.mark(end);
                return Ok(());
            }
        }
        // The three operators that do not evaluate both sides have to become
        // branches; everything else is two pushes and an instruction.
        match operator {
            BinaryOperator::LogicalAnd => {
                let short = self.stream.label();
                let end = self.stream.label();
                self.emit_expression(left, true)?;
                self.stream.emit(Instruction::BranchIfFalse(short));
                self.emit_expression(right, true)?;
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(short);
                self.stream.emit(Instruction::LoadInt32(0));
                self.stream.mark(end);
                return Ok(());
            }
            BinaryOperator::LogicalOr => {
                let short = self.stream.label();
                let end = self.stream.label();
                self.emit_expression(left, true)?;
                self.stream.emit(Instruction::BranchIfTrue(short));
                self.emit_expression(right, true)?;
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(short);
                self.stream.emit(Instruction::LoadInt32(1));
                self.stream.mark(end);
                return Ok(());
            }
            BinaryOperator::Coalesce => {
                let end = self.stream.label();
                let null = self.stream.label();
                // `a ?? b` on an `int?` has no reference to test: the left is
                // a struct, and `brfalse` on one is not a program. It asks
                // `HasValue` instead, and what it yields is the value inside.
                if self.emitter.nullable_underlying(&left.ty).is_some() {
                    let slot = self.temporary(&left.ty)?;
                    let has_value = self.emitter.nullable_member(&left.ty, "get_HasValue")?;
                    let value = self.emitter.nullable_member(&left.ty, "get_Value")?;
                    self.emit_expression(left, true)?;
                    self.stream.emit(Instruction::StoreLocal(slot));
                    self.stream.emit(Instruction::LoadLocalAddress(slot));
                    self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                    self.stream.emit(Instruction::BranchIfFalse(null));
                    // `a ?? b` where `b` is a `T?` too gives a `T?`: the
                    // left is yielded as it is, and only where the whole
                    // thing is a `T` is the value taken out of it.
                    if self.emitter.nullable_underlying(result).is_some() {
                        self.stream.emit(Instruction::LoadLocal(slot));
                    } else {
                        self.stream.emit(Instruction::LoadLocalAddress(slot));
                        self.stream.call_effect(Instruction::Call(value), 1, 1);
                        // `n ?? o` with an `object` on the right is an
                        // `object`: the value is boxed on its way out.
                        if let Some(inner) = self.emitter.nullable_underlying(&left.ty) {
                            self.emit_value_conversion(&inner, result)?;
                        }
                    }
                    self.stream.emit(Instruction::Branch(end));
                    self.stream.mark(null);
                    self.emit_expression(right, true)?;
                    self.emit_value_conversion(&right.ty, result)?;
                    self.stream.mark(end);
                    return Ok(());
                }
                // A `T` is tested boxed: a struct is never null, and the
                // verifier has no test of a `T` otherwise. What it yields is
                // the `T` itself, as the type of the whole where that differs.
                if matches!(left.ty, Type::TypeParameter(_)) {
                    let slot = self.temporary(&left.ty)?;
                    let has = self.stream.label();
                    self.emit_expression(left, true)?;
                    self.stream.emit(Instruction::StoreLocal(slot));
                    self.stream.emit(Instruction::LoadLocal(slot));
                    self.box_if_needed(&left.ty)?;
                    self.stream.emit(Instruction::BranchIfTrue(has));
                    self.emit_expression(right, true)?;
                    self.stream.emit(Instruction::Branch(end));
                    self.stream.mark(has);
                    self.stream.emit(Instruction::LoadLocal(slot));
                    if *result != left.ty {
                        self.box_if_needed(&left.ty)?;
                        if !result.is_reference_type(self.emitter.compilation.symbols())
                            || matches!(result, Type::TypeParameter(_))
                        {
                            let token = self.emitter.type_token(result)?;
                            self.stream.emit(Instruction::UnboxAny(token));
                        }
                    }
                    self.stream.mark(end);
                    return Ok(());
                }
                self.emit_expression(left, true)?;
                self.emit_value_conversion(&left.ty, result)?;
                self.stream.emit(Instruction::Dup);
                if matches!(result, Type::TypeParameter(_)) {
                    self.box_if_needed(result)?;
                }
                self.stream.emit(Instruction::BranchIfTrue(end));
                self.stream.emit(Instruction::Pop);
                self.emit_expression(right, true)?;
                self.emit_value_conversion(&right.ty, result)?;
                self.stream.mark(end);
                let _ = null;
                return Ok(());
            }
            _ => {}
        }

        // `==` on strings compares characters, not references, so it is a
        // call rather than a `ceq`; and `"a" + 1` is a call too, on whichever
        // side the string is.
        let concatenates = matches!(operator, BinaryOperator::Add)
            && self.emitter.special_type_of(result) == Some(SpecialType::String);
        let compares_strings = matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) && self.is_string(&left.ty)
            && self.is_string(&right.ty);
        if concatenates || compares_strings {
            return self.emit_string_operator(operator, left, right);
        }

        // `x == null` on a `T?` asks whether it holds anything. The binder
        // has already made the `null` a `T?` of its own — it has to, there is
        // nothing else for it to be — so what is written is the only thing
        // left saying which comparison this is.
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) {
            let held = match (self.written_null(left), self.written_null(right)) {
                (false, true) => Some(left),
                (true, false) => Some(right),
                // `default(T?) == null`: two nulls, which are equal. A `T`'s
                // default may be no null at all, and is left to the tests below.
                (true, true)
                    if !matches!(left.ty, Type::TypeParameter(_))
                        && !matches!(right.ty, Type::TypeParameter(_)) =>
                {
                    self.stream.emit(Instruction::LoadInt32(i32::from(
                        operator == BinaryOperator::Equality,
                    )));
                    return Ok(());
                }
                _ => None,
            };
            // `t == null` on a `T` boxes it first: the verifier has no
            // comparison of a `T` with a reference, and a `T` that turns out
            // a struct boxes to something that is never null, which is the
            // answer the language gives.
            if let Some(held) = held
                && matches!(held.ty, Type::TypeParameter(_))
            {
                self.emit_expression(held, true)?;
                self.box_if_needed(&held.ty)?;
                self.stream.emit(Instruction::LoadNull);
                self.stream.emit(Instruction::CompareEqual);
                if operator == BinaryOperator::Inequality {
                    self.negate();
                }
                return Ok(());
            }
            if let Some(held) = held
                && self.emitter.nullable_underlying(&held.ty).is_some()
            {
                let slot = self.temporary(&held.ty)?;
                let has_value = self.emitter.nullable_member(&held.ty, "get_HasValue")?;
                self.emit_expression(held, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                self.stream.emit(Instruction::LoadLocalAddress(slot));
                self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                if operator == BinaryOperator::Equality {
                    self.negate();
                }
                return Ok(());
            }
        }

        // Both sides a `T?` means the lifted operator of §12.4.8, which is
        // not an instruction at all: `brfalse` on a struct is no program.
        if self.emitter.nullable_underlying(&left.ty).is_some()
            && self.emitter.nullable_underlying(&right.ty).is_some()
        {
            return self.emit_lifted(operator, left, right, result);
        }

        // `b ^ true` is `!b`, and is written as the comparison with zero
        // `csc` makes of it: a `bool` holding 0xFF xored with 1 is still
        // true, and `!` has to say false.
        if operator == BinaryOperator::ExclusiveOr
            && self.emitter.special_type_of(result) == Some(SpecialType::Boolean)
        {
            let constant_true = |value: &BoundExpression| {
                matches!(
                    value.kind,
                    BoundExpressionKind::Literal(ConstantValue::Boolean(true))
                )
            };
            let other = if constant_true(right) {
                Some(left)
            } else if constant_true(left) {
                Some(right)
            } else {
                None
            };
            if let Some(other) = other {
                self.emit_expression(other, true)?;
                self.negate();
                return Ok(());
            }
        }
        // `b == true` is `b` and `b == false` is `!b`, which is what `csc`
        // writes: a `bool` is any non-zero byte, and `ceq` with 1 would call
        // 0xFF false.
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) && self.emitter.special_type_of(&left.ty) == Some(SpecialType::Boolean)
            && self.emitter.special_type_of(&right.ty) == Some(SpecialType::Boolean)
        {
            let constant = |value: &BoundExpression| match value.kind {
                BoundExpressionKind::Literal(ConstantValue::Boolean(value)) => Some(value),
                _ => None,
            };
            let (other, value) = match (constant(left), constant(right)) {
                (None, Some(value)) => (Some(left), value),
                (Some(value), None) => (Some(right), value),
                _ => (None, false),
            };
            if let Some(other) = other {
                self.emit_expression(other, true)?;
                if value != (operator == BinaryOperator::Equality) {
                    self.negate();
                }
                return Ok(());
            }
        }

        // `p + n` moves by `n` elements, not `n` bytes (§23.6.7), and `p - q`
        // is how many elements apart they are.
        if matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract)
            && (matches!(left.ty, Type::Pointer(_)) || matches!(right.ty, Type::Pointer(_)))
        {
            return self.emit_pointer_arithmetic(operator, left, right);
        }
        self.emit_expression(left, true)?;
        if Self::is_shift(operator) {
            self.emit_shift_count(right, &left.ty)?;
        } else {
            self.emit_expression(right, true)?;
        }
        // A `decimal` is not a primitive: the runtime has no instruction for
        // it, and every operator is a call on `System.Decimal`.
        if self.is_decimal(&left.ty) || self.is_decimal(&right.ty) {
            return self.emit_decimal_operator(operator);
        }
        let unsigned = self.is_unsigned(&left.ty);
        let floating = matches!(
            self.emitter.special_type_of(&left.ty),
            Some(SpecialType::Single | SpecialType::Double)
        );
        self.emit_operator(operator, unsigned, floating);
        // `E - E` is the enum's underlying type, as narrow as that is.
        let from_enums = operator == BinaryOperator::Subtract
            && self.is_enum(&left.ty)
            && self.is_enum(&right.ty);
        self.narrow_enum_result(operator, result, from_enums);
        Ok(())
    }

    fn is_enum(&self, ty: &Type) -> bool {
        ty.symbol().is_some_and(|symbol| {
            self.emitter.compilation.symbols().get(symbol).type_kind()
                == Some(rustlyn_semantics::TypeKind::Enum)
        })
    }

    /// `c + b` on an enum over a `byte` is worked out in `int` and is an
    /// enum again: it is narrowed back, and in a `checked` context the
    /// narrowing is what overflows (§12.10.5).
    fn narrow_enum_result(&mut self, operator: BinaryOperator, result: &Type, from_enums: bool) {
        // Only an enum's arithmetic is typed narrower than `int`: `E + U` is
        // the enum, and `E - E` its underlying type, the operands already
        // converted to it.
        let is_enum =
            from_enums || self.is_enum(result) || self.emitter.special_type_of(result).is_some();
        if is_enum
            && matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract)
            && matches!(
                self.integer_special(result),
                Some(
                    SpecialType::SByte
                        | SpecialType::Byte
                        | SpecialType::Int16
                        | SpecialType::UInt16
                )
            )
        {
            self.convert_number(result);
        }
    }

    fn is_decimal(&self, ty: &Type) -> bool {
        self.emitter.special_type_of(ty) == Some(SpecialType::Decimal)
    }

    /// The `System.Decimal` type as a signature spells it.
    fn decimal_sig(&mut self) -> SigType {
        let coded = self
            .emitter
            .references
            .type_ref_coded(&mut self.emitter.metadata, "System.Decimal");
        SigType::Named {
            value_type: true,
            coded,
        }
    }

    /// `a + b`, `a < b` and the rest on two decimals already on the stack,
    /// which are calls to the operators `System.Decimal` declares.
    fn emit_decimal_operator(&mut self, operator: BinaryOperator) -> Result<(), EmitError> {
        let (name, compares) = match operator {
            BinaryOperator::Add => ("op_Addition", false),
            BinaryOperator::Subtract => ("op_Subtraction", false),
            BinaryOperator::Multiply => ("op_Multiply", false),
            BinaryOperator::Divide => ("op_Division", false),
            BinaryOperator::Modulo => ("op_Modulus", false),
            BinaryOperator::Equality => ("op_Equality", true),
            BinaryOperator::Inequality => ("op_Inequality", true),
            BinaryOperator::LessThan => ("op_LessThan", true),
            BinaryOperator::GreaterThan => ("op_GreaterThan", true),
            BinaryOperator::LessThanOrEqual => ("op_LessThanOrEqual", true),
            BinaryOperator::GreaterThanOrEqual => ("op_GreaterThanOrEqual", true),
            other => {
                return Err(EmitError::new(format!(
                    "cannot emit `{other:?}` on decimals yet"
                )));
            }
        };
        let decimal = self.decimal_sig();
        let returns = if compares {
            SigType::Primitive(ElementType::Boolean)
        } else {
            decimal.clone()
        };
        let token = self.emitter.framework_member(
            "System.Decimal",
            name,
            false,
            &returns,
            &[decimal.clone(), decimal],
        );
        self.stream.call_effect(Instruction::Call(token), 2, 1);
        Ok(())
    }

    /// A number into a `decimal` or out of one: the implicit operator in,
    /// the explicit one out, both declared on `System.Decimal`.
    fn convert_number_from(&mut self, from: &Type, target: &Type) -> Result<(), EmitError> {
        let (from_decimal, to_decimal) = (self.is_decimal(from), self.is_decimal(target));
        // A native integer widens or narrows the way its source's sign says:
        // `uint` into `nint` zero-extends, `int` into `nuint` sign-extends,
        // and `nuint` into `long` zero-extends too.
        let native = |codegen: &Self, ty: &Type| {
            ty.symbol()
                .and_then(|symbol| codegen.emitter.primitive_of(symbol))
                .filter(|element| matches!(element, ElementType::I | ElementType::U))
        };
        // A pointer is an unsigned native integer, either way round:
        // `checked((void*)i)` of a negative `nint` throws.
        let pointer = |ty: &Type| matches!(ty, Type::Pointer(_) | Type::FunctionPointer(_));
        let (native_from, native_to) = (
            if pointer(from) {
                Some(ElementType::U)
            } else {
                native(self, from)
            },
            if pointer(target) {
                Some(ElementType::U)
            } else {
                native(self, target)
            },
        );
        if !from_decimal && !to_decimal && (native_from.is_some() || native_to.is_some()) {
            let source_unsigned = native_from == Some(ElementType::U)
                || matches!(
                    self.integer_special(from),
                    Some(
                        SpecialType::Byte
                            | SpecialType::UInt16
                            | SpecialType::Char
                            | SpecialType::UInt32
                            | SpecialType::UInt64
                    )
                );
            match (native_from, native_to) {
                // Inside `checked`, a native integer into one of the other
                // sign throws where the value does not fit.
                (Some(ElementType::U), Some(ElementType::I)) if self.checked => {
                    self.stream.emit(Instruction::ConvertOvfIUn);
                }
                (Some(ElementType::I), Some(ElementType::U)) if self.checked => {
                    self.stream.emit(Instruction::ConvertOvfU);
                }
                (Some(_), Some(_)) => {}
                (_, Some(to)) if self.checked => {
                    let floating = matches!(
                        self.integer_special(from),
                        Some(SpecialType::Single | SpecialType::Double)
                    );
                    self.stream.emit(match (to, source_unsigned && !floating) {
                        (ElementType::I, false) => Instruction::ConvertOvfI,
                        (ElementType::I, true) => Instruction::ConvertOvfIUn,
                        (_, false) => Instruction::ConvertOvfU,
                        (_, true) => Instruction::ConvertOvfUUn,
                    });
                }
                (_, Some(to)) => {
                    let floating = matches!(
                        self.integer_special(from),
                        Some(SpecialType::Single | SpecialType::Double)
                    );
                    let unsigned = if floating {
                        to == ElementType::U
                    } else {
                        source_unsigned
                    };
                    self.stream.emit(if unsigned {
                        Instruction::ConvertU
                    } else {
                        Instruction::ConvertI
                    });
                }
                // Inside `checked`, out of a native integer into a narrower
                // or differently signed one traps, by the source's sign: an
                // `nuint` past `long.MaxValue` is no `long`, where the
                // signed form read it as -1 and let it through.
                (Some(_), None)
                    if self.checked
                        && self.checked_conversion(target, source_unsigned).is_some() =>
                {
                    if let Some(instruction) = self.checked_conversion(target, source_unsigned) {
                        self.stream.emit(instruction);
                    }
                }
                (Some(_), None) => match self.integer_special(target) {
                    Some(SpecialType::Int64 | SpecialType::UInt64) if source_unsigned => {
                        self.stream.emit(Instruction::ConvertU8);
                    }
                    Some(SpecialType::Single | SpecialType::Double) if source_unsigned => {
                        self.stream.emit(Instruction::ConvertRUnsigned);
                        self.convert_number(target);
                    }
                    _ => self.convert_number(target),
                },
                (None, None) => unreachable!("one side is native"),
            }
            return Ok(());
        }
        if from_decimal == to_decimal {
            // A `uint` widens to a `long` by zero extension, and an unsigned
            // integer becomes a float through `conv.r.un`: `conv.i8` and
            // `conv.r8` alone would read the high bit as a sign.
            let source = self.integer_special(from);
            let destination = self.integer_special(target);
            // Inside `checked`, a conversion between integers, or from a
            // float to one, traps where the value does not fit.
            if self.checked
                && source != destination
                && let Some(instruction) = self.checked_conversion(
                    target,
                    matches!(source, Some(SpecialType::UInt32 | SpecialType::UInt64)),
                )
            {
                self.stream.emit(instruction);
                return Ok(());
            }
            match (source, destination) {
                (Some(SpecialType::UInt32), Some(SpecialType::Int64 | SpecialType::UInt64)) => {
                    self.stream.emit(Instruction::ConvertU8);
                    return Ok(());
                }
                (
                    Some(SpecialType::UInt32 | SpecialType::UInt64),
                    Some(SpecialType::Single | SpecialType::Double),
                ) => {
                    self.stream.emit(Instruction::ConvertRUnsigned);
                }
                _ => {}
            }
            self.convert_number(target);
            return Ok(());
        }
        let decimal = self.decimal_sig();
        // `Decimal` has an operator for each primitive by its own type, and
        // the narrow ones check the range: `(byte)300m` throws. An enum
        // converts as the integer underneath it.
        let primitive = |special: Option<SpecialType>| match special {
            Some(SpecialType::SByte) => Some(ElementType::I1),
            Some(SpecialType::Byte) => Some(ElementType::U1),
            Some(SpecialType::Int16) => Some(ElementType::I2),
            Some(SpecialType::UInt16) => Some(ElementType::U2),
            Some(SpecialType::Char) => Some(ElementType::Char),
            Some(SpecialType::Int32) => Some(ElementType::I4),
            Some(SpecialType::UInt32) => Some(ElementType::U4),
            Some(SpecialType::Int64) => Some(ElementType::I8),
            Some(SpecialType::UInt64) => Some(ElementType::U8),
            Some(SpecialType::Single) => Some(ElementType::R4),
            Some(SpecialType::Double) => Some(ElementType::R8),
            _ => None,
        };
        if to_decimal {
            // A native integer goes by way of the 64-bit one of its sign,
            // which `Decimal` has an operator from: an `nuint` zero-extended
            // and an `nint` sign-extended. Nothing at all was written for
            // one, and the call after it took a native integer for a
            // `decimal`.
            let element = match native_from {
                Some(ElementType::U) => {
                    self.stream.emit(Instruction::ConvertU8);
                    Some(ElementType::U8)
                }
                Some(_) => {
                    self.stream.emit(Instruction::ConvertI8);
                    Some(ElementType::I8)
                }
                None => primitive(self.integer_special(from)),
            };
            let Some(element) = element else {
                return Ok(());
            };
            // A float into a `decimal` is explicit, and so is its operator.
            let name = if matches!(element, ElementType::R4 | ElementType::R8) {
                "op_Explicit"
            } else {
                "op_Implicit"
            };
            let token = self.emitter.framework_member(
                "System.Decimal",
                name,
                false,
                &decimal,
                &[SigType::Primitive(element)],
            );
            self.stream.call_effect(Instruction::Call(token), 1, 1);
            return Ok(());
        }
        // Out of a `decimal` into a native integer the same way back: the
        // 64-bit one `Decimal` converts to, then narrowed — with a check
        // inside `checked`, where a 32-bit process has no room for it.
        let element = match native_to {
            Some(ElementType::U) => Some(ElementType::U8),
            Some(_) => Some(ElementType::I8),
            None => primitive(self.integer_special(target)),
        };
        let Some(element) = element else {
            return Ok(());
        };
        let token = self.emitter.framework_member(
            "System.Decimal",
            "op_Explicit",
            false,
            &SigType::Primitive(element),
            &[decimal],
        );
        self.stream.call_effect(Instruction::Call(token), 1, 1);
        match (native_to, self.checked) {
            (Some(ElementType::U), true) => self.stream.emit(Instruction::ConvertOvfUUn),
            (Some(ElementType::U), false) => self.stream.emit(Instruction::ConvertU),
            (Some(_), true) => self.stream.emit(Instruction::ConvertOvfI),
            (Some(_), false) => self.stream.emit(Instruction::ConvertI),
            (None, _) => {}
        }
        Ok(())
    }

    fn emit_pointer_arithmetic(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
    ) -> Result<(), EmitError> {
        match (&left.ty, &right.ty) {
            (Type::Pointer(element), Type::Pointer(_)) => {
                // Two pointers: the difference in bytes, divided by the size
                // of what they point at, as a `long`.
                self.emit_expression(left, true)?;
                self.emit_expression(right, true)?;
                self.stream.emit(Instruction::Subtract);
                self.scale_pointer_offset(element, false)?;
                self.stream.emit(Instruction::ConvertI8);
            }
            (Type::Pointer(element), _) => {
                // `p[i]` adds without a check even in a `checked` region, as
                // Roslyn does.
                let element_access = std::mem::take(&mut self.element_access);
                self.emit_expression(left, true)?;
                self.emit_expression(right, true)?;
                let signed = self.pointer_offset(&right.ty);
                let was = self.checked;
                if element_access {
                    self.checked = false;
                }
                self.scale_pointer_offset_checked(element, signed)?;
                self.emit_operator(operator, true, false);
                self.checked = was;
            }
            (_, Type::Pointer(element)) => {
                self.emit_expression(left, true)?;
                let signed = self.pointer_offset(&left.ty);
                self.scale_pointer_offset_checked(element, signed)?;
                self.emit_expression(right, true)?;
                self.emit_operator(operator, true, false);
            }
            _ => unreachable!("one side is a pointer"),
        }
        Ok(())
    }

    /// Widens an integer offset on the stack to a native one: a signed one
    /// is sign-extended and an unsigned one is not, so `p + 0x80000000u`
    /// moves forwards. Says whether the offset was signed.
    fn pointer_offset(&mut self, offset: &Type) -> bool {
        let signed = !matches!(
            self.emitter.special_type_of(offset),
            Some(
                SpecialType::Byte
                    | SpecialType::UInt16
                    | SpecialType::Char
                    | SpecialType::UInt32
                    | SpecialType::UInt64
            )
        );
        self.stream.emit(if signed {
            Instruction::ConvertI
        } else {
            Instruction::ConvertU
        });
        signed
    }

    /// Scales an offset by the element size, checking for overflow in a
    /// `checked` region the way the offset's signedness says.
    fn scale_pointer_offset_checked(
        &mut self,
        element: &Type,
        signed: bool,
    ) -> Result<(), EmitError> {
        if !self.checked {
            return self.scale_pointer_offset(element, true);
        }
        if matches!(
            self.emitter.special_type_of(element),
            Some(SpecialType::Byte | SpecialType::SByte | SpecialType::Boolean)
        ) {
            return Ok(());
        }
        let token = self.emitter.type_token(element)?;
        self.stream.emit(Instruction::SizeOf(token));
        self.stream.emit(if signed {
            Instruction::MultiplyOvf
        } else {
            Instruction::MultiplyOvfUn
        });
        Ok(())
    }

    /// Multiplies (or divides) the offset on the stack by the size of a
    /// pointer's element, unless that size is one.
    fn scale_pointer_offset(&mut self, element: &Type, multiply: bool) -> Result<(), EmitError> {
        if matches!(
            self.emitter.special_type_of(element),
            Some(SpecialType::Byte | SpecialType::SByte | SpecialType::Boolean)
        ) {
            return Ok(());
        }
        let token = self.emitter.type_token(element)?;
        self.stream.emit(Instruction::SizeOf(token));
        self.stream.emit(if multiply {
            Instruction::Multiply
        } else {
            Instruction::Divide
        });
        Ok(())
    }

    /// `stackalloc T[n]`: `n * sizeof(T)` bytes on the stack, filled with
    /// the elements written, as a `T*` — or as the `Span<T>` it was given to.
    fn emit_stackalloc(
        &mut self,
        element: &Type,
        count: &BoundExpression,
        elements: &[BoundExpression],
        span: Option<&Type>,
    ) -> Result<(), EmitError> {
        let count_slot = self.temporary(&count.ty)?;
        self.emit_expression(count, true)?;
        self.stream.emit(Instruction::StoreLocal(count_slot));
        self.stream.emit(Instruction::LoadLocal(count_slot));
        self.stream.emit(Instruction::ConvertU);
        self.scale_pointer_offset(element, true)?;
        self.stream.emit(Instruction::LocalAlloc);
        if !elements.is_empty() {
            let pointer = Type::Pointer(Box::new(element.clone()));
            let slot = self.temporary(&pointer)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            let kind = self.indirect_kind(element)?;
            for (index, value) in elements.iter().enumerate() {
                self.stream.emit(Instruction::LoadLocal(slot));
                if index > 0 {
                    self.stream.emit(Instruction::LoadInt32(index as i32));
                    self.stream.emit(Instruction::ConvertI);
                    self.scale_pointer_offset(element, true)?;
                    self.stream.emit(Instruction::Add);
                }
                self.emit_expression(value, true)?;
                self.stream.emit(Instruction::StoreIndirect(kind));
            }
            self.stream.emit(Instruction::LoadLocal(slot));
        }
        if let Some(span) = span {
            // `new Span<T>(void* pointer, int length)`.
            let constructor = self.emitter.member_of_type(
                span,
                ".ctor",
                &method_signature(
                    true,
                    &SigType::Primitive(ElementType::Void),
                    &[
                        SigType::Pointer(Box::new(SigType::Primitive(ElementType::Void))),
                        SigType::Primitive(ElementType::I4),
                    ],
                ),
            )?;
            self.stream.emit(Instruction::LoadLocal(count_slot));
            self.stream
                .call_effect(Instruction::NewObject(constructor), 2, 1);
        }
        Ok(())
    }

    /// `fixed (T* p = e) body`: what `e` names is pinned in a local the
    /// collector may not move the target of, `p` is that address, and the
    /// pin is released when the body is left.
    fn emit_fixed(
        &mut self,
        declarations: &[BoundStatement],
        body: &BoundStatement,
    ) -> Result<(), EmitError> {
        let mut pins = Vec::new();
        for declaration in declarations {
            let BoundStatementKind::LocalDeclaration {
                local,
                initializer: Some(value),
            } = &declaration.kind
            else {
                self.emit_statement(declaration)?;
                continue;
            };
            let pointer = self.local_types[local.0 as usize].clone();
            // What a `GetPinnableReference` is called on, kept where it can
            // be tested for null, is an ordinary local.
            let Type::Pointer(element) = &pointer else {
                self.emit_statement(declaration)?;
                continue;
            };
            let element_sig = self.emitter.sig_type(element)?;
            let pinned = self.locals.len() as u16;
            self.locals
                .push(SigType::Pinned(Box::new(SigType::ByRef(Box::new(
                    element_sig,
                )))));
            self.local_types.push(Type::Error);
            pins.push(pinned);

            let done = self.stream.label();
            let nothing = self.stream.label();
            self.emit_pin(value, element, pinned, nothing)?;
            self.begin_store(*local);
            self.stream.emit(Instruction::LoadLocal(pinned));
            self.stream.emit(Instruction::ConvertU);
            self.end_store(*local);
            self.stream.emit(Instruction::Branch(done));
            self.stream.mark(nothing);
            self.begin_store(*local);
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::ConvertU);
            self.end_store(*local);
            self.stream.mark(done);
        }
        self.emit_statement(body)?;
        // Unpinned on the way out: a null in the pinned local frees the
        // collector to move what it pointed at. A body that always returns
        // has no way out to unpin on.
        if self.stream.end_reachable() {
            for pinned in pins {
                self.stream.emit(Instruction::LoadInt32(0));
                self.stream.emit(Instruction::ConvertU);
                self.stream.emit(Instruction::StoreLocal(pinned));
            }
        }
        Ok(())
    }

    /// Pins what one `fixed` declaration names into `pinned`, branching to
    /// `nothing` where there is nothing to pin.
    fn emit_pin(
        &mut self,
        value: &BoundExpression,
        element: &Type,
        pinned: u16,
        nothing: Label,
    ) -> Result<(), EmitError> {
        // `GetPinnableReference()`, as the binder wrote it: the reference it
        // hands back is what is pinned. What it was called on is a local
        // where it could be null, and a null one pins nothing.
        if let BoundExpressionKind::Call {
            receiver,
            method,
            arguments,
            ..
        } = &value.kind
            && matches!(self.emitter.type_of(*method), Type::ByRef(_))
        {
            let subject =
                receiver
                    .as_deref()
                    .or(arguments.first())
                    .map(|subject| match &subject.kind {
                        BoundExpressionKind::RefArgument { operand, .. } => operand.as_ref(),
                        _ => subject,
                    });
            if let Some(subject) = subject
                && matches!(
                    subject.kind,
                    BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
                )
            {
                let symbols = self.emitter.compilation.symbols();
                let may_be_null = match &subject.ty {
                    Type::TypeParameter(symbol) => !symbols
                        .get(*symbol)
                        .as_type_parameter()
                        .is_some_and(|detail| detail.value_type),
                    other => !self.emitter.is_value_type(other),
                };
                if self.emitter.nullable_underlying(&subject.ty).is_some() {
                    let has_value = self.emitter.nullable_member(&subject.ty, "get_HasValue")?;
                    self.emit_reference(subject)?;
                    self.stream.call_effect(Instruction::Call(has_value), 1, 1);
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                } else if may_be_null {
                    self.emit_expression(subject, true)?;
                    self.box_if_needed(&subject.ty)?;
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                }
            }
            self.emit_reference(value)?;
            self.stream.emit(Instruction::StoreLocal(pinned));
            return Ok(());
        }
        {
            match &value.ty {
                // An array pins its first element, unless there is none.
                Type::Array { element, rank: 1 } => {
                    let held = self.temporary(&value.ty)?;
                    self.emit_expression(value, true)?;
                    self.stream.emit(Instruction::StoreLocal(held));
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream.emit(Instruction::LoadLength);
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream.emit(Instruction::LoadInt32(0));
                    let token = self.emitter.type_token(element)?;
                    self.stream.emit(Instruction::LoadElementAddress(token));
                    self.stream.emit(Instruction::StoreLocal(pinned));
                }
                // One with several dimensions pins `a[0, 0, …]`, reached
                // through its `Address`; its length is `System.Array`'s.
                Type::Array { element, rank } => {
                    let rank = *rank;
                    let held = self.temporary(&value.ty)?;
                    self.emit_expression(value, true)?;
                    self.stream.emit(Instruction::StoreLocal(held));
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                    self.stream.emit(Instruction::LoadLocal(held));
                    let int = SigType::Primitive(ElementType::I4);
                    let length = self.emitter.framework_member(
                        "System.Array",
                        "get_Length",
                        true,
                        &int,
                        &[],
                    );
                    self.stream
                        .call_effect(Instruction::CallVirtual(length), 1, 1);
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                    let address = self.array_member(value, ArrayMember::Address, element)?;
                    self.stream.emit(Instruction::LoadLocal(held));
                    for _ in 0..rank {
                        self.stream.emit(Instruction::LoadInt32(0));
                    }
                    self.stream
                        .call_effect(Instruction::Call(address), rank + 1, 1);
                    self.stream.emit(Instruction::StoreLocal(pinned));
                }
                // A string pins its first character, unless it is null.
                ty if self.is_string(ty) => {
                    let held = self.temporary(&value.ty)?;
                    self.emit_expression(value, true)?;
                    self.stream.emit(Instruction::StoreLocal(held));
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream.emit(Instruction::BranchIfFalse(nothing));
                    // `ref readonly char GetPinnableReference()`: a reference
                    // under a `modreq(InAttribute)`.
                    let modifier = self.emitter.references.type_ref_coded(
                        &mut self.emitter.metadata,
                        "System.Runtime.InteropServices.InAttribute",
                    );
                    let reference = self.emitter.framework_member(
                        "System.String",
                        "GetPinnableReference",
                        true,
                        &SigType::Required {
                            modifier,
                            inner: Box::new(SigType::ByRef(Box::new(SigType::Primitive(
                                ElementType::Char,
                            )))),
                        },
                        &[],
                    );
                    self.stream.emit(Instruction::LoadLocal(held));
                    self.stream
                        .call_effect(Instruction::CallVirtual(reference), 1, 1);
                    self.stream.emit(Instruction::StoreLocal(pinned));
                }
                // `&x` pins `x` itself.
                Type::Pointer(_) => match &value.kind {
                    BoundExpressionKind::AddressOf { operand } => {
                        self.emit_reference(operand)?;
                        self.stream.emit(Instruction::StoreLocal(pinned));
                    }
                    _ => {
                        self.emit_expression(value, true)?;
                        self.stream.emit(Instruction::StoreLocal(pinned));
                    }
                },
                // Anything else pins what its `GetPinnableReference` names
                // (C# 7.3 pattern-based `fixed`).
                other => {
                    // `ReadOnlySpan<T>` hands back a `ref readonly T`, which
                    // is a reference under a `modreq(InAttribute)`.
                    let read_only = other.symbol().is_some_and(|symbol| {
                        self.emitter
                            .compilation
                            .type_by_metadata_name("System.ReadOnlySpan`1")
                            == Some(symbol)
                    });
                    let mut returns = SigType::ByRef(Box::new(SigType::TypeParameter(0)));
                    if read_only {
                        let modifier = self.emitter.references.type_ref_coded(
                            &mut self.emitter.metadata,
                            "System.Runtime.InteropServices.InAttribute",
                        );
                        returns = SigType::Required {
                            modifier,
                            inner: Box::new(returns),
                        };
                    }
                    let reference = self.emitter.member_of_type(
                        other,
                        "GetPinnableReference",
                        &method_signature(true, &returns, &[]),
                    )?;
                    self.emit_receiver(value)?;
                    self.stream.call_effect(Instruction::Call(reference), 1, 1);
                    self.stream.emit(Instruction::StoreLocal(pinned));
                }
            }
        }
        let _ = element;
        Ok(())
    }

    /// `add`, `sub` or `mul`, or the overflow-checking form of it inside a
    /// `checked` region: `.ovf` for a signed integer, `.ovf.un` for an
    /// unsigned one. A float never traps.
    fn arithmetic(&self, operator: BinaryOperator, unsigned: bool, floating: bool) -> Instruction {
        match (operator, self.checked && !floating, unsigned) {
            (BinaryOperator::Add, false, _) => Instruction::Add,
            (BinaryOperator::Subtract, false, _) => Instruction::Subtract,
            (BinaryOperator::Multiply, false, _) => Instruction::Multiply,
            (BinaryOperator::Add, true, false) => Instruction::AddOvf,
            (BinaryOperator::Add, true, true) => Instruction::AddOvfUn,
            (BinaryOperator::Subtract, true, false) => Instruction::SubtractOvf,
            (BinaryOperator::Subtract, true, true) => Instruction::SubtractOvfUn,
            (BinaryOperator::Multiply, true, false) => Instruction::MultiplyOvf,
            (BinaryOperator::Multiply, true, true) => Instruction::MultiplyOvfUn,
            _ => Instruction::Add,
        }
    }

    /// `conv.ovf.*` into an integer type from a source that is signed or
    /// not, for a narrowing inside a `checked` region; `None` where the
    /// target is not an integer.
    fn checked_conversion(&self, target: &Type, from_unsigned: bool) -> Option<Instruction> {
        let special = self.integer_special(target)?;
        Some(match (special, from_unsigned) {
            (SpecialType::SByte, false) => Instruction::ConvertOvfI1,
            (SpecialType::SByte, true) => Instruction::ConvertOvfI1Un,
            (SpecialType::Byte, false) => Instruction::ConvertOvfU1,
            (SpecialType::Byte, true) => Instruction::ConvertOvfU1Un,
            (SpecialType::Int16, false) => Instruction::ConvertOvfI2,
            (SpecialType::Int16, true) => Instruction::ConvertOvfI2Un,
            (SpecialType::UInt16 | SpecialType::Char, false) => Instruction::ConvertOvfU2,
            (SpecialType::UInt16 | SpecialType::Char, true) => Instruction::ConvertOvfU2Un,
            (SpecialType::Int32, false) => Instruction::ConvertOvfI4,
            (SpecialType::Int32, true) => Instruction::ConvertOvfI4Un,
            (SpecialType::UInt32, false) => Instruction::ConvertOvfU4,
            (SpecialType::UInt32, true) => Instruction::ConvertOvfU4Un,
            (SpecialType::Int64, false) => Instruction::ConvertOvfI8,
            (SpecialType::Int64, true) => Instruction::ConvertOvfI8Un,
            (SpecialType::UInt64, false) => Instruction::ConvertOvfU8,
            (SpecialType::UInt64, true) => Instruction::ConvertOvfU8Un,
            _ => return None,
        })
    }

    /// The instruction an operator is, once both its operands are on the
    /// stack.
    fn emit_operator(&mut self, operator: BinaryOperator, unsigned: bool, floating: bool) {
        match operator {
            BinaryOperator::Add | BinaryOperator::Subtract | BinaryOperator::Multiply => {
                let instruction = self.arithmetic(operator, unsigned && !floating, floating);
                self.stream.emit(instruction);
            }
            BinaryOperator::Divide => self.stream.emit(if unsigned {
                Instruction::DivideUnsigned
            } else {
                Instruction::Divide
            }),
            BinaryOperator::Modulo => self.stream.emit(if unsigned {
                Instruction::RemainderUnsigned
            } else {
                Instruction::Remainder
            }),
            BinaryOperator::BitwiseAnd => self.stream.emit(Instruction::And),
            BinaryOperator::BitwiseOr => self.stream.emit(Instruction::Or),
            BinaryOperator::ExclusiveOr => self.stream.emit(Instruction::Xor),
            BinaryOperator::LeftShift => self.stream.emit(Instruction::ShiftLeft),
            BinaryOperator::RightShift => self.stream.emit(if unsigned {
                Instruction::ShiftRightUnsigned
            } else {
                Instruction::ShiftRight
            }),
            // `>>>` never carries the sign, whatever the left side's type is.
            BinaryOperator::UnsignedRightShift => {
                self.stream.emit(Instruction::ShiftRightUnsigned);
            }
            BinaryOperator::Equality => self.stream.emit(Instruction::CompareEqual),
            BinaryOperator::Inequality => {
                self.stream.emit(Instruction::CompareEqual);
                self.negate();
            }
            BinaryOperator::LessThan => self.stream.emit(less_than(unsigned)),
            BinaryOperator::GreaterThan => self.stream.emit(greater_than(unsigned)),
            // `a <= b` is `!(a > b)`, and with floating point the comparison
            // has to be the unordered one so that a NaN answers false both
            // ways round.
            BinaryOperator::LessThanOrEqual => {
                self.stream.emit(greater_than(unsigned || floating));
                self.negate();
            }
            BinaryOperator::GreaterThanOrEqual => {
                self.stream.emit(less_than(unsigned || floating));
                self.negate();
            }
            BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr | BinaryOperator::Coalesce => {
                unreachable!("handled above")
            }
        }
    }

    /// An operator on two `T?`s.
    ///
    /// The operands go into locals because each is read twice — once to ask
    /// whether it is there and once for the value — and a `T?` has no null to
    /// branch on the way a reference does. What a missing operand gives back
    /// depends on the operator: `null` for arithmetic, `false` for a
    /// comparison, and for `==` the answer that two nulls are equal.
    fn emit_lifted(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        result: &Type,
    ) -> Result<(), EmitError> {
        let left_slot = self.temporary(&left.ty)?;
        let right_slot = self.temporary(&right.ty)?;
        self.emit_expression(left, true)?;
        self.stream.emit(Instruction::StoreLocal(left_slot));
        self.emit_expression(right, true)?;
        self.stream.emit(Instruction::StoreLocal(right_slot));

        let left_has = self.emitter.nullable_member(&left.ty, "get_HasValue")?;
        let right_has = self.emitter.nullable_member(&right.ty, "get_HasValue")?;
        let left_value = self
            .emitter
            .nullable_member(&left.ty, "GetValueOrDefault")?;
        let right_value = self
            .emitter
            .nullable_member(&right.ty, "GetValueOrDefault")?;
        let inner = self
            .emitter
            .nullable_underlying(&left.ty)
            .unwrap_or_else(|| left.ty.clone());
        let unsigned = self.is_unsigned(&inner);
        let floating = matches!(
            self.emitter.special_type_of(&inner),
            Some(SpecialType::Single | SpecialType::Double)
        );

        let present = |codegen: &mut Self, slot, token| {
            codegen.stream.emit(Instruction::LoadLocalAddress(slot));
            codegen.stream.call_effect(Instruction::Call(token), 1, 1);
        };
        let end = self.stream.label();
        let missing = self.stream.label();

        // `x == y` on two `T?`s is true where both are null, which is the one
        // shape that cannot be written as "either missing, so no".
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) {
            // `ceq` answers for a number, a reference or an enum. A struct
            // with an `==` of its own is a call, and one without has no `==`
            // at all — neither is this.
            if !self.compares_with_ceq(&inner) {
                return Err(EmitError::new(format!(
                    "cannot compare two values of `{}` yet",
                    inner.display(self.emitter.compilation.symbols())
                )));
            }
            let neither = self.stream.label();
            present(self, left_slot, left_has);
            self.stream.emit(Instruction::BranchIfFalse(neither));
            present(self, right_slot, right_has);
            self.stream.emit(Instruction::BranchIfFalse(missing));
            present(self, left_slot, left_value);
            present(self, right_slot, right_value);
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::Branch(end));
            self.stream.mark(neither);
            present(self, right_slot, right_has);
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::Branch(end));
            self.stream.mark(missing);
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.mark(end);
            if operator == BinaryOperator::Inequality {
                self.negate();
            }
            return Ok(());
        }

        // `&` and `|` on `bool?` are three-valued (§12.13.5): `false & null`
        // is `false` and `true | null` is `true`, so an operand that decides
        // the answer on its own does so whatever the other one holds.
        if self.emitter.special_type_of(&inner) == Some(SpecialType::Boolean)
            && matches!(
                operator,
                BinaryOperator::BitwiseAnd | BinaryOperator::BitwiseOr
            )
        {
            let decisive = operator == BinaryOperator::BitwiseOr;
            let decided = self.stream.label();
            for (slot, has, value) in [
                (left_slot, left_has, left_value),
                (right_slot, right_has, right_value),
            ] {
                if decisive {
                    present(self, slot, value);
                    self.stream.emit(Instruction::BranchIfTrue(decided));
                } else {
                    let next = self.stream.label();
                    present(self, slot, value);
                    self.stream.emit(Instruction::BranchIfTrue(next));
                    present(self, slot, has);
                    self.stream.emit(Instruction::BranchIfTrue(decided));
                    self.stream.mark(next);
                }
            }
            let constructor = self.emitter.nullable_constructor(result)?;
            present(self, left_slot, left_has);
            present(self, right_slot, right_has);
            self.stream.emit(Instruction::And);
            self.stream.emit(Instruction::BranchIfFalse(missing));
            self.stream
                .emit(Instruction::LoadInt32(i32::from(!decisive)));
            self.stream
                .call_effect(Instruction::NewObject(constructor), 1, 1);
            self.stream.emit(Instruction::Branch(end));
            self.stream.mark(decided);
            self.stream
                .emit(Instruction::LoadInt32(i32::from(decisive)));
            self.stream
                .call_effect(Instruction::NewObject(constructor), 1, 1);
            self.stream.emit(Instruction::Branch(end));
            self.stream.mark(missing);
            self.emit_default(result)?;
            self.stream.mark(end);
            return Ok(());
        }

        present(self, left_slot, left_has);
        present(self, right_slot, right_has);
        self.stream.emit(Instruction::And);
        self.stream.emit(Instruction::BranchIfFalse(missing));
        present(self, left_slot, left_value);
        present(self, right_slot, right_value);
        if Self::is_shift(operator) {
            self.emit_shift_mask(&inner)?;
        }
        self.emit_operator(operator, unsigned, floating);
        if let Some(inner_result) = self.emitter.nullable_underlying(result) {
            self.narrow_enum_result(operator, &inner_result, false);
        }
        let comparison = matches!(
            operator,
            BinaryOperator::LessThan
                | BinaryOperator::GreaterThan
                | BinaryOperator::LessThanOrEqual
                | BinaryOperator::GreaterThanOrEqual
        );
        if !comparison {
            let constructor = self.emitter.nullable_constructor(result)?;
            self.stream
                .call_effect(Instruction::NewObject(constructor), 1, 1);
        }
        self.stream.emit(Instruction::Branch(end));
        self.stream.mark(missing);
        if comparison {
            self.stream.emit(Instruction::LoadInt32(0));
        } else {
            self.emit_default(result)?;
        }
        self.stream.mark(end);
        Ok(())
    }

    /// `+` and `==` on strings, which are calls rather than instructions.
    ///
    /// `==` compares the characters, and `+` on anything that is not already a
    /// string goes through the `object` overload, which calls `ToString` for
    /// each operand — including `null`, which becomes the empty string rather
    /// than throwing.
    fn emit_string_operator(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
    ) -> Result<(), EmitError> {
        let string = SigType::Primitive(ElementType::String);
        let object = SigType::Primitive(ElementType::Object);
        let boolean = SigType::Primitive(ElementType::Boolean);

        let both_strings = self.is_string(&left.ty) && self.is_string(&right.ty);
        let (name, return_type, operand) = match operator {
            BinaryOperator::Add if both_strings => ("Concat", string.clone(), string.clone()),
            BinaryOperator::Add => ("Concat", string, object),
            BinaryOperator::Equality | BinaryOperator::Inequality => {
                ("op_Equality", boolean, string)
            }
            _ => unreachable!("only these three reach here"),
        };
        let member = self.emitter.framework_member(
            "System.String",
            name,
            false,
            &return_type,
            &[operand.clone(), operand],
        );
        self.emit_expression(left, true)?;
        if !both_strings && operator == BinaryOperator::Add {
            self.box_if_needed(&left.ty)?;
        }
        self.emit_expression(right, true)?;
        if !both_strings && operator == BinaryOperator::Add {
            self.box_if_needed(&right.ty)?;
        }
        self.stream.call_effect(Instruction::Call(member), 2, 1);
        if operator == BinaryOperator::Inequality {
            self.negate();
        }
        Ok(())
    }

    fn is_string(&self, ty: &Type) -> bool {
        self.emitter.special_type_of(ty) == Some(SpecialType::String)
    }

    fn negate(&mut self) {
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream.emit(Instruction::CompareEqual);
    }

    /// Whether what was written here was the word `null`.
    ///
    /// The binder gives it the type the other side wanted, so by the time it
    /// reaches here a `null` compared against a `T?` is a `T?` holding
    /// nothing. What it was written as is the only thing left that says the
    /// comparison is a question about holding anything at all.
    fn written_null(&self, expression: &BoundExpression) -> bool {
        match &expression.kind {
            BoundExpressionKind::Conversion { operand, .. } => self.written_null(operand),
            BoundExpressionKind::Literal(ConstantValue::Null) => true,
            // `default(T?)` is the null of a `T?`, which is what a `null`
            // given to one is lowered to.
            // So is `default(T)` of a type parameter: `==` on a `T` and a
            // `null` has nothing else it can be, and `t == default(T)` is
            // only allowed where `T` is a reference type, whose default is
            // that null.
            BoundExpressionKind::Default(ty) => {
                self.emitter.nullable_underlying(ty).is_some()
                    || matches!(ty, Type::TypeParameter(_))
            }
            // `new T?()` holds nothing either.
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } => {
                arguments.is_empty()
                    && initializers.is_empty()
                    && self.emitter.nullable_underlying(&expression.ty).is_some()
            }
            _ => matches!(expression.ty, Type::Null),
        }
    }

    /// Whether `ceq` answers for two values of this type.
    ///
    /// A number, a `char`, a `bool`, an enum, a pointer and any reference
    /// compare that way; a struct does not, and `ceq` on one is refused.
    fn compares_with_ceq(&self, ty: &Type) -> bool {
        if self.emitter.special_type_of(ty).is_some()
            || matches!(ty, Type::Pointer(_) | Type::FunctionPointer(_))
        {
            return true;
        }
        let symbols = self.emitter.compilation.symbols();
        if ty.is_reference_type(symbols) || matches!(ty, Type::Array { .. } | Type::Null) {
            return true;
        }
        ty.symbol().is_some_and(|symbol| {
            symbols.get(symbol).type_kind() == Some(rustlyn_semantics::TypeKind::Enum)
        })
    }

    /// The primitive a number is compared as: its own special type, or an
    /// enum's underlying one. `None` for anything that is not a number.
    fn numeric_kind(&self, ty: &Type) -> Option<SpecialType> {
        let symbols = self.emitter.compilation.symbols();
        let ty = match ty.symbol() {
            Some(symbol) if symbols.get(symbol).type_kind() == Some(TypeKind::Enum) => {
                self.emitter.enum_underlying(symbol)
            }
            _ => ty.clone(),
        };
        self.emitter.special_type_of(&ty).filter(|special| {
            matches!(
                special,
                SpecialType::SByte
                    | SpecialType::Byte
                    | SpecialType::Int16
                    | SpecialType::UInt16
                    | SpecialType::Int32
                    | SpecialType::UInt32
                    | SpecialType::Int64
                    | SpecialType::UInt64
                    | SpecialType::Char
                    | SpecialType::Single
                    | SpecialType::Double
            )
        })
    }

    /// Brings the number on the stack to the width the comparison happens
    /// at: an `int` constant beside a `long` input is a `long`.
    fn widen_to(&mut self, kind: SpecialType) {
        let instruction = match kind {
            SpecialType::Int64 => Instruction::ConvertI8,
            SpecialType::UInt64 => Instruction::ConvertU8,
            SpecialType::Single => Instruction::ConvertR4,
            SpecialType::Double => Instruction::ConvertR8,
            _ => return,
        };
        self.stream.emit(instruction);
    }

    /// Whether a number of this type compares, divides and shifts right as
    /// an unsigned one: `clt.un`, `div.un`, `shr.un`.
    ///
    /// An `nuint` is one — `nuint.MaxValue > 1` read as signed is `-1 > 1` —
    /// and so is an enum over an unsigned type, whose members past the sign
    /// bit (`Flags.Top = 0x80000000`) are otherwise below every other.
    fn is_unsigned(&self, ty: &Type) -> bool {
        if matches!(ty, Type::Pointer(_) | Type::FunctionPointer(_)) {
            return true;
        }
        let symbols = self.emitter.compilation.symbols();
        let underlying = match ty.symbol() {
            Some(symbol) if symbols.get(symbol).type_kind() == Some(TypeKind::Enum) => {
                self.emitter.enum_underlying(symbol)
            }
            _ => ty.clone(),
        };
        if underlying
            .symbol()
            .is_some_and(|symbol| symbols.qualified_name(symbol).as_str() == "System.UIntPtr")
        {
            return true;
        }
        matches!(
            self.emitter.special_type_of(&underlying),
            Some(
                SpecialType::Byte
                    | SpecialType::UInt16
                    | SpecialType::UInt32
                    | SpecialType::UInt64
                    | SpecialType::Char
            )
        )
    }

    /// Whether an operator shifts.
    const fn is_shift(operator: BinaryOperator) -> bool {
        matches!(
            operator,
            BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::UnsignedRightShift
        )
    }

    /// Masks the shift count on the stack to the width of what is shifted
    /// (§12.11): the low five bits for an `int` or a `uint`, six for a
    /// `long` or a `ulong`, so `x << 33` on an `int` is `x << 1`. The
    /// instruction itself leaves a count as wide as the value or wider
    /// unspecified (§III.3.58): x64 happens to mask, and an interpreter or
    /// code translated ahead of time gives whatever its own shift gives.
    fn emit_shift_mask(&mut self, shifted: &Type) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let native = shifted.symbol().is_some_and(|symbol| {
            matches!(
                symbols.qualified_name(symbol).as_str(),
                "System.IntPtr" | "System.UIntPtr"
            )
        });
        if native {
            // As wide as the process: `sizeof(nint) * 8 - 1`, found there.
            let token = self.emitter.type_token(shifted)?;
            self.stream.emit(Instruction::SizeOf(token));
            self.stream.emit(Instruction::LoadInt32(8));
            self.stream.emit(Instruction::Multiply);
            self.stream.emit(Instruction::LoadInt32(1));
            self.stream.emit(Instruction::Subtract);
        } else {
            self.stream
                .emit(Instruction::LoadInt32(self.shift_mask(shifted)));
        }
        self.stream.emit(Instruction::And);
        Ok(())
    }

    /// The mask of a shift count where it is known here: 63 for a `long` or
    /// a `ulong`, 31 for everything narrower, each shifted as an `int`.
    fn shift_mask(&self, shifted: &Type) -> i32 {
        match self.emitter.special_type_of(shifted) {
            Some(SpecialType::Int64 | SpecialType::UInt64) => 63,
            _ => 31,
        }
    }

    /// The count of a shift of a `shifted`, masked: a constant count as the
    /// constant it comes to, as `csc` writes it, anything else with the mask
    /// after it.
    fn emit_shift_count(
        &mut self,
        count: &BoundExpression,
        shifted: &Type,
    ) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let native = shifted.symbol().is_some_and(|symbol| {
            matches!(
                symbols.qualified_name(symbol).as_str(),
                "System.IntPtr" | "System.UIntPtr"
            )
        });
        if let BoundExpressionKind::Literal(ConstantValue::Int32(value)) = count.kind
            && !native
        {
            self.stream
                .emit(Instruction::LoadInt32(value & self.shift_mask(shifted)));
            return Ok(());
        }
        self.emit_expression(count, true)?;
        self.emit_shift_mask(shifted)
    }

    // -- places ------------------------------------------------------------

    /// Works out where a target lives, evaluating whatever it needs exactly
    /// once into temporaries.
    pub(crate) fn place(&mut self, target: &BoundExpression) -> Result<Place, EmitError> {
        match &target.kind {
            // `*p = v` writes through the pointer, which waits in a slot so
            // that the value can be computed on top of it.
            BoundExpressionKind::Dereference { operand } => {
                let slot = self.temporary(&operand.ty)?;
                self.emit_expression(operand, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            // `GetValueRefOrNullRef(map, key) = v` writes through the
            // reference the call hands back, parked in a slot the same way;
            // so does `c[i] += v` on a `ref int this[int]`, whose getter is
            // called once, for the reference, and has no setter.
            BoundExpressionKind::Call { method: member, .. }
            | BoundExpressionKind::IndexerAccess {
                indexer: member, ..
            }
            | BoundExpressionKind::Property {
                property: member, ..
            } if matches!(self.emitter.type_of(*member), Type::ByRef(_)) => {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.emit_reference(target)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            // `(r = ref x) = v` writes to what `r` now refers to.
            BoundExpressionKind::Assignment {
                target: rebound,
                value,
            } if self.rebinds(rebound, value) => {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.emit_reference(target)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            // So does a call through a function pointer returning by
            // reference, and `__refvalue(r, T)`.
            BoundExpressionKind::RefValue(_) => {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.emit_reference(target)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            BoundExpressionKind::FunctionPointerCall { pointer, .. }
                if matches!(&pointer.ty, Type::FunctionPointer(signature)
                    if signature.returns_ref == RefKind::Ref) =>
            {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.emit_reference(target)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            // `r.F = v` on a `ref` field writes where the field points.
            BoundExpressionKind::Field {
                receiver: Some(_),
                field,
            } if self.is_ref_field(*field) => {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.emit_reference(target)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            // `(c ? ref a : ref b) = v` writes to whichever place was chosen,
            // through its address parked in a slot.
            BoundExpressionKind::Conditional {
                consequence,
                alternative,
                ..
            } if is_ref_branch(consequence) && is_ref_branch(alternative) => {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.emit_reference(target)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::IndirectLocal {
                    slot,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            // A captured variable is written where it is read: in the display
            // class, so that the lambda and the method see the same one.
            BoundExpressionKind::Local(local) if self.is_by_ref_local(*local) => {
                Ok(Place::IndirectLocal {
                    slot: self.slot(local),
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            BoundExpressionKind::Local(local) => Ok(match self.captured_local(*local) {
                Some(capture) => Place::Captured {
                    holder: capture.holder,
                    token: capture.token,
                },
                None => Place::Local(self.slot(local)),
            }),
            // `this += 1` in an `async` struct method writes the copy of
            // `this` its machine keeps, in `<>4__this`.
            BoundExpressionKind::This if let Some(capture) = self.captured_this() => {
                Ok(Place::Captured {
                    holder: capture.holder,
                    token: capture.token,
                })
            }
            // `this = default;` in a struct's constructor: inside a value
            // type `this` is a `T&` argument like any other reference, and
            // what it points at is what is written.
            BoundExpressionKind::This if self.instance && self.in_value_type => {
                Ok(Place::Indirect {
                    argument: 0,
                    kind: self.indirect_kind(&target.ty)?,
                })
            }
            BoundExpressionKind::Parameter(symbol) => Ok(match self.captured_parameter(*symbol) {
                Some(capture) => Place::Captured {
                    holder: capture.holder,
                    token: capture.token,
                },
                None if self.is_by_reference(*symbol) => Place::Indirect {
                    argument: self.argument_index(*symbol)?,
                    kind: self.indirect_kind(&target.ty)?,
                },
                None => Place::Argument(self.argument_index(*symbol)?),
            }),
            BoundExpressionKind::Field { receiver, field } => {
                let token =
                    self.field_token_on(*field, receiver.as_deref().map(|value| &value.ty))?;
                let owner = self.owner_reached(*field, receiver.as_deref().map(|value| &value.ty));
                let receiver = receiver.as_deref().filter(|value| !is_type_name(value));
                self.field_place(token, receiver, owner)
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                let array_slot = self.temporary(&array.ty)?;
                if indices.len() > 1 {
                    let get = self.array_member(array, ArrayMember::Get, &target.ty)?;
                    let set = self.array_member(array, ArrayMember::Set, &target.ty)?;
                    self.emit_expression(array, true)?;
                    self.stream.emit(Instruction::StoreLocal(array_slot));
                    let mut slots = Vec::with_capacity(indices.len());
                    for index in indices {
                        let slot = self.temporary(&self.int_type())?;
                        self.emit_expression(index, true)?;
                        self.convert_number(&self.int_type());
                        self.stream.emit(Instruction::StoreLocal(slot));
                        slots.push(slot);
                    }
                    return Ok(Place::MultiElement {
                        array: array_slot,
                        indices: slots,
                        get,
                        set,
                    });
                }
                let element = self.emitter.type_token(&target.ty)?;
                let index_slot = self.temporary(&self.int_type())?;
                self.emit_expression(array, true)?;
                self.stream.emit(Instruction::StoreLocal(array_slot));
                self.emit_single_index(indices)?;
                // The slot is an `int`, and a `long` index has been made a
                // native one: it is narrowed the rest of the way to fit.
                if let [index] = indices.as_slice()
                    && matches!(
                        self.emitter.special_type_of(&index.ty),
                        Some(SpecialType::Int64 | SpecialType::UInt64)
                    )
                {
                    self.stream.emit(Instruction::ConvertI4);
                }
                self.stream.emit(Instruction::StoreLocal(index_slot));
                Ok(Place::Element {
                    array: array_slot,
                    index: index_slot,
                    element,
                    element_type: target.ty.clone(),
                })
            }
            BoundExpressionKind::Property { receiver, property } => {
                // `public SourceText Text { get; }` written to in the
                // constructor: there is no setter to call, and there was never
                // meant to be one. The store goes to the field the property
                // reads, which is what the language means by it.
                if let Some(token) = self.backing_field_to_write(
                    *property,
                    receiver.as_ref().map(|receiver| &receiver.ty),
                )? {
                    let owner =
                        self.owner_reached(*property, receiver.as_deref().map(|value| &value.ty));
                    let receiver = receiver.as_deref().filter(|value| !is_type_name(value));
                    return self.field_place(token, receiver, owner);
                }
                let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
                let direct = receiver
                    .as_deref()
                    .is_some_and(|value| matches!(value.kind, BoundExpressionKind::Base));
                let extension = self.emitter.is_extension_property(*property);
                let receiver = match receiver.as_deref().filter(|value| !is_type_name(value)) {
                    Some(receiver) if extension => Some(self.value_receiver(receiver, *property)?),
                    Some(receiver) => Some(self.property_receiver(receiver)?),
                    None => None,
                };
                // An extension block's property is called as the static
                // method it is, with the receiver as its first argument.
                let extension_receiver = if extension {
                    receiver_type.clone()
                } else {
                    None
                };
                let receiver_type = if extension { None } else { receiver_type };
                let through = self.written_through(*property, &target.ty)?;
                Ok(Place::Property {
                    receiver,
                    arguments: Vec::new(),
                    by_address: Vec::new(),
                    property: *property,
                    receiver_type,
                    through,
                    direct,
                    extension_receiver,
                })
            }
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => {
                let extension = self.emitter.is_extension_property(*indexer);
                let held = if extension {
                    self.value_receiver(receiver, *indexer)?
                } else {
                    self.property_receiver(receiver)?
                };
                let outer = self.counted.take();
                if let Receiver::At(Address::HeldLocal(slot)) = &held
                    && self.generic_variable(receiver)
                {
                    self.counted = Some((receiver.kind.clone(), *slot));
                }
                let mut slots = Vec::with_capacity(arguments.len());
                let mut by_address = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    // An argument an `in` parameter takes is the variable
                    // itself, whose address a `ref` local keeps: the setter
                    // sees what is written to it meanwhile. Where an `await`
                    // may come between, no `ref` local survives it, and the
                    // value is kept instead and passed by its address.
                    // So does a `ref` one: `ia.P[ref x]` on a `[ComImport]`
                    // type, or the copy an omitted `ref` passes there.
                    if let BoundExpressionKind::RefArgument { kind, operand } = &argument.kind
                        && self.iterator.is_none()
                        && self.async_run.is_none()
                    {
                        let argument_slot =
                            self.temporary(&Type::ByRef(Box::new(operand.ty.clone())))?;
                        if *kind == rustlyn_semantics::RefKind::In {
                            self.emit_readonly_reference(operand)?;
                        } else {
                            self.emit_reference(operand)?;
                        }
                        self.stream.emit(Instruction::StoreLocal(argument_slot));
                        slots.push(argument_slot);
                        by_address.push(false);
                        continue;
                    }
                    let (value, address) = match &argument.kind {
                        BoundExpressionKind::RefArgument { operand, .. } => {
                            (operand.as_ref(), true)
                        }
                        _ => (argument, false),
                    };
                    let argument_slot = self.temporary(&value.ty)?;
                    self.emit_expression(value, true)?;
                    self.stream.emit(Instruction::StoreLocal(argument_slot));
                    slots.push(argument_slot);
                    by_address.push(address);
                }
                self.counted = outer;
                let through = self.written_through(*indexer, &target.ty)?;
                Ok(Place::Property {
                    receiver: Some(held),
                    arguments: slots,
                    by_address,
                    property: *indexer,
                    receiver_type: (!extension).then(|| receiver.ty.clone()),
                    through,
                    direct: matches!(receiver.kind, BoundExpressionKind::Base),
                    extension_receiver: extension.then(|| receiver.ty.clone()),
                })
            }
            // `t[Swap(ref t)..] = 42` through a `Slice` returning a
            // reference: the steps before the last run for what they do, and
            // the last is the variable.
            BoundExpressionKind::Sequence(steps) if !steps.is_empty() => {
                let (last, before) = steps.split_last().expect("not empty");
                for step in before {
                    self.emit_expression(step, false)?;
                }
                self.place(last)
            }
            other => Err(EmitError::new(format!(
                "this expression cannot be assigned to: {}{}",
                Self::describe_kind(other),
                self.at(target.span)
            ))),
        }
    }

    /// Where a field lives, given its token and whatever it hangs off.
    /// The type a member's declaring class has as seen from a receiver:
    /// `Usages<TState>` for `FromTop` reached through a `TUsages :
    /// Usages<TState>`, and the class itself where it is not generic.
    fn owner_reached(&self, member: SymbolId, receiver: Option<&Type>) -> Type {
        self.emitter.through(member, receiver).unwrap_or_else(|| {
            self.emitter
                .enclosing_type(member)
                .map_or(Type::Error, Type::named)
        })
    }

    fn field_place(
        &mut self,
        token: Token,
        receiver: Option<&BoundExpression>,
        owner: Type,
    ) -> Result<Place, EmitError> {
        // A field of a `T : class` is written on the boxed value, which is
        // the object itself at run time; the address of the `T` would be
        // the caller's slot. The boxed value is held as the class the field
        // belongs to, which a `T` constrained to it is once boxed, and which
        // is what the verifier wants under the `stfld`.
        if let Some(receiver) = receiver
            && matches!(receiver.ty, Type::TypeParameter(_))
        {
            let held = if owner.is_error() {
                self.emitter
                    .compilation
                    .special_type(SpecialType::Object)
                    .map_or(Type::Error, Type::named)
            } else {
                owner
            };
            let slot = self.temporary(&held)?;
            self.emit_expression(receiver, true)?;
            self.box_if_needed(&receiver.ty)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            return Ok(Place::Field {
                receiver: slot,
                token,
            });
        }
        if let Some(receiver) = receiver
            && self.emitter.is_value_type(&receiver.ty)
        {
            let address = match self.address_of(receiver)? {
                Some(address) => address,
                // `entries[i].bWidth = b` writes into the array itself, and
                // the element's address is not something that can be pushed
                // again for nothing: computing it twice would evaluate `i`
                // twice. So it is computed once into a `ref` local, which
                // pushing *is* free.
                None => {
                    let held = Type::ByRef(Box::new(receiver.ty.clone()));
                    let slot = self.temporary(&held)?;
                    self.emit_reference(receiver)?;
                    self.stream.emit(Instruction::StoreLocal(slot));
                    Address::HeldLocal(slot)
                }
            };
            return Ok(Place::ValueField { address, token });
        }
        match receiver {
            Some(receiver) => {
                let slot = self.temporary(&receiver.ty)?;
                self.emit_expression(receiver, true)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                Ok(Place::Field {
                    receiver: slot,
                    token,
                })
            }
            None => Ok(Place::StaticField(token)),
        }
    }

    /// The backing field of a property that has no setter, which is where a
    /// store to it has to go.
    ///
    /// C# allows `Text = text;` in a constructor of the declaring type for a
    /// `{ get; }` property, and means the field by it. Every other property
    /// answers `None` here and goes through its setter as usual.
    ///
    /// In a generic type the field is named through the construction the
    /// receiver has, as any field is: the definition's own token names a
    /// field of the open type, and a `stfld` through that from shared code
    /// does not land where the getter's `ldfld` reads.
    fn backing_field_to_write(
        &mut self,
        property: SymbolId,
        receiver: Option<&Type>,
    ) -> Result<Option<Token>, EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let Some(detail) = symbols.get(property).as_property() else {
            return Ok(None);
        };
        if detail.has_set || detail.has_init {
            return Ok(None);
        }
        if !self.emitter.fields.contains_key(&property) {
            return Ok(None);
        }
        if let Some(through) = self.emitter.through(property, receiver) {
            return self
                .emitter
                .member_of_constructed(property, &through)
                .map(Some);
        }
        if let Some(construction) = self
            .emitter
            .enclosing_type(property)
            .and_then(|container| self.emitter.own_construction(container))
        {
            return self
                .emitter
                .member_of_constructed(property, &construction)
                .map(Some);
        }
        Ok(self.emitter.fields.get(&property).copied())
    }

    /// Pushes whatever has to sit under the value a store consumes.
    fn push_place_prefix(&mut self, place: &Place) {
        match place {
            Place::Local(_) | Place::Argument(_) | Place::StaticField(_) => {}
            Place::Field { receiver, .. } => {
                self.stream.emit(Instruction::LoadLocal(*receiver));
            }
            Place::ValueField { address, .. } => self.push_address(address.clone()),
            Place::Captured { holder, .. } => self.push_holder(*holder),
            Place::Indirect { argument, .. } => {
                self.stream.emit(Instruction::LoadArgument(*argument));
            }
            Place::IndirectLocal { slot, .. } => {
                self.stream.emit(Instruction::LoadLocal(*slot));
            }
            Place::Element { array, index, .. } => {
                self.stream.emit(Instruction::LoadLocal(*array));
                self.stream.emit(Instruction::LoadLocal(*index));
            }
            Place::MultiElement { array, indices, .. } => {
                self.stream.emit(Instruction::LoadLocal(*array));
                for index in indices {
                    self.stream.emit(Instruction::LoadLocal(*index));
                }
            }
            Place::Property {
                receiver,
                arguments,
                by_address,
                receiver_type,
                property,
                through,
                extension_receiver,
                ..
            } => {
                self.push_property_receiver(receiver.as_ref(), receiver_type.as_ref());
                for (position, argument) in arguments.iter().enumerate() {
                    if by_address.get(position).copied().unwrap_or(false) {
                        self.stream.emit(Instruction::LoadLocalAddress(*argument));
                    } else {
                        self.stream.emit(Instruction::LoadLocal(*argument));
                    }
                }
                // Writing through a `ref` getter needs the reference first,
                // and the value goes on top of it.
                if through.is_some()
                    && let Ok(getter) = self.emitter.place_accessor(
                        *property,
                        receiver_type.as_ref(),
                        extension_receiver.as_ref(),
                        false,
                    )
                {
                    let pops = usize::from(receiver.is_some()) + arguments.len();
                    let instruction = match receiver_type {
                        Some(ty @ Type::TypeParameter(_)) => match self.emitter.type_token(ty) {
                            Ok(constraint) => {
                                self.stream.emit(Instruction::Constrained(constraint));
                                Instruction::CallVirtual(getter)
                            }
                            Err(_) => Instruction::Call(getter),
                        },
                        _ => Instruction::Call(getter),
                    };
                    self.stream.call_effect(instruction, pops, 1);
                }
            }
        }
    }

    /// Reads through what a `ref` getter handed back.
    ///
    /// `ref T this[int]` gives back where the value is; asking for the value
    /// is one step further.
    fn read_through_reference(
        &mut self,
        property: SymbolId,
        value: &Type,
    ) -> Result<(), EmitError> {
        if !matches!(self.emitter.type_of(property), Type::ByRef(_)) {
            return Ok(());
        }
        let kind = self.indirect_kind(value)?;
        self.stream.emit(Instruction::LoadIndirect(kind));
        Ok(())
    }

    /// How a write to this property goes through what its getter returns.
    ///
    /// `ref T this[int]` has no setter and does not need one: the getter
    /// hands back where the value lives, and writing there is the write.
    ///
    /// `value` is the property's type *as this access sees it*: `ref T
    /// this[int]` on a `SegmentedArray<char>` writes a `char`, and the
    /// declaration's `T` would name a type parameter the writer does not
    /// have.
    fn written_through(
        &mut self,
        property: SymbolId,
        value: &Type,
    ) -> Result<Option<IndirectKind>, EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let writable = symbols
            .get(property)
            .as_property()
            .is_some_and(|detail| detail.has_set || detail.has_init);
        if writable {
            return Ok(None);
        }
        let Type::ByRef(inner) = self.emitter.type_of(property) else {
            return Ok(None);
        };
        let kind = if value.is_error() {
            *inner
        } else {
            value.clone()
        };
        Ok(Some(self.indirect_kind(&kind)?))
    }

    /// Pushes a property's receiver: a struct's by address, so that a write
    /// reaches the thing itself rather than a copy of it.
    fn push_property_receiver(&mut self, receiver: Option<&Receiver>, ty: Option<&Type>) {
        match receiver {
            None => {}
            Some(Receiver::At(address)) => self.push_address(address.clone()),
            Some(Receiver::ValueAt(address, kind)) => {
                self.push_address(address.clone());
                self.stream.emit(Instruction::LoadIndirect(*kind));
            }
            Some(Receiver::This) => self.stream.emit(Instruction::LoadArgument(0)),
            Some(Receiver::Slot(slot)) => {
                // A `T` is called `constrained.`, which wants an address even
                // where `T` is a class.
                let by_address = ty.is_some_and(|ty| {
                    self.emitter.is_value_type(ty) || matches!(ty, Type::TypeParameter(_))
                });
                self.stream.emit(if by_address {
                    Instruction::LoadLocalAddress(*slot)
                } else {
                    Instruction::LoadLocal(*slot)
                });
            }
        }
    }

    /// Evaluates a property's receiver once, into wherever it can be reached
    /// from again.
    /// The receiver of an extension block's property, held as the value its
    /// accessors take as their first argument.
    fn value_receiver(
        &mut self,
        receiver: &BoundExpression,
        member: SymbolId,
    ) -> Result<Receiver, EmitError> {
        let parameter = self
            .emitter
            .compilation
            .symbols()
            .get(member)
            .as_property()
            .and_then(|detail| detail.parameters.first().copied());
        if self.emitter.is_by_reference(parameter) {
            return self.address_receiver(receiver);
        }
        let taken = parameter.map_or_else(|| receiver.ty.clone(), |p| self.emitter.type_of(p));
        // A variable that is not a reference is read again for each
        // accessor rather than copied once.
        let symbols = self.emitter.compilation.symbols();
        if !receiver.ty.is_reference_type(symbols)
            && !taken.is_reference_type(symbols)
            && (self.lives_somewhere(receiver)
                || matches!(
                    receiver.kind,
                    BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
                ))
        {
            let kind = self.indirect_kind(&receiver.ty)?;
            // A `T` that may be either is decided at run time, as Roslyn
            // does: a reference is copied once, a value read again.
            if let Type::TypeParameter(parameter) = receiver.ty
                && !self.is_a_struct_parameter(parameter)
            {
                let token = self.emitter.type_token(&receiver.ty)?;
                let probe = self.temporary(&receiver.ty)?;
                let copy = self.temporary(&receiver.ty)?;
                let held = self.temporary(&Type::ByRef(Box::new(receiver.ty.clone())))?;
                let value = self.stream.label();
                let done = self.stream.label();
                self.stream.emit(Instruction::LoadLocalAddress(probe));
                self.stream.emit(Instruction::InitObject(token));
                self.stream.emit(Instruction::LoadLocal(probe));
                self.stream.emit(Instruction::Box(token));
                self.stream.emit(Instruction::BranchIfTrue(value));
                self.emit_value_of(receiver)?;
                self.stream.emit(Instruction::StoreLocal(copy));
                self.stream.emit(Instruction::LoadLocalAddress(copy));
                self.stream.emit(Instruction::StoreLocal(held));
                self.stream.emit(Instruction::Branch(done));
                self.stream.mark(value);
                if let Receiver::At(address) = self.address_receiver(receiver)? {
                    self.push_address(address);
                } else {
                    self.stream.emit(Instruction::LoadLocalAddress(copy));
                }
                self.stream.emit(Instruction::StoreLocal(held));
                self.stream.mark(done);
                return Ok(Receiver::ValueAt(Address::HeldLocal(held), kind));
            }
            if let Receiver::At(address) = self.address_receiver(receiver)? {
                return Ok(Receiver::ValueAt(address, kind));
            }
        }
        let slot = self.temporary(&taken)?;
        self.emit_value_of(receiver)?;
        if !self.emitter.is_value_type(&taken) && self.emitter.is_value_type(&receiver.ty) {
            self.box_if_needed(&receiver.ty)?;
        }
        self.stream.emit(Instruction::StoreLocal(slot));
        Ok(Receiver::Slot(slot))
    }

    /// Where a receiver lives, for an accessor that takes it by reference:
    /// its own address where it has one, a slot's where it is a value.
    fn address_receiver(&mut self, receiver: &BoundExpression) -> Result<Receiver, EmitError> {
        if let Some(address) = self.address_of(receiver)? {
            return Ok(Receiver::At(address));
        }
        if self.lives_somewhere(receiver) {
            let held = Type::ByRef(Box::new(receiver.ty.clone()));
            let slot = self.temporary(&held)?;
            self.emit_reference(receiver)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            return Ok(Receiver::At(Address::HeldLocal(slot)));
        }
        let slot = self.temporary(&receiver.ty)?;
        self.emit_value_of(receiver)?;
        self.stream.emit(Instruction::StoreLocal(slot));
        Ok(Receiver::At(Address::Local(slot)))
    }

    /// A receiver as the value it is, the struct an initializer is filling
    /// included, which otherwise stands for its address.
    fn emit_value_of(&mut self, receiver: &BoundExpression) -> Result<(), EmitError> {
        if matches!(receiver.kind, BoundExpressionKind::CreatedObject)
            && let Some(Created::Local(slot)) = self.creating.last()
        {
            self.stream.emit(Instruction::LoadLocal(*slot));
            return Ok(());
        }
        self.emit_expression(receiver, true)?;
        Ok(())
    }

    /// Whether a receiver is a variable of a type parameter that may be a
    /// class.
    fn generic_variable(&self, receiver: &BoundExpression) -> bool {
        matches!(
            receiver.kind,
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
        ) && matches!(&receiver.ty, Type::TypeParameter(parameter)
            if !self.is_a_struct_parameter(*parameter))
    }

    /// The local holding the receiver kept for an indexer, where this is the
    /// `Length` or `Count` its `Index` counts back from.
    fn counted_through(&self, receiver: &BoundExpression, property: SymbolId) -> Option<u16> {
        let (variable, slot) = self.counted.as_ref()?;
        let same = match (&receiver.kind, variable) {
            (BoundExpressionKind::Local(a), BoundExpressionKind::Local(b)) => a == b,
            (BoundExpressionKind::Parameter(a), BoundExpressionKind::Parameter(b)) => a == b,
            _ => false,
        };
        let name = &self.emitter.compilation.symbols().get(property).name;
        (same && matches!(name.as_str(), "Length" | "Count")).then_some(*slot)
    }

    fn property_receiver(&mut self, receiver: &BoundExpression) -> Result<Receiver, EmitError> {
        // A `T` that may be either is a value where it is a struct and a
        // reference where it is a class, and which one is only known at run
        // time: `f.P += 1` on a class reads `f` once, and on a struct works
        // where `f` lives. The address is kept either way — of the value
        // itself, or of a copy of the reference — as `csc` does it.
        if let Type::TypeParameter(parameter) = &receiver.ty
            && !self.is_a_struct_parameter(*parameter)
            && (self.address_of(receiver)?.is_some() || self.lives_somewhere(receiver))
        {
            let ty = receiver.ty.clone();
            let token = self.emitter.type_token(&ty)?;
            let held = self.temporary(&Type::ByRef(Box::new(ty.clone())))?;
            let copy = self.temporary(&ty)?;
            let probe = self.temporary(&ty)?;
            match self.address_of(receiver)? {
                Some(address) => self.push_address(address),
                None => self.emit_reference(receiver)?,
            }
            let is_value = self.stream.label();
            self.stream.emit(Instruction::LoadLocalAddress(probe));
            self.stream.emit(Instruction::InitObject(token));
            self.stream.emit(Instruction::LoadLocal(probe));
            self.stream.emit(Instruction::Box(token));
            self.stream.emit(Instruction::BranchIfTrue(is_value));
            self.stream
                .emit(Instruction::LoadIndirect(IndirectKind::Object(token)));
            self.stream.emit(Instruction::StoreLocal(copy));
            self.stream.emit(Instruction::LoadLocalAddress(copy));
            self.stream.mark(is_value);
            self.stream.emit(Instruction::StoreLocal(held));
            return Ok(Receiver::At(Address::HeldLocal(held)));
        }
        if self.emitter.is_value_type(&receiver.ty) {
            if let Some(address) = self.address_of(receiver)? {
                return Ok(Receiver::At(address));
            }
            // The accessor of a value type is given an address, and it has to
            // be the address of where the value lives: a setter called on a
            // copy writes to the copy. `GreenNode.SlotCount` is one of these —
            // it sets a property of a struct field, and the node kept no
            // slots at all.
            if self.lives_somewhere(receiver) {
                let held = Type::ByRef(Box::new(receiver.ty.clone()));
                let slot = self.temporary(&held)?;
                self.emit_reference(receiver)?;
                self.stream.emit(Instruction::StoreLocal(slot));
                return Ok(Receiver::At(Address::HeldLocal(slot)));
            }
        }
        if matches!(
            receiver.kind,
            BoundExpressionKind::This | BoundExpressionKind::Base
        ) && self.captured_this().is_none()
        {
            return Ok(Receiver::This);
        }
        let slot = self.temporary(&receiver.ty)?;
        self.emit_expression(receiver, true)?;
        self.stream.emit(Instruction::StoreLocal(slot));
        Ok(Receiver::Slot(slot))
    }

    pub(crate) fn emit_place_load(&mut self, place: &Place) -> Result<(), EmitError> {
        match place {
            Place::Local(slot) => self.stream.emit(Instruction::LoadLocal(*slot)),
            Place::Argument(index) => self.stream.emit(Instruction::LoadArgument(*index)),
            Place::StaticField(token) => self.stream.emit(Instruction::LoadStaticField(*token)),
            Place::Field { receiver, token } => {
                self.stream.emit(Instruction::LoadLocal(*receiver));
                self.stream.emit(Instruction::LoadField(*token));
            }
            Place::ValueField { address, token } => {
                self.push_address(address.clone());
                self.stream.emit(Instruction::LoadField(*token));
            }
            Place::Captured { holder, token } => {
                self.push_holder(*holder);
                self.stream.emit(Instruction::LoadField(*token));
            }
            Place::Indirect { argument, kind } => {
                self.stream.emit(Instruction::LoadArgument(*argument));
                self.stream.emit(Instruction::LoadIndirect(*kind));
            }
            Place::IndirectLocal { slot, kind } => {
                self.stream.emit(Instruction::LoadLocal(*slot));
                self.stream.emit(Instruction::LoadIndirect(*kind));
            }
            Place::Element {
                array,
                index,
                element,
                element_type,
            } => {
                self.stream.emit(Instruction::LoadLocal(*array));
                self.stream.emit(Instruction::LoadLocal(*index));
                let element_type = element_type.clone();
                self.load_element(&element_type, *element);
            }
            Place::MultiElement {
                array,
                indices,
                get,
                ..
            } => {
                self.stream.emit(Instruction::LoadLocal(*array));
                for index in indices {
                    self.stream.emit(Instruction::LoadLocal(*index));
                }
                self.stream
                    .call_effect(Instruction::Call(*get), indices.len() + 1, 1);
            }
            Place::Property {
                receiver,
                arguments,
                property,
                receiver_type,
                through,
                direct,
                extension_receiver,
                ..
            } => {
                let getter = self.emitter.place_accessor(
                    *property,
                    receiver_type.as_ref(),
                    extension_receiver.as_ref(),
                    false,
                )?;
                let pops = usize::from(receiver.is_some()) + arguments.len();
                // `push_place_prefix` already calls the getter where the
                // property hands back a reference; reading is then one more
                // step through it.
                if let Some(kind) = through {
                    self.push_place_prefix(place);
                    self.stream.emit(Instruction::LoadIndirect(*kind));
                    return Ok(());
                }
                self.push_place_prefix(place);
                let instruction = match receiver_type {
                    // A static property of a generic type is named through
                    // its construction, and still has no `this` to dispatch on.
                    _ if receiver.is_none() => Instruction::Call(getter),
                    // A `T`'s accessor is reached through its address with a
                    // `constrained.` call: `node.Flag` on a `T : BoundNode`
                    // called on the address itself would hand the getter the
                    // caller's slot as `this`.
                    Some(ty @ Type::TypeParameter(_)) => {
                        let constraint = self.emitter.type_token(ty)?;
                        self.stream.emit(Instruction::Constrained(constraint));
                        Instruction::CallVirtual(getter)
                    }
                    Some(ty) if *direct || self.emitter.is_value_type(ty) => {
                        Instruction::Call(getter)
                    }
                    Some(_) => Instruction::CallVirtual(getter),
                    None => Instruction::Call(getter),
                };
                self.stream.call_effect(instruction, pops, 1);
            }
        }
        Ok(())
    }

    fn emit_place_store(&mut self, place: &Place) -> Result<(), EmitError> {
        match place {
            Place::Local(slot) => self.stream.emit(Instruction::StoreLocal(*slot)),
            Place::Argument(index) => self.stream.emit(Instruction::StoreArgument(*index)),
            Place::StaticField(token) => self.stream.emit(Instruction::StoreStaticField(*token)),
            Place::Field { token, .. }
            | Place::ValueField { token, .. }
            | Place::Captured { token, .. } => {
                self.stream.emit(Instruction::StoreField(*token));
            }
            Place::Indirect { kind, .. } | Place::IndirectLocal { kind, .. } => {
                self.stream.emit(Instruction::StoreIndirect(*kind));
            }
            Place::Element {
                element,
                element_type,
                ..
            } => {
                let element_type = element_type.clone();
                self.store_element(&element_type, *element);
            }
            // The array and the indices are already under the value.
            Place::MultiElement { indices, set, .. } => {
                self.stream
                    .call_effect(Instruction::Call(*set), indices.len() + 2, 0);
            }
            Place::Property {
                receiver,
                arguments,
                property,
                receiver_type,
                through,
                direct,
                extension_receiver,
                ..
            } => {
                if let Some(kind) = through {
                    self.stream.emit(Instruction::StoreIndirect(*kind));
                    return Ok(());
                }
                let setter = self.emitter.place_accessor(
                    *property,
                    receiver_type.as_ref(),
                    extension_receiver.as_ref(),
                    true,
                )?;
                // The receiver and the arguments are already on the stack,
                // under the value.
                let pops = usize::from(receiver.is_some()) + arguments.len() + 1;
                let instruction = match receiver_type {
                    // A static property of a generic type is named through
                    // its construction, and still has no `this` to dispatch on.
                    _ if receiver.is_none() => Instruction::Call(setter),
                    // As for a read: a `T`'s setter is a `constrained.` call
                    // on its address, never a call with the address as `this`.
                    Some(ty @ Type::TypeParameter(_)) => {
                        let constraint = self.emitter.type_token(ty)?;
                        self.stream.emit(Instruction::Constrained(constraint));
                        Instruction::CallVirtual(setter)
                    }
                    Some(ty) if *direct || self.emitter.is_value_type(ty) => {
                        Instruction::Call(setter)
                    }
                    Some(_) => Instruction::CallVirtual(setter),
                    None => Instruction::Call(setter),
                };
                self.stream.call_effect(instruction, pops, 0);
            }
        }
        Ok(())
    }

    /// Where in the source a span sits, as `: file(line,column): text`.
    ///
    /// An expression that could not be written is a question about one place
    /// in one file, and a message without the place is a question nobody can
    /// answer. It is empty rather than wrong when the member has no syntax.
    pub(crate) fn at(&self, span: rustlyn_text::TextSpan) -> String {
        let Some(owner) = self.owner else {
            return String::new();
        };
        let Some((tree, _)) = self.emitter.compilation.declaration_nodes(owner).first() else {
            return String::new();
        };
        let Some(tree) = self.emitter.compilation.trees().get(*tree) else {
            return String::new();
        };
        let source = tree.source();
        let Some(text) = source.get(span) else {
            return String::new();
        };
        let position = source.line_position(span.start());
        let mut text: String = text.chars().take(60).collect();
        if let Some(end) = text.find('\n') {
            text.truncate(end);
        }
        format!(
            ": {}({},{}): {text}",
            source.name(),
            position.line + 1,
            position.character + 1
        )
    }

    /// Whether a store to this place needs anything pushed before the value.
    /// Whether a place's prefix is parked values that can be pushed ahead
    /// of the value to store, rather than an address computed on the spot.
    const fn prefix_goes_first(place: &Place) -> bool {
        // A receiver read again for the setter is read after the value is
        // worked out, which a prefix pushed ahead of it would not be.
        Self::place_has_prefix(place)
            && !matches!(
                place,
                Place::ValueField { .. }
                    | Place::Property {
                        receiver: Some(Receiver::ValueAt(..)),
                        ..
                    }
            )
    }

    const fn place_has_prefix(place: &Place) -> bool {
        match place {
            Place::Local(_) | Place::Argument(_) | Place::StaticField(_) => false,
            Place::Field { .. }
            | Place::ValueField { .. }
            | Place::Element { .. }
            | Place::MultiElement { .. }
            | Place::Captured { .. }
            | Place::Indirect { .. }
            | Place::IndirectLocal { .. } => true,
            // A `ref` getter, static or not, is called for the reference the
            // value is written through.
            Place::Property {
                receiver,
                arguments,
                through,
                ..
            } => receiver.is_some() || !arguments.is_empty() || through.is_some(),
        }
    }

    fn emit_assignment(
        &mut self,
        target: &BoundExpression,
        value: &BoundExpression,
        used: bool,
    ) -> Result<(), EmitError> {
        // `d.X = v` and `d[i] = v` are the runtime binder's to do.
        if let BoundExpressionKind::Dynamic(dynamic) = &target.kind {
            return self.emit_dynamic_assignment(
                dynamic,
                crate::dynamic::Operand::Value(value),
                false,
                used,
            );
        }
        // `slot = ref other` gives the local a different reference to hold;
        // it does not write through the one it has. The `ref` on the right is
        // the only thing that says which of the two was written.
        // Its value, where it is used as one, is what the new reference
        // points at. A `ref` parameter is reassigned the same way.
        let rebound = match &target.kind {
            BoundExpressionKind::Local(local) if self.is_by_ref_local(*local) => {
                Some(Instruction::StoreLocal(local.0 as u16))
            }
            BoundExpressionKind::Parameter(symbol)
                if self.is_by_reference(*symbol) && self.captured_parameter(*symbol).is_none() =>
            {
                Some(Instruction::StoreArgument(self.argument_index(*symbol)?))
            }
            _ => None,
        };
        // `F = ref x` on a `ref` field stores the reference in the field.
        if let BoundExpressionKind::Field {
            receiver: Some(receiver),
            field,
        } = &target.kind
            && self.is_ref_field(*field)
            && matches!(value.kind, BoundExpressionKind::RefArgument { .. })
        {
            let token = self.field_token_on(*field, Some(&receiver.ty))?;
            self.emit_receiver(receiver)?;
            self.emit_expression(value, true)?;
            let slot = if used {
                let slot = self.temporary(&Type::ByRef(Box::new(target.ty.clone())))?;
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::StoreLocal(slot));
                Some(slot)
            } else {
                None
            };
            self.stream.emit(Instruction::StoreField(token));
            if let Some(slot) = slot {
                self.stream.emit(Instruction::LoadLocal(slot));
                let kind = self.indirect_kind(&target.ty)?;
                self.stream.emit(Instruction::LoadIndirect(kind));
            }
            return Ok(());
        }
        if let Some(store) = rebound
            && matches!(value.kind, BoundExpressionKind::RefArgument { .. })
        {
            self.emit_expression(value, true)?;
            if used {
                self.stream.emit(Instruction::Dup);
            }
            self.stream.emit(store);
            if used {
                let kind = self.indirect_kind(&target.ty)?;
                self.stream.emit(Instruction::LoadIndirect(kind));
            }
            return Ok(());
        }
        let place = self.place(target)?;
        if Self::prefix_goes_first(&place) {
            // The receiver was evaluated by `place`; what is pushed here is
            // that parked value, under the value to store, as Roslyn lays
            // it out: `ldarg.0; <value>; stfld`.
            self.push_place_prefix(&place);
            self.emit_expression(value, true)?;
            if used {
                let slot = self.temporary(&target.ty)?;
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::StoreLocal(slot));
                self.emit_place_store(&place)?;
                self.stream.emit(Instruction::LoadLocal(slot));
            } else {
                self.emit_place_store(&place)?;
            }
        } else if Self::place_has_prefix(&place) {
            // An address that is computed rather than parked is pushed once,
            // after the value, which waits in a temporary.
            let slot = self.temporary(&target.ty)?;
            self.emit_expression(value, true)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.push_place_prefix(&place);
            self.stream.emit(Instruction::LoadLocal(slot));
            self.emit_place_store(&place)?;
            if used {
                self.stream.emit(Instruction::LoadLocal(slot));
            }
        } else {
            self.emit_expression(value, true)?;
            if used {
                self.stream.emit(Instruction::Dup);
            }
            self.emit_place_store(&place)?;
        }
        Ok(())
    }

    fn emit_compound_assignment(
        &mut self,
        target: &BoundExpression,
        operator: BinaryOperator,
        value: &BoundExpression,
        ty: &Type,
        used: bool,
    ) -> Result<(), EmitError> {
        if operator != BinaryOperator::Coalesce
            && (matches!(target.kind, BoundExpressionKind::Dynamic(_))
                || matches!(target.ty, Type::Dynamic)
                || matches!(value.ty, Type::Dynamic))
        {
            return self.emit_dynamic_compound(
                target,
                crate::dynamic::Change::Binary(operator, value),
                used,
            );
        }
        if operator == BinaryOperator::Coalesce
            && let BoundExpressionKind::Dynamic(access) = &target.kind
        {
            return self.emit_dynamic_coalesce_assignment(access, value, used);
        }
        let place = self.place(target)?;
        // `x ??= y` evaluates and stores `y` only where `x` is null, so it is
        // a branch rather than an instruction.
        if operator == BinaryOperator::Coalesce {
            return self.emit_coalesce_assignment(&place, &target.ty, value, ty, used);
        }
        let slot = used.then(|| self.temporary(ty)).transpose()?;

        // `x.f += v;` as a statement: the receiver goes under the new value
        // from the start, so that no temporary holds the value.
        let ahead = !used && Self::prefix_goes_first(&place);
        if ahead {
            self.push_place_prefix(&place);
        }
        self.emit_place_load(&place)?;
        // `text += "!"`, and `cell += "!"` on an `object` cell, join strings
        // rather than add numbers: `String.Concat`, with anything that is not
        // a string boxed for it.
        if operator == BinaryOperator::Add
            && (self.is_string(&target.ty) || self.is_string(&value.ty))
        {
            let both_strings = self.is_string(&target.ty) && self.is_string(&value.ty);
            let string = SigType::Primitive(ElementType::String);
            let operand = if both_strings {
                string.clone()
            } else {
                SigType::Primitive(ElementType::Object)
            };
            if !both_strings {
                self.box_if_needed(&target.ty)?;
            }
            self.emit_expression(value, true)?;
            if !both_strings {
                self.box_if_needed(&value.ty)?;
            }
            let concat = self.emitter.framework_member(
                "System.String",
                "Concat",
                false,
                &string,
                &[operand.clone(), operand],
            );
            self.stream.call_effect(Instruction::Call(concat), 2, 1);
            if let Some(slot) = slot {
                self.stream.emit(Instruction::Dup);
                self.stream.emit(Instruction::StoreLocal(slot));
            }
            if ahead {
                self.emit_place_store(&place)?;
            } else {
                self.store_into(&place, ty)?;
            }
            if let Some(slot) = slot {
                self.stream.emit(Instruction::LoadLocal(slot));
            }
            return Ok(());
        }
        // `n += a` on an `int?` is lifted (§12.4.8): null where either side
        // is, and otherwise the operation on the values inside, wrapped again.
        if let Some(inner) = self.emitter.nullable_underlying(ty)
            && self.emitter.nullable_underlying(&target.ty).is_some()
        {
            self.emit_lifted_compound(operator, ty, &inner, value)?;
        } else {
            self.emit_expression(value, true)?;
            self.emit_compound_operation(operator, ty, &value.ty)?;
        }
        if let Some(slot) = slot {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::StoreLocal(slot));
        }
        if ahead {
            self.emit_place_store(&place)?;
        } else {
            self.store_into(&place, ty)?;
        }
        if let Some(slot) = slot {
            self.stream.emit(Instruction::LoadLocal(slot));
        }
        Ok(())
    }

    /// The lifted form of a compound assignment, with the current value of
    /// the `T?` place on the stack; leaves the new `T?` in its place.
    fn emit_lifted_compound(
        &mut self,
        operator: BinaryOperator,
        ty: &Type,
        inner: &Type,
        value: &BoundExpression,
    ) -> Result<(), EmitError> {
        let left_slot = self.temporary(ty)?;
        self.stream.emit(Instruction::StoreLocal(left_slot));
        let right_slot = self.temporary(&value.ty)?;
        self.emit_expression(value, true)?;
        self.stream.emit(Instruction::StoreLocal(right_slot));
        let right_inner = self.emitter.nullable_underlying(&value.ty);
        let (missing, end) = (self.stream.label(), self.stream.label());

        let has = self.emitter.nullable_member(ty, "get_HasValue")?;
        self.stream.emit(Instruction::LoadLocalAddress(left_slot));
        self.stream.call_effect(Instruction::Call(has), 1, 1);
        self.stream.emit(Instruction::BranchIfFalse(missing));
        if right_inner.is_some() {
            let has = self.emitter.nullable_member(&value.ty, "get_HasValue")?;
            self.stream.emit(Instruction::LoadLocalAddress(right_slot));
            self.stream.call_effect(Instruction::Call(has), 1, 1);
            self.stream.emit(Instruction::BranchIfFalse(missing));
        }
        let get = self.emitter.nullable_member(ty, "GetValueOrDefault")?;
        self.stream.emit(Instruction::LoadLocalAddress(left_slot));
        self.stream.call_effect(Instruction::Call(get), 1, 1);
        let right_type = match &right_inner {
            Some(right_inner) => {
                let get = self
                    .emitter
                    .nullable_member(&value.ty, "GetValueOrDefault")?;
                self.stream.emit(Instruction::LoadLocalAddress(right_slot));
                self.stream.call_effect(Instruction::Call(get), 1, 1);
                right_inner.clone()
            }
            None => {
                self.stream.emit(Instruction::LoadLocal(right_slot));
                value.ty.clone()
            }
        };
        self.emit_compound_operation(operator, inner, &right_type)?;
        let constructor = self.emitter.nullable_constructor(ty)?;
        self.stream
            .call_effect(Instruction::NewObject(constructor), 1, 1);
        self.stream.emit(Instruction::Branch(end));
        self.stream.mark(missing);
        self.emit_default(ty)?;
        self.stream.mark(end);
        Ok(())
    }

    /// The operation of a compound assignment on two values on the stack,
    /// giving a value of the target's type.
    fn emit_compound_operation(
        &mut self,
        operator: BinaryOperator,
        ty: &Type,
        right: &Type,
    ) -> Result<(), EmitError> {
        // `position += count` on a `long` and an `int`: the operation is a
        // `long` one, and the narrower operand is widened first (§12.4.7.3).
        // A shift keeps its count as the `int` it is.
        if !matches!(
            operator,
            BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::UnsignedRightShift
        ) && let (Some(wanted), Some(given)) = (self.numeric_kind(ty), self.numeric_kind(right))
            && wanted != given
        {
            // `sum += u` on a `long` and a `uint` zero-extends: the value
            // widened is the operand's, as it is signed or not.
            let unsigned = self.is_unsigned(right);
            match wanted {
                SpecialType::Int64 | SpecialType::UInt64 if unsigned => {
                    self.stream.emit(Instruction::ConvertU8);
                }
                SpecialType::Single | SpecialType::Double if unsigned => {
                    self.stream.emit(Instruction::ConvertRUnsigned);
                    self.widen_to(wanted);
                }
                _ => self.widen_to(wanted),
            }
        }
        self.emit_binary_instruction(operator, ty, right)?;
        self.narrow_small_result(ty);
        Ok(())
    }

    /// `s += 32000` on a `short` computes in `int` and stores back into
    /// sixteen bits, which the store truncates on its own — except inside
    /// `checked`, where the way back has to trap (§12.21.4).
    fn narrow_small_result(&mut self, ty: &Type) {
        if self.checked
            && matches!(
                self.integer_special(ty),
                Some(
                    SpecialType::SByte
                        | SpecialType::Byte
                        | SpecialType::Int16
                        | SpecialType::UInt16
                        | SpecialType::Char
                )
            )
        {
            self.convert_number(ty);
        }
    }

    /// `x ??= y`, which reads `x` once and writes only where it was null.
    ///
    /// The value ends up in a slot either way, because that is what the
    /// expression gives back when anything wants it, and because reading the
    /// place a second time would run whatever getting it costs twice.
    fn emit_coalesce_assignment(
        &mut self,
        place: &Place,
        place_type: &Type,
        value: &BoundExpression,
        ty: &Type,
        used: bool,
    ) -> Result<(), EmitError> {
        // What is stored is the variable's own type, and what the expression
        // gives back is the same: the binder converted the right-hand side
        // when it bound it.
        let underlying = self.emitter.nullable_underlying(place_type);
        // `flag ??= b` on a `bool?` is a `bool`, the value inside, while the
        // place and what is stored into it stay `bool?`: the result is kept
        // as the place's type and unwrapped once at the end.
        let unwrap = underlying.is_some() && ty != place_type;
        let result = self.temporary(place_type)?;
        let held = self.temporary(place_type)?;
        let (has, done) = (self.stream.label(), self.stream.label());

        self.emit_place_load(place)?;
        self.stream.emit(Instruction::StoreLocal(held));
        // A `T?` is null when it holds nothing, which is `HasValue` rather
        // than a comparison against zero.
        if underlying.is_some() {
            let has_value = self.emitter.nullable_member(place_type, "get_HasValue")?;
            self.stream.emit(Instruction::LoadLocalAddress(held));
            self.stream.call_effect(Instruction::Call(has_value), 1, 1);
        } else {
            self.stream.emit(Instruction::LoadLocal(held));
            // A `T` is tested boxed, as `??` tests it: `brtrue` on a struct
            // is not a program.
            if matches!(place_type, Type::TypeParameter(_)) {
                self.box_if_needed(place_type)?;
            }
        }
        self.stream.emit(Instruction::BranchIfTrue(has));

        self.emit_expression(value, true)?;
        self.stream.emit(Instruction::Dup);
        self.stream.emit(Instruction::StoreLocal(result));
        self.store_into(place, place_type)?;
        self.stream.emit(Instruction::Branch(done));

        self.stream.mark(has);
        self.stream.emit(Instruction::LoadLocal(held));
        self.stream.emit(Instruction::StoreLocal(result));

        self.stream.mark(done);
        if used {
            if unwrap {
                let value = self.emitter.nullable_member(place_type, "get_Value")?;
                self.stream.emit(Instruction::LoadLocalAddress(result));
                self.stream.call_effect(Instruction::Call(value), 1, 1);
            } else {
                self.stream.emit(Instruction::LoadLocal(result));
            }
        }
        Ok(())
    }

    /// Stores the value on top of the stack into a place.
    ///
    /// A place that needs something under the value — a receiver, an array and
    /// an index — has that pushed here rather than before the value was
    /// computed, because reading the place already pushed its own copy and a
    /// second one would be left behind. One stray slot per iteration is not a
    /// wrong answer but a stack that grows without bound, which is why this
    /// showed up as the emitter failing to terminate rather than as bad IL.
    pub(crate) fn store_into(&mut self, place: &Place, ty: &Type) -> Result<(), EmitError> {
        if Self::place_has_prefix(place) {
            let slot = self.temporary(ty)?;
            self.stream.emit(Instruction::StoreLocal(slot));
            self.push_place_prefix(place);
            self.stream.emit(Instruction::LoadLocal(slot));
        }
        self.emit_place_store(place)
    }

    /// The instruction for an operator whose operands are already on the stack.
    fn emit_binary_instruction(
        &mut self,
        operator: BinaryOperator,
        ty: &Type,
        right: &Type,
    ) -> Result<(), EmitError> {
        if self.is_decimal(ty) {
            return self.emit_decimal_operator(operator);
        }
        if self.emitter.special_type_of(ty) == Some(SpecialType::String) {
            let string = SigType::Primitive(ElementType::String);
            let concat = self.emitter.framework_member(
                "System.String",
                "Concat",
                false,
                &string.clone(),
                &[string.clone(), string],
            );
            self.stream.call_effect(Instruction::Call(concat), 2, 1);
            return Ok(());
        }
        // `handler += h` combines two delegates and `-=` takes one out of the
        // other (§12.10.5); both answer a `Delegate`, cast back to the type.
        let is_delegate = ty.symbol().is_some_and(|symbol| {
            self.emitter.compilation.symbols().get(symbol).type_kind() == Some(TypeKind::Delegate)
        });
        if is_delegate && matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract) {
            let coded = self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.Delegate");
            let delegate = SigType::Named {
                value_type: false,
                coded,
            };
            let name = if operator == BinaryOperator::Add {
                "Combine"
            } else {
                "Remove"
            };
            let combine = self.emitter.framework_member(
                "System.Delegate",
                name,
                false,
                &delegate,
                &[delegate.clone(), delegate.clone()],
            );
            self.stream.call_effect(Instruction::Call(combine), 2, 1);
            let token = self.emitter.type_token(ty)?;
            self.stream.emit(Instruction::CastClass(token));
            return Ok(());
        }
        // `p += n` moves by `n` elements.
        if let Type::Pointer(element) = ty
            && matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract)
        {
            let element = element.clone();
            self.stream.emit(Instruction::ConvertI);
            self.scale_pointer_offset(&element, true)?;
            self.stream.emit(if operator == BinaryOperator::Add {
                Instruction::Add
            } else {
                Instruction::Subtract
            });
            return Ok(());
        }
        let unsigned = self.is_unsigned(ty);
        let floating = matches!(
            self.emitter.special_type_of(ty),
            Some(SpecialType::Single | SpecialType::Double)
        );
        let instruction = match operator {
            BinaryOperator::Add | BinaryOperator::Subtract | BinaryOperator::Multiply => {
                self.arithmetic(operator, unsigned, floating)
            }
            BinaryOperator::Divide => {
                if unsigned {
                    Instruction::DivideUnsigned
                } else {
                    Instruction::Divide
                }
            }
            BinaryOperator::Modulo => {
                if unsigned {
                    Instruction::RemainderUnsigned
                } else {
                    Instruction::Remainder
                }
            }
            BinaryOperator::BitwiseAnd => Instruction::And,
            BinaryOperator::BitwiseOr => Instruction::Or,
            BinaryOperator::ExclusiveOr => Instruction::Xor,
            BinaryOperator::LeftShift => Instruction::ShiftLeft,
            BinaryOperator::RightShift => {
                if unsigned {
                    Instruction::ShiftRightUnsigned
                } else {
                    Instruction::ShiftRight
                }
            }
            BinaryOperator::UnsignedRightShift => Instruction::ShiftRightUnsigned,
            other => {
                return Err(EmitError::new(format!(
                    "cannot emit `{other:?}` as a compound assignment"
                )));
            }
        };
        let _ = right;
        if Self::is_shift(operator) {
            self.emit_shift_mask(ty)?;
        }
        self.stream.emit(instruction);
        Ok(())
    }

    fn emit_increment(
        &mut self,
        target: &BoundExpression,
        operator: IncrementOperator,
        prefix: bool,
        method: Option<SymbolId>,
        ty: &Type,
        used: bool,
    ) -> Result<(), EmitError> {
        if matches!(target.kind, BoundExpressionKind::Dynamic(_))
            || matches!(target.ty, Type::Dynamic)
        {
            let operator = match operator {
                IncrementOperator::Increment => rustlyn_semantics::DynamicUnary::Increment,
                IncrementOperator::Decrement => rustlyn_semantics::DynamicUnary::Decrement,
            };
            return self.emit_dynamic_compound(
                target,
                crate::dynamic::Change::Increment(operator, prefix),
                used,
            );
        }
        let place = self.place(target)?;
        let slot = used.then(|| self.temporary(ty)).transpose()?;

        // `x.f++;` as a statement: the receiver goes under the new value
        // from the start, so that no temporary holds the value.
        let ahead = !used && Self::prefix_goes_first(&place);
        if ahead {
            self.push_place_prefix(&place);
        }
        self.emit_place_load(&place)?;
        if let Some(slot) = slot
            && !prefix
        {
            // `x++` is worth the value from before the change.
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::StoreLocal(slot));
        }
        // `m++` on an `int?` steps the value inside where there is one and
        // leaves a null as it is (§12.4.8).
        match self.emitter.nullable_underlying(ty) {
            Some(inner) if method.is_none_or(|method| self.emitter.type_of(method) != *ty) => {
                let held = self.temporary(ty)?;
                self.stream.emit(Instruction::StoreLocal(held));
                let (missing, end) = (self.stream.label(), self.stream.label());
                let has = self.emitter.nullable_member(ty, "get_HasValue")?;
                self.stream.emit(Instruction::LoadLocalAddress(held));
                self.stream.call_effect(Instruction::Call(has), 1, 1);
                self.stream.emit(Instruction::BranchIfFalse(missing));
                let get = self.emitter.nullable_member(ty, "GetValueOrDefault")?;
                self.stream.emit(Instruction::LoadLocalAddress(held));
                self.stream.call_effect(Instruction::Call(get), 1, 1);
                self.emit_step(operator, method, &inner)?;
                let constructor = self.emitter.nullable_constructor(ty)?;
                self.stream
                    .call_effect(Instruction::NewObject(constructor), 1, 1);
                self.stream.emit(Instruction::Branch(end));
                self.stream.mark(missing);
                self.stream.emit(Instruction::LoadLocal(held));
                self.stream.mark(end);
            }
            _ => self.emit_step(operator, method, ty)?,
        }
        if let Some(slot) = slot
            && prefix
        {
            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::StoreLocal(slot));
        }
        if ahead {
            self.emit_place_store(&place)?;
        } else {
            self.store_into(&place, ty)?;
        }
        if let Some(slot) = slot {
            self.stream.emit(Instruction::LoadLocal(slot));
        }
        Ok(())
    }

    /// The step of `++` or `--` on the value on the stack, of type `ty`.
    fn emit_step(
        &mut self,
        operator: IncrementOperator,
        method: Option<SymbolId>,
        ty: &Type,
    ) -> Result<(), EmitError> {
        // A `decimal` and a type with its own `++` step through an operator
        // method, as `csc` calls `decimal.op_Increment`.
        let name = match operator {
            IncrementOperator::Increment => "op_Increment",
            IncrementOperator::Decrement => "op_Decrement",
        };
        if let Some(method) = method {
            let token = self.method_token_on(method, None)?;
            self.stream.call_effect(Instruction::Call(token), 1, 1);
            // `A operator ++(A)` declared on a base gives back what it
            // gives, and that is converted to the variable's type on the
            // way in, through an operator of its own where it takes one.
            let gives = self.emitter.type_of(method);
            if gives != *ty {
                match self.emitter.binder.implicit_operator(&gives, ty) {
                    Some(operator) => {
                        let token = self.method_token_on(operator, None)?;
                        self.stream.call_effect(Instruction::Call(token), 1, 1);
                    }
                    None => self.emit_value_conversion(&gives, ty)?,
                }
            }
        } else if self.is_decimal(ty) {
            let decimal = self.decimal_sig();
            let token = self.emitter.framework_member(
                "System.Decimal",
                name,
                false,
                &decimal,
                std::slice::from_ref(&decimal),
            );
            self.stream.call_effect(Instruction::Call(token), 1, 1);
        } else {
            self.emit_one(ty);
            let unsigned = self.is_unsigned(ty);
            let floating = matches!(
                self.emitter.special_type_of(ty),
                Some(SpecialType::Single | SpecialType::Double)
            );
            let instruction = self.arithmetic(
                match operator {
                    IncrementOperator::Increment => BinaryOperator::Add,
                    IncrementOperator::Decrement => BinaryOperator::Subtract,
                },
                unsigned,
                floating,
            );
            self.stream.emit(instruction);
            self.narrow_small_result(ty);
        }
        Ok(())
    }

    /// Whether a type declares type parameters beyond the ones it inherits
    /// from the type it is nested in.
    fn declares_own_parameters(&self, symbol: SymbolId) -> bool {
        let symbols = self.emitter.compilation.symbols();
        let count = |symbol: Option<SymbolId>| {
            symbol
                .and_then(|symbol| symbols.get(symbol).as_named_type())
                .map_or(0, |detail| detail.type_parameters.len())
        };
        count(Some(symbol)) > count(symbols.get(symbol).container)
    }

    /// The `1` that `++` adds, in the width the operand has.
    fn emit_one(&mut self, ty: &Type) {
        // `p++` moves by one element.
        if let Type::Pointer(element) = ty {
            match self.emitter.type_token(element) {
                Ok(token)
                    if !matches!(
                        self.emitter.special_type_of(element),
                        Some(SpecialType::Byte | SpecialType::SByte | SpecialType::Boolean)
                    ) =>
                {
                    self.stream.emit(Instruction::SizeOf(token));
                }
                _ => self.stream.emit(Instruction::LoadInt32(1)),
            }
            return;
        }
        match self.emitter.special_type_of(ty) {
            Some(SpecialType::Int64 | SpecialType::UInt64) => {
                self.stream.emit(Instruction::LoadInt64(1));
            }
            Some(SpecialType::Single) => self.stream.emit(Instruction::LoadFloat32(1.0)),
            Some(SpecialType::Double) => self.stream.emit(Instruction::LoadFloat64(1.0)),
            _ => self.stream.emit(Instruction::LoadInt32(1)),
        }
    }

    // -- helpers -----------------------------------------------------------

    /// Whether a local's slot holds an address rather than a value.
    fn is_by_ref_local(&self, local: rustlyn_semantics::LocalId) -> bool {
        self.by_ref_locals
            .get(local.0 as usize)
            .copied()
            .unwrap_or(false)
    }

    /// The slot a declared local lives in: its number, past the slots of
    /// whatever body this one's locals were added to — a field
    /// initializer's are emitted inside a constructor that has its own.
    fn slot(&self, local: impl std::borrow::Borrow<rustlyn_semantics::LocalId>) -> u16 {
        self.local_base + local.borrow().0 as u16
    }

    pub(crate) fn temporary(&mut self, ty: &Type) -> Result<u16, EmitError> {
        let signature = self.emitter.sig_type(ty)?;
        self.locals.push(signature);
        self.local_types.push(ty.clone());
        Ok((self.locals.len() - 1) as u16)
    }

    fn int_type(&self) -> Type {
        self.emitter
            .compilation
            .special_type(SpecialType::Int32)
            .map_or(Type::Error, Type::named)
    }

    /// The body of the `<Main>` around an `async Main`: call it, then wait
    /// on the task the way Roslyn does — `GetAwaiter().GetResult()` — and
    /// give back the result, where there is one.
    fn emit_async_main(&mut self, main: SymbolId) -> Result<(), EmitError> {
        let span = TextSpan::new(0, 0);
        let symbols = self.emitter.compilation.symbols();
        let parameters = symbols
            .get(main)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .ok_or_else(|| EmitError::new("`Main` is not a method"))?;
        let arguments: Vec<BoundExpression> = parameters
            .iter()
            .map(|parameter| {
                BoundExpression::new(
                    BoundExpressionKind::Parameter(*parameter),
                    self.emitter.type_of(*parameter),
                    span,
                )
            })
            .collect();
        let task_type = self.emitter.type_of(main);
        let call = |receiver: Option<BoundExpression>, method: SymbolId, arguments, ty: Type| {
            BoundExpression::new(
                BoundExpressionKind::Call {
                    receiver: receiver.map(Box::new),
                    method,
                    type_arguments: Vec::new(),
                    arguments,
                    virtual_call: false,
                },
                ty,
                span,
            )
        };
        let task = call(None, main, arguments, task_type.clone());
        let own = task_type
            .symbol()
            .and_then(|task| symbols.lookup(task, "GetAwaiter").first().copied());
        // A task with no `GetAwaiter` of its own is waited on through an
        // extension method that takes it (§7.1 awaits it like any `await`).
        let awaiter = match own {
            Some(get_awaiter) => {
                let awaiter_type = self.emitter.member_type(get_awaiter, &task_type);
                call(Some(task), get_awaiter, Vec::new(), awaiter_type)
            }
            None => {
                let extension = symbols
                    .iter()
                    .filter(|symbol| symbol.name == "GetAwaiter")
                    .map(|symbol| symbol.id)
                    .find(|method| {
                        self.emitter.is_extension_method_symbol(*method)
                            && symbols
                                .get(*method)
                                .as_method()
                                .and_then(|detail| detail.parameters.first())
                                .is_some_and(|this| self.emitter.type_of(*this) == task_type)
                    })
                    .ok_or_else(|| EmitError::new("the task `Main` returns has no `GetAwaiter`"))?;
                let awaiter_type = self.emitter.type_of(extension);
                call(None, extension, vec![task], awaiter_type)
            }
        };
        let awaiter_type = awaiter.ty.clone();
        let get_result = awaiter_type
            .symbol()
            .and_then(|awaiter| symbols.lookup(awaiter, "GetResult").first().copied())
            .ok_or_else(|| EmitError::new("the awaiter of `Main`'s task has no `GetResult`"))?;
        let result_type = self.emitter.member_type(get_result, &awaiter_type);
        let result = call(Some(awaiter), get_result, Vec::new(), result_type.clone());
        let statement = if matches!(result_type, Type::Void) {
            BoundStatementKind::Expression(result)
        } else {
            BoundStatementKind::Return(Some(result))
        };
        self.emit_statement(&BoundStatement::new(statement, span))
    }

    /// `x.E += h` through the event's accessor: the receiver, the handler,
    /// and a call to `add_E` or `remove_E`, which gives nothing back.
    fn emit_event_assignment(
        &mut self,
        receiver: Option<&BoundExpression>,
        event: SymbolId,
        add: bool,
        handler: &BoundExpression,
    ) -> Result<(), EmitError> {
        let receiver_type = receiver.map(|receiver| receiver.ty.clone());
        let is_static = self
            .emitter
            .compilation
            .symbols()
            .get(event)
            .modifiers
            .contains(Modifiers::STATIC);
        // `I2<string, string>.E += h` names the construction the static
        // event is on, and there is nothing to load for that.
        if let Some(receiver) = receiver.filter(|_| !is_static) {
            // A struct's accessor is called on the struct where it lives.
            if self.emitter.is_value_type(&receiver.ty)
                && !matches!(receiver.ty, Type::TypeParameter(_))
            {
                self.emit_member_receiver(receiver, event)?;
            } else {
                self.emit_expression(receiver, true)?;
            }
        }
        self.emit_expression(handler, true)?;
        let (accessor, instance) = {
            let symbols = self.emitter.compilation.symbols();
            let instance = !symbols.get(event).modifiers.contains(Modifiers::STATIC);
            let declared = symbols
                .get(event)
                .as_event()
                .and_then(|detail| if add { detail.adder } else { detail.remover });
            (declared, instance)
        };
        let token = match accessor {
            // An event out of metadata has accessor methods of its own.
            Some(accessor) => self.method_token_on(accessor, receiver_type.as_ref())?,
            // A source event's accessors were synthesized beside its field.
            None => self.emitter.event_accessor(event, add).ok_or_else(|| {
                EmitError::new(format!(
                    "the event `{}` has no `{}` accessor to call",
                    self.emitter.compilation.symbols().qualified_name(event),
                    if add { "add" } else { "remove" }
                ))
            })?,
        };
        let instruction = if instance {
            Instruction::CallVirtual(token)
        } else {
            Instruction::Call(token)
        };
        self.stream
            .call_effect(instruction, usize::from(instance) + 1, 0);
        Ok(())
    }

    /// `(a, b, …)`: the values in order and the `ValueTuple` constructor.
    /// Past seven the rest is a tuple of its own in the eighth slot, made
    /// first the same way (§8.3.11).
    fn emit_tuple_creation(
        &mut self,
        values: &[BoundExpression],
        ty: &Type,
    ) -> Result<(), EmitError> {
        if values.len() > 7 {
            for value in &values[..7] {
                self.emit_expression(value, true)?;
            }
            let rest_type = match ty {
                Type::Tuple(elements) if elements.len() == values.len() => {
                    Type::Tuple(elements[7..].to_vec())
                }
                // A `ValueTuple<…, TRest>` read as one: its eighth argument
                // is the rest.
                Type::Named { type_arguments, .. } if type_arguments.len() == 8 => {
                    type_arguments[7].clone()
                }
                _ => {
                    return Err(EmitError::new("a long tuple whose type is not a tuple"));
                }
            };
            self.emit_tuple_creation(&values[7..], &rest_type)?;
            let token = self.emitter.tuple_constructor(ty)?;
            self.stream.call_effect(Instruction::NewObject(token), 8, 1);
            return Ok(());
        }
        for value in values {
            self.emit_expression(value, true)?;
        }
        let token = self.emitter.tuple_constructor(ty)?;
        self.stream
            .call_effect(Instruction::NewObject(token), values.len(), 1);
        Ok(())
    }

    /// The body of `add_E` or `remove_E` on a field-like event (§15.8.2):
    /// `E = (D)Delegate.Combine(E, value)`, or `Delegate.Remove`.
    fn emit_event_accessor(&mut self, event: SymbolId, add: bool) -> Result<(), EmitError> {
        let (is_static, self_type) = {
            let symbols = self.emitter.compilation.symbols();
            let symbol = symbols.get(event);
            let is_static = symbol.modifiers.contains(Modifiers::STATIC);
            // Inside a generic class the field is reached through the
            // class's own construction, as `this.E` in its source would be.
            let self_type = symbol.container.map(|container| Type::Named {
                symbol: container,
                type_arguments: symbols
                    .get(container)
                    .as_named_type()
                    .map(|detail| {
                        detail
                            .type_parameters
                            .iter()
                            .map(|parameter| Type::TypeParameter(*parameter))
                            .collect()
                    })
                    .unwrap_or_default(),
            });
            (is_static, self_type)
        };
        let delegate_type = self.emitter.type_of(event);
        let field = self.field_token_on(event, self_type.as_ref())?;
        let combine = {
            let symbols = self.emitter.compilation.symbols();
            let name = if add { "Combine" } else { "Remove" };
            self.emitter
                .compilation
                .type_by_metadata_name("System.Delegate")
                .and_then(|delegate| {
                    symbols
                        .lookup(delegate, name)
                        .iter()
                        .copied()
                        .find(|candidate| {
                            symbols.get(*candidate).as_method().is_some_and(|detail| {
                                detail.parameters.len() == 2
                                    && !symbols
                                        .get(detail.parameters[0])
                                        .as_parameter()
                                        .is_some_and(|parameter| parameter.is_params)
                            })
                        })
                })
                .ok_or_else(|| {
                    EmitError::new(format!("`System.Delegate.{name}` is not available"))
                })?
        };
        let combine = self.method_token_on(combine, None)?;
        let delegate_token = self.emitter.type_token(&delegate_type)?;
        if is_static {
            self.stream.emit(Instruction::LoadStaticField(field));
            self.stream.emit(Instruction::LoadArgument(0));
        } else {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(field));
            self.stream.emit(Instruction::LoadArgument(1));
        }
        self.stream.call_effect(Instruction::Call(combine), 2, 1);
        self.stream.emit(Instruction::CastClass(delegate_token));
        if is_static {
            self.stream.emit(Instruction::StoreStaticField(field));
        } else {
            self.stream.emit(Instruction::StoreField(field));
        }
        Ok(())
    }

    pub(crate) fn argument_index(&self, parameter: SymbolId) -> Result<u16, EmitError> {
        let position = self
            .parameters
            .iter()
            .position(|plan| plan.symbol == Some(parameter))
            .ok_or_else(|| {
                let symbols = self.emitter.compilation.symbols();
                EmitError::new(format!(
                    "`{}` (a parameter of `{}`) is not a parameter of the method being emitted \
                     (in `{}`, whose parameters are {:?})",
                    symbols.get(parameter).name,
                    symbols
                        .get(parameter)
                        .container
                        .map_or_else(String::new, |it| symbols.qualified_name(it)),
                    self.owner
                        .map_or_else(String::new, |it| symbols.qualified_name(it)),
                    self.parameters
                        .iter()
                        .map(|it| it.name.clone())
                        .collect::<Vec<_>>()
                ))
            })?;
        Ok((position + usize::from(self.instance)) as u16)
    }

    /// The construction a static call to a generic type's member is on.
    ///
    /// `SyntaxList<GreenNode>.op_Implicit(builder)` has no receiver: a static
    /// member has nothing to be called on, so the construction is nowhere in
    /// the bound tree. It is in the call, though — the operator is declared
    /// on `SyntaxList<TNode>` and gives back one, and this call gives back a
    /// `SyntaxList<GreenNode>` — so the types going in and the type coming
    /// out are asked which construction of the container they are.
    fn static_container(
        &self,
        method: SymbolId,
        arguments: &[BoundExpression],
        result: &Type,
    ) -> Option<Type> {
        let symbols = self.emitter.compilation.symbols();
        let container = symbols.get(method).container?;
        if symbols
            .get(container)
            .as_named_type()
            .is_none_or(|detail| detail.arity == 0)
        {
            return None;
        }
        // `values == null` on an `ImmutableArray<T>` calls the `==` that
        // takes two `ImmutableArray<T>?`: the construction is inside the
        // nullable.
        let candidates: Vec<Type> = std::iter::once(result)
            .chain(arguments.iter().map(|argument| &argument.ty))
            .filter_map(|ty| {
                let inner = self
                    .emitter
                    .nullable_underlying(ty)
                    .unwrap_or_else(|| ty.clone());
                self.emitter.binder.constructed_from(&inner, container)
            })
            .filter(|ty| self.emitter.is_constructed(ty))
            .collect();
        // `SyntaxList<T>.op_Implicit(SyntaxList<T>)` gives a
        // `SyntaxList<GreenNode>`: both types are constructions of the
        // container, and the one meant is the one under which the operator
        // takes what it was given and gives what was asked for.
        let parameters: Vec<SymbolId> = symbols
            .get(method)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        let fits = |candidate: &Type| {
            parameters.len() == arguments.len()
                && parameters
                    .iter()
                    .zip(arguments)
                    .all(|(parameter, argument)| {
                        let taken = self.emitter.member_type(*parameter, candidate);
                        let given = self
                            .emitter
                            .nullable_underlying(&argument.ty)
                            .is_some_and(|inner| inner == taken)
                            || argument.ty == taken;
                        given || taken.is_error()
                    })
        };
        candidates
            .iter()
            .find(|candidate| {
                fits(candidate) && self.emitter.member_type(method, candidate) == *result
            })
            .or_else(|| candidates.iter().find(|candidate| fits(candidate)))
            .or_else(|| candidates.first())
            .cloned()
    }

    pub(crate) fn field_token_on(
        &mut self,
        field: SymbolId,
        receiver: Option<&Type>,
    ) -> Result<Token, EmitError> {
        if let Some(receiver) = self.emitter.through(field, receiver) {
            return self.emitter.member_of_constructed(field, &receiver);
        }
        if receiver.is_none() {
            if let Some(construction) = self.static_own_construction(field) {
                return self.emitter.member_of_constructed(field, &construction);
            }
            self.emitter.check_not_static_generic(field)?;
        }
        self.field_token(field)
    }

    /// The construction a static member is named through when the type
    /// arguments it needs are the ones already in scope.
    ///
    /// `MetadataReferenceEqualityComparer` writes no type parameters at all,
    /// but it is nested in `CommonReferenceManager<TCompilation,
    /// TAssemblySymbol>` and metadata gives a nested type its enclosing
    /// type's parameters. Its static `Instance` is therefore a member of a
    /// *construction*, and reading it from a method of the enclosing type
    /// leaves exactly one construction it could mean: the one that method is
    /// already inside, `!0` and `!1` themselves.
    ///
    /// `None` where the parameters are not in scope — a static member of some
    /// other generic type, which nothing here says which construction of.
    /// The type parameter and the constraint through which a static
    /// abstract interface member is reached: for `op_Addition` of
    /// `IAdditionOperators<TSelf, TOther, TResult>` inside `Sum<T>(T a, T b)
    /// where T : IAdditionOperators<T, T, T>`, the `T` and that construction.
    /// The constraint may be inherited: `T : INumber<T>` reaches the same
    /// interface through what `INumber<T>` extends.
    fn static_abstract_constraint(&self, method: SymbolId) -> Option<(SymbolId, Type)> {
        let symbols = self.emitter.compilation.symbols();
        let symbol = symbols.get(method);
        let container = symbol.container?;
        let container = if matches!(
            symbols.get(container).kind,
            SymbolKind::Property | SymbolKind::Event
        ) {
            symbols.get(container).container?
        } else {
            container
        };
        if !symbol.modifiers.contains(Modifiers::STATIC)
            || symbols.get(container).type_kind() != Some(TypeKind::Interface)
            || !(symbol.modifiers.contains(Modifiers::ABSTRACT)
                || symbol.modifiers.contains(Modifiers::VIRTUAL))
        {
            return None;
        }
        let mut candidates: Vec<SymbolId> = self.emitter.method_generics.clone();
        if let Some(site) = self
            .owner
            .and_then(|owner| self.emitter.enclosing_type(owner))
            && let Some(detail) = symbols.get(site).as_named_type()
        {
            candidates.extend(detail.type_parameters.iter().copied());
        }
        candidates.extend(self.emitter.display_generics.iter().copied());
        for parameter in candidates {
            let mut pending: Vec<Type> = self.emitter.binder.base_types_of(parameter);
            let mut seen = std::collections::HashSet::new();
            while let Some(current) = pending.pop() {
                if !seen.insert(current.clone()) {
                    continue;
                }
                if current.symbol() == Some(container) {
                    return Some((parameter, current));
                }
                let Some(declared) = current.symbol() else {
                    continue;
                };
                let substitution = self.emitter.binder.type_substitution(&current);
                for base in self.emitter.binder.base_types_of(declared) {
                    pending.push(base.substitute(&substitution));
                }
            }
        }
        None
    }

    fn static_own_construction(&self, member: SymbolId) -> Option<Type> {
        let symbols = self.emitter.compilation.symbols();
        // A static local function's container is the method it is written
        // in; the type it is a member of is the one around that.
        let container = self.emitter.enclosing_type(member)?;
        let construction = self.emitter.own_construction(container)?;
        let needed = &symbols.get(container).as_named_type()?.type_parameters;
        let site = self.emitter.enclosing_type(self.owner?)?;
        let in_scope = symbols
            .get(site)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        needed
            .iter()
            .all(|parameter| {
                in_scope.contains(parameter) || self.emitter.display_generics.contains(parameter)
            })
            .then_some(construction)
    }

    fn field_token(&mut self, field: SymbolId) -> Result<Token, EmitError> {
        if let Some(token) = self.emitter.fields.get(&field).copied() {
            return Ok(token);
        }
        // Not defined here, so it is referenced: `int.MaxValue` is a static
        // field of a framework type like any other.
        if self.emitter.compilation.is_from_corlib(field) {
            return self.emitter.referenced_field(field);
        }
        self.emitter.fields.get(&field).copied().ok_or_else(|| {
            EmitError::new(format!(
                "cannot reference the field `{}`: it is not defined in this assembly",
                self.emitter.compilation.symbols().qualified_name(field)
            ))
        })
    }

    /// The token a call or an `ldftn` actually names.
    ///
    /// A method with type arguments is named through the instantiation, never
    /// through the definition — and a lambda or a local function made for a
    /// generic method carries that method's parameters in front of whatever
    /// the source wrote, so it is generic even where nothing said so.
    pub(crate) fn instantiated(
        &mut self,
        token: Token,
        type_arguments: &[Type],
    ) -> Result<Token, EmitError> {
        let inherited = self
            .emitter
            .inherited_generics
            .get(&token)
            .cloned()
            .unwrap_or_default();
        if inherited.is_empty() && type_arguments.is_empty() {
            return Ok(token);
        }
        let mut all: Vec<Type> = inherited.into_iter().map(Type::TypeParameter).collect();
        all.extend(type_arguments.iter().cloned());
        self.emitter.method_instantiation(token, &all)
    }

    /// The token for a call, which depends on what it is called *through*.
    ///
    /// `Box<int>.Get()` and `Box<string>.Get()` are the same definition and
    /// two different members, so the receiver's type decides.
    pub(crate) fn method_token_on(
        &mut self,
        method: SymbolId,
        receiver: Option<&Type>,
    ) -> Result<Token, EmitError> {
        if let Some(receiver) = self.emitter.through(method, receiver) {
            // This holds for a framework type too: `List<string>.Add` is a
            // `MemberRef` under a `TypeSpec` whether or not the definition is
            // in this assembly.
            return self.emitter.member_of_constructed(method, &receiver);
        }
        if receiver.is_none() {
            if let Some(construction) = self.static_own_construction(method) {
                return self.emitter.member_of_constructed(method, &construction);
            }
            self.emitter.check_not_static_generic(method)?;
        }
        self.method_token(method)
    }

    /// The parameterless constructor of a type the language names by its
    /// metadata name, where the program declares that type itself: Roslyn
    /// looks for such a type in the compilation before the references.
    fn source_constructor(&mut self, qualified: &str) -> Result<Option<Token>, EmitError> {
        let compilation = self.emitter.compilation;
        let Some(ty) = compilation.type_by_metadata_name(qualified) else {
            return Ok(None);
        };
        if compilation.is_from_metadata(ty) {
            return Ok(None);
        }
        let symbols = compilation.symbols();
        let constructor = symbols
            .lookup(ty, ".ctor")
            .iter()
            .copied()
            .find(|candidate| {
                symbols
                    .get(*candidate)
                    .as_method()
                    .is_some_and(|detail| detail.parameters.is_empty())
            });
        match constructor {
            Some(constructor) => self.method_token(constructor).map(Some),
            None => Ok(None),
        }
    }

    /// The static abstract or virtual member of the interface a type
    /// parameter's constraint names, as a `constrained.` call reaches it:
    /// under the constraint's construction where it is one, and as the
    /// member itself where the interface is not generic.
    fn constraint_member(
        &mut self,
        method: SymbolId,
        construction: &Type,
    ) -> Result<Token, EmitError> {
        if self.emitter.is_constructed(construction) {
            self.emitter.member_of_constructed(method, construction)
        } else {
            self.method_token(method)
        }
    }

    fn method_token(&mut self, method: SymbolId) -> Result<Token, EmitError> {
        if let Some(token) = self.emitter.methods.get(&method) {
            return Ok(*token);
        }
        if self.emitter.compilation.is_from_corlib(method) {
            return self.emitter.corlib_member(method);
        }
        Err(EmitError::new(format!(
            "cannot reference the method `{}`",
            self.emitter.compilation.symbols().qualified_name(method)
        )))
    }
}

/// What a call is made of.
///
/// Emitting one needs the receiver, the method, what it was given and what it
/// gives back, and whether a reference it returns is to be read through — too
/// many things to hand over one at a time.
struct CallSite<'c> {
    receiver: Option<&'c BoundExpression>,
    method: SymbolId,
    type_arguments: &'c [Type],
    arguments: &'c [BoundExpression],
    virtual_call: bool,
    /// The type the call produces, once a reference it returns has been read
    /// through.
    result: &'c Type,
    /// Whether to read through a reference the method returns. `ref M()` is
    /// the one place that does not.
    read: bool,
}

const fn less_than(unsigned: bool) -> Instruction {
    if unsigned {
        Instruction::CompareLessUnsigned
    } else {
        Instruction::CompareLess
    }
}

const fn greater_than(unsigned: bool) -> Instruction {
    if unsigned {
        Instruction::CompareGreaterUnsigned
    } else {
        Instruction::CompareGreater
    }
}

/// A destructor's statements, which are `try { body } finally { base.Finalize(); }`
/// where a base class has a `Finalize` to chain to (Roslyn's
/// `MethodBodySynthesizer.ConstructDestructorBody`): an object is finalized
/// once, so every class up the chain has to get its turn in that one call.
fn destructor_statements(
    emitter: &Emitter<'_>,
    method: SymbolId,
    body: &BoundBody,
) -> Option<Vec<BoundStatement>> {
    let symbols = emitter.compilation.symbols();
    let is_destructor = symbols
        .get(method)
        .as_method()
        .is_some_and(|detail| detail.method_kind == rustlyn_semantics::MethodKind::Destructor);
    let base = is_destructor
        .then(|| symbols.get(method).container)
        .flatten()
        .and_then(|container| emitter.binder.base_class_of(container))?;
    let finalize = base.symbol().and_then(|symbol| {
        emitter
            .binder
            .lookup_member(symbol, "Finalize")
            .into_iter()
            .find(|member| {
                symbols.get(*member).as_method().is_some_and(|detail| {
                    detail.parameters.is_empty() && detail.type_parameters.is_empty()
                })
            })
    })?;
    let span = body
        .statements
        .first()
        .map_or_else(TextSpan::default, |first| first.span);
    let call = BoundExpression::new(
        BoundExpressionKind::Call {
            receiver: Some(Box::new(BoundExpression::new(
                BoundExpressionKind::Base,
                base,
                span,
            ))),
            method: finalize,
            type_arguments: Vec::new(),
            arguments: Vec::new(),
            virtual_call: false,
        },
        Type::Void,
        span,
    );
    let wrapped = BoundStatement::new(
        BoundStatementKind::Try {
            body: Box::new(BoundStatement::new(
                BoundStatementKind::Block(body.statements.clone()),
                span,
            )),
            catches: Vec::new(),
            finally: Some(Box::new(BoundStatement::new(
                BoundStatementKind::Expression(call),
                span,
            ))),
        },
        span,
    );
    Some(vec![wrapped])
}

/// The value an initializer body returns, which is the initializer itself.
pub(crate) fn first_returned_value(body: &BoundBody) -> Option<BoundExpression> {
    body.statements
        .iter()
        .find_map(|statement| match &statement.kind {
            BoundStatementKind::Return(Some(value)) => Some(value.clone()),
            _ => None,
        })
}

/// Whether a statement holds a protected region, however deeply.
///
/// `ret` may not leave one — §III.3.56 — so a method with any `try` at all
/// gets a single exit at the end and every `return` inside becomes a `leave`
/// to it. A `try` with only catches is as protected as one with a `finally`.
fn has_finally(statement: &BoundStatement) -> bool {
    match &statement.kind {
        // A `using` and a `lock` are both a `try`/`finally` once written out,
        // so a method that has one needs the single exit too.
        BoundStatementKind::Try { .. }
        | BoundStatementKind::Using { .. }
        | BoundStatementKind::Lock { .. } => true,
        BoundStatementKind::Block(statements) => statements.iter().any(has_finally),
        BoundStatementKind::If {
            consequence,
            alternative,
            ..
        } => has_finally(consequence) || alternative.as_deref().is_some_and(has_finally),
        BoundStatementKind::While { body, .. }
        | BoundStatementKind::DoWhile { body, .. }
        | BoundStatementKind::Fixed { body, .. } => has_finally(body),
        // `foreach` over an enumerator disposes it in a `finally`, so a method
        // with one needs the single exit too.
        BoundStatementKind::ForEach {
            body, enumeration, ..
        } => {
            enumeration
                .as_ref()
                .is_some_and(|walk| walk.dispose.is_some())
                || has_finally(body)
        }
        BoundStatementKind::For {
            initializers, body, ..
        } => initializers.iter().any(has_finally) || has_finally(body),
        BoundStatementKind::Switch { sections, .. } => sections
            .iter()
            .any(|section| section.statements.iter().any(has_finally)),
        _ => false,
    }
}

/// Whether an expression is a type name rather than a value.
///
/// `Holder<int>.Count` has one where an instance member would have a
/// receiver: it says which construction the member belongs to, and there is
/// nothing to push for it.
/// Whether a branch of a conditional was written `ref x`.
/// The `stackalloc`s at these spans inside an expression, outermost first.
fn collect_stackallocs(
    expression: &mut BoundExpression,
    spans: &[TextSpan],
    found: &mut Vec<BoundExpression>,
) {
    if matches!(expression.kind, BoundExpressionKind::StackAlloc { .. })
        && spans.contains(&expression.span)
    {
        found.push(expression.clone());
        return;
    }
    for child in crate::async_machine::children_mut(expression) {
        collect_stackallocs(child, spans, found);
    }
}

/// Whether a value is a `stackalloc`, perhaps converted.
fn contains_stackalloc(value: &BoundExpression) -> bool {
    match &value.kind {
        BoundExpressionKind::StackAlloc { .. } => true,
        BoundExpressionKind::Conversion { operand, .. } => contains_stackalloc(operand),
        _ => false,
    }
}

/// Whether a dereference is `p[i]`: the binder writes it as `*(p + i)`
/// with the addition spanning the whole access, where `*(p + i)` written
/// out has the addition inside the parentheses.
fn is_element_access(dereference: &BoundExpression) -> bool {
    matches!(&dereference.kind, BoundExpressionKind::Dereference { operand }
        if operand.span == dereference.span
            && matches!(operand.kind, BoundExpressionKind::Binary { operator: BinaryOperator::Add, .. }))
}

fn is_ref_branch(branch: &BoundExpression) -> bool {
    matches!(branch.kind, BoundExpressionKind::RefArgument { .. })
}

/// The value of a condition that is a `true` or `false` literal.
fn constant_condition(condition: &BoundExpression) -> Option<bool> {
    match &condition.kind {
        BoundExpressionKind::Literal(ConstantValue::Boolean(value)) => Some(*value),
        _ => None,
    }
}

fn is_type_name(expression: &BoundExpression) -> bool {
    matches!(expression.kind, BoundExpressionKind::TypeExpression(_))
}

/// Whether a type names a type parameter of some method other than this one.
///
/// A method's signature can only spell the type parameters it declares
/// itself, and those of the type it belongs to. Anything else belongs to a
/// nested local function, whose locals share this table without sharing this
/// method's generics.
fn foreign_parameter(symbols: &Symbols, ty: &Type, declared: &[SymbolId]) -> bool {
    match ty {
        Type::TypeParameter(symbol) => {
            !declared.contains(symbol)
                && symbols
                    .get(*symbol)
                    .container
                    .is_some_and(|container| symbols.get(container).kind == SymbolKind::Method)
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            foreign_parameter(symbols, element, declared)
        }
        Type::Named { type_arguments, .. } => type_arguments
            .iter()
            .any(|argument| foreign_parameter(symbols, argument, declared)),
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| foreign_parameter(symbols, &element.ty, declared)),
        Type::FunctionPointer(pointer) => pointer
            .types()
            .any(|ty| foreign_parameter(symbols, ty, declared)),
        Type::Error | Type::Null | Type::Void | Type::Dynamic => false,
    }
}

/// Whether an expression holds an operation on `dynamic` anywhere in it.
fn mentions_dynamic(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::Dynamic(_) => true,
        // The target of an assignment is a place, whose own parts are what
        // the walk lists; the place itself may be the `dynamic` one.
        BoundExpressionKind::Assignment { target, value }
        | BoundExpressionKind::CompoundAssignment { target, value, .. } => {
            mentions_dynamic(target) || mentions_dynamic(value)
        }
        BoundExpressionKind::Increment { target, .. } => mentions_dynamic(target),
        _ => crate::async_machine::children(expression)
            .into_iter()
            .any(mentions_dynamic),
    }
}

/// A display class's captured parameters in the order they were declared,
/// which is the order they are copied in: a map's order is a hash's, and
/// would differ from one run to the next.
fn by_declaration(parameters: &HashMap<SymbolId, Token>) -> Vec<(SymbolId, Token)> {
    let mut sorted: Vec<(SymbolId, Token)> = parameters
        .iter()
        .map(|(parameter, field)| (*parameter, *field))
        .collect();
    sorted.sort_unstable_by_key(|(parameter, _)| *parameter);
    sorted
}

/// Whether evaluating an argument cannot write the variable a receiver's
/// address was taken of (Roslyn's
/// `IsSafeToDereferenceReceiverRefAfterEvaluatingArguments`): a constant, a
/// local, a parameter, `this`, a static field or a field of one of those, and
/// the built-in operators and conversions on them.
fn safe_after_receiver(argument: &BoundExpression) -> bool {
    match &argument.kind {
        BoundExpressionKind::Literal(_)
        | BoundExpressionKind::Default(_)
        | BoundExpressionKind::TypeExpression(_)
        | BoundExpressionKind::Local(_)
        | BoundExpressionKind::Parameter(_)
        | BoundExpressionKind::This => true,
        BoundExpressionKind::Field { receiver, .. } => {
            receiver.as_deref().is_none_or(safe_after_receiver)
        }
        BoundExpressionKind::Binary { left, right, .. } => {
            safe_after_receiver(left) && safe_after_receiver(right)
        }
        // A user-defined conversion is a call, and never gets here.
        BoundExpressionKind::Conversion { operand, .. } => safe_after_receiver(operand),
        _ => false,
    }
}

/// The statements a method is made of, next to the body it was bound in.
///
/// A member's method runs the member's own statements, read from the shared
/// body where they are; a closure's runs its own, which the body holds
/// deeper down. Emitting takes them once, and from then on the method has
/// none left to look at, as though they had been moved out.
enum Statements {
    Body,
    Own(Vec<BoundStatement>),
    Taken,
}

/// The statements taken for emitting, with the body that holds them where
/// they are the body's own.
pub(crate) struct TakenStatements {
    body: Arc<BoundBody>,
    own: Option<Vec<BoundStatement>>,
}

impl std::ops::Deref for TakenStatements {
    type Target = [BoundStatement];

    fn deref(&self) -> &[BoundStatement] {
        self.own.as_deref().unwrap_or(&self.body.statements)
    }
}

impl<'s> IntoIterator for &'s TakenStatements {
    type Item = &'s BoundStatement;
    type IntoIter = std::slice::Iter<'s, BoundStatement>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl BodyEmitter<'_, '_> {
    /// The method's statements, for emitting; after this it has none.
    fn take_statements(&mut self) -> TakenStatements {
        let own = match std::mem::replace(&mut self.statements, Statements::Taken) {
            Statements::Body => None,
            Statements::Own(statements) => Some(statements),
            Statements::Taken => Some(Vec::new()),
        };
        TakenStatements {
            body: Arc::clone(&self.body),
            own,
        }
    }

    /// The method's statements, where they have not been taken yet.
    fn current_statements(&self) -> &[BoundStatement] {
        match &self.statements {
            Statements::Body => &self.body.statements,
            Statements::Own(statements) => statements,
            Statements::Taken => &[],
        }
    }
}

/// The value of a type parameter a comparison with `null` boxes: the side
/// itself, or what its conversion to a reference type converts.
fn boxed_type_parameter(side: &BoundExpression) -> Option<&BoundExpression> {
    let inner = match &side.kind {
        BoundExpressionKind::Conversion { operand, .. } => operand.as_ref(),
        _ => side,
    };
    matches!(inner.ty, Type::TypeParameter(_)).then_some(inner)
}
