//! Binding a method body.
//!
//! This is the pass that gives an expression a type, decides which overload a
//! call means, and creates the locals a body declares. What comes out is a
//! [`BoundBody`]: a tree in which every question the source asked has an
//! answer, plus the two span-keyed lookups the semantic model serves from.
//!
//! The tree is the point. A backend that walked the syntax again would have to
//! redo overload resolution and conversion classification, and would not
//! always reach the same answer as the binder did; the diagnostics would then
//! describe a program other than the one that ran.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use crate::binder::{Binder, Context, Diagnostics};
use crate::bound::{
    BoundBody, BoundExpression, BoundExpressionKind, BoundSymbol, ConstantValue, LocalId,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{RefKind, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

mod assignment;
mod calls;
mod conversions;
mod creation;
mod disposal;
mod dynamic;
mod elements;
mod expressions;
mod foreach;
mod inference;
mod instance_operators;
mod interpolation;
mod lambdas;
mod members;
mod names;
mod natural;
mod operators;
mod overloads;
mod patterns;
mod pointers;
mod queries;
mod scopes;
mod statements;
mod tuples;

/// Binds the statements and expressions of one body.
pub struct BodyBinder<'a> {
    binder: &'a Binder<'a>,
    tree: usize,
    context: Context,
    /// The method whose body this is, for the return type and for `this`.
    member: Option<SymbolId>,
    /// Locals in scope, innermost scope last.
    scopes: Vec<HashMap<String, LocalId>>,
    body: BoundBody,
    /// The lambdas being bound, innermost last. A name that resolves to a
    /// scope below one of these belongs to the enclosing method, which makes
    /// it a capture.
    lambdas: Vec<LambdaFrame>,
    /// The types of the receivers of the `?.` expressions being bound,
    /// innermost last.
    accessed: Vec<Type>,
    /// Whether the declaration being bound is a `fixed` one, which is where a
    /// string or an array is allowed to be a pointer.
    fixing: bool,
    /// The types the `switch` statements around the code being bound
    /// switch on, innermost last: what a `goto case` value converts to.
    switch_types: Vec<Type>,
    /// Which scopes sit *beside* the ones around them rather than inside: one
    /// entry per scope, so a `switch` section can see what an earlier section
    /// declared without that counting as a redeclaration.
    siblings: Vec<bool>,
    /// Where the statement being bound is, which is what a local the binder
    /// makes up — a `foreach`'s enumerator, a temporary — is said to be
    /// declared at: a backend hoisting a closure's locals by where they were
    /// declared has to see them inside the closure.
    synthetic_span: TextSpan,
    /// The locals declared `const`, with their values. A read of one is the
    /// value, not the slot: `RT_ICON + 11` folds, and a `static` lambda may
    /// name one without capturing anything.
    constant_locals: HashMap<LocalId, ConstantValue>,
    /// The first lambda frame that can capture anything at the moment: inside
    /// a `static` lambda the frames around it are cut off, and a name found
    /// in the lambda's own scope — at a depth the outer frames would read as
    /// below their floor — is not a capture of theirs.
    capture_floor: usize,
    /// The branch types of each conditional or `switch` expression left
    /// typeless because its branches disagreed, by span: overload
    /// resolution asks them which parameters the whole thing can reach.
    branch_types: HashMap<TextSpan, Vec<Type>>,
    /// The natural types of a collection expression's plain elements, by
    /// the expression's span, for overload resolution to ask whether a
    /// candidate's element type is one they reach.
    collection_types: HashMap<TextSpan, Vec<Type>>,
    /// What the elements noted in `collection_types` fold to.
    collection_constants: HashMap<TextSpan, Vec<Option<ConstantValue>>>,
    /// What kind each of the elements noted in `collection_types` is.
    collection_kinds: HashMap<TextSpan, Vec<ElementKind>>,
    /// The same with what nested collections suggest, which only inference
    /// reads.
    collection_hints: HashMap<TextSpan, Vec<inference::InferenceArgument>>,
    /// Whether a node sits in a `finally` of its function, for the nodes
    /// asked about or passed on the way up, by where they are in the tree:
    /// the statements of a long `else if` ladder are each as deep as the
    /// ladder is long, and each would walk all of it again.
    in_finally_memo: HashMap<(usize, u32), bool>,
    /// What `written_typeless` said of the conditionals it was asked about.
    typeless_memo: RefCell<HashMap<(usize, u32), bool>>,
    /// Where each variable's `out var` zone is, by the start of its name,
    /// or that it has none.
    out_var_zones: HashMap<u32, Option<(u32, u32)>>,
    /// Whether the body is a field or property initializer, where a record's
    /// positional parameter is itself and not the property made from it.
    in_initializer: bool,
    /// Whether this binds an attribute's arguments, where the parameters of
    /// the member it is on are named only by `nameof` (C# 11): `[A(p)]` on a
    /// method means a `p` of its type, whatever parameter is called that.
    pub(super) in_attribute: bool,
    /// Whether the expression being bound is a `nameof`'s argument, which is
    /// never evaluated: an outer type's instance member is a name there.
    pub(super) in_nameof: bool,
    /// Set while the name of a call is bound: what cannot be called does
    /// not hide what can.
    pub(super) invoked: bool,
    /// What the lambdas of the overload resolutions under way were found
    /// to return, innermost resolution last (see [`inference`]).
    lambda_answers: std::cell::RefCell<Vec<inference::LambdaAnswers>>,
    /// The cast being bound, whose context — not its operand's — says
    /// whether an `explicit operator checked` (C# 11) applies:
    /// `unchecked((int)checked(a + b))` casts in an unchecked context.
    cast_span: Option<TextSpan>,
    /// Whether the call being bound is one the compiler writes with no
    /// syntax behind it, which takes no caller info.
    implicit_call: bool,
    /// The argument names of the calls being resolved in written order,
    /// innermost last, with the candidates they are placed against: each
    /// candidate reads them into its own parameters (§12.6.2.2).
    argument_names: std::cell::RefCell<Vec<NamedArguments>>,
    /// The type parameters of extension blocks that the type a static
    /// member is reached through settles, while a call to it is resolved.
    static_receiver: std::cell::RefCell<HashMap<SymbolId, Type>>,
    /// The holes of interpolated strings whose values had no type of their
    /// own — a conditional, a `switch`, a `new()` — as they were written,
    /// by span. Each was made an `object` for a string, and a handler's
    /// `AppendFormatted` may take it as something else (C# 10).
    typeless_holes: HashMap<TextSpan, BoundExpression>,
    /// The temporary the receiver of the call whose arguments were just
    /// converted is to be kept in, where an interpolated string handler
    /// among them is made with it (`[InterpolatedStringHandlerArgument("")]`).
    pending_receiver: Option<LocalId>,
    /// What binding a lambda against a delegate showed, by the lambda, the
    /// delegate and the locals around it (see `probe_lambda`).
    lambda_probes: HashMap<LambdaKey, Option<LambdaProbe>>,
    /// The expressions a conversion to `object` took the `dynamic` off, by
    /// span, while a lambda is probed: the conversion changes nothing at run
    /// time and leaves no node, and the lambda's return type is `dynamic`
    /// all the same.
    dynamic_relabelled: std::collections::HashSet<TextSpan>,
    /// The nodes `syntax_at` has found, by span.
    syntax_found: std::cell::RefCell<HashMap<TextSpan, Option<SyntaxNode>>>,
    /// The outermost of `lambda_answers` read since this was last reset, by
    /// its place on the stack: a lambda's binding that read the answers of a
    /// resolution it did not start depends on more than its key.
    answers_read: std::cell::Cell<usize>,
    /// Whether this binding is an editor's: a lambda no delegate took is
    /// bound all the same (see `recover_lambdas_in`).
    recover_lambdas: bool,
    /// For an editor's binding, what a lambda of a call that resolved to
    /// nothing was tried with, by the lambda's span (see
    /// `guess_lambda_parameters`).
    lambda_guesses: HashMap<TextSpan, lambdas::LambdaGuess>,
    /// Every name recorded as a local, in order, with what the name was
    /// recorded as before: what a speculation takes back (see
    /// `unwind_speculation`).
    local_references: Vec<(TextSpan, Option<BoundSymbol>)>,
}

/// A lambda's span, the delegate it is bound against, and a 128-bit
/// fingerprint of every local — its name, type and place — as they are.
type LambdaKey = (TextSpan, Type, u64, u64);

/// The candidates of a call being resolved and the names its arguments were
/// written with, in written order.
type NamedArguments = (Vec<SymbolId>, Vec<Option<String>>);

/// What a lambda takes from around it, gathered while its body is bound.
/// A range variable of a query: its name, where it was written, and its type.
#[derive(Clone)]
struct Range {
    name: String,
    span: TextSpan,
    ty: Type,
}

/// What `detach_scopes` set aside: the scopes, the sibling flags, and the
/// capture floor, all restored together.
type DetachedScopes = (Vec<HashMap<String, LocalId>>, Vec<bool>, usize);

struct LambdaFrame {
    /// How deep the scope stack was when the lambda started. Anything found
    /// below this is not the lambda's own.
    floor: usize,
    /// What a `return` inside the lambda has to produce, which is the
    /// delegate's return type and not the enclosing method's.
    return_type: Type,
    captured: Vec<LocalId>,
    captured_parameters: Vec<SymbolId>,
    captures_this: bool,
    /// The local functions called from inside, whose captures become the
    /// frame's once every body is bound.
    calls: Vec<SymbolId>,
    /// The member whose parameters belong to this frame rather than to what
    /// encloses it. A lambda declares none that a symbol stands behind; a
    /// local function declares its own, and reading one is not a capture.
    declares: Option<SymbolId>,
    /// The element type, once a `yield` inside the frame has said it is an
    /// iterator.
    iterator: Option<Type>,
}

impl std::fmt::Debug for BodyBinder<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BodyBinder")
            .field("tree", &self.tree)
            .field("member", &self.member)
            .finish_non_exhaustive()
    }
}

/// An overload, picked, with what its type parameters turned out to be.
/// How well a candidate fits, largest best.
///
/// Taking the arguments as written beats making an array of them; then the
/// most exact matches; then, all else equal, the less generic of the two, as
/// §12.6.4.5 says.
///
/// The last says whether a lambda or a method group reached its parameter
/// only through the type it has on its own, which C# 10 ranks below every
/// candidate that did without; after it, whether the call leaves out a `ref`
/// of a COM method's parameter, which ranks below reaching one as written.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct Betterness(bool, usize, std::cmp::Reverse<usize>, bool, bool);

/// A candidate's parameters as this call sees them.
struct Shape {
    /// The parameter types with the receiver's and the method's own type
    /// arguments substituted in.
    parameters: Vec<Type>,
    /// How each parameter is passed. `Lex(mode)` and `Lex(ref mode)` are two
    /// methods with the same parameter type, and only this tells them apart.
    ref_kinds: Vec<RefKind>,
    /// The method's own type arguments, in declaration order.
    type_arguments: Vec<Type>,
    /// The same, as a substitution.
    substitution: HashMap<SymbolId, Type>,
    /// How many arguments the call must supply: the parameters that are
    /// neither optional nor `params`.
    required: usize,
    /// How many parameters are written as the method's own type parameter and
    /// nothing else. `Create<T>(T)` scores one where `Create<T>(ImmutableArray<T>)`
    /// scores none, and §12.6.4.5 says the less generic of two otherwise equal
    /// candidates is the better one.
    generality: usize,
    /// Whether a type argument was inferred from the natural type of a
    /// lambda or a method group (C# 10).
    from_function: bool,
}

/// What an element of a collection expression is, as far as overload
/// resolution asks.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ElementKind {
    Plain,
    /// A spread, whose type is that of what it walks.
    Spread,
    /// An interpolated string that is no constant, which a handler type
    /// takes as well as a string (C# 10).
    Interpolated,
}

/// An element of a collection expression as overload resolution sees it: its
/// type, what it folds to where it is a constant, and what kind it is.
type NotedElement = (Type, Option<ConstantValue>, ElementKind);

/// What a call says about its arguments beyond their types.
///
/// A constant may reach a parameter its type does not, a lambda has only an
/// arity to tell two delegates apart, and a `ref` at the call site is the
/// whole difference between `Lex(mode)` and `Lex(ref mode)` — two methods
/// whose parameter types are the same.
#[derive(Default)]
struct Evidence {
    constants: Vec<Option<ConstantValue>>,
    lambdas: Vec<Option<usize>>,
    /// Whether each lambda's expression body is a `ref` one, which reaches
    /// a delegate returning by reference and no other; `None` where the
    /// argument is no lambda or its body is a block.
    lambda_refs: Vec<Option<bool>>,
    /// Which arguments are lambdas written outside any unsafe context, which
    /// may not take a pointer (§24.2).
    lambda_safe: Vec<bool>,
    refs: Vec<RefKind>,
    /// Which arguments are a method named without being called, which has no
    /// type of its own and reaches a delegate and nothing else.
    groups: Vec<bool>,
    /// The methods each such group holds, empty where the argument is not
    /// one. A delegate parameter picks one of them by shape, and what that
    /// one returns is what the delegate's result type is inferred from.
    group_methods: Vec<Vec<SymbolId>>,
    /// Which of those groups are closed over a receiver — `symbol.IsFoo`
    /// naming an extension method — so that the receiver is the method's
    /// first parameter and the delegate takes the rest.
    group_closed: Vec<bool>,
    /// Which arguments are interpolated strings or additions of them, and
    /// what overload resolution asks of one (§12.8.3, C# 10).
    interpolated: Vec<Option<Interpolated>>,
    /// Which arguments are collection expressions, which reach a collection
    /// type and nothing else (§12.8.? collection expression conversions).
    collections: Vec<bool>,
    /// The natural types of each collection expression's elements, where
    /// they were plain enough to have any.
    elements: Vec<Option<Vec<NotedElement>>>,
    /// The branch types of an argument that is a conditional or a `switch`
    /// whose branches could not agree on a type: it reaches a parameter
    /// every branch reaches, and no other (§12.18).
    branches: Vec<Option<Vec<Type>>>,
    /// The branches of an argument that is a conditional with a lambda or a
    /// method group among them: `reverse ? (x, y) => f(y, x) : f` reaches a
    /// parameter each of those reaches — a delegate — and no `IComparer<T>`
    /// beside it, whatever order the overloads come in.
    functions: Vec<Vec<BranchFunction>>,
    /// Whether the first argument is the receiver of an extension method
    /// call, which is passed by reference to a `this ref` parameter without
    /// anyone writing `ref`.
    extension: bool,
    /// Which arguments are lambdas or method groups with a type of their
    /// own (§10.7.3 of C# 10), which reach `object` and `Delegate` too.
    natural: Vec<bool>,
    /// Those natural types themselves, where a candidate takes the argument
    /// as a bare type parameter and so infers the type argument from it.
    natural_types: Vec<Option<Type>>,
    /// What each argument written as a tuple literal is made of: `(1, 2)`
    /// reaches a `(byte, int)` because its first element is a constant that
    /// fits, which its type `(int, int)` does not say.
    tuples: Vec<Option<Vec<TupleLiteralElement>>>,
    /// The arms of an argument that is a `switch` expression with a type of
    /// its own: it reaches a parameter its type does not where every arm
    /// does (the switch expression conversion of C# 8), `b switch { false
    /// => 1, true => 2 }` an `Int16` as its constants do.
    arms: Vec<Option<Vec<TupleLiteralElement>>>,
    /// Each argument as type inference reads it; empty where the caller had
    /// only the arguments' types.
    inference: Vec<inference::InferenceArgument>,
    /// Each argument written `&M`: the methods of its group, its receiver's
    /// type and the type arguments written on it. It has no type of its own
    /// and reaches a function pointer whose signature one of them fits.
    addresses: Vec<Option<AddressOfGroup>>,
}

/// What overload resolution needs of an interpolated string argument: one
/// reaches an interpolated string handler (C# 10) as well as a `string`, a
/// lone one a `FormattableString` too (§12.8.3), and one that is no constant
/// is better given to a handler than to anything else.
#[derive(Clone, Copy)]
struct Interpolated {
    /// Not an addition: `$"a" + $"b"` reaches no `FormattableString`.
    lone: bool,
    /// Whether it folds to a constant, which gives a handler no edge.
    constant: bool,
}

/// A branch of a conditional argument that has no type of its own.
#[derive(Clone)]
enum BranchFunction {
    /// A lambda, with as many parameters as its syntax says.
    Lambda(Option<usize>),
    /// A method group: its methods, and whether it is closed over a
    /// receiver.
    Group(Vec<SymbolId>, bool),
}

/// What overload resolution needs of an `&M` argument.
#[derive(Clone)]
struct AddressOfGroup {
    candidates: Vec<SymbolId>,
    receiver: Option<Type>,
    explicit: Vec<Type>,
}

/// A `Deconstruct` a deconstruction found, with what it needs to be
/// called: its parameters' types as this receiver sees them, and for an
/// extension method the type its receiver is converted to and what its
/// type parameters stand for.
struct FoundDeconstruct {
    method: SymbolId,
    parameters: Vec<Type>,
    receiver: Option<Type>,
    type_arguments: Vec<Type>,
}

/// One element of a tuple literal, as overload resolution sees it.
#[derive(Clone)]
struct TupleLiteralElement {
    ty: Type,
    constant: Option<ConstantValue>,
    nested: Option<Vec<TupleLiteralElement>>,
    /// An interpolated string reaches a handler element (C# 10).
    interpolated: Option<Interpolated>,
}

/// Which way an argument's position constrains the type parameter inferred
/// from it (§12.6.3).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Bound {
    /// The answer may be this or anything it reaches.
    Lower,
    /// The answer is this.
    Exact,
    /// The answer may be this or anything that reaches it.
    Upper,
}

impl Bound {
    /// What the bound becomes under a contravariant type parameter.
    const fn flipped(self) -> Self {
        match self {
            Self::Lower => Self::Upper,
            Self::Exact => Self::Exact,
            Self::Upper => Self::Lower,
        }
    }
}

/// A candidate settled through its lambdas, ready to be committed to.
struct ThroughLambdas {
    candidate: SymbolId,
    type_parameters: Vec<SymbolId>,
    /// The parameters with every type argument filled in.
    parameters: Vec<Type>,
    inferred: HashMap<SymbolId, Type>,
}

/// What binding a lambda against one delegate showed.
#[derive(Clone)]
struct LambdaProbe {
    /// What the body returns; `void` where it returns nothing.
    returns: Type,
    /// Whether an expression body has a value, even where the delegate
    /// returns none and it is dropped.
    yields_value: bool,
    /// Whether the binding reported anything.
    errored: bool,
    /// The type of every value the body returns, in order, with whether it
    /// was a lambda or a method group, whose type is only its natural one.
    all_returns: Vec<(Type, TextSpan, bool)>,
}

/// How a candidate's delegate parameters take the lambdas it was handed,
/// once each lambda has been bound against the delegate it would become.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Fit {
    /// Every lambda returns exactly what its delegate says, which beats a
    /// delegate that takes the value through a conversion (§12.6.4.7):
    /// `Task<TResult>` over `Task` for a body that gives a `Task<X>`.
    Exact,
    /// Every lambda returns what its delegate says.
    Good,
    /// Nothing is wrong, but something else might be better: a lambda whose
    /// body has a value, handed to a delegate that returns none.
    Weak,
    /// A lambda returns something its delegate cannot take.
    Bad,
}

#[derive(Clone)]
struct Resolved {
    method: SymbolId,
    /// The method's own type arguments, in declaration order; empty unless the
    /// method is generic. This is what a `MethodSpec` carries.
    type_arguments: Vec<Type>,
    /// The same, as a substitution to apply to the signature.
    substitution: HashMap<SymbolId, Type>,
}

impl<'a> BodyBinder<'a> {
    /// The version of C# the body is held to: its file's.
    pub(crate) fn language_version(&self) -> rustlyn_syntax::LanguageVersion {
        self.binder
            .compilation()
            .trees()
            .get(self.tree)
            .map_or_else(
                Default::default,
                rustlyn_syntax::SyntaxTree::language_version,
            )
    }

    fn new(
        binder: &'a Binder<'a>,
        tree: usize,
        context: Context,
        member: Option<SymbolId>,
        in_initializer: bool,
    ) -> Self {
        Self {
            binder,
            tree,
            context,
            member,
            scopes: vec![HashMap::new()],
            body: BoundBody::default(),
            lambdas: Vec::new(),
            accessed: Vec::new(),
            fixing: false,
            switch_types: Vec::new(),
            cast_span: None,
            implicit_call: false,
            siblings: vec![false],
            synthetic_span: TextSpan::new(0, 0),
            constant_locals: HashMap::new(),
            capture_floor: 0,
            branch_types: HashMap::new(),
            collection_types: HashMap::new(),
            collection_constants: HashMap::new(),
            collection_kinds: HashMap::new(),
            collection_hints: HashMap::new(),
            in_finally_memo: HashMap::new(),
            typeless_memo: RefCell::new(HashMap::new()),
            out_var_zones: HashMap::new(),
            in_initializer,
            in_attribute: false,
            in_nameof: false,
            invoked: false,
            lambda_answers: std::cell::RefCell::default(),
            argument_names: std::cell::RefCell::default(),
            static_receiver: std::cell::RefCell::default(),
            typeless_holes: HashMap::new(),
            pending_receiver: None,
            lambda_probes: HashMap::new(),
            dynamic_relabelled: std::collections::HashSet::new(),
            syntax_found: std::cell::RefCell::new(HashMap::new()),
            answers_read: std::cell::Cell::new(usize::MAX),
            recover_lambdas: false,
            lambda_guesses: HashMap::new(),
            local_references: Vec::new(),
        }
    }

    /// The node at `span` of the tree being bound, as this binding sees it:
    /// the editor's text where it speculates about an edit. A span the body
    /// recorded is of that text, not of the one compiled.
    ///
    /// Found once per span: a lambda is bound again for each delegate a call
    /// tries, and every lookup from the root walks down as many levels as the
    /// lambda is nested, so a chain of them cost its depth cubed.
    fn syntax_at(&self, span: TextSpan) -> Option<SyntaxNode> {
        if let Some(found) = self.syntax_found.borrow().get(&span) {
            return found.clone();
        }
        let found = self.binder.tree_root(self.tree)?.find_node(span);
        self.syntax_found.borrow_mut().insert(span, found.clone());
        found
    }

    fn report(&mut self, code: ErrorCode, span: TextSpan, args: &[&str]) {
        self.body
            .diagnostics
            .push((self.tree, Diagnostic::new(code, span, args)));
    }

    fn display(&self, ty: &Type) -> String {
        ty.display(self.binder.compilation().symbols())
    }

    fn special(&self, special: SpecialType) -> Type {
        self.binder
            .compilation()
            .special_type(special)
            .map_or(Type::Error, Type::named)
    }

    /// `System.TypedReference`, which `__makeref` makes.
    fn typed_reference(&self) -> Type {
        self.binder
            .compilation()
            .type_by_metadata_name("System.TypedReference")
            .map_or(Type::Error, Type::named)
    }

    /// What the receiver's type arguments say its type parameters are.
    fn substitution(&self, receiver: &Type) -> HashMap<SymbolId, Type> {
        let Type::Named {
            symbol,
            type_arguments,
        } = receiver
        else {
            return HashMap::new();
        };
        if type_arguments.is_empty() {
            return HashMap::new();
        }
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(*symbol).as_named_type() else {
            return HashMap::new();
        };
        detail
            .type_parameters
            .iter()
            .copied()
            .zip(type_arguments.iter().cloned())
            .collect()
    }

    /// The type of a member as seen through a particular receiver.
    fn member_type(&self, member: SymbolId, receiver: &Type) -> Type {
        let mut sink = Diagnostics::new();
        let ty = self.binder.type_of(member, &mut sink);
        // A `ref` return is a variable of the type it refers to; reading it,
        // writing through it and passing it on all work on that type.
        ty.value()
            .substitute(&self.substitution_for(member, receiver))
    }

    /// What a receiver says the type parameters of a member's *declaring*
    /// type are.
    ///
    /// The member may be inherited: a `OperationCloner` is an
    /// `OperationVisitor<object, IOperation>`, and its `Visit` takes an
    /// `object` because that construction says so. Asking the receiver's own
    /// type arguments finds nothing, because it has none.
    fn substitution_for(&self, member: SymbolId, receiver: &Type) -> HashMap<SymbolId, Type> {
        let symbols = self.binder.compilation().symbols();
        // A parameter's container is its method, and a method's is the type:
        // the walk stops at whichever type declares the member.
        let mut current = symbols.get(member).container;
        while let Some(id) = current {
            if symbols.get(id).kind == SymbolKind::NamedType {
                break;
            }
            current = symbols.get(id).container;
        }
        let Some(container) = current else {
            return HashMap::new();
        };
        if receiver.symbol() == Some(container) {
            return self.substitution(receiver);
        }
        match self.binder.constructed_from(receiver, container) {
            Some(constructed) => self.substitution(&constructed),
            None => self.substitution(receiver),
        }
    }

    fn kind_of_type(&self, symbol: SymbolId) -> Option<TypeKind> {
        self.binder.compilation().symbols().get(symbol).type_kind()
    }

    fn kind_of(&self, symbol: SymbolId) -> SymbolKind {
        self.binder.compilation().symbols().get(symbol).kind
    }

    fn resolve(&mut self, node: &SyntaxNode) -> Type {
        let context = self.binder.context_at(self.tree, node);
        let mut sink = Diagnostics::new();
        let ty = self.binder.resolve_type(node, &context, &mut sink);
        self.body.diagnostics.append(&mut sink);
        self.note_type_names(node, &ty, &context);
        ty
    }

    /// Records what each name in a piece of type syntax is, as a name in an
    /// expression is recorded: `Model` in `Model local;`, in `(Model x) =>`,
    /// and `Step` in `new NativeArray<Step>(n)`. A name already given a
    /// symbol keeps it — `Box` in `new Box<Step>()` is the constructor.
    fn note_type_names(&mut self, node: &SyntaxNode, ty: &Type, context: &Context) {
        match node.kind() {
            SyntaxKind::IdentifierName | SyntaxKind::GenericName => {
                let symbol = match ty {
                    Type::Named { symbol, .. } | Type::TypeParameter(symbol) => *symbol,
                    _ => return,
                };
                // `var`, `nint` or an alias spell something other than the
                // type they stand for.
                let Some(token) = node
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                else {
                    return;
                };
                if self.binder.compilation().symbols().get(symbol).name != token.value_text() {
                    return;
                }
                self.body
                    .references
                    .entry(node.span())
                    .or_insert(BoundSymbol::Declared(symbol));
                self.body.symbols.entry(token.span()).or_insert(symbol);
                if let (Some(list), Type::Named { type_arguments, .. }) =
                    (node.child_of_kind(SyntaxKind::TypeArgumentList), ty)
                {
                    let written = list.children().filter(|child| child.kind().is_type_node());
                    for (argument, ty) in written.zip(type_arguments.iter()) {
                        self.note_type_names(&argument, ty, context);
                    }
                }
            }
            SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => {
                let mut children = node.children();
                let (Some(left), Some(right)) = (children.next(), children.next()) else {
                    return;
                };
                self.note_type_names(&right, ty, context);
                if node.kind() == SyntaxKind::QualifiedName {
                    self.note_container_names(&left, context);
                }
            }
            SyntaxKind::NullableType => {
                let underlying = self
                    .binder
                    .nullable_underlying(ty)
                    .unwrap_or_else(|| ty.clone());
                if let Some(element) = node.children().find(|child| child.kind().is_type_node()) {
                    self.note_type_names(&element, &underlying, context);
                }
            }
            SyntaxKind::ArrayType => {
                let mut element = ty;
                while let Type::Array { element: inner, .. } = element {
                    element = inner;
                }
                if let Some(written) = node.children().find(|child| child.kind().is_type_node()) {
                    self.note_type_names(&written, element, context);
                }
            }
            SyntaxKind::PointerType => {
                if let (Type::Pointer(pointee), Some(written)) = (
                    ty,
                    node.children().find(|child| child.kind().is_type_node()),
                ) {
                    self.note_type_names(&written, pointee, context);
                }
            }
            SyntaxKind::TupleType => {
                if let Type::Tuple(elements) = ty {
                    let written = node
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::TupleElement)
                        .filter_map(|element| {
                            element.children().find(|child| child.kind().is_type_node())
                        });
                    for (written, element) in written.zip(elements.iter()) {
                        self.note_type_names(&written, &element.ty, context);
                    }
                }
            }
            _ => {}
        }
    }

    /// The namespaces and types left of the last dot of a type's name:
    /// `System.Collections` in `System.Collections.Generic.List<int>`.
    fn note_container_names(&mut self, node: &SyntaxNode, context: &Context) {
        let Some(found) = self.binder.resolve_namespace_or_type(node, context) else {
            return;
        };
        let (name, left) = match node.kind() {
            SyntaxKind::IdentifierName | SyntaxKind::GenericName => (node.clone(), None),
            SyntaxKind::QualifiedName => {
                let mut children = node.children();
                match (children.next(), children.next()) {
                    (Some(left), Some(right)) => (right, Some(left)),
                    _ => return,
                }
            }
            _ => return,
        };
        self.body
            .references
            .entry(name.span())
            .or_insert(BoundSymbol::Declared(found));
        if let Some(token) = name
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        {
            self.body.symbols.entry(token.span()).or_insert(found);
        }
        if let Some(left) = left {
            self.note_container_names(&left, context);
        }
    }

    fn this_type(&self) -> Type {
        self.context
            .enclosing_type()
            .map_or(Type::Error, |symbol| self.binder.self_type(symbol))
    }

    /// A framework type by its metadata name, where the compilation has one.
    fn framework_type(&self, name: &str) -> Option<Type> {
        self.binder
            .compilation()
            .type_by_metadata_name(name)
            .map(Type::named)
    }
}

/// Whether a lambda written with this many parameters could be this delegate.
///
/// `None` means the syntax did not say — `delegate { ... }` takes whatever the
/// delegate does — and a target that is not a delegate is not ruled out here.
fn arity_fits(written: Option<usize>, target: &Type, symbols: &crate::symbol::Symbols) -> bool {
    let Some(written) = written else {
        return true;
    };
    if !takes_a_function(target, symbols) {
        return false;
    }
    let Some(invoke) = target
        .symbol()
        .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())
    else {
        return true;
    };
    symbols
        .get(invoke)
        .as_method()
        .is_some_and(|detail| detail.parameters.len() == written)
}

impl BodyBinder<'_> {
    /// [`takes_a_function`] where the code stands: a type parameter of the
    /// code's own — the `TSource` of the method a call is in, which the call
    /// inferred its own `TSource` to be — is a type like any other, and no
    /// lambda or method group becomes one. `Split(source, item => )` is not
    /// a call of `Split(IEnumerable<TSource>, TSource separator)`.
    fn takes_a_function_here(&self, target: &Type) -> bool {
        if matches!(target, Type::TypeParameter(_)) && !self.mentions_foreign_type_parameter(target)
        {
            return false;
        }
        takes_a_function(target, self.binder.compilation().symbols())
    }
}

/// Whether a delegate — and so a lambda or a method group — may go here.
///
/// §12.6.4.4: an anonymous function and a method group are applicable to a
/// delegate type and to `Expression<TDelegate>`, and to nothing else, so
/// `new Lazy<int>(() => 3)` may not reach `Lazy(bool)`. Anything that is not
/// a named type — a type parameter nothing has settled, a type that did not
/// resolve — is not their doing, and is left alone. An array, a pointer and
/// a tuple are no delegate: `With(Action<…>)` beside `With(Column[])` is the
/// only one a lambda goes to.
fn takes_a_function(target: &Type, symbols: &crate::symbol::Symbols) -> bool {
    if matches!(
        target,
        Type::Array { .. } | Type::Pointer(_) | Type::Tuple(_)
    ) {
        return false;
    }
    let Type::Named { symbol, .. } = target else {
        return true;
    };
    symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate)
        || symbols.qualified_name(*symbol) == "System.Linq.Expressions.Expression`1"
}

fn identifier_text(node: &SyntaxNode) -> Option<String> {
    node.child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
}

const fn binary_operator(kind: SyntaxKind) -> Option<BinaryOperator> {
    Some(match kind {
        SyntaxKind::AddExpression => BinaryOperator::Add,
        SyntaxKind::SubtractExpression => BinaryOperator::Subtract,
        SyntaxKind::MultiplyExpression => BinaryOperator::Multiply,
        SyntaxKind::DivideExpression => BinaryOperator::Divide,
        SyntaxKind::ModuloExpression => BinaryOperator::Modulo,
        SyntaxKind::LeftShiftExpression => BinaryOperator::LeftShift,
        SyntaxKind::RightShiftExpression => BinaryOperator::RightShift,
        SyntaxKind::UnsignedRightShiftExpression => BinaryOperator::UnsignedRightShift,
        SyntaxKind::BitwiseAndExpression => BinaryOperator::BitwiseAnd,
        SyntaxKind::BitwiseOrExpression => BinaryOperator::BitwiseOr,
        SyntaxKind::ExclusiveOrExpression => BinaryOperator::ExclusiveOr,
        SyntaxKind::LogicalAndExpression => BinaryOperator::LogicalAnd,
        SyntaxKind::LogicalOrExpression => BinaryOperator::LogicalOr,
        SyntaxKind::EqualsExpression => BinaryOperator::Equality,
        SyntaxKind::NotEqualsExpression => BinaryOperator::Inequality,
        SyntaxKind::LessThanExpression => BinaryOperator::LessThan,
        SyntaxKind::GreaterThanExpression => BinaryOperator::GreaterThan,
        SyntaxKind::LessThanOrEqualExpression => BinaryOperator::LessThanOrEqual,
        SyntaxKind::GreaterThanOrEqualExpression => BinaryOperator::GreaterThanOrEqual,
        SyntaxKind::CoalesceExpression => BinaryOperator::Coalesce,
        _ => return None,
    })
}

/// The operator hiding inside a compound assignment: `a += b` is `a = a + b`.
const fn compound_operator(kind: SyntaxKind) -> Option<BinaryOperator> {
    Some(match kind {
        SyntaxKind::AddAssignmentExpression => BinaryOperator::Add,
        SyntaxKind::SubtractAssignmentExpression => BinaryOperator::Subtract,
        SyntaxKind::MultiplyAssignmentExpression => BinaryOperator::Multiply,
        SyntaxKind::DivideAssignmentExpression => BinaryOperator::Divide,
        SyntaxKind::ModuloAssignmentExpression => BinaryOperator::Modulo,
        SyntaxKind::AndAssignmentExpression => BinaryOperator::BitwiseAnd,
        SyntaxKind::OrAssignmentExpression => BinaryOperator::BitwiseOr,
        SyntaxKind::ExclusiveOrAssignmentExpression => BinaryOperator::ExclusiveOr,
        SyntaxKind::LeftShiftAssignmentExpression => BinaryOperator::LeftShift,
        SyntaxKind::RightShiftAssignmentExpression => BinaryOperator::RightShift,
        SyntaxKind::UnsignedRightShiftAssignmentExpression => BinaryOperator::UnsignedRightShift,
        SyntaxKind::CoalesceAssignmentExpression => BinaryOperator::Coalesce,
        _ => return None,
    })
}

/// Gives a bare `default` on one side of an operator the other side's type.
fn retype_default_beside(
    left: BoundExpression,
    right: BoundExpression,
) -> (BoundExpression, BoundExpression) {
    let is_default =
        |value: &BoundExpression| matches!(value.kind, BoundExpressionKind::Default(Type::Error));
    let typed = |value: &BoundExpression| {
        !value.ty.is_error() && !matches!(value.ty, Type::Null) && !typeless(value)
    };
    let retyped = |value: BoundExpression, ty: &Type| {
        BoundExpression::new(
            BoundExpressionKind::Default(ty.clone()),
            ty.clone(),
            value.span,
        )
    };
    match (is_default(&left), is_default(&right)) {
        (true, false) if typed(&right) => {
            let ty = right.ty.clone();
            (retyped(left, &ty), right)
        }
        (false, true) if typed(&left) => {
            let ty = left.ty.clone();
            (left, retyped(right, &ty))
        }
        _ => (left, right),
    }
}

/// Which "does not contain a definition" a missing member is.
///
/// Roslyn words the two differently: `Type.Nonesuch` and `base.Nonesuch`
/// look on a type and find nothing there (CS0117), while `value.Nonesuch`
/// could still have been an extension method the file did not import
/// (CS1061), and the message says so.
fn missing_member_code(receiver: &BoundExpression) -> ErrorCode {
    match receiver.kind {
        BoundExpressionKind::TypeExpression(_) | BoundExpressionKind::Base => {
            ErrorCode::ErrNoSuchMember
        }
        _ => ErrorCode::ErrNoSuchMemberOrExtension,
    }
}

/// Whether a bound expression is still waiting to be told what it is.
fn typeless(value: &BoundExpression) -> bool {
    matches!(
        value.kind,
        BoundExpressionKind::MethodGroup { .. }
            | BoundExpressionKind::UnboundLambda(_)
            | BoundExpressionKind::UnboundCollection(_)
            | BoundExpressionKind::UnboundCreation(_)
            | BoundExpressionKind::UnboundConditional(_)
            | BoundExpressionKind::UnboundSwitch(_)
    )
}

/// How generic a parameter type is, for telling two candidates apart that fit
/// equally well: the less generic one is the more specific (§12.6.4.7).
///
/// A type parameter where the other candidate has a concrete type is what
/// makes a candidate less specific, and one near the top counts for more than
/// one buried in a type argument — `Func<TResult>` is more general than
/// `Func<Task<TResult>>`, which is why `Task.Run(async () => 1)` makes a
/// `Task<int>` and not a `Task<Task<int>>`.
fn generality(ty: &Type, type_parameters: &[SymbolId], depth: u32) -> usize {
    match ty {
        Type::TypeParameter(symbol) if type_parameters.contains(symbol) => {
            1 << 16u32.saturating_sub(depth)
        }
        Type::Named { type_arguments, .. } => type_arguments
            .iter()
            .map(|argument| generality(argument, type_parameters, depth + 1))
            .sum(),
        Type::Array { element, .. } | Type::ByRef(element) | Type::Pointer(element) => {
            generality(element, type_parameters, depth + 1)
        }
        Type::Tuple(elements) => elements
            .iter()
            .map(|element| generality(&element.ty, type_parameters, depth + 1))
            .sum(),
        _ => 0,
    }
}

/// Where a node is, which is what it is told apart by: the same green node
/// at the same place is the same node however many handles there are to it.
fn node_key(node: &SyntaxNode) -> (usize, u32) {
    (Arc::as_ptr(node.green()) as usize, node.full_span().start())
}

impl BodyBinder<'_> {
    /// Whether the expression has no type of its own in the way it is
    /// written: a lambda, a collection expression, a `new()`.
    ///
    /// What a conditional says is kept: the one binding a long `?:` ladder
    /// asks about the whole of what is left of it at every step, and every
    /// answer is the answer for the rest of the ladder as well.
    fn written_typeless(&self, node: &SyntaxNode) -> bool {
        match node.kind() {
            SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::CollectionExpression
            | SyntaxKind::ImplicitObjectCreationExpression => true,
            // `((string s) => int.Parse(s))` is the lambda it wraps.
            SyntaxKind::ParenthesizedExpression => node
                .children()
                .find(|child| child.kind().is_expression())
                .is_some_and(|inner| self.written_typeless(&inner)),
            SyntaxKind::ConditionalExpression => {
                let key = node_key(node);
                if let Some(&known) = self.typeless_memo.borrow().get(&key) {
                    return known;
                }
                let mut branches = node.children().skip(1);
                let answer = match (branches.next(), branches.next()) {
                    (Some(first), Some(second)) => {
                        self.written_typeless(&first) || self.written_typeless(&second)
                    }
                    _ => false,
                };
                self.typeless_memo.borrow_mut().insert(key, answer);
                answer
            }
            SyntaxKind::SwitchExpression => node.children().any(|child| {
                child.kind() == SyntaxKind::SwitchExpressionArm
                    && child
                        .children()
                        .filter(|part| part.kind().is_expression())
                        .last()
                        .is_some_and(|value| self.written_typeless(&value))
            }),
            _ => false,
        }
    }
}

/// The name a call's argument gives a parameter by: the declaring part's,
/// for a partial method whose implementing part renamed it.
fn call_name(symbols: &crate::symbol::Symbols, parameter: SymbolId) -> &str {
    let symbol = symbols.get(parameter);
    symbol
        .as_parameter()
        .and_then(|detail| detail.declared_name.as_deref())
        .unwrap_or(&symbol.name)
}

/// The parameters of a method or an indexer.
fn member_parameters(symbols: &crate::symbol::Symbols, member: SymbolId) -> Option<&[SymbolId]> {
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

/// Whether the call site already passed the array itself.
fn passes_the_array(
    binder: &Binder<'_>,
    arguments: &[BoundExpression],
    parameters: &[Type],
) -> bool {
    arguments.len() == parameters.len()
        && arguments
            .last()
            .zip(parameters.last())
            .is_some_and(|(argument, parameter)| {
                // A lambda has no type yet, and is never the collection.
                !matches!(argument.kind, BoundExpressionKind::UnboundLambda(_))
                    && binder.converts_implicitly(&argument.ty, parameter)
            })
}

/// Whether a type is a construction of a generic definition.
fn is_constructed(ty: &Type) -> bool {
    matches!(ty, Type::Named { type_arguments, .. } if !type_arguments.is_empty())
}

/// What `await foreach` walks with, before it is written out as the loop it
/// means.
struct AsyncEnumeration {
    /// The local the enumerator is kept in.
    enumerator: LocalId,
    /// `collection.GetAsyncEnumerator()`.
    get_enumerator: BoundExpression,
    /// `await enumerator.MoveNextAsync()`.
    move_next: BoundExpression,
    current: SymbolId,
    /// What `Current` yields.
    element: Type,
    /// `if (enumerator != null) await enumerator.DisposeAsync();`, where the
    /// enumerator has one — the statement an `await using` of it would run.
    dispose: Option<Box<crate::bound::BoundStatement>>,
}

/// One operand of a tuple comparison (§12.12.10), taken apart.
enum TupleSide {
    /// A tuple literal: its elements, evaluated already where that mattered.
    Literal(Vec<BoundExpression>),
    /// A value of a tuple type held in a temporary — read through
    /// `GetValueOrDefault()` where the type was nullable, with `HasValue`
    /// beside it.
    Value {
        read: Box<BoundExpression>,
        elements: Vec<Type>,
        has_value: Option<Box<BoundExpression>>,
    },
}

impl TupleSide {
    fn arity(&self) -> usize {
        match self {
            Self::Literal(values) => values.len(),
            Self::Value { elements, .. } => elements.len(),
        }
    }

    fn has_value(&self) -> Option<&BoundExpression> {
        match self {
            Self::Literal(_) => None,
            Self::Value { has_value, .. } => has_value.as_deref(),
        }
    }
}

/// What a `foreach` walks by index.
enum Walked {
    /// An inline array reached afresh through `place` on every turn.
    Inline {
        place: BoundExpression,
        element: Type,
        length: i32,
        readonly: bool,
    },
    /// A `Span<T>` or a `ReadOnlySpan<T>`, kept once.
    Span(BoundExpression),
}

/// Whether a declaration's written type is `var`, through the `scoped` and
/// `ref` written on it: `scoped var r`, `ref var x`, `out scoped var s`.
pub(crate) fn declares_var(node: &SyntaxNode) -> bool {
    let mut node = node.clone();
    while matches!(node.kind(), SyntaxKind::ScopedType | SyntaxKind::RefType) {
        match node.children().find(|child| child.kind().is_type_node()) {
            Some(inner) => node = inner,
            None => return false,
        }
    }
    node.text().trim() == "var"
}
