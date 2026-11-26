//! The bound tree: syntax with every question already answered.
//!
//! A syntax node says `a.b(c)`. A bound node says which method `b` is, what
//! type each argument has, which conversions the arguments need and what the
//! call produces. Roslyn draws the line in the same place, and for the same
//! reason: everything downstream — lowering, flow analysis, emit — would
//! otherwise have to re-answer those questions, and would not always agree.
//!
//! Two properties are worth stating, because the rest of the crate depends on
//! them. Every bound node carries its type and the span it came from, so a
//! backend never needs the syntax again. And binding never fails: a construct
//! that does not bind becomes [`BoundExpressionKind::Error`], and one that is
//! not modelled yet becomes [`BoundExpressionKind::Unsupported`], which is a
//! different thing and says so.

use rustlyn_syntax::SyntaxKind;
use rustlyn_text::TextSpan;

use crate::conversions::BinaryOperator;
use crate::symbol::{RefKind, SymbolId};
use crate::types::Type;

/// A local variable's identity inside one bound body.
///
/// Locals are not in the compilation's symbol table: they come into existence
/// while a body is being bound and mean nothing outside it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct LocalId(pub u32);

#[derive(Clone, Debug)]
pub struct LocalSymbol {
    pub name: String,
    pub ty: Type,
    pub span: TextSpan,
    /// Whether the slot holds the *address* of a value rather than the value.
    ///
    /// `ref var entry = ref entries[i];` gives a name to a place, not to a
    /// copy: reading it dereferences, and writing through it writes where it
    /// points. Its type here is what it points at; the `&` is this flag.
    pub by_ref: bool,
    /// `ref readonly`: nothing is written through the reference, and a
    /// member that may write is called on a copy of what it refers to.
    pub readonly_ref: bool,
    /// A variable the code may read and not assign, which is what a
    /// `using` or a `foreach` declares (§13.14, §13.9.5). A member called
    /// on it may still write it, as on any local, but a struct in a field
    /// of it is only read: a member that may write is called on a copy
    /// (Roslyn's `NeedsByValueFieldAccess`).
    pub readonly: bool,
}

/// A value known at compile time.
#[derive(Clone, PartialEq, Debug)]
pub enum ConstantValue {
    Null,
    Boolean(bool),
    Char(char),
    Int32(i32),
    UInt32(u32),
    Int64(i64),
    UInt64(u64),
    Single(f32),
    Double(f64),
    String(String),
}

/// A `decimal` or `DateTime` constant: neither is a CLR primitive, so
/// metadata keeps one in an attribute rather than in a `Constant` row — a
/// `[DecimalConstant(scale, sign, hi, mid, lo)]` on a `const decimal` field
/// or an optional `decimal` parameter, a `[DateTimeConstant(ticks)]` on an
/// optional `DateTime` one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpecialConstant {
    Decimal {
        scale: u8,
        negative: bool,
        hi: u32,
        mid: u32,
        lo: u32,
    },
    DateTime(i64),
}

/// An attribute written on a declaration, bound: the constructor it calls,
/// what it was given, and the fields or properties it sets by name (§22.3).
#[derive(Clone, Debug)]
pub struct BoundAttribute {
    pub ty: Type,
    /// `None` where no constructor took the arguments.
    pub constructor: Option<SymbolId>,
    pub arguments: Vec<BoundExpression>,
    pub named: Vec<(SymbolId, BoundExpression)>,
}

/// An operator with one operand, after the binder has decided what it means.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnaryOperator {
    Plus,
    Minus,
    BitwiseNot,
    LogicalNot,
}

/// `++` and `--`, which read and write their operand.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IncrementOperator {
    Increment,
    Decrement,
}

/// Why a conversion is there, which is what decides the instructions it needs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConversionKind {
    /// No instructions: the value already has the target's representation.
    Identity,
    /// `int` to `long`, `int` to `double` and the rest of §10.2.3.
    Numeric,
    /// A value type to `object` or to an interface.
    Boxing,
    /// `object` back to a value type, which is checked at run time.
    Unboxing,
    /// Up a reference type's inheritance chain, which needs nothing.
    ImplicitReference,
    /// Down it, which is checked at run time.
    ExplicitReference,
    /// `T` into a `T?`, which makes one holding the value.
    NullableWrap,
    /// A `T?` back to a `T`, which the language only allows with a cast and
    /// which throws where there is nothing in it.
    NullableUnwrap,
    /// `byte?` into an `int?`: what is inside converts, and a null stays one.
    NullableLift,
    /// `(ImmutableArray<A>, ImmutableArray<B>)` into `(IEnumerable<A>,
    /// IEnumerable<B>)`: a tuple is converted element by element into a new
    /// one (§10.2.13), which is a conversion per element and a construction.
    TupleElements,
}

/// The pattern `await` is made of (§12.9.8.2): the `GetAwaiter()` of the
/// operand, and the `IsCompleted` and `GetResult()` of what it gives back.
///
/// Each member is kept with the type it was found through, since that is the
/// construction it is called on: `Task<int>.GetAwaiter()` is a member of
/// `Task<int>`, and `TaskAwaiter<int>.GetResult()` one of `TaskAwaiter<int>`.
#[derive(Clone, Debug)]
pub struct BoundAwaiting {
    pub get_awaiter: SymbolId,
    pub get_awaiter_type: Type,
    /// What `GetAwaiter()` gives back: the type the machine keeps while it
    /// waits.
    pub awaiter: Type,
    pub is_completed: SymbolId,
    pub is_completed_type: Type,
    pub get_result: SymbolId,
    pub get_result_type: Type,
    /// Set where `GetAwaiter` is an extension method (§12.9.8.2): what its
    /// own type parameters are at this `await`, and the type of its `this`
    /// parameter, which the operand is handed over as — a struct boxed
    /// where that is an interface or `object`.
    pub extension: Option<(Vec<Type>, Type)>,
}

/// An expression, bound.
#[derive(Clone, Debug)]
pub struct BoundExpression {
    pub kind: BoundExpressionKind,
    pub ty: Type,
    pub span: TextSpan,
    /// What folding this expression came to, with the type it was folded
    /// as: kept so that an operator over a long chain of constants is not
    /// worked out again, from the leaves up, at every operator above it.
    /// Only the folder reads or writes it.
    /// Boxed: most expressions are never folded, and each one carries this.
    pub(crate) folded: std::sync::OnceLock<Box<(Type, Option<ConstantValue>)>>,
}

impl BoundExpression {
    #[must_use]
    pub const fn new(kind: BoundExpressionKind, ty: Type, span: TextSpan) -> Self {
        Self {
            kind,
            ty,
            span,
            folded: std::sync::OnceLock::new(),
        }
    }

    #[must_use]
    pub const fn error(span: TextSpan) -> Self {
        Self::new(BoundExpressionKind::Error, Type::Error, span)
    }

    #[must_use]
    pub const fn is_error(&self) -> bool {
        matches!(self.kind, BoundExpressionKind::Error)
    }

    /// The constant this expression is, if it is one.
    #[must_use]
    pub const fn constant(&self) -> Option<&ConstantValue> {
        match &self.kind {
            BoundExpressionKind::Literal(value) => Some(value),
            _ => None,
        }
    }

    /// Whether this is an interpolated string not yet given a type, or an
    /// addition of nothing but those: `$"a" + ($"b" + $"c")` is one to a
    /// handler (C# 10), which takes all three.
    #[must_use]
    pub fn is_interpolated_string(&self) -> bool {
        match &self.kind {
            BoundExpressionKind::InterpolatedString(_) => true,
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Add,
                left,
                right,
                // The right first: in a long `a + b + c` it is the leaf, and the
                // chain is turned down without walking all of it at every `+`.
            } => right.is_interpolated_string() && left.is_interpolated_string(),
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum BoundExpressionKind {
    /// The expression did not bind. A diagnostic has already been reported for
    /// it, and nothing further should be said about it.
    Error,
    /// The expression is well formed but this binder does not model it yet —
    /// a lambda, a query, a pattern. The syntax kind is kept so that a backend
    /// can say exactly what it met.
    Unsupported(SyntaxKind),
    Literal(ConstantValue),
    Local(LocalId),
    Parameter(SymbolId),
    This,
    Base,
    /// A type used where a value would go, which only a member access can do
    /// anything with: the `Console` of `Console.WriteLine`.
    TypeExpression(SymbolId),
    /// Likewise for a namespace: the `System` of `System.Console`.
    NamespaceExpression(SymbolId),
    Field {
        receiver: Option<Box<BoundExpression>>,
        field: SymbolId,
    },
    Property {
        receiver: Option<Box<BoundExpression>>,
        property: SymbolId,
    },
    /// A method name used as a value, before anything has said which
    /// overload it is. C# gives a method group no type of its own: it is only
    /// a value once it is converted to a delegate, and which overload it means
    /// depends on the delegate.
    MethodGroup {
        receiver: Option<Box<BoundExpression>>,
        candidates: Vec<SymbolId>,
    },
    /// A lambda whose body has not been bound, because nothing has said yet
    /// what its parameters are.
    ///
    /// `x => x * 2` cannot be bound on sight: what `x` is comes from the
    /// delegate it is converted to, and until then there is nothing to bind
    /// against. The span is where to find the syntax again.
    UnboundLambda(TextSpan),
    /// `[a, b, ..rest]` before anything has said what collection it is.
    ///
    /// Like a lambda, it has no type of its own: `[]` is an array, a list or
    /// an immutable array depending only on what it is being converted to.
    /// The span is where to find the syntax again.
    UnboundCollection(TextSpan),
    /// `new(a, b)` before anything has said what is being made.
    ///
    /// The type is not written, so there is none until the thing it is being
    /// given to says. The span is where to find the syntax again.
    UnboundCreation(TextSpan),
    /// `flag ? a => a + 1 : a => a - 1` before anything has said what it is.
    ///
    /// Neither branch has a type of its own, so neither can give one to the
    /// conditional; §12.18 says what it is converted to types both of them.
    /// The span is where to find the syntax again.
    UnboundConditional(TextSpan),
    /// A `switch` expression whose arms cannot say what it is either.
    UnboundSwitch(TextSpan),
    /// A lambda, bound against the delegate it became. The index is into the
    /// body's own list of them, because a backend has to plan a method for
    /// every lambda before it emits any of them.
    Lambda(usize),
    /// `__arglist(a, b)`: what a call gives a varargs method past its
    /// parameters, each passed as the type it has.
    ArgList(Vec<BoundExpression>),
    /// `__arglist` alone, in a varargs method: the `RuntimeArgumentHandle`
    /// over what it was given.
    ArgListHandle,
    /// `ref x` or `out x` at a call: what is passed is the variable, not what
    /// it holds. Its type stays the variable's, because that is what overload
    /// resolution compares; the reference is in the kind.
    RefArgument {
        kind: RefKind,
        operand: Box<BoundExpression>,
    },
    /// `new Op(Square)`, and every method group that reached a delegate.
    DelegateCreation {
        /// The method the delegate will call.
        method: SymbolId,
        /// What to call it on, for an instance method.
        receiver: Option<Box<BoundExpression>>,
        /// Whether the target is looked up on the receiver's run-time type.
        virtual_dispatch: bool,
        /// The method's own type arguments, where it is generic and the
        /// delegate said what they are: `Skip<T>` handed to a `Skipper<int>`.
        type_arguments: Vec<Type>,
    },
    Call {
        receiver: Option<Box<BoundExpression>>,
        method: SymbolId,
        /// What a generic method's type parameters stand for at this call, in
        /// declaration order; empty for an ordinary method. `Echo(3)` writes
        /// none and this still holds `int`: inference happened at binding, and
        /// a `MethodSpec` needs the answer.
        type_arguments: Vec<Type>,
        arguments: Vec<BoundExpression>,
        /// Whether the call goes through the receiver's run-time type. `base.M()`
        /// is a virtual method called non-virtually, so the method's own
        /// modifiers are not enough to decide this.
        virtual_call: bool,
    },
    ObjectCreation {
        constructor: Option<SymbolId>,
        arguments: Vec<BoundExpression>,
        /// What an object or collection initializer does to it, once it
        /// exists: assignments to its members and calls to its `Add`, each
        /// written against [`CreatedObject`](Self::CreatedObject).
        initializers: Vec<BoundExpression>,
    },
    /// `info with { Receiver = null }`: a copy of the receiver with those
    /// members set, each written against [`CreatedObject`](Self::CreatedObject)
    /// the way an object initializer writes them (§12.8.17).
    ///
    /// A struct or a tuple is copied by being loaded; a record class copies
    /// itself through the `<Clone>$` the language gives it.
    With {
        receiver: Box<BoundExpression>,
        initializers: Vec<BoundExpression>,
    },
    /// `await e`, whose value is what `e.GetAwaiter().GetResult()` gives
    /// back.
    ///
    /// The state machine that makes the waiting real is a backend's job and
    /// is not written yet; binding it is what makes the names around it — and
    /// the type of the expression itself — resolve.
    /// `(a, b)`: a `ValueTuple` made of the values, in order. The element
    /// names are on the type rather than here, because the runtime never sees
    /// them.
    TupleCreation(Vec<BoundExpression>),
    /// `sizeof(T)`: how many bytes a `T` takes, which for anything but the
    /// types the language names only the runtime knows.
    SizeOf(Type),
    /// `*p`: what a pointer points at, which is a place as much as a value.
    Dereference {
        operand: Box<BoundExpression>,
    },
    /// `&x`: where a variable is, as an unmanaged pointer.
    ///
    /// Written over a method group, `&M` has no type until it is given to a
    /// function pointer, which says which overload it is; then it is a
    /// [`BoundExpressionKind::MethodAddress`].
    AddressOf {
        operand: Box<BoundExpression>,
    },
    /// `&M` given to a `delegate*`: the address of one static method, which
    /// `ldftn` loads.
    MethodAddress {
        method: SymbolId,
        type_arguments: Vec<Type>,
    },
    /// `__makeref(x)`: a `TypedReference` to the variable `x`, carrying its
    /// type.
    MakeRef(Box<BoundExpression>),
    /// `__refvalue(r, T)`: the variable a `TypedReference` refers to, as the
    /// `T` the expression's type says; a variable, so it can be written.
    RefValue(Box<BoundExpression>),
    /// `__reftype(r)`: the `Type` of what a `TypedReference` refers to.
    RefType(Box<BoundExpression>),
    /// `f(a, b)` where `f` is a function pointer: `calli` with the pointer's
    /// signature. The arguments are converted to its parameters already.
    FunctionPointerCall {
        pointer: Box<BoundExpression>,
        arguments: Vec<BoundExpression>,
    },
    /// `stackalloc T[n]` and `stackalloc T[] { ... }`: memory on the stack,
    /// as a `T*`, or as the `Span<T>` it was given to where `span` says so.
    StackAlloc {
        element: Type,
        count: Box<BoundExpression>,
        elements: Vec<BoundExpression>,
        span: Option<Type>,
    },
    /// `x ?? throw new E()`: it throws instead of producing a value, so it
    /// fits wherever a value was wanted and has no type of its own.
    Throw(Option<Box<BoundExpression>>),
    Await {
        operand: Box<BoundExpression>,
        /// How the waiting is done, where the operand's type says: `None`
        /// where the operand is `dynamic`, and the runtime binder finds the
        /// members as it runs (the `await` is `dynamic` too), or where it
        /// has no `GetAwaiter` and the `await` was reported.
        awaiting: Option<Box<BoundAwaiting>>,
    },
    /// `a?.B`: the receiver, and what is done to it when it is not null.
    ///
    /// The whole expression is null when the receiver is — that is the point
    /// — and the access inside is written against
    /// [`AccessedValue`](Self::AccessedValue), which is the receiver once it
    /// is known not to be null.
    ConditionalAccess {
        receiver: Box<BoundExpression>,
        access: Box<BoundExpression>,
    },
    /// The receiver of the `?.` being evaluated, once it is known not to be
    /// null. Roslyn calls it a conditional receiver.
    AccessedValue,
    /// The object an initializer is initializing.
    ///
    /// `new Point { X = 1 }` has nowhere to put the new object between making
    /// it and setting `X`, and no name for it either. Roslyn calls this a
    /// placeholder; a backend answers it with whatever it already has — the
    /// value on the stack, or the object it just made.
    CreatedObject,
    ArrayCreation {
        element: Type,
        /// One per dimension; empty when only an initializer was written.
        lengths: Vec<BoundExpression>,
        elements: Vec<BoundExpression>,
    },
    ArrayAccess {
        array: Box<BoundExpression>,
        indices: Vec<BoundExpression>,
    },
    /// `a.Length`, which is an instruction rather than a member.
    ArrayLength {
        array: Box<BoundExpression>,
    },
    /// An indexer, which is a property with arguments.
    IndexerAccess {
        receiver: Box<BoundExpression>,
        indexer: SymbolId,
        arguments: Vec<BoundExpression>,
    },
    Binary {
        operator: BinaryOperator,
        left: Box<BoundExpression>,
        right: Box<BoundExpression>,
    },
    Unary {
        operator: UnaryOperator,
        operand: Box<BoundExpression>,
    },
    Conditional {
        condition: Box<BoundExpression>,
        consequence: Box<BoundExpression>,
        alternative: Box<BoundExpression>,
    },
    Assignment {
        target: Box<BoundExpression>,
        value: Box<BoundExpression>,
    },
    /// `x.E += h` or `x.E -= h` on an event reached through its accessors:
    /// the `add_E` or `remove_E` call the language makes of it (§12.21.5).
    EventAssignment {
        receiver: Option<Box<BoundExpression>>,
        event: SymbolId,
        add: bool,
        handler: Box<BoundExpression>,
    },
    /// Several expressions in order, for the places where C# means one thing
    /// and it takes more than one: taking a tuple apart writes a variable per
    /// element, and there is no single expression that does it.
    Sequence(Vec<BoundExpression>),
    /// Statements run where an expression stands, and then the value: what
    /// a loop inside an expression becomes. `[..items]` filled through `Add`
    /// walks `items` right there, and a walk is a `foreach`.
    ///
    /// Roslyn calls it a spill sequence. Nothing may be on the evaluation
    /// stack while statements run — a `try` needs it empty — so a backend
    /// moves the statements ahead of the statement that holds them, keeping
    /// in temporaries whatever was evaluated before them, and leaves the
    /// value where the sequence was.
    SpillSequence {
        statements: Vec<BoundStatement>,
        value: Box<BoundExpression>,
    },
    CompoundAssignment {
        target: Box<BoundExpression>,
        operator: BinaryOperator,
        value: Box<BoundExpression>,
    },
    Increment {
        target: Box<BoundExpression>,
        operator: IncrementOperator,
        /// Whether the value of the expression is the one after the change.
        prefix: bool,
        /// The `op_Increment` or `op_Decrement` the operand's type declares,
        /// which is called rather than adding one (§12.9.6).
        method: Option<SymbolId>,
    },
    Conversion {
        operand: Box<BoundExpression>,
        conversion: ConversionKind,
        /// Whether the source wrote the cast.
        ///
        /// A conversion the binder inserted says what was *asked for*, and
        /// inferring a lambda's return type has to look past it; a cast the
        /// program wrote is what the lambda gives, and looking past that
        /// would infer `object` from `(string)o`.
        written: bool,
    },
    /// `$"a{b}"` before anything has said what it becomes: the pieces in
    /// order, the text already the string constants it stands for.
    ///
    /// Like a lambda, it is not finished until it is given to something
    /// (§12.8.3): a `FormattableString` keeps the holes apart from the text,
    /// an interpolated string handler (C# 10) is made and appended to piece
    /// by piece, and a `string` is joined the way Roslyn joins it — folded,
    /// `string.Concat`, `DefaultInterpolatedStringHandler` or `string.Format`.
    /// The binder decides all of that once the body is bound, so a backend
    /// meets this only where nothing lowered it: inside an expression tree,
    /// which describes it as the `string.Format` it means.
    ///
    /// `$"a" + $"b"` is still one of these to its conversions: a `Binary`
    /// addition of nothing but interpolated strings, which a handler takes
    /// whole.
    ///
    /// Each piece is a string [`Literal`](Self::Literal) of text or a
    /// [`StringInsert`](Self::StringInsert): `$"{"a"}"` holds a hole whose
    /// value is a constant, and a handler appends it as a value, not as
    /// text.
    InterpolatedString(Vec<BoundExpression>),
    /// `{value,5:N2}` inside an interpolated string: the value, as it is on
    /// its own, and how it is to be written (Roslyn's `BoundStringInsert`).
    /// A handler's `AppendFormatted` is handed the clauses as arguments of
    /// their own; `string.Format` reads them out of its composite format, as
    /// [`composite_clauses`] writes them. Its type is the value's.
    StringInsert {
        value: Box<BoundExpression>,
        /// `,5`: the width, negative to pad on the right.
        alignment: Option<i32>,
        /// `:N2`: the format, without its colon.
        format: Option<String>,
    },
    /// `x is T`, which produces a `bool`.
    TypeTest {
        operand: Box<BoundExpression>,
        target: Type,
    },
    /// `x is <pattern>`, which also produces a `bool` and may bind names.
    IsPattern {
        operand: Box<BoundExpression>,
        pattern: Box<BoundPattern>,
    },
    /// `x switch { ... }`
    Switch {
        governing: Box<BoundExpression>,
        arms: Vec<BoundSwitchArm>,
    },
    /// `x as T`, which produces `null` rather than throwing.
    TryCast {
        operand: Box<BoundExpression>,
        target: Type,
    },
    /// `typeof(T)`.
    TypeOf(Type),
    /// `default(T)` and a bare `default`.
    Default(Type),
    /// An operation on a `dynamic` value, which the runtime binds when the
    /// program runs (§12.3.3).
    Dynamic(Box<BoundDynamic>),
}

/// The clauses of a hole as a composite format string writes them after
/// the hole's number: `,5:N2` for `{value,5:N2}`.
#[must_use]
pub fn composite_clauses(alignment: Option<i32>, format: Option<&str>) -> String {
    let mut clauses = String::new();
    if let Some(alignment) = alignment {
        clauses.push(',');
        clauses.push_str(&alignment.to_string());
    }
    if let Some(format) = format {
        clauses.push(':');
        clauses.push_str(format);
    }
    clauses
}

/// An operation bound at run time: what was written, kept for the runtime
/// binder to decide what it means once it sees the values (§12.3.3).
///
/// As the target of an assignment, a `GetMember` or `GetIndex` is the member
/// or element written rather than read.
#[derive(Clone, Debug)]
pub struct BoundDynamic {
    pub operation: DynamicOperation,
    /// What the operation is on: the receiver of a member access or a call,
    /// the callee of `d(...)`, the operand of an operator or a conversion.
    /// A `TypeExpression` where a static member is reached through its type:
    /// `Console.WriteLine(d)`.
    pub receiver: Option<BoundExpression>,
    /// The arguments, in the order written, `ref` and `out` ones as
    /// `RefArgument`s.
    pub arguments: Vec<BoundExpression>,
    /// The name each argument was given, where it was given one.
    pub names: Vec<Option<String>>,
}

/// Which of the runtime binder's operations a [`BoundDynamic`] is.
#[derive(Clone, Debug)]
pub enum DynamicOperation {
    /// `receiver.name<type_arguments>(arguments)`. `simple_name` says the
    /// call was written without a receiver, on an implicit `this`.
    InvokeMember {
        name: String,
        type_arguments: Vec<Type>,
        simple_name: bool,
    },
    /// `receiver.name`.
    GetMember(String),
    /// `receiver[arguments]`.
    GetIndex,
    /// `receiver(arguments)`: a call of what a `dynamic` value holds.
    Invoke,
    /// `new T(arguments)`, where `T` is the expression's type.
    InvokeConstructor,
    /// `receiver op arguments[0]`. `compound` says it is the operation of
    /// `x op= y`, which the runtime binder is told.
    Binary {
        operator: BinaryOperator,
        compound: bool,
    },
    /// `op receiver`.
    Unary(DynamicUnary),
    /// The receiver converted to the expression's type.
    Convert { explicit: bool },
}

/// The unary operations the runtime binder knows.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DynamicUnary {
    Plus,
    Minus,
    BitwiseNot,
    LogicalNot,
    Increment,
    Decrement,
    /// Whether a value is true, which is how `if (d)` and `d && e` ask.
    IsTrue,
    IsFalse,
}

/// A pattern, bound.
///
/// A pattern is a test and a set of bindings at once, and the two are not
/// separable: `o is Shape s` tests and names in one step, and the name is only
/// in scope where the test succeeded. Keeping them in one node is what lets a
/// backend emit the test and the store together rather than guess which store
/// belongs to which test.
#[derive(Clone, Debug)]
pub struct BoundPattern {
    pub kind: BoundPatternKind,
    pub span: TextSpan,
}

impl BoundPattern {
    #[must_use]
    pub const fn new(kind: BoundPatternKind, span: TextSpan) -> Self {
        Self { kind, span }
    }
}

#[derive(Clone, Debug)]
pub enum BoundPatternKind {
    /// A pattern this binder does not model yet: positional, property, list.
    /// Its variables are still declared, so names inside it resolve.
    Unsupported(SyntaxKind),
    /// `_`, which matches anything and binds nothing.
    Discard,
    /// `var x`, which matches anything and names it.
    Var {
        local: LocalId,
    },
    /// `var (a, b)`, which matches anything with something in it and takes
    /// that apart: the value goes into `local`, of type `ty`, and the
    /// deconstruction reads it from there.
    VarDeconstruct {
        ty: Type,
        local: LocalId,
        deconstruction: Box<BoundExpression>,
    },
    /// `string`, which is a type test and nothing else.
    Type(Type),
    /// `string s`: a type test that names what it matched.
    Declaration {
        ty: Type,
        local: Option<LocalId>,
    },
    /// `1`, `null`, `Kind.Red`.
    Constant(BoundExpression),
    /// `"str"` matched against a `Span<char>` or a `ReadOnlySpan<char>`
    /// (C# 11): the value goes into `local`, and `test` — a call to
    /// `MemoryExtensions.SequenceEqual` over it and the string's `AsSpan()`
    /// — has to say yes.
    SpanString {
        local: LocalId,
        test: Box<BoundExpression>,
    },
    /// `> 3`
    Relational {
        operator: BinaryOperator,
        value: BoundExpression,
    },
    /// `Shape { Width: > 2 }` and `p is (1, var b)`: a type test, then a
    /// pattern per member read or per part taken out.
    ///
    /// Boxed because it is far larger than every other pattern beside it.
    Recursive(Box<BoundRecursivePattern>),
    /// `[1, var x, ..]`: a length test, then a pattern per element.
    ///
    /// Boxed for the same reason a recursive pattern is: it is much larger
    /// than anything else this enum holds.
    List(Box<BoundListPattern>),
    And(Box<BoundPattern>, Box<BoundPattern>),
    Or(Box<BoundPattern>, Box<BoundPattern>),
    Not(Box<BoundPattern>),
    /// A pattern applied to what a union holds, reached through its
    /// `TryGetValue(out T)` (C# 15): the call has to say yes, and the
    /// pattern is then matched against the `T` it gave. A union read
    /// through its `Value` is a property pattern instead.
    UnionCase {
        try_get_value: SymbolId,
        ty: Type,
        inner: Box<BoundPattern>,
    },
}

/// What a recursive pattern tests, in the order it tests it.
#[derive(Clone, Debug)]
pub struct BoundRecursivePattern {
    /// The type written in front, where one was: `Circle { R: 1 }` checks the
    /// type before it looks at anything inside.
    pub ty: Option<Type>,
    /// `{ X: p }`: the member to read, and the pattern its value has to match.
    pub properties: Vec<(SymbolId, BoundPattern)>,
    /// `(p, q)`: what takes the value apart. A tuple has nothing to call —
    /// its parts are its own fields — so this is `None` and the patterns
    /// still stand.
    pub deconstruct: Option<SymbolId>,
    pub positional: Vec<BoundPattern>,
    /// `Circle c { ... }`, which names what matched.
    pub local: Option<LocalId>,
}

/// What a list pattern tests, in the order it tests it.
///
/// `[a, b, .., y, z]` is a length of at least four, then the first two
/// elements against `a` and `b`, then the last two against `y` and `z`. With
/// no `..` the length has to be exactly what was listed.
#[derive(Clone, Debug)]
pub struct BoundListPattern {
    /// How many elements there are: `Length` or `Count`, or nothing at all
    /// where the value is an array and the instruction says.
    pub length: Option<SymbolId>,
    /// How one is read, where the value is not an array.
    pub indexer: Option<SymbolId>,
    /// What the type the elements are read on is, which the accessors above
    /// are members of.
    pub matched: Type,
    pub element: Type,
    /// The patterns written before a `..`, and the ones written after it.
    pub before: Vec<BoundPattern>,
    pub after: Vec<BoundPattern>,
    /// Whether a `..` was written at all.
    pub slice: bool,
    /// The `Index` each element is read with, those before the `..` and
    /// then those after it, where the indexer takes an `Index` — a real
    /// `this[Index]` is preferred to the implicit support a `this[int]`
    /// gives (C# 11) — `0`, `1`, ..., `^2`, `^1`. Empty where it takes an
    /// `int` and the backend counts.
    pub indexes: Vec<BoundExpression>,
    /// `.. p`: the slice cut out and the pattern it has to match.
    pub slice_pattern: Option<Box<BoundListSlice>>,
    /// `[...] all`, which names what matched.
    pub local: Option<LocalId>,
}

impl BoundListPattern {
    /// The patterns inside, in the order they are tested: those before the
    /// `..`, the slice's, and those after it.
    pub fn patterns(&self) -> impl Iterator<Item = &BoundPattern> {
        self.before
            .iter()
            .chain(self.slice_pattern.iter().map(|slice| &slice.pattern))
            .chain(&self.after)
    }
}

/// `.. p` in a list pattern: what the slice is, and what it has to match.
#[derive(Clone, Debug)]
pub struct BoundListSlice {
    /// The locals the slice is cut from — the value being matched, and how
    /// many elements it has — which a backend stores before it evaluates
    /// `value`.
    pub list: LocalId,
    pub count: LocalId,
    /// `RuntimeHelpers.GetSubArray(list, start..^end)` on an array,
    /// `list[start..^end]` through an indexer taking a `Range`, or else
    /// `list.Slice(start, count - start - end)` (`Substring` on a string).
    pub value: BoundExpression,
    pub pattern: BoundPattern,
}

/// One arm of a switch expression.
#[derive(Clone, Debug)]
pub struct BoundSwitchArm {
    pub pattern: BoundPattern,
    /// The `when` clause, which runs only where the pattern matched and so
    /// may read the variables it bound.
    pub when: Option<BoundExpression>,
    pub value: BoundExpression,
}

/// One label of a switch section: `case <pattern>:` or `default:`.
#[derive(Clone, Debug)]
pub enum BoundSwitchLabel {
    /// Boxed because a pattern and a `when` clause together are far larger
    /// than the `default` label they sit beside.
    Case(Box<BoundCaseLabel>),
    Default,
}

#[derive(Clone, Debug)]
pub struct BoundCaseLabel {
    pub pattern: BoundPattern,
    pub when: Option<BoundExpression>,
}

/// One resource a `using` holds and then disposes.
#[derive(Clone, Debug)]
pub struct BoundUsingResource {
    /// The local the resource lives in. A `using (Open())` with no name still
    /// gets one, because the value has to be kept until the end.
    pub local: LocalId,
    pub value: BoundExpression,
    /// The `Dispose` to call, when one was found.
    pub dispose: Option<SymbolId>,
    /// How an `await using` disposes of the resource: the statement its
    /// `finally` runs, `if (r != null) await r.DisposeAsync();`, with the
    /// test left out for a struct and made `HasValue` for a `T?`.
    ///
    /// A `DisposeAsync` the type has is preferred to the one of
    /// `IAsyncDisposable` it implements, and may take optional arguments
    /// (§13.14), so which one it is and what it is given are settled here; a
    /// state machine only puts the statement in a `finally` and takes its
    /// `await` apart. `None` for a plain `using`, which calls `dispose`, and
    /// for the `dynamic` resource of an `await using`, which is disposed as
    /// the `IAsyncDisposable` held in the resource after it.
    pub awaited: Option<Box<BoundStatement>>,
}

/// What `foreach` needs to walk something that is not an array.
///
/// C# does not require the collection to implement `IEnumerable`: it looks for
/// `GetEnumerator`, then `MoveNext` and `Current` on what that returns, by
/// name. Roslyn calls this the enumerator info, and works it out once at
/// binding — which is the point, because a backend that had to look again
/// might not find the same members.
#[derive(Clone, Debug)]
pub struct BoundEnumeration {
    /// The local the enumerator is kept in.
    pub enumerator: LocalId,
    /// The type `GetEnumerator` is called through: the collection's own, or an
    /// interface it implements when the type declares no such method.
    pub collection_type: Type,
    pub get_enumerator: SymbolId,
    /// What `GetEnumerator` returned, constructed. This is what the
    /// enumerator local holds.
    pub enumerator_type: Type,
    pub move_next: SymbolId,
    /// The type `MoveNext` is called through, which is not always the
    /// enumerator's own: `IEnumerator<T>` inherits it from the non-generic
    /// `IEnumerator`, and a call has to name the type that declares it.
    pub move_next_type: Type,
    pub current: SymbolId,
    /// The type `Current` is read through, for the same reason.
    pub current_type: Type,
    /// What `Current` yields, constructed: a `ref readonly char` from
    /// `ReadOnlySpan<char>.Enumerator` is read as the `char` it refers to.
    pub element_type: Type,
    /// `Dispose`, where the enumerator is disposed: C# disposes an
    /// enumerator that is an `IDisposable` through the interface, however
    /// the loop is left, and a `ref struct`, which cannot be one, through a
    /// `Dispose` of its own (C# 8).
    pub dispose: Option<SymbolId>,
    /// What a `ref struct`'s own `Dispose` is given: the defaults of the
    /// optional parameters it has (Roslyn's `PatternDisposeInfo`).
    pub dispose_arguments: Vec<BoundExpression>,
    /// Whether the enumerator's type does not promise `Dispose` but a value
    /// of it may still have one (§13.9.5: a non-sealed class or an
    /// interface): `dispose` is then `IDisposable.Dispose`, called only
    /// where the value turns out to be one.
    pub dispose_checked: bool,
    /// The type `Dispose` is called through: `IDisposable`, or the `ref
    /// struct` itself.
    pub dispose_type: Option<Type>,
    /// Set where `GetEnumerator` is an extension method (C# 9): the type
    /// arguments the call instantiates it with, empty for a non-generic one.
    /// The collection is then its first argument rather than its receiver.
    pub extension: Option<Vec<Type>>,
    /// For an extension `GetEnumerator`: the type of its `this` parameter,
    /// which the collection converts to (a struct is boxed on its way to an
    /// `object` one), and the arguments after it — the defaults of optional
    /// parameters and the empty array of a `params` one.
    pub extension_this: Type,
    pub extension_arguments: Vec<BoundExpression>,
}

/// One `catch` clause.
#[derive(Clone, Debug)]
pub struct BoundCatch {
    /// What it catches. A bare `catch` catches `System.Exception`.
    pub exception_type: Type,
    /// The name it gives the exception, where it gives one.
    pub local: Option<LocalId>,
    /// A `when` clause, which the runtime evaluates before unwinding.
    pub filter: Option<BoundExpression>,
    pub body: BoundStatement,
}

/// One section of a switch statement: its labels and the statements they
/// share.
#[derive(Clone, Debug)]
pub struct BoundSwitchSection {
    pub labels: Vec<BoundSwitchLabel>,
    pub statements: Vec<BoundStatement>,
}

/// A statement, bound.
#[derive(Clone, Debug)]
pub struct BoundStatement {
    pub kind: BoundStatementKind,
    pub span: TextSpan,
}

impl BoundStatement {
    #[must_use]
    pub const fn new(kind: BoundStatementKind, span: TextSpan) -> Self {
        Self { kind, span }
    }
}

#[derive(Clone, Debug)]
pub enum BoundStatementKind {
    /// A statement this binder does not model yet: `switch`, `try`, `using`,
    /// `yield`. Its sub-expressions are still bound, so names inside it
    /// resolve; it is the control flow that is missing.
    Unsupported(SyntaxKind),
    Block(Vec<BoundStatement>),
    /// One declarator. `int a = 1, b = 2;` is two of these.
    LocalDeclaration {
        local: LocalId,
        initializer: Option<BoundExpression>,
    },
    Expression(BoundExpression),
    If {
        condition: BoundExpression,
        consequence: Box<BoundStatement>,
        alternative: Option<Box<BoundStatement>>,
    },
    While {
        condition: BoundExpression,
        body: Box<BoundStatement>,
    },
    DoWhile {
        body: Box<BoundStatement>,
        condition: BoundExpression,
    },
    For {
        initializers: Vec<BoundStatement>,
        condition: Option<BoundExpression>,
        incrementors: Vec<BoundExpression>,
        body: Box<BoundStatement>,
    },
    /// The loop variable, what is walked, and the body. Lowering it needs to
    /// know whether the collection is an array or an enumerable, which the
    /// collection's type says.
    ForEach {
        local: LocalId,
        collection: BoundExpression,
        body: Box<BoundStatement>,
        /// How to walk the collection, when it is not an array. An array is
        /// walked by index and needs nothing; anything else is the pattern C#
        /// looks for by name, resolved here so no backend has to look again.
        enumeration: Option<Box<BoundEnumeration>>,
        /// The two variables an array walk needs: what is being walked, and
        /// how far through it. They are declared here rather than made up by
        /// a backend because an iterator hoists every local into a field, and
        /// one it never saw would be left behind in a slot that does not
        /// survive a `yield`.
        walk: Option<(LocalId, LocalId)>,
        /// For an array of more than one dimension, an index and the upper
        /// bound it runs to, per dimension: such an array is walked as the
        /// nested loops Roslyn writes, not through `IEnumerable`, which
        /// would box every element (and cannot box a pointer at all).
        dimensions: Vec<(LocalId, LocalId)>,
    },
    /// `: base(...)` or `: this(...)`, which a constructor runs before its
    /// own body. It is a statement of its own rather than a call, because a
    /// constructor that does not write one still has to run one.
    ConstructorInitializer {
        constructor: Option<SymbolId>,
        arguments: Vec<BoundExpression>,
        /// Whether it chains to another constructor of the same type.
        chains_to_this: bool,
    },
    Switch {
        governing: BoundExpression,
        sections: Vec<BoundSwitchSection>,
    },
    Try {
        body: Box<BoundStatement>,
        catches: Vec<BoundCatch>,
        finally: Option<Box<BoundStatement>>,
    },
    /// `using`, in both the statement and the declaration form. The two mean
    /// the same thing — a resource held for a scope and disposed when it
    /// ends — so they become the same node, and where the scope ends is
    /// settled here rather than by each backend. An `await using` is the
    /// same node with each resource's [`awaited`](BoundUsingResource::awaited)
    /// disposal.
    Using {
        resources: Vec<BoundUsingResource>,
        body: Box<BoundStatement>,
    },
    /// `lock (o) { ... }`, which is a `try`/`finally` around
    /// `Monitor.Enter`/`Monitor.Exit`. The two locals are the compiler's: one
    /// holds what was locked, so the `finally` unlocks the same object even if
    /// the expression would now say something else, and one records whether
    /// the lock was actually taken.
    Lock {
        value: BoundExpression,
        held: LocalId,
        taken: LocalId,
        body: Box<BoundStatement>,
    },
    /// `fixed (T* p = e) body`: each declaration pins what `e` names for as
    /// long as the body runs, and `p` points into it.
    Fixed {
        declarations: Vec<BoundStatement>,
        body: Box<BoundStatement>,
    },
    Return(Option<BoundExpression>),
    /// `yield return e;` — the next value the iterator hands out, and where
    /// it carries on from when it is asked for another.
    YieldReturn(BoundExpression),
    /// `yield break;` — there are no more.
    YieldBreak,
    /// `break;`, or `break outer;` out of a labeled loop or `switch` further
    /// out: how many of the loops and `switch` statements around it the jump
    /// passes over before reaching the one it leaves (`0` is the innermost).
    Break(usize),
    /// `continue;`, or `continue outer;`: how many of the loops around it
    /// the jump passes over (`switch` statements do not count).
    Continue(usize),
    /// `goto case 3;` and `goto default;`: a jump to another section of the
    /// switch this sits in, carrying on from there rather than falling out.
    /// The label is named by the constant and the type it is tested in (see
    /// `Binder::case_key`); `None` is the `default` label.
    GotoCase(Option<(Type, ConstantValue)>),
    /// `Again:` — a name a `goto` in the same body can jump to.
    Label(String),
    /// `goto Again;`
    Goto(String),
    Throw(Option<BoundExpression>),
    /// `;`
    Empty,
}

/// The result of binding one body: the tree, the locals it declares, and the
/// two lookups the semantic model answers questions from.
#[derive(Clone, Debug, Default)]
pub struct BoundBody {
    /// The statements of the body, in order. An expression-bodied member has
    /// one `Return`.
    pub statements: Vec<BoundStatement>,
    pub locals: Vec<LocalSymbol>,
    /// Every lambda in the body, in the order they finished binding — which
    /// puts an inner one before the outer one that holds it. A `Lambda` node
    /// is an index into this.
    pub lambdas: Vec<BoundLambda>,
    /// Every local function in the body, with what it reads of the method
    /// that holds it. Its own locals are on this table too, because its body
    /// is bound here — which is the only way an enclosing local can be in
    /// scope inside it.
    pub local_functions: Vec<BoundLocalFunction>,
    /// The element type, where the body is an iterator.
    ///
    /// A body with a `yield` in it is not the method the source wrote: it is
    /// a state machine, and what the method returns is an instance of it. The
    /// element is what each `yield return` gives — the `T` of the
    /// `IEnumerable<T>` the method was declared to return.
    pub iterator: Option<Type>,
    /// Every `checked` and `unchecked` block or expression in the body, by
    /// its span, with `true` for `checked`. Arithmetic and narrowing inside
    /// the innermost one around it trap on overflow or do not (§12.8.20);
    /// outside any, they do not.
    pub checked_regions: Vec<(TextSpan, bool)>,
    /// Where a `stackalloc` stands inside a larger expression — an argument,
    /// an operand — rather than as a local's whole initializer. `localloc`
    /// wants an empty stack, so a backend makes these ahead of the statement.
    pub nested_stackallocs: Vec<TextSpan>,
    /// The type of each expression, by the span of its syntax.
    pub types: std::collections::HashMap<TextSpan, Type>,
    /// What each name refers to, by the span of its syntax.
    pub references: std::collections::HashMap<TextSpan, BoundSymbol>,
    /// The declared symbol each name in an expression settled on, by the span
    /// of the name's token: the overload a call chose, the field or property
    /// a member access found, the constructor a `new` calls.
    ///
    /// Keyed by the token rather than by the expression, because a name is
    /// what an editor points at: in `a.b.C()` the cursor is on `C`, and the
    /// question is about the method, not the whole call.
    pub symbols: std::collections::HashMap<TextSpan, SymbolId>,
    pub diagnostics: crate::binder::Diagnostics,
}

/// A local function, bound where it was written.
///
/// It differs from a lambda in having a symbol of its own — its parameters
/// and its name are declared, and a call to it names that symbol — and in
/// being able to capture nothing at all, which is the usual case and the one
/// that stays an ordinary method.
#[derive(Clone, Debug)]
pub struct BoundLocalFunction {
    pub symbol: SymbolId,
    pub body: BoundStatement,
    /// The element type, where the local function is an iterator of its
    /// own: a `yield` in it makes *it* the machine, not the method around
    /// it.
    pub iterator: Option<Type>,
    /// Locals of the method that holds it that the body reads.
    pub captured: Vec<LocalId>,
    /// Parameters of that method it reads.
    pub captured_parameters: Vec<SymbolId>,
    /// The local functions it calls, whose captures are its own: a lambda
    /// that calls a local function reading a variable of the method reads it
    /// too, and lives where that variable does.
    pub calls: Vec<SymbolId>,
    /// Whether the body reads `this`.
    pub captures_this: bool,
}

/// A lambda, bound.
///
/// Its locals live on the enclosing member's table rather than a table of its
/// own: one flat table per member is what the semantic model promises, and a
/// lambda's body is still that member's syntax.
#[derive(Clone, Debug)]
pub struct BoundLambda {
    /// Where it was written, which is how a backend names the method it
    /// becomes.
    pub span: TextSpan,
    /// The locals that are its parameters, in order.
    pub parameters: Vec<LocalId>,
    pub body: BoundStatement,
    /// Locals of the enclosing method the body reads. A lambda that captures
    /// needs somewhere for those to live that outlives the method, which is a
    /// display class.
    pub captured: Vec<LocalId>,
    /// Parameters of the enclosing member it reads, which are captured the
    /// same way: `Op Adder(int by) => x => x + by;` has to keep `by` alive
    /// after `Adder` returned.
    pub captured_parameters: Vec<SymbolId>,
    /// The local functions it calls, whose captures are its own: a lambda
    /// that calls a local function reading a variable of the method reads it
    /// too, and lives where that variable does.
    pub calls: Vec<SymbolId>,
    /// Whether the body reads `this`.
    pub captures_this: bool,
    pub return_type: Type,
    /// What the delegate gets back from an `async` lambda: the `Task<int>`
    /// made around the `int` its `return`s give, which is what
    /// [`return_type`](Self::return_type) holds. `None` for a lambda that is
    /// not `async`.
    pub task_type: Option<Type>,
}

/// What a name in a body turned out to refer to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BoundSymbol {
    Declared(SymbolId),
    Local(LocalId),
}

impl BoundBody {
    /// Calls `visit` on every expression of the body, however deep, and on
    /// those of its lambdas and local functions.
    pub fn each_expression(&self, visit: &mut impl FnMut(&BoundExpression)) {
        fn descend(expression: &BoundExpression, visit: &mut impl FnMut(&BoundExpression)) {
            visit(expression);
            crate::definite::each_child_of(expression, &mut |child| descend(child, visit));
        }
        let statements = self
            .statements
            .iter()
            .chain(self.lambdas.iter().map(|lambda| &lambda.body))
            .chain(self.local_functions.iter().map(|function| &function.body));
        for statement in statements {
            crate::definite::each_expression_of(statement, &mut |expression| {
                descend(expression, visit);
            });
        }
    }

    #[must_use]
    pub fn type_at(&self, span: TextSpan) -> Option<&Type> {
        self.types.get(&span)
    }

    #[must_use]
    pub fn reference_at(&self, span: TextSpan) -> Option<BoundSymbol> {
        self.references.get(&span).copied()
    }

    /// What the name whose token is at `span` refers to.
    #[must_use]
    pub fn symbol_at(&self, span: TextSpan) -> Option<BoundSymbol> {
        self.symbols
            .get(&span)
            .map(|&symbol| BoundSymbol::Declared(symbol))
            .or_else(|| self.references.get(&span).copied())
    }
}
