//! The expressions and statements a decompiled body is made of.
//!
//! This is deliberately closer to C# than to IL: a call has a receiver and
//! arguments rather than a stack, a comparison is an operator rather than a
//! `ceq` followed by a branch. Building these from IL is the job of
//! [`crate::stack`]; making them read well is the job of [`crate::simplify`];
//! writing them out is [`crate::print`]'s.

use rustlyn_metadata::signature::TypeSig;

use crate::names::{FieldRef, MethodRef};

/// A binary operator, spelled the C# way.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    /// `>>>`: a shift that fills with zeros whatever the type's sign.
    UShr,
    LogicalAnd,
    LogicalOr,
    Coalesce,
}

impl BinOp {
    #[must_use]
    pub const fn text(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::And => "&",
            Self::Or => "|",
            Self::Xor => "^",
            Self::Shl => "<<",
            Self::Shr => ">>",
            Self::UShr => ">>>",
            Self::LogicalAnd => "&&",
            Self::LogicalOr => "||",
            Self::Coalesce => "??",
        }
    }

    /// Where the operator binds, higher binding tighter.
    #[must_use]
    pub const fn precedence(self) -> u8 {
        match self {
            Self::Mul | Self::Div | Self::Rem => 13,
            Self::Add | Self::Sub => 12,
            Self::Shl | Self::Shr | Self::UShr => 11,
            Self::And => 8,
            Self::Xor => 7,
            Self::Or => 6,
            Self::LogicalAnd => 5,
            Self::LogicalOr => 4,
            Self::Coalesce => 3,
        }
    }
}

/// A comparison.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Cmp {
    #[must_use]
    pub const fn text(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }

    #[must_use]
    pub const fn negated(self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
            Self::Ge => Self::Lt,
        }
    }

    #[must_use]
    pub const fn precedence(self) -> u8 {
        match self {
            Self::Eq | Self::Ne => 9,
            _ => 10,
        }
    }
}

/// A unary operator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOp {
    /// `-x`
    Neg,
    /// `~x`
    BitNot,
    /// `!x`
    Not,
    /// `&x` as IL takes it: `ref x` in an argument, nothing at all as a
    /// receiver.
    AddressOf,
    /// `*p`, what `ldind`/`ldobj` do to an address.
    Deref,
}

/// An expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Expr {
    This,
    /// `this` as the receiver of a non-virtual call to a base member.
    Base,
    /// A parameter, numbered without `this`.
    Arg(u16),
    Local(u16),
    /// A value that crossed a block boundary on the evaluation stack.
    Slot(u32),
    /// The exception a handler was entered with.
    CaughtException,
    Int(i64),
    Long(i64),
    /// A floating constant, and whether it is a `float` rather than a `double`.
    Float(f64, bool),
    Bool(bool),
    Char(u16),
    Str(String),
    Null,
    /// `Color.Red`
    EnumMember(TypeSig, String),
    /// `default(T)` or `default`.
    Default(TypeSig),
    TypeOf(TypeSig),
    SizeOf(TypeSig),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `left op right`, with whether the operands are floating point and
    /// whether an unordered pair counts as true (the `.un` in `bge.un`).
    Compare {
        op: Cmp,
        left: Box<Expr>,
        right: Box<Expr>,
        float: bool,
        unordered: bool,
    },
    Assign(Box<Expr>, Box<Expr>),
    /// `target op= value`
    Compound(BinOp, Box<Expr>, Box<Expr>),
    /// `target++` / `target--`, and whether the old value is the result.
    Increment {
        target: Box<Expr>,
        delta: i64,
        postfix: bool,
    },
    Call {
        method: MethodRef,
        receiver: Option<Box<Expr>>,
        args: Vec<Expr>,
    },
    /// `new T(args)`
    New {
        ctor: MethodRef,
        args: Vec<Expr>,
        /// `{ a = 1, b = 2 }` folded in afterwards.
        initializer: Vec<(String, Expr)>,
    },
    /// `new T()` of a type parameter.
    NewOf(TypeSig),
    /// `source with { a = 1 }`: a record cloned and its `init` members set.
    With {
        source: Box<Expr>,
        initializer: Vec<(String, Expr)>,
    },
    /// `new T[size]`, or `new T[] { items }` once the stores are folded in.
    NewArray {
        element: TypeSig,
        size: Box<Expr>,
        items: Option<Vec<Expr>>,
    },
    Field {
        receiver: Option<Box<Expr>>,
        field: FieldRef,
    },
    /// `array[index]`
    Index {
        array: Box<Expr>,
        indices: Vec<Expr>,
    },
    /// `array.Length`
    Length(Box<Expr>),
    /// `(T)x`
    Cast(TypeSig, Box<Expr>),
    /// `(T)x` in a `checked` context.
    CheckedCast(TypeSig, Box<Expr>),
    /// `(int)t` where a type parameter's constraint declares the conversion
    /// (C# 11): the operator, not the box and unbox a plain cast of a `T`
    /// is.
    OperatorCast(TypeSig, Box<Expr>),
    /// `x as T`
    As(TypeSig, Box<Expr>),
    /// `x is T`
    Is(TypeSig, Box<Expr>),
    /// `x is T name`, with the local the match binds.
    IsPattern(TypeSig, Box<Expr>, Box<Expr>),
    /// A box, kept for its type and printed as its operand.
    Box(TypeSig, Box<Expr>),
    Conditional(Box<Expr>, Box<Expr>, Box<Expr>),
    /// A delegate over a method: `target.M`, `M`, or `new D(target.M)`.
    Delegate {
        ty: TypeSig,
        target: Option<Box<Expr>>,
        method: MethodRef,
    },
    /// `a.b`, a property.
    Property {
        receiver: Option<Box<Expr>>,
        declaring: TypeSig,
        name: String,
        /// The property's type, when the accessor said.
        ty: Option<TypeSig>,
    },
    /// `receiver[args]`, an indexer.
    Indexer {
        receiver: Box<Expr>,
        args: Vec<Expr>,
    },
    /// `await x`
    Await(Box<Expr>),
    /// `(a, b)`
    Tuple(Vec<Expr>),
    /// An interpolated string: text and holes in order.
    Interpolated(Vec<Interpolation>),
    /// A lambda folded back out of its display class. The parameters are
    /// locals of the enclosing method made for it; the id tells its body's
    /// block from every other.
    Lambda {
        id: u32,
        params: Vec<u16>,
        /// Which parameters are `out`: the rest of those by reference are
        /// `ref`.
        outs: Vec<bool>,
        body: Box<Body>,
    },
    /// `ldftn M`: the address of a method, on its way into a delegate.
    FunctionPointer(MethodRef),
    /// `checked(x)`
    Checked(Box<Expr>),
    /// A receiver reached with `?.`: the member access on it is skipped when
    /// it is null.
    MaybeNull(Box<Expr>),
    /// `stackalloc T[size]`
    StackAlloc(TypeSig, Box<Expr>),
    /// Raw text, for whatever the decompiler had to give up on.
    Raw(String),
}

/// One piece of an interpolated string.
#[derive(Clone, PartialEq, Debug)]
pub enum Interpolation {
    Text(String),
    Hole(Box<Expr>, Option<String>),
}

/// A lambda's body: an expression or a block.
#[derive(Clone, PartialEq, Debug)]
pub enum Body {
    Expr(Box<Expr>),
    Block(Vec<Stmt>),
}

impl Expr {
    #[must_use]
    pub fn unary(op: UnOp, inner: Self) -> Self {
        Self::Unary(op, Box::new(inner))
    }

    #[must_use]
    pub fn binary(op: BinOp, left: Self, right: Self) -> Self {
        Self::Binary(op, Box::new(left), Box::new(right))
    }

    #[must_use]
    pub fn compare(op: Cmp, left: Self, right: Self) -> Self {
        Self::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
            float: false,
            unordered: false,
        }
    }

    #[must_use]
    pub fn assign(target: Self, value: Self) -> Self {
        Self::Assign(Box::new(target), Box::new(value))
    }

    /// Whether evaluating the expression twice is the same as once: what
    /// `dup` may copy rather than spill.
    #[must_use]
    pub fn is_pure(&self) -> bool {
        match self {
            Self::This
            | Self::Base
            | Self::Arg(_)
            | Self::Local(_)
            | Self::Slot(_)
            | Self::CaughtException
            | Self::Int(_)
            | Self::Long(_)
            | Self::Float(..)
            | Self::Bool(_)
            | Self::Char(_)
            | Self::Str(_)
            | Self::Null
            | Self::EnumMember(..)
            | Self::Default(_)
            | Self::TypeOf(_)
            | Self::SizeOf(_) => true,
            Self::Field { receiver, .. } => receiver.as_ref().is_none_or(|inner| inner.is_pure()),
            Self::Unary(UnOp::AddressOf | UnOp::Neg | UnOp::BitNot | UnOp::Not, inner)
            | Self::Box(_, inner)
            | Self::Cast(_, inner)
            | Self::As(_, inner)
            | Self::Is(_, inner)
            | Self::Length(inner) => inner.is_pure(),
            Self::IsPattern(_, inner, _) => inner.is_pure(),
            Self::Binary(_, left, right) | Self::Compare { left, right, .. } => {
                left.is_pure() && right.is_pure()
            }
            Self::Conditional(a, b, c) => a.is_pure() && b.is_pure() && c.is_pure(),
            Self::Index { array, indices } => array.is_pure() && indices.iter().all(Self::is_pure),
            _ => false,
        }
    }

    /// Whether the expression is a place a value can be stored into.
    #[must_use]
    pub fn is_place(&self) -> bool {
        matches!(
            self,
            Self::Arg(_)
                | Self::Local(_)
                | Self::Field { .. }
                | Self::Index { .. }
                | Self::Property { .. }
                | Self::Indexer { .. }
                | Self::Unary(UnOp::Deref, _)
        )
    }

    /// Whether the expression is a constant of any kind.
    #[must_use]
    pub const fn is_constant(&self) -> bool {
        matches!(
            self,
            Self::Int(_)
                | Self::Long(_)
                | Self::Float(..)
                | Self::Bool(_)
                | Self::Char(_)
                | Self::Str(_)
                | Self::Null
                | Self::EnumMember(..)
        )
    }

    /// Walks every sub-expression, this one first.
    pub fn walk(&self, visit: &mut dyn FnMut(&Self)) {
        visit(self);
        match self {
            Self::Unary(_, inner)
            | Self::Cast(_, inner)
            | Self::CheckedCast(_, inner)
            | Self::OperatorCast(_, inner)
            | Self::As(_, inner)
            | Self::Is(_, inner)
            | Self::Box(_, inner)
            | Self::Length(inner)
            | Self::Checked(inner)
            | Self::MaybeNull(inner)
            | Self::StackAlloc(_, inner)
            | Self::Await(inner) => inner.walk(visit),
            Self::IsPattern(_, inner, target) => {
                inner.walk(visit);
                target.walk(visit);
            }
            Self::Binary(_, left, right)
            | Self::Assign(left, right)
            | Self::Compound(_, left, right)
            | Self::Compare { left, right, .. } => {
                left.walk(visit);
                right.walk(visit);
            }
            Self::Increment { target, .. } => target.walk(visit),
            Self::Call { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    receiver.walk(visit);
                }
                for arg in args {
                    arg.walk(visit);
                }
            }
            Self::New {
                args, initializer, ..
            } => {
                for arg in args {
                    arg.walk(visit);
                }
                for (_, value) in initializer {
                    value.walk(visit);
                }
            }
            Self::With {
                source,
                initializer,
            } => {
                source.walk(visit);
                for (_, value) in initializer {
                    value.walk(visit);
                }
            }
            Self::NewArray { size, items, .. } => {
                size.walk(visit);
                if let Some(items) = items {
                    for item in items {
                        item.walk(visit);
                    }
                }
            }
            Self::Field { receiver, .. } | Self::Property { receiver, .. } => {
                if let Some(receiver) = receiver {
                    receiver.walk(visit);
                }
            }
            Self::Index { array, indices } => {
                array.walk(visit);
                for index in indices {
                    index.walk(visit);
                }
            }
            Self::Indexer { receiver, args } => {
                receiver.walk(visit);
                for arg in args {
                    arg.walk(visit);
                }
            }
            Self::Conditional(a, b, c) => {
                a.walk(visit);
                b.walk(visit);
                c.walk(visit);
            }
            Self::Delegate {
                target: Some(target),
                ..
            } => target.walk(visit),
            Self::Tuple(items) => {
                for item in items {
                    item.walk(visit);
                }
            }
            Self::Interpolated(parts) => {
                for part in parts {
                    if let Interpolation::Hole(expr, _) = part {
                        expr.walk(visit);
                    }
                }
            }
            Self::Lambda { body, .. } => match body.as_ref() {
                Body::Expr(expr) => expr.walk(visit),
                Body::Block(stmts) => {
                    for stmt in stmts {
                        stmt.walk_exprs(visit);
                    }
                }
            },
            _ => {}
        }
    }

    /// Walks every sub-expression outside nested lambdas, this one first.
    pub fn walk_shallow(&self, visit: &mut dyn FnMut(&Self)) {
        if let Self::Lambda { .. } = self {
            visit(self);
            return;
        }
        // The children are visited through `walk`, which would descend
        // into lambdas; each child is walked shallowly instead.
        let mut children: Vec<&Self> = Vec::new();
        self.children(&mut children);
        visit(self);
        for child in children {
            child.walk_shallow(visit);
        }
    }

    /// The direct sub-expressions.
    pub fn children<'e>(&'e self, out: &mut Vec<&'e Self>) {
        match self {
            Self::Unary(_, inner)
            | Self::Cast(_, inner)
            | Self::CheckedCast(_, inner)
            | Self::OperatorCast(_, inner)
            | Self::As(_, inner)
            | Self::Is(_, inner)
            | Self::Box(_, inner)
            | Self::Length(inner)
            | Self::Checked(inner)
            | Self::MaybeNull(inner)
            | Self::StackAlloc(_, inner)
            | Self::Await(inner) => out.push(inner),
            Self::IsPattern(_, inner, target) => {
                out.push(inner);
                out.push(target);
            }
            Self::Binary(_, left, right)
            | Self::Assign(left, right)
            | Self::Compound(_, left, right)
            | Self::Compare { left, right, .. } => {
                out.push(left);
                out.push(right);
            }
            Self::Increment { target, .. } => out.push(target),
            Self::Call { receiver, args, .. } => {
                out.extend(receiver.iter().map(|r| r.as_ref()));
                out.extend(args.iter());
            }
            Self::New {
                args, initializer, ..
            } => {
                out.extend(args.iter());
                out.extend(initializer.iter().map(|(_, value)| value));
            }
            Self::With {
                source,
                initializer,
            } => {
                out.push(source);
                out.extend(initializer.iter().map(|(_, value)| value));
            }
            Self::NewArray { size, items, .. } => {
                out.push(size);
                if let Some(items) = items {
                    out.extend(items.iter());
                }
            }
            Self::Field { receiver, .. } | Self::Property { receiver, .. } => {
                out.extend(receiver.iter().map(|r| r.as_ref()));
            }
            Self::Index { array, indices } => {
                out.push(array);
                out.extend(indices.iter());
            }
            Self::Indexer { receiver, args } => {
                out.push(receiver);
                out.extend(args.iter());
            }
            Self::Conditional(a, b, c) => {
                out.push(a);
                out.push(b);
                out.push(c);
            }
            Self::Delegate { target, .. } => out.extend(target.iter().map(|t| t.as_ref())),
            Self::Tuple(items) => out.extend(items.iter()),
            Self::Interpolated(parts) => {
                for part in parts {
                    if let Interpolation::Hole(hole, _) = part {
                        out.push(hole);
                    }
                }
            }
            _ => {}
        }
    }

    /// Rewrites every sub-expression bottom-up.
    pub fn map(&mut self, rewrite: &mut dyn FnMut(&mut Self)) {
        match self {
            Self::Unary(_, inner)
            | Self::Cast(_, inner)
            | Self::CheckedCast(_, inner)
            | Self::OperatorCast(_, inner)
            | Self::As(_, inner)
            | Self::Is(_, inner)
            | Self::Box(_, inner)
            | Self::Length(inner)
            | Self::Checked(inner)
            | Self::MaybeNull(inner)
            | Self::StackAlloc(_, inner)
            | Self::Await(inner) => inner.map(rewrite),
            Self::IsPattern(_, inner, target) => {
                inner.map(rewrite);
                target.map(rewrite);
            }
            Self::Binary(_, left, right)
            | Self::Assign(left, right)
            | Self::Compound(_, left, right)
            | Self::Compare { left, right, .. } => {
                left.map(rewrite);
                right.map(rewrite);
            }
            Self::Increment { target, .. } => target.map(rewrite),
            Self::Call { receiver, args, .. } => {
                if let Some(receiver) = receiver {
                    receiver.map(rewrite);
                }
                for arg in args {
                    arg.map(rewrite);
                }
            }
            Self::New {
                args, initializer, ..
            } => {
                for arg in args {
                    arg.map(rewrite);
                }
                for (_, value) in initializer {
                    value.map(rewrite);
                }
            }
            Self::With {
                source,
                initializer,
            } => {
                source.map(rewrite);
                for (_, value) in initializer {
                    value.map(rewrite);
                }
            }
            Self::NewArray { size, items, .. } => {
                size.map(rewrite);
                if let Some(items) = items {
                    for item in items {
                        item.map(rewrite);
                    }
                }
            }
            Self::Field { receiver, .. } | Self::Property { receiver, .. } => {
                if let Some(receiver) = receiver {
                    receiver.map(rewrite);
                }
            }
            Self::Index { array, indices } => {
                array.map(rewrite);
                for index in indices {
                    index.map(rewrite);
                }
            }
            Self::Indexer { receiver, args } => {
                receiver.map(rewrite);
                for arg in args {
                    arg.map(rewrite);
                }
            }
            Self::Conditional(a, b, c) => {
                a.map(rewrite);
                b.map(rewrite);
                c.map(rewrite);
            }
            Self::Delegate {
                target: Some(target),
                ..
            } => target.map(rewrite),
            Self::Tuple(items) => {
                for item in items {
                    item.map(rewrite);
                }
            }
            Self::Interpolated(parts) => {
                for part in parts {
                    if let Interpolation::Hole(expr, _) = part {
                        expr.map(rewrite);
                    }
                }
            }
            Self::Lambda { body, .. } => match body.as_mut() {
                Body::Expr(expr) => expr.map(rewrite),
                Body::Block(stmts) => {
                    for stmt in stmts {
                        stmt.map_exprs(rewrite);
                    }
                }
            },
            _ => {}
        }
        rewrite(self);
    }

    /// How many times a sub-expression matching the predicate occurs.
    #[must_use]
    pub fn count(&self, matches: &dyn Fn(&Self) -> bool) -> usize {
        let mut count = 0;
        self.walk(&mut |expr| {
            if matches(expr) {
                count += 1;
            }
        });
        count
    }
}

/// One `catch` of a `try`.
#[derive(Clone, PartialEq, Debug)]
pub struct Catch {
    /// `None` catches everything.
    pub ty: Option<TypeSig>,
    /// The local the exception goes into, when it is kept.
    pub variable: Option<u16>,
    /// `when (...)`.
    pub filter: Option<Expr>,
    pub body: Vec<Stmt>,
}

/// One `case` group of a `switch`.
#[derive(Clone, PartialEq, Debug)]
pub struct Case {
    /// The labels, `None` being `default`.
    pub labels: Vec<Option<Expr>>,
    pub body: Vec<Stmt>,
}

/// A statement.
#[derive(Clone, PartialEq, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Stmt {
    Expr(Expr),
    /// `T name = value;` — the declaration of a local at its first store.
    Declare {
        local: u16,
        value: Option<Expr>,
    },
    Return(Option<Expr>),
    Throw(Option<Expr>),
    If {
        condition: Expr,
        then: Vec<Stmt>,
        otherwise: Vec<Stmt>,
    },
    While {
        condition: Expr,
        body: Vec<Stmt>,
    },
    DoWhile {
        body: Vec<Stmt>,
        condition: Expr,
    },
    For {
        initializer: Option<Box<Stmt>>,
        condition: Expr,
        step: Option<Expr>,
        body: Vec<Stmt>,
    },
    ForEach {
        /// The local the element goes into.
        local: u16,
        source: Expr,
        body: Vec<Stmt>,
    },
    Using {
        /// The local holding the resource, when it is declared by the using.
        local: Option<u16>,
        resource: Expr,
        body: Vec<Stmt>,
    },
    Lock {
        target: Expr,
        body: Vec<Stmt>,
    },
    /// `fixed (T* local = init) { body }`: `init` as C# writes it, `&x`
    /// for an address.
    Fixed {
        local: u16,
        init: Expr,
        body: Vec<Stmt>,
    },
    Switch {
        value: Expr,
        cases: Vec<Case>,
    },
    Try {
        body: Vec<Stmt>,
        catches: Vec<Catch>,
        finally: Option<Vec<Stmt>>,
    },
    /// `checked { ... }`
    Checked(Vec<Stmt>),
    Break,
    Continue,
    Goto(u32),
    Label(u32),
    /// A remark the decompiler leaves behind about what it could not do.
    Comment(String),
    /// A local function folded back out of its lifted method.
    LocalFunction {
        name: String,
        /// Its own type parameters, after those it shares with the method.
        type_params: Vec<String>,
        params: Vec<u16>,
        /// Which of the parameters are `out`.
        outs: Vec<bool>,
        returns: TypeSig,
        /// The `where` clauses of its own type parameters.
        constraints: String,
        body: Vec<Stmt>,
    },
    /// `yield return value;`
    YieldReturn(Expr),
    /// `yield break;`
    YieldBreak,
    /// Where an iterator's `try` began: the state the machine entered, to
    /// be matched with the `finally` method it calls on the way out.
    EnterTry(i64),
}

impl Stmt {
    /// Visits every expression in the statement and those nested in it.
    pub fn walk_exprs(&self, visit: &mut dyn FnMut(&Expr)) {
        match self {
            Self::Expr(expr) | Self::YieldReturn(expr) => expr.walk(visit),
            Self::Declare { value, .. } => {
                if let Some(value) = value {
                    value.walk(visit);
                }
            }
            Self::Return(value) | Self::Throw(value) => {
                if let Some(value) = value {
                    value.walk(visit);
                }
            }
            Self::If {
                condition,
                then,
                otherwise,
            } => {
                condition.walk(visit);
                walk_all(then, visit);
                walk_all(otherwise, visit);
            }
            Self::While { condition, body } | Self::DoWhile { body, condition } => {
                condition.walk(visit);
                walk_all(body, visit);
            }
            Self::For {
                initializer,
                condition,
                step,
                body,
            } => {
                if let Some(initializer) = initializer {
                    initializer.walk_exprs(visit);
                }
                condition.walk(visit);
                if let Some(step) = step {
                    step.walk(visit);
                }
                walk_all(body, visit);
            }
            Self::ForEach { source, body, .. } => {
                source.walk(visit);
                walk_all(body, visit);
            }
            Self::Using { resource, body, .. } => {
                resource.walk(visit);
                walk_all(body, visit);
            }
            Self::Lock { target, body }
            | Self::Fixed {
                init: target, body, ..
            } => {
                target.walk(visit);
                walk_all(body, visit);
            }
            Self::Switch { value, cases } => {
                value.walk(visit);
                for case in cases {
                    for label in case.labels.iter().flatten() {
                        label.walk(visit);
                    }
                    walk_all(&case.body, visit);
                }
            }
            Self::Try {
                body,
                catches,
                finally,
            } => {
                walk_all(body, visit);
                for catch in catches {
                    if let Some(filter) = &catch.filter {
                        filter.walk(visit);
                    }
                    walk_all(&catch.body, visit);
                }
                if let Some(finally) = finally {
                    walk_all(finally, visit);
                }
            }
            Self::Checked(body) | Self::LocalFunction { body, .. } => walk_all(body, visit),
            Self::Break
            | Self::Continue
            | Self::Goto(_)
            | Self::Label(_)
            | Self::Comment(_)
            | Self::YieldBreak
            | Self::EnterTry(_) => {}
        }
    }

    /// Rewrites every expression in the statement, nested ones included.
    pub fn map_exprs(&mut self, rewrite: &mut dyn FnMut(&mut Expr)) {
        match self {
            Self::Expr(expr) | Self::YieldReturn(expr) => expr.map(rewrite),
            Self::Declare { value, .. } => {
                if let Some(value) = value {
                    value.map(rewrite);
                }
            }
            Self::Return(value) | Self::Throw(value) => {
                if let Some(value) = value {
                    value.map(rewrite);
                }
            }
            Self::If {
                condition,
                then,
                otherwise,
            } => {
                condition.map(rewrite);
                map_all(then, rewrite);
                map_all(otherwise, rewrite);
            }
            Self::While { condition, body } | Self::DoWhile { body, condition } => {
                condition.map(rewrite);
                map_all(body, rewrite);
            }
            Self::For {
                initializer,
                condition,
                step,
                body,
            } => {
                if let Some(initializer) = initializer {
                    initializer.map_exprs(rewrite);
                }
                condition.map(rewrite);
                if let Some(step) = step {
                    step.map(rewrite);
                }
                map_all(body, rewrite);
            }
            Self::ForEach { source, body, .. } => {
                source.map(rewrite);
                map_all(body, rewrite);
            }
            Self::Using { resource, body, .. } => {
                resource.map(rewrite);
                map_all(body, rewrite);
            }
            Self::Lock { target, body }
            | Self::Fixed {
                init: target, body, ..
            } => {
                target.map(rewrite);
                map_all(body, rewrite);
            }
            Self::Switch { value, cases } => {
                value.map(rewrite);
                for case in cases {
                    for label in case.labels.iter_mut().flatten() {
                        label.map(rewrite);
                    }
                    map_all(&mut case.body, rewrite);
                }
            }
            Self::Try {
                body,
                catches,
                finally,
            } => {
                map_all(body, rewrite);
                for catch in catches {
                    if let Some(filter) = &mut catch.filter {
                        filter.map(rewrite);
                    }
                    map_all(&mut catch.body, rewrite);
                }
                if let Some(finally) = finally {
                    map_all(finally, rewrite);
                }
            }
            Self::Checked(body) | Self::LocalFunction { body, .. } => map_all(body, rewrite),
            Self::Break
            | Self::Continue
            | Self::Goto(_)
            | Self::Label(_)
            | Self::Comment(_)
            | Self::YieldBreak
            | Self::EnterTry(_) => {}
        }
    }

    /// The nested statement lists, for passes that work on blocks.
    pub fn blocks_mut(&mut self) -> Vec<&mut Vec<Stmt>> {
        match self {
            Self::If {
                then, otherwise, ..
            } => vec![then, otherwise],
            Self::While { body, .. }
            | Self::DoWhile { body, .. }
            | Self::For { body, .. }
            | Self::ForEach { body, .. }
            | Self::Using { body, .. }
            | Self::Lock { body, .. }
            | Self::Fixed { body, .. } => vec![body],
            Self::Switch { cases, .. } => cases.iter_mut().map(|case| &mut case.body).collect(),
            Self::Try {
                body,
                catches,
                finally,
            } => {
                let mut blocks = vec![body];
                blocks.extend(catches.iter_mut().map(|catch| &mut catch.body));
                if let Some(finally) = finally {
                    blocks.push(finally);
                }
                blocks
            }
            Self::Checked(body) | Self::LocalFunction { body, .. } => vec![body],
            _ => Vec::new(),
        }
    }

    /// The nested statement lists, read-only.
    pub fn blocks(&self) -> Vec<&Vec<Stmt>> {
        match self {
            Self::If {
                then, otherwise, ..
            } => vec![then, otherwise],
            Self::While { body, .. }
            | Self::DoWhile { body, .. }
            | Self::For { body, .. }
            | Self::ForEach { body, .. }
            | Self::Using { body, .. }
            | Self::Lock { body, .. }
            | Self::Fixed { body, .. } => vec![body],
            Self::Switch { cases, .. } => cases.iter().map(|case| &case.body).collect(),
            Self::Try {
                body,
                catches,
                finally,
            } => {
                let mut blocks = vec![body];
                blocks.extend(catches.iter().map(|catch| &catch.body));
                if let Some(finally) = finally {
                    blocks.push(finally);
                }
                blocks
            }
            Self::Checked(body) | Self::LocalFunction { body, .. } => vec![body],
            _ => Vec::new(),
        }
    }

    /// Whether control never continues past the statement.
    #[must_use]
    pub fn ends_flow(&self) -> bool {
        match self {
            Self::Return(_)
            | Self::Throw(_)
            | Self::Break
            | Self::Continue
            | Self::Goto(_)
            | Self::YieldBreak => true,
            Self::If {
                then, otherwise, ..
            } => {
                then.last().is_some_and(Self::ends_flow)
                    && otherwise.last().is_some_and(Self::ends_flow)
            }
            Self::Try { body, catches, .. } => {
                body.last().is_some_and(Self::ends_flow)
                    && catches
                        .iter()
                        .all(|catch| catch.body.last().is_some_and(Self::ends_flow))
            }
            Self::Using { body, .. }
            | Self::Lock { body, .. }
            | Self::Fixed { body, .. }
            | Self::Checked(body) => body.last().is_some_and(Self::ends_flow),
            Self::Switch { cases, .. } => {
                cases.iter().any(|case| case.labels.contains(&None))
                    && cases.iter().all(|case| {
                        case.body.last().is_some_and(|last| {
                            matches!(
                                last,
                                Self::Return(_) | Self::Throw(_) | Self::Goto(_) | Self::Continue
                            )
                        }) && !breaks_out_of(&case.body)
                    })
            }
            // A loop nothing breaks out of is never left but by a jump.
            Self::While {
                condition: Expr::Bool(true),
                body,
            } => !breaks_out_of(body),
            _ => false,
        }
    }
}

fn walk_all(stmts: &[Stmt], visit: &mut dyn FnMut(&Expr)) {
    for stmt in stmts {
        stmt.walk_exprs(visit);
    }
}

fn map_all(stmts: &mut [Stmt], rewrite: &mut dyn FnMut(&mut Expr)) {
    for stmt in stmts {
        stmt.map_exprs(rewrite);
    }
}

/// Whether statements hold a `break` out of what is around them, not out
/// of a loop or `switch` of their own.
/// Whether a `continue` in a list goes to the loop around it.
pub(crate) fn continues_in(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Continue => true,
        Stmt::While { .. }
        | Stmt::DoWhile { .. }
        | Stmt::For { .. }
        | Stmt::ForEach { .. }
        | Stmt::LocalFunction { .. } => false,
        other => other.blocks().iter().any(|block| continues_in(block)),
    })
}

pub(crate) fn breaks_out_of(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break => true,
        Stmt::While { .. }
        | Stmt::DoWhile { .. }
        | Stmt::For { .. }
        | Stmt::ForEach { .. }
        | Stmt::Switch { .. }
        | Stmt::LocalFunction { .. } => false,
        other => other.blocks().iter().any(|block| breaks_out_of(block)),
    })
}

/// Renumbers the locals statements bind: declarations, loop, `using` and
/// `fixed` variables, caught exceptions, and the parameters of local
/// functions and lambdas, in nested lambdas too. The locals expressions
/// read are the caller's to map.
pub fn renumber_binders(stmts: &mut [Stmt], map: &mut dyn FnMut(u16) -> u16) {
    stmt_binders(stmts, map);
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| {
            if let Expr::Lambda { params, body, .. } = expr {
                for param in params.iter_mut() {
                    *param = map(*param);
                }
                if let Body::Block(inner) = body.as_mut() {
                    stmt_binders(inner, map);
                }
            }
        });
    }
}

fn stmt_binders(stmts: &mut [Stmt], map: &mut dyn FnMut(u16) -> u16) {
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::Declare { local, .. }
            | Stmt::ForEach { local, .. }
            | Stmt::Fixed { local, .. } => {
                *local = map(*local);
            }
            Stmt::Using {
                local: Some(local), ..
            } => *local = map(*local),
            Stmt::LocalFunction { params, .. } => {
                for param in params.iter_mut() {
                    *param = map(*param);
                }
            }
            Stmt::Try { catches, .. } => {
                for catch in catches.iter_mut() {
                    if let Some(variable) = &mut catch.variable {
                        *variable = map(*variable);
                    }
                }
            }
            Stmt::For {
                initializer: Some(initializer),
                ..
            } => stmt_binders(std::slice::from_mut(initializer.as_mut()), map),
            _ => {}
        }
        for block in stmt.blocks_mut() {
            stmt_binders(block, map);
        }
    }
}

/// Rewrites every type the statements' expressions name: casts, `new`s,
/// the types of calls and fields, and the types caught.
pub fn map_types(stmts: &mut [Stmt], f: &dyn Fn(&TypeSig) -> TypeSig) {
    fn method(method: &mut crate::names::MethodRef, f: &dyn Fn(&TypeSig) -> TypeSig) {
        method.declaring = f(&method.declaring);
        for arg in &mut method.type_args {
            *arg = f(arg);
        }
    }
    fn catches(stmts: &mut [Stmt], f: &dyn Fn(&TypeSig) -> TypeSig) {
        for stmt in stmts.iter_mut() {
            if let Stmt::Try { catches, .. } = stmt {
                for catch in catches.iter_mut() {
                    if let Some(ty) = &mut catch.ty {
                        *ty = f(ty);
                    }
                }
            }
            for block in stmt.blocks_mut() {
                catches(block, f);
            }
        }
    }
    catches(stmts, f);
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| match expr {
            Expr::EnumMember(ty, _)
            | Expr::Default(ty)
            | Expr::TypeOf(ty)
            | Expr::SizeOf(ty)
            | Expr::NewOf(ty)
            | Expr::Cast(ty, _)
            | Expr::CheckedCast(ty, _)
            | Expr::OperatorCast(ty, _)
            | Expr::As(ty, _)
            | Expr::Is(ty, _)
            | Expr::IsPattern(ty, _, _)
            | Expr::Box(ty, _)
            | Expr::StackAlloc(ty, _)
            | Expr::NewArray { element: ty, .. } => *ty = f(ty),
            Expr::Call { method: m, .. } | Expr::New { ctor: m, .. } | Expr::FunctionPointer(m) => {
                method(m, f);
            }
            Expr::Delegate { ty, method: m, .. } => {
                *ty = f(ty);
                method(m, f);
            }
            Expr::Field { field, .. } => {
                field.declaring = f(&field.declaring);
                field.ty = f(&field.ty);
            }
            Expr::Property { declaring, ty, .. } => {
                *declaring = f(declaring);
                if let Some(ty) = ty {
                    *ty = f(ty);
                }
            }
            _ => {}
        });
    }
}
