//! Failability: whether a member can fail, with what, when — and whether
//! "when" can actually happen.
//!
//! A method that throws on a negative amount is not a problem if every call
//! passes `5`. So for each place a member can fail, three questions are
//! answered from the bound trees:
//!
//! 1. **What** fails: an explicit `throw` (the exception's type and its
//!    message, where that is a constant), an integer division by something
//!    that may be zero, or a member of the project it calls that can fail in
//!    turn — followed into, with its parameters standing for the arguments.
//! 2. **When**: the conditions on the way there — the `if` around it, the
//!    early `return` before it, the `&&`, `?:` and `??` it sits under, the
//!    `case` or arm of a `switch` (its `default` holds where no other label
//!    does), a loop that may not run, a `catch` that runs only when the block
//!    before it fails.
//! 3. **Can it**: each condition is evaluated over the values its inputs can
//!    have. A parameter has what every call in the project passes, until the
//!    body writes to it (nothing is known of a member that calls reach
//!    without naming it: a virtual one, an implementation of an interface
//!    member, one used as a delegate); after that it has that or what the
//!    body gives it, and where a write is not followed (`+=`, `++`, `ref`,
//!    `out`) nothing is known. A field has what its initializer and every
//!    assignment write (only the default, when nothing does, and for a
//!    struct's always the default too); a local what is assigned to it.
//!    Where all of them are known, the conditions are tried for every
//!    combination.
//!
//! # What a verdict says
//!
//! - **Never**: no combination of values the inputs can have makes the
//!   conditions hold together. Two conditions on one input hold together
//!   only for a value it has at both: when something that can change it lies
//!   between them (a write to it, a loop that writes it, a jump back to a
//!   label, and for a field a call of code that may write it, an `await`, a
//!   `yield`, a `lock`) they are about two values.
//! - **Always**: every combination makes them hold, and nothing on the way is
//!   open: not a loop that may not run, a statement above that may return or
//!   throw, a label that a `goto` may reach, a `catch` or its filter, a `goto
//!   case` into a `switch` section, nor a call whose member a subtype may
//!   replace. The member fails whenever it gets there.
//! - **Possible**: some combination holds, and the way there may be closed.
//! - **Unknown**: an input has no known value, or a condition is of a kind
//!   the values cannot tell. The failure's inputs say which.
//!
//! Something is asserted only where it is certain, so every doubt goes
//! towards *possible* or *unknown*, never towards *never* or *always*.
//!
//! What a call does not do: a call of an `async` method that is not awaited
//! does not throw — what it fails with is kept in its task — and a call of an
//! iterator runs none of its body. A call that goes through the run-time
//! type (a virtual, abstract or interface member, on a receiver whose exact
//! type is not known) may run another body than the one it names, and what
//! it fails with is unknown.
//!
//! The values of an input are those it can have at any time, over the whole
//! project: a field holds whatever any write gives it. That errs towards
//! *possible*; the order of events is followed only to tell which reads of
//! one input can differ.

use std::collections::{HashMap, HashSet};
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundExpression, BoundExpressionKind as E, BoundPattern,
    BoundPatternKind as P, BoundStatement, BoundStatementKind as S, BoundSwitchLabel,
    ConstantValue, LocalId, MethodKind, Modifiers, RefKind, SemanticModel, SpecialType, SymbolId,
    SymbolKind, Type, TypeKind, UnaryOperator,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::walk::{
    Visited, expression_children, pattern_expressions, statement_children, walk_body,
    walk_statement,
};
use super::{Resolved, Semantic, View, contains_word, display_type};
use crate::project::ProjectKind;

/// How deep calls into the project's own members are followed.
const CALL_DEPTH: usize = 4;
/// How far back through callers a parameter's values are looked for.
const CALLER_DEPTH: usize = 3;
/// More values than this and an input counts as unknown.
const MAX_VALUES: usize = 32;
/// More combinations of inputs than this are not tried one by one.
const MAX_COMBINATIONS: usize = 1024;
/// Places kept per input, for showing where its values come from.
const MAX_PLACES: usize = 8;

/// Library namespaces whose members run nothing of the project's, given no
/// delegate to call.
const PURE_NAMESPACES: [&str; 3] = [
    "System.Collections.Generic.",
    "System.Text.",
    "System.Globalization.",
];
/// Library types likewise.
const PURE_TYPES: [&str; 17] = [
    "System.String",
    "System.Math",
    "System.MathF",
    "System.Char",
    "System.Convert",
    "System.Boolean",
    "System.Byte",
    "System.SByte",
    "System.Int16",
    "System.Int32",
    "System.Int64",
    "System.UInt16",
    "System.UInt32",
    "System.UInt64",
    "System.Single",
    "System.Double",
    "System.Decimal",
];

// MARK: - what is reported

/// Everything that can make one member fail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failability {
    /// The member asked about, qualified: `Game.Shop.Pay`.
    pub member: String,
    pub failures: Vec<Failure>,
}

/// What kind of failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FailureKind {
    /// A `throw` written in the code.
    Throw,
    /// `a / b` or `a % b` on integers, where `b` may be zero.
    DivideByZero,
    /// A member reached through something that may be null. Reported only
    /// where the values say it can be: an unknown receiver is not a finding.
    NullReference,
    /// An array indexed outside its length, where the values say it can be.
    IndexOutOfRange,
    /// A library member that throws on what it is given: `int.Parse`,
    /// `First()`, a dictionary's indexer.
    Library,
}

/// One place the member can fail, and whether it can happen.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    pub kind: FailureKind,
    /// The exception, as C# writes its type: `ArgumentException`.
    pub exception: String,
    /// Its message, where it is a constant.
    pub message: Option<String>,
    /// Where it is thrown: the `throw`, the division.
    pub path: PathBuf,
    pub span: TextSpan,
    /// What must hold for it to happen, outermost first: the asked member's
    /// own, then those of each member called on the way.
    pub conditions: Vec<Condition>,
    /// The calls from the asked member to the one that throws; empty when it
    /// throws itself.
    pub chain: Vec<CallStep>,
    pub verdict: Verdict,
    /// What the conditions read, with the values found for each.
    pub inputs: Vec<Input>,
}

/// A condition on the way to a failure, as it reads in the code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Condition {
    /// `amount < 0`; negated where the failure is on the other branch:
    /// `!(ready)`, `count >= 10`.
    pub text: String,
    pub path: PathBuf,
    pub span: TextSpan,
}

/// A call on the way from the asked member to where it fails.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallStep {
    /// The call as written: `Withdraw(amount)`.
    pub text: String,
    /// The member it calls, qualified.
    pub callee: String,
    pub path: PathBuf,
    pub span: TextSpan,
}

/// Whether the failure can happen.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Verdict {
    /// Every value the inputs can have leads to it, and nothing on the way
    /// there is open: the member fails whenever it gets there. Not given
    /// for a failure behind a loop that may not run, a `catch`, a filter, a
    /// statement above that may return, a label a `goto` may reach, or a
    /// call whose member may be replaced by a subtype's.
    Always,
    /// Some values lead to it, and the way there may be closed.
    Possible,
    /// None do: the conditions never hold together, each read of an input
    /// being of the value it has at that point.
    Never,
    /// An input's values are not known, or a condition is of a kind the
    /// values cannot tell.
    Unknown,
}

/// An input a condition reads: a parameter, a field, a local.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Input {
    pub name: String,
    /// The values it can have, as C# writes them; `None` when not known.
    pub values: Option<Vec<String>>,
    pub origin: Origin,
    /// Where the values come from: the calls, the writes.
    pub places: Vec<(PathBuf, TextSpan)>,
}

/// Where an input's values were found, or why they were not.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Origin {
    /// A constant.
    Constant,
    /// The argument a call on the way passed for the parameter.
    Argument,
    /// What every call of the member in the project passes; `count` calls.
    Callers { count: usize },
    /// Nothing in the project calls the member: what it gets is not known.
    NoCallers,
    /// The member is reached in ways the calls do not show: it is virtual,
    /// an interface's, or used as a delegate.
    Escapes,
    /// What the field's initializer and assignments write.
    Writes { readonly: bool },
    /// Nothing ever writes the field: it keeps its default.
    NeverWritten,
    /// Unity serializes the field: the inspector may set it.
    Serialized,
    /// What the local is given.
    Local,
    /// Not known: an expression whose value is not worked out.
    Unknown,
}

// MARK: - values

#[derive(Clone, Debug, PartialEq)]
enum Val {
    Int(i128),
    Float(f64),
    Bool(bool),
    Char(char),
    Str(String),
    Null,
    /// An array of this length.
    Array(usize),
    /// Some object, not null: what `new` makes.
    Object,
}

impl Val {
    fn from_constant(value: &ConstantValue) -> Self {
        match value {
            ConstantValue::Null => Self::Null,
            ConstantValue::Boolean(b) => Self::Bool(*b),
            ConstantValue::Char(c) => Self::Char(*c),
            ConstantValue::Int32(v) => Self::Int(i128::from(*v)),
            ConstantValue::UInt32(v) => Self::Int(i128::from(*v)),
            ConstantValue::Int64(v) => Self::Int(i128::from(*v)),
            ConstantValue::UInt64(v) => Self::Int(i128::from(*v)),
            ConstantValue::Single(v) => Self::Float(f64::from(*v)),
            ConstantValue::Double(v) => Self::Float(*v),
            ConstantValue::String(s) => Self::Str(s.clone()),
        }
    }

    fn number(&self) -> Option<f64> {
        match self {
            #[allow(clippy::cast_precision_loss)]
            Self::Int(v) => Some(*v as f64),
            Self::Float(v) => Some(*v),
            #[allow(clippy::cast_precision_loss)]
            Self::Char(c) => Some(f64::from(u32::from(*c))),
            _ => None,
        }
    }

    fn integer(&self) -> Option<i128> {
        match self {
            Self::Int(v) => Some(*v),
            Self::Char(c) => Some(i128::from(u32::from(*c))),
            _ => None,
        }
    }

    fn show(&self) -> String {
        match self {
            Self::Int(v) => v.to_string(),
            Self::Float(v) => format!("{v}"),
            Self::Bool(b) => b.to_string(),
            Self::Char(c) => format!("'{c}'"),
            Self::Str(s) => format!("\"{s}\""),
            Self::Null => "null".to_owned(),
            Self::Array(length) => format!("[{length}]"),
            Self::Object => "new".to_owned(),
        }
    }
}

/// What an expression can be: one of a few values, or anything.
#[derive(Clone, Debug, PartialEq)]
enum Abs {
    Top,
    Set(Vec<Val>),
}

impl Abs {
    fn one(value: Val) -> Self {
        Self::Set(vec![value])
    }

    fn union(self, other: Self) -> Self {
        match (self, other) {
            (Self::Set(mut a), Self::Set(b)) => {
                for value in b {
                    if !a.contains(&value) {
                        a.push(value);
                    }
                }
                if a.len() > MAX_VALUES {
                    Self::Top
                } else {
                    Self::Set(a)
                }
            }
            _ => Self::Top,
        }
    }

    fn map(&self, f: &dyn Fn(&Val) -> Option<Val>) -> Self {
        let Self::Set(values) = self else {
            return Self::Top;
        };
        let mut out = Self::Set(Vec::new());
        for value in values {
            match f(value) {
                Some(mapped) => out = out.union(Self::one(mapped)),
                None => return Self::Top,
            }
        }
        out
    }

    fn map2(&self, other: &Self, f: &dyn Fn(&Val, &Val) -> Option<Val>) -> Self {
        let (Self::Set(a), Self::Set(b)) = (self, other) else {
            return Self::Top;
        };
        if a.len() * b.len() > MAX_COMBINATIONS {
            return Self::Top;
        }
        let mut out = Self::Set(Vec::new());
        for x in a {
            for y in b {
                match f(x, y) {
                    Some(value) => out = out.union(Self::one(value)),
                    None => return Self::Top,
                }
            }
        }
        out
    }

    /// Whether this is a truth value, and which.
    fn truth(&self) -> Tri {
        match self {
            Self::Set(values) if values == &[Val::Bool(true)] => Tri::True,
            Self::Set(values) if values == &[Val::Bool(false)] => Tri::False,
            Self::Set(values)
                if values.iter().all(|v| matches!(v, Val::Bool(_))) && !values.is_empty() =>
            {
                Tri::Maybe
            }
            _ => Tri::Unknown,
        }
    }
}

/// A condition's truth over the values tried.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tri {
    True,
    False,
    /// Either, and both are known to be possible.
    Maybe,
    Unknown,
}

impl Tri {
    const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Maybe, _) | (_, Self::Maybe) => Self::Maybe,
            _ => Self::True,
        }
    }

    const fn or(self, other: Self) -> Self {
        match (self, other) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Maybe, _) | (_, Self::Maybe) => Self::Maybe,
            _ => Self::False,
        }
    }

    const fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            other => other,
        }
    }
}

// MARK: - the engine

/// What a field is read through.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Recv {
    /// The current object, or a static field.
    This,
    Local(LocalId),
    Param(SymbolId),
    /// Another expression: two reads through it are told apart by where they
    /// are written, so that what one of them knows is not taken for the other.
    Other(u64),
}

/// Something a condition reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Atom {
    Param(SymbolId),
    Field(SymbolId, Recv),
    Local(LocalId),
}

/// The version a read has when it is not tied to a place in the code: it
/// stands for the atom at any time.
const ANY: u32 = u32::MAX;

/// An atom, in the frame it is read in, at a version: two reads of an atom
/// with the same version see the same value, because nothing that can change
/// it happened between them. A parameter at version `0` has what its callers
/// pass; at any other, what a write may have made of it.
type Key = (usize, Atom, u32);

/// The versions of the atoms a condition reads, as they were where it was
/// made; `None` for an expression that is read at any time.
type Ver<'a> = Option<&'a HashMap<Atom, u32>>;

fn version(ver: Ver<'_>, atom: &Atom) -> u32 {
    ver.map_or(ANY, |versions| versions.get(atom).copied().unwrap_or(0))
}

/// The atom a field or property read is, through its receiver.
fn field_atom(field: SymbolId, receiver: Option<&BoundExpression>) -> Atom {
    let through = match receiver.map(strip) {
        None => Recv::This,
        Some(receiver) => match &receiver.kind {
            E::This | E::Base | E::TypeExpression(_) | E::NamespaceExpression(_) => Recv::This,
            E::Local(l) => Recv::Local(*l),
            E::Parameter(p) => Recv::Param(*p),
            _ => Recv::Other(
                (u64::from(receiver.span.start()) << 32) | u64::from(receiver.span.end()),
            ),
        },
    };
    Atom::Field(field, through)
}

/// A variable of the body, or a field, that an expression is the place of.
fn place_atom(target: &BoundExpression) -> Option<Atom> {
    let target = strip(target);
    match &target.kind {
        E::Local(l) => Some(Atom::Local(*l)),
        E::Parameter(p) => Some(Atom::Param(*p)),
        E::Field {
            receiver, field, ..
        } => Some(field_atom(*field, receiver.as_deref())),
        E::Property {
            receiver, property, ..
        } => Some(field_atom(*property, receiver.as_deref())),
        _ => None,
    }
}

/// One bound body being looked at: the member asked about, a member called
/// on the way, or a caller whose arguments are being evaluated.
struct Frame {
    tree: usize,
    body: Arc<BoundBody>,
    /// The member the body is of.
    member: Option<SymbolId>,
    /// Where the walk starts, when that is a local function of the body
    /// rather than the body itself: its place in the body's list.
    local_function: Option<usize>,
    /// What the parameters are where a call on the way said: the argument
    /// it passed. A parameter not here has what its callers pass.
    arguments: HashMap<SymbolId, (Abs, Input)>,
}

/// What a condition tests.
#[derive(Clone, Debug)]
enum Test {
    /// That the expression is true.
    Truth(BoundExpression),
    /// That the expression is null.
    Null(BoundExpression),
    /// That the expression is zero.
    Zero(BoundExpression),
    /// That the first equals the second: a `case` label.
    Equals(BoundExpression, BoundExpression),
    /// That the index is outside the array.
    OutOfRange(BoundExpression, BoundExpression),
    /// That the string parses as the number type.
    Parses(BoundExpression, SpecialType),
    /// That the value matches one of these labels of a `switch`: each a
    /// pattern, and the `when` that has to hold with it.
    Matches(BoundExpression, Arc<Vec<Label>>, Range<usize>),
    /// Something the values cannot tell, said in words: "the sequence is
    /// empty". Whether it holds is not known.
    Opaque(String),
    /// A way in that may be closed, said in words: "the loop above does not
    /// return". It may hold and may not, and a failure behind it is at most
    /// possible, never certain.
    Reach(String),
    /// That the filter of a `catch` holds. A filter whose value is not
    /// known may hold or not.
    Filter(BoundExpression),
}

/// A `case` of a switch statement or an arm of a switch expression.
#[derive(Clone, Debug)]
struct Label {
    pattern: BoundPattern,
    when: Option<BoundExpression>,
}

impl Test {
    /// The expressions the test reads.
    fn expressions(&self) -> Vec<&BoundExpression> {
        match self {
            Self::Truth(e)
            | Self::Null(e)
            | Self::Zero(e)
            | Self::Parses(e, _)
            | Self::Filter(e) => vec![e],
            Self::Equals(a, b) | Self::OutOfRange(a, b) => vec![a, b],
            Self::Matches(governing, labels, range) => {
                let mut found = vec![governing];
                for label in &labels[range.clone()] {
                    pattern_expressions(&label.pattern, &mut found);
                    found.extend(&label.when);
                }
                found
            }
            Self::Opaque(_) | Self::Reach(_) => Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct Cond {
    frame: usize,
    test: Test,
    /// Whether the test holds on the way, or its opposite does.
    holds: bool,
    span: TextSpan,
    /// The version of each atom the test reads, as it was where the
    /// condition was made.
    versions: Arc<HashMap<Atom, u32>>,
}

/// A failure as found, before its verdict.
struct Found {
    kind: FailureKind,
    exception: String,
    exception_type: Option<Type>,
    message: Option<String>,
    frame: usize,
    span: TextSpan,
    conditions: Vec<Cond>,
    chain: Vec<CallStep>,
}

struct Engine<'s> {
    semantic: &'s Semantic,
    views: HashMap<usize, View<'s>>,
    frames: Vec<Frame>,
    /// Frames of callers, by their tree and body owner, so that one caller
    /// is evaluated once.
    caller_frames: HashMap<(usize, TextSpan), usize>,
    atoms: HashMap<Key, (Abs, Input)>,
    fields: HashMap<SymbolId, (Abs, Input)>,
    params: HashMap<SymbolId, (Abs, Input)>,
    /// Atoms and members being worked out, against cycles.
    evaluating: HashSet<Key>,
    evaluating_fields: HashSet<SymbolId>,
    evaluating_params: HashSet<SymbolId>,
    caller_depth: usize,
    /// The calls of each member, found once.
    sites: HashMap<SymbolId, Arc<Vec<Site>>>,
    /// What each body writes, by the body's address.
    scans: HashMap<usize, Arc<Scan>>,
    /// Whether each property is `{ get; set; }` with no bodies.
    auto_properties: HashMap<SymbolId, bool>,
    /// Whether calling a member runs code of the project's, apart from
    /// what it is handed.
    runs: HashMap<SymbolId, bool>,
}

/// The variables a body writes, found once for all that ask.
#[derive(Default)]
struct Scan {
    /// What each variable is given where a write names the value.
    assigned: HashMap<Atom, Vec<BoundExpression>>,
    /// Variables written in ways whose value is not tracked: `+=`, `++`,
    /// `ref` and `out`, a pattern, a `foreach`.
    opaque: HashSet<Atom>,
    /// Variables a lambda or a local function writes: they change whenever
    /// that code runs, which is whenever anything is called.
    closure: HashSet<Atom>,
}

impl Semantic {
    /// Every way the member at `offset` of `path` can fail, and whether each
    /// can happen. The member is the one the cursor names — a method, a
    /// constructor, a call of one — or else the one the cursor is in.
    ///
    /// Offsets are bytes of the compiled text.
    #[must_use]
    pub fn failability(&self, path: &Path, offset: u32) -> Option<Failability> {
        let tree = self.tree_index(path)?;
        let mut engine = Engine::new(self);
        let (member, owner) = engine.member_at(tree, offset)?;
        let body = engine.view(tree)?.body_for(&owner)?;
        let name = member.map_or_else(
            || "<body>".to_owned(),
            |member| self.compilation.symbols().qualified_name(member),
        );
        let frame = engine.push_frame(tree, body, member, None, HashMap::new());
        let mut found = Vec::new();
        let mut stack = member.into_iter().collect::<Vec<_>>();
        engine.collect(frame, &[], &[], &mut stack, &mut found);
        let mut failures: Vec<Failure> = Vec::new();
        for found in found {
            let failure = engine.judge(found);
            // A null or an index nobody can tell is not a finding: every
            // member reached through something would be one.
            let implicit = matches!(
                failure.kind,
                FailureKind::NullReference | FailureKind::IndexOutOfRange
            );
            if implicit && matches!(failure.verdict, Verdict::Unknown | Verdict::Never) {
                continue;
            }
            // The same receiver dereferenced again fails at the first one.
            let repeated = failures.iter().any(|kept| {
                kept.kind == failure.kind
                    && kept.path == failure.path
                    && kept.conditions == failure.conditions
                    && kept.chain.len() == failure.chain.len()
            });
            if implicit && repeated {
                continue;
            }
            failures.push(failure);
        }
        Some(Failability {
            member: name,
            failures,
        })
    }
}

impl<'s> Engine<'s> {
    fn new(semantic: &'s Semantic) -> Self {
        Self {
            semantic,
            views: HashMap::new(),
            frames: Vec::new(),
            caller_frames: HashMap::new(),
            atoms: HashMap::new(),
            fields: HashMap::new(),
            params: HashMap::new(),
            evaluating: HashSet::new(),
            evaluating_fields: HashSet::new(),
            evaluating_params: HashSet::new(),
            caller_depth: 0,
            sites: HashMap::new(),
            scans: HashMap::new(),
            auto_properties: HashMap::new(),
            runs: HashMap::new(),
        }
    }

    fn view(&mut self, tree: usize) -> Option<&mut View<'s>> {
        if !self.views.contains_key(&tree) {
            let view = self.semantic.view(tree)?;
            self.views.insert(tree, view);
        }
        self.views.get_mut(&tree)
    }

    fn model(&mut self, tree: usize) -> Option<&SemanticModel<'s>> {
        self.view(tree).map(|view| &view.model)
    }

    fn path(&self, tree: usize) -> PathBuf {
        self.semantic
            .path_of(tree)
            .map(Path::to_path_buf)
            .unwrap_or_default()
    }

    fn text(&self, tree: usize, span: TextSpan) -> String {
        self.semantic
            .compilation
            .trees()
            .source(tree)
            .and_then(|source| {
                source
                    .text()
                    .get(span.start() as usize..span.end() as usize)
            })
            .map(|text| text.split_whitespace().collect::<Vec<_>>().join(" "))
            .unwrap_or_default()
    }

    fn push_frame(
        &mut self,
        tree: usize,
        body: Arc<BoundBody>,
        member: Option<SymbolId>,
        local_function: Option<usize>,
        arguments: HashMap<SymbolId, (Abs, Input)>,
    ) -> usize {
        self.frames.push(Frame {
            tree,
            body,
            member,
            local_function,
            arguments,
        });
        self.frames.len() - 1
    }

    /// The member at `offset`, and the syntax that owns its body.
    fn member_at(&mut self, tree: usize, offset: u32) -> Option<(Option<SymbolId>, SyntaxNode)> {
        let view = self.view(tree)?;
        if let Some(token) = view.name_token_at(offset)
            && let Some(Resolved::Symbol(symbol)) = view.resolve(&token)
            && self.is_callable(symbol)
            && let Some((_, owner)) = self.body_owner_of(symbol)
        {
            return Some((Some(symbol), owner));
        }
        let view = self.view(tree)?;
        let token = view.root.find_token(offset)?;
        let owner = SemanticModel::body_owner(token.parent())?;
        let member = view.model.declared_symbol(&owner);
        Some((member, owner))
    }

    fn is_callable(&self, symbol: SymbolId) -> bool {
        matches!(
            self.semantic.compilation.symbols().get(symbol).kind,
            SymbolKind::Method | SymbolKind::Property
        )
    }

    /// Whether a property is `{ get; set; }` with no bodies: a field
    /// under another name, whose values are what is written to it.
    fn is_auto_property(&mut self, property: SymbolId) -> bool {
        if let Some(&known) = self.auto_properties.get(&property) {
            return known;
        }
        let found = self.find_auto_property(property);
        self.auto_properties.insert(property, found);
        found
    }

    fn find_auto_property(&mut self, property: SymbolId) -> bool {
        let symbols = self.semantic.compilation.symbols();
        let symbol = symbols.get(property);
        if symbol.kind != SymbolKind::Property || !in_project(self.semantic, property) {
            return false;
        }
        // What an abstract, virtual or interface property gives is what a
        // subtype's member gives, not what is written to this one.
        let in_interface = symbol
            .container
            .is_some_and(|c| symbols.get(c).type_kind() == Some(TypeKind::Interface));
        if in_interface
            || symbol.modifiers.contains(Modifiers::ABSTRACT)
            || symbol.modifiers.contains(Modifiers::VIRTUAL)
            || symbol.modifiers.contains(Modifiers::OVERRIDE)
        {
            return false;
        }
        let Some(location) = symbol.locations.first().copied() else {
            return false;
        };
        let Some(view) = self.view(location.tree) else {
            return false;
        };
        let Some(token) = view.root.find_token(location.span.start()) else {
            return false;
        };
        let Some(declaration) = std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find(|node| node.kind() == SyntaxKind::PropertyDeclaration)
        else {
            return false;
        };
        if declaration
            .child_of_kind(SyntaxKind::ArrowExpressionClause)
            .is_some()
        {
            return false;
        }
        declaration
            .child_of_kind(SyntaxKind::AccessorList)
            .is_some_and(|list| {
                list.children().all(|accessor| {
                    !accessor.children().any(|c| {
                        matches!(
                            c.kind(),
                            SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                        )
                    })
                })
            })
    }

    /// Where a member of the project has its body.
    fn body_owner_of(&mut self, member: SymbolId) -> Option<(usize, SyntaxNode)> {
        let locations = self
            .semantic
            .compilation
            .symbols()
            .get(member)
            .locations
            .clone();
        for location in locations {
            // A library's own source (the core library a project without
            // references is compiled against) says nothing about what runs.
            if !self.semantic.paths.contains_key(&location.tree) {
                continue;
            }
            let Some(view) = self.view(location.tree) else {
                continue;
            };
            let Some(token) = view.root.find_token(location.span.start()) else {
                continue;
            };
            let Some(owner) = SemanticModel::body_owner(token.parent()) else {
                continue;
            };
            let owner = getter(&owner).unwrap_or(owner);
            let has_body = owner.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                )
            });
            if has_body {
                return Some((location.tree, owner));
            }
        }
        None
    }

    fn body_of(&mut self, member: SymbolId) -> Option<(usize, Arc<BoundBody>)> {
        let (tree, owner) = self.body_owner_of(member)?;
        let body = self.view(tree)?.body_for(&owner)?;
        Some((tree, body))
    }

    // MARK: finding failures

    /// Every failure in the body of `frame`, under `conditions` that already
    /// hold on the way there through `chain`. `stack` is the members being
    /// followed, against recursion.
    fn collect(
        &mut self,
        frame: usize,
        conditions: &[Cond],
        chain: &[CallStep],
        stack: &mut Vec<SymbolId>,
        found: &mut Vec<Found>,
    ) {
        let body = self.frames[frame].body.clone();
        let local_function = self.frames[frame].local_function;
        let scan = self.scan(frame);
        let symbols = self.semantic.compilation.symbols();
        let by_ref = self.frames[frame]
            .member
            .and_then(|member| symbols.get(member).as_method())
            .map(|method| {
                method
                    .parameters
                    .iter()
                    .copied()
                    .filter(|p| {
                        symbols
                            .get(*p)
                            .as_parameter()
                            .is_some_and(|detail| detail.ref_kind != RefKind::None)
                    })
                    .collect()
            })
            .unwrap_or_default();
        let mut walker = Walker {
            engine: self,
            frame,
            chain: chain.to_vec(),
            stack,
            found: Vec::new(),
            catches: Vec::new(),
            state: State::default(),
            scan,
            by_ref,
            awaited: HashSet::new(),
        };
        let mut conds = conditions.to_vec();
        match local_function {
            Some(at) => {
                walker.statement(&body.local_functions[at].body, &mut conds);
            }
            None => {
                walker.statements(&body.statements, &mut conds);
            }
        }
        let mine = std::mem::take(&mut walker.found);
        found.extend(mine);
    }

    // MARK: what code changes

    /// Whether a field can change while the body runs: any but a constant
    /// or a `readonly` one.
    fn volatile_field(&self, field: SymbolId) -> bool {
        let modifiers = self.semantic.compilation.symbols().get(field).modifiers;
        !(modifiers.contains(Modifiers::READONLY) || modifiers.contains(Modifiers::CONST))
    }

    /// Whether calling a member runs code that may write any field. A
    /// member of the project does; so does what is handed a delegate to call.
    /// The library's own collections, strings and numbers run nothing of the
    /// project's.
    fn runs_code(
        &mut self,
        method: SymbolId,
        receiver: Option<&BoundExpression>,
        arguments: &[BoundExpression],
    ) -> bool {
        let semantic = self.semantic;
        let own = match self.runs.get(&method) {
            Some(&own) => own,
            None => {
                let symbols = semantic.compilation.symbols();
                let container = symbols
                    .get(method)
                    .container
                    .map(|c| symbols.qualified_name(c))
                    .unwrap_or_default();
                let own = in_project(semantic, method)
                    || !(PURE_NAMESPACES.iter().any(|ns| container.starts_with(ns))
                        || PURE_TYPES.contains(&container.as_str()));
                self.runs.insert(method, own);
                own
            }
        };
        if own {
            // `n.ToString()` is the number's, whichever type declares it.
            let symbols = semantic.compilation.symbols();
            let primitive = !in_project(semantic, method)
                && receiver.map(strip).is_some_and(|r| match &r.ty {
                    Type::Named { symbol, .. } => {
                        PURE_TYPES.contains(&symbols.qualified_name(*symbol).as_str())
                    }
                    _ => false,
                });
            if !primitive {
                return true;
            }
        }
        let callback = |e: &BoundExpression| {
            let e = strip(e);
            matches!(
                e.kind,
                E::Lambda(_)
                    | E::UnboundLambda(_)
                    | E::MethodGroup { .. }
                    | E::DelegateCreation { .. }
            ) || is_delegate(semantic, &e.ty)
        };
        receiver.into_iter().chain(arguments).any(callback)
    }

    /// What writing to a place changes.
    fn written_place(&mut self, target: &BoundExpression, out: &mut Effects) {
        let target = strip(target);
        match &target.kind {
            E::Local(l) => {
                out.written.insert(Atom::Local(*l));
            }
            E::Parameter(p) => {
                out.written.insert(Atom::Param(*p));
            }
            E::Field { field, .. } => {
                out.fields.insert(*field);
            }
            E::Property { property, receiver } => {
                if self.is_auto_property(*property) {
                    out.fields.insert(*property);
                } else if self.runs_code(*property, receiver.as_deref(), &[]) {
                    out.havoc = true;
                }
            }
            E::IndexerAccess {
                indexer,
                receiver,
                arguments,
            } if self.runs_code(*indexer, Some(receiver), arguments) => {
                out.havoc = true;
            }
            _ => {}
        }
    }

    /// What an expression changes, apart from what the expressions it holds
    /// do.
    fn node_effects(&mut self, e: &BoundExpression, out: &mut Effects) {
        match &e.kind {
            E::Assignment { target, .. } | E::CompoundAssignment { target, .. } => {
                self.written_place(target, out);
            }
            E::Increment { target, method, .. } => {
                self.written_place(target, out);
                out.havoc |= method.is_some();
            }
            E::RefArgument { kind, operand } if *kind != RefKind::In => {
                self.written_place(operand, out);
            }
            E::AddressOf { operand } | E::MakeRef(operand) => self.written_place(operand, out),
            E::Call {
                method,
                receiver,
                arguments,
                ..
            } => {
                out.havoc |= self.runs_code(*method, receiver.as_deref(), arguments);
            }
            E::ObjectCreation {
                constructor,
                arguments,
                ..
            } => {
                out.havoc |= constructor.is_none_or(|c| self.runs_code(c, None, arguments));
            }
            E::Property { property, receiver } => {
                if !self.is_auto_property(*property) {
                    out.havoc |= self.runs_code(*property, receiver.as_deref(), &[]);
                }
            }
            E::IndexerAccess {
                indexer,
                receiver,
                arguments,
            } => {
                out.havoc |= self.runs_code(*indexer, Some(receiver), arguments);
            }
            E::Await { .. }
            | E::EventAssignment { .. }
            | E::Dynamic(_)
            | E::FunctionPointerCall { .. }
            | E::With { .. } => out.havoc = true,
            E::IsPattern { pattern, .. } => self.pattern_effects(pattern, out),
            E::Switch { arms, .. } => {
                for arm in arms {
                    self.pattern_effects(&arm.pattern, out);
                }
            }
            _ => {}
        }
    }

    /// The locals a pattern gives a value.
    fn pattern_effects(&self, pattern: &BoundPattern, out: &mut Effects) {
        let mut declared = Vec::new();
        pattern_locals(pattern, &mut declared);
        out.written.extend(declared.into_iter().map(Atom::Local));
    }

    /// Everything an expression changes, in the expressions it holds too,
    /// but not in a lambda it makes.
    fn effects_of(&mut self, e: &BoundExpression, out: &mut Effects) {
        self.node_effects(e, out);
        for child in expression_children(e) {
            self.effects_of(child, out);
        }
    }

    /// Everything a statement changes, lambdas it makes included: they may
    /// run in it.
    fn statement_effects(&mut self, frame: usize, statement: &BoundStatement, out: &mut Effects) {
        let body = self.frames[frame].body.clone();
        walk_statement(&body, statement, &mut |visited| match visited {
            Visited::Expression(e) => self.node_effects(e, out),
            Visited::Statement(s) => match &s.kind {
                S::LocalDeclaration { local, .. } => {
                    out.written.insert(Atom::Local(*local));
                }
                S::ForEach { local, .. } => {
                    out.written.insert(Atom::Local(*local));
                    out.havoc = true;
                }
                S::Using { resources, .. } => {
                    out.written
                        .extend(resources.iter().map(|r| Atom::Local(r.local)));
                    out.havoc = true;
                }
                S::Lock { .. } | S::YieldReturn(_) | S::ConstructorInitializer { .. } => {
                    out.havoc = true;
                }
                S::Try { catches, .. } => {
                    out.written
                        .extend(catches.iter().filter_map(|c| c.local).map(Atom::Local));
                    for filter in catches.iter().filter_map(|c| c.filter.as_ref()) {
                        self.effects_of(filter, out);
                    }
                }
                S::Switch { sections, .. } => {
                    for section in sections {
                        for label in &section.labels {
                            if let BoundSwitchLabel::Case(case) = label {
                                self.pattern_effects(&case.pattern, out);
                            }
                        }
                    }
                }
                _ => {}
            },
        });
    }

    // MARK: judging

    fn judge(&mut self, found: Found) -> Failure {
        // The atoms the conditions read, and what each can be.
        let mut keys: Vec<Key> = Vec::new();
        for cond in &found.conditions {
            for expression in cond.test.expressions() {
                atoms_of(expression, &mut |atom| {
                    let at = cond.versions.get(&atom).copied().unwrap_or(0);
                    let key = (cond.frame, atom, at);
                    if !keys.contains(&key) {
                        keys.push(key);
                    }
                });
            }
        }
        let mut known: Vec<(Key, Vec<Val>)> = Vec::new();
        let mut inputs: Vec<Input> = Vec::new();
        for &key in &keys {
            let (abs, input) = self.atom(key);
            if !inputs.contains(&input) {
                inputs.push(input);
            }
            if let Abs::Set(values) = abs {
                known.push((key, values));
            }
        }
        // Enumerate the known atoms together, the fewest values first,
        // while the combinations stay few.
        known.sort_by_key(|(_, values)| values.len());
        let mut product = 1usize;
        let mut enumerated = Vec::new();
        for (key, values) in known {
            if values.is_empty() {
                continue;
            }
            if product.saturating_mul(values.len()) > MAX_COMBINATIONS {
                break;
            }
            product *= values.len();
            enumerated.push((key, values));
        }
        let mut results: Vec<Tri> = Vec::new();
        let mut assignment: HashMap<Key, Val> = HashMap::new();
        self.enumerate(
            &found.conditions,
            &enumerated,
            0,
            &mut assignment,
            &mut results,
        );
        let verdict = if found.conditions.is_empty() {
            Verdict::Always
        } else if results.iter().all(|r| *r == Tri::False) {
            Verdict::Never
        } else if results.iter().all(|r| *r == Tri::True) {
            Verdict::Always
        } else if results.contains(&Tri::Unknown) {
            Verdict::Unknown
        } else {
            Verdict::Possible
        };
        let conditions = found
            .conditions
            .iter()
            .map(|cond| self.condition(cond))
            .collect();
        let frame = &self.frames[found.frame];
        Failure {
            kind: found.kind,
            exception: found.exception,
            message: found.message,
            path: self.path(frame.tree),
            span: found.span,
            conditions,
            chain: found.chain,
            verdict,
            inputs,
        }
    }

    fn enumerate(
        &mut self,
        conditions: &[Cond],
        atoms: &[(Key, Vec<Val>)],
        at: usize,
        assignment: &mut HashMap<Key, Val>,
        results: &mut Vec<Tri>,
    ) {
        if let Some((key, values)) = atoms.get(at) {
            for value in values {
                assignment.insert(*key, value.clone());
                self.enumerate(conditions, atoms, at + 1, assignment, results);
            }
            assignment.remove(key);
            return;
        }
        let mut all = Tri::True;
        for cond in conditions {
            all = all.and(self.test(cond, assignment));
            if all == Tri::False {
                break;
            }
        }
        results.push(all);
    }

    fn test(&mut self, cond: &Cond, assignment: &HashMap<Key, Val>) -> Tri {
        let versions = cond.versions.clone();
        let at = Some(&*versions);
        let frame = cond.frame;
        let value = match &cond.test {
            Test::Truth(e) => self.eval(frame, e, assignment, at),
            Test::Null(e) => {
                let v = self.eval(frame, e, assignment, at);
                v.map(&|v| Some(Val::Bool(*v == Val::Null)))
            }
            Test::Zero(e) => {
                let v = self.eval(frame, e, assignment, at);
                v.map(&|v| v.number().map(|n| Val::Bool(n == 0.0)))
            }
            Test::Equals(a, b) => {
                let a = self.eval(frame, a, assignment, at);
                let b = self.eval(frame, b, assignment, at);
                a.map2(&b, &|x, y| equal(x, y).map(Val::Bool))
            }
            Test::OutOfRange(array, index) => {
                let array = self.eval(frame, array, assignment, at);
                let index = self.eval(frame, index, assignment, at);
                array.map2(&index, &|a, i| match (a, i.integer()?) {
                    (Val::Array(length), i) => {
                        Some(Val::Bool(i < 0 || i >= i128::try_from(*length).ok()?))
                    }
                    _ => None,
                })
            }
            Test::Parses(text, special) => {
                let text = self.eval(frame, text, assignment, at);
                let special = *special;
                text.map(&|v| match v {
                    Val::Str(s) => Some(Val::Bool(parses(s, special))),
                    Val::Null => Some(Val::Bool(false)),
                    _ => None,
                })
            }
            Test::Matches(governing, labels, range) => {
                self.matches(frame, governing, &labels[range.clone()], assignment, at)
            }
            Test::Opaque(_) => Abs::Top,
            Test::Reach(_) => Abs::Set(vec![Val::Bool(true), Val::Bool(false)]),
            Test::Filter(e) => match self.eval(frame, e, assignment, at) {
                value if value.truth() == Tri::Unknown => {
                    Abs::Set(vec![Val::Bool(true), Val::Bool(false)])
                }
                value => value,
            },
        };
        let truth = value.truth();
        if cond.holds { truth } else { truth.not() }
    }

    /// Whether the governing value matches one of the labels, for each value
    /// it can have.
    fn matches(
        &mut self,
        frame: usize,
        governing: &BoundExpression,
        labels: &[Label],
        assignment: &HashMap<Key, Val>,
        at: Ver<'_>,
    ) -> Abs {
        let Abs::Set(values) = self.eval(frame, governing, assignment, at) else {
            return Abs::Top;
        };
        let mut out = Abs::Set(Vec::new());
        for value in &values {
            let mut any = Tri::False;
            for label in labels {
                let mut matched =
                    self.pattern(frame, value, &label.pattern, governing, assignment, at);
                if matched != Tri::False
                    && let Some(when) = &label.when
                {
                    matched = matched.and(self.eval(frame, when, assignment, at).truth());
                }
                any = any.or(matched);
                if any == Tri::True {
                    break;
                }
            }
            out = match any {
                Tri::True => out.union(Abs::one(Val::Bool(true))),
                Tri::False => out.union(Abs::one(Val::Bool(false))),
                Tri::Maybe => out
                    .union(Abs::one(Val::Bool(true)))
                    .union(Abs::one(Val::Bool(false))),
                Tri::Unknown => return Abs::Top,
            };
        }
        out
    }

    /// Whether a value matches a pattern, where that can be told from the
    /// value alone.
    fn pattern(
        &mut self,
        frame: usize,
        value: &Val,
        pattern: &BoundPattern,
        governing: &BoundExpression,
        assignment: &HashMap<Key, Val>,
        at: Ver<'_>,
    ) -> Tri {
        let single =
            |this: &mut Self, e: &BoundExpression| match this.eval(frame, e, assignment, at) {
                Abs::Set(values) if values.len() == 1 => values.into_iter().next(),
                _ => None,
            };
        match &pattern.kind {
            P::Discard | P::Var { .. } => Tri::True,
            P::Constant(constant) => single(self, constant)
                .and_then(|constant| equal(value, &constant))
                .map_or(
                    Tri::Unknown,
                    |same| if same { Tri::True } else { Tri::False },
                ),
            P::Relational {
                operator,
                value: bound,
            } => {
                // `null` is neither above nor below anything.
                if *value == Val::Null {
                    return Tri::False;
                }
                let (Some(bound), Some(value)) =
                    (single(self, bound).and_then(|b| b.number()), value.number())
                else {
                    return Tri::Unknown;
                };
                let holds = match operator {
                    BinaryOperator::LessThan => value < bound,
                    BinaryOperator::GreaterThan => value > bound,
                    BinaryOperator::LessThanOrEqual => value <= bound,
                    BinaryOperator::GreaterThanOrEqual => value >= bound,
                    _ => return Tri::Unknown,
                };
                if holds { Tri::True } else { Tri::False }
            }
            // A type test fails for null; for anything else it is only known
            // where the type tested is the type the value already has.
            P::Type(ty) | P::Declaration { ty, .. } => {
                if *value == Val::Null {
                    Tri::False
                } else if governing.ty == *ty {
                    Tri::True
                } else {
                    Tri::Unknown
                }
            }
            P::Not(inner) => self
                .pattern(frame, value, inner, governing, assignment, at)
                .not(),
            P::And(a, b) => {
                let a = self.pattern(frame, value, a, governing, assignment, at);
                if a == Tri::False {
                    return Tri::False;
                }
                a.and(self.pattern(frame, value, b, governing, assignment, at))
            }
            P::Or(a, b) => {
                let a = self.pattern(frame, value, a, governing, assignment, at);
                if a == Tri::True {
                    return Tri::True;
                }
                a.or(self.pattern(frame, value, b, governing, assignment, at))
            }
            // `{ }`: anything that is not null.
            P::Recursive(recursive)
                if recursive.ty.is_none()
                    && recursive.properties.is_empty()
                    && recursive.positional.is_empty()
                    && recursive.deconstruct.is_none() =>
            {
                if *value == Val::Null {
                    Tri::False
                } else {
                    Tri::True
                }
            }
            _ => Tri::Unknown,
        }
    }

    fn condition(&self, cond: &Cond) -> Condition {
        let tree = self.frames[cond.frame].tree;
        let text_of = |e: &BoundExpression| self.text(tree, e.span);
        let text = match (&cond.test, cond.holds) {
            (Test::Truth(e) | Test::Filter(e), true) => text_of(e),
            (Test::Truth(e) | Test::Filter(e), false) => negated(e, &text_of),
            (Test::Null(e), holds) => {
                format!("{} {} null", text_of(e), if holds { "==" } else { "!=" })
            }
            (Test::Zero(e), holds) => {
                format!("{} {} 0", text_of(e), if holds { "==" } else { "!=" })
            }
            (Test::Equals(a, b), holds) => {
                format!(
                    "{} {} {}",
                    text_of(a),
                    if holds { "==" } else { "!=" },
                    text_of(b)
                )
            }
            (Test::OutOfRange(a, i), _) => {
                let (a, i) = (text_of(a), text_of(i));
                format!("{i} < 0 || {i} >= {a}.Length")
            }
            (Test::Parses(e, _), holds) => {
                format!(
                    "{}{} is a number",
                    text_of(e),
                    if holds { "" } else { " not" }
                )
            }
            (Test::Matches(governing, labels, range), holds) => {
                let governing = text_of(governing);
                let labels = &labels[range.clone()];
                let patterns: Vec<String> = labels
                    .iter()
                    .map(|label| {
                        // `case 1:`, `case int n when n > 5:` and `1` all
                        // name the pattern alone.
                        let text = self.text(tree, label.pattern.span);
                        let text = text.strip_prefix("case ").unwrap_or(&text);
                        let text = text.split(" when ").next().unwrap_or(text);
                        text.trim_end_matches(':').trim().to_owned()
                    })
                    .collect();
                if labels.iter().any(|label| label.when.is_some()) {
                    let each: Vec<String> = labels
                        .iter()
                        .zip(&patterns)
                        .map(|(label, pattern)| match &label.when {
                            Some(when) => {
                                format!("{governing} is {pattern} && {}", text_of(when))
                            }
                            None => format!("{governing} is {pattern}"),
                        })
                        .collect();
                    let any = each
                        .iter()
                        .map(|one| format!("({one})"))
                        .collect::<Vec<_>>()
                        .join(" || ");
                    if holds { any } else { format!("!({any})") }
                } else if holds {
                    format!("{governing} is {}", patterns.join(" or "))
                } else if let [one] = patterns.as_slice() {
                    format!("{governing} is not {one}")
                } else {
                    format!("{governing} is not ({})", patterns.join(" or "))
                }
            }
            (Test::Opaque(words) | Test::Reach(words), _) => words.clone(),
        };
        Condition {
            text,
            path: self.path(tree),
            span: cond.span,
        }
    }

    // MARK: evaluating

    fn eval(
        &mut self,
        frame: usize,
        e: &BoundExpression,
        assignment: &HashMap<Key, Val>,
        at: Ver<'_>,
    ) -> Abs {
        match &e.kind {
            E::Literal(value) => Abs::one(Val::from_constant(value)),
            E::Parameter(p) => {
                let atom = Atom::Param(*p);
                self.read((frame, atom, version(at, &atom)), assignment)
            }
            E::Local(l) => {
                let atom = Atom::Local(*l);
                self.read((frame, atom, version(at, &atom)), assignment)
            }
            E::Field { field, receiver } => {
                if let Some(constant) = self.constant(*field) {
                    return Abs::one(constant);
                }
                let atom = field_atom(*field, receiver.as_deref());
                self.read((frame, atom, version(at, &atom)), assignment)
            }
            E::Default(ty) => self.default_of(frame, ty).map_or(Abs::Top, Abs::one),
            E::Conversion { operand, .. } => {
                let value = self.eval(frame, operand, assignment, at);
                let special = self.special(frame, &e.ty);
                value.map(&|v| convert(v, special).filter(|v| fits(special, v)))
            }
            E::Unary { operator, operand } => {
                let value = self.eval(frame, operand, assignment, at);
                let operator = *operator;
                let special = self.special(frame, &e.ty);
                value.map(&|v| unary(operator, v).filter(|v| fits(special, v)))
            }
            E::Binary {
                operator,
                left,
                right,
            } => {
                let left = self.eval(frame, left, assignment, at);
                // `a && b` with `a` false is false, whatever `b` would be.
                match (operator, left.truth()) {
                    (BinaryOperator::LogicalAnd, Tri::False) => return Abs::one(Val::Bool(false)),
                    (BinaryOperator::LogicalOr, Tri::True) => return Abs::one(Val::Bool(true)),
                    _ => {}
                }
                let right = self.eval(frame, right, assignment, at);
                let operator = *operator;
                let special = self.special(frame, &e.ty);
                let integral = special.is_some_and(is_integral);
                // A result the type cannot hold wraps, or throws: not known.
                left.map2(&right, &|a, b| {
                    binary(operator, a, b, integral).filter(|v| fits(special, v))
                })
            }
            E::Conditional {
                condition,
                consequence,
                alternative,
            } => match self.eval(frame, condition, assignment, at).truth() {
                Tri::True => self.eval(frame, consequence, assignment, at),
                Tri::False => self.eval(frame, alternative, assignment, at),
                _ => {
                    let a = self.eval(frame, consequence, assignment, at);
                    let b = self.eval(frame, alternative, assignment, at);
                    a.union(b)
                }
            },
            E::ArrayCreation {
                lengths, elements, ..
            } => match lengths.as_slice() {
                [] => Abs::one(Val::Array(elements.len())),
                [length] => self.eval(frame, length, assignment, at).map(&|v| {
                    v.integer()
                        .and_then(|n| usize::try_from(n).ok())
                        .map(Val::Array)
                }),
                _ => Abs::one(Val::Object),
            },
            E::ArrayLength { array } => self.eval(frame, array, assignment, at).map(&|v| match v {
                Val::Array(length) => i128::try_from(*length).ok().map(Val::Int),
                _ => None,
            }),
            E::ObjectCreation { .. }
            | E::This
            | E::Lambda(_)
            | E::DelegateCreation { .. }
            | E::InterpolatedString(_) => Abs::one(Val::Object),
            E::Property { property, receiver } if self.is_auto_property(*property) => {
                let atom = field_atom(*property, receiver.as_deref());
                self.read((frame, atom, version(at, &atom)), assignment)
            }
            _ => Abs::Top,
        }
    }

    fn read(&mut self, key: Key, assignment: &HashMap<Key, Val>) -> Abs {
        if let Some(value) = assignment.get(&key) {
            return Abs::one(value.clone());
        }
        self.atom(key).0
    }

    /// What an atom can be, and how that was found.
    fn atom(&mut self, key: Key) -> (Abs, Input) {
        // What a value is does not depend on the receiver a field is read
        // through, nor on which version of a variable, beyond whether a
        // parameter has been written.
        let key = match key.1 {
            Atom::Param(_) => (key.0, key.1, u32::from(key.2 != 0)),
            Atom::Field(field, _) => (key.0, Atom::Field(field, Recv::This), 0),
            Atom::Local(_) => (key.0, key.1, 0),
        };
        if let Some(found) = self.atoms.get(&key) {
            return found.clone();
        }
        if !self.evaluating.insert(key) {
            let name = self.atom_name(key);
            return (Abs::Top, unknown_input(name));
        }
        let (frame, atom, written) = key;
        let found = match atom {
            Atom::Param(p) => {
                let entry = match self.frames[frame].arguments.get(&p) {
                    Some(found) => found.clone(),
                    None => self.parameter(frame, p),
                };
                if written == 0 {
                    entry
                } else {
                    self.written_parameter(frame, p, entry)
                }
            }
            // A property with a body computes what it gives: not an atom.
            Atom::Field(f, _)
                if self.semantic.compilation.symbols().get(f).kind == SymbolKind::Property
                    && !self.is_auto_property(f) =>
            {
                let name = self.atom_name(key);
                (Abs::Top, unknown_input(name))
            }
            Atom::Field(f, _) => self.field(f),
            Atom::Local(l) => self.local(frame, l),
        };
        self.evaluating.remove(&key);
        self.atoms.insert(key, found.clone());
        found
    }

    fn atom_name(&self, (frame, atom, _): Key) -> String {
        let symbols = self.semantic.compilation.symbols();
        match atom {
            Atom::Param(s) | Atom::Field(s, _) => symbols.get(s).name.clone(),
            Atom::Local(l) => self.frames[frame]
                .body
                .locals
                .get(l.0 as usize)
                .map(|local| local.name.clone())
                .unwrap_or_default(),
        }
    }

    fn constant(&mut self, field: SymbolId) -> Option<Val> {
        let symbol = self.semantic.compilation.symbols().get(field);
        if !symbol.modifiers.contains(Modifiers::CONST) && symbol.kind != SymbolKind::Field {
            return None;
        }
        let is_enum_member = symbol
            .container
            .and_then(|c| self.semantic.compilation.symbols().get(c).as_named_type())
            .is_some_and(|t| t.type_kind == Some(TypeKind::Enum));
        if !symbol.modifiers.contains(Modifiers::CONST) && !is_enum_member {
            return None;
        }
        let tree = symbol.locations.first().map_or(0, |l| l.tree);
        let model = self.model(tree)?;
        model
            .binder()
            .constant_value(field)
            .map(|v| Val::from_constant(&v))
    }

    fn special(&mut self, frame: usize, ty: &Type) -> Option<SpecialType> {
        let tree = self.frames[frame].tree;
        let model = self.model(tree)?;
        model.binder().special_of(ty)
    }

    fn default_of(&mut self, frame: usize, ty: &Type) -> Option<Val> {
        Some(match self.special(frame, ty) {
            Some(SpecialType::Boolean) => Val::Bool(false),
            Some(SpecialType::Char) => Val::Char('\0'),
            Some(SpecialType::Single | SpecialType::Double) => Val::Float(0.0),
            Some(s) if is_integral(s) => Val::Int(0),
            Some(SpecialType::String | SpecialType::Object) => Val::Null,
            _ if is_reference(self.semantic, ty) => Val::Null,
            _ => return None,
        })
    }

    // MARK: inputs

    /// What a parameter is given by every call in the project.
    fn parameter(&mut self, frame: usize, parameter: SymbolId) -> (Abs, Input) {
        if let Some(found) = self.params.get(&parameter) {
            return found.clone();
        }
        let symbols = self.semantic.compilation.symbols();
        let name = symbols.get(parameter).name.clone();
        let owns = |m: &SymbolId| {
            symbols
                .get(*m)
                .as_method()
                .is_some_and(|method| method.parameters.contains(&parameter))
        };
        let Some(member) = self.frames[frame]
            .member
            .filter(owns)
            .or_else(|| symbols.get(parameter).container.filter(owns))
        else {
            return (Abs::Top, unknown_input(name));
        };
        let index = symbols
            .get(member)
            .as_method()
            .and_then(|method| method.parameters.iter().position(|p| *p == parameter))
            .unwrap_or(0);
        let input = |values: &Abs, origin, places| Input {
            name: name.clone(),
            values: shown(values),
            origin,
            places,
        };
        let escapes = self.escapes(member) || self.implements_interface(member);
        let found = if escapes
            || self.caller_depth >= CALLER_DEPTH
            || !self.evaluating_params.insert(member)
        {
            let origin = if escapes {
                Origin::Escapes
            } else {
                Origin::Unknown
            };
            (Abs::Top, input(&Abs::Top, origin, Vec::new()))
        } else {
            self.caller_depth += 1;
            let sites = match self.sites.get(&member) {
                Some(sites) => sites.clone(),
                None => {
                    let sites = Arc::new(self.call_sites(member));
                    self.sites.insert(member, sites.clone());
                    sites
                }
            };
            let mut values = Abs::Set(Vec::new());
            let mut places = Vec::new();
            let mut escaped = false;
            for site in sites.iter() {
                match site {
                    Site::Call {
                        frame,
                        arguments,
                        span,
                    } => {
                        let tree = self.frames[*frame].tree;
                        if places.len() < MAX_PLACES {
                            places.push((self.path(tree), *span));
                        }
                        let value = match arguments.get(index) {
                            Some(argument) => {
                                self.eval(*frame, strip_ref(argument), &HashMap::new(), None)
                            }
                            None => Abs::Top,
                        };
                        values = values.union(value);
                    }
                    Site::Escape => escaped = true,
                }
            }
            self.caller_depth -= 1;
            self.evaluating_params.remove(&member);
            let calls = sites
                .iter()
                .filter(|s| matches!(s, Site::Call { .. }))
                .count();
            if escaped {
                (Abs::Top, input(&Abs::Top, Origin::Escapes, places))
            } else if calls == 0 {
                (Abs::Top, input(&Abs::Top, Origin::NoCallers, places))
            } else {
                let origin = Origin::Callers { count: calls };
                let input = input(&values, origin, places);
                (values, input)
            }
        };
        self.params.insert(parameter, found.clone());
        found
    }

    /// Whether a member implements one of an interface: calls through the
    /// interface reach it without naming it.
    fn implements_interface(&mut self, member: SymbolId) -> bool {
        let semantic = self.semantic;
        let symbols = semantic.compilation.symbols();
        let symbol = symbols.get(member);
        if symbol
            .as_method()
            .is_some_and(|m| m.method_kind != MethodKind::Ordinary)
        {
            return false;
        }
        // `void IShape.Draw()` is reached only through the interface.
        if symbol.name.contains('.') {
            return true;
        }
        let Some(container) = symbol.container else {
            return false;
        };
        let name = symbol.name.clone();
        let arity = symbol.as_method().map(|m| m.parameters.len());
        let Some(tree) = symbols
            .get(container)
            .locations
            .first()
            .map(|location| location.tree)
        else {
            return false;
        };
        let Some(model) = self.model(tree) else {
            return false;
        };
        let binder = model.binder();
        let mut pending = vec![container];
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            for base in binder.base_types_of(ty) {
                let Type::Named { symbol: base, .. } = base else {
                    continue;
                };
                let declared = symbols.get(base);
                if declared.type_kind() == Some(TypeKind::Interface)
                    && declared.members.iter().any(|m| {
                        let m = symbols.get(*m);
                        m.name == name && m.as_method().map(|m| m.parameters.len()) == arity
                    })
                {
                    return true;
                }
                pending.push(base);
            }
        }
        false
    }

    /// Whether a member can be reached other than by the calls that name
    /// it: through a base or an interface, from outside the project.
    fn escapes(&self, member: SymbolId) -> bool {
        let symbols = self.semantic.compilation.symbols();
        let symbol = symbols.get(member);
        let dispatched = symbol.modifiers.contains(Modifiers::VIRTUAL)
            || symbol.modifiers.contains(Modifiers::ABSTRACT)
            || symbol.modifiers.contains(Modifiers::OVERRIDE);
        let in_interface = symbol
            .container
            .and_then(|c| symbols.get(c).as_named_type())
            .is_some_and(|t| t.type_kind == Some(TypeKind::Interface));
        let entry = symbol
            .as_method()
            .is_some_and(|m| matches!(m.method_kind, MethodKind::StaticConstructor))
            || symbol.name == "Main";
        dispatched || in_interface || entry
    }

    /// Every place in the project that calls `member`, with its arguments
    /// and a frame to evaluate them in.
    fn call_sites(&mut self, member: SymbolId) -> Vec<Site> {
        let symbols = self.semantic.compilation.symbols();
        let symbol = symbols.get(member);
        let is_constructor = symbol
            .as_method()
            .is_some_and(|m| m.method_kind == MethodKind::Constructor);
        let word = if is_constructor {
            symbol
                .container
                .map(|c| symbols.get(c).name.clone())
                .unwrap_or_default()
        } else {
            symbol.name.clone()
        };
        let mut sites = Vec::new();
        let mut trees: Vec<usize> = self.semantic.paths.keys().copied().collect();
        trees.sort_unstable();
        for tree in trees {
            let Some(text) = self
                .semantic
                .compilation
                .trees()
                .source(tree)
                .map(|s| s.text())
            else {
                continue;
            };
            let mentions = contains_word(text, &word)
                || (is_constructor && (contains_word(text, "this") || contains_word(text, "base")));
            if !mentions {
                continue;
            }
            let (bodies, missed) = self.bodies_mentioning(tree, &word, is_constructor);
            if missed {
                sites.push(Site::Escape);
            }
            for (owner, body) in bodies {
                let caller = self
                    .view(tree)
                    .and_then(|view| view.model.declared_symbol(&owner));
                let mut calls: Vec<(Vec<BoundExpression>, TextSpan)> = Vec::new();
                let mut escaped = false;
                walk_everything(&body, &mut |visited| match visited {
                    Visited::Expression(e) => match &e.kind {
                        E::Call {
                            method, arguments, ..
                        } if *method == member => {
                            calls.push((arguments.clone(), e.span));
                        }
                        E::ObjectCreation {
                            constructor: Some(c),
                            arguments,
                            ..
                        } if *c == member => calls.push((arguments.clone(), e.span)),
                        E::DelegateCreation { method, .. } | E::MethodAddress { method, .. }
                            if *method == member =>
                        {
                            escaped = true;
                        }
                        E::MethodGroup { candidates, .. } if candidates.contains(&member) => {
                            escaped = true;
                        }
                        _ => {}
                    },
                    Visited::Statement(s) => {
                        if let S::ConstructorInitializer {
                            constructor: Some(c),
                            arguments,
                            ..
                        } = &s.kind
                            && *c == member
                        {
                            calls.push((arguments.clone(), s.span));
                        }
                    }
                });
                if escaped {
                    sites.push(Site::Escape);
                }
                if calls.is_empty() {
                    continue;
                }
                let key = (tree, owner.span());
                let frame = match self.caller_frames.get(&key) {
                    Some(&frame) => frame,
                    None => {
                        let frame =
                            self.push_frame(tree, body.clone(), caller, None, HashMap::new());
                        self.caller_frames.insert(key, frame);
                        frame
                    }
                };
                for (arguments, span) in calls {
                    sites.push(Site::Call {
                        frame,
                        arguments,
                        span,
                    });
                }
            }
        }
        sites
    }

    /// The bodies of `tree` that hold the word: each with the syntax that
    /// owns it; and whether one of them could not be bound.
    fn bodies_mentioning(
        &mut self,
        tree: usize,
        word: &str,
        constructor: bool,
    ) -> (Vec<(SyntaxNode, Arc<BoundBody>)>, bool) {
        let Some(view) = self.view(tree) else {
            return (Vec::new(), true);
        };
        let owners: Vec<SyntaxNode> = {
            let mut seen = HashSet::new();
            view.root
                .descendant_tokens()
                .filter(|token| match token.kind() {
                    SyntaxKind::IdentifierToken => token.value_text() == word,
                    SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword => constructor,
                    _ => false,
                })
                .filter_map(|token| SemanticModel::body_owner(token.parent()))
                .filter(|owner| seen.insert(owner.span()))
                .collect()
        };
        // A body that does not bind may be the one that calls or writes:
        // the caller is told, so that it does not take the rest for all.
        let mut missed = false;
        let bodies = owners
            .into_iter()
            .filter_map(|owner| {
                let body = view.body_for(&owner);
                // A file is a body only for its top-level statements: a
                // name in a declaration's header is in no body at all.
                missed |= body.is_none() && owner.kind() != SyntaxKind::CompilationUnit;
                // Nor is a body with errors to be trusted: what did not bind
                // may be the call or the write being looked for.
                missed |= body.as_ref().is_some_and(|body| {
                    body.diagnostics
                        .iter()
                        .any(|(at, diagnostic)| *at == tree && diagnostic.is_error())
                });
                Some((owner, body?))
            })
            .collect();
        (bodies, missed)
    }

    /// What a field can hold: its initializer and everything written to it.
    fn field(&mut self, field: SymbolId) -> (Abs, Input) {
        if let Some(found) = self.fields.get(&field) {
            return found.clone();
        }
        let symbols = self.semantic.compilation.symbols();
        let symbol = symbols.get(field);
        let name = symbol.name.clone();
        if !self.evaluating_fields.insert(field) {
            return (Abs::Top, unknown_input(name));
        }
        // A primary constructor's parameter, kept in a field the language
        // makes (`<window>P`): what the constructor's callers pass.
        if name.starts_with('<')
            && let Some(parameter) = self.captured_parameter(field)
        {
            let frame = self.frames.len().saturating_sub(1);
            let found = self.parameter(frame, parameter);
            self.evaluating_fields.remove(&field);
            self.fields.insert(field, found.clone());
            return found;
        }
        let symbol = self.semantic.compilation.symbols().get(field);
        // What the library declares is not written here.
        if !in_project(self.semantic, field) {
            self.evaluating_fields.remove(&field);
            return (Abs::Top, unknown_input(name));
        }
        // A `required` member is set by every `new`: its default is never
        // seen.
        let required = symbol.modifiers.contains(Modifiers::REQUIRED);
        let readonly = symbol.modifiers.contains(Modifiers::READONLY);
        let is_static = symbol.modifiers.contains(Modifiers::STATIC);
        let public = symbol.accessibility == rustlyn_semantics::Accessibility::Public;
        let is_property = symbol.kind == SymbolKind::Property;
        let field_initializer = symbol.as_field().is_some_and(|f| f.has_initializer);
        let container = symbol.container;
        let locations = symbol.locations.clone();
        let declarator = locations.first().and_then(|location| {
            let view = self.view(location.tree)?;
            let token = view.root.find_token(location.span.start())?;
            let owner = SemanticModel::body_owner(token.parent())?;
            Some((location.tree, owner))
        });
        let has_initializer = field_initializer
            || (is_property
                && declarator.as_ref().is_some_and(|(_, d)| {
                    d.child_of_kind(SyntaxKind::EqualsValueClause).is_some()
                }));
        let serialized = declarator.as_ref().is_some_and(|(_, declarator)| {
            let declaration = std::iter::once(declarator.clone())
                .chain(declarator.ancestors())
                .find(|a| {
                    matches!(
                        a.kind(),
                        SyntaxKind::FieldDeclaration | SyntaxKind::PropertyDeclaration
                    )
                });
            declaration.is_some_and(|d| {
                d.children()
                    .filter(|c| c.kind() == SyntaxKind::AttributeList)
                    .any(|list| list.text().contains("SerializeField"))
            })
        }) || (self.semantic.project.kind == ProjectKind::Unity
            && !is_property
            && public
            && !readonly
            && !is_static);
        let found = if serialized {
            (
                Abs::Top,
                Input {
                    name: name.clone(),
                    values: None,
                    origin: Origin::Serialized,
                    places: Vec::new(),
                },
            )
        } else {
            let mut values = Abs::Set(Vec::new());
            let mut places = Vec::new();
            let mut in_constructor = false;
            if has_initializer && let Some((tree, owner)) = &declarator {
                let body = self.view(*tree).and_then(|view| view.body_for(owner));
                if let Some(body) = body {
                    let frame = self.push_frame(*tree, body.clone(), None, None, HashMap::new());
                    if let Some(BoundStatement {
                        kind: S::Return(Some(value)),
                        span,
                    }) = body.statements.first()
                    {
                        places.push((self.path(*tree), *span));
                        let value = self.eval(frame, value, &HashMap::new(), None);
                        values = values.union(value);
                    } else {
                        values = Abs::Top;
                    }
                }
            }
            let mut writes = 0usize;
            let mut trees: Vec<usize> = self.semantic.paths.keys().copied().collect();
            trees.sort_unstable();
            for tree in trees {
                let Some(text) = self
                    .semantic
                    .compilation
                    .trees()
                    .source(tree)
                    .map(|s| s.text())
                else {
                    continue;
                };
                if !contains_word(text, &name) {
                    continue;
                }
                let (bodies, missed) = self.bodies_mentioning(tree, &name, false);
                if missed {
                    writes += 1;
                    values = Abs::Top;
                }
                for (owner, body) in bodies {
                    let owner_symbol = self
                        .view(tree)
                        .and_then(|view| view.model.declared_symbol(&owner));
                    let is_constructor_of_container = owner_symbol.is_some_and(|o| {
                        let o = self.semantic.compilation.symbols().get(o);
                        o.container == container
                            && o.as_method().is_some_and(|m| {
                                matches!(
                                    m.method_kind,
                                    MethodKind::Constructor | MethodKind::StaticConstructor
                                )
                            })
                    });
                    let mut assigned: Vec<(BoundExpression, TextSpan)> = Vec::new();
                    let mut opaque: Vec<TextSpan> = Vec::new();
                    walk_everything(&body, &mut |visited| {
                        if let Visited::Expression(e) = visited {
                            match &e.kind {
                                E::Assignment { target, value } if is_field(target, field) => {
                                    assigned.push(((**value).clone(), e.span));
                                }
                                E::CompoundAssignment { target, .. }
                                | E::Increment { target, .. }
                                    if is_field(target, field) =>
                                {
                                    opaque.push(e.span);
                                }
                                E::RefArgument { kind, operand }
                                    if is_field(operand, field) && *kind != RefKind::In =>
                                {
                                    opaque.push(e.span);
                                }
                                _ => {}
                            }
                        }
                    });
                    if assigned.is_empty() && opaque.is_empty() {
                        continue;
                    }
                    // A write in a lambda the constructor makes runs later,
                    // if at all: until then the field has its default.
                    let in_lambda = |span: &TextSpan| {
                        body.lambdas
                            .iter()
                            .any(|l| l.span.start() <= span.start() && span.end() <= l.span.end())
                    };
                    in_constructor |= is_constructor_of_container
                        && assigned.iter().any(|(_, span)| !in_lambda(span));
                    let frame =
                        self.push_frame(tree, body.clone(), owner_symbol, None, HashMap::new());
                    for (value, span) in assigned {
                        writes += 1;
                        if places.len() < MAX_PLACES {
                            places.push((self.path(tree), span));
                        }
                        let value = self.eval(frame, &value, &HashMap::new(), None);
                        values = values.union(value);
                    }
                    for span in opaque {
                        writes += 1;
                        if places.len() < MAX_PLACES {
                            places.push((self.path(tree), span));
                        }
                        values = Abs::Top;
                    }
                }
            }
            // Without an initializer, the default is what is read until a
            // write — unless a constructor writes it first. A struct comes
            // without one too, as `default(S)` and as an array's elements.
            let in_struct = container.is_some_and(|c| {
                matches!(
                    self.semantic.compilation.symbols().get(c).type_kind(),
                    Some(TypeKind::Struct | TypeKind::RecordStruct)
                )
            });
            if ((!has_initializer && !in_constructor) || in_struct) && !required {
                let ty = declarator
                    .as_ref()
                    .and_then(|(tree, _)| self.model(*tree).map(|m| m.type_of_symbol(field)));
                let default = ty.and_then(|ty| {
                    let frame = self.frames.len().checked_sub(1)?;
                    self.default_of(frame, &ty)
                });
                values = match default {
                    Some(default) => values.union(Abs::one(default)),
                    None => Abs::Top,
                };
            }
            let origin = if writes == 0 && !has_initializer {
                Origin::NeverWritten
            } else {
                Origin::Writes { readonly }
            };
            let input = Input {
                name: name.clone(),
                values: shown(&values),
                origin,
                places,
            };
            (values, input)
        };
        self.evaluating_fields.remove(&field);
        self.fields.insert(field, found.clone());
        found
    }

    /// The primary constructor parameter a field the language made keeps.
    fn captured_parameter(&self, field: SymbolId) -> Option<SymbolId> {
        let symbols = self.semantic.compilation.symbols();
        let container = symbols.get(field).container?;
        symbols.get(container).members.iter().find_map(|&member| {
            symbols
                .get(member)
                .as_method()?
                .parameters
                .iter()
                .copied()
                .find(|&p| {
                    symbols
                        .get(p)
                        .as_parameter()
                        .is_some_and(|detail| detail.captured == Some(field))
                })
        })
    }

    /// What a local can hold: what its declaration and assignments give it.
    fn local(&mut self, frame: usize, local: LocalId) -> (Abs, Input) {
        let body = self.frames[frame].body.clone();
        let name = body
            .locals
            .get(local.0 as usize)
            .map(|l| l.name.clone())
            .unwrap_or_default();
        let scan = self.scan(frame);
        let atom = Atom::Local(local);
        let given: &[BoundExpression] = scan.assigned.get(&atom).map_or(&[], Vec::as_slice);
        let values = if scan.opaque.contains(&atom) || given.is_empty() {
            Abs::Top
        } else {
            let mut values = Abs::Set(Vec::new());
            for value in given {
                let value = self.eval(frame, value, &HashMap::new(), None);
                values = values.union(value);
            }
            values
        };
        let input = Input {
            name,
            values: shown(&values),
            origin: if matches!(values, Abs::Top) {
                Origin::Unknown
            } else {
                Origin::Local
            },
            places: given
                .iter()
                .take(MAX_PLACES)
                .map(|g| (self.path(self.frames[frame].tree), g.span))
                .collect(),
        };
        (values, input)
    }

    /// What a parameter can be once the body has written to it: what it was
    /// given, and what the body gives it. A write whose value is not tracked
    /// leaves it unknown.
    fn written_parameter(
        &mut self,
        frame: usize,
        parameter: SymbolId,
        entry: (Abs, Input),
    ) -> (Abs, Input) {
        let scan = self.scan(frame);
        let atom = Atom::Param(parameter);
        let (mut values, mut input) = entry;
        let symbol = self.semantic.compilation.symbols().get(parameter);
        let name = symbol.name.clone();
        let ref_kind = symbol.as_parameter().map_or(RefKind::None, |p| p.ref_kind);
        // A reference is to a variable that what is called may write too.
        if matches!(ref_kind, RefKind::Ref | RefKind::In) {
            return (Abs::Top, unknown_input(name));
        }
        // What an `out` parameter had on the way in is nothing: it is
        // written before it is read.
        if ref_kind == RefKind::Out {
            values = Abs::Set(Vec::new());
        }
        let given: &[BoundExpression] = scan.assigned.get(&atom).map_or(&[], Vec::as_slice);
        if scan.opaque.contains(&atom) {
            return (Abs::Top, unknown_input(name));
        }
        for value in given {
            if input.places.len() < MAX_PLACES {
                input
                    .places
                    .push((self.path(self.frames[frame].tree), value.span));
            }
            let value = self.eval(frame, value, &HashMap::new(), None);
            values = values.union(value);
        }
        input.values = shown(&values);
        (values, input)
    }

    /// Every variable the body of `frame` writes.
    fn scan(&mut self, frame: usize) -> Arc<Scan> {
        let body = self.frames[frame].body.clone();
        let key = Arc::as_ptr(&body) as usize;
        if let Some(scan) = self.scans.get(&key) {
            return scan.clone();
        }
        let mut scan = Scan::default();
        walk_everything(&body, &mut |visited| {
            writes_of(visited, &mut |atom, value| match value {
                Some(value) => scan.assigned.entry(atom).or_default().push(value.clone()),
                None => {
                    scan.opaque.insert(atom);
                }
            });
        });
        let mut closure = HashSet::new();
        let closures = body
            .lambdas
            .iter()
            .map(|lambda| &lambda.body)
            .chain(body.local_functions.iter().map(|function| &function.body));
        for inner in closures {
            walk_statement(&body, inner, &mut |visited| {
                writes_of(visited, &mut |atom, _| {
                    closure.insert(atom);
                });
            });
        }
        scan.closure = closure;
        let scan = Arc::new(scan);
        self.scans.insert(key, scan.clone());
        scan
    }
}

/// A call of a member, found by [`Engine::call_sites`].
enum Site {
    /// A call, in the frame of the body that makes it.
    Call {
        frame: usize,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    },
    /// The member is used as a delegate: who calls it is not known.
    Escape,
}

// MARK: - the walk

/// What the walk has seen change, as a version for each thing that can: two
/// reads of something with the same version are of the same value.
#[derive(Default)]
struct State {
    clock: u32,
    /// Variables, by the last write to them.
    written: HashMap<Atom, u32>,
    /// Fields, by the last write to any object's.
    fields: HashMap<SymbolId, u32>,
    /// The last time code ran that may write fields: a call, an `await`.
    heap: u32,
    /// The last label: code can arrive there from anywhere.
    all: u32,
}

impl State {
    fn fresh(&mut self) -> u32 {
        self.clock += 1;
        self.clock
    }
}

/// What evaluating some code changes of what a condition read before it.
#[derive(Default)]
struct Effects {
    written: HashSet<Atom>,
    fields: HashSet<SymbolId>,
    /// It runs code that may write fields.
    havoc: bool,
}

/// A `catch` clause around the walk.
struct Catch {
    exception: Type,
    filter: Option<BoundExpression>,
}

/// A call as the walk meets it.
struct CallSite<'a> {
    method: SymbolId,
    receiver: Option<&'a BoundExpression>,
    /// Whether it goes through the receiver's run-time type.
    virtual_call: bool,
    arguments: &'a [BoundExpression],
    span: TextSpan,
    /// Whether the call is the operand of an `await`.
    awaited: bool,
    /// Whether the call has no value: for an `async` method, that makes
    /// its failures the program's rather than a task's.
    void: bool,
}

struct Walker<'e, 's> {
    engine: &'e mut Engine<'s>,
    frame: usize,
    chain: Vec<CallStep>,
    stack: &'e mut Vec<SymbolId>,
    found: Vec<Found>,
    /// The `catch` clauses around where the walk is, innermost last.
    catches: Vec<Vec<Catch>>,
    state: State,
    /// What the body writes.
    scan: Arc<Scan>,
    /// Parameters that are references: whatever is called may write them.
    by_ref: Vec<SymbolId>,
    /// The calls that are awaited, by where they are.
    awaited: HashSet<TextSpan>,
}

impl Walker<'_, '_> {
    // MARK: versions

    /// The version of an atom now.
    fn ver(&mut self, atom: Atom) -> u32 {
        let all = self.state.all;
        match atom {
            Atom::Local(_) | Atom::Param(_) => {
                let mut at = self.state.written.get(&atom).copied().unwrap_or(0).max(all);
                if self.is_volatile(atom) {
                    at = at.max(self.state.heap);
                }
                at
            }
            Atom::Field(field, through) => {
                let mut at = self.state.fields.get(&field).copied().unwrap_or(0).max(all);
                if self.engine.volatile_field(field) {
                    at = at.max(self.state.heap);
                }
                match through {
                    Recv::Local(l) => at.max(self.ver(Atom::Local(l))),
                    Recv::Param(p) => at.max(self.ver(Atom::Param(p))),
                    Recv::This | Recv::Other(_) => at,
                }
            }
        }
    }

    /// Whether code that runs elsewhere may change the atom.
    fn is_volatile(&self, atom: Atom) -> bool {
        match atom {
            Atom::Param(p) if self.by_ref.contains(&p) => true,
            Atom::Local(_) | Atom::Param(_) => self.scan.closure.contains(&atom),
            Atom::Field(..) => true,
        }
    }

    /// Whether `effects` change the atom.
    fn affected(&mut self, effects: &Effects, atom: Atom) -> bool {
        match atom {
            Atom::Local(_) | Atom::Param(_) => {
                effects.written.contains(&atom) || (effects.havoc && self.is_volatile(atom))
            }
            Atom::Field(field, through) => {
                effects.fields.contains(&field)
                    || (effects.havoc && self.engine.volatile_field(field))
                    || match through {
                        Recv::Local(l) => self.affected(effects, Atom::Local(l)),
                        Recv::Param(p) => self.affected(effects, Atom::Param(p)),
                        Recv::This | Recv::Other(_) => false,
                    }
            }
        }
    }

    fn apply_effects(&mut self, effects: &Effects) {
        for atom in &effects.written {
            let at = self.state.fresh();
            self.state.written.insert(*atom, at);
        }
        for field in &effects.fields {
            let at = self.state.fresh();
            self.state.fields.insert(*field, at);
        }
        if effects.havoc {
            self.havoc();
        }
    }

    /// Code that may write any field runs.
    fn havoc(&mut self) {
        self.state.heap = self.state.fresh();
    }

    /// What a loop does, which has happened by the time its next round
    /// reads anything, and by the time the code after it does.
    fn loop_effects(&mut self, statement: &BoundStatement) {
        let mut effects = Effects::default();
        self.engine
            .statement_effects(self.frame, statement, &mut effects);
        self.apply_effects(&effects);
    }

    /// Applies what evaluating an expression does, apart from what is in
    /// the expressions it holds.
    fn apply(&mut self, e: &BoundExpression) {
        let mut effects = Effects::default();
        self.engine.node_effects(e, &mut effects);
        self.apply_effects(&effects);
    }

    /// Applies everything an expression does, for one the walk does not
    /// go into.
    fn apply_all(&mut self, e: &BoundExpression) {
        let mut effects = Effects::default();
        self.engine.effects_of(e, &mut effects);
        self.apply_effects(&effects);
    }

    fn text(&self, span: TextSpan) -> String {
        self.engine.text(self.engine.frames[self.frame].tree, span)
    }

    /// A condition on the way, with the version of each thing it reads as it
    /// is here. What the condition itself changes, it reads before and
    /// after: those reads are told apart from anything later.
    fn cond(&mut self, test: Test, holds: bool, span: TextSpan) -> Cond {
        let mut effects = Effects::default();
        let mut atoms: Vec<Atom> = Vec::new();
        for expression in test.expressions() {
            self.engine.effects_of(expression, &mut effects);
            atoms_of(expression, &mut |atom| {
                if !atoms.contains(&atom) {
                    atoms.push(atom);
                }
            });
        }
        let mut versions = HashMap::new();
        for atom in atoms {
            let at = if self.affected(&effects, atom) {
                self.state.fresh()
            } else {
                self.ver(atom)
            };
            versions.insert(atom, at);
        }
        Cond {
            frame: self.frame,
            test,
            holds,
            span,
            versions: Arc::new(versions),
        }
    }

    // MARK: statements

    /// Walks a list of statements; whether it always leaves.
    fn statements(&mut self, list: &[BoundStatement], conds: &mut Vec<Cond>) -> bool {
        let base = conds.len();
        let leaves = self.statements_in(list, conds);
        conds.truncate(base);
        leaves
    }

    /// Walks a list of statements, leaving on `conds` what holds after them.
    fn statements_in(&mut self, list: &[BoundStatement], conds: &mut Vec<Cond>) -> bool {
        let base = conds.len();
        let mut at = 0;
        while at < list.len() {
            // A `goto` arrives at a label from anywhere in the list, with
            // what holds there: only what held before the list holds here.
            if is_labeled(&list[at]) {
                conds.truncate(base);
                let words = "a jump or the code above reaches this label";
                // The block a label is written in says so itself.
                if !matches!(conds.last(), Some(Cond { test: Test::Reach(w), .. }) if w == words) {
                    let reached = self.cond(Test::Reach(words.to_owned()), true, list[at].span);
                    conds.push(reached);
                }
            }
            if self.statement(&list[at], conds) {
                conds.truncate(base);
                // What follows a jump is reached only by a `goto`, to a label.
                match list[at + 1..].iter().position(is_labeled) {
                    Some(offset) => {
                        at += 1 + offset;
                        continue;
                    }
                    None => return true,
                }
            }
            // A statement that may return or throw somewhere inside, and has
            // not said so in a condition, makes what follows it reachable
            // only where it did not.
            if !matches!(list[at].kind, S::If { .. } | S::Block(_)) && contains_leave(&list[at]) {
                let words = "the code above does not return or throw".to_owned();
                let past = self.cond(Test::Reach(words), true, list[at].span);
                conds.push(past);
            }
            at += 1;
        }
        false
    }

    /// Walks a statement; whether it always leaves (returns, throws, jumps).
    /// What holds after it, because it left otherwise, is pushed onto
    /// `conds` for the statements that follow.
    fn statement(&mut self, statement: &BoundStatement, conds: &mut Vec<Cond>) -> bool {
        match &statement.kind {
            // What a block's guards leave holds after it, too.
            S::Block(list) => self.statements_in(list, conds),
            S::LocalDeclaration { local, initializer } => {
                if let Some(value) = initializer {
                    self.expression(value, conds);
                }
                let at = self.state.fresh();
                self.state.written.insert(Atom::Local(*local), at);
                false
            }
            S::Expression(e) => {
                self.expression(e, conds);
                matches!(e.kind, E::Throw(_))
            }
            S::If {
                condition,
                consequence,
                alternative,
            } => {
                self.expression(condition, conds);
                let base = conds.len();
                let holds = self.cond(Test::Truth(condition.clone()), true, condition.span);
                conds.push(holds);
                let then_leaves = self.statement(consequence, conds);
                conds.truncate(base);
                let fails = self.cond(Test::Truth(condition.clone()), false, condition.span);
                conds.push(fails);
                let else_leaves = alternative
                    .as_deref()
                    .is_some_and(|alternative| self.statement(alternative, conds));
                conds.truncate(base);
                // A branch that leaves only some of the time says nothing of
                // what holds after it.
                let residual = (!then_leaves && contains_leave(consequence))
                    || (!else_leaves && alternative.as_deref().is_some_and(contains_leave));
                match (then_leaves, else_leaves) {
                    (true, true) => return true,
                    (true, false) => {
                        let fails =
                            self.cond(Test::Truth(condition.clone()), false, condition.span);
                        conds.push(fails);
                    }
                    (false, true) => {
                        let holds = self.cond(Test::Truth(condition.clone()), true, condition.span);
                        conds.push(holds);
                    }
                    (false, false) => {}
                }
                if residual {
                    let words = "the code above does not return or throw".to_owned();
                    let past = self.cond(Test::Reach(words), true, statement.span);
                    conds.push(past);
                }
                false
            }
            S::While { condition, body } => {
                self.loop_effects(statement);
                self.expression(condition, conds);
                let base = conds.len();
                let holds = self.cond(Test::Truth(condition.clone()), true, condition.span);
                conds.push(holds);
                self.statement(body, conds);
                conds.truncate(base);
                self.loop_effects(statement);
                false
            }
            S::DoWhile { body, condition } => {
                self.loop_effects(statement);
                let base = conds.len();
                self.statement(body, conds);
                conds.truncate(base);
                self.expression(condition, conds);
                self.loop_effects(statement);
                false
            }
            S::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                let base = conds.len();
                for initializer in initializers {
                    self.statement(initializer, conds);
                }
                self.loop_effects(statement);
                if let Some(condition) = condition {
                    self.expression(condition, conds);
                    let holds = self.cond(Test::Truth(condition.clone()), true, condition.span);
                    conds.push(holds);
                }
                self.statement(body, conds);
                for incrementor in incrementors {
                    self.expression(incrementor, conds);
                }
                conds.truncate(base);
                self.loop_effects(statement);
                false
            }
            S::ForEach {
                collection, body, ..
            } => {
                self.expression(collection, conds);
                self.loop_effects(statement);
                let base = conds.len();
                // A collection with nothing in it never runs the body.
                let words = format!("{} has elements", self.text(collection.span));
                let walks = self.cond(Test::Reach(words), true, collection.span);
                conds.push(walks);
                self.statement(body, conds);
                conds.truncate(base);
                self.loop_effects(statement);
                false
            }
            S::ConstructorInitializer {
                constructor,
                arguments,
                ..
            } => {
                for argument in arguments {
                    self.expression(argument, conds);
                }
                if let Some(constructor) = constructor {
                    self.call(
                        CallSite {
                            method: *constructor,
                            receiver: None,
                            virtual_call: false,
                            arguments,
                            span: statement.span,
                            awaited: false,
                            void: true,
                        },
                        conds,
                    );
                }
                self.havoc();
                false
            }
            S::Switch {
                governing,
                sections,
            } => {
                self.expression(governing, conds);
                let base = conds.len();
                // A `goto case` enters a section without matching its labels.
                let body = self.engine.frames[self.frame].body.clone();
                let mut jumps = false;
                for section in sections {
                    for inner in &section.statements {
                        walk_statement(&body, inner, &mut |visited| {
                            if let Visited::Statement(s) = visited
                                && matches!(s.kind, S::GotoCase(_))
                            {
                                jumps = true;
                            }
                        });
                    }
                }
                let mut labels = Vec::new();
                let mut own: Vec<Range<usize>> = Vec::new();
                for section in sections {
                    let start = labels.len();
                    for label in &section.labels {
                        if let BoundSwitchLabel::Case(case) = label {
                            labels.push(Label {
                                pattern: case.pattern.clone(),
                                when: case.when.clone(),
                            });
                            // What a pattern binds and a `when` does runs
                            // as the labels are tried.
                            let mut effects = Effects::default();
                            self.engine.pattern_effects(&case.pattern, &mut effects);
                            if let Some(when) = &case.when {
                                self.engine.effects_of(when, &mut effects);
                            }
                            self.apply_effects(&effects);
                        }
                    }
                    own.push(start..labels.len());
                }
                let labels = Arc::new(labels);
                let total = labels.len();
                for (section, own) in sections.iter().zip(own) {
                    let default = section
                        .labels
                        .iter()
                        .any(|label| matches!(label, BoundSwitchLabel::Default));
                    if jumps {
                        let words = format!("{} reaches this case", self.text(governing.span));
                        let reached = self.cond(Test::Opaque(words), true, governing.span);
                        conds.push(reached);
                    } else if default {
                        // Where no label of another section matches.
                        for others in [0..own.start, own.end..total] {
                            if !others.is_empty() {
                                let none = self.cond(
                                    Test::Matches(governing.clone(), labels.clone(), others),
                                    false,
                                    governing.span,
                                );
                                conds.push(none);
                            }
                        }
                    } else {
                        let constant = match &labels[own.clone()] {
                            [
                                Label {
                                    pattern:
                                        BoundPattern {
                                            kind: P::Constant(value),
                                            ..
                                        },
                                    when: None,
                                },
                            ] => Some(value.clone()),
                            _ => None,
                        };
                        let matched = match constant {
                            Some(value) => {
                                let span = value.span;
                                self.cond(Test::Equals(governing.clone(), value), true, span)
                            }
                            None => self.cond(
                                Test::Matches(governing.clone(), labels.clone(), own.clone()),
                                true,
                                governing.span,
                            ),
                        };
                        conds.push(matched);
                        // An earlier label that matches takes the value first.
                        if own.start > 0 {
                            let earlier = self.cond(
                                Test::Matches(governing.clone(), labels.clone(), 0..own.start),
                                false,
                                governing.span,
                            );
                            conds.push(earlier);
                        }
                    }
                    self.statements(&section.statements, conds);
                    conds.truncate(base);
                }
                false
            }
            S::Try {
                body,
                catches,
                finally,
            } => {
                let caught: Vec<Catch> = catches
                    .iter()
                    .map(|c| Catch {
                        exception: c.exception_type.clone(),
                        filter: c.filter.clone(),
                    })
                    .collect();
                self.catches.push(caught);
                let base = conds.len();
                let body_leaves = self.statement(body, conds);
                conds.truncate(base);
                self.catches.pop();
                let mut all_leave = body_leaves;
                for catch in catches {
                    if let Some(filter) = &catch.filter {
                        self.apply_all(filter);
                    }
                    // A `catch` runs only when the block it follows fails.
                    let words = format!(
                        "the try block throws {}",
                        display_type(&self.engine.semantic.compilation, &catch.exception_type)
                    );
                    let runs = self.cond(Test::Reach(words), true, catch.body.span);
                    conds.push(runs);
                    all_leave &= self.statement(&catch.body, conds);
                    conds.truncate(base);
                }
                if let Some(finally) = finally {
                    self.statement(finally, conds);
                    conds.truncate(base);
                }
                all_leave && finally.is_none()
            }
            S::Using { resources, body } => {
                for resource in resources {
                    self.expression(&resource.value, conds);
                }
                // The resource is disposed when the block is left.
                self.havoc();
                let leaves = self.statement(body, conds);
                self.havoc();
                leaves
            }
            S::Lock { value, body, .. } => {
                self.expression(value, conds);
                // Another thread runs while this one waits for the lock, and
                // while it holds it.
                self.havoc();
                let leaves = self.statement(body, conds);
                self.havoc();
                leaves
            }
            S::Fixed { body, .. } => self.statement(body, conds),
            S::Return(value) => {
                if let Some(value) = value {
                    self.expression(value, conds);
                }
                true
            }
            S::YieldReturn(value) => {
                self.expression(value, conds);
                // The caller runs until it asks for the next one.
                self.havoc();
                false
            }
            S::Throw(value) => {
                if let Some(value) = value {
                    self.expression(value, conds);
                    self.throw(value, statement.span, conds);
                }
                true
            }
            S::YieldBreak | S::Break(_) | S::Continue(_) | S::Goto(_) | S::GotoCase(_) => true,
            S::Label(_) => {
                self.state.all = self.state.fresh();
                false
            }
            S::Unsupported(_) | S::Empty => false,
        }
    }

    // MARK: expressions

    /// Marks the calls an `await` waits for: the operand, and what it is
    /// called on (`Run().ConfigureAwait(false)`).
    fn mark_awaited(&mut self, operand: &BoundExpression) {
        let mut at = strip(operand);
        while let E::Call { receiver, .. } = &at.kind {
            self.awaited.insert(at.span);
            match receiver {
                Some(receiver) => at = strip(receiver),
                None => break,
            }
        }
    }

    fn expression(&mut self, e: &BoundExpression, conds: &mut Vec<Cond>) {
        let base = conds.len();
        match &e.kind {
            E::Throw(operand) => {
                if let Some(operand) = operand {
                    self.expression(operand, conds);
                    self.throw(operand, e.span, conds);
                }
            }
            E::Binary {
                operator: operator @ (BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr),
                left,
                right,
            } => {
                self.expression(left, conds);
                let holds = *operator == BinaryOperator::LogicalAnd;
                let on = self.cond(Test::Truth((**left).clone()), holds, left.span);
                conds.push(on);
                self.expression(right, conds);
            }
            E::Binary {
                operator: BinaryOperator::Coalesce,
                left,
                right,
            } => {
                self.expression(left, conds);
                let null = self.cond(Test::Null((**left).clone()), true, left.span);
                conds.push(null);
                self.expression(right, conds);
            }
            // `x ??= y` evaluates `y` only where `x` is null.
            E::CompoundAssignment {
                target,
                operator: BinaryOperator::Coalesce,
                value,
            } => {
                self.expression(target, conds);
                let null = self.cond(Test::Null((**target).clone()), true, target.span);
                conds.push(null);
                self.expression(value, conds);
            }
            E::Binary {
                operator: BinaryOperator::Divide | BinaryOperator::Modulo,
                left,
                right,
            } => {
                self.expression(left, conds);
                self.expression(right, conds);
                let integral = self
                    .engine
                    .special(self.frame, &e.ty)
                    .is_some_and(is_integral);
                let nonzero = match &right.kind {
                    E::Literal(value) => Val::from_constant(value).number() != Some(0.0),
                    _ => false,
                };
                if integral && !nonzero {
                    let mut with = conds.clone();
                    let zero = self.cond(Test::Zero((**right).clone()), true, right.span);
                    with.push(zero);
                    self.record(Found {
                        kind: FailureKind::DivideByZero,
                        exception: "DivideByZeroException".to_owned(),
                        exception_type: None,
                        message: None,
                        frame: self.frame,
                        span: e.span,
                        conditions: with,
                        chain: self.chain.clone(),
                    });
                }
            }
            E::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                self.expression(condition, conds);
                let holds = self.cond(Test::Truth((**condition).clone()), true, condition.span);
                conds.push(holds);
                self.expression(consequence, conds);
                conds.truncate(base);
                let fails = self.cond(Test::Truth((**condition).clone()), false, condition.span);
                conds.push(fails);
                self.expression(alternative, conds);
            }
            E::ConditionalAccess { receiver, access } => {
                self.expression(receiver, conds);
                let some = self.cond(Test::Null((**receiver).clone()), false, receiver.span);
                conds.push(some);
                self.expression(access, conds);
            }
            E::Await { operand, .. } => {
                self.mark_awaited(operand);
                self.expression(operand, conds);
            }
            E::Switch { governing, arms } => {
                self.expression(governing, conds);
                let labels: Arc<Vec<Label>> = Arc::new(
                    arms.iter()
                        .map(|arm| Label {
                            pattern: arm.pattern.clone(),
                            when: arm.when.clone(),
                        })
                        .collect(),
                );
                for (at, arm) in arms.iter().enumerate() {
                    let arm_base = conds.len();
                    // An arm is taken where its pattern matches, its `when`
                    // holds, and no arm before it was taken.
                    if at > 0 {
                        let earlier = self.cond(
                            Test::Matches((**governing).clone(), labels.clone(), 0..at),
                            false,
                            governing.span,
                        );
                        conds.push(earlier);
                    }
                    let mut effects = Effects::default();
                    self.engine.pattern_effects(&arm.pattern, &mut effects);
                    self.apply_effects(&effects);
                    let pattern_only: Arc<Vec<Label>> = Arc::new(vec![Label {
                        pattern: arm.pattern.clone(),
                        when: None,
                    }]);
                    let matched = self.cond(
                        Test::Matches((**governing).clone(), pattern_only, 0..1),
                        true,
                        arm.pattern.span,
                    );
                    conds.push(matched);
                    if let Some(when) = &arm.when {
                        self.expression(when, conds);
                        let holds = self.cond(Test::Truth(when.clone()), true, when.span);
                        conds.push(holds);
                    }
                    self.expression(&arm.value, conds);
                    conds.truncate(arm_base);
                }
            }
            E::Call {
                receiver,
                method,
                arguments,
                virtual_call,
                ..
            } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver, conds);
                    self.dereference(receiver, conds);
                }
                for argument in arguments {
                    self.expression(argument, conds);
                }
                let site = CallSite {
                    method: *method,
                    receiver: receiver.as_deref(),
                    virtual_call: *virtual_call,
                    arguments,
                    span: e.span,
                    awaited: self.awaited.contains(&e.span),
                    void: e.ty == Type::Void,
                };
                self.call(site, conds);
            }
            E::ObjectCreation {
                constructor,
                arguments,
                initializers,
            } => {
                for argument in arguments {
                    self.expression(argument, conds);
                }
                if let Some(constructor) = constructor {
                    self.call(
                        CallSite {
                            method: *constructor,
                            receiver: None,
                            virtual_call: false,
                            arguments,
                            span: e.span,
                            awaited: false,
                            void: false,
                        },
                        conds,
                    );
                }
                for initializer in initializers {
                    self.expression(initializer, conds);
                }
            }
            E::Field {
                receiver: Some(receiver),
                ..
            } => {
                self.expression(receiver, conds);
                self.dereference(receiver, conds);
            }
            E::Property { receiver, property } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver, conds);
                    self.dereference(receiver, conds);
                }
                self.call(
                    CallSite {
                        method: *property,
                        receiver: receiver.as_deref(),
                        virtual_call: true,
                        arguments: &[],
                        span: e.span,
                        awaited: false,
                        void: false,
                    },
                    conds,
                );
            }
            E::ArrayLength { array } => {
                self.expression(array, conds);
                self.dereference(array, conds);
            }
            E::ArrayAccess { array, indices } => {
                self.expression(array, conds);
                for index in indices {
                    self.expression(index, conds);
                }
                self.dereference(array, conds);
                if let [index] = indices.as_slice() {
                    let mut with = conds.clone();
                    let outside = self.cond(
                        Test::OutOfRange((**array).clone(), index.clone()),
                        true,
                        index.span,
                    );
                    with.push(outside);
                    self.implicit(
                        FailureKind::IndexOutOfRange,
                        "IndexOutOfRangeException",
                        e.span,
                        with,
                    );
                }
            }
            E::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => {
                self.expression(receiver, conds);
                for argument in arguments {
                    self.expression(argument, conds);
                }
                self.dereference(receiver, conds);
                self.indexer(*indexer, receiver, arguments, e.span, conds);
            }
            E::Assignment { target, value } => {
                self.target(target, conds);
                self.expression(value, conds);
            }
            // A lambda runs when it is called, not where it is written.
            E::Lambda(_) | E::UnboundLambda(_) => {}
            _ => {
                for child in expression_children(e) {
                    self.expression(child, conds);
                }
            }
        }
        self.apply(e);
        conds.truncate(base);
    }

    /// What is assigned to: its receiver and arguments are read, the place
    /// itself is not (a property's getter does not run, a dictionary's
    /// indexer adds rather than looks up).
    fn target(&mut self, target: &BoundExpression, conds: &mut Vec<Cond>) {
        match &target.kind {
            E::Field {
                receiver: Some(receiver),
                ..
            }
            | E::Property {
                receiver: Some(receiver),
                ..
            } => {
                self.expression(receiver, conds);
                self.dereference(receiver, conds);
            }
            E::IndexerAccess {
                receiver,
                arguments,
                ..
            } => {
                self.expression(receiver, conds);
                for argument in arguments {
                    self.expression(argument, conds);
                }
                self.dereference(receiver, conds);
            }
            E::Field { .. } | E::Property { .. } | E::Local(_) | E::Parameter(_) => {}
            _ => self.expression(target, conds),
        }
    }

    /// A member reached through `receiver`: a failure if it can be null.
    fn dereference(&mut self, receiver: &BoundExpression, conds: &[Cond]) {
        let receiver = strip(receiver);
        let named = matches!(
            receiver.kind,
            E::Parameter(_) | E::Local(_) | E::Field { .. } | E::Property { .. }
        );
        if !named {
            return;
        }
        let string = self
            .engine
            .special(self.frame, &receiver.ty)
            .is_some_and(|s| matches!(s, SpecialType::String | SpecialType::Object));
        if !string && !is_reference(self.engine.semantic, &receiver.ty) {
            return;
        }
        let mut with = conds.to_vec();
        with.push(self.cond(Test::Null(receiver.clone()), true, receiver.span));
        self.implicit(
            FailureKind::NullReference,
            "NullReferenceException",
            receiver.span,
            with,
        );
    }

    fn implicit(
        &mut self,
        kind: FailureKind,
        exception: &str,
        span: TextSpan,
        conditions: Vec<Cond>,
    ) {
        self.record(Found {
            kind,
            exception: exception.to_owned(),
            exception_type: None,
            message: None,
            frame: self.frame,
            span,
            conditions,
            chain: self.chain.clone(),
        });
    }

    /// `d[key]`: a dictionary's throws when the key is not there, unless a
    /// `ContainsKey` on the way said it is; a project's indexer is followed.
    fn indexer(
        &mut self,
        indexer: SymbolId,
        receiver: &BoundExpression,
        arguments: &[BoundExpression],
        span: TextSpan,
        conds: &[Cond],
    ) {
        let symbols = self.engine.semantic.compilation.symbols();
        let container = symbols
            .get(indexer)
            .container
            .map(|c| symbols.qualified_name(c))
            .unwrap_or_default();
        let dictionary = container.starts_with("System.Collections.Generic.Dictionary")
            || container.starts_with("System.Collections.Generic.IDictionary")
            || container.starts_with("System.Collections.Generic.IReadOnlyDictionary");
        if !dictionary {
            self.call(
                CallSite {
                    method: indexer,
                    receiver: Some(receiver),
                    virtual_call: true,
                    arguments,
                    span,
                    awaited: false,
                    void: false,
                },
                conds,
            );
            return;
        }
        let tree = self.engine.frames[self.frame].tree;
        let receiver_text = self.engine.text(tree, strip(receiver).span);
        let key_text = arguments
            .first()
            .map(|key| self.engine.text(tree, strip(key).span))
            .unwrap_or_default();
        if self.guarded(
            conds,
            &receiver_text,
            &["ContainsKey", "TryGetValue"],
            Some(&key_text),
        ) {
            return;
        }
        let mut with = conds.to_vec();
        with.push(self.cond(
            Test::Opaque(format!("{key_text} is not in {receiver_text}")),
            true,
            span,
        ));
        self.implicit(FailureKind::Library, "KeyNotFoundException", span, with);
    }

    /// Whether a condition on the way is a call of one of `methods` on the
    /// same receiver — with the same first argument, where one is given —
    /// that holds: `d.ContainsKey(k)` before `d[k]`, `xs.Any()` before
    /// `xs.First()`.
    fn guarded(
        &self,
        conds: &[Cond],
        receiver: &str,
        methods: &[&str],
        argument: Option<&str>,
    ) -> bool {
        let symbols = self.engine.semantic.compilation.symbols();
        conds.iter().any(|cond| {
            let Test::Truth(test) = &cond.test else {
                return false;
            };
            // `!d.ContainsKey(k)` not holding is `d.ContainsKey(k)` holding.
            let mut test = strip(test);
            let mut holds = cond.holds;
            while let E::Unary {
                operator: UnaryOperator::LogicalNot,
                operand,
            } = &test.kind
            {
                test = strip(operand);
                holds = !holds;
            }
            if !holds {
                return false;
            }
            let E::Call {
                receiver: call_receiver,
                method,
                arguments,
                ..
            } = &strip(test).kind
            else {
                return false;
            };
            if !methods.contains(&symbols.get(*method).name.as_str()) {
                return false;
            }
            let tree = self.engine.frames[cond.frame].tree;
            // An extension method's receiver is its first argument.
            let (on, rest) = match call_receiver {
                Some(on) => (Some(&**on), &arguments[..]),
                None => (arguments.first(), arguments.get(1..).unwrap_or(&[])),
            };
            let same_receiver =
                on.is_some_and(|on| self.engine.text(tree, strip(on).span) == receiver);
            let same_argument = argument.is_none_or(|argument| {
                rest.first()
                    .is_some_and(|first| self.engine.text(tree, strip(first).span) == argument)
            });
            same_receiver && same_argument
        })
    }

    /// Whether a condition on the way says the sequence has an element:
    /// `xs.Count > 0`, `xs.Length != 0`, `xs.Count() >= 1`.
    fn counted(&self, conds: &[Cond], sequence: &str) -> bool {
        let symbols = self.engine.semantic.compilation.symbols();
        // What is counted: `xs` of `xs.Count`, `xs.Length`, `xs.Count()`.
        let counted = |e: &BoundExpression| -> Option<String> {
            let e = strip(e);
            let tree = self.engine.frames[self.frame].tree;
            let text = |e: &BoundExpression| self.engine.text(tree, strip(e).span);
            match &e.kind {
                E::ArrayLength { array } => Some(text(array)),
                E::Property {
                    receiver: Some(receiver),
                    property,
                } if matches!(symbols.get(*property).name.as_str(), "Count" | "Length") => {
                    Some(text(receiver))
                }
                E::Call {
                    receiver,
                    method,
                    arguments,
                    ..
                } if symbols.get(*method).name == "Count" => match (receiver, arguments.as_slice())
                {
                    (Some(receiver), []) => Some(text(receiver)),
                    (None, [first]) => Some(text(first)),
                    _ => None,
                },
                _ => None,
            }
        };
        let number = |e: &BoundExpression| match &strip(e).kind {
            E::Literal(value) => Val::from_constant(value).integer(),
            _ => None,
        };
        conds.iter().any(|cond| {
            let Test::Truth(test) = &cond.test else {
                return false;
            };
            let mut test = strip(test);
            let mut holds = cond.holds;
            while let E::Unary {
                operator: UnaryOperator::LogicalNot,
                operand,
            } = &test.kind
            {
                test = strip(operand);
                holds = !holds;
            }
            let E::Binary {
                operator,
                left,
                right,
            } = &test.kind
            else {
                return false;
            };
            // `0 < xs.Count` is `xs.Count > 0`.
            let (size, n, mut operator) =
                match (counted(left), number(right), counted(right), number(left)) {
                    (Some(size), Some(n), _, _) => (size, n, *operator),
                    (_, _, Some(size), Some(n)) => {
                        let mirrored = match operator {
                            BinaryOperator::LessThan => BinaryOperator::GreaterThan,
                            BinaryOperator::GreaterThan => BinaryOperator::LessThan,
                            BinaryOperator::LessThanOrEqual => BinaryOperator::GreaterThanOrEqual,
                            BinaryOperator::GreaterThanOrEqual => BinaryOperator::LessThanOrEqual,
                            other => *other,
                        };
                        (size, n, mirrored)
                    }
                    _ => return false,
                };
            if size != sequence {
                return false;
            }
            if !holds {
                operator = match operator {
                    BinaryOperator::LessThan => BinaryOperator::GreaterThanOrEqual,
                    BinaryOperator::LessThanOrEqual => BinaryOperator::GreaterThan,
                    BinaryOperator::GreaterThan => BinaryOperator::LessThanOrEqual,
                    BinaryOperator::GreaterThanOrEqual => BinaryOperator::LessThan,
                    BinaryOperator::Equality => BinaryOperator::Inequality,
                    BinaryOperator::Inequality => BinaryOperator::Equality,
                    other => other,
                };
            }
            // A count is never negative.
            match operator {
                BinaryOperator::GreaterThan => n >= 0,
                BinaryOperator::GreaterThanOrEqual | BinaryOperator::Equality => n >= 1,
                BinaryOperator::Inequality => n == 0,
                _ => false,
            }
        })
    }

    /// A library member that throws on what it is given; whether `method`
    /// is one this knows.
    fn library(
        &mut self,
        method: SymbolId,
        arguments: &[BoundExpression],
        span: TextSpan,
        conds: &[Cond],
    ) -> bool {
        let symbols = self.engine.semantic.compilation.symbols();
        let symbol = symbols.get(method);
        let name = symbol.name.clone();
        let container = symbol
            .container
            .map(|c| symbols.qualified_name(c))
            .unwrap_or_default();
        let tree = self.engine.frames[self.frame].tree;
        if let Some(special) = parsed_type(&container, &name)
            && let Some(text) = arguments.first()
            && self.engine.special(self.frame, &strip(text).ty) == Some(SpecialType::String)
        {
            let mut with = conds.to_vec();
            with.push(self.cond(Test::Parses(strip(text).clone(), special), false, text.span));
            self.implicit(FailureKind::Library, "FormatException", span, with);
            return true;
        }
        if container == "System.Linq.Enumerable" {
            let (exception, words) = match name.as_str() {
                "First" | "Last" | "Max" | "Min" | "Average" | "Aggregate" => {
                    ("InvalidOperationException", "is empty")
                }
                "Single" => (
                    "InvalidOperationException",
                    "does not have exactly one element",
                ),
                "ElementAt" => ("ArgumentOutOfRangeException", "is too short"),
                _ => return false,
            };
            let Some(sequence) = arguments.first() else {
                return false;
            };
            let sequence_text = self.engine.text(tree, strip(sequence).span);
            if words == "is empty"
                && (self.guarded(conds, &sequence_text, &["Any"], None)
                    || self.counted(conds, &sequence_text))
            {
                return true;
            }
            let mut with = conds.to_vec();
            with.push(self.cond(Test::Opaque(format!("{sequence_text} {words}")), true, span));
            self.implicit(FailureKind::Library, exception, span, with);
            return true;
        }
        false
    }

    fn throw(&mut self, operand: &BoundExpression, span: TextSpan, conds: &[Cond]) {
        let compilation = &self.engine.semantic.compilation;
        let mut exception = display_type(compilation, &operand.ty);
        if operand.ty.is_error() {
            // A type that did not resolve: say what was written.
            let tree = self.engine.frames[self.frame].tree;
            exception = match &operand.kind {
                E::ObjectCreation { .. } | E::Error => {
                    let text = self.engine.text(tree, operand.span);
                    let text = text.strip_prefix("new ").unwrap_or(&text);
                    text.split(['(', '{'])
                        .next()
                        .unwrap_or(text)
                        .trim()
                        .to_owned()
                }
                _ => self.engine.text(tree, operand.span),
            };
        }
        let message = match &operand.kind {
            E::ObjectCreation { arguments, .. } => {
                arguments
                    .first()
                    .and_then(|first| match &strip(first).kind {
                        E::Literal(ConstantValue::String(text)) => Some(text.clone()),
                        _ => None,
                    })
            }
            _ => None,
        };
        self.record(Found {
            kind: FailureKind::Throw,
            exception,
            exception_type: Some(operand.ty.clone()),
            message,
            frame: self.frame,
            span,
            conditions: conds.to_vec(),
            chain: self.chain.clone(),
        });
    }

    /// Keeps a failure, unless a `catch` around it catches it; a `catch`
    /// with a filter catches it only where the filter holds.
    fn record(&mut self, mut found: Found) {
        let clauses: Vec<(Type, Option<BoundExpression>)> = self
            .catches
            .iter()
            .flatten()
            .map(|c| (c.exception.clone(), c.filter.clone()))
            .collect();
        let mut filters = Vec::new();
        for (caught, filter) in clauses {
            if !self.catches_it(&found, &caught) {
                continue;
            }
            match filter {
                None => return,
                Some(filter) => {
                    let always = self
                        .engine
                        .eval(self.frame, &filter, &HashMap::new(), None)
                        .truth();
                    if always == Tri::True {
                        return;
                    }
                    filters.push(filter);
                }
            }
        }
        // Past a filter that may be true the failure is only possible: it
        // gets away where the filter does not hold.
        for filter in filters {
            let span = filter.span;
            let escapes = self.cond(Test::Filter(filter), false, span);
            found.conditions.push(escapes);
        }
        self.found.push(found);
    }

    /// Whether a `catch` of `caught` takes the failure.
    fn catches_it(&mut self, found: &Found, caught: &Type) -> bool {
        let semantic = self.engine.semantic;
        let tree = self.engine.frames[self.frame].tree;
        let name = display_type(&semantic.compilation, caught);
        if name == "Exception" {
            return true;
        }
        match &found.exception_type {
            Some(thrown) => {
                let Some(model) = self.engine.model(tree) else {
                    return false;
                };
                thrown == caught || model.binder().inherits_from_public(thrown, caught)
            }
            None => name == found.exception || implicit_bases(&found.exception).contains(&&*name),
        }
    }

    /// Whether the call may run a member other than the one it names: it is
    /// made through the run-time type of a receiver that may be a subtype.
    fn dispatch_unknown(
        &mut self,
        method: SymbolId,
        receiver: Option<&BoundExpression>,
        virtual_call: bool,
    ) -> bool {
        if !virtual_call {
            return false;
        }
        let semantic = self.engine.semantic;
        let symbols = semantic.compilation.symbols();
        let symbol = symbols.get(method);
        let in_interface = symbol
            .container
            .and_then(|c| symbols.get(c).as_named_type())
            .is_some_and(|t| t.type_kind == Some(TypeKind::Interface));
        let overridable = symbol.modifiers.contains(Modifiers::VIRTUAL)
            || symbol.modifiers.contains(Modifiers::ABSTRACT)
            || symbol.modifiers.contains(Modifiers::OVERRIDE)
            || in_interface;
        if !overridable || symbol.modifiers.contains(Modifiers::SEALED) {
            return false;
        }
        // A type nothing derives from has no other member to run.
        let closed = |ty: SymbolId| {
            let ty = symbols.get(ty);
            ty.modifiers.contains(Modifiers::SEALED)
                || ty.modifiers.contains(Modifiers::STATIC)
                || matches!(
                    ty.as_named_type().and_then(|t| t.type_kind),
                    Some(TypeKind::Struct | TypeKind::RecordStruct | TypeKind::Enum)
                )
        };
        let container = symbol.container;
        // The member the call names is the one that runs only where the
        // object is exactly of the type that has it, and nothing derives
        // from that type or the call names it through `base`.
        let exact = |ty: Option<SymbolId>| ty.is_some() && ty == container;
        let certain = match receiver.map(strip) {
            Some(BoundExpression { kind: E::Base, .. }) => true,
            Some(BoundExpression {
                kind: E::ObjectCreation { .. },
                ty: Type::Named { symbol, .. },
                ..
            }) => exact(Some(*symbol)),
            Some(BoundExpression {
                ty: Type::Named { symbol, .. },
                ..
            }) => exact(Some(*symbol)) && closed(*symbol),
            Some(_) => false,
            None => {
                let current = self.engine.frames[self.frame]
                    .member
                    .and_then(|member| symbols.get(member).container);
                exact(current) && current.is_some_and(closed)
            }
        };
        !certain
    }

    /// Follows a call into a member of the project: what can fail in it can
    /// fail here, with its parameters being what this call passes.
    fn call(&mut self, site: CallSite<'_>, conds: &[Cond]) {
        let CallSite {
            method,
            receiver,
            virtual_call,
            arguments,
            span,
            awaited,
            void,
        } = site;
        // What the library says about its own members comes first: the
        // body a reference assembly has is not the one that runs.
        if self.library(method, arguments, span, conds) {
            return;
        }
        if self.stack.len() >= CALL_DEPTH || self.stack.contains(&method) {
            return;
        }
        let symbols = self.engine.semantic.compilation.symbols();
        let is_local = symbols
            .get(method)
            .as_method()
            .is_some_and(|m| m.method_kind == MethodKind::LocalFunction);
        // A local function is a part of the body that holds it.
        let (tree, body, local_function) = if is_local {
            let body = self.engine.frames[self.frame].body.clone();
            let Some(at) = body.local_functions.iter().position(|f| f.symbol == method) else {
                return;
            };
            (self.engine.frames[self.frame].tree, body, Some(at))
        } else {
            let Some((tree, body)) = self.engine.body_of(method) else {
                return;
            };
            (tree, body, None)
        };
        // An iterator's body runs when it is enumerated; what an `async`
        // method fails with is kept in its task, and comes out at the
        // `await`.
        let iterator = match local_function {
            Some(at) => body.local_functions[at].iterator.is_some(),
            None => body.iterator.is_some(),
        };
        if iterator
            || (symbols.get(method).modifiers.contains(Modifiers::ASYNC) && !void && !awaited)
        {
            return;
        }
        let parameters = symbols
            .get(method)
            .as_method()
            .map(|m| m.parameters.clone())
            .unwrap_or_default();
        let callee = symbols.qualified_name(method);
        let caller_tree = self.engine.frames[self.frame].tree;
        let mut bound = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let argument = strip_ref(argument);
            let value = self
                .engine
                .eval(self.frame, argument, &HashMap::new(), None);
            let name = self
                .engine
                .semantic
                .compilation
                .symbols()
                .get(*parameter)
                .name
                .clone();
            let input = Input {
                name,
                values: shown(&value),
                origin: Origin::Argument,
                places: vec![(self.engine.path(caller_tree), argument.span)],
            };
            bound.insert(*parameter, (value, input));
        }
        let frame = self
            .engine
            .push_frame(tree, body, Some(method), local_function, bound);
        let mut chain = self.chain.clone();
        chain.push(CallStep {
            text: self.engine.text(caller_tree, span),
            callee: callee.clone(),
            path: self.engine.path(caller_tree),
            span,
        });
        // A member a subtype may override is not known to be the one that
        // runs: what it does is at most possible.
        let dispatched;
        let conds = if self.dispatch_unknown(method, receiver, virtual_call) {
            let words = match receiver {
                Some(receiver) => format!("{} runs {callee}", self.text(receiver.span)),
                None => format!("this runs {callee}"),
            };
            let mut with = conds.to_vec();
            with.push(self.cond(Test::Opaque(words), true, span));
            dispatched = with;
            &dispatched[..]
        } else {
            conds
        };
        self.stack.push(method);
        let mut inner = Vec::new();
        self.engine
            .collect(frame, conds, &chain, self.stack, &mut inner);
        self.stack.pop();
        for found in inner {
            self.record(found);
        }
    }
}

// MARK: - helpers

/// Whether a symbol is declared in the project's own files.
fn is_delegate(semantic: &Semantic, ty: &Type) -> bool {
    match ty {
        Type::Named { symbol, .. } => {
            semantic.compilation.symbols().get(*symbol).type_kind() == Some(TypeKind::Delegate)
        }
        _ => false,
    }
}

/// The exception types an exception the analysis names is caught as, besides
/// its own and `Exception`.
fn implicit_bases(exception: &str) -> &'static [&'static str] {
    match exception {
        "DivideByZeroException" => &["ArithmeticException", "SystemException"],
        "ArgumentOutOfRangeException" | "ArgumentNullException" => {
            &["ArgumentException", "SystemException"]
        }
        "KeyNotFoundException"
        | "NullReferenceException"
        | "IndexOutOfRangeException"
        | "FormatException"
        | "InvalidOperationException" => &["SystemException"],
        _ => &[],
    }
}

fn in_project(semantic: &Semantic, symbol: SymbolId) -> bool {
    semantic
        .compilation
        .symbols()
        .get(symbol)
        .locations
        .iter()
        .any(|location| semantic.paths.contains_key(&location.tree))
}

/// Every statement and expression of `body`, as [`walk_body`] walks them,
/// and then the lambdas nothing in the tree reaches: those of a call that
/// did not resolve, which the editor binds all the same and keeps beside
/// the tree. A write or a call inside one is still a write or a call.
fn walk_everything<'a>(body: &'a BoundBody, visit: &mut dyn FnMut(Visited<'a>)) {
    let mut reached = HashSet::new();
    walk_body(body, &mut |visited| {
        if let Visited::Expression(BoundExpression {
            kind: E::Lambda(index),
            ..
        }) = visited
        {
            reached.insert(*index);
        }
        visit(visited);
    });
    for (index, lambda) in body.lambdas.iter().enumerate() {
        if !reached.contains(&index) {
            walk_statement(body, &lambda.body, &mut |visited| {
                if let Visited::Expression(BoundExpression {
                    kind: E::Lambda(inner),
                    ..
                }) = visited
                {
                    reached.insert(*inner);
                }
                visit(visited);
            });
        }
    }
}

/// Whether a statement holds a `return`, a `throw` or a `goto` that is not in
/// a lambda: where it may leave the body.
fn contains_leave(statement: &BoundStatement) -> bool {
    match &statement.kind {
        S::Return(_) | S::Throw(_) | S::YieldBreak | S::Goto(_) => true,
        S::Expression(e) if matches!(e.kind, E::Throw(_)) => true,
        _ => statement_children(statement)
            .0
            .into_iter()
            .any(contains_leave),
    }
}

/// Whether a statement is one a `goto` can name: `Again: ...`.
fn is_labeled(statement: &BoundStatement) -> bool {
    match &statement.kind {
        S::Label(_) => true,
        S::Block(list) => list.first().is_some_and(is_labeled),
        _ => false,
    }
}

fn strip(e: &BoundExpression) -> &BoundExpression {
    match &e.kind {
        E::Conversion { operand, .. } => strip(operand),
        _ => e,
    }
}

fn strip_ref(e: &BoundExpression) -> &BoundExpression {
    match &e.kind {
        E::RefArgument { operand, .. } => operand,
        _ => e,
    }
}

/// Whether `target` is the field, or the auto-property, `field`.
fn is_field(target: &BoundExpression, field: SymbolId) -> bool {
    match &strip(target).kind {
        E::Field { field: f, .. } => *f == field,
        E::Property { property, .. } => *property == field,
        _ => false,
    }
}

/// The `get` accessor with a body, of a property declared with accessors.
fn getter(owner: &SyntaxNode) -> Option<SyntaxNode> {
    if !matches!(
        owner.kind(),
        SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration
    ) || owner
        .child_of_kind(SyntaxKind::ArrowExpressionClause)
        .is_some()
    {
        return None;
    }
    owner
        .child_of_kind(SyntaxKind::AccessorList)?
        .children()
        .find(|accessor| {
            accessor.kind() == SyntaxKind::GetAccessorDeclaration
                && accessor.children().any(|c| {
                    matches!(
                        c.kind(),
                        SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                    )
                })
        })
}

/// Whether `text` is what `Parse` of the number type accepts.
fn parses(text: &str, special: SpecialType) -> bool {
    let text = text.trim();
    match special {
        SpecialType::Single | SpecialType::Double | SpecialType::Decimal => {
            text.parse::<f64>().is_ok()
        }
        SpecialType::Boolean => {
            text.eq_ignore_ascii_case("true") || text.eq_ignore_ascii_case("false")
        }
        _ => text.parse::<i128>().is_ok(),
    }
}

/// The number type a `Parse` or a `Convert.ToX` gives.
fn parsed_type(container: &str, name: &str) -> Option<SpecialType> {
    let by_type = |full: &str| {
        Some(match full {
            "System.Int32" => SpecialType::Int32,
            "System.Int64" => SpecialType::Int64,
            "System.Int16" => SpecialType::Int16,
            "System.UInt32" => SpecialType::UInt32,
            "System.UInt64" => SpecialType::UInt64,
            "System.UInt16" => SpecialType::UInt16,
            "System.Byte" => SpecialType::Byte,
            "System.SByte" => SpecialType::SByte,
            "System.Single" => SpecialType::Single,
            "System.Double" => SpecialType::Double,
            "System.Decimal" => SpecialType::Decimal,
            "System.Boolean" => SpecialType::Boolean,
            _ => return None,
        })
    };
    if name == "Parse" {
        return by_type(container);
    }
    if container == "System.Convert" {
        return by_type(&format!("System.{}", name.strip_prefix("To")?));
    }
    None
}

/// The locals a pattern declares.
fn pattern_locals(pattern: &BoundPattern, found: &mut Vec<LocalId>) {
    match &pattern.kind {
        P::Unsupported(_) | P::Discard | P::Type(_) | P::Constant(_) | P::Relational { .. } => {}
        P::Var { local } | P::VarDeconstruct { local, .. } | P::SpanString { local, .. } => {
            found.push(*local);
        }
        P::Declaration { local, .. } => found.extend(*local),
        P::Recursive(recursive) => {
            found.extend(recursive.local);
            for (_, inner) in &recursive.properties {
                pattern_locals(inner, found);
            }
            for inner in &recursive.positional {
                pattern_locals(inner, found);
            }
        }
        P::List(list) => {
            found.extend(list.local);
            for inner in list.patterns() {
                pattern_locals(inner, found);
            }
        }
        P::And(a, b) | P::Or(a, b) => {
            pattern_locals(a, found);
            pattern_locals(b, found);
        }
        P::Not(inner) | P::UnionCase { inner, .. } => pattern_locals(inner, found),
    }
}

/// What a node of the tree writes to a variable of the body: each variable,
/// and the value it is given where one is named.
fn writes_of<'a>(visited: Visited<'a>, write: &mut dyn FnMut(Atom, Option<&'a BoundExpression>)) {
    let mut declared = Vec::new();
    match visited {
        Visited::Statement(statement) => match &statement.kind {
            S::LocalDeclaration {
                local,
                initializer: Some(value),
            } => write(Atom::Local(*local), Some(value)),
            S::ForEach { local, .. } => write(Atom::Local(*local), None),
            S::Using { resources, .. } => {
                for resource in resources {
                    write(Atom::Local(resource.local), Some(&resource.value));
                }
            }
            S::Try { catches, .. } => {
                for local in catches.iter().filter_map(|c| c.local) {
                    write(Atom::Local(local), None);
                }
            }
            S::Switch { sections, .. } => {
                for section in sections {
                    for label in &section.labels {
                        if let BoundSwitchLabel::Case(case) = label {
                            pattern_locals(&case.pattern, &mut declared);
                        }
                    }
                }
            }
            _ => {}
        },
        Visited::Expression(e) => match &e.kind {
            E::Assignment { target, value } => {
                if let Some(atom @ (Atom::Local(_) | Atom::Param(_))) = place_atom(target) {
                    write(atom, Some(value));
                }
            }
            E::CompoundAssignment { target, .. } | E::Increment { target, .. } => {
                if let Some(atom @ (Atom::Local(_) | Atom::Param(_))) = place_atom(target) {
                    write(atom, None);
                }
            }
            E::RefArgument { kind, operand } if *kind != RefKind::In => {
                if let Some(atom @ (Atom::Local(_) | Atom::Param(_))) = place_atom(operand) {
                    write(atom, None);
                }
            }
            E::AddressOf { operand } | E::MakeRef(operand) => {
                if let Some(atom @ (Atom::Local(_) | Atom::Param(_))) = place_atom(operand) {
                    write(atom, None);
                }
            }
            E::IsPattern { pattern, .. } => pattern_locals(pattern, &mut declared),
            E::Switch { arms, .. } => {
                for arm in arms {
                    pattern_locals(&arm.pattern, &mut declared);
                }
            }
            _ => {}
        },
    }
    for local in declared {
        write(Atom::Local(local), None);
    }
}

/// Every atom an expression reads, not looking into calls.
fn atoms_of(e: &BoundExpression, add: &mut dyn FnMut(Atom)) {
    match &e.kind {
        E::Parameter(p) => add(Atom::Param(*p)),
        E::Local(l) => add(Atom::Local(*l)),
        E::Field {
            field, receiver, ..
        } => add(field_atom(*field, receiver.as_deref())),
        E::Property {
            property, receiver, ..
        } => add(field_atom(*property, receiver.as_deref())),
        _ => {}
    }
    for child in expression_children(e) {
        atoms_of(child, add);
    }
}

fn shown(values: &Abs) -> Option<Vec<String>> {
    match values {
        Abs::Set(values) => Some(values.iter().map(Val::show).collect()),
        Abs::Top => None,
    }
}

fn unknown_input(name: String) -> Input {
    Input {
        name,
        values: None,
        origin: Origin::Unknown,
        places: Vec::new(),
    }
}

/// The opposite of a condition, as C# would write it.
fn negated(e: &BoundExpression, text_of: &dyn Fn(&BoundExpression) -> String) -> String {
    match &e.kind {
        E::Binary {
            operator,
            left,
            right,
        } => {
            let flipped = match operator {
                BinaryOperator::Equality => "!=",
                BinaryOperator::Inequality => "==",
                BinaryOperator::LessThan => ">=",
                BinaryOperator::GreaterThan => "<=",
                BinaryOperator::LessThanOrEqual => ">",
                BinaryOperator::GreaterThanOrEqual => "<",
                _ => return format!("!({})", text_of(e)),
            };
            format!("{} {flipped} {}", text_of(left), text_of(right))
        }
        E::Unary {
            operator: UnaryOperator::LogicalNot,
            operand,
        } => text_of(operand),
        E::Parameter(_) | E::Local(_) | E::Field { .. } | E::Property { .. } | E::Call { .. } => {
            format!("!{}", text_of(e))
        }
        _ => format!("!({})", text_of(e)),
    }
}

const fn is_integral(special: SpecialType) -> bool {
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
    )
}

fn is_reference(semantic: &Semantic, ty: &Type) -> bool {
    match ty {
        Type::Named { symbol, .. } => semantic
            .compilation
            .symbols()
            .get(*symbol)
            .as_named_type()
            .and_then(|t| t.type_kind)
            .is_some_and(|kind| {
                matches!(
                    kind,
                    TypeKind::Class | TypeKind::Interface | TypeKind::Delegate | TypeKind::Record
                )
            }),
        Type::Array { .. } => true,
        _ => false,
    }
}

/// Whether a value is one the integer type can hold; anything else is.
fn fits(special: Option<SpecialType>, value: &Val) -> bool {
    let (Some(special), Val::Int(v)) = (special, value) else {
        return true;
    };
    let (low, high): (i128, i128) = match special {
        SpecialType::SByte => (i128::from(i8::MIN), i128::from(i8::MAX)),
        SpecialType::Byte => (0, i128::from(u8::MAX)),
        SpecialType::Int16 => (i128::from(i16::MIN), i128::from(i16::MAX)),
        SpecialType::UInt16 | SpecialType::Char => (0, i128::from(u16::MAX)),
        SpecialType::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
        SpecialType::UInt32 => (0, i128::from(u32::MAX)),
        SpecialType::Int64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
        SpecialType::UInt64 => (0, i128::from(u64::MAX)),
        _ => return true,
    };
    (low..=high).contains(v)
}

fn convert(value: &Val, to: Option<SpecialType>) -> Option<Val> {
    Some(match (to, value) {
        (Some(s), Val::Float(f)) if is_integral(s) =>
        {
            #[allow(clippy::cast_possible_truncation)]
            Val::Int(f.trunc() as i128)
        }
        (Some(SpecialType::Single | SpecialType::Double), v) => Val::Float(v.number()?),
        (Some(SpecialType::Char), Val::Int(i)) => {
            Val::Char(char::from_u32(u32::try_from(*i).ok()?)?)
        }
        (Some(s), Val::Char(c)) if is_integral(s) && s != SpecialType::Char => {
            Val::Int(i128::from(u32::from(*c)))
        }
        _ => value.clone(),
    })
}

fn unary(operator: UnaryOperator, value: &Val) -> Option<Val> {
    Some(match (operator, value) {
        (UnaryOperator::Plus, v) => v.clone(),
        (UnaryOperator::Minus, Val::Int(i)) => Val::Int(-i),
        (UnaryOperator::Minus, Val::Float(f)) => Val::Float(-f),
        (UnaryOperator::LogicalNot, Val::Bool(b)) => Val::Bool(!b),
        (UnaryOperator::BitwiseNot, Val::Int(i)) => Val::Int(!i),
        _ => return None,
    })
}

fn equal(a: &Val, b: &Val) -> Option<bool> {
    Some(match (a, b) {
        (Val::Null, Val::Null) => true,
        (Val::Null, _) | (_, Val::Null) => false,
        (Val::Object | Val::Array(_), _) | (_, Val::Object | Val::Array(_)) => return None,
        (Val::Bool(x), Val::Bool(y)) => x == y,
        (Val::Str(x), Val::Str(y)) => x == y,
        _ => a.number()? == b.number()?,
    })
}

fn binary(operator: BinaryOperator, a: &Val, b: &Val, integral: bool) -> Option<Val> {
    use BinaryOperator as B;
    let compare = |f: fn(f64, f64) -> bool| Some(Val::Bool(f(a.number()?, b.number()?)));
    match operator {
        B::Equality => equal(a, b).map(Val::Bool),
        B::Inequality => equal(a, b).map(|e| Val::Bool(!e)),
        B::LessThan => compare(|x, y| x < y),
        B::GreaterThan => compare(|x, y| x > y),
        B::LessThanOrEqual => compare(|x, y| x <= y),
        B::GreaterThanOrEqual => compare(|x, y| x >= y),
        B::LogicalAnd | B::BitwiseAnd if matches!((a, b), (Val::Bool(_), Val::Bool(_))) => {
            Some(Val::Bool(a == &Val::Bool(true) && b == &Val::Bool(true)))
        }
        B::LogicalOr | B::BitwiseOr if matches!((a, b), (Val::Bool(_), Val::Bool(_))) => {
            Some(Val::Bool(a == &Val::Bool(true) || b == &Val::Bool(true)))
        }
        B::ExclusiveOr if matches!((a, b), (Val::Bool(_), Val::Bool(_))) => Some(Val::Bool(a != b)),
        B::Coalesce => Some(if *a == Val::Null {
            b.clone()
        } else {
            a.clone()
        }),
        B::Add => match (a, b) {
            (Val::Str(x), y) => Some(Val::Str(format!("{x}{}", plain(y)))),
            (x, Val::Str(y)) => Some(Val::Str(format!("{}{y}", plain(x)))),
            _ => arithmetic(a, b, integral, i128::checked_add, |x, y| x + y),
        },
        B::Subtract => arithmetic(a, b, integral, i128::checked_sub, |x, y| x - y),
        B::Multiply => arithmetic(a, b, integral, i128::checked_mul, |x, y| x * y),
        B::Divide => arithmetic(a, b, integral, |x, y| (y != 0).then(|| x / y), |x, y| x / y),
        B::Modulo => arithmetic(a, b, integral, |x, y| (y != 0).then(|| x % y), |x, y| x % y),
        B::BitwiseAnd => Some(Val::Int(a.integer()? & b.integer()?)),
        B::BitwiseOr => Some(Val::Int(a.integer()? | b.integer()?)),
        B::ExclusiveOr => Some(Val::Int(a.integer()? ^ b.integer()?)),
        B::LeftShift => Some(Val::Int(
            a.integer()?
                .checked_shl(u32::try_from(b.integer()?).ok()?)?,
        )),
        B::RightShift | B::UnsignedRightShift => Some(Val::Int(
            a.integer()?
                .checked_shr(u32::try_from(b.integer()?).ok()?)?,
        )),
        _ => None,
    }
}

fn plain(value: &Val) -> String {
    match value {
        Val::Str(s) => s.clone(),
        Val::Char(c) => c.to_string(),
        Val::Null => String::new(),
        Val::Bool(true) => "True".to_owned(),
        Val::Bool(false) => "False".to_owned(),
        other => other.show(),
    }
}

fn arithmetic(
    a: &Val,
    b: &Val,
    integral: bool,
    int: fn(i128, i128) -> Option<i128>,
    float: fn(f64, f64) -> f64,
) -> Option<Val> {
    if integral {
        return Some(Val::Int(int(a.integer()?, b.integer()?)?));
    }
    match (a, b) {
        (Val::Int(x), Val::Int(y)) => Some(Val::Int(int(*x, *y)?)),
        _ => Some(Val::Float(float(a.number()?, b.number()?))),
    }
}

#[cfg(test)]
mod tests;
