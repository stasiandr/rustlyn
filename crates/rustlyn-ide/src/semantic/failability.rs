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
//!    early `return` before it, the `&&`, `?:` and `??` it sits under.
//! 3. **Can it**: each condition is evaluated over the values its inputs can
//!    have. A parameter has what every call in the project passes; a field
//!    what its initializer and every assignment write (only the default,
//!    when nothing does); a local what is assigned to it. Where all of them
//!    are known, the conditions are tried for every combination, and the
//!    failure is *never*, *always* or *possible*; where something is not
//!    known, it is *unknown*, and the inputs say which one.
//!
//! The analysis is flow-insensitive about values — a field holds whatever
//! any write gives it, at any time — which errs towards "possible", never
//! towards "never".

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundExpression, BoundExpressionKind as E, BoundPatternKind,
    BoundStatement, BoundStatementKind as S, BoundSwitchLabel, ConstantValue, LocalId, MethodKind,
    Modifiers, RefKind, SemanticModel, SpecialType, SymbolId, SymbolKind, Type, TypeKind,
    UnaryOperator,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::walk::{Visited, expression_children, walk_body, walk_statement};
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
    /// Every value the inputs can have leads to it: the member fails
    /// whenever it gets there.
    Always,
    /// Some values lead to it.
    Possible,
    /// None do: the conditions never hold together.
    Never,
    /// An input's values are not known.
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
}

// MARK: - the engine

/// Something a condition reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Atom {
    Param(SymbolId),
    Field(SymbolId),
    Local(LocalId),
}

/// An atom in the frame it is read in.
type Key = (usize, Atom);

/// One bound body being looked at: the member asked about, a member called
/// on the way, or a caller whose arguments are being evaluated.
struct Frame {
    tree: usize,
    body: Arc<BoundBody>,
    /// The member the body is of.
    member: Option<SymbolId>,
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
    /// Something the values cannot tell, said in words: "the sequence is
    /// empty".
    Opaque(String),
}

#[derive(Clone, Debug)]
struct Cond {
    frame: usize,
    test: Test,
    /// Whether the test holds on the way, or its opposite does.
    holds: bool,
    span: TextSpan,
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
        let frame = engine.push_frame(tree, body, member, HashMap::new());
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
        arguments: HashMap<SymbolId, (Abs, Input)>,
    ) -> usize {
        self.frames.push(Frame {
            tree,
            body,
            member,
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
        let symbol = self.semantic.compilation.symbols().get(property);
        if symbol.kind != SymbolKind::Property || !in_project(self.semantic, property) {
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
        let mut walker = Walker {
            engine: self,
            frame,
            chain: chain.to_vec(),
            stack,
            found: Vec::new(),
            catches: Vec::new(),
        };
        let mut conds = conditions.to_vec();
        walker.statements(&body.statements, &mut conds);
        let mine = std::mem::take(&mut walker.found);
        found.extend(mine);
    }

    // MARK: judging

    fn judge(&mut self, found: Found) -> Failure {
        // The atoms the conditions read, and what each can be.
        let mut keys: Vec<Key> = Vec::new();
        for cond in &found.conditions {
            let mut add = |expression: &BoundExpression| {
                atoms_of(expression, &mut |atom| {
                    let key = (cond.frame, atom);
                    if !keys.contains(&key) {
                        keys.push(key);
                    }
                });
            };
            match &cond.test {
                Test::Truth(e) | Test::Null(e) | Test::Zero(e) | Test::Parses(e, _) => add(e),
                Test::Equals(a, b) | Test::OutOfRange(a, b) => {
                    add(a);
                    add(b);
                }
                Test::Opaque(_) => {}
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
        let value = match &cond.test {
            Test::Truth(e) => self.eval(cond.frame, e, assignment),
            Test::Null(e) => {
                let v = self.eval(cond.frame, e, assignment);
                v.map(&|v| Some(Val::Bool(*v == Val::Null)))
            }
            Test::Zero(e) => {
                let v = self.eval(cond.frame, e, assignment);
                v.map(&|v| v.number().map(|n| Val::Bool(n == 0.0)))
            }
            Test::Equals(a, b) => {
                let a = self.eval(cond.frame, a, assignment);
                let b = self.eval(cond.frame, b, assignment);
                a.map2(&b, &|x, y| equal(x, y).map(Val::Bool))
            }
            Test::OutOfRange(array, index) => {
                let array = self.eval(cond.frame, array, assignment);
                let index = self.eval(cond.frame, index, assignment);
                array.map2(&index, &|a, i| match (a, i.integer()?) {
                    (Val::Array(length), i) => {
                        Some(Val::Bool(i < 0 || i >= i128::try_from(*length).ok()?))
                    }
                    _ => None,
                })
            }
            Test::Parses(text, special) => {
                let text = self.eval(cond.frame, text, assignment);
                let special = *special;
                text.map(&|v| match v {
                    Val::Str(s) => Some(Val::Bool(parses(s, special))),
                    Val::Null => Some(Val::Bool(false)),
                    _ => None,
                })
            }
            Test::Opaque(_) => Abs::Top,
        };
        let truth = value.truth();
        if cond.holds {
            truth
        } else {
            match truth {
                Tri::True => Tri::False,
                Tri::False => Tri::True,
                other => other,
            }
        }
    }

    fn condition(&self, cond: &Cond) -> Condition {
        let tree = self.frames[cond.frame].tree;
        let text_of = |e: &BoundExpression| self.text(tree, e.span);
        let text = match (&cond.test, cond.holds) {
            (Test::Truth(e), true) => text_of(e),
            (Test::Truth(e), false) => negated(e, &text_of),
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
            (Test::Opaque(words), _) => words.clone(),
        };
        Condition {
            text,
            path: self.path(tree),
            span: cond.span,
        }
    }

    // MARK: evaluating

    fn eval(&mut self, frame: usize, e: &BoundExpression, assignment: &HashMap<Key, Val>) -> Abs {
        match &e.kind {
            E::Literal(value) => Abs::one(Val::from_constant(value)),
            E::Parameter(p) => self.read((frame, Atom::Param(*p)), assignment),
            E::Local(l) => self.read((frame, Atom::Local(*l)), assignment),
            E::Field { field, .. } => {
                if let Some(constant) = self.constant(*field) {
                    return Abs::one(constant);
                }
                self.read((frame, Atom::Field(*field)), assignment)
            }
            E::Default(ty) => self.default_of(frame, ty).map_or(Abs::Top, Abs::one),
            E::Conversion { operand, .. } => {
                let value = self.eval(frame, operand, assignment);
                let special = self.special(frame, &e.ty);
                value.map(&|v| convert(v, special))
            }
            E::Unary { operator, operand } => {
                let value = self.eval(frame, operand, assignment);
                let operator = *operator;
                value.map(&|v| unary(operator, v))
            }
            E::Binary {
                operator,
                left,
                right,
            } => {
                let left = self.eval(frame, left, assignment);
                // `a && b` with `a` false is false, whatever `b` would be.
                match (operator, left.truth()) {
                    (BinaryOperator::LogicalAnd, Tri::False) => return Abs::one(Val::Bool(false)),
                    (BinaryOperator::LogicalOr, Tri::True) => return Abs::one(Val::Bool(true)),
                    _ => {}
                }
                let right = self.eval(frame, right, assignment);
                let operator = *operator;
                let integral = self.special(frame, &e.ty).is_some_and(is_integral);
                left.map2(&right, &|a, b| binary(operator, a, b, integral))
            }
            E::Conditional {
                condition,
                consequence,
                alternative,
            } => match self.eval(frame, condition, assignment).truth() {
                Tri::True => self.eval(frame, consequence, assignment),
                Tri::False => self.eval(frame, alternative, assignment),
                _ => {
                    let a = self.eval(frame, consequence, assignment);
                    let b = self.eval(frame, alternative, assignment);
                    a.union(b)
                }
            },
            E::ArrayCreation {
                lengths, elements, ..
            } => match lengths.as_slice() {
                [] => Abs::one(Val::Array(elements.len())),
                [length] => self.eval(frame, length, assignment).map(&|v| {
                    v.integer()
                        .and_then(|n| usize::try_from(n).ok())
                        .map(Val::Array)
                }),
                _ => Abs::one(Val::Object),
            },
            E::ArrayLength { array } => self.eval(frame, array, assignment).map(&|v| match v {
                Val::Array(length) => i128::try_from(*length).ok().map(Val::Int),
                _ => None,
            }),
            E::ObjectCreation { .. }
            | E::This
            | E::Lambda(_)
            | E::DelegateCreation { .. }
            | E::InterpolatedString(_) => Abs::one(Val::Object),
            E::Property { property, .. } if self.is_auto_property(*property) => {
                self.read((frame, Atom::Field(*property)), assignment)
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
        if let Some(found) = self.atoms.get(&key) {
            return found.clone();
        }
        if !self.evaluating.insert(key) {
            let name = self.atom_name(key);
            return (Abs::Top, unknown_input(name));
        }
        let (frame, atom) = key;
        let found = match atom {
            Atom::Param(p) => match self.frames[frame].arguments.get(&p) {
                Some(found) => found.clone(),
                None => self.parameter(frame, p),
            },
            // A property with a body computes what it gives: not an atom.
            Atom::Field(f)
                if self.semantic.compilation.symbols().get(f).kind == SymbolKind::Property
                    && !self.is_auto_property(f) =>
            {
                let name = self.atom_name(key);
                (Abs::Top, unknown_input(name))
            }
            Atom::Field(f) => self.field(f),
            Atom::Local(l) => self.local(frame, l),
        };
        self.evaluating.remove(&key);
        self.atoms.insert(key, found.clone());
        found
    }

    fn atom_name(&self, (frame, atom): Key) -> String {
        let symbols = self.semantic.compilation.symbols();
        match atom {
            Atom::Param(s) | Atom::Field(s) => symbols.get(s).name.clone(),
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
        let found = if self.escapes(member)
            || self.caller_depth >= CALLER_DEPTH
            || !self.evaluating_params.insert(member)
        {
            let origin = if self.escapes(member) {
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
                                self.eval(*frame, strip_ref(argument), &HashMap::new())
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
                        let frame = self.push_frame(tree, body.clone(), caller, HashMap::new());
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
                    let frame = self.push_frame(*tree, body.clone(), None, HashMap::new());
                    if let Some(BoundStatement {
                        kind: S::Return(Some(value)),
                        span,
                    }) = body.statements.first()
                    {
                        places.push((self.path(*tree), *span));
                        let value = self.eval(frame, value, &HashMap::new());
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
                    let frame = self.push_frame(tree, body.clone(), owner_symbol, HashMap::new());
                    for (value, span) in assigned {
                        writes += 1;
                        if places.len() < MAX_PLACES {
                            places.push((self.path(tree), span));
                        }
                        let value = self.eval(frame, &value, &HashMap::new());
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
            // write — unless a constructor writes it first.
            if !has_initializer && !in_constructor && !required {
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
        let mut given: Vec<BoundExpression> = Vec::new();
        let mut opaque = false;
        walk_everything(&body, &mut |visited| match visited {
            Visited::Statement(s) => match &s.kind {
                S::LocalDeclaration {
                    local: declared,
                    initializer: Some(value),
                } if *declared == local => given.push(value.clone()),
                S::ForEach {
                    local: declared, ..
                } if *declared == local => opaque = true,
                _ => {}
            },
            Visited::Expression(e) => match &e.kind {
                E::Assignment { target, value } if is_local(target, local) => {
                    given.push((**value).clone());
                }
                E::CompoundAssignment { target, .. } | E::Increment { target, .. }
                    if is_local(target, local) =>
                {
                    opaque = true;
                }
                E::RefArgument { operand, .. } if is_local(operand, local) => opaque = true,
                E::IsPattern { pattern, .. } if declares(pattern, local) => opaque = true,
                _ => {}
            },
        });
        let values = if opaque || given.is_empty() {
            Abs::Top
        } else {
            let mut values = Abs::Set(Vec::new());
            for value in &given {
                let value = self.eval(frame, value, &HashMap::new());
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

struct Walker<'e, 's> {
    engine: &'e mut Engine<'s>,
    frame: usize,
    chain: Vec<CallStep>,
    stack: &'e mut Vec<SymbolId>,
    found: Vec<Found>,
    /// The `catch` clauses around where the walk is, innermost last.
    catches: Vec<Vec<Type>>,
}

impl Walker<'_, '_> {
    fn cond(&self, test: Test, holds: bool, span: TextSpan) -> Cond {
        Cond {
            frame: self.frame,
            test,
            holds,
            span,
        }
    }

    /// Walks a list of statements; whether it always leaves.
    fn statements(&mut self, list: &[BoundStatement], conds: &mut Vec<Cond>) -> bool {
        let base = conds.len();
        for statement in list {
            if self.statement(statement, conds) {
                conds.truncate(base);
                return true;
            }
        }
        conds.truncate(base);
        false
    }

    /// Walks a statement; whether it always leaves (returns, throws, jumps).
    /// What holds after it, because it left otherwise, is pushed onto
    /// `conds` for the statements that follow.
    fn statement(&mut self, statement: &BoundStatement, conds: &mut Vec<Cond>) -> bool {
        match &statement.kind {
            S::Block(list) => self.statements(list, conds),
            S::LocalDeclaration { initializer, .. } => {
                if let Some(value) = initializer {
                    self.expression(value, conds);
                }
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
                conds.push(self.cond(Test::Truth(condition.clone()), true, condition.span));
                let then_leaves = self.statement(consequence, conds);
                conds.truncate(base);
                conds.push(self.cond(Test::Truth(condition.clone()), false, condition.span));
                let else_leaves = alternative
                    .as_deref()
                    .is_some_and(|alternative| self.statement(alternative, conds));
                conds.truncate(base);
                match (then_leaves, else_leaves) {
                    (true, true) => return true,
                    (true, false) => {
                        conds.push(self.cond(Test::Truth(condition.clone()), false, condition.span))
                    }
                    (false, true) => {
                        conds.push(self.cond(Test::Truth(condition.clone()), true, condition.span))
                    }
                    (false, false) => {}
                }
                false
            }
            S::While { condition, body } => {
                self.expression(condition, conds);
                let base = conds.len();
                conds.push(self.cond(Test::Truth(condition.clone()), true, condition.span));
                self.statement(body, conds);
                conds.truncate(base);
                false
            }
            S::DoWhile { body, condition } => {
                let base = conds.len();
                self.statement(body, conds);
                conds.truncate(base);
                self.expression(condition, conds);
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
                if let Some(condition) = condition {
                    self.expression(condition, conds);
                    conds.push(self.cond(Test::Truth(condition.clone()), true, condition.span));
                }
                self.statement(body, conds);
                for incrementor in incrementors {
                    self.expression(incrementor, conds);
                }
                conds.truncate(base);
                false
            }
            S::ForEach {
                collection, body, ..
            } => {
                self.expression(collection, conds);
                let base = conds.len();
                self.statement(body, conds);
                conds.truncate(base);
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
                    self.call(*constructor, arguments, statement.span, conds);
                }
                false
            }
            S::Switch {
                governing,
                sections,
            } => {
                self.expression(governing, conds);
                let base = conds.len();
                for section in sections {
                    let label = match section.labels.as_slice() {
                        [BoundSwitchLabel::Case(case)] if case.when.is_none() => {
                            match &case.pattern.kind {
                                BoundPatternKind::Constant(value) => Some(value.clone()),
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    if let Some(value) = label {
                        let span = value.span;
                        conds.push(self.cond(Test::Equals(governing.clone(), value), true, span));
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
                let caught: Vec<Type> = catches
                    .iter()
                    .filter(|c| c.filter.is_none())
                    .map(|c| c.exception_type.clone())
                    .collect();
                self.catches.push(caught);
                let base = conds.len();
                let body_leaves = self.statement(body, conds);
                conds.truncate(base);
                self.catches.pop();
                let mut all_leave = body_leaves;
                for catch in catches {
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
                let _ = resources;
                self.statement(body, conds)
            }
            S::Lock { value, body, .. } => {
                self.expression(value, conds);
                self.statement(body, conds)
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
            S::Unsupported(_) | S::Label(_) | S::Empty => false,
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
                conds.push(self.cond(Test::Truth((**left).clone()), holds, left.span));
                self.expression(right, conds);
            }
            E::Binary {
                operator: BinaryOperator::Coalesce,
                left,
                right,
            } => {
                self.expression(left, conds);
                conds.push(self.cond(Test::Null((**left).clone()), true, left.span));
                self.expression(right, conds);
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
                    with.push(self.cond(Test::Zero((**right).clone()), true, right.span));
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
                conds.push(self.cond(Test::Truth((**condition).clone()), true, condition.span));
                self.expression(consequence, conds);
                conds.truncate(base);
                conds.push(self.cond(Test::Truth((**condition).clone()), false, condition.span));
                self.expression(alternative, conds);
            }
            E::ConditionalAccess { receiver, access } => {
                self.expression(receiver, conds);
                conds.push(self.cond(Test::Null((**receiver).clone()), false, receiver.span));
                self.expression(access, conds);
            }
            E::Call {
                receiver,
                method,
                arguments,
                ..
            } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver, conds);
                    self.dereference(receiver, conds);
                }
                for argument in arguments {
                    self.expression(argument, conds);
                }
                self.call(*method, arguments, e.span, conds);
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
                    self.call(*constructor, arguments, e.span, conds);
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
                self.call(*property, &[], e.span, conds);
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
                    with.push(self.cond(
                        Test::OutOfRange((**array).clone(), index.clone()),
                        true,
                        index.span,
                    ));
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
            self.call(indexer, arguments, span, conds);
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
            if words == "is empty" && self.guarded(conds, &sequence_text, &["Any"], None) {
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

    /// Keeps a failure, unless a `catch` around it catches it.
    fn record(&mut self, found: Found) {
        if self.is_caught(&found) {
            return;
        }
        self.found.push(found);
    }

    fn is_caught(&mut self, found: &Found) -> bool {
        let catches: Vec<Type> = self.catches.iter().flatten().cloned().collect();
        if catches.is_empty() {
            return false;
        }
        let semantic = self.engine.semantic;
        let tree = self.engine.frames[self.frame].tree;
        let Some(model) = self.engine.model(tree) else {
            return false;
        };
        let binder = model.binder();
        catches.iter().any(|caught| {
            let is_exception = display_type(&semantic.compilation, caught) == "Exception";
            is_exception
                || found.exception_type.as_ref().is_some_and(|thrown| {
                    thrown == caught || binder.inherits_from_public(thrown, caught)
                })
                || (found.exception_type.is_none()
                    && display_type(&semantic.compilation, caught) == found.exception)
        })
    }

    /// Follows a call into a member of the project: what can fail in it can
    /// fail here, with its parameters being what this call passes.
    fn call(
        &mut self,
        method: SymbolId,
        arguments: &[BoundExpression],
        span: TextSpan,
        conds: &[Cond],
    ) {
        // What the library says about its own members comes first: the
        // body a reference assembly has is not the one that runs.
        if self.library(method, arguments, span, conds) {
            return;
        }
        if self.stack.len() >= CALL_DEPTH || self.stack.contains(&method) {
            return;
        }
        let Some((tree, body)) = self.engine.body_of(method) else {
            return;
        };
        let symbols = self.engine.semantic.compilation.symbols();
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
            let value = self.engine.eval(self.frame, argument, &HashMap::new());
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
        let frame = self.engine.push_frame(tree, body, Some(method), bound);
        let mut chain = self.chain.clone();
        chain.push(CallStep {
            text: self.engine.text(caller_tree, span),
            callee,
            path: self.engine.path(caller_tree),
            span,
        });
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

fn is_local(target: &BoundExpression, local: LocalId) -> bool {
    matches!(&strip(target).kind, E::Local(l) if *l == local)
}

fn declares(pattern: &rustlyn_semantics::BoundPattern, local: LocalId) -> bool {
    match &pattern.kind {
        BoundPatternKind::Declaration {
            local: declared, ..
        } => *declared == Some(local),
        BoundPatternKind::And(a, b) | BoundPatternKind::Or(a, b) => {
            declares(a, local) || declares(b, local)
        }
        BoundPatternKind::Not(inner) => declares(inner, local),
        _ => false,
    }
}

/// Every atom an expression reads, not looking into calls.
fn atoms_of(e: &BoundExpression, add: &mut dyn FnMut(Atom)) {
    match &e.kind {
        E::Parameter(p) => add(Atom::Param(*p)),
        E::Local(l) => add(Atom::Local(*l)),
        E::Field { field, .. } => add(Atom::Field(*field)),
        E::Property { property, .. } => add(Atom::Field(*property)),
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
