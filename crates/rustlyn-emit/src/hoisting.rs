//! Which of an iterator's locals its state machine keeps in fields, and the
//! fields it keeps them in (Roslyn's `IteratorAndAsyncCaptureWalker` and
//! `StateMachineRewriter`).
//!
//! `MoveNext` starts afresh each time it is called, so a local whose value
//! has to outlast a `yield return` cannot stay in one of its slots: it is
//! hoisted into a field of the machine. Which locals are, and what the
//! fields are called, is what reflection over a machine sees (`<s>5__2`),
//! and C# compilers agree on it, so this follows Roslyn:
//!
//! - an optimized build hoists only the locals read where a `yield` may have
//!   come between the write and the read, the ones a `finally` of a `try`
//!   that yields reads, and the ones a closure captures, whose display class
//!   the machine is. Each gets a field when its scope is entered, called
//!   `<x>5__N` with `N` one more than the count of fields handed out before
//!   it — the first is `5__2` — and hands that field on, once its scope has
//!   ended, to a later local of the same type;
//! - a debug build hoists every local the body declares, each in a field of
//!   its own, numbered in the order the locals are declared from `5__1`.
//!
//! A compiler temporary that is hoisted — a `foreach`'s enumerator, the array
//! it walks and how far, a `using`'s resource — is `<>7__wrapN` in an
//! optimized build and `<>s__N` in a debug one.

use std::collections::{HashMap, HashSet};

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundExpression, BoundExpressionKind, BoundStatement,
    BoundStatementKind, BoundSwitchLabel, LocalId, LocalSymbol, RefKind, TupleElement, Type,
};

use crate::async_machine::children;

/// Where an iterator's hoisted locals live.
#[derive(Default)]
pub(crate) struct HoistedLocals {
    /// Each field, named and typed, in the order it was handed out.
    pub(crate) fields: Vec<(String, Type)>,
    /// The field each hoisted local lives in: in an optimized build two
    /// locals of one type whose scopes do not overlap may share one.
    pub(crate) field_of: HashMap<LocalId, usize>,
}

/// Which of `candidates` a machine running `statements` keeps in fields, and
/// in which. `captured` are the ones a closure reads: the machine is its
/// display class, and they live in fields named after themselves whatever
/// else happens. `taken` are the names the machine's other fields have.
pub(crate) fn hoist(
    body: &BoundBody,
    statements: &[BoundStatement],
    candidates: &[(LocalId, LocalSymbol)],
    captured: &HashSet<LocalId>,
    optimize: bool,
    taken: &HashSet<String>,
) -> HoistedLocals {
    // The locals the machine's own statements use, as opposed to those of
    // the closures in it, whose methods have slots of their own.
    let mut own = HashSet::new();
    for statement in statements {
        used_in_statement(statement, &mut own);
    }
    // `None` where the body is beyond the analysis: then every local of it
    // is taken to outlast a `yield`.
    let crosses = Liveness::of(body, statements);
    let user = |local: LocalId| {
        body.locals
            .get(local.0 as usize)
            .is_some_and(|slot| !slot.name.starts_with('<'))
    };
    let mut names = Names {
        taken: taken.clone(),
    };
    let mut hoisted = HoistedLocals::default();
    // What a debug build keeps however short it lives: the user's locals,
    // and the temporaries a `foreach`, a `using` and a `lock` keep for as
    // long as they run.
    let lasting = lasting_temporaries(statements);
    let mut wanted = HashSet::new();
    for (local, symbol) in candidates {
        if captured.contains(local) {
            let name = names.unique(symbol.name.clone());
            hoisted.field_of.insert(*local, hoisted.fields.len());
            hoisted.fields.push((name, symbol.ty.clone()));
            continue;
        }
        if !own.contains(local) {
            continue;
        }
        let live = crosses
            .as_ref()
            .is_none_or(|crosses| crosses.contains(local));
        if live || (!optimize && (user(*local) || lasting.contains(local))) {
            wanted.insert(*local);
        }
    }
    let mut allocation = Allocation {
        body,
        wanted: wanted.clone(),
        declared: declared_by_statements(statements),
        optimize,
        next: usize::from(optimize),
        free: Vec::new(),
        names: &mut names,
        hoisted: &mut hoisted,
    };
    for statement in statements {
        allocation.statement(statement);
    }
    // Anything the walk did not meet gets a field of its own.
    let mut left: Vec<LocalId> = wanted
        .into_iter()
        .filter(|local| !allocation.hoisted.field_of.contains_key(local))
        .collect();
    left.sort_by_key(|local| local.0);
    allocation.scope(left, |_| {});
    hoisted
}

/// The field names a machine has handed out.
struct Names {
    taken: HashSet<String>,
}

impl Names {
    /// `name`, or where a field already has it, `name` made unique.
    fn unique(&mut self, name: String) -> String {
        if self.taken.insert(name.clone()) {
            return name;
        }
        let mut suffix = 1;
        loop {
            let candidate = format!("{name}~{suffix}");
            if self.taken.insert(candidate.clone()) {
                return candidate;
            }
            suffix += 1;
        }
    }
}

/// The fields, handed out in the order Roslyn meets the locals: each
/// scope's as the scope is entered, in the order it declares them. In an
/// optimized build (its `PossibleIteratorScope`) a scope gives its fields
/// back when it is left, for a later local of the same type; in a debug one
/// (its slots for the locals it hoists before it starts) every local keeps
/// its own.
struct Allocation<'a> {
    body: &'a BoundBody,
    wanted: HashSet<LocalId>,
    optimize: bool,
    /// The locals a statement declares; any other is a variable an
    /// expression declares (`out var`, a pattern), which belongs to the
    /// scope whose statements first mention it.
    declared: HashSet<LocalId>,
    /// Roslyn's `_nextHoistedFieldId`, which starts at one, in an optimized
    /// build; its next hoisted slot, from nought, in a debug one.
    next: usize,
    /// The fields given back, most recent last.
    free: Vec<(Type, usize)>,
    names: &'a mut Names,
    hoisted: &'a mut HoistedLocals,
}

impl Allocation<'_> {
    /// A scope declaring `locals`: their fields while `inner` runs.
    fn scope(&mut self, locals: Vec<LocalId>, inner: impl FnOnce(&mut Self)) {
        let mut here = Vec::new();
        for local in locals {
            if !self.wanted.contains(&local) || self.hoisted.field_of.contains_key(&local) {
                continue;
            }
            let Some(symbol) = self.body.locals.get(local.0 as usize) else {
                continue;
            };
            let key = reuse_key(&symbol.ty);
            let reused = self
                .free
                .iter()
                .rposition(|(ty, _)| *ty == key)
                .filter(|_| self.optimize);
            let field = match reused {
                Some(at) => self.free.remove(at).1,
                None => {
                    let id = self.next;
                    self.next += 1;
                    let name = match (symbol.name.starts_with('<'), self.optimize) {
                        (true, true) => format!("<>7__wrap{id}"),
                        (true, false) => format!("<>s__{}", id + 1),
                        (false, _) => format!("<{}>5__{}", symbol.name, id + 1),
                    };
                    let name = self.names.unique(name);
                    self.hoisted.fields.push((name, symbol.ty.clone()));
                    self.hoisted.fields.len() - 1
                }
            };
            self.hoisted.field_of.insert(local, field);
            here.push((key, field));
        }
        inner(self);
        self.free.extend(here);
    }

    fn statement(&mut self, statement: &BoundStatement) {
        match &statement.kind {
            BoundStatementKind::Block(statements) => {
                let locals = self.declared_in(statements);
                self.scope(locals, |this| {
                    for inner in statements {
                        this.statement(inner);
                    }
                });
            }
            BoundStatementKind::For {
                initializers, body, ..
            } => {
                let locals = self.declared_in(std::slice::from_ref(statement));
                let mut declared: Vec<LocalId> = initializers
                    .iter()
                    .filter_map(|initializer| match &initializer.kind {
                        BoundStatementKind::LocalDeclaration { local, .. } => Some(*local),
                        _ => None,
                    })
                    .collect();
                declared.extend(locals);
                self.scope(declared, |this| this.statement(body));
            }
            // An enumerator, or the array and how far through it, for the
            // whole loop; the variable for each time round.
            BoundStatementKind::ForEach { local, body, .. } => {
                self.scope(walked_with(statement), |this| {
                    this.scope(vec![*local], |this| this.statement(body));
                });
            }
            BoundStatementKind::Using { resources, body } => {
                let locals = resources.iter().map(|resource| resource.local).collect();
                self.scope(locals, |this| this.statement(body));
            }
            BoundStatementKind::Lock {
                held, taken, body, ..
            } => self.scope(vec![*held, *taken], |this| this.statement(body)),
            BoundStatementKind::Fixed { declarations, body } => {
                let locals = self.declared_in(declarations);
                self.scope(locals, |this| this.statement(body));
            }
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => {
                self.statement(body);
                for catch in catches {
                    self.scope(catch.local.into_iter().collect(), |this| {
                        this.statement(&catch.body);
                    });
                }
                if let Some(finally) = finally {
                    self.statement(finally);
                }
            }
            // What a section declares is in scope in every section.
            BoundStatementKind::Switch { sections, .. } => {
                let statements: Vec<BoundStatement> = sections
                    .iter()
                    .flat_map(|section| section.statements.iter().cloned())
                    .collect();
                let locals = self.declared_in(&statements);
                self.scope(locals, |this| {
                    for inner in &statements {
                        this.statement(inner);
                    }
                });
            }
            BoundStatementKind::If {
                consequence,
                alternative,
                ..
            } => {
                self.statement(consequence);
                if let Some(alternative) = alternative {
                    self.statement(alternative);
                }
            }
            BoundStatementKind::While { body, .. } | BoundStatementKind::DoWhile { body, .. } => {
                self.statement(body)
            }
            _ => {}
        }
    }

    /// What a list of statements declares, in the order they declare it:
    /// the locals of its declarations, and the variables its expressions
    /// declare that no scope met before.
    fn declared_in(&self, statements: &[BoundStatement]) -> Vec<LocalId> {
        let mut locals = Vec::new();
        for statement in statements {
            if let BoundStatementKind::LocalDeclaration { local, .. } = &statement.kind {
                locals.push(*local);
            }
            let mut mentioned = HashSet::new();
            for expression in own_expressions(statement) {
                used_in_expression(expression, &mut mentioned);
            }
            let mut mentioned: Vec<LocalId> = mentioned
                .into_iter()
                .filter(|local| {
                    !self.declared.contains(local) && !self.hoisted.field_of.contains_key(local)
                })
                .collect();
            mentioned.sort_by_key(|local| local.0);
            locals.extend(mentioned);
        }
        let mut seen = HashSet::new();
        locals.retain(|local| seen.insert(*local));
        locals
    }
}

/// The temporaries a statement keeps for as long as it runs: a `foreach`'s
/// variable and what it walks with, a `using`'s resources, a `lock`'s object
/// and whether it was taken.
fn lasting_temporaries(statements: &[BoundStatement]) -> HashSet<LocalId> {
    fn visit(statement: &BoundStatement, into: &mut HashSet<LocalId>) {
        if matches!(
            statement.kind,
            BoundStatementKind::ForEach { .. }
                | BoundStatementKind::Using { .. }
                | BoundStatementKind::Lock { .. }
        ) {
            into.extend(declared_by(statement));
        }
        for inner in substatements(statement) {
            visit(inner, into);
        }
    }
    let mut lasting = HashSet::new();
    for statement in statements {
        visit(statement, &mut lasting);
    }
    lasting
}

/// A type as fields are shared by it: element names make no tuple another
/// (Roslyn compares ignoring them).
fn reuse_key(ty: &Type) -> Type {
    match ty {
        Type::Tuple(elements) => Type::Tuple(
            elements
                .iter()
                .map(|element| TupleElement {
                    name: None,
                    ty: reuse_key(&element.ty),
                })
                .collect(),
        ),
        Type::Named {
            symbol,
            type_arguments,
        } => Type::Named {
            symbol: *symbol,
            type_arguments: type_arguments.iter().map(reuse_key).collect(),
        },
        Type::Array { element, rank } => Type::Array {
            element: Box::new(reuse_key(element)),
            rank: *rank,
        },
        other => other.clone(),
    }
}

/// The locals the statements declare with a statement of their own, as
/// [`declared_by`] finds them, however deep.
fn declared_by_statements(statements: &[BoundStatement]) -> HashSet<LocalId> {
    fn visit(statement: &BoundStatement, into: &mut HashSet<LocalId>) {
        into.extend(declared_by(statement));
        for inner in substatements(statement) {
            visit(inner, into);
        }
    }
    let mut declared = HashSet::new();
    for statement in statements {
        visit(statement, &mut declared);
    }
    declared
}

/// The locals a statement declares itself: a declaration's, a `foreach`'s
/// variable and what it walks with, a `using`'s resources, a `lock`'s object
/// and whether it was taken, a `catch`'s exception.
fn declared_by(statement: &BoundStatement) -> Vec<LocalId> {
    match &statement.kind {
        BoundStatementKind::LocalDeclaration { local, .. } => vec![*local],
        BoundStatementKind::ForEach { local, .. } => {
            let mut declared = walked_with(statement);
            declared.push(*local);
            declared
        }
        BoundStatementKind::Using { resources, .. } => {
            resources.iter().map(|resource| resource.local).collect()
        }
        BoundStatementKind::Lock { held, taken, .. } => vec![*held, *taken],
        BoundStatementKind::Try { catches, .. } => {
            catches.iter().filter_map(|catch| catch.local).collect()
        }
        _ => Vec::new(),
    }
}

/// What a `foreach` walks its collection with: the enumerator, or the array
/// and how far through it — an index and its bound per dimension of one
/// with more than one.
fn walked_with(statement: &BoundStatement) -> Vec<LocalId> {
    let BoundStatementKind::ForEach {
        enumeration,
        walk,
        dimensions,
        ..
    } = &statement.kind
    else {
        return Vec::new();
    };
    let mut temporaries = Vec::new();
    temporaries.extend(enumeration.as_ref().map(|walked| walked.enumerator));
    if let Some((array, index)) = walk {
        temporaries.extend([*array, *index]);
    }
    for (index, bound) in dimensions {
        temporaries.extend([*index, *bound]);
    }
    temporaries
}

/// Every local a statement or anything in it mentions, closures' bodies
/// aside.
fn used_in_statement(statement: &BoundStatement, into: &mut HashSet<LocalId>) {
    into.extend(declared_by(statement));
    for expression in own_expressions(statement) {
        used_in_expression(expression, into);
    }
    for inner in substatements(statement) {
        used_in_statement(inner, into);
    }
}

fn used_in_expression(expression: &BoundExpression, into: &mut HashSet<LocalId>) {
    match &expression.kind {
        BoundExpressionKind::Local(local) => {
            into.insert(*local);
        }
        BoundExpressionKind::Assignment { target, .. }
        | BoundExpressionKind::CompoundAssignment { target, .. }
        | BoundExpressionKind::Increment { target, .. } => {
            if let BoundExpressionKind::Local(local) = target.kind {
                into.insert(local);
            }
        }
        BoundExpressionKind::SpillSequence { statements, .. } => {
            for statement in statements {
                used_in_statement(statement, into);
            }
        }
        _ => {}
    }
    for child in children(expression) {
        used_in_expression(child, into);
    }
}

/// The expressions a statement evaluates itself, not those of the
/// statements inside it.
fn own_expressions(statement: &BoundStatement) -> Vec<&BoundExpression> {
    match &statement.kind {
        BoundStatementKind::LocalDeclaration { initializer, .. } => initializer.iter().collect(),
        BoundStatementKind::Expression(value) | BoundStatementKind::YieldReturn(value) => {
            vec![value]
        }
        BoundStatementKind::If { condition, .. }
        | BoundStatementKind::While { condition, .. }
        | BoundStatementKind::DoWhile { condition, .. } => vec![condition],
        BoundStatementKind::For {
            condition,
            incrementors,
            ..
        } => condition.iter().chain(incrementors.iter()).collect(),
        BoundStatementKind::ForEach { collection, .. } => vec![collection],
        BoundStatementKind::ConstructorInitializer { arguments, .. } => arguments.iter().collect(),
        BoundStatementKind::Switch {
            governing,
            sections,
        } => {
            let mut expressions = vec![governing];
            for section in sections {
                for label in &section.labels {
                    if let BoundSwitchLabel::Case(case) = label {
                        expressions.extend(case.when.as_ref());
                    }
                }
            }
            expressions
        }
        BoundStatementKind::Try { catches, .. } => catches
            .iter()
            .filter_map(|catch| catch.filter.as_ref())
            .collect(),
        BoundStatementKind::Using { resources, .. } => {
            resources.iter().map(|resource| &resource.value).collect()
        }
        BoundStatementKind::Lock { value, .. } => vec![value],
        BoundStatementKind::Return(value) | BoundStatementKind::Throw(value) => {
            value.iter().collect()
        }
        _ => Vec::new(),
    }
}

/// The statements directly inside a statement.
fn substatements(statement: &BoundStatement) -> Vec<&BoundStatement> {
    match &statement.kind {
        BoundStatementKind::Block(statements) => statements.iter().collect(),
        BoundStatementKind::If {
            consequence,
            alternative,
            ..
        } => std::iter::once(&**consequence)
            .chain(alternative.as_deref())
            .collect(),
        BoundStatementKind::While { body, .. }
        | BoundStatementKind::DoWhile { body, .. }
        | BoundStatementKind::ForEach { body, .. }
        | BoundStatementKind::Using { body, .. }
        | BoundStatementKind::Lock { body, .. } => vec![body],
        BoundStatementKind::For {
            initializers, body, ..
        } => initializers
            .iter()
            .chain(std::iter::once(&**body))
            .collect(),
        BoundStatementKind::Fixed { declarations, body } => declarations
            .iter()
            .chain(std::iter::once(&**body))
            .collect(),
        BoundStatementKind::Switch { sections, .. } => sections
            .iter()
            .flat_map(|section| section.statements.iter())
            .collect(),
        BoundStatementKind::Try {
            body,
            catches,
            finally,
        } => std::iter::once(&**body)
            .chain(catches.iter().map(|catch| &catch.body))
            .chain(finally.as_deref())
            .collect(),
        _ => Vec::new(),
    }
}

/// Whether a `yield return` sits anywhere in a statement.
fn yields(statement: &BoundStatement) -> bool {
    matches!(statement.kind, BoundStatementKind::YieldReturn(_))
        || substatements(statement).into_iter().any(yields)
}

/// What may have been forgotten at a point, local by local: whether a
/// `yield` may have come since it was last written. `None` where nothing
/// reaches.
type State = Option<Vec<bool>>;

/// The union of two states: forgotten where either forgot.
fn join(into: &mut State, other: &State) {
    match (into.as_mut(), other) {
        (_, None) => {}
        (None, Some(other)) => *into = Some(other.clone()),
        (Some(into), Some(other)) => {
            for (at, forgotten) in into.iter_mut().zip(other) {
                *at |= *forgotten;
            }
        }
    }
}

/// Where a `break` and a `continue` of a loop or a `switch` go.
struct Target {
    is_switch: bool,
    breaks: State,
    continues: State,
}

/// The locals read where a `yield` may have come between their write and
/// the read (Roslyn's `IteratorAndAsyncCaptureWalker`): a flow analysis in
/// which every `yield return` forgets every local, and a read of one
/// forgotten is of a local whose value has to outlast the `yield`. A write
/// counts only where it is sure to happen whenever the point it is at is
/// reached, so where it is not sure the local is taken to be forgotten: a
/// field more than Roslyn would have is a name out of step, and a field
/// fewer a value lost.
struct Liveness<'a> {
    body: &'a BoundBody,
    state: State,
    live: HashSet<LocalId>,
    targets: Vec<Target>,
    /// Set where the body does what this does not follow: a `goto`.
    lost: bool,
}

impl<'a> Liveness<'a> {
    fn of(body: &'a BoundBody, statements: &[BoundStatement]) -> Option<HashSet<LocalId>> {
        let mut walk = Liveness {
            body,
            state: Some(vec![false; body.locals.len()]),
            live: HashSet::new(),
            targets: Vec::new(),
            lost: false,
        };
        for statement in statements {
            walk.statement(statement);
        }
        (!walk.lost).then_some(walk.live)
    }

    fn read(&mut self, local: LocalId) {
        if let Some(state) = &self.state
            && state.get(local.0 as usize).copied().unwrap_or(false)
        {
            self.live.insert(local);
        }
    }

    fn write(&mut self, local: LocalId) {
        if let Some(state) = &mut self.state
            && let Some(slot) = state.get_mut(local.0 as usize)
        {
            *slot = false;
        }
    }

    /// A `yield return`: whatever comes next runs in another call of
    /// `MoveNext`.
    fn suspend(&mut self) {
        if let Some(state) = &mut self.state {
            state.fill(true);
        }
    }

    fn by_ref(&self, local: LocalId) -> bool {
        self.body
            .locals
            .get(local.0 as usize)
            .is_some_and(|slot| slot.by_ref)
    }

    /// A loop: `before` evaluated each time round ahead of the body (or
    /// after it, for a `do`), `start` just before the body, `after` just
    /// after it, until what comes back round forgets nothing the entry did
    /// not. Returns where the loop is left.
    fn looping(
        &mut self,
        before: &mut dyn FnMut(&mut Self),
        start: &mut dyn FnMut(&mut Self),
        body: &BoundStatement,
        after: &mut dyn FnMut(&mut Self),
        condition_after: bool,
    ) -> State {
        let mut head = self.state.clone();
        for _ in 0..16 {
            self.state = head.clone();
            if !condition_after {
                before(self);
            }
            let leaving = self.state.clone();
            start(self);
            self.targets.push(Target {
                is_switch: false,
                breaks: None,
                continues: None,
            });
            self.statement(body);
            let target = self.targets.pop().expect("pushed above");
            join(&mut self.state, &target.continues);
            after(self);
            let mut leaving = leaving;
            if condition_after {
                before(self);
                leaving = self.state.clone();
            }
            let mut next = head.clone();
            join(&mut next, &self.state);
            if next == head {
                join(&mut leaving, &target.breaks);
                return leaving;
            }
            head = next;
        }
        self.lost = true;
        None
    }

    fn statement(&mut self, statement: &BoundStatement) {
        match &statement.kind {
            BoundStatementKind::Block(statements) => {
                for inner in statements {
                    self.statement(inner);
                }
            }
            BoundStatementKind::LocalDeclaration { local, initializer } => {
                if let Some(value) = initializer {
                    self.expression(value, true);
                    if !self.by_ref(*local) {
                        self.write(*local);
                    }
                }
            }
            BoundStatementKind::Expression(value) => self.expression(value, true),
            BoundStatementKind::YieldReturn(value) => {
                self.expression(value, true);
                self.suspend();
            }
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                self.expression(condition, true);
                let entry = self.state.clone();
                self.statement(consequence);
                let after = std::mem::replace(&mut self.state, entry);
                if let Some(alternative) = alternative {
                    self.statement(alternative);
                }
                join(&mut self.state, &after);
            }
            BoundStatementKind::While { condition, body } => {
                self.state = self.looping(
                    &mut |this| this.expression(condition, true),
                    &mut |_| {},
                    body,
                    &mut |_| {},
                    false,
                );
            }
            BoundStatementKind::DoWhile { body, condition } => {
                self.state = self.looping(
                    &mut |this| this.expression(condition, true),
                    &mut |_| {},
                    body,
                    &mut |_| {},
                    true,
                );
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                for initializer in initializers {
                    self.statement(initializer);
                }
                let left = self.looping(
                    &mut |this| {
                        if let Some(condition) = condition {
                            this.expression(condition, true);
                        }
                    },
                    &mut |_| {},
                    body,
                    &mut |this| {
                        for incrementor in incrementors {
                            this.expression(incrementor, true);
                        }
                    },
                    false,
                );
                // `for (;;)` is left only by a `break`, which the loop has
                // already counted.
                self.state = left;
            }
            BoundStatementKind::ForEach {
                local,
                collection,
                body,
                enumeration,
                ..
            } => {
                self.expression(collection, true);
                let temporaries = walked_with(statement);
                for temporary in &temporaries {
                    self.write(*temporary);
                }
                // Each time round: `MoveNext`, or the index against the
                // length, and then the element into the variable; after the
                // body, the index goes on.
                let local = *local;
                self.state = self.looping(
                    &mut |this| {
                        for temporary in &temporaries {
                            this.read(*temporary);
                        }
                    },
                    &mut |this| {
                        if !this.by_ref(local) {
                            this.write(local);
                        }
                    },
                    body,
                    &mut |this| {
                        for temporary in &temporaries {
                            this.read(*temporary);
                        }
                    },
                    false,
                );
                // The enumerator is disposed in a `finally`, which a
                // `Dispose` may run after any `yield` of the body.
                if yields(body) {
                    self.live
                        .extend(enumeration.as_ref().map(|walked| walked.enumerator));
                }
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => {
                self.expression(governing, true);
                let entry = self.state.clone();
                self.targets.push(Target {
                    is_switch: true,
                    breaks: None,
                    continues: None,
                });
                // No case may match, and the end is reached from the entry.
                let mut end = entry.clone();
                for section in sections {
                    self.state = entry.clone();
                    for label in &section.labels {
                        if let BoundSwitchLabel::Case(case) = label
                            && let Some(when) = &case.when
                        {
                            self.expression(when, false);
                        }
                    }
                    for inner in &section.statements {
                        self.statement(inner);
                    }
                    join(&mut end, &self.state);
                }
                let target = self.targets.pop().expect("pushed above");
                join(&mut end, &target.breaks);
                // `continue` inside a `switch` belongs to the loop around it.
                if let Some(outer) = self.targets.iter_mut().rev().find(|t| !t.is_switch) {
                    join(&mut outer.continues, &target.continues);
                }
                self.state = end;
            }
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => {
                let entry = self.state.clone();
                self.statement(body);
                let mut end = self.state.clone();
                // A `catch` or a `finally` may start from anywhere in the
                // `try`: what was forgotten anywhere in it.
                let mut anywhere = entry;
                join(&mut anywhere, &end);
                if yields(body)
                    && let Some(state) = &mut anywhere
                {
                    state.fill(true);
                }
                for catch in catches {
                    self.state = anywhere.clone();
                    if let Some(local) = catch.local {
                        self.write(local);
                    }
                    if let Some(filter) = &catch.filter {
                        self.expression(filter, false);
                    }
                    self.statement(&catch.body);
                    join(&mut end, &self.state);
                    join(&mut anywhere, &self.state);
                }
                if let Some(finally) = finally {
                    let reached = end.is_some();
                    self.state = anywhere;
                    self.statement(finally);
                    if !reached {
                        self.state = None;
                    }
                } else {
                    self.state = end;
                }
            }
            BoundStatementKind::Using { resources, body } => {
                for resource in resources {
                    self.expression(&resource.value, true);
                    self.write(resource.local);
                }
                self.statement(body);
                // Disposed in a `finally`, which a `Dispose` may run after
                // any `yield` of the body.
                if yields(body) {
                    self.live
                        .extend(resources.iter().map(|resource| resource.local));
                }
                for resource in resources {
                    self.read(resource.local);
                }
            }
            BoundStatementKind::Lock {
                value,
                held,
                taken,
                body,
            } => {
                self.expression(value, true);
                self.write(*held);
                self.write(*taken);
                self.statement(body);
                if yields(body) {
                    self.live.extend([*held, *taken]);
                }
                self.read(*held);
                self.read(*taken);
            }
            BoundStatementKind::Fixed { declarations, body } => {
                for declaration in declarations {
                    self.statement(declaration);
                }
                self.statement(body);
            }
            BoundStatementKind::ConstructorInitializer { arguments, .. } => {
                for argument in arguments {
                    self.expression(argument, true);
                }
            }
            BoundStatementKind::Return(value) | BoundStatementKind::Throw(value) => {
                if let Some(value) = value {
                    self.expression(value, true);
                }
                self.state = None;
            }
            BoundStatementKind::YieldBreak => self.state = None,
            BoundStatementKind::Break(outward) => {
                let state = self.state.take();
                if let Some(target) = self.targets.iter_mut().rev().nth(*outward) {
                    join(&mut target.breaks, &state);
                }
            }
            BoundStatementKind::Continue(outward) => {
                let state = self.state.take();
                if let Some(target) = self
                    .targets
                    .iter_mut()
                    .rev()
                    .filter(|target| !target.is_switch)
                    .nth(*outward)
                {
                    join(&mut target.continues, &state);
                }
            }
            BoundStatementKind::GotoCase(_)
            | BoundStatementKind::Goto(_)
            | BoundStatementKind::Label(_)
            | BoundStatementKind::Unsupported(_) => self.lost = true,
            BoundStatementKind::Empty => {}
        }
    }

    /// Reads what an expression reads, in order, and writes what it is sure
    /// to write. Whatever is written only where a branch is taken — the
    /// right of `&&`, a conditional's arms — counts as read and not written.
    fn expression(&mut self, expression: &BoundExpression, sure: bool) {
        use BoundExpressionKind as K;
        match &expression.kind {
            K::Local(local) => self.read(*local),
            K::Assignment { target, value } => match &target.kind {
                K::Local(local) if !self.by_ref(*local) => {
                    self.expression(value, sure);
                    if sure {
                        self.write(*local);
                    }
                }
                _ => {
                    self.expression(target, sure);
                    self.expression(value, sure);
                }
            },
            K::CompoundAssignment { target, value, .. } => {
                self.expression(target, sure);
                self.expression(value, sure);
            }
            K::Increment { target, .. } => self.expression(target, sure),
            K::RefArgument {
                kind: RefKind::Out,
                operand,
            } => match &operand.kind {
                K::Local(local) if !self.by_ref(*local) => {
                    if sure {
                        self.write(*local);
                    }
                }
                _ => self.expression(operand, sure),
            },
            K::Binary {
                operator:
                    BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr | BinaryOperator::Coalesce,
                left,
                right,
            } => {
                self.expression(left, sure);
                self.expression(right, false);
            }
            K::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                self.expression(condition, sure);
                self.expression(consequence, false);
                self.expression(alternative, false);
            }
            K::ConditionalAccess { receiver, access } => {
                self.expression(receiver, sure);
                self.expression(access, false);
            }
            K::Switch { .. } => {
                for child in children(expression) {
                    self.expression(child, false);
                }
            }
            K::SpillSequence { statements, value } => {
                for statement in statements {
                    self.statement(statement);
                }
                self.expression(value, sure);
            }
            _ => {
                for child in children(expression) {
                    self.expression(child, sure);
                }
            }
        }
    }
}
