//! Which scopes of a member get a closure class, and where every closure lives.
//!
//! C# makes a captured variable a fresh one each time execution enters the
//! scope that declares it (§12.19.6, §13.9.5): the two lambdas of one loop
//! iteration share their `k`, and the next iteration's see another. So the
//! class a variable lives in is made when its scope is entered — a block, a
//! loop's iteration, a lambda's call — and holds the variables of that scope
//! alone, with a reference to the class of the scope around it.
//!
//! The layout worked out here says, for one member's body, which scopes have
//! such a class (the ones that declare something a closure captures), which
//! class each captured variable is a field of, and which class each lambda
//! and local function is a method of. The member itself is the outermost
//! scope: its class is the member's display class, and everything not owned
//! by a nested scope is its.

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use rustlyn_semantics::{BoundBody, BoundStatement, BoundStatementKind, LocalId, SymbolId};
use rustlyn_text::TextSpan;

use crate::emitter::{Closure, Emitter, loop_scope};

/// A place a closure class may be made: a lambda, a local function, or a
/// scope written in the member.
struct Candidate {
    closure: Closure,
    span: TextSpan,
    /// A part of the span that belongs to the scope around instead: what a
    /// `foreach` is walking, what a `switch` is on. It is evaluated before
    /// the scope is entered.
    exclude: Option<TextSpan>,
}

impl Candidate {
    fn holds(&self, span: TextSpan) -> bool {
        self.span.start() <= span.start()
            && span.end() <= self.span.end()
            && !self
                .exclude
                .is_some_and(|out| out.start() <= span.start() && span.end() <= out.end())
    }
}

/// How a member's closures are laid out in classes.
#[derive(Default, Debug)]
pub(crate) struct ClosureLayout {
    /// The closures whose classes exist, outermost first.
    owners: Vec<Closure>,
    index: HashMap<Closure, usize>,
    /// Each owner's enclosing owner: the class its own refers to.
    parents: Vec<Option<Closure>>,
    /// Each owner's maker: the lambda or local function whose method
    /// enters it, or `None` where the member does.
    makers: Vec<Option<Closure>>,
    locals: HashMap<LocalId, Closure>,
    /// The captured locals and parameters each owner's class has a field
    /// for, in the order a closure first captured them.
    owned: Vec<(Vec<LocalId>, Vec<SymbolId>)>,
    /// The same for the member's own class.
    root: (Vec<LocalId>, Vec<SymbolId>),
    lambda_hosts: Vec<Option<Closure>>,
    function_hosts: Vec<Option<Closure>>,
    /// The lambdas and local functions, by index, that are methods of each
    /// owner's class.
    hosted: Vec<(Vec<usize>, Vec<usize>)>,
}

impl ClosureLayout {
    /// The closures with a class of their own, outermost first.
    pub(crate) fn owners(&self) -> &[Closure] {
        &self.owners
    }

    /// Where a closure's class stands among the member's.
    pub(crate) fn position(&self, closure: Closure) -> Option<usize> {
        self.index.get(&closure).copied()
    }

    /// The owner whose class is the parent of `closure`'s, where there is one;
    /// otherwise the member's class is.
    pub(crate) fn parent(&self, closure: Closure) -> Option<Closure> {
        self.position(closure).and_then(|at| self.parents[at])
    }

    /// The lambda or local function whose method makes `closure`'s class, or
    /// `None` where the member's own does.
    pub(crate) fn maker(&self, closure: Closure) -> Option<Closure> {
        self.position(closure).and_then(|at| self.makers[at])
    }

    /// The owner a captured local is a field of; `None` for the member's own.
    pub(crate) fn local_owner(&self, local: LocalId) -> Option<Closure> {
        self.locals.get(&local).copied()
    }

    /// The captured locals and parameters an owner's class holds.
    pub(crate) fn owned(&self, closure: Closure) -> (&[LocalId], &[SymbolId]) {
        match self.position(closure) {
            Some(at) => (&self.owned[at].0, &self.owned[at].1),
            None => (&[], &[]),
        }
    }

    /// The captured locals and parameters the member's own class holds.
    pub(crate) fn root(&self) -> (&[LocalId], &[SymbolId]) {
        (&self.root.0, &self.root.1)
    }

    /// The owner whose class a lambda is a method of; `None` where the
    /// member's class (or the type) is its home.
    pub(crate) fn lambda_host(&self, index: usize) -> Option<Closure> {
        self.lambda_hosts.get(index).copied().flatten()
    }

    /// The lambdas and local functions that are methods of an owner's class.
    pub(crate) fn hosted(&self, closure: Closure) -> (&[usize], &[usize]) {
        match self.position(closure) {
            Some(at) => (&self.hosted[at].0, &self.hosted[at].1),
            None => (&[], &[]),
        }
    }

    /// The same for a local function.
    pub(crate) fn function_host(&self, index: usize) -> Option<Closure> {
        self.function_hosts.get(index).copied().flatten()
    }
}

/// Where each scope-making statement of a body is, and what it declares.
struct Walk {
    candidates: Vec<Candidate>,
    seen: HashSet<Closure>,
    /// The scope a statement declared a local in; `None` is the member's.
    declared: HashMap<LocalId, Option<Closure>>,
}

impl Walk {
    fn add(&mut self, closure: Closure, span: TextSpan, exclude: Option<TextSpan>) {
        if self.seen.insert(closure) {
            self.candidates.push(Candidate {
                closure,
                span,
                exclude,
            });
        }
    }

    /// `merged`: the statement is the body of the scope that holds it —
    /// a lambda's, a loop's — whose variables are that scope's.
    fn statement(
        &mut self,
        body: &BoundBody,
        statement: &BoundStatement,
        merged: bool,
        current: Option<Closure>,
    ) {
        use BoundStatementKind as S;
        match &statement.kind {
            S::Block(statements) => {
                let inside = if merged || !body.blocks.contains(&statement.span) {
                    current
                } else {
                    let scope = Closure::Scope(statement.span);
                    self.add(scope, statement.span, None);
                    Some(scope)
                };
                for inner in statements {
                    self.statement(body, inner, false, inside);
                }
            }
            S::LocalDeclaration { local, .. } => {
                self.declared.insert(*local, current);
            }
            S::If {
                consequence,
                alternative,
                ..
            } => {
                self.statement(body, consequence, false, current);
                if let Some(alternative) = alternative {
                    self.statement(body, alternative, false, current);
                }
            }
            S::While { body: inner, .. } | S::DoWhile { body: inner, .. } => {
                let scope = Closure::Scope(statement.span);
                self.add(scope, statement.span, None);
                self.statement(body, inner, true, Some(scope));
            }
            S::For {
                initializers,
                body: inner,
                ..
            } => {
                // What the initializers declare is one variable for the
                // whole loop; what the condition, the incrementors and the
                // body declare is one for each time round.
                let outer = Closure::Scope(statement.span);
                self.add(outer, statement.span, None);
                for initializer in initializers {
                    self.statement(body, initializer, false, Some(outer));
                }
                let each = match loop_scope(statement) {
                    Some(span) if span != statement.span => {
                        let scope = Closure::Scope(span);
                        self.add(scope, span, None);
                        scope
                    }
                    _ => outer,
                };
                self.statement(body, inner, true, Some(each));
            }
            S::ForEach {
                local,
                collection,
                body: inner,
                ..
            } => {
                let scope = Closure::Scope(statement.span);
                self.add(scope, statement.span, Some(collection.span));
                self.declared.insert(*local, Some(scope));
                self.statement(body, inner, true, Some(scope));
            }
            // An `await using` is taken apart when the body becomes a state
            // machine, and what it declares lives in the scope around.
            S::Using {
                resources,
                body: inner,
            } if resources.iter().any(|resource| resource.awaited.is_some()) => {
                for resource in resources {
                    self.declared.insert(resource.local, current);
                }
                self.statement(body, inner, false, current);
            }
            S::Using {
                resources,
                body: inner,
            } => {
                let span = using_scope(statement);
                let scope = Closure::Scope(span);
                self.add(scope, span, None);
                for resource in resources {
                    self.declared.insert(resource.local, Some(scope));
                }
                self.statement(body, inner, true, Some(scope));
            }
            S::Lock { body: inner, .. } => self.statement(body, inner, false, current),
            S::Fixed {
                declarations,
                body: inner,
            } => {
                for declaration in declarations {
                    self.statement(body, declaration, false, current);
                }
                self.statement(body, inner, false, current);
            }
            S::Switch {
                governing,
                sections,
            } => {
                // The sections share one declaration space (§13.8.3).
                let scope = Closure::Scope(statement.span);
                self.add(scope, statement.span, Some(governing.span));
                for section in sections {
                    for inner in &section.statements {
                        self.statement(body, inner, false, Some(scope));
                    }
                }
            }
            S::Try {
                body: inner,
                catches,
                finally,
            } => {
                self.statement(body, inner, false, current);
                for catch in catches {
                    // A handler that awaits is moved out of its `catch`
                    // when the body becomes a state machine, and its
                    // variable with it: it lives in the scope around.
                    if crate::async_machine::statement_awaits(&catch.body) {
                        if let Some(local) = catch.local {
                            self.declared.insert(local, current);
                        }
                        self.statement(body, &catch.body, false, current);
                        continue;
                    }
                    let span = catch_scope(body, catch);
                    let scope = Closure::Scope(span);
                    self.add(scope, span, None);
                    if let Some(local) = catch.local {
                        self.declared.insert(local, Some(scope));
                    }
                    self.statement(body, &catch.body, true, Some(scope));
                }
                if let Some(finally) = finally {
                    self.statement(body, finally, false, current);
                }
            }
            _ => {}
        }
    }
}

/// What a `using` holds: the statement and the block it governs, which for
/// `using var x = e;` is everything after it up to the end of the block —
/// statements the binder gathered under it, whose own spans lie beyond the
/// declaration's.
pub(crate) fn using_scope(statement: &BoundStatement) -> TextSpan {
    fn end(statement: &BoundStatement) -> u32 {
        let inner = match &statement.kind {
            BoundStatementKind::Using { body, .. } => end(body),
            BoundStatementKind::Block(statements) => statements.last().map_or(0, end),
            _ => 0,
        };
        statement.span.end().max(inner)
    }
    TextSpan::new(
        statement.span.start(),
        end(statement) - statement.span.start(),
    )
}

/// What a `catch` clause's variable and filter live in: from the
/// exception's name, or the filter, or the body, to the end of the body.
pub(crate) fn catch_scope(body: &BoundBody, catch: &rustlyn_semantics::BoundCatch) -> TextSpan {
    let start = catch
        .local
        .map(|local| body.locals[local.0 as usize].span.start())
        .into_iter()
        .chain(catch.filter.iter().map(|filter| filter.span.start()))
        .chain(std::iter::once(catch.body.span.start()))
        .min()
        .unwrap_or(catch.body.span.start());
    TextSpan::new(start, catch.body.span.end().saturating_sub(start))
}

impl Emitter<'_> {
    /// How a member's closures are laid out, worked out once.
    pub(crate) fn closure_layout(&mut self, owner: SymbolId) -> Arc<ClosureLayout> {
        if let Some(layout) = self.layouts.get(&owner) {
            return layout.clone();
        }
        let layout = Arc::new(match self.body_of(owner) {
            Some(body) => self.build_layout(&body),
            None => ClosureLayout::default(),
        });
        self.layouts.insert(owner, layout.clone());
        layout
    }

    /// The closures with a class of their own, outermost first.
    pub(crate) fn nested_display_owners(&mut self, owner: SymbolId) -> Vec<Closure> {
        self.closure_layout(owner).owners().to_vec()
    }

    fn build_layout(&self, body: &BoundBody) -> ClosureLayout {
        // With no closure there is nothing to capture, and no scope has a
        // class.
        if body.lambdas.is_empty() && body.local_functions.is_empty() {
            return ClosureLayout::default();
        }
        let symbols = self.compilation.symbols();
        let mut walk = Walk {
            candidates: Vec::new(),
            seen: HashSet::new(),
            declared: HashMap::new(),
        };
        for (index, lambda) in body.lambdas.iter().enumerate() {
            walk.add(Closure::Lambda(index), lambda.span, None);
        }
        for (index, function) in body.local_functions.iter().enumerate() {
            walk.add(Closure::Function(index), function.span, None);
        }
        for statement in &body.statements {
            walk.statement(body, statement, false, None);
        }
        for (index, lambda) in body.lambdas.iter().enumerate() {
            for parameter in &lambda.parameters {
                walk.declared
                    .insert(*parameter, Some(Closure::Lambda(index)));
            }
            walk.statement(body, &lambda.body, true, Some(Closure::Lambda(index)));
        }
        for (index, function) in body.local_functions.iter().enumerate() {
            walk.statement(body, &function.body, true, Some(Closure::Function(index)));
        }
        let Walk {
            candidates,
            declared,
            ..
        } = walk;

        // Everything a closure captured, once.
        let mut captured: Vec<LocalId> = Vec::new();
        let mut seen_locals: HashSet<LocalId> = HashSet::new();
        let mut captured_parameters: Vec<SymbolId> = Vec::new();
        let mut seen_parameters: HashSet<SymbolId> = HashSet::new();
        for (locals, parameters) in body
            .lambdas
            .iter()
            .map(|lambda| (&lambda.captured, &lambda.captured_parameters))
            .chain(
                body.local_functions
                    .iter()
                    .map(|function| (&function.captured, &function.captured_parameters)),
            )
        {
            for local in locals {
                if seen_locals.insert(*local) {
                    captured.push(*local);
                }
            }
            for parameter in parameters {
                if seen_parameters.insert(*parameter) {
                    captured_parameters.push(*parameter);
                }
            }
        }

        // The sweep: candidates and the points to place, in text order with
        // the larger first, so that the scopes around a position are the
        // ones still open when it is reached.
        enum Item {
            Candidate(usize),
            Local(LocalId),
        }
        let mut items: Vec<(TextSpan, bool, Item)> = Vec::new();
        for (at, candidate) in candidates.iter().enumerate() {
            items.push((candidate.span, false, Item::Candidate(at)));
        }
        for local in &captured {
            if !declared.contains_key(local) {
                let span = body.locals[local.0 as usize].span;
                items.push((span, true, Item::Local(*local)));
            }
        }
        items.sort_by_key(|(span, point, _)| (span.start(), Reverse(span.length()), *point));
        let mut open: Vec<usize> = Vec::new();
        let mut parent_of: Vec<Option<usize>> = vec![None; candidates.len()];
        let mut placed: HashMap<LocalId, Option<Closure>> = HashMap::new();
        for (span, _, item) in &items {
            while let Some(top) = open.last() {
                let top = &candidates[*top];
                if top.span.start() <= span.start() && span.end() <= top.span.end() {
                    break;
                }
                open.pop();
            }
            let holder = open
                .iter()
                .rev()
                .copied()
                .find(|at| candidates[*at].holds(*span));
            match item {
                Item::Candidate(at) => {
                    parent_of[*at] = holder;
                    open.push(*at);
                }
                Item::Local(local) => {
                    placed.insert(*local, holder.map(|at| candidates[at].closure));
                }
            }
        }
        let at_of: HashMap<Closure, usize> = candidates
            .iter()
            .enumerate()
            .map(|(at, candidate)| (candidate.closure, at))
            .collect();

        // Which closures own a captured variable.
        let mut classed: HashSet<Closure> = HashSet::new();
        let mut locals: HashMap<LocalId, Closure> = HashMap::new();
        let mut root_locals: Vec<LocalId> = Vec::new();
        for local in &captured {
            let owner = match declared.get(local) {
                Some(owner) => *owner,
                None => placed.get(local).copied().flatten(),
            };
            match owner {
                Some(owner) => {
                    classed.insert(owner);
                    locals.insert(*local, owner);
                }
                None => root_locals.push(*local),
            }
        }
        let functions: HashMap<SymbolId, usize> = body
            .local_functions
            .iter()
            .enumerate()
            .map(|(index, function)| (function.symbol, index))
            .collect();
        let mut parameters: HashMap<SymbolId, Closure> = HashMap::new();
        let mut root_parameters: Vec<SymbolId> = Vec::new();
        for parameter in &captured_parameters {
            let container = symbols.get(*parameter).container;
            match container.and_then(|container| functions.get(&container)) {
                Some(index) => {
                    let owner = Closure::Function(*index);
                    classed.insert(owner);
                    parameters.insert(*parameter, owner);
                }
                None => root_parameters.push(*parameter),
            }
        }

        // The nearest owner strictly around a candidate.
        let host = |at: usize| -> Option<Closure> {
            let mut current = parent_of[at];
            while let Some(up) = current {
                if classed.contains(&candidates[up].closure) {
                    return Some(candidates[up].closure);
                }
                current = parent_of[up];
            }
            None
        };
        let maker = |at: usize| -> Option<Closure> {
            let mut current = Some(at);
            while let Some(up) = current {
                if matches!(
                    candidates[up].closure,
                    Closure::Lambda(_) | Closure::Function(_)
                ) {
                    return Some(candidates[up].closure);
                }
                current = parent_of[up];
            }
            None
        };

        let mut owners: Vec<Closure> = classed.iter().copied().collect();
        owners.sort_by_key(|closure| {
            let span = candidates[at_of[closure]].span;
            (span.start(), Reverse(span.length()))
        });
        let mut owned: Vec<(Vec<LocalId>, Vec<SymbolId>)> = vec![Default::default(); owners.len()];
        let position: HashMap<Closure, usize> = owners
            .iter()
            .enumerate()
            .map(|(at, closure)| (*closure, at))
            .collect();
        for local in &captured {
            if let Some(at) = locals.get(local).and_then(|owner| position.get(owner)) {
                owned[*at].0.push(*local);
            }
        }
        for parameter in &captured_parameters {
            if let Some(at) = parameters
                .get(parameter)
                .and_then(|owner| position.get(owner))
            {
                owned[*at].1.push(*parameter);
            }
        }
        let owners_len = owners.len();
        let mut layout = ClosureLayout {
            index: owners
                .iter()
                .enumerate()
                .map(|(at, closure)| (*closure, at))
                .collect(),
            parents: owners.iter().map(|closure| host(at_of[closure])).collect(),
            makers: owners.iter().map(|closure| maker(at_of[closure])).collect(),
            owners,
            locals,
            owned,
            root: (root_locals, root_parameters),
            lambda_hosts: Vec::new(),
            function_hosts: Vec::new(),
            hosted: vec![Default::default(); owners_len],
        };
        layout.lambda_hosts = (0..body.lambdas.len())
            .map(|index| host(at_of[&Closure::Lambda(index)]))
            .collect();
        layout.function_hosts = (0..body.local_functions.len())
            .map(|index| host(at_of[&Closure::Function(index)]))
            .collect();
        for (index, host) in layout.lambda_hosts.clone().into_iter().enumerate() {
            if let Some(at) = host.and_then(|host| layout.index.get(&host).copied()) {
                layout.hosted[at].0.push(index);
            }
        }
        for (index, host) in layout.function_hosts.clone().into_iter().enumerate() {
            if let Some(at) = host.and_then(|host| layout.index.get(&host).copied()) {
                layout.hosted[at].1.push(index);
            }
        }
        layout
    }
}
