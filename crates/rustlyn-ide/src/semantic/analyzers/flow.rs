//! Values nobody reads and code nobody reaches.
//!
//! Roslyn answers both with its control-flow graph. This answers them with
//! the order of the code and the shape of its blocks, which is exact for
//! straight-line code and conservative everywhere else: a write followed by
//! another in the same block with no read between is dead, and so is one
//! with no read after it and no loop around it that reads. A body with a
//! `goto`, or with a local captured by a lambda or passed by `ref`, is not
//! second-guessed at all.

use std::collections::{HashMap, HashSet};

use rustlyn_diagnostics::Severity;
use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundExpression, BoundExpressionKind as E, BoundStatement,
    BoundStatementKind as S, ConstantValue, LocalId, RefKind, SpecialType, Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::walk::{expression_children, pattern_expressions, statement_children};
use super::super::{Resolved, View};
use super::{AnalyzerDiagnostic, Facts, is_discard_name};

/// How a local came to be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Declared {
    /// `int x;` or `int x = 1;`.
    Statement { initialized: bool },
    /// `out var x`.
    Out,
    /// `catch (Exception e)`.
    Catch,
    /// A loop variable, a `using` resource, a pattern's name: never
    /// reported.
    Other,
}

#[derive(Clone, Debug)]
enum Kind {
    Read,
    Write {
        /// Where the statement that does nothing but this write is: which
        /// statement list, and where in it. Such a write is followed, in the
        /// same list, only by what comes after it.
        slot: Option<(usize, usize)>,
        /// Whether the value is a constant: no side effects, and what makes
        /// CS0219 rather than IDE0059.
        constant: bool,
        /// What to point at.
        target: TextSpan,
    },
}

#[derive(Clone, Debug)]
struct Event {
    local: LocalId,
    /// Where it happens, in the order things happen: a read of the value
    /// being assigned comes before the assignment's write.
    position: u32,
    kind: Kind,
    /// The loops — and lambdas and local functions, which can run again —
    /// around it.
    loops: Vec<TextSpan>,
    /// Inside a `try` block, where an exception can carry the old value to a
    /// `catch`.
    in_try: bool,
}

struct Collector<'b> {
    body: &'b BoundBody,
    view: &'b View<'b>,
    events: Vec<Event>,
    declared: HashMap<LocalId, Declared>,
    escaped: HashSet<LocalId>,
    loops: Vec<TextSpan>,
    tries: usize,
    lists: usize,
    /// A `goto` or a label: the order of the code is not the order it runs.
    jumps: bool,
    /// Something the binder did not model: what it reads is not in the tree.
    incomplete: bool,
}

impl<'b> Collector<'b> {
    fn event(&mut self, local: LocalId, position: u32, kind: Kind) {
        self.events.push(Event {
            local,
            position,
            kind,
            loops: self.loops.clone(),
            in_try: self.tries > 0,
        });
    }

    /// Whether writing `value` to `local` is a write the compiler does not
    /// count as a use (CS0219): where a local that holds a reference, other
    /// than a string, only `null` is; for any other, a constant, a `default`,
    /// a tuple literal, a `new` of a struct with no arguments, through the
    /// conversions that keep what is inside — not a boxing into a reference
    /// type or a user's conversion.
    fn is_constant(&self, local: LocalId, value: &BoundExpression) -> bool {
        let Some(found) = self.body.locals.get(local.0 as usize) else {
            return false;
        };
        let symbols = self.view.compilation().symbols();
        let string = self.view.compilation().special_type(SpecialType::String);
        let is_string =
            |ty: &Type| matches!(ty, Type::Named { symbol, .. } if Some(*symbol) == string);
        if found.ty.is_reference_type(symbols) && !is_string(&found.ty) {
            return self.is_null(value);
        }
        self.writes_no_use(value, &is_string)
    }

    /// Whether the text at `value` is an interpolated string.
    fn is_interpolated(&self, value: &BoundExpression) -> bool {
        self.view
            .root
            .find_token(value.span.start())
            .is_some_and(|token| token.text().starts_with(['$', '@']) && token.text().contains('$'))
    }

    /// Whether `value`, a `new`, was written with an initializer, even an
    /// empty one.
    fn has_initializer(&self, value: &BoundExpression) -> bool {
        self.view
            .root
            .find_node(value.span)
            .is_some_and(|node| node.text().trim_end().ends_with('}'))
    }

    /// `null`, however it was written and converted.
    fn is_null(&self, value: &BoundExpression) -> bool {
        match &value.kind {
            E::Literal(ConstantValue::Null) => true,
            E::Default(ty) => ty.is_reference_type(self.view.compilation().symbols()),
            E::Conversion { operand, .. } => self.is_null(operand),
            _ => matches!(
                self.view.model.binder().folded(value),
                Some(ConstantValue::Null)
            ),
        }
    }

    fn writes_no_use(&self, value: &BoundExpression, is_string: &dyn Fn(&Type) -> bool) -> bool {
        let symbols = self.view.compilation().symbols();
        match &value.kind {
            E::Default(_) | E::TupleCreation(_) => true,
            // Text with holes is built at run time, and so is what a cast
            // that can fail gives.
            E::InterpolatedString(_) | E::TryCast { .. } => false,
            // `new DateTime()` and `new int?()` are the default value;
            // `new MyS { }` and `new DateTime(1)` are not. A decimal
            // literal is a call of a constructor, and a constant.
            E::ObjectCreation {
                constructor,
                arguments,
                ..
            } => {
                if self.has_initializer(value) {
                    return false;
                }
                let default_value = arguments.is_empty()
                    && matches!(&value.ty, Type::Named { symbol, .. }
                    if matches!(
                        symbols.get(*symbol).type_kind(),
                        Some(TypeKind::Struct | TypeKind::RecordStruct)
                    ))
                    && match constructor {
                        None => true,
                        // The one the compiler makes for a struct of the
                        // program's own: it has no declaration of its own.
                        Some(constructor) => {
                            let found = symbols.get(*constructor);
                            found
                                .as_method()
                                .is_some_and(|method| method.parameters.is_empty())
                                && found.locations.iter().all(|location| {
                                    location.tree == self.view.tree
                                        && self.view.root.find_node(location.span).is_none_or(
                                            |node| {
                                                node.kind() != SyntaxKind::ConstructorDeclaration
                                            },
                                        )
                                })
                        }
                    };
                // A decimal literal is a call of a constructor.
                let decimal = matches!(&value.ty, Type::Named { symbol, .. }
                        if symbols.qualified_name(*symbol) == "System.Decimal")
                    && !arguments.is_empty()
                    && arguments
                        .iter()
                        .all(|argument| self.view.model.binder().folded(argument).is_some());
                default_value || decimal || self.view.model.binder().folded(value).is_some()
            }
            // `$"a"` has no holes and binds as the text, and is still built
            // as an interpolated string.
            E::Literal(ConstantValue::String(_)) if self.is_interpolated(value) => false,
            E::Conversion { operand, .. } => self.writes_no_use(operand, is_string),
            // The framework's own conversion of a string constant to a
            // span; a conversion a program declares is a use of the value.
            E::Call {
                method, arguments, ..
            } if symbols.get(*method).name == "op_Implicit"
                && symbols.get(*method).locations.is_empty()
                && matches!(&value.ty, Type::Named { symbol, .. }
                if matches!(
                    symbols.qualified_name(*symbol).as_str(),
                    "System.ReadOnlySpan`1" | "System.Span`1"
                ))
                && symbols.get(*method).container.is_some_and(|container| {
                    matches!(
                        symbols.qualified_name(container).as_str(),
                        "System.String" | "System.ReadOnlySpan`1" | "System.Span`1"
                    )
                }) =>
            {
                matches!(arguments.as_slice(), [argument]
                    if !self.is_null(argument) && self.writes_no_use(argument, is_string))
            }
            // Joining text is constant only where every piece is text.
            E::Binary {
                operator: BinaryOperator::Add,
                left,
                right,
            } if is_string(&value.ty) => {
                let text = |side: &BoundExpression| {
                    (is_string(&side.ty) || matches!(side.kind, E::Literal(ConstantValue::Null)))
                        && self.writes_no_use(side, is_string)
                };
                text(left) && text(right)
            }
            _ => self.view.model.binder().folded(value).is_some(),
        }
    }

    /// Whether a local is a `const`: its uses are its value, not reads.
    fn is_constant_local(&self, local: LocalId) -> bool {
        let Some(found) = self.body.locals.get(local.0 as usize) else {
            return false;
        };
        self.view
            .root
            .find_token(found.span.start())
            .and_then(|token| token.parent().ancestors().nth(1))
            .is_some_and(|statement| {
                statement.kind() == SyntaxKind::LocalDeclarationStatement
                    && statement
                        .child_token_of_kind(SyntaxKind::ConstKeyword)
                        .is_some()
            })
    }

    fn statements(&mut self, list: &'b [BoundStatement]) {
        self.lists += 1;
        let id = self.lists;
        for (index, statement) in list.iter().enumerate() {
            self.statement(statement, Some((id, index)));
        }
    }

    fn statement(&mut self, statement: &'b BoundStatement, slot: Option<(usize, usize)>) {
        match &statement.kind {
            S::Block(list) => self.statements(list),
            S::LocalDeclaration { local, initializer } => {
                let how = if self.is_constant_local(*local) {
                    Declared::Other
                } else {
                    Declared::Statement {
                        initialized: initializer.is_some(),
                    }
                };
                self.declared.entry(*local).or_insert(how);
                if let Some(value) = initializer {
                    self.expression(value);
                    let constant = self.is_constant(*local, value);
                    let target = self
                        .body
                        .locals
                        .get(local.0 as usize)
                        .map_or(statement.span, |found| found.span);
                    self.event(
                        *local,
                        statement.span.end(),
                        Kind::Write {
                            slot,
                            constant,
                            target,
                        },
                    );
                }
            }
            S::Expression(expression) => match &expression.kind {
                E::Assignment { target, value } if matches!(target.kind, E::Local(_)) => {
                    let E::Local(local) = target.kind else {
                        return;
                    };
                    self.expression(value);
                    let constant = self.is_constant(local, value);
                    self.event(
                        local,
                        expression.span.end(),
                        Kind::Write {
                            slot,
                            constant,
                            target: target.span,
                        },
                    );
                }
                _ => self.expression(expression),
            },
            S::While { .. } | S::DoWhile { .. } | S::For { .. } | S::ForEach { .. } => {
                if let S::ForEach { local, .. } = &statement.kind {
                    self.declared.insert(*local, Declared::Other);
                }
                self.loops.push(statement.span);
                self.children(statement);
                self.loops.pop();
            }
            S::Switch {
                governing,
                sections,
            } => {
                self.expression(governing);
                for section in sections {
                    for label in &section.labels {
                        if let rustlyn_semantics::BoundSwitchLabel::Case(case) = label {
                            let mut values = Vec::new();
                            pattern_expressions(&case.pattern, &mut values);
                            for value in values {
                                self.expression(value);
                            }
                            if let Some(when) = &case.when {
                                self.expression(when);
                            }
                        }
                    }
                    self.statements(&section.statements);
                }
            }
            S::Try {
                body,
                catches,
                finally,
            } => {
                self.tries += 1;
                self.statement(body, None);
                self.tries -= 1;
                for catch in catches {
                    if let Some(local) = catch.local {
                        self.declared.insert(local, Declared::Catch);
                    }
                    if let Some(filter) = &catch.filter {
                        self.expression(filter);
                    }
                    self.statement(&catch.body, None);
                }
                if let Some(finally) = finally {
                    self.statement(finally, None);
                }
            }
            S::Using { resources, body } => {
                for resource in resources {
                    self.declared.insert(resource.local, Declared::Other);
                    self.expression(&resource.value);
                }
                self.statement(body, None);
            }
            S::Goto(_) | S::Label(_) | S::GotoCase(_) => self.jumps = true,
            S::Unsupported(_) => self.incomplete = true,
            _ => self.children(statement),
        }
    }

    fn children(&mut self, statement: &'b BoundStatement) {
        let (statements, expressions) = statement_children(statement);
        let before_body = !matches!(statement.kind, S::DoWhile { .. });
        if before_body {
            for expression in &expressions {
                self.expression(expression);
            }
        }
        for child in statements {
            self.statement(child, None);
        }
        if !before_body {
            for expression in &expressions {
                self.expression(expression);
            }
        }
    }

    fn expression(&mut self, expression: &'b BoundExpression) {
        match &expression.kind {
            E::Local(local) => self.event(*local, expression.span.start(), Kind::Read),
            E::Assignment { target, value } => {
                if let E::Local(local) = target.kind {
                    self.expression(value);
                    let constant = self.is_constant(local, value);
                    self.event(
                        local,
                        expression.span.end(),
                        Kind::Write {
                            slot: None,
                            constant,
                            target: target.span,
                        },
                    );
                } else {
                    self.expression(target);
                    self.expression(value);
                }
            }
            E::RefArgument { kind, operand } => match (&operand.kind, kind) {
                (E::Local(local), RefKind::Out) => {
                    let declared_here = self
                        .body
                        .locals
                        .get(local.0 as usize)
                        .is_some_and(|found| operand.span.contains_span(found.span));
                    if declared_here {
                        self.declared.insert(*local, Declared::Out);
                    }
                    self.event(
                        *local,
                        operand.span.end(),
                        Kind::Write {
                            slot: None,
                            constant: false,
                            target: operand.span,
                        },
                    );
                }
                (E::Local(local), _) => {
                    self.escaped.insert(*local);
                    self.event(*local, operand.span.start(), Kind::Read);
                }
                _ => self.expression(operand),
            },
            E::AddressOf { operand } => {
                if let E::Local(local) = operand.kind {
                    self.escaped.insert(local);
                }
                self.expression(operand);
            }
            E::Lambda(index) => {
                let Some(lambda) = self.body.lambdas.get(*index) else {
                    return;
                };
                self.escaped.extend(lambda.captured.iter().copied());
                self.loops.push(expression.span);
                self.statement(&lambda.body, None);
                self.loops.pop();
            }
            E::Unsupported(_) => self.incomplete = true,
            _ => {
                for child in expression_children(expression) {
                    self.expression(child);
                }
            }
        }
    }
}

/// IDE0059, CS0168 and CS0219: locals and values nobody reads.
pub(super) fn unused_values(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    for body in facts.bodies.iter().filter(|body| !body.broken) {
        let bound = &body.bound;
        let mut reported = Vec::new();
        {
            let shared: &View<'_> = view;
            let mut collector = Collector {
                body: bound,
                view: shared,
                events: Vec::new(),
                declared: HashMap::new(),
                escaped: HashSet::new(),
                loops: Vec::new(),
                tries: 0,
                lists: 0,
                jumps: false,
                incomplete: false,
            };
            collector.statements(&bound.statements);
            for function in &bound.local_functions {
                collector.escaped.extend(function.captured.iter().copied());
                collector.loops.push(function.body.span);
                collector.statement(&function.body, None);
                collector.loops.pop();
            }
            if collector.incomplete {
                continue;
            }
            report_locals(bound, &collector, &mut reported);
        }
        // What the bound tree says nobody reads, checked against the names
        // written: a constant the binder folded into its uses, or a read it
        // did not keep, is still a read. The identifiers of the body are
        // gathered by name when the first report needs them: a body with a
        // thousand locals nobody reads is otherwise read through a thousand
        // times.
        let mut written: Option<HashMap<String, Vec<rustlyn_syntax::SyntaxToken>>> = None;
        for report in reported {
            if report.unread {
                let names = written.get_or_insert_with(|| identifiers_by_name(&body.owner));
                if read_in_syntax(view, names, report.declared, &report.name) {
                    continue;
                }
            }
            found.push(report.diagnostic);
        }
    }
}

/// A diagnostic about a local, before it is checked against the syntax.
struct Report {
    /// Where the local is declared.
    declared: TextSpan,
    name: String,
    /// Whether it was reported because nothing reads the local at all.
    unread: bool,
    diagnostic: AnalyzerDiagnostic,
}

/// The identifier tokens of `owner`, by what they say, in order.
fn identifiers_by_name(owner: &SyntaxNode) -> HashMap<String, Vec<rustlyn_syntax::SyntaxToken>> {
    let mut names: HashMap<String, Vec<rustlyn_syntax::SyntaxToken>> = HashMap::new();
    for token in owner.descendant_tokens() {
        if token.kind() == SyntaxKind::IdentifierToken {
            names
                .entry(token.value_text().to_string())
                .or_default()
                .push(token);
        }
    }
    names
}

/// Whether a name among `names`, the identifiers of a body, other than the
/// declaration reads the local declared at `declared`.
fn read_in_syntax(
    view: &mut View<'_>,
    names: &HashMap<String, Vec<rustlyn_syntax::SyntaxToken>>,
    declared: TextSpan,
    name: &str,
) -> bool {
    names.get(name).is_some_and(|tokens| {
        tokens.iter().any(|token| {
            token.span() != declared
                && matches!(view.resolve(token), Some(Resolved::Local { span, .. }) if span == declared)
                && super::access_of(token) != super::Access::Write
        })
    })
}

fn report_locals(body: &BoundBody, collector: &Collector<'_>, found: &mut Vec<Report>) {
    let mut by_local: HashMap<LocalId, Vec<&Event>> = HashMap::new();
    for event in &collector.events {
        by_local.entry(event.local).or_default().push(event);
    }
    let mut declared: Vec<(&LocalId, &Declared)> = collector.declared.iter().collect();
    declared.sort_by_key(|(local, _)| local.0);
    for (&local, &how) in declared {
        let Some(symbol) = body.locals.get(local.0 as usize) else {
            continue;
        };
        if symbol.name.is_empty()
            || symbol.name.starts_with('<')
            || is_discard_name(&symbol.name)
            || symbol.by_ref
            || collector.escaped.contains(&local)
        {
            continue;
        }
        let mut events: Vec<&Event> = by_local.remove(&local).unwrap_or_default();
        events.sort_by_key(|event| event.position);
        let reads = events
            .iter()
            .filter(|event| matches!(event.kind, Kind::Read))
            .count();
        let name = &symbol.name;
        match how {
            Declared::Statement { initialized: false } | Declared::Catch if events.is_empty() => {
                found.push(Report {
                    declared: symbol.span,
                    name: name.clone(),
                    unread: true,
                    diagnostic: AnalyzerDiagnostic::new(
                        "CS0168",
                        Severity::Warning,
                        symbol.span,
                        format!("The variable '{name}' is declared but never used"),
                    ),
                });
                continue;
            }
            Declared::Statement { .. }
                if reads == 0
                    && !events.is_empty()
                    && events
                        .iter()
                        .all(|event| matches!(event.kind, Kind::Write { constant: true, .. })) =>
            {
                found.push(Report {
                    declared: symbol.span,
                    name: name.clone(),
                    unread: true,
                    diagnostic: AnalyzerDiagnostic::new(
                        "CS0219",
                        Severity::Warning,
                        symbol.span,
                        format!("The variable '{name}' is assigned but its value is never used"),
                    ),
                });
                continue;
            }
            Declared::Statement { .. } | Declared::Out => {}
            Declared::Catch | Declared::Other => continue,
        }
        if collector.jumps {
            continue;
        }
        for (index, event) in events.iter().enumerate() {
            let Kind::Write { slot, target, .. } = &event.kind else {
                continue;
            };
            let overwritten = !event.in_try
                && slot.is_some_and(|(list, at)| {
                    events.get(index + 1).is_some_and(|next| {
                        matches!(&next.kind, Kind::Write { slot: Some((other, later)), .. }
                            if *other == list && *later > at)
                    })
                });
            let never_read = !events.iter().any(|other| {
                matches!(other.kind, Kind::Read)
                    && (other.position > event.position
                        || event
                            .loops
                            .iter()
                            .any(|around| around.contains(other.position)))
            });
            if overwritten || never_read {
                // `out var x` is pointed at by its name.
                let span = if target.contains_span(symbol.span) {
                    symbol.span
                } else {
                    *target
                };
                found.push(Report {
                    declared: symbol.span,
                    name: name.clone(),
                    unread: reads == 0,
                    diagnostic: AnalyzerDiagnostic::new(
                        "IDE0059",
                        Severity::Info,
                        span,
                        format!("Unnecessary assignment of a value to '{name}'"),
                    )
                    .unnecessary(),
                });
            }
        }
    }
}

// MARK: - unreachable code

/// CS0162 and IDE0035: statements after a `return`, `throw`, `break`,
/// `continue` or `goto` in the same block, up to the next label.
pub(super) fn unreachable_code(
    view: &mut View<'_>,
    _: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let mut reported: Vec<TextSpan> = Vec::new();
    for list in view
        .root
        .descendants()
        .filter(|node| matches!(node.kind(), SyntaxKind::Block | SyntaxKind::SwitchSection))
    {
        if reported.iter().any(|span| span.contains_span(list.span())) {
            continue;
        }
        let statements: Vec<SyntaxNode> = list
            .children()
            .filter(|child| child.kind().is_statement_node())
            .collect();
        let mut reachable = true;
        let mut run: Vec<SyntaxNode> = Vec::new();
        let mut runs: Vec<Vec<SyntaxNode>> = Vec::new();
        for statement in statements {
            if statement.kind() == SyntaxKind::LabeledStatement {
                reachable = true;
            }
            if !reachable && statement.kind() != SyntaxKind::LocalFunctionStatement {
                run.push(statement.clone());
                continue;
            }
            if !run.is_empty() {
                runs.push(std::mem::take(&mut run));
            }
            if reachable && !completes(&statement) {
                reachable = false;
            }
        }
        if !run.is_empty() {
            runs.push(run);
        }
        for run in runs {
            let (Some(first), Some(last)) = (run.first(), run.last()) else {
                continue;
            };
            let whole = TextSpan::from_bounds(first.span().start(), last.span().end());
            reported.push(whole);
            found.push(AnalyzerDiagnostic::new(
                "CS0162",
                Severity::Warning,
                first.span(),
                "Unreachable code detected",
            ));
            found.push(
                AnalyzerDiagnostic::new(
                    "IDE0035",
                    Severity::Hidden,
                    whole,
                    "Unreachable code detected",
                )
                .unnecessary(),
            );
        }
    }
}

/// Whether control can reach the end of a statement.
fn completes(statement: &SyntaxNode) -> bool {
    match statement.kind() {
        SyntaxKind::ReturnStatement
        | SyntaxKind::ThrowStatement
        | SyntaxKind::BreakStatement
        | SyntaxKind::ContinueStatement
        | SyntaxKind::GotoStatement
        | SyntaxKind::GotoCaseStatement
        | SyntaxKind::GotoDefaultStatement
        | SyntaxKind::YieldBreakStatement => false,
        SyntaxKind::Block => {
            let mut reachable = true;
            for child in statement
                .children()
                .filter(|child| child.kind().is_statement_node())
            {
                if child.kind() == SyntaxKind::LabeledStatement {
                    reachable = true;
                }
                if reachable && !completes(&child) {
                    reachable = false;
                }
            }
            reachable
        }
        SyntaxKind::IfStatement => {
            let consequence = statement
                .children()
                .find(|child| child.kind().is_statement_node());
            let alternative = statement
                .child_of_kind(SyntaxKind::ElseClause)
                .and_then(|clause| {
                    clause
                        .children()
                        .find(|child| child.kind().is_statement_node())
                });
            match (consequence, alternative) {
                (Some(consequence), Some(alternative)) => {
                    completes(&consequence) || completes(&alternative)
                }
                _ => true,
            }
        }
        SyntaxKind::WhileStatement | SyntaxKind::DoStatement | SyntaxKind::ForStatement => {
            !loops_forever(statement) || breaks_out(statement)
        }
        SyntaxKind::TryStatement => {
            if let Some(finally) = statement
                .child_of_kind(SyntaxKind::FinallyClause)
                .and_then(|clause| clause.child_of_kind(SyntaxKind::Block))
                && !completes(&finally)
            {
                return false;
            }
            let body = statement.child_of_kind(SyntaxKind::Block);
            body.is_none_or(|body| completes(&body))
                || statement
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::CatchClause)
                    .any(|catch| {
                        catch
                            .child_of_kind(SyntaxKind::Block)
                            .is_none_or(|block| completes(&block))
                    })
        }
        SyntaxKind::LabeledStatement
        | SyntaxKind::CheckedStatement
        | SyntaxKind::UncheckedStatement
        | SyntaxKind::UnsafeStatement
        | SyntaxKind::LockStatement
        | SyntaxKind::UsingStatement
        | SyntaxKind::FixedStatement => statement
            .children()
            .filter(|child| child.kind().is_statement_node())
            .last()
            .is_none_or(|inner| completes(&inner)),
        _ => true,
    }
}

/// `while (true)`, `do { } while (true)` and `for (;;)`.
fn loops_forever(statement: &SyntaxNode) -> bool {
    match statement.kind() {
        SyntaxKind::WhileStatement | SyntaxKind::DoStatement => statement
            .children()
            .any(|child| child.kind() == SyntaxKind::TrueLiteralExpression),
        SyntaxKind::ForStatement => {
            let semicolons: Vec<TextSpan> = statement
                .child_tokens()
                .filter(|token| token.kind() == SyntaxKind::SemicolonToken)
                .map(|token| token.span())
                .collect();
            let [first, second, ..] = semicolons.as_slice() else {
                return false;
            };
            let condition = statement.children().find(|child| {
                child.span().start() >= first.end() && child.span().end() <= second.start()
            });
            condition.is_none_or(|condition| condition.kind() == SyntaxKind::TrueLiteralExpression)
        }
        _ => false,
    }
}

/// Whether a `break` leaves this loop: one not inside a loop or a `switch`
/// of its own.
fn breaks_out(looping: &SyntaxNode) -> bool {
    looping
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::BreakStatement)
        .any(|found| {
            found
                .ancestors()
                .find(|ancestor| {
                    matches!(
                        ancestor.kind(),
                        SyntaxKind::WhileStatement
                            | SyntaxKind::DoStatement
                            | SyntaxKind::ForStatement
                            | SyntaxKind::ForEachStatement
                            | SyntaxKind::ForEachVariableStatement
                            | SyntaxKind::SwitchStatement
                    )
                })
                .is_some_and(|nearest| nearest.span() == looping.span())
        })
}

#[cfg(test)]
mod tests {
    use super::super::tests::found_with;

    #[test]
    fn declared_and_never_used() {
        let text = "class C { public void M() {\n\
                      int unused;\n\
                      int constant = 5;\n\
                      string text = null;\n\
                      int used = 1; System.Console.WriteLine(used);\n\
                      try { } catch (System.Exception e) { }\n\
                    } }\n";
        assert_eq!(found_with(text, "CS0168"), vec!["unused", "e"]);
        assert_eq!(found_with(text, "CS0219"), vec!["constant", "text"]);
        assert!(found_with(text, "IDE0059").is_empty());
    }

    #[test]
    fn values_nobody_reads() {
        let text = "class C {\n\
                      int Compute() => 1;\n\
                      public int M(int p) {\n\
                        var never = Compute();\n\
                        int x = Compute();\n\
                        x = Compute();\n\
                        int y = Compute();\n\
                        if (p > 0) { y = 2; }\n\
                        int z = Compute(); z = z + 1;\n\
                        int.TryParse(\"1\", out var parsed);\n\
                        int last = Compute(); System.Console.WriteLine(last); last = Compute();\n\
                        return x + y + z;\n\
                      }\n\
                    }\n";
        assert_eq!(
            found_with(text, "IDE0059"),
            vec!["never", "x", "parsed", "last"]
        );
        // Only the first `x` is overwritten, and only the last `last` is
        // not read.
        let semantic =
            super::super::super::tests::compile(&[("C.cs", text)], false).expect("compiled");
        let all = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .expect("analyzed");
        let starts: Vec<u32> = all
            .iter()
            .filter(|found| found.id == "IDE0059")
            .map(|found| found.span.start())
            .collect();
        let first_x = super::super::super::tests::at(text, "x = Compute", 0);
        let last_last = text.rfind("last = Compute()").expect("the marker") as u32;
        assert!(starts.contains(&first_x), "{starts:?}");
        assert!(starts.contains(&last_last), "{starts:?}");
        assert_eq!(starts.len(), 4, "{starts:?}");
    }

    #[test]
    fn loops_lambdas_and_refs_keep_values_alive() {
        let text = "using System;\n\
                    class C {\n\
                      bool More() => false;\n\
                      void Take(ref int r) { }\n\
                      public void M() {\n\
                        int total = 0;\n\
                        while (More()) { Console.WriteLine(total); total = 5; }\n\
                        int seen = 0; Action a = () => Console.WriteLine(seen); seen = 2; a();\n\
                        int passed = 0; Take(ref passed);\n\
                        for (int i = 0; i < 3; i++) { }\n\
                        int local = 1; int Get() => local; local = 2; Console.WriteLine(Get());\n\
                        const double half = 0.5; Func<double, double> scale = x => x * half; Console.WriteLine(scale(1));\n\
                      }\n\
                    }\n";
        assert!(
            found_with(text, "IDE0059").is_empty(),
            "{:?}",
            found_with(text, "IDE0059")
        );
        // A constant read only inside a lambda: the binder folds it into
        // its use, and it is still used.
        assert!(found_with(text, "CS0219").is_empty());
    }

    #[test]
    fn code_after_a_jump_is_unreachable() {
        let text = "class C {\n\
                      public int M(int p) {\n\
                        if (p > 0) { return 1; p = 2; p = 3; }\n\
                        while (true) { if (p > 5) break; p++; }\n\
                        while (true) { p++; }\n\
                        p = 4;\n\
                      }\n\
                      public void N(int p) {\n\
                        if (p > 0) return; else throw new System.Exception();\n\
                        p = 1;\n\
                      }\n\
                      public void L(int p) {\n\
                        goto end; p = 1; end: p = 2;\n\
                      }\n\
                    }\n";
        assert_eq!(
            found_with(text, "CS0162"),
            vec!["p = 2;", "p = 4;", "p = 1;", "p = 1;"]
        );
        assert_eq!(found_with(text, "IDE0035")[0], "p = 2; p = 3;");
    }

    /// What the variants below are declared beside.
    const LOCALS: &str = "using System; using System.Collections.Generic;\n\
        struct MyS { public static implicit operator MyS(int x) => default; public static implicit operator int(MyS x) => 0; }\n\
        class MyC { public static implicit operator MyC(int x) => null; }\n\
        class T2 { }\n\
        class Q {\n\
          static int Foo() => 1; const int Cst = 5; static readonly int Ro = 5; static readonly string Sro = \"a\"; static string Bar => \"b\"; static int Fld = 3; static int Prop => 1; static double Dbl = 1.5; static bool this_ = true; static object Obj = 1;\n";

    /// For each variant, whether the analyzers give its local CS0219, in a
    /// class with a method for each and compiled against the real framework:
    /// `None` where there is none.
    fn warned(variants: &[&str]) -> Option<Vec<bool>> {
        let mut text = LOCALS.to_string();
        let first = text.matches('\n').count();
        for (at, variant) in variants.iter().enumerate() {
            text.push_str(&format!("  static void M{at}() {{ {variant} }}\n"));
        }
        text.push_str("}\n");
        let semantic = crate::semantic::tests::compile(&[("C.cs", &text)], true)?;
        let lines: Vec<usize> = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .expect("analyzed")
            .iter()
            .filter(|diagnostic| diagnostic.id == "CS0219")
            .map(|diagnostic| {
                text[..diagnostic.span.start() as usize]
                    .matches('\n')
                    .count()
            })
            .collect();
        Some(
            (0..variants.len())
                .map(|at| lines.contains(&(first + at)))
                .collect(),
        )
    }

    /// Where the compiler says a local is assigned and never used: a constant,
    /// `default`, a tuple literal, a struct made with no arguments, through the
    /// conversions that keep what is inside, and `null` for a reference.
    #[test]
    fn a_value_the_compiler_calls_unused_is_reported() {
        let variants = [
            "int v = 1;",
            "uint v = 1u;",
            "long v = 1L;",
            "ulong v = 1UL;",
            "float v = 1f;",
            "double v = 1.5;",
            "decimal v = 1m;",
            "bool v = true;",
            "char v = 'a';",
            "string v = \"a\";",
            "byte v = 1;",
            "short v = 1;",
            "sbyte v = 1;",
            "ushort v = 1;",
            "var v = 1;",
            "var v = \"a\";",
            "var v = 1L;",
            "var v = 'a';",
            "var v = true;",
            "string v = null;",
            "object v = null;",
            "int? v = null;",
            "int[] v = null;",
            "int v = default;",
            "int v = default(int);",
            "string v = default;",
            "string v = default(string);",
            "object v = default;",
            "int? v = default;",
            "DateTime v = default;",
            "DateTime v = default(DateTime);",
            "(int, int) v = default;",
            "var v = default(int);",
            "System.Collections.Generic.List<int> v = null;",
            "int v = 1 + 2;",
            "int v = -1;",
            "int v = ~1;",
            "bool v = !true;",
            "bool v = true && false;",
            "string v = \"a\" + \"b\";",
            "int v = sizeof(int);",
            "string v = nameof(Console);",
            "int v = int.MaxValue;",
            "double v = Math.PI;",
            "int v = (int)1.5;",
            "char v = (char)65;",
            "int v = 'a';",
            "byte v = (byte)1;",
            "int v = 1 << 3;",
            "int v = true ? 1 : 2;",
            "const int c = 1; int v = c;",
            "const string c = \"a\"; string v = c;",
            "const int c = 1; var v = c + 1;",
            "DayOfWeek v = DayOfWeek.Monday;",
            "DayOfWeek v = 0;",
            "DayOfWeek v = (DayOfWeek)1;",
            "var v = DayOfWeek.Monday;",
            "int v = (int)DayOfWeek.Monday;",
            "long v = 1;",
            "double v = 1;",
            "decimal v = 1;",
            "float v = 1;",
            "ulong v = 1;",
            "double v = 'a';",
            "long v = int.MaxValue;",
            "int? v = 1;",
            "long? v = 1;",
            "double? v = 1;",
            "DayOfWeek? v = DayOfWeek.Monday;",
            "bool? v = true;",
            "char? v = 'a';",
            "int? v = (int?)1;",
            "var v = (int?)1;",
            "object v = (object)null;",
            "object v = (string)null;",
            "object v = default(string);",
            "ReadOnlySpan<char> v = \"a\";",
            "ReadOnlySpan<char> v = default;",
            "Span<int> v = default;",
            "MyS v = default;",
            "MyC v = null;",
            "MyS v = new MyS();",
            "int v = new int();",
            "var v = (1, 2);",
            "(int, int) v = (1, 2);",
            "var v = (1, \"a\");",
            "(object, object) v = (1, 2);",
            "int v = Cst;",
            "int v; v = 1;",
            "int v = 0; v = 1;",
            "string v; v = null;",
            "int v = (int)(object)1;",
            "string v = (string)(object)\"a\";",
            "long? v = (long?)1;",
            "int? v = (int?)null;",
            "double? v = 1 + 1;",
            "decimal? v = 1m;",
            "(int, object) v = (1, \"a\");",
            "(int, int) v = (Foo(), 1);",
            "((int, int), int) v = ((1, 2), 3);",
            "(int?, int?) v = (1, null);",
            "(string, string) v = (null, null);",
            "(object, object) v = (null, null);",
            "var v = ((object)1, 2);",
            "(int, int) v = (1, default);",
            "ValueTuple<int,int> v = default;",
            "int v = checked(1 + 2);",
            "int v = unchecked((int)3000000000);",
            "TimeSpan v = new TimeSpan();",
            "DateTime v = new DateTime();",
            "Guid v = new Guid();",
            "KeyValuePair<int,int> v = new KeyValuePair<int,int>();",
            "int v = 'a' + 1;",
            "ReadOnlySpan<char> v = \"a\" + \"b\";",
            "string v = (string)null;",
            "var v = (string)null;",
            "Nullable<int> v = new Nullable<int>();",
            "int? v = new int?();",
            "string v = \"x\"; v = null;",
            "string v = \"x\"; v = \"y\";",
            "int v = 0; v = 1; v = 2;",
            "int v = 0; if (this_) v = 1;",
            "int v = 0; for (int i = 0; i < 2; i++) v = 1;",
            "float v = 1.0f; v = 2;",
            "long v = (long)int.MaxValue;",
            "double v = (double)1;",
            "object v = (object)(string)null;",
            "IComparable v = null;",
            "dynamic v = null;",
            "Action v = null;",
            "MyC v = default;",
            "Func<int> v = default;",
            "T2 v = default;",
            "var v = new MyS();",
            "var v = default(MyS);",
            "var v = default(MyC);",
            "var v = (MyC)null;",
            "int v = (int)(short)1;",
            "int v = Cst + 1;",
            "long v = Cst;",
            "string v = \"a\" + \"b\" + \"c\";",
            "string v = \"a\" + null;",
            "string v = null + \"a\";",
            "ReadOnlySpan<int> v = default(ReadOnlySpan<int>);",
            "(int, int) v = (Foo(), Foo());",
            "var v = (Foo(), 1);",
            "var v = (Foo(), Foo());",
            "(object, int) v = (new object(), 1);",
            "var v = (new object(), 1);",
            "var v = (Obj, 1);",
            "var v = (1, (Foo(), 2));",
            "(int, int) v = (1, 1); v = (Foo(), 1);",
            "(int, int) v = (Foo(), 1); v = (1, 1);",
            "var v = (a: 1, b: 2);",
            "(long, long) v = (1, 2);",
            "(int, int) v = (this_ ? 1 : 2, 1);",
        ];
        let Some(found) = warned(&variants) else {
            return;
        };
        for (variant, found) in variants.iter().zip(found) {
            assert!(found, "no CS0219 for {variant}");
        }
    }

    /// Where the compiler counts the value as used: a non-null value boxed or
    /// converted into a reference type, text built with holes, a call, a user's
    /// conversion, a read of a field, an initializer on a `new`.
    #[test]
    fn a_value_the_compiler_calls_used_is_not_reported() {
        let variants = [
            "var v = null as string;",
            "string v = \"a\" + 1;",
            "string v = string.Empty;",
            "object v = \"a\";",
            "object v = 1;",
            "object v = 'a';",
            "object v = true;",
            "object v = 1L;",
            "object v = 1.5;",
            "object v = DayOfWeek.Monday;",
            "var v = (object)\"a\";",
            "var v = (object)1;",
            "IComparable v = \"a\";",
            "IComparable v = 1;",
            "ValueType v = 1;",
            "Enum v = DayOfWeek.Monday;",
            "IFormattable v = 1;",
            "IFormattable v = 1.5;",
            "IConvertible v = 1;",
            "dynamic v = 1;",
            "dynamic v = \"a\";",
            "ICloneable v = \"a\";",
            "System.Collections.IEnumerable v = \"a\";",
            "IComparable<string> v = \"a\";",
            "object v = 1 + 2;",
            "object v = \"a\" + \"b\";",
            "IComparable v = 1 + 2;",
            "string v = $\"a\";",
            "string v = $\"{1}\";",
            "const string c = \"x\"; string v = $\"{c}\";",
            "object v = $\"a\";",
            "IFormattable v = $\"a\";",
            "var v = $\"a\";",
            "FormattableString v = $\"a\";",
            "string v = $\"a{1}b\";",
            "ReadOnlySpan<byte> v = new byte[] { 1 };",
            "MyS v = 1;",
            "MyC v = 1;",
            "MyS? v = 1;",
            "int v = new MyS();",
            "object v = new object();",
            "var v = new object();",
            "object v = new();",
            "var v = typeof(int);",
            "Type v = typeof(int);",
            "var v = new int[0];",
            "int v = Foo();",
            "string v = Bar;",
            "int v = Fld;",
            "var v = new List<int>();",
            "int v = Ro;",
            "string v = Sro;",
            "int v = Prop;",
            "Action v = () => { };",
            "Func<int> v = () => 1;",
            "var v = new { A = 1 };",
            "int v = this_ ? 1 : 2;",
            "int v = this_ ? 1 : 1;",
            "int v = (int)Dbl;",
            "object v; v = \"a\";",
            "int v = 1; v++;",
            "int v = 1; v += 1;",
            "object v = null; v = 1;",
            "int v = 0; v = Foo();",
            "int v = Foo(); v = 1;",
            "object v = \"a\"; v = \"b\";",
            "int v = ((int?)1).Value;",
            "int v = (int?)1 ?? 2;",
            "DateTime v = new DateTime(1);",
            "MyS v = new MyS { };",
            "object v = new MyS();",
            "int v = new int { };",
            "int? v = new int?(1);",
            "int[] v = { 1 };",
            "int[] v = new int[] { };",
            "string v = \"x\"; v = Bar;",
            "object v = Cst;",
            "string v = $\"{Cst}\";",
            "string v = Cst + \"a\";",
            "string v = \"a\" + 'b';",
            "string v = \"a\" + (object)\"b\";",
            "ReadOnlySpan<char> v = $\"a\";",
            "ReadOnlySpan<char> v = Bar;",
            "ReadOnlySpan<char> v = string.Empty;",
            "ValueTuple<int, int> v = new ValueTuple<int, int>(1, 2);",
            "var v = ValueTuple.Create(1, 2);",
            "var v = Tuple.Create(1, 2);",
        ];
        let Some(found) = warned(&variants) else {
            return;
        };
        for (variant, found) in variants.iter().zip(found) {
            assert!(!found, "CS0219 for {variant}");
        }
    }
}
