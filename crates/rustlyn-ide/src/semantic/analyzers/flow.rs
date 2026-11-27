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
    BoundBody, BoundExpression, BoundExpressionKind as E, BoundStatement, BoundStatementKind as S,
    LocalId, RefKind,
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

    fn is_constant(&self, value: &BoundExpression) -> bool {
        matches!(value.kind, E::Default(_)) || self.view.model.binder().folded(value).is_some()
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
                    let constant = self.is_constant(value);
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
                    let constant = self.is_constant(value);
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
                    let constant = self.is_constant(value);
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
}
