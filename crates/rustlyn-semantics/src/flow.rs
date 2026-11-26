//! What a body's control flow and its use of locals say is wrong with it:
//! a method whose end can be reached without a `return` (CS0161, and CS1643
//! for a lambda), statements nothing can reach (CS0162), and locals declared
//! and never read (CS0168, CS0219).
//!
//! This is a reachability analysis over the bound tree, the part of Roslyn's
//! flow analysis these diagnostics need, and no more: it does not track
//! definite assignment. Like the declaration checks, it would rather say
//! nothing than something wrong. A `goto`, a label, a statement the binder
//! does not model, a condition that may be a constant the folder cannot see
//! — any of these makes the answer for the whole body "not sure", and a body
//! the analysis is not sure about gets no flow diagnostic at all.

use std::collections::{HashMap, HashSet};

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use crate::binder::{Binder, Diagnostics};
use crate::bound::{
    BoundBody, BoundExpression, BoundExpressionKind, BoundPatternKind, BoundStatement,
    BoundStatementKind, BoundSwitchLabel, BoundSymbol, ConstantValue, LocalId,
};
use crate::checks::member_display;
use crate::corlib::SpecialType;
use crate::symbol::{MethodKind, Modifiers, SymbolId, SymbolKind};
use crate::types::Type;

/// Checks one bound member body and adds what it finds to its diagnostics.
pub(crate) fn check(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    member: Option<SymbolId>,
    body: &mut BoundBody,
) {
    let mut found = Diagnostics::new();
    let report = |found: &mut Diagnostics, code: ErrorCode, span: TextSpan, args: &[&str]| {
        found.push((tree, Diagnostic::new(code, span, args)));
    };

    // The member's own statements.
    if let Some(analysis) = Reachability::of(binder, declaration, &body.statements) {
        for span in &analysis.unreachable {
            report(&mut found, ErrorCode::WrnUnreachableCode, *span, &[]);
        }
        if analysis.end_reachable
            && let Some((name, at)) =
                member.and_then(|member| member_needs_return(binder, declaration, member, body))
        {
            report(&mut found, ErrorCode::ErrReturnExpected, at, &[&name]);
        }
    }

    // `skip:` that no `goto`, `break` or `continue` names.
    for span in unreferenced_labels(declaration) {
        report(&mut found, ErrorCode::WrnUnreferencedLabel, span, &[]);
    }

    // `return 1;` in a `void` method, and `return;` in one that returns a
    // value.
    if let Some(member) = member {
        found.extend(mismatched_returns(binder, tree, declaration, member, body));
    }

    // Each local function, as a method of its own.
    for function in &body.local_functions {
        // `static extern int Call();` declares a local function whose body
        // is somewhere else entirely.
        if !written_with_block(declaration, binder, function.symbol) {
            continue;
        }
        let analysis = Reachability::of(binder, declaration, std::slice::from_ref(&function.body));
        let Some(analysis) = analysis else { continue };
        for span in &analysis.unreachable {
            report(&mut found, ErrorCode::WrnUnreachableCode, *span, &[]);
        }
        if analysis.end_reachable
            && function.iterator.is_none()
            && let Some((name, at)) = local_function_needs_return(binder, function.symbol)
        {
            report(&mut found, ErrorCode::ErrReturnExpected, at, &[&name]);
        }
    }

    // Each lambda with a block for a body.
    for lambda in &body.lambdas {
        let Some(analysis) =
            Reachability::of(binder, declaration, std::slice::from_ref(&lambda.body))
        else {
            continue;
        };
        for span in &analysis.unreachable {
            report(&mut found, ErrorCode::WrnUnreachableCode, *span, &[]);
        }
        if !analysis.end_reachable
            || matches!(lambda.return_type, Type::Void | Type::Error)
            || !matches!(lambda.body.kind, BoundStatementKind::Block(_))
        {
            continue;
        }
        let syntax = find_node(declaration, lambda.span);
        let arrow = syntax.as_ref().and_then(|node| {
            node.child_tokens()
                .find(|token| token.kind() == SyntaxKind::EqualsGreaterThanToken)
        });
        let delegate = body.types.get(&lambda.span).filter(|ty| !ty.is_error());
        if let (Some(arrow), Some(delegate)) = (arrow, delegate) {
            let name = delegate.display(binder.compilation().symbols());
            report(
                &mut found,
                ErrorCode::ErrAnonymousReturnExpected,
                arrow.span(),
                &[&name],
            );
        }
    }

    found.extend(unused_locals(binder, tree, declaration, body));
    found.extend(unreadable_properties(binder, tree, body));
    // A member written without a body has no `out` parameter to assign.
    let has_body = declaration.child_of_kind(SyntaxKind::Block).is_some()
        || declaration
            .child_of_kind(SyntaxKind::ArrowExpressionClause)
            .is_some();
    found.extend(crate::definite::check(
        binder,
        tree,
        member.filter(|_| has_body),
        body,
    ));
    body.diagnostics.extend(found);
}

/// Whether a member has to return a value on every path: its name for the
/// message and where to put it, or `None` where it need not or where that
/// cannot be told.
fn member_needs_return(
    binder: &Binder<'_>,
    declaration: &SyntaxNode,
    member: SymbolId,
    body: &BoundBody,
) -> Option<(String, TextSpan)> {
    // Only a body written as a block can run off its end; `=> e` is a return.
    declaration.child_of_kind(SyntaxKind::Block)?;
    if body.iterator.is_some() {
        return None;
    }
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    let symbol = symbols.get(member);
    let detail = symbol.as_method()?;
    let (name, at) = match (declaration.kind(), detail.method_kind) {
        (SyntaxKind::MethodDeclaration, MethodKind::Ordinary) => (
            member_display(compilation, member, &Default::default(), None),
            symbol.locations.first()?.span,
        ),
        (SyntaxKind::GetAccessorDeclaration, MethodKind::PropertyGet) => {
            let property = symbol.container?;
            let keyword = declaration
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::GetKeyword)?;
            (
                format!(
                    "{}.get",
                    member_display(compilation, property, &Default::default(), None)
                ),
                keyword.span(),
            )
        }
        _ => return None,
    };
    let returns = binder.type_of(member, &mut Diagnostics::new());
    if !needs_value(&returns, symbol.modifiers.contains(Modifiers::ASYNC)) {
        return None;
    }
    Some((name, at))
}

/// Whether the local function `function` was written with a block body.
fn written_with_block(declaration: &SyntaxNode, binder: &Binder<'_>, function: SymbolId) -> bool {
    let symbols = binder.compilation().symbols();
    let Some(location) = symbols.get(function).locations.first() else {
        return false;
    };
    declaration
        .find_token(location.span.start())
        .filter(|token| token.span() == location.span)
        .is_some_and(|token| {
            let statement = token.parent();
            statement.kind() == SyntaxKind::LocalFunctionStatement
                && statement.child_of_kind(SyntaxKind::Block).is_some()
        })
}

fn local_function_needs_return(
    binder: &Binder<'_>,
    function: SymbolId,
) -> Option<(String, TextSpan)> {
    let compilation = binder.compilation();
    let symbol = compilation.symbols().get(function);
    if symbol.kind != SymbolKind::Method {
        return None;
    }
    let returns = binder.type_of(function, &mut Diagnostics::new());
    if !needs_value(&returns, symbol.modifiers.contains(Modifiers::ASYNC)) {
        return None;
    }
    let name = member_display(compilation, function, &Default::default(), Some(""));
    Some((name, symbol.locations.first()?.span))
}

/// Whether a body declared to return `returns` has to hand back a value:
/// not for `void`, and not for an `async` method whose task carries none.
fn needs_value(returns: &Type, is_async: bool) -> bool {
    match returns {
        Type::Void | Type::Error => false,
        Type::Named { type_arguments, .. } if is_async => !type_arguments.is_empty(),
        _ => !is_async,
    }
}

/// CS0127 and CS0126: a `return` that gives a value where the method
/// returns none, or none where it returns one.
fn mismatched_returns(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    member: SymbolId,
    body: &BoundBody,
) -> Diagnostics {
    let mut found = Diagnostics::new();
    if declaration.kind() != SyntaxKind::MethodDeclaration
        || declaration.child_of_kind(SyntaxKind::Block).is_none()
        || body.iterator.is_some()
    {
        return found;
    }
    let compilation = binder.compilation();
    let symbol = compilation.symbols().get(member);
    if symbol.modifiers.contains(Modifiers::ASYNC)
        || symbol
            .as_method()
            .is_none_or(|detail| detail.method_kind != MethodKind::Ordinary)
    {
        return found;
    }
    // Whether it returns `void` the syntax says; the type itself is only
    // worked out for a message that needs it.
    let Some(written) = declaration
        .children()
        .find(|child| child.kind().is_type_node())
    else {
        return found;
    };
    let void = written.kind() == SyntaxKind::PredefinedType
        && written
            .first_token()
            .is_some_and(|token| token.kind() == SyntaxKind::VoidKeyword);
    let name = || member_display(compilation, member, &Default::default(), None);
    // Where each `return` keyword is, found by one walk over the tokens the
    // first time a `return` is met: looking each up from the root costs the
    // depth of the tree, which in a long `else if` ladder is its length.
    let mut keywords: Option<HashMap<u32, TextSpan>> = None;
    let mut visit = |statement: &BoundStatement| {
        let BoundStatementKind::Return(value) = &statement.kind else {
            return;
        };
        let keywords = keywords.get_or_insert_with(|| {
            declaration
                .descendant_tokens()
                .filter(|token| {
                    token.kind() == SyntaxKind::ReturnKeyword && !token.span().is_empty()
                })
                .map(|token| (token.span().start(), token.span()))
                .collect()
        });
        let Some(&keyword) = keywords.get(&statement.span.start()) else {
            return;
        };
        match value {
            Some(_) if void => found.push((
                tree,
                Diagnostic::new(ErrorCode::ErrRetNoObjectRequired, keyword, &[&name()]),
            )),
            None if !void => {
                let returns = binder.type_of(member, &mut Diagnostics::new());
                if !returns.is_error() {
                    let shown = returns.display(compilation.symbols());
                    found.push((
                        tree,
                        Diagnostic::new(ErrorCode::ErrRetObjectRequired, keyword, &[&shown]),
                    ));
                }
            }
            _ => {}
        }
    };
    for statement in &body.statements {
        each_statement(statement, &mut visit);
    }
    found
}

/// Calls `visit` on a statement and every statement inside it, but not on
/// the bodies of lambdas and local functions, which return for themselves.
fn each_statement(statement: &BoundStatement, visit: &mut impl FnMut(&BoundStatement)) {
    visit(statement);
    match &statement.kind {
        BoundStatementKind::Block(statements) => {
            for inner in statements {
                each_statement(inner, visit);
            }
        }
        BoundStatementKind::If {
            consequence,
            alternative,
            ..
        } => {
            each_statement(consequence, visit);
            if let Some(alternative) = alternative {
                each_statement(alternative, visit);
            }
        }
        BoundStatementKind::While { body, .. }
        | BoundStatementKind::DoWhile { body, .. }
        | BoundStatementKind::ForEach { body, .. }
        | BoundStatementKind::Using { body, .. }
        | BoundStatementKind::Lock { body, .. }
        | BoundStatementKind::Fixed { body, .. } => each_statement(body, visit),
        BoundStatementKind::For {
            initializers, body, ..
        } => {
            for inner in initializers {
                each_statement(inner, visit);
            }
            each_statement(body, visit);
        }
        BoundStatementKind::Switch { sections, .. } => {
            for section in sections {
                for inner in &section.statements {
                    each_statement(inner, visit);
                }
            }
        }
        BoundStatementKind::Try {
            body,
            catches,
            finally,
        } => {
            each_statement(body, visit);
            for catch in catches {
                each_statement(&catch.body, visit);
            }
            if let Some(finally) = finally {
                each_statement(finally, visit);
            }
        }
        _ => {}
    }
}

/// Where a body's control can reach.
struct Reachability<'s> {
    declaration: &'s SyntaxNode,
    binder: &'s Binder<'s>,
    /// The first statement of each stretch nothing reaches.
    unreachable: Vec<TextSpan>,
    /// Whether the stretch being walked has been reported already.
    reported: bool,
    /// The loops and `switch`es being walked, innermost last.
    targets: Vec<Target>,
    end_reachable: bool,
    /// Something the analysis cannot judge was met.
    unsure: bool,
}

struct Target {
    is_switch: bool,
    broken: bool,
    continued: bool,
    /// For a loop, whether the end of its body is reached.
    ends: bool,
}

impl<'s> Reachability<'s> {
    /// Walks the statements of a body; `None` where the walk met something
    /// it cannot judge.
    fn of(
        binder: &'s Binder<'s>,
        declaration: &'s SyntaxNode,
        statements: &[BoundStatement],
    ) -> Option<Self> {
        let mut walk = Self {
            declaration,
            binder,
            unreachable: Vec::new(),
            reported: false,
            targets: Vec::new(),
            end_reachable: true,
            unsure: false,
        };
        walk.end_reachable = walk.list(statements, true);
        (!walk.unsure).then_some(walk)
    }

    fn list(&mut self, statements: &[BoundStatement], mut reachable: bool) -> bool {
        for statement in statements {
            reachable = self.statement(statement, reachable);
        }
        reachable
    }

    /// Walks one statement that is reached or not, and answers whether its
    /// end is.
    fn statement(&mut self, statement: &BoundStatement, reachable: bool) -> bool {
        if reachable {
            self.reported = false;
        } else if !self.reported && self.reportable(statement) {
            if let Some(span) = self.first_token(statement.span) {
                self.unreachable.push(span);
            }
            self.reported = true;
        }
        match &statement.kind {
            BoundStatementKind::Block(statements) => self.list(statements, reachable),
            BoundStatementKind::LocalDeclaration { .. }
            | BoundStatementKind::Expression(_)
            | BoundStatementKind::ConstructorInitializer { .. }
            | BoundStatementKind::YieldReturn(_)
            | BoundStatementKind::Empty => reachable,
            BoundStatementKind::Return(_)
            | BoundStatementKind::Throw(_)
            | BoundStatementKind::YieldBreak
            | BoundStatementKind::GotoCase(_) => false,
            BoundStatementKind::Break(outward) => {
                if reachable && let Some(target) = self.targets.iter_mut().rev().nth(*outward) {
                    target.broken = true;
                }
                false
            }
            BoundStatementKind::Continue(outward) => {
                if reachable
                    && let Some(target) = self
                        .targets
                        .iter_mut()
                        .rev()
                        .filter(|target| !target.is_switch)
                        .nth(*outward)
                {
                    target.continued = true;
                }
                false
            }
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                let constant = self.condition(condition);
                let then_end = self.statement(consequence, reachable && constant != Some(false));
                let else_reachable = reachable && constant != Some(true);
                let else_end = match alternative {
                    Some(alternative) => self.statement(alternative, else_reachable),
                    None => else_reachable,
                };
                then_end || else_end
            }
            BoundStatementKind::While { condition, body } => {
                let constant = self.condition(condition);
                let target = self.looping(body, reachable && constant != Some(false));
                target.broken || (reachable && constant != Some(true))
            }
            BoundStatementKind::DoWhile { body, condition } => {
                let constant = self.condition(condition);
                self.targets.push(Target {
                    is_switch: false,
                    broken: false,
                    continued: false,
                    ends: false,
                });
                let body_end = self.statement(body, reachable);
                let target = self.targets.pop().unwrap_or(Target {
                    is_switch: false,
                    broken: false,
                    continued: false,
                    ends: false,
                });
                target.broken || ((body_end || target.continued) && constant != Some(true))
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                let reachable = self.list(initializers, reachable);
                let constant = match condition {
                    Some(condition) => self.condition(condition),
                    None => Some(true),
                };
                let entered = reachable && constant != Some(false);
                let target = self.looping(body, entered);
                // `i++` runs after the body; where the body never ends and
                // nothing continues, it never runs.
                if entered
                    && !target.ends
                    && !target.continued
                    && let Some(first) = incrementors.first()
                    && let Some(token) = self.declaration.find_token(first.span.start())
                {
                    self.unreachable.push(token.span());
                }
                target.broken || (reachable && constant != Some(true))
            }
            BoundStatementKind::ForEach { body, .. } => {
                self.looping(body, reachable);
                reachable
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => self.switch(governing, sections, reachable),
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => {
                let mut end = self.statement(body, reachable);
                for catch in catches {
                    end |= self.statement(&catch.body, reachable);
                }
                match finally {
                    Some(finally) => self.statement(finally, reachable) && end,
                    None => end,
                }
            }
            BoundStatementKind::Using { body, .. }
            | BoundStatementKind::Lock { body, .. }
            | BoundStatementKind::Fixed { body, .. } => self.statement(body, reachable),
            // A label nothing jumps to is where the code falls through to;
            // a `goto` is what the walk cannot follow.
            BoundStatementKind::Label(_) => reachable,
            BoundStatementKind::Goto(_) | BoundStatementKind::Unsupported(_) => {
                self.unsure = true;
                reachable
            }
        }
    }

    /// Walks the body of a loop and gives back what it learned about how
    /// the loop is left.
    fn looping(&mut self, body: &BoundStatement, reachable: bool) -> Target {
        self.targets.push(Target {
            is_switch: false,
            broken: false,
            continued: false,
            ends: false,
        });
        let ends = self.statement(body, reachable);
        let mut target = self.targets.pop().unwrap_or(Target {
            is_switch: false,
            broken: false,
            continued: false,
            ends: false,
        });
        target.ends = ends;
        target
    }

    fn switch(
        &mut self,
        governing: &BoundExpression,
        sections: &[crate::bound::BoundSwitchSection],
        reachable: bool,
    ) -> bool {
        // A constant to switch on picks its section at compile time, and a
        // `bool` or a pattern may cover every value without a `default`:
        // both are for a finer analysis than this one.
        if could_be_constant(governing) {
            self.unsure = true;
            return reachable;
        }
        let mut has_default = false;
        let mut only_constants = true;
        for section in sections {
            for label in &section.labels {
                match label {
                    BoundSwitchLabel::Default => has_default = true,
                    BoundSwitchLabel::Case(case) => {
                        if !matches!(case.pattern.kind, BoundPatternKind::Constant(_)) {
                            only_constants = false;
                        }
                    }
                }
            }
        }
        let governed_by_bool = self.is_boolean(&governing.ty);
        if !has_default && (!only_constants || governed_by_bool) {
            self.unsure = true;
            return reachable;
        }
        self.targets.push(Target {
            is_switch: true,
            broken: false,
            continued: false,
            ends: false,
        });
        for section in sections {
            if self.list(&section.statements, reachable) {
                // Falling out of a section is an error of its own.
                self.unsure = true;
            }
        }
        let target = self.targets.pop().unwrap_or(Target {
            is_switch: true,
            broken: false,
            continued: false,
            ends: false,
        });
        if target.continued
            && let Some(outer) = self
                .targets
                .iter_mut()
                .rev()
                .find(|target| !target.is_switch)
        {
            outer.continued = true;
        }
        target.broken || (reachable && !has_default)
    }

    fn is_boolean(&self, ty: &Type) -> bool {
        let compilation = self.binder.compilation();
        let boolean = compilation.special_type(SpecialType::Boolean);
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                Some(*symbol) == boolean
                    || type_arguments.first().is_some_and(|argument| {
                        matches!(argument, Type::Named { symbol, .. } if Some(*symbol) == boolean)
                    })
            }
            _ => false,
        }
    }

    /// The value a condition always has, if it is a constant; a condition
    /// that may be one this folder cannot work out makes the walk unsure.
    fn condition(&mut self, condition: &BoundExpression) -> Option<bool> {
        match self.binder.folded(condition) {
            Some(ConstantValue::Boolean(value)) => Some(value),
            _ => {
                if could_be_constant(condition) {
                    self.unsure = true;
                }
                None
            }
        }
    }

    /// Whether Roslyn would warn about this statement being unreachable: a
    /// block, an empty statement, a `throw` and a local function are exempt.
    fn reportable(&self, statement: &BoundStatement) -> bool {
        !matches!(
            statement.kind,
            BoundStatementKind::Block(_)
                | BoundStatementKind::Empty
                | BoundStatementKind::Throw(_)
                | BoundStatementKind::Label(_)
        )
    }

    /// The first token of the statement written at `span`, which is where
    /// Roslyn puts the warning.
    fn first_token(&self, span: TextSpan) -> Option<TextSpan> {
        let token = self.declaration.find_token(span.start())?;
        let statement = std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find(|node| node.kind().is_statement_node())?;
        Some(statement.first_token()?.span())
    }
}

/// Whether an expression is made only of what a constant can be made of, so
/// that it may be one even where the folder says it is not.
fn could_be_constant(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::Literal(_) | BoundExpressionKind::Default(_) => true,
        BoundExpressionKind::Field { receiver, .. } => receiver
            .as_deref()
            .is_none_or(|receiver| matches!(receiver.kind, BoundExpressionKind::TypeExpression(_))),
        BoundExpressionKind::Unary { operand, .. }
        | BoundExpressionKind::Conversion { operand, .. } => could_be_constant(operand),
        BoundExpressionKind::Binary { left, right, .. } => {
            could_be_constant(left) && could_be_constant(right)
        }
        _ => false,
    }
}

fn find_node(declaration: &SyntaxNode, span: TextSpan) -> Option<SyntaxNode> {
    declaration
        .descendants()
        .find(|node| node.span() == span && node.kind().is_expression_node())
}

// MARK: - locals never used

/// CS0168 and CS0219: a local declared and never read.
///
/// Which names read a local is taken from the syntax rather than the bound
/// tree: every `x` in the body that the binder says is this local, or that
/// the binder never got to, counts as a read unless it is the left side of
/// a plain assignment. A name inside a lambda nothing converted is still a
/// read that way, so the one mistake this can make is to stay quiet.
fn unused_locals(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    body: &BoundBody,
) -> Diagnostics {
    let mut found = Diagnostics::new();
    // Where each local name is declared, to tell a name declared twice.
    let mut declared: HashMap<&str, HashSet<TextSpan>> = HashMap::new();
    for local in &body.locals {
        declared
            .entry(local.name.as_str())
            .or_default()
            .insert(local.span);
    }
    // Every simple name in the body by its text, made on first need: most
    // bodies declare no local that could go unused.
    let mut names: Option<HashMap<String, Vec<SyntaxNode>>> = None;
    for (index, local) in body.locals.iter().enumerate() {
        let id = LocalId(index as u32);
        // A local made while an overload was being tried has no name that
        // the final binding says is it.
        if body.references.get(&local.span) != Some(&BoundSymbol::Local(id)) || local.ty.is_error()
        {
            continue;
        }
        let Some(token) = declaration.find_token(local.span.start()) else {
            continue;
        };
        // Two locals of one name, in one body: which name reads which is
        // for the scopes to say, and a redeclaration is its own error. A
        // `catch (Exception e)` beside another `catch (... e)` is no
        // redeclaration: each is its own clause's, and every name in one
        // was bound to its own.
        if declared
            .get(local.name.as_str())
            .is_some_and(|spans| spans.len() > 1)
            && token.parent().kind() != SyntaxKind::CatchDeclaration
        {
            continue;
        }
        if token.span() != local.span || token.value_text() != local.name {
            continue;
        }
        let parent = token.parent();
        let (declared_by_statement, initializer) = match parent.kind() {
            SyntaxKind::VariableDeclarator => {
                let Some(statement) = parent
                    .parent()
                    .and_then(|declaration| declaration.parent())
                    .filter(|statement| statement.kind() == SyntaxKind::LocalDeclarationStatement)
                else {
                    continue;
                };
                // `using var` is used by being disposed, and a constant is
                // not a variable at all.
                if statement.child_tokens().any(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::UsingKeyword | SyntaxKind::ConstKeyword
                    )
                }) {
                    continue;
                }
                let value = parent
                    .child_of_kind(SyntaxKind::EqualsValueClause)
                    .and_then(|clause| clause.children().next());
                (true, value)
            }
            SyntaxKind::CatchDeclaration => (true, None),
            _ => continue,
        };
        if !declared_by_statement {
            continue;
        }

        let mut read = false;
        let mut written = initializer.is_some();
        let mut written_with_value = initializer
            .as_ref()
            .is_some_and(|value| !is_constant_write(value, &local.ty, binder));
        let names = names.get_or_insert_with(|| {
            let mut by_text: HashMap<String, Vec<SyntaxNode>> = HashMap::new();
            for node in declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::IdentifierName)
            {
                if let Some(token) = node.first_token() {
                    by_text
                        .entry(token.value_text().to_string())
                        .or_default()
                        .push(node);
                }
            }
            by_text
        });
        for name in names.get(&local.name).map_or(&[][..], Vec::as_slice) {
            if name.span() == local.span {
                continue;
            }
            match body.references.get(&name.span()) {
                Some(BoundSymbol::Local(other)) if *other != id => continue,
                Some(BoundSymbol::Declared(_)) => continue,
                _ => {}
            }
            match assigned_value(name) {
                Some(value) => {
                    written = true;
                    if !is_constant_write(&value, &local.ty, binder) {
                        written_with_value = true;
                    }
                }
                None => read = true,
            }
        }
        if read || written_with_value {
            continue;
        }
        let code = if written {
            ErrorCode::WrnUnreferencedVarAssg
        } else {
            ErrorCode::WrnUnreferencedVar
        };
        found.push((tree, Diagnostic::new(code, local.span, &[&local.name])));
    }
    found
}

/// The value assigned where `name` is the whole left side of `name = value`.
fn assigned_value(name: &SyntaxNode) -> Option<SyntaxNode> {
    let parent = name.parent()?;
    if parent.kind() != SyntaxKind::SimpleAssignmentExpression {
        return None;
    }
    let mut children = parent.children();
    if children.next().as_ref() != Some(name) {
        return None;
    }
    // `x = y = 1` reads the assignment's value, which is not `x`'s business.
    children.next()
}

/// Whether writing `value` to a local of type `ty` leaves it unused, as
/// Roslyn sees it: a constant is, for a value type or a string; for any
/// other reference type only `null` is, since holding a reference keeps an
/// object alive and the debugger shows it.
fn is_constant_write(value: &SyntaxNode, ty: &Type, binder: &Binder<'_>) -> bool {
    let value = strip_parentheses(value);
    let constant = match value.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression
        | SyntaxKind::DefaultLiteralExpression
        | SyntaxKind::DefaultExpression => true,
        SyntaxKind::UnaryMinusExpression => value
            .children()
            .next()
            .is_some_and(|operand| operand.kind() == SyntaxKind::NumericLiteralExpression),
        _ => false,
    };
    if !constant {
        return false;
    }
    let null_like = matches!(
        value.kind(),
        SyntaxKind::NullLiteralExpression
            | SyntaxKind::DefaultLiteralExpression
            | SyntaxKind::DefaultExpression
    );
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    match ty {
        Type::Named { symbol, .. } => {
            // The types a literal is a constant of: the language's own,
            // `string` among them, and an enum, which `0` converts to.
            let primitive = PRIMITIVES
                .iter()
                .any(|special| compilation.special_type(*special) == Some(*symbol))
                || symbols.get(*symbol).type_kind() == Some(crate::symbol::TypeKind::Enum);
            if primitive {
                true
            } else if ty.is_reference_type(symbols) {
                null_like
            } else {
                // `BigInteger n = 0` converts through an operator the type
                // declares, which is a call and not a constant; `int? x = 1`
                // Roslyn does warn about, and this says nothing.
                null_like && binder.nullable_underlying(ty).is_none()
            }
        }
        Type::TypeParameter(_) | Type::Array { .. } => null_like,
        _ => false,
    }
}

/// The types a literal can be a constant of.
const PRIMITIVES: [SpecialType; 14] = [
    SpecialType::Boolean,
    SpecialType::Char,
    SpecialType::SByte,
    SpecialType::Byte,
    SpecialType::Int16,
    SpecialType::UInt16,
    SpecialType::Int32,
    SpecialType::UInt32,
    SpecialType::Int64,
    SpecialType::UInt64,
    SpecialType::Single,
    SpecialType::Double,
    SpecialType::Decimal,
    SpecialType::String,
];

fn strip_parentheses(node: &SyntaxNode) -> SyntaxNode {
    let mut node = node.clone();
    while node.kind() == SyntaxKind::ParenthesizedExpression {
        match node.children().next() {
            Some(inner) => node = inner,
            None => break,
        }
    }
    node
}

// MARK: - properties with nothing to read

/// CS0154: a property or indexer with no `get` read anywhere but as the
/// target of an assignment. One that overrides may take its getter from the
/// property it overrides, and is left alone.
fn unreadable_properties(binder: &Binder<'_>, tree: usize, body: &BoundBody) -> Diagnostics {
    let mut found = Diagnostics::new();
    let mut check = |expression: &BoundExpression| {
        unreadable_in(binder, tree, expression, false, &mut found);
    };
    for statement in &body.statements {
        crate::definite::each_expression_of(statement, &mut check);
    }
    for function in &body.local_functions {
        crate::definite::each_expression_of(&function.body, &mut check);
    }
    for lambda in &body.lambdas {
        crate::definite::each_expression_of(&lambda.body, &mut check);
    }
    found
}

fn unreadable_in(
    binder: &Binder<'_>,
    tree: usize,
    expression: &BoundExpression,
    written: bool,
    found: &mut Diagnostics,
) {
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    let property = match &expression.kind {
        BoundExpressionKind::Property { property, .. } => Some(*property),
        BoundExpressionKind::IndexerAccess { indexer, .. } => Some(*indexer),
        _ => None,
    };
    if let Some(property) = property
        && !written
    {
        let symbol = symbols.get(property);
        if let Some(detail) = symbol.as_property()
            && !detail.has_get
            && (detail.has_set || detail.has_init)
            && !symbol.modifiers.contains(Modifiers::OVERRIDE)
            && !compilation.is_from_metadata(property)
        {
            let name = member_display(compilation, property, &Default::default(), None);
            found.push((
                tree,
                Diagnostic::new(ErrorCode::ErrPropertyLacksGet, expression.span, &[&name]),
            ));
        }
    }
    let mut read = |child: &BoundExpression| unreadable_in(binder, tree, child, false, found);
    match &expression.kind {
        // What is assigned to is written, not read; what it is reached
        // through is read.
        BoundExpressionKind::Assignment { target, value } => {
            unreadable_in(binder, tree, target, true, found);
            unreadable_in(binder, tree, value, false, found);
        }
        BoundExpressionKind::Property { receiver, .. } if written => {
            if let Some(receiver) = receiver {
                read(receiver);
            }
        }
        BoundExpressionKind::IndexerAccess {
            receiver,
            arguments,
            ..
        } if written => {
            read(receiver);
            for argument in arguments {
                read(argument);
            }
        }
        BoundExpressionKind::TupleCreation(elements) if written => {
            for element in elements {
                unreadable_in(binder, tree, element, true, found);
            }
        }
        _ => crate::definite::each_child_of(expression, &mut read),
    }
}

/// Whether a node is a body of its own: a jump inside it cannot leave it,
/// and a label inside it is not one of the body around it.
pub(crate) fn is_function_boundary(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::LocalFunctionStatement
    ) || !(kind.is_statement_node() || kind.is_expression() || is_inside_statement(kind))
}

/// The syntax that sits between statements without being one: a `switch`
/// section, a `catch`, a declaration's parts.
fn is_inside_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::SwitchSection
            | SyntaxKind::CatchClause
            | SyntaxKind::CatchDeclaration
            | SyntaxKind::CatchFilterClause
            | SyntaxKind::FinallyClause
            | SyntaxKind::ElseClause
            | SyntaxKind::VariableDeclaration
            | SyntaxKind::VariableDeclarator
            | SyntaxKind::EqualsValueClause
            | SyntaxKind::Argument
            | SyntaxKind::ArgumentList
            | SyntaxKind::GlobalStatement
    )
}

/// The labels written in the function a node is in, not counting the ones in
/// lambdas and local functions inside it.
pub(crate) fn labels_in_function(node: &SyntaxNode) -> Vec<String> {
    let Some(root) = node
        .ancestors()
        .find(|ancestor| is_function_boundary(ancestor.kind()))
    else {
        return Vec::new();
    };
    let mut labels = Vec::new();
    let mut stack: Vec<SyntaxNode> = root.children().collect();
    while let Some(current) = stack.pop() {
        if is_function_boundary(current.kind()) {
            continue;
        }
        if current.kind() == SyntaxKind::LabeledStatement
            && let Some(token) = current
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        {
            labels.push(token.value_text().to_string());
        }
        stack.extend(current.children());
    }
    labels
}

/// The labels in a member's body that nothing jumps to by name, as the
/// label's own name. A jump reaches only the labels of the function it is
/// written in: a `goto` inside a lambda does not reference the method's.
fn unreferenced_labels(declaration: &SyntaxNode) -> Vec<TextSpan> {
    let mut labels = Vec::new();
    let mut named = HashSet::new();
    let mut stack = vec![declaration.clone()];
    while let Some(current) = stack.pop() {
        match current.kind() {
            SyntaxKind::LabeledStatement => {
                if let Some(token) = current
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    && !token.span().is_empty()
                {
                    labels.push((function_of(&current), token));
                }
            }
            SyntaxKind::GotoStatement
            | SyntaxKind::BreakStatement
            | SyntaxKind::ContinueStatement => {
                if let Some(token) = current
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                {
                    named.insert((function_of(&current), token.value_text().to_string()));
                }
            }
            // A type written in the body's file is a body of its own.
            SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::NamespaceDeclaration
            | SyntaxKind::FileScopedNamespaceDeclaration
                if current != *declaration =>
            {
                continue;
            }
            _ => {}
        }
        stack.extend(current.children());
    }
    let mut spans: Vec<TextSpan> = labels
        .into_iter()
        .filter(|(function, token)| !named.contains(&(*function, token.value_text().to_string())))
        .map(|(_, token)| token.span())
        .collect();
    spans.sort_by_key(|span| span.start());
    spans
}

/// Where the function a statement is in is written: its lambda, local
/// function or member.
fn function_of(node: &SyntaxNode) -> Option<TextSpan> {
    node.ancestors()
        .find(|ancestor| is_function_boundary(ancestor.kind()))
        .map(|function| function.span())
}
