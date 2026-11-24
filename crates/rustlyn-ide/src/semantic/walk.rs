//! Walking a bound body: every statement and expression in it, lambdas and
//! local functions included.
//!
//! The bound tree is what the binder decided, and several editor features
//! want to look at all of it: which cast was written, which operator a `+`
//! called, where a local is read. Each would otherwise carry its own copy of
//! the same forty-armed match, and each copy would forget a different arm.

use rustlyn_semantics::{
    BoundBody, BoundExpression, BoundExpressionKind as E, BoundPattern, BoundPatternKind as P,
    BoundStatement, BoundStatementKind as S, BoundSwitchLabel,
};

/// A node of the bound tree, as a walk meets it.
#[derive(Clone, Copy, Debug)]
pub(super) enum Visited<'a> {
    Statement(&'a BoundStatement),
    Expression(&'a BoundExpression),
}

/// Calls `visit` for every statement and expression of `body`, parents
/// before children, in source order within each. A lambda's body is walked
/// where the lambda is; local functions' bodies after everything else.
pub(super) fn walk_body<'a>(body: &'a BoundBody, visit: &mut dyn FnMut(Visited<'a>)) {
    for statement in &body.statements {
        walk_statement(body, statement, visit);
    }
    for function in &body.local_functions {
        walk_statement(body, &function.body, visit);
    }
}

pub(super) fn walk_statement<'a>(
    body: &'a BoundBody,
    statement: &'a BoundStatement,
    visit: &mut dyn FnMut(Visited<'a>),
) {
    visit(Visited::Statement(statement));
    let (statements, expressions) = statement_children(statement);
    // Source order: a statement's own expressions (a condition, an
    // initializer) come before the statements it holds, except where the
    // statement is a loop whose condition is written after its body.
    if matches!(statement.kind, S::DoWhile { .. }) {
        for child in statements {
            walk_statement(body, child, visit);
        }
        for child in expressions {
            walk_expression(body, child, visit);
        }
        return;
    }
    for child in expressions {
        walk_expression(body, child, visit);
    }
    for child in statements {
        walk_statement(body, child, visit);
    }
}

pub(super) fn walk_expression<'a>(
    body: &'a BoundBody,
    expression: &'a BoundExpression,
    visit: &mut dyn FnMut(Visited<'a>),
) {
    visit(Visited::Expression(expression));
    if let E::Lambda(index) = expression.kind
        && let Some(lambda) = body.lambdas.get(index)
    {
        walk_statement(body, &lambda.body, visit);
        return;
    }
    for child in expression_children(expression) {
        walk_expression(body, child, visit);
    }
}

/// The statements and expressions a statement holds directly.
pub(super) fn statement_children(
    statement: &BoundStatement,
) -> (Vec<&BoundStatement>, Vec<&BoundExpression>) {
    let mut statements: Vec<&BoundStatement> = Vec::new();
    let mut expressions: Vec<&BoundExpression> = Vec::new();
    match &statement.kind {
        S::Unsupported(_)
        | S::YieldBreak
        | S::Break(_)
        | S::Continue(_)
        | S::GotoCase(_)
        | S::Label(_)
        | S::Goto(_)
        | S::Empty => {}
        S::Block(inner) => statements.extend(inner),
        S::LocalDeclaration { initializer, .. } => expressions.extend(initializer),
        S::Expression(expression) | S::YieldReturn(expression) => expressions.push(expression),
        S::If {
            condition,
            consequence,
            alternative,
        } => {
            expressions.push(condition);
            statements.push(consequence);
            statements.extend(alternative.as_deref());
        }
        S::While { condition, body } => {
            expressions.push(condition);
            statements.push(body);
        }
        S::DoWhile { body, condition } => {
            statements.push(body);
            expressions.push(condition);
        }
        S::For {
            initializers,
            condition,
            incrementors,
            body,
        } => {
            statements.extend(initializers);
            expressions.extend(condition);
            expressions.extend(incrementors);
            statements.push(body);
        }
        S::ForEach {
            collection, body, ..
        } => {
            expressions.push(collection);
            statements.push(body);
        }
        S::ConstructorInitializer { arguments, .. } => expressions.extend(arguments),
        S::Switch {
            governing,
            sections,
        } => {
            expressions.push(governing);
            for section in sections {
                for label in &section.labels {
                    if let BoundSwitchLabel::Case(case) = label {
                        pattern_expressions(&case.pattern, &mut expressions);
                        expressions.extend(&case.when);
                    }
                }
                statements.extend(&section.statements);
            }
        }
        S::Try {
            body,
            catches,
            finally,
        } => {
            statements.push(body);
            for catch in catches {
                expressions.extend(&catch.filter);
                statements.push(&catch.body);
            }
            statements.extend(finally.as_deref());
        }
        S::Using { resources, body } => {
            expressions.extend(resources.iter().map(|resource| &resource.value));
            statements.push(body);
        }
        S::Lock { value, body, .. } => {
            expressions.push(value);
            statements.push(body);
        }
        S::Fixed { declarations, body } => {
            statements.extend(declarations);
            statements.push(body);
        }
        S::Return(value) | S::Throw(value) => expressions.extend(value),
    }
    (statements, expressions)
}

/// The expressions an expression holds directly.
pub(super) fn expression_children(expression: &BoundExpression) -> Vec<&BoundExpression> {
    let mut found: Vec<&BoundExpression> = Vec::new();
    match &expression.kind {
        E::Error
        | E::Unsupported(_)
        | E::Literal(_)
        | E::Local(_)
        | E::Parameter(_)
        | E::This
        | E::Base
        | E::TypeExpression(_)
        | E::NamespaceExpression(_)
        | E::UnboundLambda(_)
        | E::UnboundCollection(_)
        | E::UnboundCreation(_)
        | E::UnboundConditional(_)
        | E::UnboundSwitch(_)
        | E::Lambda(_)
        | E::SizeOf(_)
        | E::MethodAddress { .. }
        | E::AccessedValue
        | E::CreatedObject
        | E::TypeOf(_)
        | E::ArgListHandle
        | E::Default(_) => {}
        E::Field { receiver, .. }
        | E::Property { receiver, .. }
        | E::MethodGroup { receiver, .. }
        | E::DelegateCreation { receiver, .. } => found.extend(receiver.as_deref()),
        E::RefArgument { operand, .. }
        | E::Dereference { operand }
        | E::AddressOf { operand }
        | E::MakeRef(operand)
        | E::RefValue(operand)
        | E::RefType(operand)
        | E::Unary { operand, .. }
        | E::Conversion { operand, .. }
        | E::TypeTest { operand, .. }
        | E::TryCast { operand, .. }
        | E::Await { operand, .. } => found.push(operand),
        E::FunctionPointerCall { pointer, arguments } => {
            found.push(pointer);
            found.extend(arguments.iter());
        }
        E::Call {
            receiver,
            arguments,
            ..
        } => {
            found.extend(receiver.as_deref());
            found.extend(arguments);
        }
        E::ObjectCreation {
            arguments,
            initializers,
            ..
        } => {
            found.extend(arguments);
            found.extend(initializers);
        }
        E::With {
            receiver,
            initializers,
        } => {
            found.push(receiver);
            found.extend(initializers);
        }
        E::TupleCreation(items)
        | E::Sequence(items)
        | E::InterpolatedString(items)
        | E::ArgList(items) => {
            found.extend(items);
        }
        // The walk a spread became: what it walks and what it does are
        // expressions the source wrote, inside statements it did not.
        E::SpillSequence { statements, value } => {
            let mut pending: Vec<&BoundStatement> = statements.iter().rev().collect();
            while let Some(statement) = pending.pop() {
                let (inner, expressions) = statement_children(statement);
                found.extend(expressions);
                pending.extend(inner.into_iter().rev());
            }
            found.push(value);
        }
        E::Dynamic(operation) => {
            found.extend(operation.receiver.as_ref());
            found.extend(&operation.arguments);
        }
        E::StackAlloc {
            count, elements, ..
        } => {
            found.push(count);
            found.extend(elements);
        }
        E::Throw(value) => found.extend(value.as_deref()),
        E::ConditionalAccess { receiver, access } => {
            found.push(receiver);
            found.push(access);
        }
        E::ArrayCreation {
            lengths, elements, ..
        } => {
            found.extend(lengths);
            found.extend(elements);
        }
        E::ArrayAccess { array, indices } => {
            found.push(array);
            found.extend(indices);
        }
        E::ArrayLength { array } => found.push(array),
        E::IndexerAccess {
            receiver,
            arguments,
            ..
        } => {
            found.push(receiver);
            found.extend(arguments);
        }
        E::Binary { left, right, .. } => {
            found.push(left);
            found.push(right);
        }
        E::Conditional {
            condition,
            consequence,
            alternative,
        } => {
            found.push(condition);
            found.push(consequence);
            found.push(alternative);
        }
        E::Assignment { target, value } | E::CompoundAssignment { target, value, .. } => {
            found.push(target);
            found.push(value);
        }
        E::EventAssignment {
            receiver, handler, ..
        } => {
            found.extend(receiver.as_deref());
            found.push(handler);
        }
        E::Increment { target, .. } => found.push(target),
        E::StringInsert { value, .. } => found.push(value),
        E::IsPattern { operand, pattern } => {
            found.push(operand);
            pattern_expressions(pattern, &mut found);
        }
        E::Switch { governing, arms } => {
            found.push(governing);
            for arm in arms {
                pattern_expressions(&arm.pattern, &mut found);
                found.extend(&arm.when);
                found.push(&arm.value);
            }
        }
    }
    found
}

/// The expressions a pattern holds: constants, and what a `var (a, b)`
/// takes apart.
pub(super) fn pattern_expressions<'a>(
    pattern: &'a BoundPattern,
    found: &mut Vec<&'a BoundExpression>,
) {
    match &pattern.kind {
        P::Unsupported(_) | P::Discard | P::Var { .. } | P::Type(_) | P::Declaration { .. } => {}
        P::VarDeconstruct { deconstruction, .. } => found.push(deconstruction),
        P::Constant(value) | P::Relational { value, .. } => found.push(value),
        // The string it compares with is inside the call.
        P::SpanString { test, .. } => found.push(test),
        P::Recursive(recursive) => {
            for (_, inner) in &recursive.properties {
                pattern_expressions(inner, found);
            }
            for inner in &recursive.positional {
                pattern_expressions(inner, found);
            }
        }
        P::List(list) => {
            for inner in list.patterns() {
                pattern_expressions(inner, found);
            }
        }
        P::And(a, b) | P::Or(a, b) => {
            pattern_expressions(a, found);
            pattern_expressions(b, found);
        }
        P::Not(inner) | P::UnionCase { inner, .. } => pattern_expressions(inner, found),
    }
}

/// The first expression of `body` whose span is `span` and that `accept`
/// takes: the call a `+` became, the object a `new()` made.
pub(super) fn find_expression<'a>(
    body: &'a BoundBody,
    accept: &dyn Fn(&BoundExpression) -> bool,
) -> Option<&'a BoundExpression> {
    let mut found = None;
    walk_body(body, &mut |visited| {
        if found.is_none()
            && let Visited::Expression(expression) = visited
            && accept(expression)
        {
            found = Some(expression);
        }
    });
    found
}
