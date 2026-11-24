//! Null checks written the short way: `??`, `??=`, `?.` and `throw`
//! expressions.
//!
//! Roslyn reports these as hidden (or suggestion) code-style diagnostics
//! and fixes them from the light bulb wherever the pattern is; here they
//! are refactorings offered with the cursor anywhere in the code the
//! diagnostic would cover, under the titles of Roslyn's fixes:
//!
//! * "Use coalesce expression" (IDE0029, IDE0030): `x != null ? x : y`,
//!   `x == null ? y : x` and `x.HasValue ? x.Value : y` become `x ?? y`;
//! * "Use compound assignment" (IDE0074): `x = x ?? y` and
//!   `if (x == null) x = y;` become `x ??= y`;
//! * "Use null propagation" (IDE0031): `x != null ? x.M() : null` and
//!   `if (x != null) x.M();` become `x?.M()`; a delegate called that way,
//!   `if (h != null) h(a);`, becomes `h?.Invoke(a);` — "Delegate invocation
//!   can be simplified." (IDE1005);
//! * "Use 'throw' expression" (IDE0016): `if (x == null) throw ...;`
//!   followed by `field = x;` becomes `field = x ?? throw ...;`.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    parenthesized_for, precedence, same_tokens, skip_parentheses, statements_of,
};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let around: Vec<SyntaxNode> = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| !super::super::text::is_member(node.kind()))
        .collect();
    let mut offered = |title: &str, edits: Vec<TextEdit>| {
        if !found.iter().any(|action| action.title == title) {
            found.push(context.local(title, ActionKind::Rewrite, None, edits));
        }
    };
    if let Some(conditional) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::ConditionalExpression)
    {
        if let Some(edit) = coalesce(conditional) {
            offered("Use coalesce expression", vec![edit]);
        }
        if let Some(edit) = propagate(conditional) {
            offered("Use null propagation", vec![edit]);
        }
    }
    if let Some(assignment) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::SimpleAssignmentExpression)
        && let Some(edit) = coalesce_assignment(assignment)
    {
        offered("Use compound assignment", vec![edit]);
    }
    if let Some(statement) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::IfStatement)
    {
        if let Some(edit) = assign_if_null(statement) {
            offered("Use compound assignment", vec![edit]);
        }
        if let Some((title, edit)) = call_if_not_null(statement) {
            offered(title, vec![edit]);
        }
        if let Some(edits) = throw_expression(statement) {
            offered("Use 'throw' expression", edits);
        }
    }
}

/// What a null test tests, and whether it is `== null` (or `is null`)
/// rather than `!= null` (or `is not null`).
pub(super) fn null_test(node: &SyntaxNode) -> Option<(SyntaxNode, bool)> {
    let node = skip_parentheses(node);
    let is_null =
        |node: &SyntaxNode| skip_parentheses(node).kind() == SyntaxKind::NullLiteralExpression;
    match node.kind() {
        SyntaxKind::EqualsExpression | SyntaxKind::NotEqualsExpression => {
            let mut sides = node.children();
            let (left, right) = (sides.next()?, sides.next()?);
            let tested = if is_null(&right) {
                left
            } else if is_null(&left) {
                right
            } else {
                return None;
            };
            Some((tested, node.kind() == SyntaxKind::EqualsExpression))
        }
        SyntaxKind::IsPatternExpression => {
            let mut parts = node.children();
            let (tested, pattern) = (parts.next()?, parts.next()?);
            match pattern.kind() {
                SyntaxKind::ConstantPattern
                    if pattern
                        .children()
                        .next()
                        .is_some_and(|value| is_null(&value)) =>
                {
                    Some((tested, true))
                }
                SyntaxKind::NotPattern => {
                    let inner = pattern.children().next()?;
                    (inner.kind() == SyntaxKind::ConstantPattern
                        && inner.children().next().is_some_and(|value| is_null(&value)))
                    .then_some((tested, false))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The three parts of `c ? a : b`.
fn parts(conditional: &SyntaxNode) -> Option<(SyntaxNode, SyntaxNode, SyntaxNode)> {
    let mut children = conditional.children();
    Some((children.next()?, children.next()?, children.next()?))
}

/// `left ?? right` written in place of `at`, each side in parentheses when
/// it binds more loosely than `??` does there.
fn coalesced(left: &SyntaxNode, right: &SyntaxNode, at: &SyntaxNode) -> String {
    let left_text = if precedence(skip_parentheses(left).kind())
        <= precedence(SyntaxKind::CoalesceExpression)
    {
        format!("({})", skip_parentheses(left).text())
    } else {
        skip_parentheses(left).text()
    };
    let right_inner = skip_parentheses(right);
    let right_text = if precedence(right_inner.kind()) < precedence(SyntaxKind::CoalesceExpression)
        && right_inner.kind() != SyntaxKind::ThrowExpression
    {
        format!("({})", right_inner.text())
    } else {
        right_inner.text()
    };
    parenthesized_for(
        &format!("{left_text} ?? {right_text}"),
        SyntaxKind::CoalesceExpression,
        at,
    )
}

/// `x != null ? x : y` → `x ?? y`; `x.HasValue ? x.Value : y` → `x ?? y`.
fn coalesce(conditional: &SyntaxNode) -> Option<TextEdit> {
    let (condition, when_true, when_false) = parts(conditional)?;
    let (value, other) = if let Some((tested, is_equal)) = null_test(&condition) {
        let (value, other) = if is_equal {
            (when_false, when_true)
        } else {
            (when_true, when_false)
        };
        if !same_tokens(&skip_parentheses(&value), &skip_parentheses(&tested)) {
            return None;
        }
        (tested, other)
    } else {
        // `x.HasValue ? x.Value : y`, or with `!` and the branches swapped.
        let condition = skip_parentheses(&condition);
        let (access, negated) = if condition.kind() == SyntaxKind::LogicalNotExpression {
            (skip_parentheses(&condition.children().next()?), true)
        } else {
            (condition, false)
        };
        let nullable = member_of(&access, "HasValue")?;
        let (value, other) = if negated {
            (when_false, when_true)
        } else {
            (when_true, when_false)
        };
        let read = member_of(&skip_parentheses(&value), "Value")?;
        if !same_tokens(&read, &nullable) {
            return None;
        }
        (nullable, other)
    };
    if skip_parentheses(&other).kind() == SyntaxKind::NullLiteralExpression {
        return None;
    }
    Some(TextEdit::new(
        conditional.span(),
        coalesced(&value, &other, conditional),
    ))
}

/// `x` of `x.Name`.
fn member_of(node: &SyntaxNode, name: &str) -> Option<SyntaxNode> {
    if node.kind() != SyntaxKind::SimpleMemberAccessExpression {
        return None;
    }
    let mut children = node.children();
    let (receiver, member) = (children.next()?, children.next()?);
    (member.text() == name).then_some(receiver)
}

/// `x != null ? x.M() : null` → `x?.M()`.
fn propagate(conditional: &SyntaxNode) -> Option<TextEdit> {
    let (condition, when_true, when_false) = parts(conditional)?;
    let (tested, is_equal) = null_test(&condition)?;
    let (access, other) = if is_equal {
        (when_false, when_true)
    } else {
        (when_true, when_false)
    };
    if skip_parentheses(&other).kind() != SyntaxKind::NullLiteralExpression {
        return None;
    }
    let rewritten = propagated(&skip_parentheses(&access), &skip_parentheses(&tested))?;
    Some(TextEdit::new(
        conditional.span(),
        parenthesized_for(
            &rewritten,
            SyntaxKind::ConditionalAccessExpression,
            conditional,
        ),
    ))
}

/// `access`, a chain of member accesses, calls and indexing that starts
/// with `tested`, with `?` after `tested`: `x.A.B()` → `x?.A.B()`.
fn propagated(access: &SyntaxNode, tested: &SyntaxNode) -> Option<String> {
    let mut current = access.clone();
    loop {
        let receiver = match current.kind() {
            SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::InvocationExpression
            | SyntaxKind::ElementAccessExpression => current.children().next()?,
            _ => return None,
        };
        if same_tokens(&skip_parentheses(&receiver), tested) {
            // `x()` of a delegate has no `.` to put `?` before.
            if current.kind() == SyntaxKind::InvocationExpression {
                return None;
            }
            let text = access.text();
            let start = (receiver.span().end() - access.span().start()) as usize;
            let receiver_text = skip_parentheses(&receiver).text();
            return Some(format!("{receiver_text}?{}", &text[start..]));
        }
        current = receiver;
    }
}

/// `x = x ?? y` → `x ??= y`.
fn coalesce_assignment(assignment: &SyntaxNode) -> Option<TextEdit> {
    let mut children = assignment.children();
    let (target, value) = (children.next()?, children.next()?);
    let value = skip_parentheses(&value);
    if value.kind() != SyntaxKind::CoalesceExpression {
        return None;
    }
    let mut sides = value.children();
    let (left, right) = (sides.next()?, sides.next()?);
    if !same_tokens(&skip_parentheses(&left), &target) {
        return None;
    }
    Some(TextEdit::new(
        assignment.span(),
        format!("{} ??= {}", target.text(), right.text()),
    ))
}

/// The one statement an `if` without `else` runs: itself, or the only
/// statement of its block.
fn only_statement(statement: &SyntaxNode) -> Option<(SyntaxNode, SyntaxNode)> {
    if statement.child_of_kind(SyntaxKind::ElseClause).is_some() {
        return None;
    }
    let mut children = statement.children();
    let condition = children.next()?;
    let body = children.next()?;
    let body = if body.kind() == SyntaxKind::Block {
        let statements = statements_of(&body);
        let [only] = statements.as_slice() else {
            return None;
        };
        only.clone()
    } else {
        body
    };
    Some((condition, body))
}

/// `if (x == null) x = y;` → `x ??= y;`.
fn assign_if_null(statement: &SyntaxNode) -> Option<TextEdit> {
    let (condition, body) = only_statement(statement)?;
    let (tested, is_equal) = null_test(&condition)?;
    if !is_equal || body.kind() != SyntaxKind::ExpressionStatement {
        return None;
    }
    let assignment = body.children().next()?;
    if assignment.kind() != SyntaxKind::SimpleAssignmentExpression {
        return None;
    }
    let mut children = assignment.children();
    let (target, value) = (children.next()?, children.next()?);
    if !same_tokens(&target, &skip_parentheses(&tested)) {
        return None;
    }
    Some(TextEdit::new(
        statement.span(),
        format!("{} ??= {};", target.text(), value.text()),
    ))
}

/// `if (x != null) x.M();` → `x?.M();`, and `if (h != null) h(a);` →
/// `h?.Invoke(a);`.
fn call_if_not_null(statement: &SyntaxNode) -> Option<(&'static str, TextEdit)> {
    let (condition, body) = only_statement(statement)?;
    let (tested, is_equal) = null_test(&condition)?;
    if is_equal || body.kind() != SyntaxKind::ExpressionStatement {
        return None;
    }
    let call = body.children().next()?;
    if call.kind() != SyntaxKind::InvocationExpression {
        return None;
    }
    let tested = skip_parentheses(&tested);
    let callee = call.children().next()?;
    if same_tokens(&callee, &tested) {
        let arguments = call.child_of_kind(SyntaxKind::ArgumentList)?.text();
        return Some((
            "Delegate invocation can be simplified.",
            TextEdit::new(
                statement.span(),
                format!("{}?.Invoke{arguments};", tested.text()),
            ),
        ));
    }
    let rewritten = propagated(&call, &tested)?;
    Some((
        "Use null propagation",
        TextEdit::new(statement.span(), format!("{rewritten};")),
    ))
}

/// `if (x == null) throw e;` followed by an assignment of `x` → the
/// assignment of `x ?? throw e`.
fn throw_expression(statement: &SyntaxNode) -> Option<Vec<TextEdit>> {
    let (condition, body) = only_statement(statement)?;
    let (tested, is_equal) = null_test(&condition)?;
    let tested = skip_parentheses(&tested);
    if !is_equal
        || body.kind() != SyntaxKind::ThrowStatement
        || tested.kind() != SyntaxKind::IdentifierName
    {
        return None;
    }
    let thrown = body.children().next()?;
    let block = statement.parent()?;
    let statements = statements_of(block);
    let at = statements.iter().position(|other| other == statement)?;
    let next = statements.get(at + 1)?;
    if next.kind() != SyntaxKind::ExpressionStatement {
        return None;
    }
    let assignment = next.children().next()?;
    if assignment.kind() != SyntaxKind::SimpleAssignmentExpression {
        return None;
    }
    let value = assignment.children().nth(1)?;
    if !same_tokens(&skip_parentheses(&value), &tested) {
        return None;
    }
    // The `if` goes with its line; the assignment takes the check.
    let removed = TextSpan::from_bounds(statement.span().start(), next.span().start());
    Some(vec![
        TextEdit::delete(removed),
        TextEdit::new(
            value.span(),
            format!("{} ?? throw {}", tested.text(), thrown.text()),
        ),
    ])
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn a_conditional_null_check_becomes_coalesce() {
        let source = "class C\n{\n    string M(string a, string b) => a != null $$? a : b;\n}\n";
        assert_eq!(
            apply(source, "Use coalesce expression"),
            "class C\n{\n    string M(string a, string b) => a ?? b;\n}\n"
        );
        let source = "class C\n{\n    int M(int? a) => $$a.HasValue ? a.Value : 0;\n}\n";
        assert_eq!(
            apply(source, "Use coalesce expression"),
            "class C\n{\n    int M(int? a) => a ?? 0;\n}\n"
        );
        refuses(
            "class C\n{\n    string M(string a, string b) => a != null $$? b : a;\n}\n",
            "Use coalesce expression",
        );
    }

    #[test]
    fn assigning_when_null_becomes_coalesce_assignment() {
        let source = "class C\n{\n    string name;\n    void M()\n    {\n        $$if (name == null)\n        {\n            name = \"none\";\n        }\n        name = name ?? \"x\";\n    }\n}\n";
        assert_eq!(
            apply(source, "Use compound assignment"),
            "class C\n{\n    string name;\n    void M()\n    {\n        name ??= \"none\";\n        name = name ?? \"x\";\n    }\n}\n"
        );
        let source = "class C\n{\n    string name;\n    void M() { name = $$name ?? \"x\"; }\n}\n";
        assert_eq!(
            apply(source, "Use compound assignment"),
            "class C\n{\n    string name;\n    void M() { name ??= \"x\"; }\n}\n"
        );
    }

    #[test]
    fn a_guarded_access_propagates_null() {
        let source = "class C\n{\n    string Name;\n    string M(C c) => c != null $$? c.Name.Trim() : null;\n}\n";
        assert_eq!(
            apply(source, "Use null propagation"),
            "class C\n{\n    string Name;\n    string M(C c) => c?.Name.Trim();\n}\n"
        );
        let source = "class C\n{\n    void Run() { }\n    void M(C c, System.Action done)\n    {\n        $$if (c != null) c.Run();\n        if (done != null)\n        {\n            done();\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Use null propagation"),
            "class C\n{\n    void Run() { }\n    void M(C c, System.Action done)\n    {\n        c?.Run();\n        if (done != null)\n        {\n            done();\n        }\n    }\n}\n"
        );
        let source = source
            .replace("$$if (c", "if (c")
            .replace("if (done", "$$if (done");
        assert_eq!(
            apply(&source, "Delegate invocation can be simplified."),
            "class C\n{\n    void Run() { }\n    void M(C c, System.Action done)\n    {\n        if (c != null) c.Run();\n        done?.Invoke();\n    }\n}\n"
        );
    }

    #[test]
    fn a_throwing_check_moves_into_the_assignment() {
        let source = "class C\n{\n    string name;\n    C(string value)\n    {\n        $$if (value == null) throw new System.ArgumentNullException(nameof(value));\n        name = value;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use 'throw' expression"),
            "class C\n{\n    string name;\n    C(string value)\n    {\n        name = value ?? throw new System.ArgumentNullException(nameof(value));\n    }\n}\n"
        );
    }
}
