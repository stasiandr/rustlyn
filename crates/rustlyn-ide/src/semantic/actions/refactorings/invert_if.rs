//! Invert if: negate the condition and swap what runs in each case.
//!
//! Roslyn's `InvertIf`. With an `else`, the two branches change places.
//! Without one, an `if` that is the last thing a method (or a loop body)
//! does becomes an early exit — `if (!c) return;` (or `continue;`) — and
//! what it guarded follows it, one level further out.
//!
//! The condition is negated the way a person would: `==` becomes `!=`, `<`
//! becomes `>=`, `!x` becomes `x`, `is null` becomes `is not null`, and
//! `&&` and `||` swap by De Morgan's laws with each side negated in turn.
//! Comparisons of floating-point values are wrapped in `!( )` instead: with
//! a NaN on one side, `!(a < b)` and `a >= b` are different answers.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::text::{precedence, reindent, skip_parentheses, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use super::expression_body::{block, returns_nothing};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(statement) = if_at_cursor(context) else {
        return;
    };
    if let Some(edits) = invert(context, &statement) {
        found.push(context.local("Invert if", ActionKind::Rewrite, None, edits));
    }
}

/// The `if` whose header — the keyword to the closing parenthesis — the
/// cursor is in.
pub(super) fn if_at_cursor(context: &Context<'_, '_>) -> Option<SyntaxNode> {
    let token = context.token_at_cursor()?;
    let statement = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| node.kind() == SyntaxKind::IfStatement)?;
    let close = statement.child_token_of_kind(SyntaxKind::CloseParenToken)?;
    let span = context.trimmed_span();
    (span.start() >= statement.span().start() && span.start() <= close.span().end())
        .then_some(statement)
}

fn invert(context: &mut Context<'_, '_>, statement: &SyntaxNode) -> Option<Vec<TextEdit>> {
    let condition = statement
        .children()
        .find(|child| child.kind().is_expression())?;
    let consequence = statement
        .children()
        .find(|child| super::super::text::is_statement(child.kind()))?;
    let (negated, _) = negate(context, &condition)?;

    if let Some(clause) = statement.child_of_kind(SyntaxKind::ElseClause) {
        let alternative = clause.children().next()?;
        if alternative.kind() == SyntaxKind::IfStatement {
            return None;
        }
        return Some(vec![
            TextEdit::new(condition.span(), negated),
            TextEdit::new(consequence.span(), alternative.text()),
            TextEdit::new(alternative.span(), consequence.text()),
        ]);
    }

    // No `else`: the early exit, when the `if` is the last thing done.
    let block_node = statement.parent()?;
    if block_node.kind() != SyntaxKind::Block || statements_of(block_node).last() != Some(statement)
    {
        return None;
    }
    let owner = block_node.parent()?;
    let jump = match owner.kind() {
        SyntaxKind::WhileStatement
        | SyntaxKind::DoStatement
        | SyntaxKind::ForStatement
        | SyntaxKind::ForEachStatement
        | SyntaxKind::ForEachVariableStatement => "continue;",
        _ if returns_nothing(context, owner) == Some(true) => "return;",
        _ => return None,
    };
    let indent = context.indentation_at(statement.span().start());
    let newline = context.newline();
    let (body, from) = if consequence.kind() == SyntaxKind::Block {
        let inner = statements_of(&consequence);
        let (first, last) = (inner.first()?, inner.last()?);
        let span = rustlyn_text::TextSpan::from_bounds(first.span().start(), last.span().end());
        (
            context.slice(span).to_string(),
            context.indentation_at(first.span().start()),
        )
    } else {
        (
            consequence.text(),
            format!("{indent}{}", context.indent_unit()),
        )
    };
    let body = reindent(&body, &from, &indent);
    let exit = if consequence.kind() == SyntaxKind::Block {
        block(context, &indent, jump)
    } else {
        format!(" {jump}")
    };
    Some(vec![TextEdit::new(
        statement.span(),
        format!("if ({negated}){exit}{newline}{indent}{body}"),
    )])
}

/// `node`, a condition, negated; with the kind of expression the result
/// is, which says where it needs parentheses.
pub(super) fn negate(
    context: &mut Context<'_, '_>,
    node: &SyntaxNode,
) -> Option<(String, SyntaxKind)> {
    use SyntaxKind as K;
    let children: Vec<SyntaxNode> = node.children().collect();
    Some(match node.kind() {
        K::ParenthesizedExpression => {
            let (text, kind) = negate(context, children.first()?)?;
            if precedence(kind) >= precedence(K::LogicalNotExpression) {
                (text, kind)
            } else {
                (format!("({text})"), K::ParenthesizedExpression)
            }
        }
        K::LogicalNotExpression => {
            let operand = skip_parentheses(children.first()?);
            (operand.text(), operand.kind())
        }
        K::TrueLiteralExpression => ("false".to_string(), K::FalseLiteralExpression),
        K::FalseLiteralExpression => ("true".to_string(), K::TrueLiteralExpression),
        K::LogicalAndExpression | K::LogicalOrExpression => {
            let (joined, result) = if node.kind() == K::LogicalAndExpression {
                ("||", K::LogicalOrExpression)
            } else {
                ("&&", K::LogicalAndExpression)
            };
            let (left, left_kind) = negate(context, children.first()?)?;
            let (right, right_kind) = negate(context, children.get(1)?)?;
            let wrap = |text: String, kind: K| {
                if precedence(kind) < precedence(result) {
                    format!("({text})")
                } else {
                    text
                }
            };
            (
                format!(
                    "{} {joined} {}",
                    wrap(left, left_kind),
                    wrap(right, right_kind)
                ),
                result,
            )
        }
        K::EqualsExpression | K::NotEqualsExpression => {
            let operator = if node.kind() == K::EqualsExpression {
                "!="
            } else {
                "=="
            };
            let result = if node.kind() == K::EqualsExpression {
                K::NotEqualsExpression
            } else {
                K::EqualsExpression
            };
            (
                format!(
                    "{} {operator} {}",
                    children.first()?.text(),
                    children.get(1)?.text()
                ),
                result,
            )
        }
        K::LessThanExpression
        | K::LessThanOrEqualExpression
        | K::GreaterThanExpression
        | K::GreaterThanOrEqualExpression
            if !children
                .iter()
                .any(|operand| may_be_floating(context, operand)) =>
        {
            let (operator, result) = match node.kind() {
                K::LessThanExpression => (">=", K::GreaterThanOrEqualExpression),
                K::LessThanOrEqualExpression => (">", K::GreaterThanExpression),
                K::GreaterThanExpression => ("<=", K::LessThanOrEqualExpression),
                _ => ("<", K::LessThanExpression),
            };
            (
                format!(
                    "{} {operator} {}",
                    children.first()?.text(),
                    children.get(1)?.text()
                ),
                result,
            )
        }
        K::IsPatternExpression => {
            let operand = children.first()?;
            let pattern = children.get(1)?;
            let negated = if pattern.kind() == K::NotPattern {
                pattern.children().next()?.text()
            } else {
                format!("not {}", pattern.text())
            };
            (
                format!("{} is {negated}", operand.text()),
                K::IsPatternExpression,
            )
        }
        K::IsExpression => (
            format!(
                "{} is not {}",
                children.first()?.text(),
                children.get(1)?.text()
            ),
            K::IsPatternExpression,
        ),
        kind => {
            let text = node.text();
            if precedence(kind) >= precedence(K::LogicalNotExpression) {
                (format!("!{text}"), K::LogicalNotExpression)
            } else {
                (format!("!({text})"), K::LogicalNotExpression)
            }
        }
    })
}

/// Whether an operand could be a `float` or a `double`, whose comparisons
/// are not each other's negations.
fn may_be_floating(context: &mut Context<'_, '_>, node: &SyntaxNode) -> bool {
    let Some(ty) = context.view.expression_type(node) else {
        return true;
    };
    let ty = match ty {
        Type::Named {
            symbol,
            type_arguments,
        } if context.view.compiled().symbols().qualified_name(symbol) == "System.Nullable`1"
            && type_arguments.len() == 1 =>
        {
            type_arguments[0].clone()
        }
        other => other,
    };
    match ty {
        Type::Named { symbol, .. } => {
            let name = context.view.compiled().symbols().qualified_name(symbol);
            matches!(name.as_str(), "System.Single" | "System.Double")
        }
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn the_branches_swap_and_the_condition_negates() {
        let source = "class C\n{\n    void M(int a, bool b)\n    {\n        $$if (a == 1 && !b)\n        {\n            System.Console.WriteLine(1);\n        }\n        else\n        {\n            System.Console.WriteLine(2);\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Invert if"),
            "class C\n{\n    void M(int a, bool b)\n    {\n        if (a != 1 || b)\n        {\n            System.Console.WriteLine(2);\n        }\n        else\n        {\n            System.Console.WriteLine(1);\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn comparisons_flip_unless_they_are_floating() {
        let source = "class C\n{\n    int M(int a, double d, object o)\n    {\n        $$if (a < 3 || d > 1.0 || o is null) return 1; else return 2;\n    }\n}\n";
        assert_eq!(
            apply(source, "Invert if"),
            "class C\n{\n    int M(int a, double d, object o)\n    {\n        if (a >= 3 && !(d > 1.0) && o is not null) return 2; else return 1;\n    }\n}\n"
        );
    }

    #[test]
    fn a_last_if_becomes_an_early_return() {
        let source = "class C\n{\n    void M(string s)\n    {\n        System.Console.WriteLine(0);\n        $$if (s != null)\n        {\n            System.Console.WriteLine(s);\n            System.Console.WriteLine(1);\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Invert if"),
            "class C\n{\n    void M(string s)\n    {\n        System.Console.WriteLine(0);\n        if (s == null)\n        {\n            return;\n        }\n        System.Console.WriteLine(s);\n        System.Console.WriteLine(1);\n    }\n}\n"
        );
    }

    #[test]
    fn in_a_loop_it_continues() {
        let source = "class C\n{\n    void M(int[] items)\n    {\n        foreach (var item in items)\n        {\n            $$if (item > 0) System.Console.WriteLine(item);\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Invert if"),
            "class C\n{\n    void M(int[] items)\n    {\n        foreach (var item in items)\n        {\n            if (item <= 0) continue;\n            System.Console.WriteLine(item);\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn an_if_with_code_after_it_and_no_else_stays() {
        refuses(
            "class C\n{\n    void M(bool b)\n    {\n        $$if (b) System.Console.WriteLine(1);\n        System.Console.WriteLine(2);\n    }\n}\n",
            "Invert if",
        );
    }
}
