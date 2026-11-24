//! Expressions written the short way: compound assignments, `^` and `..`,
//! and conditions without a `? true : false` around them.
//!
//! Roslyn's code styles, offered with the cursor in the code they rewrite:
//!
//! * "Use compound assignment" (IDE0054): `x = x + y` becomes `x += y`, and
//!   `x = x + 1` as a statement becomes `x++`;
//! * "Use index operator" (IDE0056): `a[a.Length - 1]` and
//!   `list[list.Count - 2]` become `a[^1]` and `list[^2]`;
//! * "Use range operator" (IDE0057): `s.Substring(1)` becomes `s[1..]`,
//!   `s.Substring(0, n)` becomes `s[..n]` and `s.Substring(i, s.Length -
//!   i)` becomes `s[i..]` — where the compilation has `System.Range`;
//! * "Simplify conditional expression" (IDE0075): `c ? true : false`
//!   becomes `c`, `c ? false : true` becomes `!c`, `c ? true : x` becomes
//!   `c || x` and `c ? x : false` becomes `c && x`;
//! * "Remove redundant equality" (IDE0100): `b == true` becomes `b`, `b ==
//!   false` becomes `!b`.

use rustlyn_semantics::{SpecialType, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::text::{parenthesized_for, precedence, same_tokens, skip_parentheses};
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
    let mut push = |context: &Context<'_, '_>, title: &str, edit: TextEdit| {
        if !found.iter().any(|action| action.title == title) {
            found.push(context.local(title, ActionKind::Rewrite, None, vec![edit]));
        }
    };
    for node in &around {
        match node.kind() {
            SyntaxKind::SimpleAssignmentExpression => {
                if let Some(edit) = compound(node) {
                    push(context, "Use compound assignment", edit);
                }
            }
            SyntaxKind::ElementAccessExpression => {
                if let Some(edit) = index_from_end(context, node) {
                    push(context, "Use index operator", edit);
                }
            }
            SyntaxKind::InvocationExpression => {
                if let Some(edit) = range(context, node) {
                    push(context, "Use range operator", edit);
                }
            }
            SyntaxKind::ConditionalExpression => {
                if let Some(edit) = simplified_conditional(context, node) {
                    push(context, "Simplify conditional expression", edit);
                }
            }
            SyntaxKind::EqualsExpression | SyntaxKind::NotEqualsExpression => {
                if let Some(edit) = redundant_equality(context, node) {
                    push(context, "Remove redundant equality", edit);
                }
            }
            _ => {}
        }
    }
}

/// The compound operator for a binary one.
fn compound_operator(kind: SyntaxKind) -> Option<&'static str> {
    Some(match kind {
        SyntaxKind::AddExpression => "+=",
        SyntaxKind::SubtractExpression => "-=",
        SyntaxKind::MultiplyExpression => "*=",
        SyntaxKind::DivideExpression => "/=",
        SyntaxKind::ModuloExpression => "%=",
        SyntaxKind::BitwiseAndExpression => "&=",
        SyntaxKind::BitwiseOrExpression => "|=",
        SyntaxKind::ExclusiveOrExpression => "^=",
        SyntaxKind::LeftShiftExpression => "<<=",
        SyntaxKind::RightShiftExpression => ">>=",
        _ => return None,
    })
}

/// `x = x + y` → `x += y`; `x = x + 1;` → `x++;`.
fn compound(assignment: &SyntaxNode) -> Option<TextEdit> {
    let mut sides = assignment.children();
    let (target, value) = (sides.next()?, skip_parentheses(&sides.next()?));
    let operator = compound_operator(value.kind())?;
    let mut operands = value.children();
    let (left, right) = (operands.next()?, operands.next()?);
    if !same_tokens(&skip_parentheses(&left), &target) {
        return None;
    }
    let is_statement = assignment
        .parent()
        .is_some_and(|parent| parent.kind() == SyntaxKind::ExpressionStatement);
    let right_text = skip_parentheses(&right).text();
    if is_statement && right_text == "1" {
        match operator {
            "+=" => {
                return Some(TextEdit::new(
                    assignment.span(),
                    format!("{}++", target.text()),
                ));
            }
            "-=" => {
                return Some(TextEdit::new(
                    assignment.span(),
                    format!("{}--", target.text()),
                ));
            }
            _ => {}
        }
    }
    Some(TextEdit::new(
        assignment.span(),
        format!("{} {operator} {}", target.text(), right.text()),
    ))
}

/// `a[a.Length - k]` → `a[^k]`.
fn index_from_end(context: &mut Context<'_, '_>, access: &SyntaxNode) -> Option<TextEdit> {
    context
        .view
        .compiled()
        .type_by_metadata_name("System.Index")?;
    let receiver = access.children().next()?;
    if !matches!(
        receiver.kind(),
        SyntaxKind::IdentifierName
            | SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::ThisExpression
    ) {
        return None;
    }
    let list = access.child_of_kind(SyntaxKind::BracketedArgumentList)?;
    let arguments: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
        .collect();
    let [argument] = arguments.as_slice() else {
        return None;
    };
    let value = skip_parentheses(&argument.children().last()?);
    if value.kind() != SyntaxKind::SubtractExpression {
        return None;
    }
    let mut sides = value.children();
    let (length, from_end) = (skip_parentheses(&sides.next()?), sides.next()?);
    if length.kind() != SyntaxKind::SimpleMemberAccessExpression {
        return None;
    }
    let mut parts = length.children();
    let (of, member) = (parts.next()?, parts.next()?);
    if !matches!(member.text().as_str(), "Length" | "Count")
        || !same_tokens(&skip_parentheses(&of), &receiver)
    {
        return None;
    }
    // Only where the receiver is indexed by `int` and counts: an array, a
    // string, a list.
    let ty = context.view.expression_type(&receiver)?;
    let countable = match &ty {
        Type::Array { rank, .. } => *rank == 1,
        Type::Named { symbol, .. } => {
            let symbols = context.view.compiled().symbols();
            let name = symbols.qualified_name(*symbol);
            name == SpecialType::String.metadata_name()
                || name == "System.Collections.Generic.List`1"
        }
        _ => false,
    };
    if !countable {
        return None;
    }
    let from_end_text =
        parenthesized_for(&from_end.text(), skip_parentheses(&from_end).kind(), &value);
    let from_end_text = if precedence(skip_parentheses(&from_end).kind())
        < precedence(SyntaxKind::IndexExpression)
    {
        format!("({})", skip_parentheses(&from_end).text())
    } else {
        from_end_text
    };
    Some(TextEdit::new(value.span(), format!("^{from_end_text}")))
}

/// `s.Substring(i)` → `s[i..]`; `s.Substring(0, n)` → `s[..n]`;
/// `s.Substring(i, s.Length - i)` → `s[i..]`.
fn range(context: &mut Context<'_, '_>, call: &SyntaxNode) -> Option<TextEdit> {
    context
        .view
        .compiled()
        .type_by_metadata_name("System.Range")?;
    let callee = call.children().next()?;
    if callee.kind() != SyntaxKind::SimpleMemberAccessExpression {
        return None;
    }
    let mut parts = callee.children();
    let (receiver, name) = (parts.next()?, parts.next()?);
    if name.text() != "Substring"
        || !matches!(
            receiver.kind(),
            SyntaxKind::IdentifierName
                | SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::ThisExpression
        )
    {
        return None;
    }
    let ty = context.view.expression_type(&receiver)?;
    let is_string = ty.symbol().is_some_and(|symbol| {
        context.view.compiled().symbols().qualified_name(symbol)
            == SpecialType::String.metadata_name()
    });
    if !is_string {
        return None;
    }
    let arguments: Vec<SyntaxNode> = call
        .child_of_kind(SyntaxKind::ArgumentList)?
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
        .filter_map(|argument| argument.children().last())
        .collect();
    let bound = |node: &SyntaxNode| {
        if precedence(skip_parentheses(node).kind()) <= precedence(SyntaxKind::RangeExpression) {
            format!("({})", skip_parentheses(node).text())
        } else {
            node.text()
        }
    };
    let range = match arguments.as_slice() {
        [start] => format!("{}..", bound(start)),
        [start, length] if skip_parentheses(start).text() == "0" => format!("..{}", bound(length)),
        [start, length] => {
            // `s.Length - start`
            let length = skip_parentheses(length);
            if length.kind() != SyntaxKind::SubtractExpression {
                return None;
            }
            let mut sides = length.children();
            let (whole, subtracted) = (skip_parentheses(&sides.next()?), sides.next()?);
            let is_length = whole.kind() == SyntaxKind::SimpleMemberAccessExpression
                && whole
                    .children()
                    .nth(1)
                    .is_some_and(|member| member.text() == "Length")
                && whole
                    .children()
                    .next()
                    .is_some_and(|of| same_tokens(&skip_parentheses(&of), &receiver));
            if !is_length || !same_tokens(&skip_parentheses(&subtracted), &skip_parentheses(start))
            {
                return None;
            }
            format!("{}..", bound(start))
        }
        _ => return None,
    };
    Some(TextEdit::new(
        call.span(),
        format!("{}[{range}]", receiver.text()),
    ))
}

/// Whether `node` is `bool`, not `bool?`.
fn is_bool(context: &mut Context<'_, '_>, node: &SyntaxNode) -> bool {
    let bool_type = context.view.compiled().special_type(SpecialType::Boolean);
    context
        .view
        .expression_type(node)
        .is_some_and(|ty| ty.symbol().is_some() && ty.symbol() == bool_type)
}

/// `!c`, with parentheses around `c` when it needs them.
fn negated(node: &SyntaxNode) -> String {
    let inner = skip_parentheses(node);
    if inner.kind() == SyntaxKind::LogicalNotExpression
        && let Some(operand) = inner.children().next()
    {
        return skip_parentheses(&operand).text();
    }
    if precedence(inner.kind()) < precedence(SyntaxKind::LogicalNotExpression) {
        format!("!({})", inner.text())
    } else {
        format!("!{}", inner.text())
    }
}

/// `operand` as a side of `kind`.
fn side(node: &SyntaxNode, kind: SyntaxKind) -> String {
    let inner = skip_parentheses(node);
    if precedence(inner.kind()) < precedence(kind) {
        format!("({})", inner.text())
    } else {
        inner.text()
    }
}

/// `c ? true : false` → `c`, and the rest of IDE0075.
fn simplified_conditional(
    context: &mut Context<'_, '_>,
    conditional: &SyntaxNode,
) -> Option<TextEdit> {
    let mut parts = conditional.children();
    let (condition, when_true, when_false) = (parts.next()?, parts.next()?, parts.next()?);
    let literal = |node: &SyntaxNode| match skip_parentheses(node).kind() {
        SyntaxKind::TrueLiteralExpression => Some(true),
        SyntaxKind::FalseLiteralExpression => Some(false),
        _ => None,
    };
    let (kind, text) = match (literal(&when_true), literal(&when_false)) {
        (Some(true), Some(false)) => (
            skip_parentheses(&condition).kind(),
            skip_parentheses(&condition).text(),
        ),
        (Some(false), Some(true)) => (SyntaxKind::LogicalNotExpression, negated(&condition)),
        (Some(true), None) if is_bool(context, &when_false) => (
            SyntaxKind::LogicalOrExpression,
            format!(
                "{} || {}",
                side(&condition, SyntaxKind::LogicalOrExpression),
                side(&when_false, SyntaxKind::LogicalAndExpression)
            ),
        ),
        (None, Some(false)) if is_bool(context, &when_true) => (
            SyntaxKind::LogicalAndExpression,
            format!(
                "{} && {}",
                side(&condition, SyntaxKind::LogicalAndExpression),
                side(&when_true, SyntaxKind::BitwiseOrExpression)
            ),
        ),
        _ => return None,
    };
    Some(TextEdit::new(
        conditional.span(),
        parenthesized_for(&text, kind, conditional),
    ))
}

/// `b == true` → `b`; `b == false` and `b != true` → `!b`.
fn redundant_equality(context: &mut Context<'_, '_>, comparison: &SyntaxNode) -> Option<TextEdit> {
    let mut sides = comparison.children();
    let (left, right) = (sides.next()?, sides.next()?);
    let literal = |node: &SyntaxNode| match skip_parentheses(node).kind() {
        SyntaxKind::TrueLiteralExpression => Some(true),
        SyntaxKind::FalseLiteralExpression => Some(false),
        _ => None,
    };
    let (value, constant) = match (literal(&left), literal(&right)) {
        (None, Some(constant)) => (left, constant),
        (Some(constant), None) => (right, constant),
        _ => return None,
    };
    if !is_bool(context, &value) {
        return None;
    }
    let keep = (comparison.kind() == SyntaxKind::EqualsExpression) == constant;
    let (kind, text) = if keep {
        (
            skip_parentheses(&value).kind(),
            skip_parentheses(&value).text(),
        )
    } else {
        (SyntaxKind::LogicalNotExpression, negated(&value))
    };
    Some(TextEdit::new(
        comparison.span(),
        parenthesized_for(&text, kind, comparison),
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn assignments_become_compound() {
        let source = "class C\n{\n    int total;\n    void M(int x)\n    {\n        total = $$total * (x + 1);\n        total = total + 1;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use compound assignment"),
            "class C\n{\n    int total;\n    void M(int x)\n    {\n        total *= (x + 1);\n        total = total + 1;\n    }\n}\n"
        );
        let source = source
            .replace("$$total *", "total *")
            .replace("total = total + 1", "total = $$total + 1");
        assert_eq!(
            apply(&source, "Use compound assignment"),
            "class C\n{\n    int total;\n    void M(int x)\n    {\n        total = total * (x + 1);\n        total++;\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    int M(int a, int b) => a = $$b + a;\n}\n",
            "Use compound assignment",
        );
    }

    #[test]
    fn counting_from_the_end_uses_the_hat() {
        let index = "namespace System { public readonly struct Index { public Index(int value, bool fromEnd = false) { } public int GetOffset(int length) => 0; } }\n";
        let source = format!(
            "{index}class C\n{{\n    int M(int[] items, int n) => items[$$items.Length - 1] + items[items.Length - (n + 1)];\n}}\n"
        );
        assert_eq!(
            apply(&source, "Use index operator"),
            format!(
                "{index}class C\n{{\n    int M(int[] items, int n) => items[^1] + items[items.Length - (n + 1)];\n}}\n"
            )
        );
        let source = format!(
            "{index}class C\n{{\n    int M(int[] items, int n) => items[items.Length - 1] + items[items.Length - $$(n + 1)];\n}}\n"
        );
        assert_eq!(
            apply(&source, "Use index operator"),
            format!(
                "{index}class C\n{{\n    int M(int[] items, int n) => items[items.Length - 1] + items[^(n + 1)];\n}}\n"
            )
        );
        refuses(
            &format!(
                "{index}class C\n{{\n    int M(int[] items, int[] other) => items[$$other.Length - 1];\n}}\n"
            ),
            "Use index operator",
        );
        // Without `System.Index` there is no `^`.
        refuses(
            "class C\n{\n    int M(int[] items) => items[$$items.Length - 1];\n}\n",
            "Use index operator",
        );
    }

    #[test]
    fn substrings_become_ranges_where_there_are_ranges() {
        let range = "namespace System { public readonly struct Index { public Index(int value, bool fromEnd = false) { } } public readonly struct Range { public Range(Index start, Index end) { } } }\n";
        let source = format!(
            "{range}class C\n{{\n    string M(string s, int i) => s.$$Substring(i, s.Length - i) + s.Substring(0, 2);\n}}\n"
        );
        assert_eq!(
            apply(&source, "Use range operator"),
            format!(
                "{range}class C\n{{\n    string M(string s, int i) => s[i..] + s.Substring(0, 2);\n}}\n"
            )
        );
        refuses(
            "class C\n{\n    string M(string s) => s.$$Substring(1);\n}\n",
            "Use range operator",
        );
    }

    #[test]
    fn conditionals_and_equalities_with_literals_simplify() {
        let source = "class C\n{\n    bool M(int a, bool b) => a > 1 $$? true : b;\n}\n";
        assert_eq!(
            apply(source, "Simplify conditional expression"),
            "class C\n{\n    bool M(int a, bool b) => a > 1 || b;\n}\n"
        );
        let source = "class C\n{\n    bool M(int a) => a > 1 $$? false : true;\n}\n";
        assert_eq!(
            apply(source, "Simplify conditional expression"),
            "class C\n{\n    bool M(int a) => !(a > 1);\n}\n"
        );
        let source = "class C\n{\n    bool M(bool b) => b $$== false;\n}\n";
        assert_eq!(
            apply(source, "Remove redundant equality"),
            "class C\n{\n    bool M(bool b) => !b;\n}\n"
        );
        refuses(
            "class C\n{\n    bool M(bool? b) => b $$== true;\n}\n",
            "Remove redundant equality",
        );
    }
}
