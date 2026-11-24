//! Split and merge `if` statements on `&&` and `||`.
//!
//! Roslyn's `SplitOrMergeIfStatements` providers:
//!
//! * "Split into nested 'if' statements", with the cursor on a top-level
//!   `&&` of an `if` without `else`: `if (a && b) S` becomes
//!   `if (a) { if (b) S }`.
//! * "Merge with nested 'if' statement" on the outer `if`, and "Merge with
//!   outer 'if' statement" on the inner one, the other way.
//! * "Split into consecutive 'if' statements", on a top-level `||` of an
//!   `if` without `else` whose body cannot complete (it returns, throws,
//!   breaks or continues): `if (a || b) return;` becomes `if (a) return;`
//!   then `if (b) return;` — the second runs only when the first did not
//!   leave, which is when `a` was false.
//!
//! A split happens at the operator the cursor is on: `a && b && c` split
//! at the second `&&` tests `a && b` outside and `c` inside.

use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::text::{is_statement, precedence, reindent, starts_line, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    if let Some(token) = context.token_at_cursor()
        && matches!(
            token.kind(),
            SyntaxKind::AmpersandAmpersandToken | SyntaxKind::BarBarToken
        )
        && let Some((statement, condition)) = top_level(&token)
    {
        let edit = if token.kind() == SyntaxKind::AmpersandAmpersandToken {
            split_nested(context, &statement, &condition, &token)
                .map(|edit| ("Split into nested 'if' statements", edit))
        } else {
            split_consecutive(context, &statement, &condition, &token)
                .map(|edit| ("Split into consecutive 'if' statements", edit))
        };
        if let Some((title, edit)) = edit {
            found.push(context.local(title, ActionKind::Refactor, None, vec![edit]));
        }
    }
    if let Some(statement) = super::invert_if::if_at_cursor(context) {
        if let Some(inner) = nested_in(&statement)
            && let Some(edit) = merge(context, &statement, &inner)
        {
            found.push(context.local(
                "Merge with nested 'if' statement",
                ActionKind::Refactor,
                None,
                vec![edit],
            ));
        }
        if let Some(outer) = outer_of(&statement)
            && let Some(edit) = merge(context, &outer, &statement)
        {
            found.push(context.local(
                "Merge with outer 'if' statement",
                ActionKind::Refactor,
                None,
                vec![edit],
            ));
        }
    }
}

/// The `if` whose condition `token` is a top-level operator of, and that
/// condition: every expression between the operator and the condition is
/// the same operator, so splitting there splits the whole condition.
fn top_level(token: &SyntaxToken) -> Option<(SyntaxNode, SyntaxNode)> {
    let operator = token.parent().clone();
    let mut current = operator.clone();
    loop {
        let parent = current.parent()?.clone();
        if parent.kind() == SyntaxKind::IfStatement {
            let condition = parent
                .children()
                .find(|child| child.kind().is_expression())?;
            if condition != current || parent.child_of_kind(SyntaxKind::ElseClause).is_some() {
                return None;
            }
            return Some((parent, condition));
        }
        if parent.kind() != operator.kind() {
            return None;
        }
        current = parent;
    }
}

/// The text of the condition on each side of the operator.
fn sides(
    context: &Context<'_, '_>,
    condition: &SyntaxNode,
    token: &SyntaxToken,
) -> (String, String) {
    let left = context
        .slice(TextSpan::from_bounds(
            condition.span().start(),
            token.span().start(),
        ))
        .trim()
        .to_string();
    let right = context
        .slice(TextSpan::from_bounds(
            token.span().end(),
            condition.span().end(),
        ))
        .trim()
        .to_string();
    (left, right)
}

/// The text from an `if`'s `)` to the end of its statement: what follows
/// the condition, moved one level in or out.
fn tail(context: &Context<'_, '_>, statement: &SyntaxNode) -> Option<String> {
    let close = statement.child_token_of_kind(SyntaxKind::CloseParenToken)?;
    // A `)` the parser made up stands where the next token is, which can be
    // past the end of the statement (found by fuzzing).
    if close.is_missing() || close.span().end() > statement.span().end() {
        return None;
    }
    Some(
        context
            .slice(TextSpan::from_bounds(
                close.span().end(),
                statement.span().end(),
            ))
            .to_string(),
    )
}

fn split_nested(
    context: &Context<'_, '_>,
    statement: &SyntaxNode,
    condition: &SyntaxNode,
    token: &SyntaxToken,
) -> Option<TextEdit> {
    let (left, right) = sides(context, condition, token);
    let newline = context.newline();
    let unit = context.indent_unit();
    let indent = context.indentation_at(statement.span().start());
    let inner_indent = format!("{indent}{unit}");
    let inner = format!("if ({right}){}", tail(context, statement)?);
    let inner = reindent(&inner, &indent, &inner_indent);
    Some(TextEdit::new(
        statement.span(),
        format!("if ({left}){newline}{indent}{{{newline}{inner_indent}{inner}{newline}{indent}}}"),
    ))
}

fn split_consecutive(
    context: &Context<'_, '_>,
    statement: &SyntaxNode,
    condition: &SyntaxNode,
    token: &SyntaxToken,
) -> Option<TextEdit> {
    let body = statement
        .children()
        .find(|child| is_statement(child.kind()))?;
    let last = if body.kind() == SyntaxKind::Block {
        statements_of(&body).last()?.clone()
    } else {
        body
    };
    if !matches!(
        last.kind(),
        SyntaxKind::ReturnStatement
            | SyntaxKind::ThrowStatement
            | SyntaxKind::BreakStatement
            | SyntaxKind::ContinueStatement
    ) {
        return None;
    }
    let (left, right) = sides(context, condition, token);
    let rest = tail(context, statement)?;
    let newline = context.newline();
    let indent = context.indentation_at(statement.span().start());
    Some(TextEdit::new(
        statement.span(),
        format!("if ({left}){rest}{newline}{newline}{indent}if ({right}){rest}"),
    ))
}

/// The `if` that is all of `statement`'s body, when neither has an `else`.
fn nested_in(statement: &SyntaxNode) -> Option<SyntaxNode> {
    if statement.child_of_kind(SyntaxKind::ElseClause).is_some() {
        return None;
    }
    let body = statement
        .children()
        .find(|child| is_statement(child.kind()))?;
    let inner = if body.kind() == SyntaxKind::Block {
        let statements = statements_of(&body);
        match statements.as_slice() {
            [only] => only.clone(),
            _ => return None,
        }
    } else {
        body
    };
    (inner.kind() == SyntaxKind::IfStatement
        && inner.child_of_kind(SyntaxKind::ElseClause).is_none())
    .then_some(inner)
}

/// The `if` whose whole body `statement` is.
fn outer_of(statement: &SyntaxNode) -> Option<SyntaxNode> {
    let parent = statement.parent()?;
    let outer = if parent.kind() == SyntaxKind::Block {
        parent.parent()?.clone()
    } else {
        parent.clone()
    };
    (outer.kind() == SyntaxKind::IfStatement && nested_in(&outer).as_ref() == Some(statement))
        .then_some(outer)
}

fn merge(context: &Context<'_, '_>, outer: &SyntaxNode, inner: &SyntaxNode) -> Option<TextEdit> {
    let condition = |statement: &SyntaxNode| {
        let condition = statement
            .children()
            .find(|child| child.kind().is_expression())?;
        Some(
            if precedence(condition.kind()) < precedence(SyntaxKind::LogicalAndExpression) {
                format!("({})", condition.text())
            } else {
                condition.text()
            },
        )
    };
    let (a, b) = (condition(outer)?, condition(inner)?);
    // Comments in the outer block would be lost.
    let body = outer.children().find(|child| is_statement(child.kind()))?;
    if body.kind() == SyntaxKind::Block && super::super::text::has_comments(&body) {
        return None;
    }
    let rest = tail(context, inner)?;
    let from = if starts_line(&context.text, inner.span().start()) {
        context.indentation_at(inner.span().start())
    } else {
        context.indentation_at(outer.span().start())
    };
    let to = context.indentation_at(outer.span().start());
    let rest = reindent(&rest, &from, &to);
    Some(TextEdit::new(
        outer.span(),
        format!("if ({a} && {b}){rest}"),
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn an_and_splits_into_nested_ifs_and_merges_back() {
        let split = "class C\n{\n    void M(bool a, bool b)\n    {\n        if (a $$&& b)\n        {\n            M(b, a);\n        }\n    }\n}\n";
        let nested = "class C\n{\n    void M(bool a, bool b)\n    {\n        if (a)\n        {\n            if (b)\n            {\n                M(b, a);\n            }\n        }\n    }\n}\n";
        assert_eq!(apply(split, "Split into nested 'if' statements"), nested);
        let outer = nested.replacen("if (a)", "$$if (a)", 1);
        assert_eq!(
            apply(&outer, "Merge with nested 'if' statement"),
            split.replace("$$", "")
        );
        let inner = nested.replacen("if (b)", "$$if (b)", 1);
        assert_eq!(
            apply(&inner, "Merge with outer 'if' statement"),
            split.replace("$$", "")
        );
    }

    #[test]
    fn merging_keeps_an_or_together() {
        let source = "class C\n{\n    void M(bool a, bool b, bool c)\n    {\n        $$if (a || b)\n            if (c) M(a, b, c);\n    }\n}\n";
        assert_eq!(
            apply(source, "Merge with nested 'if' statement"),
            "class C\n{\n    void M(bool a, bool b, bool c)\n    {\n        if ((a || b) && c) M(a, b, c);\n    }\n}\n"
        );
    }

    #[test]
    fn an_or_that_leaves_splits_into_consecutive_ifs() {
        let source = "class C\n{\n    void M(string s)\n    {\n        if (s == null $$|| s.Length == 0) return;\n        M(s);\n    }\n}\n";
        assert_eq!(
            apply(source, "Split into consecutive 'if' statements"),
            "class C\n{\n    void M(string s)\n    {\n        if (s == null) return;\n\n        if (s.Length == 0) return;\n        M(s);\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    void M(bool a, bool b)\n    {\n        if (a $$|| b) M(a, b);\n    }\n}\n",
            "Split into consecutive 'if' statements",
        );
        refuses(
            "class C\n{\n    void M(bool a, bool b, bool c)\n    {\n        if (a $$&& b || c) M(a, b);\n    }\n}\n",
            "Split into nested 'if' statements",
        );
    }

    #[test]
    fn an_if_the_file_cuts_off_is_not_merged() {
        // The `)` the parser made up stands past the end of the statement
        // (found by fuzzing).
        refuses("if$$ if ", "Merge with nested 'if' statement");
    }
}
