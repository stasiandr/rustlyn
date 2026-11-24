//! The fixes that are one edit each: add a missing `;`, remove an unused
//! variable.
//!
//! The parser reports CS1002 where the `;` should be, and the fix puts it
//! there. The binder reports neither CS0168 (declared and never used) nor
//! CS0219 (assigned and never used), so the provider looks for itself: a
//! local, with the cursor on its name, that nothing in its body reads or
//! writes. As in Roslyn, one whose value is not a constant is left alone,
//! since removing it would remove whatever computing the value does.

use rustlyn_semantics::BoundSymbol;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::support::{line_start, next_line_start, starts_line};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let semicolons: Vec<u32> = context
        .diagnostics_with(&["CS1002"])
        .map(|diagnostic| diagnostic.span().start())
        .collect();
    for at in semicolons {
        found.push(context.local(
            "Add missing ';'",
            ActionKind::QuickFix,
            Some("CS1002"),
            vec![TextEdit::insert(at, ";")],
        ));
    }
    unused_variable(context, found);
}

fn unused_variable(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.view.name_token_at(context.span.start()) else {
        return;
    };
    let declarator = token.parent().clone();
    if declarator.kind() != SyntaxKind::VariableDeclarator {
        return;
    }
    let Some(declaration) = declarator.parent().cloned() else {
        return;
    };
    let Some(statement) = declaration.parent().cloned() else {
        return;
    };
    if statement.kind() != SyntaxKind::LocalDeclarationStatement {
        return;
    }
    let initializer = declarator.child_of_kind(SyntaxKind::EqualsValueClause);
    if let Some(initializer) = &initializer
        && !initializer.children().all(|value| is_constant(&value))
    {
        return;
    }
    let Some(body) = context.view.body_for(&declarator) else {
        return;
    };
    let Some(index) = body
        .locals
        .iter()
        .position(|local| local.span == token.span())
    else {
        return;
    };
    let used = body.references.iter().any(|(span, symbol)| {
        *symbol == BoundSymbol::Local(rustlyn_semantics::LocalId(index as u32))
            && *span != token.span()
    });
    if used {
        return;
    }
    let code = if initializer.is_some() {
        "CS0219"
    } else {
        "CS0168"
    };
    let text = &context.text;
    let declarators: Vec<SyntaxNode> = declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let edit = if declarators.len() == 1 {
        // The whole statement, and its line when it has one to itself.
        let start = statement.span().start();
        let end = statement.span().end();
        let rest_of_line = &text[end as usize..next_line_start(text, end) as usize];
        if starts_line(text, start) && rest_of_line.trim().is_empty() {
            TextEdit::delete(rustlyn_text::TextSpan::from_bounds(
                line_start(text, start),
                next_line_start(text, end),
            ))
        } else {
            TextEdit::delete(statement.span())
        }
    } else {
        // One of several: it and the comma that joins it to the next, or
        // to the one before when it is last.
        let commas: Vec<u32> = declaration
            .child_tokens()
            .filter(|token| token.kind() == SyntaxKind::CommaToken)
            .map(|token| token.span().start())
            .collect();
        let span = declarator.span();
        match declarators.iter().position(|other| *other == declarator) {
            Some(position) if position + 1 < declarators.len() => {
                let next = declarators[position + 1].span().start();
                TextEdit::delete(rustlyn_text::TextSpan::from_bounds(span.start(), next))
            }
            _ => {
                let comma = commas
                    .iter()
                    .copied()
                    .filter(|comma| *comma < span.start())
                    .max()
                    .unwrap_or(span.start());
                TextEdit::delete(rustlyn_text::TextSpan::from_bounds(comma, span.end()))
            }
        }
    };
    found.push(context.local(
        "Remove unused variable",
        ActionKind::QuickFix,
        Some(code),
        vec![edit],
    ));
}

/// Whether a value is a constant whose computing does nothing.
fn is_constant(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression
        | SyntaxKind::DefaultLiteralExpression
        | SyntaxKind::DefaultExpression => true,
        SyntaxKind::UnaryMinusExpression
        | SyntaxKind::UnaryPlusExpression
        | SyntaxKind::ParenthesizedExpression => node.children().all(|child| is_constant(&child)),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    #[test]
    fn a_missing_semicolon_is_added() {
        let source = "class C\n{\n    void M()\n    {\n        int y = 2$$\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Add missing ';'"),
            "class C\n{\n    void M()\n    {\n        int y = 2;\n    }\n}\n"
        );
    }

    #[test]
    fn an_unused_local_is_removed_with_its_line() {
        let source = "class C\n{\n    int M()\n    {\n        int $$unused;\n        int used = 1;\n        return used;\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Remove unused variable"),
            "class C\n{\n    int M()\n    {\n        int used = 1;\n        return used;\n    }\n}\n"
        );
        let several = "class C\n{\n    int M()\n    {\n        int a = 1, $$b = 2, c = 3;\n        return a + c;\n    }\n}\n";
        assert_eq!(
            fix(&[several], "Remove unused variable"),
            "class C\n{\n    int M()\n    {\n        int a = 1, c = 3;\n        return a + c;\n    }\n}\n"
        );
    }

    #[test]
    fn a_used_or_computed_local_stays() {
        let used = "class C\n{\n    int M()\n    {\n        int $$used = 1;\n        return used;\n    }\n}\n";
        assert!(!titles(&[used]).contains(&"Remove unused variable".to_string()));
        let computed = "class C\n{\n    int F() => 1;\n\n    void M()\n    {\n        int $$value = F();\n    }\n}\n";
        assert!(!titles(&[computed]).contains(&"Remove unused variable".to_string()));
    }
}
