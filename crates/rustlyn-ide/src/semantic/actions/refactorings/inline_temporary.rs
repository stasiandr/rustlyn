//! Inline temporary variable: replace every use of a local with the value
//! it was declared with, and remove the declaration.
//!
//! Roslyn's `InlineTemporary`. It applies to a local that is given a value
//! once, where it is declared, and never written again — anything else and
//! the uses would not all see that value. Each use becomes the initializer,
//! in parentheses where the place it lands would otherwise read it
//! differently, and with a cast where the local's declared type is not the
//! type the initializer has on its own.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    is_written, needs_parentheses, precedence, skip_parentheses, whole_lines,
};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    if let Some(edits) = inline(context) {
        found.push(context.local("Inline temporary variable", ActionKind::Inline, None, edits));
    }
}

fn inline(context: &mut Context<'_, '_>) -> Option<Vec<TextEdit>> {
    let token = context.token_at_cursor()?;
    if token.kind() != SyntaxKind::IdentifierToken {
        return None;
    }
    let declarator = token.parent().clone();
    if declarator.kind() != SyntaxKind::VariableDeclarator {
        return None;
    }
    let declaration = declarator.parent()?.clone();
    let statement = declaration.parent()?.clone();
    if statement.kind() != SyntaxKind::LocalDeclarationStatement
        || statement.child_tokens().any(|token| {
            matches!(
                token.kind(),
                SyntaxKind::UsingKeyword | SyntaxKind::ConstKeyword
            )
        })
        || !matches!(
            statement.parent().map(SyntaxNode::kind),
            Some(SyntaxKind::Block | SyntaxKind::SwitchSection)
        )
    {
        return None;
    }
    let value = declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)?
        .children()
        .next()?;
    if matches!(
        value.kind(),
        SyntaxKind::ArrayInitializerExpression | SyntaxKind::RefExpression
    ) {
        return None;
    }
    let Resolved::Local {
        span: declared, ty, ..
    } = context.view.resolve(&token)?
    else {
        return None;
    };

    // Every use, none of them a write.
    let scope = statement.parent()?.clone();
    let name = token.value_text().to_string();
    let candidates: Vec<_> = scope
        .descendant_tokens()
        .filter(|other| {
            other.kind() == SyntaxKind::IdentifierToken
                && other.value_text() == name
                && other.span().start() > declarator.span().end()
        })
        .collect();
    let mut uses = Vec::new();
    for candidate in candidates {
        if let Some(Resolved::Local { span, .. }) = context.view.resolve(&candidate)
            && span == declared
        {
            let node = candidate.parent().clone();
            if node.kind() != SyntaxKind::IdentifierName || is_written(&node) {
                return None;
            }
            uses.push(node);
        }
    }
    if uses.is_empty() {
        return None;
    }

    // The initializer as it reads anywhere: cast to the local's type when
    // it has another of its own.
    let bare = skip_parentheses(&value);
    let mut text = bare.text();
    let mut kind = bare.kind();
    let own = context.view.expression_type(&value);
    let needs_cast = match (&own, &ty) {
        (_, Type::Error) => return None,
        (Some(own), declared) => own != declared,
        (None, _) => true,
    };
    let is_var = declaration
        .children()
        .next()
        .is_some_and(|ty| ty.kind() == SyntaxKind::IdentifierName && ty.text() == "var");
    if needs_cast && !is_var {
        let written = context.view.display_type(&ty, &value)?;
        let operand = if precedence(kind) >= precedence(SyntaxKind::CastExpression) {
            text
        } else {
            format!("({text})")
        };
        text = format!("({written}){operand}");
        kind = SyntaxKind::CastExpression;
    }

    let mut edits: Vec<TextEdit> = uses
        .iter()
        .map(|node| {
            let replaced = if needs_parentheses(kind, node) {
                format!("({text})")
            } else {
                text.clone()
            };
            TextEdit::new(node.span(), replaced)
        })
        .collect();

    // The declaration goes: the statement, or the one declarator of several.
    let declarators: Vec<SyntaxNode> = declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let removed = if declarators.len() == 1 {
        whole_lines(&context.text, statement.span())
    } else {
        let at = declarators.iter().position(|other| *other == declarator)?;
        if at + 1 < declarators.len() {
            TextSpan::from_bounds(
                declarator.span().start(),
                declarators[at + 1].span().start(),
            )
        } else {
            TextSpan::from_bounds(declarators[at - 1].span().end(), declarator.span().end())
        }
    };
    edits.push(TextEdit::delete(removed));
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn every_use_becomes_the_value() {
        let source = "class C\n{\n    int M(int a, int b)\n    {\n        int $$sum = a + b;\n        return sum * sum;\n    }\n}\n";
        assert_eq!(
            apply(source, "Inline temporary variable"),
            "class C\n{\n    int M(int a, int b)\n    {\n        return (a + b) * (a + b);\n    }\n}\n"
        );
    }

    #[test]
    fn a_value_that_binds_tightly_needs_no_parentheses() {
        let source = "class C\n{\n    void M(string s)\n    {\n        var $$n = s.Length;\n        System.Console.WriteLine(n + 1);\n    }\n}\n";
        assert_eq!(
            apply(source, "Inline temporary variable"),
            "class C\n{\n    void M(string s)\n    {\n        System.Console.WriteLine(s.Length + 1);\n    }\n}\n"
        );
    }

    #[test]
    fn a_declared_type_that_differs_is_kept_with_a_cast() {
        let source = "class C\n{\n    void M(int a)\n    {\n        long $$wide = a, other = 2;\n        System.Console.WriteLine(wide);\n    }\n}\n";
        assert_eq!(
            apply(source, "Inline temporary variable"),
            "class C\n{\n    void M(int a)\n    {\n        long other = 2;\n        System.Console.WriteLine((long)a);\n    }\n}\n"
        );
    }

    #[test]
    fn a_local_written_again_is_not_inlined() {
        refuses(
            "class C\n{\n    int M()\n    {\n        int $$x = 1;\n        x++;\n        return x;\n    }\n}\n",
            "Inline temporary variable",
        );
    }
}
