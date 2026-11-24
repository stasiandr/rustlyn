//! Use 'var', use explicit type: the type of a local, written out or
//! inferred.
//!
//! Roslyn's `UseImplicitType` and `UseExplicitType` refactorings, offered
//! with the cursor on the type of a local declaration, a `foreach`
//! variable or an `out` variable. `var` is offered only where it infers
//! exactly the type that is written: one declarator, with an initializer
//! whose own type is that type — `long x = 1` is not `var x = 1`, and `null`
//! or a lambda has no type to infer. The explicit type is the one the binder
//! gave the local, spelled as it would be written at that place.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    // The type the cursor is in, and what declares with it.
    let Some(ty) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| node.kind().is_type_node())
        .last()
    else {
        return;
    };
    let Some(owner) = ty.parent().cloned() else {
        return;
    };
    // The type the declaration is written with, not a type somewhere else
    // in it: `foreach (var x in values)` is about `var`, not `values`.
    if owner
        .children()
        .find(|child| child.kind().is_type_node())
        .as_ref()
        != Some(&ty)
    {
        return;
    }
    let (names, initializer): (Vec<SyntaxNode>, Option<SyntaxNode>) = match owner.kind() {
        SyntaxKind::VariableDeclaration => {
            let parent = owner.parent();
            if parent.is_some_and(|parent| {
                parent.kind() == SyntaxKind::LocalDeclarationStatement
                    && parent
                        .child_token_of_kind(SyntaxKind::ConstKeyword)
                        .is_some()
            }) || parent.is_some_and(|parent| {
                !matches!(
                    parent.kind(),
                    SyntaxKind::LocalDeclarationStatement
                        | SyntaxKind::ForStatement
                        | SyntaxKind::UsingStatement
                )
            }) {
                return;
            }
            let declarators: Vec<SyntaxNode> = owner
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                .collect();
            let initializer = match declarators.as_slice() {
                [only] => only
                    .child_of_kind(SyntaxKind::EqualsValueClause)
                    .and_then(|clause| clause.children().next()),
                _ => None,
            };
            (declarators, initializer)
        }
        SyntaxKind::ForEachStatement => (vec![owner.clone()], None),
        SyntaxKind::DeclarationExpression => {
            let Some(designation) = owner.child_of_kind(SyntaxKind::SingleVariableDesignation)
            else {
                return;
            };
            (vec![designation], None)
        }
        _ => return,
    };
    let Some(first) = names.first() else {
        return;
    };
    let Some(name) = first.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let Some(Resolved::Local { ty: local_type, .. }) = context.view.resolve(&name) else {
        return;
    };

    let is_var = ty.kind() == SyntaxKind::IdentifierName && ty.text() == "var";
    if is_var {
        if let Some(written) = context.view.display_type(&local_type, &ty) {
            found.push(context.local(
                "Use explicit type",
                ActionKind::Rewrite,
                None,
                vec![TextEdit::new(ty.span(), written)],
            ));
        }
        return;
    }

    // `var` infers from the initializer; `foreach` and `out` from what is
    // there, which is always the type the binder recorded.
    let infers_the_same = match owner.kind() {
        SyntaxKind::VariableDeclaration => {
            let Some(initializer) = initializer else {
                return;
            };
            if matches!(
                initializer.kind(),
                SyntaxKind::NullLiteralExpression
                    | SyntaxKind::DefaultLiteralExpression
                    | SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
                    | SyntaxKind::ArrayInitializerExpression
                    | SyntaxKind::CollectionExpression
                    | SyntaxKind::ImplicitObjectCreationExpression
                    | SyntaxKind::StackAllocArrayCreationExpression
                    | SyntaxKind::ImplicitStackAllocArrayCreationExpression
            ) {
                return;
            }
            context.view.expression_type(&initializer).as_ref() == Some(&local_type)
        }
        _ => true,
    };
    if infers_the_same && !matches!(local_type, rustlyn_semantics::Type::Error) {
        found.push(context.local(
            "Use 'var'",
            ActionKind::Rewrite,
            None,
            vec![TextEdit::new(ty.span(), "var")],
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn var_becomes_the_type_it_stands_for() {
        let source = "using System.Collections.Generic;\nclass C\n{\n    void M()\n    {\n        v$$ar items = new List<int>();\n        foreach (var item in items) { }\n    }\n}\n";
        assert_eq!(
            apply(source, "Use explicit type"),
            "using System.Collections.Generic;\nclass C\n{\n    void M()\n    {\n        List<int> items = new List<int>();\n        foreach (var item in items) { }\n    }\n}\n"
        );
        let foreach = "class C\n{\n    void M(int?[] items)\n    {\n        foreach ($$var item in items) { }\n    }\n}\n";
        assert_eq!(
            apply(foreach, "Use explicit type"),
            "class C\n{\n    void M(int?[] items)\n    {\n        foreach (int? item in items) { }\n    }\n}\n"
        );
    }

    #[test]
    fn a_type_from_elsewhere_is_qualified() {
        let source = "namespace N { class Thing { } }\nclass C\n{\n    void M()\n    {\n        $$var thing = new N.Thing();\n    }\n}\n";
        assert_eq!(
            apply(source, "Use explicit type"),
            "namespace N { class Thing { } }\nclass C\n{\n    void M()\n    {\n        N.Thing thing = new N.Thing();\n    }\n}\n"
        );
    }

    #[test]
    fn a_written_type_becomes_var_only_when_it_is_what_var_infers() {
        let source =
            "class C\n{\n    void M(string s)\n    {\n        in$$t n = s.Length;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use 'var'"),
            "class C\n{\n    void M(string s)\n    {\n        var n = s.Length;\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    void M()\n    {\n        lo$$ng n = 1;\n    }\n}\n",
            "Use 'var'",
        );
        refuses(
            "class C\n{\n    void M()\n    {\n        str$$ing s = null;\n    }\n}\n",
            "Use 'var'",
        );
    }
}
