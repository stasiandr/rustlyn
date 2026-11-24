//! Collection expressions: `[1, 2, 3]` for an array or a list whose type
//! the code around already says, and back.
//!
//! * "Use collection expression" (IDE0300, IDE0301, IDE0028): `new int[] {
//!   1, 2 }`, `new[] { 1, 2 }`, `new List<int> { 1, 2 }`, `new int[0]`,
//!   `new List<int>()` and `Array.Empty<int>()` become `[1, 2]` or `[]` —
//!   where the target is typed: the value of a declaration with a written
//!   type, what a method returns, or what is assigned to something typed.
//!   The target's type must be the collection's own, so that the
//!   expression makes the same thing.
//! * "Convert to 'new' expression": the other way, for an array or a
//!   `List<T>` target, when the collection expression spreads nothing.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

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
    if let Some(creation) = around.iter().find(|node| {
        matches!(
            node.kind(),
            SyntaxKind::ArrayCreationExpression
                | SyntaxKind::ImplicitArrayCreationExpression
                | SyntaxKind::ObjectCreationExpression
                | SyntaxKind::InvocationExpression
        )
    }) && let Some(edit) = to_collection_expression(context, creation)
    {
        found.push(context.local(
            "Use collection expression",
            ActionKind::Rewrite,
            None,
            vec![edit],
        ));
    }
    if let Some(collection) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::CollectionExpression)
        && let Some(edit) = to_new(context, collection)
    {
        found.push(context.local(
            "Convert to 'new' expression",
            ActionKind::Rewrite,
            None,
            vec![edit],
        ));
    }
}

/// The type the place `value` is in gives it, as written there: the type
/// of the declaration it initializes, the return type of the member it is
/// returned from, the type of what it is assigned to.
fn target_type(
    context: &mut Context<'_, '_>,
    value: &SyntaxNode,
) -> Option<(Type, Option<SyntaxNode>)> {
    let parent = value.parent()?;
    match parent.kind() {
        SyntaxKind::EqualsValueClause => {
            let declarator = parent.parent()?;
            let declaration = declarator.parent()?;
            if declaration.kind() != SyntaxKind::VariableDeclaration {
                return None;
            }
            let ty = declaration
                .children()
                .find(|child| child.kind().is_type_node())?;
            if ty.text() == "var" {
                return None;
            }
            Some((context.view.model.type_of_syntax(&ty), Some(ty)))
        }
        SyntaxKind::ReturnStatement | SyntaxKind::ArrowExpressionClause => {
            let owner = parent.ancestors().find(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::MethodDeclaration
                        | SyntaxKind::PropertyDeclaration
                        | SyntaxKind::LocalFunctionStatement
                        | SyntaxKind::SimpleLambdaExpression
                        | SyntaxKind::ParenthesizedLambdaExpression
                        | SyntaxKind::AnonymousMethodExpression
                        | SyntaxKind::GetAccessorDeclaration
                )
            })?;
            let owner = if owner.kind() == SyntaxKind::GetAccessorDeclaration {
                owner
                    .ancestors()
                    .find(|ancestor| ancestor.kind() == SyntaxKind::PropertyDeclaration)?
            } else {
                owner
            };
            if !matches!(
                owner.kind(),
                SyntaxKind::MethodDeclaration
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::LocalFunctionStatement
            ) || owner
                .child_token_of_kind(SyntaxKind::AsyncKeyword)
                .is_some()
            {
                return None;
            }
            let ty = owner.children().find(|child| child.kind().is_type_node())?;
            Some((context.view.model.type_of_syntax(&ty), Some(ty)))
        }
        SyntaxKind::SimpleAssignmentExpression
            if parent.children().nth(1).as_ref() == Some(value) =>
        {
            let target = parent.children().next()?;
            Some((context.view.expression_type(&target)?, None))
        }
        _ => None,
    }
}

/// Whether `ty` is `List<T>`.
fn is_list(context: &Context<'_, '_>, ty: &Type) -> bool {
    ty.symbol().is_some_and(|symbol| {
        context.view.compiled().symbols().qualified_name(symbol)
            == "System.Collections.Generic.List`1"
    })
}

/// `[` + what is between the braces of `initializer` + `]`, on one line
/// when it was on one line.
fn bracketed(initializer: &SyntaxNode) -> Option<String> {
    let open = initializer.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
    let close = initializer.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
    // A brace the parser made up stands where the next token is, which can
    // be past the end of the initializer's text (found by fuzzing).
    if open.is_missing() || close.is_missing() {
        return None;
    }
    let text = initializer.text();
    let start = (open.span().end() - initializer.span().start()) as usize;
    let end = (close.span().start() - initializer.span().start()) as usize;
    let inner = text.get(start..end)?;
    if inner.contains('\n') {
        Some(format!("[{inner}]"))
    } else {
        Some(format!("[{}]", inner.trim()))
    }
}

fn to_collection_expression(
    context: &mut Context<'_, '_>,
    creation: &SyntaxNode,
) -> Option<TextEdit> {
    let (target, _) = target_type(context, creation)?;
    let made = context.view.expression_type(creation)?;
    if made != target {
        return None;
    }
    let written = match creation.kind() {
        SyntaxKind::ArrayCreationExpression | SyntaxKind::ImplicitArrayCreationExpression => {
            match creation.child_of_kind(SyntaxKind::ArrayInitializerExpression) {
                Some(initializer) => bracketed(&initializer)?,
                None => {
                    // `new int[0]`.
                    let ty = creation.child_of_kind(SyntaxKind::ArrayType)?;
                    let rank = ty.child_of_kind(SyntaxKind::ArrayRankSpecifier)?;
                    let sizes: Vec<SyntaxNode> = rank.children().collect();
                    if sizes.len() != 1 || sizes[0].text() != "0" {
                        return None;
                    }
                    "[]".to_string()
                }
            }
        }
        SyntaxKind::ObjectCreationExpression => {
            if !is_list(context, &made) {
                return None;
            }
            let arguments = creation
                .child_of_kind(SyntaxKind::ArgumentList)
                .is_some_and(|list| {
                    list.children()
                        .any(|child| child.kind() == SyntaxKind::Argument)
                });
            if arguments {
                return None;
            }
            match creation.child_of_kind(SyntaxKind::CollectionInitializerExpression) {
                Some(initializer) => {
                    // `{ { a, b } }` calls a two-argument `Add`.
                    if initializer.children().any(|element| {
                        matches!(
                            element.kind(),
                            SyntaxKind::ComplexElementInitializerExpression
                                | SyntaxKind::SimpleAssignmentExpression
                        )
                    }) {
                        return None;
                    }
                    bracketed(&initializer)?
                }
                None if creation
                    .child_of_kind(SyntaxKind::ObjectInitializerExpression)
                    .is_none() =>
                {
                    "[]".to_string()
                }
                None => return None,
            }
        }
        SyntaxKind::InvocationExpression => {
            // `Array.Empty<T>()`.
            let callee = creation.children().next()?;
            let text = callee.text().replace(' ', "");
            let empty = (text.starts_with("Array.Empty<")
                || text.starts_with("System.Array.Empty<"))
                && creation
                    .child_of_kind(SyntaxKind::ArgumentList)
                    .is_some_and(|list| list.children().next().is_none());
            if !empty {
                return None;
            }
            "[]".to_string()
        }
        _ => return None,
    };
    Some(TextEdit::new(creation.span(), written))
}

fn to_new(context: &mut Context<'_, '_>, collection: &SyntaxNode) -> Option<TextEdit> {
    if collection
        .children()
        .any(|element| element.kind() == SyntaxKind::SpreadElement)
    {
        return None;
    }
    let (target, written) = target_type(context, collection)?;
    let ty = match written {
        Some(ty) => ty.text(),
        None => context.view.display_type(&target, collection)?,
    };
    let is_array = matches!(target, Type::Array { rank: 1, .. });
    if !is_array && !is_list(context, &target) {
        return None;
    }
    let open = collection.child_token_of_kind(SyntaxKind::OpenBracketToken)?;
    let close = collection.child_token_of_kind(SyntaxKind::CloseBracketToken)?;
    let text = collection.text();
    let start = (open.span().end() - collection.span().start()) as usize;
    let end = (close.span().start() - collection.span().start()) as usize;
    let inner = &text[start..end];
    let written = if inner.trim().is_empty() {
        if is_array {
            let element = ty.strip_suffix("[]")?;
            format!("new {element}[0]")
        } else {
            format!("new {ty}()")
        }
    } else if inner.contains('\n') {
        format!("new {ty} {{{inner}}}")
    } else {
        format!("new {ty} {{ {} }}", inner.trim())
    };
    Some(TextEdit::new(collection.span(), written))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn creations_with_a_typed_target_become_collection_expressions() {
        let source = "using System.Collections.Generic;\nclass C\n{\n    int[] numbers = new $$int[] { 1, 2, 3 };\n}\n";
        assert_eq!(
            apply(source, "Use collection expression"),
            "using System.Collections.Generic;\nclass C\n{\n    int[] numbers = [1, 2, 3];\n}\n"
        );
        let source = "using System.Collections.Generic;\nclass C\n{\n    List<string> Names()\n    {\n        return new $$List<string>\n        {\n            \"a\",\n            \"b\",\n        };\n    }\n}\n";
        assert_eq!(
            apply(source, "Use collection expression"),
            "using System.Collections.Generic;\nclass C\n{\n    List<string> Names()\n    {\n        return [\n            \"a\",\n            \"b\",\n        ];\n    }\n}\n"
        );
        let source = "class C\n{\n    int[] empty;\n    void M() { empty = new $$int[0]; }\n}\n";
        assert_eq!(
            apply(source, "Use collection expression"),
            "class C\n{\n    int[] empty;\n    void M() { empty = []; }\n}\n"
        );
        refuses(
            "class C\n{\n    void M() { var a = new $$int[] { 1 }; }\n}\n",
            "Use collection expression",
        );
        refuses(
            "using System.Collections.Generic;\nclass C\n{\n    IEnumerable<int> a = new $$List<int> { 1 };\n}\n",
            "Use collection expression",
        );
    }

    #[test]
    fn an_initializer_the_file_cuts_off_is_left_alone() {
        // The `}` the parser made up stands past the initializer's text
        // (found by fuzzing).
        refuses(
            "System.TypeCode[]x=new System.TypeCode[{$$\n",
            "Use collection expression",
        );
    }

    #[test]
    fn a_collection_expression_becomes_a_creation_again() {
        let source = "using System.Collections.Generic;\nclass C\n{\n    List<int> a = $$[1, 2];\n    int[] b = [];\n}\n";
        assert_eq!(
            apply(source, "Convert to 'new' expression"),
            "using System.Collections.Generic;\nclass C\n{\n    List<int> a = new List<int> { 1, 2 };\n    int[] b = [];\n}\n"
        );
        let source = "class C\n{\n    int[] b = $$[];\n}\n";
        assert_eq!(
            apply(source, "Convert to 'new' expression"),
            "class C\n{\n    int[] b = new int[0];\n}\n"
        );
    }
}
