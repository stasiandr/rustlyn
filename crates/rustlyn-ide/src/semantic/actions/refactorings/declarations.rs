//! Declarations folded into what uses them.
//!
//! * "Inline variable declaration" (IDE0018): `int value;` followed by
//!   `int.TryParse(s, out value)` becomes `int.TryParse(s, out int value)`.
//!   Offered on the `out` argument when the local is declared, without a
//!   value, just for it in the same block and not used before it; and only
//!   in a statement whose variables are the block's — an expression, a
//!   declaration, an `if`'s condition, a `return` — so that uses after it
//!   still see it.
//! * "Deconstruct variable declaration" (IDE0042): `var point = GetPoint();`
//!   whose every use is `point.X` or `point.Y` becomes `var (x, y) =
//!   GetPoint();`, each use its element's variable.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{camel_case, is_written, statements_of, whole_lines};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let around: Vec<SyntaxNode> = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| !super::super::text::is_member(node.kind()))
        .collect();
    if let Some(argument) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::Argument)
        && let Some(edits) = inline_out(context, argument)
    {
        found.push(context.local(
            "Inline variable declaration",
            ActionKind::Rewrite,
            None,
            edits,
        ));
    }
    if let Some(declaration) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::LocalDeclarationStatement)
        && let Some(edits) = deconstruct(context, declaration)
    {
        found.push(context.local(
            "Deconstruct variable declaration",
            ActionKind::Rewrite,
            None,
            edits,
        ));
    }
}

/// `int value; ... out value` → `out int value`.
fn inline_out(context: &mut Context<'_, '_>, argument: &SyntaxNode) -> Option<Vec<TextEdit>> {
    argument.child_token_of_kind(SyntaxKind::OutKeyword)?;
    let name = argument.children().last()?;
    if name.kind() != SyntaxKind::IdentifierName {
        return None;
    }
    let token = name.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let Resolved::Local { span: declared, .. } = context.view.resolve(&token)? else {
        return None;
    };
    // The statement the argument is in, and the block both are in.
    let statement = argument
        .ancestors()
        .find(|ancestor| super::super::text::is_statement(ancestor.kind()))?;
    let block = statement.parent()?;
    if block.kind() != SyntaxKind::Block {
        return None;
    }
    let scoped_to_block = match statement.kind() {
        SyntaxKind::ExpressionStatement
        | SyntaxKind::LocalDeclarationStatement
        | SyntaxKind::ReturnStatement
        | SyntaxKind::ThrowStatement => true,
        SyntaxKind::IfStatement => statement
            .children()
            .next()
            .is_some_and(|condition| condition.span().contains(argument.span().start())),
        _ => false,
    };
    if !scoped_to_block
        || argument
            .ancestors()
            .take_while(|ancestor| *ancestor != statement)
            .any(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::SimpleLambdaExpression
                        | SyntaxKind::ParenthesizedLambdaExpression
                        | SyntaxKind::AnonymousMethodExpression
                        | SyntaxKind::ConditionalExpression
                        | SyntaxKind::LogicalAndExpression
                        | SyntaxKind::LogicalOrExpression
                        | SyntaxKind::CoalesceExpression
                )
            })
    {
        return None;
    }
    let statements = statements_of(block);
    let at = statements.iter().position(|other| *other == statement)?;
    let declaration = statements[..at].iter().find(|candidate| {
        candidate.kind() == SyntaxKind::LocalDeclarationStatement
            && candidate.descendants().any(|node| {
                node.kind() == SyntaxKind::VariableDeclarator
                    && node.span().contains(declared.start())
            })
    })?;
    let variable = declaration.child_of_kind(SyntaxKind::VariableDeclaration)?;
    let declarators: Vec<SyntaxNode> = variable
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let [declarator] = declarators.as_slice() else {
        return None;
    };
    if declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)
        .is_some()
        || declaration
            .child_token_of_kind(SyntaxKind::ConstKeyword)
            .is_some()
    {
        return None;
    }
    let ty = variable
        .children()
        .find(|child| child.kind().is_type_node())?
        .text();
    // Not used before the argument: between the declaration and the
    // statement, or earlier in the statement.
    let local = token.value_text().to_string();
    let used_before = |node: &SyntaxNode| {
        node.descendant_tokens().any(|other| {
            other.kind() == SyntaxKind::IdentifierToken
                && other.value_text() == local
                && other.span().start() < token.span().start()
                && other.span().start() > declarator.span().end()
        })
    };
    let from = statements.iter().position(|other| other == declaration)?;
    if statements[from + 1..=at].iter().any(used_before) {
        return None;
    }
    let lines = whole_lines(&context.text, declaration.span());
    Some(vec![
        TextEdit::delete(lines),
        TextEdit::insert(name.span().start(), format!("{ty} ")),
    ])
}

/// `var point = GetPoint();` read only as `point.X` → `var (x, y) =
/// GetPoint();`.
fn deconstruct(context: &mut Context<'_, '_>, declaration: &SyntaxNode) -> Option<Vec<TextEdit>> {
    if declaration
        .child_token_of_kind(SyntaxKind::ConstKeyword)
        .is_some()
        || declaration
            .child_token_of_kind(SyntaxKind::UsingKeyword)
            .is_some()
    {
        return None;
    }
    let variable = declaration.child_of_kind(SyntaxKind::VariableDeclaration)?;
    let declarators: Vec<SyntaxNode> = variable
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let [declarator] = declarators.as_slice() else {
        return None;
    };
    let value = declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)?
        .children()
        .next()?;
    let Some(Type::Tuple(elements)) = context.view.expression_type(&value) else {
        return None;
    };
    let name_token = declarator.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let local = name_token.value_text().to_string();
    let block = declaration.parent()?;
    let taken = context.view.names_near(declaration);
    let element_names: Vec<String> = elements
        .iter()
        .enumerate()
        .map(|(index, element)| match &element.name {
            Some(name) => name.clone(),
            None => format!("Item{}", index + 1),
        })
        .collect();
    let variables: Vec<String> = element_names.iter().map(|name| camel_case(name)).collect();
    if variables
        .iter()
        .enumerate()
        .any(|(index, name)| taken.contains(name) || variables[..index].contains(name))
    {
        return None;
    }
    // Every use reads one element.
    let mut edits = Vec::new();
    for token in block.descendant_tokens() {
        if token.kind() != SyntaxKind::IdentifierToken
            || token.value_text() != local
            || token.span() == name_token.span()
        {
            continue;
        }
        let name = token.parent().clone();
        let access = name.parent()?.clone();
        if access.kind() != SyntaxKind::SimpleMemberAccessExpression
            || access.children().next().as_ref() != Some(&name)
            || is_written(&access)
        {
            return None;
        }
        let member = access.children().nth(1)?.text();
        let index = element_names
            .iter()
            .position(|element| *element == member)?;
        edits.push(TextEdit::new(access.span(), variables[index].clone()));
    }
    if edits.is_empty() {
        return None;
    }
    let ty = variable
        .children()
        .find(|child| child.kind().is_type_node())?;
    let head = if ty.text() == "var" {
        format!("var ({})", variables.join(", "))
    } else {
        let Type::Tuple(_) = context.view.model.type_of_syntax(&ty) else {
            return None;
        };
        // `(int x, int y) point` → `(int x, int y)`.
        let types: Vec<String> = ty
            .children()
            .filter(|child| child.kind() == SyntaxKind::TupleElement)
            .filter_map(|element| {
                element
                    .children()
                    .find(|part| part.kind().is_type_node())
                    .map(|part| part.text())
            })
            .collect();
        if types.len() != variables.len() {
            return None;
        }
        let parts: Vec<String> = types
            .iter()
            .zip(&variables)
            .map(|(ty, name)| format!("{ty} {name}"))
            .collect();
        format!("({})", parts.join(", "))
    };
    edits.push(TextEdit::new(
        TextSpan::from_bounds(ty.span().start(), name_token.span().end()),
        head,
    ));
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn an_out_variable_is_declared_where_it_is_passed() {
        let source = "class C\n{\n    int M(string s)\n    {\n        int value;\n        if (int.TryParse(s, out $$value))\n        {\n            return value;\n        }\n        return value;\n    }\n}\n";
        assert_eq!(
            apply(source, "Inline variable declaration"),
            "class C\n{\n    int M(string s)\n    {\n        if (int.TryParse(s, out int value))\n        {\n            return value;\n        }\n        return value;\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    int M(string s)\n    {\n        int value;\n        value = 1;\n        int.TryParse(s, out $$value);\n        return value;\n    }\n}\n",
            "Inline variable declaration",
        );
        refuses(
            "class C\n{\n    void M(string s)\n    {\n        int value;\n        while (int.TryParse(s, out $$value)) { }\n        value++;\n    }\n}\n",
            "Inline variable declaration",
        );
    }

    #[test]
    fn a_tuple_read_by_element_is_deconstructed() {
        let source = "class C\n{\n    (int Width, int Height) Size() => (1, 2);\n    int M()\n    {\n        var $$size = Size();\n        return size.Width * size.Height;\n    }\n}\n";
        assert_eq!(
            apply(source, "Deconstruct variable declaration"),
            "class C\n{\n    (int Width, int Height) Size() => (1, 2);\n    int M()\n    {\n        var (width, height) = Size();\n        return width * height;\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    (int Width, int Height) Size() => (1, 2);\n    object M()\n    {\n        var $$size = Size();\n        return size;\n    }\n}\n",
            "Deconstruct variable declaration",
        );
    }
}
