//! Convert to 'foreach', convert to 'for': a counting loop over a
//! collection and a loop over its elements, each into the other.
//!
//! Roslyn's `ConvertForToForEach` and `ConvertForEachToFor`. A `for` becomes
//! a `foreach` when it counts an index from zero up to the collection's
//! `Length` or `Count` by one, and uses the index for nothing but reading
//! the element at it; each read becomes the new loop variable. A `foreach`
//! becomes a `for` over a collection that can be indexed — an array, a
//! string, or a type with `Count` and an indexer — with the loop variable
//! declared first in the body.
//!
//! The collection has to be a plain name or a chain of member accesses:
//! anything that runs code would run once where it ran every time round,
//! or the other way.

use rustlyn_semantics::{SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    fresh_name, is_written, reindent, same_tokens, skip_parentheses, starts_line,
};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let Some(statement) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| {
            matches!(
                node.kind(),
                SyntaxKind::ForStatement | SyntaxKind::ForEachStatement
            )
        })
    else {
        return;
    };
    // The header only.
    let Some(close) = statement.child_token_of_kind(SyntaxKind::CloseParenToken) else {
        return;
    };
    if context.trimmed_span().start() > close.span().end() {
        return;
    }
    if statement.kind() == SyntaxKind::ForStatement {
        if let Some(edits) = to_foreach(context, &statement) {
            found.push(context.local("Convert to 'foreach'", ActionKind::Refactor, None, edits));
        }
    } else if let Some(edits) = to_for(context, &statement) {
        found.push(context.local("Convert to 'for'", ActionKind::Refactor, None, edits));
    }
}

/// Whether `node` reads the same thing each time it runs: a name, `this`,
/// or member accesses on those.
fn is_plain(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::ThisExpression => true,
        SyntaxKind::SimpleMemberAccessExpression => node.children().all(|child| is_plain(&child)),
        SyntaxKind::ParenthesizedExpression => node.children().all(|child| is_plain(&child)),
        _ => false,
    }
}

fn to_foreach(context: &mut Context<'_, '_>, statement: &SyntaxNode) -> Option<Vec<TextEdit>> {
    // `for (int i = 0; i < items.Length; i++)`
    let declaration = statement.child_of_kind(SyntaxKind::VariableDeclaration)?;
    let declarators: Vec<SyntaxNode> = declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let [declarator] = declarators.as_slice() else {
        return None;
    };
    let index_token = declarator.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let start = declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)?
        .children()
        .next()?;
    if start.text() != "0" {
        return None;
    }
    let index = index_token.value_text().to_string();
    let condition = statement.children().find(|child| {
        child.kind() == SyntaxKind::LessThanExpression
            && child.span().start() > declaration.span().end()
    })?;
    let mut sides = condition.children();
    let (left, bound) = (sides.next()?, sides.next()?);
    if left.text() != index || bound.kind() != SyntaxKind::SimpleMemberAccessExpression {
        return None;
    }
    let collection = bound.children().next()?;
    let size = bound.children().last()?.text();
    if !matches!(size.as_str(), "Length" | "Count") || !is_plain(&collection) {
        return None;
    }
    let steps: Vec<SyntaxNode> = statement
        .children()
        .filter(|child| {
            child.span().start() > condition.span().end() && child.kind().is_expression()
        })
        .collect();
    let [step] = steps.as_slice() else {
        return None;
    };
    let step_text: String = step.text().split_whitespace().collect();
    if ![
        format!("{index}++"),
        format!("++{index}"),
        format!("{index}+=1"),
    ]
    .contains(&step_text)
    {
        return None;
    }
    let body = statement.children().last()?;
    if !super::super::text::is_statement(body.kind()) {
        return None;
    }

    // Every use of the index reads `collection[index]`, and nothing writes
    // the element.
    let declared = match context.view.resolve(&index_token)? {
        Resolved::Local { span, .. } => span,
        Resolved::Symbol(_) => return None,
    };
    let tokens: Vec<_> = body
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken && token.value_text() == index)
        .collect();
    let mut accesses = Vec::new();
    for token in tokens {
        if !matches!(context.view.resolve(&token), Some(Resolved::Local { span, .. }) if span == declared)
        {
            continue;
        }
        let name = token.parent().clone();
        let access = name
            .parent()
            .and_then(SyntaxNode::parent)
            .and_then(SyntaxNode::parent)
            .filter(|access| access.kind() == SyntaxKind::ElementAccessExpression)?
            .clone();
        let receiver = access.children().next()?;
        let arguments: Vec<SyntaxNode> = access
            .child_of_kind(SyntaxKind::BracketedArgumentList)?
            .children()
            .collect();
        if !same_tokens(&receiver, &collection)
            || arguments.len() != 1
            || arguments[0].children().next().as_ref() != Some(&name)
            || is_written(&access)
        {
            return None;
        }
        accesses.push(access);
    }
    // The collection itself is not replaced while the loop runs.
    if collection
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .any(|token| {
            body.descendant_tokens().any(|other| {
                other.kind() == SyntaxKind::IdentifierToken
                    && other.value_text() == token.value_text()
                    && is_written(other.parent())
            })
        })
    {
        return None;
    }
    let first = accesses.first()?;
    let element = context.view.expression_type(first)?;
    let element = context.view.display_type(&element, first)?;
    let taken = context.view.names_near(statement);
    let last_name = collection
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .last()
        .map(|token| token.value_text().to_string())
        .unwrap_or_default();
    let base = match last_name.strip_suffix('s') {
        Some(single) if single.len() > 1 && !last_name.ends_with("ss") => {
            super::super::text::camel_case(single)
        }
        _ => "item".to_string(),
    };
    let name = fresh_name(&base, &taken);
    let open = statement.child_token_of_kind(SyntaxKind::ForKeyword)?;
    let close = statement.child_token_of_kind(SyntaxKind::CloseParenToken)?;
    let mut edits = vec![TextEdit::new(
        TextSpan::from_bounds(open.span().start(), close.span().end()),
        format!(
            "foreach ({element} {name} in {})",
            skip_parentheses(&collection).text()
        ),
    )];
    edits.extend(
        accesses
            .iter()
            .map(|access| TextEdit::new(access.span(), name.clone())),
    );
    Some(edits)
}

fn to_for(context: &mut Context<'_, '_>, statement: &SyntaxNode) -> Option<Vec<TextEdit>> {
    let ty = statement
        .children()
        .find(|child| child.kind().is_type_node())?;
    let variable = statement.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let collection = statement.children().find(|child| {
        child.kind().is_expression() && child.span().start() > variable.span().end()
    })?;
    if !is_plain(&collection)
        || statement
            .child_token_of_kind(SyntaxKind::AwaitKeyword)
            .is_some()
    {
        return None;
    }
    let size = match context.view.expression_type(&collection)? {
        Type::Array { rank: 1, .. } => "Length",
        Type::Named { symbol, .. } => {
            let symbols = context.view.compiled().symbols();
            if symbols.qualified_name(symbol) == "System.String" {
                "Length"
            } else {
                let members = &symbols.get(symbol).members;
                let has_count = members.iter().any(|&member| {
                    let found = symbols.get(member);
                    found.kind == SymbolKind::Property && found.name == "Count"
                });
                let has_indexer = members.iter().any(|&member| {
                    symbols.get(member).as_property().is_some_and(|property| {
                        property.is_indexer && property.parameters.len() == 1
                    })
                });
                if !(has_count && has_indexer) {
                    return None;
                }
                "Count"
            }
        }
        _ => return None,
    };
    let body = statement.children().last()?;
    let taken = context.view.names_near(statement);
    let index = fresh_name("i", &taken);
    let collection_text = skip_parentheses(&collection).text();
    let open = statement.child_token_of_kind(SyntaxKind::ForEachKeyword)?;
    let close = statement.child_token_of_kind(SyntaxKind::CloseParenToken)?;
    let header = format!("for (int {index} = 0; {index} < {collection_text}.{size}; {index}++)");
    let declaration = format!(
        "{} {} = {collection_text}[{index}];",
        ty.text(),
        variable.value_text()
    );
    let newline = context.newline();
    let indent = context.indentation_at(statement.span().start());
    let unit = context.indent_unit();
    let inner = format!("{indent}{unit}");
    let mut edits = vec![TextEdit::new(
        TextSpan::from_bounds(open.span().start(), close.span().end()),
        header,
    )];
    if body.kind() == SyntaxKind::Block {
        let brace = body.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
        let first = super::super::text::statements_of(&body);
        let inner = first
            .first()
            .filter(|first| starts_line(&context.text, first.span().start()))
            .map_or(inner, |first| context.indentation_at(first.span().start()));
        edits.push(TextEdit::insert(
            brace.span().end(),
            format!("{newline}{inner}{declaration}"),
        ));
    } else {
        let from = if starts_line(&context.text, body.span().start()) {
            context.indentation_at(body.span().start())
        } else {
            inner.clone()
        };
        let moved = reindent(&body.text(), &from, &inner);
        edits.push(TextEdit::new(
            TextSpan::from_bounds(close.span().end(), body.span().end()),
            format!(
                "{newline}{indent}{{{newline}{inner}{declaration}{newline}{inner}{moved}{newline}{indent}}}"
            ),
        ));
    }
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn a_counting_loop_becomes_a_foreach() {
        let source = "class C\n{\n    void M(string[] names)\n    {\n        $$for (int i = 0; i < names.Length; i++)\n        {\n            System.Console.WriteLine(names[i]);\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to 'foreach'"),
            "class C\n{\n    void M(string[] names)\n    {\n        foreach (string name in names)\n        {\n            System.Console.WriteLine(name);\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn an_index_used_for_anything_else_stays() {
        refuses(
            "class C\n{\n    void M(int[] items)\n    {\n        $$for (int i = 0; i < items.Length; i++)\n        {\n            System.Console.WriteLine(i + items[i]);\n        }\n    }\n}\n",
            "Convert to 'foreach'",
        );
        refuses(
            "class C\n{\n    void M(int[] items)\n    {\n        $$for (int i = 0; i < items.Length; i++) items[i] = 0;\n    }\n}\n",
            "Convert to 'foreach'",
        );
    }

    #[test]
    fn a_foreach_over_a_list_becomes_a_for() {
        let source = "using System.Collections.Generic;\nclass C\n{\n    void M(List<int> values)\n    {\n        $$foreach (var value in values)\n        {\n            System.Console.WriteLine(value);\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to 'for'"),
            "using System.Collections.Generic;\nclass C\n{\n    void M(List<int> values)\n    {\n        for (int i = 0; i < values.Count; i++)\n        {\n            var value = values[i];\n            System.Console.WriteLine(value);\n        }\n    }\n}\n"
        );
        let embedded = "class C\n{\n    void M(int[] values)\n    {\n        $$foreach (int value in values) System.Console.WriteLine(value);\n    }\n}\n";
        assert_eq!(
            apply(embedded, "Convert to 'for'"),
            "class C\n{\n    void M(int[] values)\n    {\n        for (int i = 0; i < values.Length; i++)\n        {\n            int value = values[i];\n            System.Console.WriteLine(value);\n        }\n    }\n}\n"
        );
    }
}
