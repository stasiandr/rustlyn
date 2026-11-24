//! Introduce field: an expression selected in a field's initializer gets a
//! field of its own.
//!
//! Roslyn's `IntroduceVariable` in a field initializer, where there is no
//! statement to put a local before: "Introduce field for 'e'" declares
//! `private static readonly T name = e;` just above the field, and the
//! expression becomes the name. The new field is static because an
//! initializer cannot read an instance field (CS0236). Constant expressions
//! are left to "Introduce constant".

use rustlyn_semantics::Type;
use rustlyn_syntax::SyntaxKind;

use super::super::text::{fresh_name, one_line, pascal_case, skip_parentheses};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(expression) = context.selected_node() else {
        return;
    };
    if !expression.kind().is_expression() || expression.kind().is_type_node() {
        return;
    }
    // In a field's initializer, outside any lambda.
    let Some(field) = expression
        .ancestors()
        .find(|ancestor| ancestor.kind() == SyntaxKind::FieldDeclaration)
    else {
        return;
    };
    let in_initializer = expression
        .ancestors()
        .take_while(|ancestor| *ancestor != field)
        .any(|ancestor| ancestor.kind() == SyntaxKind::EqualsValueClause);
    let in_lambda = expression
        .ancestors()
        .take_while(|ancestor| *ancestor != field)
        .any(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
            )
        });
    if !in_initializer
        || in_lambda
        || field
            .child_token_of_kind(SyntaxKind::ConstKeyword)
            .is_some()
        || skip_parentheses(&expression).kind() == SyntaxKind::NumericLiteralExpression
        || skip_parentheses(&expression).kind() == SyntaxKind::StringLiteralExpression
    {
        return;
    }
    // The whole initializer is the field already.
    if expression
        .parent()
        .is_some_and(|parent| parent.kind() == SyntaxKind::EqualsValueClause)
    {
        return;
    }
    let Some(ty) = context.view.expression_type(&expression) else {
        return;
    };
    if matches!(ty, Type::Void | Type::Null | Type::Error) {
        return;
    }
    let Some(written) = context.view.display_type(&ty, &expression) else {
        return;
    };
    let taken = context.view.names_near(&expression);
    let name = fresh_name(
        &pascal_case(&super::introduce_variable::suggested_name(&expression)),
        &taken,
    );
    let indent = context.indentation_at(field.span().start());
    let nl = context.newline();
    let start = super::members::member_start(&field);
    let line = super::super::text::line_start(&context.text, start);
    let edits = vec![
        TextEdit::insert(
            line,
            format!(
                "{indent}private static readonly {written} {name} = {};{nl}",
                skip_parentheses(&expression).text()
            ),
        ),
        TextEdit::new(expression.span(), name),
    ];
    found.push(context.local(
        format!("Introduce field for '{}'", one_line(&expression)),
        ActionKind::Extract,
        None,
        edits,
    ));
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn an_initializer_part_gets_a_field() {
        let source =
            "class Clock\n{\n    static int Now() => 1;\n\n    int started = [|Now()|] * 2;\n}\n";
        assert_eq!(
            apply(source, "Introduce field for 'Now()'"),
            "class Clock\n{\n    static int Now() => 1;\n\n    private static readonly int Now1 = Now();\n    int started = Now1 * 2;\n}\n"
        );
        refuses(
            "class C\n{\n    int x = [|1|] + 2;\n}\n",
            "Introduce field for '1'",
        );
    }
}
