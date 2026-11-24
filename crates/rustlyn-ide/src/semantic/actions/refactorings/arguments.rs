//! Arguments and parameters: name an argument after its parameter, and
//! wrap or unwrap a list of them.
//!
//! Roslyn's `UseNamedArguments` ("Add argument name 'x'", with a second
//! variant naming the arguments after it too) and the wrapping providers
//! for argument and parameter lists ("Wrap every argument", "Indent all
//! arguments", "Unwrap argument list", and the same for parameters).
//!
//! A name is added only where the call bound to one method and the
//! argument is not one of several gathered into a `params` array. Wrapping
//! is offered for lists of two or more with nothing but whitespace between
//! their items: a comment in there would have to go somewhere, and there is
//! no telling where.

use rustlyn_semantics::BoundSymbol;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{has_comments, line_start};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    argument_names(context, found);
    wrapping(context, found);
}

// MARK: - argument names

fn argument_names(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(argument) = context.ancestor_of_kind(&[SyntaxKind::Argument]) else {
        return;
    };
    let Some(list) = argument.parent().cloned() else {
        return;
    };
    let Some(call) = list.parent().cloned() else {
        return;
    };
    if list.kind() != SyntaxKind::ArgumentList
        || !matches!(
            call.kind(),
            SyntaxKind::InvocationExpression | SyntaxKind::ObjectCreationExpression
        )
    {
        return;
    }
    let arguments: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
        .collect();
    let Some(index) = arguments.iter().position(|other| *other == argument) else {
        return;
    };
    if arguments[..=index]
        .iter()
        .any(|argument| argument.child_of_kind(SyntaxKind::NameColon).is_some())
    {
        return;
    }
    let Some(parameters) = parameters_of(context, &call) else {
        return;
    };
    let names: Vec<Option<String>> = (0..arguments.len())
        .map(|at| {
            let (name, is_params) = parameters.get(at)?;
            (!is_params).then(|| name.clone())
        })
        .collect();
    let Some(Some(name)) = names.get(index) else {
        return;
    };
    found.push(context.local(
        format!("Add argument name '{name}'"),
        ActionKind::Refactor,
        None,
        vec![TextEdit::insert(
            argument.span().start(),
            format!("{name}: "),
        )],
    ));
    let trailing = &arguments[index + 1..];
    if !trailing.is_empty()
        && trailing
            .iter()
            .all(|argument| argument.child_of_kind(SyntaxKind::NameColon).is_none())
        && names[index + 1..].iter().all(Option::is_some)
    {
        let edits = arguments[index..]
            .iter()
            .zip(&names[index..])
            .filter_map(|(argument, name)| {
                Some(TextEdit::insert(
                    argument.span().start(),
                    format!("{}: ", name.as_ref()?),
                ))
            })
            .collect();
        found.push(context.local(
            format!("Add argument name '{name}' (including trailing arguments)"),
            ActionKind::Refactor,
            None,
            edits,
        ));
    }
}

/// The parameters of the method a call bound to, as its arguments line up
/// with them: each name, and whether it is a `params` array.
fn parameters_of(context: &mut Context<'_, '_>, call: &SyntaxNode) -> Option<Vec<(String, bool)>> {
    let callee = if call.kind() == SyntaxKind::InvocationExpression {
        call.children().next()?
    } else {
        call.children().find(|child| child.kind().is_type_node())?
    };
    let name = callee
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .last()?;
    let body = context.view.bound_body(call)?;
    let Some(BoundSymbol::Declared(method)) = body.symbol_at(name.span()) else {
        return None;
    };
    let symbols = context.view.compiled().symbols();
    let found = symbols.get(method).as_method()?;
    let mut parameters: Vec<(String, bool)> = found
        .parameters
        .iter()
        .map(|&parameter| {
            let parameter = symbols.get(parameter);
            (
                parameter.name.clone(),
                parameter
                    .as_parameter()
                    .is_some_and(|detail| detail.is_params),
            )
        })
        .collect();
    // `values.Where(...)`: the receiver is the first parameter.
    if found.is_extension && callee.kind() == SyntaxKind::SimpleMemberAccessExpression {
        let receiver = callee.children().next()?;
        let is_type = receiver
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .last()
            .and_then(|token| context.view.resolve(&token))
            .is_some_and(|resolved| match resolved {
                Resolved::Symbol(symbol) => {
                    context.view.compiled().symbols().get(symbol).kind
                        == rustlyn_semantics::SymbolKind::NamedType
                }
                Resolved::Local { .. } => false,
            });
        if !is_type && !parameters.is_empty() {
            parameters.remove(0);
        }
    }
    Some(parameters)
}

// MARK: - wrapping

fn wrapping(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(list) = context.ancestor_of_kind(&[
        SyntaxKind::ArgumentList,
        SyntaxKind::BracketedArgumentList,
        SyntaxKind::ParameterList,
        SyntaxKind::BracketedParameterList,
    ]) else {
        return;
    };
    let noun = match list.kind() {
        SyntaxKind::ArgumentList | SyntaxKind::BracketedArgumentList => "argument",
        _ => "parameter",
    };
    let items: Vec<SyntaxNode> = list
        .children()
        .filter(|child| matches!(child.kind(), SyntaxKind::Argument | SyntaxKind::Parameter))
        .collect();
    let (Some(open), Some(close)) = (list.first_token(), list.last_token()) else {
        return;
    };
    if items.len() < 2 || has_comments(&list) || close.is_missing() {
        return;
    }
    let inside = TextSpan::from_bounds(open.span().end(), close.span().start());
    let current = context.slice(inside).to_string();
    let texts: Vec<String> = items.iter().map(SyntaxNode::text).collect();
    let newline = context.newline();
    let indent = context.indentation_at(open.span().start());
    let unit = context.indent_unit();

    // Every item on its own line, lined up under the first.
    let column = context
        .slice(TextSpan::from_bounds(
            line_start(&context.text, open.span().end()),
            open.span().end(),
        ))
        .chars()
        .count();
    let aligned = texts.join(&format!(",{newline}{}", " ".repeat(column)));
    let indented = format!(
        "{newline}{indent}{unit}{}",
        texts.join(&format!(",{newline}{indent}{unit}"))
    );
    let plural = format!("{noun}s");
    let mut push = |title: String, text: &str| {
        if text != current {
            found.push(context.local(
                title,
                ActionKind::Refactor,
                None,
                vec![TextEdit::new(inside, text)],
            ));
        }
    };
    push(format!("Wrap every {noun}"), &aligned);
    push(format!("Indent all {plural}"), &indented);
    if current.contains('\n') && !texts.iter().any(|text| text.contains('\n')) {
        push(format!("Unwrap {noun} list"), &texts.join(", "));
    }
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn an_argument_is_named_after_its_parameter() {
        let source = "class C\n{\n    void Move(int x, int y, bool fast) { }\n    void M() { Move(1, $$2, true); }\n}\n";
        assert_eq!(
            apply(source, "Add argument name 'y'"),
            "class C\n{\n    void Move(int x, int y, bool fast) { }\n    void M() { Move(1, y: 2, true); }\n}\n"
        );
        assert_eq!(
            apply(
                source,
                "Add argument name 'y' (including trailing arguments)"
            ),
            "class C\n{\n    void Move(int x, int y, bool fast) { }\n    void M() { Move(1, y: 2, fast: true); }\n}\n"
        );
    }

    #[test]
    fn a_params_argument_is_not_named() {
        refuses(
            "class C\n{\n    void Log(string format, params object[] args) { }\n    void M() { Log(\"a\", 1, $$2); }\n}\n",
            "Add argument name 'args'",
        );
    }

    #[test]
    fn a_list_wraps_and_unwraps() {
        let source = "class C\n{\n    void Move(int x, int y, bool fast) { }\n    void M()\n    {\n        Move(1, $$2, true);\n    }\n}\n";
        assert_eq!(
            apply(source, "Wrap every argument"),
            "class C\n{\n    void Move(int x, int y, bool fast) { }\n    void M()\n    {\n        Move(1,\n             2,\n             true);\n    }\n}\n"
        );
        assert_eq!(
            apply(source, "Indent all arguments"),
            "class C\n{\n    void Move(int x, int y, bool fast) { }\n    void M()\n    {\n        Move(\n            1,\n            2,\n            true);\n    }\n}\n"
        );
        let wrapped = "class C\n{\n    void Move(int x,\n              int $$y) { }\n}\n";
        assert_eq!(
            apply(wrapped, "Unwrap parameter list"),
            "class C\n{\n    void Move(int x, int y) { }\n}\n"
        );
    }
}
