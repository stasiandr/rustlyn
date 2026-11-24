//! Rewrites of string literals: concatenation and `string.Format` into an
//! interpolated string, a regular string into a verbatim one and back, and
//! either into a raw string.
//!
//! Roslyn's `ConvertConcatenationToInterpolatedString`,
//! `ConvertPlaceholderToInterpolatedString`,
//! `ConvertBetweenRegularAndVerbatimString` and `ConvertToRawString`. Each
//! keeps the value of the string exactly: a literal whose value one form
//! cannot hold — a control character in a verbatim string, a line break in a
//! single-line raw string — is not converted to it.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken, TokenValue};

use super::super::text::{newline, skip_parentheses};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    if let Some(edit) = concatenation(context, &token) {
        found.push(context.local(
            "Convert to interpolated string",
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
    if let Some(edit) = format_call(context, &token) {
        found.push(context.local(
            "Convert to interpolated string",
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
    if token.kind() == SyntaxKind::StringLiteralToken
        && let TokenValue::String(value) = token.value()
    {
        let value = value.to_string();
        let text = token.text();
        if text.starts_with('"') {
            if text.contains('\\') && !value.chars().any(|c| c.is_control() && c != '\t') {
                found.push(context.local(
                    "Convert to verbatim string",
                    ActionKind::Refactor,
                    None,
                    vec![TextEdit::new(token.span(), verbatim(&value))],
                ));
            }
        } else if text.starts_with('@') {
            found.push(context.local(
                "Convert to regular string",
                ActionKind::Refactor,
                None,
                vec![TextEdit::new(token.span(), regular(&value))],
            ));
        }
        if let Some(raw) = raw(context, &token, &value) {
            found.push(context.local(
                "Convert to raw string",
                ActionKind::Refactor,
                None,
                vec![TextEdit::new(token.span(), raw)],
            ));
        }
    }
}

/// `value` as a verbatim literal.
fn verbatim(value: &str) -> String {
    format!("@\"{}\"", value.replace('"', "\"\""))
}

/// `value` as a regular literal, escaped.
fn regular(value: &str) -> String {
    let mut out = String::from("\"");
    for c in value.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_control() => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `value` as a raw literal: on one line when it fits on one, otherwise
/// with its lines indented as far as the line the literal starts on. `None`
/// when a raw literal would not make it easier to read, or could not hold
/// it.
fn raw(context: &Context<'_, '_>, token: &SyntaxToken, value: &str) -> Option<String> {
    if value.is_empty()
        || !(value.contains('"') || value.contains('\\') || value.contains('\n'))
        || value
            .chars()
            .any(|c| c.is_control() && c != '\n' && c != '\t' && c != '\r')
    {
        return None;
    }
    let longest = value
        .split(|c| c != '"')
        .map(str::len)
        .max()
        .unwrap_or_default();
    let quotes = "\"".repeat((longest + 1).max(3));
    if !value.contains('\n') && !value.contains('\r') {
        if value.starts_with('"') || value.ends_with('"') {
            return None;
        }
        return Some(format!("{quotes}{value}{quotes}"));
    }
    // A raw literal's line breaks are the file's: the value's have to be
    // the same ones.
    let newline = newline(&context.text);
    let lines: Vec<&str> = if newline == "\r\n" {
        if value.replace("\r\n", "").contains(['\r', '\n']) {
            return None;
        }
        value.split("\r\n").collect()
    } else {
        if value.contains('\r') {
            return None;
        }
        value.split('\n').collect()
    };
    let indent = context.indentation_at(token.span().start());
    let mut out = format!("{quotes}{newline}");
    for line in &lines {
        if !line.is_empty() {
            out.push_str(&indent);
            out.push_str(line);
        }
        out.push_str(newline);
    }
    out.push_str(&indent);
    out.push_str(&quotes);
    Some(out)
}

// MARK: - concatenation

fn is_string(context: &mut Context<'_, '_>, node: &SyntaxNode) -> bool {
    match context.view.expression_type(node) {
        Some(Type::Named { symbol, .. }) => {
            context.view.compiled().symbols().qualified_name(symbol) == "System.String"
        }
        _ => false,
    }
}

/// `"a" + b + "c"` as `$"a{b}c"`.
fn concatenation(context: &mut Context<'_, '_>, token: &SyntaxToken) -> Option<TextEdit> {
    let mut top = None;
    for ancestor in std::iter::once(token.parent().clone()).chain(token.parent().ancestors()) {
        if ancestor.kind() == SyntaxKind::AddExpression {
            if is_string(context, &ancestor) {
                top = Some(ancestor);
            } else if top.is_some() {
                break;
            }
        } else if top.is_some() {
            break;
        }
    }
    let top = top?;
    let mut operands = Vec::new();
    flatten(context, &top, &mut operands);
    let mut verbatim = None;
    let mut any_literal = false;
    for operand in &operands {
        let is_verbatim = match operand.kind() {
            SyntaxKind::StringLiteralExpression => {
                let token = operand.first_token()?;
                if token.kind() != SyntaxKind::StringLiteralToken {
                    return None;
                }
                token.text().starts_with('@')
            }
            SyntaxKind::InterpolatedStringExpression => {
                let start = operand.first_token()?;
                match start.text() {
                    "$\"" => false,
                    "$@\"" | "@$\"" => true,
                    _ => return None,
                }
            }
            _ => continue,
        };
        any_literal = true;
        if verbatim.is_some_and(|seen| seen != is_verbatim) {
            return None;
        }
        verbatim = Some(is_verbatim);
    }
    if !any_literal {
        return None;
    }
    let verbatim = verbatim.unwrap_or(false);
    let mut out = String::from(if verbatim { "$@\"" } else { "$\"" });
    for operand in &operands {
        match operand.kind() {
            SyntaxKind::StringLiteralExpression => {
                let text = operand.text();
                let inner = if verbatim {
                    &text[2..text.len() - 1]
                } else {
                    &text[1..text.len() - 1]
                };
                out.push_str(&inner.replace('{', "{{").replace('}', "}}"));
            }
            SyntaxKind::InterpolatedStringExpression => {
                let text = operand.text();
                let open = operand.first_token()?.text().len();
                out.push_str(&text[open..text.len() - 1]);
            }
            _ => out.push_str(&hole(operand)),
        }
    }
    out.push('"');
    Some(TextEdit::new(top.span(), out))
}

/// The operands of a chain of string `+`, in order.
fn flatten(context: &mut Context<'_, '_>, node: &SyntaxNode, out: &mut Vec<SyntaxNode>) {
    if node.kind() == SyntaxKind::AddExpression && is_string(context, node) {
        for child in node.children() {
            flatten(context, &child, out);
        }
    } else {
        out.push(node.clone());
    }
}

/// An expression as an interpolation hole: `{x}`, or `{(a ? b : c)}` where
/// a `:` would be read as the start of a format.
fn hole(expression: &SyntaxNode) -> String {
    let bare = skip_parentheses(expression);
    if bare.kind() == SyntaxKind::ConditionalExpression {
        format!("{{({})}}", bare.text())
    } else {
        format!("{{{}}}", bare.text())
    }
}

// MARK: - string.Format

/// `string.Format("{0} of {1}", a, b)` as `$"{a} of {b}"`.
fn format_call(context: &mut Context<'_, '_>, token: &SyntaxToken) -> Option<TextEdit> {
    let call = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| node.kind() == SyntaxKind::InvocationExpression)?;
    let callee = call.children().next()?;
    if callee.kind() != SyntaxKind::SimpleMemberAccessExpression {
        return None;
    }
    let receiver = callee.children().next()?;
    let name = callee.children().last()?;
    if name.text() != "Format" {
        return None;
    }
    let is_string_type = match receiver.kind() {
        SyntaxKind::PredefinedType => receiver.text() == "string",
        _ => {
            let last = receiver
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .last()?;
            matches!(
                context.view.resolve(&last),
                Some(Resolved::Symbol(symbol))
                    if context.view.compiled().symbols().qualified_name(symbol) == "System.String"
            )
        }
    };
    if !is_string_type {
        return None;
    }
    let arguments: Vec<SyntaxNode> = call
        .child_of_kind(SyntaxKind::ArgumentList)?
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
        .collect();
    if arguments.iter().any(|argument| {
        argument.child_of_kind(SyntaxKind::NameColon).is_some()
            || argument.child_tokens().next().is_some()
    }) {
        return None;
    }
    let format = arguments.first()?.children().next()?;
    if format.kind() != SyntaxKind::StringLiteralExpression {
        return None;
    }
    let literal = format.first_token()?;
    if literal.kind() != SyntaxKind::StringLiteralToken {
        return None;
    }
    let values: Vec<SyntaxNode> = arguments[1..]
        .iter()
        .map(|argument| argument.children().next())
        .collect::<Option<_>>()?;
    let text = literal.text();
    let verbatim = text.starts_with('@');
    let inner = if verbatim {
        &text[2..text.len() - 1]
    } else {
        &text[1..text.len() - 1]
    };
    let mut used = vec![0usize; values.len()];
    let mut out = String::from(if verbatim { "$@\"" } else { "$\"" });
    let mut chars = inner.char_indices().peekable();
    while let Some((at, c)) = chars.next() {
        match c {
            '{' if chars.peek().map(|(_, next)| *next) == Some('{') => {
                chars.next();
                out.push_str("{{");
            }
            '}' if chars.peek().map(|(_, next)| *next) == Some('}') => {
                chars.next();
                out.push_str("}}");
            }
            '}' => return None,
            '{' => {
                let rest = &inner[at + 1..];
                let close = rest.find('}')?;
                let item = &rest[..close];
                let digits: String = item.chars().take_while(char::is_ascii_digit).collect();
                let tail = item[digits.len()..].trim_start();
                if digits.is_empty() || !(tail.is_empty() || tail.starts_with([',', ':'])) {
                    return None;
                }
                let index: usize = digits.parse().ok()?;
                let value = values.get(index)?;
                used[index] += 1;
                let expression = hole(value);
                out.push_str(&expression[..expression.len() - 1]);
                out.push_str(tail);
                out.push('}');
                for _ in 0..=close {
                    chars.next();
                }
            }
            c => out.push(c),
        }
    }
    out.push('"');
    // Every argument once: an unused one would no longer be evaluated, a
    // repeated one would be evaluated twice.
    for (value, &count) in values.iter().zip(&used) {
        if count == 0 {
            return None;
        }
        if count > 1
            && !matches!(
                skip_parentheses(value).kind(),
                SyntaxKind::IdentifierName
                    | SyntaxKind::NumericLiteralExpression
                    | SyntaxKind::StringLiteralExpression
                    | SyntaxKind::ThisExpression
            )
        {
            return None;
        }
    }
    Some(TextEdit::new(call.span(), out))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn concatenation_becomes_one_interpolated_string() {
        let source = "class C\n{\n    string M(string name, int count, bool b)\n    {\n        return \"Hello, \" + name + $$\"! {\" + (count + 1) + (b ? \"x\" : \"y\");\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to interpolated string"),
            "class C\n{\n    string M(string name, int count, bool b)\n    {\n        return $\"Hello, {name}! {{{count + 1}{(b ? \"x\" : \"y\")}\";\n    }\n}\n"
        );
    }

    #[test]
    fn numbers_added_first_stay_one_hole() {
        let source = "class C\n{\n    string M(int a, int b)\n    {\n        return a + b + $$\" total\";\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to interpolated string"),
            "class C\n{\n    string M(int a, int b)\n    {\n        return $\"{a + b} total\";\n    }\n}\n"
        );
    }

    #[test]
    fn format_placeholders_become_holes() {
        let source = "class C\n{\n    string M(int a, double b)\n    {\n        return string.$$Format(\"{0} and {1,5:N2} {{0}}\", a, b);\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to interpolated string"),
            "class C\n{\n    string M(int a, double b)\n    {\n        return $\"{a} and {b,5:N2} {{0}}\";\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    string M(int a, int b)\n    {\n        return string.$$Format(\"{0}\", a, b);\n    }\n}\n",
            "Convert to interpolated string",
        );
    }

    #[test]
    fn regular_and_verbatim_convert_both_ways() {
        let source = "class C\n{\n    string P = $$\"C:\\\\dir\\\\\\\"x\\\"\";\n}\n";
        assert_eq!(
            apply(source, "Convert to verbatim string"),
            "class C\n{\n    string P = @\"C:\\dir\\\"\"x\"\"\";\n}\n"
        );
        let back = "class C\n{\n    string P = $$@\"C:\\dir\\\"\"x\"\"\";\n}\n";
        assert_eq!(
            apply(back, "Convert to regular string"),
            "class C\n{\n    string P = \"C:\\\\dir\\\\\\\"x\\\"\";\n}\n"
        );
        refuses(
            "class C\n{\n    string P = $$\"line\\n\";\n}\n",
            "Convert to verbatim string",
        );
    }

    #[test]
    fn a_string_with_quotes_becomes_raw() {
        let source = "class C\n{\n    string P = $$\"say \\\"hi\\\" now\";\n}\n";
        assert_eq!(
            apply(source, "Convert to raw string"),
            "class C\n{\n    string P = \"\"\"say \"hi\" now\"\"\";\n}\n"
        );
        let lines = "class C\n{\n    string P = $$\"one\\ntwo\";\n}\n";
        assert_eq!(
            apply(lines, "Convert to raw string"),
            "class C\n{\n    string P = \"\"\"\n    one\n    two\n    \"\"\";\n}\n"
        );
    }
}
