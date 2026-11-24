//! Ever larger pieces of code around a selection: what "extend selection"
//! steps through. A name, the expression it is in, the argument list's
//! inside, the whole call, the statement, the block's inside, the block, the
//! method, the type.
//!
//! Syntax only, so it answers before the project is compiled and for a file
//! that is not in it.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

/// Spans around `start..end`, smallest first, each strictly larger than the
/// one before and than the selection itself.
#[must_use]
pub fn selection_ranges(root: &SyntaxNode, text: &str, start: u32, end: u32) -> Vec<TextSpan> {
    let (start, end) = (start.min(end), start.max(end));
    let mut spans: Vec<TextSpan> = Vec::new();

    // Inside a comment: the comment. The comment is trivia of the token
    // whose full span holds the position.
    if let Some(holder) = root.find_token(start) {
        for trivia in holder
            .leading_trivia()
            .into_iter()
            .chain(holder.trailing_trivia())
        {
            let span = trivia.span();
            if matches!(
                trivia.kind(),
                SyntaxKind::SingleLineCommentTrivia
                    | SyntaxKind::MultiLineCommentTrivia
                    | SyntaxKind::SingleLineDocumentationCommentTrivia
                    | SyntaxKind::MultiLineDocumentationCommentTrivia
            ) && span.start() <= start
                && end <= span.end()
            {
                spans.push(trimmed(text, span));
            }
        }
    }
    // The token under the start; at the end of a word, that word.
    let token = root
        .find_token(start)
        .filter(|token| token.span().contains(start) || token.span().end() == start)
        .or_else(|| root.find_token(start.checked_sub(1)?));
    if let Some(token) = &token {
        let span = token.span();
        if token.kind() == SyntaxKind::StringLiteralToken && span.length() >= 2 {
            // The string's inside, then the string with its quotes.
            let quote =
                u32::from(token.text().starts_with('@') || token.text().starts_with('$')) + 1;
            if span.length() > quote + 1 {
                spans.push(TextSpan::from_bounds(span.start() + quote, span.end() - 1));
            }
        }
        spans.push(span);
        for node in std::iter::once(token.parent().clone()).chain(token.parent().ancestors()) {
            if let Some(inner) = inside_delimiters(&node, text) {
                spans.push(inner);
            }
            spans.push(node.span());
        }
    }

    spans.retain(|span| span.start() <= start && end <= span.end() && span.length() > end - start);
    spans.sort_by_key(|span| (span.length(), span.start()));
    spans.dedup();
    spans
}

/// Between a node's own braces, brackets or parentheses, without the
/// whitespace next to them.
fn inside_delimiters(node: &SyntaxNode, text: &str) -> Option<TextSpan> {
    let (open, close) = match node.kind() {
        SyntaxKind::Block
        | SyntaxKind::ClassDeclaration
        | SyntaxKind::StructDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::RecordDeclaration
        | SyntaxKind::RecordStructDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::NamespaceDeclaration
        | SyntaxKind::AccessorList
        | SyntaxKind::SwitchStatement
        | SyntaxKind::ObjectInitializerExpression
        | SyntaxKind::CollectionInitializerExpression
        | SyntaxKind::ArrayInitializerExpression
        | SyntaxKind::AnonymousObjectCreationExpression
        | SyntaxKind::SwitchExpression
        | SyntaxKind::PropertyPatternClause => {
            (SyntaxKind::OpenBraceToken, SyntaxKind::CloseBraceToken)
        }
        SyntaxKind::ArgumentList
        | SyntaxKind::ParameterList
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::TupleExpression
        | SyntaxKind::TupleType
        | SyntaxKind::PositionalPatternClause => {
            (SyntaxKind::OpenParenToken, SyntaxKind::CloseParenToken)
        }
        SyntaxKind::BracketedArgumentList
        | SyntaxKind::BracketedParameterList
        | SyntaxKind::AttributeList
        | SyntaxKind::ListPattern
        | SyntaxKind::CollectionExpression => {
            (SyntaxKind::OpenBracketToken, SyntaxKind::CloseBracketToken)
        }
        SyntaxKind::TypeArgumentList | SyntaxKind::TypeParameterList => {
            (SyntaxKind::LessThanToken, SyntaxKind::GreaterThanToken)
        }
        _ => return None,
    };
    let open = node.child_token_of_kind(open)?;
    let close = node.child_token_of_kind(close)?;
    if open.is_missing() || close.is_missing() || close.span().start() <= open.span().end() {
        return None;
    }
    Some(trimmed(
        text,
        TextSpan::from_bounds(open.span().end(), close.span().start()),
    ))
}

/// `span` without the whitespace at either end.
fn trimmed(text: &str, span: TextSpan) -> TextSpan {
    let bytes = text.as_bytes();
    let (mut start, mut end) = (
        span.start() as usize,
        (span.end() as usize).min(bytes.len()),
    );
    while start < end && bytes[start].is_ascii_whitespace() {
        start += 1;
    }
    while end > start && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    TextSpan::from_bounds(start as u32, end as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_syntax::parse;
    use rustlyn_text::SourceText;

    fn steps(source: &str, marker: &str) -> Vec<String> {
        let at = source.find(marker).expect("marker") as u32;
        let tree = parse(SourceText::new("a.cs", source));
        selection_ranges(&tree.root(), source, at, at)
            .into_iter()
            .map(|span| source[span.start() as usize..span.end() as usize].to_string())
            .collect()
    }

    #[test]
    fn a_name_grows_into_its_call_then_the_statement_then_the_block() {
        let source = "class C { void M() { Log(count, 2); } }";
        let got = steps(source, "count");
        assert_eq!(got[0], "count");
        assert!(got.contains(&"count, 2".to_string()), "{got:?}");
        assert!(got.contains(&"(count, 2)".to_string()), "{got:?}");
        assert!(got.contains(&"Log(count, 2)".to_string()), "{got:?}");
        assert!(got.contains(&"Log(count, 2);".to_string()), "{got:?}");
        assert!(got.contains(&"{ Log(count, 2); }".to_string()), "{got:?}");
        assert_eq!(got.last().map(String::as_str), Some(source));
        let lengths: Vec<usize> = got.iter().map(String::len).collect();
        assert!(lengths.windows(2).all(|pair| pair[0] < pair[1]), "{got:?}");
    }

    #[test]
    fn a_string_selects_its_inside_before_its_quotes() {
        let source = "class C { string s = \"hello world\"; }";
        let got = steps(source, "world");
        assert_eq!(got[0], "hello world");
        assert_eq!(got[1], "\"hello world\"");
    }

    #[test]
    fn a_comment_is_selected_whole() {
        let source = "class C {\n    // explains it\n    int x;\n}";
        let got = steps(source, "explains");
        assert_eq!(got[0], "// explains it");
    }

    #[test]
    fn a_block_selects_its_inside_without_the_braces() {
        let source = "class C { void M() {\n    a();\n    b();\n} }";
        let got = steps(source, "a()");
        assert!(got.contains(&"a();\n    b();".to_string()), "{got:?}");
    }
}
