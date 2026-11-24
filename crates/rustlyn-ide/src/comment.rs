//! Commenting and uncommenting a selection: Roslyn's `CommentSelection`
//! service, its toggle-line and toggle-block commands.
//!
//! Line comments go in at the column of the least indented line of the
//! selection, so that the block keeps its shape, and blank lines are left
//! alone. The selection is uncommented instead when every line of it that
//! is not blank already starts with `//`. As in Roslyn, `//` goes in without
//! a space after it, and only the `//` comes out.
//!
//! A block comment wraps the selection in `/*` and `*/` — or, with no
//! selection, the line's code — unless the selection is block comments
//! already, or the caret is inside one, in which case the markers come out.
//!
//! Whether a `//` or a `/*` is really a comment is the lexer's call, not the
//! text's: a `//` in a string is not a comment to take out.

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxTrivia};
use rustlyn_text::{LineIndex, TextSpan};

use crate::edit::TextEdit;

/// Comments or uncomments the lines `span` touches with `//`.
#[must_use]
pub fn toggle_line_comment(root: &SyntaxNode, text: &str, span: TextSpan) -> Vec<TextEdit> {
    let lines = LineIndex::new(text);
    let first = lines.line_of(span.start());
    let mut last = lines.line_of(span.end());
    // A selection that ends at the start of a line does not take that line.
    if last > first && lines.line_start(last) == Some(span.end()) {
        last -= 1;
    }
    let comments = comment_trivia(root);
    let mut code: Vec<(u32, &str)> = Vec::new();
    for line in first..=last {
        let Some(start) = lines.line_start(line) else {
            continue;
        };
        let content = line_text(text, start);
        if !content.trim().is_empty() {
            code.push((start, content));
        }
    }
    if code.is_empty() {
        return Vec::new();
    }
    let indent = |content: &str| content.len() - content.trim_start().len();
    let commented = code.iter().all(|(start, content)| {
        let at = start + indent(content) as u32;
        content.trim_start().starts_with("//")
            && comments.iter().any(|trivia| {
                matches!(
                    trivia.kind(),
                    K::SingleLineCommentTrivia | K::SingleLineDocumentationCommentTrivia
                ) && trivia.span().start() == at
            })
    });
    if commented {
        return code
            .iter()
            .map(|(start, content)| {
                TextEdit::delete(TextSpan::new(start + indent(content) as u32, 2))
            })
            .collect();
    }
    let column = code
        .iter()
        .map(|(_, content)| indent(content))
        .min()
        .unwrap_or(0) as u32;
    code.iter()
        .map(|(start, _)| TextEdit::insert(start + column, "//"))
        .collect()
}

/// Wraps `span` in `/* */`, or takes the markers off the block comments it
/// is.
#[must_use]
pub fn toggle_block_comment(root: &SyntaxNode, text: &str, span: TextSpan) -> Vec<TextEdit> {
    let blocks: Vec<TextSpan> = comment_trivia(root)
        .into_iter()
        .filter(|trivia| {
            matches!(
                trivia.kind(),
                K::MultiLineCommentTrivia | K::MultiLineDocumentationCommentTrivia
            )
        })
        .map(|trivia| trivia.span())
        .collect();
    let uncomment = |block: TextSpan| {
        let closed = text[block.start() as usize..block.end() as usize].ends_with("*/")
            && block.length() >= 4;
        let mut edits = vec![TextEdit::delete(TextSpan::new(block.start(), 2))];
        if closed {
            edits.push(TextEdit::delete(TextSpan::new(block.end() - 2, 2)));
        }
        edits
    };

    // The caret, or the whole selection, inside one comment.
    if let Some(&block) = blocks.iter().find(|block| {
        block.start() < span.start() && span.end() < block.end()
            || (!span.is_empty() && block.contains_span(span))
    }) {
        return uncomment(block);
    }
    if span.is_empty() {
        let lines = LineIndex::new(text);
        let Some(start) = lines.line_start(lines.line_of(span.start())) else {
            return Vec::new();
        };
        let content = line_text(text, start);
        let trimmed = content.trim();
        if trimmed.is_empty() {
            return Vec::new();
        }
        let from = start + (content.len() - content.trim_start().len()) as u32;
        return vec![
            TextEdit::insert(from, "/*"),
            TextEdit::insert(from + trimmed.len() as u32, "*/"),
        ];
    }

    // A selection made of block comments and whitespace: uncomment them all.
    let inside: Vec<TextSpan> = blocks
        .iter()
        .copied()
        .filter(|block| span.contains_span(*block))
        .collect();
    let mut rest = text[span.start() as usize..span.end() as usize].to_owned();
    for block in inside.iter().rev() {
        let (from, to) = (
            (block.start() - span.start()) as usize,
            (block.end() - span.start()) as usize,
        );
        rest.replace_range(from..to, "");
    }
    if !inside.is_empty() && rest.trim().is_empty() {
        return inside.into_iter().flat_map(uncomment).collect();
    }
    vec![
        TextEdit::insert(span.start(), "/*"),
        TextEdit::insert(span.end(), "*/"),
    ]
}

/// Every comment in the file, as the lexer found them.
fn comment_trivia(root: &SyntaxNode) -> Vec<SyntaxTrivia> {
    let mut found = Vec::new();
    for token in root.descendant_tokens() {
        for trivia in token
            .leading_trivia()
            .into_iter()
            .chain(token.trailing_trivia())
        {
            if matches!(
                trivia.kind(),
                K::SingleLineCommentTrivia
                    | K::SingleLineDocumentationCommentTrivia
                    | K::MultiLineCommentTrivia
                    | K::MultiLineDocumentationCommentTrivia
            ) {
                found.push(trivia);
            }
        }
    }
    found
}

/// The line starting at `start`, without its line break.
fn line_text(text: &str, start: u32) -> &str {
    let rest = &text[start as usize..];
    &rest[..rest.find(['\n', '\r']).unwrap_or(rest.len())]
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_text::SourceText;

    /// Applies a toggle to the selection between the two `|` (or at the one
    /// `|`), returning the text after it.
    fn toggle(marked: &str, command: fn(&SyntaxNode, &str, TextSpan) -> Vec<TextEdit>) -> String {
        let start = marked.find('|').expect("a caret");
        let text = marked.replacen('|', "", 1);
        let end = text.find('|').unwrap_or(start);
        let text = text.replacen('|', "", 1);
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", text.as_str())).root();
        let edits = command(
            &root,
            &text,
            TextSpan::from_bounds(start as u32, end as u32),
        );
        crate::edit::apply(&text, &edits)
    }

    #[test]
    fn line_comments_go_in_at_the_least_indented_column() {
        let text =
            "class C\n{\n    void M()\n    {\n|        a();\n\n            b();\n|    }\n}\n";
        assert_eq!(
            toggle(text, toggle_line_comment),
            "class C\n{\n    void M()\n    {\n        //a();\n\n        //    b();\n    }\n}\n"
        );
        // A caret alone comments its line.
        assert_eq!(
            toggle("class C { int |x; }\n", toggle_line_comment),
            "//class C { int x; }\n"
        );
    }

    #[test]
    fn line_comments_come_out_when_every_line_has_one() {
        let text = "class C\n{\n|    //int a;\n\n      // int b;\n|}\n";
        assert_eq!(
            toggle(text, toggle_line_comment),
            "class C\n{\n    int a;\n\n       int b;\n}\n"
        );
        // One line without a comment: all of them get one.
        let text = "class C\n{\n|    //int a;\n    int b;|\n}\n";
        assert_eq!(
            toggle(text, toggle_line_comment),
            "class C\n{\n    ////int a;\n    //int b;\n}\n"
        );
        // A `//` inside a string is not a comment.
        let text = "class C\n{\n    string s = @\"\n|//not a comment|\n\";\n}\n";
        assert_eq!(
            toggle(text, toggle_line_comment),
            "class C\n{\n    string s = @\"\n////not a comment\n\";\n}\n"
        );
    }

    #[test]
    fn block_comments_wrap_and_unwrap() {
        assert_eq!(
            toggle("class C { void M() { |a(); b();| } }", toggle_block_comment),
            "class C { void M() { /*a(); b();*/ } }"
        );
        assert_eq!(
            toggle(
                "class C { void M() { |/*a(); b();*/| } }",
                toggle_block_comment
            ),
            "class C { void M() { a(); b(); } }"
        );
        // The caret inside a block comment takes it out.
        assert_eq!(
            toggle("class C { /* int |x; */ }", toggle_block_comment),
            "class C {  int x;  }"
        );
        // The caret on a line of code comments the line's code.
        assert_eq!(
            toggle("class C\n{\n    int |x;\n}", toggle_block_comment),
            "class C\n{\n    /*int x;*/\n}"
        );
        // Several comments and the space between them.
        assert_eq!(
            toggle("int a = 1; |/* one */ /* two */|", toggle_block_comment),
            "int a = 1;  one   two "
        );
    }
}
