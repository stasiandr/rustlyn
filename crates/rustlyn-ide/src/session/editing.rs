//! The session's syntax-level editing services: formatting, smart
//! indentation, block structure, brace matching, documentation snippets and
//! comment toggling.
//!
//! None of them needs a compilation, or even the project: each parses the
//! one file it is asked about — the editor's text when it passes one, the
//! open document's otherwise — and answers from the tree. So they work the
//! moment a file is open, before anything has been indexed or compiled. As
//! everywhere in the session, offsets come in and go out in UTF-16.

use std::path::Path;

use rustlyn_syntax::SyntaxNode;
use rustlyn_text::{SourceText, TextSpan};

use super::{Changes, Refusal, Session};
use crate::braces::matching_braces;
use crate::comment::{toggle_block_comment, toggle_line_comment};
use crate::doc_comment::{DocCommentSnippet, insert_comment, on_enter, on_typed_slash};
use crate::document::Document;
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::fingerprint::Fingerprint;
use crate::format::{
    FormatOptions, format_document, format_on_type, format_range, indentation_for_new_line,
};
use crate::structure::{FoldKind, StructureOptions, block_structure};
use crate::utf16::Utf16Map;

/// A foldable block, in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fold {
    /// What folds away: UTF-16 offsets.
    pub start: u32,
    pub end: u32,
    /// The whole construct, for a tooltip over the folded block.
    pub hint_start: u32,
    pub hint_end: u32,
    /// What stands in for the folded text.
    pub banner: String,
    pub kind: FoldKind,
    pub collapsible: bool,
    pub collapsed_by_default: bool,
}

/// Two delimiters that belong together, in the editor's units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BraceMatch {
    pub open_start: u32,
    pub open_end: u32,
    pub close_start: u32,
    pub close_end: u32,
}

/// Documentation to write, and where the caret goes once it is written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snippet {
    pub changes: Changes,
    /// UTF-16 offset in the text once the changes are applied.
    pub caret: u32,
}

/// A file's text and its tree, for the syntax-only services.
struct Parsed {
    text: String,
    root: SyntaxNode,
    map: Utf16Map,
}

impl Session {
    fn parsed(&self, path: &Path, text: Option<&str>) -> Result<Parsed, Refusal> {
        let text = self.plain_text_of(path, text).ok_or(Refusal::NotOpen)?;
        let tree = rustlyn_syntax::parse_with(
            SourceText::new(path.to_string_lossy(), text.as_str()),
            &self.options,
        );
        Ok(Parsed {
            map: Utf16Map::new(&text),
            root: tree.root(),
            text,
        })
    }

    /// Byte edits to one file, as changes in the editor's units.
    fn edits_to_changes(&self, path: &Path, parsed: &Parsed, edits: Vec<TextEdit>) -> Changes {
        self.changes_of(
            None,
            path,
            &parsed.text,
            &WorkspaceEdit::single(path, edits),
        )
    }

    /// How to format `path`: the indentation and line breaks the open
    /// document uses, or that `text` shows, with Roslyn's defaults where the
    /// file does not say.
    ///
    /// What the `.editorconfig` files above `path` say comes on top: an
    /// `indent_size` there beats what the file happens to do, as in Roslyn.
    #[must_use]
    pub fn format_options(&self, path: impl AsRef<Path>, text: Option<&str>) -> FormatOptions {
        let path = path.as_ref();
        crate::editorconfig::settings_for(path)
            .format_options(self.detected_format_options(path, text))
    }

    /// The layout the file itself shows, before `.editorconfig` has a say.
    fn detected_format_options(&self, path: &Path, text: Option<&str>) -> FormatOptions {
        if text.is_none()
            && let Some(document) = self.document(path)
        {
            return FormatOptions::from_document(document.indent(), document.line_ending());
        }
        match text
            .map(str::to_owned)
            .or_else(|| self.plain_text_of(path, None))
        {
            Some(text) => {
                let document = Document::from_bytes(
                    path,
                    text.as_bytes(),
                    Fingerprint::of_bytes(text.as_bytes()),
                    0,
                );
                FormatOptions::from_document(document.indent(), document.line_ending())
            }
            None => FormatOptions::default(),
        }
    }

    /// The edits that format the whole file.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn format_document(
        &self,
        path: impl AsRef<Path>,
        text: Option<&str>,
    ) -> Result<Changes, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let options = self.format_options(path, Some(&parsed.text));
        let edits = format_document(&parsed.root, &parsed.text, &options);
        Ok(self.edits_to_changes(path, &parsed, edits))
    }

    /// The edits that format the lines `start..end` (UTF-16) touches.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn format_range(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
    ) -> Result<Changes, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let options = self.format_options(path, Some(&parsed.text));
        let span = TextSpan::from_bounds(
            parsed.map.to_byte(start.min(end)),
            parsed.map.to_byte(start.max(end)),
        );
        let edits = format_range(&parsed.root, &parsed.text, span, &options);
        Ok(self.edits_to_changes(path, &parsed, edits))
    }

    /// What typing `typed` reformats, with `position` (UTF-16) the caret
    /// just after it: Roslyn's triggers `;`, `}`, a line break, and `#`.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn format_on_type(
        &self,
        path: impl AsRef<Path>,
        position: u32,
        typed: char,
        text: Option<&str>,
    ) -> Result<Changes, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let options = self.format_options(path, Some(&parsed.text));
        let byte = parsed.map.to_byte(position);
        let edits = format_on_type(&parsed.root, &parsed.text, byte, typed, &options);
        Ok(self.edits_to_changes(path, &parsed, edits))
    }

    /// The indentation for the new line when Enter is pressed at `position`
    /// (UTF-16, in the text before the line break goes in). `None` where
    /// there is no opinion, as inside a string over several lines.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn indentation_for_new_line(
        &self,
        path: impl AsRef<Path>,
        position: u32,
        text: Option<&str>,
    ) -> Result<Option<String>, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let options = self.format_options(path, Some(&parsed.text));
        Ok(indentation_for_new_line(
            &parsed.root,
            &parsed.text,
            parsed.map.to_byte(position),
            &options,
        ))
    }

    /// Every foldable block of the file, in order.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn block_structure(
        &self,
        path: impl AsRef<Path>,
        text: Option<&str>,
        options: StructureOptions,
    ) -> Result<Vec<Fold>, Refusal> {
        let parsed = self.parsed(path.as_ref(), text)?;
        let map = &parsed.map;
        Ok(block_structure(&parsed.root, &parsed.text, options)
            .into_iter()
            .map(|range| Fold {
                start: map.to_utf16(range.span.start()),
                end: map.to_utf16(range.span.end()),
                hint_start: map.to_utf16(range.hint.start()),
                hint_end: map.to_utf16(range.hint.end()),
                banner: range.banner,
                kind: range.kind,
                collapsible: range.collapsible,
                collapsed_by_default: range.collapsed_by_default,
            })
            .collect())
    }

    /// The pair the delimiter beside `position` (UTF-16) belongs to.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn brace_match(
        &self,
        path: impl AsRef<Path>,
        position: u32,
        text: Option<&str>,
    ) -> Result<Option<BraceMatch>, Refusal> {
        let parsed = self.parsed(path.as_ref(), text)?;
        let map = &parsed.map;
        Ok(
            matching_braces(&parsed.root, map.to_byte(position)).map(|pair| BraceMatch {
                open_start: map.to_utf16(pair.open.start()),
                open_end: map.to_utf16(pair.open.end()),
                close_start: map.to_utf16(pair.close.start()),
                close_end: map.to_utf16(pair.close.end()),
            }),
        )
    }

    /// A documentation snippet in the editor's units.
    fn snippet(&self, path: &Path, parsed: &Parsed, found: DocCommentSnippet) -> Snippet {
        let after = crate::edit::apply(&parsed.text, std::slice::from_ref(&found.edit));
        let caret = Utf16Map::new(&after).to_utf16(found.caret);
        Snippet {
            changes: self.edits_to_changes(path, parsed, vec![found.edit]),
            caret,
        }
    }

    /// What typing the third `/` of `///` expands into, with `position`
    /// (UTF-16) the caret after it.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn doc_comment_on_typed(
        &self,
        path: impl AsRef<Path>,
        position: u32,
        text: Option<&str>,
    ) -> Result<Option<Snippet>, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let newline = self.format_options(path, Some(&parsed.text)).newline;
        let byte = parsed.map.to_byte(position);
        Ok(on_typed_slash(&parsed.root, &parsed.text, byte, &newline)
            .map(|found| self.snippet(path, &parsed, found)))
    }

    /// What Enter adds inside documentation, with `position` (UTF-16) the
    /// start of the new line and the line break already in the text.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn doc_comment_on_enter(
        &self,
        path: impl AsRef<Path>,
        position: u32,
        text: Option<&str>,
    ) -> Result<Option<Snippet>, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let newline = self.format_options(path, Some(&parsed.text)).newline;
        let byte = parsed.map.to_byte(position);
        Ok(on_enter(&parsed.root, &parsed.text, byte, &newline)
            .map(|found| self.snippet(path, &parsed, found)))
    }

    /// The "insert comment" command: documentation for the declaration
    /// around `position` (UTF-16).
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn insert_doc_comment(
        &self,
        path: impl AsRef<Path>,
        position: u32,
        text: Option<&str>,
    ) -> Result<Option<Snippet>, Refusal> {
        let path = path.as_ref();
        let parsed = self.parsed(path, text)?;
        let newline = self.format_options(path, Some(&parsed.text)).newline;
        let byte = parsed.map.to_byte(position);
        Ok(insert_comment(&parsed.root, &parsed.text, byte, &newline)
            .map(|found| self.snippet(path, &parsed, found)))
    }

    /// Comments the lines of `start..end` (UTF-16) with `//`, or uncomments
    /// them when they all are.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn toggle_line_comment(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
    ) -> Result<Changes, Refusal> {
        self.toggle(path.as_ref(), start, end, text, toggle_line_comment)
    }

    /// Wraps `start..end` (UTF-16) in `/* */`, or unwraps it.
    ///
    /// # Errors
    ///
    /// Fails when the file is neither given, open nor readable.
    pub fn toggle_block_comment(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
    ) -> Result<Changes, Refusal> {
        self.toggle(path.as_ref(), start, end, text, toggle_block_comment)
    }

    fn toggle(
        &self,
        path: &Path,
        start: u32,
        end: u32,
        text: Option<&str>,
        command: fn(&SyntaxNode, &str, TextSpan) -> Vec<TextEdit>,
    ) -> Result<Changes, Refusal> {
        let parsed = self.parsed(path, text)?;
        let span = TextSpan::from_bounds(
            parsed.map.to_byte(start.min(end)),
            parsed.map.to_byte(start.max(end)),
        );
        let edits = command(&parsed.root, &parsed.text, span);
        Ok(self.edits_to_changes(path, &parsed, edits))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn session() -> Session {
        Session::new(std::env::temp_dir(), None, Vec::<String>::new())
    }

    fn apply(text: &str, changes: &Changes) -> String {
        // UTF-16 changes, applied from the last to the first.
        let mut units: Vec<u16> = text.encode_utf16().collect();
        for change in changes.changes.iter().rev() {
            let start = change.start as usize;
            let end = start + change.length as usize;
            units.splice(start..end, change.text.encode_utf16());
        }
        String::from_utf16(&units).expect("valid UTF-16")
    }

    #[test]
    fn every_service_survives_every_position_of_broken_code() {
        let session = session();
        let texts = [
            "class C { void M() { if (x) { Foo(a, ",
            "/// <summary>\n///\nclass C<T { int this[ { get",
            "#region A\n#if B\n\"unterminated\n#endregion\n",
            "class C { string s = $\"{a + \u{1F600}\"; char c = '",
            "/* open comment\nclass C { }",
            "",
        ];
        for text in texts {
            let length = text.encode_utf16().count() as u32;
            for position in 0..=length {
                let at = Some(text);
                let _ = session.format_range("A.cs", 0, position, at);
                let _ = session.format_on_type("A.cs", position, '}', at);
                let _ = session.indentation_for_new_line("A.cs", position, at);
                let _ = session.brace_match("A.cs", position, at);
                let _ = session.doc_comment_on_typed("A.cs", position, at);
                let _ = session.doc_comment_on_enter("A.cs", position, at);
                let _ = session.insert_doc_comment("A.cs", position, at);
                let _ = session.toggle_line_comment("A.cs", position, length, at);
                let _ = session.toggle_block_comment("A.cs", position / 2, position, at);
            }
            let _ = session.format_document("A.cs", Some(text));
            let _ = session.block_structure("A.cs", Some(text), StructureOptions::default());
        }
    }

    #[test]
    fn formatting_counts_in_utf16_and_follows_the_file() {
        let session = session();
        // Tabs and CRLF in the file: the braces it adds use them too, and
        // the offsets after the emoji count it as two units.
        let text =
            "class C\r\n{\r\n\tstring s = \"\u{1F600}\";void M() {\r\n\t\tx=1;\r\n\t}\r\n}\r\n";
        let changes = session
            .format_document("A.cs", Some(text))
            .expect("formatted");
        assert_eq!(
            apply(text, &changes),
            "class C\r\n{\r\n\tstring s = \"\u{1F600}\"; void M()\r\n\t{\r\n\t\tx = 1;\r\n\t}\r\n}\r\n"
        );
        let range = session
            .format_range("A.cs", 0, 5, Some("class  C { }\nint  x;\n"))
            .expect("formatted");
        assert_eq!(
            apply("class  C { }\nint  x;\n", &range),
            "class C { }\nint  x;\n"
        );
    }

    #[test]
    fn typing_and_indenting() {
        let session = session();
        let text = "class C\n{\n    void M()\n    {\n        int x=1;\n    }\n}\n";
        let position = (text.find("=1;").expect("the statement") + 3) as u32;
        let changes = session
            .format_on_type("A.cs", position, ';', Some(text))
            .expect("formatted");
        assert!(apply(text, &changes).contains("int x = 1;"));
        let indent = session
            .indentation_for_new_line(
                "A.cs",
                (text.find("{\n        int").expect("the brace") + 1) as u32,
                Some(text),
            )
            .expect("answered");
        assert_eq!(indent.as_deref(), Some("        "));
    }

    #[test]
    fn structure_braces_snippets_and_comments() {
        let session = session();
        let text = "// \u{1F600}\nclass C\n{\n    ///\n    int M(int a) { return a; }\n}\n";
        let folds = session
            .block_structure("A.cs", Some(text), StructureOptions::default())
            .expect("structure");
        let class = folds
            .iter()
            .find(|fold| fold.kind == FoldKind::Type)
            .expect("the class");
        // `// ` then two units for the emoji, a line break, `class C`.
        assert_eq!(class.start, 3 + 2 + 1 + 7);

        let open = text.find("{\n    ///").expect("the brace");
        let utf16 = |bytes: usize| Utf16Map::new(text).to_utf16(bytes as u32);
        let pair = session
            .brace_match("A.cs", utf16(open), Some(text))
            .expect("answered")
            .expect("a pair");
        assert_eq!(pair.open_start, utf16(open));
        assert_eq!(pair.close_start, utf16(text.rfind('}').expect("the end")));

        let slashes = text.find("///").expect("the slashes") + 3;
        let snippet = session
            .doc_comment_on_typed("A.cs", utf16(slashes), Some(text))
            .expect("answered")
            .expect("a snippet");
        let after = apply(text, &snippet.changes);
        assert!(
            after.contains("    /// <param name=\"a\"></param>\n    /// <returns></returns>\n")
        );
        let before_caret =
            String::from_utf16(&after.encode_utf16().collect::<Vec<_>>()[..snippet.caret as usize])
                .expect("valid");
        assert!(before_caret.ends_with("/// <summary>\n    /// "));

        let toggled = session
            .toggle_line_comment("A.cs", utf16(slashes + 5), utf16(slashes + 5), Some(text))
            .expect("toggled");
        assert!(apply(text, &toggled).contains("    //int M(int a)"));
        let block = session
            .toggle_block_comment("A.cs", 0, 2, Some("int x;"))
            .expect("toggled");
        assert_eq!(apply("int x;", &block), "/*in*/t x;");
        assert!(
            session
                .insert_doc_comment("A.cs", 0, Some("class C { }"))
                .expect("answered")
                .is_some()
        );
        assert!(
            session
                .doc_comment_on_enter("A.cs", 0, Some("class C { }"))
                .expect("answered")
                .is_none()
        );
    }
}
