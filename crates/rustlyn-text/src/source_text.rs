use std::fmt;
use std::sync::Arc;

use crate::{LineIndex, LinePosition, LinePositionSpan, TextSpan, is_line_break};

/// An immutable source file: its contents, a display name and a line index.
///
/// Cloning is cheap; the text is shared.
#[derive(Clone)]
pub struct SourceText {
    inner: Arc<SourceTextInner>,
}

struct SourceTextInner {
    name: String,
    text: String,
    lines: LineIndex,
}

impl SourceText {
    /// Creates a source file with the given display name (usually a path).
    #[must_use]
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> Self {
        let text = text.into();
        let lines = LineIndex::new(&text);
        Self {
            inner: Arc::new(SourceTextInner {
                name: name.into(),
                text,
                lines,
            }),
        }
    }

    /// Creates an unnamed source file, for tests and snippets.
    #[must_use]
    pub fn from_string(text: impl Into<String>) -> Self {
        Self::new("<unnamed>", text)
    }

    /// The display name, as it appears in diagnostics.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.inner.name
    }

    #[must_use]
    pub fn text(&self) -> &str {
        &self.inner.text
    }

    /// Length in UTF-8 bytes.
    #[must_use]
    pub fn len(&self) -> u32 {
        self.inner.text.len() as u32
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.text.is_empty()
    }

    /// The span covering the whole file.
    #[must_use]
    pub fn span(&self) -> TextSpan {
        TextSpan::new(0, self.len())
    }

    #[must_use]
    pub fn lines(&self) -> &LineIndex {
        &self.inner.lines
    }

    /// The text covered by `span`.
    ///
    /// # Panics
    ///
    /// Panics if the span is out of bounds or splits a character.
    #[must_use]
    pub fn slice(&self, span: TextSpan) -> &str {
        &self.inner.text[std::ops::Range::<usize>::from(span)]
    }

    /// The text covered by `span`, or `None` if it is not a valid slice.
    #[must_use]
    pub fn get(&self, span: TextSpan) -> Option<&str> {
        self.inner.text.get(std::ops::Range::<usize>::from(span))
    }

    #[must_use]
    pub fn line_position(&self, offset: u32) -> LinePosition {
        self.inner.lines.line_position(offset)
    }

    #[must_use]
    pub fn line_position_span(&self, span: TextSpan) -> LinePositionSpan {
        LinePositionSpan::new(
            self.line_position(span.start()),
            self.line_position(span.end()),
        )
    }

    #[must_use]
    pub fn line_count(&self) -> u32 {
        self.inner.lines.line_count()
    }

    /// The span of `line` without its trailing line break.
    #[must_use]
    pub fn line_span(&self, line: u32) -> Option<TextSpan> {
        let full = self.inner.lines.line_span_including_break(line)?;
        let text = self.slice(full);
        let trimmed = match text.chars().next_back() {
            Some(last) if is_line_break(last) => {
                let mut end = text.len() - last.len_utf8();
                // `\r\n` is one break: drop the carriage return too.
                if last == '\n' && text[..end].ends_with('\r') {
                    end -= 1;
                }
                end as u32
            }
            _ => full.length(),
        };
        Some(TextSpan::new(full.start(), trimmed))
    }

    /// The text of `line` without its trailing line break.
    #[must_use]
    pub fn line_text(&self, line: u32) -> Option<&str> {
        self.line_span(line).map(|span| self.slice(span))
    }
}

impl fmt::Debug for SourceText {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SourceText")
            .field("name", &self.inner.name)
            .field("len", &self.len())
            .field("lines", &self.line_count())
            .finish()
    }
}

impl From<&str> for SourceText {
    fn from(text: &str) -> Self {
        Self::from_string(text)
    }
}

impl From<String> for SourceText {
    fn from(text: String) -> Self {
        Self::from_string(text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slices_and_lines() {
        let source = SourceText::new("a.cs", "class C\r\n{\n}\n");
        assert_eq!(source.name(), "a.cs");
        assert_eq!(source.line_count(), 4);
        assert_eq!(source.line_text(0), Some("class C"));
        assert_eq!(source.line_text(1), Some("{"));
        assert_eq!(source.line_text(3), Some(""));
        assert_eq!(source.line_text(4), None);
        assert_eq!(source.slice(TextSpan::from_bounds(0, 5)), "class");
    }

    #[test]
    fn positions_are_zero_based() {
        let source = SourceText::from_string("ab\ncd");
        assert_eq!(source.line_position(4), LinePosition::new(1, 1));
        let span = source.line_position_span(TextSpan::from_bounds(1, 4));
        assert_eq!(span.start, LinePosition::new(0, 1));
        assert_eq!(span.end, LinePosition::new(1, 1));
    }

    #[test]
    fn handles_multibyte_text() {
        let source = SourceText::from_string("var имя = 1;");
        assert_eq!(source.line_count(), 1);
        assert_eq!(source.slice(TextSpan::new(4, 6)), "имя");
        assert_eq!(source.get(TextSpan::new(5, 1)), None);
    }
}
