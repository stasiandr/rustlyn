use crate::{LinePosition, TextSpan};

/// Whether `ch` terminates a line according to §6.3.1 of the C# specification.
///
/// Note that form feed (`\u{0C}`) is *not* a line terminator in C#; it is
/// whitespace. Getting this wrong shifts every diagnostic after a form feed.
#[must_use]
pub const fn is_line_break(ch: char) -> bool {
    matches!(ch, '\r' | '\n' | '\u{0085}' | '\u{2028}' | '\u{2029}')
}

/// Byte offsets of the first character of every line, built once per file.
#[derive(Clone, Debug)]
pub struct LineIndex {
    /// Always starts with `0`; has one entry per line.
    line_starts: Vec<u32>,
    len: u32,
}

impl LineIndex {
    /// Scans `text` and records where each line begins.
    #[must_use]
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0u32];
        let bytes = text.as_bytes();
        let mut i = 0usize;
        while i < bytes.len() {
            match bytes[i] {
                b'\n' => {
                    i += 1;
                    line_starts.push(i as u32);
                }
                b'\r' => {
                    i += 1;
                    // `\r\n` is a single line break, not two.
                    if bytes.get(i) == Some(&b'\n') {
                        i += 1;
                    }
                    line_starts.push(i as u32);
                }
                // The remaining line terminators are multi-byte: NEL is C2 85,
                // LS and PS are E2 80 A8 / E2 80 A9.
                0xC2 if bytes.get(i + 1) == Some(&0x85) => {
                    i += 2;
                    line_starts.push(i as u32);
                }
                0xE2 if bytes.get(i + 1) == Some(&0x80)
                    && matches!(bytes.get(i + 2), Some(0xA8 | 0xA9)) =>
                {
                    i += 3;
                    line_starts.push(i as u32);
                }
                b => {
                    // Skip the whole UTF-8 sequence so continuation bytes are
                    // never mistaken for a line break lead byte.
                    i += utf8_sequence_len(b);
                }
            }
        }
        Self {
            line_starts,
            len: text.len() as u32,
        }
    }

    /// Number of lines. A file always has at least one, and a trailing line
    /// break opens a final empty line, matching Roslyn.
    #[must_use]
    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }

    /// Byte offset where `line` starts, or `None` if the line does not exist.
    #[must_use]
    pub fn line_start(&self, line: u32) -> Option<u32> {
        self.line_starts.get(line as usize).copied()
    }

    /// The zero-based line containing `offset`.
    #[must_use]
    pub fn line_of(&self, offset: u32) -> u32 {
        match self.line_starts.binary_search(&offset) {
            Ok(line) => line as u32,
            Err(next) => next as u32 - 1,
        }
    }

    /// Converts a byte offset into line/character coordinates.
    ///
    /// The character component counts UTF-8 bytes from the start of the line,
    /// consistent with [`TextSpan`].
    #[must_use]
    pub fn line_position(&self, offset: u32) -> LinePosition {
        let line = self.line_of(offset);
        let start = self.line_starts[line as usize];
        LinePosition::new(line, offset - start)
    }

    /// Converts line/character coordinates back into a byte offset.
    #[must_use]
    pub fn offset(&self, position: LinePosition) -> Option<u32> {
        let start = self.line_start(position.line)?;
        let offset = start.checked_add(position.character)?;
        (offset <= self.len).then_some(offset)
    }

    /// The span of `line` up to and including its line break.
    ///
    /// Use [`SourceText::line_span`](crate::SourceText::line_span) for the
    /// trimmed span; deciding where the break starts needs the text itself.
    #[must_use]
    pub fn line_span_including_break(&self, line: u32) -> Option<TextSpan> {
        let start = self.line_start(line)?;
        let end = self
            .line_start(line + 1)
            .map_or(self.len, |next| next.min(self.len));
        Some(TextSpan::from_bounds(start, end))
    }
}

const fn utf8_sequence_len(lead: u8) -> usize {
    match lead {
        0x00..=0x7F => 1,
        0xC0..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xF7 => 4,
        // Stray continuation byte: cannot happen in a `str`, but stay in bounds.
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_line() {
        let index = LineIndex::new("abc");
        assert_eq!(index.line_count(), 1);
        assert_eq!(index.line_position(2), LinePosition::new(0, 2));
    }

    #[test]
    fn crlf_is_one_break() {
        let index = LineIndex::new("a\r\nb");
        assert_eq!(index.line_count(), 2);
        assert_eq!(index.line_position(3), LinePosition::new(1, 0));
    }

    #[test]
    fn lone_cr_and_unicode_breaks() {
        let index = LineIndex::new("a\rb\u{2028}c\u{85}d");
        assert_eq!(index.line_count(), 4);
        assert_eq!(index.line_of(0), 0);
        assert_eq!(index.line_of(2), 1);
    }

    #[test]
    fn trailing_break_opens_an_empty_line() {
        let index = LineIndex::new("a\n");
        assert_eq!(index.line_count(), 2);
        assert_eq!(index.line_position(2), LinePosition::new(1, 0));
    }

    #[test]
    fn form_feed_is_not_a_line_break() {
        let index = LineIndex::new("a\u{0C}b");
        assert_eq!(index.line_count(), 1);
    }

    #[test]
    fn round_trips_positions() {
        let index = LineIndex::new("one\ntwo\nthree");
        for offset in 0..=13u32 {
            let pos = index.line_position(offset);
            assert_eq!(index.offset(pos), Some(offset));
        }
    }
}
