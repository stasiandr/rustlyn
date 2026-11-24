//! A file's text as the value graph reads it: UTF-16 code units (the
//! units of [`super::flow`]), its lines, and the conversions between a
//! line and column (as the compiler's locations give them), an offset, and
//! the UTF-8 byte offset of the public API.

/// A file's text in UTF-16 and where its lines start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    text: String,
    units: Vec<u16>,
    /// The UTF-16 offset each line starts at; the first is 0.
    starts: Vec<usize>,
}

impl Document {
    #[must_use]
    pub fn new(text: &str) -> Self {
        let units: Vec<u16> = text.encode_utf16().collect();
        let mut starts = vec![0];
        starts.extend(
            units
                .iter()
                .enumerate()
                .filter(|(_, u)| **u == 0x0A)
                .map(|(i, _)| i + 1),
        );
        Self {
            text: text.to_owned(),
            units,
            starts,
        }
    }

    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    #[must_use]
    pub fn units(&self) -> &[u16] {
        &self.units
    }

    #[must_use]
    pub fn line_count(&self) -> usize {
        self.starts.len()
    }

    /// The line holding the offset.
    #[must_use]
    pub fn line(&self, offset: usize) -> usize {
        self.starts
            .partition_point(|&s| s <= offset)
            .saturating_sub(1)
    }

    /// A line and a UTF-16 column → an offset. Positions past the end of
    /// a line or of the file are clamped.
    #[must_use]
    pub fn offset(&self, line: usize, character: usize) -> usize {
        let count = self.line_count();
        let line = line.min(count - 1);
        let start = self.starts[line];
        let end = if line + 1 < count {
            self.starts[line + 1]
        } else {
            self.units.len()
        };
        // The line's end without its line break.
        let mut line_end = end;
        if line_end > start && self.units[line_end - 1] == 0x0A {
            line_end -= 1;
        }
        if line_end > start && self.units[line_end - 1] == 0x0D {
            line_end -= 1;
        }
        (start + character).min(line_end)
    }

    /// An offset → its line and UTF-16 column.
    #[must_use]
    pub fn position(&self, offset: usize) -> (usize, usize) {
        let clamped = offset.min(self.units.len());
        let line = self.line(clamped);
        (line, clamped - self.starts[line])
    }

    /// The UTF-8 byte offset of a UTF-16 offset.
    #[must_use]
    pub fn byte(&self, offset: usize) -> usize {
        let units = &self.units[..offset.min(self.units.len())];
        char::decode_utf16(units.iter().copied())
            .map(|c| c.map_or(3, char::len_utf8))
            .sum()
    }

    /// The text of line `number`, without its line break.
    #[must_use]
    pub fn line_text(&self, number: usize) -> String {
        let Some(&start) = self.starts.get(number) else {
            return String::new();
        };
        let end = self
            .starts
            .get(number + 1)
            .copied()
            .unwrap_or(self.units.len());
        let mut text = String::from_utf16_lossy(&self.units[start..end]);
        while text.ends_with(['\n', '\r']) {
            text.pop();
        }
        text
    }

    /// Lines `first..=last` (clamped to the file) as an excerpt.
    #[must_use]
    pub fn excerpt(&self, first: usize, last: usize) -> Excerpt {
        let last = last.min(self.line_count() - 1);
        Excerpt {
            first,
            lines: (first..=last).map(|n| self.line_text(n)).collect(),
        }
    }
}

/// Lines of a file around a place, as plain text. A front end may show them
/// as they are or highlight them from the file (`first..first + len`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Excerpt {
    /// The number of the first line, zero-based.
    pub first: usize,
    pub lines: Vec<String>,
}

impl Excerpt {
    /// The text of line `number`, if the excerpt has it.
    #[must_use]
    pub fn line(&self, number: usize) -> Option<&str> {
        number
            .checked_sub(self.first)
            .and_then(|i| self.lines.get(i))
            .map(String::as_str)
    }

    /// The last line's number.
    #[must_use]
    pub fn last(&self) -> usize {
        (self.first + self.lines.len()).saturating_sub(1)
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lines_offsets_and_bytes() {
        let document = Document::new("ab\r\néü\nx");
        assert_eq!(document.line_count(), 3);
        assert_eq!(document.offset(1, 1), 5);
        assert_eq!(document.offset(0, 9), 2, "clamped before the line break");
        assert_eq!(document.position(5), (1, 1));
        assert_eq!(document.line(7), 2);
        assert_eq!(document.byte(5), 6, "two bytes per accented letter");
        assert_eq!(document.line_text(0), "ab");
        let excerpt = document.excerpt(1, 9);
        assert_eq!((excerpt.first, excerpt.last()), (1, 2));
        assert_eq!(excerpt.line(2), Some("x"));
    }
}
