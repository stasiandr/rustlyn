//! Offsets that an editor and a compiler both understand.
//!
//! Rustlyn addresses code by byte offsets into UTF-8, because that is what
//! `&str` indexes by. The editors this serves address code by UTF-16 code
//! units: `NSRange` on macOS, `Position.character` in LSP, and `String` in
//! Java and JavaScript. The two agree on ASCII and nowhere else, so a comment
//! in Russian or one emoji in a string literal is enough to make every
//! highlight below it land on the wrong character.
//!
//! The conversion could be done by rescanning the line every time, but it is
//! asked for once per token on every repaint, so it gets a table. The table
//! is built lazily and only where it is needed: a file of pure ASCII has the
//! same offsets in both units, and that is the overwhelming majority of source
//! code, so the common case pays nothing at all.

use rustlyn_text::TextSpan;

/// The UTF-16 view of a piece of text.
#[derive(Clone, Debug)]
pub struct Utf16Map {
    /// Where the runs of non-ASCII are: byte offset, and how far the UTF-16
    /// offset has drifted from the byte offset by the end of that run.
    ///
    /// Empty for pure ASCII, which is the case worth being free.
    drifts: Vec<Drift>,
    byte_len: u32,
    utf16_len: u32,
}

#[derive(Clone, Copy, Debug)]
struct Drift {
    /// The byte offset just past a non-ASCII character.
    byte: u32,
    /// The UTF-16 offset of that same place.
    utf16: u32,
    /// How wide that character is, in each unit. Kept so that an offset
    /// landing *inside* the character can be answered with the character's
    /// own start rather than with a place that does not exist.
    bytes: u32,
    units: u32,
}

impl Utf16Map {
    /// Builds the map for `text`.
    ///
    /// Pure ASCII is recognised without building anything: the scan stops
    /// looking for drift the moment it can prove there is none.
    #[must_use]
    pub fn new(text: &str) -> Self {
        let byte_len = text.len() as u32;
        if text.is_ascii() {
            return Self {
                drifts: Vec::new(),
                byte_len,
                utf16_len: byte_len,
            };
        }

        let mut drifts = Vec::new();
        let mut utf16 = 0u32;
        for (byte, ch) in text.char_indices() {
            let bytes = ch.len_utf8() as u32;
            let units = ch.len_utf16() as u32;
            utf16 += units;
            if bytes != 1 {
                drifts.push(Drift {
                    byte: byte as u32 + bytes,
                    utf16,
                    bytes,
                    units,
                });
            }
        }
        Self {
            drifts,
            byte_len,
            utf16_len: utf16,
        }
    }

    /// Whether byte offsets and UTF-16 offsets are the same here.
    #[must_use]
    pub fn is_ascii(&self) -> bool {
        self.drifts.is_empty()
    }

    /// The length of the text in UTF-16 code units.
    #[must_use]
    pub const fn utf16_len(&self) -> u32 {
        self.utf16_len
    }

    /// The UTF-16 offset of a byte offset.
    ///
    /// An offset inside a character — which a caller should not produce, but
    /// a caller mapping a span it computed arithmetically can — is rounded
    /// down to that character's start rather than being made up.
    #[must_use]
    pub fn to_utf16(&self, byte: u32) -> u32 {
        if self.drifts.is_empty() {
            return byte.min(self.byte_len);
        }
        let byte = byte.min(self.byte_len);
        // The last character boundary at or before `byte`.
        match self.drifts.binary_search_by_key(&byte, |drift| drift.byte) {
            Ok(index) => self.drifts[index].utf16,
            Err(index) => {
                let (base_byte, base_utf16) = match index {
                    0 => (0, 0),
                    _ => (self.drifts[index - 1].byte, self.drifts[index - 1].utf16),
                };
                // `byte` may land inside the next multi-byte character, which
                // is a place no UTF-16 offset names. Answer with that
                // character's start, the nearest place that is real.
                if let Some(next) = self.drifts.get(index) {
                    let starts_at = next.byte - next.bytes;
                    if byte > starts_at {
                        return base_utf16 + (starts_at - base_byte);
                    }
                }
                base_utf16 + (byte - base_byte)
            }
        }
    }

    /// The byte offset of a UTF-16 offset — the other direction, for a
    /// selection or a click coming in from the editor.
    #[must_use]
    pub fn to_byte(&self, utf16: u32) -> u32 {
        if self.drifts.is_empty() {
            return utf16.min(self.byte_len);
        }
        let utf16 = utf16.min(self.utf16_len);
        match self
            .drifts
            .binary_search_by_key(&utf16, |drift| drift.utf16)
        {
            Ok(index) => self.drifts[index].byte,
            Err(index) => {
                let (base_byte, base_utf16) = match index {
                    0 => (0, 0),
                    _ => (self.drifts[index - 1].byte, self.drifts[index - 1].utf16),
                };
                // The same clamp the other way: an offset between the two
                // halves of a surrogate pair names half a character.
                if let Some(next) = self.drifts.get(index) {
                    let starts_at = next.utf16 - next.units;
                    if utf16 > starts_at {
                        return base_byte + (starts_at - base_utf16);
                    }
                }
                base_byte + (utf16 - base_utf16)
            }
        }
    }

    /// A span in UTF-16 units.
    #[must_use]
    pub fn span(&self, span: TextSpan) -> (u32, u32) {
        let start = self.to_utf16(span.start());
        let end = self.to_utf16(span.end());
        (start, end.saturating_sub(start))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ascii_costs_nothing_and_maps_one_to_one() {
        let map = Utf16Map::new("class A { }");
        assert!(map.is_ascii());
        for offset in 0..=11 {
            assert_eq!(map.to_utf16(offset), offset);
            assert_eq!(map.to_byte(offset), offset);
        }
    }

    #[test]
    fn a_two_byte_character_shifts_everything_after_it() {
        // `é` is two bytes of UTF-8 and one UTF-16 unit.
        let text = "// é\nclass A";
        let map = Utf16Map::new(text);
        assert!(!map.is_ascii());
        assert_eq!(map.to_utf16(0), 0);
        assert_eq!(map.to_utf16(3), 3); // just before the é
        assert_eq!(map.to_utf16(5), 4); // just after it: two bytes, one unit
        assert_eq!(map.to_utf16(text.len() as u32), map.utf16_len());
    }

    #[test]
    fn an_astral_character_is_two_units_and_four_bytes() {
        // A rocket is four bytes of UTF-8 and a surrogate pair in UTF-16.
        let text = "\"🚀\"";
        let map = Utf16Map::new(text);
        assert_eq!(map.to_utf16(0), 0);
        assert_eq!(map.to_utf16(1), 1); // after the quote
        assert_eq!(map.to_utf16(5), 3); // after the rocket: 4 bytes, 2 units
        assert_eq!(map.utf16_len(), 4);
    }

    #[test]
    fn the_two_directions_agree() {
        let text = "// комментарий\nclass Ünïcödé { /* 🚀🚀 */ }\n";
        let map = Utf16Map::new(text);
        // Every character boundary must survive the round trip.
        for (byte, _) in text.char_indices() {
            let byte = byte as u32;
            assert_eq!(
                map.to_byte(map.to_utf16(byte)),
                byte,
                "byte {byte} did not survive the round trip",
            );
        }
    }

    #[test]
    fn utf16_length_matches_what_the_standard_library_counts() {
        for text in [
            "",
            "ascii only",
            "// комментарий",
            "\"🚀\"",
            "mixed é 🚀 text",
            "🚀🚀🚀",
        ] {
            let map = Utf16Map::new(text);
            assert_eq!(
                map.utf16_len() as usize,
                text.encode_utf16().count(),
                "{text:?}",
            );
        }
    }

    #[test]
    fn an_offset_past_the_end_is_clamped_rather_than_invented() {
        let map = Utf16Map::new("é");
        assert_eq!(map.to_utf16(1000), map.utf16_len());
        assert_eq!(map.to_byte(1000), 2);
    }

    #[test]
    fn an_offset_inside_a_character_rounds_down() {
        // Nobody should ask this, but the answer must still be a real place.
        let map = Utf16Map::new("é!");
        assert_eq!(map.to_utf16(1), 0);

        // The same in the middle of the text rather than at its start.
        let map = Utf16Map::new("ab🚀cd");
        assert_eq!(map.to_utf16(2), 2); // the rocket starts here
        for inside in 3..6 {
            assert_eq!(
                map.to_utf16(inside),
                2,
                "byte {inside} is inside the rocket"
            );
        }
        assert_eq!(map.to_utf16(6), 4); // past it: four bytes, two units
    }

    #[test]
    fn an_offset_between_the_halves_of_a_surrogate_pair_rounds_down() {
        let map = Utf16Map::new("ab🚀cd");
        assert_eq!(map.to_byte(2), 2); // the rocket starts here
        assert_eq!(map.to_byte(3), 2); // between its two units
        assert_eq!(map.to_byte(4), 6); // past it
    }
}
