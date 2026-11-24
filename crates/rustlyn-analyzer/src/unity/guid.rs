//! A Unity asset's GUID: the 32 hexadecimal digits in its `.meta` file.

use std::fmt;

/// Kept as two words rather than a string: a map of tens of thousands of
/// assets holds no string per key, and comparing is two instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Guid {
    pub hi: u64,
    pub lo: u64,
}

impl Guid {
    #[must_use]
    pub const fn new(hi: u64, lo: u64) -> Self {
        Self { hi, lo }
    }

    /// Exactly 32 hexadecimal digits.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        let bytes = text.as_bytes();
        if bytes.len() != 32 {
            return None;
        }
        Self::parse_at(bytes, 0)
    }

    /// Exactly 32 hexadecimal digits from `start`, and no hexadecimal digit
    /// right after: otherwise this is a piece of something longer. Works on
    /// UTF-8 bytes and on UTF-16 code units alike.
    pub fn parse_at<T: Copy + Into<u32>>(c: &[T], start: usize) -> Option<Self> {
        if start + 32 > c.len() {
            return None;
        }
        if start + 32 < c.len() && hex_value(c[start + 32].into()).is_some() {
            return None;
        }
        let mut hi: u64 = 0;
        let mut lo: u64 = 0;
        for k in 0..32 {
            let v = u64::from(hex_value(c[start + k].into())?);
            if k < 16 {
                hi = (hi << 4) | v;
            } else {
                lo = (lo << 4) | v;
            }
        }
        Some(Self { hi, lo })
    }

    /// Unity's built-in resources (`0000000000000000e000000000000000` and
    /// relatives) and the empty reference. A project has none of them, so a
    /// reference to one is not broken.
    #[must_use]
    pub const fn is_builtin(&self) -> bool {
        self.hi == 0
    }
}

/// The value of a hexadecimal digit, given as a code point.
#[must_use]
pub const fn hex_value(c: u32) -> Option<u8> {
    match c {
        0x30..=0x39 => Some((c - 0x30) as u8),
        0x61..=0x66 => Some((c - 0x61 + 10) as u8),
        0x41..=0x46 => Some((c - 0x41 + 10) as u8),
        _ => None,
    }
}

/// Lowercase, the way Unity writes GUIDs into files.
impl fmt::Display for Guid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}{:016x}", self.hi, self.lo)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEXT: &str = "a79441f348de89743a2939f4d699eac1";

    #[test]
    fn parses_and_prints() {
        let guid = Guid::parse(TEXT);
        assert!(guid.is_some(), "32 hexadecimal digits parse");
        assert_eq!(guid.unwrap().to_string(), TEXT, "and print back the same");
        assert_eq!(
            Guid::parse("A79441F348DE89743A2939F4D699EAC1"),
            guid,
            "case does not matter"
        );
        assert_eq!(
            Guid::parse(&format!("{TEXT}0")),
            None,
            "33 digits are not a GUID"
        );
        assert_eq!(
            Guid::parse("g79441f348de89743a2939f4d699eac1"),
            None,
            "a non-hexadecimal character is not a GUID"
        );
        let mut longer = TEXT.as_bytes().to_vec();
        longer.push(b'0');
        assert_eq!(
            Guid::parse_at(&longer, 0),
            None,
            "a hexadecimal digit after it: a piece of something longer"
        );
        let units: Vec<u16> = TEXT.encode_utf16().collect();
        assert_eq!(
            Guid::parse_at(&units, 0),
            guid,
            "UTF-16 units read the same"
        );
    }

    #[test]
    fn builtin() {
        assert!(
            Guid::parse("0000000000000000e000000000000000")
                .unwrap()
                .is_builtin(),
            "a built-in resource is recognized"
        );
        assert!(
            !Guid::parse(TEXT).unwrap().is_builtin(),
            "an ordinary GUID is not built in"
        );
    }
}
