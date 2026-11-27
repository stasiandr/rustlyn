//! What .NET's `Parse` does with a string, for the strings whose outcome the
//! analysis can state.
//!
//! `int.Parse(s)` reads `s` by the current culture, which the program
//! sets and the analysis does not know: the sign is `-` in most cultures
//! and `U+061C -` in the Arabic ones (which then refuse a plain `-5`), the
//! decimal point is `.` or `,`, a group separator may be a space or a
//! point. A text is judged only by what holds in every culture the runtime
//! ships:
//!
//! - ASCII digits, the white space `\t \n \v \f \r` and the space, and the
//!   NUL that may end a string are read the same everywhere;
//! - an ASCII `+` or `-` is the sign in most cultures and nothing at all in
//!   some, so a text with one is judged both ways and the outcomes are
//!   joined;
//! - a letter, `.` or `,` means a number's exponent, point or group
//!   separator, or `NaN` and `Infinity`, in a culture-dependent way for
//!   `float`, `double` and `decimal` (the text is not judged), and nothing
//!   at all for an integer type (it fails);
//! - an ASCII character that no culture uses (`_`, `(`, `$`, a control
//!   character) makes every number type fail;
//! - a character beyond ASCII may be a culture's sign (`U+2212`, the
//!   bidirectional marks around it), and for a `float`, `double` or `decimal`
//!   a separator or a symbol: the text is not judged; any other makes an
//!   integer type fail.
//!
//! A text this does not judge has no answer (`None`); the analysis then
//! says the failure is unknown.

use rustlyn_semantics::SpecialType;

/// What a parse can come to. A set of them is a bit mask.
pub(super) const PARSED: u8 = 1;
pub(super) const FORMAT: u8 = 2;
pub(super) const OVERFLOW: u8 = 4;

/// The culture a number is read by.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Culture {
    /// The current culture, or one the analysis cannot see: any that ships.
    Any,
    /// `CultureInfo.InvariantCulture`: `+` and `-` are the signs.
    Invariant,
}

/// The type a text is read as.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Target {
    Number(SpecialType),
    Boolean,
    Char,
}

impl Target {
    /// The type as C# writes it, for saying what the text is not.
    pub(super) fn keyword(self) -> &'static str {
        match self {
            Self::Boolean => "bool",
            Self::Char => "char",
            Self::Number(special) => match special {
                SpecialType::SByte => "sbyte",
                SpecialType::Byte => "byte",
                SpecialType::Int16 => "short",
                SpecialType::UInt16 => "ushort",
                SpecialType::Int32 => "int",
                SpecialType::UInt32 => "uint",
                SpecialType::Int64 => "long",
                SpecialType::UInt64 => "ulong",
                SpecialType::Single => "float",
                SpecialType::Double => "double",
                _ => "decimal",
            },
        }
    }

    /// Whether the type has a range a text can fall outside of.
    pub(super) fn has_range(self) -> bool {
        match self {
            Self::Number(special) => !matches!(special, SpecialType::Single | SpecialType::Double),
            _ => false,
        }
    }
}

/// Whether `ch` is white space to a number: the characters `\t` to `\r`
/// and the space.
fn white(ch: u8) -> bool {
    ch == b' ' || (b'\t'..=b'\r').contains(&ch)
}

/// The largest magnitude of a type, and of a negative value of it.
fn limits(special: SpecialType) -> Option<(u128, u128)> {
    Some(match special {
        SpecialType::SByte => (127, 128),
        SpecialType::Byte => (255, 0),
        SpecialType::Int16 => (32_767, 32_768),
        SpecialType::UInt16 => (65_535, 0),
        SpecialType::Int32 => (2_147_483_647, 2_147_483_648),
        SpecialType::UInt32 => (4_294_967_295, 0),
        SpecialType::Int64 => (9_223_372_036_854_775_807, 9_223_372_036_854_775_808),
        SpecialType::UInt64 => (18_446_744_073_709_551_615, 0),
        SpecialType::Decimal => (
            79_228_162_514_264_337_593_543_950_335,
            79_228_162_514_264_337_593_543_950_335,
        ),
        _ => return None,
    })
}

/// What `Parse` of a number type does with `text`, over every culture
/// there is: the outcomes it can have, or `None` where the text is not one
/// this judges.
pub(super) fn number(text: &str, special: SpecialType, culture: Culture) -> Option<u8> {
    let bytes = text.as_bytes();
    let integral = !matches!(
        special,
        SpecialType::Single | SpecialType::Double | SpecialType::Decimal
    );
    if !text.is_ascii() {
        // An integer has no separators or symbols: beyond the characters
        // some culture signs with, nothing outside ASCII is part of one.
        let signs = ['\u{2212}', '\u{61c}', '\u{200e}', '\u{200f}'];
        return (integral && !text.contains(signs)).then_some(FORMAT);
    }
    let mut sign = false;
    for &ch in bytes {
        match ch {
            b'0'..=b'9' | b'\0' => {}
            _ if white(ch) => {}
            b'+' | b'-' => sign = true,
            b'.' | b',' => {
                if !integral {
                    return None;
                }
                return Some(FORMAT);
            }
            _ if ch.is_ascii_alphabetic() => {
                if special == SpecialType::Single || special == SpecialType::Double {
                    return None;
                }
                return Some(FORMAT);
            }
            // Nothing a culture uses in a number.
            _ => return Some(FORMAT),
        }
    }
    let trailing_sign = special == SpecialType::Decimal;
    // Each way the signs may be read: as a sign, or as nothing a number has.
    let ways: &[(bool, bool)] = match (sign, culture) {
        (false, _) => &[(true, true)],
        (true, Culture::Invariant) => &[(true, true)],
        (true, Culture::Any) => &[(true, true), (true, false), (false, true), (false, false)],
    };
    let mut outcomes = 0;
    for &(plus, minus) in ways {
        outcomes |= read(bytes, special, trailing_sign, plus, minus)?;
    }
    Some(outcomes)
}

/// One reading of a text over digits, white space, signs and NULs.
fn read(
    text: &[u8],
    special: SpecialType,
    trailing_sign: bool,
    plus: bool,
    minus: bool,
) -> Option<u8> {
    let is_sign = |ch: u8| (ch == b'+' && plus) || (ch == b'-' && minus);
    let mut at = 0;
    while at < text.len() && white(text[at]) {
        at += 1;
    }
    let mut negative = false;
    let mut signed = false;
    if at < text.len() && is_sign(text[at]) {
        negative = text[at] == b'-';
        signed = true;
        at += 1;
        // Whether white space may follow a sign depends on the culture's
        // pattern for negative numbers.
        if at < text.len() && white(text[at]) {
            return None;
        }
    }
    let first = at;
    while at < text.len() && text[at].is_ascii_digit() {
        at += 1;
    }
    let digits = &text[first..at];
    if digits.is_empty() {
        // `-` or white space alone, or something that is no number.
        return Some(FORMAT);
    }
    if at < text.len() && is_sign(text[at]) {
        if !trailing_sign || signed {
            return Some(FORMAT);
        }
        negative = text[at] == b'-';
        at += 1;
    }
    let digits_end = at;
    while at < text.len() && white(text[at]) {
        at += 1;
    }
    // A space is a group separator in some cultures: the digits of a
    // fraction-bearing type may go on after it.
    if at > digits_end
        && at < text.len()
        && text[at].is_ascii_digit()
        && matches!(
            special,
            SpecialType::Single | SpecialType::Double | SpecialType::Decimal
        )
    {
        return None;
    }
    // A string may end in NULs.
    if text[at..].iter().any(|&ch| ch != b'\0') {
        // A sign after white space after digits is a pattern some cultures
        // have and some do not.
        if trailing_sign
            && !signed
            && text[at..].iter().any(|&ch| is_sign(ch))
            && text[at..]
                .iter()
                .all(|&ch| ch == b'\0' || white(ch) || is_sign(ch))
        {
            return None;
        }
        return Some(FORMAT);
    }
    let Some((positive, below)) = limits(special) else {
        return Some(PARSED);
    };
    let significant = {
        let start = digits
            .iter()
            .position(|&d| d != b'0')
            .unwrap_or(digits.len());
        &digits[start..]
    };
    if significant.len() > 39 {
        return Some(OVERFLOW);
    }
    let magnitude: u128 = significant
        .iter()
        .fold(0, |acc, &d| acc * 10 + u128::from(d - b'0'));
    let limit = if negative && special != SpecialType::Decimal {
        below
    } else {
        positive
    };
    let fits = if negative && below == 0 && special != SpecialType::Decimal {
        // `-0` is zero for an unsigned type; any other negative is out.
        magnitude == 0
    } else {
        magnitude <= limit
    };
    Some(if fits { PARSED } else { OVERFLOW })
}

/// What `bool.Parse` does with `text`: culture does not matter, and the
/// ends of it are trimmed of white space and NULs.
pub(super) fn boolean(text: &str) -> Option<u8> {
    if !text.is_ascii() {
        return None;
    }
    let trimmed = text.trim_matches(|c: char| c == '\0' || white(c as u8));
    Some(
        if trimmed.eq_ignore_ascii_case("true") || trimmed.eq_ignore_ascii_case("false") {
            PARSED
        } else {
            FORMAT
        },
    )
}

/// What `char.Parse` does with `text`: exactly one UTF-16 unit.
pub(super) fn character(text: &str) -> u8 {
    if text.encode_utf16().count() == 1 {
        PARSED
    } else {
        FORMAT
    }
}

/// What parsing `text` as `target` comes to.
pub(super) fn outcomes(text: &str, target: Target, culture: Culture) -> Option<u8> {
    match target {
        Target::Number(special) => number(text, special, culture),
        Target::Boolean => boolean(text),
        Target::Char => Some(character(text)),
    }
}
