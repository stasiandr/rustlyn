//! Character classification, following §6.3 and §6.4 of the C# specification.
//!
//! The non-ASCII rules are approximated with the Unicode properties `std`
//! exposes rather than the exact `Lu/Ll/Lt/Lm/Lo/Nl/Nd/Pc/Mn/Mc/Cf` category
//! tables the specification names. The two agree on every ASCII character and
//! on ordinary letters; they can disagree on rare marks and format characters.

/// Whether `ch` is whitespace.
///
/// This mirrors Roslyn, including the two characters it accepts for
/// compatibility with the native compiler even though they are not in
/// category `Zs`: the byte-order mark and `SUB`.
#[must_use]
pub(crate) const fn is_whitespace(ch: char) -> bool {
    matches!(
        ch,
        ' ' | '\t' | '\u{000B}' | '\u{000C}' | '\u{001A}' | '\u{FEFF}'
    ) || is_space_separator(ch)
}

/// Category `Zs`, spelled out because `std` has no category query.
const fn is_space_separator(ch: char) -> bool {
    matches!(
        ch,
        '\u{0020}' | '\u{00A0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200A}' | '\u{202F}' | '\u{205F}' | '\u{3000}'
    )
}

/// Whether `ch` can start an identifier.
#[must_use]
pub(crate) fn is_identifier_start(ch: char) -> bool {
    if ch.is_ascii() {
        ch.is_ascii_alphabetic() || ch == '_'
    } else {
        ch.is_alphabetic()
    }
}

/// Whether `ch` can continue an identifier.
#[must_use]
pub(crate) fn is_identifier_part(ch: char) -> bool {
    if ch.is_ascii() {
        ch.is_ascii_alphanumeric() || ch == '_'
    } else {
        ch.is_alphanumeric() || is_connecting_or_formatting(ch)
    }
}

/// Whether `ch` is a formatting character (category `Cf`), which an
/// identifier may contain and which is no part of the name it spells.
#[must_use]
pub(crate) const fn is_formatting(ch: char) -> bool {
    matches!(
        ch,
        '\u{00AD}'
            | '\u{0600}'..='\u{0605}'
            | '\u{061C}'
            | '\u{06DD}'
            | '\u{070F}'
            | '\u{08E2}'
            | '\u{180E}'
            | '\u{200B}'..='\u{200F}'
            | '\u{202A}'..='\u{202E}'
            | '\u{2060}'..='\u{2064}'
            | '\u{2066}'..='\u{206F}'
            | '\u{FEFF}'
            | '\u{FFF9}'..='\u{FFFB}'
            | '\u{110BD}'
            | '\u{110CD}'
            | '\u{13430}'..='\u{1343F}'
            | '\u{1BCA0}'..='\u{1BCA3}'
            | '\u{1D173}'..='\u{1D17A}'
            | '\u{E0001}'
            | '\u{E0020}'..='\u{E007F}'
    )
}

/// The parts of categories `Pc` and `Cf` that turn up in real identifiers.
const fn is_connecting_or_formatting(ch: char) -> bool {
    matches!(
        ch,
        '\u{00AD}'
            | '\u{200B}'..='\u{200F}'
            | '\u{202A}'..='\u{202E}'
            | '\u{203F}'..='\u{2040}'
            | '\u{2054}'
            | '\u{2060}'..='\u{2064}'
            | '\u{206A}'..='\u{206F}'
            | '\u{FE33}'..='\u{FE34}'
            | '\u{FE4D}'..='\u{FE4F}'
            | '\u{FEFF}'
            | '\u{FF3F}'
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whitespace_excludes_line_breaks() {
        assert!(is_whitespace(' '));
        assert!(is_whitespace('\t'));
        assert!(is_whitespace('\u{000C}'));
        assert!(is_whitespace('\u{00A0}'));
        assert!(is_whitespace('\u{3000}'));
        assert!(!is_whitespace('\n'));
        assert!(!is_whitespace('\r'));
        assert!(!is_whitespace('a'));
    }

    #[test]
    fn identifier_characters() {
        assert!(is_identifier_start('_'));
        assert!(is_identifier_start('A'));
        assert!(is_identifier_start('я'));
        assert!(!is_identifier_start('1'));
        assert!(!is_identifier_start('$'));
        assert!(is_identifier_part('1'));
        assert!(is_identifier_part('_'));
        assert!(!is_identifier_part('-'));
    }
}
