//! String helpers: spaces as `CharacterSet.whitespaces` has them, and the
//! case-insensitive comparisons NuGet ids need.

use std::cmp::Ordering;
use std::collections::HashSet;

/// Spaces, no line breaks.
pub(crate) fn is_space(c: char) -> bool {
    matches!(
        c,
        '\t' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}' | '\u{202f}' | '\u{205f}' | '\u{3000}'
    )
}

/// U+000A–U+000D, NEL, LS, PS.
pub(crate) fn is_newline(c: char) -> bool {
    matches!(
        c,
        '\n' | '\r' | '\u{0b}' | '\u{0c}' | '\u{85}' | '\u{2028}' | '\u{2029}'
    )
}

/// Without spaces at either end.
pub(crate) fn trim_spaces(text: &str) -> &str {
    text.trim_matches(is_space)
}

/// Without spaces and line breaks at either end.
pub(crate) fn trim_blank(text: &str) -> &str {
    text.trim_matches(|c| is_space(c) || is_newline(c))
}

/// Ignoring case.
pub(crate) fn compare_ignoring_case(a: &str, b: &str) -> Ordering {
    a.to_lowercase().cmp(&b.to_lowercase())
}

pub(crate) fn equal_ignoring_case(a: &str, b: &str) -> bool {
    a == b || a.to_lowercase() == b.to_lowercase()
}

/// In order and without repeats, case ignored (NuGet ids).
pub(crate) fn unique_ignoring_case(items: impl IntoIterator<Item = String>) -> Vec<String> {
    let mut seen = HashSet::new();
    items
        .into_iter()
        .filter(|item| seen.insert(item.to_lowercase()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ignoring_case() {
        assert_eq!(
            unique_ignoring_case(["A".to_string(), "a".into(), "b".into()]),
            vec!["A", "b"]
        );
        assert!(equal_ignoring_case("Serilog", "serilog"));
        assert_eq!(compare_ignoring_case("b", "A"), Ordering::Greater);
        assert_eq!(trim_blank(" \u{a0}x\n"), "x");
        assert_eq!(trim_spaces(" x\n"), "x\n");
    }
}
