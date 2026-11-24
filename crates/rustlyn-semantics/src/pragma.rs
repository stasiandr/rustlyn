//! `#pragma warning disable` and `#pragma warning restore`: which warnings a
//! file has switched off, and from where to where.
//!
//! The directives are trivia, read in the order they are written; a warning
//! is reported unless the last directive before it that names its code, or
//! names none and so means every code, disabled it. Errors cannot be turned
//! off this way, and nothing here tries to.

use rustlyn_diagnostics::{Diagnostic, Severity};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

/// The `#pragma warning` directives of one file, in order.
#[derive(Clone, Debug, Default)]
pub struct WarningState {
    /// Where each directive is, whether it disables, and the codes it names
    /// (`None` for all of them).
    directives: Vec<(u32, bool, Option<Vec<u16>>)>,
}

impl WarningState {
    /// Reads the directives out of a file.
    #[must_use]
    pub fn of(root: &SyntaxNode) -> Self {
        let mut directives = Vec::new();
        for token in root.descendant_tokens() {
            for trivia in token
                .leading_trivia()
                .into_iter()
                .chain(token.trailing_trivia())
            {
                if trivia.kind() != SyntaxKind::PragmaWarningDirectiveTrivia {
                    continue;
                }
                if let Some((disable, codes)) = parse(trivia.text()) {
                    directives.push((trivia.span().start(), disable, codes));
                }
            }
        }
        directives.sort_by_key(|(at, _, _)| *at);
        Self { directives }
    }

    /// Whether a directive before the diagnostic switched it off.
    #[must_use]
    pub fn is_suppressed(&self, diagnostic: &Diagnostic) -> bool {
        if diagnostic.severity() == Severity::Error {
            return false;
        }
        let code = diagnostic.code().number();
        let at = diagnostic.span().start();
        let mut disabled = false;
        for (position, disable, codes) in &self.directives {
            if *position > at {
                break;
            }
            if codes.as_ref().is_none_or(|codes| codes.contains(&code)) {
                disabled = *disable;
            }
        }
        disabled
    }

    /// Whether the file has any directive at all, which is most files not.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.directives.is_empty()
    }
}

/// `#pragma warning disable CS0618, 168 // why` as whether it disables and
/// which codes it names; `None` for a `#pragma` that is not about warnings.
fn parse(text: &str) -> Option<(bool, Option<Vec<u16>>)> {
    let text = text.split("//").next().unwrap_or(text);
    let mut words = text
        .trim()
        .trim_start_matches('#')
        .trim_start()
        .strip_prefix("pragma")?
        .trim_start()
        .strip_prefix("warning")?
        .trim_start()
        .splitn(2, char::is_whitespace);
    let disable = match words.next()? {
        "disable" => true,
        "restore" => false,
        _ => return None,
    };
    let rest = words.next().unwrap_or("").trim();
    if rest.is_empty() {
        return Some((disable, None));
    }
    // Codes of other tools — `IDE0051`, `RS0016` — are named too, and match
    // nothing here.
    let codes = rest
        .split(',')
        .filter_map(|code| {
            let code = code.trim();
            let digits = code.strip_prefix("CS").unwrap_or(code);
            digits.parse::<u16>().ok()
        })
        .collect();
    Some((disable, Some(codes)))
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn a_directive_names_its_codes_or_all_of_them() {
        assert_eq!(
            parse("#pragma warning disable CS0618 // obsolete"),
            Some((true, Some(vec![618])))
        );
        assert_eq!(
            parse("#pragma warning restore 168, CS0219"),
            Some((false, Some(vec![168, 219])))
        );
        assert_eq!(parse("#pragma warning disable"), Some((true, None)));
        assert_eq!(
            parse("#pragma warning disable IDE0051"),
            Some((true, Some(vec![])))
        );
        assert_eq!(parse("#pragma checksum \"a\" \"{0}\" \"1\""), None);
    }
}
