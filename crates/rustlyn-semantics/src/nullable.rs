//! `#nullable`: where a file annotates its reference types.
//!
//! In an annotated context `string` is a string that is not null and
//! `string?` one that may be; outside one both are simply `string`, which
//! is what metadata calls oblivious. Only the annotations matter to what a
//! compilation writes: `#nullable enable warnings` and its kin change what
//! is reported, not what a declaration says.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};

/// The `#nullable` directives of one file that set its annotation
/// context, in order.
#[derive(Clone, Debug, Default)]
pub struct NullableContexts {
    /// Where each directive is, and whether it turns annotations on (`Some
    /// (true)`), off, or back to the compilation's setting (`None`).
    directives: Vec<(u32, Option<bool>)>,
}

impl NullableContexts {
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
                if trivia.kind() != SyntaxKind::NullableDirectiveTrivia {
                    continue;
                }
                if let Some(setting) = parse(trivia.text()) {
                    directives.push((trivia.span().start(), setting));
                }
            }
        }
        directives.sort_by_key(|(at, _)| *at);
        Self { directives }
    }

    /// Whether annotations are on at `position`, where `default` is the
    /// compilation's own setting (`/nullable`).
    #[must_use]
    pub fn annotations_at(&self, position: u32, default: bool) -> bool {
        let mut enabled = default;
        for (at, setting) in &self.directives {
            if *at > position {
                break;
            }
            enabled = setting.unwrap_or(default);
        }
        enabled
    }
}

/// What one directive does to annotations: `None` for nothing at all (it
/// sets only the warnings, or cannot be read), `Some(None)` for `restore`.
fn parse(text: &str) -> Option<Option<bool>> {
    let text = text.trim_start().strip_prefix('#')?.trim_start();
    let text = text.strip_prefix("nullable")?;
    // A comment may follow the directive on its line.
    let text = text.split("//").next().unwrap_or_default();
    let mut words = text.split_whitespace();
    let setting = match words.next()? {
        "enable" => Some(true),
        "disable" => Some(false),
        "restore" => None,
        _ => return None,
    };
    match words.next() {
        None | Some("annotations") => Some(setting),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn directives_set_annotations_unless_they_name_only_the_warnings() {
        assert_eq!(parse("#nullable enable"), Some(Some(true)));
        assert_eq!(parse("# nullable disable annotations"), Some(Some(false)));
        assert_eq!(parse("#nullable restore // back"), Some(None));
        assert_eq!(parse("#nullable enable warnings"), None);
        assert_eq!(parse("#nullable"), None);
    }
}
