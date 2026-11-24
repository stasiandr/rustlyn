//! Which typed characters open the completion list — Roslyn's trigger
//! rules. The list opens on the first letter of a word, on `.`, on a space
//! after the few keywords whose next word completion knows best (`new`,
//! `override`, `using`, `case`, `is`, `as`, `partial`), on `#` at the start
//! of a line, and on `<` in a documentation comment. It stays shut inside
//! comments and strings, after a digit, and on `(` and `,`: signature help
//! answers those.

use rustlyn_syntax::{ParseOptions, SyntaxNode, parse_with};
use rustlyn_text::SourceText;

use super::context::{Spot, in_trivia, token_before};

/// Keywords a space after which opens the list.
const SPACE_AFTER: &[&str] = &[
    "new", "override", "using", "case", "is", "as", "partial", "static", "goto",
];

/// Directives a space after which opens the list.
const SPACE_AFTER_DIRECTIVE: &[&str] = &["if", "elif", "pragma", "nullable", "warning"];

/// Whether typing `typed`, which ends at byte `offset` of `text` (the text
/// with it typed), should open the completion list.
#[must_use]
pub fn completion_trigger(text: &str, offset: u32, typed: char) -> bool {
    let offset = (offset as usize).min(text.len());
    let Some(before_typed) = offset.checked_sub(typed.len_utf8()) else {
        return false;
    };
    if !text.is_char_boundary(before_typed) {
        return false;
    }
    let previous = text[..before_typed].chars().next_back();
    let line_start = text[..before_typed].rfind('\n').map_or(0, |at| at + 1);
    let line = &text[line_start..before_typed];

    let tree = parse_with(
        SourceText::new("", text.to_string()),
        &ParseOptions::default(),
    );
    let root = tree.root();
    let place = in_trivia(&root, offset as u32);
    match place {
        Some(Spot::Documentation) => {
            return typed == '<'
                || (is_word_start(typed) && previous == Some('<'))
                || (typed == '"' && line.trim_end().ends_with('='));
        }
        Some(Spot::Directive) => {
            let directive = line.trim_start();
            return match typed {
                '#' => directive.is_empty(),
                ' ' => {
                    let word = directive.trim_start_matches('#').trim();
                    SPACE_AFTER_DIRECTIVE.contains(&word)
                        || word == "pragma warning"
                        || word.ends_with("&&")
                        || word.ends_with("||")
                }
                c if is_word_start(c) => !previous.is_some_and(is_word_char),
                _ => false,
            };
        }
        Some(_) => return false,
        None => {}
    }
    if in_open_text(&root, before_typed as u32) {
        return false;
    }
    match typed {
        '#' => line.trim().is_empty(),
        '.' => {
            // Not a decimal point, not the second dot of `..`.
            !previous.is_some_and(|c| c.is_ascii_digit() || c == '.')
                && token_before(&root, before_typed as u32)
                    .is_some_and(|token| !token.kind().is_literal_token())
        }
        ':' => previous == Some(':'),
        ' ' => {
            let word: String = text[..before_typed]
                .chars()
                .rev()
                .take_while(|c| is_word_char(*c))
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .collect();
            SPACE_AFTER.contains(&word.as_str())
        }
        c if is_word_start(c) => {
            // The first letter of a word, not one in the middle or after a
            // number.
            !previous.is_some_and(|c| is_word_char(c) || c == '@' || c == '$')
        }
        _ => false,
    }
}

fn is_word_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Whether `offset` is inside a string or character literal, closed or not.
fn in_open_text(root: &SyntaxNode, offset: u32) -> bool {
    let Some(token) = offset.checked_sub(1).and_then(|at| root.find_token(at)) else {
        return false;
    };
    let span = token.span();
    if !(span.start() < offset && offset <= span.end()) {
        return false;
    }
    let text = token.text();
    let kind = token.kind();
    if offset < span.end() {
        return kind.is_literal_token()
            || matches!(
                kind,
                rustlyn_syntax::SyntaxKind::InterpolatedStringTextToken
                    | rustlyn_syntax::SyntaxKind::InterpolatedStringStartToken
            );
    }
    match kind {
        rustlyn_syntax::SyntaxKind::StringLiteralToken => {
            text.len() < 2 || !text.ends_with('"') || text == "@\""
        }
        rustlyn_syntax::SyntaxKind::CharacterLiteralToken => {
            text.len() < 2 || !text.ends_with('\'')
        }
        rustlyn_syntax::SyntaxKind::InterpolatedStringTextToken
        | rustlyn_syntax::SyntaxKind::InterpolatedStringStartToken => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::completion_trigger;

    fn triggers(text: &str, typed: char) -> bool {
        completion_trigger(text, text.len() as u32, typed)
    }

    #[test]
    fn letters_open_the_list_at_the_start_of_a_word() {
        assert!(triggers("class C { void M() { x", 'x'));
        assert!(!triggers("class C { void M() { xy", 'y'));
        assert!(!triggers("class C { void M() { var a = 1e", 'e'));
    }

    #[test]
    fn a_dot_opens_it_but_not_in_a_number() {
        assert!(triggers("class C { void M() { this.", '.'));
        assert!(!triggers("class C { void M() { var x = 1.", '.'));
        assert!(!triggers("class C { void M() { var r = a..", '.'));
    }

    #[test]
    fn a_space_opens_it_after_the_keywords_that_want_one() {
        assert!(triggers("class C { void M() { var x = new ", ' '));
        assert!(triggers("class C : B { override ", ' '));
        assert!(triggers("using ", ' '));
        assert!(!triggers("class C { void M() { return ", ' '));
        assert!(!triggers("class C { void M() { F(", '('));
        assert!(!triggers("class C { void M() { F(a,", ','));
    }

    #[test]
    fn comments_and_strings_stay_shut_but_documentation_opens_on_a_bracket() {
        assert!(!triggers("class C { void M() { // x", 'x'));
        assert!(!triggers("class C { void M() { var s = \"a", 'a'));
        assert!(!triggers("class C { void M() { var s = \"a.", '.'));
        assert!(triggers("class C {\n    /// <", '<'));
        assert!(!triggers("class C { void M() { if (a <", '<'));
    }

    #[test]
    fn a_hash_opens_it_at_the_start_of_a_line() {
        assert!(triggers("class C {\n#", '#'));
        assert!(triggers("#if ", ' '));
        assert!(!triggers("class C { void M() { var s = $\"{a}#", '#'));
    }
}
