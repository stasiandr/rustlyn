//! Completion on `#` lines: the directive names after `#`, what each
//! directive takes after it (`#pragma warning disable`, `#nullable enable`),
//! and the symbols a condition can test after `#if` — those the project
//! defines, those the file `#define`s, and the usual `DEBUG` and `TRACE`.

use std::collections::BTreeSet;

use super::context::Site;
use super::{Completion, CompletionKind};

const DIRECTIVES: &[&str] = &[
    "if",
    "elif",
    "else",
    "endif",
    "region",
    "endregion",
    "define",
    "undef",
    "warning",
    "error",
    "line",
    "pragma",
    "nullable",
];

pub(super) fn complete(text: &str, site: &Site, defined: &[String], items: &mut Vec<Completion>) {
    let line_start = text[..site.start as usize]
        .rfind('\n')
        .map_or(0, |at| at + 1);
    let line = &text[line_start..site.start as usize];
    let Some(after_hash) = line.trim_start().strip_prefix('#') else {
        return;
    };
    let words: Vec<&str> = after_hash.split_whitespace().collect();
    let ends_in_space = after_hash.ends_with(char::is_whitespace);
    // The words before the one being typed.
    let complete_words: &[&str] = if ends_in_space || words.is_empty() {
        &words
    } else {
        &words[..words.len() - 1]
    };
    let keywords = |list: &[&str], items: &mut Vec<Completion>| {
        for word in list {
            items.push(Completion::keyword(word));
        }
    };
    match complete_words {
        [] => keywords(DIRECTIVES, items),
        ["pragma"] => keywords(&["warning", "checksum"], items),
        ["pragma", "warning"] => keywords(&["disable", "restore"], items),
        ["nullable"] => keywords(&["enable", "disable", "restore"], items),
        ["nullable", _] => keywords(&["warnings", "annotations"], items),
        ["line"] => keywords(&["default", "hidden"], items),
        ["if" | "elif", ..] => {
            // A symbol can follow an operator or another symbol's `!`.
            let last = after_hash.trim_end();
            let expects_symbol = complete_words.len() == 1
                || last.ends_with('!')
                || last.ends_with('(')
                || last.ends_with("&&")
                || last.ends_with("||")
                || last.ends_with("==")
                || last.ends_with("!=");
            if !expects_symbol {
                return;
            }
            let mut symbols: BTreeSet<String> = defined.iter().cloned().collect();
            symbols.extend(["DEBUG".to_string(), "TRACE".to_string()]);
            for line in text.lines() {
                let trimmed = line.trim_start();
                if let Some(rest) = trimmed.strip_prefix('#') {
                    let mut parts = rest.split_whitespace();
                    if parts.next() == Some("define")
                        && let Some(name) = parts.next()
                    {
                        symbols.insert(name.to_string());
                    }
                }
            }
            for symbol in symbols {
                items.push(Completion {
                    label: symbol,
                    kind: CompletionKind::Constant,
                    detail: "preprocessor symbol".to_string(),
                    rank: 20,
                    ..Completion::default()
                });
            }
            keywords(&["true", "false"], items);
        }
        _ => {}
    }
}
