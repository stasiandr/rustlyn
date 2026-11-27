//! Small text helpers the value graph shares: spaces, letters, paths and
//! reading a source file the way the project index reads it.

use std::path::Path;

/// A space or tab, or one of Unicode's space separators — not a newline.
#[must_use]
pub fn is_space(c: char) -> bool {
    matches!(
        c,
        '\t' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}' | '\u{202f}' | '\u{205f}' | '\u{3000}'
    )
}

/// The text without spaces (not newlines) at either end.
#[must_use]
pub fn trim_spaces(text: &str) -> &str {
    text.trim_matches(is_space)
}

/// A letter, digit or `_`: what words are made of.
#[must_use]
pub fn is_word(c: char) -> bool {
    c.is_alphabetic() || c.is_numeric() || c == '_'
}

/// The words of a text: runs of letters, digits and `_`.
pub fn words(text: &str) -> impl Iterator<Item = &str> {
    text.split(|c: char| !is_word(c)).filter(|w| !w.is_empty())
}

/// The lines of a text split at `\n`, where `\r\n` counts as one character
/// and is not split. Empty pieces stay.
#[must_use]
pub fn split_lf_letters(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut result = Vec::new();
    let mut start = 0;
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'\n' && !(i > 0 && bytes[i - 1] == b'\r') {
            result.push(&text[start..i]);
            start = i + 1;
        }
    }
    result.push(&text[start..]);
    result
}

/// The letters (grapheme clusters, for ordinary text) of a string:
/// combining marks, variation selectors and what follows a zero-width
/// joiner belong to the letter before; `\r\n` is one letter.
#[must_use]
pub fn letters(text: &str) -> Vec<&str> {
    let mut result: Vec<&str> = Vec::new();
    let mut start: Option<usize> = None;
    let mut previous: Option<char> = None;
    for (i, c) in text.char_indices() {
        let joins = match previous {
            None => false,
            Some('\r') => c == '\n',
            Some('\u{200d}') => true,
            Some(_) => is_extending(c),
        };
        if !joins {
            if let Some(s) = start {
                result.push(&text[s..i]);
            }
            start = Some(i);
        }
        previous = Some(c);
    }
    if let Some(s) = start {
        result.push(&text[s..]);
    }
    result
}

const fn is_extending(c: char) -> bool {
    matches!(c,
        '\u{300}'..='\u{36f}' | '\u{483}'..='\u{489}' | '\u{591}'..='\u{5bd}' | '\u{610}'..='\u{61a}'
        | '\u{64b}'..='\u{65f}' | '\u{1ab0}'..='\u{1aff}' | '\u{1dc0}'..='\u{1dff}' | '\u{200c}' | '\u{200d}'
        | '\u{20d0}'..='\u{20ff}' | '\u{fe00}'..='\u{fe0f}' | '\u{fe20}'..='\u{fe2f}'
        | '\u{1f3fb}'..='\u{1f3ff}' | '\u{e0020}'..='\u{e007f}' | '\u{e0100}'..='\u{e01ef}')
}

/// The first `n` letters of a string.
#[must_use]
pub fn prefix_letters(text: &str, n: usize) -> &str {
    let all = letters(text);
    if all.len() <= n {
        return text;
    }
    let end = all[n].as_ptr() as usize - text.as_ptr() as usize;
    &text[..end]
}

fn is_separator(c: char) -> bool {
    c == '/' || (cfg!(windows) && c == '\\')
}

/// The last component of a path.
#[must_use]
pub fn last_component(path: &str) -> &str {
    let trimmed = path.trim_end_matches(is_separator);
    if trimmed.is_empty() {
        return if path.is_empty() { "" } else { "/" };
    }
    trimmed.rsplit(is_separator).next().unwrap_or(trimmed)
}

/// The folder above a path.
#[must_use]
pub fn parent(path: &str) -> String {
    let trimmed = path.trim_end_matches(is_separator);
    match trimmed.rfind(is_separator) {
        Some(0) | None => "/".to_owned(),
        Some(i) => trimmed[..i].to_owned(),
    }
}

/// `relative` under `root`. A Windows root (`C:\…`) continues with `\`.
#[must_use]
pub fn join(root: &str, relative: &str) -> String {
    if root.ends_with(is_separator) {
        format!("{root}{relative}")
    } else if cfg!(windows) && root.contains('\\') {
        format!("{root}\\{relative}")
    } else {
        format!("{root}/{relative}")
    }
}

/// The file's extension, without the dot.
#[must_use]
pub fn extension(path: &str) -> &str {
    let name = last_component(path);
    match name.rfind('.') {
        Some(i) if i > 0 => &name[i + 1..],
        _ => "",
    }
}

/// The file's name without its extension.
#[must_use]
pub fn stem(path: &str) -> &str {
    let name = last_component(path);
    match name.rfind('.') {
        Some(i) if i > 0 => &name[..i],
        _ => name,
    }
}

/// Source files larger than this are not read: they are generated data,
/// not code anyone writes values in.
pub const MAX_SOURCE_BYTES: usize = 1 << 20;

/// A source file from disk: at most [`MAX_SOURCE_BYTES`], no NUL bytes in
/// its first 8 KiB, read as the compiler reads it.
#[must_use]
pub fn read_source(path: impl AsRef<Path>) -> Option<String> {
    let data = std::fs::read(path.as_ref()).ok()?;
    if data.len() > MAX_SOURCE_BYTES || data[..data.len().min(8192)].contains(&0) {
        return None;
    }
    Some(rustlyn_ide::document::decode_source(&data))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lines_letters_and_paths() {
        assert_eq!(split_lf_letters("a\nb\r\nc"), vec!["a", "b\r\nc"]);
        assert_eq!(letters("e\u{301}x\r\n").len(), 3);
        assert_eq!(prefix_letters("abc", 2), "ab");
        assert_eq!(last_component("/work/game"), "game");
        assert_eq!(parent("/work/game"), "/work");
        assert_eq!(parent("/game"), "/");
        assert_eq!(join("/", "x"), "/x");
        assert_eq!(stem("/a/B.cs"), "B");
        assert_eq!(extension("/a/B.cs"), "cs");
        assert_eq!(trim_spaces("\u{a0} x\u{2003}"), "x");
    }
}
