//! String and character literals, and the escape sequences inside them.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_text::is_line_break;

use super::chars::is_whitespace;
use super::{Lexer, Scan};
use crate::{SyntaxKind, TokenValue};

const HIGH_SURROGATES: std::ops::RangeInclusive<u32> = 0xD800..=0xDBFF;
const LOW_SURROGATES: std::ops::RangeInclusive<u32> = 0xDC00..=0xDFFF;

impl Lexer<'_> {
    /// Scans `"..."`, including its escape sequences and an optional `u8`
    /// suffix.
    pub(crate) fn scan_string_literal(&mut self) -> Scan {
        let start = self.position();
        self.bump(); // opening quote
        let mut value = String::new();

        loop {
            match self.peek() {
                Some('"') => {
                    self.bump();
                    break;
                }
                Some('\\') => {
                    if let Some(ch) = self.scan_escape_sequence() {
                        value.push(ch);
                    }
                }
                // A regular string literal may not span lines.
                Some(ch) if is_line_break(ch) => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    break;
                }
                Some(ch) => {
                    self.bump();
                    value.push(ch);
                }
                None => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    break;
                }
            }
        }

        let kind = if self.eat_utf8_suffix() {
            SyntaxKind::Utf8StringLiteralToken
        } else {
            SyntaxKind::StringLiteralToken
        };
        Scan::kind(kind).with_value(TokenValue::String(value.into()))
    }

    /// Scans `@"..."`, where the only escape is a doubled quote and line breaks
    /// are part of the value.
    pub(crate) fn scan_verbatim_string_literal(&mut self) -> Scan {
        let start = self.position();
        self.bump(); // `@`
        self.bump(); // opening quote
        let mut value = String::new();

        loop {
            match self.peek() {
                Some('"') => {
                    self.bump();
                    if self.eat('"') {
                        value.push('"');
                    } else {
                        break;
                    }
                }
                Some(ch) => {
                    self.bump();
                    value.push(ch);
                }
                None => {
                    self.error(
                        ErrorCode::ErrUnterminatedStringLit,
                        self.span_from(start),
                        &[],
                    );
                    break;
                }
            }
        }

        let kind = if self.eat_utf8_suffix() {
            SyntaxKind::Utf8StringLiteralToken
        } else {
            SyntaxKind::StringLiteralToken
        };
        Scan::kind(kind).with_value(TokenValue::String(value.into()))
    }

    /// Scans `'c'`.
    pub(crate) fn scan_character_literal(&mut self) -> Scan {
        let start = self.position();
        self.bump(); // opening quote
        let mut value = String::new();

        loop {
            match self.peek() {
                Some('\'') => {
                    self.bump();
                    break;
                }
                Some('\\') => {
                    if let Some(ch) = self.scan_escape_sequence() {
                        value.push(ch);
                    }
                }
                Some(ch) if is_line_break(ch) => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    break;
                }
                Some(ch) => {
                    self.bump();
                    value.push(ch);
                }
                None => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    break;
                }
            }
        }

        // A C# `char` is one UTF-16 code unit, so an astral character such as
        // an emoji is two characters too many, not one character exactly.
        let units: usize = value.chars().map(char::len_utf16).sum();
        if units != 1 {
            let code = if units == 0 {
                ErrorCode::ErrEmptyCharConst
            } else {
                ErrorCode::ErrTooManyCharsInConst
            };
            self.error(code, self.span_from(start), &[]);
        }

        let scan = Scan::kind(SyntaxKind::CharacterLiteralToken);
        match value.chars().next() {
            Some(ch) => scan.with_value(TokenValue::Char(ch)),
            None => scan,
        }
    }

    /// Consumes the `u8` suffix that turns a string literal into a
    /// `ReadOnlySpan<byte>`.
    pub(crate) fn eat_utf8_suffix(&mut self) -> bool {
        if matches!(self.peek(), Some('u' | 'U')) && self.peek_nth(1) == Some('8') {
            self.advance(2);
            true
        } else {
            false
        }
    }

    /// Scans a `\`-escape and returns the character it denotes.
    ///
    /// Returns `None` when the escape is malformed; a diagnostic has been
    /// reported and the offending text consumed, so the caller can carry on.
    fn scan_escape_sequence(&mut self) -> Option<char> {
        let start = self.position();

        match self.peek_nth(1) {
            Some('u' | 'U') => {
                let value = self.scan_unicode_escape_value()?;
                if let Some(ch) = char::from_u32(value) {
                    return Some(ch);
                }
                // A surrogate pair spells a real character.
                if HIGH_SURROGATES.contains(&value)
                    && self.peeks_low_surrogate()
                    && let Some(low) = self.scan_unicode_escape_value()
                {
                    let combined = 0x1_0000 + ((value - 0xD800) << 10) + (low - 0xDC00);
                    return char::from_u32(combined);
                }
                // A lone surrogate is legal C#, whose strings are UTF-16
                // sequences rather than sequences of characters. A Rust string
                // cannot hold one, so the token keeps its text and the decoded
                // value gets a replacement character in its place.
                Some(char::REPLACEMENT_CHARACTER)
            }
            Some('x') => {
                self.advance(2); // `\x`
                let mut value = 0u32;
                let mut digits = 0;
                while digits < 4 {
                    let Some(digit) = self.peek().and_then(|ch| ch.to_digit(16)) else {
                        break;
                    };
                    self.bump();
                    value = value * 16 + digit;
                    digits += 1;
                }
                if digits == 0 {
                    self.error(ErrorCode::ErrIllegalEscape, self.span_from(start), &[]);
                    return None;
                }
                // Four digits at most: nothing but a surrogate fails to be a
                // character, and a lone one is legal C# — the decoded value
                // gets a replacement character, as for `\u` (see above).
                Some(char::from_u32(value).unwrap_or(char::REPLACEMENT_CHARACTER))
            }
            Some(ch) => {
                self.bump(); // `\`
                self.bump(); // the escape character
                match ch {
                    '\'' => Some('\''),
                    '"' => Some('"'),
                    '\\' => Some('\\'),
                    '0' => Some('\0'),
                    'a' => Some('\u{0007}'),
                    'b' => Some('\u{0008}'),
                    'e' => Some('\u{001B}'),
                    'f' => Some('\u{000C}'),
                    'n' => Some('\n'),
                    'r' => Some('\r'),
                    't' => Some('\t'),
                    'v' => Some('\u{000B}'),
                    _ => {
                        self.error(ErrorCode::ErrIllegalEscape, self.span_from(start), &[]);
                        None
                    }
                }
            }
            None => {
                self.bump(); // the dangling backslash
                self.error(ErrorCode::ErrIllegalEscape, self.span_from(start), &[]);
                None
            }
        }
    }

    /// Whether a `\uXXXX` escape naming a low surrogate follows, without
    /// consuming it: a high surrogate only pairs with one of those.
    fn peeks_low_surrogate(&self) -> bool {
        if !self.at("\\u") {
            return false;
        }
        let mut value = 0u32;
        for offset in 0..4 {
            match self.peek_nth(2 + offset).and_then(|ch| ch.to_digit(16)) {
                Some(digit) => value = value * 16 + digit,
                None => return false,
            }
        }
        LOW_SURROGATES.contains(&value)
    }

    /// Scans `\uXXXX` or `\UXXXXXXXX` and returns the code point.
    ///
    /// The value may be a surrogate; deciding what to do with one is the
    /// caller's business, since an identifier and a string literal differ.
    pub(crate) fn scan_unicode_escape_value(&mut self) -> Option<u32> {
        let start = self.position();
        self.bump(); // `\`
        let long = self.bump() == Some('U');
        let width = if long { 8 } else { 4 };

        let mut value = 0u32;
        for _ in 0..width {
            let Some(digit) = self.peek().and_then(|ch| ch.to_digit(16)) else {
                self.error(ErrorCode::ErrIllegalEscape, self.span_from(start), &[]);
                return None;
            };
            self.bump();
            value = value * 16 + digit;
        }

        if value > char::MAX as u32 {
            self.error(ErrorCode::ErrIllegalEscape, self.span_from(start), &[]);
            return None;
        }
        Some(value)
    }
}

impl Lexer<'_> {
    /// Whether a raw string literal starts at the cursor.
    ///
    /// Raw strings open with at least three quotes, optionally preceded by the
    /// `$` of an interpolated one.
    pub(crate) fn at_raw_string(&self) -> bool {
        let mut offset = 0;
        while self.peek_nth(offset) == Some('$') {
            offset += 1;
        }
        (0..3).all(|extra| self.peek_nth(offset + extra) == Some('"'))
    }

    /// Scans `"""..."""`.
    ///
    /// The delimiter can be any run of three or more quotes, which is the
    /// point: a string containing `""` just needs a longer fence. A multi-line
    /// raw string also strips the indentation its closing fence sits at, so the
    /// text can be indented with the code around it.
    pub(crate) fn scan_raw_string_literal(&mut self) -> Scan {
        let source = self.source_str();
        let start = self.position();

        let mut interpolated = false;
        while self.peek() == Some('$') {
            self.bump();
            interpolated = true;
        }

        let mut fence = 0usize;
        while self.peek() == Some('"') {
            self.bump();
            fence += 1;
        }
        let content_start = self.position();

        // Whether the literal is multi-line is decided by the opening fence
        // alone: if nothing but whitespace follows it to the end of the line,
        // the content starts on the next line. The two forms end by different
        // rules, so this has to be settled before scanning the content.
        let multi_line = self
            .rest()
            .chars()
            .take_while(|&ch| !is_line_break(ch))
            .all(is_whitespace);

        let content_end = if multi_line {
            self.scan_multi_line_raw_string_body(start, fence)
        } else {
            self.scan_single_line_raw_string_body(start, fence)
        };

        // `"""..."""u8` is a sequence of bytes rather than of characters.
        let utf8 = self.eat_utf8_suffix();
        let kind = match (multi_line, utf8) {
            (true, false) => SyntaxKind::MultiLineRawStringLiteralToken,
            (false, false) => SyntaxKind::SingleLineRawStringLiteralToken,
            (true, true) => SyntaxKind::Utf8MultiLineRawStringLiteralToken,
            (false, true) => SyntaxKind::Utf8SingleLineRawStringLiteralToken,
        };
        let scan = Scan::kind(kind);

        // The holes of an interpolated raw string are not taken apart yet, so
        // it carries no value for the binder to read.
        if interpolated {
            return scan;
        }
        let content = &source[content_start as usize..content_end as usize];
        scan.with_value(TokenValue::String(if multi_line {
            trim_raw_string(content).into()
        } else {
            content.into()
        }))
    }

    /// Scans to the end of a single-line raw string, whose content stops at the
    /// first run of at least `fence` quotes. Returns where the content ends.
    fn scan_single_line_raw_string_body(&mut self, start: u32, fence: usize) -> u32 {
        loop {
            match self.peek() {
                // A single-line raw string may not cross a line break, and the
                // break itself belongs to the next line rather than the token.
                None => {
                    self.error(
                        ErrorCode::ErrUnterminatedStringLit,
                        self.span_from(start),
                        &[],
                    );
                    return self.position();
                }
                Some(ch) if is_line_break(ch) => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    return self.position();
                }
                Some('"') => {
                    let quote_start = self.position();
                    let mut run = 0usize;
                    while self.peek() == Some('"') {
                        self.bump();
                        run += 1;
                    }
                    if run >= fence {
                        // Only the last `fence` quotes close the string, so
                        // `"""he said "hi""""` ends with a quote of its own.
                        return quote_start + (run - fence) as u32;
                    }
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    /// Scans to the end of a multi-line raw string. Only a run of at least
    /// `fence` quotes that starts a line, preceded by nothing but whitespace,
    /// closes it; anywhere else such a run is content. That is what lets a raw
    /// string quote raw strings. Returns where the content ends.
    fn scan_multi_line_raw_string_body(&mut self, start: u32, fence: usize) -> u32 {
        loop {
            match self.peek() {
                None => {
                    self.error(
                        ErrorCode::ErrUnterminatedStringLit,
                        self.span_from(start),
                        &[],
                    );
                    return self.position();
                }
                Some('"') => {
                    let quote_start = self.position();
                    let at_line_start = self.at_line_start(quote_start);
                    while self.peek() == Some('"') {
                        self.bump();
                    }
                    if at_line_start && self.position() - quote_start >= fence as u32 {
                        // The whole run is the closing delimiter; the content
                        // stops before the line's indentation is reached.
                        return quote_start;
                    }
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }
}

/// Removes the opening line break and the closing fence's indentation from the
/// body of a multi-line raw string.
fn trim_raw_string(content: &str) -> String {
    let body = content
        .strip_prefix("\r\n")
        .or_else(|| content.strip_prefix('\n'))
        .unwrap_or(content);

    // The last line holds only the whitespace the closing fence is indented by,
    // and that much is removed from every line.
    let (body, indent) = match body.rfind('\n') {
        Some(index) => {
            let indent = &body[index + 1..];
            (body[..index].trim_end_matches('\r'), indent)
        }
        None => (body, ""),
    };

    if indent.is_empty() {
        return body.to_string();
    }
    body.split_inclusive('\n')
        .map(|line| line.strip_prefix(indent).unwrap_or(line))
        .collect()
}
