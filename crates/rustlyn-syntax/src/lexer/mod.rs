//! The C# lexer.
//!
//! It turns source text into a flat list of [`Token`]s that keeps every byte of
//! the original: whitespace and comments become [`Trivia`] hanging off the
//! token that follows or precedes them, so the token stream can be concatenated
//! back into the exact input. Everything after this point in the pipeline
//! depends on that property, because a full-fidelity syntax tree is what lets
//! an IDE hand back edited source that only differs where the user edited.
//!
//! Like Roslyn's lexer, it never fails: anything it cannot make sense of turns
//! into a [`SyntaxKind::BadToken`] plus a diagnostic, and lexing continues.

mod chars;
mod directives;
mod identifier;
mod interpolation;
mod number;
mod quoted;

use rustlyn_diagnostics::{Diagnostic, DiagnosticBag, ErrorCode};
use rustlyn_text::{SourceText, TextSpan, is_line_break};

use crate::{LanguageVersion, SyntaxKind, Token, TokenValue, Trivia, kind::kind_from_text};

use chars::{is_identifier_start, is_whitespace};
use directives::Preprocessor;
use interpolation::Interpolation;

/// The result of lexing a whole file.
#[derive(Debug)]
pub struct LexResult {
    /// Every token in order, always ending with [`SyntaxKind::EndOfFileToken`].
    pub tokens: Vec<Token>,
    pub diagnostics: DiagnosticBag,
    /// Each `#define` and `#undef` in live code: its position, the symbol,
    /// and whether the symbol is defined after it.
    pub definitions: Vec<(u32, String, bool)>,
}

/// Settings that change how a file is read.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ParseOptions {
    /// Symbols that count as defined, as `/define:` sets them. `#if DEBUG` is
    /// false unless `DEBUG` is listed here.
    pub preprocessor_symbols: Vec<String>,
    /// The version of C# the file is written in.
    pub language_version: LanguageVersion,
}

impl ParseOptions {
    /// Options with the given preprocessor symbols defined.
    #[must_use]
    pub fn with_symbols<S: Into<String>>(symbols: impl IntoIterator<Item = S>) -> Self {
        Self {
            preprocessor_symbols: symbols.into_iter().map(Into::into).collect(),
            language_version: LanguageVersion::default(),
        }
    }

    /// The same options for another version of the language.
    #[must_use]
    pub fn with_language_version(mut self, version: LanguageVersion) -> Self {
        self.language_version = version;
        self
    }
}

/// Lexes `source` completely.
#[must_use]
pub fn tokenize(source: &SourceText) -> LexResult {
    tokenize_with(source, &ParseOptions::default())
}

/// Lexes `source` with the given options.
#[must_use]
pub fn tokenize_with(source: &SourceText, options: &ParseOptions) -> LexResult {
    let mut lexer = Lexer::with_options(source, options);
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token();
        let at_end = token.is_end_of_file();
        tokens.push(token);
        if at_end {
            break;
        }
    }
    lexer.check_unclosed_conditionals();
    let definitions = std::mem::take(&mut lexer.preprocessor.changes);
    LexResult {
        tokens,
        diagnostics: lexer.into_diagnostics(),
        definitions,
    }
}

/// A cursor over source text that yields one token at a time.
#[derive(Debug)]
pub struct Lexer<'a> {
    text: &'a str,
    pos: u32,
    diagnostics: DiagnosticBag,
    preprocessor: Preprocessor,
    /// The interpolated strings the cursor is inside, innermost last.
    interpolations: Vec<Interpolation>,
}

/// Everything the lexer carries across a token boundary.
///
/// A token's meaning depends on where the cursor has been: `*/` closes a
/// comment only inside one, a brace opens a hole only inside an interpolated
/// string, and a line is live code only if the `#if` around it was taken. All
/// of that lives here, so lexing can be picked up mid-file from a state saved
/// earlier instead of starting over at the top.
///
/// This is what lets an editor colour the screen it is showing without lexing
/// the file above it: keep a state every few hundred lines, and any screen is
/// a short scan from the nearest one.
#[derive(Clone, Debug)]
pub struct LexerState {
    pos: u32,
    preprocessor: Preprocessor,
    interpolations: Vec<Interpolation>,
}

impl LexerState {
    /// The offset the cursor stands at.
    #[must_use]
    pub const fn position(&self) -> u32 {
        self.pos
    }

    /// Whether this is a state a line can be entered in with nothing open —
    /// no `#if`, no interpolated string. Two such states at the same offset
    /// lex the rest of the file identically, which is what lets an
    /// incremental relex stop as soon as it meets one it has seen before.
    #[must_use]
    pub fn is_quiescent(&self) -> bool {
        self.interpolations.is_empty() && self.preprocessor.is_quiescent()
    }
}

/// What [`Lexer::scan_token`] produced, before trivia is attached.
#[derive(Debug)]
pub(crate) struct Scan {
    kind: SyntaxKind,
    contextual_kind: SyntaxKind,
    value: TokenValue,
    value_text: Option<Box<str>>,
}

impl Scan {
    pub(crate) fn kind(kind: SyntaxKind) -> Self {
        Self {
            kind,
            contextual_kind: kind,
            value: TokenValue::None,
            value_text: None,
        }
    }

    pub(crate) fn with_value(mut self, value: TokenValue) -> Self {
        self.value = value;
        self
    }

    pub(crate) fn with_value_text(mut self, text: impl Into<Box<str>>) -> Self {
        self.value_text = Some(text.into());
        self
    }

    pub(crate) fn with_contextual_kind(mut self, kind: SyntaxKind) -> Self {
        self.contextual_kind = kind;
        self
    }
}

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(source: &'a SourceText) -> Self {
        Self::with_options(source, &ParseOptions::default())
    }

    #[must_use]
    pub fn with_options(source: &'a SourceText, options: &ParseOptions) -> Self {
        Self {
            text: source.text(),
            pos: 0,
            diagnostics: DiagnosticBag::new(),
            preprocessor: Preprocessor::new(&options.preprocessor_symbols),
            interpolations: Vec::new(),
        }
    }

    /// The state the cursor stands in, to be handed back to [`Self::resume`].
    #[must_use]
    pub fn state(&self) -> LexerState {
        LexerState {
            pos: self.pos,
            preprocessor: self.preprocessor.clone(),
            interpolations: self.interpolations.clone(),
        }
    }

    /// Carries on from a state saved earlier by [`Self::state`].
    ///
    /// The source must be the same text the state was taken from; a state
    /// taken from one file and used on another points into the wrong place.
    #[must_use]
    pub fn resume(source: &'a SourceText, state: &LexerState) -> Self {
        Self {
            text: source.text(),
            pos: state.pos.min(source.len()),
            diagnostics: DiagnosticBag::new(),
            preprocessor: state.preprocessor.clone(),
            interpolations: state.interpolations.clone(),
        }
    }

    /// Diagnostics reported so far.
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        self.diagnostics.as_slice()
    }

    #[must_use]
    pub fn into_diagnostics(self) -> DiagnosticBag {
        self.diagnostics
    }

    /// Lexes the next token together with its trivia.
    ///
    /// Once the end of the file is reached this keeps returning
    /// [`SyntaxKind::EndOfFileToken`].
    pub fn next_token(&mut self) -> Token {
        let full_start = self.pos;
        // Inside the text of an interpolated string there is no such thing as
        // trivia: every space is part of the value.
        let reading_text = self.in_interpolated_text();
        let leading_trivia = if reading_text {
            Vec::new()
        } else {
            self.lex_trivia(false)
        };
        let start = self.pos;
        let mut scan = if reading_text {
            self.scan_interpolated_text()
        } else {
            let scan = self.scan_token();
            self.track_interpolation(scan.kind);
            scan
        };
        if self.pos == start && scan.kind != SyntaxKind::EndOfFileToken {
            // A scanner that took nothing is asked again at the same place,
            // forever, growing the token list as it goes. That is a bug in
            // the scanner, and a debug build says so; a release build is
            // inside an editor, where taking a character is better than
            // taking the editor down.
            if cfg!(debug_assertions) {
                panic!("scanning a token must consume input");
            }
            if self.bump().is_none() {
                self.interpolations.clear();
                scan = Scan::kind(SyntaxKind::EndOfFileToken);
            } else {
                scan = Scan::kind(SyntaxKind::BadToken);
            }
        }
        let end = self.pos;
        // Trivia after the last token belongs to the end-of-file token, which
        // has already claimed it as leading trivia.
        let trailing_trivia =
            if scan.kind == SyntaxKind::EndOfFileToken || self.in_interpolated_text() {
                Vec::new()
            } else {
                self.lex_trivia(true)
            };

        Token {
            kind: scan.kind,
            contextual_kind: scan.contextual_kind,
            span: TextSpan::from_bounds(start, end),
            full_span: TextSpan::from_bounds(full_start, self.pos),
            leading_trivia,
            trailing_trivia,
            value: scan.value,
            value_text: scan.value_text,
        }
    }

    fn scan_token(&mut self) -> Scan {
        // The braces that close the hole of a raw interpolated string are
        // counted as a group, so they have to be claimed before the
        // punctuation scanner takes them one at a time.
        if let Some(scan) = self.scan_raw_hole_close() {
            return scan;
        }

        let Some(ch) = self.peek() else {
            return Scan::kind(SyntaxKind::EndOfFileToken);
        };

        match ch {
            '$' if self.at_raw_string() => self.scan_interpolated_raw_start(),
            '"' if self.at_raw_string() => self.scan_raw_string_literal(),
            '$' if self.peek_nth(1) == Some('"') => self.scan_interpolated_start(false),
            '$' if self.peek_nth(1) == Some('@') && self.peek_nth(2) == Some('"') => {
                self.scan_interpolated_start(true)
            }
            '"' => self.scan_string_literal(),
            '\'' => self.scan_character_literal(),
            '@' => self.scan_verbatim(),
            '0'..='9' => self.scan_numeric_literal(),
            // `.5` is a literal, but the dot in `1.ToString()` is an operator.
            '.' if self.peek_nth(1).is_some_and(|next| next.is_ascii_digit()) => {
                self.scan_numeric_literal()
            }
            // An identifier may open with a Unicode escape: `abc` is `abc`.
            '\\' if matches!(self.peek_nth(1), Some('u' | 'U')) => self.scan_identifier(),
            _ if is_identifier_start(ch) => self.scan_identifier(),
            _ => match self.scan_punctuation(ch) {
                Some(kind) => Scan::kind(kind),
                None => self.scan_bad_token(),
            },
        }
    }

    /// Consumes the longest operator or separator starting at `ch`.
    fn scan_punctuation(&mut self, ch: char) -> Option<SyntaxKind> {
        // Candidates are ordered longest first, which is all "maximal munch"
        // amounts to: `>>=` must win over `>>`, and `>>` over `>`.
        let candidates: &[&str] = match ch {
            '~' => &["~"],
            '!' => &["!=", "!"],
            '$' => &["$"],
            '%' => &["%=", "%"],
            '^' => &["^=", "^"],
            '&' => &["&&", "&=", "&"],
            '*' => &["*=", "*"],
            '(' => &["("],
            ')' => &[")"],
            '-' => &["->", "--", "-=", "-"],
            '+' => &["++", "+=", "+"],
            '=' => &["==", "=>", "="],
            '{' => &["{"],
            '}' => &["}"],
            '[' => &["["],
            ']' => &["]"],
            '|' => &["||", "|=", "|"],
            '\\' => &["\\"],
            ':' => &["::", ":"],
            ';' => &[";"],
            '<' => &["<<=", "<<", "<=", "<"],
            ',' => &[","],
            // `>>` and `>>=` are single tokens here; the parser splits them
            // apart again when it closes nested generics such as `List<int[]>>`.
            '>' => &[">>>=", ">>>", ">>=", ">>", ">=", ">"],
            '.' => &["..", "."],
            '?' => &["??=", "??", "?"],
            '#' => &["#"],
            '/' => &["/=", "/"],
            _ => return None,
        };

        for candidate in candidates {
            if self.at(candidate) {
                self.advance(candidate.len());
                return kind_from_text(candidate);
            }
        }
        None
    }

    fn scan_bad_token(&mut self) -> Scan {
        let start = self.pos;
        let ch = self.bump().expect("scan_bad_token requires a character");
        self.error(
            ErrorCode::ErrUnexpectedCharacter,
            TextSpan::from_bounds(start, self.pos),
            &[&ch.to_string()],
        );
        Scan::kind(SyntaxKind::BadToken)
    }

    /// Consumes trivia until the next token starts.
    ///
    /// Trailing trivia stops after the first line break, so a comment stays
    /// attached to the line it was written on and the next line's trivia leads
    /// the next token.
    fn lex_trivia(&mut self, trailing: bool) -> Vec<Trivia> {
        let mut list = Vec::new();
        loop {
            let start = self.pos;
            let Some(ch) = self.peek() else { break };

            if is_whitespace(ch) {
                while self.peek().is_some_and(is_whitespace) {
                    self.bump();
                }
                list.push(Trivia::new(
                    SyntaxKind::WhitespaceTrivia,
                    self.span_from(start),
                ));
                continue;
            }

            if is_line_break(ch) {
                self.consume_line_break();
                list.push(Trivia::new(
                    SyntaxKind::EndOfLineTrivia,
                    self.span_from(start),
                ));
                if trailing {
                    break;
                }
                continue;
            }

            // A directive only counts at the start of a line, which is also
            // why one can never be trailing trivia.
            if ch == '#' && !trailing && self.at_line_start(start) {
                self.lex_directive(&mut list);
                continue;
            }

            if ch == '/' {
                match self.peek_nth(1) {
                    Some('/') => {
                        // `///` opens a documentation comment, `////` does not.
                        let documentation =
                            self.peek_nth(2) == Some('/') && self.peek_nth(3) != Some('/');
                        // Documentation belongs to what follows it, so it never
                        // ends up as trailing trivia.
                        if documentation && trailing {
                            break;
                        }
                        self.consume_single_line_comment();
                        let kind = if documentation {
                            SyntaxKind::SingleLineDocumentationCommentTrivia
                        } else {
                            SyntaxKind::SingleLineCommentTrivia
                        };
                        list.push(Trivia::new(kind, self.span_from(start)));
                        continue;
                    }
                    Some('*') => {
                        // `/**` opens a documentation comment, but `/***` and
                        // the empty `/**/` do not.
                        let documentation = self.peek_nth(2) == Some('*')
                            && !matches!(self.peek_nth(3), Some('*' | '/'));
                        if documentation && trailing {
                            break;
                        }
                        self.consume_multi_line_comment();
                        let kind = if documentation {
                            SyntaxKind::MultiLineDocumentationCommentTrivia
                        } else {
                            SyntaxKind::MultiLineCommentTrivia
                        };
                        list.push(Trivia::new(kind, self.span_from(start)));
                        continue;
                    }
                    _ => break,
                }
            }

            break;
        }
        list
    }

    fn consume_single_line_comment(&mut self) {
        while let Some(ch) = self.peek() {
            if is_line_break(ch) {
                break;
            }
            self.bump();
        }
    }

    fn consume_multi_line_comment(&mut self) {
        let start = self.pos;
        self.advance(2); // `/*`
        loop {
            match self.peek() {
                None => {
                    self.error(ErrorCode::ErrOpenEndedComment, self.span_from(start), &[]);
                    break;
                }
                Some('*') if self.peek_nth(1) == Some('/') => {
                    self.advance(2);
                    break;
                }
                Some(_) => {
                    self.bump();
                }
            }
        }
    }

    /// Consumes one line break; `\r\n` counts as a single break.
    fn consume_line_break(&mut self) {
        if self.bump() == Some('\r') && self.peek() == Some('\n') {
            self.bump();
        }
    }

    // -- cursor ------------------------------------------------------------

    pub(crate) fn rest(&self) -> &'a str {
        &self.text[self.pos as usize..]
    }

    pub(crate) fn at_end(&self) -> bool {
        self.pos as usize >= self.text.len()
    }

    pub(crate) fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    pub(crate) fn peek_nth(&self, n: usize) -> Option<char> {
        self.rest().chars().nth(n)
    }

    pub(crate) fn at(&self, prefix: &str) -> bool {
        self.rest().starts_with(prefix)
    }

    /// Where the cursor stands.
    ///
    /// Public because it is free, where [`Self::state`] is not: a caller
    /// looking for the places worth saving a state at asks this on every
    /// token and [`Self::state`] only on the few that turn out to be.
    #[must_use]
    pub const fn position(&self) -> u32 {
        self.pos
    }

    pub(crate) fn bump(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.pos += ch.len_utf8() as u32;
        Some(ch)
    }

    /// Consumes `ch` if it is next, reporting whether it was.
    pub(crate) fn eat(&mut self, ch: char) -> bool {
        if self.peek() == Some(ch) {
            self.bump();
            true
        } else {
            false
        }
    }

    pub(crate) fn advance(&mut self, bytes: usize) {
        self.pos += bytes as u32;
        debug_assert!(self.text.is_char_boundary(self.pos as usize));
    }

    pub(crate) fn span_from(&self, start: u32) -> TextSpan {
        TextSpan::from_bounds(start, self.pos)
    }

    pub(crate) fn error(&mut self, code: ErrorCode, span: TextSpan, args: &[&str]) {
        self.diagnostics.error(code, span, args);
    }

    /// The whole file, borrowed for as long as the source lives rather than
    /// for as long as the lexer is borrowed, so scanners can keep a slice of
    /// it while they keep advancing.
    pub(crate) fn source_str(&self) -> &'a str {
        self.text
    }
}
