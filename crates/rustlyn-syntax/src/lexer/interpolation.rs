//! Interpolated strings.
//!
//! Roslyn lexes `$"a{b}c"` as one token and takes it apart again in the
//! parser. This lexer instead hands the parser a stream — a start token, text
//! tokens, and ordinary tokens inside the holes — so that `{x + y}` is parsed
//! by the expression parser that already exists rather than by a second copy
//! of it.
//!
//! The cost is that the lexer becomes stateful: it has to know whether it is
//! reading string text or code, and a `}` only ends a hole when the braces and
//! brackets opened inside it have been closed.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_text::is_line_break;

use super::chars::is_whitespace;
use super::{Lexer, Scan};
use crate::SyntaxKind;

/// One interpolated string being lexed. Nested, because a hole may contain
/// another interpolated string.
#[derive(Clone, Copy, Debug)]
pub(super) struct Interpolation {
    /// `@$"..."`, where line breaks are allowed and `\` is not an escape.
    verbatim: bool,
    /// Quotes in the fence of a raw string, or zero when the string is not raw.
    fence: usize,
    /// How many braces open and close a hole: one for `$"..."`, and `n` for a
    /// raw string opened with `n` dollar signs. This is what lets `$$"""{a}"""`
    /// hold a literal `{a}` and interpolate only on `{{a}}`.
    dollars: usize,
    /// Raw strings only: whether the closing fence must start its own line.
    multi_line: bool,
    /// How many `{` are open. Zero means the lexer is reading string text.
    hole_depth: usize,
    /// How many `(` and `[` are open inside the hole, which is what decides
    /// whether a `:` starts a format specifier or belongs to something else.
    group_depth: usize,
    /// Whether the lexer is past the `:` and reading the format specifier,
    /// which is text rather than code.
    in_format: bool,
}

impl Interpolation {
    /// Whether the lexer should be reading text rather than code.
    const fn reading_text(&self) -> bool {
        self.hole_depth == 0 || self.in_format
    }

    const fn raw(&self) -> bool {
        self.fence > 0
    }
}

impl Lexer<'_> {
    /// Whether the cursor is inside the text of an interpolated string, where
    /// whitespace is content rather than trivia.
    pub(super) fn in_interpolated_text(&self) -> bool {
        self.interpolations
            .last()
            .is_some_and(Interpolation::reading_text)
    }

    /// Scans `$"`, `$@"` or `@$"` and enters the string.
    pub(super) fn scan_interpolated_start(&mut self, verbatim: bool) -> Scan {
        self.bump(); // `$` or `@`
        if verbatim {
            self.bump(); // the other of the two
        }
        self.bump(); // the quote

        self.interpolations.push(Interpolation {
            verbatim,
            fence: 0,
            dollars: 1,
            multi_line: false,
            hole_depth: 0,
            group_depth: 0,
            in_format: false,
        });

        Scan::kind(if verbatim {
            SyntaxKind::InterpolatedVerbatimStringStartToken
        } else {
            SyntaxKind::InterpolatedStringStartToken
        })
    }

    /// Scans one token of string text: a run of characters, a brace that opens
    /// or closes a hole, or the closing quote.
    pub(super) fn scan_interpolated_text(&mut self) -> Scan {
        let state = *self
            .interpolations
            .last()
            .expect("only called while inside an interpolated string");
        if state.raw() {
            return self.scan_interpolated_raw_text(state);
        }
        let start = self.position();

        if state.in_format {
            return match self.peek() {
                Some('}') => {
                    self.bump();
                    self.leave_hole();
                    Scan::kind(SyntaxKind::CloseBraceToken)
                }
                // The file ends inside the format specifier: the string ends
                // with it, as it does when the file ends in its text. Left on
                // the stack, it asked for more text at the end forever.
                None => {
                    self.report_unterminated(start, state);
                    self.interpolations.pop();
                    Scan::kind(SyntaxKind::EndOfFileToken)
                }
                Some(_) => self.scan_text_run(start, state, true),
            };
        }

        match self.peek() {
            Some('"') => {
                // In a verbatim string `""` is an escaped quote, not the end.
                if state.verbatim && self.peek_nth(1) == Some('"') {
                    return self.scan_text_run(start, state, false);
                }
                self.bump();
                self.interpolations.pop();
                Scan::kind(SyntaxKind::InterpolatedStringEndToken)
            }
            Some('{') => {
                if self.peek_nth(1) == Some('{') {
                    return self.scan_text_run(start, state, false);
                }
                self.bump();
                self.enter_hole();
                Scan::kind(SyntaxKind::OpenBraceToken)
            }
            None => {
                self.report_unterminated(start, state);
                self.interpolations.pop();
                Scan::kind(SyntaxKind::EndOfFileToken)
            }
            _ => self.scan_text_run(start, state, false),
        }
    }

    /// Consumes characters up to the next brace, quote or end of line.
    fn scan_text_run(&mut self, start: u32, state: Interpolation, format: bool) -> Scan {
        loop {
            match self.peek() {
                None => {
                    self.report_unterminated(start, state);
                    break;
                }
                Some(ch) if is_line_break(ch) && !state.verbatim => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    self.interpolations.pop();
                    break;
                }
                Some('}') => {
                    if format {
                        break;
                    }
                    if self.peek_nth(1) == Some('}') {
                        self.advance(2);
                        continue;
                    }
                    // A lone `}` outside a hole is not valid, but keeping it as
                    // text keeps the file reconstructible.
                    self.bump();
                }
                Some('{') if !format => {
                    if self.peek_nth(1) == Some('{') {
                        self.advance(2);
                        continue;
                    }
                    break;
                }
                Some('"') => {
                    if state.verbatim && self.peek_nth(1) == Some('"') {
                        self.advance(2);
                        continue;
                    }
                    break;
                }
                Some('\\') if !state.verbatim && !format => {
                    // The escape is kept as written; decoding it is the
                    // binder's problem, not the lexer's.
                    self.bump();
                    self.bump();
                }
                Some(_) => {
                    self.bump();
                }
            }
        }

        if self.position() == start {
            // Nothing was consumed, which would stall the token loop.
            self.bump();
        }
        Scan::kind(SyntaxKind::InterpolatedStringTextToken)
    }

    /// Scans `$"""` — any number of dollar signs followed by a fence of at
    /// least three quotes — and enters the string.
    ///
    /// Roslyn keeps a raw interpolated string as a single token and re-lexes
    /// its holes later. Streaming it instead means a hole is lexed as ordinary
    /// code from the start, which is what lets a hole hold a raw string of its
    /// own: `$$"""{{s.Replace("""a""", """b""")}}"""` has quote runs inside it
    /// that are not the end of the outer string.
    pub(super) fn scan_interpolated_raw_start(&mut self) -> Scan {
        let mut dollars = 0usize;
        while self.peek() == Some('$') {
            self.bump();
            dollars += 1;
        }
        let mut fence = 0usize;
        while self.peek() == Some('"') {
            self.bump();
            fence += 1;
        }

        // As for a plain raw string, nothing but whitespace after the fence
        // means the content starts on the next line.
        let multi_line = self
            .rest()
            .chars()
            .take_while(|&ch| !is_line_break(ch))
            .all(is_whitespace);

        self.interpolations.push(Interpolation {
            verbatim: false,
            fence,
            dollars,
            multi_line,
            hole_depth: 0,
            group_depth: 0,
            in_format: false,
        });

        Scan::kind(if multi_line {
            SyntaxKind::InterpolatedMultiLineRawStringStartToken
        } else {
            SyntaxKind::InterpolatedSingleLineRawStringStartToken
        })
    }

    /// Closes a hole of a raw interpolated string from code position.
    ///
    /// The braces that close a hole are counted rather than matched, so this
    /// has to run before the punctuation scanner would take them one at a time.
    pub(super) fn scan_raw_hole_close(&mut self) -> Option<Scan> {
        let state = *self.interpolations.last()?;
        if !state.raw() || state.hole_depth != 1 || state.in_format {
            return None;
        }
        if self.run_of('}') < state.dollars {
            return None;
        }
        // Any braces beyond the hole's own are content, and the pass over the
        // text picks them up.
        self.advance(state.dollars);
        self.leave_hole();
        Some(Scan::kind(SyntaxKind::CloseBraceToken))
    }

    /// Scans one token of the text of a raw interpolated string.
    fn scan_interpolated_raw_text(&mut self, state: Interpolation) -> Scan {
        let start = self.position();

        if state.in_format && self.run_of('}') >= state.dollars {
            self.advance(state.dollars);
            self.leave_hole();
            return Scan::kind(SyntaxKind::CloseBraceToken);
        }

        if !state.in_format {
            let quotes = self.run_of('"');
            if quotes >= state.fence && self.raw_fence_closes(state) {
                // A multi-line string ends on the whole run; a single-line one
                // keeps the extra quotes as content, so only the fence is left
                // by the time the run is reached again.
                let width = if state.multi_line {
                    quotes
                } else {
                    state.fence
                };
                self.advance(width);
                self.interpolations.pop();
                return Scan::kind(SyntaxKind::InterpolatedRawStringEndToken);
            }

            let braces = self.run_of('{');
            if braces >= state.dollars {
                // Of `{{{` in a one-dollar string, the first two braces are
                // content and only the last opens the hole.
                if braces > state.dollars {
                    self.advance(braces - state.dollars);
                    return Scan::kind(SyntaxKind::InterpolatedStringTextToken);
                }
                self.advance(state.dollars);
                self.enter_hole();
                return Scan::kind(SyntaxKind::OpenBraceToken);
            }
        }

        self.scan_raw_text_run(start, state)
    }

    /// Whether a quote run at the cursor really ends the string. In a
    /// multi-line raw string the closing fence has to begin its own line.
    fn raw_fence_closes(&self, state: Interpolation) -> bool {
        if !state.multi_line {
            return true;
        }
        self.at_line_start(self.position())
    }

    /// Consumes content up to the next quote or brace, which are the only
    /// characters that can end it. Raw strings have no escapes.
    fn scan_raw_text_run(&mut self, start: u32, state: Interpolation) -> Scan {
        loop {
            match self.peek() {
                None => {
                    self.error(
                        ErrorCode::ErrUnterminatedStringLit,
                        self.span_from(start),
                        &[],
                    );
                    self.interpolations.pop();
                    break;
                }
                Some(ch) if is_line_break(ch) && !state.multi_line => {
                    self.error(ErrorCode::ErrNewlineInConst, self.span_from(start), &[]);
                    self.interpolations.pop();
                    break;
                }
                // A run of quotes or braces that got this far is content, and
                // taking all of it keeps the token loop from stalling on the
                // same character. Later runs end the token so that the check
                // for the closing fence runs against them.
                Some(ch @ ('"' | '{')) => {
                    if self.position() > start {
                        break;
                    }
                    while self.peek() == Some(ch) {
                        self.bump();
                    }
                }
                // A run of braces short of closing the hole is content: with
                // nothing taken before it, breaking here would stall the
                // token loop on it.
                Some('}') if state.in_format => {
                    if self.position() > start {
                        break;
                    }
                    while self.peek() == Some('}') {
                        self.bump();
                    }
                }
                Some(_) => {
                    self.bump();
                }
            }
        }

        Scan::kind(SyntaxKind::InterpolatedStringTextToken)
    }

    /// How many `ch` in a row start at the cursor.
    fn run_of(&self, ch: char) -> usize {
        let mut run = 0usize;
        while self.peek_nth(run) == Some(ch) {
            run += 1;
        }
        run
    }

    fn report_unterminated(&mut self, start: u32, state: Interpolation) {
        let code = if state.verbatim {
            ErrorCode::ErrUnterminatedStringLit
        } else {
            ErrorCode::ErrNewlineInConst
        };
        self.error(code, self.span_from(start), &[]);
    }

    fn enter_hole(&mut self) {
        if let Some(state) = self.interpolations.last_mut() {
            state.hole_depth = 1;
            state.group_depth = 0;
            state.in_format = false;
        }
    }

    fn leave_hole(&mut self) {
        if let Some(state) = self.interpolations.last_mut() {
            state.hole_depth = 0;
            state.group_depth = 0;
            state.in_format = false;
        }
    }

    /// Follows the braces and brackets inside a hole, so the lexer knows when
    /// the hole ends and when a `:` starts a format specifier.
    pub(super) fn track_interpolation(&mut self, kind: SyntaxKind) {
        let Some(state) = self.interpolations.last_mut() else {
            return;
        };
        if state.hole_depth == 0 {
            return;
        }
        match kind {
            SyntaxKind::OpenBraceToken => state.hole_depth += 1,
            SyntaxKind::CloseBraceToken => {
                state.hole_depth -= 1;
                if state.hole_depth == 0 {
                    state.group_depth = 0;
                    state.in_format = false;
                }
            }
            SyntaxKind::OpenParenToken | SyntaxKind::OpenBracketToken => state.group_depth += 1,
            SyntaxKind::CloseParenToken | SyntaxKind::CloseBracketToken => {
                state.group_depth = state.group_depth.saturating_sub(1);
            }
            // `$"{x:N2}"` formats; `$"{(a ? b : c)}"` does not, which is why
            // the parentheses are counted.
            SyntaxKind::ColonToken if state.hole_depth == 1 && state.group_depth == 0 => {
                state.in_format = true;
            }
            _ => {}
        }
    }
}
