//! Preprocessor directives and the text they switch off.
//!
//! C# directives are not part of the grammar: they are trivia that the lexer
//! acts on as it goes. `#if` decides whether the lines after it are lexed at
//! all, and the ones that are not become a single run of
//! [`SyntaxKind::DisabledTextTrivia`], so the file is still covered end to end
//! even though most of it never became tokens.
//!
//! A directive only counts when nothing but whitespace precedes it on its line,
//! which is also why one can never turn up in trailing trivia.

use std::collections::HashSet;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_text::is_line_break;

use super::Lexer;
use super::chars::{is_formatting, is_identifier_part, is_whitespace};
use crate::{SyntaxKind, Trivia};

/// One level of `#if` nesting.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ConditionalState {
    /// Whether some branch of this `#if` chain has already been taken, which is
    /// what makes a later `#elif` false even when its condition holds.
    any_branch_taken: bool,
    /// Whether the branch being lexed right now is the live one.
    active: bool,
    /// Whether `#else` has been seen, so a second one is an error.
    seen_else: bool,
}

/// The preprocessor's state for one file.
#[derive(Clone, Debug, Default)]
pub(crate) struct Preprocessor {
    defined: HashSet<String>,
    stack: Vec<ConditionalState>,
    /// Each `#define` and `#undef` in live code, where it stands, with the
    /// symbol and whether it is defined from there on: what a
    /// `[Conditional]` call asks about is the symbol at the call.
    pub(crate) changes: Vec<(u32, String, bool)>,
}

impl Preprocessor {
    pub(crate) fn new(symbols: &[String]) -> Self {
        Self {
            defined: symbols.iter().cloned().collect(),
            stack: Vec::new(),
            changes: Vec::new(),
        }
    }

    /// Whether the lexer is currently inside live code.
    fn active(&self) -> bool {
        self.stack.iter().all(|state| state.active)
    }

    /// Whether the enclosing region is live, ignoring the innermost `#if`.
    fn enclosing_active(&self) -> bool {
        self.stack.iter().rev().skip(1).all(|state| state.active)
    }

    /// Whether no `#if` is open, so the lines that follow do not depend on
    /// a condition read earlier in the file.
    pub(crate) fn is_quiescent(&self) -> bool {
        self.stack.is_empty()
    }
}

impl<'a> Lexer<'a> {
    /// Whether everything between the previous line break and `position` is
    /// whitespace.
    pub(super) fn at_line_start(&self, position: u32) -> bool {
        self.source_str()[..position as usize]
            .chars()
            .rev()
            .take_while(|ch| !is_line_break(*ch))
            .all(is_whitespace)
    }

    /// Lexes one directive line and, if it switched the code off, the text it
    /// switched off.
    pub(super) fn lex_directive(&mut self, list: &mut Vec<Trivia>) {
        let start = self.position();
        let was_active = self.preprocessor.active();
        self.bump(); // `#`

        while self.peek().is_some_and(is_whitespace) {
            self.bump();
        }
        // `#!` and `#:` are the two directives whose name is punctuation:
        // the shebang of a file-based program, and the `#:package`-style
        // directives the compiler passes to the build and otherwise ignores.
        let name_start = self.position();
        if matches!(self.peek(), Some('!' | ':')) {
            self.bump();
        } else {
            while self.peek().is_some_and(is_identifier_part) {
                self.bump();
            }
        }
        let text = self.source_str();
        let name = &text[name_start as usize..self.position() as usize];

        let rest_start = self.position();
        while self.peek().is_some_and(|ch| !is_line_break(ch)) {
            self.bump();
        }
        let rest = text[rest_start as usize..self.position() as usize].trim();
        let span = self.span_from(start);

        let kind = match name {
            "if" => {
                let condition = self.evaluate(rest, span.start());
                let taken = was_active && condition;
                self.preprocessor.stack.push(ConditionalState {
                    any_branch_taken: taken,
                    active: taken,
                    seen_else: false,
                });
                SyntaxKind::IfDirectiveTrivia
            }
            "elif" => {
                let condition = self.evaluate(rest, span.start());
                self.take_branch(span.start(), |state, enclosing| {
                    enclosing && !state.any_branch_taken && condition
                });
                SyntaxKind::ElifDirectiveTrivia
            }
            "else" => {
                self.take_branch(span.start(), |state, enclosing| {
                    enclosing && !state.any_branch_taken
                });
                if let Some(state) = self.preprocessor.stack.last_mut() {
                    if state.seen_else {
                        self.diagnostics
                            .error(ErrorCode::ErrUnexpectedDirective, span, &[]);
                    } else {
                        state.seen_else = true;
                    }
                }
                SyntaxKind::ElseDirectiveTrivia
            }
            "endif" => {
                if self.preprocessor.stack.pop().is_none() {
                    self.error(ErrorCode::ErrUnexpectedDirective, span, &[]);
                }
                SyntaxKind::EndIfDirectiveTrivia
            }
            "define" | "undef" => {
                // The name ends where a comment after it begins.
                let symbol = rest
                    .split(|ch: char| ch.is_whitespace() || ch == '/')
                    .next()
                    .unwrap_or_default();
                let define = name == "define";
                if was_active && !symbol.is_empty() {
                    if define {
                        self.preprocessor.defined.insert(symbol.to_string());
                    } else {
                        self.preprocessor.defined.remove(symbol);
                    }
                    self.preprocessor
                        .changes
                        .push((span.start(), symbol.to_string(), define));
                }
                if define {
                    SyntaxKind::DefineDirectiveTrivia
                } else {
                    SyntaxKind::UndefDirectiveTrivia
                }
            }
            "region" => SyntaxKind::RegionDirectiveTrivia,
            "endregion" => SyntaxKind::EndRegionDirectiveTrivia,
            "error" => {
                if was_active {
                    self.error(ErrorCode::ErrErrorDirective, span, &[rest]);
                }
                SyntaxKind::ErrorDirectiveTrivia
            }
            "warning" => {
                if was_active {
                    self.error(ErrorCode::WrnWarningDirective, span, &[rest]);
                }
                SyntaxKind::WarningDirectiveTrivia
            }
            "line" => SyntaxKind::LineDirectiveTrivia,
            "pragma" => {
                if rest.starts_with("checksum") {
                    SyntaxKind::PragmaChecksumDirectiveTrivia
                } else {
                    SyntaxKind::PragmaWarningDirectiveTrivia
                }
            }
            "nullable" => SyntaxKind::NullableDirectiveTrivia,
            "reference" => SyntaxKind::ReferenceDirectiveTrivia,
            "load" => SyntaxKind::LoadDirectiveTrivia,
            // A shebang is only one on the first line; anywhere else `#!` is
            // as meaningless as any other unknown directive.
            "!" if start == 0 => SyntaxKind::ShebangDirectiveTrivia,
            ":" => SyntaxKind::IgnoredDirectiveTrivia,
            _ => {
                self.error(ErrorCode::ErrPpDirectiveExpected, span, &[]);
                SyntaxKind::BadDirectiveTrivia
            }
        };

        list.push(Trivia::new(kind, span));

        if !self.preprocessor.active() {
            self.skip_excluded_text(list);
        }
    }

    /// Updates the innermost `#if` for an `#elif` or `#else`.
    fn take_branch(&mut self, position: u32, decide: impl FnOnce(ConditionalState, bool) -> bool) {
        let enclosing = self.preprocessor.enclosing_active();
        let Some(&state) = self.preprocessor.stack.last() else {
            self.error(
                ErrorCode::ErrUnexpectedDirective,
                rustlyn_text::TextSpan::at(position),
                &[],
            );
            return;
        };
        let taken = decide(state, enclosing);
        let state = self
            .preprocessor
            .stack
            .last_mut()
            .expect("the stack was just checked");
        state.active = taken;
        state.any_branch_taken |= taken;
    }

    /// Consumes the lines between a false branch and the directive that ends
    /// it, keeping them as one piece of trivia.
    fn skip_excluded_text(&mut self, list: &mut Vec<Trivia>) {
        // The line break at the end of the directive belongs to the directive's
        // line, not to the text being skipped.
        if self.peek().is_some_and(is_line_break) {
            let start = self.position();
            self.consume_line_break();
            list.push(Trivia::new(
                SyntaxKind::EndOfLineTrivia,
                self.span_from(start),
            ));
        }

        let start = self.position();
        let mut depth = 0usize;
        while !self.at_end() {
            match self.directive_name_on_this_line() {
                Some("if") => depth += 1,
                Some("endif") => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                Some("elif" | "else") if depth == 0 => break,
                _ => {}
            }
            while self.peek().is_some_and(|ch| !is_line_break(ch)) {
                self.bump();
            }
            if !self.at_end() {
                self.consume_line_break();
            }
        }

        if self.position() > start {
            list.push(Trivia::new(
                SyntaxKind::DisabledTextTrivia,
                self.span_from(start),
            ));
        }
    }

    /// The directive name on the line at the cursor, without moving it.
    fn directive_name_on_this_line(&self) -> Option<&'a str> {
        let text = self.source_str();
        let mut probe = self.position() as usize;
        let bytes = text.as_bytes();
        while probe < bytes.len() && (bytes[probe] == b' ' || bytes[probe] == b'\t') {
            probe += 1;
        }
        if bytes.get(probe) != Some(&b'#') {
            return None;
        }
        probe += 1;
        while probe < bytes.len() && (bytes[probe] == b' ' || bytes[probe] == b'\t') {
            probe += 1;
        }
        let name_start = probe;
        while probe < bytes.len() && bytes[probe].is_ascii_alphabetic() {
            probe += 1;
        }
        Some(&text[name_start..probe])
    }

    fn evaluate(&mut self, condition: &str, position: u32) -> bool {
        match evaluate_condition(condition, &self.preprocessor.defined) {
            Some(value) => value,
            None => {
                self.error(
                    ErrorCode::ErrInvalidPreprocExpr,
                    rustlyn_text::TextSpan::at(position),
                    &[],
                );
                false
            }
        }
    }

    /// Reports an unclosed `#if` at the end of the file.
    pub(super) fn check_unclosed_conditionals(&mut self) {
        if !self.preprocessor.stack.is_empty() {
            let position = self.position();
            self.error(
                ErrorCode::ErrEndifDirectiveExpected,
                rustlyn_text::TextSpan::at(position),
                &[],
            );
        }
    }
}

/// Evaluates a `#if` condition, or returns `None` if it does not parse.
///
/// The grammar is deliberately tiny: symbols, `true`, `false`, `!`, `&&`,
/// `||`, `==`, `!=` and parentheses. Anything else in C# source is not a
/// preprocessing expression.
fn evaluate_condition(text: &str, defined: &HashSet<String>) -> Option<bool> {
    let mut parser = Condition {
        chars: text.as_bytes(),
        text,
        position: 0,
        defined,
    };
    let value = parser.or()?;
    parser.skip_space();
    // A trailing `//` comment is allowed and ends the expression.
    if parser.position < parser.chars.len() && !parser.rest().starts_with("//") {
        return None;
    }
    Some(value)
}

struct Condition<'a> {
    chars: &'a [u8],
    text: &'a str,
    position: usize,
    defined: &'a HashSet<String>,
}

impl Condition<'_> {
    fn rest(&self) -> &str {
        &self.text[self.position..]
    }

    fn skip_space(&mut self) {
        while self
            .chars
            .get(self.position)
            .is_some_and(|byte| byte.is_ascii_whitespace())
        {
            self.position += 1;
        }
    }

    fn eat(&mut self, token: &str) -> bool {
        self.skip_space();
        if self.rest().starts_with(token) {
            self.position += token.len();
            return true;
        }
        false
    }

    fn or(&mut self) -> Option<bool> {
        let mut value = self.and()?;
        while self.eat("||") {
            value |= self.and()?;
        }
        Some(value)
    }

    fn and(&mut self) -> Option<bool> {
        let mut value = self.equality()?;
        while self.eat("&&") {
            value &= self.equality()?;
        }
        Some(value)
    }

    fn equality(&mut self) -> Option<bool> {
        let mut value = self.unary()?;
        loop {
            if self.eat("==") {
                value = value == self.unary()?;
            } else if self.eat("!=") {
                value = value != self.unary()?;
            } else {
                return Some(value);
            }
        }
    }

    fn unary(&mut self) -> Option<bool> {
        self.skip_space();
        // `!=` is handled above, so a `!` here is negation.
        if self.rest().starts_with('!') && !self.rest().starts_with("!=") {
            self.position += 1;
            return Some(!self.unary()?);
        }
        if self.eat("(") {
            let value = self.or()?;
            return self.eat(")").then_some(value);
        }

        // A name may spell a character with `\uXXXX` or `\UXXXXXXXX`, and
        // a formatting character in it is no part of it: `A\uFFFB` is `A`.
        let start = self.position;
        let mut name = String::new();
        loop {
            let rest = &self.text[self.position..];
            let escaped = |prefix: &str, digits: usize| {
                rest.strip_prefix(prefix)
                    .and_then(|after| after.get(..digits))
                    .filter(|hex| hex.chars().all(|ch| ch.is_ascii_hexdigit()))
                    .and_then(|hex| u32::from_str_radix(hex, 16).ok())
                    .and_then(char::from_u32)
                    .map(|ch| (ch, prefix.len() + digits))
            };
            let Some((ch, width)) = escaped("\\u", 4)
                .or_else(|| escaped("\\U", 8))
                .or_else(|| rest.chars().next().map(|ch| (ch, ch.len_utf8())))
            else {
                break;
            };
            if !(is_identifier_part(ch) || is_formatting(ch)) {
                break;
            }
            self.position += width;
            if !is_formatting(ch) {
                name.push(ch);
            }
        }
        if self.position == start {
            return None;
        }
        Some(match name.as_str() {
            "true" => true,
            "false" => false,
            _ => self.defined.contains(&name),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn defined(symbols: &[&str]) -> HashSet<String> {
        symbols.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn symbols_and_literals() {
        let symbols = defined(&["DEBUG"]);
        assert_eq!(evaluate_condition("DEBUG", &symbols), Some(true));
        assert_eq!(evaluate_condition("RELEASE", &symbols), Some(false));
        assert_eq!(evaluate_condition("true", &symbols), Some(true));
        assert_eq!(evaluate_condition("false", &symbols), Some(false));
    }

    #[test]
    fn operators() {
        let symbols = defined(&["A"]);
        assert_eq!(evaluate_condition("!A", &symbols), Some(false));
        assert_eq!(evaluate_condition("A && B", &symbols), Some(false));
        assert_eq!(evaluate_condition("A || B", &symbols), Some(true));
        assert_eq!(evaluate_condition("A == true", &symbols), Some(true));
        assert_eq!(evaluate_condition("A != B", &symbols), Some(true));
        assert_eq!(evaluate_condition("(A || B) && !B", &symbols), Some(true));
    }

    #[test]
    fn a_trailing_comment_is_allowed() {
        let symbols = defined(&["A"]);
        assert_eq!(evaluate_condition("A // why", &symbols), Some(true));
    }

    #[test]
    fn nonsense_is_rejected() {
        let symbols = defined(&[]);
        assert_eq!(evaluate_condition("", &symbols), None);
        assert_eq!(evaluate_condition("A +", &symbols), None);
        assert_eq!(evaluate_condition("(A", &symbols), None);
    }
}
