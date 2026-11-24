//! Identifiers, keywords and the `@` verbatim prefix.

use rustlyn_diagnostics::ErrorCode;

use super::chars::{is_identifier_part, is_identifier_start};
use super::{Lexer, Scan};
use crate::SyntaxKind;
use crate::kind::{contextual_keyword_kind, reserved_keyword_kind};

impl<'a> Lexer<'a> {
    /// Scans whatever follows an `@`: a verbatim string, or an identifier that
    /// is allowed to spell a keyword.
    pub(crate) fn scan_verbatim(&mut self) -> Scan {
        match self.peek_nth(1) {
            Some('"') => self.scan_verbatim_string_literal(),
            Some('$') if self.peek_nth(2) == Some('"') => self.scan_interpolated_start(true),
            Some('\\') if matches!(self.peek_nth(2), Some('u' | 'U')) => self.scan_identifier(),
            Some(ch) if is_identifier_start(ch) => self.scan_identifier(),
            _ => {
                let start = self.position();
                self.bump(); // `@`
                self.error(
                    ErrorCode::ErrExpectedVerbatimLiteral,
                    self.span_from(start),
                    &[],
                );
                Scan::kind(SyntaxKind::BadToken)
            }
        }
    }

    /// Scans an identifier and decides whether it spells a keyword.
    ///
    /// Reserved keywords become their own kind. Contextual keywords stay
    /// identifiers and only record what they *could* mean, because whether
    /// `record` introduces a type or names a variable is the parser's call.
    pub(crate) fn scan_identifier(&mut self) -> Scan {
        let text = self.source_str();
        let start = self.position();
        let verbatim = self.eat('@');
        let body_start = self.position();

        // Only allocated when the spelling differs from the source text, which
        // is the rare case of `@name` or an escaped character.
        let mut decoded: Option<String> = verbatim.then(String::new);
        let mut escaped = false;
        let mut length = 0usize;

        loop {
            let is_first = self.position() == body_start;
            let accepts = |ch: char| {
                if is_first {
                    is_identifier_start(ch)
                } else {
                    is_identifier_part(ch)
                }
            };

            let char_start = self.position();
            match self.peek() {
                Some('\\') if matches!(self.peek_nth(1), Some('u' | 'U')) => {
                    let Some(ch) = self
                        .scan_unicode_escape_value()
                        .and_then(char::from_u32)
                        .filter(|ch| accepts(*ch))
                    else {
                        // The escape is not a usable identifier character; it
                        // has already been reported, so stop the identifier
                        // here rather than inventing one.
                        break;
                    };
                    let buffer = decoded.get_or_insert_with(|| {
                        text[body_start as usize..char_start as usize].to_string()
                    });
                    buffer.push(ch);
                    escaped = true;
                    length += 1;
                }
                Some(ch) if accepts(ch) => {
                    self.bump();
                    if let Some(buffer) = &mut decoded {
                        buffer.push(ch);
                    }
                    length += 1;
                }
                _ => break,
            }
        }

        if length == 0 {
            // `@` or a broken escape with nothing usable behind it.
            return Scan::kind(SyntaxKind::BadToken);
        }

        if verbatim || escaped {
            let spelling = decoded.expect("verbatim or escaped identifiers are decoded");
            return Scan::kind(SyntaxKind::IdentifierToken).with_value_text(spelling);
        }

        let spelling = &text[start as usize..self.position() as usize];
        if let Some(kind) = reserved_keyword_kind(spelling) {
            Scan::kind(kind)
        } else if let Some(kind) = contextual_keyword_kind(spelling) {
            Scan::kind(SyntaxKind::IdentifierToken).with_contextual_kind(kind)
        } else {
            Scan::kind(SyntaxKind::IdentifierToken)
        }
    }
}
