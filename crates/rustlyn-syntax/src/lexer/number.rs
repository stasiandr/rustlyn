//! Numeric literals.

use rustlyn_diagnostics::ErrorCode;

use super::{Lexer, Scan};
use crate::{SyntaxKind, TokenValue};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Radix {
    Decimal = 10,
    Hex = 16,
    Binary = 2,
}

/// The letter a literal ends with, which pins down its type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Suffix {
    None,
    /// `u`
    Unsigned,
    /// `l`
    Long,
    /// `ul`
    UnsignedLong,
    /// `f`
    Float,
    /// `d`
    Double,
    /// `m`
    Decimal,
}

/// What one run of digits contained.
#[derive(Clone, Copy, Debug)]
struct DigitRun {
    count: usize,
    /// Whether the run ended on a `_`, which C# does not allow.
    trailing_separator: bool,
}

impl Lexer<'_> {
    /// Scans an integer or real literal and decodes its value.
    pub(crate) fn scan_numeric_literal(&mut self) -> Scan {
        let start = self.position();
        // The digits with `_` separators stripped, ready to be parsed.
        let mut digits = String::new();
        let mut radix = Radix::Decimal;
        let mut is_real = false;
        let mut malformed = false;

        if self.peek() == Some('0') && matches!(self.peek_nth(1), Some('x' | 'X')) {
            radix = Radix::Hex;
            self.advance(2);
            malformed |= self.scan_digits(&mut digits, radix).is_malformed();
        } else if self.peek() == Some('0') && matches!(self.peek_nth(1), Some('b' | 'B')) {
            radix = Radix::Binary;
            self.advance(2);
            malformed |= self.scan_digits(&mut digits, radix).is_malformed();
        } else {
            let whole = self.scan_digits(&mut digits, radix);
            malformed |= whole.trailing_separator;

            // A dot only continues the literal if a digit follows it, so that
            // `1.ToString()` and `1..2` still lex as three tokens.
            if self.peek() == Some('.') && self.peek_nth(1).is_some_and(|ch| ch.is_ascii_digit()) {
                is_real = true;
                self.bump();
                digits.push('.');
                malformed |= self.scan_digits(&mut digits, radix).is_malformed();
            } else if whole.count == 0 {
                malformed = true;
            }

            if matches!(self.peek(), Some('e' | 'E')) && self.exponent_follows() {
                is_real = true;
                self.bump();
                digits.push('e');
                if let Some(sign @ ('+' | '-')) = self.peek() {
                    self.bump();
                    digits.push(sign);
                }
                malformed |= self.scan_digits(&mut digits, radix).is_malformed();
            }
        }

        // `f`, `d` and `m` are hex digits or would be, so only a decimal
        // literal can carry a real suffix.
        let suffix = self.scan_suffix(radix == Radix::Decimal);

        if malformed {
            self.error(ErrorCode::ErrInvalidNumber, self.span_from(start), &[]);
            return Scan::kind(SyntaxKind::NumericLiteralToken);
        }

        let value = if is_real || matches!(suffix, Suffix::Float | Suffix::Double | Suffix::Decimal)
        {
            self.real_value(&digits, suffix, start)
        } else {
            self.integer_value(&digits, radix, suffix, start)
        };

        Scan::kind(SyntaxKind::NumericLiteralToken).with_value(value)
    }

    /// Whether `e` starts an exponent rather than an identifier, which decides
    /// whether `1e` is one token or two.
    fn exponent_follows(&self) -> bool {
        match self.peek_nth(1) {
            Some(ch) if ch.is_ascii_digit() => true,
            Some('+' | '-') => self.peek_nth(2).is_some_and(|ch| ch.is_ascii_digit()),
            _ => false,
        }
    }

    /// Consumes digits of `radix`, dropping the `_` separators between them.
    fn scan_digits(&mut self, out: &mut String, radix: Radix) -> DigitRun {
        let mut run = DigitRun {
            count: 0,
            trailing_separator: false,
        };
        while let Some(ch) = self.peek() {
            if ch == '_' {
                self.bump();
                run.trailing_separator = true;
                continue;
            }
            if ch.to_digit(radix as u32).is_none() {
                break;
            }
            self.bump();
            out.push(ch);
            run.count += 1;
            run.trailing_separator = false;
        }
        run
    }

    fn scan_suffix(&mut self, allow_real: bool) -> Suffix {
        match self.peek() {
            Some('u' | 'U') => {
                self.bump();
                if matches!(self.peek(), Some('l' | 'L')) {
                    self.bump();
                    Suffix::UnsignedLong
                } else {
                    Suffix::Unsigned
                }
            }
            Some('l' | 'L') => {
                self.bump();
                if matches!(self.peek(), Some('u' | 'U')) {
                    self.bump();
                    Suffix::UnsignedLong
                } else {
                    Suffix::Long
                }
            }
            Some('f' | 'F') if allow_real => {
                self.bump();
                Suffix::Float
            }
            Some('d' | 'D') if allow_real => {
                self.bump();
                Suffix::Double
            }
            Some('m' | 'M') if allow_real => {
                self.bump();
                Suffix::Decimal
            }
            _ => Suffix::None,
        }
    }

    fn integer_value(
        &mut self,
        digits: &str,
        radix: Radix,
        suffix: Suffix,
        start: u32,
    ) -> TokenValue {
        let Ok(value) = u64::from_str_radix(digits, radix as u32) else {
            self.error(ErrorCode::ErrIntOverflow, self.span_from(start), &[]);
            return TokenValue::None;
        };

        // §6.4.5.3: the literal takes the first type of its suffix's list that
        // can hold it.
        match suffix {
            Suffix::None if value <= i32::MAX as u64 => TokenValue::Int32(value as i32),
            Suffix::None if value <= u32::MAX as u64 => TokenValue::UInt32(value as u32),
            Suffix::None | Suffix::Long if value <= i64::MAX as u64 => {
                TokenValue::Int64(value as i64)
            }
            Suffix::Unsigned if value <= u32::MAX as u64 => TokenValue::UInt32(value as u32),
            _ => TokenValue::UInt64(value),
        }
    }

    fn real_value(&mut self, digits: &str, suffix: Suffix, start: u32) -> TokenValue {
        if suffix == Suffix::Decimal {
            return TokenValue::Decimal(digits.into());
        }

        // Rust and C# both round to nearest, so parsing the cleaned-up digits
        // gives the value the C# compiler would compute.
        if suffix == Suffix::Float {
            let value: f32 = digits.parse().unwrap_or(f32::INFINITY);
            if value.is_infinite() {
                self.error(
                    ErrorCode::ErrFloatOverflow,
                    self.span_from(start),
                    &["float"],
                );
                return TokenValue::None;
            }
            return TokenValue::Single(value);
        }

        let value: f64 = digits.parse().unwrap_or(f64::INFINITY);
        if value.is_infinite() {
            self.error(
                ErrorCode::ErrFloatOverflow,
                self.span_from(start),
                &["double"],
            );
            return TokenValue::None;
        }
        TokenValue::Double(value)
    }
}

impl DigitRun {
    const fn is_malformed(self) -> bool {
        self.count == 0 || self.trailing_separator
    }
}
