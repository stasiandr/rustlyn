//! Source text handling for Rustlyn.
//!
//! Everything downstream — the lexer, the parser, diagnostics — addresses code
//! through [`TextSpan`] offsets into a [`SourceText`], so this crate is the one
//! place that knows how bytes map to lines and columns.

mod line_index;
mod source_text;
mod span;

pub use line_index::{LineIndex, is_line_break};
pub use source_text::SourceText;
pub use span::{LinePosition, LinePositionSpan, TextSpan};
