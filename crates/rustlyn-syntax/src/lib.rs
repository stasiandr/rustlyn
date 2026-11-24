//! Syntax for Rustlyn: the kinds of the C# grammar, and the lexer that turns
//! source text into tokens.
//!
//! The guiding constraint, borrowed from Roslyn, is *full fidelity*: the tokens
//! for a file cover it completely, so pasting their text back together
//! reproduces the input byte for byte, comments and whitespace included.

pub mod green;
mod kind;
mod language_version;
mod lexer;
mod parser;
mod red;
mod token;

pub use kind::{SyntaxKind, contextual_keyword_kind, kind_from_text, reserved_keyword_kind};
pub use language_version::{LanguageVersion, UnknownLanguageVersion};
pub use lexer::{LexResult, Lexer, LexerState, ParseOptions, tokenize, tokenize_with};
pub use parser::{parse, parse_with};
pub use red::{
    Ancestors, ChildElements, DescendantTokens, Descendants, SyntaxElement, SyntaxNode,
    SyntaxToken, SyntaxTree, SyntaxTrivia,
};
pub use token::{Token, TokenValue, Trivia};
