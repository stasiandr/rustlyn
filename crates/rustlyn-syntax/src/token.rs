use rustlyn_text::{SourceText, TextSpan};

use crate::SyntaxKind;

/// Whitespace, a line break or a comment: text that carries no meaning for the
/// grammar but must survive so that a parsed tree can reproduce its source
/// byte for byte.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Trivia {
    pub kind: SyntaxKind,
    pub span: TextSpan,
}

impl Trivia {
    #[must_use]
    pub const fn new(kind: SyntaxKind, span: TextSpan) -> Self {
        Self { kind, span }
    }

    #[must_use]
    pub fn text<'a>(&self, source: &'a SourceText) -> &'a str {
        source.slice(self.span)
    }

    /// Whether the trivia is a comment of any flavour.
    #[must_use]
    pub const fn is_comment(&self) -> bool {
        matches!(
            self.kind,
            SyntaxKind::SingleLineCommentTrivia
                | SyntaxKind::MultiLineCommentTrivia
                | SyntaxKind::SingleLineDocumentationCommentTrivia
                | SyntaxKind::MultiLineDocumentationCommentTrivia
        )
    }

    /// Whether the trivia is a documentation comment.
    #[must_use]
    pub const fn is_documentation(&self) -> bool {
        matches!(
            self.kind,
            SyntaxKind::SingleLineDocumentationCommentTrivia
                | SyntaxKind::MultiLineDocumentationCommentTrivia
        )
    }
}

/// The decoded value of a literal token.
///
/// The variant records the type C# gives the literal, which is why an
/// unsuffixed `1` is [`TokenValue::Int32`] while `1u` is
/// [`TokenValue::UInt32`]. `decimal` has no Rust counterpart, so its digits
/// are kept verbatim until the binder needs them.
#[derive(Clone, PartialEq, Debug, Default)]
pub enum TokenValue {
    #[default]
    None,
    Int32(i32),
    UInt32(u32),
    Int64(i64),
    UInt64(u64),
    Single(f32),
    Double(f64),
    Decimal(Box<str>),
    Char(char),
    String(Box<str>),
}

impl TokenValue {
    #[must_use]
    pub const fn is_none(&self) -> bool {
        matches!(self, Self::None)
    }
}

/// A lexed token together with the trivia attached to it.
///
/// Leading trivia is everything since the previous token; trailing trivia is
/// what follows on the same line, up to and including the line break. Splitting
/// it this way is what lets a comment stay with the line it was written on.
#[derive(Clone, PartialEq, Debug)]
pub struct Token {
    /// What the token is. Contextual keywords are [`SyntaxKind::IdentifierToken`].
    pub kind: SyntaxKind,
    /// The contextual keyword this token spells, or `kind` when it spells none.
    pub contextual_kind: SyntaxKind,
    /// The token itself, without trivia.
    pub span: TextSpan,
    /// The token together with its leading and trailing trivia.
    pub full_span: TextSpan,
    pub leading_trivia: Vec<Trivia>,
    pub trailing_trivia: Vec<Trivia>,
    /// The decoded value of a literal token.
    pub value: TokenValue,
    /// The identifier's spelling once `@` and `\u` escapes are resolved, when
    /// that differs from the source text.
    pub value_text: Option<Box<str>>,
}

impl Token {
    /// The source text of the token, without trivia.
    #[must_use]
    pub fn text<'a>(&self, source: &'a SourceText) -> &'a str {
        source.slice(self.span)
    }

    /// The source text of the token including its trivia.
    #[must_use]
    pub fn full_text<'a>(&self, source: &'a SourceText) -> &'a str {
        source.slice(self.full_span)
    }

    /// The identifier spelling this token denotes: `@class` and `class`
    /// both yield `class`.
    #[must_use]
    pub fn value_text<'a>(&'a self, source: &'a SourceText) -> &'a str {
        match &self.value_text {
            Some(text) => text,
            None => self.text(source),
        }
    }

    #[must_use]
    pub fn is_kind(&self, kind: SyntaxKind) -> bool {
        self.kind == kind
    }

    /// Whether the token is a keyword, contextual ones included.
    #[must_use]
    pub fn is_keyword(&self) -> bool {
        self.kind.is_reserved_keyword() || self.contextual_kind.is_contextual_keyword()
    }

    #[must_use]
    pub fn is_end_of_file(&self) -> bool {
        self.kind == SyntaxKind::EndOfFileToken
    }
}
