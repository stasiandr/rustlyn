//! The green tree: immutable nodes that know their width but not where they
//! are.
//!
//! This is the half of Roslyn's design that makes an incremental compiler
//! possible. A green node stores only its kind, its children and how many
//! characters it spans, so the very same node can sit at three different
//! offsets in three different versions of a file, and re-parsing an edit can
//! keep every subtree the edit did not touch. Positions live in the red tree
//! ([`crate::SyntaxNode`]), which is built on top of this one and thrown away
//! freely.
//!
//! Green nodes are shared through [`Arc`], and identical trivia is interned, so
//! the thousands of single-space runs in a file cost one allocation between
//! them.

mod cache;

use std::sync::Arc;

use rustlyn_text::SourceText;

use crate::{SyntaxKind, Token, TokenValue};

pub use cache::GreenCache;
pub(crate) use cache::NodeCache;

/// A run of whitespace, a line break or a comment.
#[derive(Debug, PartialEq, Eq)]
pub struct GreenTrivia {
    kind: SyntaxKind,
    text: Box<str>,
}

impl GreenTrivia {
    #[must_use]
    pub fn new(kind: SyntaxKind, text: &str) -> Self {
        debug_assert!(kind.is_trivia());
        Self {
            kind,
            text: text.into(),
        }
    }

    #[must_use]
    pub const fn kind(&self) -> SyntaxKind {
        self.kind
    }

    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    #[must_use]
    pub fn width(&self) -> u32 {
        self.text.len() as u32
    }
}

/// A leaf of the tree: one token with the trivia that surrounds it.
#[derive(Debug)]
pub struct GreenToken {
    kind: SyntaxKind,
    contextual_kind: SyntaxKind,
    text: Box<str>,
    leading: Box<[Arc<GreenTrivia>]>,
    trailing: Box<[Arc<GreenTrivia>]>,
    value: TokenValue,
    value_text: Option<Box<str>>,
    /// Whether the parser invented this token to repair the tree.
    missing: bool,
    /// The widths of the trivia on either side, summed once: every position
    /// in a red tree is worked out from them.
    leading_width: u32,
    trailing_width: u32,
}

impl GreenToken {
    #[must_use]
    pub fn new(
        kind: SyntaxKind,
        contextual_kind: SyntaxKind,
        text: &str,
        leading: Vec<Arc<GreenTrivia>>,
        trailing: Vec<Arc<GreenTrivia>>,
        value: TokenValue,
        value_text: Option<Box<str>>,
    ) -> Self {
        Self {
            kind,
            contextual_kind,
            text: text.into(),
            leading_width: leading.iter().map(|t| t.width()).sum(),
            trailing_width: trailing.iter().map(|t| t.width()).sum(),
            leading: leading.into_boxed_slice(),
            trailing: trailing.into_boxed_slice(),
            value,
            value_text,
            missing: false,
        }
    }

    /// A zero-width stand-in for a token the source never had.
    ///
    /// The parser inserts these so that a tree with syntax errors still has the
    /// shape the grammar calls for, which is what lets everything downstream
    /// keep working on broken code.
    #[must_use]
    pub fn missing(kind: SyntaxKind) -> Self {
        Self {
            kind,
            contextual_kind: kind,
            text: "".into(),
            leading: Box::new([]),
            trailing: Box::new([]),
            value: TokenValue::None,
            value_text: None,
            missing: true,
            leading_width: 0,
            trailing_width: 0,
        }
    }

    #[must_use]
    pub const fn kind(&self) -> SyntaxKind {
        self.kind
    }

    #[must_use]
    pub const fn contextual_kind(&self) -> SyntaxKind {
        self.contextual_kind
    }

    /// The token's own text, without trivia.
    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    /// What the token spells once `@` and escapes are resolved.
    #[must_use]
    pub fn value_text(&self) -> &str {
        self.value_text.as_deref().unwrap_or(&self.text)
    }

    #[must_use]
    pub const fn value(&self) -> &TokenValue {
        &self.value
    }

    #[must_use]
    pub const fn is_missing(&self) -> bool {
        self.missing
    }

    #[must_use]
    pub fn leading_trivia(&self) -> &[Arc<GreenTrivia>] {
        &self.leading
    }

    #[must_use]
    pub fn trailing_trivia(&self) -> &[Arc<GreenTrivia>] {
        &self.trailing
    }

    #[must_use]
    pub const fn leading_width(&self) -> u32 {
        self.leading_width
    }

    #[must_use]
    pub const fn trailing_width(&self) -> u32 {
        self.trailing_width
    }

    /// The width of the token itself.
    #[must_use]
    pub fn width(&self) -> u32 {
        self.text.len() as u32
    }

    /// The width of the token plus its trivia.
    #[must_use]
    pub fn full_width(&self) -> u32 {
        self.leading_width() + self.width() + self.trailing_width()
    }

    fn write_full_text(&self, out: &mut String) {
        for trivia in &self.leading {
            out.push_str(trivia.text());
        }
        out.push_str(&self.text);
        for trivia in &self.trailing {
            out.push_str(trivia.text());
        }
    }
}

/// An interior node: a kind plus the children under it.
///
/// The trivia widths at its edges are kept, not found: finding them walks
/// down to the first and the last token, which is as deep as the node is,
/// and every span asks for them. Asked of each ancestor in a deep tree — a
/// chain of calls, nested parentheses — that walk made the question cost the
/// square of the depth (found by fuzzing, `examples/fuzz.rs` in
/// rustlyn-ide). They cost nothing to keep: a node's allocation had the room.
#[derive(Debug)]
pub struct GreenNode {
    kind: SyntaxKind,
    /// How many nodes deep the tree under this one goes, itself counted;
    /// see [`Self::height`].
    height: u16,
    full_width: u32,
    leading_width: u32,
    trailing_width: u32,
    children: Box<[GreenElement]>,
}

impl GreenNode {
    #[must_use]
    pub fn new(kind: SyntaxKind, children: Vec<GreenElement>) -> Arc<Self> {
        let full_width = children.iter().map(GreenElement::full_width).sum();
        // The children's own widths are kept already, so this is a step, not
        // a walk.
        let leading_width = children
            .iter()
            .find(|child| child.full_width() > 0)
            .map_or(0, GreenElement::leading_width);
        let trailing_width = children
            .iter()
            .rev()
            .find(|child| child.full_width() > 0)
            .map_or(0, GreenElement::trailing_width);
        let height = children
            .iter()
            .map(GreenElement::height)
            .max()
            .unwrap_or(0)
            .saturating_add(1);
        Arc::new(Self {
            kind,
            height,
            full_width,
            leading_width,
            trailing_width,
            children: children.into_boxed_slice(),
        })
    }

    #[must_use]
    pub const fn kind(&self) -> SyntaxKind {
        self.kind
    }

    /// How many nodes deep the tree under this one goes, itself counted: 1
    /// for a node holding only tokens. Everything that walks a tree by
    /// recursion goes this deep, so the parser keeps it under a limit
    /// instead of handing out a tree nothing can walk; kept, not found, for
    /// the same reason the widths are.
    #[must_use]
    pub const fn height(&self) -> u16 {
        self.height
    }

    #[must_use]
    pub const fn full_width(&self) -> u32 {
        self.full_width
    }

    #[must_use]
    pub fn children(&self) -> &[GreenElement] {
        &self.children
    }

    /// The child in slot `index`, in Roslyn's vocabulary.
    #[must_use]
    pub fn slot(&self, index: usize) -> Option<&GreenElement> {
        self.children.get(index)
    }

    /// The trivia width in front of the first token underneath this node.
    #[must_use]
    pub const fn leading_width(&self) -> u32 {
        self.leading_width
    }

    /// The trivia width after the last token underneath this node.
    #[must_use]
    pub const fn trailing_width(&self) -> u32 {
        self.trailing_width
    }

    fn write_full_text(&self, out: &mut String) {
        for child in &self.children {
            child.write_full_text(out);
        }
    }
}

/// A child of a green node: either another node or a token.
#[derive(Debug, Clone)]
pub enum GreenElement {
    Node(Arc<GreenNode>),
    Token(Arc<GreenToken>),
}

impl GreenElement {
    #[must_use]
    pub fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(node) => node.kind(),
            Self::Token(token) => token.kind(),
        }
    }

    /// A node's [`GreenNode::height`]; a token has none.
    #[must_use]
    pub fn height(&self) -> u16 {
        match self {
            Self::Node(node) => node.height(),
            Self::Token(_) => 0,
        }
    }

    #[must_use]
    pub fn full_width(&self) -> u32 {
        match self {
            Self::Node(node) => node.full_width(),
            Self::Token(token) => token.full_width(),
        }
    }

    #[must_use]
    pub fn leading_width(&self) -> u32 {
        match self {
            Self::Node(node) => node.leading_width(),
            Self::Token(token) => token.leading_width(),
        }
    }

    #[must_use]
    pub fn trailing_width(&self) -> u32 {
        match self {
            Self::Node(node) => node.trailing_width(),
            Self::Token(token) => token.trailing_width(),
        }
    }

    #[must_use]
    pub fn as_node(&self) -> Option<&Arc<GreenNode>> {
        match self {
            Self::Node(node) => Some(node),
            Self::Token(_) => None,
        }
    }

    #[must_use]
    pub fn as_token(&self) -> Option<&Arc<GreenToken>> {
        match self {
            Self::Token(token) => Some(token),
            Self::Node(_) => None,
        }
    }

    /// Appends the text this element covers, trivia included.
    pub fn write_full_text(&self, out: &mut String) {
        match self {
            Self::Node(node) => node.write_full_text(out),
            Self::Token(token) => token.write_full_text(out),
        }
    }

    /// The text this element covers, trivia included.
    #[must_use]
    pub fn full_text(&self) -> String {
        let mut out = String::new();
        self.write_full_text(&mut out);
        out
    }
}

impl From<Arc<GreenNode>> for GreenElement {
    fn from(node: Arc<GreenNode>) -> Self {
        Self::Node(node)
    }
}

impl From<Arc<GreenToken>> for GreenElement {
    fn from(token: Arc<GreenToken>) -> Self {
        Self::Token(token)
    }
}

/// Turns a lexed token into a green token, interning its trivia.
#[must_use]
pub fn green_token(token: &Token, source: &SourceText, cache: &mut GreenCache) -> Arc<GreenToken> {
    green_token_as(token, token.kind, source, cache)
}

/// Turns a lexed token into a green token of a different kind.
///
/// This is how a contextual keyword becomes a keyword: the lexer hands back
/// `yield` as an identifier, and the parser, once it knows the identifier is
/// starting a `yield return`, rewrites the kind. Roslyn calls the same move
/// `ConvertToKeyword`.
#[must_use]
pub fn green_token_as(
    token: &Token,
    kind: SyntaxKind,
    source: &SourceText,
    cache: &mut GreenCache,
) -> Arc<GreenToken> {
    let leading = token
        .leading_trivia
        .iter()
        .map(|trivia| cache.trivia(trivia.kind, source.slice(trivia.span)))
        .collect();
    let trailing = token
        .trailing_trivia
        .iter()
        .map(|trivia| cache.trivia(trivia.kind, source.slice(trivia.span)))
        .collect();

    if matches!(token.value, TokenValue::None) && token.value_text.is_none() {
        return cache.token(
            kind,
            token.contextual_kind,
            token.text(source),
            leading,
            trailing,
        );
    }
    Arc::new(GreenToken::new(
        kind,
        token.contextual_kind,
        token.text(source),
        leading,
        trailing,
        token.value.clone(),
        token.value_text.clone(),
    ))
}
