//! A small direct-mapped cache for green trivia and tokens.
//!
//! A source file is mostly the same handful of trivia over and over: one space,
//! four spaces, a newline. Roslyn keeps a text-keyed cache in its lexer for
//! exactly this; the version here is the same idea, sized to a power of two so
//! the bucket index is a mask, and deliberately lossy — a collision throws the
//! older entry away rather than chaining, because a miss only costs one
//! allocation.
//!
//! Tokens repeat the same way — `;` and a newline, `(` with nothing around it,
//! `return` and a space — and Roslyn shares those green tokens too (its
//! `SyntaxNodeCache`). A green token knows no position, so one can stand in
//! as many places as it is written.

use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::SyntaxKind;
use crate::token::TokenValue;

use super::{GreenElement, GreenNode, GreenToken, GreenTrivia};

const BUCKETS: usize = 1 << 10;

/// Interns green trivia so repeated whitespace is allocated once, and
/// tokens with no value of their own so repeated punctuation and keywords are.
#[derive(Debug)]
pub struct GreenCache {
    entries: Box<[Option<Entry>]>,
    tokens: Box<[Option<TokenEntry>]>,
    hits: u64,
    misses: u64,
}

#[derive(Debug)]
struct Entry {
    hash: u64,
    trivia: Arc<GreenTrivia>,
}

#[derive(Debug)]
struct TokenEntry {
    hash: u64,
    token: Arc<GreenToken>,
}

impl Default for GreenCache {
    fn default() -> Self {
        Self::new()
    }
}

impl GreenCache {
    #[must_use]
    pub fn new() -> Self {
        Self {
            entries: std::iter::repeat_with(|| None).take(BUCKETS).collect(),
            tokens: std::iter::repeat_with(|| None).take(BUCKETS).collect(),
            hits: 0,
            misses: 0,
        }
    }

    /// The shared green token with this kind, text and trivia and no value,
    /// making it the first time. The trivia are compared by identity: they
    /// came out of [`GreenCache::trivia`], so equal trivia are one allocation
    /// as long as neither was pushed out of its bucket.
    pub fn token(
        &mut self,
        kind: SyntaxKind,
        contextual_kind: SyntaxKind,
        text: &str,
        leading: Vec<Arc<GreenTrivia>>,
        trailing: Vec<Arc<GreenTrivia>>,
    ) -> Arc<GreenToken> {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        kind.hash(&mut hasher);
        contextual_kind.hash(&mut hasher);
        text.hash(&mut hasher);
        leading.len().hash(&mut hasher);
        for trivia in leading.iter().chain(&trailing) {
            std::ptr::hash(Arc::as_ptr(trivia), &mut hasher);
        }
        let hash = hasher.finish();
        let bucket = (hash as usize) & (BUCKETS - 1);
        if let Some(TokenEntry { hash: known, token }) = &self.tokens[bucket]
            && *known == hash
            && token.kind() == kind
            && token.contextual_kind() == contextual_kind
            && token.text() == text
            && same_trivia(token.leading_trivia(), &leading)
            && same_trivia(token.trailing_trivia(), &trailing)
        {
            return Arc::clone(token);
        }
        let token = Arc::new(GreenToken::new(
            kind,
            contextual_kind,
            text,
            leading,
            trailing,
            TokenValue::None,
            None,
        ));
        self.tokens[bucket] = Some(TokenEntry {
            hash,
            token: Arc::clone(&token),
        });
        token
    }

    /// Returns the interned trivia with this kind and text, creating it once.
    pub fn trivia(&mut self, kind: SyntaxKind, text: &str) -> Arc<GreenTrivia> {
        let hash = hash_of(kind, text);
        let bucket = (hash as usize) & (BUCKETS - 1);

        if let Some(entry) = &self.entries[bucket]
            && entry.hash == hash
            && entry.trivia.kind() == kind
            && entry.trivia.text() == text
        {
            self.hits += 1;
            return Arc::clone(&entry.trivia);
        }

        self.misses += 1;
        let trivia = Arc::new(GreenTrivia::new(kind, text));
        self.entries[bucket] = Some(Entry {
            hash,
            trivia: Arc::clone(&trivia),
        });
        trivia
    }

    /// How often a lookup found an existing allocation. Useful for gauging
    /// whether the cache is worth its size.
    #[must_use]
    pub const fn stats(&self) -> (u64, u64) {
        (self.hits, self.misses)
    }
}

/// Interns small green nodes by their kind and the identity of their
/// children, direct-mapped and lossy like [`GreenCache`].
#[derive(Debug)]
pub(crate) struct NodeCache {
    entries: Box<[Option<NodeEntry>]>,
}

impl Default for NodeCache {
    fn default() -> Self {
        Self {
            entries: std::iter::repeat_with(|| None).take(NODE_BUCKETS).collect(),
        }
    }
}

const NODE_BUCKETS: usize = 1 << 12;

#[derive(Debug)]
struct NodeEntry {
    hash: u64,
    node: Arc<GreenNode>,
}

impl NodeCache {
    /// The shared node of this kind over these very children, making it the
    /// first time.
    pub(crate) fn node(&mut self, kind: SyntaxKind, children: Vec<GreenElement>) -> Arc<GreenNode> {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        kind.hash(&mut hasher);
        for child in &children {
            element_address(child).hash(&mut hasher);
        }
        let hash = hasher.finish();
        let bucket = (hash as usize) & (NODE_BUCKETS - 1);
        if let Some(NodeEntry { hash: known, node }) = &self.entries[bucket]
            && *known == hash
            && node.kind() == kind
            && node.children().len() == children.len()
            && node
                .children()
                .iter()
                .zip(&children)
                .all(|(a, b)| element_address(a) == element_address(b))
        {
            return Arc::clone(node);
        }
        let node = GreenNode::new(kind, children);
        self.entries[bucket] = Some(NodeEntry {
            hash,
            node: Arc::clone(&node),
        });
        node
    }
}

/// Which allocation a green child is, and whether it is a node or a token.
fn element_address(element: &GreenElement) -> (bool, usize) {
    match element {
        GreenElement::Node(node) => (true, Arc::as_ptr(node) as usize),
        GreenElement::Token(token) => (false, Arc::as_ptr(token) as usize),
    }
}

/// Whether two lists of trivia are the same allocations in the same order.
fn same_trivia(a: &[Arc<GreenTrivia>], b: &[Arc<GreenTrivia>]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| Arc::ptr_eq(a, b))
}

fn hash_of(kind: SyntaxKind, text: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    kind.hash(&mut hasher);
    text.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repeated_trivia_is_shared() {
        let mut cache = GreenCache::new();
        let a = cache.trivia(SyntaxKind::WhitespaceTrivia, "    ");
        let b = cache.trivia(SyntaxKind::WhitespaceTrivia, "    ");
        assert!(Arc::ptr_eq(&a, &b));
        assert_eq!(cache.stats(), (1, 1));
    }

    #[test]
    fn different_text_is_not_shared() {
        let mut cache = GreenCache::new();
        let a = cache.trivia(SyntaxKind::WhitespaceTrivia, " ");
        let b = cache.trivia(SyntaxKind::WhitespaceTrivia, "  ");
        assert!(!Arc::ptr_eq(&a, &b));
        assert_eq!(b.text(), "  ");
    }

    #[test]
    fn a_token_with_the_same_text_and_trivia_is_shared() {
        let mut cache = GreenCache::new();
        let space = cache.trivia(SyntaxKind::WhitespaceTrivia, " ");
        let semicolon = SyntaxKind::SemicolonToken;
        let a = cache.token(
            semicolon,
            semicolon,
            ";",
            Vec::new(),
            vec![Arc::clone(&space)],
        );
        let b = cache.token(
            semicolon,
            semicolon,
            ";",
            Vec::new(),
            vec![Arc::clone(&space)],
        );
        assert!(Arc::ptr_eq(&a, &b));
        assert_eq!(b.trailing_width(), 1);
    }

    #[test]
    fn a_token_with_other_trivia_is_not_shared() {
        let mut cache = GreenCache::new();
        let space = cache.trivia(SyntaxKind::WhitespaceTrivia, " ");
        let semicolon = SyntaxKind::SemicolonToken;
        let a = cache.token(
            semicolon,
            semicolon,
            ";",
            Vec::new(),
            vec![Arc::clone(&space)],
        );
        let b = cache.token(semicolon, semicolon, ";", vec![space], Vec::new());
        let c = cache.token(semicolon, semicolon, ";", Vec::new(), Vec::new());
        assert!(!Arc::ptr_eq(&a, &b));
        assert!(!Arc::ptr_eq(&a, &c));
        assert_eq!((b.leading_width(), b.trailing_width()), (1, 0));
    }

    #[test]
    fn a_small_node_over_the_same_children_is_shared() {
        let mut cache = GreenCache::new();
        let mut nodes = NodeCache::default();
        let name = SyntaxKind::IdentifierToken;
        let x = cache.token(name, name, "x", Vec::new(), Vec::new());
        let y = cache.token(name, name, "y", Vec::new(), Vec::new());
        let a = nodes.node(
            SyntaxKind::IdentifierName,
            vec![GreenElement::Token(Arc::clone(&x))],
        );
        let b = nodes.node(SyntaxKind::IdentifierName, vec![GreenElement::Token(x)]);
        let c = nodes.node(SyntaxKind::IdentifierName, vec![GreenElement::Token(y)]);
        assert!(Arc::ptr_eq(&a, &b));
        assert!(!Arc::ptr_eq(&a, &c));
    }

    #[test]
    fn kind_is_part_of_the_key() {
        let mut cache = GreenCache::new();
        let a = cache.trivia(SyntaxKind::WhitespaceTrivia, "\n");
        let b = cache.trivia(SyntaxKind::EndOfLineTrivia, "\n");
        assert!(!Arc::ptr_eq(&a, &b));
        assert_eq!(b.kind(), SyntaxKind::EndOfLineTrivia);
    }
}
