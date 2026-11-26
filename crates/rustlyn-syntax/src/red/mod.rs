//! The red tree: a positioned, navigable view over the green tree.
//!
//! Green nodes know their width but not where they sit, and they have no idea
//! who their parent is — that is what makes them shareable. The red tree adds
//! the missing half: each node here pairs a green node with an absolute
//! position and a link upwards. Red nodes are created on demand as you walk the
//! tree and thrown away just as cheaply, so the expensive half stays shared
//! while the convenient half stays disposable.

use std::fmt::{self, Write as _};
use std::sync::Arc;

use rustlyn_diagnostics::Diagnostic;
use rustlyn_text::{SourceText, TextSpan};

use crate::green::{GreenElement, GreenNode, GreenToken, GreenTrivia};
use crate::{LanguageVersion, SyntaxKind};

/// A parsed file: the source it came from, the tree, and what went wrong.
#[derive(Debug, Clone)]
pub struct SyntaxTree {
    source: SourceText,
    green: Arc<GreenNode>,
    diagnostics: Arc<[Diagnostic]>,
    /// The symbols that were defined while this file was parsed. `#if` is not
    /// the only thing they decide: a call to a `[Conditional("DEBUG")]` method
    /// is written out of the program where `DEBUG` is not one of them.
    defined: Arc<[String]>,
    /// The `#define`s and `#undef`s of the file, in order: where each stands,
    /// its symbol, and whether the symbol is defined from there on.
    definitions: Arc<[(u32, String, bool)]>,
    /// The version of C# the file was parsed as.
    language_version: LanguageVersion,
}

impl SyntaxTree {
    #[must_use]
    pub fn new(source: SourceText, green: Arc<GreenNode>, diagnostics: Vec<Diagnostic>) -> Self {
        Self::with_defined(source, green, diagnostics, Vec::new())
    }

    /// The same, remembering which preprocessor symbols were defined.
    #[must_use]
    pub fn with_defined(
        source: SourceText,
        green: Arc<GreenNode>,
        diagnostics: Vec<Diagnostic>,
        defined: Vec<String>,
    ) -> Self {
        Self {
            source,
            green,
            diagnostics: diagnostics.into(),
            defined: defined.into(),
            definitions: Arc::new([]),
            language_version: LanguageVersion::default(),
        }
    }

    /// The same tree, as parsed with `defined` instead: right only where no
    /// `#if` of the text asks about a symbol the two disagree on, since the
    /// tree's shape is left as it is.
    #[must_use]
    pub fn with_symbols(&self, defined: Vec<String>) -> Self {
        Self {
            defined: defined.into(),
            ..self.clone()
        }
    }

    /// The same tree, with the `#define`s and `#undef`s its text makes.
    #[must_use]
    pub fn with_definitions(mut self, definitions: Vec<(u32, String, bool)>) -> Self {
        self.definitions = definitions.into();
        self
    }

    /// The same tree, parsed as the given version of the language.
    #[must_use]
    pub fn with_language_version(mut self, version: LanguageVersion) -> Self {
        self.language_version = version;
        self
    }

    /// The version of C# this file was parsed as.
    #[must_use]
    pub const fn language_version(&self) -> LanguageVersion {
        self.language_version
    }

    /// The preprocessor symbols this file was parsed with.
    #[must_use]
    pub fn defined(&self) -> &[String] {
        &self.defined
    }

    /// Whether `symbol` is defined at `position`: by the options the file
    /// was parsed with, then as the `#define`s and `#undef`s before that
    /// point leave it — what Roslyn's `IsPreprocessorSymbolDefined` asks
    /// for a `[Conditional]` call.
    #[must_use]
    pub fn is_defined_at(&self, symbol: &str, position: u32) -> bool {
        self.definitions
            .iter()
            .take_while(|(at, _, _)| *at < position)
            .filter(|(_, name, _)| name == symbol)
            .last()
            .map_or_else(
                || self.defined.iter().any(|defined| defined == symbol),
                |(_, _, defined)| *defined,
            )
    }

    /// The root node, which is always a compilation unit.
    #[must_use]
    pub fn root(&self) -> SyntaxNode {
        SyntaxNode::root(Arc::clone(&self.green))
    }

    #[must_use]
    pub const fn source(&self) -> &SourceText {
        &self.source
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }

    /// The text the tree covers. For a tree straight from the parser this is
    /// the source file, byte for byte.
    #[must_use]
    pub fn text(&self) -> String {
        self.root().full_text()
    }
}

/// An interior node, positioned in a file.
#[derive(Clone)]
pub struct SyntaxNode(Arc<NodeData>);

#[derive(Debug)]
struct NodeData {
    green: Arc<GreenNode>,
    parent: Option<SyntaxNode>,
    /// Where the node starts, leading trivia included.
    position: u32,
    /// Which child of the parent this is.
    slot: u32,
}

/// The parents of a deep node are let go in a loop: each holds the one
/// above it, and dropping the last reference to the bottom of a tree
/// thousands of levels deep took a frame of stack for each of them.
impl Drop for NodeData {
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(SyntaxNode(node)) = parent {
            // Only the last reference to a node lets go of what it holds.
            parent = Arc::into_inner(node).and_then(|mut data| data.parent.take());
        }
    }
}

impl SyntaxNode {
    fn root(green: Arc<GreenNode>) -> Self {
        Self(Arc::new(NodeData {
            green,
            parent: None,
            position: 0,
            slot: 0,
        }))
    }

    fn child(green: Arc<GreenNode>, parent: Self, position: u32, slot: u32) -> Self {
        Self(Arc::new(NodeData {
            green,
            parent: Some(parent),
            position,
            slot,
        }))
    }

    #[must_use]
    pub fn kind(&self) -> SyntaxKind {
        self.0.green.kind()
    }

    #[must_use]
    pub fn green(&self) -> &Arc<GreenNode> {
        &self.0.green
    }

    #[must_use]
    pub fn parent(&self) -> Option<&Self> {
        self.0.parent.as_ref()
    }

    /// Which child of its parent this node is.
    #[must_use]
    pub fn slot(&self) -> u32 {
        self.0.slot
    }

    /// The node together with the trivia at its edges.
    #[must_use]
    pub fn full_span(&self) -> TextSpan {
        TextSpan::new(self.0.position, self.0.green.full_width())
    }

    /// The node without the trivia at its edges, which is what a diagnostic or
    /// an IDE selection should point at.
    #[must_use]
    pub fn span(&self) -> TextSpan {
        let full = self.full_span();
        TextSpan::from_bounds(
            full.start() + self.0.green.leading_width(),
            full.end() - self.0.green.trailing_width(),
        )
    }

    /// The text of the node, trivia at the edges included.
    #[must_use]
    pub fn full_text(&self) -> String {
        let mut out = String::new();
        GreenElement::Node(Arc::clone(&self.0.green)).write_full_text(&mut out);
        out
    }

    /// The text of the node without the trivia at its edges.
    #[must_use]
    pub fn text(&self) -> String {
        let full = self.full_text();
        let leading = self.0.green.leading_width() as usize;
        let trailing = self.0.green.trailing_width() as usize;
        full[leading..full.len() - trailing].to_string()
    }

    /// Whether the node covers no text at all, which happens when the parser
    /// built it entirely out of missing tokens.
    #[must_use]
    pub fn is_missing(&self) -> bool {
        self.descendant_tokens().all(|token| token.is_missing())
    }

    /// Children that are nodes and tokens alike, in source order.
    #[must_use]
    pub fn children_with_tokens(&self) -> ChildElements {
        ChildElements {
            parent: self.clone(),
            index: 0,
            offset: self.0.position,
        }
    }

    /// Children that are nodes, skipping tokens: a token is passed over in
    /// the green tree, where it costs nothing, rather than made red first.
    pub fn children(&self) -> impl Iterator<Item = Self> + use<> {
        ChildNodes {
            parent: self.clone(),
            index: 0,
            offset: self.0.position,
        }
    }

    /// Pushes this node's child nodes onto a stack, last first, so that
    /// popping gives them back in source order.
    fn push_children_reversed(&self, stack: &mut Vec<Self>) {
        let start = stack.len();
        let mut offset = self.0.position;
        for (index, green) in self.0.green.children().iter().enumerate() {
            if let GreenElement::Node(child) = green {
                stack.push(Self::child(
                    Arc::clone(child),
                    self.clone(),
                    offset,
                    index as u32,
                ));
            }
            offset += green.full_width();
        }
        stack[start..].reverse();
    }

    /// Children that are tokens, skipping nodes.
    pub fn child_tokens(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        self.children_with_tokens()
            .filter_map(SyntaxElement::into_token)
    }

    /// The first child node of the given kind.
    ///
    /// Asked far more often than it is answered: the search runs over the
    /// green children, where a kind costs nothing to read, and only the child
    /// that matches is made into a red node. Iterating `children()` instead
    /// would allocate one red node per child just to look at its kind, and a
    /// binder does this for every name it resolves.
    #[must_use]
    pub fn child_of_kind(&self, kind: SyntaxKind) -> Option<Self> {
        self.find_child(|green| matches!(green, GreenElement::Node(node) if node.kind() == kind))
            .and_then(SyntaxElement::into_node)
    }

    /// The first child token of the given kind.
    #[must_use]
    pub fn child_token_of_kind(&self, kind: SyntaxKind) -> Option<SyntaxToken> {
        self.find_child(|green| matches!(green, GreenElement::Token(token) if token.kind() == kind))
            .and_then(SyntaxElement::into_token)
    }

    /// The first child the green tree says matches, made red.
    fn find_child(&self, matches: impl Fn(&GreenElement) -> bool) -> Option<SyntaxElement> {
        let mut offset = self.0.position;
        let mut index = 0;
        while let Some(green) = self.0.green.slot(index) {
            if matches(green) {
                return Some(self.element_at(green, offset, index as u32));
            }
            offset += green.full_width();
            index += 1;
        }
        None
    }

    /// One green child, as a red element.
    fn element_at(&self, green: &GreenElement, position: u32, slot: u32) -> SyntaxElement {
        match green {
            GreenElement::Node(node) => {
                SyntaxElement::Node(Self::child(Arc::clone(node), self.clone(), position, slot))
            }
            GreenElement::Token(token) => SyntaxElement::Token(SyntaxToken {
                green: Arc::clone(token),
                parent: self.clone(),
                position,
                slot,
            }),
        }
    }

    /// Every node underneath this one, this node first, in source order.
    #[must_use]
    pub fn descendants(&self) -> Descendants {
        Descendants {
            stack: vec![self.clone()],
        }
    }

    /// Every token underneath this one, in source order.
    #[must_use]
    pub fn descendant_tokens(&self) -> DescendantTokens {
        DescendantTokens {
            stack: vec![SyntaxElement::Node(self.clone())],
        }
    }

    /// This node's ancestors, closest first.
    #[must_use]
    pub fn ancestors(&self) -> Ancestors {
        Ancestors {
            current: self.parent().cloned(),
        }
    }

    #[must_use]
    pub fn first_token(&self) -> Option<SyntaxToken> {
        self.descendant_tokens().next()
    }

    #[must_use]
    pub fn last_token(&self) -> Option<SyntaxToken> {
        self.descendant_tokens().last()
    }

    /// The token whose full span contains `position`.
    ///
    /// Walking down beats scanning the token list: each step skips every
    /// subtree that cannot contain the position.
    #[must_use]
    pub fn find_token(&self, position: u32) -> Option<SyntaxToken> {
        if !self.full_span().contains(position) {
            return None;
        }
        // The green children know their widths, so which one holds the
        // position is arithmetic, and only that one is made red.
        let mut node = self.clone();
        'descend: loop {
            let mut offset = node.0.position;
            let mut index = 0;
            while let Some(green) = node.0.green.slot(index) {
                let width = green.full_width();
                if TextSpan::new(offset, width).contains(position) {
                    match node.element_at(green, offset, index as u32) {
                        SyntaxElement::Token(token) => return Some(token),
                        SyntaxElement::Node(child) => {
                            node = child;
                            continue 'descend;
                        }
                    }
                }
                offset += width;
                index += 1;
            }
            return None;
        }
    }

    /// The innermost node whose span covers `span`.
    #[must_use]
    pub fn find_node(&self, span: TextSpan) -> Option<Self> {
        if !self.full_span().contains_span(span) {
            return None;
        }
        // One red node per level, not one per child: the green children know
        // their widths, so which one holds the span is arithmetic, and only
        // the winner has to be made into a node.
        let mut node = self.clone();
        'descend: loop {
            let mut offset = node.0.position;
            let mut index = 0;
            while let Some(green) = node.0.green.slot(index) {
                let width = green.full_width();
                if let GreenElement::Node(child) = green
                    && TextSpan::new(offset, width).contains_span(span)
                {
                    let child = Self::child(Arc::clone(child), node.clone(), offset, index as u32);
                    node = child;
                    continue 'descend;
                }
                offset += width;
                index += 1;
            }
            return Some(node);
        }
    }

    /// An indented dump of the subtree, for tests and for looking at.
    #[must_use]
    pub fn debug_tree(&self) -> String {
        let mut out = String::new();
        write_element(&mut out, &SyntaxElement::Node(self.clone()), 0);
        out
    }
}

fn write_element(out: &mut String, element: &SyntaxElement, depth: usize) {
    for _ in 0..depth {
        out.push_str("  ");
    }
    match element {
        SyntaxElement::Node(node) => {
            let _ = writeln!(out, "{:?} {}", node.kind(), node.span());
            for child in node.children_with_tokens() {
                write_element(out, &child, depth + 1);
            }
        }
        SyntaxElement::Token(token) => {
            if token.is_missing() {
                let _ = writeln!(out, "{:?} <missing> {}", token.kind(), token.span());
            } else {
                let _ = writeln!(
                    out,
                    "{:?} {:?} {}",
                    token.kind(),
                    token.text(),
                    token.span()
                );
            }
        }
    }
}

impl PartialEq for SyntaxNode {
    /// Two handles are the same node when they point at the same green node in
    /// the same place; the red wrappers themselves are disposable.
    fn eq(&self, other: &Self) -> bool {
        self.0.position == other.0.position && Arc::ptr_eq(&self.0.green, &other.0.green)
    }
}

impl Eq for SyntaxNode {}

impl fmt::Debug for SyntaxNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}@{}", self.kind(), self.span())
    }
}

impl fmt::Display for SyntaxNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.full_text())
    }
}

/// A token, positioned in a file.
#[derive(Clone)]
pub struct SyntaxToken {
    green: Arc<GreenToken>,
    parent: SyntaxNode,
    position: u32,
    slot: u32,
}

impl SyntaxToken {
    #[must_use]
    pub fn kind(&self) -> SyntaxKind {
        self.green.kind()
    }

    #[must_use]
    pub fn contextual_kind(&self) -> SyntaxKind {
        self.green.contextual_kind()
    }

    #[must_use]
    pub fn green(&self) -> &Arc<GreenToken> {
        &self.green
    }

    #[must_use]
    pub const fn parent(&self) -> &SyntaxNode {
        &self.parent
    }

    #[must_use]
    pub const fn slot(&self) -> u32 {
        self.slot
    }

    /// The token's text, without trivia.
    #[must_use]
    pub fn text(&self) -> &str {
        self.green.text()
    }

    /// What the token spells once `@` and escapes are resolved.
    #[must_use]
    pub fn value_text(&self) -> &str {
        self.green.value_text()
    }

    #[must_use]
    pub fn value(&self) -> &crate::TokenValue {
        self.green.value()
    }

    /// Whether the parser invented this token to repair a syntax error.
    #[must_use]
    pub fn is_missing(&self) -> bool {
        self.green.is_missing()
    }

    #[must_use]
    pub fn full_span(&self) -> TextSpan {
        TextSpan::new(self.position, self.green.full_width())
    }

    #[must_use]
    pub fn span(&self) -> TextSpan {
        TextSpan::new(
            self.position + self.green.leading_width(),
            self.green.width(),
        )
    }

    #[must_use]
    pub fn full_text(&self) -> String {
        GreenElement::Token(Arc::clone(&self.green)).full_text()
    }

    #[must_use]
    pub fn leading_trivia(&self) -> Vec<SyntaxTrivia> {
        let mut position = self.position;
        self.green
            .leading_trivia()
            .iter()
            .map(|green| {
                let trivia = SyntaxTrivia {
                    green: Arc::clone(green),
                    position,
                };
                position += green.width();
                trivia
            })
            .collect()
    }

    #[must_use]
    pub fn trailing_trivia(&self) -> Vec<SyntaxTrivia> {
        let mut position = self.position + self.green.leading_width() + self.green.width();
        self.green
            .trailing_trivia()
            .iter()
            .map(|green| {
                let trivia = SyntaxTrivia {
                    green: Arc::clone(green),
                    position,
                };
                position += green.width();
                trivia
            })
            .collect()
    }
}

impl PartialEq for SyntaxToken {
    fn eq(&self, other: &Self) -> bool {
        self.position == other.position && Arc::ptr_eq(&self.green, &other.green)
    }
}

impl Eq for SyntaxToken {}

impl fmt::Debug for SyntaxToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}@{} {:?}", self.kind(), self.span(), self.text())
    }
}

impl fmt::Display for SyntaxToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.full_text())
    }
}

/// A piece of trivia, positioned in a file.
#[derive(Clone, Debug)]
pub struct SyntaxTrivia {
    green: Arc<GreenTrivia>,
    position: u32,
}

impl SyntaxTrivia {
    #[must_use]
    pub fn kind(&self) -> SyntaxKind {
        self.green.kind()
    }

    #[must_use]
    pub fn text(&self) -> &str {
        self.green.text()
    }

    #[must_use]
    pub fn span(&self) -> TextSpan {
        TextSpan::new(self.position, self.green.width())
    }
}

/// A node or a token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SyntaxElement {
    Node(SyntaxNode),
    Token(SyntaxToken),
}

impl SyntaxElement {
    #[must_use]
    pub fn kind(&self) -> SyntaxKind {
        match self {
            Self::Node(node) => node.kind(),
            Self::Token(token) => token.kind(),
        }
    }

    #[must_use]
    pub fn span(&self) -> TextSpan {
        match self {
            Self::Node(node) => node.span(),
            Self::Token(token) => token.span(),
        }
    }

    #[must_use]
    pub fn full_span(&self) -> TextSpan {
        match self {
            Self::Node(node) => node.full_span(),
            Self::Token(token) => token.full_span(),
        }
    }

    #[must_use]
    pub fn into_node(self) -> Option<SyntaxNode> {
        match self {
            Self::Node(node) => Some(node),
            Self::Token(_) => None,
        }
    }

    #[must_use]
    pub fn into_token(self) -> Option<SyntaxToken> {
        match self {
            Self::Token(token) => Some(token),
            Self::Node(_) => None,
        }
    }
}

/// Iterator over a node's children, nodes and tokens alike.
#[derive(Debug)]
pub struct ChildElements {
    parent: SyntaxNode,
    index: usize,
    offset: u32,
}

impl Iterator for ChildElements {
    type Item = SyntaxElement;

    fn next(&mut self) -> Option<Self::Item> {
        let green = self.parent.green().slot(self.index)?;
        let position = self.offset;
        let slot = self.index as u32;
        self.offset += green.full_width();
        self.index += 1;

        Some(self.parent.element_at(green, position, slot))
    }
}

/// Iterator over a subtree's nodes, in source order.
#[derive(Debug)]
pub struct Descendants {
    stack: Vec<SyntaxNode>,
}

impl Iterator for Descendants {
    type Item = SyntaxNode;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        node.push_children_reversed(&mut self.stack);
        Some(node)
    }
}

/// Iterator over a node's children that are nodes.
#[derive(Debug)]
struct ChildNodes {
    parent: SyntaxNode,
    index: usize,
    offset: u32,
}

impl Iterator for ChildNodes {
    type Item = SyntaxNode;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let green = self.parent.green().slot(self.index)?;
            let position = self.offset;
            let slot = self.index as u32;
            self.offset += green.full_width();
            self.index += 1;
            if let GreenElement::Node(node) = green {
                return Some(SyntaxNode::child(
                    Arc::clone(node),
                    self.parent.clone(),
                    position,
                    slot,
                ));
            }
        }
    }
}

/// Iterator over a subtree's tokens, in source order.
#[derive(Debug)]
pub struct DescendantTokens {
    stack: Vec<SyntaxElement>,
}

impl Iterator for DescendantTokens {
    type Item = SyntaxToken;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.pop()? {
                SyntaxElement::Token(token) => return Some(token),
                SyntaxElement::Node(node) => {
                    let children: Vec<_> = node.children_with_tokens().collect();
                    self.stack.extend(children.into_iter().rev());
                }
            }
        }
    }
}

/// Iterator over a node's ancestors, closest first.
#[derive(Debug)]
pub struct Ancestors {
    current: Option<SyntaxNode>,
}

impl Iterator for Ancestors {
    type Item = SyntaxNode;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.current.take()?;
        self.current = node.parent().cloned();
        Some(node)
    }
}
