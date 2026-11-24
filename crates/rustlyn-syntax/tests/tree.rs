//! Green and red tree behaviour, on a tree assembled by hand.
//!
//! The parser is what will normally build these, but checking the two layers on
//! their own keeps a tree bug from looking like a parser bug.

use std::sync::Arc;

use rustlyn_syntax::green::{GreenCache, GreenElement, GreenNode, GreenToken, green_token};
use rustlyn_syntax::{SyntaxElement, SyntaxKind, SyntaxTree, tokenize};
use rustlyn_text::{SourceText, TextSpan};

const SOURCE: &str = "class C /* hi */ { }\n";

/// Builds the tree the parser would build for [`SOURCE`].
fn sample_tree() -> SyntaxTree {
    let source = SourceText::new("Sample.cs", SOURCE);
    let lexed = tokenize(&source);
    let mut cache = GreenCache::new();
    let tokens: Vec<GreenElement> = lexed
        .tokens
        .iter()
        .map(|token| GreenElement::Token(green_token(token, &source, &mut cache)))
        .collect();

    let (declaration, end_of_file) = tokens.split_at(4);
    let declaration = GreenNode::new(SyntaxKind::ClassDeclaration, declaration.to_vec());
    let root = GreenNode::new(
        SyntaxKind::CompilationUnit,
        vec![declaration.into(), end_of_file[0].clone()],
    );

    SyntaxTree::new(source, root, Vec::new())
}

#[test]
fn the_tree_reproduces_its_source() {
    let tree = sample_tree();
    assert_eq!(tree.text(), SOURCE);
    assert_eq!(tree.root().full_text(), SOURCE);
}

#[test]
fn spans_exclude_edge_trivia_and_full_spans_include_it() {
    let tree = sample_tree();
    let root = tree.root();
    assert_eq!(
        root.full_span(),
        TextSpan::from_bounds(0, SOURCE.len() as u32)
    );
    // The trailing newline is trivia, so it is outside the node's own span.
    assert_eq!(root.span(), TextSpan::from_bounds(0, 20));

    let class = root.child_of_kind(SyntaxKind::ClassDeclaration).unwrap();
    assert_eq!(class.text(), "class C /* hi */ { }");

    let keyword = class.child_token_of_kind(SyntaxKind::ClassKeyword).unwrap();
    assert_eq!(keyword.span(), TextSpan::from_bounds(0, 5));
    // The space after the keyword is its trailing trivia.
    assert_eq!(keyword.full_span(), TextSpan::from_bounds(0, 6));
    assert_eq!(keyword.text(), "class");
    assert_eq!(keyword.full_text(), "class ");
}

#[test]
fn children_are_positioned_end_to_end() {
    let tree = sample_tree();
    let mut position = 0;
    for element in tree.root().descendant_tokens() {
        assert_eq!(element.full_span().start(), position);
        position = element.full_span().end();
    }
    assert_eq!(position, SOURCE.len() as u32);
}

#[test]
fn navigation_goes_both_ways() {
    let tree = sample_tree();
    let root = tree.root();
    let class = root.child_of_kind(SyntaxKind::ClassDeclaration).unwrap();
    assert_eq!(class.parent(), Some(&root));
    assert!(root.parent().is_none());
    assert_eq!(class.ancestors().collect::<Vec<_>>(), vec![root.clone()]);

    let kinds: Vec<_> = root.descendants().map(|node| node.kind()).collect();
    assert_eq!(
        kinds,
        vec![SyntaxKind::CompilationUnit, SyntaxKind::ClassDeclaration]
    );
}

#[test]
fn find_token_walks_down_to_a_leaf() {
    let tree = sample_tree();
    let root = tree.root();
    assert_eq!(root.find_token(0).unwrap().kind(), SyntaxKind::ClassKeyword);
    assert_eq!(
        root.find_token(6).unwrap().kind(),
        SyntaxKind::IdentifierToken
    );
    // Position 10 is inside the comment. Nothing separates it from `C` by a
    // line break, so it is that token's trailing trivia and belongs to it.
    assert_eq!(
        root.find_token(10).unwrap().kind(),
        SyntaxKind::IdentifierToken
    );
    assert_eq!(
        root.find_token(17).unwrap().kind(),
        SyntaxKind::OpenBraceToken
    );
    assert_eq!(
        root.find_token(19).unwrap().kind(),
        SyntaxKind::CloseBraceToken
    );
    assert!(root.find_token(SOURCE.len() as u32).is_none());
}

#[test]
fn find_node_returns_the_innermost_cover() {
    let tree = sample_tree();
    let root = tree.root();
    let found = root.find_node(TextSpan::from_bounds(6, 7)).unwrap();
    assert_eq!(found.kind(), SyntaxKind::ClassDeclaration);
    // The closing brace carries the trailing newline, so the declaration's
    // full span reaches the end of the file and still wins over the root.
    let found = root.find_node(TextSpan::from_bounds(0, 21)).unwrap();
    assert_eq!(found.kind(), SyntaxKind::ClassDeclaration);
}

#[test]
fn trivia_is_positioned_and_classified() {
    let tree = sample_tree();
    let name = tree.root().find_token(6).expect("`C` sits at 6");
    assert_eq!(name.kind(), SyntaxKind::IdentifierToken);
    let trailing: Vec<_> = name
        .trailing_trivia()
        .iter()
        .map(|t| (t.kind(), t.text().to_string(), t.span()))
        .collect();
    assert_eq!(
        trailing,
        vec![
            (
                SyntaxKind::WhitespaceTrivia,
                " ".to_string(),
                TextSpan::from_bounds(7, 8)
            ),
            (
                SyntaxKind::MultiLineCommentTrivia,
                "/* hi */".to_string(),
                TextSpan::from_bounds(8, 16)
            ),
            (
                SyntaxKind::WhitespaceTrivia,
                " ".to_string(),
                TextSpan::from_bounds(16, 17)
            ),
        ]
    );
    // The brace itself therefore starts clean.
    let brace = tree.root().find_token(17).unwrap();
    assert!(brace.leading_trivia().is_empty());
}

#[test]
fn identical_trivia_is_interned() {
    let source = SourceText::from_string("a b c d");
    let lexed = tokenize(&source);
    let mut cache = GreenCache::new();
    let tokens: Vec<_> = lexed
        .tokens
        .iter()
        .map(|token| green_token(token, &source, &mut cache))
        .collect();

    let first = &tokens[0].trailing_trivia()[0];
    let second = &tokens[1].trailing_trivia()[0];
    assert!(Arc::ptr_eq(first, second), "the single spaces should share");
    let (hits, misses) = cache.stats();
    assert_eq!((hits, misses), (2, 1));
}

#[test]
fn missing_tokens_have_no_width() {
    let missing = Arc::new(GreenToken::missing(SyntaxKind::SemicolonToken));
    assert!(missing.is_missing());
    assert_eq!(missing.full_width(), 0);

    let root = GreenNode::new(SyntaxKind::CompilationUnit, vec![missing.into()]);
    let tree = SyntaxTree::new(SourceText::from_string(""), root, Vec::new());
    assert!(tree.root().is_missing());
    assert_eq!(tree.text(), "");
}

#[test]
fn the_debug_dump_shows_kinds_spans_and_text() {
    let tree = sample_tree();
    assert_eq!(
        tree.root().debug_tree(),
        "\
CompilationUnit [0..20)
  ClassDeclaration [0..20)
    ClassKeyword \"class\" [0..5)
    IdentifierToken \"C\" [6..7)
    OpenBraceToken \"{\" [17..18)
    CloseBraceToken \"}\" [19..20)
  EndOfFileToken \"\" [21..21)
"
    );
}

#[test]
fn elements_expose_either_half() {
    let tree = sample_tree();
    let children: Vec<SyntaxElement> = tree.root().children_with_tokens().collect();
    assert_eq!(children.len(), 2);
    assert!(children[0].clone().into_node().is_some());
    assert!(children[1].clone().into_token().is_some());
}
