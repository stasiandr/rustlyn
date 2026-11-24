//! Prints the node shape of each argument, the way the parser tests spell it.
//!
//! ```sh
//! cargo run --example shapes -- 'expr:a + b' 'stmt:if (a) b();'
//! ```

use rustlyn_syntax::{SyntaxKind, SyntaxNode, parse};
use rustlyn_text::SourceText;

fn shape_of(node: &SyntaxNode) -> String {
    let children: Vec<String> = node.children().map(|child| shape_of(&child)).collect();
    if children.is_empty() {
        format!("{:?}", node.kind())
    } else {
        format!("({:?} {})", node.kind(), children.join(" "))
    }
}

fn main() {
    for argument in std::env::args().skip(1) {
        let (mode, text) = argument.split_once(':').unwrap_or(("expr", &argument));
        let (source, wanted) = match mode {
            "stmt" => (
                format!("class C {{ void M() {{ {text} }} }}"),
                SyntaxKind::Block,
            ),
            "member" => (
                format!("class C {{ {text} }}"),
                SyntaxKind::ClassDeclaration,
            ),
            _ => (
                format!("class C {{ void M() {{ Use({text}); }} }}"),
                SyntaxKind::Argument,
            ),
        };
        let source = SourceText::new("<shapes>", source);
        let tree = parse(source.clone());
        let found = tree
            .root()
            .descendants()
            .find(|node| node.kind() == wanted)
            .and_then(|node| node.children().next());
        match found {
            Some(node) => println!("{text}\n  {}", shape_of(&node)),
            None => println!("{text}\n  <nothing>"),
        }
        for diagnostic in tree.diagnostics() {
            println!("  !! {}", diagnostic.display_with(&source));
        }
    }
}
