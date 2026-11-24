//! Parses a file (or stdin) and prints the tree, for looking at what the
//! parser did.
//!
//! ```sh
//! cargo run --example dump -- Program.cs
//! ```

use std::io::Read as _;

use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn main() {
    let mut args = std::env::args().skip(1);
    let (name, text) = match args.next() {
        Some(path) => {
            let text = std::fs::read_to_string(&path).expect("the file should be readable");
            (path, text)
        }
        None => {
            let mut text = String::new();
            std::io::stdin()
                .read_to_string(&mut text)
                .expect("stdin should be readable");
            ("<stdin>".to_string(), text)
        }
    };

    let source = SourceText::new(name, text);
    let tree = parse(source.clone());

    print!("{}", tree.root().debug_tree());

    if tree.text() != source.text() {
        println!("\n!! the tree does not reproduce its source");
    }
    for diagnostic in tree.diagnostics() {
        println!("{}", diagnostic.display_with(&source));
    }
}
