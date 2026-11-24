//! Prints the type of every expression in a file, for checking the binder.
//!
//! ```sh
//! cargo run --example typeof -- Program.cs
//! ```

use rustlyn_semantics::{Compilation, SemanticModel};
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn main() {
    let path = std::env::args().nth(1).expect("usage: typeof <file.cs>");
    let text = std::fs::read_to_string(&path).expect("the file should be readable");
    let compilation = Compilation::create(vec![parse(SourceText::new(path, text))]);
    let model = SemanticModel::new(&compilation, 1);

    for node in compilation.source_trees()[0].root().descendants() {
        if !node.kind().is_expression_node() {
            continue;
        }
        let ty = model.type_of(&node);
        println!(
            "{:?} {:?} -> {}",
            node.kind(),
            node.text(),
            ty.display(compilation.symbols())
        );
    }
}
