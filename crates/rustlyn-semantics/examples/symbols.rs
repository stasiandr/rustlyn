//! Prints the declaration table of a file.
//!
//! ```sh
//! cargo run --example symbols -- Program.cs
//! ```

use rustlyn_semantics::{Compilation, SymbolId, SymbolKind};
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn main() {
    let path = std::env::args().nth(1).expect("usage: symbols <file.cs>");
    let text = std::fs::read_to_string(&path).expect("the file should be readable");
    let compilation = Compilation::create(vec![parse(SourceText::new(path, text))]);

    print(&compilation, compilation.global_namespace(), 0);

    for entry in compilation.source_diagnostics() {
        println!("{}", compilation.render(entry));
    }
}

fn print(compilation: &Compilation, id: SymbolId, depth: usize) {
    let symbols = compilation.symbols();
    let symbol = symbols.get(id);

    // The synthesised core library would bury the file's own declarations.
    let from_corlib = symbol
        .locations
        .first()
        .is_some_and(|location| location.tree == 0);
    if from_corlib && symbol.kind != SymbolKind::Namespace {
        return;
    }

    if depth > 0 {
        let indent = "  ".repeat(depth - 1);
        let details = [
            symbol.accessibility.to_string(),
            format!("{:?}", symbol.modifiers),
        ]
        .into_iter()
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
        println!(
            "{indent}{:?} {} {details}",
            symbol.kind,
            symbols.qualified_name(id),
        );
    }

    for member in &symbol.members {
        print(compilation, *member, depth + 1);
    }
}
