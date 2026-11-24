//! Reports the types a file uses that cannot be found.
//!
//! ```sh
//! cargo run --example typecheck -- Program.cs
//! ```

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn main() {
    let path = std::env::args().nth(1).expect("usage: typecheck <file.cs>");
    let text = std::fs::read_to_string(&path).expect("the file should be readable");
    let compilation = Compilation::create(vec![parse(SourceText::new(path, text))]);

    let mut reported = 0;
    for entry in compilation.source_diagnostics() {
        println!("{}", compilation.render(entry));
        reported += 1;
    }
    for entry in &compilation.semantic_diagnostics() {
        println!("{}", compilation.render(entry));
        reported += 1;
    }
    println!("{reported} diagnostics");
}
