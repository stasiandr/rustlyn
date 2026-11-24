//! Shows where a tree stops matching its source, for chasing a lost token.
//!
//! ```sh
//! cargo run --example diverge -- Program.cs
//! ```

use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn main() {
    let path = std::env::args().nth(1).expect("usage: diverge <file.cs>");
    let text = std::fs::read_to_string(&path).expect("the file should be readable");
    let source = SourceText::new(path, text.clone());
    let tree = parse(source.clone());
    let rebuilt = tree.text();

    if rebuilt == text {
        println!("the tree reproduces its source");
        return;
    }

    let at = text
        .bytes()
        .zip(rebuilt.bytes())
        .position(|(a, b)| a != b)
        .unwrap_or(text.len().min(rebuilt.len()));
    let position = source.line_position(at as u32);
    println!(
        "diverges at {}:{} (offset {at})",
        position.line + 1,
        position.character + 1
    );
    println!(
        "source:  {:?}",
        &text[at.saturating_sub(40)..(at + 60).min(text.len())]
    );
    println!(
        "tree:    {:?}",
        &rebuilt[at.saturating_sub(40)..(at + 60).min(rebuilt.len())]
    );
}
