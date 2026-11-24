//! Reads file paths from stdin, parses each one, and reports whether the tree
//! still prints back as the file.
//!
//! ```sh
//! find . -name '*.cs' | cargo run --release --example fidelity
//! ```

use std::collections::HashMap;
use std::io::BufRead as _;

use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn main() {
    let mut files = 0u32;
    let mut broken = 0u32;
    let mut clean = 0u32;
    let mut diagnostics = 0u64;
    let mut by_code: HashMap<String, u64> = HashMap::new();
    let mut worst: Vec<(usize, String)> = Vec::new();

    for line in std::io::stdin().lock().lines() {
        let path = line.expect("stdin should be readable");
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        files += 1;

        let source = SourceText::new(path.clone(), text.clone());
        let tree = parse(source.clone());
        if tree.text() != text {
            broken += 1;
            println!("round trip broken: {path}");
        }
        if tree.diagnostics().is_empty() {
            clean += 1;
        }
        diagnostics += tree.diagnostics().len() as u64;
        if let Some(first) = tree.diagnostics().first() {
            *by_code.entry(first.code().to_string()).or_default() += 1;
            let filter = std::env::var("SHOW").unwrap_or_default();
            if filter == "ALL" || filter == first.code().to_string() {
                // The line the first complaint points at, trimmed, so the
                // causes can be grouped by eye.
                let line = source.line_position(first.span().start()).line;
                let text = source.line_text(line).unwrap_or("").trim();
                println!("{}\t{}\t{}", first.code(), path, text);
            }
        }
        worst.push((tree.diagnostics().len(), path));
    }

    println!(
        "{files} files, {broken} round trips broken, {clean} parsed clean, {diagnostics} diagnostics"
    );

    let mut codes: Vec<_> = by_code.into_iter().collect();
    codes.sort_by_key(|(_, count)| std::cmp::Reverse(*count));
    println!("first diagnostic in each file, by code:");
    for (code, count) in codes.iter().take(10) {
        println!("  {code}: {count}");
    }

    worst.sort_by_key(|(count, _)| std::cmp::Reverse(*count));
    println!("noisiest files:");
    for (count, path) in worst.iter().take(5) {
        println!("  {count}: {path}");
    }
}
