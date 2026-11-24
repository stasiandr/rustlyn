//! What a compilation costs made again with one file changed, as the hot
//! patch daemon and the IDE make one on every save — and whether the one made
//! without declaring everything again (`Compilation::with_tree_replaced`) is
//! the one a whole build makes.
//!
//! ```text
//! cargo run --release -p rustlyn-semantics --example redeclare -- \
//!     <references directory> <sources list> [--define "A;B"] [--pairs file] <path> <edited text file>...
//! ```
//!
//! Each pair is a file of the list and a text it is given; each is checked
//! on its own against the compilation of the list as it is.

use std::path::PathBuf;
use std::time::Instant;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::{ParseOptions, parse_with};
use rustlyn_text::SourceText;

fn main() {
    let mut arguments: Vec<String> = std::env::args().skip(1).collect();
    let symbols: Vec<String> = match arguments.iter().position(|argument| argument == "--define") {
        Some(at) => {
            let defines = arguments.remove(at + 1);
            arguments.remove(at);
            defines.split(';').map(str::to_string).collect()
        }
        None => Vec::new(),
    };
    // `--pairs <file>`: the pairs one per line each, for paths with spaces.
    if let Some(at) = arguments.iter().position(|argument| argument == "--pairs") {
        let file = arguments.remove(at + 1);
        arguments.remove(at);
        arguments.extend(
            std::fs::read_to_string(file)
                .expect("the pairs")
                .lines()
                .filter(|line| !line.is_empty())
                .map(str::to_string),
        );
    }
    let [references, list, pairs @ ..] = arguments.as_slice() else {
        eprintln!(
            "usage: redeclare <references directory> <sources list> [--define A;B] (<path> <edited text>)..."
        );
        std::process::exit(2);
    };
    let options = ParseOptions::with_symbols(symbols);
    let mut paths: Vec<PathBuf> = std::fs::read_dir(references)
        .expect("the references directory")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
        .collect();
    paths.sort();
    let bytes: Vec<Vec<u8>> = paths
        .iter()
        .filter_map(|path| std::fs::read(path).ok())
        .collect();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let sources: Vec<SourceText> = std::fs::read_to_string(list)
        .expect("the sources list")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter_map(|path| {
            std::fs::read_to_string(path)
                .ok()
                .map(|text| SourceText::new(path, text))
        })
        .collect();

    let started = Instant::now();
    let base = Compilation::parse_with_references(sources, &options, &images);
    println!(
        "whole: {} ms, {} trees",
        started.elapsed().as_millis(),
        base.trees().len()
    );
    let trees = base.trees();

    let (mut same, mut whole, mut wrong) = (0, 0, 0);
    let (mut fast_ms, mut slow_ms) = (0u128, 0u128);
    for pair in pairs.chunks(2) {
        let [path, edited] = pair else { break };
        let Some(index) = (0..trees.len())
            .find(|&at| trees.source(at).is_some_and(|source| source.name() == path))
        else {
            println!("{path}: not a source");
            continue;
        };
        let text = std::fs::read_to_string(edited).expect("the edited text");
        let tree = parse_with(SourceText::new(path.as_str(), text), &options);
        let started = Instant::now();
        let fast = base.with_tree_replaced(index, tree.clone());
        let fast_took = started.elapsed().as_millis();
        let started = Instant::now();
        let all: Vec<_> = (0..trees.len())
            .map(|at| {
                if at == index {
                    tree.clone()
                } else {
                    trees.get(at).expect("every tree").clone()
                }
            })
            .collect();
        let full = Compilation::create_with_references(all, &images);
        let slow_took = started.elapsed().as_millis();
        match fast {
            None => {
                whole += 1;
                println!("{path}: whole build ({slow_took} ms)");
            }
            Some(fast) => match fast.first_declaration_difference(&full) {
                None => {
                    same += 1;
                    fast_ms += fast_took;
                    slow_ms += slow_took;
                    println!("{path}: same, {fast_took} ms against {slow_took} ms");
                }
                Some(difference) => {
                    wrong += 1;
                    println!("{path}: DIFFERS: {difference}");
                }
            },
        }
    }
    if same > 0 {
        println!(
            "same {same}, whole build {whole}, differs {wrong}; {} ms against {} ms on average",
            fast_ms / same as u128,
            slow_ms / same as u128
        );
    } else {
        println!("same 0, whole build {whole}, differs {wrong}");
    }
}
