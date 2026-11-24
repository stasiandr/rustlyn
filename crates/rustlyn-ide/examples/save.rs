//! A save as the editor sees it: the project compiled, one file edited on
//! disk, compiled again — how long each took.
//!
//! ```text
//! cargo run --release -p rustlyn-ide --example save -- <root> <file> [--define "A;B"]
//! ```
//!
//! The file is given a space inside its first `return` and put back after.

use std::path::{Path, PathBuf};
use std::time::Instant;

use rustlyn_ide::Session;

fn sources(directory: &Path, found: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            sources(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "cs") {
            found.push(path);
        }
    }
}

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
    let [root, file] = arguments.as_slice() else {
        eprintln!("usage: save <root> <file> [--define A;B]");
        std::process::exit(2);
    };
    let root = PathBuf::from(root);
    let mut paths = Vec::new();
    sources(&root.join("Assets"), &mut paths);
    let paths: Vec<PathBuf> = paths
        .into_iter()
        .map(|path| path.strip_prefix(&root).unwrap_or(&path).to_path_buf())
        .collect();
    let session = Session::new(&root, None, symbols);
    let started = Instant::now();
    let compiled = session.compile(&paths);
    println!(
        "first: {} ms ({} files, reported {} ms)",
        started.elapsed().as_millis(),
        compiled.files,
        compiled.milliseconds
    );
    let full = root.join(file);
    let original = std::fs::read_to_string(&full).expect("the file");
    let edited = original.replacen("return ", "return  ", 1);
    for round in 0..3 {
        std::fs::write(&full, if round % 2 == 0 { &edited } else { &original }).expect("writable");
        let started = Instant::now();
        let compiled = session.compile(&paths);
        println!(
            "save {round}: {} ms (reported {} ms, unchanged {})",
            started.elapsed().as_millis(),
            compiled.milliseconds,
            compiled.unchanged
        );
    }
    std::fs::write(&full, &original).expect("writable");
}
