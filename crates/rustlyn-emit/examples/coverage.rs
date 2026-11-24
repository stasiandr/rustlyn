//! Tries to emit every method body in a project and counts what came out.
//!
//! The binder sweep answers "do we understand this". This answers the other
//! half: "can we say what the machine should do about it". Both are needed to
//! plan a road to compiling Roslyn, and neither says much about the other — a
//! file can bind without a single diagnostic and still have nothing this
//! backend knows how to write down.
//!
//! ```text
//! find roslyn/src/Compilers -name '*.cs' |
//!   cargo run --release -p rustlyn-emit --example coverage -- $FRAMEWORK --define NET
//! ```
//!
//! Bodies whose file did not bind cleanly are counted too: a binder that gave
//! up on an expression hands the emitter an error node, and what the emitter
//! says about that is noise. `--bound` leaves those bodies out of the count —
//! out of the count, not out of the compilation, which would be a different
//! program with different answers — and what is left says what the backend
//! alone is waiting on.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::{ParseOptions, parse_with};
use rustlyn_text::SourceText;

fn main() {
    let mut arguments = std::env::args().skip(1);
    let Some(framework) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: coverage <shared framework directory> [--define A;B] [--bound]");
        std::process::exit(2);
    };
    let arguments: Vec<String> = arguments.collect();
    let bound_only = arguments.iter().any(|argument| argument == "--bound");
    let mut symbols: Vec<String> = Vec::new();
    let mut expecting = false;
    for argument in &arguments {
        if expecting {
            symbols.extend(argument.split(';').map(str::to_string));
            expecting = false;
        } else if argument == "--define" {
            expecting = true;
        }
    }
    let options = ParseOptions::with_symbols(symbols);

    let mut references: Vec<_> = std::fs::read_dir(&framework)
        .unwrap_or_else(|error| panic!("{}: {error}", framework.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
        .collect();
    references.sort();
    let bytes: Vec<Vec<u8>> = references
        .iter()
        .filter_map(|path| std::fs::read(path).ok())
        .collect();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();

    let mut list = String::new();
    std::io::stdin()
        .read_to_string(&mut list)
        .expect("the file list should be readable");
    let paths: Vec<&str> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();

    let trees: Vec<_> = paths
        .iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(path).ok()?;
            Some(parse_with(SourceText::new(*path, &text), &options))
        })
        .collect();
    let parsed = trees.len();
    let compilation = Compilation::create_with_references(trees, &images);

    // Which files the binder had nothing to say about. Leaving the others out
    // of the *count* is what `--bound` means; leaving them out of the
    // compilation would be a different program, and the files that remained
    // would stop binding for want of what the others declared.
    let mut clean = vec![true; parsed];
    for entry in compilation.semantic_diagnostics() {
        if let Some(slot) = clean.get_mut(entry.tree) {
            *slot = false;
        }
    }

    let started = std::time::Instant::now();
    let coverage = match rustlyn_emit::coverage(&compilation, "Sweep") {
        Ok(coverage) => coverage,
        Err(error) => {
            println!("{parsed} files; could not build the plan: {error}");
            return;
        }
    };
    let elapsed = started.elapsed();

    let counted: Vec<&rustlyn_emit::CoverageEntry> = coverage
        .bodies
        .iter()
        .filter(|entry| {
            !bound_only
                || entry
                    .tree
                    .is_some_and(|tree| clean.get(tree).copied().unwrap_or(false))
        })
        .collect();
    let attempted = counted.len();
    let emitted = counted
        .iter()
        .filter(|entry| entry.failure.is_none())
        .count();
    let files = if bound_only {
        clean.iter().filter(|clean| **clean).count()
    } else {
        parsed
    };
    println!("{files} files, {attempted} method bodies, emitted in {elapsed:.2?}");
    println!(
        "{emitted} bodies emitted ({:.1}%)",
        emitted as f64 * 100.0 / attempted.max(1) as f64
    );

    // The same reason many times over is one gap, not many. Where a message
    // names a construct it prints as it stands; where it names a symbol the
    // name is the noise, so only the first few words are counted.
    let mut by_reason: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for entry in &counted {
        let Some(reason) = &entry.failure else {
            continue;
        };
        let key: String = reason
            .split_whitespace()
            .take(8)
            .collect::<Vec<_>>()
            .join(" ");
        let bucket = by_reason.entry(key).or_default();
        bucket.0 += 1;
        if bucket.1.is_empty() {
            bucket.1 = format!("{}: {reason}", entry.method);
        }
    }
    // Every body that did not come out, with why, for reading a whole bucket
    // rather than the one example above.
    if let Some(at) = arguments.iter().position(|argument| argument == "--dump")
        && let Some(path) = arguments.get(at + 1)
    {
        let lines: Vec<String> = counted
            .iter()
            .filter_map(|entry| {
                let reason = entry.failure.as_ref()?;
                let file = entry
                    .tree
                    .and_then(|tree| paths.get(tree))
                    .copied()
                    .unwrap_or("?");
                Some(format!("{file}\t{}\t{reason}", entry.method))
            })
            .collect();
        std::fs::write(path, lines.join("\n")).expect("the dump should be writable");
    }

    let mut ranked: Vec<_> = by_reason.into_iter().collect();
    ranked.sort_by_key(|b| std::cmp::Reverse(b.1.0));
    println!("most common failures:");
    for (reason, (count, example)) in ranked.iter().take(25) {
        println!("{count:>8}  {reason}");
        println!("          {example}");
    }
}
