//! Binds a whole project's worth of C# against the real framework and counts
//! what came back.
//!
//! The parse-fidelity sweep answers "can we read this". This answers the next
//! question: "do we understand it". It is the only honest way to plan the road
//! to compiling Roslyn — a list of language features ranked by guesswork is
//! worth less than a histogram of what actually fails.
//!
//! ```text
//! find roslyn/src/Compilers/CSharp/Portable -name '*.cs' |
//!   cargo run --release -p rustlyn-semantics --example bind -- $FRAMEWORK
//! ```
//!
//! With `--verbose`, the first few of each kind are printed with their file
//! and position, which is where a histogram stops being enough.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::{ParseOptions, parse_with};
use rustlyn_text::SourceText;

fn main() {
    let mut arguments = std::env::args().skip(1);
    let Some(framework) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: bind <shared framework directory> [--define A;B] [--verbose]");
        std::process::exit(2);
    };
    // The same `/define:` the real build passes: without them a file takes
    // the branch nobody compiles, and what comes back says more about the
    // preprocessor than about the binder.
    let arguments: Vec<String> = arguments.collect();
    let verbose = arguments.iter().any(|argument| argument == "--verbose");
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

    let started = std::time::Instant::now();
    let trees: Vec<_> = paths
        .iter()
        .filter_map(|path| {
            let text = read_source(path)?;
            Some(parse_with(SourceText::new(*path, &text), &options))
        })
        .collect();
    let parsed = trees.len();
    let parse_time = started.elapsed();

    let started = std::time::Instant::now();
    let compilation = Compilation::create_with_references(trees, &images);
    let declare_time = started.elapsed();

    // `--only <substring>`: bind the bodies of the matching files alone
    // and stop, for profiling one file's binding.
    if let Some(at) = arguments.iter().position(|argument| argument == "--only")
        && let Some(needle) = arguments.get(at + 1)
    {
        // Repeated, so that a profiler sees the binding rather than the
        // loading of the framework around it.
        let repeat: u32 = std::env::var("RUSTLYN_BIND_REPEAT")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(1);
        let started = std::time::Instant::now();
        for _ in 0..repeat {
            for (tree, path) in paths.iter().enumerate() {
                if path.contains(needle.as_str()) {
                    let _ = rustlyn_semantics::SemanticModel::new(&compilation, tree)
                        .body_diagnostics();
                }
            }
        }
        println!("bodies of {needle}: {:.2?}", started.elapsed() / repeat);
        return;
    }
    // `--times`: the slowest files to bind, for finding what is slow.
    if arguments.iter().any(|argument| argument == "--times") {
        let mut times: Vec<(std::time::Duration, &str)> = Vec::new();
        for (tree, path) in paths.iter().enumerate() {
            let started = std::time::Instant::now();
            let _ = rustlyn_semantics::SemanticModel::new(&compilation, tree).body_diagnostics();
            times.push((started.elapsed(), path));
        }
        times.sort_by_key(|b| std::cmp::Reverse(b.0));
        let total: std::time::Duration = times.iter().map(|(time, _)| *time).sum();
        println!("bodies: {total:.2?} in total");
        for (time, path) in times.iter().take(15) {
            println!("{time:>10.2?}  {path}");
        }
    }

    let started = std::time::Instant::now();
    let diagnostics = compilation.semantic_diagnostics();
    let bind_time = started.elapsed();

    // Which files got through untouched is the number that has to reach a
    // hundred percent; the histogram is what stands in the way.
    let focus = arguments
        .iter()
        .position(|argument| argument == "--focus")
        .and_then(|at| arguments.get(at + 1))
        .cloned();
    let mut by_code: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
    let mut files: BTreeMap<usize, usize> = BTreeMap::new();
    for entry in &diagnostics {
        let code = format!("{:?}", entry.diagnostic.code());
        let bucket = by_code.entry(code).or_default();
        bucket.0 += 1;
        let interesting = focus.as_ref().is_none_or(|focus| {
            paths
                .get(entry.tree)
                .is_some_and(|path| path.contains(focus))
                || entry.diagnostic.message().contains(focus)
        });
        // An unfocused run wants a sample; a focused one was asked about
        // something in particular and wants all of it.
        let wanted = if focus.is_some() { 40 } else { 4 };
        if interesting && bucket.1.len() < wanted {
            bucket.1.push(compilation.render(entry));
        }
        *files.entry(entry.tree).or_default() += 1;
    }

    println!(
        "{parsed} files, {} types, {} symbols",
        compilation.all_types().count(),
        compilation.symbols().len()
    );
    println!("parse {parse_time:.2?}, declarations {declare_time:.2?}, binding {bind_time:.2?}");
    println!(
        "{} files without a single diagnostic ({:.1}%)",
        parsed - files.len(),
        (parsed - files.len()) as f64 * 100.0 / parsed.max(1) as f64
    );
    println!("{} diagnostics in total:", diagnostics.len());

    // Every failing file, for diffing two runs against each other: a change
    // that lowers the total while breaking four files is two changes, and the
    // top ten are not enough to see the second one.
    if let Some(at) = arguments.iter().position(|argument| argument == "--files")
        && let Some(path) = arguments.get(at + 1)
    {
        let mut lines: Vec<String> = files
            .iter()
            .map(|(tree, count)| {
                format!("{count:>6}  {}", paths.get(*tree).copied().unwrap_or("?"))
            })
            .collect();
        lines.sort();
        std::fs::write(path, lines.join("\n")).expect("the list should be writable");
    }

    // Every diagnostic there is, for reading a whole bucket rather than the
    // sample above: a fix for the top message is planned against everything
    // that message covers, not against its first four instances.
    if let Some(at) = arguments.iter().position(|argument| argument == "--dump")
        && let Some(path) = arguments.get(at + 1)
    {
        let lines: Vec<String> = diagnostics
            .iter()
            .map(|entry| {
                format!(
                    "{:?}\t{}",
                    entry.diagnostic.code(),
                    compilation.render(entry)
                )
            })
            .collect();
        std::fs::write(path, lines.join("\n")).expect("the dump should be writable");
    }

    // Which files are worst says whether a bucket is one pathological file or
    // a language feature missing everywhere.
    let mut worst: Vec<(usize, usize)> = files.iter().map(|(a, b)| (*b, *a)).collect();
    worst.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));
    println!("worst files:");
    for (count, tree) in worst.iter().take(10) {
        println!("{count:>8}  {}", paths.get(*tree).copied().unwrap_or("?"));
    }

    // The same message many times over is one gap, not many.
    let mut by_message: BTreeMap<String, usize> = BTreeMap::new();
    for entry in &diagnostics {
        *by_message
            .entry(entry.diagnostic.message().to_string())
            .or_default() += 1;
    }
    let mut messages: Vec<_> = by_message.into_iter().collect();
    messages.sort_by_key(|b| std::cmp::Reverse(b.1));
    println!("most common:");
    for (message, count) in messages.iter().take(if verbose { 40 } else { 15 }) {
        println!("{count:>8}  {message}");
    }

    let mut ranked: Vec<_> = by_code.into_iter().collect();
    ranked.sort_by_key(|b| std::cmp::Reverse(b.1.0));
    for (code, (count, examples)) in &ranked {
        println!("{count:>8}  {code}");
        if verbose {
            for example in examples {
                println!("          {example}");
            }
        }
    }
}

/// A source file as text: UTF-8, or — as csc falls back to when the bytes
/// are not UTF-8 — each byte as the Latin-1 character it is. Skipping such a
/// file silently loses a type the rest of the code depends on.
fn read_source(path: &str) -> Option<String> {
    let bytes = std::fs::read(path).ok()?;
    Some(String::from_utf8(bytes).unwrap_or_else(|error| {
        error
            .into_bytes()
            .iter()
            .map(|&byte| byte as char)
            .collect()
    }))
}
