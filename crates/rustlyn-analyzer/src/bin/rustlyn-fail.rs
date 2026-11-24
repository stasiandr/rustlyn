//! `rustlyn-fail`: how a method can fail, when, and whether it can happen.
//!
//! ```text
//! rustlyn-fail ROOT File.cs:line[:column]   the member on the line
//! rustlyn-fail ROOT File.cs                 every method of the file that can fail
//!              [--all]                      and those that cannot
//!              [--no-cache]                 do not keep the compilation between runs
//! ```
//!
//! Lines and columns are one-based; without a column, the first declaration
//! on the line. The project is all its `.cs` files, compiled by Rustlyn
//! (the cache is under `$RUSTLYN_FAIL_CACHE` or the platform's cache folder).

use std::path::{Path, PathBuf};

use rustlyn_analyzer::blast::{project, setup};
use rustlyn_analyzer::fail::{English, Lines, Wording, offsets, report, split_target};

const USAGE: &str = "rustlyn-fail ROOT File.cs[:line[:column]] [--all] [--no-cache]

How a C# member can fail (throw, division by zero, null, index, a library
call), where, through which calls, under which condition, and whether that
can happen given the values of its inputs across the project.";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{USAGE}");
        return;
    }
    let all = args.iter().any(|a| a == "--all");
    let no_cache = args.iter().any(|a| a == "--no-cache");
    let positional: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    let [root, target] = positional.as_slice() else {
        eprintln!("{USAGE}");
        std::process::exit(2);
    };
    let root = setup::canonical_root(root);
    let (file, line, column) = split_target(target);
    let file = if Path::new(&file).is_absolute() {
        PathBuf::from(&file)
    } else {
        Path::new(&root).join(&file)
    };
    let file = std::fs::canonicalize(&file).unwrap_or(file);
    let Ok(text) = std::fs::read_to_string(&file) else {
        eprintln!("rustlyn-fail: cannot read {}", file.display());
        std::process::exit(2);
    };
    let cache = if no_cache {
        None
    } else {
        setup::cache_dir("rustlyn-fail", &root)
    };
    let session = match project::compiled(&root, cache) {
        Ok(session) => session,
        Err(why) => {
            eprintln!("rustlyn-fail: {why}");
            std::process::exit(1);
        }
    };
    let _ = session.open(&file);
    let declarations: Vec<_> = match (session.outline(&file), session.document(&file)) {
        (Ok(outline), Some(document)) => outline
            .declarations
            .iter()
            .map(|d| (d.kind, document.utf16().span(d.name_span).0))
            .collect(),
        _ => Vec::new(),
    };
    let wording = English;
    let mut lines = Lines::default();
    let mut shown = 0;
    for offset in offsets(&text, line, column, &declarations) {
        match rustlyn_analyzer::deep::run(|| session.failability(&file, offset)) {
            Ok(found) => {
                if found.failures.is_empty() && !all && line.is_none() {
                    continue;
                }
                if shown > 0 {
                    println!();
                }
                print!("{}", report(&found, &root, &mut lines, &wording));
                shown += 1;
            }
            Err(refusal) => eprintln!("rustlyn-fail: no answer: {refusal}"),
        }
    }
    if shown == 0 && line.is_none() {
        println!("{}", wording.nothing_in_file());
    }
}
