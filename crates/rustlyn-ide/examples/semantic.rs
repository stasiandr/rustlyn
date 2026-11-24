//! Compiles a project the way an editor would and asks it what an editor asks,
//! timing each question.
//!
//! ```text
//! find src -name '*.cs' | cargo run --release -p rustlyn-ide --example semantic -- <root>
//! ```
//!
//! Every identifier in a sample of files is followed to its declaration; a
//! sample of them is searched for across the project; and every `.` in the
//! sample is completed. What comes back is how often each answered and how
//! long the slowest took, which is what decides whether an editor can ask it
//! on a keystroke.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use rustlyn_ide::project::{Project, compiled_files};
use rustlyn_ide::semantic::Semantic;

fn main() {
    let root = PathBuf::from(std::env::args().nth(1).expect("usage: semantic <root>"));
    let mut list = String::new();
    std::io::stdin()
        .read_to_string(&mut list)
        .expect("a file list");
    let paths: Vec<PathBuf> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(|line| {
            let path = PathBuf::from(line);
            if path.is_absolute() {
                path
            } else {
                root.join(path)
            }
        })
        .collect();

    let started = Instant::now();
    let project = Project::discover(&root, &[]);
    println!(
        "project: {:?}, {} projects, {} references, {} symbols in {:.2?}",
        project.kind,
        project.projects,
        project.references.len(),
        project.symbols.len(),
        started.elapsed()
    );
    let files = compiled_files(&project, &paths);
    let started = Instant::now();
    let sources: Vec<(PathBuf, String)> = files
        .iter()
        .filter_map(|path| Some((path.clone(), std::fs::read_to_string(path).ok()?)))
        .collect();
    let references: Vec<(PathBuf, Arc<[u8]>)> = project
        .references
        .iter()
        .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(path).ok()?))))
        .collect();
    let read = started.elapsed();
    let started = Instant::now();
    let semantic = Semantic::build(project, sources.clone(), &references, None);
    println!(
        "{} files read in {read:.2?}, compiled in {:.2?}",
        semantic.files(),
        started.elapsed()
    );
    let resident = std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status
                .lines()
                .find(|line| line.starts_with("VmHWM:"))
                .map(str::to_string)
        })
        .unwrap_or_default();
    println!(
        "peak memory after compiling: {}",
        resident.trim_start_matches("VmHWM:").trim()
    );
    let started = Instant::now();
    let bytes = semantic.write();
    let wrote = started.elapsed();
    let started = Instant::now();
    let read = Semantic::read(&bytes).expect("the snapshot reads back");
    let reading = started.elapsed();
    let first = files.iter().step_by(97).take(20).collect::<Vec<_>>();
    let started = Instant::now();
    let mut found = 0;
    for path in &first {
        if let Some(text) = read.text(path)
            && let Some(at) = text.find("public ")
            && read.definition(path, at as u32 + 12, None).is_some()
        {
            found += 1;
        }
    }
    println!(
        "snapshot: {:.1} MB, written in {wrote:.2?}, read in {reading:.2?}; 20 first questions after reading: {:.2?} ({found} answered)",
        bytes.len() as f64 / 1e6,
        started.elapsed()
    );
    // What an editor shows for a file it opens: every diagnostic of it.
    let started = Instant::now();
    let (mut reported, mut worst, mut worst_file) =
        (0usize, std::time::Duration::ZERO, PathBuf::new());
    for path in &files {
        let one = Instant::now();
        reported += semantic
            .diagnostics(path, None)
            .map_or(0, |found| found.len());
        if one.elapsed() > worst {
            worst = one.elapsed();
            worst_file = path.clone();
        }
    }
    println!(
        "diagnostics of every file: {reported} in {:.2?}, {:.2?} a file, worst {worst:.2?} ({})",
        started.elapsed(),
        started.elapsed() / files.len().max(1) as u32,
        worst_file
            .file_name()
            .map(|name| name.to_string_lossy())
            .unwrap_or_default()
    );
    let started = Instant::now();
    let unchanged = read.unchanged(read.project(), &sources);
    println!("unchanged check: {unchanged} in {:.2?}", started.elapsed());
    drop(read);
    let started = Instant::now();
    let again = Semantic::build(
        semantic.project().clone(),
        sources,
        &references,
        Some(&semantic),
    );
    println!(
        "rebuilt with every tree reused in {:.2?}",
        started.elapsed()
    );
    drop(again);

    // Every tenth file, every identifier.
    let sample: Vec<&Path> = files.iter().step_by(10).map(PathBuf::as_path).collect();
    let mut asked = 0;
    let mut answered = 0;
    let mut slowest = Duration::ZERO;
    let mut total = Duration::ZERO;
    let mut targets = Vec::new();
    let mut misses = Vec::new();
    let mut not_references = 0;
    let mut categories: std::collections::HashMap<String, (usize, Vec<String>)> =
        std::collections::HashMap::new();
    for path in &sample {
        let Some(text) = semantic.text(path) else {
            continue;
        };
        let Some(mut view) = semantic
            .tree_index(path)
            .and_then(|tree| semantic.view(tree))
        else {
            continue;
        };
        // Names only: a keyword is not a question anyone asks.
        let offsets: Vec<u32> = identifier_starts(text)
            .into_iter()
            .filter(|&offset| {
                view.name_token_at(offset).is_some_and(|token| {
                    token.kind() == rustlyn_syntax::SyntaxKind::IdentifierToken
                        && token.span().start() == offset
                })
            })
            .collect();
        for offset in offsets.into_iter().step_by(7) {
            asked += 1;
            let started = Instant::now();
            let found = semantic.definition(path, offset, None);
            let took = started.elapsed();
            total += took;
            slowest = slowest.max(took);
            let hit = found.as_ref().is_some_and(|(_, found)| !found.is_empty());
            // Tokens that look like names and are not references to anything:
            // a discard, `assembly:` in front of an attribute, the `nameof`
            // operator itself, a tuple element's name where it is declared.
            let not_a_reference = view.name_token_at(offset).is_some_and(|token| {
                use rustlyn_syntax::SyntaxKind as K;
                let parent = token.parent().kind();
                token.value_text() == "_"
                    || matches!(
                        parent,
                        K::AttributeTargetSpecifier
                            | K::TupleElement
                            | K::DiscardDesignation
                            | K::DiscardPattern
                    )
                    || (token.value_text() == "nameof"
                        && token
                            .parent()
                            .parent()
                            .is_some_and(|p| p.kind() == K::InvocationExpression))
            });
            if not_a_reference {
                not_references += 1;
            }
            if !hit && let Some(token) = view.name_token_at(offset) {
                let category = if view.resolve(&token).is_some() {
                    "resolved, nowhere to go".to_string()
                } else {
                    let kinds: Vec<String> = std::iter::once(token.parent().clone())
                        .chain(token.parent().ancestors())
                        .take(3)
                        .map(|node| format!("{:?}", node.kind()))
                        .collect();
                    kinds.join(" < ")
                };
                let start = text[..offset as usize].rfind('\n').map_or(0, |at| at + 1);
                let end = text[offset as usize..]
                    .find('\n')
                    .map_or(text.len(), |at| offset as usize + at);
                let line = text[..offset as usize].matches('\n').count() + 1;
                let sample = format!(
                    "{}:{line}: {}‸{}",
                    path.display(),
                    text[start..offset as usize].trim_start(),
                    &text[offset as usize..end]
                );
                let entry = categories.entry(category).or_insert((0usize, Vec::new()));
                entry.0 += 1;
                if entry.1.len() < 6 {
                    entry.1.push(sample);
                }
            }
            if !hit && misses.len() < 400 {
                let start = text[..offset as usize].rfind('\n').map_or(0, |at| at + 1);
                let end = text[offset as usize..]
                    .find('\n')
                    .map_or(text.len(), |at| offset as usize + at);
                misses.push(format!(
                    "{}: {}‸{}",
                    path.file_name().unwrap().to_string_lossy(),
                    text[start..offset as usize].trim_start(),
                    &text[offset as usize..end]
                ));
            }
            if let Some((_, found)) = found
                && !found.is_empty()
            {
                answered += 1;
                if targets.len() < 40 && asked % 97 == 0 {
                    targets.push((path.to_path_buf(), offset));
                }
            }
        }
    }
    println!(
        "definition: {answered}/{asked} answered ({:.1}%), mean {:.2?}, slowest {slowest:.2?}",
        answered as f64 * 100.0 / asked.max(1) as f64,
        total / asked.max(1) as u32
    );

    let references_asked = asked - not_references;
    println!(
        "  of which references: {answered}/{references_asked} ({:.1}%); {not_references} tokens were names of nothing",
        answered as f64 * 100.0 / references_asked.max(1) as f64
    );
    let mut ranked: Vec<_> = categories.into_iter().collect();
    ranked.sort_by_key(|b| std::cmp::Reverse(b.1.0));
    for (category, (count, samples)) in ranked.iter().take(40) {
        println!("  {count:>5}  {category}");
        if std::env::var_os("SAMPLES").is_some() {
            for sample in samples {
                println!("           {sample}");
            }
        }
    }
    if std::env::var_os("MISSES").is_some() {
        for miss in misses.iter().step_by(8) {
            println!("  miss {miss}");
        }
    }
    let mut slowest = Duration::ZERO;
    let mut total = Duration::ZERO;
    let mut hits = 0;
    for (path, offset) in &targets {
        let started = Instant::now();
        let found = semantic.references(path, *offset, None);
        let took = started.elapsed();
        total += took;
        if took > slowest {
            slowest = took;
        }
        hits += found.map_or(0, |(_, found)| found.len());
    }
    println!(
        "references: {} searches, {hits} uses, mean {:.2?}, slowest {slowest:.2?}",
        targets.len(),
        total / targets.len().max(1) as u32
    );

    let mut asked = 0;
    let mut answered = 0;
    let mut slowest = Duration::ZERO;
    let mut total = Duration::ZERO;
    for path in sample.iter().take(60) {
        let Some(text) = semantic.text(path) else {
            continue;
        };
        let dots: Vec<u32> = text
            .match_indices('.')
            .map(|(at, _)| at as u32 + 1)
            .filter(|&at| {
                text.as_bytes()
                    .get(at as usize)
                    .is_some_and(u8::is_ascii_alphabetic)
            })
            .step_by(5)
            .collect();
        for offset in dots {
            asked += 1;
            let started = Instant::now();
            let found = semantic.completions(path, offset, None);
            let took = started.elapsed();
            total += took;
            slowest = slowest.max(took);
            if found.is_some_and(|found| !found.items.is_empty()) {
                answered += 1;
            }
        }
    }
    println!(
        "completion after a dot: {answered}/{asked} answered ({:.1}%), mean {:.2?}, slowest {slowest:.2?}",
        answered as f64 * 100.0 / asked.max(1) as f64,
        total / asked.max(1) as u32
    );
}

/// Where each identifier-looking word in `text` starts.
fn identifier_starts(text: &str) -> Vec<u32> {
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        if bytes[at].is_ascii_alphabetic() || bytes[at] == b'_' {
            let start = at;
            while at < bytes.len() && (bytes[at].is_ascii_alphanumeric() || bytes[at] == b'_') {
                at += 1;
            }
            if start == 0 || !matches!(bytes[start - 1], b'"' | b'/' | b'#') {
                found.push(start as u32);
            }
        } else {
            at += 1;
        }
    }
    found
}
