//! Failability of every method of a project: what each can throw, and how
//! many of those can actually happen — for seeing what the analysis says
//! on real code, and how long it takes.
//!
//! ```text
//! find src -name '*.cs' | cargo run --release -p rustlyn-ide --example failability -- <root> [-v]
//! ```

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use rustlyn_ide::project::{Project, compiled_files};
use rustlyn_ide::semantic::{Semantic, Verdict};

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut args = std::env::args().skip(1);
    let root = PathBuf::from(args.next().expect("usage: failability <root> [-v]"));
    let rest: Vec<String> = args.collect();
    let verbose = rest.iter().any(|a| a == "-v");
    let only = rest
        .iter()
        .find(|a| a.starts_with("--only="))
        .map(|a| a[7..].to_owned());
    let mut list = String::new();
    std::io::stdin()
        .read_to_string(&mut list)
        .expect("a file list");
    let paths: Vec<PathBuf> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(|line| root.join(line))
        .collect();
    let project = Project::discover(&root, &[]);
    let files = compiled_files(&project, &paths);
    let sources: Vec<(PathBuf, String)> = files
        .iter()
        .filter_map(|path| Some((path.clone(), std::fs::read_to_string(path).ok()?)))
        .collect();
    let references: Vec<(PathBuf, Arc<[u8]>)> = project
        .references
        .iter()
        .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(path).ok()?))))
        .collect();
    let started = Instant::now();
    let semantic = Semantic::build(project, sources.clone(), &references, None);
    println!(
        "{} files compiled in {:.2?}",
        semantic.files(),
        started.elapsed()
    );

    let mut members = 0usize;
    let mut verdicts: BTreeMap<String, usize> = BTreeMap::new();
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    let (mut worst, mut worst_member) = (Duration::ZERO, String::new());
    let started = Instant::now();
    for (path, text) in &sources {
        if only
            .as_ref()
            .is_some_and(|o| !path.to_string_lossy().contains(o.as_str()))
        {
            continue;
        }
        // Every method: where a `(` follows a name after a return type, the
        // name's start. Crude, but what a cursor on each name would ask.
        for (offset, _) in text.match_indices('(') {
            let before = &text[..offset];
            let name_start = before
                .rfind(|c: char| !(c.is_alphanumeric() || c == '_'))
                .map_or(0, |i| i + 1);
            if name_start == offset {
                continue;
            }
            let line_start = before.rfind('\n').map_or(0, |i| i + 1);
            let line = text[line_start..].lines().next().unwrap_or_default();
            let declares = (line.contains("public ")
                || line.contains("private ")
                || line.contains("internal ")
                || line.contains("protected ")
                || line.contains("static "))
                && !line.contains('=')
                && !line.trim_start().starts_with("//");
            if !declares {
                continue;
            }
            let asked = Instant::now();
            let asked_about = || semantic.failability(path, name_start as u32);
            let Ok(found) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(asked_about))
            else {
                println!(
                    "panicked: {}:{}",
                    path.display(),
                    text[..name_start].lines().count()
                );
                continue;
            };
            let Some(found) = found else {
                continue;
            };
            let took = asked.elapsed();
            if took > worst {
                worst = took;
                worst_member = found.member.clone();
            }
            members += 1;
            for failure in &found.failures {
                *verdicts
                    .entry(format!("{:?}", failure.verdict))
                    .or_default() += 1;
                *kinds
                    .entry(format!("{:?} {}", failure.kind, failure.exception))
                    .or_default() += 1;
                if verbose && failure.verdict != Verdict::Unknown {
                    let conditions: Vec<&str> =
                        failure.conditions.iter().map(|c| c.text.as_str()).collect();
                    let line = std::fs::read_to_string(&failure.path)
                        .map(|text| {
                            text.as_bytes()
                                .iter()
                                .take(failure.span.start() as usize)
                                .filter(|b| **b == b'\n')
                                .count()
                                + 1
                        })
                        .unwrap_or(0);
                    println!(
                        "{}: {:?} {} at {}:{line} when [{}]",
                        found.member,
                        failure.verdict,
                        failure.exception,
                        failure.path.display(),
                        conditions.join(" && ")
                    );
                    for input in &failure.inputs {
                        println!(
                            "    {} = {:?} ({:?}) {:?}",
                            input.name,
                            input.values,
                            input.origin,
                            input
                                .places
                                .iter()
                                .map(|(p, s)| format!(
                                    "{}@{}",
                                    p.file_name().unwrap_or_default().to_string_lossy(),
                                    s.start()
                                ))
                                .collect::<Vec<_>>()
                        );
                    }
                }
            }
        }
    }
    println!(
        "{members} members in {:.2?}, slowest {worst:.2?} ({worst_member})",
        started.elapsed()
    );
    println!("verdicts: {verdicts:?}");
    for (kind, count) in kinds.iter().rev().take(20) {
        println!("  {count:5} {kind}");
    }
}
