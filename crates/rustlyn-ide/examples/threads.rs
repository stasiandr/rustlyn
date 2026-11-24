//! Compiles a project and prints what the thread analyzers find in it:
//! RLN1001 races, RLN1002 Unity off its main thread, RLN1003 `Parallel`
//! writes.
//!
//! ```text
//! cargo run --release -p rustlyn-ide --example threads -- <root> [--all]
//! ```
//!
//! Every `.cs` file under the root is given to the project (a Unity
//! project's packages too); what is reported is the project's own code,
//! or everything with `--all`. A summary by id ends the output.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use rustlyn_ide::project::{Project, compiled_files};
use rustlyn_ide::semantic::Semantic;

fn sources_under(root: &Path, found: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        if path.is_dir() {
            if matches!(
                name.as_str(),
                "obj" | "bin" | "Temp" | ".git" | "Logs" | "node_modules"
            ) {
                continue;
            }
            sources_under(&path, found);
        } else if name.ends_with(".cs") {
            found.push(path);
        }
    }
}

fn is_package(path: &Path) -> bool {
    path.components().any(|part| {
        let part = part.as_os_str().to_string_lossy();
        part == "PackageCache" || part == "Packages"
    })
}

fn main() {
    let mut args = std::env::args().skip(1);
    let root = PathBuf::from(args.next().expect("usage: threads <root> [--all]"));
    let all = args.any(|arg| arg == "--all");
    let mut paths = Vec::new();
    sources_under(&root, &mut paths);

    let started = Instant::now();
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
    eprintln!(
        "{:?}: {} files, {} references",
        project.kind,
        sources.len(),
        references.len()
    );
    let semantic = Semantic::build(project, sources.clone(), &references, None);
    eprintln!("compiled in {:.2?}", started.elapsed());

    let started = Instant::now();
    let mut by_id: BTreeMap<&'static str, usize> = BTreeMap::new();
    for (path, text) in &sources {
        if !all && is_package(path) {
            continue;
        }
        let Some(found) = semantic.analyzer_diagnostics(path, None) else {
            continue;
        };
        for diagnostic in found.iter().filter(|found| found.id.starts_with("RLN")) {
            let start = diagnostic.span.start() as usize;
            let line = text[..start.min(text.len())].matches('\n').count() + 1;
            let source_line = text.lines().nth(line - 1).unwrap_or("").trim();
            println!(
                "{}:{line}: {} {}\n    {source_line}",
                path.display(),
                diagnostic.id,
                diagnostic.message
            );
            *by_id.entry(diagnostic.id).or_default() += 1;
        }
    }
    eprintln!("analyzed in {:.2?}", started.elapsed());
    for (id, count) in by_id {
        println!("{id}: {count}");
    }
}
