//! A project with no editor around it: a Rustlyn session over the root,
//! indexed and compiled.

use std::path::{Path, PathBuf};
use std::time::Instant;

use rustlyn_ide::Session;

use super::ask::ask;
use super::walk::sources;

/// A compiled session over `root`. `cache` is a folder to keep the parse
/// and the compilation in between runs: the second run on a large project
/// takes the compilation from there.
///
/// # Errors
///
/// When the compiler panics while indexing or compiling.
pub fn compiled(root: &str, cache: Option<PathBuf>) -> Result<Session, String> {
    compiled_timed(root, cache, &mut Vec::new())
}

/// The same, with the time of each phase in `phases`.
///
/// # Errors
///
/// When the compiler panics while indexing or compiling.
pub fn compiled_timed(
    root: &str,
    cache: Option<PathBuf>,
    phases: &mut Vec<(&'static str, u128)>,
) -> Result<Session, String> {
    let mut lap = Instant::now();
    let mut phase = |name: &'static str, phases: &mut Vec<(&'static str, u128)>| {
        phases.push((name, lap.elapsed().as_millis()));
        lap = Instant::now();
    };
    let session = Session::new(trimmed(root), cache.clone(), Vec::new());
    if cache.is_some() {
        let _ = ask(|| {
            session
                .load_compilation()
                .ok_or(rustlyn_ide::Refusal::NotCompiled)
        });
    }
    phase("load", phases);
    let paths = source_paths(root);
    phase("scan", phases);
    ask(|| Ok(session.reindex(&paths))).ok_or("the compiler failed while indexing")?;
    phase("reindex", phases);
    ask(|| Ok(session.compile(&[]))).ok_or("the compiler failed while compiling")?;
    phase("compile", phases);
    if cache.is_some() {
        let _ = ask(|| {
            session
                .save_compilation()
                .map_err(|e| rustlyn_ide::Refusal::Io(e.to_string()))
        });
    }
    phase("save", phases);
    Ok(session)
}

/// The same session after changes on disk: indexed and compiled again
/// (what did not change, Rustlyn takes from the previous compilation).
///
/// # Errors
///
/// When the compiler panics while indexing or compiling.
pub fn recompile(root: &str, session: Session) -> Result<Session, String> {
    let paths = source_paths(root);
    ask(|| Ok(session.reindex(&paths))).ok_or("the compiler failed while indexing")?;
    ask(|| Ok(session.compile(&[]))).ok_or("the compiler failed while compiling")?;
    Ok(session)
}

fn source_paths(root: &str) -> Vec<PathBuf> {
    let mut files = Vec::new();
    sources(Path::new(root), Path::new(root), &mut files);
    files.iter().map(|f| Path::new(root).join(f)).collect()
}

/// The root without a trailing separator; `/` stays `/`.
fn trimmed(root: &str) -> &str {
    let trimmed = root.trim_end_matches('/');
    if trimmed.is_empty() && root.starts_with('/') {
        "/"
    } else {
        trimmed
    }
}
