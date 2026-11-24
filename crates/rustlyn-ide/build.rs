//! A fingerprint of the source this library is built from.
//!
//! A compilation snapshot is read back only by the build that wrote it (see
//! `program_stamp` in `semantic.rs`). What decides whether two builds agree
//! is their source, not the program they were linked into: an editor that
//! is rebuilt, re-copied or re-signed without a line of Rustlyn changing
//! must keep its snapshot, or every start compiles the project from nothing.
//!
//! So the fingerprint is a hash of every Rust file of the workspace's crates
//! and of the lock file — the source of everything that goes into a
//! snapshot, and nothing else.

use std::path::{Path, PathBuf};

fn main() {
    let manifest = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("set by cargo"));
    // `crates/rustlyn-ide` → `crates`, and the workspace above it. Built
    // outside the workspace, only this crate's own source is there to hash.
    let crates = manifest.parent().map(Path::to_path_buf);
    let workspace = crates
        .as_deref()
        .and_then(Path::parent)
        .map(Path::to_path_buf);

    let mut files = Vec::new();
    match &crates {
        Some(crates) if crates.file_name().is_some_and(|name| name == "crates") => {
            for entry in read_dir(crates) {
                let source = entry.join("src");
                if source.is_dir() {
                    println!("cargo:rerun-if-changed={}", source.display());
                    rust_files(&source, &mut files);
                }
            }
        }
        _ => {
            let source = manifest.join("src");
            println!("cargo:rerun-if-changed={}", source.display());
            rust_files(&source, &mut files);
        }
    }
    if let Some(lock) = workspace.map(|workspace| workspace.join("Cargo.lock"))
        && lock.is_file()
    {
        println!("cargo:rerun-if-changed={}", lock.display());
        files.push(lock);
    }
    files.sort();

    // FNV-1a over each path and its bytes: stable across runs and machines,
    // and nothing to depend on.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut feed = |bytes: &[u8]| {
        for &byte in bytes {
            hash = (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3);
        }
    };
    for file in &files {
        let relative = file.strip_prefix(&manifest).unwrap_or(file);
        feed(relative.to_string_lossy().as_bytes());
        feed(&std::fs::read(file).unwrap_or_default());
    }
    feed(
        std::env::var("CARGO_PKG_VERSION")
            .unwrap_or_default()
            .as_bytes(),
    );
    println!("cargo:rustc-env=RUSTLYN_SOURCE_HASH={hash}");
}

fn read_dir(directory: &Path) -> Vec<PathBuf> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(directory)
        .map(|entries| {
            entries
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .collect()
        })
        .unwrap_or_default();
    entries.sort();
    entries
}

fn rust_files(directory: &Path, into: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if path.is_dir() {
            rust_files(&path, into);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            into.push(path);
        }
    }
}
