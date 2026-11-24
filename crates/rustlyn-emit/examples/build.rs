//! Compiles a C# file to a .NET assembly.
//!
//! ```sh
//! cargo run --example build -- Program.cs out/ --define DEBUG
//! dotnet out/Program.dll
//! ```
//!
//! `--library` makes a library (no entry point) and each `--reference
//! <file.dll>` adds one more assembly to compile against, beside the
//! directory `--references` names:
//!
//! ```sh
//! cargo run --example build -- Lib.cs out/ --references $FW --library
//! cargo run --example build -- Program.cs out/ --references $FW --reference out/Lib.dll
//! ```
//!
//! More files of the same compilation come with `--source <file.cs>`, and
//! the rest of the options are those of `csc`: `--langversion <version>`,
//! `--main <type>`, `--checked`, `--optimize`, `--unsafe`, `--nullable
//! <context>` and `--define A;B` (as many times as need be). `--path <k>
//! <path>` names source `k` (0 is the first) as `path` rather than by the
//! file it was read from: the name a file-local type is given hashes it.

use std::path::PathBuf;

use rustlyn_semantics::{Compilation, CompilationOptions};
use rustlyn_syntax::{LanguageVersion, ParseOptions, parse_with};
use rustlyn_text::SourceText;

fn main() -> std::process::ExitCode {
    let mut args = std::env::args().skip(1);
    let (Some(path), directory) = (args.next(), args.next()) else {
        eprintln!(
            "usage: build <file.cs> [output directory] [--source <file.cs>]... [--references <dir>] [--reference [alias,...=]<file.dll>]... [--library] [--define A;B]... [--langversion <version>] [--main <type>] [--checked] [--optimize] [--unsafe] [--nullable <enable|annotations|warnings|disable>] [--path <k> <path>]..."
        );
        return std::process::ExitCode::FAILURE;
    };
    let directory = PathBuf::from(directory.unwrap_or_else(|| ".".to_string()));
    // Without a directory of assemblies the core library is the synthesized
    // one: enough for a program that uses only what the language itself
    // needs, and nothing like enough for one that reads another assembly.
    let rest: Vec<String> = args.collect();
    let references = rest
        .iter()
        .position(|argument| argument == "--references")
        .and_then(|at| rest.get(at + 1))
        .map(PathBuf::from);
    let values = |flag: &str| -> Vec<String> {
        rest.windows(2)
            .filter(|pair| pair[0] == flag)
            .map(|pair| pair[1].clone())
            .collect()
    };
    let has = |flag: &str| rest.iter().any(|argument| argument == flag);
    let mut symbols: Vec<String> = Vec::new();
    for list in values("--define") {
        for symbol in list.split([';', ',']).filter(|symbol| !symbol.is_empty()) {
            if !symbols.iter().any(|known| known == symbol) {
                symbols.push(symbol.to_string());
            }
        }
    }
    let library = has("--library");
    // `--reference A,B=lib.dll` names the reference with `extern alias`es,
    // as `csc /r:A=lib.dll` does.
    let files: Vec<(Vec<String>, PathBuf)> = values("--reference")
        .into_iter()
        .map(|file| match file.split_once('=') {
            Some((aliases, file)) if !aliases.contains(['/', '\\']) => (
                aliases.split(',').map(str::to_string).collect(),
                PathBuf::from(file),
            ),
            _ => (Vec::new(), PathBuf::from(file)),
        })
        .collect();
    let language_version = match values("--langversion").last().map(|text| text.parse()) {
        None => LanguageVersion::default(),
        Some(Ok(version)) => version,
        Some(Err(error)) => {
            eprintln!("error: {error}");
            return std::process::ExitCode::FAILURE;
        }
    };
    let options = ParseOptions::with_symbols(symbols).with_language_version(language_version);
    let compilation_options = CompilationOptions {
        main_type_name: values("--main").pop(),
        check_overflow: has("--checked"),
        optimize: has("--optimize"),
        allow_unsafe: has("--unsafe"),
        // `--nullable enable` and `--nullable annotations` annotate; the
        // warnings alone do nothing to metadata.
        nullable_annotations: values("--nullable")
            .last()
            .is_some_and(|value| matches!(value.as_str(), "enable" | "annotations")),
        writes_readonly_fields: false,
    };
    // `--path <k> <path>`: the name source `k` goes by.
    let mut names: Vec<(usize, String)> = Vec::new();
    for at in 0..rest.len() {
        if rest[at] == "--path"
            && let (Some(index), Some(name)) = (rest.get(at + 1), rest.get(at + 2))
            && let Ok(index) = index.parse()
        {
            names.push((index, name.clone()));
        }
    }
    let name = PathBuf::from(&path).file_stem().map_or_else(
        || "Program".to_string(),
        |stem| stem.to_string_lossy().into(),
    );

    let mut trees = Vec::new();
    for (index, file) in std::iter::once(path).chain(values("--source")).enumerate() {
        let Some(text) = read_source(&file) else {
            eprintln!("{file}: cannot be read");
            return std::process::ExitCode::FAILURE;
        };
        let named = names
            .iter()
            .rev()
            .find(|(k, _)| *k == index)
            .map_or(file, |(_, name)| name.clone());
        trees.push(parse_with(SourceText::new(named, text), &options));
    }
    let mut bytes: Vec<Vec<u8>> = references
        .as_ref()
        .map(|directory| {
            let mut paths: Vec<_> = std::fs::read_dir(directory)
                .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
                .collect();
            paths.sort();
            rustlyn_semantics::parallel::map(&paths, |path| std::fs::read(path).ok())
                .into_iter()
                .flatten()
                .collect()
        })
        .unwrap_or_default();
    let mut aliases: Vec<Vec<String>> = vec![Vec::new(); bytes.len()];
    for (named, file) in &files {
        match std::fs::read(file) {
            Ok(image) => {
                bytes.push(image);
                aliases.push(named.clone());
            }
            Err(error) => {
                eprintln!("{}: {error}", file.display());
                return std::process::ExitCode::FAILURE;
            }
        }
    }
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    // The process ends right after, and handing the compilation back to the
    // allocator a symbol at a time costs more than the rest of a small build.
    let compilation = std::mem::ManuallyDrop::new(
        if images.is_empty() {
            Compilation::create(trees)
        } else {
            Compilation::create_with_aliased_references(trees, &images, &aliases)
        }
        .with_options(compilation_options),
    );
    let mut failed = false;
    for entry in compilation.source_diagnostics() {
        println!("{}", compilation.render(entry));
        failed |= entry.diagnostic.is_error();
    }
    for entry in compilation.semantic_diagnostics() {
        println!("{}", compilation.render(&entry));
        failed |= entry.diagnostic.is_error();
    }
    if failed {
        return std::process::ExitCode::FAILURE;
    }

    let emitted = if library {
        rustlyn_emit::emit_library(&compilation, &name)
    } else {
        rustlyn_emit::emit(&compilation, &name)
    };
    match emitted {
        Ok(emitted) => {
            std::fs::create_dir_all(&directory).expect("the output directory should be writable");
            let assembly = directory.join(format!("{name}.dll"));
            std::fs::write(&assembly, &emitted.assembly).expect("the assembly should be writable");
            if !library {
                std::fs::write(
                    directory.join(format!("{name}.runtimeconfig.json")),
                    &emitted.runtime_config,
                )
                .expect("the runtime configuration should be writable");
            }
            println!(
                "wrote {} ({} bytes)",
                assembly.display(),
                emitted.assembly.len()
            );
            std::process::ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {error}");
            std::process::ExitCode::FAILURE
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
