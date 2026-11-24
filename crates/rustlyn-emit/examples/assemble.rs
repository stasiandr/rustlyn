//! Writes one assembly out of a whole corpus, whatever is still missing.
//!
//! The coverage sweep counts bodies. This asks the other question: can an
//! assembly be *made* at all — the rows, the signatures, the layout — with a
//! throwing body standing in wherever one could not be written. What comes
//! out is a file a metadata reader can be pointed at, which is the only way
//! to find the problems that are not in any one body.
//!
//! ```text
//! find roslyn/src/Compilers -name '*.cs' |
//!   cargo run --release -p rustlyn-emit --example assemble -- \
//!     $FRAMEWORK out/Roslyn.dll --define NET
//! ```

use std::io::Read;
use std::path::PathBuf;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::ParseOptions;
use rustlyn_text::SourceText;

fn main() -> std::process::ExitCode {
    let mut arguments = std::env::args().skip(1);
    let (Some(framework), Some(out)) = (
        arguments.next().map(PathBuf::from),
        arguments.next().map(PathBuf::from),
    ) else {
        eprintln!(
            "usage: assemble <shared framework directory> <out.dll> [--define A;B] [--resource Ns.Class=file.resx]"
        );
        return std::process::ExitCode::FAILURE;
    };
    let arguments: Vec<String> = arguments.collect();
    let mut symbols: Vec<String> = Vec::new();
    // `--diagnostics <text>` says why something did not bind: the stub says
    // which expression, and this says what the binder made of it.
    let mut wanted: Option<String> = None;
    // `--resource Namespace.Class=path/to/Class.resx` embeds the strings of
    // a `.resx` under `Namespace.Class.resources`, which is where the
    // `ResourceManager` the generated class makes goes looking for them.
    let mut resources: Vec<rustlyn_emit::Resource> = Vec::new();
    let mut expecting = None;
    for argument in &arguments {
        match expecting.take() {
            Some("define") => symbols.extend(argument.split(';').map(str::to_string)),
            Some("diagnostics") => wanted = Some(argument.clone()),
            Some("resource") => {
                let Some((base, path)) = argument.split_once('=') else {
                    eprintln!("--resource wants Namespace.Class=file.resx, not `{argument}`");
                    return std::process::ExitCode::FAILURE;
                };
                let text =
                    std::fs::read_to_string(path).unwrap_or_else(|error| panic!("{path}: {error}"));
                let entries = rustlyn_emit::resources::resx_strings(&text);
                resources.push(rustlyn_emit::Resource::strings(
                    &format!("{base}.resources"),
                    &entries,
                ));
            }
            _ if argument == "--define" => expecting = Some("define"),
            _ if argument == "--diagnostics" => expecting = Some("diagnostics"),
            _ if argument == "--resource" => expecting = Some("resource"),
            _ => {}
        }
    }
    let options = ParseOptions::with_symbols(symbols);

    let reading = rustlyn_semantics::timing::phase("read references");
    let mut references: Vec<_> = std::fs::read_dir(&framework)
        .unwrap_or_else(|error| panic!("{}: {error}", framework.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
        .collect();
    references.sort();
    let bytes: Vec<Vec<u8>> =
        rustlyn_semantics::parallel::map(&references, |path| std::fs::read(path).ok())
            .into_iter()
            .flatten()
            .collect();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    drop(reading);

    let parsing = rustlyn_semantics::timing::phase("read sources");
    let mut list = String::new();
    std::io::stdin()
        .read_to_string(&mut list)
        .expect("the file list should be readable");
    let paths: Vec<&str> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();
    // Every file is read on its own, so they are read side by side; parsing
    // them is left to the compilation, which declares each as it comes.
    let sources: Vec<SourceText> = rustlyn_semantics::parallel::map(&paths, |&path| {
        read_source(path).map(|text| SourceText::new(path, text))
    })
    .into_iter()
    .flatten()
    .collect();
    let files = sources.len();
    drop(parsing);
    let compilation = Compilation::parse_with_references(sources, &options, &images);

    if let Some(wanted) = &wanted {
        let mut found = 0usize;
        for entry in compilation.semantic_diagnostics() {
            let rendered = compilation.render(&entry);
            if rendered.contains(wanted.as_str()) {
                println!("{rendered}");
                found += 1;
            }
        }
        println!("{found} diagnostics about `{wanted}`");
    }

    let name = out.file_stem().map_or_else(
        || "Assembly".to_string(),
        |stem| stem.to_string_lossy().into(),
    );
    let started = std::time::Instant::now();
    let result = rustlyn_emit::survey_with_resources(&compilation, &name, &resources);
    // The process ends here, and handing a whole compilation back to the
    // allocator one node at a time is a second the operating system does in
    // no time at all.
    std::mem::forget(compilation);
    match result {
        Ok((emitted, skipped)) => {
            if let Some(directory) = out.parent() {
                let _ = std::fs::create_dir_all(directory);
            }
            std::fs::write(&out, &emitted.assembly).expect("the assembly should be writable");
            println!(
                "{files} files → {} ({} bytes) in {:.2?}",
                out.display(),
                emitted.assembly.len(),
                started.elapsed()
            );
            println!("{} bodies replaced with a stub", skipped.len());
            // The list itself, next to the assembly: what is still missing is
            // the whole point of making one that is not finished.
            let listed: String = skipped
                .iter()
                .map(|(method, reason)| format!("{method}\t{reason}\n"))
                .collect();
            let beside = out.with_extension("stubs.txt");
            if std::fs::write(&beside, listed).is_ok() {
                println!("list: {}", beside.display());
            }
            std::process::ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("could not build the assembly: {error}");
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
