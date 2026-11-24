//! Binds a C# file and lists its diagnostics one per line, in the shape the
//! diagnostics benchmark (`tools/diag`) compares with what Roslyn reports:
//! severity, code, line and column (1-based), and the text the diagnostic
//! points at, tab-separated.
//!
//! ```sh
//! cargo run --example diagnose -- Program.cs --references $FW --langversion preview --unsafe
//! ```
//!
//! Nothing is emitted: this is the compiler up to and including binding.

use std::path::PathBuf;

use rustlyn_semantics::{Compilation, CompilationDiagnostic, CompilationOptions};
use rustlyn_syntax::{LanguageVersion, ParseOptions, parse_with};
use rustlyn_text::SourceText;

fn main() -> std::process::ExitCode {
    let mut args = std::env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!(
            "usage: diagnose <file.cs> [--references <dir>] [--define A;B] [--langversion <version>] [--unsafe]"
        );
        return std::process::ExitCode::FAILURE;
    };
    let rest: Vec<String> = args.collect();
    let option = |name: &str| {
        rest.iter()
            .position(|argument| argument == name)
            .and_then(|at| rest.get(at + 1))
    };
    let symbols: Vec<String> = option("--define")
        .map(|list| list.split(';').map(str::to_string).collect())
        .unwrap_or_default();
    let language_version = match option("--langversion").map(|text| text.parse()) {
        None => LanguageVersion::default(),
        Some(Ok(version)) => version,
        Some(Err(error)) => {
            eprintln!("error: {error}");
            return std::process::ExitCode::FAILURE;
        }
    };
    let text = std::fs::read_to_string(&path).expect("the file should be readable");
    let tree = parse_with(
        SourceText::new(path, text),
        &ParseOptions::with_symbols(symbols).with_language_version(language_version),
    );
    let images: Vec<Vec<u8>> = option("--references")
        .map(PathBuf::from)
        .map(|directory| {
            let mut paths: Vec<_> = std::fs::read_dir(&directory)
                .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
                .collect();
            paths.sort();
            paths
                .iter()
                .filter_map(|path| std::fs::read(path).ok())
                .collect()
        })
        .unwrap_or_default();
    let images: Vec<&[u8]> = images.iter().map(Vec::as_slice).collect();
    let compilation = if images.is_empty() {
        Compilation::create(vec![tree])
    } else {
        Compilation::create_with_references(vec![tree], &images)
    }
    .with_options(CompilationOptions {
        allow_unsafe: rest.iter().any(|argument| argument == "--unsafe"),
        ..CompilationOptions::default()
    });

    let print = |entry: &CompilationDiagnostic| {
        let source = compilation.trees()[entry.tree].source();
        let lines = mapped_lines(source.text());
        let span = entry.diagnostic.span();
        let position = source.line_position(span.start());
        let all = source.text();
        let (start, end) = (span.start() as usize, span.end() as usize);
        // Roslyn counts columns in UTF-16 code units, not in bytes.
        let line_start = all[..start].rfind('\n').map_or(0, |at| at + 1);
        let column = all[line_start..start].encode_utf16().count();
        println!(
            "{}\t{}\t{}\t{}\t{}",
            entry.diagnostic.severity(),
            entry.diagnostic.code(),
            lines
                .get(position.line as usize)
                .copied()
                .unwrap_or(position.line as usize + 1),
            column + 1,
            json_string(&all[start..end.min(all.len())]),
        );
    };
    for entry in compilation.source_diagnostics() {
        print(entry);
    }
    for entry in &compilation.semantic_diagnostics() {
        print(entry);
    }
    std::process::ExitCode::SUCCESS
}

/// The text as a JSON string literal, which is how the expected side writes it.
fn json_string(text: &str) -> String {
    let mut out = String::from('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                let mut units = [0u16; 2];
                for unit in c.encode_utf16(&mut units) {
                    out.push_str(&format!("\\u{unit:04x}"));
                }
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// The line each line of the file is reported at, 1-based, after the
/// `#line` directives in it: `#line 15` makes the next line line 15, and
/// `#line default` goes back to counting lines as they are.
fn mapped_lines(text: &str) -> Vec<usize> {
    let mut mapped = Vec::new();
    let mut offset: isize = 0;
    for (index, line) in text.split('\n').enumerate() {
        let physical = index as isize + 1;
        mapped.push((physical + offset).max(1) as usize);
        let directive = line.trim_start();
        let Some(rest) = directive.strip_prefix('#') else {
            continue;
        };
        let Some(argument) = rest.trim_start().strip_prefix("line") else {
            continue;
        };
        let argument = argument.trim();
        if argument.starts_with("default") {
            offset = 0;
        } else if let Some(number) = argument
            .split_whitespace()
            .next()
            .and_then(|word| word.parse::<isize>().ok())
        {
            offset = number - (physical + 1);
        }
    }
    mapped
}
