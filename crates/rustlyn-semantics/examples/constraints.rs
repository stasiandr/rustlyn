//! Prints what every `where` clause in a corpus was understood to say.
//!
//! A constraint is written in one place and checked in another, so a
//! constraint on the wrong type parameter is invisible until the runtime
//! refuses a construction. This lists them by the type parameter they landed
//! on, which is where a mistake shows.
//!
//! ```text
//! find roslyn/src/Compilers -name '*.cs' |
//!   cargo run --release -p rustlyn-semantics --example constraints -- \
//!     $FRAMEWORK --define NET --focus SegmentedArray
//! ```

use std::io::Read;
use std::path::PathBuf;

use rustlyn_semantics::{Binder, Compilation, Diagnostics, SymbolKind};
use rustlyn_syntax::{ParseOptions, parse_with};
use rustlyn_text::SourceText;

fn main() {
    let mut arguments = std::env::args().skip(1);
    let Some(framework) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: constraints <shared framework directory> [--define A;B] [--focus name]");
        std::process::exit(2);
    };
    let arguments: Vec<String> = arguments.collect();
    let mut symbols: Vec<String> = Vec::new();
    let mut focus: Option<String> = None;
    let mut expecting: Option<&str> = None;
    for argument in &arguments {
        match expecting.take() {
            Some("--define") => symbols.extend(argument.split(';').map(str::to_string)),
            Some("--focus") => focus = Some(argument.clone()),
            _ => match argument.as_str() {
                "--define" => expecting = Some("--define"),
                "--focus" => expecting = Some("--focus"),
                _ => {}
            },
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
    let trees: Vec<_> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter_map(|path| {
            let text = std::fs::read_to_string(path).ok()?;
            Some(parse_with(SourceText::new(path, &text), &options))
        })
        .collect();
    let compilation = Compilation::create_with_references(trees, &images);
    let binder = Binder::new(&compilation);
    let symbols = compilation.symbols();

    for symbol in symbols.iter() {
        if symbol.kind != SymbolKind::TypeParameter {
            continue;
        }
        let Some(detail) = symbol.as_type_parameter() else {
            continue;
        };
        let owner = symbol
            .container
            .map(|owner| symbols.qualified_name(owner))
            .unwrap_or_default();
        if let Some(focus) = &focus
            && !owner.contains(focus.as_str())
        {
            continue;
        }
        if detail.constraints.is_empty() && !detail.value_type && !detail.reference_type {
            continue;
        }
        let mut written: Vec<String> = Vec::new();
        if detail.reference_type {
            written.push("class".to_string());
        }
        if detail.value_type {
            written.push("struct".to_string());
        }
        for reference in &detail.constraints {
            let mut sink = Diagnostics::new();
            let ty = binder.resolve_type_ref(*reference, &mut sink);
            written.push(ty.display(symbols));
        }
        println!("{owner}.{} : {}", symbol.name, written.join(", "));
    }
}
