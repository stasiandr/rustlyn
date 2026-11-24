//! Loads every assembly of a shared framework and reports what came out.
//!
//! The point is the last number. A loader that quietly answers `?` to every
//! signature it does not understand looks exactly like one that works, until
//! something tries to bind against it — so this counts the types it could not
//! work out and prints them, rather than only counting what it declared.
//!
//! ```text
//! cargo run -p rustlyn-semantics --example load -- ~/dotnet/shared/Microsoft.NETCore.App/8.0.11
//! ```

use std::collections::BTreeMap;
use std::path::PathBuf;

use rustlyn_semantics::{Compilation, SymbolKind, Type};

fn main() {
    let Some(directory) = std::env::args().nth(1).map(PathBuf::from) else {
        eprintln!("usage: load <shared framework directory>");
        std::process::exit(2);
    };

    let mut paths: Vec<_> = std::fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
        .collect();
    paths.sort();
    let bytes: Vec<Vec<u8>> = paths
        .iter()
        .filter_map(|path| std::fs::read(path).ok())
        .collect();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();

    let started = std::time::Instant::now();
    let compilation = Compilation::create_with_references(Vec::new(), &images);
    let elapsed = started.elapsed();

    let symbols = compilation.symbols();
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut unresolved = Vec::new();
    for symbol in symbols.iter() {
        if !compilation.is_from_metadata(symbol.id) {
            continue;
        }
        let name = match symbol.kind {
            SymbolKind::Namespace => "namespaces",
            SymbolKind::NamedType => "types",
            SymbolKind::Method => "methods",
            SymbolKind::Field => "fields",
            SymbolKind::Property => "properties",
            SymbolKind::Parameter => "parameters",
            SymbolKind::TypeParameter => "type parameters",
            _ => "other",
        };
        *counts.entry(name).or_default() += 1;
        if compilation.metadata_type(symbol.id) == Some(&Type::Error) {
            unresolved.push(symbols.qualified_name(symbol.id));
        }
    }

    println!("{} assemblies in {:.2?}", images.len(), elapsed);
    for (kind, count) in counts {
        println!("{count:>9} {kind}");
    }
    println!("{:>9} types that did not resolve", unresolved.len());
    for name in unresolved.iter().take(20) {
        println!("          {name}");
    }
}
