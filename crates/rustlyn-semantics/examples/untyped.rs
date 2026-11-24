//! Finds the expressions a binder gave no type to without saying so.
//!
//! A diagnostic is the binder admitting it did not understand something. This
//! counts the other half: the expressions whose type came out `?` in a file
//! that bound without a single diagnostic. Those are the ones the backend
//! meets as a type it cannot write down, and nothing in the diagnostic
//! histogram points at them.
//!
//! ```text
//! find roslyn/src/Compilers -name '*.cs' |
//!   cargo run --release -p rustlyn-semantics --example untyped -- \
//!     $FRAMEWORK --define NET
//! ```

use std::collections::BTreeMap;
use std::io::Read;
use std::path::PathBuf;

use rustlyn_semantics::{Compilation, SemanticModel};
use rustlyn_syntax::{ParseOptions, SyntaxKind, parse_with};
use rustlyn_text::SourceText;

fn main() {
    let mut arguments = std::env::args().skip(1);
    let Some(framework) = arguments.next().map(PathBuf::from) else {
        eprintln!("usage: untyped <shared framework directory> [--define A;B]");
        std::process::exit(2);
    };
    let arguments: Vec<String> = arguments.collect();
    let mut symbols: Vec<String> = Vec::new();
    let mut expecting = false;
    for argument in &arguments {
        if expecting {
            symbols.extend(argument.split(';').map(str::to_string));
            expecting = false;
        } else if argument == "--define" {
            expecting = true;
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
    let paths: Vec<&str> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();

    let trees: Vec<_> = paths
        .iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(path).ok()?;
            Some(parse_with(SourceText::new(*path, &text), &options))
        })
        .collect();
    let compilation = Compilation::create_with_references(trees, &images);

    // Only files the binder had nothing to say about: where it did report
    // something, an untyped expression is that report's consequence.
    let mut clean = vec![true; compilation.source_trees().len()];
    for entry in compilation.semantic_diagnostics() {
        if let Some(slot) = clean.get_mut(entry.tree) {
            *slot = false;
        }
    }

    // What was written, by the shape of it: the syntax kind and the first few
    // words, so that a thousand different names count as one gap.
    // A model names a tree by its place among *all* of them, and a
    // synthesized core library comes first where there is one.
    let offset = compilation.trees().len() - compilation.source_trees().len();
    let mut by_shape: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for (index, tree) in compilation.source_trees().iter().enumerate() {
        if !clean[index] {
            continue;
        }
        let model = SemanticModel::new(&compilation, offset + index);
        for node in tree.root().descendants() {
            if !is_member(node.kind()) {
                continue;
            }
            let Some(body) = model.bound_body_containing(&node) else {
                continue;
            };
            for (span, ty) in &body.types {
                if !ty.is_error() {
                    continue;
                }
                let Some(at) = tree.root().find_node(*span) else {
                    continue;
                };
                // The outermost error is the one to report: everything it is
                // written inside is an error because of it.
                if std::env::var("UNTYPED_ALL").is_err()
                    && at.ancestors().any(|parent| {
                        body.types
                            .get(&parent.span())
                            .is_some_and(rustlyn_semantics::Type::is_error)
                    })
                {
                    continue;
                }
                // Two shapes have no type in the language either: a
                // namespace is not a value, and a `throw` expression
                // produces nothing. Counting them would bury what is
                // actually missing.
                let names_a_namespace = |node: &rustlyn_syntax::SyntaxNode| {
                    matches!(
                        body.reference_at(node.span()),
                        Some(rustlyn_semantics::BoundSymbol::Declared(symbol))
                            if compilation.symbols().get(symbol).kind
                                == rustlyn_semantics::SymbolKind::Namespace
                    )
                };
                if at.kind() == SyntaxKind::ThrowExpression
                    || names_a_namespace(&at)
                    || at
                        .children()
                        .last()
                        .is_some_and(|last| names_a_namespace(&last))
                {
                    continue;
                }
                let key = format!("{:?}", at.kind());
                let bucket = by_shape.entry(key).or_default();
                bucket.0 += 1;
                if bucket.1.is_empty() {
                    bucket.1 = format!("{}: {}", tree.source().name(), snippet(&at.text()));
                }
            }
        }
    }

    let files = clean.iter().filter(|clean| **clean).count();
    let total: usize = by_shape.values().map(|(count, _)| count).sum();
    println!("{files} files without diagnostics, {total} expressions without a type");
    let mut ranked: Vec<_> = by_shape.into_iter().collect();
    ranked.sort_by_key(|b| std::cmp::Reverse(b.1.0));
    for (kind, (count, example)) in ranked.iter().take(30) {
        println!("{count:>8}  {kind}");
        println!("          {example}");
    }
}

const fn is_member(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::FieldDeclaration
            | SyntaxKind::EventDeclaration
    )
}

/// One line of the source, short enough to read in a list.
fn snippet(text: &str) -> String {
    let line: String = text.split('\n').next().unwrap_or(text).trim().to_string();
    if line.chars().count() > 90 {
        line.chars().take(90).collect::<String>() + "…"
    } else {
        line
    }
}
