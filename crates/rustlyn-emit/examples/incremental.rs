//! How long writing an assembly again takes when one method body changed.
//!
//! Builds the whole corpus once and keeps it, then edits one file in memory
//! (the first `--find` becomes `--replace`, with `{n}` standing for the
//! round) and writes the assembly again, several rounds over. Each round
//! parses the one file, declares the compilation again over the trees it
//! already had, and generates only the bodies of the member the edit is in.
//!
//! ```text
//! cargo run --release -p rustlyn-emit --example incremental -- \
//!     $REFERENCES out/ --define "A;B" --edit Some/File.cs \
//!     --find 'return 1;' --replace 'return {n};' < files.txt
//! ```

use std::io::Read;
use std::path::PathBuf;
use std::time::Instant;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::{ParseOptions, SyntaxKind, parse_with};
use rustlyn_text::SourceText;

fn main() -> std::process::ExitCode {
    let mut arguments = std::env::args().skip(1);
    let (Some(framework), Some(out)) = (
        arguments.next().map(PathBuf::from),
        arguments.next().map(PathBuf::from),
    ) else {
        eprintln!(
            "usage: incremental <references directory> <out directory> [--define A;B] \
             --edit file.cs --find text --replace text [--rounds 3] [--full]"
        );
        return std::process::ExitCode::FAILURE;
    };
    let arguments: Vec<String> = arguments.collect();
    let value = |name: &str| {
        arguments
            .iter()
            .position(|argument| argument == name)
            .and_then(|at| arguments.get(at + 1))
            .cloned()
    };
    let symbols: Vec<String> = value("--define")
        .map(|defines| defines.split(';').map(str::to_string).collect())
        .unwrap_or_default();
    let (Some(edit), Some(find), Some(replace)) =
        (value("--edit"), value("--find"), value("--replace"))
    else {
        eprintln!("--edit, --find and --replace are all needed");
        return std::process::ExitCode::FAILURE;
    };
    let rounds: usize = value("--rounds").map_or(3, |rounds| rounds.parse().unwrap_or(3));
    // Also build the last edit from scratch, to compare the two assemblies.
    let full = arguments.iter().any(|argument| argument == "--full");
    let options = ParseOptions::with_symbols(symbols);
    std::fs::create_dir_all(&out).expect("the out directory should be makeable");

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
    let sources: Vec<SourceText> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter_map(|path| read_source(path).map(|text| SourceText::new(path, text)))
        .collect();

    let started = Instant::now();
    let first: &'static Compilation = Box::leak(Box::new(Compilation::parse_with_references(
        sources, &options, &images,
    )));
    let (mut kept, emitted, skipped) =
        rustlyn_emit::incremental(first, "Assembly-CSharp").expect("the first build");
    std::fs::write(out.join("first.dll"), &emitted.assembly).expect("writable");
    println!(
        "full build: {:.2?}, {} bytes, {} stubs",
        started.elapsed(),
        emitted.assembly.len(),
        skipped.len()
    );

    let trees = first.trees();
    let Some(index) = (0..trees.len()).find(|&index| {
        trees
            .source(index)
            .is_some_and(|source| source.name().ends_with(edit.as_str()))
    }) else {
        eprintln!("{edit} is not among the sources");
        return std::process::ExitCode::FAILURE;
    };
    let original = trees.source(index).expect("found above");
    let Some(at) = original.text().find(find.as_str()) else {
        eprintln!("`{find}` is not in {edit}");
        return std::process::ExitCode::FAILURE;
    };

    let mut last = None;
    for round in 1..=rounds {
        let text = original.text().replacen(
            find.as_str(),
            &replace.replace("{n}", &round.to_string()),
            1,
        );
        let round_started = Instant::now();

        let parsing = Instant::now();
        let tree = parse_with(SourceText::new(original.name(), text), &options);
        let parsed = parsing.elapsed();

        let declaring = Instant::now();
        let trees: Vec<_> = (0..first.trees().len())
            .map(|other| {
                if other == index {
                    tree.clone()
                } else {
                    first.trees().get(other).expect("every tree").clone()
                }
            })
            .collect();
        let compilation: &'static Compilation = Box::leak(Box::new(
            Compilation::create_with_references(trees, &images),
        ));
        let declared = declaring.elapsed();
        if compilation.symbols().len() != first.symbols().len() {
            eprintln!(
                "the edit changed the declarations ({} symbols, was {}): a full build is needed",
                compilation.symbols().len(),
                first.symbols().len()
            );
            return std::process::ExitCode::FAILURE;
        }

        // The member the edit is in: the innermost declaration with a body
        // around it, a local function being part of its member's body.
        let root = tree.root();
        let member = root
            .descendants()
            .filter(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::MethodDeclaration
                        | SyntaxKind::ConstructorDeclaration
                        | SyntaxKind::DestructorDeclaration
                        | SyntaxKind::OperatorDeclaration
                        | SyntaxKind::ConversionOperatorDeclaration
                        | SyntaxKind::GetAccessorDeclaration
                        | SyntaxKind::SetAccessorDeclaration
                        | SyntaxKind::InitAccessorDeclaration
                        | SyntaxKind::AddAccessorDeclaration
                        | SyntaxKind::RemoveAccessorDeclaration
                ) && node.span().start() <= at as u32
                    && (at as u32) < node.span().end()
            })
            .min_by_key(|node| node.span().length());
        let Some(symbol) = member.and_then(|node| compilation.declared_symbol(index, node.span()))
        else {
            eprintln!("the edit is not inside a member with a body");
            return std::process::ExitCode::FAILURE;
        };

        let emitting = Instant::now();
        let rebuilt = match kept.rebuild(compilation, &[symbol]) {
            Ok(rebuilt) => rebuilt,
            Err(error) => {
                eprintln!("{error}");
                return std::process::ExitCode::FAILURE;
            }
        };
        let emitted_in = emitting.elapsed();

        let writing = Instant::now();
        std::fs::write(out.join(format!("round{round}.dll")), &rebuilt.assembly).expect("writable");
        let written = writing.elapsed();
        println!(
            "edit {round} ({}): parse {parsed:.2?}, declarations {declared:.2?}, \
             bodies {emitted_in:.2?} ({} bodies, +{} bytes of IL), write to disk {written:.2?}; \
             total {:.2?}",
            compilation.symbols().qualified_name(symbol),
            rebuilt.bodies,
            rebuilt.appended_bytes,
            round_started.elapsed()
        );
        last = Some(compilation);
    }

    if full && let Some(compilation) = last {
        let started = Instant::now();
        let (emitted, _) =
            rustlyn_emit::survey(compilation, "Assembly-CSharp").expect("the full build");
        std::fs::write(out.join("full.dll"), &emitted.assembly).expect("writable");
        println!("the same edit from scratch: {:.2?}", started.elapsed());
    }
    std::process::ExitCode::SUCCESS
}

/// A source file as text: UTF-8, or each byte as the Latin-1 character it is.
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
