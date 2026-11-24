//! Every action offered anywhere in a realistic file, applied, leaves a
//! file with no more errors than it had: the providers' promise that what
//! they offer is a correct edit, checked by the compiler.

use std::path::Path;

use rustlyn_syntax::SyntaxKind;
use rustlyn_text::TextSpan;

use crate::semantic::tests::compile;

const SOURCES: [&str; 3] = [
    include_str!("sweep.cs"),
    include_str!("sweep2.cs"),
    include_str!("sweep3.cs"),
];

fn errors(text: &str) -> Vec<String> {
    errors_in(&[("A.cs".to_string(), text.to_string())])
}

/// The errors of the files compiled together: `A.cs`, and the files an
/// action made beside it.
fn errors_in(files: &[(String, String)]) -> Vec<String> {
    let borrowed: Vec<(&str, &str)> = files
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect();
    let semantic = compile(&borrowed, false).expect("compiles");
    let mut found = Vec::new();
    for (name, text) in files {
        found.extend(
            semantic
                .diagnostics(&Path::new("/p").join(name), None)
                .unwrap_or_default()
                .into_iter()
                .filter(rustlyn_diagnostics::Diagnostic::is_error)
                .map(|diagnostic| {
                    let at = diagnostic.span();
                    let end = at.end().min(text.len() as u32);
                    format!(
                        "{} at {:?}: {}",
                        diagnostic.code(),
                        &text[at.start().min(end) as usize..end as usize],
                        diagnostic.message()
                    )
                }),
        );
    }
    found
}

#[test]
fn every_action_anywhere_compiles() {
    for source in SOURCES {
        sweep(source);
    }
}

fn sweep(source: &str) {
    let semantic = compile(&[("A.cs", source)], false).expect("compiles");
    let path = Path::new("/p/A.cs");
    let before = errors(source);
    assert!(before.is_empty(), "the sample should compile: {before:?}");
    let tree = rustlyn_syntax::parse_with(
        rustlyn_text::SourceText::new("A.cs", source),
        &rustlyn_syntax::ParseOptions::default(),
    );
    let mut spans: Vec<TextSpan> = tree
        .root()
        .descendant_tokens()
        .map(|token| TextSpan::new(token.span().start(), 0))
        .collect();
    spans.extend(tree.root().descendants().filter_map(|node| {
        (node.kind().is_expression()
            || super::super::text::is_statement(node.kind())
            || node.kind() == SyntaxKind::FieldDeclaration
            || node.kind() == SyntaxKind::PropertyDeclaration)
            .then(|| node.span())
    }));
    let mut failures = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut checked = 0;
    for span in spans {
        let actions = semantic
            .code_actions(path, span, None)
            .expect("in the project");
        for action in actions {
            // Edits to other files make new ones: extract interface into a
            // file of its own, move type.
            let after = crate::edit::apply(source, action.edit.edits_of(path));
            let mut files = vec![("A.cs".to_string(), after.clone())];
            for file in &action.edit.files {
                if file.path != path
                    && let Some(name) = file.path.file_name()
                {
                    files.push((
                        name.to_string_lossy().into_owned(),
                        crate::edit::apply("", &file.edits),
                    ));
                }
            }
            if !seen.insert(files.clone()) {
                continue;
            }
            checked += 1;
            let found = errors_in(&files);
            if !found.is_empty() {
                failures.push(format!("{} at {span:?}: {found:?}\n{after}", action.title));
            }
        }
    }
    assert!(checked > 100, "only {checked} actions were offered");
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
