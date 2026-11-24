//! Move type to its own file, rename file to match type, rename type to
//! match file.
//!
//! Roslyn's `MoveTypeToFile` provider, with the cursor on the name of a type
//! declared at the top of a file (not nested in another type), whose name
//! is not the file's.
//!
//! * With other types in the file: "Move type to Foo.cs". The type leaves
//!   this file and is the content of `Foo.cs` beside it, under the same
//!   `using` directives and in the same namespace, written the same way
//!   (block or file-scoped). The new file is a [`FileEdit`] inserting into
//!   a path that does not exist yet: the editor creates the file when it
//!   applies the edit, as an LSP client does with a text edit to a new
//!   document. Not offered when a file of that name is there already.
//! * With no other type: "Rename file to Foo.cs", a rename in the
//!   workspace edit; and "Rename type to Bar", which renames the type and
//!   every reference to it across the project to the file's name.
//!
//! [`FileEdit`]: crate::edit::FileEdit

use std::path::PathBuf;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{declaration_lines, is_identifier, line_start};
use super::super::{ActionKind, CodeAction, Context};
use super::{across_files, references_at};
use crate::edit::{TextEdit, WorkspaceEdit};

fn is_type(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::DelegateDeclaration
    )
}

fn is_namespace(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
    )
}

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let declaration = token.parent().clone();
    if token.kind() != SyntaxKind::IdentifierToken
        || !is_type(declaration.kind())
        || declaration
            .child_token_of_kind(SyntaxKind::IdentifierToken)
            .as_ref()
            != Some(&token)
        || !declaration.parent().is_some_and(|parent| {
            parent.kind() == SyntaxKind::CompilationUnit || is_namespace(parent.kind())
        })
    {
        return;
    }
    let name = token.value_text().to_string();
    let Some(stem) = context
        .path
        .file_stem()
        .map(|stem| stem.to_string_lossy().into_owned())
    else {
        return;
    };
    if stem == name {
        return;
    }
    let directory = context.path.parent().map(PathBuf::from).unwrap_or_default();
    let target = directory.join(format!("{name}.cs"));
    let exists = context.view.project().tree_index(&target).is_some() || target.exists();

    let root = context.view.syntax_root().clone();
    let top_level: Vec<SyntaxNode> = root
        .descendants()
        .filter(|node| {
            is_type(node.kind())
                && node.parent().is_some_and(|parent| {
                    parent.kind() == SyntaxKind::CompilationUnit || is_namespace(parent.kind())
                })
        })
        .collect();

    if top_level.len() > 1 {
        if !exists && let Some(action) = move_type(context, &declaration, &target, &name) {
            found.push(action);
        }
        return;
    }
    if !exists {
        let mut edit = WorkspaceEdit::default();
        edit.renames.push((context.path.clone(), target));
        found.push(CodeAction {
            title: format!("Rename file to {name}.cs"),
            kind: ActionKind::Refactor,
            fixes: None,
            edit,
        });
    }
    if is_identifier(&stem) && !context.view.names_near(&declaration).contains(&stem) {
        let edits: Vec<_> = references_at(context, token.span().start())
            .into_iter()
            .map(|(path, span)| (path, TextEdit::new(span, stem.clone())))
            .collect();
        if !edits.is_empty() {
            found.push(across_files(
                format!("Rename type to {stem}"),
                ActionKind::Refactor,
                edits,
            ));
        }
    }
}

fn move_type(
    context: &Context<'_, '_>,
    declaration: &SyntaxNode,
    target: &std::path::Path,
    name: &str,
) -> Option<CodeAction> {
    let newline = context.newline();
    let root = context.view.syntax_root();
    // The type with its comments and attributes, from the start of its
    // first line.
    let full = declaration.full_span().start();
    let line = line_start(&context.text, full);
    let start = if context
        .slice(TextSpan::from_bounds(line, full))
        .trim()
        .is_empty()
    {
        line
    } else {
        full
    };
    let span = TextSpan::from_bounds(start, declaration.span().end());
    let moved = context.slice(span).trim_end().to_string();
    let moved = moved.trim_start_matches(['\r', '\n']).to_string();

    // The same usings, then the same namespaces.
    let mut out = String::new();
    let usings: Vec<String> = root
        .children()
        .filter(|child| child.kind() == SyntaxKind::UsingDirective)
        .map(|using| using.text())
        .collect();
    if !usings.is_empty() {
        out.push_str(&usings.join(newline));
        out.push_str(newline);
        out.push_str(newline);
    }
    let namespaces: Vec<SyntaxNode> = declaration
        .ancestors()
        .filter(|ancestor| is_namespace(ancestor.kind()))
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();
    let mut closing = String::new();
    for namespace in &namespaces {
        let name = namespace
            .children()
            .find(|child| child.kind().is_type_node())?
            .text();
        let indent = context.indentation_at(namespace.span().start());
        let inner_usings: Vec<String> = namespace
            .children()
            .filter(|child| child.kind() == SyntaxKind::UsingDirective)
            .map(|using| {
                format!(
                    "{}{}",
                    context.indentation_at(using.span().start()),
                    using.text()
                )
            })
            .collect();
        if namespace.kind() == SyntaxKind::FileScopedNamespaceDeclaration {
            out.push_str(&format!("namespace {name};{newline}{newline}"));
            for using in &inner_usings {
                out.push_str(&format!("{using}{newline}"));
            }
            if !inner_usings.is_empty() {
                out.push_str(newline);
            }
        } else {
            out.push_str(&format!(
                "{indent}namespace {name}{newline}{indent}{{{newline}"
            ));
            for using in &inner_usings {
                out.push_str(&format!("{using}{newline}"));
            }
            if !inner_usings.is_empty() {
                out.push_str(newline);
            }
            closing = format!("{newline}{indent}}}{closing}");
        }
    }
    out.push_str(&moved);
    out.push_str(&closing);
    out.push_str(newline);

    let mut edit = WorkspaceEdit::single(
        context.path.clone(),
        vec![TextEdit::delete(declaration_lines(&context.text, span))],
    );
    edit.add(target.to_path_buf(), TextEdit::insert(0, out));
    Some(CodeAction {
        title: format!("Move type to {name}.cs"),
        kind: ActionKind::Refactor,
        fixes: None,
        edit,
    })
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::support::{actions_in, apply_in, titles};

    #[test]
    fn a_second_type_moves_to_a_file_of_its_own() {
        let source = "using System;\n\nnamespace Game\n{\n    class Player { }\n\n    /// <summary>An enemy.</summary>\n    class $$Enemy\n    {\n        int hp;\n    }\n}\n";
        let changed = apply_in(&[("Player.cs", source)], "Move type to Enemy.cs");
        let text = |name: &str| {
            changed
                .iter()
                .find(|(path, _)| path == Path::new(name))
                .unwrap()
                .1
                .clone()
        };
        assert_eq!(
            text("/p/Player.cs"),
            "using System;\n\nnamespace Game\n{\n    class Player { }\n}\n"
        );
        assert_eq!(
            text("/p/Enemy.cs"),
            "using System;\n\nnamespace Game\n{\n    /// <summary>An enemy.</summary>\n    class Enemy\n    {\n        int hp;\n    }\n}\n"
        );
    }

    #[test]
    fn a_file_scoped_namespace_stays_file_scoped() {
        let source = "namespace Game;\n\nclass $$Enemy { }\n\nclass Player { }\n";
        let changed = apply_in(&[("Player.cs", source)], "Move type to Enemy.cs");
        let text = |name: &str| {
            changed
                .iter()
                .find(|(path, _)| path == Path::new(name))
                .unwrap()
                .1
                .clone()
        };
        assert_eq!(
            text("/p/Player.cs"),
            "namespace Game;\n\nclass Player { }\n"
        );
        assert_eq!(text("/p/Enemy.cs"), "namespace Game;\n\nclass Enemy { }\n");
    }

    #[test]
    fn a_lone_type_renames_its_file_or_itself() {
        let source = "class $$Enemy\n{\n    public Enemy() { }\n}\n";
        let other = "class User { Enemy e = new Enemy(); }\n";
        let (_, actions) = actions_in(&[("Monster.cs", source), ("B.cs", other)]);
        let rename = actions
            .iter()
            .find(|action| action.title == "Rename file to Enemy.cs")
            .expect("offered");
        assert_eq!(
            rename.edit.renames,
            [(
                Path::new("/p/Monster.cs").to_path_buf(),
                Path::new("/p/Enemy.cs").to_path_buf()
            )]
        );
        let changed = apply_in(
            &[("Monster.cs", source), ("B.cs", other)],
            "Rename type to Monster",
        );
        let text = |name: &str| {
            changed
                .iter()
                .find(|(path, _)| path == Path::new(name))
                .unwrap()
                .1
                .clone()
        };
        assert_eq!(
            text("/p/Monster.cs"),
            "class Monster\n{\n    public Monster() { }\n}\n"
        );
        assert_eq!(
            text("/p/B.cs"),
            "class User { Monster e = new Monster(); }\n"
        );
        assert!(
            titles("class $$A { }\n")
                .iter()
                .all(|title| !title.starts_with("Move") && !title.starts_with("Rename"))
        );
    }
}
