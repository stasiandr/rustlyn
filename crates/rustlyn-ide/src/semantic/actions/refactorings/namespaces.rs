//! Namespace declarations: file-scoped and block-scoped, each into the
//! other, and a namespace changed to match the folder the file is in.
//!
//! Roslyn's `ConvertNamespace` refactoring and `SyncNamespace`'s "Change
//! namespace to '...'", offered with the cursor on the declaration's
//! header. Changing the namespace changes the declaration only: code
//! elsewhere that names the types by their old namespace is not updated.
//!
//! The namespace a folder stands for is the project's root namespace
//! followed by the folders from the project's directory down: the root
//! namespace is the `<RootNamespace>` of the project file in that
//! directory, or the project file's name, or the directory's name, which is
//! what the SDK defaults to.
//!
//! Converting re-indents the members by one level, so a file with a
//! multi-line string literal in it — whose lines are part of its value — is
//! left alone.

use std::path::Path;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::is_identifier;
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let Some(namespace) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| {
            matches!(
                node.kind(),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
            )
        })
    else {
        return;
    };
    let Some(name) = namespace
        .children()
        .find(|child| child.kind().is_type_node())
    else {
        return;
    };
    // The header: up to the end of the name.
    if context.trimmed_span().start() > name.span().end() {
        return;
    }
    let root = context.view.syntax_root().clone();
    let only = root
        .descendants()
        .filter(|node| {
            matches!(
                node.kind(),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
            )
        })
        .count()
        == 1;
    let multi_line_strings = namespace.descendant_tokens().any(|token| {
        matches!(
            token.kind(),
            SyntaxKind::StringLiteralToken
                | SyntaxKind::MultiLineRawStringLiteralToken
                | SyntaxKind::InterpolatedStringTextToken
        ) && token.text().contains('\n')
    });
    if namespace.kind() == SyntaxKind::NamespaceDeclaration {
        if only
            && namespace.parent() == Some(&root)
            && !multi_line_strings
            && !root.children().any(|child| {
                child != namespace
                    && !matches!(
                        child.kind(),
                        SyntaxKind::UsingDirective
                            | SyntaxKind::ExternAliasDirective
                            | SyntaxKind::AttributeList
                    )
            })
            && let Some(edit) = to_file_scoped(context, &namespace, &name)
        {
            found.push(context.local(
                "Convert to file-scoped namespace",
                ActionKind::Refactor,
                None,
                vec![edit],
            ));
        }
    } else if !multi_line_strings && let Some(edit) = to_block(context, &namespace) {
        found.push(context.local(
            "Convert to block scoped namespace",
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
    if only
        && let Some(expected) = folder_namespace(context)
        && expected != name.text().trim()
    {
        found.push(context.local(
            format!("Change namespace to '{expected}'"),
            ActionKind::Refactor,
            None,
            vec![TextEdit::new(name.span(), expected)],
        ));
    }
}

fn to_file_scoped(
    context: &Context<'_, '_>,
    namespace: &SyntaxNode,
    name: &SyntaxNode,
) -> Option<TextEdit> {
    let open = namespace.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
    let close = namespace.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
    if open.is_missing() || close.is_missing() {
        return None;
    }
    let newline = context.newline();
    let unit = context.indent_unit();
    let inside = context.slice(TextSpan::from_bounds(
        open.span().end(),
        close.span().start(),
    ));
    let inside = inside.trim_end_matches([' ', '\t']);
    let inside = inside.trim_end_matches(['\r', '\n']);
    let inside = inside.trim_start_matches([' ', '\t']);
    let inside = inside
        .strip_prefix("\r\n")
        .or_else(|| inside.strip_prefix('\n'))
        .unwrap_or(inside);
    let body: Vec<String> = inside
        .split('\n')
        .map(|line| line.strip_prefix(unit.as_str()).unwrap_or(line).to_string())
        .collect();
    let header = context.slice(TextSpan::from_bounds(
        namespace.span().start(),
        name.span().end(),
    ));
    Some(TextEdit::new(
        namespace.span(),
        format!("{header};{newline}{newline}{}", body.join("\n")),
    ))
}

fn to_block(context: &Context<'_, '_>, namespace: &SyntaxNode) -> Option<TextEdit> {
    let semicolon = namespace.child_token_of_kind(SyntaxKind::SemicolonToken)?;
    let newline = context.newline();
    let unit = context.indent_unit();
    let members = context.slice(TextSpan::from_bounds(
        semicolon.span().end(),
        namespace.span().end(),
    ));
    let members = members.trim_start_matches([' ', '\t', '\r', '\n']);
    let body: Vec<String> = members
        .split('\n')
        .map(|line| {
            if line.trim().is_empty() {
                line.trim_start_matches([' ', '\t']).to_string()
            } else {
                format!("{unit}{line}")
            }
        })
        .collect();
    Some(TextEdit::new(
        TextSpan::from_bounds(semicolon.span().start(), namespace.span().end()),
        format!("{newline}{{{newline}{}{newline}}}", body.join("\n")),
    ))
}

/// The namespace the file's folder stands for, when the project says where
/// its root is.
fn folder_namespace(context: &Context<'_, '_>) -> Option<String> {
    let project = context.view.project().project();
    let root = project
        .roots
        .iter()
        .filter(|root| context.path.starts_with(root))
        .max_by_key(|root| root.components().count())?;
    let mut parts = vec![root_namespace(root)?];
    let relative = context.path.parent()?.strip_prefix(root).ok()?;
    for folder in relative.components() {
        let folder = folder.as_os_str().to_string_lossy();
        parts.push(identifier_of(&folder));
    }
    let expected = parts.join(".");
    expected.split('.').all(is_identifier).then_some(expected)
}

/// A folder's or a project's name as a namespace part: what is not allowed
/// in an identifier becomes `_`, as the SDK does it.
fn identifier_of(name: &str) -> String {
    let mut out: String = name
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

/// The root namespace of the project in `root`.
fn root_namespace(root: &Path) -> Option<String> {
    let project_file = std::fs::read_dir(root).ok().and_then(|entries| {
        entries
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .find(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "csproj")
            })
    });
    if let Some(file) = project_file {
        if let Ok(text) = std::fs::read_to_string(&file)
            && let Some(start) = text.find("<RootNamespace>")
            && let Some(end) = text[start..].find("</RootNamespace>")
        {
            let value = text[start + "<RootNamespace>".len()..start + end].trim();
            if !value.is_empty() && !value.contains('$') {
                return Some(value.to_string());
            }
        }
        return file.file_stem().map(|stem| {
            stem.to_string_lossy()
                .split('.')
                .map(identifier_of)
                .collect::<Vec<_>>()
                .join(".")
        });
    }
    root.file_name()
        .map(|name| identifier_of(&name.to_string_lossy()))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::super::support::apply;
    use crate::project::{Project, ProjectKind};
    use crate::semantic::Semantic;
    use rustlyn_text::TextSpan;

    #[test]
    fn a_block_namespace_becomes_file_scoped_and_back() {
        let block = "using System;\n\nnamespace $$Game.Core\n{\n    class Player\n    {\n        int hp;\n    }\n\n    enum Kind { A }\n}\n";
        let scoped = "using System;\n\nnamespace Game.Core;\n\nclass Player\n{\n    int hp;\n}\n\nenum Kind { A }\n";
        assert_eq!(apply(block, "Convert to file-scoped namespace"), scoped);
        let back = scoped.replace("namespace Game", "namespace $$Game");
        assert_eq!(
            apply(&back, "Convert to block scoped namespace"),
            block.replace("$$", "")
        );
    }

    #[test]
    fn a_namespace_follows_the_folder() {
        let project = Project {
            kind: ProjectKind::Folder,
            projects: 0,
            roots: vec![PathBuf::from("/nowhere/Shooter")],
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: Vec::new(),
            owned_files: Vec::new(),
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let text = "namespace Wrong\n{\n    class Player { }\n}\n";
        let path = PathBuf::from("/nowhere/Shooter/Actors/Heroes/Player.cs");
        let semantic = Semantic::build(project, vec![(path.clone(), text.to_string())], &[], None);
        let actions = semantic
            .code_actions(&path, TextSpan::new(12, 0), None)
            .expect("in the project");
        let action = actions
            .iter()
            .find(|action| action.title == "Change namespace to 'Shooter.Actors.Heroes'")
            .expect("offered");
        assert_eq!(
            crate::edit::apply(text, action.edit.edits_of(&path)),
            "namespace Shooter.Actors.Heroes\n{\n    class Player { }\n}\n"
        );
    }
}
