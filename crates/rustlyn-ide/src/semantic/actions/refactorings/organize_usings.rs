//! Sort usings, remove unnecessary usings: the `using` directives of a file
//! put in order, or pruned to those a name in the file needs.
//!
//! Roslyn's Organize Usings, offered with the cursor on a directive. The
//! order is Roslyn's default: `global` directives, then namespaces, then
//! `using static`, then aliases; within each, `System` and its children
//! first (`dotnet_sort_system_directives_first = true`), then by name, part
//! by part, ignoring case. What is unnecessary is what
//! [`unnecessary_usings`](crate::semantic::usings::unnecessary_usings)
//! says, which keeps a directive whenever it cannot be sure.

use std::cmp::Ordering;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{has_comments, whole_lines};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let Some(directive) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| node.kind() == SyntaxKind::UsingDirective)
    else {
        return;
    };
    if let Some(edit) = sort(context, &directive) {
        found.push(context.local("Sort usings", ActionKind::Organize, None, vec![edit]));
    }
    let unnecessary = crate::semantic::usings::unnecessary_usings(context.view);
    if !unnecessary.is_empty() {
        let edits = removals(context, &unnecessary);
        found.push(context.local(
            "Remove unnecessary usings",
            ActionKind::Organize,
            None,
            edits,
        ));
    }
}

/// The run of directives `directive` is in: its siblings with nothing else
/// between them.
fn run_of(directive: &SyntaxNode) -> Vec<SyntaxNode> {
    let Some(parent) = directive.parent() else {
        return vec![directive.clone()];
    };
    let mut runs: Vec<Vec<SyntaxNode>> = vec![Vec::new()];
    for child in parent.children() {
        if child.kind() == SyntaxKind::UsingDirective {
            runs.last_mut().expect("one").push(child);
        } else if !runs.last().expect("one").is_empty() {
            runs.push(Vec::new());
        }
    }
    runs.into_iter()
        .find(|run| run.contains(directive))
        .unwrap_or_default()
}

/// How a directive sorts: its group, then its name.
fn key(directive: &SyntaxNode) -> (u8, bool, Vec<String>) {
    let group = if directive
        .child_token_of_kind(SyntaxKind::GlobalKeyword)
        .is_some()
    {
        0
    } else if directive.child_of_kind(SyntaxKind::NameEquals).is_some() {
        3
    } else if directive
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some()
    {
        2
    } else {
        1
    };
    let name = if group == 3 {
        directive
            .child_of_kind(SyntaxKind::NameEquals)
            .map(|alias| alias.text())
            .unwrap_or_default()
    } else {
        directive
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|name| name.text())
            .unwrap_or_default()
    };
    let name = name.trim().trim_start_matches("global::").to_string();
    // `dotnet_sort_system_directives_first = false` sorts `System` with
    // the rest.
    let system_first = crate::editorconfig::current_code_style()
        .system_directives_first
        .unwrap_or(true);
    let system = !system_first || name == "System" || name.starts_with("System.");
    let parts = name
        .split('.')
        .map(|part| part.trim().to_lowercase())
        .collect();
    (group, !system, parts)
}

fn compare(a: &SyntaxNode, b: &SyntaxNode) -> Ordering {
    key(a).cmp(&key(b)).then_with(|| a.text().cmp(&b.text()))
}

fn sort(context: &Context<'_, '_>, directive: &SyntaxNode) -> Option<TextEdit> {
    let run = run_of(directive);
    if run.len() < 2 {
        return None;
    }
    let mut sorted = run.clone();
    sorted.sort_by(compare);
    if sorted == run {
        return None;
    }
    // Comments between directives belong to one of them, and there is no
    // telling which.
    let span = TextSpan::from_bounds(run[0].span().start(), run[run.len() - 1].span().end());
    if run[1..].iter().any(|node| {
        node.first_token().is_some_and(|token| {
            token.leading_trivia().iter().any(|trivia| {
                !matches!(
                    trivia.kind(),
                    SyntaxKind::WhitespaceTrivia | SyntaxKind::EndOfLineTrivia
                )
            })
        })
    }) || run.iter().any(has_comments)
    {
        return None;
    }
    let separator = format!(
        "{}{}",
        context.newline(),
        context.indentation_at(run[0].span().start())
    );
    let text: Vec<String> = sorted.iter().map(SyntaxNode::text).collect();
    Some(TextEdit::new(span, text.join(&separator)))
}

/// Deletes the directives at `spans`, whole lines at a time; and when a
/// run of them goes entirely, the blank line that separated it from what
/// followed.
fn removals(context: &Context<'_, '_>, spans: &[TextSpan]) -> Vec<TextEdit> {
    let mut edits: Vec<TextSpan> = spans
        .iter()
        .map(|span| whole_lines(&context.text, *span))
        .collect();
    let root = context.view.syntax_root();
    for span in spans {
        let Some(node) = root.find_node(*span) else {
            continue;
        };
        let run = run_of(&node);
        let all_gone = run
            .iter()
            .all(|directive| spans.contains(&directive.span()));
        if all_gone && run.last().map(SyntaxNode::span) == Some(*span) {
            let Some(last) = edits.iter_mut().find(|edit| edit.contains_span(*span)) else {
                continue;
            };
            let rest = &context.text[last.end() as usize..];
            if let Some(end) = rest.find('\n')
                && rest[..end].trim().is_empty()
            {
                *last = TextSpan::from_bounds(last.start(), last.end() + end as u32 + 1);
            }
        }
    }
    edits.into_iter().map(TextEdit::delete).collect()
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn usings_sort_with_system_first() {
        let source = "using Zeta;\nusing static System.Math;\nusing $$Alpha;\nusing System.Collections.Generic;\nusing System;\n\nclass C { List<int> l; double d = Abs(1.0); }\nnamespace Zeta { class Z { } }\nnamespace Alpha { class A { } }\n";
        assert_eq!(
            apply(source, "Sort usings"),
            "using System;\nusing System.Collections.Generic;\nusing Alpha;\nusing Zeta;\nusing static System.Math;\n\nclass C { List<int> l; double d = Abs(1.0); }\nnamespace Zeta { class Z { } }\nnamespace Alpha { class A { } }\n"
        );
        refuses(
            "using $$System;\nusing System.Text;\nclass C { }\n",
            "Sort usings",
        );
    }

    #[test]
    fn unnecessary_usings_are_removed_with_their_lines() {
        let source = "using $$System;\nusing System.Collections.Generic;\n\nclass C\n{\n    List<int> items;\n}\n";
        assert_eq!(
            apply(source, "Remove unnecessary usings"),
            "using System.Collections.Generic;\n\nclass C\n{\n    List<int> items;\n}\n"
        );
        let all = "using $$System;\n\nclass C { }\n";
        assert_eq!(apply(all, "Remove unnecessary usings"), "class C { }\n");
    }
}
