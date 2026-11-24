//! Change 'Foo' to 'Food': a name that does not exist, and one that does
//! and is spelled almost the same.
//!
//! Roslyn's spell-check fix. The candidates are what completion would offer
//! in the same place — the members of the type left of the dot, or the
//! locals, members and types in scope — narrowed to what can stand there: a
//! type where a type goes, a method where one is called. Closeness is
//! Roslyn's `WordSimilarityChecker`, and at most three are offered, nearest
//! first.

use std::collections::HashSet;

use super::super::{ActionKind, CodeAction, Context};
use super::Unresolved;
use super::support::similarity;
use crate::edit::TextEdit;
use crate::semantic::{Completion, CompletionKind};

/// How many spellings are offered for one name.
const MOST: usize = 3;

pub(super) fn offer(
    context: &mut Context<'_, '_>,
    names: &[Unresolved],
    found: &mut Vec<CodeAction>,
) {
    for name in names {
        let candidates = candidates(context, name);
        let written = name.text();
        let mut near: Vec<(u32, String)> = Vec::new();
        let mut seen = HashSet::new();
        for candidate in candidates {
            let label = if name.attribute {
                candidate
                    .label
                    .strip_suffix("Attribute")
                    .filter(|stem| !stem.is_empty())
                    .map_or(candidate.label.clone(), str::to_owned)
            } else {
                candidate.label.clone()
            };
            if !seen.insert(label.clone()) {
                continue;
            }
            if let Some(distance) = similarity(written, &label) {
                near.push((distance, label));
            }
        }
        near.sort();
        for (_, label) in near.into_iter().take(MOST) {
            let edit = TextEdit::new(name.identifier.span(), label.clone());
            found.push(context.local(
                format!("Change '{written}' to '{label}'."),
                ActionKind::QuickFix,
                Some(&name.code),
                vec![edit],
            ));
        }
    }
}

/// What could be written where the name is.
fn candidates(context: &mut Context<'_, '_>, name: &Unresolved) -> Vec<Completion> {
    let mut items = Vec::new();
    let view = &mut *context.view;
    match &name.receiver {
        Some(receiver) => {
            let enclosing = view.enclosing_types(&name.name);
            let symbols = view.compilation().symbols();
            if let Some(symbol) = view.named(receiver) {
                if symbols.get(symbol).kind == rustlyn_semantics::SymbolKind::Namespace {
                    for &member in &symbols.get(symbol).members {
                        if view.offerable(member) {
                            view.push_symbol(member, 20, &mut items);
                        }
                    }
                } else {
                    view.push_members(symbol, Some(true), &enclosing, &mut items);
                }
            } else if let Some(symbol) = view.type_of(receiver).symbol() {
                view.push_members(symbol, Some(false), &enclosing, &mut items);
            }
        }
        None => view.scope_completions(name.identifier.span().start(), &mut items),
    }
    let invoked = name.invocation().is_some();
    items.retain(|item| {
        let is_type = matches!(
            item.kind,
            CompletionKind::Class
                | CompletionKind::Struct
                | CompletionKind::Interface
                | CompletionKind::Enum
                | CompletionKind::Delegate
                | CompletionKind::TypeParameter
                | CompletionKind::Namespace
        );
        match item.kind {
            CompletionKind::Keyword => false,
            _ if name.in_type => is_type,
            CompletionKind::Method => invoked,
            _ => !invoked || is_type,
        }
    });
    items
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    #[test]
    fn a_misspelled_local_is_corrected() {
        let source = "class C\n{\n    void M()\n    {\n        int count = 1;\n        System.Console.WriteLine($$cout);\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Change 'cout' to 'count'."),
            "class C\n{\n    void M()\n    {\n        int count = 1;\n        System.Console.WriteLine(count);\n    }\n}\n"
        );
    }

    #[test]
    fn a_misspelled_member_is_corrected() {
        let source = "class C\n{\n    void M()\n    {\n        System.Console.$$WriteLin(\"a\");\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Change 'WriteLin' to 'WriteLine'."),
            "class C\n{\n    void M()\n    {\n        System.Console.WriteLine(\"a\");\n    }\n}\n"
        );
    }

    #[test]
    fn a_misspelled_type_is_corrected_to_a_type() {
        let source = "class Widget { }\nclass C\n{\n    $$Widgte field;\n    int Widgter;\n}\n";
        let offered = titles(&[source]);
        assert!(
            offered.contains(&"Change 'Widgte' to 'Widget'.".to_string()),
            "{offered:?}"
        );
        assert!(
            !offered.contains(&"Change 'Widgte' to 'Widgter'.".to_string()),
            "{offered:?}"
        );
        assert_eq!(
            fix(&[source], "Change 'Widgte' to 'Widget'."),
            "class Widget { }\nclass C\n{\n    Widget field;\n    int Widgter;\n}\n"
        );
    }

    #[test]
    fn a_misspelled_instance_member_is_found_on_the_value() {
        let source = "class Box { public int Length; }\nclass C\n{\n    int M(Box box) => box.$$Lenght;\n}\n";
        assert_eq!(
            fix(&[source], "Change 'Lenght' to 'Length'."),
            "class Box { public int Length; }\nclass C\n{\n    int M(Box box) => box.Length;\n}\n"
        );
    }

    #[test]
    fn nothing_close_is_nothing_offered() {
        let source = "class C\n{\n    void M()\n    {\n        $$Frobnicate();\n    }\n}\n";
        assert!(
            !titles(&[source])
                .iter()
                .any(|title| title.starts_with("Change"))
        );
    }
}
