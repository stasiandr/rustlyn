//! Document highlights: everything in this file that the cursor's word is
//! about.
//!
//! On a name, that is every other name in the file bound to the same symbol,
//! each marked as the declaration, a write or a read — what an editor paints
//! in three shades when the cursor rests. On a keyword it is the construct
//! the keyword belongs to: the other keywords of an `if`/`else` chain, the
//! `break`s and `continue`s of a loop, the `return`s of a method. That half
//! is syntax only (see [`keyword_highlights`]) and so it answers before the
//! project is compiled.

mod keywords;

use std::collections::HashSet;
use std::path::Path;

use rustlyn_text::TextSpan;

pub use keywords::keyword_highlights;

use super::references::{ReferenceKind, same};
use super::{Resolved, Semantic};

/// What a highlighted span is, as Roslyn's `HighlightSpanKind` has it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum HighlightKind {
    /// A keyword of the construct under the cursor: nothing is declared,
    /// written or read.
    Text = 0,
    Definition = 1,
    Reference = 2,
    WrittenReference = 3,
}

/// One span to highlight, in bytes of the text asked about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Highlight {
    pub span: TextSpan,
    pub kind: HighlightKind,
}

impl Semantic {
    /// What to highlight in `path` for the cursor at `offset`: the keywords
    /// of the construct a keyword belongs to, or every occurrence in the
    /// file of the symbol a name refers to. `None` when the cursor is on
    /// neither.
    #[must_use]
    pub fn highlights(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<Vec<Highlight>> {
        let mut view = self.view_of(path, text)?;
        if let Some(spans) = keyword_highlights(&view.root, offset) {
            return Some(
                spans
                    .into_iter()
                    .map(|span| Highlight {
                        span,
                        kind: HighlightKind::Text,
                    })
                    .collect(),
            );
        }
        let token = view.name_token_at(offset)?;
        let target = view.resolve_use(&token)?;
        let name = match &target {
            Resolved::Symbol(symbol) => self.search_name(*symbol),
            Resolved::Local { name, .. } => name.clone(),
        };
        let creations = self.is_made_by_new(&target);
        let names: HashSet<String> = std::iter::once(name).collect();
        let found = view
            .uses_of(&names, creations)
            .into_iter()
            .filter(|found| {
                self.use_is_of(found, &target)
                    // Highlighting a type from one of its constructors
                    // should still light the type's name.
                    || same(self, &target, &found.resolved)
            })
            .map(|found| Highlight {
                span: found.span,
                kind: match found.kind {
                    ReferenceKind::Definition => HighlightKind::Definition,
                    ReferenceKind::Write => HighlightKind::WrittenReference,
                    ReferenceKind::Read => HighlightKind::Reference,
                },
            })
            .collect();
        Some(found)
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{at, compile};
    use super::*;

    fn highlights(text: &str, marker: &str, into: usize) -> Vec<(String, HighlightKind)> {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = semantic
            .highlights(Path::new("/p/C.cs"), at(text, marker, into), None)
            .unwrap_or_default();
        found
            .iter()
            .map(|highlight| {
                (
                    text[highlight.span.start() as usize..highlight.span.end() as usize]
                        .to_string(),
                    highlight.kind,
                )
            })
            .collect()
    }

    #[test]
    fn a_local_is_declared_written_and_read() {
        let text = "class C { int M(int start) { var total = start; total += 1; total++; return total * 2; } }\n";
        use HighlightKind::{Definition, Reference, WrittenReference};
        let found = highlights(text, "total =", 0);
        let kinds: Vec<HighlightKind> = found.iter().map(|(_, kind)| *kind).collect();
        assert_eq!(
            kinds,
            vec![Definition, WrittenReference, WrittenReference, Reference],
            "{found:?}"
        );
        // A parameter: its declaration, and a read.
        let found = highlights(text, "start;", 0);
        let kinds: Vec<HighlightKind> = found.iter().map(|(_, kind)| *kind).collect();
        assert_eq!(kinds, vec![Definition, Reference], "{found:?}");
    }

    #[test]
    fn a_field_through_this_and_out_arguments_are_writes() {
        let text = "class C {\n  int value;\n  void Set(int v) { this.value = v; Fill(out value); }\n  void Fill(out int x) { x = value; }\n}\n";
        use HighlightKind::{Definition, Reference, WrittenReference};
        let kinds: Vec<HighlightKind> = highlights(text, "value;", 0)
            .into_iter()
            .map(|(_, kind)| kind)
            .collect();
        assert_eq!(
            kinds,
            vec![Definition, WrittenReference, WrittenReference, Reference]
        );
    }

    #[test]
    fn a_type_lights_its_constructors_and_its_uses() {
        let text =
            "class Box { public Box() { } static Box Make() => new Box(); Box other = new(); }\n";
        let found = highlights(text, "Box {", 0);
        let spelled: Vec<&str> = found.iter().map(|(text, _)| text.as_str()).collect();
        assert_eq!(
            spelled,
            vec!["Box", "Box", "Box", "Box", "Box", "new"],
            "{found:?}"
        );
        assert_eq!(found[0].1, HighlightKind::Definition);
        assert_eq!(found[1].1, HighlightKind::Definition);
    }

    #[test]
    fn a_method_from_a_call_lights_its_overload_only() {
        let text = "class C { void Go(int a) { } void Go(string s) { } void T() { Go(1); Go(\"x\"); Go(2); } }\n";
        let found = highlights(text, "Go(1)", 0);
        assert_eq!(found.len(), 3, "{found:?}");
        assert_eq!(found[0].1, HighlightKind::Definition);
    }

    #[test]
    fn a_delegate_local_is_used_where_it_is_called() {
        let text = "using System;\nclass C { int M() { Func<int, int> twice = n => n * 2; return twice(3) + twice(4); } }\n";
        let found = highlights(text, "twice(4)", 0);
        let kinds: Vec<HighlightKind> = found.iter().map(|(_, kind)| *kind).collect();
        assert_eq!(
            kinds,
            vec![
                HighlightKind::Definition,
                HighlightKind::Reference,
                HighlightKind::Reference
            ]
        );
    }

    #[test]
    fn a_keyword_highlights_its_construct() {
        let text = "class C { int M(int x) { if (x > 0) { return 1; } else if (x < 0) { return -1; } else { return 0; } } }\n";
        let found = highlights(text, "else if", 0);
        let spelled: Vec<&str> = found.iter().map(|(text, _)| text.as_str()).collect();
        assert_eq!(spelled, vec!["if", "else if", "else"]);
        assert!(found.iter().all(|(_, kind)| *kind == HighlightKind::Text));
    }
}
