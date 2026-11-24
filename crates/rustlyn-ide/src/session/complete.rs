//! The editor's end of completion: items put in the units the editor counts
//! in, the description of the item it has selected, and whether a typed
//! character should open the list at all.

use std::path::Path;

use rustlyn_text::TextSpan;

use super::{Refusal, Session};
use crate::semantic::{Completion, Documentation, completion_trigger};
use crate::utf16::Utf16Map;

/// A completion item with its edits and caret in UTF-16 code units rather
/// than bytes: the edits count in `map`'s text, the caret in the item's own
/// insert text.
pub(super) fn in_units(map: &Utf16Map, mut item: Completion) -> Completion {
    for edit in &mut item.additional_edits {
        let (start, length) = map.span(edit.span);
        edit.span = TextSpan::new(start, length);
    }
    if let Some(caret) = item.caret {
        let inserted = item.text_to_insert();
        let caret = (caret as usize).min(inserted.len());
        let units = inserted
            .get(..caret)
            .map_or(caret, |before| before.encode_utf16().count());
        item.caret = Some(units as u32);
    }
    item
}

impl Session {
    /// The documentation of the completion item labelled `label` at `offset`
    /// (UTF-16): what an editor shows beside the selected item.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, or when no item has the label.
    pub fn completion_description(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        label: &str,
    ) -> Result<Documentation, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        semantic
            .completion_description(path, byte, text, label)
            .ok_or(Refusal::NotAName)
    }

    /// Whether typing `typed` into `text`, which leaves the cursor at
    /// `offset` (UTF-16, after the character), should open the completion
    /// list. Syntax only: it answers before anything is compiled.
    #[must_use]
    pub fn completion_trigger(&self, text: &str, offset: u32, typed: char) -> bool {
        let byte = Utf16Map::new(text).to_byte(offset);
        completion_trigger(text, byte, typed)
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    fn compiled(name: &str, files: &[(&str, &str)]) -> (Session, PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "rustlyn-complete-{name}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a temporary directory");
        let paths: Vec<PathBuf> = files
            .iter()
            .map(|(name, text)| {
                let path = dir.join(name);
                std::fs::write(&path, text).expect("writing");
                path
            })
            .collect();
        let session = Session::new(&dir, None, Vec::new());
        session.reindex(&paths);
        session.compile(&paths);
        (session, dir)
    }

    fn units(text: &str, marker: &str) -> u32 {
        text[..text.find(marker).expect("marker")]
            .encode_utf16()
            .count() as u32
    }

    #[test]
    fn edits_and_the_caret_come_back_in_utf16() {
        let tools = "namespace Lib.Tools { public class Hammer { } }\n";
        let main = "// привет\nusing System;\nclass C {\n    void M() { }\n}\n";
        let (session, dir) = compiled("units", &[("Tools.cs", tools), ("Main.cs", main)]);
        let path = dir.join("Main.cs");
        let typed = main.replace("void M() { }", "void M() { Ham }");
        let list = session
            .completions(&path, units(&typed, "Ham }") + 3, Some(&typed))
            .expect("completed");
        let hammer = list
            .items
            .iter()
            .find(|item| item.label == "Hammer")
            .expect("the unimported type");
        // After `using System;`, counted in UTF-16: the Cyrillic comment is
        // two bytes a letter but one unit.
        assert_eq!(
            hammer.additional_edits[0].span.start(),
            units(&typed, "class C")
        );

        let with_override = main.replace("void M() { }", "override ");
        let list = session
            .completions(
                &path,
                units(&with_override, "override ") + 9,
                Some(&with_override),
            )
            .expect("completed");
        let to_string = list
            .items
            .iter()
            .find(|item| item.label == "ToString()")
            .expect("ToString");
        let caret = to_string.caret.expect("a caret") as usize;
        let inserted: Vec<u16> = to_string.text_to_insert().encode_utf16().collect();
        assert!(String::from_utf16_lossy(&inserted[caret..]).starts_with("return base.ToString()"));

        let description = session
            .completion_description(&path, units(&typed, "Ham }") + 3, Some(&typed), "Hammer")
            .expect("described");
        assert_eq!(description.signature, "class Lib.Tools.Hammer");
        assert_eq!(description.container, "Lib.Tools");
    }

    #[test]
    fn the_trigger_counts_in_utf16() {
        let session = Session::new(std::env::temp_dir(), None, Vec::new());
        let text = "// ё\nclass C { void M() { this.";
        assert!(session.completion_trigger(text, text.encode_utf16().count() as u32, '.'));
        let text = "// ё\nclass C { void M() { var s = \"ё.";
        assert!(!session.completion_trigger(text, text.encode_utf16().count() as u32, '.'));
    }
}
