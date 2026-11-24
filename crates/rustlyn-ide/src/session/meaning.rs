//! The editor's end of semantic colouring, document highlights, the
//! detailed references list and code lens: the answers of
//! [`Semantic`](crate::semantic::Semantic) put in the units the editor
//! counts in.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rustlyn_text::TextSpan;

use super::{Refusal, Session};
use crate::semantic::{
    HighlightKind, ReferenceKind, SemanticClass, SemanticModifiers, keyword_highlights,
};
use crate::utf16::Utf16Map;

/// A name coloured by what it means, in UTF-16 code units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticRun {
    pub start: u32,
    pub length: u32,
    pub class: SemanticClass,
    pub modifiers: SemanticModifiers,
}

/// A span to highlight, in UTF-16 code units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HighlightRun {
    pub start: u32,
    pub length: u32,
    pub kind: HighlightKind,
}

/// One entry of a references list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceItem {
    /// Relative to the project root when it is under it.
    pub path: PathBuf,
    pub line: u32,
    /// UTF-16 code units from the start of the line.
    pub character: u32,
    pub length: u32,
    pub kind: ReferenceKind,
    /// The member or type it is in: `Arena.Fight`.
    pub container: String,
    /// Its line, trimmed.
    pub preview: String,
}

/// Every reference to a name, classified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DetailedUses {
    pub word: String,
    pub items: Vec<ReferenceItem>,
}

/// A reference count over a declaration's name, in UTF-16 code units.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LensRun {
    pub start: u32,
    pub length: u32,
    pub count: u32,
}

impl Session {
    /// The names in `start..end` (UTF-16) of the file as the editor has it,
    /// coloured by what they refer to. Only the bodies in that range are
    /// bound, so ask for what is on screen.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn semantic_tokens(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
    ) -> Result<Vec<SemanticRun>, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let range = TextSpan::from_bounds(map.to_byte(start), map.to_byte(end.max(start)));
        let found = semantic
            .semantic_tokens(path, range, text)
            .ok_or(Refusal::NotCompiled)?;
        Ok(found
            .into_iter()
            .map(|token| {
                let (start, length) = map.span(token.span);
                SemanticRun {
                    start,
                    length,
                    class: token.class,
                    modifiers: token.modifiers,
                }
            })
            .collect())
    }

    /// What to highlight for the cursor at `offset`: every occurrence in the
    /// file of the symbol under it, as declaration, write or read; or the
    /// keywords of the construct a keyword belongs to. The keywords need no
    /// compilation and are answered before there is one.
    ///
    /// # Errors
    ///
    /// Fails when the cursor is on neither a name nor such a keyword, and on
    /// a name before the project is compiled.
    pub fn document_highlights(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Vec<HighlightRun>, Refusal> {
        let path = path.as_ref();
        let Ok(semantic) = self.compiled(path) else {
            let here = self.plain_text_of(path, text).ok_or(Refusal::NotOpen)?;
            let tree = rustlyn_syntax::parse_with(
                rustlyn_text::SourceText::new(path.to_string_lossy(), here.as_str()),
                &self.options,
            );
            let map = Utf16Map::new(&here);
            let spans = keyword_highlights(&tree.root(), map.to_byte(offset))
                .ok_or(Refusal::NotCompiled)?;
            return Ok(spans
                .into_iter()
                .map(|span| {
                    let (start, length) = map.span(span);
                    HighlightRun {
                        start,
                        length,
                        kind: HighlightKind::Text,
                    }
                })
                .collect());
        };
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let found = semantic
            .highlights(path, map.to_byte(offset), text)
            .ok_or(Refusal::NotAName)?;
        Ok(found
            .into_iter()
            .map(|highlight| {
                let (start, length) = map.span(highlight.span);
                HighlightRun {
                    start,
                    length,
                    kind: highlight.kind,
                }
            })
            .collect())
    }

    /// Every reference to the name at `offset` across the project, each
    /// with whether it declares, writes or reads, the member it is in and
    /// its line. Overrides and implementations are included.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and off a name.
    pub fn references_detailed(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<DetailedUses, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        let (word, found) = semantic
            .references_detailed(path, byte, text)
            .ok_or(Refusal::NotAName)?;
        let mut files: HashMap<PathBuf, Lines> = HashMap::new();
        let items = found
            .into_iter()
            .map(|reference| {
                let lines = files.entry(reference.path.clone()).or_insert_with(|| {
                    let content = if reference.path == path {
                        here.clone()
                    } else {
                        self.text_of(&semantic, &reference.path, None)
                            .unwrap_or_default()
                    };
                    Lines::new(content)
                });
                let (line, character, length) = lines.position(reference.span);
                ReferenceItem {
                    path: reference
                        .path
                        .strip_prefix(&self.root)
                        .unwrap_or(&reference.path)
                        .to_path_buf(),
                    line,
                    character,
                    length,
                    kind: reference.kind,
                    container: reference.container,
                    preview: reference.preview,
                }
            })
            .collect();
        Ok(DetailedUses { word, items })
    }

    /// Where the code lens of the file goes — each declaration's name, in
    /// the order `code_lens` gives — without the counts: nothing but this
    /// file is looked at, so it is cheap enough to ask while the file opens.
    /// `count` is `u32::MAX`, not counted.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, as `code_lens` does.
    pub fn code_lens_places(
        &self,
        path: impl AsRef<Path>,
        text: Option<&str>,
    ) -> Result<Vec<LensRun>, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let found = semantic
            .lens_places(path, text)
            .ok_or(Refusal::NotCompiled)?;
        Ok(found
            .into_iter()
            .map(|span| {
                let (start, length) = map.span(span);
                LensRun {
                    start,
                    length,
                    count: u32::MAX,
                }
            })
            .collect())
    }

    /// How many references each type and member declared in the file has
    /// across the project, over its name: the numbers of a code lens.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn code_lens(
        &self,
        path: impl AsRef<Path>,
        text: Option<&str>,
    ) -> Result<Vec<LensRun>, Refusal> {
        let path = path.as_ref();
        let epoch = self.lens_epoch();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let found = semantic.reference_counts_until(path, text, &|| self.lens_cancelled(epoch));
        if self.lens_cancelled(epoch) {
            return Err(Refusal::Cancelled);
        }
        let found = found.ok_or(Refusal::NotCompiled)?;
        Ok(found
            .into_iter()
            .map(|lens| {
                let (start, length) = map.span(lens.span);
                LensRun {
                    start,
                    length,
                    count: u32::try_from(lens.count).unwrap_or(u32::MAX),
                }
            })
            .collect())
    }
}

/// A file's text with where each line starts, for turning many byte offsets
/// into lines and columns without counting from the top each time.
struct Lines {
    text: String,
    starts: Vec<usize>,
}

impl Lines {
    fn new(text: String) -> Self {
        let starts = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(at, _)| at + 1))
            .collect();
        Self { text, starts }
    }

    /// The line, the UTF-16 column and the UTF-16 length of a byte span.
    fn position(&self, span: TextSpan) -> (u32, u32, u32) {
        let start = (span.start() as usize).min(self.text.len());
        let end = (span.end() as usize).clamp(start, self.text.len());
        let line = self.starts.partition_point(|&at| at <= start) - 1;
        let utf16 = |from: usize, to: usize| {
            self.text
                .get(from..to)
                .map_or(0, |part| part.encode_utf16().count() as u32)
        };
        (
            line as u32,
            utf16(self.starts[line], start),
            utf16(start, end),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A directory of its own for one test.
    fn directory(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "rustlyn-meaning-{name}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a temporary directory");
        dir
    }

    /// A compiled session over files written to a fresh directory.
    fn compiled(name: &str, files: &[(&str, &str)]) -> (Session, PathBuf) {
        let dir = directory(name);
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

    /// UTF-16 offset of `marker` in `text`.
    fn units(text: &str, marker: &str) -> u32 {
        text[..text.find(marker).expect("the marker")]
            .encode_utf16()
            .count() as u32
    }

    #[test]
    fn everything_is_in_utf16_past_a_character_outside_the_bmp() {
        // The emoji is two UTF-16 units and four bytes: an answer in bytes
        // would be two units off.
        let pawn =
            "// \u{1F600}\nclass Pawn { public int Health; public void Hit() { Health -= 1; } }\n";
        let arena = "class Arena { void F(Pawn p) { p.Hit(); p.Health = 0; } }\n";
        let (session, dir) = compiled("utf16", &[("Pawn.cs", pawn), ("Arena.cs", arena)]);
        let path = dir.join("Pawn.cs");

        let runs = session
            .semantic_tokens(&path, 0, pawn.encode_utf16().count() as u32, None)
            .expect("classified");
        let health = runs
            .iter()
            .find(|run| run.start == units(pawn, "Health"))
            .expect("Health is classified where it is");
        assert_eq!(health.class, SemanticClass::FieldName);
        assert_eq!(health.length, 6);

        let highlights = session
            .document_highlights(&path, units(pawn, "Health -="), None)
            .expect("highlighted");
        assert_eq!(
            highlights
                .iter()
                .map(|run| (run.start, run.kind))
                .collect::<Vec<_>>(),
            vec![
                (units(pawn, "Health"), HighlightKind::Definition),
                (units(pawn, "Health -="), HighlightKind::WrittenReference),
            ]
        );

        let uses = session
            .references_detailed(&path, units(pawn, "Health"), None)
            .expect("found");
        assert_eq!(uses.word, "Health");
        assert_eq!(uses.items.len(), 3, "{:?}", uses.items);
        let in_arena = uses
            .items
            .iter()
            .find(|item| item.path == Path::new("Arena.cs"))
            .expect("the use in Arena.cs");
        assert_eq!(
            (in_arena.line, in_arena.character),
            (0, units(arena, "Health"))
        );
        assert_eq!(in_arena.kind, ReferenceKind::Write);
        assert_eq!(in_arena.container, "Arena.F");

        let places = session.code_lens_places(&path, None).expect("placed");
        // A count begun after a cancel is not affected by it.
        session.cancel_code_lens();
        let lenses = session.code_lens(&path, None).expect("counted");
        assert_eq!(
            lenses
                .iter()
                .map(|lens| (lens.start, lens.count))
                .collect::<Vec<_>>(),
            vec![
                (units(pawn, "Pawn"), 1),
                (units(pawn, "Health"), 2),
                (units(pawn, "Hit"), 1)
            ]
        );
        assert_eq!(
            places
                .iter()
                .map(|place| (place.start, place.length, place.count))
                .collect::<Vec<_>>(),
            lenses
                .iter()
                .map(|lens| (lens.start, lens.length, u32::MAX))
                .collect::<Vec<_>>(),
            "the places are where the counts go"
        );
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn keywords_are_highlighted_before_anything_is_compiled() {
        let text = "class C { void M() { while (true) { break; } } }\n";
        let dir = directory("keywords");
        let session = Session::new(&dir, None, Vec::new());
        let path = dir.join("C.cs");
        let found = session
            .document_highlights(&path, units(text, "while"), Some(text))
            .expect("keywords need no compilation");
        assert_eq!(found.len(), 2);
        assert_eq!(
            session.document_highlights(&path, units(text, "M()"), Some(text)),
            Err(Refusal::NotCompiled)
        );
        let _ = std::fs::remove_dir_all(dir);
    }
}
