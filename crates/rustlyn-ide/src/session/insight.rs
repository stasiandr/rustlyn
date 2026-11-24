//! The editor's end of inlay hints, the IDE analyzers and quick info: the
//! answers of [`Semantic`] put in the units the editor counts in.

use std::path::Path;

use rustlyn_diagnostics::Severity;
use rustlyn_text::TextSpan;

use super::{Change, FileDiagnostic, Location, Refusal, Session};
use crate::semantic::{InlayHintKind, InlayHintOptions, QuickInfo, Semantic};
use crate::utf16::Utf16Map;

/// An inlay hint, in UTF-16 code units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InlayHintRun {
    /// Where it is drawn: before the character here.
    pub position: u32,
    /// `count:` or `int`.
    pub label: String,
    pub kind: InlayHintKind,
    pub padding_left: bool,
    pub padding_right: bool,
    /// Where clicking it goes: the parameter, or the type.
    pub target: Option<Location>,
    /// What double-clicking it writes into the file asked about.
    pub replacement: Option<Change>,
}

/// Quick info, with the span it is about in UTF-16 code units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuickInfoAt {
    pub start: u32,
    pub length: u32,
    /// Its `span` is in bytes; `start` and `length` are the same place in
    /// the editor's units.
    pub info: QuickInfo,
}

impl Session {
    /// The inlay hints for `start..end` (UTF-16) of the file as the editor
    /// has it. Only the bodies in that range are bound, so ask for what is
    /// on screen.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn inlay_hints(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
        options: &InlayHintOptions,
    ) -> Result<Vec<InlayHintRun>, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let range = TextSpan::from_bounds(map.to_byte(start), map.to_byte(end.max(start)));
        let found = semantic
            .inlay_hints(path, range, text, options)
            .ok_or(Refusal::NotCompiled)?;
        Ok(found
            .into_iter()
            .map(|hint| {
                let target = hint.target.as_ref().and_then(|place| {
                    let found = crate::semantic::Found {
                        place: place.clone(),
                        kind: crate::outline::DeclarationKind::Field,
                        name: hint.label.trim_end_matches(':').to_string(),
                    };
                    self.place_location(&semantic, path, &here, text.is_some(), &found)
                });
                let replacement = hint.replacement.as_ref().map(|edit| {
                    let (start, length) = map.span(edit.span);
                    Change {
                        path: path.to_path_buf(),
                        start,
                        length,
                        text: edit.text.clone(),
                    }
                });
                InlayHintRun {
                    position: map.to_utf16(hint.position),
                    label: hint.label,
                    kind: hint.kind,
                    padding_left: hint.padding_left,
                    padding_right: hint.padding_right,
                    target,
                    replacement,
                }
            })
            .collect())
    }

    /// What the mouse is on at `offset`: Roslyn's quick info.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and where there is nothing to
    /// say: a literal, a keyword that stands for nothing, blank space.
    pub fn quick_info(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<QuickInfoAt, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let info = semantic
            .quick_info(path, map.to_byte(offset), text)
            .ok_or(Refusal::NotAName)?;
        let (start, length) = map.span(info.span);
        Ok(QuickInfoAt {
            start,
            length,
            info,
        })
    }
}

/// The IDE analyzers' diagnostics of a file, as the editor gets them with
/// the compiler's. A hidden one is left out unless it marks code as
/// unnecessary: the editor does not list it, but draws the code faded.
pub(super) fn analyzer_items(
    semantic: &Semantic,
    path: &Path,
    text: Option<&str>,
    map: &Utf16Map,
) -> Vec<FileDiagnostic> {
    semantic
        .analyzer_diagnostics(path, text)
        .unwrap_or_default()
        .into_iter()
        .filter(|diagnostic| diagnostic.severity != Severity::Hidden || diagnostic.unnecessary)
        .map(|diagnostic| {
            let (start, length) = map.span(diagnostic.span);
            FileDiagnostic {
                start,
                length,
                severity: match diagnostic.severity {
                    Severity::Hidden => 0,
                    Severity::Info => 1,
                    Severity::Warning => 2,
                    Severity::Error => 3,
                },
                code: diagnostic.id.to_string(),
                message: diagnostic.message,
                unnecessary: diagnostic.unnecessary,
                deprecated: diagnostic.deprecated,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    /// A compiled session over files written to a fresh directory.
    fn compiled(name: &str, files: &[(&str, &str)]) -> (Session, PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "rustlyn-insight-{name}-{}-{:?}",
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

    /// The UTF-16 offset of `marker` in `text`.
    fn utf16_at(text: &str, marker: &str) -> u32 {
        text[..text.find(marker).expect("the marker")]
            .encode_utf16()
            .count() as u32
    }

    #[test]
    fn hints_count_in_utf16_and_lead_to_their_declarations() {
        // `é` is two bytes and one UTF-16 unit: offsets after it differ.
        let pawn = "public class Pawn { public void Hit(int damage) { } }\n";
        let game = "// é\npublic class Game { void Run(Pawn p) { var name = \"é\"; p.Hit(3); } }\n";
        let (session, dir) = compiled("hints", &[("Pawn.cs", pawn), ("Game.cs", game)]);
        let path = dir.join("Game.cs");
        let end = game.encode_utf16().count() as u32;
        let hints = session
            .inlay_hints(&path, 0, end, None, &InlayHintOptions::default())
            .expect("hints");
        let labels: Vec<(&str, u32)> = hints
            .iter()
            .map(|hint| (hint.label.as_str(), hint.position))
            .collect();
        assert_eq!(
            labels,
            vec![
                ("string", utf16_at(game, "name =")),
                ("damage:", utf16_at(game, "3)"))
            ]
        );
        let target = hints[1].target.as_ref().expect("a target");
        assert_eq!(target.path, PathBuf::from("Pawn.cs"));
        assert_eq!(target.character, utf16_at(pawn, "damage"));
        let replacement = hints[0].replacement.as_ref().expect("a replacement");
        assert_eq!(replacement.start, utf16_at(game, "var"));
        assert_eq!(
            (replacement.length, replacement.text.as_str()),
            (3, "string")
        );
    }

    #[test]
    fn quick_info_says_where_it_is_in_utf16() {
        let text = "// é\npublic class Game { public int Score; int Twice() => Score * 2; }\n";
        let (session, dir) = compiled("quick", &[("Game.cs", text)]);
        let found = session
            .quick_info(dir.join("Game.cs"), utf16_at(text, "Score *"), None)
            .expect("quick info");
        assert_eq!(found.info.description, "(field) int Game.Score");
        assert_eq!((found.start, found.length), (utf16_at(text, "Score *"), 5));
        assert!(matches!(
            session.quick_info(dir.join("Game.cs"), utf16_at(text, "2;"), None),
            Err(Refusal::NotAName)
        ));
    }

    #[test]
    fn diagnostics_carry_the_analyzers_with_their_tags() {
        let text = "using System;\nusing System.Collections.Generic;\n\
                    public class Game {\n\
                      private int unused;\n\
                      [Obsolete(\"Use Run\")] public void Old() { }\n\
                      public int Run() { Old(); this.Old(); Console.WriteLine(1); return (int)1; }\n\
                    }\n";
        let (session, dir) = compiled("tags", &[("Game.cs", text)]);
        let found = session
            .diagnostics(dir.join("Game.cs"), None)
            .expect("diagnostics");
        let by = |code: &str| {
            found
                .items
                .iter()
                .find(|item| item.code == code)
                .unwrap_or_else(|| panic!("{code} in {:?}", found.items))
        };
        // Hidden, but unnecessary: there, with severity 0, to fade.
        let using = by("IDE0005");
        assert_eq!((using.severity, using.unnecessary), (0, true));
        assert_eq!(using.start, utf16_at(text, "using System.Collections"));
        let cast = by("IDE0004");
        assert_eq!((cast.severity, cast.unnecessary), (0, true));
        let unused = by("IDE0051");
        assert_eq!((unused.severity, unused.unnecessary), (1, true));
        let obsolete = by("CS0618");
        assert_eq!((obsolete.severity, obsolete.deprecated), (2, true));
        // One entry a use, though the compiler reports `this.Old` from
        // `this` and the analyzer strikes through `Old` alone.
        let uses: Vec<u32> = found
            .items
            .iter()
            .filter(|item| item.code == "CS0618")
            .map(|item| item.start)
            .collect();
        assert_eq!(
            uses,
            [utf16_at(text, "Old();"), utf16_at(text, "Old(); Console")]
        );
        // Sorted by place.
        assert!(
            found
                .items
                .windows(2)
                .all(|pair| pair[0].start <= pair[1].start)
        );
    }
}
