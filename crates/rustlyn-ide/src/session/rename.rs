//! Rename, in the editor's units.
//!
//! The renamer itself is [`Semantic::rename`](crate::semantic::Semantic):
//! this turns its byte spans into UTF-16 ones, and hands it the assemblies
//! the project was compiled against, which checking for conflicts compiles
//! the changed project with again.

use std::path::{Path, PathBuf};

use super::{Changes, Refusal, Session};
use crate::semantic::{Conflict, RenameOptions, Semantic};
use crate::utf16::Utf16Map;

/// Whether the name at the cursor can be renamed, and where it is.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RenameInfo {
    /// The name's UTF-16 offset and length: where the box the new name is
    /// typed into goes.
    pub start: u32,
    pub length: u32,
    /// The name as written, to fill the box with.
    pub text: String,
    /// What is being renamed, as one line.
    pub description: String,
    /// Why it cannot be renamed, when it cannot.
    pub refused: Option<String>,
}

/// A place a rename would break, in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenameConflict {
    pub path: PathBuf,
    /// UTF-16, in the same text the changes to that file count in.
    pub start: u32,
    pub length: u32,
    pub message: String,
    /// Whether the changes already put it right, by qualifying the name.
    pub resolved: bool,
}

/// A rename worked out, or the reason it cannot be.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RenameResult {
    pub changes: Changes,
    pub conflicts: Vec<RenameConflict>,
    /// Why nothing was renamed: not a name, or not a valid new one.
    pub refused: Option<String>,
}

impl Session {
    /// Whether what is at `offset` (UTF-16) of `path` can be renamed.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled. A name that cannot be renamed
    /// is not an error: the answer says why.
    pub fn prepare_rename(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<RenameInfo, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        if let Some(why) =
            self.declared_only_in_generated(&semantic, path, map.to_byte(offset), text)
        {
            return Ok(RenameInfo {
                refused: Some(why),
                ..RenameInfo::default()
            });
        }
        Ok(
            match semantic.prepare_rename(path, map.to_byte(offset), text) {
                Ok(target) => {
                    let start = map.to_utf16(target.span.start());
                    RenameInfo {
                        start,
                        length: map.to_utf16(target.span.end()) - start,
                        text: target.text,
                        description: target.description,
                        refused: None,
                    }
                }
                Err(why) => RenameInfo {
                    refused: Some(why),
                    ..RenameInfo::default()
                },
            },
        )
    }

    /// Renames what is at `offset` (UTF-16) of `path` to `new_name`: the
    /// changes to every file, the files to rename, and the conflicts.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled. A rename that cannot be done
    /// is not an error: the answer says why.
    pub fn rename(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        new_name: &str,
        text: Option<&str>,
        options: RenameOptions,
    ) -> Result<RenameResult, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        if let Some(why) = self.declared_only_in_generated(&semantic, path, byte, text) {
            return Ok(RenameResult {
                refused: Some(why),
                ..RenameResult::default()
            });
        }
        let references = self.read_references(&semantic.project().references);
        match semantic.rename(path, byte, new_name, text, options, &references) {
            Ok(renamed) => Ok(RenameResult {
                changes: self.changes_of(Some(&semantic), path, &here, &renamed.edit),
                conflicts: self.conflicts_of(&semantic, path, &here, &renamed.conflicts),
                refused: None,
            }),
            Err(why) => Ok(RenameResult {
                refused: Some(why),
                ..RenameResult::default()
            }),
        }
    }

    /// Why a name cannot be renamed when every declaration of it is in code
    /// a generator wrote: the generator would write the old name back on
    /// the next compilation. Roslyn refuses the same. A partial type with a
    /// part of its own in the project is renamed there, and the generated
    /// part is left to its generator.
    fn declared_only_in_generated(
        &self,
        semantic: &Semantic,
        path: &Path,
        byte: u32,
        text: Option<&str>,
    ) -> Option<String> {
        let (_, found) = semantic.definition(path, byte, text)?;
        let generated = self.generated_folders();
        let sources: Vec<&Path> = found
            .iter()
            .filter_map(|found| match &found.place {
                crate::semantic::Place::Source { path, .. } => Some(path.as_path()),
                crate::semantic::Place::Metadata { .. } => None,
            })
            .collect();
        (!sources.is_empty()
            && sources
                .iter()
                .all(|source| crate::project::is_generated(&generated, source)))
        .then(|| "it is declared in generated code".to_owned())
    }

    /// Conflicts in the editor's units: counted in `asked_text` for the file
    /// asked about, in the compiled text for any other.
    fn conflicts_of(
        &self,
        semantic: &Semantic,
        asked: &Path,
        asked_text: &str,
        conflicts: &[Conflict],
    ) -> Vec<RenameConflict> {
        conflicts
            .iter()
            .map(|conflict| {
                let owned;
                let text: &str = if conflict.path == asked {
                    asked_text
                } else {
                    owned = semantic
                        .text(&conflict.path)
                        .map(str::to_owned)
                        .unwrap_or_default();
                    &owned
                };
                let map = Utf16Map::new(text);
                let start = map.to_utf16(conflict.span.start());
                RenameConflict {
                    path: conflict.path.clone(),
                    start,
                    length: map.to_utf16(conflict.span.end()).saturating_sub(start),
                    message: conflict.message.clone(),
                    resolved: conflict.resolved,
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_rename_counts_in_utf16_across_files() {
        let dir = std::env::temp_dir().join(format!("rustlyn-rename-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("a directory");
        // `é` is two bytes and one UTF-16 unit: offsets after it differ.
        let pawn = "// é\nnamespace Game;\npublic class Pawn { public int Health; }\n";
        let use_text = "namespace Game;\nclass Use { int M(Pawn p) => p.Health; }\n";
        let pawn_path = dir.join("Pawn.cs");
        let use_path = dir.join("Use.cs");
        std::fs::write(&pawn_path, pawn).expect("written");
        std::fs::write(&use_path, use_text).expect("written");
        let session = Session::new(&dir, None, Vec::new());
        session.compile(&[pawn_path.clone(), use_path.clone()]);

        let health = pawn.find("Health").expect("there") as u32 - 1;
        let info = session
            .prepare_rename(&pawn_path, health, None)
            .expect("compiled");
        assert_eq!(info.refused, None);
        assert_eq!((info.start, info.length), (health, 6));
        assert_eq!(info.text, "Health");

        let result = session
            .rename(&pawn_path, health, "Life", None, RenameOptions::default())
            .expect("compiled");
        assert_eq!(result.refused, None);
        assert!(result.conflicts.is_empty(), "{:?}", result.conflicts);
        assert_eq!(result.changes.changes.len(), 2);
        let in_pawn = result
            .changes
            .changes
            .iter()
            .find(|change| change.path == pawn_path)
            .expect("the declaration");
        assert_eq!((in_pawn.start, in_pawn.length), (health, 6));
        assert_eq!(in_pawn.text, "Life");

        // The type, with its file.
        let class = pawn.find("Pawn {").expect("there") as u32 - 1;
        let result = session
            .rename(&pawn_path, class, "Piece", None, RenameOptions::default())
            .expect("compiled");
        assert_eq!(
            result.changes.renames,
            vec![(pawn_path.clone(), dir.join("Piece.cs"))]
        );

        let refused = session
            .rename(
                &pawn_path,
                class,
                "not a name",
                None,
                RenameOptions::default(),
            )
            .expect("compiled");
        assert!(refused.refused.is_some());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
