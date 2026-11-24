//! The refactorings Visual Studio drives through a dialog, in the editor's
//! units: change signature, extract interface, extract base class, pull
//! members up, generate overrides and move static members.
//!
//! Each dialog first asks what to show — [`Session::signature_info`] for
//! change signature, [`Session::dialog_members`] for the rest — and then
//! hands back what was chosen. The refactorings themselves are
//! [`Semantic`]'s; this turns offsets into bytes on the way in and edits
//! into UTF-16 on the way out. A refactoring that cannot be done is not an
//! error: the answer says why, and has no changes.

use std::path::Path;

use super::{Changes, Refusal, Session};
use crate::edit::WorkspaceEdit;
use crate::semantic::{
    ChangeParam, DialogKind, DialogMembers, ExtractedMember, Semantic, SignatureTarget,
};
use crate::utf16::Utf16Map;

/// A dialog's refactoring worked out, or the reason it cannot be.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RefactorResult {
    pub changes: Changes,
    /// Why nothing changed.
    pub refused: Option<String>,
}

impl Session {
    /// Runs a refactoring at `offset` (UTF-16) of `path` and turns its
    /// edits into the editor's units.
    fn refactor(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        work: impl FnOnce(&Semantic, &Path, u32, Option<&str>) -> Result<WorkspaceEdit, String>,
    ) -> Result<RefactorResult, Refusal> {
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        Ok(match work(&semantic, path, byte, text) {
            Ok(edit) => RefactorResult {
                changes: self.changes_of(Some(&semantic), path, &here, &edit),
                refused: None,
            },
            Err(why) => RefactorResult {
                refused: Some(why),
                ..RefactorResult::default()
            },
        })
    }

    /// The method or constructor at `offset` (UTF-16) of `path` and its
    /// parameters, for the change-signature dialog; or why its signature
    /// cannot change.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn signature_info(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Result<SignatureTarget, String>, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        Ok(semantic.change_signature_info(path, byte, text))
    }

    /// What the dialog of `kind` lists for the type at `offset` (UTF-16) of
    /// `path`; or why there is nothing to list.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn dialog_members(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        kind: DialogKind,
    ) -> Result<Result<DialogMembers, String>, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        Ok(semantic.dialog_members(path, byte, text, kind))
    }

    /// Changes the signature of the method or constructor at `offset` to
    /// `order`, with every declaration and call of it.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn change_signature(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        order: &[ChangeParam],
    ) -> Result<RefactorResult, Refusal> {
        self.refactor(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.change_signature(path, byte, text, order)
        })
    }

    /// Extracts an interface called `name` with the members called
    /// `members` from the type at `offset`, into a file of its own or not.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn extract_interface(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        name: &str,
        members: &[String],
        in_new_file: bool,
    ) -> Result<RefactorResult, Refusal> {
        self.refactor(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.extract_interface(path, byte, text, name, members, in_new_file)
        })
    }

    /// Extracts a base class called `name` from the class at `offset`.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn extract_base_class(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        name: &str,
        members: &[ExtractedMember],
        in_new_file: bool,
    ) -> Result<RefactorResult, Refusal> {
        self.refactor(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.extract_base_class(path, byte, text, name, members, in_new_file)
        })
    }

    /// Pulls members of the type at `offset` up to its base type called
    /// `destination`.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn pull_members_up(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        destination: &str,
        members: &[ExtractedMember],
    ) -> Result<RefactorResult, Refusal> {
        self.refactor(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.pull_members_up(path, byte, text, destination, members)
        })
    }

    /// Overrides the inherited members `members` in the type at `offset`.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn generate_overrides(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        members: &[String],
    ) -> Result<RefactorResult, Refusal> {
        self.refactor(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.generate_overrides(path, byte, text, members)
        })
    }

    /// Moves static members of the type at `offset` to the type called
    /// `destination`, which is made when it does not exist.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn move_static_members(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        destination: &str,
        members: &[String],
        in_new_file: bool,
    ) -> Result<RefactorResult, Refusal> {
        self.refactor(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.move_static_members(path, byte, text, destination, members, in_new_file)
        })
    }
}
