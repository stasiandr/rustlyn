//! What the light bulb offers: fixes for what is wrong at the cursor, and
//! rewrites of what is right.
//!
//! Roslyn splits these into code fixes, which answer a diagnostic, and
//! refactorings, which answer a selection. Both are the same thing to an
//! editor — a title and the edits it stands for — so they come back as one
//! list, each saying which it is. [`fixes`] holds the first kind and
//! [`refactorings`] the second; each is a list of providers asked in turn,
//! and a provider that has nothing to say about the place adds nothing.
//!
//! Every action is computed with its edits. An action whose edits cannot be
//! worked out is not offered: a title that does nothing when chosen is worse
//! than no title.

use std::path::{Path, PathBuf};

use rustlyn_diagnostics::Diagnostic;
use rustlyn_text::TextSpan;

use super::{Semantic, View};
use crate::edit::WorkspaceEdit;

mod analyzer_fixes;
mod fixes;
mod refactorings;
mod text;

// MARK: - .editorconfig: the code-style fixes, and fix all
mod configured;
pub use configured::FixAllScope;

pub use refactorings::{
    AddedParameter, ChangeParam, DialogKind, DialogMember, DialogMembers, ExtractedMember,
    SignatureParameter, SignatureTarget,
};

/// What sort of action it is: how an editor groups the list and which
/// icon it gives each entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ActionKind {
    /// Fixes a diagnostic.
    QuickFix = 0,
    /// Rewrites code without changing what it does.
    Refactor,
    /// Pulls code out into a new declaration: extract method, introduce
    /// local.
    Extract,
    /// Puts a declaration's code where it is used: inline temporary.
    Inline,
    /// Rewrites code in place: invert `if`, use `var`.
    Rewrite,
    /// Tidies the file as a whole: sort and remove `using`s.
    Organize,
    /// Writes code that was not there: implement interface, generate
    /// constructor.
    Generate,
}

/// One entry of the light bulb.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodeAction {
    pub title: String,
    pub kind: ActionKind,
    /// The diagnostic it fixes, `CS0246`, for a fix.
    pub fixes: Option<String>,
    /// What choosing it does. Spans are bytes of each file's text: the
    /// editor's text for the file asked about, the compiled text for any
    /// other.
    pub edit: WorkspaceEdit,
}

/// What a provider is asked about: the place, the file as the editor has it,
/// and what is wrong there.
#[derive(Debug)]
pub struct Context<'v, 'a> {
    pub view: &'v mut View<'a>,
    pub path: PathBuf,
    /// The file as it reads now.
    pub text: String,
    /// The selection, or the cursor as an empty span.
    pub span: TextSpan,
    /// Every diagnostic of the file that touches `span`.
    pub diagnostics: Vec<Diagnostic>,
}

impl Context<'_, '_> {
    /// An action whose edits are all to the file asked about.
    #[must_use]
    pub fn local(
        &self,
        title: impl Into<String>,
        kind: ActionKind,
        fixes: Option<&str>,
        edits: Vec<crate::edit::TextEdit>,
    ) -> CodeAction {
        CodeAction {
            title: title.into(),
            kind,
            fixes: fixes.map(str::to_owned),
            edit: WorkspaceEdit::single(self.path.clone(), edits),
        }
    }

    /// The diagnostics here with one of `codes`.
    pub fn diagnostics_with<'c>(
        &'c self,
        codes: &'c [&str],
    ) -> impl Iterator<Item = &'c Diagnostic> + 'c {
        self.diagnostics
            .iter()
            .filter(move |diagnostic| codes.contains(&diagnostic.code().to_string().as_str()))
    }
}

impl Semantic {
    /// Every action that applies at `span` of `path`.
    #[must_use]
    pub fn code_actions(
        &self,
        path: &Path,
        span: TextSpan,
        text: Option<&str>,
    ) -> Option<Vec<CodeAction>> {
        let current = match text {
            Some(text) => text.to_owned(),
            None => self.text(path)?.to_owned(),
        };
        let diagnostics: Vec<Diagnostic> = self
            .diagnostics(path, text)
            .unwrap_or_default()
            .into_iter()
            .filter(|diagnostic| {
                let at = diagnostic.span();
                at.overlaps_with(span)
                    || at.contains(span.start())
                    || span.contains(at.start())
                    || at.end() == span.start()
            })
            .collect();
        let mut view = self.view_of(path, text)?;
        let mut context = Context {
            view: &mut view,
            path: path.to_path_buf(),
            text: current,
            span,
            diagnostics,
        };
        let mut found = Vec::new();
        // The providers write code the way the file's `.editorconfig` asks,
        // unless the caller has already said which style to write in.
        let style = crate::editorconfig::ambient_code_style()
            .unwrap_or_else(|| crate::editorconfig::settings_for(path).code_style());
        crate::editorconfig::with_code_style(style, || {
            fixes::collect(&mut context, &mut found);
            refactorings::collect(&mut context, &mut found);
            analyzer_fixes::collect(&mut context, &mut found);
        });
        found.retain(|action| !action.edit.is_empty());
        let mut seen = std::collections::HashSet::new();
        found.retain(|action| seen.insert(action.title.clone()));
        Some(found)
    }
}
