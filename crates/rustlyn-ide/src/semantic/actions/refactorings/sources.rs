//! The project's files as a refactoring that reaches into all of them sees
//! them, and the context a refactoring driven by a dialog runs in.
//!
//! A light-bulb provider is handed a [`Context`] for the file the editor
//! asked about. The refactorings behind Visual Studio's dialogs — change
//! signature, extract interface, pull members up — are the same providers
//! asked again with the choices the dialog made, so they need the same
//! context outside the light bulb; [`with_context`] builds it the way
//! [`Semantic::code_actions`] does.
//!
//! Their edits reach every file that calls or implements what they change.
//! Each of those files is read the way [`crate::edit::WorkspaceEdit`] counts
//! it: the editor's text for the file asked about, the compiled text for
//! every other.

use std::path::{Path, PathBuf};

use rustlyn_syntax::{SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::Context;
use crate::semantic::{Semantic, View};

/// Runs `work` with a context for `span` of `path`, as the light bulb would
/// have one there, but with no diagnostics: a dialog's refactoring answers
/// a choice, not a squiggle.
pub(crate) fn with_context<R>(
    semantic: &Semantic,
    path: &Path,
    text: Option<&str>,
    span: TextSpan,
    work: impl FnOnce(&mut Context<'_, '_>) -> R,
) -> Option<R> {
    let current = match text {
        Some(text) => text.to_owned(),
        None => semantic.text(path)?.to_owned(),
    };
    let mut view = semantic.view_of(path, text)?;
    let mut context = Context {
        view: &mut view,
        path: path.to_path_buf(),
        text: current,
        span,
        diagnostics: Vec::new(),
    };
    Some(work(&mut context))
}

/// Every file of the project: its path, its text and its tree, with the
/// file asked about as the editor has it.
pub(super) fn project_files(context: &Context<'_, '_>) -> Vec<(PathBuf, String, SyntaxNode)> {
    let semantic = context.view.project();
    let mut files = vec![(
        context.path.clone(),
        context.text.clone(),
        context.view.syntax_root().clone(),
    )];
    let mut others: Vec<(PathBuf, String, SyntaxNode)> = semantic
        .paths
        .iter()
        .filter(|(_, path)| **path != context.path)
        .filter_map(|(&tree, path)| {
            let text = semantic.text(path)?.to_string();
            let root = semantic.compilation.trees().get(tree)?.root();
            Some((path.clone(), text, root))
        })
        .collect();
    others.sort_by(|a, b| a.0.cmp(&b.0));
    files.extend(others);
    files
}

/// The token whose span is exactly `span` in `path`: the name a reference
/// was found at. `None` for a place that is not a token of the code, such
/// as a `cref` inside a documentation comment.
pub(super) fn token_at(
    context: &Context<'_, '_>,
    path: &Path,
    span: TextSpan,
) -> Option<SyntaxToken> {
    let root = root_of(context, path)?;
    root.find_token(span.start())
        .filter(|token| token.span() == span)
}

/// The tree of `path`: the editor's for the file asked about.
pub(super) fn root_of(context: &Context<'_, '_>, path: &Path) -> Option<SyntaxNode> {
    if path == context.path {
        return Some(context.view.syntax_root().clone());
    }
    let semantic = context.view.project();
    let tree = semantic.tree_index(path)?;
    Some(semantic.compilation.trees().get(tree)?.root())
}

/// The text of `path`: the editor's for the file asked about.
pub(super) fn text_of(context: &Context<'_, '_>, path: &Path) -> Option<String> {
    if path == context.path {
        return Some(context.text.clone());
    }
    context.view.project().text(path).map(str::to_owned)
}

/// Runs `work` with a view of `path`: the context's own for the file asked
/// about, a fresh one of the compiled file for any other.
pub(super) fn with_view<R>(
    context: &mut Context<'_, '_>,
    path: &Path,
    work: impl FnOnce(&mut View<'_>) -> R,
) -> Option<R> {
    if path == context.path {
        return Some(work(context.view));
    }
    let semantic = context.view.project();
    let tree = semantic.tree_index(path)?;
    let mut view = semantic.view(tree)?;
    Some(work(&mut view))
}
