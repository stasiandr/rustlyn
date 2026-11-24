//! Refactorings: rewrites of code that is not wrong.
//!
//! Each file here is one of Roslyn's refactoring providers, under the title
//! Roslyn gives it, asked about the selection (or the cursor) in turn. A
//! provider looks at the place, decides whether its rewrite applies, and if
//! it does, works out every edit before it offers anything: a provider that
//! cannot produce a correct edit offers nothing.

use super::{CodeAction, Context};

// MARK: - refactoring dialogs
mod change_signature;
mod collections;
mod declarations;
mod dialog_members;
mod extract_base_class;
mod extract_interface;
mod generate_overrides;
mod inline_method;
mod introduce_field;
mod introduce_parameter;
mod linq;
mod make_static;
mod members;
mod move_static_members;
mod null_checks;
mod patterns;
mod primary_constructor;
mod pull_members_up;
mod simplify;
mod sources;
mod tuples;
pub use change_signature::{AddedParameter, ChangeParam, SignatureParameter, SignatureTarget};
pub use dialog_members::{DialogKind, DialogMember, DialogMembers};
pub use extract_base_class::ExtractedMember;

mod add_braces;
mod arguments;
mod conditional;
mod encapsulate_field;
mod expression_body;
mod extract_method;
mod for_foreach;
mod generate;
mod inline_temporary;
mod introduce_variable;
mod invert_if;
mod move_type;
mod namespaces;
mod nested_if;
mod object_initializer;
mod organize_usings;
mod parameters;
mod properties;
mod strings;
#[cfg(test)]
mod sweep;
mod switch_expression;
mod use_var;

/// Asks every refactoring provider about the place.
pub(super) fn collect(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let providers: &[fn(&mut Context<'_, '_>, &mut Vec<CodeAction>)] = &[
        introduce_variable::offer,
        extract_method::offer,
        inline_temporary::offer,
        expression_body::offer,
        invert_if::offer,
        use_var::offer,
        add_braces::offer,
        strings::offer,
        for_foreach::offer,
        switch_expression::offer,
        conditional::offer,
        generate::offer,
        parameters::offer,
        encapsulate_field::offer,
        properties::offer,
        organize_usings::offer,
        move_type::offer,
        namespaces::offer,
        arguments::offer,
        nested_if::offer,
        object_initializer::offer,
        introduce_field::offer,
        tuples::offer,
        primary_constructor::offer,
        linq::offer,
        collections::offer,
        declarations::offer,
        simplify::offer,
        patterns::offer,
        null_checks::offer,
        make_static::offer,
        inline_method::offer,
        introduce_parameter::offer,
        move_static_members::offer,
        generate_overrides::offer,
        pull_members_up::offer,
        extract_base_class::offer,
        extract_interface::offer,
    ];
    for provider in providers {
        provider(context, found);
    }
}

/// Only the providers whose rewrites answer a code-style preference —
/// `var` or the type, an expression body or a block — for the fixes of the
/// analyzers an `.editorconfig` switches on.
pub(super) fn collect_style(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    use_var::offer(context, found);
    expression_body::offer(context, found);
}

/// An action whose edits may reach into other files: each edit with the
/// file it is to, spans in that file's text (the editor's for the file
/// asked about, the compiled one for the rest).
fn across_files(
    title: impl Into<String>,
    kind: super::ActionKind,
    edits: Vec<(std::path::PathBuf, crate::edit::TextEdit)>,
) -> CodeAction {
    let mut edit = crate::edit::WorkspaceEdit::default();
    for (path, one) in edits {
        edit.add(path, one);
    }
    CodeAction {
        title: title.into(),
        kind,
        fixes: None,
        edit,
    }
}

/// Every place in the project that names what the name at `offset` of the
/// file asked about declares or refers to.
fn references_at(
    context: &Context<'_, '_>,
    offset: u32,
) -> Vec<(std::path::PathBuf, rustlyn_text::TextSpan)> {
    context
        .view
        .project()
        .references(&context.path, offset, Some(&context.text))
        .map(|(_, found)| found)
        .unwrap_or_default()
}

#[cfg(test)]
pub(super) mod support {
    //! Asking the light bulb about marked-up source: `$$` is the cursor,
    //! `[|` and `|]` are the ends of a selection.

    use std::path::{Path, PathBuf};

    use rustlyn_text::TextSpan;

    use crate::semantic::CodeAction;
    use crate::semantic::tests::compile;

    /// The source without its markers, and the span they marked.
    pub(crate) fn unmark(source: &str) -> (String, TextSpan) {
        if let Some(at) = source.find("$$") {
            let text = source.replacen("$$", "", 1);
            return (text, TextSpan::new(at as u32, 0));
        }
        let start = source.find("[|").expect("a cursor or a selection");
        let text = source.replacen("[|", "", 1);
        let end = text.find("|]").expect("the end of the selection");
        let text = text.replacen("|]", "", 1);
        (text, TextSpan::from_bounds(start as u32, end as u32))
    }

    /// The actions offered in `/p/A.cs`, whose marked-up source is the first
    /// of `files`, and the texts every file had.
    pub(crate) fn actions_in(files: &[(&str, &str)]) -> (Vec<(PathBuf, String)>, Vec<CodeAction>) {
        let (first, span) = unmark(files[0].1);
        let mut plain: Vec<(String, String)> = vec![(files[0].0.to_string(), first)];
        plain.extend(
            files[1..]
                .iter()
                .map(|(name, text)| ((*name).to_string(), (*text).to_string())),
        );
        let borrowed: Vec<(&str, &str)> = plain
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect();
        let semantic = compile(&borrowed, false).expect("compiles");
        let path = PathBuf::from(format!("/p/{}", files[0].0));
        let actions = semantic
            .code_actions(&path, span, None)
            .expect("the file is in the project");
        let texts = plain
            .into_iter()
            .map(|(name, text)| (PathBuf::from(format!("/p/{name}")), text))
            .collect();
        (texts, actions)
    }

    /// The titles offered at the marked place of `source`.
    pub(crate) fn titles(source: &str) -> Vec<String> {
        actions_in(&[("A.cs", source)])
            .1
            .into_iter()
            .map(|action| action.title)
            .collect()
    }

    /// `source` after the action called `title` is applied.
    pub(crate) fn apply(source: &str, title: &str) -> String {
        let changed = apply_in(&[("A.cs", source)], title);
        changed
            .into_iter()
            .find(|(path, _)| path == Path::new("/p/A.cs"))
            .map(|(_, text)| text)
            .expect("the file")
    }

    /// Every file after the action called `title` is applied: those the
    /// action touches and those it does not, and any it creates.
    pub(crate) fn apply_in(files: &[(&str, &str)], title: &str) -> Vec<(PathBuf, String)> {
        let (texts, actions) = actions_in(files);
        let Some(action) = actions.iter().find(|action| action.title == title) else {
            let offered: Vec<&str> = actions.iter().map(|action| action.title.as_str()).collect();
            panic!("{title:?} is not offered; these are: {offered:?}");
        };
        let mut out = texts.clone();
        for file in &action.edit.files {
            let before = texts
                .iter()
                .find(|(path, _)| *path == file.path)
                .map(|(_, text)| text.clone());
            let after = crate::edit::apply(before.as_deref().unwrap_or_default(), &file.edits);
            match out.iter_mut().find(|(path, _)| *path == file.path) {
                Some(entry) => entry.1 = after,
                None => out.push((file.path.clone(), after)),
            }
        }
        out
    }

    /// Asserts nothing called `title` is offered at the marked place.
    pub(crate) fn refuses(source: &str, title: &str) {
        let offered = titles(source);
        assert!(
            !offered.iter().any(|offered| offered == title),
            "{title:?} should not be offered; these are: {offered:?}"
        );
    }
}
