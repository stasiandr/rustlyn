//! Rename: a new name for something, everywhere it is called by its old one,
//! and nowhere else.
//!
//! Roslyn's renamer works in three steps, and so does this.
//!
//! * **What is being renamed.** The name at the cursor is bound, and the
//!   symbol followed to what actually has the name: a constructor's name is
//!   its type's, an override's is the member it overrides, and an
//!   implementation's is the interface member's. What has to be renamed with
//!   it is then gathered — the whole family of overrides and
//!   implementations, both declarations of a partial method, the property a
//!   record's parameter becomes — because renaming half of them changes what
//!   the program does, or stops it compiling.
//! * **Where it is called that.** Every token in the project spelled the old
//!   way is bound, and kept if it binds to one of those symbols; `[Obsolete]`
//!   counts for `ObsoleteAttribute`. Documentation comments are not code,
//!   but `<see cref="..."/>` and `<paramref name="..."/>` name code, and are
//!   bound as well. Comments and strings, on request, are only text, and are
//!   matched as whole words.
//! * **Whether the program still means the same.** A new name can collide:
//!   with another member of the type, with a local in an overlapping scope,
//!   or silently, by making a use bind to something else — a field renamed to
//!   the name of a local that is in scope where the field is used. The
//!   collisions of declarations are seen by looking; the silent ones only by
//!   doing. The edits are applied, the changed files compiled again, and every
//!   renamed use bound in the new compilation: each must still refer to what
//!   was renamed, and every other use of the new name must refer to what it
//!   did before. Where qualifying the name puts it right — `this.name`,
//!   `Type.name` — the qualification is added and the conflict reported as
//!   resolved; anything else is reported for the editor to show.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_semantics::{
    Binder, BoundSymbol, Diagnostics, MethodKind, Modifiers, SemanticModel, SymbolId, SymbolKind,
    Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken, reserved_keyword_kind, tokenize};
use rustlyn_text::{SourceText, TextSpan};

use super::{Resolved, Semantic, View, attribute_stem, contains_word, describe_symbol, parallel};
use crate::edit::{TextEdit, WorkspaceEdit};

/// What a rename does besides renaming the code: Roslyn's four check boxes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RenameOptions {
    /// Also rename the name where it stands as a whole word in a comment.
    pub in_comments: bool,
    /// Also rename it where it stands as a whole word in a string.
    pub in_strings: bool,
    /// Rename every overload of a method, not only the one at the cursor.
    pub overloads: bool,
    /// Rename the file a type is declared in when the file is named after it.
    pub file: bool,
}

impl Default for RenameOptions {
    fn default() -> Self {
        Self {
            in_comments: false,
            in_strings: false,
            overloads: false,
            file: true,
        }
    }
}

impl RenameOptions {
    pub const IN_COMMENTS: u32 = 1;
    pub const IN_STRINGS: u32 = 2;
    pub const OVERLOADS: u32 = 4;
    pub const FILE: u32 = 8;

    /// The options a set of the flags above stands for, as they cross the C
    /// boundary.
    #[must_use]
    pub const fn from_flags(flags: u32) -> Self {
        Self {
            in_comments: flags & Self::IN_COMMENTS != 0,
            in_strings: flags & Self::IN_STRINGS != 0,
            overloads: flags & Self::OVERLOADS != 0,
            file: flags & Self::FILE != 0,
        }
    }
}

/// What the cursor is on, when it can be renamed: where to put the box the
/// new name is typed into, and what to fill it with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RenameTarget {
    /// The name token, in bytes of the text asked about.
    pub span: TextSpan,
    /// The token as written: `@class` for an escaped keyword.
    pub text: String,
    /// What is being renamed, as one line: `class Game.Pawn`.
    pub description: String,
}

/// A place where the new name would change what the program means, or stop
/// it compiling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conflict {
    pub path: PathBuf,
    /// Bytes of the file's text: the editor's text for the file asked
    /// about, the compiled text for any other.
    pub span: TextSpan,
    pub message: String,
    /// Whether the edit already puts it right, by qualifying the name.
    pub resolved: bool,
}

/// A rename worked out: its edits, and what they would break.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Renamed {
    pub edit: WorkspaceEdit,
    pub conflicts: Vec<Conflict>,
}

/// What is being renamed, once the cursor has been followed to it.
#[derive(Clone, Debug)]
enum Subject {
    /// Symbols, all of which have to change name together.
    Symbols(Vec<SymbolId>),
    /// A local or a lambda's parameter, by its declaration in the file asked
    /// about.
    Local { tree: usize, span: TextSpan },
    /// A label, within the member that declares it.
    Label { owner: TextSpan },
    /// A `using X = ...;` alias, within the scope of its directive.
    Alias { scope: TextSpan, global: bool },
}

/// The subject, and what it is called now.
#[derive(Clone, Debug)]
struct Plan {
    subject: Subject,
    /// The name as the compiler reads it, without `@`.
    old: String,
    /// Whether the cursor was on `[Obsolete]` for `ObsoleteAttribute`: the
    /// name typed is then the short one too.
    short_form: bool,
    description: String,
}

/// One change to one file, as the renamer keeps it until the end.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Change {
    span: TextSpan,
    text: String,
    /// Where the renamed name starts inside `text`: after `this.` when the
    /// name had to be qualified.
    name_offset: u32,
    /// A use of the name in code, which the new compilation must still bind
    /// to what was renamed. Comments and strings are not checked.
    code: bool,
}

/// A symbol's identity across two compilations of the same project: where
/// it is declared, in the text after the rename.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Key {
    Source {
        path: PathBuf,
        start: u32,
        kind: SymbolKind,
    },
    Local {
        path: PathBuf,
        start: u32,
    },
    Elsewhere(String),
}

impl Semantic {
    /// Whether what is at `offset` of `path` can be renamed, and where its
    /// name is. `text` is the editor's copy when it has changed.
    ///
    /// # Errors
    ///
    /// Says why not: a keyword, something declared in an assembly, a name
    /// the compiler made up.
    pub fn prepare_rename(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Result<RenameTarget, String> {
        let mut view = self
            .view_of(path, text)
            .ok_or_else(|| "the file is not part of the compilation".to_string())?;
        let (token, plan) = self.subject_at(&mut view, offset)?;
        Ok(RenameTarget {
            span: token.span(),
            text: token.text().to_string(),
            description: plan.description,
        })
    }

    /// Renames what is at `offset` of `path` to `new_name`.
    ///
    /// The edits count in the editor's `text` for `path`, and in the
    /// compiled text for every other file. `references` are the assemblies
    /// the project was compiled against: checking for conflicts compiles the
    /// changed project again, which needs them.
    ///
    /// # Errors
    ///
    /// Says why it cannot be done: nothing to rename there, or a new name
    /// that is not an identifier.
    pub fn rename(
        &self,
        path: &Path,
        offset: u32,
        new_name: &str,
        text: Option<&str>,
        options: RenameOptions,
        references: &[(PathBuf, Arc<[u8]>)],
    ) -> Result<Renamed, String> {
        let mut view = self
            .view_of(path, text)
            .ok_or_else(|| "the file is not part of the compilation".to_string())?;
        let (_, plan) = self.subject_at(&mut view, offset)?;
        let (mut value, _) = identifier(new_name)?;
        let old = plan.old.clone();
        if plan.short_form && !value.ends_with("Attribute") {
            value.push_str("Attribute");
        }
        if value == old {
            return Ok(Renamed::default());
        }
        let written = escaped(&value);
        let targets = match &plan.subject {
            Subject::Symbols(targets) => self.expand(targets, options.overloads)?,
            _ => Vec::new(),
        };

        let mut changes: BTreeMap<PathBuf, Vec<Change>> = BTreeMap::new();
        let mut add = |path: &Path, found: Vec<Change>| {
            if !found.is_empty() {
                changes.entry(path.to_path_buf()).or_default().extend(found);
            }
        };
        match &plan.subject {
            Subject::Symbols(_) => {
                for (file, found) in self.symbol_changes(path, &mut view, &targets, &old, &value) {
                    add(&file, found);
                }
            }
            Subject::Local { .. } => {
                let found = uses_in(&mut view, &plan, &old, &[], &written, &value);
                add(path, found);
            }
            Subject::Label { owner } => {
                add(path, label_changes(&view.root, *owner, &old, &written));
            }
            Subject::Alias { scope, global } => {
                if *global {
                    for (file, found) in
                        self.alias_changes_everywhere(path, &mut view, &old, &written)
                    {
                        add(&file, found);
                    }
                } else {
                    add(path, alias_changes(&mut view, *scope, &old, &written));
                }
            }
        }

        // Comments and strings, in the files the name is used in.
        if options.in_comments || options.in_strings {
            let files: Vec<PathBuf> = changes.keys().cloned().collect();
            for file in files {
                let root = if file == path {
                    view.root.clone()
                } else {
                    match self.tree_index(&file).and_then(|tree| self.view(tree)) {
                        Some(other) => other.root,
                        None => continue,
                    }
                };
                let taken = changes.get(&file).cloned().unwrap_or_default();
                let found = text_changes(&root, &old, &value, options, &taken);
                changes.entry(file).or_default().extend(found);
            }
        }
        for found in changes.values_mut() {
            found.sort_by_key(|change| (change.span.start(), change.span.end()));
            found.dedup_by_key(|change| change.span);
        }

        // Conflicts: of declarations first, then of meaning.
        let mut conflicts = self.declaration_conflicts(path, &mut view, &plan, &targets, &value);
        if matches!(plan.subject, Subject::Symbols(_) | Subject::Local { .. }) {
            conflicts.extend(self.meaning_conflicts(
                path,
                text,
                &plan,
                &targets,
                &value,
                &mut changes,
                references,
            ));
        }

        let mut edit = WorkspaceEdit::default();
        for (file, found) in &changes {
            edit.add_all(
                file.clone(),
                found
                    .iter()
                    .map(|change| TextEdit::new(change.span, change.text.clone()))
                    .collect(),
            );
        }
        // A file named after the type follows it.
        if options.file
            && let Subject::Symbols(_) = &plan.subject
        {
            let symbols = self.compilation.symbols();
            for &target in &targets {
                if symbols.get(target).kind != SymbolKind::NamedType {
                    continue;
                }
                for location in &symbols.get(target).locations {
                    let Some(file) = self.path_of(location.tree) else {
                        continue;
                    };
                    if file
                        .file_stem()
                        .is_some_and(|stem| stem.to_string_lossy() == old)
                    {
                        let extension = file
                            .extension()
                            .map_or_else(String::new, |ext| format!(".{}", ext.to_string_lossy()));
                        let renamed = file.with_file_name(format!("{value}{extension}"));
                        let pair = (file.to_path_buf(), renamed);
                        if !edit.renames.contains(&pair) {
                            edit.renames.push(pair);
                        }
                    }
                }
            }
        }
        conflicts.sort_by(|a, b| {
            a.path
                .cmp(&b.path)
                .then(a.span.start().cmp(&b.span.start()))
        });
        conflicts.dedup();
        Ok(Renamed { edit, conflicts })
    }

    // MARK: - what is being renamed

    /// The token at `offset` and what renaming it renames.
    fn subject_at(&self, view: &mut View<'_>, offset: u32) -> Result<(SyntaxToken, Plan), String> {
        let Some(token) = view.name_token_at(offset) else {
            let here = view
                .root
                .find_token(offset)
                .filter(|token| token.span().contains(offset) || token.span().end() == offset);
            return Err(match here {
                Some(token) if reserved_keyword_kind(token.text()).is_some() => {
                    format!("`{}` is a keyword, and cannot be renamed", token.text())
                }
                _ => "there is nothing to rename here".to_string(),
            });
        };
        match token.kind() {
            SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword => {
                return Err(format!("`{}` cannot be renamed", token.text()));
            }
            SyntaxKind::IdentifierToken => {}
            _ => {
                return Err(format!(
                    "`{}` is a predefined type, and cannot be renamed",
                    token.text()
                ));
            }
        }
        let parent = token.parent().clone();
        let name = token.value_text().to_string();

        // A label is named by `L:` and `goto L`.
        if is_label_token(&token) {
            let owner = SemanticModel::body_owner(&parent)
                .map_or_else(|| view.root.span(), |owner| owner.span());
            return Ok((
                token,
                Plan {
                    subject: Subject::Label { owner },
                    old: name.clone(),
                    short_form: false,
                    description: format!("label {name}"),
                },
            ));
        }

        // `using X = ...;` and the uses of `X`.
        if let Some((scope, global)) = alias_at(view, &token) {
            return Ok((
                token,
                Plan {
                    subject: Subject::Alias { scope, global },
                    old: name.clone(),
                    short_form: false,
                    description: format!("alias {name}"),
                },
            ));
        }

        let resolved = resolve_name(view, &token)
            .ok_or_else(|| format!("`{name}` does not refer to anything the compiler knows"))?;

        // `var` is the type it stands for, which is not called `var`.
        if name == "var"
            && let Resolved::Symbol(symbol) = &resolved
            && self.compilation.symbols().get(*symbol).name != "var"
        {
            return Err("`var` is a keyword, and cannot be renamed".to_string());
        }

        match resolved {
            Resolved::Local {
                tree,
                span,
                name,
                ty,
                ..
            } => {
                let description = format!("{} {name}", ty.display(self.compilation.symbols()));
                Ok((
                    token,
                    Plan {
                        subject: Subject::Local { tree, span },
                        old: name,
                        short_form: false,
                        description,
                    },
                ))
            }
            Resolved::Symbol(symbol) => {
                let symbol = self.canonical(symbol);
                self.renameable(symbol)?;
                let symbols = self.compilation.symbols();
                let old = short_name(&symbols.get(symbol).name).to_string();
                let short_form = old != name
                    && attribute_stem(&old) == Some(name.as_str())
                    && symbols.get(symbol).kind == SymbolKind::NamedType;
                if old != name && !short_form {
                    return Err(format!("`{name}` does not name `{old}` here"));
                }
                let mut targets = vec![symbol];
                targets.extend(self.record_twin(symbol));
                Ok((
                    token,
                    Plan {
                        subject: Subject::Symbols(targets),
                        old,
                        short_form,
                        description: describe_symbol(&self.compilation, symbol),
                    },
                ))
            }
        }
    }

    /// What has the name a symbol is called by: a constructor's is its
    /// type's, an accessor's its property's.
    fn canonical(&self, symbol: SymbolId) -> SymbolId {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let Some(method) = found.as_method() else {
            return symbol;
        };
        match method.method_kind {
            MethodKind::Constructor | MethodKind::StaticConstructor | MethodKind::Destructor => {
                found.container.unwrap_or(symbol)
            }
            MethodKind::PropertyGet | MethodKind::PropertySet => found
                .container
                .and_then(|container| {
                    symbols
                        .get(container)
                        .members
                        .iter()
                        .copied()
                        .find(|&member| {
                            symbols.get(member).as_property().is_some_and(|property| {
                                property.getter == Some(symbol) || property.setter == Some(symbol)
                            }) || symbols.get(member).as_event().is_some_and(|event| {
                                event.adder == Some(symbol) || event.remover == Some(symbol)
                            })
                        })
                })
                .unwrap_or(symbol),
            _ => symbol,
        }
    }

    /// Whether every declaration of `symbol` is in the project's own files:
    /// the only places a rename can write to.
    fn in_source(&self, symbol: SymbolId) -> bool {
        let locations = &self.compilation.symbols().get(symbol).locations;
        !self.compilation.is_from_metadata(symbol)
            && !self.compilation.is_from_corlib(symbol)
            && !locations.is_empty()
            && locations
                .iter()
                .all(|location| self.path_of(location.tree).is_some())
    }

    /// Refuses what Roslyn refuses: what an assembly declares, what the
    /// compiler made up, and names that are not names.
    fn renameable(&self, symbol: SymbolId) -> Result<(), String> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let name = &found.name;
        if self.compilation.is_from_metadata(symbol) || self.compilation.is_from_corlib(symbol) {
            return Err(format!(
                "`{name}` is declared in an assembly, not in this project"
            ));
        }
        if !self.in_source(symbol) {
            return Err(format!("`{name}` is not declared in this project's files"));
        }
        if let Some(method) = found.as_method()
            && matches!(
                method.method_kind,
                MethodKind::Operator | MethodKind::Conversion | MethodKind::RecordSynthesized
            )
        {
            return Err(format!("`{name}` has no name of its own to rename"));
        }
        if let Some(property) = found.as_property()
            && property.is_indexer
        {
            return Err("an indexer has no name to rename".to_string());
        }
        if found.kind == SymbolKind::Namespace {
            // A namespace an assembly also has types in is not only this
            // project's to rename.
            let shared = found.members.iter().any(|&member| {
                self.compilation.is_from_metadata(member) || self.compilation.is_from_corlib(member)
            });
            if shared {
                return Err(format!(
                    "`{name}` is also a namespace of a referenced assembly"
                ));
            }
        }
        if let Some(named) = found.as_named_type()
            && named.anonymous
        {
            return Err("an anonymous type has no name".to_string());
        }
        Ok(())
    }

    /// A record's positional parameter and the property it becomes are one
    /// name: renaming either renames both.
    fn record_twin(&self, symbol: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let record = |ty: SymbolId| {
            let named = symbols.get(ty).as_named_type()?;
            let constructor = named.primary_constructor?;
            Some((ty, constructor))
        };
        match found.kind {
            SymbolKind::Parameter => {
                let method = found.container?;
                let ty = symbols.get(method).container?;
                let (ty, constructor) = record(ty)?;
                if constructor != method
                    || !matches!(
                        symbols.get(ty).type_kind(),
                        Some(TypeKind::Record | TypeKind::RecordStruct)
                    )
                {
                    return None;
                }
                symbols
                    .lookup(ty, &found.name)
                    .iter()
                    .copied()
                    .find(|&member| symbols.get(member).kind == SymbolKind::Property)
            }
            SymbolKind::Property => {
                let (ty, constructor) = record(found.container?)?;
                if !matches!(
                    symbols.get(ty).type_kind(),
                    Some(TypeKind::Record | TypeKind::RecordStruct)
                ) {
                    return None;
                }
                symbols
                    .get(constructor)
                    .as_method()?
                    .parameters
                    .iter()
                    .copied()
                    .find(|&parameter| symbols.get(parameter).name == found.name)
            }
            _ => None,
        }
    }

    /// Everything that has to be renamed with `targets`: overrides and what
    /// they override, implementations and what they implement, across the
    /// project; and, when asked, the other overloads.
    fn expand(&self, targets: &[SymbolId], overloads: bool) -> Result<Vec<SymbolId>, String> {
        let symbols = self.compilation.symbols();
        let binder = Binder::new(&self.compilation);
        let mut work: Vec<SymbolId> = targets.to_vec();
        if overloads {
            for &target in targets {
                let found = symbols.get(target);
                if found.kind == SymbolKind::Method
                    && let Some(container) = found.container
                {
                    work.extend(
                        symbols
                            .lookup(container, &found.name)
                            .iter()
                            .copied()
                            .filter(|&other| symbols.get(other).kind == SymbolKind::Method),
                    );
                }
            }
        }
        let mut family: Vec<SymbolId> = Vec::new();
        let mut hierarchy = Hierarchy::new(self, &binder);
        while let Some(member) = work.pop() {
            if family.contains(&member) {
                continue;
            }
            family.push(member);
            let found = symbols.get(member);
            if !matches!(
                found.kind,
                SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
            ) || found.modifiers.contains(Modifiers::STATIC)
                || found
                    .as_method()
                    .is_some_and(|method| method.method_kind != MethodKind::Ordinary)
            {
                continue;
            }
            let Some(container) = found.container else {
                continue;
            };
            let name = short_name(&found.name).to_string();
            let explicit = found.name.contains('.');
            let is_interface = symbols.get(container).type_kind() == Some(TypeKind::Interface);

            // Up: what it overrides, and what it implements.
            if found.modifiers.contains(Modifiers::OVERRIDE) {
                for base in hierarchy.base_classes(container) {
                    if let Some(overridden) = symbols
                        .lookup(base, &name)
                        .iter()
                        .copied()
                        .find(|&other| same_signature(&binder, member, other))
                    {
                        work.push(overridden);
                        break;
                    }
                }
            }
            for interface in hierarchy.interfaces(container) {
                if interface == container {
                    continue;
                }
                if explicit {
                    let written = found.name.rsplit_once('.').map_or("", |(before, _)| before);
                    let written = written.split('<').next().unwrap_or(written);
                    let written = written.rsplit('.').next().unwrap_or(written);
                    if symbols.get(interface).name != written {
                        continue;
                    }
                }
                work.extend(
                    symbols
                        .lookup(interface, &name)
                        .iter()
                        .copied()
                        .filter(|&other| same_signature(&binder, member, other)),
                );
            }

            // Down: what overrides it, and what implements it. Only what
            // is virtual, or an interface's, can have either.
            let overridable = is_interface
                || found.modifiers.contains(Modifiers::VIRTUAL)
                || found.modifiers.contains(Modifiers::ABSTRACT)
                || found.modifiers.contains(Modifiers::OVERRIDE);
            if !overridable {
                continue;
            }
            for derived in hierarchy.derived(container) {
                let mut candidates: Vec<SymbolId> = symbols.lookup(derived, &name).to_vec();
                candidates.extend(
                    symbols
                        .get(derived)
                        .members
                        .iter()
                        .copied()
                        .filter(|&other| {
                            let other_name = &symbols.get(other).name;
                            other_name.contains('.') && short_name(other_name) == name
                        }),
                );
                for other in candidates {
                    if !same_signature(&binder, member, other) {
                        continue;
                    }
                    let other_symbol = symbols.get(other);
                    let overrides = other_symbol.modifiers.contains(Modifiers::OVERRIDE);
                    if is_interface || overrides {
                        work.push(other);
                    }
                }
                // An implementation a base class provides without naming the
                // interface itself.
                if is_interface {
                    for base in hierarchy.base_classes(derived) {
                        if let Some(inherited) = symbols
                            .lookup(base, &name)
                            .iter()
                            .copied()
                            .find(|&other| same_signature(&binder, member, other))
                        {
                            work.push(inherited);
                            break;
                        }
                    }
                }
            }
        }
        for &member in &family {
            if !self.in_source(member) {
                let found = symbols.get(member);
                return Err(format!(
                    "`{}` overrides or implements `{}`, which is declared in an assembly",
                    short_name(&symbols.get(targets[0]).name),
                    symbols
                        .qualified_name(member)
                        .trim_end_matches(&found.name)
                        .to_string()
                        + &found.name
                ));
            }
        }
        family.sort();
        Ok(family)
    }

    // MARK: - where it is called that

    /// Every change a rename of `targets` makes, file by file: code, and
    /// documentation comments.
    fn symbol_changes(
        &self,
        asked: &Path,
        view: &mut View<'_>,
        targets: &[SymbolId],
        old: &str,
        value: &str,
    ) -> Vec<(PathBuf, Vec<Change>)> {
        let written = escaped(value);
        let plan = Plan {
            subject: Subject::Symbols(targets.to_vec()),
            old: old.to_string(),
            short_form: false,
            description: String::new(),
        };
        let asked_tree = view.tree;
        let stem = attribute_stem(old).map(str::to_owned);
        let mut out = Vec::new();
        let found = uses_in(view, &plan, old, targets, &written, value);
        let docs = doc_changes(view, targets, old, &written, value);
        out.push((asked.to_path_buf(), [found, docs].concat()));

        let candidates: Vec<usize> = self
            .paths
            .keys()
            .copied()
            .filter(|&tree| tree != asked_tree)
            .collect();
        let found = parallel(candidates.len(), |index| {
            let tree = candidates[index];
            let text = self
                .compilation
                .trees()
                .source(tree)
                .map(|source| source.text())?;
            if !contains_word(text, old)
                && !stem
                    .as_deref()
                    .is_some_and(|stem| contains_word(text, stem))
            {
                return None;
            }
            let mut other = self.view(tree)?;
            let found = uses_in(&mut other, &plan, old, targets, &written, value);
            let docs = doc_changes(&mut other, targets, old, &written, value);
            Some((self.paths[&tree].clone(), [found, docs].concat()))
        });
        out.extend(found.into_iter().flatten());
        out
    }

    /// The uses of a `global using X = ...;` alias, in every file.
    fn alias_changes_everywhere(
        &self,
        asked: &Path,
        view: &mut View<'_>,
        old: &str,
        written: &str,
    ) -> Vec<(PathBuf, Vec<Change>)> {
        let mut out = vec![(
            asked.to_path_buf(),
            alias_changes(view, view.root.span(), old, written),
        )];
        for (&tree, path) in &self.paths {
            if tree == view.tree {
                continue;
            }
            if let Some(mut other) = self.view(tree) {
                let scope = other.root.span();
                out.push((path.clone(), alias_changes(&mut other, scope, old, written)));
            }
        }
        out
    }

    // MARK: - conflicts of declarations

    /// Declarations the new name collides with: a member of the same type,
    /// a type in the same namespace, a local or parameter whose scope
    /// overlaps.
    fn declaration_conflicts(
        &self,
        asked: &Path,
        view: &mut View<'_>,
        plan: &Plan,
        targets: &[SymbolId],
        value: &str,
    ) -> Vec<Conflict> {
        let symbols = self.compilation.symbols();
        let binder = Binder::new(&self.compilation);
        let mut out = Vec::new();
        let mut reported = Vec::new();
        let mut report = |this: &Self, symbol: SymbolId, message: String| {
            for location in &this.compilation.symbols().get(symbol).locations {
                let Some(path) = this.path_of(location.tree) else {
                    continue;
                };
                let span = if path == asked {
                    match &view.speculation {
                        Some(speculation) => match speculation.unmap(location.span) {
                            Some(span) => span,
                            None => continue,
                        },
                        None => location.span,
                    }
                } else {
                    location.span
                };
                reported.push(Conflict {
                    path: path.to_path_buf(),
                    span,
                    message: message.clone(),
                    resolved: false,
                });
            }
        };
        match &plan.subject {
            Subject::Symbols(_) => {
                for &target in targets {
                    let found = symbols.get(target);
                    let Some(container) = found.container else {
                        continue;
                    };
                    let parent = symbols.get(container);
                    let clashes: Vec<SymbolId> = symbols
                        .lookup(container, value)
                        .iter()
                        .copied()
                        .filter(|other| !targets.contains(other))
                        .collect();
                    match found.kind {
                        SymbolKind::Namespace => {
                            for other in clashes {
                                if symbols.get(other).kind == SymbolKind::NamedType {
                                    report(
                                        self,
                                        target,
                                        format!(
                                            "`{}` already has a type named `{value}`",
                                            display_container(self, container)
                                        ),
                                    );
                                }
                            }
                        }
                        SymbolKind::NamedType => {
                            let arity = found.as_named_type().map_or(0, |named| named.arity);
                            for other in clashes {
                                let other_symbol = symbols.get(other);
                                let same_arity = other_symbol
                                    .as_named_type()
                                    .is_some_and(|named| named.arity == arity);
                                let clash = match parent.kind {
                                    SymbolKind::Namespace => {
                                        same_arity || other_symbol.kind == SymbolKind::Namespace
                                    }
                                    _ => true,
                                };
                                if clash {
                                    report(
                                        self,
                                        target,
                                        format!(
                                            "`{}` already contains a definition for `{value}`",
                                            display_container(self, container)
                                        ),
                                    );
                                }
                            }
                            if parent.kind == SymbolKind::NamedType && parent.name == value {
                                report(
                                    self,
                                    target,
                                    format!(
                                        "`{value}`: member names cannot be the same as their enclosing type"
                                    ),
                                );
                            }
                            let own_member = found.members.iter().any(|&member| {
                                let member = symbols.get(member);
                                member.name == value
                                    && member.kind != SymbolKind::TypeParameter
                                    && member
                                        .locations
                                        .iter()
                                        .any(|location| self.path_of(location.tree).is_some())
                            });
                            if own_member {
                                report(
                                    self,
                                    target,
                                    format!(
                                        "`{value}` has a member named `{value}`: member names cannot be the same as their enclosing type"
                                    ),
                                );
                            }
                        }
                        SymbolKind::Method
                        | SymbolKind::Property
                        | SymbolKind::Field
                        | SymbolKind::Event
                            if parent.kind == SymbolKind::NamedType =>
                        {
                            let local_function = found.as_method().is_some_and(|method| {
                                method.method_kind == MethodKind::LocalFunction
                            });
                            if local_function {
                                continue;
                            }
                            for other in clashes {
                                let other_symbol = symbols.get(other);
                                if other_symbol.kind == SymbolKind::TypeParameter {
                                    continue;
                                }
                                let both_methods = found.kind == SymbolKind::Method
                                    && other_symbol.kind == SymbolKind::Method;
                                if both_methods && !same_parameter_types(&binder, target, other) {
                                    continue;
                                }
                                report(
                                    self,
                                    target,
                                    format!(
                                        "`{}` already contains a definition for `{value}`",
                                        display_container(self, container)
                                    ),
                                );
                            }
                            if parent.name == value {
                                report(
                                    self,
                                    target,
                                    format!(
                                        "`{value}`: member names cannot be the same as their enclosing type"
                                    ),
                                );
                            }
                        }
                        SymbolKind::TypeParameter => {
                            let siblings = parent
                                .as_method()
                                .map(|method| method.type_parameters.clone())
                                .or_else(|| {
                                    parent
                                        .as_named_type()
                                        .map(|named| named.type_parameters.clone())
                                })
                                .unwrap_or_default();
                            if siblings
                                .iter()
                                .any(|&other| other != target && symbols.get(other).name == value)
                            {
                                report(
                                    self,
                                    target,
                                    format!("there is already a type parameter named `{value}`"),
                                );
                            }
                        }
                        SymbolKind::Parameter => {
                            let siblings = parent
                                .as_method()
                                .map(|method| method.parameters.clone())
                                .or_else(|| {
                                    parent
                                        .as_property()
                                        .map(|property| property.parameters.clone())
                                })
                                .unwrap_or_default();
                            if siblings
                                .iter()
                                .any(|&other| other != target && symbols.get(other).name == value)
                            {
                                report(
                                    self,
                                    target,
                                    format!("there is already a parameter named `{value}`"),
                                );
                            }
                        }
                        _ => {}
                    }
                    // Parameters and local functions: the locals their scope
                    // overlaps with, in the file asked about.
                    let scoped = found.kind == SymbolKind::Parameter
                        || found
                            .as_method()
                            .is_some_and(|method| method.method_kind == MethodKind::LocalFunction);
                    if scoped && let Some(token) = declaration_token(self, view, target) {
                        for span in scope_clashes(&token, value) {
                            out.push(Conflict {
                                path: asked.to_path_buf(),
                                span,
                                message: format!(
                                    "a local or parameter named `{value}` is already in scope here"
                                ),
                                resolved: false,
                            });
                        }
                    }
                }
            }
            Subject::Local { span, .. } => {
                if let Some(token) = view
                    .root
                    .find_token(span.start())
                    .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                {
                    for clash in scope_clashes(&token, value) {
                        out.push(Conflict {
                            path: asked.to_path_buf(),
                            span: clash,
                            message: format!(
                                "a local or parameter named `{value}` is already in scope here"
                            ),
                            resolved: false,
                        });
                    }
                }
            }
            Subject::Label { owner } => {
                if let Some(owner) = view.root.find_node(*owner) {
                    for token in owner.descendant_tokens() {
                        if token.value_text() == value
                            && token.parent().kind() == SyntaxKind::LabeledStatement
                        {
                            out.push(Conflict {
                                path: asked.to_path_buf(),
                                span: token.span(),
                                message: format!("there is already a label named `{value}`"),
                                resolved: false,
                            });
                        }
                    }
                }
            }
            Subject::Alias { scope, .. } => {
                if let Some(scope) = view.root.find_node(*scope) {
                    for directive in scope
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::UsingDirective)
                    {
                        if let Some(alias) = alias_name(&directive)
                            && alias.value_text() == value
                        {
                            out.push(Conflict {
                                path: asked.to_path_buf(),
                                span: alias.span(),
                                message: format!("there is already an alias named `{value}`"),
                                resolved: false,
                            });
                        }
                    }
                }
            }
        }
        out.extend(reported);
        out
    }

    // MARK: - conflicts of meaning

    /// The project compiled again with the edits applied, and every use of
    /// the old and the new name bound in it: what binds to something else
    /// than before is a conflict. Uses that qualifying puts right are
    /// qualified, and the result checked once more.
    #[allow(clippy::too_many_arguments)]
    fn meaning_conflicts(
        &self,
        asked: &Path,
        text: Option<&str>,
        plan: &Plan,
        targets: &[SymbolId],
        value: &str,
        changes: &mut BTreeMap<PathBuf, Vec<Change>>,
        references: &[(PathBuf, Arc<[u8]>)],
    ) -> Vec<Conflict> {
        let first = self.rebind(asked, text, plan, targets, value, changes, references, true);
        let Some(first) = first else {
            return Vec::new();
        };
        let resolved: Vec<Conflict> = first.iter().filter(|c| c.resolved).cloned().collect();
        if resolved.is_empty() {
            return first;
        }
        // Qualified: see whether that did it.
        let second = self
            .rebind(
                asked, text, plan, targets, value, changes, references, false,
            )
            .unwrap_or_default();
        let mut out: Vec<Conflict> = resolved
            .into_iter()
            .filter(|conflict| {
                !second
                    .iter()
                    .any(|other| other.path == conflict.path && other.span == conflict.span)
            })
            .collect();
        out.extend(second);
        out
    }

    /// One round of the check: compile the changed project, bind, compare.
    /// With `qualify`, conflicts that a qualification resolves are resolved
    /// by adding it to `changes`.
    #[allow(clippy::too_many_arguments)]
    fn rebind(
        &self,
        asked: &Path,
        text: Option<&str>,
        plan: &Plan,
        targets: &[SymbolId],
        value: &str,
        changes: &mut BTreeMap<PathBuf, Vec<Change>>,
        references: &[(PathBuf, Arc<[u8]>)],
        qualify: bool,
    ) -> Option<Vec<Conflict>> {
        let asked_text = match text {
            Some(text) => text.to_string(),
            None => self.text(asked)?.to_string(),
        };
        // The project as it would read.
        let mut texts: HashMap<PathBuf, String> = HashMap::new();
        for (path, found) in changes.iter() {
            let before = if path == asked {
                asked_text.clone()
            } else {
                self.text(path)?.to_string()
            };
            texts.insert(path.clone(), apply_changes(&before, found));
        }
        if !texts.contains_key(asked) && text.is_some() {
            texts.insert(asked.to_path_buf(), asked_text.clone());
        }
        let mut ordered: Vec<(usize, PathBuf)> = self
            .paths
            .iter()
            .map(|(&tree, path)| (tree, path.clone()))
            .collect();
        ordered.sort();
        let sources: Vec<(PathBuf, String)> = ordered
            .into_iter()
            .filter_map(|(_, path)| {
                let text = match texts.get(&path) {
                    Some(text) => text.clone(),
                    None => self.text(&path)?.to_string(),
                };
                Some((path, text))
            })
            .collect();
        let after = Semantic::build(self.project.clone(), sources, references, Some(self));

        let empty = Vec::new();
        let old_view = |path: &Path| -> Option<View<'_>> {
            if path == asked {
                self.view_of(asked, text)
            } else {
                self.view(self.tree_index(path)?)
            }
        };
        let old_key =
            |view: &View<'_>, resolved: &Resolved, changes: &BTreeMap<PathBuf, Vec<Change>>| {
                self.key_of(resolved, &|path: &Path, span: TextSpan, local: bool| {
                    let span = if path == asked && !local {
                        match &view.speculation {
                            Some(speculation) => speculation.unmap(span)?,
                            None => span,
                        }
                    } else {
                        span
                    };
                    Some(map_start(changes.get(path).unwrap_or(&empty), span.start()))
                })
            };
        let new_key = |resolved: &Resolved| {
            after.key_of(resolved, &|_: &Path, span: TextSpan, _| Some(span.start()))
        };

        let mut wanted: HashSet<Key> = HashSet::new();
        match &plan.subject {
            Subject::Symbols(_) => {
                let view = old_view(asked)?;
                for &target in targets {
                    if let Some(key) = old_key(&view, &Resolved::Symbol(target), changes) {
                        wanted.insert(key);
                    }
                }
            }
            Subject::Local { tree, span } => {
                let view = old_view(asked)?;
                let local = Resolved::Local {
                    tree: *tree,
                    span: *span,
                    name: plan.old.clone(),
                    ty: Type::Error,
                };
                wanted.extend(old_key(&view, &local, changes));
            }
            _ => return None,
        }
        let description = &plan.description;
        let mut conflicts = Vec::new();
        let mut qualified: Vec<(PathBuf, usize, String)> = Vec::new();
        let mut inserted: Vec<(PathBuf, Change)> = Vec::new();

        // Every renamed use must still mean what was renamed.
        for (path, found) in changes.iter() {
            let Some(tree) = after.tree_index(path) else {
                continue;
            };
            let Some(mut new_view) = after.view(tree) else {
                continue;
            };
            let mut before = old_view(path);
            for (index, change) in found.iter().enumerate() {
                if !change.code {
                    continue;
                }
                let start = map_start(found, change.span.start());
                let now = new_view
                    .name_token_at(start)
                    .and_then(|token| resolve_name(&mut new_view, &token));
                let key = now.as_ref().and_then(new_key);
                if key.as_ref().is_some_and(|key| wanted.contains(key)) {
                    continue;
                }
                let what = match &now {
                    Some(resolved) => after.describe(resolved),
                    None => "nothing".to_string(),
                };
                let mut conflict = Conflict {
                    path: path.clone(),
                    span: change.span,
                    message: format!(
                        "`{value}` here would refer to {what} instead of `{description}`"
                    ),
                    resolved: false,
                };
                // `this.value` or `Type.value` binds to the member whatever
                // is in scope.
                if qualify
                    && let Subject::Symbols(_) = &plan.subject
                    && let Some(view) = before.as_mut()
                    && let Some(token) = view
                        .root
                        .find_token(change.span.start())
                        .filter(|token| token.span() == change.span)
                    && is_simple_name(&token)
                    && let Some(Resolved::Symbol(symbol)) = resolve_name(view, &token)
                    && let Some(prefix) = self.qualifier(symbol)
                {
                    qualified.push((path.clone(), index, prefix));
                    conflict.resolved = true;
                }
                conflicts.push(conflict);
            }
        }

        // Every other use of the new name must mean what it meant.
        let spelled: Vec<PathBuf> = self
            .paths
            .values()
            .filter(|path| {
                texts
                    .get(*path)
                    .map(String::as_str)
                    .or_else(|| self.text(path))
                    .is_some_and(|text| contains_word(text, value))
            })
            .cloned()
            .collect();
        for path in spelled {
            let (Some(mut view), Some(tree)) = (old_view(&path), after.tree_index(&path)) else {
                continue;
            };
            let Some(mut new_view) = after.view(tree) else {
                continue;
            };
            let found = changes.get(&path).cloned().unwrap_or_default();
            let tokens: Vec<SyntaxToken> = view
                .root
                .descendant_tokens()
                .filter(|token| {
                    token.kind() == SyntaxKind::IdentifierToken && token.value_text() == value
                })
                .collect();
            for token in tokens {
                if found
                    .iter()
                    .any(|change| change.span.contains_span(token.span()))
                {
                    continue;
                }
                let Some(was) = resolve_name(&mut view, &token) else {
                    continue;
                };
                let Some(was_key) = old_key(&view, &was, changes) else {
                    continue;
                };
                if wanted.contains(&was_key) {
                    continue;
                }
                let start = map_start(&found, token.span().start());
                let now = new_view
                    .name_token_at(start)
                    .and_then(|token| resolve_name(&mut new_view, &token));
                let Some(now_key) = now.as_ref().and_then(new_key) else {
                    continue;
                };
                if !wanted.contains(&now_key) {
                    continue;
                }
                let mut conflict = Conflict {
                    path: path.clone(),
                    span: token.span(),
                    message: format!(
                        "`{value}` here refers to {}, and would refer to `{description}` after the rename",
                        self.describe(&was)
                    ),
                    resolved: false,
                };
                if qualify
                    && is_simple_name(&token)
                    && let Resolved::Symbol(symbol) = was
                    && let Some(prefix) = self.qualifier(symbol)
                {
                    conflict.resolved = true;
                    inserted.push((
                        path.clone(),
                        Change {
                            span: TextSpan::new(token.span().start(), 0),
                            name_offset: prefix.len() as u32,
                            text: prefix,
                            code: false,
                        },
                    ));
                }
                conflicts.push(conflict);
            }
        }

        for (path, index, prefix) in qualified {
            if let Some(change) = changes
                .get_mut(&path)
                .and_then(|found| found.get_mut(index))
            {
                change.text = format!("{prefix}{}", change.text);
                change.name_offset = prefix.len() as u32;
            }
        }
        for (path, change) in inserted {
            let found = changes.entry(path).or_default();
            found.push(change);
            found.sort_by_key(|change| (change.span.start(), change.span.end()));
        }
        Some(conflicts)
    }

    /// A symbol's identity, by where it is declared. `place` turns a span
    /// of this compilation into an offset of the text after the rename;
    /// its third argument says the span is a local's, which is already in
    /// the editor's text.
    fn key_of(
        &self,
        resolved: &Resolved,
        place: &dyn Fn(&Path, TextSpan, bool) -> Option<u32>,
    ) -> Option<Key> {
        match resolved {
            Resolved::Local { tree, span, .. } => {
                let path = self.path_of(*tree)?;
                Some(Key::Local {
                    path: path.to_path_buf(),
                    start: place(path, *span, true)?,
                })
            }
            Resolved::Symbol(symbol) => {
                let symbol = self.canonical(*symbol);
                let symbols = self.compilation.symbols();
                let found = symbols.get(symbol);
                if self.in_source(symbol) {
                    let location = found.locations.first()?;
                    let path = self.path_of(location.tree)?;
                    Some(Key::Source {
                        path: path.to_path_buf(),
                        start: place(path, location.span, false)?,
                        kind: found.kind,
                    })
                } else {
                    Some(Key::Elsewhere(format!(
                        "{:?} {}",
                        found.kind,
                        symbols.qualified_name(symbol)
                    )))
                }
            }
        }
    }

    /// What to put in front of a use of `symbol` so that it binds to it
    /// whatever else is in scope: `this.` for an instance member,
    /// `Type.` for a static one, `global::Namespace.` for a type.
    fn qualifier(&self, symbol: SymbolId) -> Option<String> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let container = found.container?;
        match found.kind {
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Event | SymbolKind::Method => {
                if found
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::LocalFunction)
                    || symbols.get(container).kind != SymbolKind::NamedType
                {
                    return None;
                }
                let is_static = found.modifiers.contains(Modifiers::STATIC)
                    || found.modifiers.contains(Modifiers::CONST);
                if is_static {
                    Some(format!("{}.", escaped(&symbols.get(container).name)))
                } else {
                    Some("this.".to_string())
                }
            }
            SymbolKind::NamedType => {
                let parent = symbols.get(container);
                if parent.kind == SymbolKind::Namespace && parent.name.is_empty() {
                    Some("global::".to_string())
                } else {
                    Some(format!("global::{}.", symbols.qualified_name(container)))
                }
            }
            _ => None,
        }
    }
}

// MARK: - the type hierarchy

/// Who derives from whom among the project's types, worked out once per
/// rename.
struct Hierarchy<'s> {
    semantic: &'s Semantic,
    binder: &'s Binder<'s>,
    /// Every type a source type derives from or implements, transitively.
    supertypes: HashMap<SymbolId, Vec<SymbolId>>,
}

impl<'s> Hierarchy<'s> {
    fn new(semantic: &'s Semantic, binder: &'s Binder<'s>) -> Self {
        Self {
            semantic,
            binder,
            supertypes: HashMap::new(),
        }
    }

    fn supertypes(&mut self, ty: SymbolId) -> Vec<SymbolId> {
        if let Some(found) = self.supertypes.get(&ty) {
            return found.clone();
        }
        let mut seen: Vec<SymbolId> = Vec::new();
        let mut work = vec![ty];
        while let Some(current) = work.pop() {
            for base in self.binder.base_types_of(current) {
                if let Some(symbol) = base.symbol()
                    && symbol != ty
                    && !seen.contains(&symbol)
                {
                    seen.push(symbol);
                    work.push(symbol);
                }
            }
            if let Some(Type::Named { symbol, .. }) = self.binder.base_class_of(current)
                && symbol != ty
                && !seen.contains(&symbol)
            {
                seen.push(symbol);
                work.push(symbol);
            }
        }
        self.supertypes.insert(ty, seen.clone());
        seen
    }

    /// The classes `ty` derives from, nearest first.
    fn base_classes(&self, ty: SymbolId) -> Vec<SymbolId> {
        let mut out = Vec::new();
        let mut current = ty;
        while let Some(Type::Named { symbol, .. }) = self.binder.base_class_of(current) {
            if out.contains(&symbol) || symbol == ty || out.len() > 64 {
                break;
            }
            out.push(symbol);
            current = symbol;
        }
        out
    }

    /// The interfaces `ty` implements, directly or through its bases; `ty`
    /// itself when it is one.
    fn interfaces(&mut self, ty: SymbolId) -> Vec<SymbolId> {
        let symbols = self.semantic.compilation.symbols();
        let mut out: Vec<SymbolId> = self
            .supertypes(ty)
            .into_iter()
            .filter(|&other| symbols.get(other).type_kind() == Some(TypeKind::Interface))
            .collect();
        if symbols.get(ty).type_kind() == Some(TypeKind::Interface) {
            out.push(ty);
        }
        out
    }

    /// The project's types that derive from or implement `ty`.
    fn derived(&mut self, ty: SymbolId) -> Vec<SymbolId> {
        let types: Vec<SymbolId> = self
            .semantic
            .compilation
            .all_types()
            .map(|symbol| symbol.id)
            .filter(|&other| other != ty && self.semantic.in_source(other))
            .collect();
        types
            .into_iter()
            .filter(|&other| self.supertypes(other).contains(&ty))
            .collect()
    }
}

/// Whether `b` has the shape of `a`: an override or implementation of it,
/// or it of `b`. Types are compared loosely where a type parameter stands in
/// one of them, since `IList<T>.Add(T)` is implemented by `Add(int)`.
fn same_signature(binder: &Binder<'_>, a: SymbolId, b: SymbolId) -> bool {
    let symbols = binder.compilation().symbols();
    let (x, y) = (symbols.get(a), symbols.get(b));
    if x.kind != y.kind {
        return false;
    }
    match (x.as_method(), y.as_method()) {
        (Some(m), Some(n)) => {
            m.parameters.len() == n.parameters.len()
                && m.type_parameters.len() == n.type_parameters.len()
                && m.parameters.iter().zip(&n.parameters).all(|(&p, &q)| {
                    let refs = symbols.get(p).as_parameter().map(|p| p.ref_kind)
                        == symbols.get(q).as_parameter().map(|q| q.ref_kind);
                    refs && loosely_equal(&type_of(binder, p), &type_of(binder, q))
                })
        }
        (None, None) => match (x.as_property(), y.as_property()) {
            (Some(p), Some(q)) => p.parameters.len() == q.parameters.len(),
            _ => true,
        },
        _ => false,
    }
}

/// Whether two methods take exactly the same parameter types: two such
/// cannot be declared in one type.
fn same_parameter_types(binder: &Binder<'_>, a: SymbolId, b: SymbolId) -> bool {
    let symbols = binder.compilation().symbols();
    let (Some(m), Some(n)) = (symbols.get(a).as_method(), symbols.get(b).as_method()) else {
        return false;
    };
    m.parameters.len() == n.parameters.len()
        && m.type_parameters.len() == n.type_parameters.len()
        && m.parameters
            .iter()
            .zip(&n.parameters)
            .all(|(&p, &q)| type_of(binder, p) == type_of(binder, q))
}

fn type_of(binder: &Binder<'_>, symbol: SymbolId) -> Type {
    let mut sink = Diagnostics::new();
    binder.type_of(symbol, &mut sink)
}

fn loosely_equal(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::TypeParameter(_), _)
        | (_, Type::TypeParameter(_))
        | (Type::Error, _)
        | (_, Type::Error) => true,
        (
            Type::Named {
                symbol: s,
                type_arguments: x,
            },
            Type::Named {
                symbol: t,
                type_arguments: y,
            },
        ) => s == t && x.len() == y.len() && x.iter().zip(y).all(|(x, y)| loosely_equal(x, y)),
        (
            Type::Array {
                element: x,
                rank: r,
            },
            Type::Array {
                element: y,
                rank: s,
            },
        ) => r == s && loosely_equal(x, y),
        (Type::Pointer(x), Type::Pointer(y)) | (Type::ByRef(x), Type::ByRef(y)) => {
            loosely_equal(x, y)
        }
        _ => a == b,
    }
}

// MARK: - finding the uses

/// What `token` refers to, for renaming: as the view resolves it, except
/// that a delegate called through a local or a field is the local or the
/// field, not the delegate's `Invoke`.
fn resolve_name(view: &mut View<'_>, token: &SyntaxToken) -> Option<Resolved> {
    let resolved = view.resolve(token)?;
    if let Resolved::Symbol(symbol) = &resolved
        && token.value_text() != "Invoke"
    {
        let symbols = view.compilation().symbols();
        let found = symbols.get(*symbol);
        let is_invoke = found.name == "Invoke"
            && found
                .container
                .is_some_and(|ty| symbols.get(ty).type_kind() == Some(TypeKind::Delegate));
        if is_invoke && let Some(body) = view.body_for(token.parent()) {
            match body.reference_at(token.span()) {
                Some(BoundSymbol::Local(local)) => {
                    let local = body.locals.get(local.0 as usize)?;
                    return Some(Resolved::Local {
                        tree: view.tree,
                        span: local.span,
                        name: local.name.clone(),
                        ty: local.ty.clone(),
                    });
                }
                Some(BoundSymbol::Declared(other)) => return Some(Resolved::Symbol(other)),
                None => {}
            }
        }
    }
    Some(resolved)
}

/// The uses of what `plan` renames in one file, each with its new text.
fn uses_in(
    view: &mut View<'_>,
    plan: &Plan,
    old: &str,
    targets: &[SymbolId],
    written: &str,
    value: &str,
) -> Vec<Change> {
    let stem = attribute_stem(old).filter(|_| matches!(plan.subject, Subject::Symbols(_)));
    // `[Obsolete]` for `ObsoleteAttribute`: the short form keeps short.
    let new_stem = attribute_stem(value).map_or_else(|| written.to_string(), escaped);
    let tokens: Vec<SyntaxToken> = view
        .root
        .descendant_tokens()
        .filter(|token| {
            token.kind() == SyntaxKind::IdentifierToken
                && (token.value_text() == old
                    || stem.is_some_and(|stem| token.value_text() == stem))
        })
        .collect();
    let semantic = view.semantic;
    let mut out = Vec::new();
    for token in tokens {
        let Some(resolved) = resolve_name(view, &token) else {
            continue;
        };
        let hit = match (&plan.subject, &resolved) {
            (Subject::Symbols(_), Resolved::Symbol(symbol)) => {
                targets.contains(&semantic.canonical(*symbol))
            }
            (
                Subject::Local { tree, span },
                Resolved::Local {
                    tree: t, span: s, ..
                },
            ) => tree == t && span == s,
            _ => false,
        };
        if !hit {
            continue;
        }
        let text = if token.value_text() == old {
            written.to_string()
        } else {
            new_stem.clone()
        };
        out.push(Change {
            span: token.span(),
            text,
            name_offset: 0,
            code: true,
        });
    }
    out
}

/// A label's declaration and its `goto`s, inside the member `owner`.
fn label_changes(root: &SyntaxNode, owner: TextSpan, old: &str, written: &str) -> Vec<Change> {
    let Some(owner) = root.find_node(owner) else {
        return Vec::new();
    };
    owner
        .descendant_tokens()
        .filter(|token| token.value_text() == old && is_label_token(token))
        .map(|token| Change {
            span: token.span(),
            text: written.to_string(),
            name_offset: 0,
            code: false,
        })
        .collect()
}

fn is_label_token(token: &SyntaxToken) -> bool {
    if token.kind() != SyntaxKind::IdentifierToken {
        return false;
    }
    let parent = token.parent();
    matches!(
        parent.kind(),
        SyntaxKind::LabeledStatement | SyntaxKind::GotoStatement
    ) || (parent.kind() == SyntaxKind::IdentifierName
        && parent
            .parent()
            .is_some_and(|grand| grand.kind() == SyntaxKind::GotoStatement))
}

/// The name a `using X = ...;` directive declares.
fn alias_name(directive: &SyntaxNode) -> Option<SyntaxToken> {
    let equals = directive.child_of_kind(SyntaxKind::NameEquals)?;
    equals
        .descendant_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
}

/// Whether `token` is an alias or a use of one, and if so the scope of its
/// directive and whether it is global.
fn alias_at(view: &mut View<'_>, token: &SyntaxToken) -> Option<(TextSpan, bool)> {
    let directives: Vec<SyntaxNode> = view
        .root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::UsingDirective)
        .collect();
    for directive in directives {
        let Some(alias) = alias_name(&directive) else {
            continue;
        };
        if alias.value_text() != token.value_text() {
            continue;
        }
        let global = directive
            .child_token_of_kind(SyntaxKind::GlobalKeyword)
            .is_some();
        let scope = directive.parent()?.span();
        if alias == *token {
            return Some((scope, global));
        }
        if (global || scope.contains_span(token.span())) && is_alias_use(view, token) {
            return Some((scope, global));
        }
    }
    None
}

/// Whether a token spelled like an alias is a use of it: the leftmost part
/// of a name, and bound to nothing that has the name itself.
fn is_alias_use(view: &mut View<'_>, token: &SyntaxToken) -> bool {
    let parent = token.parent().clone();
    if parent.kind() != SyntaxKind::IdentifierName {
        return false;
    }
    if let Some(grand) = parent.parent()
        && matches!(
            grand.kind(),
            SyntaxKind::QualifiedName
                | SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::PointerMemberAccessExpression
        )
        && grand.children().next().as_ref() != Some(&parent)
    {
        return false;
    }
    if parent
        .ancestors()
        .any(|ancestor| ancestor.kind() == SyntaxKind::NameEquals)
    {
        return false;
    }
    match resolve_name(view, token) {
        Some(Resolved::Local { .. }) => false,
        Some(Resolved::Symbol(symbol)) => {
            view.compilation().symbols().get(symbol).name != token.value_text()
        }
        None => true,
    }
}

/// The directive's name and its uses in `scope`.
fn alias_changes(view: &mut View<'_>, scope: TextSpan, old: &str, written: &str) -> Vec<Change> {
    let tokens: Vec<SyntaxToken> = view
        .root
        .descendant_tokens()
        .filter(|token| {
            token.kind() == SyntaxKind::IdentifierToken
                && token.value_text() == old
                && scope.contains_span(token.span())
        })
        .collect();
    let mut out = Vec::new();
    for token in tokens {
        let declares = std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find(|node| node.kind() == SyntaxKind::UsingDirective)
            .and_then(|directive| alias_name(&directive))
            .is_some_and(|alias| alias == token);
        if declares || is_alias_use(view, &token) {
            out.push(Change {
                span: token.span(),
                text: written.to_string(),
                name_offset: 0,
                code: false,
            });
        }
    }
    out
}

// MARK: - documentation comments

/// `<see cref="Old"/>`, `<param name="old">` and their kind, in the
/// documentation comments of one file, where they name what is renamed.
fn doc_changes(
    view: &mut View<'_>,
    targets: &[SymbolId],
    old: &str,
    written: &str,
    value: &str,
) -> Vec<Change> {
    let mut out = Vec::new();
    let tokens: Vec<SyntaxToken> = view
        .root
        .descendant_tokens()
        .filter(|token| {
            token.leading_trivia().iter().any(|trivia| {
                matches!(
                    trivia.kind(),
                    SyntaxKind::SingleLineDocumentationCommentTrivia
                        | SyntaxKind::MultiLineDocumentationCommentTrivia
                ) && trivia.text().contains(old)
            })
        })
        .collect();
    for token in tokens {
        // The declaration the comment is on: the node the token begins.
        let declaration = std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .take_while(|node| node.first_token().as_ref() == Some(&token))
            .find(|node| view.model.declared_symbol(node).is_some());
        let documented = declaration
            .as_ref()
            .and_then(|node| view.model.declared_symbol(node));
        let context_node = declaration.unwrap_or_else(|| token.parent().clone());
        for trivia in token.leading_trivia() {
            if !matches!(
                trivia.kind(),
                SyntaxKind::SingleLineDocumentationCommentTrivia
                    | SyntaxKind::MultiLineDocumentationCommentTrivia
            ) {
                continue;
            }
            let base = trivia.span().start();
            for attribute in xml_attributes(trivia.text()) {
                let at = base + attribute.value_start as u32;
                match attribute.name.as_str() {
                    "name" if attribute.value == old => {
                        let Some(documented) = documented else {
                            continue;
                        };
                        let named = match attribute.element.as_str() {
                            "param" | "paramref" => parameters_of(view, documented),
                            "typeparam" | "typeparamref" => type_parameters_of(view, documented),
                            _ => continue,
                        };
                        let symbols = view.compilation().symbols();
                        if named.iter().any(|&symbol| {
                            symbols.get(symbol).name == old && targets.contains(&symbol)
                        }) {
                            out.push(Change {
                                span: TextSpan::new(at, attribute.value.len() as u32),
                                text: value.to_string(),
                                name_offset: 0,
                                code: false,
                            });
                        }
                    }
                    "cref" => {
                        for (offset, length) in cref_hits(
                            view,
                            &context_node,
                            documented,
                            &attribute.value,
                            old,
                            targets,
                        ) {
                            out.push(Change {
                                span: TextSpan::new(at + offset, length),
                                text: written.to_string(),
                                name_offset: 0,
                                code: false,
                            });
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// An attribute of an element in a documentation comment.
#[derive(Debug)]
struct XmlAttribute {
    element: String,
    name: String,
    value: String,
    /// Byte offset of the value in the comment.
    value_start: usize,
}

/// Every `name="value"` of every element start in `text`: enough of XML to
/// find `cref` and `name`.
fn xml_attributes(text: &str) -> Vec<XmlAttribute> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(open) = text[at..].find('<') {
        let mut index = at + open + 1;
        let start = index;
        while index < bytes.len() && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
        {
            index += 1;
        }
        let element = text[start..index].to_string();
        at = index.max(at + open + 1);
        if element.is_empty() {
            continue;
        }
        // Attributes until the element closes.
        loop {
            while index < bytes.len() && matches!(bytes[index], b' ' | b'\t') {
                index += 1;
            }
            let name_start = index;
            while index < bytes.len()
                && (bytes[index].is_ascii_alphanumeric() || matches!(bytes[index], b'_' | b':'))
            {
                index += 1;
            }
            if index == name_start || index >= bytes.len() {
                break;
            }
            let name = text[name_start..index].to_string();
            while index < bytes.len() && bytes[index] == b' ' {
                index += 1;
            }
            if index >= bytes.len() || bytes[index] != b'=' {
                break;
            }
            index += 1;
            while index < bytes.len() && bytes[index] == b' ' {
                index += 1;
            }
            let Some(&quote) = bytes
                .get(index)
                .filter(|&&byte| byte == b'"' || byte == b'\'')
            else {
                break;
            };
            index += 1;
            let value_start = index;
            let Some(length) = text[index..].find(quote as char) else {
                break;
            };
            index += length;
            out.push(XmlAttribute {
                element: element.clone(),
                name,
                value: text[value_start..index].to_string(),
                value_start,
            });
            index += 1;
        }
        at = index.max(at);
    }
    out
}

fn parameters_of(view: &View<'_>, symbol: SymbolId) -> Vec<SymbolId> {
    let symbols = view.compilation().symbols();
    let found = symbols.get(symbol);
    if let Some(method) = found.as_method() {
        return method.parameters.clone();
    }
    if let Some(property) = found.as_property() {
        return property.parameters.clone();
    }
    if let Some(named) = found.as_named_type() {
        if let Some(constructor) = named.primary_constructor
            && let Some(method) = symbols.get(constructor).as_method()
        {
            return method.parameters.clone();
        }
        if named.type_kind == Some(TypeKind::Delegate) {
            return symbols
                .lookup(symbol, "Invoke")
                .iter()
                .filter_map(|&invoke| symbols.get(invoke).as_method())
                .flat_map(|method| method.parameters.clone())
                .collect();
        }
    }
    Vec::new()
}

fn type_parameters_of(view: &View<'_>, symbol: SymbolId) -> Vec<SymbolId> {
    let found = view.compilation().symbols().get(symbol);
    found
        .as_method()
        .map(|method| method.type_parameters.clone())
        .or_else(|| {
            found
                .as_named_type()
                .map(|named| named.type_parameters.clone())
        })
        .unwrap_or_default()
}

/// The parts of a `cref` that name what is renamed: offsets into the value
/// and lengths. `N.Type.Member(int)`: each dotted part is looked up in what
/// the one before it found, the first from where the comment is.
fn cref_hits(
    view: &View<'_>,
    at: &SyntaxNode,
    documented: Option<SymbolId>,
    cref: &str,
    old: &str,
    targets: &[SymbolId],
) -> Vec<(u32, u32)> {
    // `T:Namespace.Type` is already an ID; the prefix is not a name.
    let skip = if cref.len() > 2 && cref.as_bytes()[1] == b':' {
        2
    } else {
        0
    };
    let body = &cref[skip..];
    let name_end = body.find('(').unwrap_or(body.len());
    let parameters = body[name_end..]
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .map(|list| {
            if list.trim().is_empty() {
                0
            } else {
                split_top_level(list, ',').len()
            }
        });
    let parts = split_top_level(&body[..name_end], '.');

    let semantic = view.semantic;
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let context = binder.context_at(view.tree, at);
    let mut current: Vec<SymbolId> = Vec::new();
    let mut hits = Vec::new();
    for (index, (offset, part)) in parts.iter().enumerate() {
        let (name, arity) = match part.find(['{', '<']) {
            Some(open) => (
                part[..open].trim(),
                split_top_level(&part[open + 1..part.len().saturating_sub(1)], ',').len(),
            ),
            None => (part.trim(), 0),
        };
        let last = index + 1 == parts.len();
        let mut found: Vec<SymbolId> = Vec::new();
        if index == 0 {
            if let Some(documented) = documented {
                found.extend(symbols.lookup(documented, name).iter().copied());
                if symbols.get(documented).name == name {
                    found.push(documented);
                }
            }
            for ty in context.enclosing_types() {
                if found.is_empty() {
                    found.extend(binder.lookup_member(ty, name));
                }
            }
            if found.is_empty()
                && let Some(symbol) = binder.lookup(name, arity, &context)
            {
                found.push(symbol);
            }
            if found.is_empty()
                && let Some(namespace) =
                    symbols.lookup_namespace(view.compilation().global_namespace(), name)
            {
                found.push(namespace);
            }
        } else {
            for &container in &current {
                match symbols.get(container).kind {
                    SymbolKind::Namespace => found.extend(symbols.lookup(container, name)),
                    SymbolKind::NamedType => {
                        found.extend(binder.lookup_member(container, name));
                        if found.is_empty() {
                            found.extend(symbols.lookup(container, name));
                        }
                    }
                    _ => {}
                }
            }
        }
        if last && let Some(count) = parameters {
            let fitting: Vec<SymbolId> = found
                .iter()
                .copied()
                .filter(|&symbol| {
                    symbols
                        .get(symbol)
                        .as_method()
                        .is_some_and(|method| method.parameters.len() == count)
                })
                .collect();
            if !fitting.is_empty() {
                found = fitting;
            }
        }
        if name == old
            && found
                .iter()
                .any(|&symbol| targets.contains(&semantic.canonical(symbol)))
        {
            let lead = part.len() - part.trim_start().len();
            hits.push(((skip + offset + lead) as u32, name.len() as u32));
        }
        if found.is_empty() {
            break;
        }
        current = found;
    }
    hits
}

/// `text` split at `separator` where it is not inside brackets, each part
/// with its offset.
fn split_top_level(text: &str, separator: char) -> Vec<(usize, &str)> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (index, ch) in text.char_indices() {
        match ch {
            '{' | '<' | '(' | '[' => depth += 1,
            '}' | '>' | ')' | ']' => depth -= 1,
            _ if ch == separator && depth == 0 => {
                parts.push((start, &text[start..index]));
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }
    parts.push((start, &text[start..]));
    parts
}

// MARK: - comments and strings

/// Whole-word occurrences of `old` in the comments and strings of a file,
/// as the options ask, where no other change already is.
fn text_changes(
    root: &SyntaxNode,
    old: &str,
    value: &str,
    options: RenameOptions,
    taken: &[Change],
) -> Vec<Change> {
    let mut out = Vec::new();
    let mut add = |base: u32, text: &str| {
        for at in word_positions(text, old) {
            let span = TextSpan::new(base + at as u32, old.len() as u32);
            if taken
                .iter()
                .any(|change| change.span.overlaps_with(span) || change.span == span)
            {
                continue;
            }
            out.push(Change {
                span,
                text: value.to_string(),
                name_offset: 0,
                code: false,
            });
        }
    };
    for token in root.descendant_tokens() {
        if options.in_strings
            && matches!(
                token.kind(),
                SyntaxKind::StringLiteralToken
                    | SyntaxKind::Utf8StringLiteralToken
                    | SyntaxKind::SingleLineRawStringLiteralToken
                    | SyntaxKind::MultiLineRawStringLiteralToken
                    | SyntaxKind::Utf8SingleLineRawStringLiteralToken
                    | SyntaxKind::Utf8MultiLineRawStringLiteralToken
                    | SyntaxKind::InterpolatedStringTextToken
            )
        {
            add(token.span().start(), token.text());
        }
        if options.in_comments {
            for trivia in token
                .leading_trivia()
                .into_iter()
                .chain(token.trailing_trivia())
            {
                if matches!(
                    trivia.kind(),
                    SyntaxKind::SingleLineCommentTrivia
                        | SyntaxKind::MultiLineCommentTrivia
                        | SyntaxKind::SingleLineDocumentationCommentTrivia
                        | SyntaxKind::MultiLineDocumentationCommentTrivia
                ) {
                    add(trivia.span().start(), trivia.text());
                }
            }
        }
    }
    out
}

/// Where `word` stands as a whole identifier in `text`.
fn word_positions(text: &str, word: &str) -> Vec<usize> {
    let mut out = Vec::new();
    if word.is_empty() {
        return out;
    }
    let bytes = text.as_bytes();
    let is_part = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_' || byte >= 0x80;
    let mut from = 0;
    while let Some(at) = text[from..].find(word) {
        let start = from + at;
        let end = start + word.len();
        let before = start == 0 || !is_part(bytes[start - 1]);
        let after = end == bytes.len() || !is_part(bytes[end]);
        if before && after {
            out.push(start);
        }
        from = end;
    }
    out
}

// MARK: - scopes

/// The declarations spelled `value` whose scope overlaps that of the
/// declaration `token`, within the member it is in.
fn scope_clashes(token: &SyntaxToken, value: &str) -> Vec<TextSpan> {
    let Some(own_scope) = scope_of(token) else {
        return Vec::new();
    };
    let owner = token
        .parent()
        .ancestors()
        .find(|node| is_member(node.kind()))
        .unwrap_or_else(|| own_scope.clone());
    owner
        .descendant_tokens()
        .filter(|other| {
            other.kind() == SyntaxKind::IdentifierToken
                && other.value_text() == value
                && declares_local(other)
        })
        .filter(|other| {
            scope_of(other).is_some_and(|scope| {
                scope.span().contains_span(token.span())
                    || own_scope.span().contains_span(other.span())
            })
        })
        .map(|other| other.span())
        .collect()
}

/// Whether a token is the name a local, a parameter, a pattern variable or
/// a local function is declared with.
fn declares_local(token: &SyntaxToken) -> bool {
    let parent = token.parent();
    matches!(
        parent.kind(),
        SyntaxKind::VariableDeclarator
            | SyntaxKind::Parameter
            | SyntaxKind::SingleVariableDesignation
            | SyntaxKind::ForEachStatement
            | SyntaxKind::CatchDeclaration
            | SyntaxKind::LocalFunctionStatement
    ) && parent.child_tokens().any(|child| child == *token)
        && !(parent.kind() == SyntaxKind::VariableDeclarator
            && parent.ancestors().any(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                )
            }))
}

/// The node a declared name is visible in: the block around a local, the
/// statement a `foreach` or `for` variable belongs to, the member or lambda
/// a parameter belongs to.
fn scope_of(token: &SyntaxToken) -> Option<SyntaxNode> {
    let parent = token.parent().clone();
    let start = if parent.kind() == SyntaxKind::LocalFunctionStatement {
        parent.parent()?.clone()
    } else {
        parent
    };
    std::iter::once(start.clone())
        .chain(start.ancestors())
        .find(|node| is_scope(node.kind()))
}

const fn is_scope(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Block
            | SyntaxKind::SwitchSection
            | SyntaxKind::ForStatement
            | SyntaxKind::ForEachStatement
            | SyntaxKind::ForEachVariableStatement
            | SyntaxKind::UsingStatement
            | SyntaxKind::FixedStatement
            | SyntaxKind::CatchClause
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::CompilationUnit
    ) || is_member(kind)
}

const fn is_member(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::FieldDeclaration
    )
}

/// The token that declares `symbol` in the view, where it is declared in
/// the view's file.
fn declaration_token(
    semantic: &Semantic,
    view: &View<'_>,
    symbol: SymbolId,
) -> Option<SyntaxToken> {
    let found = semantic.compilation.symbols().get(symbol);
    let location = found
        .locations
        .iter()
        .find(|location| location.tree == view.tree)?;
    let span = match &view.speculation {
        Some(speculation) => speculation.unmap(location.span)?,
        None => location.span,
    };
    view.root
        .find_token(span.start())
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
}

// MARK: - names

/// The new name read as C# reads an identifier: its value, and whether it
/// is a keyword that needs `@`.
///
/// # Errors
///
/// When it is not exactly one identifier.
fn identifier(name: &str) -> Result<(String, bool), String> {
    let invalid = || format!("`{name}` is not a valid C# identifier");
    if name.is_empty() {
        return Err("the new name is empty".to_string());
    }
    let lexed = tokenize(&SourceText::new("<rename>", name));
    if !lexed.diagnostics.is_empty() {
        return Err(invalid());
    }
    let [token, end] = lexed.tokens.as_slice() else {
        return Err(invalid());
    };
    if !end.is_end_of_file()
        || token.full_span != TextSpan::new(0, name.len() as u32)
        || token.span != token.full_span
    {
        return Err(invalid());
    }
    if token.kind == SyntaxKind::IdentifierToken {
        let value = token
            .value_text
            .as_deref()
            .map_or_else(|| name.to_string(), str::to_owned);
        return Ok((value, false));
    }
    if reserved_keyword_kind(name).is_some() {
        return Ok((name.to_string(), true));
    }
    Err(invalid())
}

/// A name as it has to be written: `@class` for a keyword.
fn escaped(value: &str) -> String {
    if reserved_keyword_kind(value).is_some() {
        format!("@{value}")
    } else {
        value.to_string()
    }
}

/// The name a member is called by: `M` for the explicit implementation
/// `IFoo.M`.
fn short_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn display_container(semantic: &Semantic, container: SymbolId) -> String {
    let symbols = semantic.compilation.symbols();
    let name = symbols.qualified_name(container);
    if name.is_empty() {
        "the global namespace".to_string()
    } else {
        name
    }
}

/// Whether a token is a name standing on its own — not after a `.`, not
/// the name of an argument — which is what qualifying can be put in front
/// of.
fn is_simple_name(token: &SyntaxToken) -> bool {
    let parent = token.parent();
    if !matches!(
        parent.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) {
        return false;
    }
    let Some(grand) = parent.parent() else {
        return false;
    };
    match grand.kind() {
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName => grand.children().next().as_ref() == Some(parent),
        SyntaxKind::MemberBindingExpression
        | SyntaxKind::NameColon
        | SyntaxKind::NameEquals
        | SyntaxKind::GotoStatement => false,
        _ => !parent
            .ancestors()
            .any(|ancestor| ancestor.kind() == SyntaxKind::Attribute),
    }
}

/// Where an offset of the text before the changes is after them. A change
/// that starts at `at` is the name's own, and the name then starts where
/// the change puts it.
fn map_start(changes: &[Change], at: u32) -> u32 {
    let mut shift: i64 = 0;
    for change in changes {
        if change.span.start() == at {
            return (i64::from(at) + shift + i64::from(change.name_offset)) as u32;
        }
        if change.span.end() <= at {
            shift += change.text.len() as i64 - i64::from(change.span.length());
        }
    }
    (i64::from(at) + shift) as u32
}

fn apply_changes(text: &str, changes: &[Change]) -> String {
    let edits: Vec<TextEdit> = changes
        .iter()
        .map(|change| TextEdit::new(change.span, change.text.clone()))
        .collect();
    crate::edit::apply(text, &edits)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::super::tests::{at, compile};
    use super::*;

    /// Renames what is at `marker` (plus `into`) of `file` to `new`, and
    /// returns every file as it reads afterwards, by name, with the result.
    fn rename_with(
        files: &[(&str, &str)],
        file: &str,
        marker: &str,
        into: usize,
        new: &str,
        options: RenameOptions,
    ) -> Result<(BTreeMap<String, String>, Renamed), String> {
        let semantic = compile(files, false).expect("compiled");
        let text = files
            .iter()
            .find(|(name, _)| *name == file)
            .map(|(_, text)| *text)
            .expect("the file is there");
        let path = PathBuf::from(format!("/p/{file}"));
        let renamed = semantic.rename(&path, at(text, marker, into), new, None, options, &[])?;
        Ok((texts_after(files, &renamed), renamed))
    }

    fn texts_after(files: &[(&str, &str)], renamed: &Renamed) -> BTreeMap<String, String> {
        files
            .iter()
            .map(|(name, text)| {
                let path = PathBuf::from(format!("/p/{name}"));
                (
                    (*name).to_string(),
                    crate::edit::apply(text, renamed.edit.edits_of(&path)),
                )
            })
            .collect()
    }

    fn rename(
        files: &[(&str, &str)],
        file: &str,
        marker: &str,
        new: &str,
    ) -> BTreeMap<String, String> {
        let (texts, renamed) =
            rename_with(files, file, marker, 0, new, RenameOptions::default()).expect("renamed");
        assert!(
            renamed.conflicts.is_empty(),
            "no conflicts expected: {:?}",
            renamed.conflicts
        );
        texts
    }

    fn prepare(
        files: &[(&str, &str)],
        file: &str,
        marker: &str,
        into: usize,
    ) -> Result<RenameTarget, String> {
        let semantic = compile(files, false).expect("compiled");
        let text = files
            .iter()
            .find(|(name, _)| *name == file)
            .map(|(_, text)| *text)
            .expect("the file is there");
        semantic.prepare_rename(
            Path::new(&format!("/p/{file}")),
            at(text, marker, into),
            None,
        )
    }

    #[test]
    fn a_local_is_renamed_where_it_is_declared_and_used() {
        let a = "class C { int M() { int count = 1; count += 2; return count; } int count; }";
        let texts = rename(&[("A.cs", a)], "A.cs", "count +=", "total");
        assert_eq!(
            texts["A.cs"],
            "class C { int M() { int total = 1; total += 2; return total; } int count; }"
        );
    }

    #[test]
    fn a_lambda_parameter_and_a_delegate_local_are_renamed() {
        let a = "using System; class C { int M() { Func<int, int> twice = x => x * 2; return twice(3); } }";
        let texts = rename(&[("A.cs", a)], "A.cs", "x =>", "value");
        assert!(
            texts["A.cs"].contains("value => value * 2"),
            "{}",
            texts["A.cs"]
        );
        let texts = rename(&[("A.cs", a)], "A.cs", "twice(", "doubled");
        assert!(
            texts["A.cs"].contains("doubled = x") && texts["A.cs"].contains("return doubled(3)"),
            "{}",
            texts["A.cs"]
        );
    }

    #[test]
    fn a_parameter_renames_its_named_arguments_and_its_documentation() {
        let a = "class C {\n  /// <summary>Scales <paramref name=\"factor\"/>.</summary>\n  /// <param name=\"factor\">How much.</param>\n  public int Scale(int factor) => factor * 2;\n}\n";
        let b = "class D { int Use(C c) => c.Scale(factor: 3); }\n";
        let texts = rename(&[("A.cs", a), ("B.cs", b)], "A.cs", "factor) =>", "by");
        assert_eq!(
            texts["A.cs"],
            "class C {\n  /// <summary>Scales <paramref name=\"by\"/>.</summary>\n  /// <param name=\"by\">How much.</param>\n  public int Scale(int by) => by * 2;\n}\n"
        );
        assert_eq!(
            texts["B.cs"],
            "class D { int Use(C c) => c.Scale(by: 3); }\n"
        );
    }

    #[test]
    fn a_field_is_renamed_across_files_with_nameof_and_cref() {
        let a = "/// <see cref=\"Player.health\"/>\nclass Player { public int health; void Hit() { health -= 1; this.health = 0; } }\n";
        let b = "class Game { string Name(Player p) => nameof(Player.health) + p.health; }\n";
        let texts = rename(&[("A.cs", a), ("B.cs", b)], "B.cs", "health)", "life");
        assert_eq!(
            texts["A.cs"],
            "/// <see cref=\"Player.life\"/>\nclass Player { public int life; void Hit() { life -= 1; this.life = 0; } }\n"
        );
        assert_eq!(
            texts["B.cs"],
            "class Game { string Name(Player p) => nameof(Player.life) + p.life; }\n"
        );
    }

    #[test]
    fn a_property_is_renamed_with_its_uses() {
        let a = "class Box { public int Size { get; set; } void Grow() { Size = Size + 1; } }\n";
        let b = "class User { int Get(Box b) => b.Size; void Set(Box b) { b.Size = 2; var n = new Box { Size = 3 }; } }\n";
        let texts = rename(&[("A.cs", a), ("B.cs", b)], "A.cs", "Size {", "Volume");
        assert!(!texts["A.cs"].contains("Size"), "{}", texts["A.cs"]);
        assert!(!texts["B.cs"].contains("Size"), "{}", texts["B.cs"]);
        assert_eq!(texts["B.cs"].matches("Volume").count(), 3);
    }

    #[test]
    fn a_virtual_method_renames_its_overrides_and_an_interface_its_implementations() {
        let a = "public interface IShape { double Area(); }\npublic abstract class Shape : IShape { public abstract double Area(); }\n";
        let b = "class Square : Shape { public override double Area() => 4; }\nclass Odd : IShape { double IShape.Area() => 1; }\nclass Use { double Sum(Shape s, IShape i, Square q) => s.Area() + i.Area() + q.Area(); }\n";
        // From an override in another file: the whole family.
        let texts = rename(
            &[("A.cs", a), ("B.cs", b)],
            "B.cs",
            "Area() => 4",
            "Surface",
        );
        assert_eq!(
            texts["A.cs"],
            "public interface IShape { double Surface(); }\npublic abstract class Shape : IShape { public abstract double Surface(); }\n"
        );
        assert_eq!(
            texts["B.cs"],
            "class Square : Shape { public override double Surface() => 4; }\nclass Odd : IShape { double IShape.Surface() => 1; }\nclass Use { double Sum(Shape s, IShape i, Square q) => s.Surface() + i.Surface() + q.Surface(); }\n"
        );
    }

    #[test]
    fn an_implementation_renames_the_interface_member_and_its_other_implementations() {
        let a = "interface IRun { void Run(); void Run(int n); }\nclass Base { public void Run() { } }\nclass Fast : Base, IRun { public void Run(int n) { } }\nclass Slow : IRun { public void Run() { } public void Run(int n) { } }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "Run() { } public", "Go");
        assert_eq!(
            texts["A.cs"],
            "interface IRun { void Go(); void Run(int n); }\nclass Base { public void Go() { } }\nclass Fast : Base, IRun { public void Run(int n) { } }\nclass Slow : IRun { public void Go() { } public void Run(int n) { } }\n"
        );
    }

    #[test]
    fn a_generic_and_a_nested_type_are_renamed() {
        let a = "class Outer { public class Bag<T> { public Bag() { } } Bag<int> b = new Bag<int>(); Outer.Bag<string> c; }\nclass Bag { }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "Bag<T>", "Sack");
        assert_eq!(
            texts["A.cs"],
            "class Outer { public class Sack<T> { public Sack() { } } Sack<int> b = new Sack<int>(); Outer.Sack<string> c; }\nclass Bag { }\n"
        );
    }

    #[test]
    fn a_member_that_implements_an_assembly_member_is_refused() {
        let a = "class C { public override string ToString() => \"c\"; }\n";
        let error = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "ToString",
            0,
            "Text",
            RenameOptions::default(),
        )
        .expect_err("refused");
        assert!(error.contains("assembly"), "{error}");
    }

    #[test]
    fn a_type_renames_constructors_destructor_uses_and_its_file() {
        let a = "namespace N {\n  /// <see cref=\"Pawn\"/>\n  public class Pawn { public Pawn() { } public Pawn(int x) : this() { } ~Pawn() { } public static Pawn Make() => new Pawn(1); }\n}\n";
        let b = "using N;\nclass Board { Pawn p = new Pawn(); N.Pawn q; System.Type t = typeof(Pawn); }\n";
        let (texts, renamed) = rename_with(
            &[("Pawn.cs", a), ("Board.cs", b)],
            "Board.cs",
            "Pawn p",
            0,
            "Piece",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(renamed.conflicts.is_empty(), "{:?}", renamed.conflicts);
        assert_eq!(
            texts["Pawn.cs"],
            "namespace N {\n  /// <see cref=\"Piece\"/>\n  public class Piece { public Piece() { } public Piece(int x) : this() { } ~Piece() { } public static Piece Make() => new Piece(1); }\n}\n"
        );
        assert_eq!(
            texts["Board.cs"],
            "using N;\nclass Board { Piece p = new Piece(); N.Piece q; System.Type t = typeof(Piece); }\n"
        );
        assert_eq!(
            renamed.edit.renames,
            vec![(PathBuf::from("/p/Pawn.cs"), PathBuf::from("/p/Piece.cs"))]
        );
        // And not when asked not to.
        let (_, renamed) = rename_with(
            &[("Pawn.cs", a), ("Board.cs", b)],
            "Board.cs",
            "Pawn p",
            0,
            "Piece",
            RenameOptions {
                file: false,
                ..RenameOptions::default()
            },
        )
        .expect("renamed");
        assert!(renamed.edit.renames.is_empty());
    }

    #[test]
    fn an_attribute_class_renames_its_short_form() {
        let a = "using System;\nclass MarkAttribute : Attribute { }\n[Mark] class A { }\n[MarkAttribute] class B { }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "MarkAttribute :", "FlagAttribute");
        assert_eq!(
            texts["A.cs"],
            "using System;\nclass FlagAttribute : Attribute { }\n[Flag] class A { }\n[FlagAttribute] class B { }\n"
        );
        // Renamed from the short form, the name typed is the short one.
        let texts = rename(&[("A.cs", a)], "A.cs", "Mark]", "Tag");
        assert_eq!(
            texts["A.cs"],
            "using System;\nclass TagAttribute : Attribute { }\n[Tag] class A { }\n[TagAttribute] class B { }\n"
        );
        // A new name without the suffix is used whole.
        let texts = rename(&[("A.cs", a)], "A.cs", "MarkAttribute :", "Flag");
        assert_eq!(
            texts["A.cs"],
            "using System;\nclass Flag : Attribute { }\n[Flag] class A { }\n[Flag] class B { }\n"
        );
    }

    #[test]
    fn a_type_parameter_is_renamed_in_its_declaration_and_constraints() {
        let a = "/// <typeparam name=\"T\">The item.</typeparam>\nclass Bag<T> where T : class { T item; T Get() => item; }\nclass Other<T> { T x; }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "T item", "TItem");
        assert_eq!(
            texts["A.cs"],
            "/// <typeparam name=\"TItem\">The item.</typeparam>\nclass Bag<TItem> where TItem : class { TItem item; TItem Get() => item; }\nclass Other<T> { T x; }\n"
        );
    }

    #[test]
    fn a_partial_class_and_a_partial_method_are_renamed_everywhere() {
        let a = "partial class Part { partial void Hook(); void Run() { Hook(); } }\n";
        let b =
            "partial class Part { partial void Hook() { } }\nclass Use { Part p = new Part(); }\n";
        let texts = rename(&[("A.cs", a), ("B.cs", b)], "B.cs", "Hook()", "OnRun");
        assert_eq!(
            texts["A.cs"].matches("OnRun").count(),
            2,
            "{}",
            texts["A.cs"]
        );
        assert_eq!(
            texts["B.cs"].matches("OnRun").count(),
            1,
            "{}",
            texts["B.cs"]
        );
        let texts = rename(&[("A.cs", a), ("B.cs", b)], "A.cs", "Part {", "Piece");
        assert_eq!(
            texts["A.cs"],
            "partial class Piece { partial void Hook(); void Run() { Hook(); } }\n"
        );
        assert_eq!(
            texts["B.cs"],
            "partial class Piece { partial void Hook() { } }\nclass Use { Piece p = new Piece(); }\n"
        );
    }

    #[test]
    fn a_namespace_is_renamed_in_declarations_usings_and_qualified_names() {
        let a = "namespace Game.Core { class Unit { } }\n";
        let b = "using Game.Core;\nnamespace Game.Core { class More { } }\nclass Use { Game.Core.Unit u; }\n";
        let texts = rename(&[("A.cs", a), ("B.cs", b)], "A.cs", "Core", "Engine");
        assert_eq!(texts["A.cs"], "namespace Game.Engine { class Unit { } }\n");
        assert_eq!(
            texts["B.cs"],
            "using Game.Engine;\nnamespace Game.Engine { class More { } }\nclass Use { Game.Engine.Unit u; }\n"
        );
    }

    #[test]
    fn a_record_parameter_renames_its_property() {
        let a = "record Size(int Width) { int Twice => Width * 2; }\nclass Use { int W(Size s) => s.Width; Size Make() => new Size(Width: 1); }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "Width)", "Across");
        assert_eq!(
            texts["A.cs"],
            "record Size(int Across) { int Twice => Across * 2; }\nclass Use { int W(Size s) => s.Across; Size Make() => new Size(Across: 1); }\n"
        );
    }

    #[test]
    fn a_label_and_an_alias_are_renamed() {
        let a =
            "using Number = System.Int32;\nclass C { Number n; void M() { again: goto again; } }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "again:", "retry");
        assert!(
            texts["A.cs"].contains("retry: goto retry;"),
            "{}",
            texts["A.cs"]
        );
        let texts = rename(&[("A.cs", a)], "A.cs", "Number n", "Count");
        assert_eq!(
            texts["A.cs"],
            "using Count = System.Int32;\nclass C { Count n; void M() { again: goto again; } }\n"
        );
    }

    #[test]
    fn a_keyword_is_escaped_and_an_invalid_name_refused() {
        let a = "class C { int value; int M() => value; }\n";
        let texts = rename(&[("A.cs", a)], "A.cs", "value;", "class");
        assert_eq!(
            texts["A.cs"],
            "class C { int @class; int M() => @class; }\n"
        );
        let texts = rename(&[("A.cs", a)], "A.cs", "value;", "@event");
        assert_eq!(
            texts["A.cs"],
            "class C { int @event; int M() => @event; }\n"
        );
        for bad in ["1st", "a b", "a-b", "", "x;", "//", "a.b"] {
            let error = rename_with(
                &[("A.cs", a)],
                "A.cs",
                "value;",
                0,
                bad,
                RenameOptions::default(),
            )
            .expect_err("refused");
            assert!(
                error.contains("identifier") || error.contains("empty"),
                "{bad}: {error}"
            );
        }
        // Unicode letters are letters.
        let texts = rename(&[("A.cs", a)], "A.cs", "value;", "größe");
        assert_eq!(texts["A.cs"], "class C { int größe; int M() => größe; }\n");
    }

    #[test]
    fn what_cannot_be_renamed_says_why() {
        let a = "using System;\nclass C : Object { int M() { var x = 1; string s = this.ToString(); return x; } }\n";
        let files = [("A.cs", a)];
        for (marker, into, why) in [
            ("int M", 0, "predefined"),
            ("var x", 0, "var"),
            ("this.", 0, "this"),
            ("Object", 0, "assembly"),
            ("ToString", 0, "assembly"),
            ("class C", 0, "keyword"),
            ("{ int M", 0, "nothing"),
        ] {
            let error = prepare(&files, "A.cs", marker, into).expect_err(marker);
            assert!(error.contains(why), "{marker}: {error}");
        }
        let target = prepare(&files, "A.cs", "x;", 0).expect("a local");
        assert_eq!(target.text, "x");
        assert_eq!(target.span, TextSpan::new(at(a, "x;", 0), 1));
        let target = prepare(&files, "A.cs", "M()", 1).expect("a method, from its end");
        assert_eq!(target.text, "M");
        assert!(target.description.contains("M()"), "{}", target.description);
    }

    #[test]
    fn a_member_clash_is_a_conflict() {
        let a = "class C { int a; int b; void Go() { } void Go(int x) { } void Run() { } }\n";
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "a;",
            0,
            "b",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert_eq!(renamed.conflicts.len(), 1, "{:?}", renamed.conflicts);
        assert!(renamed.conflicts[0].message.contains("already contains"));
        assert_eq!(renamed.conflicts[0].span, TextSpan::new(at(a, "a;", 0), 1));
        // Another overload is not a clash; the same signature is.
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "Run",
            0,
            "Go",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert_eq!(renamed.conflicts.len(), 1, "{:?}", renamed.conflicts);
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "Go(int",
            0,
            "Run",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(renamed.conflicts.is_empty(), "{:?}", renamed.conflicts);
        // A member cannot be named after its type.
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "Run",
            0,
            "C",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(!renamed.conflicts.is_empty());
    }

    #[test]
    fn a_type_clash_in_the_namespace_is_a_conflict() {
        let a = "namespace N { class A { } }\n";
        let b = "namespace N { class B { } }\n";
        let (_, renamed) = rename_with(
            &[("A.cs", a), ("B.cs", b)],
            "A.cs",
            "A {",
            0,
            "B",
            RenameOptions::default(),
        )
        .expect("renamed");
        // The declaration, and the use of `B` that would now be ambiguous.
        assert!(
            renamed
                .conflicts
                .iter()
                .any(|conflict| conflict.path == Path::new("/p/A.cs")
                    && conflict.message.contains("already contains")),
            "{:?}",
            renamed.conflicts
        );
        assert!(renamed.conflicts.iter().all(|conflict| !conflict.resolved));
    }

    #[test]
    fn a_local_in_an_overlapping_scope_is_a_conflict() {
        let a = "class C { void M(int p) { int a = 1; { int b = 2; } int c = a; } void N() { int b = 0; } }\n";
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "a = 1",
            0,
            "b",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert_eq!(renamed.conflicts.len(), 1, "{:?}", renamed.conflicts);
        assert_eq!(
            renamed.conflicts[0].span,
            TextSpan::new(at(a, "b = 2", 0), 1)
        );
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "a = 1",
            0,
            "p",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(!renamed.conflicts.is_empty());
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "c = a",
            0,
            "d",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(renamed.conflicts.is_empty(), "{:?}", renamed.conflicts);
    }

    #[test]
    fn a_field_shadowed_by_a_local_is_qualified() {
        let a = "class C { int count; void M() { int total = 0; count = total; } }\n";
        let (texts, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "count;",
            0,
            "total",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert_eq!(
            texts["A.cs"],
            "class C { int total; void M() { int total = 0; this.total = total; } }\n"
        );
        assert_eq!(renamed.conflicts.len(), 1, "{:?}", renamed.conflicts);
        assert!(renamed.conflicts[0].resolved, "{:?}", renamed.conflicts);
    }

    #[test]
    fn a_local_that_would_capture_a_field_is_a_conflict() {
        let a = "class C { static int limit; int M() { int top = 1; return top + limit; } }\n";
        let (texts, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "top =",
            0,
            "limit",
            RenameOptions::default(),
        )
        .expect("renamed");
        // The field's use is now `C.limit`, which still means the field.
        assert_eq!(
            texts["A.cs"],
            "class C { static int limit; int M() { int limit = 1; return limit + C.limit; } }\n"
        );
        assert!(
            renamed.conflicts.iter().all(|conflict| conflict.resolved),
            "{:?}",
            renamed.conflicts
        );
        assert!(!renamed.conflicts.is_empty());
    }

    #[test]
    fn a_method_renamed_to_a_local_function_in_scope_is_a_conflict() {
        let a = "class C { void Go() { } void M() { void Stop() { } Go(); Stop(); } }\n";
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "Go()",
            0,
            "Stop",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(
            !renamed.conflicts.is_empty(),
            "the call would reach the local function"
        );
    }

    #[test]
    fn a_rename_in_unsaved_text_works_on_the_text_as_it_is() {
        let a = "class C { int speed; }\n";
        let b = "class D { int Get(C c) => 0; }\n";
        let semantic = compile(&[("A.cs", a), ("B.cs", b)], false).expect("compiled");
        // Typed since: a use of `speed`, and a local that moves everything.
        let typed = "class C { int speed; int Twice() { int k = 2; return speed * k; } }\n";
        let renamed = semantic
            .rename(
                Path::new("/p/A.cs"),
                at(typed, "speed *", 0),
                "velocity",
                Some(typed),
                RenameOptions::default(),
                &[],
            )
            .expect("renamed");
        assert!(renamed.conflicts.is_empty(), "{:?}", renamed.conflicts);
        assert_eq!(
            crate::edit::apply(typed, renamed.edit.edits_of(Path::new("/p/A.cs"))),
            "class C { int velocity; int Twice() { int k = 2; return velocity * k; } }\n"
        );
        let target = semantic
            .prepare_rename(Path::new("/p/A.cs"), at(typed, "k;", 0), Some(typed))
            .expect("a local typed a moment ago");
        assert_eq!(target.span, TextSpan::new(at(typed, "k;", 0), 1));
    }

    #[test]
    fn comments_and_strings_are_renamed_on_request() {
        let a = "class C {\n  // speed is how fast\n  int speed;\n  string Name => \"speed\" + \"speedy\";\n}\n";
        let (texts, _) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "speed;",
            0,
            "pace",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(texts["A.cs"].contains("// speed is"));
        assert!(texts["A.cs"].contains("\"speed\""));
        let (texts, _) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "speed;",
            0,
            "pace",
            RenameOptions {
                in_comments: true,
                in_strings: true,
                ..RenameOptions::default()
            },
        )
        .expect("renamed");
        assert_eq!(
            texts["A.cs"],
            "class C {\n  // pace is how fast\n  int pace;\n  string Name => \"pace\" + \"speedy\";\n}\n"
        );
    }

    #[test]
    fn overloads_are_renamed_together_on_request() {
        let a = "class C { void Log(int a) { } void Log(string s) { } void Use() { Log(1); Log(\"x\"); } }\n";
        let (texts, _) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "Log(int",
            0,
            "Write",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert_eq!(
            texts["A.cs"].matches("Write").count(),
            2,
            "{}",
            texts["A.cs"]
        );
        let (texts, _) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "Log(int",
            0,
            "Write",
            RenameOptions {
                overloads: true,
                ..RenameOptions::default()
            },
        )
        .expect("renamed");
        assert!(!texts["A.cs"].contains("Log"), "{}", texts["A.cs"]);
    }

    #[test]
    fn renaming_to_the_same_name_changes_nothing() {
        let a = "class C { int a; }\n";
        let (_, renamed) = rename_with(
            &[("A.cs", a)],
            "A.cs",
            "a;",
            0,
            "a",
            RenameOptions::default(),
        )
        .expect("renamed");
        assert!(renamed.edit.is_empty());
    }

    #[test]
    fn xml_attributes_are_read_with_their_offsets() {
        let text = "/// <param name=\"x\">the <see cref='T.M(int)'/></param>";
        let found = xml_attributes(text);
        assert_eq!(found.len(), 2);
        assert_eq!(found[0].element, "param");
        assert_eq!(&text[found[0].value_start..found[0].value_start + 1], "x");
        assert_eq!(found[1].name, "cref");
        assert_eq!(found[1].value, "T.M(int)");
    }

    #[test]
    fn flags_are_the_options() {
        let options = RenameOptions::from_flags(RenameOptions::IN_STRINGS | RenameOptions::FILE);
        assert!(options.in_strings && options.file && !options.in_comments && !options.overloads);
    }
}
