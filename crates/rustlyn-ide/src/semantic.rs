//! Layer 6: what the code means.
//!
//! Layer 4 follows a name the way C# looks it up, but only as far as a
//! declaration can say: it knows the type a field was declared with, not the
//! type an expression has, and so it gives up at the first `var` whose value
//! is anything but `new`. Past that point the only honest answer is the one a
//! compiler gives, and this layer is the compiler: the whole project bound
//! against its real references, and asked the questions an editor asks.
//!
//! * **Where is this declared?** The symbol the binder settled on, whether it
//!   is in the project or in an assembly — the overload the call chose, not
//!   every method with the name.
//! * **Where is this used?** Every name in the project spelled the same way,
//!   bound, and kept if it binds to the same symbol. Spelling first, because
//!   it is free and throws away nearly everything; binding second, and only
//!   the bodies a candidate is in.
//! * **What can go here?** The members of the type to the left of a `.`, or
//!   everything in scope where there is no `.`.
//!
//! Building it costs what declaring the project costs — seconds on a large
//! one — so it is built in the background and replaced wholesale, like the
//! index. Binding is on demand and by body: a question about one name binds
//! the one method it is in.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use rustlyn_semantics::{
    Accessibility, BoundBody, BoundSymbol, Compilation, MethodKind, Modifiers, SemanticModel,
    SpecialType, Speculation, SymbolId, SymbolKind, Type, TypeKind,
};
use rustlyn_syntax::{ParseOptions, SyntaxKind, SyntaxNode, SyntaxToken, SyntaxTree, parse_with};
use rustlyn_text::{SourceText, TextSpan};

mod actions;
mod assist;
mod classify;
mod complete;
mod lens;
mod occurrences;
mod references;
mod rename;

pub use actions::{ActionKind, CodeAction, Context as ActionContext};
// MARK: - refactoring dialogs
pub use actions::{
    AddedParameter, ChangeParam, DialogKind, DialogMember, DialogMembers, ExtractedMember,
    SignatureParameter, SignatureTarget,
};
pub use assist::{Documentation, Signature, Signatures, parse_documentation};
pub use classify::{SemanticClass, SemanticModifiers, SemanticToken};
pub use complete::completion_trigger;
pub use lens::Lens;
pub use occurrences::{Highlight, HighlightKind, keyword_highlights};
pub use references::{Reference, ReferenceKind};
pub use rename::{Conflict, RenameOptions, RenameTarget, Renamed};

// MARK: - inlay hints, IDE analyzers, quick info

mod analyzers;
mod inlay;
mod quick_info;
mod walk;

pub use analyzers::AnalyzerDiagnostic;
pub use inlay::{InlayHint, InlayHintKind, InlayHintOptions};
pub use quick_info::QuickInfo;

// MARK: - navigation: types, bases, implementations, calls
mod hierarchy;
mod implicit;
mod links;
pub use hierarchy::{HierarchyItem, IncomingCall, OutgoingCall};
pub use implicit::UseKind;
pub use links::{FileLinks, Link, LinkRole, LinkSymbol, LinkTarget};

// MARK: - Unity: the methods the engine calls by name
pub mod unity;

// MARK: - failability: what can make a member fail, and whether it can happen
mod failability;
pub use failability::{
    CallStep, Condition, Failability, Failure, FailureKind, Input, Origin, Verdict,
};

use crate::project::{Project, ProjectKind};
use crate::wire::{Reader, Writer};

/// The project compiled: every file's tree and every symbol, ready to be
/// asked about.
pub struct Semantic {
    compilation: Compilation,
    project: Project,
    /// Which tree of the compilation each file is.
    trees: HashMap<PathBuf, usize>,
    paths: HashMap<usize, PathBuf>,
    /// Each reference by its file's name, lower-cased: where a jump into an
    /// assembly lands.
    assemblies: HashMap<String, PathBuf>,
    /// How many reference assemblies went in, for saying so.
    references: usize,
    /// Each reference with the length and modification time it was read
    /// at: what says, next time, whether the same assemblies are there.
    reference_stamps: Vec<(PathBuf, Stamp)>,
    /// Bodies bound so far, by tree and the span of the member that owns
    /// them. An editor asks about the method it is in over and over, and a
    /// long method takes longer to bind than everything else a question
    /// costs.
    bodies: Mutex<HashMap<(usize, TextSpan), Arc<BoundBody>>>,
    /// Every type and extension method there is, by namespace: what import
    /// completion searches. Made the first time it is asked for.
    completion_index: std::sync::OnceLock<Arc<complete::ImportIndex>>,
    /// What the project reaches without naming it, by the constructs
    /// searched: see [`implicit`].
    implicit: Mutex<HashMap<(u32, rustlyn_semantics::SymbolId), Arc<implicit::ImplicitIndex>>>,
    /// The names a body mentions that can bring it a value of a type, by
    /// that type: see [`implicit`].
    reaching: Mutex<HashMap<rustlyn_semantics::SymbolId, Arc<implicit::Reach>>>,
    /// The types the signature of each member of the project mentions: what
    /// [`implicit`] looks up the members that bring a value of a type by.
    member_types: std::sync::OnceLock<Vec<implicit::MemberTypes>>,
    /// What every question of [`failability`] finds out about the project
    /// as a whole: where each name is used, who calls what.
    failing: failability::Shared,
}

/// How many bound bodies are kept before the cache starts over. A body is
/// kilobytes to tens of kilobytes.
const KEPT_BODIES: usize = 4096;

impl Drop for Semantic {
    fn drop(&mut self) {
        // A bound body is dropped level by level, as deep as the code it
        // was bound from: the bodies this kept are let go on a stack made
        // for that, wherever the last of the project's users is.
        let kept = std::mem::take(
            &mut *self
                .bodies
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        );
        if !kept.is_empty() {
            rustlyn_semantics::parallel::deep(move || drop(kept));
        }
    }
}

impl std::fmt::Debug for Semantic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Semantic")
            .field("files", &self.trees.len())
            .field("references", &self.references)
            .finish_non_exhaustive()
    }
}

/// What the cursor is on, once bound.
#[derive(Clone, Debug, PartialEq)]
pub enum Resolved {
    Symbol(SymbolId),
    /// A local variable or a lambda's parameter: it has no symbol of its own,
    /// only a place in the body that declared it.
    Local {
        tree: usize,
        span: TextSpan,
        name: String,
        ty: Type,
    },
}

/// Somewhere a jump can land, before it is put in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    /// A span of a source file, in bytes.
    Source { path: PathBuf, span: TextSpan },
    /// A type or member in an assembly.
    Metadata {
        assembly: PathBuf,
        /// The type as metadata names it: `Namespace.Outer/Inner`.
        type_name: String,
        /// The member's name inside it, for a member.
        member: Option<String>,
    },
}

/// A declaration found for a name, with what to call it in a list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Found {
    pub place: Place,
    pub kind: crate::outline::DeclarationKind,
    /// The qualified name, as a list of candidates shows it.
    pub name: String,
}

/// One entry of a completion list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    pub label: String,
    pub kind: CompletionKind,
    /// The type or signature, shown beside the name.
    pub detail: String,
    /// Lower sorts first: locals before members before types before keywords.
    pub rank: u8,
    /// What to write in place of the word when it is not the label:
    /// `List<int>` for a preselected type, `@class` for a name that is a
    /// keyword, a whole member for an override.
    pub insert_text: Option<String>,
    /// What the typed word is matched against when it is not the label:
    /// `ToString` for the override labelled `ToString()`.
    pub filter_text: Option<String>,
    /// Edits elsewhere in the file that go with this one, in bytes of the
    /// text asked about: the `using` an unimported type needs, the modifiers
    /// an override rewrites. They never overlap the word being replaced.
    pub additional_edits: Vec<crate::edit::TextEdit>,
    /// Whether this is the item to select when the list opens: the type
    /// after `new`, the members of the enum a comparison wants.
    pub preselect: bool,
    /// Characters that commit this item as well as typing them, when they
    /// differ from the editor's usual ones. Empty means the usual ones.
    pub commit_characters: String,
    /// Whether `insert_text` is a template with `caret` inside it.
    pub is_snippet: bool,
    /// Where the cursor goes after inserting, in bytes into `insert_text`
    /// (UTF-16 code units once a session hands it out). `None` is the end.
    pub caret: Option<u32>,
    /// The symbol this item offers, for its description.
    pub symbol: Option<SymbolId>,
}

/// What a completion is, which decides its icon.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum CompletionKind {
    Method = 0,
    Field,
    Property,
    Event,
    Local,
    Parameter,
    Class,
    Struct,
    Interface,
    Enum,
    EnumMember,
    Delegate,
    Namespace,
    Keyword,
    TypeParameter,
    Constant,
    /// A piece of code with a shortcut name: `cw`, `prop`, `for`.
    Snippet,
}

/// What a completion list is for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completions {
    pub items: Vec<Completion>,
    /// Where the word being completed starts, in bytes: everything from here
    /// to the cursor is what the editor filters by and replaces.
    pub start: u32,
    /// Where a new name is being written, so nothing should be committed by
    /// typing a space or a punctuation character: the names offered are
    /// suggestions, not the only choices.
    pub suggestion_mode: bool,
}

impl Semantic {
    /// Compiles `sources` against `references`.
    ///
    /// Each source is a path and its text: the editor's copy for a file it has
    /// open, the disk's otherwise. A file whose text is the same as in
    /// `previous` keeps its tree rather than being parsed again, which is most
    /// of them after a save.
    #[must_use]
    pub fn build(
        project: Project,
        sources: Vec<(PathBuf, String)>,
        references: &[(PathBuf, Arc<[u8]>)],
        previous: Option<&Self>,
    ) -> Self {
        // Each file is parsed as the version of C# its project is written in:
        // `field` is a name to a Unity script and a keyword to C# 14.
        let owners = {
            let paths: Vec<&Path> = sources.iter().map(|(path, _)| path.as_path()).collect();
            project.owners_of(&paths)
        };
        let options: HashMap<u16, ParseOptions> = owners
            .iter()
            .map(|&owner| (owner, project.parse_options(owner)))
            .collect();
        let reused = |path: &Path, text: &str| -> Option<SyntaxTree> {
            let previous = previous?;
            let &index = previous.trees.get(path)?;
            let trees = previous.compilation.trees();
            let same = trees.source(index)?.text() == text
                && previous.project.symbols == project.symbols
                && previous.project.assembly_symbols == project.assembly_symbols
                && previous.project.language_versions == project.language_versions;
            same.then(|| trees.get(index).cloned()).flatten()
        };

        let mut trees: Vec<Option<SyntaxTree>> = vec![None; sources.len()];
        parallel(sources.len(), |index| {
            let (path, text) = &sources[index];
            reused(path, text).unwrap_or_else(|| {
                parse_with(
                    SourceText::new(path.to_string_lossy(), text.as_str()),
                    &options[&owners[index]],
                )
            })
        })
        .into_iter()
        .enumerate()
        .for_each(|(index, tree)| trees[index] = Some(tree));
        let mut trees: Vec<SyntaxTree> = trees.into_iter().flatten().collect();
        let files = trees.len();
        if !project.generated.is_empty() {
            trees.push(parse_with(
                SourceText::new("<generated>", project.generated.as_str()),
                &project.parse_options(u16::MAX),
            ));
        }

        // Without a core library among the references there is no
        // `System.Object`, and nothing would bind at all. The synthesised one
        // is small, but everything in it is real.
        let has_core = references.iter().any(|(path, _)| is_core_library(path));
        // A save inside bodies declares nothing new: the previous
        // compilation with the edited files' trees in it is this one, made
        // without declaring the rest of the project again.
        let quick = previous.and_then(|previous| {
            let reference_stamps: Vec<(PathBuf, Stamp)> = references
                .iter()
                .map(|(path, _)| (path.clone(), Stamp::of(path)))
                .collect();
            if previous.project != project
                || previous.references != if has_core { references.len() } else { 0 }
                || previous.reference_stamps != reference_stamps
                || previous.paths.len() != files
            {
                return None;
            }
            let earlier = previous.compilation.trees();
            let offset = earlier.len() - files - usize::from(!project.generated.is_empty());
            let mut edited = Vec::new();
            for (index, (path, _)) in sources.iter().enumerate() {
                if previous.paths.get(&(offset + index)) != Some(path) {
                    return None;
                }
                if earlier.source(offset + index)?.text() != trees[index].source().text() {
                    edited.push((offset + index, trees[index].clone()));
                }
            }
            previous.compilation.with_trees_replaced(edited)
        });
        let mut compilation = match quick {
            Some(compilation) => compilation,
            None if has_core => {
                let images: Vec<&[u8]> = references.iter().map(|(_, bytes)| &bytes[..]).collect();
                let names: Vec<&str> = project.assemblies.iter().map(String::as_str).collect();
                Compilation::create_with_references_as_any(trees, &images, &names)
            }
            None => Compilation::create(trees),
        };
        let offset = compilation.trees().len() - files - usize::from(!project.generated.is_empty());
        // Which project each file is of: a reference's internals are for the
        // code of the assemblies it names in an `[InternalsVisibleTo]`.
        if !project.assemblies.is_empty() {
            let mut by_tree = vec![u16::MAX; compilation.trees().len()];
            for (index, owner) in owners.iter().enumerate() {
                by_tree[offset + index] = *owner;
            }
            compilation.set_tree_assemblies(by_tree);
            compilation.set_assembly_references(project.assembly_references.clone());
            compilation.set_metadata_references(project.assembly_metadata.clone());
            compilation.set_assembly_nullable(project.assembly_nullable.clone());
            compilation.set_source_friends(source_friends(&project, &sources, &owners));
            let shared: HashMap<&Path, Vec<u16>> =
                project
                    .shared_files
                    .iter()
                    .fold(HashMap::new(), |mut shared, (path, owner)| {
                        shared
                            .entry(path.as_path())
                            .or_insert_with(Vec::new)
                            .push(*owner);
                        shared
                    });
            let also: HashMap<usize, Vec<u16>> = sources
                .iter()
                .enumerate()
                .filter_map(|(index, (path, _))| {
                    Some((offset + index, shared.get(path.as_path())?.clone()))
                })
                .collect();
            compilation.set_tree_assemblies_also(also);
        }

        let mut tree_of = HashMap::new();
        let mut paths = HashMap::new();
        for (index, (path, _)) in sources.into_iter().enumerate() {
            tree_of.insert(path.clone(), offset + index);
            paths.insert(offset + index, path);
        }
        let assemblies = references
            .iter()
            .filter_map(|(path, _)| {
                let stem = path.file_stem()?.to_string_lossy().to_ascii_lowercase();
                Some((stem, path.clone()))
            })
            .collect();
        Self {
            compilation,
            project,
            trees: tree_of,
            paths,
            assemblies,
            references: if has_core { references.len() } else { 0 },
            reference_stamps: references
                .iter()
                .map(|(path, _)| (path.clone(), Stamp::of(path)))
                .collect(),
            bodies: Mutex::new(HashMap::new()),
            completion_index: std::sync::OnceLock::new(),
            implicit: Mutex::new(HashMap::new()),
            reaching: Mutex::new(HashMap::new()),
            member_types: std::sync::OnceLock::new(),
            failing: failability::Shared::default(),
        }
    }

    #[must_use]
    pub const fn compilation(&self) -> &Compilation {
        &self.compilation
    }

    /// Whether compiling `sources` for `project` would give this compilation
    /// again: the same project, the same files with the same text, and the
    /// same assemblies as they were read.
    ///
    /// This is what makes compiling after opening a project free when the
    /// project is as it was: the compilation read back from disk is
    /// compared with the files, and the comparison is reading them, which
    /// compiling would have done first anyway.
    #[must_use]
    pub fn unchanged(&self, project: &Project, sources: &[(PathBuf, String)]) -> bool {
        if *project != self.project || sources.len() != self.trees.len() {
            return false;
        }
        let same_files = sources.iter().all(|(path, text)| {
            self.trees
                .get(path)
                .and_then(|&tree| self.compilation.trees().source(tree))
                .is_some_and(|source| source.text() == text)
        });
        same_files
            && self.reference_stamps.len() == project.references.len()
            && self
                .reference_stamps
                .iter()
                .all(|(path, stamp)| Stamp::of(path) == *stamp)
    }

    // MARK: - on disk

    /// The compilation as bytes, for [`Semantic::read`]: the project it was
    /// compiled as, which file each tree is, and the compilation itself.
    #[must_use]
    pub fn write(&self) -> Vec<u8> {
        let mut out = Writer::new();
        out.bytes(SNAPSHOT_MAGIC);
        write_program_stamp(&mut out);
        write_project(&mut out, &self.project);
        out.u64(self.references as u64);
        out.u32(self.reference_stamps.len() as u32);
        for (path, stamp) in &self.reference_stamps {
            out.str(&path.to_string_lossy());
            out.u64(stamp.length);
            out.u128(stamp.modified);
        }
        let mut paths: Vec<_> = self.paths.iter().collect();
        paths.sort_by_key(|(tree, _)| **tree);
        out.u32(paths.len() as u32);
        for (tree, path) in paths {
            out.u64(*tree as u64);
            out.str(&path.to_string_lossy());
        }
        out.bytes(&self.compilation.write_snapshot());
        out.finish()
    }

    /// A compilation read back from [`Semantic::write`], or `None` when the
    /// bytes are damaged, or were written by another build of this library
    /// — whose declarations may not be what this one would make.
    #[must_use]
    pub fn read(bytes: &[u8]) -> Option<Self> {
        let mut input = Reader::new(bytes);
        if input.bytes()? != SNAPSHOT_MAGIC || !read_program_stamp(&mut input)? {
            return None;
        }
        let project = read_project(&mut input)?;
        let references = usize::try_from(input.u64()?).ok()?;
        let reference_stamps = input.seq(|input| {
            let path = PathBuf::from(input.string()?);
            let length = input.u64()?;
            let modified = input.u128()?;
            Some((path, Stamp { length, modified }))
        })?;
        let listed = input.seq(|input| {
            let tree = usize::try_from(input.u64()?).ok()?;
            Some((tree, PathBuf::from(input.string()?)))
        })?;
        let compilation = Compilation::read_snapshot(input.bytes()?)?;
        if !input.is_done() {
            return None;
        }
        let mut trees = HashMap::new();
        let mut paths = HashMap::new();
        for (tree, path) in listed {
            if tree >= compilation.trees().len() {
                return None;
            }
            trees.insert(path.clone(), tree);
            paths.insert(tree, path);
        }
        let assemblies = reference_stamps
            .iter()
            .filter_map(|(path, _)| {
                let stem = path.file_stem()?.to_string_lossy().to_ascii_lowercase();
                Some((stem, path.clone()))
            })
            .collect();
        Some(Self {
            compilation,
            project,
            trees,
            paths,
            assemblies,
            references,
            reference_stamps,
            bodies: Mutex::new(HashMap::new()),
            completion_index: std::sync::OnceLock::new(),
            implicit: Mutex::new(HashMap::new()),
            reaching: Mutex::new(HashMap::new()),
            member_types: std::sync::OnceLock::new(),
            failing: failability::Shared::default(),
        })
    }

    #[must_use]
    pub const fn project(&self) -> &Project {
        &self.project
    }

    #[must_use]
    pub fn files(&self) -> usize {
        self.trees.len()
    }

    #[must_use]
    pub const fn reference_count(&self) -> usize {
        self.references
    }

    /// How to parse `path` again: as the version of C# its project is
    /// written in.
    #[must_use]
    pub fn parse_options_of(&self, path: &Path) -> ParseOptions {
        let owner = self
            .tree_index(path)
            .map_or(u16::MAX, |tree| self.compilation.tree_assembly(tree));
        self.project.parse_options(owner)
    }

    /// The text a file was compiled from, which is what every offset asked
    /// about it has to be an offset into.
    #[must_use]
    pub fn text(&self, path: &Path) -> Option<&str> {
        let &index = self.trees.get(path)?;
        Some(self.compilation.trees().source(index)?.text())
    }

    #[must_use]
    pub fn tree_index(&self, path: &Path) -> Option<usize> {
        self.trees.get(path).copied()
    }

    #[must_use]
    pub fn path_of(&self, tree: usize) -> Option<&Path> {
        self.paths.get(&tree).map(PathBuf::as_path)
    }

    /// A view of one of the compiled files.
    #[must_use]
    pub fn view(&self, tree: usize) -> Option<View<'_>> {
        let root = self.compilation.trees().get(tree)?.root();
        Some(View {
            semantic: self,
            tree,
            root,
            model: SemanticModel::new(&self.compilation, tree),
            bodies: HashMap::new(),
            above: HashMap::new(),
            contexts: HashMap::new(),
            speculation: None,
        })
    }

    /// A view of `path` as it reads now: `text` when the editor has changes
    /// the compilation has not seen, the compiled file otherwise.
    ///
    /// The changed file is parsed again, and nothing else is: its bodies are
    /// bound against the compilation as it is, through a [`Speculation`]
    /// that maps what the edit did not touch back onto what was compiled.
    #[must_use]
    pub fn view_of(&self, path: &Path, text: Option<&str>) -> Option<View<'_>> {
        let tree = self.tree_index(path)?;
        let compiled = self.compilation.trees().source(tree)?;
        let Some(text) = text.filter(|text| *text != compiled.text()) else {
            return self.view(tree);
        };
        let edited = parse_with(
            SourceText::new(path.to_string_lossy(), text),
            &self.parse_options_of(path),
        );
        let speculation = Speculation::new(tree, compiled.text(), &edited);
        Some(View {
            semantic: self,
            tree,
            root: edited.root(),
            model: SemanticModel::speculative(&self.compilation, speculation.clone()),
            bodies: HashMap::new(),
            above: HashMap::new(),
            contexts: HashMap::new(),
            speculation: Some(speculation),
        })
    }

    // MARK: - definition

    /// Where whatever is at `offset` of `path` was declared.
    ///
    /// `text` is the editor's copy of the file when it has changed since the
    /// compilation was built; offsets, in and out, are into that text.
    #[must_use]
    pub fn definition(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(String, Vec<Found>)> {
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        let resolved = view.resolve_definition(&token)?;
        let mut found = self.places_of(&resolved);
        view.move_into_edited(path, &resolved, &mut found);
        Some((token.value_text().to_string(), found))
    }

    /// Where a resolved name leads: every declaration of it, since a partial
    /// type has several.
    #[must_use]
    pub fn places_of(&self, resolved: &Resolved) -> Vec<Found> {
        match resolved {
            Resolved::Local {
                tree, span, name, ..
            } => self
                .path_of(*tree)
                .map(|path| Found {
                    place: Place::Source {
                        path: path.to_path_buf(),
                        span: *span,
                    },
                    kind: crate::outline::DeclarationKind::Field,
                    name: name.clone(),
                })
                .into_iter()
                .collect(),
            Resolved::Symbol(symbol) => self.declarations_of(*symbol),
        }
    }

    fn declarations_of(&self, symbol: SymbolId) -> Vec<Found> {
        let symbols = self.compilation.symbols();
        let kind = declaration_kind(&self.compilation, symbol);
        let name = symbols.qualified_name(symbol);

        if self.compilation.is_from_metadata(symbol) {
            return self
                .metadata_place(symbol)
                .map(|place| Found { place, kind, name })
                .into_iter()
                .collect();
        }

        let mut found = Vec::new();
        for location in &symbols.get(symbol).locations {
            if let Some(path) = self.path_of(location.tree) {
                found.push(Found {
                    place: Place::Source {
                        path: path.to_path_buf(),
                        span: location.span,
                    },
                    kind,
                    name: name.clone(),
                });
            }
        }
        // A constructor nobody wrote is the type's: go there.
        if found.is_empty()
            && let Some(container) = symbols.get(symbol).container
            && symbols.get(symbol).kind == SymbolKind::Method
        {
            return self.declarations_of(container);
        }
        found
    }

    /// Where in an assembly a symbol is: the type it is in, and its own name
    /// when it is a member.
    fn metadata_place(&self, symbol: SymbolId) -> Option<Place> {
        let symbols = self.compilation.symbols();
        let mut ty = symbol;
        while symbols.get(ty).kind != SymbolKind::NamedType {
            ty = symbols.get(ty).container?;
        }
        let member = (ty != symbol).then(|| symbols.get(symbol).metadata_name());
        let reference = self.compilation.assembly_of(ty)?;
        let assembly = self
            .assemblies
            .get(&reference.name.to_ascii_lowercase())?
            .clone();
        Some(Place::Metadata {
            assembly,
            type_name: symbols.metadata_qualified_name(ty).replace('+', "/"),
            member,
        })
    }

    // MARK: - references

    /// Every place in the project that refers to what is at `offset`,
    /// declarations included.
    #[must_use]
    pub fn references(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(String, Vec<(PathBuf, TextSpan)>)> {
        let tree = self.tree_index(path)?;
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        let target = view.resolve_use(&token)?;
        let word = token.value_text().to_string();

        // A local cannot be named outside the body that declared it.
        if let Resolved::Local { .. } = &target {
            let spans = view.matching_tokens(&word, &target);
            return Some((
                word,
                spans
                    .into_iter()
                    .map(|span| (path.to_path_buf(), span))
                    .collect(),
            ));
        }

        let name = match &target {
            Resolved::Symbol(symbol) => self.search_name(*symbol),
            Resolved::Local { name, .. } => name.clone(),
        };
        // The file being edited is searched as it is now; every other one as
        // compiled.
        let mut edited: Vec<(PathBuf, TextSpan)> = Vec::new();
        if view.speculation.is_some() {
            edited = view
                .matching_tokens(&name, &target)
                .into_iter()
                .map(|span| (path.to_path_buf(), span))
                .collect();
        }
        let candidates: Vec<usize> = self
            .paths
            .keys()
            .copied()
            .filter(|&other| other != tree || view.speculation.is_none())
            .collect();
        let found = parallel(candidates.len(), |index| {
            let tree = candidates[index];
            // The text, not the tree: most files do not have the word at
            // all, and parsing them to find that out is what this avoids.
            let Some(text) = self
                .compilation
                .trees()
                .source(tree)
                .map(|source| source.text())
            else {
                return Vec::new();
            };
            if !contains_word(text, &name)
                && !attribute_stem(&name).is_some_and(|stem| contains_word(text, stem))
            {
                return Vec::new();
            }
            let Some(mut view) = self.view(tree) else {
                return Vec::new();
            };
            let path = self.paths[&tree].clone();
            view.matching_tokens(&name, &target)
                .into_iter()
                .map(|span| (path.clone(), span))
                .collect::<Vec<_>>()
        });
        let mut found: Vec<(PathBuf, TextSpan)> =
            found.into_iter().flatten().chain(edited).collect();
        found.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.start().cmp(&b.1.start())));
        found.dedup();
        Some((word, found))
    }

    /// The word a use of `symbol` is spelled with: a constructor is called
    /// by its type's name, and an explicit implementation `IWidget.Pick` by
    /// the name its interface gives it.
    fn search_name(&self, symbol: SymbolId) -> String {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        if found
            .as_method()
            .is_some_and(|method| method.method_kind == MethodKind::Constructor)
            && let Some(container) = found.container
        {
            return symbols.get(container).name.clone();
        }
        references::short_name(&found.name).to_string()
    }

    // MARK: - completion

    /// What can be written at `offset` of `path`.
    #[must_use]
    pub fn completions(&self, path: &Path, offset: u32, text: Option<&str>) -> Option<Completions> {
        let mut view = self.view_of(path, text)?;
        Some(view.completions(offset))
    }

    /// A one-line description of a symbol: its signature or its type.
    #[must_use]
    pub fn describe(&self, resolved: &Resolved) -> String {
        match resolved {
            // Only a label has no type.
            Resolved::Local {
                name,
                ty: Type::Void,
                ..
            } => format!("label {name}"),
            Resolved::Local { name, ty, .. } => {
                format!("{} {name}", display_type(&self.compilation, ty))
            }
            Resolved::Symbol(symbol) => describe_symbol(&self.compilation, *symbol),
        }
    }
}

/// One compiled file, with the bodies bound so far kept for the next
/// question: finding every use of a name in a method binds that method once,
/// not once per use.
pub struct View<'a> {
    semantic: &'a Semantic,
    tree: usize,
    root: SyntaxNode,
    model: SemanticModel<'a>,
    bodies: HashMap<TextSpan, Arc<BoundBody>>,
    /// What climbing from a node finds, kept for every node climbed from or
    /// through: see [`Above`].
    above: HashMap<NodeKey, Above>,
    /// The scopes of the declarations asked about, worked out once each.
    contexts: HashMap<NodeKey, Arc<rustlyn_semantics::Context>>,
    /// Set when this is the editor's text rather than the compiled one.
    speculation: Option<Speculation>,
}

/// Which node of the tree: where it starts and the green node it is. The
/// green tree shares equal subtrees, so the place is part of it; no node
/// holds itself, so the pair is one node's alone.
type NodeKey = (u32, usize);

fn key_of(node: &SyntaxNode) -> NodeKey {
    (node.full_span().start(), Arc::as_ptr(node.green()) as usize)
}

/// What is above `node`: kept in `known` for every node climbed through, so
/// that the next question stops at the nearest node already asked about.
fn above_in(known: &mut HashMap<NodeKey, Above>, node: &SyntaxNode) -> Above {
    let mut pending: Vec<SyntaxNode> = Vec::new();
    let mut cursor = Some(node.clone());
    let mut found: Option<Above> = None;
    while let Some(current) = cursor {
        if let Some(above) = known.get(&key_of(&current)) {
            found = Some(above.clone());
            break;
        }
        cursor = current.parent().cloned();
        pending.push(current);
    }
    for current in pending.into_iter().rev() {
        let above = Above::of(&current, found.as_ref());
        known.insert(key_of(&current), above.clone());
        found = Some(above);
    }
    found.expect("the node itself is climbed from")
}

/// The scopes of `node`: those of the declaration it is in, kept in
/// `contexts`.
fn context_in(
    known: &mut HashMap<NodeKey, Above>,
    contexts: &mut HashMap<NodeKey, Arc<rustlyn_semantics::Context>>,
    binder: &rustlyn_semantics::Binder<'_>,
    tree: usize,
    root: &SyntaxNode,
    node: &SyntaxNode,
) -> Arc<rustlyn_semantics::Context> {
    let scope = above_in(known, node).scope.unwrap_or_else(|| root.clone());
    contexts
        .entry(key_of(&scope))
        .or_insert_with(|| Arc::new(binder.context_at(tree, &scope)))
        .clone()
}

/// What a name, or any node, needs to know of the nodes above it, which
/// asking afresh for each costs the depth of the tree: a chain of ten
/// thousand calls has a name at the bottom of every one of ten thousand
/// climbs. Kept for each node, it is worked out from its parent's, so that
/// the whole tree costs what one climb does.
#[derive(Clone)]
struct Above {
    /// The `Attribute` the node is in, if the code around it up to the
    /// body it is in has one.
    attribute: Option<SyntaxNode>,
    /// The clause that holds the node as a parameter's default value, an
    /// enum member's value or a fixed buffer's size, in the same reach.
    default: Option<SyntaxNode>,
    /// [`SemanticModel::body_owner`] of the node.
    owner: Option<SyntaxNode>,
    /// The declaration whose scopes the node is in: the node or the nearest
    /// node above it that opens one.
    scope: Option<SyntaxNode>,
    /// The nearest namespace declaration above the node.
    namespace: Option<SyntaxNode>,
    /// The nearest `using` or namespace declaration above the node.
    directive: Option<SyntaxNode>,
    /// The nearest `Attribute` above the node, in whatever it is on.
    enclosing_attribute: Option<SyntaxNode>,
}

impl Above {
    /// What the node finds, given what its parent found (`None` for the
    /// root).
    fn of(node: &SyntaxNode, parent: Option<&Above>) -> Self {
        let up = node.parent();
        let reaches = up.is_some_and(|up| !rustlyn_semantics::is_body_owner(up.kind()));
        let from_parent = |wanted: fn(&SyntaxNode) -> bool, inherited: Option<&SyntaxNode>| {
            let up = up?;
            if !reaches {
                None
            } else if wanted(up) {
                Some(up.clone())
            } else {
                inherited.cloned()
            }
        };
        let owner = match node.kind() {
            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => Some(node.clone()),
            kind if rustlyn_semantics::is_body_owner(kind) => Some(node.clone()),
            // A field's initializer belongs to its declarator, the outermost
            // one: `int a = 1, b = 2;` is two bodies.
            SyntaxKind::VariableDeclarator => match parent.and_then(|above| above.owner.as_ref()) {
                Some(found)
                    if matches!(
                        found.kind(),
                        SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                    ) =>
                {
                    Some(node.clone())
                }
                other => other.cloned(),
            },
            _ => parent.and_then(|above| above.owner.clone()),
        };
        let scope = if opens_scope(node.kind()) {
            Some(node.clone())
        } else {
            parent.and_then(|above| above.scope.clone())
        };
        Self {
            attribute: from_parent(
                |node| node.kind() == SyntaxKind::Attribute,
                parent.and_then(|above| above.attribute.as_ref()),
            ),
            default: from_parent(
                is_default_value,
                parent.and_then(|above| above.default.as_ref()),
            ),
            owner,
            scope,
            namespace: match up {
                Some(up) if up.kind() == SyntaxKind::NamespaceDeclaration => Some(up.clone()),
                _ => parent.and_then(|above| above.namespace.clone()),
            },
            directive: match up {
                Some(up)
                    if matches!(
                        up.kind(),
                        SyntaxKind::UsingDirective
                            | SyntaxKind::NamespaceDeclaration
                            | SyntaxKind::FileScopedNamespaceDeclaration
                    ) =>
                {
                    Some(up.clone())
                }
                _ => parent.and_then(|above| above.directive.clone()),
            },
            enclosing_attribute: match up {
                Some(up) if up.kind() == SyntaxKind::Attribute => Some(up.clone()),
                _ => parent.and_then(|above| above.enclosing_attribute.clone()),
            },
        }
    }
}

/// Whether a node is the clause of a parameter's default value, an enum
/// member's value, or a fixed buffer's size.
fn is_default_value(node: &SyntaxNode) -> bool {
    (node.kind() == SyntaxKind::EqualsValueClause
        && node.parent().is_some_and(|parent| {
            matches!(
                parent.kind(),
                SyntaxKind::Parameter | SyntaxKind::EnumMemberDeclaration
            )
        }))
        || (node.kind() == SyntaxKind::Argument
            && node.parent().is_some_and(|list| {
                list.kind() == SyntaxKind::BracketedArgumentList
                    && list
                        .parent()
                        .is_some_and(|parent| parent.kind() == SyntaxKind::VariableDeclarator)
            }))
}

/// Whether a declaration puts scopes around what is in it, as
/// [`rustlyn_semantics::Binder::context_at`] reads them off the ancestors.
const fn opens_scope(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::DelegateDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::ExtensionBlockDeclaration
            | SyntaxKind::NamespaceDeclaration
            | SyntaxKind::FileScopedNamespaceDeclaration
            | SyntaxKind::CompilationUnit
    )
}

impl std::fmt::Debug for View<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("View")
            .field("tree", &self.tree)
            .finish_non_exhaustive()
    }
}

impl<'a> View<'a> {
    fn compilation(&self) -> &'a Compilation {
        &self.semantic.compilation
    }

    /// Moves places in the file being edited from where the compilation has
    /// them to where they are in the editor's text. A local's place came
    /// from binding that text and is there already.
    fn move_into_edited(&self, path: &Path, resolved: &Resolved, found: &mut Vec<Found>) {
        let Some(speculation) = &self.speculation else {
            return;
        };
        if matches!(resolved, Resolved::Local { .. }) {
            return;
        }
        found.retain_mut(|found| match &mut found.place {
            Place::Source { path: at, span } if at == path => match speculation.unmap(*span) {
                Some(moved) => {
                    *span = moved;
                    true
                }
                // Declared inside what was changed: the declaration is not
                // where it was, and nothing says where it went.
                None => false,
            },
            _ => true,
        });
    }

    /// The name at `offset`, or just before it: a cursor at the end of a word
    /// is on that word.
    #[must_use]
    pub fn name_token_at(&self, offset: u32) -> Option<SyntaxToken> {
        let is_name = |token: &SyntaxToken| {
            matches!(
                token.kind(),
                SyntaxKind::IdentifierToken | SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword
            ) || token.parent().kind() == SyntaxKind::PredefinedType
        };
        let at = self
            .root
            .find_token(offset)
            .filter(|token| token.span().contains(offset) && is_name(token));
        at.or_else(|| {
            let before = self.root.find_token(offset.checked_sub(1)?)?;
            (before.span().end() == offset && is_name(&before)).then_some(before)
        })
    }

    /// What is above `node`, worked out from the nearest node above it that
    /// is known, and kept for every node on the way.
    fn above_of(&mut self, node: &SyntaxNode) -> Above {
        above_in(&mut self.above, node)
    }

    /// The scopes `node` sits in, as the binder reads them off its
    /// ancestors: worked out once for the declaration they are the scopes
    /// of, not once for each of what is inside it.
    fn context_at(&mut self, node: &SyntaxNode) -> Arc<rustlyn_semantics::Context> {
        context_in(
            &mut self.above,
            &mut self.contexts,
            self.model.binder(),
            self.tree,
            &self.root,
            node,
        )
    }

    /// The bound body `node` is in, bound once per view.
    fn body_for(&mut self, node: &SyntaxNode) -> Option<Arc<BoundBody>> {
        let owner = self.above_of(node).owner?;
        self.body_of(owner)
    }

    /// The bound body of `owner`, one of what [`SemanticModel::body_owner`]
    /// returns, bound once per view.
    fn body_of(&mut self, owner: SyntaxNode) -> Option<Arc<BoundBody>> {
        if owner.kind() == SyntaxKind::CompilationUnit
            && !owner
                .children()
                .any(|child| child.kind() == SyntaxKind::GlobalStatement)
        {
            return None;
        }
        if let Some(body) = self.bodies.get(&owner.span()) {
            return Some(body.clone());
        }
        if self.speculation.is_some() {
            // Bound against the editor's text: nobody else will ask about
            // this version of it.
            let body = Arc::new(self.model.bind_body_for_editor(&owner));
            self.bodies.insert(owner.span(), body.clone());
            return Some(body);
        }
        let key = (self.tree, owner.span());
        let shared = |semantic: &Semantic| {
            semantic
                .bodies
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .get(&key)
                .cloned()
        };
        let body = match shared(self.semantic) {
            Some(body) => body,
            None => {
                let body = Arc::new(self.model.bind_body_for_editor(&owner));
                let mut kept = self
                    .semantic
                    .bodies
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                if kept.len() >= KEPT_BODIES {
                    let dropped = std::mem::take(&mut *kept);
                    rustlyn_semantics::parallel::deep(move || drop(dropped));
                }
                kept.insert(key, body.clone());
                body
            }
        };
        self.bodies.insert(owner.span(), body.clone());
        Some(body)
    }

    /// What a name token refers to.
    pub fn resolve(&mut self, token: &SyntaxToken) -> Option<Resolved> {
        let parent = token.parent().clone();

        // The name of a declaration declares; it does not refer.
        if names_declaration(&parent, token)
            && let Some(symbol) = self.model.declared_symbol(&parent)
        {
            return Some(Resolved::Symbol(symbol));
        }

        // `goto retry;` and `retry:` are the label: a place in the code
        // around them, with no type and no symbol.
        if matches!(
            parent.kind(),
            SyntaxKind::GotoStatement | SyntaxKind::LabeledStatement
        ) {
            return self.label(token, &parent);
        }

        // A name in an attribute's arguments is bound with the attribute,
        // not with the body of what it is on.
        let above = self.above_of(&parent);
        let attribute = above.attribute;
        // So is a parameter's default value, with the parameter, an enum
        // member's value and the size of a fixed buffer.
        let default = above
            .default
            .and_then(|clause| clause.children().find(|child| child.kind().is_expression()));
        let body = match (attribute, default) {
            (Some(attribute), _) => Some(match self.bodies.get(&attribute.span()) {
                Some(body) => body.clone(),
                None => {
                    let body = Arc::new(self.model.bind_attribute_for_editor(&attribute));
                    self.bodies.insert(attribute.span(), body.clone());
                    body
                }
            }),
            (None, Some(value)) => Some(match self.bodies.get(&value.span()) {
                Some(body) => body.clone(),
                None => {
                    let body = Arc::new(self.model.bind_default_for_editor(&value));
                    self.bodies.insert(value.span(), body.clone());
                    body
                }
            }),
            (None, None) => above.owner.and_then(|owner| self.body_of(owner)),
        };
        if let Some(body) = body {
            match body.symbol_at(token.span()) {
                Some(BoundSymbol::Declared(symbol)) => return Some(Resolved::Symbol(symbol)),
                Some(BoundSymbol::Local(local)) => {
                    let local = body.locals.get(local.0 as usize)?;
                    return Some(Resolved::Local {
                        tree: self.tree,
                        span: local.span,
                        name: local.name.clone(),
                        ty: local.ty.clone(),
                    });
                }
                None => {}
            }
        }

        // `this` and `base` are the type the code is in, and its base.
        if matches!(
            token.kind(),
            SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword
        ) {
            let context = self.model.binder().context_at(self.tree, &parent);
            let ty = context.enclosing_type()?;
            if token.kind() == SyntaxKind::BaseKeyword {
                return match self.model.binder().base_class_of(ty) {
                    Some(Type::Named { symbol, .. }) => Some(Resolved::Symbol(symbol)),
                    _ => None,
                };
            }
            return Some(Resolved::Symbol(ty));
        }

        // `int` is `System.Int32`.
        if parent.kind() == SyntaxKind::PredefinedType {
            return match self.model.type_of_syntax(&parent) {
                Type::Named { symbol, .. } => Some(Resolved::Symbol(symbol)),
                _ => None,
            };
        }

        if let Some(resolved) = self.resolve_special(token, &parent) {
            return Some(resolved);
        }

        // Everything the bodies do not cover: types in signatures, base
        // lists, `using` directives, attributes.
        let (above, contexts, tree, root) =
            (&mut self.above, &mut self.contexts, self.tree, &self.root);
        let binder = self.model.binder();
        self.model
            .symbol_at_with(&parent, &mut |at| {
                context_in(above, contexts, binder, tree, root, at)
            })
            .map(Resolved::Symbol)
    }

    /// The label a `goto` names, or a label itself, as the place it is
    /// written: labels are seen anywhere in the function they are in.
    fn label(&self, token: &SyntaxToken, parent: &SyntaxNode) -> Option<Resolved> {
        let name = token.value_text();
        let function = parent.ancestors().find(|node| {
            rustlyn_semantics::is_body_owner(node.kind())
                || matches!(
                    node.kind(),
                    SyntaxKind::LocalFunctionStatement
                        | SyntaxKind::SimpleLambdaExpression
                        | SyntaxKind::ParenthesizedLambdaExpression
                        | SyntaxKind::AnonymousMethodExpression
                        | SyntaxKind::CompilationUnit
                )
        })?;
        let label = function
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::LabeledStatement)
            .filter_map(|node| {
                node.child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            })
            .find(|label| label.value_text() == name)?;
        Some(Resolved::Local {
            tree: self.tree,
            span: label.span(),
            name: name.to_string(),
            ty: Type::Void,
        })
    }

    /// The names the binder does not record because they are not
    /// expressions: `var`, namespaces, attribute names, named arguments.
    fn resolve_special(&mut self, token: &SyntaxToken, parent: &SyntaxNode) -> Option<Resolved> {
        let grand = parent.parent().cloned();

        // `delegate* unmanaged[Cdecl]` names `CallConvCdecl`.
        if parent.kind() == SyntaxKind::FunctionPointerUnmanagedCallingConvention {
            return self
                .compilation()
                .type_by_metadata_name(&format!(
                    "System.Runtime.CompilerServices.CallConv{}",
                    token.value_text()
                ))
                .map(Resolved::Symbol);
        }

        // `new { slotRef = key }` declares the anonymous type's property.
        if parent.kind() == SyntaxKind::NameEquals
            && let Some(creation) = grand
                .as_ref()
                .filter(|grand| grand.kind() == SyntaxKind::AnonymousObjectMemberDeclarator)
                .and_then(|declarator| {
                    declarator
                        .ancestors()
                        .find(|node| node.kind() == SyntaxKind::AnonymousObjectCreationExpression)
                })
            && let Some(body) = self.body_for(&creation)
            && let Some(ty) = body.type_at(creation.span()).and_then(Type::symbol)
        {
            return self
                .model
                .binder()
                .lookup_member(ty, token.value_text())
                .first()
                .copied()
                .map(Resolved::Symbol);
        }

        // The name `using Real = System.Single;` declares is what it stands
        // for.
        if parent.kind() == SyntaxKind::NameEquals
            && let Some(directive) = grand
                .as_ref()
                .filter(|grand| grand.kind() == SyntaxKind::UsingDirective)
            && let Some(target) = directive
                .children()
                .filter(|child| child.kind().is_type_node())
                .last()
        {
            return self.model.symbol_at(&target).map(Resolved::Symbol);
        }

        // `global::` is the global namespace, and `Alias::` the namespace an
        // `extern alias` gives a reference.
        if parent.kind() == SyntaxKind::IdentifierName
            && let Some(qualified) = grand
                .as_ref()
                .filter(|grand| grand.kind() == SyntaxKind::AliasQualifiedName)
            && qualified
                .children()
                .next()
                .is_some_and(|first| first.span() == parent.span())
        {
            let name = token.value_text();
            return if name == "global" {
                Some(Resolved::Symbol(self.compilation().global_namespace()))
            } else {
                self.compilation().extern_alias(name).map(Resolved::Symbol)
            };
        }

        // `var` is the type of what it declares. `ref var` and `scoped var`
        // wrap it in one more node.
        let declaration = grand.as_ref().and_then(|grand| {
            if matches!(grand.kind(), SyntaxKind::RefType | SyntaxKind::ScopedType) {
                grand.parent().cloned()
            } else {
                Some(grand.clone())
            }
        });
        if token.value_text() == "var"
            && parent.kind() == SyntaxKind::IdentifierName
            && let Some(declaration) = declaration.filter(|declaration| {
                matches!(
                    declaration.kind(),
                    SyntaxKind::VariableDeclaration
                        | SyntaxKind::ForEachStatement
                        | SyntaxKind::DeclarationExpression
                        | SyntaxKind::DeclarationPattern
                )
            })
        {
            let body = self.body_for(parent)?;
            // `var (s, t) = pair` stands for the tuple, not for `s`: a
            // `ValueTuple` of as many as it designates.
            let designation =
                declaration.child_of_kind(SyntaxKind::ParenthesizedVariableDesignation);
            if let Some(designation) = &designation {
                let count = designation
                    .children()
                    .filter(|child| {
                        matches!(
                            child.kind(),
                            SyntaxKind::SingleVariableDesignation
                                | SyntaxKind::DiscardDesignation
                                | SyntaxKind::ParenthesizedVariableDesignation
                        )
                    })
                    .count();
                return self
                    .compilation()
                    .type_by_metadata_name(&format!("System.ValueTuple`{}", count.clamp(1, 8)))
                    .map(Resolved::Symbol);
            }
            let deconstructs = false;
            let local = (!deconstructs).then_some(()).and_then(|()| {
                declaration
                    .descendant_tokens()
                    .filter(|other| {
                        other.kind() == SyntaxKind::IdentifierToken
                            && other.span().start() > token.span().start()
                    })
                    .find_map(|other| match body.symbol_at(other.span()) {
                        Some(BoundSymbol::Local(local)) => body
                            .locals
                            .get(local.0 as usize)
                            .map(|local| local.ty.clone()),
                        _ => None,
                    })
            });
            // `out var _` declares nothing to look up: the expression has
            // the type all the same.
            let ty = local.or_else(|| {
                (declaration.kind() == SyntaxKind::DeclarationExpression || deconstructs)
                    .then(|| body.type_at(declaration.span()).cloned())
                    .flatten()
            })?;
            // `var buffer = new char[n]` is a `char[]`: what there is to go to
            // is `char`.
            let mut ty = ty;
            while let Type::Array { element, .. } | Type::Pointer(element) = ty {
                ty = *element;
            }
            return match ty {
                Type::Named { symbol, .. } | Type::TypeParameter(symbol) => {
                    Some(Resolved::Symbol(symbol))
                }
                // `var pair = (1, "a")` is a `ValueTuple<int, string>`.
                Type::Tuple(elements) => self
                    .compilation()
                    .type_by_metadata_name(&format!("System.ValueTuple`{}", elements.len().min(8)))
                    .map(Resolved::Symbol),
                // `var p = buffer.GetUnsafePtr()` is a `void*`.
                Type::Void => self
                    .compilation()
                    .type_by_metadata_name("System.Void")
                    .map(Resolved::Symbol),
                _ => None,
            };
        }

        // `where T : ...` names a type parameter of what it constrains.
        if parent.kind() == SyntaxKind::TypeParameterConstraintClause
            && let Some(owner) = parent.parent()
            && let Some(declared) = self.model.declared_symbol(owner)
        {
            let symbols = self.compilation().symbols();
            let found = symbols
                .get(declared)
                .members
                .iter()
                .copied()
                .find(|&member| {
                    symbols.get(member).kind == SymbolKind::TypeParameter
                        && symbols.get(member).name == token.value_text()
                });
            if let Some(found) = found {
                return Some(Resolved::Symbol(found));
            }
        }

        // The name of a namespace, in `using` or `namespace`: looked up from
        // the global namespace, as far as the cursor.
        let above = self.above_of(parent);
        if let Some(directive) = above.directive
            && let Some(name) = directive
                .children()
                .find(|child| child.kind().is_type_node())
            && name.span().contains_span(token.span())
        {
            let symbols = self.compilation().symbols();
            let written = self
                .root
                .full_text()
                .get(name.span().start() as usize..token.span().end() as usize)?
                .to_string();
            let written = written.trim_start_matches("global::");
            let mut current = self.compilation().global_namespace();
            let mut found = true;
            for part in written.split('.') {
                match symbols.lookup_namespace(current, part.trim()) {
                    Some(next) => current = next,
                    None => {
                        found = false;
                        break;
                    }
                }
            }
            if found {
                return Some(Resolved::Symbol(current));
            }
        }

        // `[Serializable]` is `SerializableAttribute`, and `[X(Name = 1)]`
        // names a property of it.
        if let Some(attribute) = above.enclosing_attribute {
            let ty = self.attribute_type(&attribute);
            if let Some(name) = attribute.children().next()
                && name.span().contains_span(token.span())
            {
                // Its last name is the attribute; a name before it, the
                // `System` of `[System.Serializable]`, is what it names.
                if name
                    .last_token()
                    .is_some_and(|last| last.span() == token.span())
                {
                    return ty.map(Resolved::Symbol);
                }
                let written: String = name.text().to_string()
                    [..usize::try_from(token.span().end() - name.span().start()).unwrap_or(0)]
                    .chars()
                    .filter(|c| !c.is_whitespace())
                    .collect();
                let symbols = self.compilation().symbols();
                let mut current = Some(self.compilation().global_namespace());
                for part in written.trim_start_matches("global::").split('.') {
                    current = current.and_then(|at| symbols.lookup_namespace(at, part));
                }
                return current
                    .or_else(|| self.model.symbol_at(parent))
                    .map(Resolved::Symbol);
            }
            if let Some(ty) = ty
                && std::iter::once(parent.clone())
                    .chain(parent.ancestors())
                    .any(|ancestor| ancestor.kind() == SyntaxKind::NameEquals)
            {
                return self
                    .model
                    .binder()
                    .lookup_member(ty, token.value_text())
                    .first()
                    .copied()
                    .map(Resolved::Symbol);
            }
        }

        // `Call(expected: false)`: the parameter of the method called.
        // `: base(name: x)` and `: this(name: x)` call a constructor that is
        // not written anywhere in the call: the base type's, or this type's.
        if parent.kind() == SyntaxKind::NameColon
            && let Some(initializer) = parent.ancestors().find(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer
                )
            })
        {
            let context = self.model.binder().context_at(self.tree, &initializer);
            let own = context.enclosing_type()?;
            let target = if initializer.kind() == SyntaxKind::BaseConstructorInitializer {
                match self.model.binder().base_class_of(own)? {
                    Type::Named { symbol, .. } => symbol,
                    _ => return None,
                }
            } else {
                own
            };
            let symbols = self.compilation().symbols();
            return symbols
                .get(target)
                .members
                .iter()
                .filter_map(|&member| symbols.get(member).as_method())
                .filter(|method| method.method_kind == MethodKind::Constructor)
                .flat_map(|method| method.parameters.iter().copied())
                .find(|&parameter| symbols.get(parameter).name == token.value_text())
                .map(Resolved::Symbol);
        }

        // The name of a `name:` is the colon's own token.
        if (parent.kind() == SyntaxKind::NameColon
            || grand
                .as_ref()
                .is_some_and(|grand| grand.kind() == SyntaxKind::NameColon))
            && let Some(call) = parent.ancestors().find(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::InvocationExpression | SyntaxKind::ObjectCreationExpression
                )
            })
        {
            let callee = if call.kind() == SyntaxKind::InvocationExpression {
                call.children().next()
            } else {
                call.children().find(|child| child.kind().is_type_node())
            }?;
            let name = callee
                .descendant_tokens()
                .filter(|other| other.kind() == SyntaxKind::IdentifierToken)
                .last()?;
            let body = self.body_for(&call)?;
            let Some(BoundSymbol::Declared(called)) = body.symbol_at(name.span()) else {
                return None;
            };
            // The overload the call chose, then its siblings: when the call
            // did not bind, what was recorded is the type or the first
            // candidate, and the name still says which parameter it meant.
            let symbols = self.compilation().symbols();
            let found = symbols.get(called);
            let mut candidates = vec![called];
            let siblings: Vec<SymbolId> = match found.kind {
                SymbolKind::NamedType => found.members.clone(),
                SymbolKind::Method => found
                    .container
                    .map(|container| symbols.get(container).members.clone())
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|&member| symbols.get(member).name == found.name)
                    .collect(),
                _ => Vec::new(),
            };
            candidates.extend(siblings.into_iter().filter(|&member| {
                symbols.get(member).as_method().is_some_and(|method| {
                    found.kind == SymbolKind::Method
                        || method.method_kind == MethodKind::Constructor
                })
            }));
            return candidates
                .into_iter()
                .filter_map(|candidate| symbols.get(candidate).as_method())
                .flat_map(|method| method.parameters.iter().copied())
                .find(|&parameter| symbols.get(parameter).name == token.value_text())
                .map(Resolved::Symbol);
        }
        None
    }

    /// The class an attribute names: `X`, or `XAttribute` when there is no
    /// `X` that is one.
    fn attribute_type(&self, attribute: &SyntaxNode) -> Option<SymbolId> {
        let name = attribute.children().next()?;
        let written = name.text();
        let written = written.trim();
        let last = written.rsplit('.').next()?.trim();
        let context = self.model.binder().context_at(self.tree, attribute);
        let binder = self.model.binder();
        let with_suffix = format!("{last}Attribute");
        // `[System.Diagnostics.CodeAnalysis.SuppressMessage]`: the namespace
        // is written out, and needs no `using`.
        if let Some((namespace, _)) = written.rsplit_once('.') {
            let symbols = self.compilation().symbols();
            let mut current = Some(self.compilation().global_namespace());
            for part in namespace.trim_start_matches("global::").split('.') {
                current = current.and_then(|at| symbols.lookup_namespace(at, part.trim()));
            }
            // Or what it names in scope: an alias of a namespace, as in
            // `[ShaderKeywordFilter.RemoveIf]` under `using
            // ShaderKeywordFilter = UnityEditor.ShaderKeywordFilter;`.
            let current = current.or_else(|| {
                let left = name
                    .children()
                    .next()
                    .filter(|_| name.kind() == SyntaxKind::QualifiedName)?;
                self.model.symbol_at(&left)
            });
            if let Some(namespace) = current {
                let found = symbols
                    .lookup_type(namespace, &with_suffix, 0)
                    .or_else(|| symbols.lookup_type(namespace, last, 0));
                if found.is_some() {
                    return found;
                }
            }
        }
        binder
            .lookup(&with_suffix, 0, &context)
            .or_else(|| binder.lookup(last, 0, &context))
            .or_else(|| match self.model.type_of_syntax(&name) {
                Type::Named { symbol, .. } => Some(symbol),
                _ => None,
            })
    }

    /// Every token spelled `name` in this file that resolves to `target`.
    fn matching_tokens(&mut self, name: &str, target: &Resolved) -> Vec<TextSpan> {
        // `[Serializable]` is a use of `SerializableAttribute`.
        let stem = attribute_stem(name);
        let tokens: Vec<SyntaxToken> = self
            .root
            .descendant_tokens()
            .filter(|token| {
                token.kind() == SyntaxKind::IdentifierToken
                    && (token.value_text() == name
                        || stem.is_some_and(|stem| token.value_text() == stem))
            })
            .collect();
        let mut found = Vec::new();
        for token in tokens {
            let Some(resolved) = self.resolve_use(&token) else {
                continue;
            };
            if self.same(&resolved, target) {
                found.push(token.span());
            }
        }
        found
    }

    /// Whether a use refers to the target. A `new C()` refers to `C` as well
    /// as to its constructor, and a use of a generic method's instance is a
    /// use of the method.
    fn same(&self, resolved: &Resolved, target: &Resolved) -> bool {
        match (resolved, target) {
            (Resolved::Symbol(a), Resolved::Symbol(b)) => {
                if a == b {
                    return true;
                }
                let symbols = self.compilation().symbols();
                let is_constructor = |symbol: SymbolId| {
                    symbols
                        .get(symbol)
                        .as_method()
                        .is_some_and(|method| method.method_kind == MethodKind::Constructor)
                };
                (is_constructor(*a) && symbols.get(*a).container == Some(*b))
                    || (is_constructor(*b) && symbols.get(*b).container == Some(*a))
            }
            (Resolved::Local { span: a, .. }, Resolved::Local { span: b, .. }) => a == b,
            _ => false,
        }
    }

    // MARK: - completion

    /// What can be written at `offset`: what the providers of
    /// [`complete`] find for the place it is in.
    pub fn completions(&mut self, offset: u32) -> Completions {
        self.complete(offset)
    }

    /// After `x.`: the members of whatever `x` is.
    fn member_completions(&mut self, dot: &SyntaxToken, items: &mut Vec<Completion>) {
        let parent = dot.parent().clone();
        let receiver = match parent.kind() {
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName => {
                parent.children().next()
            }
            // `x.‸.Name`, read as the range `x..Name` — and `!x..Name` as
            // the range from `!x`, whose member it still is of `x`.
            SyntaxKind::RangeExpression => {
                let mut left = parent
                    .children()
                    .next()
                    .filter(|left| left.span().end() == dot.span().start());
                while let Some(operand) = left.as_ref().filter(|left| {
                    matches!(
                        left.kind(),
                        SyntaxKind::UnaryPlusExpression
                            | SyntaxKind::UnaryMinusExpression
                            | SyntaxKind::BitwiseNotExpression
                            | SyntaxKind::LogicalNotExpression
                            | SyntaxKind::PreIncrementExpression
                            | SyntaxKind::PreDecrementExpression
                            | SyntaxKind::PointerIndirectionExpression
                            | SyntaxKind::AddressOfExpression
                            | SyntaxKind::AwaitExpression
                            | SyntaxKind::IndexExpression
                            | SyntaxKind::CastExpression
                    )
                }) {
                    left = operand
                        .children()
                        .filter(|child| child.kind().is_expression())
                        .last()
                        .filter(|inner| inner.span().end() == dot.span().start());
                }
                left
            }
            SyntaxKind::MemberBindingExpression => parent
                .ancestors()
                .find(|ancestor| ancestor.kind() == SyntaxKind::ConditionalAccessExpression)
                .and_then(|access| access.children().next()),
            _ => None,
        };
        let Some(receiver) = receiver else {
            return;
        };

        // A type or a namespace to the left: its static members, its nested
        // types, its namespaces.
        if let Some(symbol) = self.named(&receiver) {
            let symbols = self.compilation().symbols();
            match symbols.get(symbol).kind {
                SymbolKind::Namespace => {
                    for &member in &symbols.get(symbol).members {
                        self.push_symbol(member, 20, items);
                    }
                    return;
                }
                SymbolKind::NamedType
                    // `World.Create()` beside a `World` property of type
                    // `World` reads the type, but the name is the property
                    // too: its instance members are in reach below.
                    if !self
                        .value_named(&receiver, dot.span().start())
                        .is_some_and(|value| value.symbol() == Some(symbol)) =>
                {
                    let enclosing = self.enclosing_types(&receiver);
                    self.push_members(symbol, Some(true), &enclosing, items);
                    return;
                }
                _ => {}
            }
        }

        // An expression: its type's instance members, and the extension
        // methods that take it.
        let mut ty = self.type_of(&receiver);
        // `p.Ag` with the next line read into it — `p.Ag other = 1;`, a
        // declaration of `other`, or `e.Va (e, r) => …`, a lambda that writes
        // its return type — is a name of a type to the parser; `p` is still
        // the variable it is in scope.
        if ty.is_error()
            && parent.kind() == SyntaxKind::QualifiedName
            && let Some(value) = self.value_named(&receiver, dot.span().start())
        {
            ty = value;
        }
        let ty = match ty {
            Type::Named { .. } | Type::Array { .. } | Type::TypeParameter(_) | Type::Tuple(_) => ty,
            _ => return,
        };
        // A tuple is a `ValueTuple<…>` with names on: it has `Item1` and
        // `Equals` as well as what its elements are called. A type
        // parameter has what its constraints promise.
        let ty = if let Type::Tuple(elements) = &ty {
            let types: Vec<Type> = elements.iter().map(|element| element.ty.clone()).collect();
            match self.model.binder().value_tuple_of(&types) {
                Some(underlying) => {
                    self.push_tuple_elements(elements, items);
                    underlying
                }
                None => ty.clone(),
            }
        } else {
            ty
        };
        let symbol = match &ty {
            Type::Named { symbol, .. } | Type::TypeParameter(symbol) => Some(*symbol),
            Type::Array { .. } => self.compilation().type_by_metadata_name("System.Array"),
            _ => None,
        };
        if let Type::Tuple(elements) = &ty {
            for (index, element) in elements.iter().enumerate() {
                let detail = element.ty.display(self.compilation().symbols());
                items.push(Completion {
                    label: element
                        .name
                        .clone()
                        .unwrap_or_else(|| format!("Item{}", index + 1)),
                    kind: CompletionKind::Field,
                    detail,
                    rank: 10,
                    ..Completion::default()
                });
            }
        }
        if let Some(symbol) = symbol {
            let enclosing = self.enclosing_types(&receiver);
            // `protected` is reached through `this`, `base`, or a value of
            // the code's own type or one derived from it — not through any
            // value: `kv.MemberwiseClone()` does not compile.
            let own = matches!(
                receiver.kind(),
                SyntaxKind::ThisExpression | SyntaxKind::BaseExpression
            ) || {
                let reachable = self.types_of(&ty);
                enclosing.iter().any(|ty| reachable.contains(ty))
            };
            let through = Through {
                receiver: &ty,
                protected: own,
            };
            self.push_members_through(symbol, Some(false), &enclosing, Some(&through), items);
            self.push_extensions(&receiver, &ty, items);
            // `ConditionType.Faction` where `ConditionType` is a property of
            // the type of that name: the name is the type as well (§12.8.7.2,
            // "Color Color"), and its static members are in reach too.
            if receiver.kind() == SyntaxKind::IdentifierName
                && receiver.first_token().is_some_and(|name| {
                    name.value_text() == self.compilation().symbols().get(symbol).name
                })
            {
                self.push_members(symbol, Some(true), &enclosing, items);
            }
        }
    }

    /// The type of the local, parameter or member a simple name would read
    /// as an expression at `offset`: what the left of a dotted name the
    /// parser took for a type stands for when it is a variable.
    fn value_named(&mut self, name: &SyntaxNode, offset: u32) -> Option<Type> {
        if name.kind() != SyntaxKind::IdentifierName {
            return None;
        }
        let text = name.first_token()?.value_text().to_string();
        if let Some(body) = self.body_for(name)
            && let Some(local) = body.locals.iter().rev().find(|local| {
                local.name == text
                    && local.span.end() <= offset
                    && !local.ty.is_error()
                    && self.in_scope_at(local.span, offset)
            })
        {
            return Some(local.ty.clone());
        }
        let context = self.model.binder().context_at(self.tree, name);
        let symbols = self.compilation().symbols();
        let parameter = context.enclosing_member().and_then(|member| {
            symbols.get(member).members.iter().copied().find(|&child| {
                symbols.get(child).kind == SymbolKind::Parameter && symbols.get(child).name == text
            })
        });
        let member = parameter.or_else(|| {
            context.enclosing_types().into_iter().find_map(|ty| {
                symbols.lookup(ty, &text).iter().copied().find(|&member| {
                    matches!(
                        symbols.get(member).kind,
                        SymbolKind::Field | SymbolKind::Property
                    )
                })
            })
        })?;
        let ty = self.model.type_of_symbol(member);
        (!ty.is_error()).then_some(ty)
    }

    /// The names a tuple's elements were given, as fields of it.
    fn push_tuple_elements(
        &self,
        elements: &[rustlyn_semantics::TupleElement],
        items: &mut Vec<Completion>,
    ) {
        for element in elements {
            let Some(name) = &element.name else {
                continue;
            };
            items.push(Completion {
                label: name.clone(),
                kind: CompletionKind::Field,
                detail: element.ty.display(self.compilation().symbols()),
                rank: 10,
                ..Completion::default()
            });
        }
    }

    /// The type or namespace a piece of syntax names, if that is what it is.
    fn named(&mut self, node: &SyntaxNode) -> Option<SymbolId> {
        let name = match node.kind() {
            SyntaxKind::IdentifierName | SyntaxKind::GenericName => node.clone(),
            SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::QualifiedName
            | SyntaxKind::AliasQualifiedName => node.children().last()?,
            SyntaxKind::PredefinedType => {
                return match self.model.type_of_syntax(node) {
                    Type::Named { symbol, .. } => Some(symbol),
                    _ => None,
                };
            }
            _ => return None,
        };
        let token = name
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
        match self.resolve(&token)? {
            Resolved::Symbol(symbol)
                if matches!(
                    self.compilation().symbols().get(symbol).kind,
                    SymbolKind::Namespace | SymbolKind::NamedType
                ) =>
            {
                // `Color.Red` where `Color` is both a property and its type
                // binds to the property; a name that binds to a type in an
                // expression is the type.
                Some(symbol)
            }
            _ => None,
        }
    }

    /// The type of an expression, from the body it is in.
    fn type_of(&mut self, node: &SyntaxNode) -> Type {
        if let Some(body) = self.body_for(node)
            && let Some(ty) = body.type_at(node.span())
        {
            return ty.clone();
        }
        // Not in a body the binder reached: a name alone can still be typed
        // by what it names.
        let token = node
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .last();
        match token.and_then(|token| self.resolve(&token)) {
            Some(Resolved::Local { ty, .. }) => ty,
            Some(Resolved::Symbol(symbol)) => self.model.type_of_symbol(symbol),
            None => Type::Error,
        }
    }

    /// The members of `ty` and of what it derives from. `statics` picks
    /// static members only, instance members only, or both.
    fn push_members(
        &self,
        ty: SymbolId,
        statics: Option<bool>,
        enclosing: &HashSet<SymbolId>,
        items: &mut Vec<Completion>,
    ) {
        self.push_members_through(ty, statics, enclosing, None, items);
    }

    /// [`View::push_members`] of a value: what is reached `through` it is
    /// shown with its type arguments — `Key` of an `IGrouping<int, Item>`
    /// is an `int`.
    fn push_members_through(
        &self,
        ty: SymbolId,
        statics: Option<bool>,
        enclosing: &HashSet<SymbolId>,
        through: Option<&Through<'_>>,
        items: &mut Vec<Completion>,
    ) {
        let symbols = self.compilation().symbols();
        let mut visited = HashSet::new();
        let mut queue = vec![ty];
        // A class's interfaces add nothing it does not already have; an
        // interface's are its members, and so are a type parameter's.
        let takes_interfaces = |symbol: SymbolId| {
            symbols.get(symbol).type_kind() == Some(TypeKind::Interface)
                || symbols.get(symbol).kind == SymbolKind::TypeParameter
        };
        while let Some(current) = queue.pop() {
            if !visited.insert(current) {
                continue;
            }
            let arguments: HashMap<SymbolId, Type> = through
                .map(|through| self.arguments_through(through.receiver, current))
                .unwrap_or_default()
                .into_iter()
                .collect();
            for &member in &symbols.get(current).members {
                let symbol = symbols.get(member);
                // A type's type parameters are its own: no dot reaches them.
                if symbol.kind == SymbolKind::TypeParameter || !self.offerable(member) {
                    continue;
                }
                let is_static = symbol.modifiers.contains(Modifiers::STATIC)
                    || symbol.modifiers.contains(Modifiers::CONST)
                    || symbol.kind == SymbolKind::NamedType
                    || (symbol.kind == SymbolKind::Field
                        && symbols.get(current).type_kind() == Some(TypeKind::Enum));
                if statics.is_some_and(|statics| statics != is_static) {
                    continue;
                }
                // Private members are for the type itself.
                if symbol.accessibility == Accessibility::Private && !enclosing.contains(&current) {
                    continue;
                }
                if through.is_some_and(|through| !through.protected)
                    && matches!(
                        symbol.accessibility,
                        Accessibility::Protected | Accessibility::ProtectedAndInternal
                    )
                {
                    continue;
                }
                self.push_symbol_in(
                    member,
                    if current == ty { 10 } else { 12 },
                    &arguments,
                    items,
                );
            }
            let mut bases = self.model.base_types_of(current);
            // `object`, `ValueType` and `Enum` are bases nobody writes, and
            // whatever has a value has their members: `ToString` of a class
            // that names no base, or of an interface.
            let names_a_class = bases.iter().any(|base| {
                base.symbol().is_some_and(|symbol| {
                    symbols.get(symbol).type_kind() != Some(TypeKind::Interface)
                })
            });
            let implicit = if symbols.get(current).type_kind() == Some(TypeKind::Interface) {
                (current == ty)
                    .then(|| self.compilation().special_type(SpecialType::Object))
                    .flatten()
                    .map(Type::named)
            } else if names_a_class {
                None
            } else {
                self.model.binder().base_class_of(current)
            };
            bases.extend(implicit);
            for base in bases {
                if let Type::Named { symbol, .. } | Type::TypeParameter(symbol) = base {
                    let base_is_interface =
                        symbols.get(symbol).type_kind() == Some(TypeKind::Interface);
                    if !base_is_interface || takes_interfaces(current) {
                        queue.push(symbol);
                    }
                }
            }
        }
    }

    /// Extension methods whose first parameter takes `ty`, among those the
    /// file can see.
    fn push_extensions(&self, at: &SyntaxNode, ty: &Type, items: &mut Vec<Completion>) {
        let compilation = self.compilation();
        let context = self.model.binder().context_at(self.tree, at);
        let receiver_types = self.types_of(ty);
        let names: Vec<&str> = compilation.extension_method_names().collect();
        for name in names {
            for method in self.model.binder().extensions_in_scope(&context, name) {
                let Some(detail) = compilation.symbols().get(method).as_method() else {
                    continue;
                };
                let Some(&first) = detail.parameters.first() else {
                    continue;
                };
                let takes = match self.model.type_of_symbol(first) {
                    Type::TypeParameter(_) => true,
                    Type::Named { symbol, .. } => receiver_types.contains(&symbol),
                    other => self.model.binder().converts_implicitly(ty, &other),
                };
                if takes {
                    let arguments = self.receiver_arguments(ty, &self.model.type_of_symbol(first));
                    self.push_symbol_in(method, 14, &arguments, items);
                }
            }
        }
    }

    /// A type and everything it converts to by derivation: what an extension
    /// method's `this` parameter may name.
    fn types_of(&self, ty: &Type) -> HashSet<SymbolId> {
        let mut found = HashSet::new();
        let mut queue = Vec::new();
        match ty {
            Type::Named { symbol, .. } => queue.push(*symbol),
            Type::Array { .. } => {
                // `T[]` is an `IEnumerable<T>`, an `IList<T>` and the rest;
                // the array type's own bases only give the non-generic ones.
                for name in [
                    "System.Collections.Generic.IEnumerable`1",
                    "System.Collections.Generic.IList`1",
                    "System.Collections.Generic.ICollection`1",
                    "System.Collections.Generic.IReadOnlyList`1",
                    "System.Collections.Generic.IReadOnlyCollection`1",
                ] {
                    if let Some(symbol) = self.compilation().type_by_metadata_name(name) {
                        queue.push(symbol);
                    }
                }
                if let Some(array) = self.compilation().type_by_metadata_name("System.Array") {
                    queue.push(array);
                }
            }
            _ => {}
        }
        while let Some(symbol) = queue.pop() {
            if !found.insert(symbol) {
                continue;
            }
            for base in self.model.base_types_of(symbol) {
                if let Type::Named { symbol, .. } = base {
                    queue.push(symbol);
                }
            }
        }
        found
    }

    /// The types the code at `node` is written in, whose private members it
    /// can see.
    fn enclosing_types(&self, node: &SyntaxNode) -> HashSet<SymbolId> {
        self.model
            .binder()
            .context_at(self.tree, node)
            .enclosing_types()
            .into_iter()
            .collect()
    }

    /// Without a `.`: what is in scope where the cursor is.
    fn scope_completions(&mut self, offset: u32, items: &mut Vec<Completion>) {
        let node = self
            .root
            .find_token(offset.saturating_sub(1))
            .map_or_else(|| self.root.clone(), |token| token.parent().clone());
        let context = self.model.binder().context_at(self.tree, &node);
        let symbols = self.compilation().symbols();

        // Locals declared above the cursor, in a block that is still open.
        if let Some(body) = self.body_for(&node) {
            for local in &body.locals {
                if local.span.end() > offset || local.name.starts_with('<') {
                    continue;
                }
                if !self.in_scope_at(local.span, offset) {
                    continue;
                }
                items.push(Completion {
                    label: local.name.clone(),
                    kind: CompletionKind::Local,
                    detail: local.ty.display(symbols),
                    rank: 0,
                    ..Completion::default()
                });
            }
        }

        // The enclosing member's parameters and type parameters.
        if let Some(member) = context.enclosing_member() {
            for &child in &symbols.get(member).members {
                if matches!(
                    symbols.get(child).kind,
                    SymbolKind::Parameter | SymbolKind::TypeParameter
                ) {
                    self.push_symbol(child, 1, items);
                }
            }
        }

        // The members of every enclosing type, private ones included.
        let enclosing: HashSet<SymbolId> = context.enclosing_types().into_iter().collect();
        for &ty in &enclosing {
            self.push_members(ty, None, &enclosing, items);
        }

        // Types and namespaces: the global namespace, the namespaces the code
        // is in, and what `using` brought in.
        let mut namespaces = vec![self.compilation().global_namespace()];
        namespaces.extend(self.namespaces_in_scope(&node));
        let mut seen = HashSet::new();
        for namespace in namespaces {
            if !seen.insert(namespace) {
                continue;
            }
            for &member in &symbols.get(namespace).members {
                let symbol = symbols.get(member);
                if symbol.kind == SymbolKind::NamedType && !self.offerable(member) {
                    continue;
                }
                self.push_symbol(member, 20, items);
            }
        }
    }

    /// Whether a local declared at `declared` is still in scope at `offset`:
    /// the innermost block or statement around its declaration must still be
    /// open there.
    fn in_scope_at(&self, declared: TextSpan, offset: u32) -> bool {
        let Some(token) = self.root.find_token(declared.start()) else {
            return false;
        };
        let scope = token.parent().ancestors().find(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::Block
                    | SyntaxKind::ForStatement
                    | SyntaxKind::ForEachStatement
                    | SyntaxKind::UsingStatement
                    | SyntaxKind::CatchClause
                    | SyntaxKind::SwitchSection
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::LocalFunctionStatement
                    | SyntaxKind::ArrowExpressionClause
            )
        });
        scope.is_none_or(|scope| scope.span().contains(offset) || scope.span().end() == offset)
    }

    /// The namespaces a name at `node` is looked up in besides the global
    /// one: those the code is declared in, outward, and those `using` names.
    fn namespaces_in_scope(&self, node: &SyntaxNode) -> Vec<SymbolId> {
        let compilation = self.compilation();
        let symbols = compilation.symbols();
        let global = compilation.global_namespace();
        let mut found = Vec::new();
        let lookup = |name: &str| -> Option<SymbolId> {
            let mut current = global;
            for part in name.split('.') {
                current = symbols.lookup_namespace(current, part.trim())?;
            }
            Some(current)
        };
        let mut scopes: Vec<SyntaxNode> = node
            .ancestors()
            .filter(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::NamespaceDeclaration
                        | SyntaxKind::FileScopedNamespaceDeclaration
                        | SyntaxKind::CompilationUnit
                )
            })
            .collect();
        // File-scoped namespaces are siblings of the code, not ancestors.
        if let Some(unit) = scopes.last().cloned() {
            scopes.extend(
                unit.children()
                    .filter(|child| child.kind() == SyntaxKind::FileScopedNamespaceDeclaration),
            );
        }
        for scope in &scopes {
            if scope.kind() != SyntaxKind::CompilationUnit
                && let Some(name) = scope.children().find(|child| child.kind().is_type_node())
            {
                let name = name.text();
                let name = name.trim();
                // `namespace A.B.C` brings in `A.B.C`, `A.B` and `A`.
                let mut rest = name;
                loop {
                    if let Some(namespace) = lookup(rest) {
                        found.push(namespace);
                    }
                    match rest.rfind('.') {
                        Some(dot) => rest = &rest[..dot],
                        None => break,
                    }
                }
            }
            for using in scope
                .children()
                .filter(|child| child.kind() == SyntaxKind::UsingDirective)
            {
                if using.child_of_kind(SyntaxKind::NameEquals).is_some()
                    || using
                        .child_token_of_kind(SyntaxKind::StaticKeyword)
                        .is_some()
                {
                    continue;
                }
                if let Some(name) = using.children().find(|child| child.kind().is_type_node())
                    && let Some(namespace) = lookup(name.text().trim())
                {
                    found.push(namespace);
                }
            }
        }
        // `global using` from every file, the SDK's generated ones among them.
        for tree in compilation
            .global_using_trees()
            .iter()
            .filter_map(|&index| compilation.trees().get(index))
        {
            for using in tree
                .root()
                .children()
                .filter(|child| child.kind() == SyntaxKind::UsingDirective)
            {
                if using
                    .child_token_of_kind(SyntaxKind::GlobalKeyword)
                    .is_none()
                    || using.child_of_kind(SyntaxKind::NameEquals).is_some()
                    || using
                        .child_token_of_kind(SyntaxKind::StaticKeyword)
                        .is_some()
                {
                    continue;
                }
                if let Some(name) = using.children().find(|child| child.kind().is_type_node()) {
                    let text = name.text();
                    let text = text.trim().trim_start_matches("global::");
                    if let Some(namespace) = lookup(text) {
                        found.push(namespace);
                    }
                }
            }
        }
        found
    }

    /// Whether a symbol is something a person would write: not a
    /// constructor, not an accessor, not a name the compiler made up.
    fn offerable(&self, symbol: SymbolId) -> bool {
        let found = self.compilation().symbols().get(symbol);
        if found.name.is_empty() || found.name.contains('<') || found.name.starts_with('.') {
            return false;
        }
        if let Some(method) = found.as_method() {
            return matches!(
                method.method_kind,
                MethodKind::Ordinary | MethodKind::LocalFunction
            );
        }
        if found.kind == SymbolKind::NamedType
            && self.compilation().is_from_metadata(symbol)
            && !matches!(
                found.accessibility,
                Accessibility::Public
                    | Accessibility::ProtectedOrInternal
                    | Accessibility::Protected
            )
        {
            // An assembly's internal types are not the project's to use.
            return false;
        }
        !matches!(found.kind, SymbolKind::Local)
    }

    fn push_symbol(&self, symbol: SymbolId, rank: u8, items: &mut Vec<Completion>) {
        self.push_symbol_in(symbol, rank, &HashMap::new(), items);
    }

    /// [`View::push_symbol`], described with what its type parameters stand
    /// for where it is offered.
    fn push_symbol_in(
        &self,
        symbol: SymbolId,
        rank: u8,
        arguments: &HashMap<SymbolId, Type>,
        items: &mut Vec<Completion>,
    ) {
        let compilation = self.compilation();
        let found = compilation.symbols().get(symbol);
        let kind = completion_kind(compilation, symbol);
        items.push(Completion {
            label: found.name.clone(),
            kind,
            detail: describe_symbol_in(compilation, symbol, arguments),
            rank,
            symbol: Some(symbol),
            ..Completion::default()
        });
    }

    /// What an extension method's own type parameters stand for when its
    /// `this` parameter, of type `parameter`, takes `receiver`: `TSource` of
    /// `Where` is `Item` on a `List<Item>`, as on any `IEnumerable<Item>`.
    fn receiver_arguments(&self, receiver: &Type, parameter: &Type) -> HashMap<SymbolId, Type> {
        let mut found = HashMap::new();
        match parameter {
            Type::TypeParameter(own) => {
                found.insert(*own, receiver.clone());
            }
            Type::Named {
                symbol,
                type_arguments,
            } => {
                // An array is an `IEnumerable<T>` and the rest of its element.
                let seen = match receiver {
                    Type::Array { element, rank: 1 } if type_arguments.len() == 1 => {
                        vec![(*symbol, element.as_ref().clone())]
                    }
                    _ => self.arguments_through(receiver, *symbol),
                };
                for (argument, (_, given)) in type_arguments.iter().zip(seen) {
                    if let Type::TypeParameter(own) = argument {
                        found.entry(*own).or_insert(given);
                    }
                }
            }
            Type::Array { element, .. } => {
                if let (Type::TypeParameter(own), Type::Array { element: given, .. }) =
                    (element.as_ref(), receiver)
                {
                    found.insert(*own, given.as_ref().clone());
                }
            }
            _ => {}
        }
        found
    }
}

/// A value whose members are being offered: its type, and whether its
/// `protected` members are within reach of the code.
struct Through<'a> {
    receiver: &'a Type,
    protected: bool,
}

/// What a snapshot starts with.
const SNAPSHOT_MAGIC: &[u8] = b"rustlyn-semantic-1";

/// A file's length and modification time: enough to say it is the file it
/// was, without reading it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Stamp {
    length: u64,
    /// Nanoseconds since the epoch; zero where the system does not say.
    modified: u128,
}

impl Stamp {
    fn of(path: &Path) -> Self {
        let metadata = std::fs::metadata(path).ok();
        Self {
            length: metadata.as_ref().map_or(0, std::fs::Metadata::len),
            modified: metadata
                .and_then(|metadata| metadata.modified().ok())
                .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |since| since.as_nanos()),
        }
    }
}

/// The build of this library, as a number. A snapshot is read only by the
/// build that wrote it: another build may declare the same source
/// differently, and a symbol table from it would be wrong in ways nothing
/// could notice.
///
/// It is a hash of Rustlyn's source (see `build.rs`), not a stamp of the
/// program running it: an editor rebuilt, copied or signed again with the
/// same Rustlyn inside reads its snapshot back instead of compiling anew.
fn program_stamp() -> u64 {
    env!("RUSTLYN_SOURCE_HASH").parse().unwrap_or(0)
}

fn write_program_stamp(out: &mut Writer) {
    out.u64(program_stamp());
}

fn read_program_stamp(input: &mut Reader<'_>) -> Option<bool> {
    Some(input.u64()? == program_stamp())
}

fn write_project(out: &mut Writer, project: &Project) {
    out.u8(match project.kind {
        ProjectKind::Msbuild => 0,
        ProjectKind::Unity => 1,
        ProjectKind::Folder => 2,
    });
    out.u64(project.projects as u64);
    let paths = |out: &mut Writer, list: &[PathBuf]| {
        out.seq(list, |out, path| out.str(&path.to_string_lossy()));
    };
    paths(out, &project.roots);
    paths(out, &project.files);
    out.u8(u8::from(project.everything));
    paths(out, &project.references);
    out.seq(&project.symbols, |out, symbol| out.str(symbol));
    out.str(&project.generated);
    out.seq(&project.assemblies, |out, name| out.str(name));
    for owned in [&project.owned_files, &project.owned_folders] {
        out.seq(owned, |out, (path, index)| {
            out.str(&path.to_string_lossy());
            out.u64(u64::from(*index));
        });
    }
    out.seq(&project.language_versions, |out, version| out.str(version));
    out.u8(u8::from(project.owned_only));
    out.seq(&project.unbuilt, |out, index| out.u64(u64::from(*index)));
    out.seq(&project.assembly_symbols, |out, symbols| {
        out.seq(symbols, |out, symbol| out.str(symbol));
    });
    out.seq(&project.assembly_references, |out, references| {
        out.seq(references, |out, index| out.u64(u64::from(*index)));
    });
    out.seq(&project.shared_files, |out, (path, index)| {
        out.str(&path.to_string_lossy());
        out.u64(u64::from(*index));
    });
    out.seq(&project.assembly_metadata, |out, names| {
        out.seq(names, |out, name| out.str(name));
    });
    out.seq(&project.assembly_warnings, |out, warnings| {
        out.u64(warnings.level.map_or(u64::MAX, u64::from));
        out.seq(&warnings.suppressed, |out, code| out.u64(u64::from(*code)));
    });
    out.seq(&project.assembly_nullable, |out, enabled| {
        out.u8(u8::from(*enabled))
    });
}

fn read_project(input: &mut Reader<'_>) -> Option<Project> {
    let kind = match input.u8()? {
        0 => ProjectKind::Msbuild,
        1 => ProjectKind::Unity,
        2 => ProjectKind::Folder,
        _ => return None,
    };
    let projects = usize::try_from(input.u64()?).ok()?;
    let paths = |input: &mut Reader<'_>| input.seq(|input| input.string().map(PathBuf::from));
    let roots = paths(input)?;
    let files = paths(input)?;
    let everything = input.u8()? != 0;
    let references = paths(input)?;
    let symbols = input.seq(Reader::string)?;
    let generated = input.string()?;
    let assemblies = input.seq(Reader::string)?;
    let owned = |input: &mut Reader<'_>| {
        input.seq(|input| {
            let path = PathBuf::from(input.string()?);
            Some((path, u16::try_from(input.u64()?).ok()?))
        })
    };
    let owned_files = owned(input)?;
    let owned_folders = owned(input)?;
    let language_versions = input.seq(Reader::string)?;
    let owned_only = input.u8()? != 0;
    let unbuilt = input.seq(|input| u16::try_from(input.u64()?).ok())?;
    let assembly_symbols = input.seq(|input| input.seq(Reader::string))?;
    let assembly_references =
        input.seq(|input| input.seq(|input| u16::try_from(input.u64()?).ok()))?;
    let shared_files = owned(input)?;
    let assembly_metadata = input.seq(|input| input.seq(Reader::string))?;
    let assembly_warnings = input.seq(|input| {
        let level = input.u64()?;
        Some(crate::project::WarningOptions {
            level: u8::try_from(level).ok(),
            suppressed: input.seq(|input| u32::try_from(input.u64()?).ok())?,
        })
    })?;
    let assembly_nullable = input.seq(|input| Some(input.u8()? != 0))?;
    Some(Project {
        kind,
        projects,
        roots,
        files,
        everything,
        references,
        symbols,
        generated,
        assemblies,
        owned_files,
        owned_folders,
        language_versions,
        owned_only,
        unbuilt,
        assembly_symbols,
        assembly_references,
        shared_files,
        assembly_metadata,
        assembly_warnings,
        assembly_nullable,
    })
}

/// Which assemblies each project names in an `[assembly:
/// InternalsVisibleTo("…")]` of its source, by index into its assemblies.
fn source_friends(
    project: &Project,
    sources: &[(PathBuf, String)],
    owners: &[u16],
) -> Vec<Vec<u16>> {
    let mut friends: Vec<Vec<u16>> = vec![Vec::new(); project.assemblies.len()];
    for ((_, text), &owner) in sources.iter().zip(owners) {
        let Some(list) = friends.get_mut(usize::from(owner)) else {
            continue;
        };
        let mut rest = text.as_str();
        while let Some(at) = rest.find("InternalsVisibleTo") {
            rest = &rest[at + "InternalsVisibleTo".len()..];
            let Some(name) = rest
                .trim_start()
                .strip_prefix("Attribute")
                .unwrap_or(rest.trim_start())
                .trim_start()
                .strip_prefix('(')
                .map(str::trim_start)
                .and_then(|argument| argument.strip_prefix('"'))
                .and_then(|argument| argument.split(['"', ',']).next())
            else {
                continue;
            };
            if let Some(index) = project
                .assemblies
                .iter()
                .position(|known| known.eq_ignore_ascii_case(name.trim()))
                .and_then(|index| u16::try_from(index).ok())
                && !list.contains(&index)
            {
                list.push(index);
            }
        }
    }
    friends
}

/// Whether `token` is the name of the declaration `node`, rather than a
/// name used inside it.
fn names_declaration(node: &SyntaxNode, token: &SyntaxToken) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::DelegateDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::VariableDeclarator
            | SyntaxKind::Parameter
            | SyntaxKind::TypeParameter
            | SyntaxKind::EnumMemberDeclaration
            | SyntaxKind::LocalFunctionStatement
    ) && token.kind() == SyntaxKind::IdentifierToken
}

/// Whether `text` has `word` in it as a whole identifier.
/// What an attribute class is written as in brackets: `Serializable` for
/// `SerializableAttribute`.
fn attribute_stem(name: &str) -> Option<&str> {
    name.strip_suffix("Attribute")
        .filter(|stem| !stem.is_empty())
}

fn contains_word(text: &str, word: &str) -> bool {
    if word.is_empty() {
        return false;
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
            return true;
        }
        from = start + 1;
        while !text.is_char_boundary(from) {
            from += 1;
        }
    }
    false
}

fn is_core_library(path: &Path) -> bool {
    path.file_stem().is_some_and(|stem| {
        let stem = stem.to_string_lossy().to_ascii_lowercase();
        matches!(
            stem.as_str(),
            "mscorlib" | "netstandard" | "system.runtime" | "system.private.corelib"
        )
    })
}

/// Runs `work` for every index in `0..count` across every core, and returns
/// the answers in order.
///
/// The work binds bodies, and binding recurses as deep as the code it reads:
/// an enum member whose value is an expression over other members folds them
/// in turn, each through the binder's large frames. The default 2 MB stack
/// of a spawned thread runs out on real projects, so the workers get a stack
/// to match; it is only reserved, not touched, until it is needed.
pub(crate) fn parallel<T: Send>(count: usize, work: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let threads = std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .min(count.max(1));
    let next = AtomicUsize::new(0);
    let mut results: Vec<(usize, T)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|_| {
                std::thread::Builder::new()
                    .name("rustlyn-worker".into())
                    .stack_size(64 << 20)
                    .spawn_scoped(scope, || {
                        let mut done = Vec::new();
                        loop {
                            let index = next.fetch_add(1, Ordering::Relaxed);
                            if index >= count {
                                break;
                            }
                            done.push((index, work(index)));
                        }
                        done
                    })
                    .expect("a worker thread")
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| handle.join().unwrap_or_default())
            .collect()
    });
    results.sort_by_key(|(index, _)| *index);
    results.into_iter().map(|(_, value)| value).collect()
}

/// A symbol's kind, in the terms of an outline.
fn declaration_kind(
    compilation: &Compilation,
    symbol: SymbolId,
) -> crate::outline::DeclarationKind {
    use crate::outline::DeclarationKind as Kind;
    let found = compilation.symbols().get(symbol);
    match found.kind {
        SymbolKind::Namespace => Kind::Namespace,
        SymbolKind::NamedType => match found.type_kind() {
            Some(TypeKind::Struct) => Kind::Struct,
            Some(TypeKind::Interface) => Kind::Interface,
            Some(TypeKind::Enum) => Kind::Enum,
            Some(TypeKind::Delegate) => Kind::Delegate,
            Some(TypeKind::Record) => Kind::Record,
            Some(TypeKind::RecordStruct) => Kind::Struct,
            _ => Kind::Class,
        },
        SymbolKind::Method => match found.as_method().map(|method| method.method_kind) {
            Some(MethodKind::Constructor | MethodKind::StaticConstructor) => Kind::Constructor,
            Some(MethodKind::Destructor) => Kind::Destructor,
            Some(MethodKind::Operator | MethodKind::Conversion) => Kind::Operator,
            _ => Kind::Method,
        },
        SymbolKind::Property => {
            if found
                .as_property()
                .is_some_and(|property| property.is_indexer)
            {
                Kind::Indexer
            } else {
                Kind::Property
            }
        }
        SymbolKind::Event => Kind::Event,
        SymbolKind::Field => {
            let in_enum = found.container.is_some_and(|container| {
                compilation.symbols().get(container).type_kind() == Some(TypeKind::Enum)
            });
            if in_enum {
                Kind::EnumMember
            } else {
                Kind::Field
            }
        }
        SymbolKind::Parameter | SymbolKind::TypeParameter | SymbolKind::Local => Kind::Field,
    }
}

fn completion_kind(compilation: &Compilation, symbol: SymbolId) -> CompletionKind {
    let found = compilation.symbols().get(symbol);
    match found.kind {
        SymbolKind::Namespace => CompletionKind::Namespace,
        SymbolKind::NamedType => match found.type_kind() {
            Some(TypeKind::Struct | TypeKind::RecordStruct) => CompletionKind::Struct,
            Some(TypeKind::Interface) => CompletionKind::Interface,
            Some(TypeKind::Enum) => CompletionKind::Enum,
            Some(TypeKind::Delegate) => CompletionKind::Delegate,
            _ => CompletionKind::Class,
        },
        SymbolKind::Method => CompletionKind::Method,
        SymbolKind::Property => CompletionKind::Property,
        SymbolKind::Event => CompletionKind::Event,
        SymbolKind::Field => {
            if found.modifiers.contains(Modifiers::CONST) {
                let in_enum = found.container.is_some_and(|container| {
                    compilation.symbols().get(container).type_kind() == Some(TypeKind::Enum)
                });
                if in_enum {
                    CompletionKind::EnumMember
                } else {
                    CompletionKind::Constant
                }
            } else if found.container.is_some_and(|container| {
                compilation.symbols().get(container).type_kind() == Some(TypeKind::Enum)
            }) {
                CompletionKind::EnumMember
            } else {
                CompletionKind::Field
            }
        }
        SymbolKind::Parameter => CompletionKind::Parameter,
        SymbolKind::TypeParameter => CompletionKind::TypeParameter,
        SymbolKind::Local => CompletionKind::Local,
    }
}

/// A symbol as one line: `int Count`, `void Add(T item)`, `class List<T>`.
#[must_use]
pub fn describe_symbol(compilation: &Compilation, symbol: SymbolId) -> String {
    describe_symbol_in(compilation, symbol, &HashMap::new())
}

/// [`describe_symbol`] as a use sees the symbol: each type parameter in
/// `arguments` written as what it stands for there. `Key` of an
/// `IGrouping<int, Item>` is `int Key`, not `TKey Key`, and `Select` called on
/// a list of items `IEnumerable<string> Select<Item, string>(...)`.
#[must_use]
pub fn describe_symbol_in(
    compilation: &Compilation,
    symbol: SymbolId,
    arguments: &HashMap<SymbolId, Type>,
) -> String {
    let symbols = compilation.symbols();
    let model = SemanticModel::new(compilation, 0);
    let found = symbols.get(symbol);
    let shown = |ty: Type| display_type(compilation, &ty.substitute(arguments));
    let parameter_list = |parameters: &[SymbolId]| -> String {
        let names: Vec<String> = parameters
            .iter()
            .map(|&parameter| shown(Type::TypeParameter(parameter)))
            .collect();
        if names.is_empty() {
            String::new()
        } else {
            format!("<{}>", names.join(", "))
        }
    };
    match found.kind {
        SymbolKind::Namespace => format!("namespace {}", symbols.qualified_name(symbol)),
        SymbolKind::NamedType => {
            let keyword = match found.type_kind() {
                Some(TypeKind::Struct) => "struct",
                Some(TypeKind::Interface) => "interface",
                Some(TypeKind::Enum) => "enum",
                Some(TypeKind::Delegate) => "delegate",
                Some(TypeKind::Record) => "record",
                Some(TypeKind::RecordStruct) => "record struct",
                _ => "class",
            };
            let parameters: Vec<SymbolId> = found
                .members
                .iter()
                .copied()
                .filter(|member| symbols.get(*member).kind == SymbolKind::TypeParameter)
                .collect();
            let name = symbols.qualified_name(symbol);
            let name = name.split('`').next().unwrap_or_default();
            format!("{keyword} {name}{}", parameter_list(&parameters))
        }
        SymbolKind::Method => {
            let Some(method) = found.as_method() else {
                return found.name.clone();
            };
            let returns = shown(model.type_of_symbol(symbol));
            let parameters: Vec<String> = method
                .parameters
                .iter()
                .map(|&parameter| {
                    let ty = shown(model.type_of_symbol(parameter));
                    format!("{ty} {}", symbols.get(parameter).name)
                })
                .collect();
            let name = match method.method_kind {
                MethodKind::Constructor | MethodKind::StaticConstructor => found
                    .container
                    .map(|container| symbols.get(container).name.clone())
                    .unwrap_or_default(),
                _ => found.name.clone(),
            };
            let generic = parameter_list(&method.type_parameters);
            let this = if method.is_extension { "this " } else { "" };
            if matches!(
                method.method_kind,
                MethodKind::Constructor | MethodKind::StaticConstructor
            ) {
                format!("{name}({this}{})", parameters.join(", "))
            } else {
                format!("{returns} {name}{generic}({this}{})", parameters.join(", "))
            }
        }
        SymbolKind::Field
        | SymbolKind::Property
        | SymbolKind::Event
        | SymbolKind::Parameter
        | SymbolKind::Local => {
            let ty = shown(model.type_of_symbol(symbol));
            format!("{ty} {}", found.name)
        }
        SymbolKind::TypeParameter => found.name.clone(),
    }
}

/// A type as the editor writes it: as a diagnostic would, but an anonymous
/// type as what it holds, `new { string Title, int Twice }`, rather than the
/// class the compiler declared for it.
#[must_use]
pub fn display_type(compilation: &Compilation, ty: &Type) -> String {
    let symbols = compilation.symbols();
    ty.display_by(symbols, &|symbol, type_arguments| {
        let names = compilation.anonymous_names(symbol)?;
        let members: Vec<String> = names
            .iter()
            .zip(type_arguments)
            .map(|(name, ty)| format!("{} {name}", display_type(compilation, ty)))
            .collect();
        Some(format!("new {{ {} }}", members.join(", ")))
    })
}

/// A project kind as a word, for status lines.
#[must_use]
pub const fn describe_kind(kind: ProjectKind) -> &'static str {
    match kind {
        ProjectKind::Msbuild => "msbuild",
        ProjectKind::Unity => "unity",
        ProjectKind::Folder => "folder",
    }
}

// MARK: - unnecessary usings

/// Which `using` directives a file does not need, for the light bulb's
/// "Remove unnecessary usings" and for fading them.
mod usings;

// MARK: - .editorconfig: code-style analyzers, naming rules, fix all

/// The analyzers an `.editorconfig` switches on, and severities applied.
mod code_style;
/// IDE1006: names that break the `.editorconfig`'s naming rules.
mod naming;

pub use actions::FixAllScope;
pub use naming::{
    Capitalization, NamingRule, NamingStyle, SymbolSpecification, rules as naming_rules,
};

#[cfg(test)]
mod tests {
    use super::*;

    /// What is kept of the nodes above one is what climbing from it says,
    /// for every node of a file that has each kind of declaration a climb
    /// stops at, and each kind of body.
    #[test]
    fn what_is_kept_of_the_nodes_above_is_what_climbing_says() {
        let text = "using System;\n\
                    namespace A.B {\n\
                      [AttributeUsage(AttributeTargets.All)] class Mark : Attribute { }\n\
                      enum E { One = 1, Two = One + 1 }\n\
                      public unsafe struct S { public fixed int buf[4 + 1]; int a = 1, b = 2; event Action Done, Gone; }\n\
                      class C<T> where T : class {\n\
                        int field = 3, other = 4;\n\
                        [Mark] int Prop { get { return field; } set { field = value; } }\n\
                        C([Mark] int p = 5) : this(p, 1) { }\n\
                        C(int p, int q) { }\n\
                        int M(int x = 7) {\n\
                          Func<int, int> f = y => { int z = y + x; return z; };\n\
                          int Local(int w) => w + 1;\n\
                          return f(Local(x)) + System.Math.Abs(x);\n\
                        }\n\
                      }\n\
                    }\n\
                    namespace D { class Other { void N() { } } }\n\
                    Console.WriteLine(1);\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let mut view = semantic
            .view(semantic.tree_index(Path::new("/p/C.cs")).expect("a tree"))
            .expect("a view");
        let brief = |node: Option<SyntaxNode>| node.map(|node| (node.kind(), node.span()));
        let mut checked = 0;
        for node in view.root.clone().descendants() {
            let above = view.above_of(&node);
            let stops = |ancestor: &SyntaxNode| rustlyn_semantics::is_body_owner(ancestor.kind());
            assert_eq!(
                brief(above.owner),
                brief(SemanticModel::body_owner(&node)),
                "owner of {:?} at {:?}",
                node.kind(),
                node.span()
            );
            assert_eq!(
                brief(above.attribute),
                brief(
                    node.ancestors()
                        .take_while(|ancestor| !stops(ancestor))
                        .find(|ancestor| ancestor.kind() == SyntaxKind::Attribute)
                ),
                "attribute of {:?} at {:?}",
                node.kind(),
                node.span()
            );
            assert_eq!(
                brief(above.default),
                brief(
                    node.ancestors()
                        .take_while(|ancestor| !stops(ancestor))
                        .find(is_default_value)
                ),
                "default value of {:?} at {:?}",
                node.kind(),
                node.span()
            );
            assert_eq!(
                brief(above.namespace),
                brief(
                    node.ancestors()
                        .find(|ancestor| ancestor.kind() == SyntaxKind::NamespaceDeclaration)
                )
            );
            assert_eq!(
                brief(above.directive),
                brief(node.ancestors().find(|ancestor| matches!(
                    ancestor.kind(),
                    SyntaxKind::UsingDirective
                        | SyntaxKind::NamespaceDeclaration
                        | SyntaxKind::FileScopedNamespaceDeclaration
                )))
            );
            assert_eq!(
                brief(above.enclosing_attribute),
                brief(
                    node.ancestors()
                        .find(|ancestor| ancestor.kind() == SyntaxKind::Attribute)
                )
            );
            assert_eq!(
                format!("{:?}", view.context_at(&node)),
                format!("{:?}", view.model.binder().context_at(view.tree, &node)),
                "scopes of {:?} at {:?}",
                node.kind(),
                node.span()
            );
            checked += 1;
        }
        assert!(checked > 150, "{checked}");
    }

    /// After `ConditionType.` where `ConditionType` is a property of the type
    /// of that name, the type's own members are offered — the enum's
    /// constants — as well as the value's (§12.8.7.2).
    #[test]
    fn a_property_named_as_its_type_completes_the_types_members() {
        let full = "enum ConditionType { Faction, Other }\n\
                    abstract class Base { public abstract ConditionType ConditionType { get; } }\n\
                    class FactionCondition : Base { public override ConditionType ConditionType => ConditionType.Faction; }";
        let Some(semantic) = compile(&[("C.cs", full)], true) else {
            return;
        };
        let dot = full.find("ConditionType.Faction").unwrap() + "ConditionType.".len();
        let edited = format!("{}{}", &full[..dot], &full[dot + "Faction".len()..]);
        let labels: Vec<String> = semantic
            .completions(Path::new("/p/C.cs"), dot as u32, Some(&edited))
            .map(|found| found.items.into_iter().map(|item| item.label).collect())
            .unwrap_or_default();
        assert!(labels.iter().any(|label| label == "Faction"), "{labels:?}");
        assert!(labels.iter().any(|label| label == "HasFlag"), "{labels:?}");
    }

    /// `World.Create()` half typed from `World.CreateEntity()`, where `World`
    /// is a property of type `World` with a static `Create`: the name reads
    /// as the type, but the property's instance members are offered too.
    #[test]
    fn a_static_member_half_typed_keeps_the_values_members() {
        let full = "class World { public static World Create() => null; public object CreateEntity() => null; }\n\
                    class System { public World World { get; set; } void Run() { var e = World.CreateEntity(); } }";
        let Some(semantic) = compile(&[("C.cs", full)], false) else {
            return;
        };
        let dot = full.find("World.CreateEntity").unwrap() + "World.".len();
        let half = dot + "Create".len();
        let edited = format!("{}{}", &full[..half], &full[dot + "CreateEntity".len()..]);
        let labels: Vec<String> = semantic
            .completions(Path::new("/p/C.cs"), half as u32, Some(&edited))
            .map(|found| found.items.into_iter().map(|item| item.label).collect())
            .unwrap_or_default();
        assert!(
            labels.iter().any(|label| label == "CreateEntity"),
            "{labels:?}"
        );
        assert!(labels.iter().any(|label| label == "Create"), "{labels:?}");
    }

    /// Compiles files given as `(name, text)` against the synthesised core
    /// library, or against the real framework when `framework` is set and
    /// one is installed.
    pub(super) fn compile(files: &[(&str, &str)], framework: bool) -> Option<Semantic> {
        let references: Vec<(PathBuf, Arc<[u8]>)> = if framework {
            let found = crate::project::framework_references(None);
            if found.is_empty() {
                return None;
            }
            found
                .into_iter()
                .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(&path).ok()?))))
                .collect()
        } else {
            Vec::new()
        };
        let project = Project {
            kind: ProjectKind::Folder,
            projects: 0,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: Vec::new(),
            owned_files: Vec::new(),
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let sources = files
            .iter()
            .map(|(name, text)| (PathBuf::from(format!("/p/{name}")), (*text).to_string()))
            .collect();
        Some(Semantic::build(project, sources, &references, None))
    }

    /// One compilation of several projects is still several projects: what
    /// one declares is seen only by those that reference it, a namespace
    /// with nothing it sees is not there for it, and each project's files
    /// are parsed with its own symbols.
    #[test]
    fn a_project_sees_only_the_projects_it_references() {
        let gui = "namespace Game.GUI { public class Window { } }\n\
                   namespace Game { public static class Extensions { public static int Twice(this int n) => n * 2; } }";
        let links = "namespace Engine { public static class GUI { public static bool enabled; } }\n\
                     namespace Game.Links {\n\
                         using Engine;\n\
                         class Panel {\n\
                             void M() { GUI.enabled = false; }\n\
                         #if LINKS\n\
                             int Linked => 1;\n\
                         #endif\n\
                             int N() => Linked;\n\
                         }\n\
                     }";
        let uses = "using Game;\nclass User { int M() => 2.Twice() + (new Game.GUI.Window() == null ? 0 : 1); }";
        let project = |references: Vec<Vec<u16>>| Project {
            kind: ProjectKind::Msbuild,
            projects: 3,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: vec!["Game".into(), "Links".into(), "User".into()],
            owned_files: vec![
                (PathBuf::from("/p/Gui.cs"), 0),
                (PathBuf::from("/p/Links.cs"), 1),
                (PathBuf::from("/p/User.cs"), 2),
            ],
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: vec![Vec::new(), vec!["LINKS".into()], Vec::new()],
            assembly_references: references,
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let errors = |references: Vec<Vec<u16>>| {
            let semantic = Semantic::build(
                project(references),
                vec![
                    (PathBuf::from("/p/Gui.cs"), gui.to_string()),
                    (PathBuf::from("/p/Links.cs"), links.to_string()),
                    (PathBuf::from("/p/User.cs"), uses.to_string()),
                ],
                &[],
                None,
            );
            ["/p/Gui.cs", "/p/Links.cs", "/p/User.cs"]
                .iter()
                .flat_map(|path| {
                    semantic
                        .diagnostics(Path::new(path), None)
                        .unwrap_or_default()
                })
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        // `Links` does not reference `Game`, so `GUI` there is `Engine.GUI`;
        // `User` does, and sees its namespace and its extension method.
        assert_eq!(
            errors(vec![Vec::new(), Vec::new(), vec![0]]),
            Vec::<String>::new()
        );
        // Without the reference, `User` sees neither.
        assert!(!errors(vec![Vec::new(), Vec::new(), Vec::new()]).is_empty());
    }

    /// What another project declares `internal` is its own, though this one
    /// references it — unless that project names this one in an
    /// `[assembly: InternalsVisibleTo]`. And of two internal types of one
    /// name in two projects each sees its own.
    #[test]
    fn another_projects_internals_are_seen_only_by_its_friends() {
        let core = |friend: &str| {
            format!(
                "{friend}\nnamespace Lists {{ internal sealed class FastList<T> {{ public int length; }} internal class Hidden {{ public int x; }} }}"
            )
        };
        let mine = "namespace Lists { internal sealed class FastList<T> { public int count; } }\n\
                    class User { int M(Lists.FastList<int> list) => list.count; int N(Lists.Hidden h) => h.x; }";
        let errors = |friend: &str| {
            let project = Project {
                kind: ProjectKind::Msbuild,
                projects: 2,
                roots: Vec::new(),
                files: Vec::new(),
                everything: true,
                references: Vec::new(),
                symbols: Vec::new(),
                generated: String::new(),
                assemblies: vec!["Core".into(), "User".into()],
                owned_files: vec![
                    (PathBuf::from("/p/Core.cs"), 0),
                    (PathBuf::from("/p/User.cs"), 1),
                ],
                owned_folders: Vec::new(),
                language_versions: Vec::new(),
                owned_only: false,
                unbuilt: Vec::new(),
                assembly_symbols: Vec::new(),
                assembly_references: vec![Vec::new(), vec![0]],
                shared_files: Vec::new(),
                assembly_metadata: Vec::new(),
                assembly_warnings: Vec::new(),
                assembly_nullable: Vec::new(),
            };
            let semantic = Semantic::build(
                project,
                vec![
                    (PathBuf::from("/p/Core.cs"), core(friend)),
                    (PathBuf::from("/p/User.cs"), mine.to_string()),
                ],
                &[],
                None,
            );
            semantic
                .diagnostics(Path::new("/p/User.cs"), None)
                .unwrap_or_default()
                .iter()
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        // `User` sees its own `FastList`, not `Core`'s, and no `Hidden`.
        assert_eq!(errors(""), ["CS0234"]);
        // A friend sees `Hidden`; its own `FastList` still wins.
        assert_eq!(
            errors("[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"User\")]"),
            Vec::<String>::new()
        );
        // An assembly's name is the same in any case, as .NET compares it:
        // Unity's PSD importer names `Unity.2D.PsdImporter.Editor`, which
        // is `Unity.2D.Psdimporter.Editor`.
        assert_eq!(
            errors("[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"USER\")]"),
            Vec::<String>::new()
        );
    }

    /// A project's warning options hide the compiler's warnings, never its
    /// errors: Unity builds its packages with `-warn:0`, and Rider shows
    /// nothing there either.
    #[test]
    fn a_projects_warning_options_hide_its_warnings() {
        let code = "class Old { [System.Obsolete(\"no\")] public static void M() { } public static int N() { M(); return \"x\"; } }";
        let errors = |warnings: Vec<crate::project::WarningOptions>| {
            let project = Project {
                kind: ProjectKind::Msbuild,
                projects: 1,
                roots: Vec::new(),
                files: Vec::new(),
                everything: true,
                references: Vec::new(),
                symbols: Vec::new(),
                generated: String::new(),
                assemblies: vec!["Package".into()],
                owned_files: vec![(PathBuf::from("/p/Old.cs"), 0)],
                owned_folders: Vec::new(),
                language_versions: Vec::new(),
                owned_only: false,
                unbuilt: Vec::new(),
                assembly_symbols: Vec::new(),
                assembly_references: Vec::new(),
                shared_files: Vec::new(),
                assembly_metadata: Vec::new(),
                assembly_warnings: warnings,
                assembly_nullable: Vec::new(),
            };
            let semantic = Semantic::build(
                project,
                vec![(PathBuf::from("/p/Old.cs"), code.to_string())],
                &[],
                None,
            );
            semantic
                .diagnostics(Path::new("/p/Old.cs"), None)
                .unwrap_or_default()
                .iter()
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(errors(Vec::new()), ["CS0618", "CS0029"]);
        let none = crate::project::WarningOptions {
            level: Some(0),
            suppressed: Vec::new(),
        };
        assert_eq!(errors(vec![none]), ["CS0029"]);
        let without = crate::project::WarningOptions {
            level: None,
            suppressed: vec![618],
        };
        assert_eq!(errors(vec![without]), ["CS0029"]);
    }

    /// A generator writes the same internal attribute into every assembly it
    /// runs in; the copy compiled once is each of theirs.
    #[test]
    fn a_generated_file_shared_by_assemblies_is_each_ones_own() {
        let generated = "internal sealed class MarkAttribute : System.Attribute { }";
        let user = "[Mark] class Marked { }";
        let errors = |shared: Vec<(PathBuf, u16)>| {
            let project = Project {
                kind: ProjectKind::Msbuild,
                projects: 2,
                roots: Vec::new(),
                files: Vec::new(),
                everything: true,
                references: Vec::new(),
                symbols: Vec::new(),
                generated: String::new(),
                assemblies: vec!["A".into(), "B".into()],
                owned_files: vec![
                    (PathBuf::from("/p/A/Mark.g.cs"), 0),
                    (PathBuf::from("/p/B/Use.cs"), 1),
                ],
                owned_folders: Vec::new(),
                language_versions: Vec::new(),
                owned_only: false,
                unbuilt: Vec::new(),
                assembly_symbols: Vec::new(),
                assembly_references: vec![Vec::new(), Vec::new()],
                shared_files: shared,
                assembly_metadata: Vec::new(),
                assembly_warnings: Vec::new(),
                assembly_nullable: Vec::new(),
            };
            let semantic = Semantic::build(
                project,
                vec![
                    (PathBuf::from("/p/A/Mark.g.cs"), generated.to_string()),
                    (PathBuf::from("/p/B/Use.cs"), user.to_string()),
                ],
                &[],
                None,
            );
            semantic
                .diagnostics(Path::new("/p/B/Use.cs"), None)
                .unwrap_or_default()
                .iter()
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            errors(vec![(PathBuf::from("/p/A/Mark.g.cs"), 1)]),
            Vec::<String>::new()
        );
        assert!(!errors(Vec::new()).is_empty());
    }

    /// A file is parsed as the version of C# its project says: in a Unity
    /// script (C# 9) `field` inside an accessor is a field of that name, not
    /// the property's backing field of C# 14.
    #[test]
    fn a_project_written_in_csharp_9_has_no_field_keyword() {
        let framework: Vec<(PathBuf, Arc<[u8]>)> = crate::project::framework_references(None)
            .into_iter()
            .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(&path).ok()?))))
            .collect();
        if framework.is_empty() {
            return;
        }
        let text =
            "class C {\n    System.Reflection.FieldInfo field;\n    string Name => field.Name;\n}";
        let errors = |version: &str| {
            let project = Project {
                kind: ProjectKind::Msbuild,
                projects: 1,
                roots: Vec::new(),
                files: Vec::new(),
                everything: true,
                references: Vec::new(),
                symbols: Vec::new(),
                generated: String::new(),
                assemblies: vec!["Game".to_string()],
                owned_files: vec![(PathBuf::from("/p/C.cs"), 0)],
                owned_folders: Vec::new(),
                language_versions: vec![version.to_string()],
                owned_only: false,
                unbuilt: Vec::new(),
                assembly_symbols: Vec::new(),
                assembly_references: Vec::new(),
                shared_files: Vec::new(),
                assembly_metadata: Vec::new(),
                assembly_warnings: Vec::new(),
                assembly_nullable: Vec::new(),
            };
            let semantic = Semantic::build(
                project,
                vec![(PathBuf::from("/p/C.cs"), text.to_string())],
                &framework,
                None,
            );
            semantic
                .diagnostics(Path::new("/p/C.cs"), None)
                .unwrap_or_default()
                .iter()
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(errors("9.0"), Vec::<String>::new());
        // As C# 14 reads it, `field` is the string behind `Name`.
        assert_eq!(errors("14"), ["CS1061"]);
    }

    /// Two assemblies of the project may each have a type of one name — every
    /// Unity assembly gets its own `UnitySourceGeneratedAssemblyMonoScriptTypes_v1`
    /// from a generator — and compiling them at once is no reason to call
    /// either a duplicate. In one assembly it still is.
    #[test]
    fn a_type_of_one_name_in_two_projects_is_no_duplicate() {
        let text = "internal class Gen { public int X { get; } void M() { } }";
        let project = |owners: [u16; 2]| Project {
            kind: ProjectKind::Msbuild,
            projects: 2,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: vec!["A".to_string(), "B".to_string()],
            owned_files: vec![
                (PathBuf::from("/p/A/Gen.cs"), owners[0]),
                (PathBuf::from("/p/B/Gen.cs"), owners[1]),
            ],
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let errors = |owners: [u16; 2]| {
            let semantic = Semantic::build(
                project(owners),
                vec![
                    (PathBuf::from("/p/A/Gen.cs"), text.to_string()),
                    (PathBuf::from("/p/B/Gen.cs"), text.to_string()),
                ],
                &[],
                None,
            );
            ["/p/A/Gen.cs", "/p/B/Gen.cs"]
                .iter()
                .flat_map(|path| {
                    semantic
                        .diagnostics(Path::new(path), None)
                        .unwrap_or_default()
                })
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(errors([0, 1]), Vec::<String>::new());
        assert!(!errors([0, 0]).is_empty());
    }

    /// `global` in `global::System.Int32` is the global namespace, in a type,
    /// a `using` and an expression alike.
    #[test]
    fn global_before_two_colons_is_the_global_namespace() {
        let text = "using G = global::System;\nclass C {\n    global::System.Int32 f;\n    void M() { global::System.Console.WriteLine(); }\n}";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let mut view = semantic
            .view_of(Path::new("/p/C.cs"), None)
            .expect("a view");
        let global = semantic.compilation().global_namespace();
        let mut at = 0;
        let mut found = 0;
        while let Some(offset) = text[at..].find("global::") {
            let offset = at + offset;
            let token = view.name_token_at(offset as u32).expect("a token");
            assert_eq!(
                view.resolve(&token),
                Some(Resolved::Symbol(global)),
                "at {offset}"
            );
            found += 1;
            at = offset + 8;
        }
        assert_eq!(found, 3);
    }

    /// A name in an attribute's arguments refers to what it names, as one
    /// in a body does: `MethodImplOptions` and `AggressiveInlining` in
    /// `[MethodImpl(MethodImplOptions.AggressiveInlining)]`, on a method, a
    /// type and the assembly alike. So does one in a parameter's default
    /// value, an enum member's value and a fixed buffer's size, and an
    /// attribute named through an alias of its namespace.
    #[test]
    fn a_name_in_an_attributes_arguments_resolves() {
        let text = "using System.Runtime.CompilerServices;\n\
                    using System.ComponentModel;\n\
                    using Model = System.ComponentModel;\n\
                    [assembly: CompilationRelaxations(CompilationRelaxations.NoStringInterning)]\n\
                    [EditorBrowsable(EditorBrowsableState.Never)]\n\
                    class C {\n\
                        const int Size = 4;\n\
                        [MethodImpl(MethodImplOptions.AggressiveInlining)]\n\
                        void M([DefaultValue(Size)] int x, uint state = uint.MaxValue) { }\n\
                        [Model.Browsable(false)] int P { get; }\n\
                    }\n\
                    enum Kind { None = MethodImplOptions.NoInlining }\n\
                    unsafe struct Buffer { const int Count = 2; fixed int items[Count]; }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let mut view = semantic
            .view_of(Path::new("/p/C.cs"), None)
            .expect("a view");
        let mut found = Vec::new();
        for name in [
            "CompilationRelaxations.NoStringInterning",
            "NoStringInterning",
            "EditorBrowsableState",
            "Never",
            "MethodImplOptions",
            "AggressiveInlining",
            "Size)",
            "MaxValue",
            "Browsable(false",
            "NoInlining",
            "Count]",
        ] {
            let offset = text.find(name).expect("the name is there");
            let token = view.name_token_at(offset as u32).expect("a token");
            found.push(match view.resolve(&token) {
                Some(Resolved::Symbol(symbol)) => {
                    semantic.compilation().symbols().get(symbol).name.clone()
                }
                other => format!("{other:?}"),
            });
        }
        assert_eq!(
            found,
            [
                "CompilationRelaxations",
                "NoStringInterning",
                "EditorBrowsableState",
                "Never",
                "MethodImplOptions",
                "AggressiveInlining",
                "Size",
                "MaxValue",
                "BrowsableAttribute",
                "NoInlining",
                "Count"
            ]
        );
    }

    /// `nameof` names an outer class's instance method from a nested class's
    /// static field, which no other expression there may.
    #[test]
    fn nameof_an_outer_instance_method_resolves() {
        let text = "class R {\n\
                        static class Profiling {\n\
                            const string k_Name = nameof(R);\n\
                            public static readonly string a = $\"{k_Name}.{nameof(Setup)}\";\n\
                            public static readonly string b = nameof(Lights);\n\
                        }\n\
                        void Setup(int a) { }\n\
                        void Setup(int a, bool b) { }\n\
                        public virtual void Lights() { }\n\
                    }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let mut view = semantic
            .view_of(Path::new("/p/C.cs"), None)
            .expect("a view");
        for name in ["Lights)", "Setup)"] {
            let offset = text.find(name).expect("the name") as u32;
            let token = view.name_token_at(offset).expect("a token");
            match view.resolve(&token) {
                Some(Resolved::Symbol(symbol)) => assert_eq!(
                    semantic.compilation().symbols().get(symbol).name,
                    name.trim_end_matches(')')
                ),
                other => panic!("{name}: {other:?}"),
            }
        }
    }

    /// Names in expressions an editor found unresolved in a large Unity project: `var`
    /// of a conditional between a method group and a cast one, the members
    /// an anonymous type is made with, the variable a degenerate `select`
    /// gives back, a local in a lambda beside `null`, a calling convention.
    #[test]
    fn names_in_awkward_expressions_resolve() {
        let text = "using System;\nusing System.Linq;\n\
                    class Slot { }\n\
                    class C {\n\
                        Slot Out(int i) => null;\n\
                        Slot In(int i) => null;\n\
                        void M(bool input, string[] paths) {\n\
                            var getSlots = input ? Out : (Func<int, Slot>)In;\n\
                            var slot = getSlots(1);\n\
                            var pair = new { slotRef = slot, count = 1 };\n\
                            var scenes = (from scene in paths where scene.EndsWith(\"x\") select scene).ToArray();\n\
                            var inspect = new Action(() => { });\n\
                            unsafe { delegate* unmanaged[Cdecl]<int> pointer = null; }\n\
                            var holder = new Holder { Inspect = input ? null : () => { Console.Write(1); inspect(); }, Count = 1 };\n\
                        }\n\
                        class Holder { public Action Inspect; public int Count; }\n\
                    }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let mut view = semantic
            .view_of(Path::new("/p/C.cs"), None)
            .expect("a view");
        let mut unresolved = Vec::new();
        for name in [
            "var getSlots",
            "var slot",
            "getSlots(1)",
            "slotRef",
            "count =",
            "scene).ToArray",
            "inspect();",
            "Cdecl",
        ] {
            let offset = text.find(name).expect("the name") as u32;
            let token = view.name_token_at(offset).expect("a token");
            if view.resolve(&token).is_none() {
                unresolved.push(name);
            }
        }
        assert_eq!(unresolved, Vec::<&str>::new());
    }

    /// A lambda handed to the one overload a delegate can be has that
    /// delegate's parameters, past an earlier call in the chain.
    #[test]
    fn a_lambda_in_a_builder_chain_is_typed() {
        let text = "using System;\nusing System.Collections.Generic;\n\
                    struct Column { public string Name; }\n\
                    class TreeBuilder {\n\
                        public TreeBuilder With(Column column) => this;\n\
                        public TreeBuilder With(Column[] columns) => this;\n\
                        public TreeBuilder With(Action<IEnumerable<object>> selected) => this;\n\
                    }\n\
                    abstract class View {\n\
                        public Action<IEnumerable<object>> ItemsSelected;\n\
                        internal abstract Column[] Columns { get; }\n\
                        void M() {\n\
                            var tb = new TreeBuilder()\n\
                                .With(Columns)\n\
                                .With((items) => ItemsSelected.Invoke(items));\n\
                        }\n\
                    }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let mut view = semantic
            .view_of(Path::new("/p/C.cs"), None)
            .expect("a view");
        let offset = text.find("(items)").expect("the lambda") as u32 + 1;
        let token = view.name_token_at(offset).expect("a token");
        match view.resolve(&token) {
            Some(Resolved::Local { ty, .. }) => assert!(!ty.is_error(), "{ty:?}"),
            other => panic!("{other:?}"),
        }
    }

    /// What is wrong in a field's initializer reaches the editor: it is
    /// the declarator's body, not the declaration's, and asking the
    /// declaration for it found nothing.
    #[test]
    fn a_field_initializer_is_checked_for_the_editor() {
        let text = "using System.Collections.Generic;\n\
                    [System.Obsolete(\"x\")] class UiInstance<T> { }\n\
                    class H {\n\
                        List<UiInstance<H>> items =\n\
                            new List<UiInstance<H>>();\n\
                        int count = \"many\", other = 1;\n\
                    }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let found: Vec<(u32, String, String)> = semantic
            .diagnostics(Path::new("/p/C.cs"), None)
            .unwrap_or_default()
            .iter()
            .map(|d| {
                (
                    d.span().start(),
                    d.code().to_string(),
                    d.message().to_string(),
                )
            })
            .collect();
        let at = |needle: &str| text.find(needle).expect("there") as u32;
        assert_eq!(
            found,
            [
                (
                    at("UiInstance<H>> items"),
                    "CS0618".into(),
                    "'UiInstance<H>' is obsolete: 'x'".into()
                ),
                (
                    at("UiInstance<H>>()"),
                    "CS0618".into(),
                    "'UiInstance<H>' is obsolete: 'x'".into()
                ),
                (
                    at("\"many\""),
                    "CS0029".into(),
                    "Cannot implicitly convert type 'string' to 'int'".into()
                ),
            ]
        );
    }

    /// Names resolved as Roslyn's `GetSymbolInfo` has them, where Rustlyn
    /// said otherwise: the `System` of `[System.Serializable]`, the enum of
    /// `RenderType.Custom` beside a `RenderType` property, a setter's `value`
    /// at its `set`, the tuple `var (a, b)` stands for, and an override where
    /// the receiver's type has one.
    #[test]
    fn names_resolve_as_roslyn_resolves_them() {
        let text = "using System;\n\
                    enum RenderType { Opaque, Custom }\n\
                    class Base { public virtual void Destroy() { } }\n\
                    class Node : Base { public override void Destroy() { } }\n\
                    delegate float Ranged(float start, float end, float value);\n\
                    static class Cubic { public static float Out(float v) => v; public static float Out(float s, float e, float v) => v; }\n\
                    class Timer { public static Timer Start() => new Timer(); }\n\
                    [System.Serializable]\n\
                    class C {\n\
                        RenderType RenderType { get; set; }\n\
                        int count;\n\
                        public event System.EventHandler<System.EventArgs> Changed;\n\
                        public int Count { get => count; private set { count = value; } }\n\
                        void M(Node node, (int, string) pair) {\n\
                            RenderType = RenderType.Custom;\n\
                            var (number, name) = pair;\n\
                            node.Destroy();\n\
                            Ranged ranged; ranged = Cubic.Out;\n\
                            Func<float, float> generic = Pick<float>;\n\
                            string text = pair.Item2?.ToString(); }\n\
                        public override string ToString() => \"c\";\n\
                        static float Pick(float v, int n) => v;\n\
                        Timer Timer = Timer.Start();\n\
                        static T Pick<T>(T v) => v;\n\
                        void N() {\n\
                        }\n\
                    }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let path = Path::new("/p/C.cs");
        let mut view = semantic.view_of(path, None).expect("a view");
        let symbols = semantic.compilation().symbols();
        let mut name_at = |needle: &str, skip: usize| {
            let offset = text.find(needle).expect("there") + skip;
            let token = view.name_token_at(offset as u32).expect("a token");
            match view.resolve_definition(&token) {
                Some(Resolved::Symbol(symbol)) => {
                    let found = symbols.get(symbol);
                    let owner = found
                        .container
                        .map(|owner| symbols.get(owner).name.clone())
                        .unwrap_or_default();
                    let arity = found.as_named_type().map_or(0, |detail| detail.arity);
                    let arity = if arity > 0 {
                        format!("`{arity}")
                    } else {
                        String::new()
                    };
                    format!("{:?} {owner}.{}{arity}", found.kind, found.name)
                }
                Some(Resolved::Local { span, .. }) => format!("local at {}", span.start()),
                None => "nothing".to_string(),
            }
        };
        assert_eq!(name_at("System.Serializable", 0), "Namespace .System");
        assert_eq!(name_at("RenderType.Custom", 0), "NamedType .RenderType");
        assert_eq!(name_at("Timer.Start", 0), "NamedType .Timer");
        assert_eq!(name_at("var (number", 0), "NamedType System.ValueTuple`2");
        assert_eq!(name_at("Destroy();\n", 0), "Method Node.Destroy");
        assert_eq!(
            name_at("EventHandler<", 0),
            "NamedType System.EventHandler`1"
        );
        // After `?.` the receiver is what is before the `?`.
        assert_eq!(name_at("ToString(); }", 0), "Method String.ToString");
        let set = text.find("set {").expect("the setter") as u32;
        let offset = text.find("value; }").expect("value") as u32;
        let token = view.name_token_at(offset).expect("a token");
        let Some(Resolved::Symbol(value)) = view.resolve_definition(&token) else {
            panic!("value is a parameter");
        };
        assert_eq!(symbols.get(value).locations[0].span.start(), set);
        // The overload the delegate takes, not the first of the group.
        let out = text.find("Cubic.Out;").expect("the group") + 6;
        let token = view.name_token_at(out as u32).expect("a token");
        let Some(Resolved::Symbol(chosen)) = view.resolve_definition(&token) else {
            panic!("Out is a method");
        };
        assert_eq!(
            symbols
                .get(chosen)
                .as_method()
                .map(|method| method.parameters.len()),
            Some(3)
        );
        // `Pick<float>` is the generic one, written with its type arguments.
        let pick = text.find("Pick<float>").expect("the group");
        let token = view.name_token_at(pick as u32).expect("a token");
        let Some(Resolved::Symbol(chosen)) = view.resolve_definition(&token) else {
            panic!("Pick is a method");
        };
        assert_eq!(
            symbols
                .get(chosen)
                .as_method()
                .map(|method| method.type_parameters.len()),
            Some(1)
        );
    }

    /// A `goto` leads to its label, and the label is itself; the name a
    /// `using` alias declares is what it stands for.
    #[test]
    fn a_label_and_an_alias_name_resolve() {
        let text = "using Real = System.Single;\n\
                    class C {\n\
                        void M(int n) {\n\
                            retry:\n\
                            if (n-- > 0) goto retry;\n\
                            void Local() { again: goto again; }\n\
                        }\n\
                    }";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let mut view = semantic
            .view_of(Path::new("/p/C.cs"), None)
            .expect("a view");
        let label = text.find("retry:").expect("the label") as u32;
        for name in ["retry:", "retry;"] {
            let offset = text.find(name).expect("the name") as u32;
            let token = view.name_token_at(offset).expect("a token");
            match view.resolve(&token) {
                Some(Resolved::Local { span, .. }) => assert_eq!(span.start(), label),
                other => panic!("{name}: {other:?}"),
            }
        }
        let again = text.find("again:").expect("the label") as u32;
        let token = view
            .name_token_at(text.find("again;").expect("the goto") as u32)
            .expect("a token");
        assert!(
            matches!(view.resolve(&token), Some(Resolved::Local { span, .. }) if span.start() == again)
        );
        let token = view
            .name_token_at(text.find("Real").expect("the alias") as u32)
            .expect("a token");
        match view.resolve(&token) {
            Some(Resolved::Symbol(symbol)) => {
                assert_eq!(semantic.compilation().symbols().get(symbol).name, "Single");
            }
            other => panic!("{other:?}"),
        }
    }

    /// `var` is the type it stands for wherever it declares something: a
    /// `ref` local, a discarded `out`, a tuple.
    #[test]
    fn var_resolves_to_its_type_in_every_declaration() {
        let text = "class C {\n    void M(int x) {\n        ref var r = ref x;\n        int.TryParse(\"1\", out var _);\n        var t = (1, \"a\");\n        foreach (ref var e in new System.Span<int>(new int[1])) { }\n    }\n}";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let path = Path::new("/p/C.cs");
        let mut view = semantic.view_of(path, None).expect("a view");
        let mut found = Vec::new();
        let mut at = 0;
        while let Some(offset) = text[at..].find("var ") {
            let offset = at + offset;
            let token = view.name_token_at(offset as u32).expect("a token");
            found.push(match view.resolve(&token) {
                Some(Resolved::Symbol(symbol)) => {
                    semantic.compilation().symbols().get(symbol).name.clone()
                }
                other => format!("{other:?}"),
            });
            at = offset + 4;
        }
        assert_eq!(found, ["Int32", "Int32", "ValueTuple", "Int32"]);
    }

    /// Unity's engine assemblies show their internals to its own packages
    /// with `[InternalsVisibleTo]`. The editor compiles every project at
    /// once, so each file sees the internals of a reference only when the
    /// project it is of is named.
    #[test]
    fn a_reference_shows_its_internals_only_to_the_projects_it_names() {
        let framework: Vec<(PathBuf, Arc<[u8]>)> = crate::project::framework_references(None)
            .into_iter()
            .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(&path).ok()?))))
            .collect();
        if framework.is_empty() {
            return;
        }
        let images: Vec<&[u8]> = framework.iter().map(|(_, bytes)| &bytes[..]).collect();
        let library = Compilation::create_with_references(
            vec![parse_with(
                SourceText::new(
                    "Engine.cs",
                    "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"Game.Editor\")]\n\
                     namespace Engine {\n\
                         internal enum Hidden { One }\n\
                         internal class Button { }\n\
                         public class Open { internal int Secret; internal void Style(string path) { } }\n\
                     }\n\
                     namespace Widgets { public class Button { public int Clicks; } }\n\
                     namespace Game.System { internal class Hidden { } }",
                ),
                &ParseOptions::default(),
            )],
            &images,
        );
        let library = rustlyn_emit::emit_library(&library, "Engine")
            .expect("the library emits")
            .assembly;
        let mut references = framework.clone();
        references.push((PathBuf::from("/refs/Engine.dll"), Arc::from(library)));
        let tool =
            "class Tool { int M(Engine.Open open) => (int)Engine.Hidden.One + open.Secret; }";
        // Not a friend: `Button` is the public one, as it is to Roslyn.
        // An internal method it may not call is not there for it: the call
        // is the extension method's. And `System` is not `Game.System`, where
        // there is nothing but another assembly's internal type.
        let game = "using Engine;\nusing Widgets;\n\
                    namespace Game {\n\
                    static class Styles { public static void Style(this Open open, string path) { } }\n\
                    class Game {\n\
                        int M(Button b) => b.Clicks;\n\
                        void N(Open open) => open.Style(\"x\");\n\
                        System.Int32 count;\n\
                    }\n\
                    }";
        let project = Project {
            kind: ProjectKind::Msbuild,
            projects: 2,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: vec!["Game".to_string(), "Game.Editor".to_string()],
            owned_files: vec![
                (PathBuf::from("/p/Game.cs"), 0),
                (PathBuf::from("/p/Tool.cs"), 1),
                (PathBuf::from("/p/Copy.cs"), 0),
            ],
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let semantic = Semantic::build(
            project,
            vec![
                (PathBuf::from("/p/Tool.cs"), tool.to_string()),
                (PathBuf::from("/p/Game.cs"), game.to_string()),
                (PathBuf::from("/p/Copy.cs"), tool.replace("Tool", "Copy")),
            ],
            &references,
            None,
        );
        let errors = |path: &str| {
            semantic
                .diagnostics(Path::new(path), None)
                .unwrap_or_default()
                .iter()
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(errors("/p/Tool.cs"), Vec::<String>::new());
        assert_eq!(errors("/p/Game.cs"), Vec::<String>::new());
        // The same code in a project the reference does not name sees only
        // what is public.
        assert!(!errors("/p/Copy.cs").is_empty());
    }

    /// A compiled class that implements an interface explicitly shows
    /// nothing of how — the methods are private — and a class deriving
    /// from it that lists the interface again implements it all the same:
    /// Unity's `PropertyBag<T>` is an `IPropertyBag`, the engine's `Editor`
    /// an `IToolModeOwner`.
    #[test]
    fn a_compiled_base_implements_the_interfaces_it_has() {
        let framework: Vec<(PathBuf, Arc<[u8]>)> = crate::project::framework_references(None)
            .into_iter()
            .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(&path).ok()?))))
            .collect();
        if framework.is_empty() {
            return;
        }
        let images: Vec<&[u8]> = framework.iter().map(|(_, bytes)| &bytes[..]).collect();
        let library = Compilation::create_with_references(
            vec![parse_with(
                SourceText::new(
                    "Bag.cs",
                    "namespace Properties {\n\
                         public interface IPropertyBag { void Accept(object visitor, ref object container); bool Available { get; } }\n\
                         public interface IListPropertyBag<T> : IPropertyBag { int Count(T list); }\n\
                         public abstract class PropertyBag<T> : IPropertyBag {\n\
                             void IPropertyBag.Accept(object visitor, ref object container) { }\n\
                             bool IPropertyBag.Available => true;\n\
                         }\n\
                     }",
                ),
                &ParseOptions::default(),
            )],
            &images,
        );
        let library = rustlyn_emit::emit_library(&library, "Properties")
            .expect("the library emits")
            .assembly;
        let mut references = framework.clone();
        references.push((PathBuf::from("/refs/Properties.dll"), Arc::from(library)));
        let bag = "using Properties;\n\
                   class ArrayBag : PropertyBag<int[]>, IListPropertyBag<int[]> { public int Count(int[] list) => list.Length; }\n\
                   class Missing : PropertyBag<int[]>, IListPropertyBag<int[]> { }";
        let semantic = Semantic::build(
            Project {
                kind: ProjectKind::Folder,
                projects: 0,
                roots: Vec::new(),
                files: Vec::new(),
                everything: true,
                references: Vec::new(),
                symbols: Vec::new(),
                generated: String::new(),
                assemblies: Vec::new(),
                owned_files: Vec::new(),
                owned_folders: Vec::new(),
                language_versions: Vec::new(),
                owned_only: false,
                unbuilt: Vec::new(),
                assembly_symbols: Vec::new(),
                assembly_references: Vec::new(),
                shared_files: Vec::new(),
                assembly_metadata: Vec::new(),
                assembly_warnings: Vec::new(),
                assembly_nullable: Vec::new(),
            },
            vec![(PathBuf::from("/p/Bag.cs"), bag.to_string())],
            &references,
            None,
        );
        let errors: Vec<String> = semantic
            .diagnostics(Path::new("/p/Bag.cs"), None)
            .unwrap_or_default()
            .iter()
            .filter(|diagnostic| diagnostic.is_error())
            .map(|diagnostic| diagnostic.code().to_string())
            .collect();
        // Only what the base does not have is missing.
        assert_eq!(errors, ["CS0535"]);
    }

    /// The engine's `Editor` has `internal virtual` methods its friends
    /// override — Timeline's inspectors, the sprite editor. A friend's
    /// `internal override` overrides one; anybody else's overrides nothing.
    #[test]
    fn a_friend_overrides_a_references_internal_virtual_method() {
        let framework: Vec<(PathBuf, Arc<[u8]>)> = crate::project::framework_references(None)
            .into_iter()
            .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(&path).ok()?))))
            .collect();
        if framework.is_empty() {
            return;
        }
        let images: Vec<&[u8]> = framework.iter().map(|(_, bytes)| &bytes[..]).collect();
        let library = Compilation::create_with_references(
            vec![parse_with(
                SourceText::new(
                    "Editor.cs",
                    "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"Timeline\")]\n\
                     namespace UnityEditor { public class Editor { internal virtual void OnHeaderIconGUI(int rect) { } } }",
                ),
                &ParseOptions::default(),
            )],
            &images,
        );
        let library = rustlyn_emit::emit_library(&library, "UnityEditor")
            .expect("the library emits")
            .assembly;
        let mut references = framework.clone();
        references.push((PathBuf::from("/refs/UnityEditor.dll"), Arc::from(library)));
        let inspector = "class Inspector : UnityEditor.Editor { internal override void OnHeaderIconGUI(int rect) { } }";
        let project = Project {
            kind: ProjectKind::Msbuild,
            projects: 2,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: vec!["Timeline".to_string(), "Other".to_string()],
            owned_files: vec![
                (PathBuf::from("/p/Timeline.cs"), 0),
                (PathBuf::from("/p/Other.cs"), 1),
            ],
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let semantic = Semantic::build(
            project,
            vec![
                (PathBuf::from("/p/Timeline.cs"), inspector.to_string()),
                (PathBuf::from("/p/Other.cs"), inspector.to_string()),
            ],
            &references,
            None,
        );
        let errors = |path: &str| {
            semantic
                .diagnostics(Path::new(path), None)
                .unwrap_or_default()
                .iter()
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(errors("/p/Timeline.cs"), Vec::<String>::new());
        assert_eq!(errors("/p/Other.cs"), ["CS0115"]);
    }

    /// Unity's Burst carries its own copy of Cecil beside the one other
    /// packages compile against, and both are references of the project: a
    /// name of Cecil's is the copy the code's assembly references, and
    /// ambiguous (CS0433) only to one that references both. A namespace
    /// only an unreferenced assembly declares is not there either: the
    /// engine's `Unity.CompilationPipeline` hides no `CompilationPipeline`
    /// class from code in `namespace Unity.Burst`.
    #[test]
    fn a_type_two_references_declare_is_the_one_the_assembly_references() {
        let framework: Vec<(PathBuf, Arc<[u8]>)> = crate::project::framework_references(None)
            .into_iter()
            .filter_map(|path| Some((path.clone(), Arc::from(std::fs::read(&path).ok()?))))
            .collect();
        if framework.is_empty() {
            return;
        }
        let images: Vec<&[u8]> = framework.iter().map(|(_, bytes)| &bytes[..]).collect();
        let mut references = framework.clone();
        for (name, member) in [
            ("Mono.Cecil", "Mono"),
            ("Unity.Burst.Cecil", "Burst"),
            ("Unity.CompilationPipeline.Common", "Pipeline"),
        ] {
            let source = if member == "Pipeline" {
                "namespace Unity.CompilationPipeline.Common { public class Message { } }"
                    .to_string()
            } else {
                format!(
                    "namespace Mono.Cecil {{ public class AssemblyDefinition {{ public int {member}; \
                     public static AssemblyDefinition Read() => null; }} }}"
                )
            };
            let library = Compilation::create_with_references(
                vec![parse_with(
                    SourceText::new("Cecil.cs", source.as_str()),
                    &ParseOptions::default(),
                )],
                &images,
            );
            let library = rustlyn_emit::emit_library(&library, name)
                .expect("the library emits")
                .assembly;
            references.push((
                PathBuf::from(format!("/refs/{name}.dll")),
                Arc::from(library),
            ));
        }
        let code = |member: &str| {
            format!(
                "using Mono.Cecil;\n\
                 class C {{ int M(AssemblyDefinition d) => d.{member} + Mono.Cecil.AssemblyDefinition.Read().{member}; }}"
            )
        };
        let project = Project {
            kind: ProjectKind::Unity,
            projects: 3,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: vec![
                "Burst.CodeGen".to_string(),
                "Collections.CodeGen".to_string(),
                "Both".to_string(),
            ],
            owned_files: vec![
                (PathBuf::from("/p/Burst.cs"), 0),
                (PathBuf::from("/p/Collections.cs"), 1),
                (PathBuf::from("/p/Both.cs"), 2),
            ],
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: vec![
                vec!["unity.burst.cecil".to_string()],
                vec!["mono.cecil".to_string()],
                vec!["mono.cecil".to_string(), "unity.burst.cecil".to_string()],
            ],
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let semantic = Semantic::build(
            project,
            vec![
                (
                    PathBuf::from("/p/Burst.cs"),
                    "using UnityEditor.Compilation;\n".to_string()
                        + &code("Burst")
                        + "\nnamespace UnityEditor.Compilation { public static class CompilationPipeline { public static int Started; } }\n\
                           namespace Unity.Burst { class Loader { int M() => CompilationPipeline.Started; } }",
                ),
                (PathBuf::from("/p/Collections.cs"), code("Mono")),
                (PathBuf::from("/p/Both.cs"), code("Mono")),
            ],
            &references,
            None,
        );
        let errors = |path: &str| {
            semantic
                .diagnostics(Path::new(path), None)
                .unwrap_or_default()
                .iter()
                .filter(|diagnostic| diagnostic.is_error())
                .map(|diagnostic| diagnostic.code().to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(errors("/p/Burst.cs"), Vec::<String>::new());
        assert_eq!(errors("/p/Collections.cs"), Vec::<String>::new());
        assert!(errors("/p/Both.cs").contains(&"CS0433".to_string()));
    }

    /// A save inside a body reuses the previous compilation rather than
    /// declaring every file again, and comes out as a whole build would.
    #[test]
    fn a_save_inside_a_body_is_the_previous_compilation_with_its_tree() {
        let project = || Project {
            kind: ProjectKind::Folder,
            projects: 0,
            roots: Vec::new(),
            files: Vec::new(),
            everything: true,
            references: Vec::new(),
            symbols: Vec::new(),
            generated: String::new(),
            assemblies: Vec::new(),
            owned_files: Vec::new(),
            owned_folders: Vec::new(),
            language_versions: Vec::new(),
            owned_only: false,
            unbuilt: Vec::new(),
            assembly_symbols: Vec::new(),
            assembly_references: Vec::new(),
            shared_files: Vec::new(),
            assembly_metadata: Vec::new(),
            assembly_warnings: Vec::new(),
            assembly_nullable: Vec::new(),
        };
        let other = "class B { int Get() => 1; }";
        let before = "class A {\n    int x;\n    void M() { x = 1; }\n    void N() { }\n}";
        let after = "class A {\n    int x;\n    void M() { x = 2; x++; System.Console.WriteLine(x); }\n    void N() { }\n}";
        let sources = |text: &str| {
            vec![
                (PathBuf::from("/p/A.cs"), text.to_string()),
                (PathBuf::from("/p/B.cs"), other.to_string()),
            ]
        };
        let first = Semantic::build(project(), sources(before), &[], None);
        let second = Semantic::build(project(), sources(after), &[], Some(&first));
        let whole = Semantic::build(project(), sources(after), &[], None);
        assert_eq!(
            second
                .compilation()
                .first_declaration_difference(whole.compilation()),
            None
        );
        // The edited tree is the new text, and the other one is shared.
        let index = second.trees[&PathBuf::from("/p/A.cs")];
        assert_eq!(
            second
                .compilation()
                .trees()
                .source(index)
                .map(|source| source.text().to_string()),
            Some(after.to_string())
        );
        // And it is the quick one: what declares something goes the whole way.
        let quick = first.compilation().with_tree_replaced(
            index,
            rustlyn_syntax::parse_with(
                rustlyn_text::SourceText::new("/p/A.cs", after),
                &rustlyn_syntax::ParseOptions::default(),
            ),
        );
        assert!(quick.is_some());
        let declaring =
            "class A {\n    int x;\n    void M() { x = 1; }\n    void N() { }\n    void O() { }\n}";
        let added = first.compilation().with_tree_replaced(
            index,
            rustlyn_syntax::parse_with(
                rustlyn_text::SourceText::new("/p/A.cs", declaring),
                &rustlyn_syntax::ParseOptions::default(),
            ),
        );
        assert!(added.is_none());
    }

    /// The offset of the `nth` occurrence of `marker` in `text`, plus `into`.
    pub(super) fn at(text: &str, marker: &str, into: usize) -> u32 {
        (text.find(marker).expect("the marker should be there") + into) as u32
    }

    fn source_spans(found: &[Found]) -> Vec<(String, u32)> {
        found
            .iter()
            .filter_map(|found| match &found.place {
                Place::Source { path, span } => Some((
                    path.file_name()?.to_string_lossy().into_owned(),
                    span.start(),
                )),
                Place::Metadata { .. } => None,
            })
            .collect()
    }

    #[test]
    fn a_call_goes_to_the_overload_it_calls() {
        let text =
            "class C {\n  void M(int a) { }\n  void M(string s) { }\n  void T() { M(\"x\"); }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let (word, found) = semantic
            .definition(Path::new("/p/C.cs"), at(text, "M(\"x\")", 0), None)
            .expect("resolved");
        assert_eq!(word, "M");
        assert_eq!(
            source_spans(&found),
            vec![("C.cs".to_string(), at(text, "M(string", 0))]
        );
    }

    #[test]
    fn a_member_of_a_var_goes_to_the_type_the_value_has() {
        let player =
            "class Player { public string Name; public static Player Make() => new Player(); }\n";
        let game = "class Game { void Run() { var p = Player.Make(); var n = p.Name; } }\n";
        let semantic =
            compile(&[("Player.cs", player), ("Game.cs", game)], false).expect("compiled");
        let (_, found) = semantic
            .definition(Path::new("/p/Game.cs"), at(game, "p.Name", 2), None)
            .expect("resolved");
        assert_eq!(
            source_spans(&found),
            vec![("Player.cs".to_string(), at(player, "Name", 0))]
        );
    }

    #[test]
    fn a_local_goes_to_where_it_was_declared() {
        let text = "class C { int T() { int count = 1; return count + 1; } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let (_, found) = semantic
            .definition(Path::new("/p/C.cs"), at(text, "count + 1", 0), None)
            .expect("resolved");
        assert_eq!(
            source_spans(&found),
            vec![("C.cs".to_string(), at(text, "count", 0))]
        );
    }

    #[test]
    fn references_find_the_method_and_not_its_namesake() {
        let a = "class A { public void Go() { } void Self() { Go(); } }\n";
        let b = "class B { public void Go() { } void Use(A a) { a.Go(); Go(); } }\n";
        let semantic = compile(&[("A.cs", a), ("B.cs", b)], false).expect("compiled");
        let (word, found) = semantic
            .references(Path::new("/p/A.cs"), at(a, "Go", 0), None)
            .expect("resolved");
        assert_eq!(word, "Go");
        let found: Vec<(String, u32)> = found
            .iter()
            .map(|(path, span)| {
                (
                    path.file_name().unwrap().to_string_lossy().into_owned(),
                    span.start(),
                )
            })
            .collect();
        assert_eq!(
            found,
            vec![
                ("A.cs".to_string(), at(a, "Go()", 0)),
                ("A.cs".to_string(), at(a, "Go(); }", 0)),
                ("B.cs".to_string(), at(b, "a.Go", 2)),
            ]
        );
    }

    #[test]
    fn references_to_a_type_include_its_construction() {
        let a = "class Thing { }\n";
        let b = "class User { Thing t = new Thing(); }\n";
        let semantic = compile(&[("A.cs", a), ("B.cs", b)], false).expect("compiled");
        let (_, found) = semantic
            .references(Path::new("/p/A.cs"), at(a, "Thing", 0), None)
            .expect("resolved");
        assert_eq!(found.len(), 3, "{found:?}");
    }

    #[test]
    fn completion_after_a_dot_lists_the_members_of_the_type() {
        let text = "class Player { public int Health; public void Heal() { } int secret; }\n\
                    class Game { void Run(Player p) { p. } }\n";
        let semantic = compile(&[("G.cs", text)], false).expect("compiled");
        let completions = semantic
            .completions(Path::new("/p/G.cs"), at(text, "p. }", 2), None)
            .expect("completed");
        let labels: Vec<&str> = completions
            .items
            .iter()
            .map(|item| item.label.as_str())
            .collect();
        assert!(labels.contains(&"Health"), "{labels:?}");
        assert!(labels.contains(&"Heal"), "{labels:?}");
        assert!(!labels.contains(&"secret"), "{labels:?}");
        assert!(!labels.contains(&"Game"), "{labels:?}");
    }

    #[test]
    fn completion_of_a_word_offers_locals_members_and_types() {
        let text = "class Game { int score; void Run(int level) { int lives = 3; li } }\n";
        let semantic = compile(&[("G.cs", text)], false).expect("compiled");
        let completions = semantic
            .completions(Path::new("/p/G.cs"), at(text, "li }", 2), None)
            .expect("completed");
        assert_eq!(completions.start, at(text, "li }", 0));
        let labels: Vec<&str> = completions
            .items
            .iter()
            .map(|item| item.label.as_str())
            .collect();
        for expected in ["lives", "level", "score", "Run", "Game", "return"] {
            assert!(labels.contains(&expected), "{expected} in {labels:?}");
        }
        // Locals first.
        assert_eq!(completions.items[0].label, "lives");
    }

    #[test]
    fn a_framework_member_leads_into_its_assembly() {
        let text = "using System;\nclass C { void T() { Console.WriteLine(1); } }\n";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            eprintln!("no .NET installed; skipped");
            return;
        };
        let (_, found) = semantic
            .definition(Path::new("/p/C.cs"), at(text, "WriteLine", 0), None)
            .expect("resolved");
        let [
            Found {
                place:
                    Place::Metadata {
                        assembly,
                        type_name,
                        member,
                    },
                ..
            },
        ] = found.as_slice()
        else {
            panic!("expected one metadata place, got {found:?}");
        };
        assert_eq!(type_name, "System.Console");
        assert_eq!(member.as_deref(), Some("WriteLine"));
        assert!(assembly.to_string_lossy().ends_with(".dll"));

        let completions = semantic
            .completions(Path::new("/p/C.cs"), at(text, "WriteLine", 0), None)
            .expect("completed");
        let labels: Vec<&str> = completions
            .items
            .iter()
            .map(|item| item.label.as_str())
            .collect();
        assert!(
            labels.contains(&"WriteLine") && labels.contains(&"ReadLine"),
            "{labels:?}"
        );
    }

    #[test]
    fn linq_is_offered_on_a_list() {
        let text = "using System.Linq;\nusing System.Collections.Generic;\n\
                    class C { void T(List<int> xs) { xs. } }\n";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        let completions = semantic
            .completions(Path::new("/p/C.cs"), at(text, "xs. }", 3), None)
            .expect("completed");
        let labels: Vec<&str> = completions
            .items
            .iter()
            .map(|item| item.label.as_str())
            .collect();
        for expected in ["Add", "Count", "Where", "Select"] {
            assert!(labels.contains(&expected), "{expected} in {labels:?}");
        }
    }

    #[test]
    fn words_are_matched_whole() {
        assert!(contains_word("a Go b", "Go"));
        assert!(!contains_word("Gone", "Go"));
        assert!(!contains_word("aGo", "Go"));
        assert!(contains_word("x.Go()", "Go"));
    }

    #[test]
    fn completion_answers_about_text_that_was_never_compiled() {
        let compiled = "class P { public int Hp; public void Heal() { } }\n\
                        class G { void R(P p) { } }\n";
        let semantic = compile(&[("G.cs", compiled)], false).expect("compiled");
        // Typed since: a new local, and a dot after it.
        let typed = "class P { public int Hp; public void Heal() { } }\n\
                     class G { void R(P p) { var q = p; q. } }\n";
        let completions = semantic
            .completions(Path::new("/p/G.cs"), at(typed, "q. }", 2), Some(typed))
            .expect("completed");
        let labels: Vec<&str> = completions
            .items
            .iter()
            .map(|item| item.label.as_str())
            .collect();
        assert!(
            labels.contains(&"Hp") && labels.contains(&"Heal"),
            "{labels:?}"
        );
    }

    /// The labels completion offers at `marker` (its first occurrence,
    /// `into` bytes in) of `typed`, the editor's text for a file compiled as
    /// something else.
    fn offered(
        semantic: &Semantic,
        file: &str,
        typed: &str,
        marker: &str,
        into: usize,
    ) -> Vec<String> {
        semantic
            .completions(
                Path::new(&format!("/p/{file}")),
                at(typed, marker, into),
                Some(typed),
            )
            .map(|list| list.items.into_iter().map(|item| item.label).collect())
            .unwrap_or_default()
    }

    /// The lambdas of an edited file are found as it reads now, wherever the
    /// edit moved them: binding one looks its syntax up by where it is.
    #[test]
    fn a_lambda_below_an_edit_is_bound_where_it_is_now() {
        let library = "using System;\nusing System.Collections.Generic;\n\
                       static class Seq {\n\
                           public static IEnumerable<R> Map<T, R>(this IEnumerable<T> s, Func<T, R> f) => null;\n\
                           public static IEnumerable<R> Map<T, R>(this IEnumerable<T> s, Func<T, int, R> f) => null;\n\
                       }\n\
                       class P { public int Age; }\n";
        let compiled = "using System.Collections.Generic;\n\
                        class C {\n    void M(List<P> list) {\n        var r = list.Map(e => e.Age);\n    }\n}\n";
        let semantic =
            compile(&[("Seq.cs", library), ("C.cs", compiled)], false).expect("compiled");
        // A statement typed above, and the member being typed again.
        let typed = "using System.Collections.Generic;\n\
                     class C {\n    void M(List<P> list) {\n        int extra = 42;\n        var r = list.Map(e => e.);\n    }\n}\n";
        let found = offered(&semantic, "C.cs", typed, "e.)", 2);
        assert!(found.iter().any(|label| label == "Age"), "{found:?}");
        // What a lambda wrote is read off it there too: `T` comes from the
        // `P` written on `e` alone.
        let apply = "using System;\nstatic class Ops { public static R Apply<T, R>(Func<T, R> f) => default; }\n\
                     class P { public int Age; }\n\
                     class C {\n    void M() {\n        var r = Ops.Apply((P e) => e.Age);\n    }\n}\n";
        let semantic = compile(&[("C.cs", apply)], false).expect("compiled");
        let typed = apply.replacen("        var r", "        int extra = 42;\n        var r", 1);
        let info = semantic
            .quick_info(Path::new("/p/C.cs"), at(&typed, "r =", 0), Some(&typed))
            .expect("described");
        assert!(info.description.contains("int r"), "{}", info.description);
    }

    /// Edits in two places leave what is between them as compiled: a field
    /// whose initializer is being typed in, below an edit near the top, is
    /// still the field it was.
    #[test]
    fn what_lies_between_two_edits_is_still_known() {
        let compiled = "using System;\n\
                        class Failure { public int Code; }\n\
                        static class Stubs {\n\
                            public static readonly Func<Failure, int> Read = f => f.Code;\n\
                            public static readonly Action<Failure> Throw = f => { f.Code.ToString(); };\n\
                        }\n";
        let semantic = compile(&[("Stubs.cs", compiled)], false).expect("compiled");
        let above = "// typed above\n";
        let typed = format!(
            "{above}{}",
            compiled.replacen("f => f.Code;", "f => f.;", 1)
        );
        let found = offered(&semantic, "Stubs.cs", &typed, "f.;", 2);
        assert!(found.iter().any(|label| label == "Code"), "{found:?}");
        // Cut off where it is typed, so the next lines run into it: the
        // field it is in no longer ends where it did, and is still found by
        // where it starts.
        let cut = format!(
            "{above}{}",
            compiled.replacen("f => { f.Code.ToString(); };", "f => { f.", 1)
        );
        let found = offered(&semantic, "Stubs.cs", &cut, "f => { f.", 9);
        assert!(found.iter().any(|label| label == "Code"), "{found:?}");
        // A file of top-level statements is their method, whatever was
        // typed at its very start.
        let program = "var count = 1;\nSystem.Console.WriteLine(count);\n";
        let semantic = compile(&[("Program.cs", program)], false).expect("compiled");
        let typed = format!("using System;\n{program}");
        let info = semantic
            .quick_info(
                Path::new("/p/Program.cs"),
                at(&typed, "count)", 0),
                Some(&typed),
            )
            .expect("described");
        assert!(
            info.description.contains("int count"),
            "{}",
            info.description
        );
    }

    /// What hovering `marker` (its first occurrence, `into` bytes in) says
    /// in `typed`, the editor's text for a file compiled as something else,
    /// or in the file as compiled where nothing else is typed.
    fn described(
        semantic: &Semantic,
        file: &str,
        typed: &str,
        edited: bool,
        marker: &str,
        into: usize,
    ) -> String {
        semantic
            .quick_info(
                Path::new(&format!("/p/{file}")),
                at(typed, marker, into),
                edited.then_some(typed),
            )
            .map(|info| info.description)
            .unwrap_or_default()
    }

    /// An accessor cut short where it is typed, so that the lines after
    /// run into it, is still the accessor it was: a setter has its
    /// `value`, and the lambda being written beside it what it is given.
    #[test]
    fn an_accessor_whose_end_moved_is_still_known() {
        let compiled = "using System;\nusing System.Collections.Generic;\n\
                        class Selector { public Selector(IEnumerable<string> sets) { } }\n\
                        class Options {\n\
                            Func<IEnumerable<string>, Selector> _factory;\n\
                            public Func<IEnumerable<string>, Selector> Factory {\n\
                                get => _factory;\n\
                                set => _factory = value ?? (sets => new Selector(sets));\n\
                            }\n\
                        }\n";
        let semantic = compile(&[("Options.cs", compiled)], false).expect("compiled");
        let typed = compiled.replacen("(sets => new Selector(sets));", "(sets =>", 1);
        let info = described(&semantic, "Options.cs", &typed, true, "sets =>", 0);
        assert!(info.contains("IEnumerable<string> sets"), "{info}");
        let info = described(&semantic, "Options.cs", &typed, true, "value ??", 0);
        assert!(info.contains("Selector> value"), "{info}");
    }

    /// A lambda bound to see what it returns and then unbound leaves no
    /// name behind: the slot its parameter had is the next local's — a
    /// query's range variable named like it — and the parameter is still
    /// itself.
    #[test]
    fn a_lambda_bound_on_trial_takes_its_names_back() {
        let source = "using System;\nusing System.Collections.Generic;\n\
                      static class Seq {\n\
                          public static IEnumerable<R> Select<T, R>(this IEnumerable<T> source, Func<T, R> f) => null;\n\
                          public static IEnumerable<KeyValuePair<K, int>> ScanBy<T, K>(this IEnumerable<T> source, Func<T, K> key, Func<K, int> seed) => null;\n\
                      }\n\
                      static class C {\n\
                          static IEnumerable<T> M<T>(IEnumerable<T> source) {\n\
                              return from e in source.ScanBy(e =>\n\
                          }\n\
                      }\n";
        let semantic = compile(&[("C.cs", source)], false).expect("compiled");
        let info = described(&semantic, "C.cs", source, false, "e =>", 0);
        assert!(info.contains("(parameter) T e"), "{info}");
    }

    /// A lambda a lambda returns, where the call they are given to cannot
    /// be settled yet: what the outer one is guessed to return is the
    /// delegate the inner one becomes.
    #[test]
    fn a_lambda_returned_by_a_lambda_is_the_delegate_returned() {
        let source = "using System;\nclass Args { public int Code; }\n\
                      delegate void Handler(object sender, Args e);\n\
                      static class Events {\n\
                          public static int FromEvent<TDelegate, TArgs>(Func<Action<TArgs>, TDelegate> conversion, Action<TDelegate> add, Action<TDelegate> remove) => 0;\n\
                      }\n\
                      class C {\n\
                          void M() {\n\
                              var r = Events.FromEvent<Handler, Args>(h => (sender, e) =>\n\
                          }\n\
                      }\n";
        let semantic = compile(&[("C.cs", source)], false).expect("compiled");
        let info = described(&semantic, "C.cs", source, false, "sender,", 0);
        assert!(info.contains("object sender"), "{info}");
        let info = described(&semantic, "C.cs", source, false, "(sender, e)", 9);
        assert!(info.contains("Args e"), "{info}");
    }

    /// What a constructor hands its base is bound for the editor too: a
    /// lambda there knows its parameter while the call is still typed.
    #[test]
    fn a_lambda_handed_to_the_base_constructor_knows_its_parameter() {
        let source = "using System;\n\
                      class Rule<T, TProperty> {\n\
                          public Rule(string name, Func<T, TProperty> property, Type type) { }\n\
                      }\n\
                      class Include<T> : Rule<T, T> {\n\
                          public Include(Type type)\n\
                              : base(null, x =>\n\
                              var adaptor = 1;\n\
                          }\n\
                      }\n";
        let semantic = compile(&[("Include.cs", source)], false).expect("compiled");
        let info = described(&semantic, "Include.cs", source, false, "x =>", 0);
        assert!(info.contains("(parameter) T x"), "{info}");
    }

    #[test]
    fn a_definition_below_the_edit_lands_where_it_is_now() {
        let compiled = "class G {\n  void R() { M(); }\n  void M() { }\n}\n";
        let semantic = compile(&[("G.cs", compiled)], false).expect("compiled");
        let typed = "class G {\n  void R() { int extra = 42; M(); }\n  void M() { }\n}\n";
        let (_, found) = semantic
            .definition(Path::new("/p/G.cs"), at(typed, "M();", 0), Some(typed))
            .expect("resolved");
        assert_eq!(
            source_spans(&found),
            vec![("G.cs".to_string(), at(typed, "M() { }", 0))]
        );
        // And a local typed a moment ago is found where it was typed.
        let local = "class G {\n  void R() { int extra = 42; M(extra); }\n  void M(int a) { }\n}\n";
        let (_, found) = semantic
            .definition(Path::new("/p/G.cs"), at(local, "extra)", 0), Some(local))
            .expect("resolved");
        assert_eq!(
            source_spans(&found),
            vec![("G.cs".to_string(), at(local, "extra", 0))]
        );
    }

    #[test]
    fn references_search_the_edited_file_as_it_is_now() {
        let a = "class A { public void Go() { } }\n";
        let b = "class B { void U(A a) { a.Go(); } }\n";
        let semantic = compile(&[("A.cs", a), ("B.cs", b)], false).expect("compiled");
        let typed = "class B { void U(A a) { a.Go(); a.Go(); } }\n";
        let (_, found) = semantic
            .references(Path::new("/p/B.cs"), at(typed, "Go", 0), Some(typed))
            .expect("resolved");
        let in_b: Vec<u32> = found
            .iter()
            .filter(|(path, _)| path.ends_with("B.cs"))
            .map(|(_, span)| span.start())
            .collect();
        assert_eq!(in_b.len(), 2, "{found:?}");
        assert_eq!(found.len(), 3, "{found:?}");
    }

    /// Where the name written as `marker` (its first occurrence, `into` bytes
    /// in) leads, as the text at the place found.
    fn lands(
        semantic: &Semantic,
        file: &str,
        text: &str,
        marker: &str,
        into: usize,
    ) -> Vec<String> {
        let (_, found) = semantic
            .definition(
                Path::new(&format!("/p/{file}")),
                at(text, marker, into),
                None,
            )
            .unwrap_or_default();
        found
            .iter()
            .map(|found| match &found.place {
                Place::Source { span, .. } => {
                    text[span.start() as usize..span.end() as usize].to_string()
                }
                Place::Metadata {
                    type_name, member, ..
                } => format!("{type_name}::{}", member.as_deref().unwrap_or("")),
            })
            .collect()
    }

    #[test]
    fn a_named_argument_is_the_parameter_it_names() {
        let text = "class C {\n  void M(int a, bool isTerminal) { }\n  void T() { M(1, isTerminal: false); }\n\
                    static readonly D Made = new D(flag: true);\n}\n\
                    class D { public D(bool flag) { } internal D(int count, bool flag) { } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        assert_eq!(
            lands(&semantic, "C.cs", text, "isTerminal:", 0),
            vec!["isTerminal"]
        );
        // In a field's initializer, which is a body of its own.
        assert_eq!(
            lands(&semantic, "C.cs", text, "flag: true", 0),
            vec!["flag"]
        );
    }

    #[test]
    fn a_named_argument_to_base_is_a_parameter_of_the_base_constructor() {
        let text = "class B { protected B(int a, bool flag) { } }\n\
                    class D : B { D() : base(1, flag: true) { } D(int x) : this() { } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        assert_eq!(
            lands(&semantic, "C.cs", text, "flag: true", 0),
            vec!["flag"]
        );
        assert_eq!(
            source_spans(
                &semantic
                    .definition(Path::new("/p/C.cs"), at(text, "flag: true", 0), None)
                    .expect("resolved")
                    .1
            ),
            vec![("C.cs".to_string(), at(text, "flag)", 0))]
        );
    }

    #[test]
    fn a_property_pattern_names_members_of_what_it_matches() {
        let text = "class Shape { public int Sides; public Shape Parent; }\n\
                    class C { bool T(Shape s) => s is { Sides: 3, Parent.Sides: 4 }; }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        assert_eq!(
            source_spans(
                &semantic
                    .definition(Path::new("/p/C.cs"), at(text, "Sides: 3", 0), None)
                    .expect("resolved")
                    .1
            ),
            vec![("C.cs".to_string(), at(text, "Sides", 0))]
        );
        assert_eq!(
            lands(&semantic, "C.cs", text, "Parent.Sides", 0),
            vec!["Parent"]
        );
        assert_eq!(
            lands(&semantic, "C.cs", text, "Parent.Sides", 7),
            vec!["Sides"]
        );
    }

    #[test]
    fn nameof_names_what_it_names() {
        let text =
            "class C { void T(int count) { var s = nameof(count); var t = nameof(C.T); } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        assert_eq!(lands(&semantic, "C.cs", text, "count);", 0), vec!["count"]);
        assert_eq!(lands(&semantic, "C.cs", text, "T);", 0), vec!["T"]);
    }

    #[test]
    fn var_of_an_array_is_its_element_type_and_where_names_a_type_parameter() {
        let text = "class Item { }\nclass C { void T() { var items = new Item[3]; }\n\
                    void G<TKey>() where TKey : class { } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        assert_eq!(lands(&semantic, "C.cs", text, "var items", 0), vec!["Item"]);
        assert_eq!(lands(&semantic, "C.cs", text, "TKey :", 0), vec!["TKey"]);
    }

    #[test]
    fn a_qualified_attribute_and_an_array_length_resolve_into_the_framework() {
        let text = "[assembly: System.Diagnostics.CodeAnalysis.SuppressMessage(\"a\", \"b\", Justification = \"c\")]\n\
                    class C { int T(int[] xs) => xs.Length; }\n";
        let Some(semantic) = compile(&[("C.cs", text)], true) else {
            return;
        };
        assert_eq!(
            lands(&semantic, "C.cs", text, "SuppressMessage(", 0),
            vec!["System.Diagnostics.CodeAnalysis.SuppressMessageAttribute::"]
        );
        assert_eq!(
            lands(&semantic, "C.cs", text, "Justification", 0),
            vec!["System.Diagnostics.CodeAnalysis.SuppressMessageAttribute::Justification"]
        );
        assert_eq!(
            lands(&semantic, "C.cs", text, "Length", 0),
            vec!["System.Array::Length"]
        );
    }
}
