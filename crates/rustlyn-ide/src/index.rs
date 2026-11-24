//! Layer 4: the project, and following a name across it.
//!
//! Layer 3 says what one file declares. This joins those answers together
//! into the thing an editor is actually asked for: given a name under the
//! cursor, where was it declared? That is `⌘B`, and it is the question that
//! separates reading code from navigating it.
//!
//! The expensive way to answer it is to bind the whole project — resolve
//! every name against every reference, the way a compiler does. That is
//! minutes and gigabytes on a real project, which is why editors that do it
//! make you wait for them. The cheap way is to match names as strings, which
//! is instant and confidently wrong whenever two types share a short name —
//! and in a Unity project with its own `Vector3` alongside the engine's, that
//! is not a corner case.
//!
//! What is done here is neither. Each file already arrived from layer 3
//! carrying its `using` directives and the namespace it was written in, so a
//! name can be resolved the way C# resolves it — against the scope it was
//! written in — without binding anything. `Vector3` in a file that says
//! `using UnityEngine;` finds the engine's; the same word in a file that does
//! not finds yours. That is most of what binding buys, for none of what it
//! costs, and where it is not enough it says so rather than guessing: a name
//! that resolves to several types comes back as several, because picking one
//! at random sends you to the wrong file silently.
//!
//! The index is built across every core, and every file goes through the
//! cache on the way in. So the second time a project is opened, building it
//! is reading it back; and when one file is saved, only that file is read
//! again.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustlyn_syntax::ParseOptions;
use rustlyn_text::SourceText;

use crate::cache::{Cache, Key, Layer, Lookup};
use crate::document::Document;
use crate::outline::{Declaration, DeclarationKind, FileOutline, Using};

/// A file as the index knows it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct IndexedFile {
    /// Relative to the project root, which is how an editor names files.
    pub path: PathBuf,
    /// The namespaces declared in it.
    pub namespaces: Vec<String>,
    pub usings: Vec<Using>,
}

impl IndexedFile {
    /// The namespaces a name written in this file is looked up in, nearest
    /// first.
    ///
    /// C# looks in the namespace the code is in, then in the ones it
    /// encloses, then in whatever `using` brought in. Getting that order
    /// right is what tells your `Vector3` from the engine's.
    fn scopes(&self) -> Vec<&str> {
        let mut scopes: Vec<&str> = Vec::new();
        for namespace in &self.namespaces {
            // `A.B.C` also searches `A.B` and `A`, innermost first.
            let mut rest = namespace.as_str();
            loop {
                if !scopes.contains(&rest) {
                    scopes.push(rest);
                }
                match rest.rfind('.') {
                    Some(dot) => rest = &rest[..dot],
                    None => break,
                }
            }
        }
        for using in &self.usings {
            if using.alias.is_none() && !scopes.contains(&using.name.as_str()) {
                scopes.push(&using.name);
            }
        }
        scopes
    }

    /// What `using Vec = UnityEngine.Vector3;` makes `Vec` mean here.
    fn alias(&self, name: &str) -> Option<&str> {
        self.usings
            .iter()
            .find(|using| using.alias.as_deref() == Some(name))
            .map(|using| using.name.as_str())
    }
}

/// One declaration, and the file it is in.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Entry {
    pub declaration: Declaration,
    /// Which file, as an index into [`ProjectIndex::files`].
    pub file: u32,
}

/// Why a lookup came back with what it did.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Confidence {
    /// One declaration, and the scope it was looked up in picked it.
    Certain,
    /// Several fit and nothing in scope told them apart. All of them are
    /// returned, nearest first, because choosing for the reader is how a
    /// navigator sends them somewhere wrong without saying so.
    Ambiguous,
}

/// What a lookup found.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Found {
    pub entries: Vec<u32>,
    pub confidence: Confidence,
}

impl Found {
    fn certain(entry: u32) -> Self {
        Self {
            entries: vec![entry],
            confidence: Confidence::Certain,
        }
    }

    fn of(mut entries: Vec<u32>) -> Option<Self> {
        entries.dedup();
        match entries.len() {
            0 => None,
            1 => Some(Self::certain(entries[0])),
            _ => Some(Self {
                entries,
                confidence: Confidence::Ambiguous,
            }),
        }
    }

    /// The one answer, when there is only one.
    #[must_use]
    pub fn only(&self) -> Option<u32> {
        match self.confidence {
            Confidence::Certain => self.entries.first().copied(),
            Confidence::Ambiguous => None,
        }
    }
}

/// How the index was built: what it read, and what it did not have to.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct BuildReport {
    pub files: usize,
    /// Files whose outline came back from the cache untouched.
    pub reused: usize,
    /// Files that had to be parsed.
    pub parsed: usize,
    /// Files that could not be read at all.
    pub unreadable: usize,
}

/// Everything declared in a project, and the tables to find it by.
///
/// Immutable once built. A save produces a new index rather than changing
/// this one, so background work holding an old one keeps answering from it
/// instead of blocking on a lock in the middle of a repaint.
#[derive(Debug, Default)]
pub struct ProjectIndex {
    root: PathBuf,
    files: Vec<IndexedFile>,
    entries: Vec<Entry>,

    /// Every declaration by its plain name.
    by_name: HashMap<String, Vec<u32>>,
    /// Types by their plain name — several when a type is `partial` or when
    /// two namespaces use the same word.
    types_by_name: HashMap<String, Vec<u32>>,
    /// Members by the plain name of the type that declares them.
    members_by_owner: HashMap<String, Vec<u32>>,
    /// The reverse of `: Base, IFoo` — who derives from a name.
    derived_by_base: HashMap<String, Vec<u32>>,
    /// Extension methods by the plain name of the type they extend.
    extensions_by_receiver: HashMap<String, Vec<u32>>,

    report: BuildReport,
}

impl ProjectIndex {
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    #[must_use]
    pub fn files(&self) -> &[IndexedFile] {
        &self.files
    }

    #[must_use]
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    #[must_use]
    pub fn entry(&self, id: u32) -> Option<&Entry> {
        self.entries.get(id as usize)
    }

    #[must_use]
    pub fn file_of(&self, id: u32) -> Option<&IndexedFile> {
        self.entry(id)
            .and_then(|entry| self.files.get(entry.file as usize))
    }

    #[must_use]
    pub const fn report(&self) -> BuildReport {
        self.report
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Builds the index for a set of files.
    ///
    /// Every file goes through `cache`, so a project opened a second time is
    /// read back rather than reparsed, and a project with one file saved
    /// reparses one file.
    #[must_use]
    pub fn build(
        root: impl Into<PathBuf>,
        paths: &[PathBuf],
        cache: &Cache,
        options: &ParseOptions,
    ) -> Self {
        let root = root.into();
        let salt = Key::salt_of(
            &options
                .preprocessor_symbols
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        );

        let reused = AtomicUsize::new(0);
        let parsed = AtomicUsize::new(0);
        let unreadable = AtomicUsize::new(0);

        // One chunk per core. The work is per-file and independent, so the
        // only shared thing is the cache, which takes its own lock.
        let threads = std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
        let chunk = paths.len().div_ceil(threads.max(1)).max(1);
        let mut outlines: Vec<Option<Arc<FileOutline>>> = Vec::new();

        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for slice in paths.chunks(chunk) {
                let reused = &reused;
                let parsed = &parsed;
                let unreadable = &unreadable;
                // Parsing recurses as deep as the expressions it reads: the
                // same stack as the semantic workers, not the default 2 MB.
                let worker = std::thread::Builder::new()
                    .name("rustlyn-index".into())
                    .stack_size(64 << 20);
                handles.push(
                    worker
                        .spawn_scoped(scope, move || {
                            slice
                                .iter()
                                .map(|path| match outline_of(path, cache, options, salt) {
                                    Outcome::Reused(outline) => {
                                        reused.fetch_add(1, Ordering::Relaxed);
                                        Some(outline)
                                    }
                                    Outcome::Parsed(outline) => {
                                        parsed.fetch_add(1, Ordering::Relaxed);
                                        Some(outline)
                                    }
                                    Outcome::Unreadable => {
                                        unreadable.fetch_add(1, Ordering::Relaxed);
                                        None
                                    }
                                })
                                .collect::<Vec<_>>()
                        })
                        .expect("an index thread"),
                );
            }
            for handle in handles {
                outlines.extend(handle.join().unwrap_or_default());
            }
        });

        let mut index = Self {
            root,
            report: BuildReport {
                files: paths.len(),
                reused: reused.load(Ordering::Relaxed),
                parsed: parsed.load(Ordering::Relaxed),
                unreadable: unreadable.load(Ordering::Relaxed),
            },
            ..Self::default()
        };

        for (path, outline) in paths.iter().zip(outlines) {
            let Some(outline) = outline else { continue };
            index.add(path, &outline);
        }
        index.build_tables();
        index
    }

    /// Builds an index straight from outlines already in hand — what tests
    /// and an editor with unsaved buffers use.
    #[must_use]
    pub fn from_outlines(
        root: impl Into<PathBuf>,
        files: impl IntoIterator<Item = (PathBuf, FileOutline)>,
    ) -> Self {
        let mut index = Self {
            root: root.into(),
            ..Self::default()
        };
        for (path, outline) in files {
            index.add(&path, &outline);
            index.report.files += 1;
            index.report.parsed += 1;
        }
        index.build_tables();
        index
    }

    fn add(&mut self, path: &Path, outline: &FileOutline) {
        let relative = path.strip_prefix(&self.root).unwrap_or(path).to_path_buf();
        let file = self.files.len() as u32;
        self.files.push(IndexedFile {
            path: relative,
            namespaces: outline.namespaces.clone(),
            usings: outline.usings.clone(),
        });
        for declaration in &outline.declarations {
            if declaration.kind == DeclarationKind::Namespace {
                continue; // a namespace is a scope, not something to jump to
            }
            self.entries.push(Entry {
                declaration: declaration.clone(),
                file,
            });
        }
    }

    fn build_tables(&mut self) {
        for (id, entry) in self.entries.iter().enumerate() {
            let id = id as u32;
            let declaration = &entry.declaration;

            self.by_name
                .entry(declaration.name.clone())
                .or_default()
                .push(id);

            if declaration.kind.is_type() {
                self.types_by_name
                    .entry(declaration.name.clone())
                    .or_default()
                    .push(id);
                for base in &declaration.bases {
                    self.derived_by_base
                        .entry(plain_name(base).to_owned())
                        .or_default()
                        .push(id);
                }
            } else if let Some(container) = &declaration.container {
                self.members_by_owner
                    .entry(plain_name(container).to_owned())
                    .or_default()
                    .push(id);
            }

            if declaration.is_extension_method()
                && let Some(receiver) = declaration.parameters.first()
            {
                self.extensions_by_receiver
                    .entry(plain_name(&receiver.type_text).to_owned())
                    .or_default()
                    .push(id);
            }
        }
    }

    // MARK: - following a name

    /// The type a name means, read from the file it was written in.
    ///
    /// The whole point of taking the file: `Vector3` means one thing in a
    /// file that says `using UnityEngine;` and another in one that does not.
    #[must_use]
    pub fn resolve_type(&self, name: &str, from: u32) -> Option<Found> {
        let file = self.files.get(from as usize)?;

        // An alias is not a guess: the file said what the name means.
        let name = file.alias(name).unwrap_or(name);

        // A qualified name says which one it wants.
        if let Some(dot) = name.rfind('.') {
            let (namespace, plain) = name.split_at(dot);
            let plain = plain_name(&plain[1..]);
            let candidates: Vec<u32> = self
                .types_by_name
                .get(plain)
                .map(Vec::as_slice)
                .unwrap_or_default()
                .iter()
                .copied()
                .filter(|&id| {
                    self.entries[id as usize]
                        .declaration
                        .container
                        .as_deref()
                        .is_some_and(|container| {
                            container == namespace || container.ends_with(namespace)
                        })
                })
                .collect();
            return Found::of(candidates);
        }

        let plain = plain_name(name);
        let candidates = self.types_by_name.get(plain)?;
        let scopes = file.scopes();
        if let [only] = candidates.as_slice() {
            // The only type by that name in the project is the answer only
            // when the file can see it. One nested in another type is not
            // seen by its plain name from outside — `Vector3` in a file that
            // uses UnityEngine is the engine's, not a test fixture's — so it
            // is no answer, and whoever asks next looks elsewhere. One in a
            // namespace the file does not bring in is a guess, and says so.
            let container = self.entries[*only as usize]
                .declaration
                .container
                .as_deref()
                .unwrap_or("");
            if container.is_empty() || scopes.contains(&container) {
                return Some(Found::certain(*only));
            }
            if self.is_type(container) {
                return None;
            }
            return Some(Found {
                entries: vec![*only],
                confidence: Confidence::Ambiguous,
            });
        }

        // Several types share the name. The one in scope wins, and "in scope"
        // is ordered: the namespace the file is in beats one it merely brought
        // in with a `using`.
        let mut ranked: Vec<(usize, u32)> = candidates
            .iter()
            .filter_map(|&id| {
                let container = self.entries[id as usize]
                    .declaration
                    .container
                    .as_deref()
                    .unwrap_or("");
                let rank = scopes.iter().position(|scope| *scope == container)?;
                Some((rank, id))
            })
            .collect();

        if ranked.is_empty() {
            // Nothing in scope names any of them. Rather than pick, say so.
            return Found::of(candidates.clone());
        }
        ranked.sort_by_key(|&(rank, id)| (rank, id));

        // Everything at the best rank. Two partial halves of one type rank
        // together, and both are real places to go.
        let best = ranked[0].0;
        let entries: Vec<u32> = ranked
            .iter()
            .filter(|&&(rank, _)| rank == best)
            .map(|&(_, id)| id)
            .collect();

        // Partial declarations of one type are one answer, not an ambiguity.
        if entries.len() > 1
            && entries
                .iter()
                .all(|&id| self.entries[id as usize].declaration.is_partial)
        {
            return Some(Found::certain(entries[0]));
        }
        Found::of(entries)
    }

    /// Whether `qualified` names a type of the project rather than a
    /// namespace.
    fn is_type(&self, qualified: &str) -> bool {
        let plain = qualified.rsplit('.').next().unwrap_or(qualified);
        self.types_by_name.get(plain).is_some_and(|ids| {
            ids.iter()
                .any(|&id| self.entries[id as usize].declaration.qualified_name() == qualified)
        })
    }

    /// A member of a type, looked up the way C# looks it up: in the type, and
    /// then in what it derives from.
    #[must_use]
    pub fn member(&self, type_entry: u32, name: &str) -> Option<Found> {
        let mut seen = Vec::new();
        self.member_through(type_entry, name, &mut seen)
    }

    fn member_through(&self, type_entry: u32, name: &str, seen: &mut Vec<u32>) -> Option<Found> {
        // A cycle in `: Base` is not valid C#, but an index built from files
        // being edited will meet one, and it must not spin.
        if seen.contains(&type_entry) {
            return None;
        }
        seen.push(type_entry);

        let entry = self.entries.get(type_entry as usize)?;
        let type_name = &entry.declaration.name;

        let here: Vec<u32> = self
            .members_by_owner
            .get(plain_name(type_name))
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .copied()
            .filter(|&id| self.entries[id as usize].declaration.name == name)
            // A member of a different type that happens to share a short
            // container name is not this type's member.
            .filter(|&id| self.same_type(id, type_entry))
            .collect();

        if !here.is_empty() {
            return Found::of(here);
        }

        // Not here: ask what this derives from. Interfaces as well as the
        // base class, because a member reached through an interface is still
        // the member you meant.
        for base in entry.declaration.bases.clone() {
            let Some(found) = self.resolve_type(&base, entry.file) else {
                continue;
            };
            for base_id in found.entries {
                if let Some(found) = self.member_through(base_id, name, seen) {
                    return Some(found);
                }
            }
        }
        None
    }

    /// Whether a member belongs to this exact type rather than to another one
    /// with the same short name.
    fn same_type(&self, member: u32, type_entry: u32) -> bool {
        let Some(member) = self.entries.get(member as usize) else {
            return false;
        };
        let Some(declared_in) = self.entries.get(type_entry as usize) else {
            return false;
        };
        member.declaration.container.as_deref() == Some(&declared_in.declaration.qualified_name())
            // A member of a partial type declared in another file has the
            // same qualified container, so that comparison already covers it;
            // this is the case where neither is qualified at all.
            || (member.declaration.container.as_deref() == Some(declared_in.declaration.name.as_str())
                && declared_in.declaration.container.is_none())
    }

    /// The extension methods that could be called on a type, by name.
    ///
    /// C# looks for an extension only when the type has no member of that
    /// name, which is the order [`Self::member`] and this should be tried in.
    #[must_use]
    pub fn extension(&self, type_entry: u32, name: &str) -> Option<Found> {
        let entry = self.entries.get(type_entry as usize)?;
        let candidates: Vec<u32> = self
            .extensions_by_receiver
            .get(plain_name(&entry.declaration.name))
            .map(Vec::as_slice)
            .unwrap_or_default()
            .iter()
            .copied()
            .filter(|&id| self.entries[id as usize].declaration.name == name)
            .filter(|&id| {
                // The receiver has to be the same type, not another one
                // spelled the same. Resolve it in the extension's own file.
                let extension = &self.entries[id as usize];
                let Some(receiver) = extension.declaration.parameters.first() else {
                    return false;
                };
                self.resolve_type(&receiver.type_text, extension.file)
                    .is_some_and(|found| found.entries.contains(&type_entry))
            })
            .collect();
        Found::of(candidates)
    }

    /// Everything that derives from a type, directly or through anything in
    /// between: what `⌥⌘B` shows.
    ///
    /// The walk goes level by level, and at each level it checks that the
    /// base really is the type at *that* level rather than one spelled the
    /// same somewhere else. Checking against the type the walk started from
    /// would stop it after one step, since `Pawn : Actor` does not name the
    /// interface `Actor` implements.
    #[must_use]
    pub fn implementations(&self, type_entry: u32) -> Vec<u32> {
        if self.entries.get(type_entry as usize).is_none() {
            return Vec::new();
        }
        let mut found = Vec::new();
        let mut seen = vec![type_entry];
        let mut queue = vec![type_entry];

        while let Some(current) = queue.pop() {
            let name = self.entries[current as usize].declaration.name.clone();
            for &candidate in self
                .derived_by_base
                .get(plain_name(&name))
                .map(Vec::as_slice)
                .unwrap_or_default()
            {
                if seen.contains(&candidate) {
                    continue;
                }
                if !self.derives_from(candidate, current) {
                    continue;
                }
                seen.push(candidate);
                found.push(candidate);
                queue.push(candidate);
            }
        }
        found
    }

    /// Whether `derived` names `base` among its bases — the real one, not
    /// another type that happens to be spelled the same.
    fn derives_from(&self, derived: u32, base: u32) -> bool {
        let Some(derived) = self.entries.get(derived as usize) else {
            return false;
        };
        let Some(base_entry) = self.entries.get(base as usize) else {
            return false;
        };
        let wanted = base_entry.declaration.qualified_name();
        derived.declaration.bases.iter().any(|written| {
            if plain_name(written) != plain_name(&base_entry.declaration.name) {
                return false;
            }
            match self.resolve_type(written, derived.file) {
                // Comparing qualified names rather than ids, so that the two
                // halves of a partial type count as the same type.
                Some(found) => found
                    .entries
                    .iter()
                    .any(|&id| self.entries[id as usize].declaration.qualified_name() == wanted),
                // The name is in the index under this short name but did not
                // resolve from here — no `using` reaches it. It is not this.
                None => false,
            }
        })
    }

    /// The overrides of a member: the same name, on everything that derives
    /// from the type that declares it.
    #[must_use]
    pub fn overrides(&self, member: u32) -> Vec<u32> {
        let Some(entry) = self.entries.get(member as usize) else {
            return Vec::new();
        };
        let Some(container) = entry.declaration.container.as_deref() else {
            return Vec::new();
        };
        // Resolve the declaring type from the member's own file, so a
        // container name shared with another namespace does not send the
        // walk down the wrong hierarchy.
        let Some(declaring) = self.resolve_type(container, entry.file) else {
            return Vec::new();
        };
        let name = &entry.declaration.name;

        let mut found = Vec::new();
        for root in declaring.entries {
            for derived in self.implementations(root) {
                let derived_name = self.entries[derived as usize].declaration.name.clone();
                for &id in self
                    .members_by_owner
                    .get(plain_name(&derived_name))
                    .map(Vec::as_slice)
                    .unwrap_or_default()
                {
                    if &self.entries[id as usize].declaration.name == name
                        && self.same_type(id, derived)
                        && !found.contains(&id)
                    {
                        found.push(id);
                    }
                }
            }
        }
        found
    }

    /// Every declaration with a given name, for a plain search.
    #[must_use]
    pub fn by_name(&self, name: &str) -> &[u32] {
        self.by_name
            .get(name)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// Every type declared in the project, for a type search.
    pub fn types(&self) -> impl Iterator<Item = (u32, &Entry)> {
        self.entries
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.declaration.kind.is_type())
            .map(|(id, entry)| (id as u32, entry))
    }

    /// The names of every declaration, laid end to end, with a span each.
    ///
    /// The shape a fuzzy search wants: matching a query against a hundred
    /// thousand names should not allocate a hundred thousand strings, and the
    /// editor above this already has a scorer that reads exactly this. Names
    /// are lowercased here so the scorer does not have to do it per keystroke.
    #[must_use]
    pub fn search_buffer(&self) -> SearchBuffer {
        let mut bytes = Vec::new();
        let mut spans = Vec::with_capacity(self.entries.len());
        for entry in &self.entries {
            let start = bytes.len() as u32;
            if let Some(container) = &entry.declaration.container {
                bytes.extend(container.to_lowercase().bytes());
                bytes.push(b'.');
            }
            let name_start = bytes.len() as u32;
            bytes.extend(entry.declaration.name.to_lowercase().bytes());
            spans.push(Span {
                start,
                length: bytes.len() as u32 - start,
                name_start,
            });
        }
        SearchBuffer { bytes, spans }
    }
}

/// Names laid end to end for a search to run over without allocating.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct SearchBuffer {
    pub bytes: Vec<u8>,
    pub spans: Vec<Span>,
}

/// Where one name sits in a [`SearchBuffer`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    pub start: u32,
    pub length: u32,
    /// Where the name begins inside `container.name`, so a match in the name
    /// can be scored above a match in the namespace.
    pub name_start: u32,
}

enum Outcome {
    Reused(Arc<FileOutline>),
    Parsed(Arc<FileOutline>),
    Unreadable,
}

/// One file's outline, from the cache when it can be.
fn outline_of(path: &Path, cache: &Cache, options: &ParseOptions, salt: u64) -> Outcome {
    let key = Key::new(Layer::FileSymbols, path).salted(salt);
    match cache.lookup::<FileOutline>(&key, path) {
        Ok(Lookup::Hit(outline)) => Outcome::Reused(outline),
        Ok(Lookup::Miss(bytes, print)) => {
            let document = Document::from_bytes(path, &bytes, print, 0);
            let outline = FileOutline::of(document.source(), options);
            Outcome::Parsed(cache.store(&key, print, outline))
        }
        Err(_) => Outcome::Unreadable,
    }
}

/// A type name with its namespace and type arguments taken off.
///
/// `UnityEngine.Vector3` and `List<Stash<T>>` are keyed by `Vector3` and
/// `List`, because that is the word written at the use site.
#[must_use]
pub fn plain_name(name: &str) -> &str {
    let name = match name.find('<') {
        Some(angle) => &name[..angle],
        None => name,
    };
    // `int[]`, `Foo?`, `Bar*` are all keyed by the name inside.
    let name = name.trim_end_matches(['[', ']', '?', '*', ' ']);
    match name.rfind('.') {
        Some(dot) => &name[dot + 1..],
        None => name,
    }
}

/// An outline for a snippet, for building test indexes.
#[must_use]
pub fn outline_of_text(text: &str) -> FileOutline {
    FileOutline::of(&SourceText::new("Test.cs", text), &ParseOptions::default())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An index over named snippets.
    fn index(files: &[(&str, &str)]) -> ProjectIndex {
        ProjectIndex::from_outlines(
            "/project",
            files
                .iter()
                .map(|(name, text)| (PathBuf::from(name), outline_of_text(text))),
        )
    }

    fn file_id(index: &ProjectIndex, name: &str) -> u32 {
        index
            .files
            .iter()
            .position(|file| file.path == Path::new(name))
            .unwrap_or_else(|| panic!("no file {name}")) as u32
    }

    fn name_of(index: &ProjectIndex, id: u32) -> String {
        index.entries[id as usize].declaration.qualified_name()
    }

    fn in_file(index: &ProjectIndex, id: u32) -> String {
        index.files[index.entries[id as usize].file as usize]
            .path
            .display()
            .to_string()
    }

    #[test]
    fn a_plain_name_drops_its_namespace_and_arguments() {
        assert_eq!(plain_name("Vector3"), "Vector3");
        assert_eq!(plain_name("UnityEngine.Vector3"), "Vector3");
        assert_eq!(plain_name("List<int>"), "List");
        assert_eq!(plain_name("System.Collections.Generic.List<T>"), "List");
        assert_eq!(plain_name("int[]"), "int");
        assert_eq!(plain_name("Foo?"), "Foo");
    }

    #[test]
    fn a_name_declared_once_resolves_to_it() {
        let index = index(&[
            ("Pawn.cs", "namespace Game; class Pawn { }"),
            ("Use.cs", "namespace Game; class Use { Pawn p; }"),
        ]);
        let found = index
            .resolve_type("Pawn", file_id(&index, "Use.cs"))
            .expect("Pawn should resolve");
        assert_eq!(found.confidence, Confidence::Certain);
        assert_eq!(name_of(&index, found.entries[0]), "Game.Pawn");
    }

    #[test]
    fn the_only_type_by_a_name_is_no_answer_where_it_cannot_be_seen() {
        // Unity's collections package has a test fixture that nests its own
        // `Vector3`; a game's `Vector3` is the engine's, not that one.
        let index = index(&[
            (
                "Fixture.cs",
                "namespace Tests; class ValidateTypes { struct Vector3 { } }",
            ),
            ("Elsewhere.cs", "namespace Far.Away; class Widget { }"),
            (
                "Game.cs",
                "using UnityEngine;\nnamespace Game;\nclass A { Vector3 v; Widget w; }",
            ),
        ]);
        let game = file_id(&index, "Game.cs");
        assert!(index.resolve_type("Vector3", game).is_none());
        // Not brought in, but not hidden either: a guess, and it says so.
        let widget = index.resolve_type("Widget", game).expect("a guess");
        assert_ne!(widget.confidence, Confidence::Certain);
    }

    #[test]
    fn the_using_in_the_file_decides_between_two_types_of_the_same_name() {
        // The case that makes matching by name alone wrong: a project with
        // its own `Vector3` next to the engine's.
        let index = index(&[
            (
                "Engine.cs",
                "namespace UnityEngine; public class Vector3 { }",
            ),
            ("Mine.cs", "namespace Game.Math; public class Vector3 { }"),
            (
                "UsesEngine.cs",
                "using UnityEngine;\nnamespace Game;\nclass A { Vector3 v; }",
            ),
            (
                "UsesMine.cs",
                "using Game.Math;\nnamespace Game;\nclass B { Vector3 v; }",
            ),
        ]);

        let engine = index
            .resolve_type("Vector3", file_id(&index, "UsesEngine.cs"))
            .expect("resolves");
        assert_eq!(engine.confidence, Confidence::Certain);
        assert_eq!(in_file(&index, engine.entries[0]), "Engine.cs");

        let mine = index
            .resolve_type("Vector3", file_id(&index, "UsesMine.cs"))
            .expect("resolves");
        assert_eq!(mine.confidence, Confidence::Certain);
        assert_eq!(in_file(&index, mine.entries[0]), "Mine.cs");
    }

    #[test]
    fn the_namespace_the_file_is_in_beats_one_it_merely_used() {
        let index = index(&[
            ("Theirs.cs", "namespace Other; class Thing { }"),
            ("Mine.cs", "namespace Game; class Thing { }"),
            (
                "Here.cs",
                "using Other;\nnamespace Game;\nclass Use { Thing t; }",
            ),
        ]);
        let found = index
            .resolve_type("Thing", file_id(&index, "Here.cs"))
            .expect("resolves");
        assert_eq!(found.confidence, Confidence::Certain);
        assert_eq!(
            in_file(&index, found.entries[0]),
            "Mine.cs",
            "the file's own namespace is nearer than a `using`",
        );
    }

    #[test]
    fn an_alias_says_what_a_name_means() {
        let index = index(&[
            ("Engine.cs", "namespace UnityEngine; class Vector3 { }"),
            ("Mine.cs", "namespace Game; class Vector3 { }"),
            (
                "Here.cs",
                "using Vec = UnityEngine.Vector3;\nnamespace Game;\nclass Use { Vec v; }",
            ),
        ]);
        let found = index
            .resolve_type("Vec", file_id(&index, "Here.cs"))
            .expect("the alias resolves");
        assert_eq!(found.confidence, Confidence::Certain);
        assert_eq!(in_file(&index, found.entries[0]), "Engine.cs");
    }

    #[test]
    fn a_qualified_name_picks_its_own() {
        let index = index(&[
            ("Engine.cs", "namespace UnityEngine; class Vector3 { }"),
            ("Mine.cs", "namespace Game; class Vector3 { }"),
            ("Here.cs", "namespace Game; class Use { }"),
        ]);
        let found = index
            .resolve_type("UnityEngine.Vector3", file_id(&index, "Here.cs"))
            .expect("resolves");
        assert_eq!(found.confidence, Confidence::Certain);
        assert_eq!(in_file(&index, found.entries[0]), "Engine.cs");
    }

    #[test]
    fn a_name_nothing_in_scope_explains_comes_back_as_all_of_them() {
        // Two candidates and no reason to prefer either. Saying "here are
        // both" is the honest answer; picking one sends the reader to the
        // wrong file without telling them.
        let index = index(&[
            ("A.cs", "namespace Alpha; class Thing { }"),
            ("B.cs", "namespace Beta; class Thing { }"),
            ("Here.cs", "namespace Gamma; class Use { }"),
        ]);
        let found = index
            .resolve_type("Thing", file_id(&index, "Here.cs"))
            .expect("resolves to something");
        assert_eq!(found.confidence, Confidence::Ambiguous);
        assert_eq!(found.entries.len(), 2);
        assert!(found.only().is_none());
    }

    #[test]
    fn the_two_halves_of_a_partial_type_are_one_answer() {
        let index = index(&[
            (
                "A.cs",
                "namespace Game; partial class Pawn { void One() {} }",
            ),
            (
                "B.cs",
                "namespace Game; partial class Pawn { void Two() {} }",
            ),
            ("Here.cs", "namespace Game; class Use { }"),
        ]);
        let found = index
            .resolve_type("Pawn", file_id(&index, "Here.cs"))
            .expect("resolves");
        assert_eq!(
            found.confidence,
            Confidence::Certain,
            "a partial type split over files is one type",
        );
    }

    #[test]
    fn a_nested_namespace_is_in_scope_from_inside_it() {
        let index = index(&[
            ("Deep.cs", "namespace Game.Systems.Combat; class Sword { }"),
            (
                "Here.cs",
                "namespace Game.Systems.Combat.Effects; class Use { }",
            ),
        ]);
        // `Game.Systems.Combat.Effects` searches its enclosing namespaces too.
        let found = index
            .resolve_type("Sword", file_id(&index, "Here.cs"))
            .expect("resolves");
        assert_eq!(found.confidence, Confidence::Certain);
    }

    // MARK: - members

    #[test]
    fn a_member_is_found_on_its_own_type() {
        let index = index(&[("A.cs", "namespace Game; class Pawn { public int Health; }")]);
        let pawn = index
            .resolve_type("Pawn", file_id(&index, "A.cs"))
            .expect("Pawn")
            .entries[0];
        let health = index.member(pawn, "Health").expect("Health");
        assert_eq!(name_of(&index, health.entries[0]), "Game.Pawn.Health");
    }

    #[test]
    fn a_member_is_found_through_a_base_class() {
        let index = index(&[
            (
                "Base.cs",
                "namespace Game; class Actor { public int Health; }",
            ),
            ("Derived.cs", "namespace Game; class Pawn : Actor { }"),
        ]);
        let pawn = index
            .resolve_type("Pawn", file_id(&index, "Derived.cs"))
            .expect("Pawn")
            .entries[0];
        let health = index.member(pawn, "Health").expect("through the base");
        assert_eq!(name_of(&index, health.entries[0]), "Game.Actor.Health");
    }

    #[test]
    fn a_member_is_found_through_a_chain_of_bases() {
        let index = index(&[
            ("A.cs", "namespace Game; class A { public int Deep; }"),
            ("B.cs", "namespace Game; class B : A { }"),
            ("C.cs", "namespace Game; class C : B { }"),
        ]);
        let c = index
            .resolve_type("C", file_id(&index, "C.cs"))
            .expect("C")
            .entries[0];
        assert!(index.member(c, "Deep").is_some());
    }

    #[test]
    fn a_member_of_a_same_named_type_elsewhere_is_not_this_types_member() {
        let index = index(&[
            (
                "Mine.cs",
                "namespace Game; class Config { public int Mine; }",
            ),
            (
                "Theirs.cs",
                "namespace Other; class Config { public int Theirs; }",
            ),
        ]);
        let mine = index
            .resolve_type("Game.Config", file_id(&index, "Mine.cs"))
            .expect("Game.Config")
            .entries[0];
        assert!(index.member(mine, "Mine").is_some());
        assert!(
            index.member(mine, "Theirs").is_none(),
            "a member of the other Config must not leak in",
        );
    }

    #[test]
    fn a_cycle_in_the_bases_does_not_spin() {
        // Not valid C#, but a file half-typed will produce it.
        let index = index(&[
            ("A.cs", "namespace Game; class A : B { }"),
            ("B.cs", "namespace Game; class B : A { }"),
        ]);
        let a = index
            .resolve_type("A", file_id(&index, "A.cs"))
            .expect("A")
            .entries[0];
        assert!(index.member(a, "Nothing").is_none());
    }

    // MARK: - extension methods

    #[test]
    fn an_extension_method_is_callable_on_the_type_it_extends() {
        let index = index(&[
            ("Pawn.cs", "namespace Game; class Pawn { }"),
            (
                "Ext.cs",
                "namespace Game; static class Extras { public static void Say(this Pawn p) { } }",
            ),
        ]);
        let pawn = index
            .resolve_type("Pawn", file_id(&index, "Pawn.cs"))
            .expect("Pawn")
            .entries[0];
        let say = index.extension(pawn, "Say").expect("Say");
        assert_eq!(name_of(&index, say.entries[0]), "Game.Extras.Say");
    }

    #[test]
    fn an_extension_of_a_same_named_type_from_elsewhere_does_not_apply() {
        let index = index(&[
            ("Mine.cs", "namespace Game; class Pawn { }"),
            ("Theirs.cs", "namespace Other; class Pawn { }"),
            (
                "Ext.cs",
                "using Other;\nnamespace Ext;\nstatic class E { public static void Say(this Pawn p) { } }",
            ),
        ]);
        let mine = index
            .resolve_type("Game.Pawn", file_id(&index, "Mine.cs"))
            .expect("Game.Pawn")
            .entries[0];
        assert!(
            index.extension(mine, "Say").is_none(),
            "the extension is for Other.Pawn",
        );
    }

    // MARK: - going down the hierarchy

    #[test]
    fn implementations_reach_through_the_middle_of_a_hierarchy() {
        let index = index(&[
            ("I.cs", "namespace Game; interface IDamageable { }"),
            ("A.cs", "namespace Game; class Actor : IDamageable { }"),
            ("P.cs", "namespace Game; class Pawn : Actor { }"),
            ("E.cs", "namespace Game; class Enemy : Pawn { }"),
            ("X.cs", "namespace Game; class Unrelated { }"),
        ]);
        let interface = index
            .resolve_type("IDamageable", file_id(&index, "I.cs"))
            .expect("the interface")
            .entries[0];
        let mut names: Vec<String> = index
            .implementations(interface)
            .into_iter()
            .map(|id| index.entries[id as usize].declaration.name.clone())
            .collect();
        names.sort();
        assert_eq!(names, ["Actor", "Enemy", "Pawn"]);
    }

    #[test]
    fn overrides_of_a_method_are_found_down_the_hierarchy() {
        let index = index(&[
            (
                "A.cs",
                "namespace Game; abstract class Actor { public virtual void Tick() {} }",
            ),
            (
                "P.cs",
                "namespace Game; class Pawn : Actor { public override void Tick() {} }",
            ),
            (
                "E.cs",
                "namespace Game; class Enemy : Pawn { public override void Tick() {} }",
            ),
        ]);
        let actor = index
            .resolve_type("Actor", file_id(&index, "A.cs"))
            .expect("Actor")
            .entries[0];
        let tick = index.member(actor, "Tick").expect("Tick").entries[0];
        let overrides = index.overrides(tick);
        assert_eq!(overrides.len(), 2, "Pawn and Enemy override it");
    }

    // MARK: - searching

    #[test]
    fn the_search_buffer_holds_every_name_lowercased_and_qualified() {
        let index = index(&[("A.cs", "namespace Game; class Pawn { public int Health; }")]);
        let buffer = index.search_buffer();
        let text = String::from_utf8(buffer.bytes.clone()).expect("utf8");
        assert!(text.contains("game.pawn"), "{text}");
        assert!(text.contains("game.pawn.health"), "{text}");
        assert_eq!(buffer.spans.len(), index.len());

        // The name's own start is marked, so a scorer can weigh a hit in the
        // name above one in the namespace.
        let health = index.by_name("Health")[0] as usize;
        let span = buffer.spans[health];
        let name = &text[span.name_start as usize..(span.start + span.length) as usize];
        assert_eq!(name, "health");
    }

    #[test]
    fn types_are_listable_on_their_own() {
        let index = index(&[(
            "A.cs",
            "namespace Game; class Pawn { void M() {} } struct S { } enum E { X }",
        )]);
        let mut names: Vec<&str> = index
            .types()
            .map(|(_, entry)| entry.declaration.name.as_str())
            .collect();
        names.sort_unstable();
        assert_eq!(names, ["E", "Pawn", "S"], "members are not types");
    }

    #[test]
    fn an_empty_project_answers_nothing_rather_than_panicking() {
        let index = ProjectIndex::default();
        assert!(index.is_empty());
        assert!(index.resolve_type("Anything", 0).is_none());
        assert!(index.member(0, "Anything").is_none());
        assert!(index.implementations(0).is_empty());
        assert!(index.search_buffer().spans.is_empty());
    }

    // MARK: - building it from disk, which is where the cache matters

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "rustlyn-index-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).expect("a temporary directory");
            Self(path)
        }
        fn write(&self, name: &str, text: &str) -> PathBuf {
            let path = self.0.join(name);
            std::fs::write(&path, text).expect("writing");
            path
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn building_twice_reads_the_second_time_instead_of_parsing() {
        let dir = TempDir::new("reuse");
        let paths: Vec<PathBuf> = (0..20)
            .map(|n| {
                dir.write(
                    &format!("File{n}.cs"),
                    &format!("namespace Game; class Type{n} {{ public int Field{n}; }}"),
                )
            })
            .collect();
        let cache = Cache::in_memory(1 << 22);
        let options = ParseOptions::default();

        let first = ProjectIndex::build(&dir.0, &paths, &cache, &options);
        assert_eq!(first.report().parsed, 20);
        assert_eq!(first.report().reused, 0);
        assert_eq!(first.len(), 40, "twenty types and twenty fields");

        let second = ProjectIndex::build(&dir.0, &paths, &cache, &options);
        assert_eq!(second.report().parsed, 0, "nothing should be parsed again");
        assert_eq!(second.report().reused, 20);
        assert_eq!(second.len(), first.len());
    }

    #[test]
    fn saving_one_file_reparses_one_file() {
        let dir = TempDir::new("onefile");
        let paths: Vec<PathBuf> = (0..10)
            .map(|n| dir.write(&format!("F{n}.cs"), &format!("class T{n} {{ }}")))
            .collect();
        let cache = Cache::in_memory(1 << 22);
        let options = ParseOptions::default();

        let _first = ProjectIndex::build(&dir.0, &paths, &cache, &options);
        std::thread::sleep(std::time::Duration::from_millis(10));
        dir.write("F3.cs", "class T3 { public int Added; }");

        let after = ProjectIndex::build(&dir.0, &paths, &cache, &options);
        assert_eq!(after.report().parsed, 1, "only the file that changed");
        assert_eq!(after.report().reused, 9);
        assert_eq!(after.by_name("Added").len(), 1, "and the change is in");
    }

    #[test]
    fn a_file_that_cannot_be_read_is_counted_rather_than_fatal() {
        let dir = TempDir::new("missing");
        let good = dir.write("Good.cs", "class Good { }");
        let missing = dir.0.join("Gone.cs");
        let cache = Cache::in_memory(1 << 20);

        let index = ProjectIndex::build(&dir.0, &[good, missing], &cache, &ParseOptions::default());
        assert_eq!(index.report().unreadable, 1);
        assert_eq!(index.by_name("Good").len(), 1, "the rest still indexed");
    }

    #[test]
    fn paths_in_the_index_are_relative_to_the_project_root() {
        let dir = TempDir::new("relative");
        let path = dir.write("Deep.cs", "class D { }");
        let cache = Cache::in_memory(1 << 20);
        let index = ProjectIndex::build(&dir.0, &[path], &cache, &ParseOptions::default());
        assert_eq!(index.files()[0].path, Path::new("Deep.cs"));
    }
}
