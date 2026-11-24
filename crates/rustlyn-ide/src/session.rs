//! One editor's worth of state, and the layers arranged behind it.
//!
//! Everything below this is a pure function of some bytes. This is where the
//! bytes live: which files are open, which version of each one, the
//! checkpoints the colouring has laid down, and the index of the project
//! around them. It is the only part of the crate that is mutable, and the
//! only part an editor needs to hold on to.
//!
//! Two rules shape it.
//!
//! **Nothing here blocks on a layer above the one being asked for.** Opening
//! a file does not wait for it to be parsed; colouring does not wait for the
//! index; the index does not wait for an assembly to be read. A caller that
//! asks for layer 2 gets layer 2, and if the answer needs layer 4 and layer 4
//! is not built yet, it is told so rather than made to wait for it.
//!
//! **Offsets change units at this boundary.** Below, everything is a byte
//! offset into UTF-8, because that is what `&str` indexes by and what the
//! compiler counts in. Above, everything is a UTF-16 code unit, because that
//! is what `NSRange` and LSP count in. The conversion happens here, once,
//! rather than being remembered at every call site.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, RwLock};

use rustlyn_syntax::{ParseOptions, SyntaxTree};

use crate::cache::{Cache, Key, Layer, Lookup, Statistics};
use crate::decompile::{AssemblySurface, Failure, MethodBody};
use crate::document::Document;
use crate::fingerprint::Fingerprint;
use crate::highlight::{Class, Highlighter};
use crate::index::{BuildReport, ProjectIndex};
use crate::navigate::{Miss, definition_at};
use crate::outline::FileOutline;
use crate::project::{Project, ProjectKind, compiled_files};
use crate::semantic::{Completion, Place, Semantic};
use crate::utf16::Utf16Map;

// MARK: - rename

mod rename;
pub use rename::{RenameConflict, RenameInfo, RenameResult};

// MARK: - navigation: type definition, bases, implementations, hierarchies, search
mod navigation;
pub use navigation::{Call, Item, LineRange, SearchResult};

// MARK: - syntax-level editing: formatting, structure, braces, comments
pub mod editing;

// MARK: - refactoring dialogs: change signature, extract interface and base class, pull up, overrides, move statics
mod refactor;
pub use refactor::RefactorResult;

/// A coloured run, in the units the editor counts in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Run {
    /// UTF-16 code units from the start of the document.
    pub start: u32,
    pub length: u32,
    pub class: Class,
}

/// Somewhere to go: a file and a place in it, in the editor's units.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Location {
    /// Relative to the project root.
    pub path: PathBuf,
    pub line: u32,
    /// UTF-16 code units from the start of the line.
    pub character: u32,
    pub length: u32,
    /// What is there, for an icon.
    pub kind: crate::outline::DeclarationKind,
    /// The fully qualified name, for a list of candidates.
    pub name: String,
}

/// What `⌘B` came back with.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Definition {
    /// The word that was under the cursor.
    pub word: String,
    /// Where it leads. More than one when nothing in scope told them apart,
    /// and the editor should offer the choice rather than pick.
    pub targets: Vec<Location>,
    /// Whether the scope settled it.
    pub certain: bool,
}

/// Why a question could not be answered.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Refusal {
    /// The file is not open.
    NotOpen,
    /// The file is not C#, so the layers above 1 have nothing to say.
    NotCsharp,
    /// The project has not been indexed yet.
    NotIndexed,
    /// The project has not been compiled yet, so nothing is known about what
    /// the code means — only what it declares.
    NotCompiled,
    /// The cursor is not on a name.
    NotAName,
    /// The receiver of a member access could not be typed.
    ReceiverUnknown(String),
    /// The name is nowhere in the project.
    NotInProject(String),
    /// An assembly could not be read.
    Assembly(Failure),
    /// The file could not be read from disk.
    Io(String),
    /// Called off by the caller before it finished (see
    /// `Session::cancel_code_lens`).
    Cancelled,
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotOpen => f.write_str("the file is not open"),
            Self::NotCsharp => f.write_str("this only understands C#"),
            Self::NotIndexed => f.write_str("the project has not been indexed yet"),
            Self::NotCompiled => f.write_str("the project has not been compiled yet"),
            Self::NotAName => f.write_str("the cursor is not on a name"),
            Self::ReceiverUnknown(what) => {
                write!(f, "nothing here says what `{what}` is")
            }
            Self::NotInProject(name) => write!(f, "`{name}` is not declared in this project"),
            Self::Assembly(failure) => write!(f, "{failure}"),
            Self::Io(why) => f.write_str(why),
            Self::Cancelled => f.write_str("called off"),
        }
    }
}

impl std::error::Error for Refusal {}

impl From<Miss> for Refusal {
    fn from(miss: Miss) -> Self {
        match miss {
            Miss::NotAName => Self::NotAName,
            Miss::ReceiverUnknown(what) => Self::ReceiverUnknown(what),
            Miss::NotInProject(name) => Self::NotInProject(name),
        }
    }
}

/// One open file and what has been worked out about it.
struct Open {
    document: Arc<Document>,
    highlighter: Highlighter,
    /// The parse, once something has asked for it. A file may be opened,
    /// scrolled through and closed without ever being parsed.
    tree: Option<Arc<SyntaxTree>>,
}

/// The editor's handle on everything below.
pub struct Session {
    root: PathBuf,
    cache: Arc<Cache>,
    options: ParseOptions,
    open: Mutex<HashMap<PathBuf, Open>>,
    /// Each file's text as a compile last read it, by its length and time:
    /// a save changes one file, and reading the other tens of thousands
    /// again is most of what a compile after it would take.
    read: RwLock<HashMap<PathBuf, ReadSource>>,
    /// Swapped wholesale when the project is reindexed, so a reader holding
    /// the old one keeps answering from it.
    index: RwLock<Arc<ProjectIndex>>,
    /// The project compiled, swapped the same way.
    semantic: RwLock<Option<Arc<Semantic>>>,
    /// Whether the compilation has changed since it was last written to
    /// disk or read from it.
    unsaved: std::sync::atomic::AtomicBool,
    /// Reference assemblies as read last time, by path, with the length and
    /// modification time they were read at. A Unity project references two
    /// hundred of them and changes none between saves.
    assemblies: Mutex<HashMap<PathBuf, ReadAssembly>>,
    /// Where decompiled assemblies are kept, when it is not the project's
    /// cache: `UnityEngine.CoreModule` is the same file in every Unity
    /// project of one editor version, and decompiling it once per project
    /// is waste. See [`Session::share_assembly_cache`].
    assembly_cache: std::sync::OnceLock<Arc<Cache>>,
    /// Where the project's source generators write, as last found. Finding
    /// it walks `Library/Bee` and reads every response file there — tens of
    /// milliseconds on a Unity project, seconds when the disk is busy — and
    /// an editor asks on every file it opens. The folders change only when
    /// Unity compiles scripts, so they are found again on each `compile`.
    generated: RwLock<Option<Arc<Vec<PathBuf>>>>,
    /// Hot reload, once started (see `crate::hot`).
    hot: Mutex<Option<crate::hot::Hot>>,
    /// The generated code compiled while hot reload runs, in place of what
    /// Unity's last compile left.
    hot_generated: RwLock<Option<PathBuf>>,
    /// Bumped by `cancel_code_lens`: a count begun under an older value
    /// stops at the next file it would search.
    lens_epoch: std::sync::atomic::AtomicU64,
}

/// An assembly's bytes, with the length and modification time they were
/// read at.
type ReadAssembly = (u64, Option<std::time::SystemTime>, Arc<[u8]>);

/// A source file's text as read, under the length and modification time it
/// was read at.
type ReadSource = ((u64, u128), Arc<str>);

/// What compiling the project did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compiled {
    pub kind: ProjectKind,
    /// How many `.csproj` files described it.
    pub projects: usize,
    pub files: usize,
    pub references: usize,
    pub milliseconds: u64,
    /// Nothing had changed since the compilation that was there — often one
    /// read back from disk — so it was kept rather than built again.
    pub unchanged: bool,
}

/// Every use of a name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Uses {
    pub word: String,
    pub locations: Vec<Location>,
}

/// Something wrong in a file, in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileDiagnostic {
    /// UTF-16 offset and length in the text asked about.
    pub start: u32,
    pub length: u32,
    /// 0 hidden, 1 info, 2 warning, 3 error. Hidden ones are only reported
    /// when they are `unnecessary`: an IDE analyzer's code to fade, which
    /// an editor draws faded and does not list.
    pub severity: u8,
    /// `CS0103`, or an IDE analyzer's `IDE0051`.
    pub code: String,
    pub message: String,
    /// The code can go: draw it faded.
    pub unnecessary: bool,
    /// A use of something obsolete: strike it through.
    pub deprecated: bool,
}

/// Everything wrong in a file, and whether that is all of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileDiagnostics {
    pub items: Vec<FileDiagnostic>,
    /// Whether the compiler looked, or only the parser: before the project
    /// is compiled, and for a file outside it, only syntax is checked.
    pub semantic: bool,
}

/// The overloads of the call being typed. Parameter ranges are UTF-16 into
/// each label.
pub type SignatureList = crate::semantic::Signatures;

/// What can be written at the cursor, in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompletionList {
    pub items: Vec<Completion>,
    /// Where the word being completed starts, in UTF-16 code units.
    pub start: u32,
    /// Where a new name is being written: offer the items, commit none of
    /// them on a space or punctuation.
    pub suggestion_mode: bool,
}

/// One replacement, in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Change {
    /// Absolute, as the edit named it.
    pub path: PathBuf,
    /// UTF-16 offset and length in that file's text: the editor's text for
    /// the file asked about, the compiled or saved text for any other.
    pub start: u32,
    pub length: u32,
    pub text: String,
}

/// Edits across the project, in the editor's units.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Changes {
    /// In order within each file; never overlapping.
    pub changes: Vec<Change>,
    /// `(from, to)`: files to rename.
    pub renames: Vec<(PathBuf, PathBuf)>,
}

/// A light-bulb entry, in the editor's units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Action {
    pub title: String,
    pub kind: crate::semantic::ActionKind,
    /// The diagnostic code it fixes.
    pub fixes: Option<String>,
    pub changes: Changes,
}

impl std::fmt::Debug for Session {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Session")
            .field("root", &self.root)
            .field(
                "open",
                &self.open.lock().map(|open| open.len()).unwrap_or(0),
            )
            .field("indexed", &self.index().len())
            .finish()
    }
}

impl Session {
    /// A session over `root`, keeping its cache in `cache_directory`.
    ///
    /// `symbols` are the preprocessor symbols the project compiles with,
    /// which decide which branch of an `#if` is live — and so which code is
    /// coloured, outlined and indexed at all.
    #[must_use]
    pub fn new(
        root: impl Into<PathBuf>,
        cache_directory: Option<PathBuf>,
        symbols: Vec<String>,
    ) -> Self {
        Self {
            root: root.into(),
            // 256MB of answers. A Unity project's index is tens of megabytes
            // and a file's outline is kilobytes, so this holds everything
            // about a large project and evicts on nothing but a pathological
            // one.
            cache: Arc::new(Cache::new(cache_directory, 256 << 20)),
            options: ParseOptions::with_symbols(symbols),
            open: Mutex::new(HashMap::new()),
            read: RwLock::new(HashMap::new()),
            index: RwLock::new(Arc::new(ProjectIndex::default())),
            semantic: RwLock::new(None),
            unsaved: std::sync::atomic::AtomicBool::new(false),
            assemblies: Mutex::new(HashMap::new()),
            assembly_cache: std::sync::OnceLock::new(),
            generated: RwLock::new(None),
            hot: Mutex::new(None),
            hot_generated: RwLock::new(None),
            lens_epoch: std::sync::atomic::AtomicU64::new(0),
        }
    }

    /// Calls off every `code_lens` running now: each stops at the next file
    /// of the project it would search and refuses with `Cancelled`. One
    /// begun after this is not affected. For an editor whose file is no
    /// longer on screen: its counts would be thrown away, and the search
    /// takes every core the next file needs.
    pub fn cancel_code_lens(&self) {
        self.lens_epoch
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// Whether `cancel_code_lens` was called since `epoch` was read.
    pub(crate) fn lens_cancelled(&self, epoch: u64) -> bool {
        self.lens_epoch.load(std::sync::atomic::Ordering::Relaxed) != epoch
    }

    pub(crate) fn lens_epoch(&self) -> u64 {
        self.lens_epoch.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Where the project's source generators write (see `generated`).
    fn generated_folders(&self) -> Arc<Vec<PathBuf>> {
        if let Some(found) = self.generated.read().ok().and_then(|held| held.clone()) {
            return found;
        }
        self.refresh_generated_folders()
    }

    fn refresh_generated_folders(&self) -> Arc<Vec<PathBuf>> {
        let mut folders = crate::project::generated_folders(&self.root);
        if let Some(hot) = self.hot_generated.read().ok().and_then(|held| held.clone()) {
            folders.push(hot);
        }
        let found = Arc::new(folders);
        if let Ok(mut held) = self.generated.write() {
            *held = Some(found.clone());
        }
        found
    }

    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    #[must_use]
    pub fn statistics(&self) -> Statistics {
        self.cache.statistics()
    }

    #[must_use]
    pub fn index(&self) -> Arc<ProjectIndex> {
        self.index
            .read()
            .unwrap_or_else(|error| error.into_inner())
            .clone()
    }

    // MARK: - layer 1

    /// Opens a file. Reads it and decodes it, and does nothing else.
    ///
    /// # Errors
    ///
    /// Fails when the file cannot be read.
    pub fn open(&self, path: impl AsRef<Path>) -> Result<Arc<Document>, Refusal> {
        let path = path.as_ref().to_path_buf();
        let document = Document::open(&path).map_err(|error| Refusal::Io(error.to_string()))?;
        self.install(path, document.clone());
        Ok(document)
    }

    /// Opens a buffer whose text the editor already has — one being typed
    /// into, which is not what is on disk.
    pub fn open_text(&self, path: impl AsRef<Path>, text: &str) -> Arc<Document> {
        let path = path.as_ref().to_path_buf();
        let document = Document::from_bytes(
            &path,
            text.as_bytes(),
            Fingerprint::of_bytes(text.as_bytes()),
            0,
        );
        self.install(path, document.clone());
        document
    }

    /// Replaces an open file's text: what an edit produces.
    ///
    /// Everything worked out about the old text is dropped, because it was
    /// about the old text. The checkpoints go with it, which is why this is
    /// not the thing to call on every keystroke — an editor that colours as
    /// you type should hold its own buffer and hand it over when it settles.
    pub fn set_text(&self, path: impl AsRef<Path>, text: &str) -> Result<Arc<Document>, Refusal> {
        let path = path.as_ref().to_path_buf();
        let mut open = self.open.lock().unwrap_or_else(|error| error.into_inner());
        let existing = open.get(&path).ok_or(Refusal::NotOpen)?;
        let document = existing.document.with_text(text.to_owned());
        open.insert(
            path,
            Open {
                highlighter: Highlighter::new(document.clone(), self.options.clone()),
                document: document.clone(),
                tree: None,
            },
        );
        Ok(document)
    }

    pub fn close(&self, path: impl AsRef<Path>) {
        self.open
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .remove(path.as_ref());
    }

    #[must_use]
    pub fn document(&self, path: impl AsRef<Path>) -> Option<Arc<Document>> {
        self.open
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .get(path.as_ref())
            .map(|open| open.document.clone())
    }

    fn install(&self, path: PathBuf, document: Arc<Document>) {
        let highlighter = Highlighter::new(document.clone(), self.options.clone());
        self.open
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .insert(
                path,
                Open {
                    document,
                    highlighter,
                    tree: None,
                },
            );
    }

    // MARK: - layer 2

    /// Colours lines `first` through `last` of an open file.
    ///
    /// # Errors
    ///
    /// Fails when the file is not open or is not C#.
    pub fn classify(
        &self,
        path: impl AsRef<Path>,
        first: u32,
        last: u32,
    ) -> Result<Vec<Run>, Refusal> {
        let mut open = self.open.lock().unwrap_or_else(|error| error.into_inner());
        let file = open.get_mut(path.as_ref()).ok_or(Refusal::NotOpen)?;
        if !file.document.is_csharp() {
            return Err(Refusal::NotCsharp);
        }
        let runs = file.highlighter.classify(first, last);
        let map = file.document.utf16();
        Ok(runs
            .into_iter()
            .map(|run| {
                let start = map.to_utf16(run.start);
                Run {
                    start,
                    length: map.to_utf16(run.start + run.length) - start,
                    class: run.class,
                }
            })
            .collect())
    }

    /// Walks the whole of an open file, laying down every checkpoint, so that
    /// a jump to any line is as cheap as a scroll.
    ///
    /// For a background thread. Nothing is returned; the point is what it
    /// leaves behind.
    ///
    /// # Errors
    ///
    /// Fails when the file is not open or is not C#.
    pub fn warm(&self, path: impl AsRef<Path>) -> Result<(), Refusal> {
        let mut open = self.open.lock().unwrap_or_else(|error| error.into_inner());
        let file = open.get_mut(path.as_ref()).ok_or(Refusal::NotOpen)?;
        if !file.document.is_csharp() {
            return Err(Refusal::NotCsharp);
        }
        file.highlighter.warm();
        Ok(())
    }

    // MARK: - layer 3

    /// The outline of an open file.
    ///
    /// # Errors
    ///
    /// Fails when the file is not open or is not C#.
    pub fn outline(&self, path: impl AsRef<Path>) -> Result<Arc<FileOutline>, Refusal> {
        let path = path.as_ref();
        let document = self.document(path).ok_or(Refusal::NotOpen)?;
        if !document.is_csharp() {
            return Err(Refusal::NotCsharp);
        }
        let key = self.key(Layer::Outline, path);
        match self
            .cache
            .lookup_bytes::<FileOutline>(&key, document.text().as_bytes())
        {
            Lookup::Hit(outline) => Ok(outline),
            Lookup::Miss(_, print) => {
                let outline = FileOutline::of(document.source(), &self.options);
                Ok(self.cache.store(&key, print, outline))
            }
        }
    }

    /// The parse of an open file, made once and kept.
    fn tree(&self, path: &Path) -> Result<Arc<SyntaxTree>, Refusal> {
        let mut open = self.open.lock().unwrap_or_else(|error| error.into_inner());
        let file = open.get_mut(path).ok_or(Refusal::NotOpen)?;
        if !file.document.is_csharp() {
            return Err(Refusal::NotCsharp);
        }
        if let Some(tree) = &file.tree {
            return Ok(tree.clone());
        }
        let tree = Arc::new(rustlyn_syntax::parse_with(
            file.document.source().clone(),
            &self.options,
        ));
        file.tree = Some(tree.clone());
        Ok(tree)
    }

    // MARK: - layer 4

    /// Builds the project index over `paths`, and installs it.
    ///
    /// Files that have not changed since the last build come back from the
    /// cache rather than being parsed again, so this is cheap to call after
    /// a save and expensive only the first time.
    pub fn reindex(&self, paths: &[PathBuf]) -> BuildReport {
        let index = Arc::new(ProjectIndex::build(
            &self.root,
            paths,
            &self.cache,
            &self.options,
        ));
        let report = index.report();
        *self
            .index
            .write()
            .unwrap_or_else(|error| error.into_inner()) = index;
        report
    }

    /// Where the name at `offset` was declared.
    ///
    /// `offset` is in UTF-16 code units, as the editor counts them.
    ///
    /// # Errors
    ///
    /// Says why rather than answering emptily: not a name, a receiver that
    /// cannot be typed, and a name from outside the project each want
    /// something different to happen next.
    pub fn definition(&self, path: impl AsRef<Path>, offset: u32) -> Result<Definition, Refusal> {
        self.definition_in(path, offset, None)
    }

    /// Where the name at `offset` was declared, in `text` when the editor
    /// has changes it has not saved.
    ///
    /// The compiler answers when the project has been compiled and it knows;
    /// the index answers otherwise, and says when it is guessing.
    ///
    /// # Errors
    ///
    /// The same as [`Self::definition`].
    pub fn definition_in(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Definition, Refusal> {
        let path = path.as_ref();
        let answer = self.semantic_definition(path, offset, text);
        match answer {
            Ok(definition) if !definition.targets.is_empty() => return Ok(definition),
            Err(Refusal::NotAName) => return Err(Refusal::NotAName),
            _ => {}
        }
        // The index reads the file as it was opened. Offsets into text that
        // has moved on from that would land on other words, so for an edited
        // file the compiler's answer is the only one.
        let edited = text.is_some_and(|text| {
            self.document(path)
                .is_none_or(|document| document.text() != text)
        });
        if edited {
            return answer;
        }
        self.index_definition(path, offset)
    }

    fn index_definition(&self, path: &Path, offset: u32) -> Result<Definition, Refusal> {
        let document = self.document(path).ok_or(Refusal::NotOpen)?;
        let index = self.index();
        if index.is_empty() {
            return Err(Refusal::NotIndexed);
        }
        let file = self.file_id(&index, path).ok_or(Refusal::NotIndexed)?;
        let tree = self.tree(path)?;

        let byte = document.utf16().to_byte(offset);
        let target = definition_at(&tree, byte, &index, file)?;

        let targets = target
            .found
            .entries
            .iter()
            .filter_map(|&id| self.location_of(&index, id))
            .collect();
        Ok(Definition {
            word: target.word,
            targets,
            certain: target.found.confidence == crate::index::Confidence::Certain,
        })
    }

    /// Everything that derives from, or overrides, whatever is at `offset`.
    ///
    /// # Errors
    ///
    /// The same refusals as [`Self::definition`].
    pub fn implementations(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
    ) -> Result<Vec<Location>, Refusal> {
        let path = path.as_ref();
        let document = self.document(path).ok_or(Refusal::NotOpen)?;
        let index = self.index();
        if index.is_empty() {
            return Err(Refusal::NotIndexed);
        }
        let file = self.file_id(&index, path).ok_or(Refusal::NotIndexed)?;
        let tree = self.tree(path)?;

        let byte = document.utf16().to_byte(offset);
        let target = definition_at(&tree, byte, &index, file)?;

        let mut found = Vec::new();
        for &entry in &target.found.entries {
            let is_type = index
                .entry(entry)
                .is_some_and(|entry| entry.declaration.kind.is_type());
            let ids = if is_type {
                index.implementations(entry)
            } else {
                index.overrides(entry)
            };
            for id in ids {
                if let Some(location) = self.location_of(&index, id)
                    && !found.contains(&location)
                {
                    found.push(location);
                }
            }
        }
        Ok(found)
    }

    /// Which file of the index a path is, if any.
    fn file_id(&self, index: &ProjectIndex, path: &Path) -> Option<u32> {
        let relative = path.strip_prefix(&self.root).unwrap_or(path);
        index
            .files()
            .iter()
            .position(|file| file.path == relative)
            .map(|position| position as u32)
    }

    /// Turns an index entry into somewhere to go, in the editor's units.
    ///
    /// The line and column have to be counted in the file the declaration is
    /// in, which the index does not hold — it holds byte offsets, because
    /// that is what it was built from. Reading the file to count them is the
    /// price of not keeping a line table for every file in the project, and
    /// it is paid once per jump rather than once per file.
    fn location_of(&self, index: &ProjectIndex, id: u32) -> Option<Location> {
        let entry = index.entry(id)?;
        let file = index.files().get(entry.file as usize)?;
        let absolute = self.root.join(&file.path);

        // The open copy first: a file being edited has moved on from disk,
        // and the offsets in the index are the ones it was indexed at.
        let text = self
            .document(&absolute)
            .map(|document| document.text().to_owned())
            .or_else(|| std::fs::read_to_string(&absolute).ok())?;

        let mut start = entry.declaration.name_span.start() as usize;
        if start > text.len() {
            return None;
        }
        // An open copy edited since it was indexed can have a character
        // where the offset points; the jump lands on that character.
        while !text.is_char_boundary(start) {
            start -= 1;
        }
        let line_start = text[..start].rfind('\n').map_or(0, |at| at + 1);
        let line = text[..start].bytes().filter(|&byte| byte == b'\n').count() as u32;
        let character = text[line_start..start].encode_utf16().count() as u32;
        let length = text
            .get(start..start + entry.declaration.name_span.length() as usize)
            .map_or(0, |name| name.encode_utf16().count() as u32);

        Some(Location {
            path: file.path.clone(),
            line,
            character,
            length,
            kind: entry.declaration.kind,
            name: entry.declaration.qualified_name(),
        })
    }

    // MARK: - layer 6

    /// Compiles the project: works out its references and symbols, reads
    /// every file it compiles, and installs the result.
    ///
    /// `paths` are the files the editor knows of; the project decides which
    /// of them it compiles and adds what it names that the editor does not.
    /// An empty list means the files of the index. Blocks for as long as
    /// declaring the project takes — seconds on a large one — so it belongs
    /// on a background thread, and the old compilation keeps answering until
    /// the new one is in.
    pub fn compile(&self, paths: &[PathBuf]) -> Compiled {
        self.compile_with(paths, &[])
    }

    /// The same, with the files of `from_disk` read from disk even where the
    /// editor holds them open: a hot reload round over files written by
    /// something else, which the editor has not read back yet.
    fn compile_with(&self, paths: &[PathBuf], from_disk: &[PathBuf]) -> Compiled {
        let started = std::time::Instant::now();
        let discovering = rustlyn_semantics::timing::phase("discover project");
        // Unity may have compiled since: its generators may write elsewhere.
        self.refresh_generated_folders();
        let mut project = Project::discover(&self.root, &self.options.preprocessor_symbols);
        // Hot reload compiles what its generators write, which the build
        // the editor runs was made with.
        let mut unity_generated = Vec::new();
        if let Some(hot) = self.hot_generated.read().ok().and_then(|held| held.clone()) {
            unity_generated = crate::project::generated_folders(&self.root);
            project.files.retain(|path| {
                !unity_generated
                    .iter()
                    .any(|folder| path.starts_with(folder))
            });
            let mut made = Vec::new();
            crate::project::files_under(&hot, &mut made);
            made.sort();
            project.files.extend(made);
        }
        drop(discovering);
        let mut known: Vec<PathBuf> = if paths.is_empty() {
            self.index()
                .files()
                .iter()
                .map(|file| self.root.join(&file.path))
                .collect()
        } else {
            paths.iter().map(|path| self.root.join(path)).collect()
        };
        // An editor that lists Unity's generated code (to show it) does not
        // bring it back in either.
        known.retain(|path| {
            !unity_generated
                .iter()
                .any(|folder| path.starts_with(folder))
        });
        let files = compiled_files(&project, &known);
        let reading = rustlyn_semantics::timing::phase("read sources");

        // The editor's copy of an open file is newer than the disk's.
        let open: HashMap<PathBuf, String> = self
            .open
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .iter()
            .filter(|(path, _)| !from_disk.contains(path))
            .map(|(path, file)| (path.clone(), file.document.text().to_owned()))
            .collect();
        let kept = self
            .read
            .read()
            .unwrap_or_else(|error| error.into_inner())
            .clone();
        let read: Vec<Option<(PathBuf, String, Option<ReadSource>)>> =
            crate::semantic::parallel(files.len(), |index| {
                let path = &files[index];
                if let Some(text) = open.get(path) {
                    return Some((path.clone(), text.clone(), None));
                }
                let metadata = std::fs::metadata(path).ok()?;
                let stamp = (
                    metadata.len(),
                    metadata
                        .modified()
                        .ok()
                        .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
                        .map_or(0, |since| since.as_nanos()),
                );
                if let Some((kept_stamp, text)) = kept.get(path)
                    && *kept_stamp == stamp
                {
                    return Some((path.clone(), text.to_string(), None));
                }
                let bytes = std::fs::read(path).ok()?;
                let text = Document::from_bytes(path, &bytes, Fingerprint::of_bytes(&bytes), 0)
                    .text()
                    .to_owned();
                let fresh = Arc::<str>::from(text.as_str());
                Some((path.clone(), text, Some((stamp, fresh))))
            });
        {
            let mut held = self.read.write().unwrap_or_else(|error| error.into_inner());
            for entry in read.iter().flatten() {
                if let (path, _, Some(fresh)) = entry {
                    held.insert(path.clone(), fresh.clone());
                }
            }
        }
        let sources: Vec<(PathBuf, String)> = read
            .into_iter()
            .flatten()
            .map(|(path, text, _)| (path, text))
            .collect();

        drop(reading);
        let previous = self.semantic();
        let comparing = rustlyn_semantics::timing::phase("compare");
        let same = previous
            .as_ref()
            .is_some_and(|previous| previous.unchanged(&project, &sources));
        drop(comparing);
        if let Some(previous) = &previous
            && same
        {
            return Compiled {
                kind: project.kind,
                projects: project.projects,
                files: sources.len(),
                references: previous.reference_count(),
                milliseconds: started.elapsed().as_millis() as u64,
                unchanged: true,
            };
        }
        let references = self.read_references(&project.references);
        let compiled = Compiled {
            kind: project.kind,
            projects: project.projects,
            files: sources.len(),
            references: references.len(),
            milliseconds: 0,
            unchanged: false,
        };
        let semantic = Semantic::build(project, sources, &references, previous.as_deref());
        let references = semantic.reference_count();
        *self
            .semantic
            .write()
            .unwrap_or_else(|error| error.into_inner()) = Some(Arc::new(semantic));
        self.unsaved
            .store(true, std::sync::atomic::Ordering::Release);
        Compiled {
            references,
            milliseconds: started.elapsed().as_millis() as u64,
            ..compiled
        }
    }

    /// The compilation, if `path` is in it: a file that is not — new since
    /// the last compile, or not part of the project — is as unknown to the
    /// compiler as the whole project is before it is compiled.
    fn compiled(&self, path: &Path) -> Result<Arc<Semantic>, Refusal> {
        let semantic = self.semantic().ok_or(Refusal::NotCompiled)?;
        if semantic.tree_index(path).is_none() {
            return Err(Refusal::NotCompiled);
        }
        Ok(semantic)
    }

    /// Where the compilation is kept between runs.
    fn snapshot_path(&self) -> Option<PathBuf> {
        Some(self.cache.directory()?.join("compilation.bin"))
    }

    /// Writes the compilation to the cache directory, if it has changed since
    /// it was last written or read. `Ok(false)` when there was nothing to
    /// write: no compilation, no cache directory, or no change.
    ///
    /// The file is written beside its place and renamed into it, so a
    /// process that dies halfway leaves the old snapshot, not half a new one.
    ///
    /// # Errors
    ///
    /// Fails when the file cannot be written.
    pub fn save_compilation(&self) -> std::io::Result<bool> {
        let (Some(path), Some(semantic)) = (self.snapshot_path(), self.semantic()) else {
            return Ok(false);
        };
        if !self
            .unsaved
            .swap(false, std::sync::atomic::Ordering::AcqRel)
        {
            return Ok(false);
        }
        let bytes = semantic.write();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let partial = path.with_extension(format!("{}.partial", std::process::id()));
        let written =
            std::fs::write(&partial, &bytes).and_then(|()| std::fs::rename(&partial, &path));
        if written.is_err() {
            let _ = std::fs::remove_file(&partial);
            self.unsaved
                .store(true, std::sync::atomic::Ordering::Release);
        }
        written.map(|()| true)
    }

    /// Reads the compilation the last run wrote, and installs it — unless
    /// there is a compilation already, which is newer. `None` when there is
    /// nothing to read, or it is from another build, or damaged.
    ///
    /// What is read may be out of date: files may have changed since. It
    /// answers straight away all the same, and the next [`Self::compile`]
    /// finds out, keeping it if nothing changed and replacing it if
    /// anything did.
    pub fn load_compilation(&self) -> Option<Compiled> {
        let started = std::time::Instant::now();
        if self.semantic().is_some() {
            return None;
        }
        let bytes = std::fs::read(self.snapshot_path()?).ok()?;
        let semantic = Semantic::read(&bytes)?;
        let compiled = Compiled {
            kind: semantic.project().kind,
            projects: semantic.project().projects,
            files: semantic.files(),
            references: semantic.reference_count(),
            milliseconds: 0,
            unchanged: true,
        };
        let mut slot = self
            .semantic
            .write()
            .unwrap_or_else(|error| error.into_inner());
        if slot.is_some() {
            return None;
        }
        *slot = Some(Arc::new(semantic));
        Some(Compiled {
            milliseconds: started.elapsed().as_millis() as u64,
            ..compiled
        })
    }

    /// Starts hot reload: every generator over Assembly-CSharp, the
    /// project compiled with what they wrote, and the build for the editor
    /// made beside it. `paths` are as for [`Self::compile`].
    ///
    /// # Errors
    /// What keeps it from starting.
    pub fn hot_start(
        &self,
        tools: crate::hot::Tools,
        paths: &[PathBuf],
    ) -> Result<crate::hot::Built, String> {
        let mut response = crate::hot::Response::find(&self.root)?;
        // Files added since Unity last compiled are not in its list yet.
        let listed: std::collections::HashSet<PathBuf> = response
            .sources
            .iter()
            .map(|path| self.root.join(path))
            .collect();
        let mut added: Vec<PathBuf> = self
            .index()
            .files()
            .iter()
            .map(|file| self.root.join(&file.path))
            .filter(|path| {
                !listed.contains(path) && crate::hot::in_assembly_csharp(&self.root, path)
            })
            .collect();
        added.sort();
        response.sources.extend(added.into_iter().map(|path| {
            path.strip_prefix(&self.root)
                .map(Path::to_path_buf)
                .unwrap_or(path)
        }));
        let work = crate::hot::work_directory(&self.root);
        let generated = work.join("generated");
        crate::hot::generate_all(&tools, &self.root, &response, &generated)?;
        *self
            .hot_generated
            .write()
            .unwrap_or_else(|error| error.into_inner()) = Some(generated.clone());
        self.compile(paths);
        let base = self.semantic().ok_or("the project did not compile")?;
        let (built, tails, image) = crate::hot::build_whole(
            &self.root,
            &response,
            &response.sources,
            &generated,
            &work.join("Assembly-CSharp.dll"),
            &crate::hot::parsed_trees(&base),
        )?;
        let hot = crate::hot::Hot::new(&self.root, tools, response, base, tails, image, &built)?;
        *self.hot.lock().unwrap_or_else(|error| error.into_inner()) = Some(hot);
        Ok(built)
    }

    /// What saving `saved` comes to under hot reload: the generators run
    /// over them, the project compiled, the patch made — or why not.
    /// `paths` are as for [`Self::compile`]; `saved` are relative to the
    /// root or absolute.
    /// The text of `path` as the build the editor runs has it.
    pub fn hot_base_text(&self, path: &Path) -> Option<String> {
        let hot = self.hot.lock().unwrap_or_else(|error| error.into_inner());
        hot.as_ref()?.base_text(&self.root.join(path))
    }

    pub fn hot_save(
        &self,
        saved: &[PathBuf],
        paths: &[PathBuf],
    ) -> Result<crate::hot::Answer, String> {
        let saved: Vec<PathBuf> = saved.iter().map(|path| self.root.join(path)).collect();
        let started = std::time::Instant::now();
        let generated = {
            let mut hot = self.hot.lock().unwrap_or_else(|error| error.into_inner());
            hot.as_mut()
                .ok_or("hot reload has not started")?
                .generate(&saved)?
        };
        let generating = started.elapsed();
        // What was saved is what the round is about: on disk, whatever the
        // editor still holds of it.
        self.compile_with(paths, &saved);
        let compiling = started.elapsed() - generating;
        let current = self.semantic().ok_or("the project did not compile")?;
        let mut hot = self.hot.lock().unwrap_or_else(|error| error.into_inner());
        let answer = hot
            .as_mut()
            .ok_or("hot reload has not started")?
            .answer(&current, &saved, &generated);
        if std::env::var_os("RUSTLYN_TIMINGS").is_some() {
            eprintln!(
                "hot save: generators {} ms, compile {} ms, patch {} ms",
                generating.as_millis(),
                compiling.as_millis(),
                (started.elapsed() - generating - compiling).as_millis()
            );
        }
        Ok(answer)
    }

    /// A whole build for the editor to reload on, of the files as they are:
    /// what a save no patch carries needs.
    ///
    /// # Errors
    /// What keeps it from being built.
    pub fn hot_rebuild(&self, paths: &[PathBuf]) -> Result<crate::hot::Built, String> {
        let (response, sources, generated) = {
            let hot = self.hot.lock().unwrap_or_else(|error| error.into_inner());
            let hot = hot.as_ref().ok_or("hot reload has not started")?;
            (hot.response().clone(), hot.sources(), hot.generated())
        };
        self.compile(paths);
        let base = self.semantic().ok_or("the project did not compile")?;
        let work = crate::hot::work_directory(&self.root);
        let (built, _, image) = crate::hot::build_whole(
            &self.root,
            &response,
            &sources,
            &generated,
            &work.join("Assembly-CSharp.dll"),
            &crate::hot::parsed_trees(&base),
        )?;
        let mut hot = self.hot.lock().unwrap_or_else(|error| error.into_inner());
        hot.as_mut()
            .ok_or("hot reload has not started")?
            .reloaded(base, image);
        Ok(built)
    }

    pub fn semantic(&self) -> Option<Arc<Semantic>> {
        self.semantic
            .read()
            .unwrap_or_else(|error| error.into_inner())
            .clone()
    }

    fn read_references(&self, paths: &[PathBuf]) -> Vec<(PathBuf, Arc<[u8]>)> {
        let mut kept = self
            .assemblies
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let mut found = Vec::with_capacity(paths.len());
        for path in paths {
            let Ok(metadata) = std::fs::metadata(path) else {
                continue;
            };
            let stamp = (metadata.len(), metadata.modified().ok());
            if let Some((length, modified, bytes)) = kept.get(path)
                && (*length, *modified) == stamp
            {
                found.push((path.clone(), bytes.clone()));
                continue;
            }
            let Ok(bytes) = std::fs::read(path) else {
                continue;
            };
            let bytes: Arc<[u8]> = Arc::from(bytes);
            kept.insert(path.clone(), (stamp.0, stamp.1, bytes.clone()));
            found.push((path.clone(), bytes));
        }
        found
    }

    /// The text offsets into `path` count in: the editor's when it gave one,
    /// the compiled one otherwise.
    fn text_of(&self, semantic: &Semantic, path: &Path, text: Option<&str>) -> Option<String> {
        if let Some(text) = text {
            return Some(text.to_owned());
        }
        semantic.text(path).map(str::to_owned).or_else(|| {
            self.document(path)
                .map(|document| document.text().to_owned())
        })
    }

    fn semantic_definition(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Definition, Refusal> {
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        let (word, found) = semantic
            .definition(path, byte, text)
            .ok_or(Refusal::NotAName)?;
        let targets: Vec<Location> = found
            .iter()
            .filter_map(|found| self.place_location(&semantic, path, &here, text.is_some(), found))
            .collect();
        if targets.is_empty() {
            return Err(Refusal::NotInProject(word));
        }
        Ok(Definition {
            word,
            certain: targets.len() == 1,
            targets,
        })
    }

    /// Every use of the name at `offset`, declarations included — of the
    /// member's whole family, as `references_detailed` has it: a call
    /// through the interface member a method implements, or of the virtual
    /// method it overrides, is a use of it too, and the declarations of
    /// those members are among the places.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and when the cursor is not on
    /// a name the compiler knows.
    pub fn references(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Uses, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        let (word, found) = semantic
            .references_detailed(path, byte, text)
            .ok_or(Refusal::NotAName)?;
        let found = found
            .into_iter()
            .map(|reference| (reference.path, reference.span));
        let mut texts: HashMap<PathBuf, (String, Utf16Map)> = HashMap::new();
        let mut locations = Vec::with_capacity(found.len());
        for (file, span) in found {
            let entry = texts.entry(file.clone()).or_insert_with(|| {
                let content = if file == path {
                    here.clone()
                } else {
                    self.text_of(&semantic, &file, None).unwrap_or_default()
                };
                let map = Utf16Map::new(&content);
                (content, map)
            });
            if let Some(location) = self.location_in(
                &file,
                &entry.0,
                span,
                crate::outline::DeclarationKind::Field,
                &word,
            ) {
                locations.push(location);
            }
        }
        Ok(Uses { word, locations })
    }

    /// Every way the member at `offset` (UTF-16) can fail, and whether each
    /// can happen: [`Semantic::failability`]. Places in the answer are
    /// bytes of the compiled files, which are the files on disk.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and off a member.
    pub fn failability(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
    ) -> Result<crate::semantic::Failability, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, None)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        semantic.failability(path, byte).ok_or(Refusal::NotAName)
    }

    /// What can be written at `offset`.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn completions(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<CompletionList, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let byte = map.to_byte(offset);
        let list = semantic
            .completions(path, byte, text)
            .ok_or(Refusal::NotIndexed)?;
        Ok(CompletionList {
            items: list
                .items
                .into_iter()
                .map(|item| complete::in_units(&map, item))
                .collect(),
            start: map.to_utf16(list.start),
            suggestion_mode: list.suggestion_mode,
        })
    }

    /// What the name at `offset` is, as one line: `int Count`,
    /// `void Add(T item)`.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, or off a name.
    pub fn describe(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<String, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        let mut view = semantic.view_of(path, text).ok_or(Refusal::NotIndexed)?;
        let token = view.name_token_at(byte).ok_or(Refusal::NotAName)?;
        let resolved = view
            .resolve_use(&token)
            .ok_or_else(|| Refusal::NotInProject(token.value_text().to_string()))?;
        Ok(semantic.describe(&resolved))
    }

    /// What is wrong with a file as the editor has it. Before the project is
    /// compiled — or for a file outside it — the syntax only.
    ///
    /// # Errors
    ///
    /// Fails when there is no text: not given, not open, not on disk.
    pub fn diagnostics(
        &self,
        path: impl AsRef<Path>,
        text: Option<&str>,
    ) -> Result<FileDiagnostics, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path).ok();
        let here = match &semantic {
            Some(semantic) => self.text_of(semantic, path, text),
            None => self.plain_text_of(path, text),
        }
        .ok_or(Refusal::NotOpen)?;
        let (found, is_semantic) = match semantic
            .as_ref()
            .and_then(|semantic| semantic.diagnostics(path, text))
        {
            Some(found) => (found, true),
            None => {
                let tree = rustlyn_syntax::parse_with(
                    rustlyn_text::SourceText::new(path.to_string_lossy(), here.as_str()),
                    &self.options,
                );
                (tree.diagnostics().to_vec(), false)
            }
        };
        let map = Utf16Map::new(&here);
        let mut items: Vec<FileDiagnostic> = found
            .into_iter()
            .filter(|diagnostic| diagnostic.severity() != rustlyn_diagnostics::Severity::Hidden)
            .map(|diagnostic| {
                let span = diagnostic.span();
                let start = map.to_utf16(span.start());
                let end = map.to_utf16(span.end());
                FileDiagnostic {
                    start,
                    length: end.saturating_sub(start),
                    severity: match diagnostic.severity() {
                        rustlyn_diagnostics::Severity::Hidden => 0,
                        rustlyn_diagnostics::Severity::Info => 1,
                        rustlyn_diagnostics::Severity::Warning => 2,
                        rustlyn_diagnostics::Severity::Error => 3,
                    },
                    code: diagnostic.code().to_string(),
                    message: diagnostic.message().to_owned(),
                    // Roslyn tags these compiler warnings the same way its
                    // analyzers tag theirs: unreachable code fades, a use of
                    // something obsolete is struck through.
                    unnecessary: diagnostic.code().to_string() == "CS0162",
                    deprecated: matches!(
                        diagnostic.code().to_string().as_str(),
                        "CS0612" | "CS0618" | "CS0619"
                    ),
                }
            })
            .collect();
        let settings = self.settings(path);
        configured::configure_compiler_items(&settings, &mut items);
        if is_semantic && let Some(semantic) = &semantic {
            // The binder and the analyzers both report some things — an
            // unused local, unreachable code, an obsolete member. One entry
            // each: the analyzer's, which knows the span to fade or strike
            // through. The compiler's may be wider — an obsolete member from
            // its receiver, as Roslyn reports it — so overlapping is enough.
            let analyzed = configured::analyzer_items(semantic, path, text, &map, &settings);
            items.retain(|item| {
                !analyzed.iter().any(|other| {
                    other.code == item.code
                        && other.start < item.start + item.length.max(1)
                        && item.start < other.start + other.length.max(1)
                })
            });
            items.extend(analyzed);
            items.sort_by_key(|item| (item.start, item.length));
        }
        Ok(FileDiagnostics {
            items,
            semantic: is_semantic,
        })
    }

    /// The overloads of the call whose argument list holds `offset`, and
    /// which parameter the cursor is at.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and outside an argument list.
    pub fn signatures(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<SignatureList, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        let mut found = semantic
            .signatures(path, byte, text)
            .ok_or(Refusal::NotAName)?;
        for item in &mut found.items {
            let label = Utf16Map::new(&item.label);
            for range in &mut item.parameters {
                *range = (label.to_utf16(range.0), label.to_utf16(range.1));
            }
        }
        Ok(found)
    }

    /// What the documentation says about the name at `offset`.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, or off a name.
    pub fn documentation(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<crate::semantic::Documentation, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = Utf16Map::new(&here).to_byte(offset);
        semantic
            .documentation(path, byte, text)
            .ok_or(Refusal::NotAName)
    }

    /// Ever larger pieces of code around a selection, UTF-16, smallest
    /// first: what extend selection steps through. Syntax only.
    ///
    /// # Errors
    ///
    /// Fails when there is no text.
    pub fn selection_ranges(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
    ) -> Result<Vec<(u32, u32)>, Refusal> {
        let path = path.as_ref();
        let here = self.plain_text_of(path, text).ok_or(Refusal::NotOpen)?;
        let tree = rustlyn_syntax::parse_with(
            rustlyn_text::SourceText::new(path.to_string_lossy(), here.as_str()),
            &self.options,
        );
        let map = Utf16Map::new(&here);
        Ok(crate::selection::selection_ranges(
            &tree.root(),
            &here,
            map.to_byte(start),
            map.to_byte(end),
        )
        .into_iter()
        .map(|span| (map.to_utf16(span.start()), map.to_utf16(span.end())))
        .collect())
    }

    /// A file's text without a compilation: given, open, or on disk.
    fn plain_text_of(&self, path: &Path, text: Option<&str>) -> Option<String> {
        if let Some(text) = text {
            return Some(text.to_owned());
        }
        self.document(path)
            .map(|document| document.text().to_owned())
            .or_else(|| std::fs::read_to_string(path).ok())
    }

    /// A place the compiler found, as a location in the editor's units.
    fn place_location(
        &self,
        semantic: &Semantic,
        asked: &Path,
        asked_text: &str,
        edited: bool,
        found: &crate::semantic::Found,
    ) -> Option<Location> {
        match &found.place {
            Place::Source { path, span } => {
                let text = if path == asked && edited {
                    asked_text.to_owned()
                } else {
                    self.text_of(semantic, path, None)?
                };
                self.location_in(path, &text, *span, found.kind, &found.name)
            }
            Place::Metadata {
                assembly,
                type_name,
                member,
            } => {
                let surface = self.assembly(assembly).ok()?;
                let types: Vec<usize> = surface
                    .declarations
                    .iter()
                    .enumerate()
                    .filter(|(_, declaration)| declaration.is_type)
                    .map(|(index, _)| index)
                    .collect();
                let at = *types
                    .iter()
                    .find(|&&index| surface.declarations[index].name == *type_name)?;
                // A type's members follow it, up to the next type. The
                // surface writes a property or an event as its accessors and
                // a constructor under its type's name, so those are what a
                // member is known by there.
                let mut chosen = at;
                if let Some(member) = member {
                    let owner = type_name.rsplit(['.', '/']).next().unwrap_or(type_name);
                    let owner = owner.split('`').next().unwrap_or(owner);
                    let names: Vec<String> = if member == ".ctor" || member == ".cctor" {
                        vec![owner.to_owned()]
                    } else {
                        ["", "get_", "set_", "add_", "remove_"]
                            .iter()
                            .map(|prefix| format!("{prefix}{member}"))
                            .collect()
                    };
                    let members = surface
                        .declarations
                        .iter()
                        .enumerate()
                        .skip(at + 1)
                        .take_while(|(_, declaration)| !declaration.is_type);
                    // The name itself first: a field `one` beats `get_one`.
                    if let Some((index, _)) = names.iter().find_map(|name| {
                        members
                            .clone()
                            .find(|(_, declaration)| declaration.name == *name)
                    }) {
                        chosen = index;
                    }
                }
                let declaration = &surface.declarations[chosen];
                let text = &surface.text;
                let start = declaration.name_start as usize;
                let line_start = text.get(..start)?.rfind('\n').map_or(0, |at| at + 1);
                Some(Location {
                    path: assembly.clone(),
                    line: declaration.line,
                    character: text[line_start..start].encode_utf16().count() as u32,
                    length: text
                        .get(start..start + declaration.name_length as usize)
                        .map_or(0, |name| name.encode_utf16().count() as u32),
                    kind: found.kind,
                    name: found.name.clone(),
                })
            }
        }
    }

    /// A byte span of `text` as a location, the path relative to the root
    /// when it is under it.
    fn location_in(
        &self,
        path: &Path,
        text: &str,
        span: rustlyn_text::TextSpan,
        kind: crate::outline::DeclarationKind,
        name: &str,
    ) -> Option<Location> {
        let start = span.start() as usize;
        let end = span.end() as usize;
        let before = text.get(..start)?;
        let line_start = before.rfind('\n').map_or(0, |at| at + 1);
        Some(Location {
            path: path.strip_prefix(&self.root).unwrap_or(path).to_path_buf(),
            line: before.bytes().filter(|&byte| byte == b'\n').count() as u32,
            character: before[line_start..].encode_utf16().count() as u32,
            length: text
                .get(start..end)
                .map_or(0, |name| name.encode_utf16().count() as u32),
            kind,
            name: name.to_owned(),
        })
    }

    // MARK: - edits

    /// A workspace edit in the editor's units. `asked` is the file the
    /// question was about, and `asked_text` the text its spans count in;
    /// every other file's spans count in its compiled text, or its open or
    /// saved text when it is not compiled.
    pub(crate) fn changes_of(
        &self,
        semantic: Option<&Semantic>,
        asked: &Path,
        asked_text: &str,
        edit: &crate::edit::WorkspaceEdit,
    ) -> Changes {
        let mut changes = Vec::new();
        // What a generator wrote is written again on the next compilation:
        // an edit there would be lost, so none is ever made.
        let generated = self.generated_folders();
        for file in &edit.files {
            if crate::project::is_generated(&generated, &file.path) {
                continue;
            }
            let owned;
            let text: &str = if file.path == asked {
                asked_text
            } else {
                owned = semantic
                    .and_then(|semantic| semantic.text(&file.path).map(str::to_owned))
                    .or_else(|| self.plain_text_of(&file.path, None))
                    .unwrap_or_default();
                &owned
            };
            let map = Utf16Map::new(text);
            for one in &file.edits {
                let start = map.to_utf16(one.span.start());
                let end = map.to_utf16(one.span.end());
                changes.push(Change {
                    path: file.path.clone(),
                    start,
                    length: end.saturating_sub(start),
                    text: one.text.clone(),
                });
            }
        }
        Changes {
            changes,
            renames: edit.renames.clone(),
        }
    }

    /// Whether `path` is source a generator wrote — in a Unity project,
    /// what its source generators left for the compiler. Such a file is
    /// compiled and can be read and navigated, but not edited: nothing this
    /// session returns ever changes it, and an editor should open it
    /// read-only.
    #[must_use]
    pub fn is_generated(&self, path: impl AsRef<Path>) -> bool {
        crate::project::is_generated(&self.generated_folders(), path.as_ref())
    }

    /// What the light bulb offers for `start..end` (UTF-16) of `path`:
    /// fixes for the diagnostics there, and refactorings of the selection.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn code_actions(
        &self,
        path: impl AsRef<Path>,
        start: u32,
        end: u32,
        text: Option<&str>,
    ) -> Result<Vec<Action>, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let map = Utf16Map::new(&here);
        let (from, to) = (map.to_byte(start), map.to_byte(end.max(start)));
        let span = rustlyn_text::TextSpan::from_bounds(from, to);
        let mut found = semantic
            .code_actions(path, span, text)
            .ok_or(Refusal::NotIndexed)?;
        found.extend(configured::extra_actions(self, &semantic, path, span, text));
        Ok(found
            .into_iter()
            .map(|action| Action {
                changes: self.changes_of(Some(&semantic), path, &here, &action.edit),
                title: action.title,
                kind: action.kind,
                fixes: action.fixes,
            })
            // Everything it would have changed was generated code.
            .filter(|action| {
                !action.changes.changes.is_empty() || !action.changes.renames.is_empty()
            })
            .collect())
    }

    // MARK: - layer 5

    /// Keeps decompiled assemblies in `directory` rather than in the
    /// project's cache, so every session given the same directory shares
    /// them. An assembly's answer depends on its bytes alone — nothing of
    /// the project goes into it — so sharing is safe. Set once, before the
    /// first assembly is asked for; `false` when it was set already.
    pub fn share_assembly_cache(&self, directory: PathBuf) -> bool {
        // Decompiled text is large and read whole: UnityEditor is 27MB.
        self.assembly_cache
            .set(Arc::new(Cache::new(Some(directory), 512 << 20)))
            .is_ok()
    }

    fn assembly_store(&self) -> &Arc<Cache> {
        self.assembly_cache.get().unwrap_or(&self.cache)
    }

    /// An assembly's surface, from the cache when it has been read before.
    ///
    /// # Errors
    ///
    /// Fails when the file cannot be read, is not a PE image, or has no CLI
    /// header.
    pub fn assembly(&self, path: impl AsRef<Path>) -> Result<Arc<AssemblySurface>, Refusal> {
        let path = path.as_ref();
        // No preprocessor symbols in the key: they change how the project's
        // sources read, not what an assembly says.
        let key = Key::new(Layer::AssemblySurface, path);
        let cache = self.assembly_store();
        match cache.lookup::<AssemblySurface>(&key, path) {
            Ok(Lookup::Hit(surface)) => Ok(surface),
            Ok(Lookup::Miss(bytes, print)) => {
                let name = path
                    .file_name()
                    .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
                let references = sibling_assemblies(path);
                let surface = AssemblySurface::decompiled(&bytes, &name, &references)
                    .map_err(Refusal::Assembly)?;
                Ok(cache.store(&key, print, surface))
            }
            Err(error) => Err(Refusal::Io(error.to_string())),
        }
    }

    /// One method's IL, asked for by the token the surface handed out.
    ///
    /// # Errors
    ///
    /// Fails when the assembly cannot be read or there is no such method.
    pub fn method_body(
        &self,
        path: impl AsRef<Path>,
        token: u32,
    ) -> Result<Arc<MethodBody>, Refusal> {
        let path = path.as_ref();
        // The token is part of the key: one assembly has many bodies, and
        // they are asked for one at a time.
        let key = Key::new(Layer::DecompiledType, path).salted(u64::from(token));
        let cache = self.assembly_store();
        match cache.lookup::<MethodBody>(&key, path) {
            Ok(Lookup::Hit(body)) => Ok(body),
            Ok(Lookup::Miss(bytes, print)) => {
                let body = MethodBody::of(&bytes, token).map_err(Refusal::Assembly)?;
                Ok(cache.store(&key, print, body))
            }
            Err(error) => Err(Refusal::Io(error.to_string())),
        }
    }

    /// The key for a layer and a file, salted by the options that change what
    /// the answer is.
    fn key(&self, layer: Layer, path: &Path) -> Key {
        let symbols: Vec<&str> = self
            .options
            .preprocessor_symbols
            .iter()
            .map(String::as_str)
            .collect();
        Key::new(layer, path).salted(Key::salt_of(&symbols))
    }
}

// MARK: - semantic colouring, highlights, detailed references, code lens

mod meaning;

pub use meaning::{DetailedUses, HighlightRun, LensRun, ReferenceItem, SemanticRun};

// MARK: - inlay hints, IDE analyzers, quick info

mod insight;

pub use insight::{InlayHintRun, QuickInfoAt};

// MARK: - completion parity

mod complete;

// MARK: - .editorconfig, fix all, completion filtering

mod configured;

pub use configured::{FilteredItem, filter_names};

/// The assemblies beside one: what it was most likely built against. An
/// engine's or a framework's folder holds everything its assemblies refer
/// to, and a plugin's usually holds its dependencies.
fn sibling_assemblies(path: &Path) -> Vec<Vec<u8>> {
    let Some(directory) = path.parent() else {
        return Vec::new();
    };
    let Ok(entries) = std::fs::read_dir(directory) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|found| {
            found != path
                && found
                    .extension()
                    .is_some_and(|extension| extension.eq_ignore_ascii_case("dll"))
        })
        .collect();
    paths.sort();
    paths
        .iter()
        .filter_map(|found| std::fs::read(found).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "rustlyn-session-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).expect("a temporary directory");
            Self(path)
        }
        fn write(&self, name: &str, text: &str) -> PathBuf {
            let path = self.0.join(name);
            if let Some(parent) = path.parent() {
                let _ = std::fs::create_dir_all(parent);
            }
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
    fn under_hot_reload_unitys_generated_code_stays_out_even_when_the_editor_lists_it() {
        let dir = TempDir::new("hot-generated");
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 2022.3.0f1\n",
        );
        let game = dir.write(
            "Assets/Game.cs",
            "partial class Game { void Run() { Made(); } }",
        );
        let unitys = dir.write(
            "Temp/GeneratedCode/Assembly-CSharp/Game.g.cs",
            "partial class Game { void Made() {} }",
        );
        dir.write(
            "Library/PilotHot/generated/Game.g.cs",
            "partial class Game { void Made() {} }",
        );
        let session = Session::new(&dir.0, None, Vec::new());
        session.reindex(&[game.clone(), unitys.clone()]);
        *session.hot_generated.write().expect("not poisoned") =
            Some(dir.0.join("Library/PilotHot/generated"));
        let compiled = session.compile(&[]);
        assert_eq!(
            compiled.files, 2,
            "the game and hot reload's copy of what was generated, not Unity's too"
        );
    }

    #[test]
    fn a_hot_round_compiles_what_was_saved_from_disk_even_when_the_editor_holds_it_open() {
        let dir = TempDir::new("hot-from-disk");
        let path = dir.write("A.cs", "class A { int M() => 1; }");
        let session = Session::new(&dir.0, None, Vec::new());
        session.reindex(std::slice::from_ref(&path));
        // The editor has the file open, as it was.
        session.open(&path).expect("opened");
        session
            .set_text(&path, "class A { int M() => 1; }")
            .expect("held");
        std::fs::write(&path, "class A { int M() => 2; }").expect("written");
        // By path: without reference assemblies the compilation's first tree
        // is the stand-in core library, not `A.cs`.
        let text = |session: &Session| {
            let semantic = session.semantic().expect("compiled");
            let tree = semantic.tree_index(&path).expect("A.cs is compiled");
            semantic
                .compilation()
                .trees()
                .source(tree)
                .map(|source| source.text().to_string())
                .unwrap_or_default()
        };
        session.compile(&[]);
        assert!(
            text(&session).contains("=> 1"),
            "an editor's open text is what it compiles"
        );
        session.compile_with(&[], std::slice::from_ref(&path));
        assert!(
            text(&session).contains("=> 2"),
            "a hot round's saved file is read from disk"
        );
    }

    /// A session over a small project, indexed.
    fn project(dir: &TempDir, files: &[(&str, &str)]) -> (Session, Vec<PathBuf>) {
        let paths: Vec<PathBuf> = files
            .iter()
            .map(|(name, text)| dir.write(name, text))
            .collect();
        let session = Session::new(&dir.0, None, Vec::new());
        session.reindex(&paths);
        (session, paths)
    }

    #[test]
    fn a_file_opens_without_anything_else_happening() {
        let dir = TempDir::new("open");
        let path = dir.write("A.cs", "class A { }\n");
        let session = Session::new(&dir.0, None, Vec::new());
        let document = session.open(&path).expect("it should open");
        assert_eq!(document.text(), "class A { }\n");
        // Opening is layer 1 and nothing else: no parse has happened.
        assert_eq!(session.statistics().computed, 0);
    }

    #[test]
    fn a_file_that_is_not_there_says_so() {
        let dir = TempDir::new("missing");
        let session = Session::new(&dir.0, None, Vec::new());
        assert!(matches!(
            session.open(dir.0.join("Gone.cs")),
            Err(Refusal::Io(_))
        ));
    }

    #[test]
    fn colouring_answers_in_the_units_the_editor_counts_in() {
        let dir = TempDir::new("utf16");
        // A comment in Cyrillic above the code: every byte offset below it is
        // ahead of its UTF-16 offset, so an editor given bytes would paint
        // everything in the wrong place.
        let text = "// комментарий\nclass A { }\n";
        let path = dir.write("A.cs", text);
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");

        let runs = session.classify(&path, 0, 1).expect("classify");
        let units: Vec<u16> = text.encode_utf16().collect();
        let class_run = runs
            .iter()
            .find(|run| run.class == Class::Keyword)
            .expect("the `class` keyword");
        let found = String::from_utf16_lossy(
            &units[class_run.start as usize..(class_run.start + class_run.length) as usize],
        );
        assert_eq!(found, "class");
    }

    #[test]
    fn colouring_a_file_that_is_not_csharp_is_refused_rather_than_guessed_at() {
        let dir = TempDir::new("notcs");
        let path = dir.write("main.rs", "fn main() {}\n");
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");
        assert_eq!(session.classify(&path, 0, 0), Err(Refusal::NotCsharp));
        assert_eq!(session.outline(&path), Err(Refusal::NotCsharp));
    }

    #[test]
    fn an_unopened_file_is_refused_rather_than_read_behind_the_callers_back() {
        let dir = TempDir::new("notopen");
        let path = dir.write("A.cs", "class A { }");
        let session = Session::new(&dir.0, None, Vec::new());
        assert_eq!(session.classify(&path, 0, 0), Err(Refusal::NotOpen));
        assert_eq!(session.outline(&path), Err(Refusal::NotOpen));
    }

    #[test]
    fn an_outline_is_computed_once_and_then_read() {
        let dir = TempDir::new("outline");
        let path = dir.write("A.cs", "class A { void M() { } }");
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");

        let first = session.outline(&path).expect("outline");
        assert_eq!(first.declarations.len(), 2);
        let computed = session.statistics().computed;
        let second = session.outline(&path).expect("outline");
        assert_eq!(
            session.statistics().computed,
            computed,
            "not computed twice"
        );
        assert!(Arc::ptr_eq(&first, &second), "and it is the same answer");
    }

    #[test]
    fn an_edit_makes_a_new_version_and_a_new_outline() {
        let dir = TempDir::new("edit");
        let path = dir.write("A.cs", "class A { }");
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");
        assert_eq!(
            session.outline(&path).expect("outline").declarations.len(),
            1
        );

        session
            .set_text(&path, "class A { void Added() { } }")
            .expect("edit");
        let outline = session.outline(&path).expect("outline");
        assert_eq!(outline.declarations.len(), 2);
        assert!(outline.declarations.iter().any(|d| d.name == "Added"));
    }

    #[test]
    fn editing_a_file_that_is_not_open_is_refused() {
        let dir = TempDir::new("editclosed");
        let session = Session::new(&dir.0, None, Vec::new());
        assert!(matches!(
            session.set_text(dir.0.join("A.cs"), "class A { }"),
            Err(Refusal::NotOpen),
        ));
    }

    #[test]
    fn going_to_a_definition_gives_a_place_in_the_editors_units() {
        let dir = TempDir::new("goto");
        let (session, paths) = project(
            &dir,
            &[
                (
                    "Pawn.cs",
                    "namespace Game;\nclass Pawn { public int Health; }\n",
                ),
                (
                    "Use.cs",
                    "namespace Game;\nclass Use { void M(Pawn p) { var n = p.Health; } }\n",
                ),
            ],
        );
        session.open(&paths[1]).expect("open");

        let text = std::fs::read_to_string(&paths[1]).expect("read");
        let offset = text.find("Health").expect("Health") as u32;
        let definition = session.definition(&paths[1], offset).expect("it resolves");

        assert!(definition.certain);
        assert_eq!(definition.word, "Health");
        assert_eq!(definition.targets.len(), 1);
        let target = &definition.targets[0];
        assert_eq!(target.path, Path::new("Pawn.cs"));
        assert_eq!(target.name, "Game.Pawn.Health");
        assert_eq!(target.line, 1);

        // And the column really points at the name.
        let pawn = std::fs::read_to_string(&paths[0]).expect("read");
        let line = pawn.lines().nth(target.line as usize).expect("the line");
        let units: Vec<u16> = line.encode_utf16().collect();
        let found = String::from_utf16_lossy(
            &units[target.character as usize..(target.character + target.length) as usize],
        );
        assert_eq!(found, "Health");
    }

    #[test]
    fn a_column_is_counted_in_utf16_even_when_the_line_is_not_ascii() {
        let dir = TempDir::new("gotoutf16");
        let (session, paths) = project(
            &dir,
            &[
                (
                    "Pawn.cs",
                    "namespace Game;\nclass Pawn { /* здоровье */ public int Health; }\n",
                ),
                (
                    "Use.cs",
                    "namespace Game;\nclass Use { void M(Pawn p) { var n = p.Health; } }\n",
                ),
            ],
        );
        session.open(&paths[1]).expect("open");
        let text = std::fs::read_to_string(&paths[1]).expect("read");
        let offset = text.find("Health").expect("Health") as u32;
        let target = &session
            .definition(&paths[1], offset)
            .expect("resolves")
            .targets[0];

        let pawn = std::fs::read_to_string(&paths[0]).expect("read");
        let line = pawn.lines().nth(target.line as usize).expect("the line");
        let units: Vec<u16> = line.encode_utf16().collect();
        let found = String::from_utf16_lossy(
            &units[target.character as usize..(target.character + target.length) as usize],
        );
        assert_eq!(found, "Health", "the column must be in UTF-16 units");
    }

    #[test]
    fn an_index_older_than_the_open_copy_still_gives_a_place() {
        let dir = TempDir::new("gotostale");
        let (session, paths) = project(&dir, &[("A.cs", "class A { }\nclass B { A a; }\n")]);
        // A line separator typed where the index has `A`: the offset it
        // keeps is now in the middle of a character.
        let edited = "class\u{2028}A { }\nclass B { A a; }\n";
        session.open_text(&paths[0], edited);

        let offset = edited[..edited.rfind("A a").expect("the use")]
            .encode_utf16()
            .count() as u32;
        let definition = session.definition(&paths[0], offset).expect("it resolves");
        let target = &definition.targets[0];
        assert_eq!(target.path, Path::new("A.cs"));
        assert_eq!((target.line, target.character), (0, 5));
    }

    #[test]
    fn asking_before_the_project_is_indexed_says_so() {
        let dir = TempDir::new("unindexed");
        let path = dir.write("A.cs", "class A { void M() { } }");
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");
        assert_eq!(session.definition(&path, 0), Err(Refusal::NotIndexed));
    }

    #[test]
    fn two_projects_share_one_decompiled_assembly() {
        let dir = TempDir::new("shared-assemblies");
        let assembly = PathBuf::from(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../rustlyn-decompile/tests/fixtures/roslyn_sample.dll"
        ));
        let shared = dir.0.join("assemblies");
        let files_in = |directory: &Path| {
            std::fs::read_dir(directory.join("assembly")).map_or(0, |entries| entries.count())
        };
        // Different projects, different symbols: neither changes what an
        // assembly says, so the second reads what the first wrote.
        for (name, symbols) in [("one", vec![]), ("two", vec!["UNITY_EDITOR".to_owned()])] {
            let session = Session::new(
                dir.0.join(name),
                Some(dir.0.join(name).join("cache")),
                symbols,
            );
            assert!(session.share_assembly_cache(shared.clone()));
            assert!(!session.share_assembly_cache(shared.clone()), "set once");
            let surface = session.assembly(&assembly).expect("readable");
            assert!(surface.text.contains("class Point"));
            assert_eq!(files_in(&dir.0.join(name).join("cache")), 0, "{name}");
        }
        assert_eq!(files_in(&shared), 1);
    }

    #[test]
    fn a_cursor_on_nothing_says_so_rather_than_answering() {
        let dir = TempDir::new("notaname");
        let (session, paths) = project(&dir, &[("A.cs", "class A { void M() { } }")]);
        session.open(&paths[0]).expect("open");
        // Offset 0 is the `class` keyword.
        assert_eq!(session.definition(&paths[0], 0), Err(Refusal::NotAName));
    }

    #[test]
    fn implementations_are_found_from_the_cursor() {
        let dir = TempDir::new("impls");
        let (session, paths) = project(
            &dir,
            &[
                ("I.cs", "namespace Game;\ninterface IThing { }\n"),
                ("A.cs", "namespace Game;\nclass Actor : IThing { }\n"),
                ("P.cs", "namespace Game;\nclass Pawn : Actor { }\n"),
            ],
        );
        session.open(&paths[0]).expect("open");
        let text = std::fs::read_to_string(&paths[0]).expect("read");
        let offset = text.find("IThing").expect("IThing") as u32;

        let mut names: Vec<String> = session
            .implementations(&paths[0], offset)
            .expect("it resolves")
            .into_iter()
            .map(|location| location.name)
            .collect();
        names.sort();
        assert_eq!(names, ["Game.Actor", "Game.Pawn"]);
    }

    #[test]
    fn reindexing_after_a_save_reads_the_rest_rather_than_reparsing_it() {
        let dir = TempDir::new("reindex");
        let (session, paths) = project(
            &dir,
            &[
                ("A.cs", "class A { }"),
                ("B.cs", "class B { }"),
                ("C.cs", "class C { }"),
            ],
        );
        std::thread::sleep(std::time::Duration::from_millis(10));
        dir.write("B.cs", "class B { public int Added; }");

        let report = session.reindex(&paths);
        assert_eq!(report.parsed, 1);
        assert_eq!(report.reused, 2);
        assert_eq!(session.index().by_name("Added").len(), 1);
    }

    #[test]
    fn an_assembly_that_is_not_one_is_refused_with_a_reason() {
        let dir = TempDir::new("notdll");
        let path = dir.write("fake.dll", "this is not a PE image");
        let session = Session::new(&dir.0, None, Vec::new());
        assert!(
            matches!(session.assembly(&path), Err(Refusal::Assembly(_))),
            "{:?}",
            session.assembly(&path).map(|_| ()),
        );
    }

    #[test]
    fn a_preprocessor_symbol_changes_what_is_indexed() {
        let dir = TempDir::new("symbols");
        let path = dir.write(
            "A.cs",
            "#if DEBUG\nclass OnlyInDebug { }\n#endif\nclass Always { }\n",
        );

        let plain = Session::new(&dir.0, None, Vec::new());
        plain.reindex(std::slice::from_ref(&path));
        assert_eq!(plain.index().by_name("OnlyInDebug").len(), 0);
        assert_eq!(plain.index().by_name("Always").len(), 1);

        let debugging = Session::new(&dir.0, None, vec!["DEBUG".to_owned()]);
        debugging.reindex(std::slice::from_ref(&path));
        assert_eq!(
            debugging.index().by_name("OnlyInDebug").len(),
            1,
            "the same file, read under different symbols, is different code",
        );
    }

    #[test]
    fn two_sessions_with_different_symbols_do_not_share_cached_answers() {
        let dir = TempDir::new("saltshare");
        let path = dir.write("A.cs", "#if DEBUG\nclass OnlyInDebug { }\n#endif\n");
        let store = dir.0.join("cache");

        let plain = Session::new(&dir.0, Some(store.clone()), Vec::new());
        plain.reindex(std::slice::from_ref(&path));
        assert_eq!(plain.index().len(), 0);

        let debugging = Session::new(&dir.0, Some(store), vec!["DEBUG".to_owned()]);
        debugging.reindex(std::slice::from_ref(&path));
        assert_eq!(
            debugging.index().len(),
            1,
            "the other session's answer must not be read as this one's",
        );
    }

    #[test]
    fn closing_a_file_forgets_it() {
        let dir = TempDir::new("close");
        let path = dir.write("A.cs", "class A { }");
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");
        assert!(session.document(&path).is_some());
        session.close(&path);
        assert!(session.document(&path).is_none());
        assert_eq!(session.classify(&path, 0, 0), Err(Refusal::NotOpen));
    }

    #[test]
    fn a_buffer_that_was_never_on_disk_still_works() {
        let dir = TempDir::new("untitled");
        let session = Session::new(&dir.0, None, Vec::new());
        let path = dir.0.join("Untitled.cs");
        session.open_text(&path, "class Draft { void M() { } }");
        let outline = session.outline(&path).expect("outline");
        assert_eq!(outline.declarations.len(), 2);
    }

    #[test]
    fn warming_makes_a_far_jump_as_cheap_as_a_scroll() {
        let dir = TempDir::new("warm");
        let text: String = (0..3000).map(|n| format!("// line {n}\n")).collect();
        let path = dir.write("Big.cs", &text);
        let session = Session::new(&dir.0, None, Vec::new());
        session.open(&path).expect("open");
        session.warm(&path).expect("warm");
        // What matters is that it answers; the cost is measured elsewhere.
        assert!(
            !session
                .classify(&path, 2900, 2910)
                .expect("classify")
                .is_empty()
        );
    }

    #[test]
    fn a_compiled_project_answers_in_the_editors_units() {
        let dir = TempDir::new("compiled");
        // Cyrillic above the code: every byte offset below it is ahead of its
        // UTF-16 offset.
        let player = "// игрок\nclass Player { public int Health; public void Heal(int by) { } }\n";
        let game = "// игра\nclass Game { void Run(Player p) { p.Heal(1); var h = p.Health; } }\n";
        let (session, paths) = project(&dir, &[("Player.cs", player), ("Game.cs", game)]);
        let compiled = session.compile(&paths);
        assert_eq!(compiled.files, 2);

        let units = |text: &str, marker: &str| -> u32 {
            text[..text.find(marker).expect("marker")]
                .encode_utf16()
                .count() as u32
        };
        let game_path = dir.0.join("Game.cs");
        session.open(&game_path).expect("open");

        let definition = session
            .definition(&game_path, units(game, "Heal(1)"))
            .expect("resolved");
        assert!(definition.certain);
        let target = &definition.targets[0];
        assert_eq!(target.path, PathBuf::from("Player.cs"));
        assert_eq!(
            (target.line, target.character),
            (1, units(player.lines().nth(1).expect("line"), "Heal(int"))
        );

        let uses = session
            .references(dir.0.join("Player.cs"), units(player, "Health"), None)
            .expect("found");
        assert_eq!(uses.locations.len(), 2, "{uses:?}");

        // A dot typed and not saved.
        let typed = game.replace("var h = p.Health;", "var h = p.Health; p.");
        let completions = session
            .completions(&game_path, units(&typed, "p. }") + 2, Some(&typed))
            .expect("completed");
        assert_eq!(completions.start, units(&typed, "p. }") + 2);
        assert!(completions.items.iter().any(|item| item.label == "Heal"));

        assert_eq!(
            session
                .describe(&game_path, units(game, "Heal(1)"), None)
                .as_deref(),
            Ok("void Heal(int by)")
        );
    }

    #[test]
    fn before_compiling_the_index_still_answers() {
        let dir = TempDir::new("uncompiled");
        let (session, _) = project(
            &dir,
            &[("A.cs", "class A { B b; }\n"), ("B.cs", "class B { }\n")],
        );
        let path = dir.0.join("A.cs");
        session.open(&path).expect("open");
        let definition = session.definition(&path, 11).expect("the index knows");
        assert_eq!(definition.targets[0].path, PathBuf::from("B.cs"));
        assert_eq!(
            session.references(&path, 11, None),
            Err(Refusal::NotCompiled)
        );
    }

    #[test]
    fn a_compilation_survives_the_session_and_is_kept_while_nothing_changes() {
        let dir = TempDir::new("snapshot");
        let cache = dir.0.join(".cache");
        let player = "class Player { public int Health; }\n";
        let game = "class Game { void Run(Player p) { var h = p.Health; } }\n";
        let paths = vec![dir.write("Player.cs", player), dir.write("Game.cs", game)];

        let first = Session::new(&dir.0, Some(cache.clone()), Vec::new());
        first.reindex(&paths);
        assert!(!first.compile(&paths).unchanged);
        assert!(
            first.compile(&paths).unchanged,
            "the same files compile to the same thing"
        );
        assert_eq!(first.save_compilation().ok(), Some(true));
        assert_eq!(
            first.save_compilation().ok(),
            Some(false),
            "nothing new to write"
        );
        drop(first);

        let second = Session::new(&dir.0, Some(cache.clone()), Vec::new());
        let loaded = second.load_compilation().expect("the snapshot reads back");
        assert_eq!(loaded.files, 2);
        let game_path = dir.0.join("Game.cs");
        second.open(&game_path).expect("open");
        let offset = game[..game.find("Health").expect("marker")]
            .encode_utf16()
            .count() as u32;
        let definition = second
            .definition(&game_path, offset)
            .expect("answers before compiling");
        assert_eq!(definition.targets[0].path, PathBuf::from("Player.cs"));
        second.reindex(&paths);
        assert!(
            second.compile(&paths).unchanged,
            "and compiling finds it current"
        );

        // A change on disk is noticed and compiled.
        dir.write(
            "Player.cs",
            "class Player { public int Health; public int Mana; }\n",
        );
        assert!(!second.compile(&paths).unchanged);
        assert!(
            second.load_compilation().is_none(),
            "a compilation in hand is not replaced"
        );
    }
}

/// A session is handed to more than one thread on purpose: the editor's own
/// thread asks for colour while a background one indexes and warms. Nothing
/// here is `unsafe`, so the compiler works this out by itself — but it works
/// it out silently, and a field added later that breaks it would break the
/// callers rather than the build. This makes it break the build.
#[cfg(test)]
mod thread_safety {
    const fn assert_shareable<T: Send + Sync>() {}

    #[test]
    fn a_session_can_be_shared_across_threads() {
        assert_shareable::<super::Session>();
        assert_shareable::<std::sync::Arc<super::Session>>();
    }
}
