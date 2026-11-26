//! A compilation: the syntax trees, the symbols they declare, and the answers
//! that need all of them at once.

use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, RwLock};
use std::thread::ThreadId;

use rustlyn_diagnostics::Diagnostic;
use rustlyn_syntax::{LanguageVersion, ParseOptions, SyntaxTree, parse, parse_with};
use rustlyn_text::{SourceText, TextSpan};

use crate::binder::Import;
use crate::bound::ConstantValue;
use crate::corlib::{CORLIB_SOURCE, SpecialType};
use crate::declare::{Declared, Declarer, TreeFacts, TreeSource};
use crate::metadata::{Loaded, Reference};
use crate::symbol::{Accessibility, Modifiers, SymbolId, SymbolKind, Symbols, TypeKind};
use crate::trees::Trees;
use crate::types::Type;

/// A diagnostic together with the file it belongs to.
///
/// A [`Diagnostic`] carries only a span, which is enough inside one file and
/// not enough across several.
#[derive(Clone, Debug)]
pub struct CompilationDiagnostic {
    pub tree: usize,
    pub diagnostic: Diagnostic,
}

/// Where a scope's `using` directives are: the tree, and the span and kind
/// of the node that holds them.
pub(crate) type ImportsKey = (usize, TextSpan, rustlyn_syntax::SyntaxKind);

/// How a compilation is to be built, as the command line sets it: the
/// counterpart of Roslyn's `CSharpCompilationOptions`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompilationOptions {
    /// The type whose `Main` starts the program (`/main:`), when more than
    /// one type has one.
    pub main_type_name: Option<String>,
    /// Whether integer arithmetic outside any `checked`/`unchecked` is
    /// checked (`/checked`).
    pub check_overflow: bool,
    /// Whether the code is optimized (`/optimize`).
    pub optimize: bool,
    /// Whether `unsafe` code is allowed (`/unsafe`).
    pub allow_unsafe: bool,
    /// Whether reference types are annotated where no `#nullable` says
    /// otherwise (`/nullable:enable` or `/nullable:annotations`): `string`
    /// is then not null and `string?` may be.
    pub nullable_annotations: bool,
    /// Whether a `readonly` field may be written outside its type's
    /// constructors — what a hot patch does, a constructor patched being a
    /// static method of another assembly. The runtime does not hold a
    /// store to an `initonly` field against it; only C# does.
    pub writes_readonly_fields: bool,
}

/// Everything being compiled together.
#[derive(Debug)]
pub struct Compilation {
    pub(crate) trees: Trees,
    /// The trees that hold a `global using`, which every other tree sees.
    /// Kept so that working the imports out does not mean parsing every
    /// file of a compilation read back from disk.
    pub(crate) global_using_trees: Vec<usize>,
    pub(crate) symbols: Symbols,
    pub(crate) global: SymbolId,
    pub(crate) diagnostics: Vec<CompilationDiagnostic>,
    /// Each special type, by its discriminant.
    pub(crate) special_types: [Option<SymbolId>; SpecialType::ALL.len()],
    /// What each of [`WELL_KNOWN`] names, found once when the compilation is
    /// made: these are asked for millions of times — `System.Object` at
    /// every step of every inheritance walk — and from every thread at
    /// once, which a cache behind a lock turns into a queue.
    pub(crate) well_known: [Option<SymbolId>; WELL_KNOWN.len()],
    pub(crate) declarations: HashMap<(usize, TextSpan), SymbolId>,
    pub(crate) declaration_nodes: HashMap<SymbolId, Vec<(usize, TextSpan)>>,
    /// The class declared for each anonymous object shape, by property names.
    pub(crate) anonymous_types: HashMap<Vec<String>, SymbolId>,
    /// How many of the trees are the synthesised core library, which come
    /// first and are not the user's code.
    pub(crate) corlib_trees: usize,
    /// The types of symbols that came from an assembly rather than from
    /// syntax, which is where their types have to live: there is no tree for a
    /// [`TypeSyntaxRef`] to point into.
    ///
    /// [`TypeSyntaxRef`]: crate::symbol::TypeSyntaxRef
    pub(crate) loaded: Loaded,
    /// The first symbol a referenced assembly contributed. Everything from
    /// here up came out of metadata, which is the cheapest way to ask.
    pub(crate) metadata_floor: usize,
    /// What each type extends and implements, worked out once.
    ///
    /// This is a property of the compilation and not of whoever asked, so it
    /// lives here rather than in a [`Binder`]: a binder is made per file, and
    /// a thousand files asking a thousand times what `SyntaxNode` derives from
    /// is a thousand times too many.
    ///
    /// [`Binder`]: crate::Binder
    pub(crate) base_types: SymbolCache<Vec<Type>>,
    /// The types whose base types are being worked out right now, which is how
    /// `class A : A` stops instead of recursing.
    ///
    /// Per thread: an editor asks from several at once, and a type another
    /// thread happens to be resolving is not a cycle on this one.
    pub(crate) resolving: Mutex<HashSet<(ThreadId, SymbolId)>>,
    /// The `using` directives of each scope, resolved once, by the tree, the
    /// span and the kind of the node they are in: a file that is one
    /// namespace declaration and nothing else has a compilation unit of the
    /// very span of the declaration, and the two have `using`s of their own.
    pub(crate) imports: RwLock<HashMap<ImportsKey, Vec<Import>>>,
    /// The `global using` directives of every file, resolved once.
    pub(crate) global_imports: RwLock<Option<Vec<Import>>>,
    /// Which `op_Implicit` takes one type to another, worked out once.
    ///
    /// The question is asked for every conversion that nothing standard
    /// covers, which in a large compilation is most of the failures, and the
    /// answer is usually that there is none.
    pub(crate) conversions: RwLock<HashMap<(Type, Type), Option<SymbolId>>>,
    /// The value of every `const` field and enum member asked about so far.
    ///
    /// An enum member with no initializer is one more than the member before
    /// it, so working one out means working out every member before it — and
    /// each of those means binding an initializer, which may name another
    /// member and start the walk again. Roslyn's `UnaryOperatorKind` has four
    /// hundred members written in terms of each other, and without this it
    /// takes longer to emit that one file than to emit eight hundred others.
    pub(crate) constants: RwLock<HashMap<SymbolId, Option<ConstantValue>>>,
    /// The circles of constants defined in terms of themselves; see
    /// [`Self::note_circular_constants`].
    pub(crate) circular_constants: RwLock<std::collections::BTreeSet<Vec<SymbolId>>>,
    /// Every extension method, by name.
    ///
    /// An extension method is found by the name at the call site rather than
    /// by the type of the receiver, so this is the only index that helps: the
    /// scope rules then cut the list down to what the file can see.
    pub(crate) extensions: HashMap<String, Vec<SymbolId>>,
    /// The properties, indexers and static methods of extension blocks
    /// (C# 14), by name.
    pub(crate) extension_members: HashMap<String, Vec<SymbolId>>,
    /// Every declaration of the source marked `[Obsolete]`, found once
    /// when a body first asks.
    pub(crate) obsolete: std::sync::OnceLock<HashMap<SymbolId, crate::obsolete::Obsolete>>,
    /// What each metadata name asked about so far names.
    ///
    /// `System.Object` is asked for at every step of every inheritance walk;
    /// splitting the name and walking the namespaces each time was most of
    /// what binding a file full of overloads cost.
    pub(crate) metadata_names: RwLock<HashMap<String, Option<SymbolId>>>,
    /// Whether one type derives from or implements another, once walked.
    pub(crate) inheritance: RwLock<HashMap<(Type, Type), bool>>,
    /// Whether one type converts implicitly to another, once classified.
    /// Overload resolution asks the same pairs over and over: every
    /// argument against every parameter of every candidate.
    pub(crate) implicit_conversions: RwLock<HashMap<(Type, Type), bool>>,
    /// The declared type of each source symbol asked about so far.
    ///
    /// Resolving one means finding its syntax from the root of its tree and
    /// rebuilding the scopes around it; a parameter's type is asked for at
    /// every call that considers its method, which is every call by that
    /// name.
    pub(crate) symbol_types: SymbolCache<Type>,
    /// The delegate types bodies have needed synthesized so far.
    pub(crate) anonymous_delegates: Mutex<crate::delegates::AnonymousDelegates>,
    /// How the compilation is to be built.
    pub(crate) options: CompilationOptions,
    /// The `[OverloadResolutionPriority]` of every member of the source that
    /// has one, found when overload resolution first asks.
    pub(crate) priorities: std::sync::OnceLock<HashMap<SymbolId, i32>>,
    /// Which of the assemblies the compilation was made as each tree goes
    /// into, as an index into those names, for an editor compiling several
    /// projects at once. A tree past the end, or at `u16::MAX`, is any of
    /// them.
    pub(crate) tree_assemblies: Vec<u16>,
    /// Which assemblies of those the compilation was made as each one
    /// references, by index (see [`Compilation::set_assembly_references`]).
    pub(crate) assembly_references: Vec<Vec<u16>>,
    /// Whether code of an assembly sees a namespace, once worked out.
    pub(crate) namespaces_seen: RwLock<HashMap<(SymbolId, u16), bool>>,
    /// Which assemblies each one shows its source's internals to, by index.
    pub(crate) source_friends: Vec<Vec<u16>>,
    /// The precompiled assemblies each assembly references, by lowercased
    /// file stem (see [`Compilation::set_metadata_references`]).
    pub(crate) metadata_references: Vec<Vec<String>>,
    /// Which assemblies annotate their reference types where no `#nullable`
    /// says (see [`Compilation::set_assembly_nullable`]).
    pub(crate) assembly_nullable: Vec<bool>,
    /// More assemblies a tree goes into besides its own, by tree: generated
    /// code several assemblies had a copy of.
    pub(crate) tree_assemblies_also: HashMap<usize, Vec<u16>>,
}

impl Compilation {
    /// The same compilation, built with `options`.
    #[must_use]
    pub fn with_options(mut self, options: CompilationOptions) -> Self {
        self.options = options;
        self
    }

    /// How the compilation is to be built.
    #[must_use]
    pub const fn options(&self) -> &CompilationOptions {
        &self.options
    }

    /// The version of C# the compilation is held to: that of its source
    /// files (Roslyn requires them all to agree), or the latest when it has
    /// none.
    #[must_use]
    pub fn language_version(&self) -> LanguageVersion {
        self.trees
            .iter()
            .skip(self.corlib_trees)
            .map(SyntaxTree::language_version)
            .next()
            .unwrap_or_default()
    }

    /// The name a type has in metadata: `List`1` for `List<T>`, and for a
    /// file-local type that name after `<File>F<hash>__`, the file's name
    /// and the SHA-256 of its path — Roslyn's
    /// `MakeFileTypeMetadataNamePrefix`, which keeps two files' `file
    /// class C` apart.
    #[must_use]
    pub fn metadata_name_of(&self, id: SymbolId) -> String {
        let symbol = self.symbols.get(id);
        let name = symbol.metadata_name();
        let Some(tree) = self.symbols.file_of(id) else {
            return name;
        };
        let path = self.trees.get(tree).map_or("", |tree| tree.source().name());
        let file = path.rsplit(['/', '\\']).next().unwrap_or_default();
        let stem = file.rfind('.').map_or(file, |dot| &file[..dot]);
        let mut prefix = String::from("<");
        prefix.extend(
            stem.chars()
                .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' }),
        );
        prefix.push_str(">F");
        for byte in crate::sha256::sha256(path.as_bytes()) {
            prefix.push_str(&format!("{byte:02X}"));
        }
        format!("{prefix}__{name}")
    }

    /// Compiles `trees` against the synthesised core library.
    #[must_use]
    pub fn create(trees: Vec<SyntaxTree>) -> Self {
        let corlib = parse(SourceText::new("<corlib>", CORLIB_SOURCE));
        let mut all = vec![corlib];
        all.extend(trees);
        Self::build(all, 1, &[], &[], &[])
    }

    /// Compiles `trees` against real assemblies rather than the synthesised
    /// core library.
    ///
    /// This is what a compiler actually does: `System.Object` is not a piece
    /// of source it knows by heart, it is a row in a table in a file the user
    /// named on the command line.
    #[must_use]
    pub fn create_with_references(trees: Vec<SyntaxTree>, references: &[&[u8]]) -> Self {
        Self::build(trees, 0, references, &[], &[])
    }

    /// The same, for an assembly that will be named `name`: a reference that
    /// names it in an `[InternalsVisibleTo]` shows it its internal types and
    /// members, as it would its own.
    #[must_use]
    pub fn create_with_references_as(
        trees: Vec<SyntaxTree>,
        references: &[&[u8]],
        name: &str,
    ) -> Self {
        Self::build(trees, 0, references, &[], &[name])
    }

    /// The same, for source that goes into any of several assemblies, as an
    /// editor compiling every project of a solution at once does: a
    /// reference that names one of them in an `[InternalsVisibleTo]` shows
    /// its internals to all of the source, as each project's internals are
    /// already seen by the others there.
    #[must_use]
    pub fn create_with_references_as_any(
        trees: Vec<SyntaxTree>,
        references: &[&[u8]],
        names: &[&str],
    ) -> Self {
        Self::build(trees, 0, references, &[], names)
    }

    /// The same, with the `extern alias` names each reference is given, in
    /// the same order (`/r:A=x.dll`). A reference given none is seen from
    /// the global namespace, as any other is.
    #[must_use]
    pub fn create_with_aliased_references(
        trees: Vec<SyntaxTree>,
        references: &[&[u8]],
        aliases: &[Vec<String>],
    ) -> Self {
        Self::build(trees, 0, references, aliases, &[])
    }

    /// The namespace an `extern alias` names, where a reference was given it.
    #[must_use]
    pub fn extern_alias(&self, name: &str) -> Option<SymbolId> {
        self.loaded.extern_aliases.get(name).copied()
    }

    /// Compiles `trees` on their own, for tests that want to see exactly what
    /// the source declares.
    #[must_use]
    pub fn create_without_corlib(trees: Vec<SyntaxTree>) -> Self {
        Self::build(trees, 0, &[], &[], &[])
    }

    /// Compiles one snippet, the shortest path from text to symbols.
    #[must_use]
    pub fn from_source(text: &str) -> Self {
        Self::create(vec![parse(SourceText::new("Program.cs", text))])
    }

    /// Parses `sources` and compiles them against real assemblies, as
    /// [`Compilation::create_with_references`] does with trees already parsed.
    ///
    /// The files are parsed on every core, and declared on this thread as
    /// they come: declaring goes through the files in order, and the first
    /// ones are parsed long before the last, so by the time the declarations
    /// are done most of the parsing has been done beside them.
    ///
    /// # Panics
    ///
    /// Panics where parsing a file does, or where a thread cannot be started.
    #[must_use]
    pub fn parse_with_references(
        sources: Vec<SourceText>,
        options: &ParseOptions,
        references: &[&[u8]],
    ) -> Self {
        let queue = ParseQueue::new(sources, options);
        let parsing = crate::timing::phase("parse and declare");
        let declared = std::thread::scope(|scope| {
            // This thread declares, and parses too whenever the file it is
            // up to is not ready, so one core fewer parses throughout.
            for _ in 0..crate::parallel::threads().saturating_sub(1).max(1) {
                std::thread::Builder::new()
                    .stack_size(crate::parallel::PARSE_STACK)
                    .spawn_scoped(scope, || while queue.parse_next() {})
                    .expect("a parsing thread should start");
            }
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let mut declarer = Declarer::new(TreeSource::Parsing(&queue));
                declarer.declare_all();
                Declared::from(declarer)
            }))
        });
        drop(parsing);
        // A file that did not parse is the first thing to report; the
        // declarations stopping at its empty slot is only a consequence.
        if let Some(panic) = lock(&queue.failure).take() {
            std::panic::resume_unwind(panic);
        }
        let declared = declared.unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        let trees = queue
            .slots
            .into_iter()
            .map(|slot| {
                slot.into_inner()
                    .flatten()
                    .expect("every file should have parsed")
                    .0
            })
            .collect();
        Self::assemble(trees, 0, references, &[], declared, &[])
    }

    fn build(
        trees: Vec<SyntaxTree>,
        corlib_trees: usize,
        references: &[&[u8]],
        aliases: &[Vec<String>],
        names: &[&str],
    ) -> Self {
        let declaring = crate::timing::phase("declare");
        let gathering = crate::timing::phase("tree facts");
        let facts = crate::parallel::map(&trees, TreeFacts::of);
        drop(gathering);
        let walking = crate::timing::phase("declare trees");
        let mut declarer = Declarer::new(TreeSource::Parsed(&trees, &facts));
        declarer.declare_all();
        drop(walking);
        let declared = Declared::from(declarer);
        drop(declaring);
        Self::assemble(trees, corlib_trees, references, aliases, declared, names)
    }

    /// The rest of making a compilation, once its trees are declared.
    fn assemble(
        trees: Vec<SyntaxTree>,
        corlib_trees: usize,
        references: &[&[u8]],
        aliases: &[Vec<String>],
        declared: Declared,
        names: &[&str],
    ) -> Self {
        let Declared {
            mut symbols,
            global,
            diagnostics: declaration_diagnostics,
            declarations,
            anonymous: anonymous_types,
        } = declared;
        // The source is declared first, so every symbol from here up came out
        // of a referenced assembly.
        let metadata_floor = symbols.len();
        let loading = crate::timing::phase("load references");
        let loaded = crate::metadata::load(&mut symbols, global, references, aliases, names);
        drop(loading);
        // A record over a referenced record could not see it while it was
        // declared: what it inherits is settled now that it can.
        let settling = crate::timing::phase("settle records");
        let declared: std::collections::HashSet<SymbolId> =
            declarations.values().copied().collect();
        crate::declare::settle_records_over_references(
            &mut symbols,
            metadata_floor,
            &declared,
            &loaded.bases,
            &trees,
        );

        drop(settling);
        let gathering = crate::timing::phase("gather diagnostics");
        // Syntax errors first, in file order, then what the declaration pass
        // found: the order a compiler reports them in.
        let mut diagnostics: Vec<_> = trees
            .iter()
            .enumerate()
            .flat_map(|(tree, syntax)| {
                syntax
                    .diagnostics()
                    .iter()
                    .map(move |diagnostic| CompilationDiagnostic {
                        tree,
                        diagnostic: diagnostic.clone(),
                    })
            })
            .collect();
        diagnostics.extend(
            declaration_diagnostics
                .into_iter()
                .map(|(tree, diagnostic)| CompilationDiagnostic { tree, diagnostic }),
        );

        let global_using_trees = trees
            .iter()
            .enumerate()
            .filter(|(_, tree)| has_global_using(tree))
            .map(|(index, _)| index)
            .collect();
        drop(gathering);
        let indexing = crate::timing::phase("derive indexes");
        let mut compilation = Self {
            trees: Trees::parsed(trees),
            global_using_trees,
            symbols,
            global,
            diagnostics,
            special_types: [None; SpecialType::ALL.len()],
            well_known: [None; WELL_KNOWN.len()],
            declarations,
            declaration_nodes: HashMap::new(),
            anonymous_types,
            corlib_trees,
            loaded,
            metadata_floor,
            base_types: SymbolCache::new(metadata_floor),
            resolving: Mutex::new(HashSet::new()),
            extensions: HashMap::new(),
            extension_members: HashMap::new(),
            conversions: RwLock::new(HashMap::new()),
            constants: RwLock::new(HashMap::new()),
            circular_constants: RwLock::new(std::collections::BTreeSet::new()),
            imports: RwLock::new(HashMap::new()),
            global_imports: RwLock::new(None),
            obsolete: std::sync::OnceLock::new(),
            metadata_names: RwLock::new(HashMap::new()),
            inheritance: RwLock::new(HashMap::new()),
            implicit_conversions: RwLock::new(HashMap::new()),
            symbol_types: SymbolCache::new(metadata_floor),
            anonymous_delegates: Mutex::new(crate::delegates::AnonymousDelegates::default()),
            options: CompilationOptions::default(),
            priorities: std::sync::OnceLock::new(),
            tree_assemblies: Vec::new(),
            assembly_references: Vec::new(),
            namespaces_seen: RwLock::new(HashMap::new()),
            source_friends: Vec::new(),
            metadata_references: Vec::new(),
            assembly_nullable: Vec::new(),
            tree_assemblies_also: HashMap::new(),
        };
        compilation.derive_indexes();
        drop(indexing);
        compilation
    }

    /// The indexes worked out from the symbols and declarations rather than
    /// kept: which nodes declare each symbol, every extension method by name,
    /// and where the special types are.
    pub(crate) fn derive_indexes(&mut self) {
        let mut declaration_nodes: HashMap<SymbolId, Vec<(usize, TextSpan)>> = HashMap::new();
        for ((tree, span), symbol) in &self.declarations {
            declaration_nodes
                .entry(*symbol)
                .or_default()
                .push((*tree, *span));
        }
        // Several files may declare one partial type; keep them in file order.
        for nodes in declaration_nodes.values_mut() {
            nodes.sort_unstable();
        }
        self.declaration_nodes = declaration_nodes;
        let mut extensions: HashMap<String, Vec<SymbolId>> = HashMap::new();
        for symbol in self.symbols.iter() {
            if symbol.as_method().is_some_and(|detail| detail.is_extension) {
                extensions
                    .entry(symbol.name.clone())
                    .or_default()
                    .push(symbol.id);
            }
        }
        self.extensions = extensions;
        let mut members: HashMap<String, Vec<SymbolId>> = HashMap::new();
        for symbol in self.symbols.iter() {
            let extended = match &symbol.detail {
                crate::symbol::Detail::Property(detail) => detail.extended.is_some(),
                crate::symbol::Detail::Method(detail) => {
                    detail.extended.is_some() && !detail.is_extension
                }
                _ => false,
            };
            if extended {
                members
                    .entry(symbol.name.clone())
                    .or_default()
                    .push(symbol.id);
            }
        }
        self.extension_members = members;
        self.well_known = [None; WELL_KNOWN.len()];
        let well_known = WELL_KNOWN.map(|name| self.type_by_metadata_name_uncached(name));
        self.well_known = well_known;
        let mut special_types = [None; SpecialType::ALL.len()];
        for special in SpecialType::ALL {
            // `int` is the core library's `System.Int32` even where the
            // program declares a `System.Int32` of its own, as Roslyn's
            // special types always come from the core library.
            let name = special.metadata_name();
            special_types[*special as usize] = self
                .core_library_type(name)
                .or_else(|| self.type_by_metadata_name(name));
        }
        self.special_types = special_types;
    }

    /// A top-level type of the core library or a referenced assembly by its
    /// metadata name, passing over one the source declares by that name.
    fn core_library_type(&self, name: &str) -> Option<SymbolId> {
        let (namespace_path, type_name) = name.rsplit_once('.').unwrap_or(("", name));
        let mut container = self.global;
        if !namespace_path.is_empty() {
            for part in namespace_path.split('.') {
                container = self.symbols.lookup_namespace(container, part)?;
            }
        }
        let (type_name, arity) = match type_name.rsplit_once('`') {
            Some((name, arity)) => (name, arity.parse().unwrap_or(0)),
            None => (type_name, 0),
        };
        self.symbols
            .lookup(container, type_name)
            .iter()
            .copied()
            .find(|id| {
                let symbol = self.symbols.get(*id);
                symbol.kind == SymbolKind::NamedType
                    && symbol
                        .as_named_type()
                        .is_some_and(|detail| detail.arity == arity)
                    && self.is_from_corlib(*id)
            })
    }

    /// The trees, parsed as they are asked for.
    #[must_use]
    pub const fn trees(&self) -> &Trees {
        &self.trees
    }

    /// The trees the caller handed over, without the core library.
    #[must_use]
    pub fn source_trees(&self) -> Vec<&SyntaxTree> {
        (self.corlib_trees..self.trees.len())
            .filter_map(|index| self.trees.get(index))
            .collect()
    }

    /// The trees that declare a `global using`.
    #[must_use]
    pub fn global_using_trees(&self) -> &[usize] {
        &self.global_using_trees
    }

    #[must_use]
    pub const fn symbols(&self) -> &Symbols {
        &self.symbols
    }

    #[must_use]
    pub const fn global_namespace(&self) -> SymbolId {
        self.global
    }

    #[must_use]
    pub fn diagnostics(&self) -> &[CompilationDiagnostic] {
        &self.diagnostics
    }

    /// Diagnostics from the user's files, leaving the core library's out.
    #[must_use]
    pub fn source_diagnostics(&self) -> Vec<&CompilationDiagnostic> {
        self.diagnostics
            .iter()
            .filter(|entry| entry.tree >= self.corlib_trees)
            .collect()
    }

    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|entry| entry.diagnostic.is_error())
    }

    /// Renders a diagnostic with the name and position of its file.
    #[must_use]
    pub fn render(&self, entry: &CompilationDiagnostic) -> String {
        entry
            .diagnostic
            .display_with(self.trees[entry.tree].source())
            .to_string()
    }

    /// The type named by a metadata name such as
    /// `System.Collections.Generic.List\`1`.
    #[must_use]
    pub fn type_by_metadata_name(&self, name: &str) -> Option<SymbolId> {
        if let Some(index) = WELL_KNOWN.iter().position(|known| *known == name) {
            return self.well_known[index];
        }
        if let Some(found) = read(&self.metadata_names).get(name) {
            return *found;
        }
        let found = self.type_by_metadata_name_uncached(name);
        write(&self.metadata_names).insert(name.to_string(), found);
        found
    }

    fn type_by_metadata_name_uncached(&self, name: &str) -> Option<SymbolId> {
        let (namespace_path, type_name) = match name.rsplit_once('.') {
            Some((namespace, type_name)) => (namespace, type_name),
            None => ("", name),
        };

        let mut container = self.global;
        if !namespace_path.is_empty() {
            for part in namespace_path.split('.') {
                container = self.symbols.lookup_namespace(container, part)?;
            }
        }

        // `Outer+Inner` names a nested type, and each step is looked up in
        // what the step before it found.
        let mut found = None;
        for part in type_name.split('+') {
            // `List\`1` says both the name and how many type parameters.
            let (part, arity) = match part.rsplit_once('`') {
                Some((name, arity)) => (name, arity.parse().unwrap_or(0)),
                None => (part, 0),
            };
            container = self.symbols.lookup_type(container, part, arity)?;
            found = Some(container);
        }
        found
    }

    /// The type of a symbol that came out of metadata, which is worked out
    /// when its assembly is read rather than when its syntax is bound.
    #[must_use]
    pub fn metadata_type(&self, symbol: SymbolId) -> Option<&Type> {
        self.loaded.types.get(&symbol)
    }

    /// The value of a `const` field read out of a referenced assembly.
    ///
    /// A literal field has no storage: `char.MaxValue` is the value, and
    /// loading it would look for a field that is not there.
    #[must_use]
    pub fn metadata_constant(&self, symbol: SymbolId) -> Option<&ConstantValue> {
        self.loaded.constants.get(&symbol)
    }

    /// What a COM attribute on a parameter read from metadata makes of it,
    /// were it an `[Optional] object` a call leaves out.
    #[must_use]
    pub fn metadata_com_default(&self, parameter: SymbolId) -> Option<crate::metadata::ComDefault> {
        self.loaded.com_defaults.get(&parameter).copied()
    }

    /// The `decimal` or `DateTime` constant a referenced assembly writes as
    /// an attribute on a field or a parameter.
    #[must_use]
    pub fn metadata_special_constant(
        &self,
        symbol: SymbolId,
    ) -> Option<crate::bound::SpecialConstant> {
        self.loaded.special_constants.get(&symbol).copied()
    }

    /// Whether a parameter read from metadata is `in` under a
    /// `modreq(InAttribute)`, rather than only marked `[In]`.
    #[must_use]
    pub fn metadata_in_modifier(&self, parameter: SymbolId) -> bool {
        self.loaded.in_modifiers.contains(&parameter)
    }

    /// The priority `[OverloadResolutionPriority(n)]` gives a member, from
    /// the source or a referenced assembly: 0 without one.
    #[must_use]
    pub fn overload_resolution_priority(&self, member: SymbolId) -> i32 {
        crate::priority::priority(self, member)
    }

    /// The `InAttribute` that the `modreq` on a metadata parameter, or on a
    /// metadata member's return, names, where that is not the framework's.
    #[must_use]
    pub fn metadata_modifier_type(&self, symbol: SymbolId) -> Option<SymbolId> {
        self.loaded.modifier_types.get(&symbol).copied()
    }

    /// The custom modifiers a metadata parameter's type, or a metadata
    /// member's return, carries in its signature.
    #[must_use]
    pub fn metadata_modifiers(
        &self,
        symbol: SymbolId,
    ) -> Option<&[crate::metadata::SignatureModifier]> {
        self.loaded.custom_modifiers.get(&symbol).map(Vec::as_slice)
    }

    /// The default value of an optional parameter read from metadata.
    #[must_use]
    pub fn metadata_parameter_default(&self, parameter: SymbolId) -> Option<&ConstantValue> {
        self.loaded.parameter_defaults.get(&parameter)
    }

    /// The struct a `fixed` buffer field read from metadata is of.
    #[must_use]
    pub fn metadata_fixed_buffer(&self, field: SymbolId) -> Option<SymbolId> {
        self.loaded.fixed_buffers.get(&field).copied()
    }

    /// The symbols a `[Conditional("...")]` in a referenced assembly names.
    #[must_use]
    pub fn metadata_conditions(&self, symbol: SymbolId) -> Option<&[String]> {
        self.loaded.conditions.get(&symbol).map(Vec::as_slice)
    }

    /// The class the language declared for `new { ... }` with these member
    /// names, in this order.
    #[must_use]
    pub fn anonymous_type(&self, names: &[String]) -> Option<SymbolId> {
        self.anonymous_types.get(names).copied()
    }

    /// The member names of an anonymous type, in order, where the class is
    /// one the language declared for `new { ... }`.
    #[must_use]
    pub fn anonymous_names(&self, symbol: SymbolId) -> Option<&[String]> {
        self.anonymous_types
            .iter()
            .find(|(_, declared)| **declared == symbol)
            .map(|(names, _)| names.as_slice())
    }

    /// What a metadata type extends and implements.
    #[must_use]
    pub fn metadata_bases(&self, symbol: SymbolId) -> Option<&[Type]> {
        self.loaded.bases.get(&symbol).map(Vec::as_slice)
    }

    /// The base types of `ty`, or `None` if they have not been worked out.
    ///
    /// The second answer says whether the caller may work them out: a type
    /// already on the stack gets an empty list rather than an infinite one.
    pub(crate) fn cached_base_types(&self, ty: SymbolId) -> Option<Vec<Type>> {
        if let Some(cached) = self.base_types.get(ty) {
            return Some(cached);
        }
        let key = (std::thread::current().id(), ty);
        if !lock(&self.resolving).insert(key) {
            return Some(Vec::new());
        }
        None
    }

    pub(crate) fn cache_base_types(&self, ty: SymbolId, resolved: Vec<Type>) {
        lock(&self.resolving).remove(&(std::thread::current().id(), ty));
        self.base_types.insert(ty, resolved);
    }

    pub(crate) fn cached_symbol_type(&self, symbol: SymbolId) -> Option<Type> {
        self.symbol_types.get(symbol)
    }

    pub(crate) fn cache_symbol_type(&self, symbol: SymbolId, ty: Type) {
        self.symbol_types.insert(symbol, ty);
    }

    pub(crate) fn cached_inheritance(&self, key: &(Type, Type)) -> Option<bool> {
        read(&self.inheritance).get(key).copied()
    }

    pub(crate) fn cache_inheritance(&self, key: (Type, Type), inherits: bool) {
        write(&self.inheritance).insert(key, inherits);
    }

    pub(crate) fn cached_implicit(&self, key: &(Type, Type)) -> Option<bool> {
        read(&self.implicit_conversions).get(key).copied()
    }

    pub(crate) fn cache_implicit(&self, key: (Type, Type), converts: bool) {
        write(&self.implicit_conversions).insert(key, converts);
    }

    pub(crate) fn cached_conversion(&self, key: &(Type, Type)) -> Option<Option<SymbolId>> {
        read(&self.conversions).get(key).copied()
    }

    pub(crate) fn cache_conversion(&self, key: (Type, Type), operator: Option<SymbolId>) {
        write(&self.conversions).insert(key, operator);
    }

    pub(crate) fn cached_constant(&self, symbol: SymbolId) -> Option<Option<ConstantValue>> {
        read(&self.constants).get(&symbol).cloned()
    }

    pub(crate) fn cache_constant(&self, symbol: SymbolId, value: Option<ConstantValue>) {
        write(&self.constants).insert(symbol, value);
    }

    /// Notes constants whose values are written in terms of each other all
    /// the way round (CS0110): the members of one circle.
    pub(crate) fn note_circular_constants(&self, mut circle: Vec<SymbolId>) {
        circle.sort_unstable();
        circle.dedup();
        write(&self.circular_constants).insert(circle);
    }

    /// Every circle of constants found so far, each with its members in
    /// order; a circle is found when one of its members is evaluated.
    pub(crate) fn circular_constants(&self) -> Vec<Vec<SymbolId>> {
        read(&self.circular_constants).iter().cloned().collect()
    }

    pub(crate) fn cached_imports(&self, key: ImportsKey) -> Option<Vec<Import>> {
        read(&self.imports).get(&key).cloned()
    }

    pub(crate) fn cache_imports(&self, key: ImportsKey, imports: Vec<Import>) {
        write(&self.imports).insert(key, imports);
    }

    pub(crate) fn cached_global_imports(&self) -> Option<Vec<Import>> {
        read(&self.global_imports).clone()
    }

    pub(crate) fn cache_global_imports(&self, imports: Vec<Import>) {
        *write(&self.global_imports) = Some(imports);
    }

    /// The name of every extension method there is, which is where a list of
    /// what can follow a `.` starts.
    pub fn extension_method_names(&self) -> impl Iterator<Item = &str> {
        self.extensions.keys().map(String::as_str)
    }

    /// Every extension method with this name, wherever it was declared.
    #[must_use]
    pub fn extension_methods(&self, name: &str) -> &[SymbolId] {
        self.extensions.get(name).map_or(&[], Vec::as_slice)
    }

    /// The members of extension blocks called `name` that are not extension
    /// methods: properties, indexers and static methods.
    #[must_use]
    pub fn extension_members(&self, name: &str) -> &[SymbolId] {
        self.extension_members.get(name).map_or(&[], Vec::as_slice)
    }

    /// Whether a type read from metadata is `[ComImport]`, and the class its
    /// `[CoClass]` names as the attribute spells it: `Some(None)` for one
    /// with no coclass.
    #[must_use]
    pub fn metadata_com_import(&self, symbol: SymbolId) -> Option<Option<&str>> {
        self.loaded
            .com_imports
            .get(&symbol)
            .map(|co_class| co_class.as_deref())
    }

    /// What builds a `[CollectionBuilder]` type: the builder's full metadata
    /// name and the method on it that takes a `ReadOnlySpan<T>`.
    #[must_use]
    pub fn collection_builder(&self, symbol: SymbolId) -> Option<(&str, &str)> {
        self.loaded
            .builders
            .get(&symbol)
            .map(|(builder, method)| (builder.as_str(), method.as_str()))
    }

    /// The full metadata name of the builder a task-like type read from an
    /// assembly names with `[AsyncMethodBuilder(typeof(B))]`.
    #[must_use]
    pub fn metadata_async_method_builder(&self, symbol: SymbolId) -> Option<&str> {
        self.loaded.async_builders.get(&symbol).map(String::as_str)
    }

    /// The assembly a loaded type came out of.
    ///
    /// A backend needs this and the binder never does: to the binder a symbol
    /// is a symbol, and to a writer of metadata one is a row it defines and
    /// another is a row in a file it has to name.
    #[must_use]
    pub fn assembly_of(&self, symbol: SymbolId) -> Option<&Reference> {
        // A member's assembly is its type's, and a nested type's is the one
        // its enclosing type came from.
        let mut current = Some(symbol);
        while let Some(id) = current {
            if let Some(reference) = self.loaded.assemblies.get(&id) {
                return Some(reference);
            }
            current = self.symbols.get(id).container;
        }
        None
    }

    /// Another referenced assembly's type of the same namespace, name and
    /// arity as `ty`, which a name that found `ty` found as well (CS0433).
    ///
    /// A type the source declares wins over one of a reference, and the core
    /// library's loses to any other (Roslyn's `BestSymbolLocation`), so only
    /// two types of two ordinary references are ambiguous. Only what code
    /// here can see was loaded at all, so whatever is here is a candidate —
    /// except where the assembly of `tree` says which references it has,
    /// and the other type's is not one of them.
    #[must_use]
    pub fn same_type_elsewhere(&self, ty: SymbolId, tree: usize) -> Option<SymbolId> {
        if !self.is_from_metadata(ty) {
            return None;
        }
        let symbol = self.symbols.get(ty);
        let container = symbol.container?;
        if self.symbols.get(container).kind != SymbolKind::Namespace {
            return None;
        }
        let arity = symbol.as_named_type()?.arity;
        let corlib = self
            .special_type(SpecialType::Object)
            .and_then(|object| self.assembly_of(object))
            .map(|reference| reference.name.as_str());
        let assembly = self.assembly_of(ty)?;
        if Some(assembly.name.as_str()) == corlib {
            return None;
        }
        self.symbols
            .lookup(container, &symbol.name)
            .iter()
            .copied()
            .find(|&other| {
                other != ty
                    && self.is_from_metadata(other)
                    && self.symbols.get(other).kind == SymbolKind::NamedType
                    && self
                        .symbols
                        .get(other)
                        .as_named_type()
                        .is_some_and(|detail| detail.arity == arity)
                    && self.assembly_of(other).is_some_and(|reference| {
                        reference.name != assembly.name && Some(reference.name.as_str()) != corlib
                    })
                    && self.references_assembly_of(other, tree) != Some(false)
            })
    }

    /// Whether the symbol came from a referenced assembly rather than from a
    /// syntax tree.
    #[must_use]
    pub fn is_from_metadata(&self, symbol: SymbolId) -> bool {
        symbol.index() >= self.metadata_floor && !symbol.is_late()
    }

    /// Whether `symbol` is declared in trees of two assemblies of those the
    /// compilation was made as: two projects' types of one name, which one
    /// compilation of both declares as one.
    #[must_use]
    pub fn declared_in_several_assemblies(&self, symbol: SymbolId) -> bool {
        let mut seen = None;
        for location in &self.symbols.get(symbol).locations {
            let Some(&assembly) = self.tree_assemblies.get(location.tree) else {
                continue;
            };
            if assembly == u16::MAX {
                continue;
            }
            match seen {
                None => seen = Some(assembly),
                Some(other) if other != assembly => return true,
                Some(_) => {}
            }
        }
        false
    }

    /// Which assembly `tree` goes into, as [`Compilation::set_tree_assemblies`]
    /// said: `u16::MAX` where nothing did.
    #[must_use]
    pub fn tree_assembly(&self, tree: usize) -> u16 {
        self.tree_assemblies.get(tree).copied().unwrap_or(u16::MAX)
    }

    /// Says which assembly each tree goes into, by its index into the names
    /// given to [`Compilation::create_with_references_as_any`]: a reference's
    /// internals are then seen only by the code of an assembly it names in
    /// an `[InternalsVisibleTo]`. `u16::MAX` is any of them.
    pub fn set_tree_assemblies(&mut self, assemblies: Vec<u16>) {
        self.tree_assemblies = assemblies;
    }

    /// Says which of the assemblies the compilation was made as each one
    /// references, by index; `u16::MAX` in a list is "any of them".
    pub fn set_assembly_references(&mut self, references: Vec<Vec<u16>>) {
        self.assembly_references = references;
        if let Ok(mut seen) = self.namespaces_seen.write() {
            seen.clear();
        }
    }

    /// Whether code of assembly `from` sees what assembly `to` declares: its
    /// own, or one it references. What nothing was said about is seen.
    #[must_use]
    pub fn assembly_sees(&self, from: u16, to: u16) -> bool {
        from == to
            || from == u16::MAX
            || to == u16::MAX
            || self
                .assembly_references
                .get(usize::from(from))
                .is_none_or(|references| references.contains(&to) || references.contains(&u16::MAX))
    }

    /// Whether a reference names an assembly compiled here in an
    /// `[InternalsVisibleTo]`, which is when internals of it are loaded.
    #[must_use]
    pub fn trusts_any(&self) -> bool {
        !self.loaded.trusting.is_empty()
    }

    /// Whether code in `tree` sees `symbol`, for an editor compiling several
    /// projects at once: a reference's internal type or member only where the
    /// reference names this tree's assembly in an `[InternalsVisibleTo]`, and
    /// what another project's source declares only where this tree's
    /// assembly references that project.
    #[must_use]
    pub fn sees(&self, symbol: SymbolId, tree: usize) -> bool {
        let Some(&assembly) = self.tree_assemblies.get(tree) else {
            return true;
        };
        if assembly == u16::MAX {
            return true;
        }
        self.assembly_sees_symbol(assembly, symbol)
    }

    /// Whether the assembly `symbol` was read from names the one the code
    /// in `tree` is compiled into its friend (`[InternalsVisibleTo]`).
    pub(crate) fn befriended_by(&self, symbol: SymbolId, tree: usize) -> bool {
        let Some(trusted) = self
            .assembly_of(symbol)
            .and_then(|reference| self.loaded.trusting.get(&reference.name))
        else {
            return false;
        };
        match self.tree_assemblies.get(tree) {
            Some(&assembly) if assembly != u16::MAX => trusted.contains(&assembly),
            // One assembly is being compiled, and it is the one named.
            _ => true,
        }
    }

    fn assembly_sees_symbol(&self, assembly: u16, symbol: SymbolId) -> bool {
        if self.is_from_metadata(symbol) {
            if self.loaded.trusting.is_empty()
                || !matches!(
                    self.symbols.get(symbol).accessibility,
                    Accessibility::Internal | Accessibility::ProtectedAndInternal
                )
            {
                return true;
            }
            return self.assembly_of(symbol).is_none_or(|reference| {
                self.loaded
                    .trusting
                    .get(&reference.name)
                    .is_none_or(|trusted| trusted.contains(&assembly))
            });
        }
        if self.assembly_references.is_empty() || symbol.is_late() {
            return true;
        }
        // A member is where its outermost type is, and internal where it or
        // a type around it is.
        let internal = |id: SymbolId| {
            matches!(
                self.symbols.get(id).accessibility,
                Accessibility::Internal | Accessibility::ProtectedAndInternal
            )
        };
        let mut outermost = symbol;
        let mut is_internal = internal(symbol);
        while let Some(container) = self.symbols.get(outermost).container
            && self.symbols.get(container).kind == SymbolKind::NamedType
        {
            outermost = container;
            is_internal |= internal(outermost);
        }
        if self.symbols.get(outermost).kind != SymbolKind::NamedType {
            return true;
        }
        let declared: Vec<u16> = self
            .symbols
            .get(outermost)
            .locations
            .iter()
            .flat_map(|location| {
                std::iter::once(self.tree_assembly(location.tree)).chain(
                    self.tree_assemblies_also
                        .get(&location.tree)
                        .into_iter()
                        .flatten()
                        .copied(),
                )
            })
            .collect();
        if declared.is_empty() || declared.contains(&assembly) {
            return true;
        }
        // Another project's: one this one references, and what is internal
        // there only where that project names this one its friend.
        declared.iter().any(|&owner| {
            self.assembly_sees(assembly, owner)
                && (!is_internal
                    || owner == u16::MAX
                    || self
                        .source_friends
                        .get(usize::from(owner))
                        .is_some_and(|friends| friends.contains(&assembly)))
        })
    }

    /// Says which more assemblies than its own each tree goes into.
    pub fn set_tree_assemblies_also(&mut self, also: HashMap<usize, Vec<u16>>) {
        self.tree_assemblies_also = also;
        if let Ok(mut seen) = self.namespaces_seen.write() {
            seen.clear();
        }
    }

    /// Says which assemblies each one names in an `[assembly:
    /// InternalsVisibleTo]` of its source, by index.
    pub fn set_source_friends(&mut self, friends: Vec<Vec<u16>>) {
        self.source_friends = friends;
        if let Ok(mut seen) = self.namespaces_seen.write() {
            seen.clear();
        }
    }

    /// Says which assemblies annotate their reference types by default
    /// (`-nullable:enable`), by index; one not said of takes the
    /// compilation's own setting.
    pub fn set_assembly_nullable(&mut self, nullable: Vec<bool>) {
        self.assembly_nullable = nullable;
    }

    /// Whether reference types are annotated in file `tree` where no
    /// `#nullable` says otherwise.
    #[must_use]
    pub fn nullable_annotations_in(&self, tree: usize) -> bool {
        self.assembly_nullable
            .get(usize::from(self.tree_assembly(tree)))
            .copied()
            .unwrap_or(self.options.nullable_annotations)
    }

    /// Says which precompiled assemblies each assembly references, by
    /// lowercased file stem; an empty list says nothing. Two references
    /// that declare one type — Unity's Burst carries its own Cecil beside
    /// the one other packages use — are no ambiguity to an assembly that
    /// references only one of them.
    pub fn set_metadata_references(&mut self, references: Vec<Vec<String>>) {
        self.metadata_references = references;
        if let Ok(mut seen) = self.namespaces_seen.write() {
            seen.clear();
        }
    }

    /// Whether the code of `tree` references the assembly `symbol` came
    /// from, as far as anything says: `None` where nothing does.
    pub(crate) fn references_assembly_of(&self, symbol: SymbolId, tree: usize) -> Option<bool> {
        self.assembly_references_assembly_of(self.tree_assembly(tree), symbol)
    }

    fn assembly_references_assembly_of(&self, assembly: u16, symbol: SymbolId) -> Option<bool> {
        let names = self
            .metadata_references
            .get(usize::from(assembly))
            .filter(|names| !names.is_empty())?;
        let reference = self.assembly_of(symbol)?;
        Some(
            names
                .iter()
                .any(|name| name.eq_ignore_ascii_case(&reference.name)),
        )
    }

    /// Whether code in `tree` sees the namespace `namespace`: one with
    /// nothing in it this code sees — only another project's types, or only
    /// friends' internal ones — is not there for it, and a name there is
    /// looked up further out.
    #[must_use]
    pub fn sees_namespace(&self, namespace: SymbolId, tree: usize) -> bool {
        if self.loaded.trusting.is_empty()
            && self.assembly_references.is_empty()
            && self.metadata_references.is_empty()
        {
            return true;
        }
        let Some(&assembly) = self.tree_assemblies.get(tree) else {
            return true;
        };
        if assembly == u16::MAX {
            return true;
        }
        self.assembly_sees_namespace(assembly, namespace, 0)
    }

    fn assembly_sees_namespace(&self, assembly: u16, namespace: SymbolId, depth: usize) -> bool {
        if let Some(&known) = self
            .namespaces_seen
            .read()
            .ok()
            .and_then(|seen| seen.get(&(namespace, assembly)).copied())
            .as_ref()
        {
            return known;
        }
        let members = &self.symbols.get(namespace).members;
        let seen = members.is_empty()
            || members
                .iter()
                .any(|&member| match self.symbols.get(member).kind {
                    SymbolKind::Namespace => {
                        depth > 64 || self.assembly_sees_namespace(assembly, member, depth + 1)
                    }
                    // A namespace only a reference the assembly does not have
                    // declares is not there for it: the engine's
                    // `Unity.CompilationPipeline` does not hide
                    // `UnityEditor.Compilation.CompilationPipeline` from code in
                    // `namespace Unity.Burst` that never referenced it.
                    SymbolKind::NamedType => {
                        self.assembly_sees_symbol(assembly, member)
                            && (!self.is_from_metadata(member)
                                || self.assembly_references_assembly_of(assembly, member)
                                    != Some(false))
                    }
                    _ => true,
                });
        if let Ok(mut cache) = self.namespaces_seen.write() {
            cache.insert((namespace, assembly), seen);
        }
        seen
    }

    /// The type of `container` called `name` with `arity` type parameters
    /// that code in `tree` sees, as [`Symbols::lookup_type_from`] finds it,
    /// less a reference's internal type this tree is not a friend of.
    #[must_use]
    pub fn lookup_type_from(
        &self,
        container: SymbolId,
        name: &str,
        arity: usize,
        tree: usize,
    ) -> Option<SymbolId> {
        let mut found = None;
        for &id in self.symbols.lookup(container, name) {
            let symbol = self.symbols.get(id);
            if symbol.kind != SymbolKind::NamedType
                || symbol.as_named_type().is_none_or(|d| d.arity != arity)
                || !self.symbols.visible_from(id, tree)
                || !self.sees(id, tree)
            {
                continue;
            }
            if self.symbols.file_of(id).is_some() {
                return Some(id);
            }
            // Of two references' types, the one of the assembly the code
            // references.
            if found.is_none_or(|earlier| {
                self.references_assembly_of(earlier, tree) == Some(false)
                    && self.references_assembly_of(id, tree) == Some(true)
            }) {
                found = Some(id);
            }
        }
        found
    }

    /// The symbol behind a language keyword such as `int`.
    #[must_use]
    pub fn special_type(&self, special: SpecialType) -> Option<SymbolId> {
        self.special_types[special as usize]
    }

    /// Resolves every declared type and reports the ones that do not exist.
    ///
    /// This is the pass that turns `Foo field;` with no `Foo` anywhere into
    /// CS0246. It is separate from declaring, because a type may be used
    /// before it is declared.
    #[must_use]
    pub fn semantic_diagnostics(&self) -> Vec<CompilationDiagnostic> {
        // Bodies are bound here, as deep as they nest.
        crate::parallel::deep(|| self.semantic_diagnostics_here())
    }

    fn semantic_diagnostics_here(&self) -> Vec<CompilationDiagnostic> {
        let mut sink = self.check_declarations(None);

        // Then the bodies, where names and expressions are bound.
        for tree in self.corlib_trees..self.trees.len() {
            sink.extend(crate::model::SemanticModel::new(self, tree).body_diagnostics());
        }

        // A type written once can be asked about many times — an alias at
        // each use, a field-like event for itself and each accessor — and
        // says the same about the access to it each time (CS0122).
        let mut told: std::collections::HashSet<(usize, u32, u32, String)> =
            std::collections::HashSet::new();
        sink.retain(|(tree, diagnostic)| {
            diagnostic.code() != rustlyn_diagnostics::ErrorCode::ErrBadAccess
                || told.insert((
                    *tree,
                    diagnostic.span().start(),
                    diagnostic.span().end(),
                    diagnostic.message().to_string(),
                ))
        });

        // What a `#pragma warning disable` switched off is not reported.
        let mut pragmas: HashMap<usize, crate::pragma::WarningState> = HashMap::new();
        sink.into_iter()
            .filter(|(tree, _)| *tree >= self.corlib_trees)
            .filter(|(tree, diagnostic)| {
                diagnostic.is_error()
                    || !pragmas
                        .entry(*tree)
                        .or_insert_with(|| {
                            self.trees
                                .get(*tree)
                                .map(|syntax| crate::pragma::WarningState::of(&syntax.root()))
                                .unwrap_or_default()
                        })
                        .is_suppressed(diagnostic)
            })
            .map(|(tree, diagnostic)| CompilationDiagnostic { tree, diagnostic })
            .collect()
    }

    /// Whether the symbol comes from the synthesised core library rather than
    /// from the user's files.
    ///
    /// The two are declared by the same pass into the same table, so nothing
    /// but the file a symbol came from tells them apart — and a backend has to
    /// tell them apart, because one it defines and the other it references.
    #[must_use]
    pub fn is_from_corlib(&self, symbol: SymbolId) -> bool {
        // A symbol's locations, not its declaration nodes: a synthesised
        // member — the constructor a class gets when it declares none — has a
        // location but no node of its own, and it belongs to whichever file
        // its type does.
        self.is_from_metadata(symbol)
            || self
                .symbols
                .get(symbol)
                .locations
                .first()
                .is_some_and(|location| location.tree < self.corlib_trees)
    }

    /// The symbol a declaration node produced, which is how the semantic model
    /// gets from a piece of syntax back to what it means.
    #[must_use]
    pub fn declared_symbol(&self, tree: usize, span: TextSpan) -> Option<SymbolId> {
        self.declarations.get(&(tree, span)).copied()
    }

    /// Where a symbol was declared, as syntax rather than as a name.
    ///
    /// This is the way back from a symbol to its body, which is what an
    /// interpreter or a code generator needs.
    #[must_use]
    pub fn declaration_nodes(&self, symbol: SymbolId) -> &[(usize, TextSpan)] {
        self.declaration_nodes
            .get(&symbol)
            .map_or(&[], Vec::as_slice)
    }

    /// The syntax of a symbol's first declaration.
    #[must_use]
    pub fn declaration_node(&self, symbol: SymbolId) -> Option<rustlyn_syntax::SyntaxNode> {
        let (tree, span) = *self.declaration_nodes(symbol).first()?;
        self.trees.get(tree)?.root().find_node(span)
    }

    /// Whether a field declared in source is `ref readonly T F`: what it
    /// refers to may not be written through it.
    #[must_use]
    pub fn is_ref_readonly_field(&self, field: SymbolId) -> bool {
        self.declaration_node(field)
            .and_then(|declarator| declarator.parent().cloned())
            .and_then(|declaration| declaration.child_of_kind(rustlyn_syntax::SyntaxKind::RefType))
            .is_some_and(|reference| {
                reference
                    .child_tokens()
                    .any(|token| token.kind() == rustlyn_syntax::SyntaxKind::ReadOnlyKeyword)
            })
    }

    /// A member of an interface with what its declaration left unsaid filled
    /// in, as C# 8 reads it (Roslyn's `AdjustModifiersForAnInterfaceMember`).
    ///
    /// `void M();` is `abstract` and `void M() { }` is `virtual`, unless the
    /// member says otherwise: `sealed void M() { }` is a method nothing can
    /// override, neither sealed nor virtual, and a `private` one or a partial
    /// method is no slot of anyone's either. `abstract void I1.M();` in a
    /// derived interface takes `I1.M`'s body away again, and nothing may
    /// override that, so it is `sealed` as well. A member of any other type,
    /// or one read from metadata — whose flags already say all of this —
    /// comes back as it was declared.
    #[must_use]
    pub fn interface_member_modifiers(&self, member: SymbolId) -> Modifiers {
        use rustlyn_syntax::SyntaxKind;
        let symbol = self.symbols.get(member);
        let mut modifiers = symbol.modifiers;
        let in_interface = symbol
            .container
            .is_some_and(|owner| self.symbols.get(owner).type_kind() == Some(TypeKind::Interface));
        if !in_interface || self.is_from_metadata(member) {
            return modifiers;
        }
        let Some(node) = self.declaration_node(member) else {
            return modifiers;
        };
        if node
            .child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier)
            .is_some()
        {
            if modifiers.contains(Modifiers::ABSTRACT) {
                modifiers.insert(Modifiers::SEALED);
            }
            return modifiers;
        }
        let without_sealed = Modifiers::from_bits(modifiers.bits() & !Modifiers::SEALED.bits());
        if modifiers.contains(Modifiers::STATIC) {
            return without_sealed;
        }
        let partial_method =
            symbol.kind == SymbolKind::Method && modifiers.contains(Modifiers::PARTIAL);
        if symbol.accessibility == Accessibility::Private
            || modifiers.contains(Modifiers::VIRTUAL)
            || modifiers.contains(Modifiers::ABSTRACT)
            || partial_method
        {
            return modifiers;
        }
        let with_body = |node: &rustlyn_syntax::SyntaxNode| {
            node.child_of_kind(SyntaxKind::Block).is_some()
                || node
                    .child_of_kind(SyntaxKind::ArrowExpressionClause)
                    .is_some()
        };
        // An event has a body where it wrote `add` and `remove`; a property
        // where any accessor has one, or the property is `=> e`.
        let has_body = match symbol.kind {
            SymbolKind::Event => node.kind() != SyntaxKind::VariableDeclarator,
            _ => {
                with_body(&node)
                    || node
                        .child_of_kind(SyntaxKind::AccessorList)
                        .is_some_and(|list| list.children().any(|accessor| with_body(&accessor)))
            }
        };
        if modifiers.contains(Modifiers::SEALED) {
            without_sealed
        } else if has_body
            || modifiers.contains(Modifiers::EXTERN)
            || modifiers.contains(Modifiers::PARTIAL)
        {
            modifiers.union(Modifiers::VIRTUAL)
        } else {
            modifiers.union(Modifiers::ABSTRACT)
        }
    }

    /// Every type declared anywhere, in declaration order.
    pub fn all_types(&self) -> impl Iterator<Item = &crate::symbol::Symbol> {
        self.symbols
            .iter()
            .filter(|symbol| symbol.kind == SymbolKind::NamedType)
    }
}

/// An answer per symbol, worked out once and asked for from every thread.
///
/// The symbols declared in source are numbered densely from zero, so each
/// has a slot of its own that is read without taking a lock: a lock every
/// reader takes, even a shared one, is one word every core writes to, and
/// with the questions asked millions of times that word is the bottleneck.
/// Symbols past the slots — from metadata, or made late — share a map.
#[derive(Debug)]
pub(crate) struct SymbolCache<T> {
    slots: Box<[std::sync::OnceLock<T>]>,
    rest: RwLock<HashMap<SymbolId, T>>,
}

impl<T: Clone> SymbolCache<T> {
    /// Slots for the symbols numbered below `slots`.
    pub(crate) fn new(slots: usize) -> Self {
        Self {
            slots: std::iter::repeat_with(std::sync::OnceLock::new)
                .take(slots)
                .collect(),
            rest: RwLock::new(HashMap::new()),
        }
    }

    pub(crate) fn get(&self, symbol: SymbolId) -> Option<T> {
        match self.slots.get(symbol.index()) {
            Some(slot) => slot.get().cloned(),
            None => read(&self.rest).get(&symbol).cloned(),
        }
    }

    /// Keeps an answer. Two threads that worked the same one out at once
    /// worked out the same answer, so the second is dropped.
    pub(crate) fn insert(&self, symbol: SymbolId, value: T) {
        match self.slots.get(symbol.index()) {
            Some(slot) => {
                let _ = slot.set(value);
            }
            None => {
                write(&self.rest).insert(symbol, value);
            }
        }
    }
}

/// Files waiting to be parsed, and the trees made of them so far, for
/// threads that parse and one that declares the trees in order as they come.
pub(crate) struct ParseQueue<'a> {
    sources: Vec<Mutex<Option<SourceText>>>,
    options: &'a ParseOptions,
    next: std::sync::atomic::AtomicUsize,
    /// Each file's tree and facts, once parsed: `None` where parsing failed.
    pub(crate) slots: Vec<std::sync::OnceLock<Option<(SyntaxTree, TreeFacts)>>>,
    /// Why the first file that failed to parse failed.
    failure: Mutex<Option<Box<dyn std::any::Any + Send>>>,
}

impl<'a> ParseQueue<'a> {
    fn new(sources: Vec<SourceText>, options: &'a ParseOptions) -> Self {
        let slots = sources.iter().map(|_| std::sync::OnceLock::new()).collect();
        Self {
            sources: sources
                .into_iter()
                .map(|source| Mutex::new(Some(source)))
                .collect(),
            options,
            next: std::sync::atomic::AtomicUsize::new(0),
            slots,
            failure: Mutex::new(None),
        }
    }

    /// Parses the next file nobody has taken yet; `false` when none is left.
    pub(crate) fn parse_next(&self) -> bool {
        let index = self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let Some(source) = self.sources.get(index) else {
            return false;
        };
        let source = lock(source).take().expect("each file is parsed once");
        // A file that fails to parse still fills its slot, or the
        // declarations would wait for it for ever.
        let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let tree = parse_with(source, self.options);
            let facts = TreeFacts::of(&tree);
            (tree, facts)
        }));
        match parsed {
            Ok(parsed) => {
                let _ = self.slots[index].set(Some(parsed));
            }
            Err(panic) => {
                let _ = self.slots[index].set(None);
                lock(&self.failure).get_or_insert(panic);
            }
        }
        true
    }

    /// One file's tree and facts, parsing others meanwhile rather than
    /// waiting idle while there are files left to parse.
    pub(crate) fn get(&self, index: usize) -> Option<&Option<(SyntaxTree, TreeFacts)>> {
        let slot = self.slots.get(index)?;
        loop {
            if let Some(parsed) = slot.get() {
                return Some(parsed);
            }
            if !self.parse_next() {
                return Some(slot.wait());
            }
        }
    }
}

/// The metadata names asked for most, most asked first: the bases every
/// type has without writing them, and what the language itself builds on.
const WELL_KNOWN: [&str; 16] = [
    "System.Object",
    "System.Nullable`1",
    "System.ValueType",
    "System.Enum",
    "System.UIntPtr",
    "System.ValueTuple`2",
    "System.MulticastDelegate",
    "System.Index",
    "System.Range",
    "System.Array",
    "System.Collections.IEnumerable",
    "System.Collections.Generic.IReadOnlyList`1",
    "System.Collections.Generic.IReadOnlyCollection`1",
    "System.Collections.Generic.IList`1",
    "System.Collections.Generic.IEnumerable`1",
    "System.Collections.Generic.ICollection`1",
];

/// The caches only ever hold finished answers, so one left behind by a thread
/// that panicked is still a good answer.
fn read<T>(lock: &RwLock<T>) -> std::sync::RwLockReadGuard<'_, T> {
    lock.read()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn write<T>(lock: &RwLock<T>) -> std::sync::RwLockWriteGuard<'_, T> {
    lock.write()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

pub(crate) fn lock<T>(lock: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    lock.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// An editor asks one compilation questions from several threads at once.
const _: () = {
    const fn shared<T: Send + Sync>() {}
    shared::<Compilation>();
};

/// Whether a file declares a `global using`, which is every file's business.
pub(crate) fn has_global_using(tree: &SyntaxTree) -> bool {
    tree.root().children().any(|child| {
        child.kind() == rustlyn_syntax::SyntaxKind::UsingDirective
            && child
                .child_token_of_kind(rustlyn_syntax::SyntaxKind::GlobalKeyword)
                .is_some()
    })
}
