//! Hot patches: what changed between the compilation a running editor
//! loaded and the one the files make now, written as a small assembly whose
//! static methods the editor sends the old ones to, without a reload.
//!
//! The pieces: [`diff`] finds what changed by declaration, [`patch`] writes
//! the changed members as static methods of a patch class, [`tails`] gives
//! structs room for the fields an edit adds to them. A [`Session`] keeps
//! what one editor has been sent since it last loaded a whole build: every
//! patch holds everything since then, so an edit can be undone or changed
//! again.

/// A line on standard error where `RUSTLYN_TIMINGS` asks for them.
macro_rules! trace {
    ($($argument:tt)*) => {
        if std::env::var_os("RUSTLYN_TIMINGS").is_some() {
            eprintln!($($argument)*);
        }
    };
}

pub(crate) mod diff;
pub(crate) mod patch;
pub(crate) mod tails;

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use rustlyn_semantics::{Compilation, CompilationOptions, SymbolId};
use rustlyn_syntax::{ParseOptions, SyntaxKind, parse_with};
use rustlyn_text::SourceText;

/// What the tails are made of: a file the compilation of an editor's build
/// declares beside the program's own.
pub const TAIL_SUPPORT: &str = tails::SUPPORT;

/// The file that lets a patch reach what is private in the build.
pub const PATCH_ACCESS: &str =
    "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"PilotPatch\")]\n";

/// The structs an editor's build gives a tail (see [`tails`]).
#[derive(Default, Debug, Clone)]
pub struct Tails(tails::Tailed);

impl Tails {
    /// The structs of `compilation` a tail does not break.
    #[must_use]
    pub fn choose(compilation: &Compilation) -> Self {
        Self(tails::choose(compilation))
    }

    /// For [`crate::IncrementalOptions::struct_tails`].
    #[must_use]
    pub fn struct_tails(&self) -> HashMap<String, bool> {
        self.0.references()
    }

    /// One line per struct, for two builds to be compared by.
    #[must_use]
    pub fn listing(&self) -> String {
        self.0.listing()
    }
}

/// What one editor has been sent since it last loaded a whole build.
#[derive(Debug)]
pub struct Session {
    base_image: Vec<u8>,
    known: HashSet<String>,
    patched: HashSet<String>,
    ran: HashMap<String, String>,
    edited: Vec<String>,
    rounds: usize,
    tails: Tails,
    references: Vec<Arc<[u8]>>,
    directory: PathBuf,
    options: ParseOptions,
    /// The source of the last patch sent, its round's number taken out: a
    /// save that comes to the same patch — spacing, a comment — sends none.
    last_sent: Option<String>,
    /// The files of the patched assembly, where known: a class compiled
    /// from any other is another assembly's to a patch.
    assembly: Option<HashSet<String>>,
}

impl Session {
    /// A session for an editor that loaded `base_image`, built from `base`.
    /// `references` are what a patch is compiled against besides the build:
    /// the build's own references and the runtime the patches call
    /// (`PilotRuntime.dll`). Patches are written into `directory`.
    #[must_use]
    pub fn new(
        base: &Compilation,
        base_image: Vec<u8>,
        tails: Tails,
        references: Vec<Arc<[u8]>>,
        directory: PathBuf,
        options: ParseOptions,
    ) -> Self {
        Self {
            known: diff::type_names(base),
            base_image,
            patched: HashSet::new(),
            ran: HashMap::new(),
            edited: Vec::new(),
            rounds: 0,
            tails,
            references,
            directory,
            options,
            last_sent: None,
            assembly: None,
        }
    }

    /// The files of the patched assembly, as the compilation names them.
    pub fn set_assembly_files(&mut self, files: HashSet<String>) {
        self.assembly = Some(files);
    }

    /// A file the patched assembly has gained.
    pub fn add_assembly_file(&mut self, file: String) {
        if let Some(files) = &mut self.assembly {
            files.insert(file);
        }
    }

    /// The editor loaded a whole build again, made from `base`: what was
    /// sent before is in it.
    pub fn reloaded(&mut self, base: &Compilation, base_image: Vec<u8>) {
        self.known = diff::type_names(base);
        self.base_image = base_image;
        self.patched.clear();
        self.ran.clear();
        self.edited.clear();
        self.last_sent = None;
    }

    /// The build the editor has loaded.
    #[must_use]
    pub fn base_image(&self) -> &[u8] {
        &self.base_image
    }

    /// A file that is gone, which no patch can speak of.
    pub fn forget(&mut self, path: &str) {
        self.edited.retain(|seen| seen != path);
    }

    /// The patch for everything that differs between `base` — what the
    /// editor loaded — and `current`, now that `saved` were saved: the
    /// path of the assembly written, `None` where nothing that runs
    /// changed, or why only a reload carries the edit.
    ///
    /// # Errors
    /// What keeps the edit from being a patch, one reason per line.
    pub fn patch(
        &mut self,
        base: &Compilation,
        current: &Compilation,
        saved: &[String],
    ) -> Result<Option<PathBuf>, String> {
        for path in saved {
            if !self.edited.iter().any(|seen| seen == path) {
                self.edited.push(path.clone());
            }
        }
        self.rounds += 1;
        let diffing = Instant::now();
        let mut changes =
            self.edited
                .iter()
                .try_fold(diff::Changes::default(), |mut all, file| {
                    all.extend(diff::changes(
                        base,
                        current,
                        file,
                        &self.known,
                        &self.patched,
                    )?);
                    Ok::<_, String>(all)
                })?;
        trace!("diff {} ms", diffing.elapsed().as_millis());
        named_elsewhere(base, current, &changes.reshaped, &self.edited)?;
        constant_readers(current, &mut changes)?;
        self.patched.extend(changes.body_keys.iter().cloned());
        // What runs once runs again only when it changed again: a static
        // that has been running keeps its state.
        let mut again = Vec::new();
        for list in [&mut changes.reinitialized, &mut changes.rerun] {
            list.retain(|&symbol| {
                let key = current.symbols().qualified_name(symbol);
                let text = current
                    .declaration_node(symbol)
                    .map(|node| node.text())
                    .unwrap_or_default();
                let changed = self.ran.get(&key) != Some(&text);
                if changed {
                    again.push((key, text));
                }
                changed
            });
        }
        let images: Vec<&[u8]> = self.references.iter().map(|bytes| &bytes[..]).collect();
        let dll = make_patch(
            current,
            &changes,
            &self.tails.0,
            self.rounds,
            &self.options,
            &images,
            &self.base_image,
            &self.directory,
            Some(&mut self.last_sent),
            self.assembly.as_ref(),
        )?;
        self.ran.extend(again);
        Ok((!dll.as_os_str().is_empty()).then_some(dll))
    }
}

/// The patch an edit from `before` to `current` of the files at `paths`
/// would be, made as a [`Session`] makes one but keeping nothing: what a
/// replay of a commit asks.
///
/// # Errors
/// What keeps the edit from being a patch.
#[allow(clippy::too_many_arguments)]
pub fn patch_between(
    before: &Compilation,
    current: &Compilation,
    paths: &[String],
    tails: &Tails,
    round: usize,
    options: &ParseOptions,
    references: &[&[u8]],
    base_image: &[u8],
    directory: &Path,
) -> Result<PathBuf, String> {
    let known = diff::type_names(before);
    let mut changes = paths
        .iter()
        .try_fold(diff::Changes::default(), |mut all, file| {
            all.extend(diff::changes(
                before,
                current,
                file,
                &known,
                &HashSet::new(),
            )?);
            Ok::<_, String>(all)
        })?;
    named_elsewhere(before, current, &changes.reshaped, paths)?;
    constant_readers(current, &mut changes)?;
    make_patch(
        current, &changes, &tails.0, round, options, references, base_image, directory, None, None,
    )
}

/// Every member that reads a constant the edit gave another value, added to
/// what the patch writes again: the value was written into it when it was
/// compiled. Where it was written into something a patch cannot write again
/// — an attribute, a parameter's default, another constant — an error.
pub(crate) fn constant_readers(
    compilation: &Compilation,
    changes: &mut diff::Changes,
) -> Result<(), String> {
    if changes.reconstants.is_empty() {
        return Ok(());
    }
    let symbols = compilation.symbols();
    let trees = compilation.trees();
    let names: Vec<String> = changes
        .reconstants
        .iter()
        .map(|constant| symbols.get(*constant).name.clone())
        .collect();
    let candidates: Vec<usize> = (0..trees.len())
        .filter(|&index| {
            trees.source(index).is_some_and(|source| {
                names
                    .iter()
                    .any(|name| source.text().contains(name.as_str()))
            })
        })
        .collect();
    for index in candidates {
        let Some(tree) = trees.get(index) else {
            continue;
        };
        let model = rustlyn_semantics::SemanticModel::new(compilation, index);
        for node in tree.root().descendants() {
            if node.kind() != SyntaxKind::IdentifierName
                || !node
                    .first_token()
                    .is_some_and(|token| names.iter().any(|name| name == token.text()))
                || !model
                    .symbol_at(&node)
                    .is_some_and(|found| changes.reconstants.contains(&found))
            {
                continue;
            }
            // The member it is read in: the nearest one with a body.
            let mut at = node.parent().cloned();
            let mut reader = None;
            while let Some(around) = at {
                match around.kind() {
                    SyntaxKind::MethodDeclaration
                    | SyntaxKind::ConstructorDeclaration
                    | SyntaxKind::OperatorDeclaration
                    | SyntaxKind::ConversionOperatorDeclaration
                    | SyntaxKind::GetAccessorDeclaration
                    | SyntaxKind::SetAccessorDeclaration
                    | SyntaxKind::InitAccessorDeclaration
                    | SyntaxKind::AddAccessorDeclaration
                    | SyntaxKind::RemoveAccessorDeclaration => {
                        reader = compilation.declared_symbol(index, around.span());
                        break;
                    }
                    SyntaxKind::PropertyDeclaration
                        if around
                            .children()
                            .any(|child| child.kind() == SyntaxKind::ArrowExpressionClause) =>
                    {
                        reader = compilation.declared_symbol(index, around.span());
                        break;
                    }
                    // A static field's initializer runs again, as a changed
                    // one does.
                    SyntaxKind::VariableDeclarator
                        if around
                            .parent()
                            .and_then(|list| list.parent())
                            .is_some_and(|field| field.kind() == SyntaxKind::FieldDeclaration) =>
                    {
                        if let Some(field) = compilation.declared_symbol(index, around.span())
                            && symbols
                                .get(field)
                                .modifiers
                                .contains(rustlyn_semantics::Modifiers::STATIC)
                            && !symbols
                                .get(field)
                                .modifiers
                                .contains(rustlyn_semantics::Modifiers::CONST)
                        {
                            if !changes.reinitialized.contains(&field) {
                                changes.reinitialized.push(field);
                            }
                            reader = Some(field);
                        }
                        break;
                    }
                    SyntaxKind::AttributeList
                    | SyntaxKind::Parameter
                    | SyntaxKind::FieldDeclaration
                    | SyntaxKind::EnumMemberDeclaration
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::ClassDeclaration
                    | SyntaxKind::StructDeclaration => break,
                    _ => {}
                }
                at = around.parent().cloned();
            }
            match reader {
                Some(field) if symbols.get(field).kind == rustlyn_semantics::SymbolKind::Field => {}
                // A static constructor runs again, as a changed one does.
                Some(reader)
                    if symbols.get(reader).as_method().is_some_and(|method| {
                        method.method_kind == rustlyn_semantics::MethodKind::StaticConstructor
                    }) =>
                {
                    if !changes.rerun.contains(&reader) {
                        changes.rerun.push(reader);
                    }
                }
                Some(reader) => {
                    if !changes.bodies.contains(&reader) && !changes.added_methods.contains(&reader)
                    {
                        changes.bodies.push(reader);
                    }
                }
                None => {
                    return Err(format!(
                        "{} changed its value, and {} reads it where a patch cannot write it again",
                        node.text().trim(),
                        trees
                            .source(index)
                            .map(|source| source.name().to_string())
                            .unwrap_or_default()
                    ));
                }
            }
        }
    }
    Ok(())
}

/// An error where a method whose shape changed is named in a file the edit
/// did not touch: that file's code calls the old one, and only a reload
/// would make it call the new.
pub(crate) fn named_elsewhere(
    base: &Compilation,
    compilation: &Compilation,
    reshaped: &[SymbolId],
    edited: &[String],
) -> Result<(), String> {
    if reshaped.is_empty() {
        return Ok(());
    }
    let searching = Instant::now();
    let symbols = compilation.symbols();
    let trees = compilation.trees();
    let word = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    // Whether the file `index` names `name`, as a word of its own.
    let names = |index: usize, name: &str| -> Option<String> {
        let source = trees.source(index)?;
        if edited.iter().any(|path| path == source.name()) {
            return None;
        }
        let text = source.text();
        let bytes = text.as_bytes();
        let mut from = 0;
        while let Some(at) = text[from..].find(name) {
            let at = from + at;
            let before = at.checked_sub(1).map(|index| bytes[index]);
            let after = bytes.get(at + name.len()).copied();
            if !before.is_some_and(word) && !after.is_some_and(word) {
                return Some(source.name().to_string());
            }
            from = at + name.len();
        }
        None
    };
    // A private method is named only in the files of its type; any other
    // could be named anywhere.
    let found = reshaped.iter().find_map(|&method| {
        let symbol = symbols.get(method);
        let files: Vec<usize> = match symbol.container {
            Some(owner) if symbol.accessibility == rustlyn_semantics::Accessibility::Private => {
                compilation
                    .declaration_nodes(owner)
                    .iter()
                    .map(|&(tree, _)| tree)
                    .collect()
            }
            _ => (0..trees.len()).collect(),
        };
        // The files in as many slices as there are cores, searched at once
        // for the name as text; then each that has it is asked whether a
        // name there is the old member, as the loaded assembly has it.
        let threads = std::thread::available_parallelism().map_or(4, usize::from);
        let slice = files.len().div_ceil(threads).max(1);
        let mentioning: Vec<String> = std::thread::scope(|scope| {
            let searches: Vec<_> = files
                .chunks(slice)
                .map(|part| {
                    let names = &names;
                    let name = symbol.name.as_str();
                    scope.spawn(move || {
                        part.iter()
                            .filter_map(|&index| names(index, name))
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            searches
                .into_iter()
                .flat_map(|search| search.join().unwrap_or_default())
                .collect()
        });
        let owner_name = symbol.container.map(|owner| symbols.qualified_name(owner));
        let old: Vec<SymbolId> = base
            .all_types()
            .find(|ty| Some(base.symbols().qualified_name(ty.id)) == owner_name)
            .map(|ty| base.symbols().lookup(ty.id, &symbol.name).to_vec())
            .unwrap_or_default();
        mentioning
            .into_iter()
            .find(|file| {
                let Some(index) = find_tree(base, file) else {
                    return true;
                };
                let Some(tree) = base.trees().get(index) else {
                    return true;
                };
                let model = rustlyn_semantics::SemanticModel::new(base, index);
                tree.root().descendants().any(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::IdentifierName | SyntaxKind::GenericName
                    ) && node
                        .first_token()
                        .is_some_and(|token| token.text() == symbol.name)
                        && model
                            .symbol_at(&node)
                            .is_some_and(|found| old.is_empty() || old.contains(&found))
                })
            })
            .map(|file| {
                let generic = symbol
                    .as_method()
                    .is_some_and(|method| !method.type_parameters.is_empty());
                (file, symbol.name.clone(), generic)
            })
    });
    trace!("named elsewhere {} ms", searching.elapsed().as_millis());
    match found {
        // A generic method's new body is a method of the patch even when
        // its signature is the same: Mono shares one body among its type
        // arguments, which a jump cannot tell apart.
        Some((file, name, true)) => Err(format!(
            "{name} is generic, so its new body is a new method, and {file} still calls the old one"
        )),
        Some((file, name, false)) => Err(format!(
            "{name} changed its signature, and {file} names it: its code still calls the old one"
        )),
        None => Ok(()),
    }
}

/// Writes the patch for `changed` beside its manifest, compiled against the
/// assembly just built: what it names of the game resolves against the game
/// as it now is, and whatever reaches into private members goes through the
/// assembly's `InternalsVisibleTo`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn make_patch(
    compilation: &Compilation,
    changes: &diff::Changes,
    tailed: &tails::Tailed,
    round: usize,
    options: &ParseOptions,
    images: &[&[u8]],
    assembly: &[u8],
    directory: &Path,
    last_sent: Option<&mut Option<String>>,
    assembly_files: Option<&HashSet<String>>,
) -> Result<PathBuf, String> {
    let writing = Instant::now();
    let symbols = compilation.symbols();
    let tailed_fields: Vec<SymbolId> = changes
        .added_fields
        .iter()
        .chain(
            changes
                .added_properties
                .iter()
                .filter(|property| patch::is_stored(compilation, **property)),
        )
        .copied()
        .filter(|field| {
            !symbols
                .get(*field)
                .modifiers
                .contains(rustlyn_semantics::Modifiers::STATIC)
                && symbols
                    .get(*field)
                    .container
                    .is_some_and(|owner| tailed.of(compilation, owner).is_some())
        })
        .collect();
    let offsets = tails::check(compilation, tailed, &tailed_fields)?;
    let source = patch::write(compilation, changes, round, &offsets, assembly_files)?;
    // An edit the running code does not see — a comment, a member taken
    // away — needs nothing.
    if !source.text.contains(" class ")
        && !source.text.contains(" struct ")
        && !source.text.contains(" enum ")
        && !source.text.contains(" interface ")
    {
        return Ok(PathBuf::new());
    }
    trace!("write {} ms", writing.elapsed().as_millis());
    // The same patch as the last one sent, but for its round: the editor
    // already runs it.
    let unnumbered = source.text.replace(&format!("_{round}"), "_#");
    if last_sent
        .as_deref()
        .is_some_and(|last| last.as_deref() == Some(unnumbered.as_str()))
    {
        return Ok(PathBuf::new());
    }
    let compiling = Instant::now();
    let name = format!("PilotPatch-{round}");
    std::fs::write(directory.join(format!("{name}.cs")), &source.text)
        .map_err(|error| error.to_string())?;
    let tree = parse_with(SourceText::new(format!("{name}.cs"), source.text), options);
    let mut all: Vec<&[u8]> = images.to_vec();
    all.push(assembly);
    let patched = Compilation::create_with_references_as(vec![tree], &all, "PilotPatch")
        .with_options(CompilationOptions {
            allow_unsafe: true,
            writes_readonly_fields: true,
            ..CompilationOptions::default()
        });
    let errors: Vec<String> = patched
        .source_diagnostics()
        .into_iter()
        .map(|entry| patched.render(entry))
        .chain(
            patched
                .semantic_diagnostics()
                .iter()
                .map(|entry| patched.render(entry)),
        )
        .filter(|text| text.contains(": error "))
        .collect();
    if !errors.is_empty() {
        return Err(errors.join("\n"));
    }
    let emitted = crate::emit_library(&patched, "PilotPatch").map_err(|error| error.to_string())?;
    trace!("compile {} ms", compiling.elapsed().as_millis());
    let dll = directory.join(format!("{name}.dll"));
    write_atomically(&dll, &emitted.assembly);
    let manifest: String = source
        .entries
        .iter()
        .map(|entry| {
            format!(
                "{}\t{}\t{}\t{}\t{}\n",
                entry.original_type,
                entry.method,
                entry.parameters.join(","),
                entry.patch_type,
                entry.patch_method
            )
        })
        .collect();
    std::fs::write(dll.with_extension("txt"), manifest).map_err(|error| error.to_string())?;
    if let Some(last) = last_sent {
        *last = Some(unnumbered);
    }
    Ok(dll)
}

/// The first error in the files at `paths`, as a compiler prints it: what
/// does not parse, or else what does not bind in a body.
pub fn broken(compilation: &Compilation, paths: &[String]) -> Option<String> {
    // An editor writing a file in place leaves it empty for a moment; an
    // edited file left empty is that moment more often than a wish.
    if let Some(path) = paths
        .iter()
        .find(|path| std::fs::metadata(path).is_ok_and(|file| file.len() == 0))
    {
        return Some(format!("{path}: the file is empty"));
    }
    let indices: Vec<usize> = paths
        .iter()
        .filter_map(|path| find_tree(compilation, path))
        .collect();
    let trees = compilation.trees();
    for &index in &indices {
        let tree = trees.get(index)?;
        if let Some(entry) = tree.diagnostics().iter().find(|entry| entry.is_error()) {
            return Some(entry.display_with(tree.source()).to_string());
        }
    }
    // What binds in a body is asked of the files someone saved — listed by
    // their path in the project — not of what the generators wrote for them.
    let saved: Vec<usize> = paths
        .iter()
        .filter(|path| !Path::new(path.as_str()).is_absolute())
        .filter_map(|path| find_tree(compilation, path))
        .collect();
    for &index in &saved {
        let tree = trees.get(index)?;
        let model = rustlyn_semantics::SemanticModel::new(compilation, index);
        if let Some((_, entry)) = model
            .body_diagnostics()
            .into_iter()
            .find(|(_, entry)| entry.is_error())
        {
            return Some(entry.display_with(tree.source()).to_string());
        }
    }
    None
}

/// The tree read from `path`: by its name as listed, or else by the file it
/// names — which asks the file system about every tree, so it comes second.
pub fn find_tree(compilation: &Compilation, path: &str) -> Option<usize> {
    let trees = compilation.trees();
    let named = |index: usize, wanted: &dyn Fn(&str) -> bool| {
        trees
            .source(index)
            .is_some_and(|source| wanted(source.name()))
    };
    (0..trees.len())
        .find(|&index| named(index, &|name| name == path))
        .or_else(|| {
            let given = std::fs::canonicalize(path).ok()?;
            (0..trees.len()).find(|&index| {
                named(index, &|name| {
                    std::fs::canonicalize(name).is_ok_and(|listed| listed == given)
                })
            })
        })
}

/// Writes the assembly beside its place and moves it there, so that a
/// reader never sees half of it and one that has the old file open keeps it.
pub fn write_atomically(path: &Path, bytes: &[u8]) {
    let temporary = path.with_extension("dll.writing");
    std::fs::write(&temporary, bytes).expect("the assembly should be writable");
    std::fs::rename(&temporary, path).expect("the assembly should be movable into place");
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_syntax::parse;
    use rustlyn_text::SourceText;

    fn compile(files: &[(&str, &str)]) -> Compilation {
        Compilation::create(
            files
                .iter()
                .map(|(name, text)| parse(SourceText::new(*name, *text)))
                .collect(),
        )
    }

    /// Why an edited method that another file calls is a reload, as the
    /// editor's window says it: a generic one has not changed its signature.
    fn reason(before: &str, after: &str) -> String {
        let caller = "class C { void N() { A.M<C>(); } }";
        let base = compile(&[("A.cs", before), ("C.cs", caller)]);
        let current = compile(&[("A.cs", after), ("C.cs", caller)]);
        let paths = vec!["A.cs".to_string()];
        let changes = diff::changes(
            &base,
            &current,
            "A.cs",
            &diff::type_names(&base),
            &HashSet::new(),
        )
        .expect("an edit a patch can carry");
        named_elsewhere(&base, &current, &changes.reshaped, &paths)
            .expect_err("another file calls it")
    }

    #[test]
    fn a_generic_methods_new_body_is_a_reload_for_being_generic_not_for_its_signature() {
        let said = reason(
            "static class A { public static T M<T>() where T : class => null; }",
            "static class A { public static T M<T>() where T : class { var (a, b) = (1, 2); return null; } }",
        );
        assert!(
            said.contains("M is generic") && said.contains("C.cs"),
            "{said}"
        );
        assert!(!said.contains("signature"), "{said}");
    }

    #[test]
    fn a_generic_types_constructor_is_a_reload_that_says_so() {
        let before = "class B<T> { int n; public B(int n) { this.n = n; } }";
        let after = "class B<T> { int n; public B(int n) { this.n = n + 1; } }";
        let base = compile(&[("B.cs", before)]);
        let current = compile(&[("B.cs", after)]);
        let said = diff::changes(
            &base,
            &current,
            "B.cs",
            &diff::type_names(&base),
            &HashSet::new(),
        )
        .err()
        .expect("a reload");
        assert!(said.contains("a generic type's constructor"), "{said}");
    }
}
