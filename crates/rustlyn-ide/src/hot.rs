//! Hot reload for a Unity project: what a save changed in Assembly-CSharp,
//! as a small assembly the running editor sends the old methods to, made
//! from the compilation the editor already keeps.
//!
//! The editor Unity runs is given a build of Assembly-CSharp made here — its
//! files as Unity's own response file lists them, what Unity's source
//! generators write for them, every member opened to the patches and every
//! struct a tail for the fields an edit adds (see `rustlyn_emit::hot`). The
//! compilation the IDE keeps is the base the patches are measured against:
//! it holds every file of the project, so it is the same base for the
//! patches as long as its generated code is the one that build was made
//! with — which is why, once hot reload starts, the IDE compiles what the
//! generators write here rather than what Unity's last compile left.
//!
//! The generators are .NET processes (`tools/unity/gend`, which runs all of
//! them over the assembly, and `tools/unity/minigen`, which runs them over
//! one saved file in milliseconds).

use std::collections::{HashMap, HashSet};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::Arc;
use std::time::Instant;

use rustlyn_emit::hot::{PATCH_ACCESS, Session as Patches, TAIL_SUPPORT, Tails};
use rustlyn_semantics::Compilation;
use rustlyn_syntax::{ParseOptions, SyntaxTree, parse_with};
use rustlyn_text::SourceText;

use crate::semantic::Semantic;

/// Where the tools hot reload runs are.
#[derive(Clone, Debug)]
pub struct Tools {
    /// `dotnet`, to run the generators with.
    pub dotnet: PathBuf,
    /// `gend.dll`: every generator over the whole assembly, once.
    pub gend: PathBuf,
    /// `minigen.dll`: the generators over one saved file.
    pub minigen: PathBuf,
    /// `PilotRuntime.dll`, which patches call into.
    pub runtime: PathBuf,
}

/// Assembly-CSharp as Unity compiles it, out of its response file.
#[derive(Clone, Debug, Default)]
pub struct Response {
    pub path: PathBuf,
    /// The files, relative to the project.
    pub sources: Vec<PathBuf>,
    pub references: Vec<PathBuf>,
    pub defines: Vec<String>,
}

impl Response {
    /// The editor's response file for Assembly-CSharp under `project`: the
    /// newest of the editor's debug builds Unity has made.
    ///
    /// # Errors
    /// Where Unity has not compiled the project.
    pub fn find(project: &Path) -> Result<Self, String> {
        let artifacts = project.join("Library/Bee/artifacts");
        let mut found: Vec<(std::time::SystemTime, PathBuf)> = std::fs::read_dir(&artifacts)
            .map_err(|error| format!("{}: {error}", artifacts.display()))?
            .flatten()
            .filter(|entry| entry.file_name().to_string_lossy().ends_with("EDbg.dag"))
            .map(|entry| entry.path().join("Assembly-CSharp.rsp"))
            .filter_map(|path| Some((std::fs::metadata(&path).ok()?.modified().ok()?, path)))
            .collect();
        found.sort();
        let (_, path) = found
            .pop()
            .ok_or("Unity has not compiled Assembly-CSharp for the editor yet")?;
        let text = std::fs::read_to_string(&path).map_err(|error| error.to_string())?;
        let mut response = Self {
            path,
            ..Self::default()
        };
        for line in text.lines().map(str::trim) {
            let value = |prefix: &str| {
                line.strip_prefix(prefix)
                    .map(|rest| rest.trim_matches('"').to_string())
            };
            if let Some(reference) = value("-r:").or_else(|| value("/reference:")) {
                let reference = PathBuf::from(reference);
                response.references.push(if reference.is_absolute() {
                    reference
                } else {
                    project.join(reference)
                });
            } else if let Some(define) = value("-define:").or_else(|| value("/define:")) {
                response.defines.extend(
                    define
                        .split(';')
                        .filter(|name| !name.is_empty())
                        .map(str::to_string),
                );
            } else if !line.starts_with(['-', '/']) && line.trim_matches('"').ends_with(".cs") {
                response.sources.push(PathBuf::from(line.trim_matches('"')));
            }
        }
        Ok(response)
    }
}

/// A generator process: a path per line in, `gen <ms>` and the files it
/// wrote out, a tab before each.
struct Generators {
    process: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

impl Generators {
    fn start(command: &mut Command, ready: &str) -> Result<(Self, String), String> {
        let mut process = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|error| format!("the generators did not start: {error}"))?;
        let input = process.stdin.take().ok_or("no input")?;
        let output = BufReader::new(process.stdout.take().ok_or("no output")?);
        let mut started = Self {
            process,
            input,
            output,
        };
        let said = started.until(ready)?;
        Ok((started, said))
    }

    fn until(&mut self, head: &str) -> Result<String, String> {
        loop {
            let mut line = String::new();
            if self
                .output
                .read_line(&mut line)
                .map_err(|error| error.to_string())?
                == 0
            {
                return Err("the generators stopped".to_string());
            }
            if line.starts_with(head) {
                return Ok(line.trim_end().to_string());
            }
            if line.starts_with("failed") {
                return Err(line.trim().to_string());
            }
        }
    }

    /// What the generators wrote for `path`; a `-` before one it deleted.
    /// `path` is relative to `project`, as the generators name it; whether
    /// it is still there is asked of the project, not of whatever directory
    /// this process runs in — an editor's is `/`.
    fn run(&mut self, project: &Path, path: &Path) -> Result<Vec<String>, String> {
        let line = if project.join(path).exists() {
            path.display().to_string()
        } else {
            format!("delete {}", path.display())
        };
        writeln!(self.input, "{line}").map_err(|error| error.to_string())?;
        self.input.flush().map_err(|error| error.to_string())?;
        let said = self.until("gen")?;
        Ok(said.split('\t').skip(1).map(str::to_string).collect())
    }
}

impl Drop for Generators {
    fn drop(&mut self) {
        let _ = writeln!(self.input, "quit");
        let _ = self.process.kill();
    }
}

/// What a save comes to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// A patch for the editor: the assembly, and each method it replaces
    /// (`Type::Method`).
    Patch {
        assembly: PathBuf,
        methods: Vec<String>,
    },
    /// Nothing that runs changed: spacing, comments.
    Unchanged,
    /// The file does not compile, which a save in the middle of typing is.
    Broken(String),
    /// Only a whole build and a reload carry the edit; why.
    Reload(String),
    /// Not a file of Assembly-CSharp: Unity builds it, not hot reload.
    Outside,
}

/// Whether Unity compiles `path`, a `.cs` file of `project`, into
/// Assembly-CSharp: under `Assets`, with no assembly definition (or
/// reference) in a folder above it, and not in an `Editor` folder (that is
/// Assembly-CSharp-Editor) or under `Assets/Plugins`, `Assets/Standard
/// Assets` or `Assets/Pro Standard Assets` (the firstpass assemblies).
#[must_use]
pub fn in_assembly_csharp(project: &Path, path: &Path) -> bool {
    let assets = project.join("Assets");
    let Ok(inside) = path.strip_prefix(&assets) else {
        return false;
    };
    if path.extension().is_none_or(|extension| extension != "cs") {
        return false;
    }
    let folders: Vec<&std::ffi::OsStr> = inside
        .parent()
        .map(|parent| parent.iter().collect())
        .unwrap_or_default();
    if folders.first().is_some_and(|first| {
        ["Plugins", "Standard Assets", "Pro Standard Assets"]
            .iter()
            .any(|name| first == name)
    }) {
        return false;
    }
    if folders.iter().any(|folder| *folder == "Editor") {
        return false;
    }
    let mut folder = path.parent();
    while let Some(at) = folder {
        let defines = std::fs::read_dir(at)
            .into_iter()
            .flatten()
            .flatten()
            .any(|entry| {
                entry
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "asmdef" || extension == "asmref")
            });
        if defines {
            return false;
        }
        if at == assets {
            break;
        }
        folder = at.parent();
    }
    true
}

/// A type the file at `path` declares that the editor's build has, a part of
/// it from a file gone since — the file renamed or moved. A patch speaks of a file's
/// types as the build had them there: of one it never had, it would make a
/// patch of nothing.
fn moved_type(base: &Compilation, current: &Compilation, path: &Path) -> Option<String> {
    let name = path.display().to_string();
    if rustlyn_emit::hot::find_tree(base, &name).is_some() {
        return None;
    }
    let tree = rustlyn_emit::hot::find_tree(current, &name)?;
    let symbols = current.symbols();
    let base_trees = base.trees();
    current
        .all_types()
        .filter(|ty| {
            symbols
                .get(ty.id)
                .locations
                .iter()
                .any(|location| location.tree == tree)
        })
        .find_map(|ty| {
            let qualified = symbols.metadata_qualified_name(ty.id);
            let before = base.type_by_metadata_name(&qualified)?;
            // A part of it whose file is gone: a `partial` type keeps its
            // generated part where it was, and a new part beside parts that
            // are all still there is a part added, not one moved.
            let gone = base.symbols().get(before).locations.iter().any(|location| {
                base_trees
                    .source(location.tree)
                    .is_some_and(|source| !Path::new(source.name()).exists())
            });
            gone.then_some(qualified)
        })
}

/// The build the editor loads, and what has been sent to it since.
pub struct Hot {
    project: PathBuf,
    work: PathBuf,
    tools: Tools,
    response: Response,
    /// The IDE's compilation the build was made beside: what patches are
    /// measured against.
    base: Arc<Semantic>,
    patches: Patches,
    minigen: Generators,
    /// Assembly-CSharp's files, as absolute paths.
    members: std::collections::HashSet<PathBuf>,
}

impl std::fmt::Debug for Hot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Hot")
            .field("project", &self.project)
            .field("work", &self.work)
            .finish_non_exhaustive()
    }
}

/// What a whole build made.
#[derive(Clone, Debug)]
pub struct Built {
    /// The assembly for the editor to load.
    pub assembly: PathBuf,
    pub milliseconds: u64,
    /// Members the build could not make, stubbed instead.
    pub stubs: usize,
}

/// Where hot reload keeps what it makes for `project`: under `Library`,
/// which Unity keeps, not `Temp`, which it empties when it starts.
#[must_use]
pub fn work_directory(project: &Path) -> PathBuf {
    project.join("Library/PilotHot")
}

/// What every generator writes for Assembly-CSharp, into `generated`.
///
/// # Errors
/// Where the generators do not start or do not finish.
pub fn generate_all(
    tools: &Tools,
    project: &Path,
    response: &Response,
    generated: &Path,
) -> Result<String, String> {
    std::fs::create_dir_all(generated).map_err(|error| error.to_string())?;
    // The files as they are — with those added since Unity's last compile,
    // which its response file does not list — rather than the response
    // file's.
    let list = generated.with_file_name("gend-sources.txt");
    let relative: Vec<String> = response
        .sources
        .iter()
        .filter(|path| !path.is_absolute())
        .map(|path| path.display().to_string())
        .collect();
    std::fs::write(&list, relative.join("\n") + "\n").map_err(|error| error.to_string())?;
    // What the generators read is what they wrote last time from it — a
    // second start of hot reload over files no one changed since — and what
    // they wrote is still there, kept up to date save by save.
    let stamp = generator_inputs(tools, project, response);
    let stamp_file = generated.with_file_name("gend-stamp");
    let have_output =
        std::fs::read_dir(generated).is_ok_and(|mut entries| entries.next().is_some());
    if have_output && std::fs::read_to_string(&stamp_file).is_ok_and(|kept| kept == stamp) {
        return Ok("unchanged since the last run".to_string());
    }
    let _ = std::fs::remove_file(&stamp_file);
    let mut command = Command::new(&tools.dotnet);
    command
        .arg(&tools.gend)
        .arg(&response.path)
        .arg(project)
        .arg(generated)
        .arg(&list)
        .current_dir(project);
    let (_gend, said) = Generators::start(&mut command, "ready")?;
    let _ = std::fs::write(&stamp_file, stamp);
    Ok(said.split('\t').next().unwrap_or_default().to_string())
}

/// Everything the whole-assembly generators read, by size and time: the
/// response file, the generator runner and each source.
fn generator_inputs(tools: &Tools, project: &Path, response: &Response) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    let mut stamp = |path: &Path| {
        path.hash(&mut hasher);
        crate::project::stamp_of(path).hash(&mut hasher);
    };
    stamp(&response.path);
    stamp(&tools.gend);
    for source in &response.sources {
        stamp(&project.join(source));
    }
    format!("{:016x} {}", hasher.finish(), response.sources.len())
}

/// The symbols the `#if` and `#elif` lines of `text` ask about.
pub fn directive_symbols(text: &str) -> HashSet<String> {
    let mut found = HashSet::new();
    for line in text.lines() {
        let Some(directive) = line.trim_start().strip_prefix('#') else {
            continue;
        };
        let directive = directive.trim_start();
        let Some(condition) = directive
            .strip_prefix("elif")
            .or_else(|| directive.strip_prefix("if"))
        else {
            continue;
        };
        if condition.starts_with(|c: char| c.is_alphanumeric() || c == '_') {
            continue;
        }
        let condition = condition.split("//").next().unwrap_or_default();
        found.extend(
            condition
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .filter(|word| word.starts_with(|c: char| c.is_alphabetic() || c == '_'))
                .filter(|word| *word != "true" && *word != "false")
                .map(str::to_string),
        );
    }
    found
}

/// The symbols one of the two lists defines and the other does not.
fn disagreeing(one: &[String], other: &[String]) -> HashSet<String> {
    let one: HashSet<&String> = one.iter().collect();
    let other: HashSet<&String> = other.iter().collect();
    one.symmetric_difference(&other)
        .map(|symbol| (*symbol).clone())
        .collect()
}

/// The IDE's trees of `base` by file name, for [`build_whole`] to take
/// rather than parse again.
pub fn parsed_trees(base: &Semantic) -> HashMap<String, SyntaxTree> {
    let trees = base.compilation().trees();
    (0..trees.len())
        .filter_map(|index| trees.get(index))
        .map(|tree| (tree.source().name().to_string(), tree.clone()))
        .collect()
}

/// The whole build of Assembly-CSharp an editor loads: Unity's files, what
/// the generators wrote into `generated`, the tails' types and the patches'
/// access, built with every member opened to the patches.
///
/// # Errors
/// What keeps it from being built.
pub fn build_whole(
    project: &Path,
    response: &Response,
    sources: &[PathBuf],
    generated: &Path,
    assembly: &Path,
    parsed: &HashMap<String, SyntaxTree>,
) -> Result<(Built, Tails, Vec<u8>), String> {
    let started = Instant::now();
    let options = ParseOptions::with_symbols(response.defines.clone());
    // A file the IDE already parsed, to the same text and language version,
    // is the tree parsing it again would make — with Unity's symbols, where
    // no `#if` of it asks about one the IDE's union of every project's
    // symbols disagrees on.
    let blank = parse_with(SourceText::new("", ""), &options);
    let symbols = blank.defined().to_vec();
    let reused = |tree: &SyntaxTree, text: &str| -> Option<SyntaxTree> {
        let same_text = tree.source().text().trim_start_matches('\u{feff}')
            == text.trim_start_matches('\u{feff}');
        if !same_text || tree.language_version() != blank.language_version() {
            return None;
        }
        let disagree = disagreeing(tree.defined(), &symbols);
        directive_symbols(text)
            .is_disjoint(&disagree)
            .then(|| tree.with_symbols(symbols.clone()))
    };
    let mut files: Vec<PathBuf> = sources.iter().map(|path| project.join(path)).collect();
    let mut made = Vec::new();
    crate::project::files_under(generated, &mut made);
    made.sort();
    files.extend(made);
    let taken = std::sync::atomic::AtomicUsize::new(0);
    let reading = rustlyn_semantics::timing::phase("whole: read and parse");
    let texts: Vec<Option<(PathBuf, String)>> = crate::semantic::parallel(files.len(), |index| {
        let text = std::fs::read_to_string(&files[index]).ok()?;
        Some((files[index].clone(), text))
    });
    let mut trees: Vec<_> = crate::semantic::parallel(texts.len(), |index| {
        texts[index].as_ref().map(|(path, text)| {
            let name = path.to_string_lossy();
            match parsed
                .get(name.as_ref())
                .and_then(|tree| reused(tree, text))
            {
                Some(tree) => {
                    taken.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    tree
                }
                None => parse_with(SourceText::new(name, text.as_str()), &options),
            }
        })
    })
    .into_iter()
    .flatten()
    .collect();
    trees.push(parse_with(
        SourceText::new("PilotTails.cs", TAIL_SUPPORT),
        &options,
    ));
    trees.push(parse_with(
        SourceText::new("PilotPatchAccess.cs", PATCH_ACCESS),
        &options,
    ));
    drop(reading);
    if std::env::var_os("RUSTLYN_TIMINGS").is_some() {
        eprintln!(
            "whole: {} of {} trees the IDE's",
            taken.into_inner(),
            trees.len()
        );
    }
    let bytes: Vec<Vec<u8>> = response
        .references
        .iter()
        .filter_map(|path| std::fs::read(path).ok())
        .collect();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(trees, &images);
    let _emitting = rustlyn_semantics::timing::phase("whole: emit and write");
    let tails = Tails::choose(&compilation);
    let (_, emitted, skipped) = rustlyn_emit::incremental_with(
        &compilation,
        "Assembly-CSharp",
        rustlyn_emit::IncrementalOptions {
            widen_for_patches: true,
            struct_tails: tails.struct_tails(),
        },
    )
    .map_err(|error| error.to_string())?;
    if let Some(parent) = assembly.parent() {
        std::fs::create_dir_all(parent).map_err(|error| error.to_string())?;
    }
    rustlyn_emit::hot::write_atomically(assembly, &emitted.assembly);
    // What the build stubbed — methods that throw in the editor rather than
    // run — is listed beside it, one per line with why.
    let stubs: String = skipped
        .iter()
        .map(|(method, why)| format!("{method}\t{}\n", why.replace('\n', " ")))
        .collect();
    let _ = std::fs::write(assembly.with_file_name("stubs.txt"), stubs);
    Ok((
        Built {
            assembly: assembly.to_path_buf(),
            milliseconds: started.elapsed().as_millis() as u64,
            stubs: skipped.len(),
        },
        tails,
        emitted.assembly,
    ))
}

impl Hot {
    /// Hot reload over `base`, the IDE's compilation of the project with the
    /// generated code in `work/generated`, for an editor that loads `built`.
    ///
    /// # Errors
    /// Where minigen does not start.
    pub fn new(
        project: &Path,
        tools: Tools,
        response: Response,
        base: Arc<Semantic>,
        tails: Tails,
        image: Vec<u8>,
        built: &Built,
    ) -> Result<Self, String> {
        let work = work_directory(project);
        let generated = work.join("generated");
        let list = work.join("sources.txt");
        let mut listed: Vec<String> = response
            .sources
            .iter()
            .map(|path| path.display().to_string())
            .collect();
        let mut made = Vec::new();
        crate::project::files_under(&generated, &mut made);
        listed.extend(made.iter().map(|path| path.display().to_string()));
        std::fs::write(&list, listed.join("\n") + "\n").map_err(|error| error.to_string())?;
        let mut command = Command::new(&tools.dotnet);
        command
            .arg(&tools.minigen)
            .arg(&response.path)
            .arg(project)
            .arg(&generated)
            .arg(&built.assembly)
            .arg("UpdateMiddleware\\(|InjectionResolver\\(")
            .arg(&list)
            .current_dir(project);
        let (minigen, _) = Generators::start(&mut command, "ready")?;
        let mut references: Vec<Arc<[u8]>> = response
            .references
            .iter()
            .filter_map(|path| std::fs::read(path).ok().map(Arc::<[u8]>::from))
            .collect();
        if let Ok(runtime) = std::fs::read(&tools.runtime) {
            references.push(Arc::from(runtime));
        }
        let patches_directory = work.join("patches");
        // A new session numbers its patches from one again: what an earlier
        // one wrote is only in the way (the editor read its patches' bytes).
        let _ = std::fs::remove_dir_all(&patches_directory);
        std::fs::create_dir_all(&patches_directory).map_err(|error| error.to_string())?;
        let patches = Patches::new(
            base.compilation(),
            image,
            tails,
            references,
            patches_directory,
            ParseOptions::with_symbols(response.defines.clone()),
        );
        let members: std::collections::HashSet<PathBuf> = response
            .sources
            .iter()
            .map(|path| project.join(path))
            .collect();
        let mut patches = patches;
        patches.set_assembly_files(
            members
                .iter()
                .map(|path| path.display().to_string())
                .collect(),
        );
        Ok(Self {
            project: project.to_path_buf(),
            work,
            tools,
            response,
            base,
            patches,
            minigen,
            members,
        })
    }

    /// The folder of generated code the IDE compiles while hot reload runs.
    #[must_use]
    pub fn generated(&self) -> PathBuf {
        self.work.join("generated")
    }

    #[must_use]
    pub fn tools(&self) -> &Tools {
        &self.tools
    }

    /// The text of the file at `path` in the compilation the editor's build
    /// was made beside, as the build has it.
    #[must_use]
    pub fn base_text(&self, path: &Path) -> Option<String> {
        let name = path.display().to_string();
        let trees = self.base.compilation().trees();
        (0..trees.len())
            .filter_map(|index| trees.get(index))
            .find(|tree| tree.source().name() == name)
            .map(|tree| tree.source().text().to_string())
    }

    #[must_use]
    pub fn response(&self) -> &Response {
        &self.response
    }

    /// Runs the generators over the saved files: what they wrote, as the
    /// IDE names files (absolute), a `-` before what they deleted.
    ///
    /// # Errors
    /// Where the generators fail.
    pub fn generate(&mut self, saved: &[PathBuf]) -> Result<Vec<String>, String> {
        let mut written = Vec::new();
        for path in saved {
            let relative = path.strip_prefix(&self.project).unwrap_or(path);
            for file in self.minigen.run(&self.project, relative)? {
                let (gone, file) = file
                    .strip_prefix('-')
                    .map_or((false, file.as_str()), |rest| (true, rest));
                let absolute = if Path::new(file).is_absolute() {
                    PathBuf::from(file)
                } else {
                    self.project.join(file)
                };
                written.push(format!(
                    "{}{}",
                    if gone { "-" } else { "" },
                    absolute.display()
                ));
            }
        }
        Ok(written)
    }

    /// Why the IDE reads one of `paths` otherwise than Unity compiles it, if
    /// it does: an `#if` on a symbol only one of them defines.
    fn read_otherwise(&self, current: &Semantic, paths: &[String]) -> Option<String> {
        let trees = current.compilation().trees();
        for path in paths {
            let Some(tree) = (0..trees.len())
                .filter_map(|index| trees.get(index))
                .find(|tree| tree.source().name() == path)
            else {
                continue;
            };
            let disagree = disagreeing(tree.defined(), &self.response.defines);
            let asked = directive_symbols(tree.source().text());
            if let Some(symbol) = asked.intersection(&disagree).min() {
                let defined = self.response.defines.contains(symbol);
                return Some(format!(
                    "{path}: #if {symbol} — Unity compiles Assembly-CSharp {} it, the IDE reads the file {} it: a whole build carries it",
                    if defined { "with" } else { "without" },
                    if defined { "without" } else { "with" },
                ));
            }
        }
        None
    }

    /// What the saves of `saved` (and what the generators wrote for them)
    /// come to, `current` being the IDE's compilation of the project as it
    /// now is.
    pub fn answer(
        &mut self,
        current: &Semantic,
        saved: &[PathBuf],
        generated: &[String],
    ) -> Answer {
        // A file added since the editor's build is Assembly-CSharp's where
        // Unity would put it there.
        for path in saved {
            if !self.members.contains(path)
                && path.exists()
                && in_assembly_csharp(&self.project, path)
            {
                self.members.insert(path.clone());
                self.patches.add_assembly_file(path.display().to_string());
            }
        }
        if saved.iter().all(|path| !self.members.contains(path)) {
            return Answer::Outside;
        }
        let mut paths: Vec<String> = saved
            .iter()
            .map(|path| path.display().to_string())
            .collect();
        paths.extend(
            generated
                .iter()
                .filter(|path| !path.starts_with('-'))
                .cloned(),
        );
        if let Some(why) = rustlyn_emit::hot::broken(current.compilation(), &paths) {
            return Answer::Broken(why);
        }
        // The IDE reads every file with the symbols of all the projects: a
        // patch made of a file whose `#if` asks about one Unity does not give
        // Assembly-CSharp (or the other way round) would be of code Unity
        // does not compile.
        if let Some(why) = self.read_otherwise(current, &paths) {
            return Answer::Reload(why);
        }
        for path in saved {
            if let Some(moved) = moved_type(self.base.compilation(), current.compilation(), path) {
                return Answer::Reload(format!(
                    "{moved} moved to {}: a whole build carries it",
                    path.display()
                ));
            }
        }
        match self
            .patches
            .patch(self.base.compilation(), current.compilation(), &paths)
        {
            // A patch of nothing: what changed is nothing the running code
            // sees — a comment, a member taken away.
            Ok(None) => Answer::Unchanged,
            Ok(Some(assembly)) if assembly.as_os_str().is_empty() => Answer::Unchanged,
            Ok(Some(assembly)) => {
                let methods = std::fs::read_to_string(assembly.with_extension("txt"))
                    .unwrap_or_default()
                    .lines()
                    .filter_map(|line| {
                        let mut parts = line.split('\t');
                        Some(format!("{}::{}", parts.next()?, parts.next()?))
                    })
                    .collect();
                Answer::Patch { assembly, methods }
            }
            Err(why) => Answer::Reload(why),
        }
    }

    /// Assembly-CSharp's files as they are now: Unity's list when the
    /// editor's build was made, and what was added since; what is gone is
    /// left out.
    #[must_use]
    pub fn sources(&self) -> Vec<PathBuf> {
        let mut sources: Vec<PathBuf> = self
            .members
            .iter()
            .filter(|path| path.exists())
            .cloned()
            .collect();
        sources.sort();
        sources
    }

    /// The editor loaded a whole build again, made beside `base`.
    pub fn reloaded(&mut self, base: Arc<Semantic>, image: Vec<u8>) {
        self.patches.reloaded(base.compilation(), image);
        self.base = base;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_symbols_an_if_asks_about_are_found_and_nothing_else() {
        let text = "#if UNITY_EDITOR && !FBX_EXPORTER\n  #elif (A || B_2) // C\n#endif\n#region IFFY\n#define D\nvar x = 1; // #if E\n#if true\n#endif";
        let found = directive_symbols(text);
        let mut found: Vec<&str> = found.iter().map(String::as_str).collect();
        found.sort_unstable();
        assert_eq!(found, ["A", "B_2", "FBX_EXPORTER", "UNITY_EDITOR"]);
    }

    #[test]
    fn a_new_file_is_assembly_csharps_where_unity_would_compile_it_there() {
        let project =
            std::env::temp_dir().join(format!("rustlyn-hot-members-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&project);
        for folder in [
            "Assets/Game",
            "Assets/Game/Editor",
            "Assets/Plugins/Lib",
            "Assets/Module/Code",
        ] {
            std::fs::create_dir_all(project.join(folder)).expect("a temporary folder");
        }
        std::fs::write(project.join("Assets/Module/Module.asmdef"), "{}").expect("writable");
        let member = |path: &str| in_assembly_csharp(&project, &project.join(path));
        assert!(member("Assets/Game/New.cs"));
        assert!(member("Assets/Top.cs"));
        assert!(
            !member("Assets/Game/Editor/Tool.cs"),
            "Assembly-CSharp-Editor"
        );
        assert!(!member("Assets/Plugins/Lib/Lib.cs"), "firstpass");
        assert!(!member("Assets/Module/Code/Part.cs"), "its own assembly");
        assert!(!member("Packages/Some/Thing.cs"));
        assert!(!member("Assets/Game/Notes.txt"));
        let _ = std::fs::remove_dir_all(&project);
    }
}
