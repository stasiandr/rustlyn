//! What the project is: which files are compiled together, against which
//! assemblies, with which preprocessor symbols.
//!
//! A compiler is told all of this on its command line. An editor opening a
//! folder is told nothing, and the usual way to find out is to ask MSBuild —
//! which is what makes a language server take a minute before it answers
//! anything. MSBuild is a programming language; most of what it computes for a
//! C# project is nevertheless written down in a handful of places that can be
//! read directly:
//!
//! * a **`.csproj`** names its references (`HintPath`), its symbols
//!   (`DefineConstants`), its target framework and, in the old format Unity
//!   still writes, every file it compiles;
//! * **`obj/project.assets.json`**, left behind by a restore, lists every
//!   package assembly the project compiles against, transitively;
//! * a **.NET install** keeps the framework's reference assemblies in
//!   `packs/Microsoft.NETCore.App.Ref`;
//! * a **Unity project** with no project files at all — a fresh clone, since
//!   Unity does not commit them — still says which editor it belongs to, and
//!   the editor's assemblies are where they always are.
//!
//! Reading those is milliseconds rather than a minute. What it misses is what
//! only evaluating MSBuild would find — a reference added by a target, a
//! symbol set by a property function — and the cost of missing it is a name
//! that does not resolve, which the editor answers from its index instead.
//! Nothing here is ever fatal: a project that cannot be read is a folder of
//! `.cs` files against the newest framework on the machine.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::formats::json::Json;
use crate::formats::xml::{Reader as Xml, Tag as Element};

/// A path with the length and modification time it was seen at.
type Stamped = (PathBuf, (u64, u128));

/// The files asked about, the stamps of their folders, and the answer kept.
type KeptListing = (Vec<PathBuf>, Vec<(u64, u128)>, GeneratedListing);

/// Generated files to compile, and for each one kept that others had the same
/// text as, those others: a generator writes the same file for each assembly
/// it runs in.
type GeneratedListing = (Vec<PathBuf>, Vec<(PathBuf, PathBuf)>);

/// How the project was worked out, which is what an editor shows for it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProjectKind {
    /// From `.csproj` files.
    Msbuild,
    /// A Unity project without project files, from the editor it belongs to.
    Unity,
    /// Neither: every `.cs` file, against the newest framework installed.
    Folder,
}

/// Everything a compilation needs besides the text of the files.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Project {
    pub kind: ProjectKind,
    /// How many `.csproj` files went into this.
    pub projects: usize,
    /// Directories whose `.cs` files are compiled, for projects in the SDK
    /// format, which compiles whatever is under it.
    pub roots: Vec<PathBuf>,
    /// Files named one by one: the old project format lists them, and a
    /// Unity package cache is outside anything an editor indexes.
    pub files: Vec<PathBuf>,
    /// Whether files outside `roots` and `files` are compiled too. True when
    /// there were no project files to say otherwise.
    pub everything: bool,
    /// Assemblies to compile against, one per assembly name.
    pub references: Vec<PathBuf>,
    /// Preprocessor symbols, the union over every project.
    pub symbols: Vec<String>,
    /// Source nobody wrote but every file sees, such as the `global using`
    /// directives the SDK generates for `<ImplicitUsings>`.
    pub generated: String,
    /// The assemblies the source is built into, one per project: a
    /// reference that names one of them in an `[InternalsVisibleTo]` shows
    /// it its internals. Unity's engine does that for its own packages.
    pub assemblies: Vec<String>,
    /// Which of `assemblies` a file named in a project goes into, by its
    /// index there.
    pub owned_files: Vec<(PathBuf, u16)>,
    /// The same for every file under a folder: an SDK project's, and the
    /// folder Unity's generators write an assembly's code to.
    pub owned_folders: Vec<(PathBuf, u16)>,
    /// The version of C# each of `assemblies` is written in, as its project
    /// says (`9.0`, `latest`), empty where it says nothing.
    pub language_versions: Vec<String>,
    /// Whether a file found by the editor is compiled only when it goes into
    /// one of `assemblies` that is built: Unity compiles nothing outside its
    /// assemblies — a generator's own solution beside `Assets/`, a package's
    /// tests it was not asked to build.
    pub owned_only: bool,
    /// Which of `assemblies` are not built, by index: an assembly definition
    /// Unity has neither a project file nor a compile for.
    pub unbuilt: Vec<u16>,
    /// The preprocessor symbols each of `assemblies` is compiled with, where
    /// its project or Unity's last compile of it says; empty for `symbols`.
    pub assembly_symbols: Vec<Vec<String>>,
    /// Which of `assemblies` each one references, by index; `u16::MAX` in a
    /// list where nothing says, which counts as all of them.
    pub assembly_references: Vec<Vec<u16>>,
    /// More assemblies a file goes into besides its own: generated code that
    /// several assemblies had a copy of, compiled once.
    pub shared_files: Vec<(PathBuf, u16)>,
    /// The precompiled assemblies each of `assemblies` references, by file
    /// name without its extension, lowercased; empty where nothing says,
    /// which counts as all of them. Two references may declare one type —
    /// two copies of Cecil — and an assembly means the one it references.
    pub assembly_metadata: Vec<Vec<String>>,
    /// Which compiler warnings each of `assemblies` is built with, by index;
    /// empty where nothing says, which is all of them. Unity builds its
    /// packages with `-warn:0`, and most assemblies with `-nowarn:0169`.
    pub assembly_warnings: Vec<WarningOptions>,
    /// Whether each of `assemblies` annotates its reference types where no
    /// `#nullable` says (`-nullable:enable`, `<Nullable>enable</Nullable>`),
    /// by index; empty where nothing says, which is no.
    pub assembly_nullable: Vec<bool>,
}

/// What a `-nullable:` or `<Nullable>` setting says of annotations:
/// `enable` and `annotations` turn them on.
fn nullable_annotations(setting: &str) -> bool {
    matches!(
        setting
            .trim()
            .trim_matches('"')
            .to_ascii_lowercase()
            .as_str(),
        "enable" | "annotations"
    )
}

/// What a project says of the compiler's warnings: `<WarningLevel>` or
/// `-warn:`, where `0` is none at all, and the codes `<NoWarn>` or
/// `-nowarn:` turn off.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WarningOptions {
    pub level: Option<u8>,
    pub suppressed: Vec<u32>,
}

impl WarningOptions {
    /// Whether warning `code` (`618` for CS0618) is reported.
    #[must_use]
    pub fn reports(&self, code: u32) -> bool {
        self.level != Some(0) && !self.suppressed.contains(&code)
    }
}

/// The codes of a `NoWarn` or `-nowarn:` list: `CS0618`, `0618` and `618`
/// alike; anything else (`$(NoWarn)`, an analyzer's id) is skipped.
fn warning_codes(list: &str) -> Vec<u32> {
    list.split([';', ','])
        .filter_map(|code| {
            let code = code.trim();
            let digits = code
                .strip_prefix("CS")
                .or_else(|| code.strip_prefix("cs"))
                .unwrap_or(code);
            digits.parse().ok()
        })
        .collect()
}

impl Project {
    /// Works out the project in `root`.
    ///
    /// `symbols` are what the editor already knows to be defined — Unity's,
    /// for instance — and are kept alongside whatever the project files add.
    #[must_use]
    pub fn discover(root: &Path, symbols: &[String]) -> Self {
        // Unity writes its project files beside `Assets/`. A Unity project
        // without them there is described by the editor, not by whatever
        // `.csproj` a tool in a subfolder brought: a source generator's
        // project knows nothing of `UnityEngine`, and compiling the game by
        // it leaves every engine type unresolved.
        let finding = rustlyn_semantics::timing::phase("project files");
        let paths = match unity_root(root) {
            Some(unity) if !has_project_files(&unity) => Vec::new(),
            _ => project_files(root),
        };
        drop(finding);
        let reading = rustlyn_semantics::timing::phase("project read");
        let mut project = if paths.is_empty() {
            unity_project(root).unwrap_or_else(|| folder_project(root))
        } else {
            let mut project = msbuild_project(&paths);
            // Unity compiles everything under `Assets/`, and writes project
            // files only when its editor runs: a script added since is in no
            // `<Compile>` list yet. The files are the truth, the lists a
            // snapshot of them.
            if unity_root(root).is_some() {
                project.everything = true;
            }
            project
        };
        drop(reading);
        let generating = rustlyn_semantics::timing::phase("generated files");
        for symbol in symbols {
            if !project.symbols.contains(symbol) {
                project.symbols.push(symbol.clone());
            }
        }
        if let Some(unity) = unity_root(root) {
            // Every assembly definition is an assembly, project file or not:
            // Unity writes the files only when an editor asks it to.
            for name in unity_assembly_names(&unity) {
                if !project.assemblies.contains(&name) {
                    project.assemblies.push(name);
                    project
                        .language_versions
                        .push(UNITY_LANGUAGE_VERSION.to_string());
                }
            }
            // Unity's generators write each assembly's code to a folder of
            // its name.
            let generated = unity.join("Temp/GeneratedCode");
            for (index, name) in project.assemblies.iter().enumerate() {
                if let Ok(index) = u16::try_from(index) {
                    project.owned_folders.push((generated.join(name), index));
                }
            }
            // Which assembly a script goes into is Unity's rule, by the folders
            // it is in: the project files' lists are only as new as the last
            // time Unity wrote them.
            project.owned_files.clear();
            let owned = unity_ownership(&unity, &project.assemblies);
            project.owned_folders.extend(owned);
            // What Unity builds is what it has compiled: it writes project
            // files for test assemblies it never compiles too. A definition
            // newer than its last compile is one it has not seen yet, and
            // counts as built. Until Unity has compiled anything, nothing
            // says which it skips.
            let build = unity_build(&unity);
            project.owned_only = true;
            if !build.assemblies.is_empty() {
                let added = unity_definitions_since(&unity, build.newest);
                // A predefined assembly is compiled once it has a script.
                project.unbuilt = project
                    .assemblies
                    .iter()
                    .enumerate()
                    .filter(|(_, name)| {
                        !name.starts_with("Assembly-CSharp")
                            && !build.assemblies.contains_key(name.as_str())
                            && !added.contains(name.as_str())
                    })
                    .filter_map(|(index, _)| u16::try_from(index).ok())
                    .collect();
            }
            // What Unity's last compile of an assembly was given is newer than
            // any project file: its symbols, and which others it referenced.
            let count = project.assemblies.len();
            project.assembly_symbols.resize(count, Vec::new());
            project.assembly_references.resize(count, vec![u16::MAX]);
            project.assembly_metadata.resize(count, Vec::new());
            project
                .assembly_warnings
                .resize(count, WarningOptions::default());
            project.assembly_nullable.resize(count, false);
            let index_of: HashMap<&str, u16> = project
                .assemblies
                .iter()
                .enumerate()
                .filter_map(|(index, name)| Some((name.as_str(), u16::try_from(index).ok()?)))
                .collect();
            // Package sources live in the package cache, which no editor
            // indexes; the project files name them only as far as they are
            // new. Every script there of an assembly Unity builds is
            // compiled.
            let mut cached = Vec::new();
            cs_under(&unity.join("Library/PackageCache"), 0, &mut cached);
            cached.retain(|path| !in_ignored_folder(path));
            cached.sort();
            let listed: HashSet<&PathBuf> = project.files.iter().collect();
            let cached: Vec<PathBuf> = cached
                .into_iter()
                .filter(|path| !listed.contains(path))
                .collect();
            let paths: Vec<&Path> = cached.iter().map(PathBuf::as_path).collect();
            let owners = project.owners_of(&paths);
            let built: Vec<PathBuf> = cached
                .iter()
                .zip(owners)
                .filter(|(_, owner)| *owner != u16::MAX && !project.unbuilt.contains(owner))
                .map(|(path, _)| path.clone())
                .collect();
            project.files.extend(built);
            // Precompiled assemblies the compiles named that the project
            // files do not: a NuGet package or a plugin added since they
            // were written, an engine assembly only a package's IL
            // post-processor references.
            let known: HashSet<String> = project
                .references
                .iter()
                .filter_map(|path| path.file_stem())
                .map(|stem| stem.to_string_lossy().to_ascii_lowercase())
                .collect();
            let mut added: Vec<PathBuf> = build
                .plugins
                .iter()
                .filter(|path| {
                    path.file_stem().is_some_and(|stem| {
                        !known.contains(&stem.to_string_lossy().to_ascii_lowercase())
                    })
                })
                .cloned()
                .collect();
            added.sort();
            added.dedup();
            project.references.extend(added);
            // An assembly compiled here from its source is not also a
            // reference: the project files name `Library/ScriptAssemblies/
            // UniTask.dll` for packages they do not list, and that copy's
            // extension methods — over types of references it brings none
            // of — took any receiver at all.
            let compiled: HashSet<String> = project
                .assemblies
                .iter()
                .enumerate()
                .filter(|(index, _)| {
                    u16::try_from(*index).is_ok_and(|index| !project.unbuilt.contains(&index))
                })
                .map(|(_, name)| name.to_ascii_lowercase())
                .collect();
            project.references.retain(|path| {
                !path.file_stem().is_some_and(|stem| {
                    compiled.contains(&stem.to_string_lossy().to_ascii_lowercase())
                })
            });
            for (assembly, folder) in &build.generated {
                if let Some(&index) = index_of.get(assembly.as_str()) {
                    project.owned_folders.push((folder.clone(), index));
                }
            }
            for (index, name) in project.assemblies.iter().enumerate() {
                let Some((defines, references)) = build.assemblies.get(name) else {
                    continue;
                };
                for symbol in defines {
                    if !project.symbols.contains(symbol) {
                        project.symbols.push(symbol.clone());
                    }
                }
                project.assembly_symbols[index] = defines.clone();
                if let Some(metadata) = build.metadata.get(name) {
                    project.assembly_metadata[index] = metadata.clone();
                }
                if let Some(warnings) = build.warnings.get(name) {
                    project.assembly_warnings[index] = warnings.clone();
                }
                project.assembly_nullable[index] = build.nullable.contains(name);
                project.assembly_references[index] = references
                    .iter()
                    .filter_map(|reference| index_of.get(reference.as_str()).copied())
                    .collect();
            }
            // Tens of thousands of generated files against tens of thousands
            // listed: a search of the list for each took half a minute.
            let mut listed: HashSet<PathBuf> = project.files.iter().cloned().collect();
            let (generated, copies) = unity_generated_files(&unity);
            for path in generated {
                if listed.insert(path.clone()) {
                    project.files.push(path);
                }
            }
            // A copy compiled once is each assembly's that had one.
            let copied: Vec<&Path> = copies.iter().map(|(_, copy)| copy.as_path()).collect();
            for ((kept, _), owner) in copies.iter().zip(project.owners_of(&copied)) {
                if owner != u16::MAX {
                    project.shared_files.push((kept.clone(), owner));
                }
            }
        }
        drop(generating);
        project
    }

    /// Which of `assemblies` each of `paths` goes into, `u16::MAX` where
    /// nothing says.
    #[must_use]
    pub fn owners_of(&self, paths: &[&Path]) -> Vec<u16> {
        let files: HashMap<&Path, u16> = self
            .owned_files
            .iter()
            .map(|(path, index)| (path.as_path(), *index))
            .collect();
        paths
            .iter()
            .map(|path| {
                files.get(path).copied().unwrap_or_else(|| {
                    self.owned_folders
                        .iter()
                        .filter(|(folder, _)| path.starts_with(folder))
                        .max_by_key(|(folder, _)| folder.components().count())
                        .map_or(u16::MAX, |(_, index)| *index)
                })
            })
            .collect()
    }

    /// How to parse a file of the assembly `owner` (from
    /// [`Project::owners_of`]): with the project's symbols, as the version of
    /// C# that assembly is written in.
    #[must_use]
    pub fn parse_options(&self, owner: u16) -> rustlyn_syntax::ParseOptions {
        let symbols = self
            .assembly_symbols
            .get(usize::from(owner))
            .filter(|symbols| !symbols.is_empty())
            .unwrap_or(&self.symbols);
        let options = rustlyn_syntax::ParseOptions::with_symbols(symbols.clone());
        match self
            .language_versions
            .get(usize::from(owner))
            .and_then(|version| version.parse::<rustlyn_syntax::LanguageVersion>().ok())
        {
            Some(version) => options.with_language_version(version),
            None => options,
        }
    }

    /// Whether `path` is compiled, given a list the editor already has.
    #[must_use]
    pub fn compiles(&self, path: &Path) -> bool {
        (self.everything && !in_ignored_folder(path))
            || (self.roots.iter().any(|root| path.starts_with(root)) && !in_build_output(path))
    }
}

/// A folder whose name ends in `~`: Unity imports nothing from it, which is
/// where packages keep samples and documentation that are compiled only once
/// copied into a project.
fn in_ignored_folder(path: &Path) -> bool {
    path.parent().is_some_and(|folder| {
        folder
            .components()
            .any(|component| component.as_os_str().to_string_lossy().ends_with('~'))
    })
}

/// `bin/` and `obj/` under a project hold copies and generated files, not
/// source anyone means to compile twice.
fn in_build_output(path: &Path) -> bool {
    path.components().any(|component| {
        let name = component.as_os_str();
        name == "bin" || name == "obj"
    })
}

// MARK: - finding project files

/// Directories no project lives in, and walking which would cost seconds.
const SKIPPED: &[&str] = &[
    "bin",
    "obj",
    "node_modules",
    "Library",
    "Temp",
    "Logs",
    "packages",
    "artifacts",
];

/// The `.csproj` files of the project at `root`.
///
/// A solution says which ones, when there is one; a Unity project has it at
/// its root, or one folder down when the repository holds more than the
/// project. Without one, every `.csproj` a few levels down counts.
fn project_files(root: &Path) -> Vec<PathBuf> {
    let mut solutions = solutions_in(root);
    if solutions.is_empty() {
        for child in subdirectories(root) {
            solutions.extend(solutions_in(&child));
        }
    }
    let mut found: Vec<PathBuf> = Vec::new();
    for solution in &solutions {
        for path in solution_projects(solution) {
            if path.is_file() && !found.contains(&path) {
                found.push(path);
            }
        }
    }
    if found.is_empty() {
        walk_projects(root, 0, &mut found);
    }
    found.sort();
    found
}

/// Whether `directory` itself holds a solution or a project file.
fn has_project_files(directory: &Path) -> bool {
    read_dir(directory).iter().any(|path| {
        path.is_file()
            && path.extension().is_some_and(|extension| {
                extension == "sln" || extension == "slnx" || extension == "csproj"
            })
    })
}

fn solutions_in(directory: &Path) -> Vec<PathBuf> {
    let mut solutions: Vec<PathBuf> = read_dir(directory)
        .into_iter()
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "sln" || extension == "slnx")
        })
        .collect();
    solutions.sort();
    solutions
}

fn subdirectories(directory: &Path) -> Vec<PathBuf> {
    read_dir(directory)
        .into_iter()
        .filter(|path| path.is_dir() && !is_skipped(path))
        .collect()
}

/// The entries of a directory with whether each is one, as the listing
/// says it: no `stat` a file, which in a folder of thousands adds up.
fn read_dir_kinds(directory: &Path) -> Vec<(PathBuf, bool)> {
    std::fs::read_dir(directory)
        .map(|entries| {
            entries
                .filter_map(|entry| {
                    let entry = entry.ok()?;
                    let directory = entry.file_type().ok()?.is_dir()
                        || (entry.file_type().ok()?.is_symlink() && entry.path().is_dir());
                    Some((entry.path(), directory))
                })
                .collect()
        })
        .unwrap_or_default()
}

/// A file's length and modification time.
pub(crate) fn stamp_of(path: &Path) -> (u64, u128) {
    let metadata = std::fs::metadata(path).ok();
    (
        metadata.as_ref().map_or(0, std::fs::Metadata::len),
        metadata
            .and_then(|metadata| metadata.modified().ok())
            .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(0, |since| since.as_nanos()),
    )
}

fn read_dir(directory: &Path) -> Vec<PathBuf> {
    std::fs::read_dir(directory)
        .map(|entries| {
            entries
                .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                .collect()
        })
        .unwrap_or_default()
}

fn is_skipped(path: &Path) -> bool {
    path.file_name().is_some_and(|name| {
        let name = name.to_string_lossy();
        name.starts_with('.') || name.ends_with('~') || SKIPPED.contains(&name.as_ref())
    })
}

/// Every `.csproj` up to four folders under `root`, whatever a solution says,
/// past hidden folders, build output and dependencies: the projects a tool
/// that manages packages has to know about. Sorted.
#[must_use]
pub fn csproj_files(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    walk_projects(root, 0, &mut found);
    found.sort();
    found
}

fn walk_projects(directory: &Path, depth: usize, found: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if path.is_dir() {
            if depth < 4 && !is_skipped(&path) {
                walk_projects(&path, depth + 1, found);
            }
        } else if path
            .extension()
            .is_some_and(|extension| extension == "csproj")
        {
            found.push(path);
        }
    }
}

/// The projects a `.sln` or `.slnx` names.
fn solution_projects(solution: &Path) -> Vec<PathBuf> {
    let Ok(text) = std::fs::read_to_string(solution) else {
        return Vec::new();
    };
    let directory = solution.parent().unwrap_or(Path::new(""));
    let mut found = Vec::new();
    if solution
        .extension()
        .is_some_and(|extension| extension == "slnx")
    {
        for element in Xml::new(&text).elements() {
            if element.name == "Project"
                && let Some(path) = element.attribute("Path")
            {
                found.push(normalized(&directory.join(native_path(path))));
            }
        }
    } else {
        // Project("{FAE04EC0-...}") = "Name", "Path\To\Name.csproj", "{GUID}"
        for line in text.lines().filter(|line| line.starts_with("Project(")) {
            let quoted: Vec<&str> = line.split('"').skip(1).step_by(2).collect();
            if let Some(path) = quoted.get(2) {
                found.push(normalized(&directory.join(native_path(path))));
            }
        }
    }
    found
        .into_iter()
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "csproj")
        })
        .collect()
}

/// `a/b/../c` as `a/c`, without asking the disk: a file reached through a
/// shared project's `..\` must be the same path the editor has for it, or
/// it is compiled twice and every type in it declared twice.
fn normalized(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                if !out.pop() {
                    out.push("..");
                }
            }
            other => out.push(other),
        }
    }
    out
}

/// MSBuild writes paths with backslashes, whatever it runs on.
fn native_path(path: &str) -> PathBuf {
    PathBuf::from(path.trim().replace('\\', "/"))
}

// MARK: - reading a project file

/// What one `.csproj` says.
#[derive(Default, Debug)]
struct ProjectFile {
    /// The project file itself.
    path: PathBuf,
    /// The projects it references, by their files.
    project_references: Vec<PathBuf>,
    directory: PathBuf,
    /// `<Project Sdk="...">`: the SDK format, which compiles every file under
    /// the project's folder and adds the framework by itself.
    sdk: Option<String>,
    assembly_name: String,
    /// `<LangVersion>`, as written.
    language_version: Option<String>,
    frameworks: Vec<String>,
    defines: Vec<String>,
    hint_paths: Vec<PathBuf>,
    compile: Vec<PathBuf>,
    implicit_usings: bool,
    /// `<Using>` items: the namespace or type, whether it is `static`, and
    /// the alias it is given, if any.
    usings: Vec<(String, bool, Option<String>)>,
    /// `<Using Remove>`: what is not to be imported after all, implicit
    /// ones included.
    removed_usings: Vec<String>,
    /// `<WarningLevel>` and `<NoWarn>`.
    warnings: WarningOptions,
    /// `<Nullable>`.
    nullable: bool,
}

/// Whether an MSBuild condition holds, as far as comparing strings says:
/// `'$(TargetFramework)' == 'net8.0'`, joined by `Or` and `And`. A property
/// other than the framework is empty, as one nobody set is; anything this
/// cannot read — a property function — does not hold.
fn holds(condition: &str, framework: &str) -> bool {
    let lower = condition.to_ascii_lowercase();
    if lower.contains("$([") || (lower.contains('(') && !lower.contains("$(")) {
        return false;
    }
    let value = |operand: &str| -> Option<String> {
        let operand = operand.trim();
        let inner = operand
            .strip_prefix('\'')
            .and_then(|rest| rest.strip_suffix('\''))
            .unwrap_or(operand);
        if inner.contains("$(") && !inner.starts_with("$(") {
            return None;
        }
        Some(
            match inner
                .strip_prefix("$(")
                .and_then(|rest| rest.strip_suffix(')'))
            {
                Some(property) if property.eq_ignore_ascii_case("TargetFramework") => {
                    framework.to_ascii_lowercase()
                }
                Some(_) => String::new(),
                None => inner.to_ascii_lowercase(),
            },
        )
    };
    let comparison = |part: &str| -> bool {
        let (left, right, equal) = if let Some((left, right)) = part.split_once("==") {
            (left, right, true)
        } else if let Some((left, right)) = part.split_once("!=") {
            (left, right, false)
        } else {
            return false;
        };
        match (value(left), value(right)) {
            (Some(left), Some(right)) => (left == right) == equal,
            _ => false,
        }
    };
    lower
        .split(" or ")
        .any(|alternative| alternative.split(" and ").all(comparison))
}

/// A path with `$(MSBuildThisFileDirectory)` taken out of it, however its
/// case is spelled: what is left is relative to the file it is written in.
fn without_this_file_directory(path: &str) -> String {
    const PROPERTY: &str = "$(msbuildthisfiledirectory)";
    let mut path = path.to_string();
    while let Some(at) = path.to_ascii_lowercase().find(PROPERTY) {
        path.replace_range(at..at + PROPERTY.len(), "");
    }
    path
}

/// The `Directory.Build.props` or `.targets` MSBuild imports into a project
/// in `directory`: the nearest one in it or above it.
fn nearest_above(directory: &Path, name: &str) -> Option<PathBuf> {
    directory
        .ancestors()
        .map(|folder| folder.join(name))
        .find(|path| path.is_file())
}

/// The files a shared project (`.projitems`) lists, which it spells
/// relative to itself.
fn shared_files(path: &Path) -> Vec<PathBuf> {
    let Ok(text) = std::fs::read_to_string(path) else {
        return Vec::new();
    };
    let directory = path.parent().unwrap_or(Path::new(""));
    Xml::new(&text)
        .elements()
        .into_iter()
        .filter(|element| element.name == "Compile")
        .filter_map(|element| {
            let include = element.attribute("Include")?;
            Some(compile_items(
                directory,
                &include.replace("$(MSBuildThisFileDirectory)", ""),
            ))
        })
        .flatten()
        .collect()
}

/// The files a `<Compile Include>` names: one path, or a glob — `*.cs`,
/// `Sub\*.cs`, `**\*.cs` — which shared projects use to take a whole folder.
/// Anything with a property left in it is skipped: it needs MSBuild.
fn compile_items(directory: &Path, include: &str) -> Vec<PathBuf> {
    include
        .split(';')
        .map(str::trim)
        .filter(|item| !item.is_empty() && !item.contains("$("))
        .flat_map(|item| {
            let item = native_path(item);
            let text = item.to_string_lossy().into_owned();
            let Some(star) = text.find('*') else {
                return vec![normalized(&directory.join(item))];
            };
            // Everything up to the folder holding the first `*` is a plain
            // path; the rest is what the files under it must match.
            let base_end = text[..star].rfind('/').map_or(0, |slash| slash + 1);
            let base = normalized(&directory.join(&text[..base_end]));
            let pattern = &text[base_end..];
            let recursive = pattern.starts_with("**/");
            let name = pattern.rsplit('/').next().unwrap_or(pattern);
            let mut found = Vec::new();
            files_matching(&base, name, recursive, &mut found);
            found.sort();
            found
        })
        .collect()
}

fn files_matching(directory: &Path, name: &str, recursive: bool, found: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if path.is_dir() {
            if recursive && !is_skipped(&path) {
                files_matching(&path, name, recursive, found);
            }
        } else if path
            .file_name()
            .is_some_and(|file| wildcard(name, &file.to_string_lossy()))
        {
            found.push(path);
        }
    }
}

/// `*` against a file name, the only wildcard project files use in practice.
fn wildcard(pattern: &str, name: &str) -> bool {
    let parts: Vec<&str> = pattern.split('*').collect();
    let [first, middle @ .., last] = parts.as_slice() else {
        return pattern == name;
    };
    if !name.starts_with(first) || name.len() < first.len() + last.len() || !name.ends_with(last) {
        return false;
    }
    let mut rest = &name[first.len()..name.len() - last.len()];
    for part in middle {
        match rest.find(part) {
            Some(at) => rest = &rest[at + part.len()..],
            None => return false,
        }
    }
    true
}

impl ProjectFile {
    fn read(path: &Path) -> Option<Self> {
        let text = std::fs::read_to_string(path).ok()?;
        let directory = path.parent().unwrap_or(Path::new("")).to_path_buf();
        let mut project = Self {
            assembly_name: path
                .file_stem()
                .map(|stem| stem.to_string_lossy().into_owned())
                .unwrap_or_default(),
            path: normalized(path),
            directory,
            ..Self::default()
        };
        // MSBuild imports the `Directory.Build.props` nearest above a project
        // ahead of it, and a repository says there what all its projects
        // share: `<ImplicitUsings>`, `<Using>` items, the frameworks.
        // A condition there may ask which framework is being built, and
        // the project says: the first it names, as for its symbols.
        let own_frameworks: Vec<String> = Xml::new(&text)
            .elements()
            .iter()
            .filter(|element| matches!(element.name, "TargetFramework" | "TargetFrameworks"))
            .filter_map(|element| element.text.clone())
            .flat_map(|text| {
                text.split(';')
                    .map(str::trim)
                    .filter(|framework| !framework.is_empty() && !framework.contains("$("))
                    .map(str::to_string)
                    .collect::<Vec<_>>()
            })
            .collect();
        let framework = own_frameworks.first().cloned().unwrap_or_default();
        // Only the SDK reads them, and makes `global using`s: a Unity
        // project's files are of the old kind, whatever lies above them.
        let sdk = Xml::new(&text)
            .elements()
            .iter()
            .any(|element| element.name == "Project" && element.attribute("Sdk").is_some());
        if sdk && let Some(props) = nearest_above(&project.directory, "Directory.Build.props") {
            project.read_shared(&props, &framework, 0);
        }
        // What the project says for itself wins over what it shares.
        if !own_frameworks.is_empty() {
            project.frameworks.clear();
        }
        let xml = Xml::new(&text);
        for element in xml.elements() {
            match element.name {
                "Project" => {
                    project.sdk = element.attribute("Sdk").map(str::to_string);
                }
                "LangVersion" => {
                    if let Some(version) = element.text.filter(|version| !version.contains("$(")) {
                        project.language_version = Some(version.trim().to_string());
                    }
                }
                "Nullable" => {
                    project.nullable = nullable_annotations(&element.text.unwrap_or_default());
                }
                "WarningLevel" => {
                    if let Some(level) = element.text.and_then(|level| level.trim().parse().ok()) {
                        project.warnings.level = Some(level);
                    }
                }
                "NoWarn" => {
                    project
                        .warnings
                        .suppressed
                        .extend(warning_codes(&element.text.unwrap_or_default()));
                }
                "AssemblyName" => {
                    if let Some(name) = element.text.filter(|name| !name.contains("$(")) {
                        project.assembly_name = name.trim().to_string();
                    }
                }
                "TargetFramework" | "TargetFrameworks" => {
                    for framework in element.text.unwrap_or_default().split(';') {
                        let framework = framework.trim();
                        if !framework.is_empty() && !framework.contains("$(") {
                            project.frameworks.push(framework.to_string());
                        }
                    }
                }
                "TargetFrameworkVersion" => {
                    // The old format: `v4.7.1` means `net471`.
                    if let Some(version) = element.text {
                        let digits: String = version.chars().filter(char::is_ascii_digit).collect();
                        project.frameworks.push(format!("net{digits}"));
                    }
                }
                "DefineConstants" => {
                    for symbol in element.text.unwrap_or_default().split([';', ',']) {
                        let symbol = symbol.trim();
                        if !symbol.is_empty() && !symbol.contains("$(") {
                            project.defines.push(symbol.to_string());
                        }
                    }
                }
                "HintPath" => {
                    if let Some(path) = element.text {
                        project
                            .hint_paths
                            .push(normalized(&project.directory.join(native_path(&path))));
                    }
                }
                "ProjectReference" => {
                    if let Some(include) = element.attribute("Include")
                        && !include.contains("$(")
                    {
                        project
                            .project_references
                            .push(normalized(&project.directory.join(native_path(include))));
                    }
                }
                "Compile" => {
                    // In the SDK format a glob only repeats what is compiled
                    // anyway; in the old one it is the only list there is.
                    if let Some(include) = element.attribute("Include") {
                        let items = compile_items(&project.directory, include);
                        project.compile.extend(items);
                    }
                }
                "Import" => {
                    // A shared project: its files are compiled as this one's.
                    if let Some(imported) = element.attribute("Project")
                        && imported.ends_with(".projitems")
                        && !imported.contains("$(")
                    {
                        let shared = normalized(&project.directory.join(native_path(imported)));
                        project.compile.extend(shared_files(&shared));
                    }
                }
                "ImplicitUsings" | "Using" => project.read_using(&element),
                _ => {}
            }
        }
        // `Directory.Build.targets` comes after the project, and is where
        // some repositories keep their `<Using>` items.
        if sdk && let Some(targets) = nearest_above(&project.directory, "Directory.Build.targets") {
            let framework = project.frameworks.first().cloned().unwrap_or_default();
            project.read_shared(&targets, &framework, 0);
        }
        Some(project)
    }

    /// What a `Directory.Build.props` says that this reads: properties,
    /// `<Using>` items, and the files it imports from beside it. Paths in
    /// it are another file's business.
    fn read_shared(&mut self, path: &Path, framework: &str, depth: usize) {
        let Ok(text) = std::fs::read_to_string(path) else {
            return;
        };
        let here = path.parent().unwrap_or(Path::new(""));
        for element in Xml::new(&text).elements().into_iter().filter(|element| {
            element
                .conditions
                .iter()
                .all(|condition| holds(condition, framework))
        }) {
            match element.name {
                "Import" if depth < 4 => {
                    // `$(MSBuildThisFileDirectory)eng/Common.props`, the one
                    // property an import is spelled with that needs nothing
                    // evaluated.
                    let Some(imported) = element.attribute("Project") else {
                        continue;
                    };
                    let imported = without_this_file_directory(imported);
                    if !imported.contains("$(") {
                        let imported = normalized(&here.join(native_path(&imported)));
                        self.read_shared(&imported, framework, depth + 1);
                    }
                }
                "TargetFramework" | "TargetFrameworks" => {
                    for framework in element.text.unwrap_or_default().split(';') {
                        let framework = framework.trim();
                        if !framework.is_empty() && !framework.contains("$(") {
                            self.frameworks.push(framework.to_string());
                        }
                    }
                }
                "DefineConstants" => {
                    for symbol in element.text.unwrap_or_default().split([';', ',']) {
                        let symbol = symbol.trim();
                        if !symbol.is_empty() && !symbol.contains("$(") {
                            self.defines.push(symbol.to_string());
                        }
                    }
                }
                "ImplicitUsings" | "Using" => self.read_using(&element),
                _ => {}
            }
        }
    }

    /// `<ImplicitUsings>` and the `<Using>` items, which the SDK makes
    /// `global using` directives of.
    fn read_using(&mut self, element: &Element<'_>) {
        if element.name == "ImplicitUsings" {
            self.implicit_usings = element
                .text
                .as_deref()
                .is_some_and(|value| matches!(value.trim(), "enable" | "true"));
            return;
        }
        if let Some(name) = element.attribute("Include") {
            let is_static = element.attribute("Static") == Some("true");
            let alias = element.attribute("Alias").map(str::to_string);
            self.usings.push((name.to_string(), is_static, alias));
            self.removed_usings.retain(|removed| removed != name);
        }
        if let Some(name) = element.attribute("Remove") {
            self.usings.retain(|(using, _, _)| using != name);
            self.removed_usings.push(name.to_string());
        }
    }

    /// The symbols the SDK defines by itself for the target framework.
    fn implicit_defines(&self) -> Vec<String> {
        let mut symbols = vec!["DEBUG".to_string(), "TRACE".to_string()];
        if self.sdk.is_none() {
            return symbols;
        }
        if let Some(framework) = self.frameworks.first() {
            symbols.extend(framework_symbols(framework));
        }
        symbols
    }

    /// The `global using` lines `<ImplicitUsings>` would have generated.
    fn global_usings(&self) -> String {
        let mut usings: Vec<(String, bool, Option<String>)> = Vec::new();
        if self.implicit_usings {
            let sdk = self.sdk.as_deref().unwrap_or_default();
            let mut names = vec![
                "System",
                "System.Collections.Generic",
                "System.IO",
                "System.Linq",
                "System.Net.Http",
                "System.Threading",
                "System.Threading.Tasks",
            ];
            if sdk.contains("Web") {
                names.extend([
                    "System.Net.Http.Json",
                    "Microsoft.AspNetCore.Builder",
                    "Microsoft.AspNetCore.Hosting",
                    "Microsoft.AspNetCore.Http",
                    "Microsoft.AspNetCore.Routing",
                    "Microsoft.Extensions.Configuration",
                    "Microsoft.Extensions.DependencyInjection",
                    "Microsoft.Extensions.Hosting",
                    "Microsoft.Extensions.Logging",
                ]);
            } else if sdk.contains("Worker") {
                names.extend([
                    "Microsoft.Extensions.Configuration",
                    "Microsoft.Extensions.DependencyInjection",
                    "Microsoft.Extensions.Hosting",
                    "Microsoft.Extensions.Logging",
                ]);
            }
            usings.extend(
                names
                    .into_iter()
                    .filter(|name| !self.removed_usings.iter().any(|removed| removed == name))
                    .map(|name| (name.to_string(), false, None)),
            );
        }
        usings.extend(self.usings.iter().cloned());
        usings
            .iter()
            .map(|(name, is_static, alias)| match alias {
                Some(alias) => format!("global using {alias} = global::{name};\n"),
                None if *is_static => format!("global using static global::{name};\n"),
                None => format!("global using global::{name};\n"),
            })
            .collect()
    }
}

/// `NET8_0`, `NET8_0_OR_GREATER` and the rest of what the SDK defines for a
/// target framework moniker.
fn framework_symbols(framework: &str) -> Vec<String> {
    let mut symbols = Vec::new();
    let framework = framework.to_ascii_lowercase();
    let framework = framework.split('-').next().unwrap_or_default();
    if let Some(version) = framework.strip_prefix("netstandard") {
        symbols.push("NETSTANDARD".to_string());
        let (major, minor) = split_version(version);
        symbols.push(format!("NETSTANDARD{major}_{minor}"));
        for (a, b) in [
            (1, 0),
            (1, 1),
            (1, 2),
            (1, 3),
            (1, 4),
            (1, 5),
            (1, 6),
            (2, 0),
            (2, 1),
        ] {
            if (a, b) <= (major, minor) {
                symbols.push(format!("NETSTANDARD{a}_{b}_OR_GREATER"));
            }
        }
    } else if let Some(version) = framework.strip_prefix("netcoreapp") {
        symbols.push("NETCOREAPP".to_string());
        let (major, minor) = split_version(version);
        symbols.push(format!("NETCOREAPP{major}_{minor}"));
        symbols.extend(core_ladder(major, minor));
    } else if let Some(version) = framework.strip_prefix("net") {
        if version.contains('.') {
            // net5.0 and on: .NET, which is also still NETCOREAPP.
            let (major, minor) = split_version(version);
            symbols.push("NET".to_string());
            symbols.push("NETCOREAPP".to_string());
            symbols.push(format!("NET{major}_{minor}"));
            symbols.extend(core_ladder(major, minor));
        } else {
            // net472: the .NET Framework.
            symbols.push("NETFRAMEWORK".to_string());
            symbols.push(format!("NET{}", version.to_ascii_uppercase()));
            for known in [
                "20", "35", "40", "45", "451", "452", "46", "461", "462", "47", "471", "472", "48",
                "481",
            ] {
                if pad(known) <= pad(version) {
                    symbols.push(format!("NET{known}_OR_GREATER"));
                }
            }
        }
    }
    symbols
}

fn pad(version: &str) -> String {
    format!("{version:0<3}")
}

fn split_version(version: &str) -> (u32, u32) {
    let mut parts = version.split('.').map(|part| part.parse().unwrap_or(0));
    (parts.next().unwrap_or(0), parts.next().unwrap_or(0))
}

/// `NETCOREAPP1_0_OR_GREATER` up to `NET{major}_{minor}_OR_GREATER`.
fn core_ladder(major: u32, minor: u32) -> Vec<String> {
    let mut symbols = Vec::new();
    for (a, b) in [(1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)] {
        if (a, b) <= (major, minor) {
            symbols.push(format!("NETCOREAPP{a}_{b}_OR_GREATER"));
        }
    }
    for a in 5..=major {
        symbols.push(format!("NET{a}_0_OR_GREATER"));
    }
    symbols
}

/// [`msbuild_project_read`], kept for as long as the project files are as
/// they were: reading a hundred of them is most of a compile after a save.
fn msbuild_project(paths: &[PathBuf]) -> Project {
    let stamps: Vec<(PathBuf, (u64, u128))> = paths
        .iter()
        .map(|path| (path.clone(), stamp_of(path)))
        .collect();
    static KEPT: std::sync::Mutex<Option<(Vec<Stamped>, Project)>> = std::sync::Mutex::new(None);
    if let Ok(kept) = KEPT.lock()
        && let Some((kept_stamps, project)) = kept.as_ref()
        && *kept_stamps == stamps
    {
        return project.clone();
    }
    let project = msbuild_project_read(paths);
    if let Ok(mut kept) = KEPT.lock() {
        *kept = Some((stamps, project.clone()));
    }
    project
}

fn msbuild_project_read(paths: &[PathBuf]) -> Project {
    let files: Vec<ProjectFile> = paths
        .iter()
        .filter_map(|path| ProjectFile::read(path))
        .collect();

    // An assembly the project builds from source is not also a reference:
    // Unity's project files point at `Library/ScriptAssemblies/X.dll` for the
    // very `X` another of them compiles, and reading both would declare every
    // type twice.
    let built: HashSet<String> = files
        .iter()
        .map(|file| file.assembly_name.to_ascii_lowercase())
        .collect();

    let mut references = References::default();
    let mut symbols: Vec<String> = Vec::new();
    let mut roots = Vec::new();
    let mut compile = Vec::new();
    let mut generated = String::new();
    let mut seen_usings = HashSet::new();
    for file in &files {
        for path in &file.hint_paths {
            references.add(path, &built);
        }
        for symbol in file.defines.iter().cloned().chain(file.implicit_defines()) {
            if !symbols.contains(&symbol) {
                symbols.push(symbol);
            }
        }
        if file.sdk.is_some() {
            roots.push(file.directory.clone());
            for path in assets_references(&file.directory) {
                references.add(&path, &built);
            }
        }
        compile.extend(file.compile.iter().cloned());
        for line in file.global_usings().lines() {
            if seen_usings.insert(line.to_string()) {
                generated.push_str(line);
                generated.push('\n');
            }
        }
    }

    // The framework comes last, so an assembly the project names itself wins
    // over the framework's copy of it.
    let framework = files
        .iter()
        .filter(|file| file.hint_paths.is_empty() || file.sdk.is_some())
        .flat_map(|file| file.frameworks.iter())
        .max_by_key(|framework| framework_rank(framework));
    // An old-format project names its core library, and the projects of one
    // solution share it: Unity writes project files for test assemblies with
    // no `netstandard` of their own, and the newest framework installed
    // beside the engine's would make `WebClient` two types.
    let needs_framework = files.iter().any(|file| file.sdk.is_some())
        || !files
            .iter()
            .any(|file| file.hint_paths.iter().any(|path| is_core_library(path)));
    if needs_framework {
        for path in framework_references(framework.map(String::as_str)) {
            references.add(&path, &built);
        }
    }

    let mut assemblies: Vec<String> = Vec::new();
    let mut owned_files = Vec::new();
    let mut owned_folders = Vec::new();
    let mut language_versions = Vec::new();
    let mut assembly_symbols: Vec<Vec<String>> = Vec::new();
    let mut assembly_warnings: Vec<WarningOptions> = Vec::new();
    let mut assembly_nullable: Vec<bool> = Vec::new();
    let mut by_path: HashMap<&Path, u16> = HashMap::new();
    for file in &files {
        let index = assemblies
            .iter()
            .position(|name| *name == file.assembly_name)
            .unwrap_or_else(|| {
                assemblies.push(file.assembly_name.clone());
                language_versions.push(file.language_version.clone().unwrap_or_default());
                let mut defines = file.defines.clone();
                for symbol in file.implicit_defines() {
                    if !defines.contains(&symbol) {
                        defines.push(symbol);
                    }
                }
                assembly_symbols.push(defines);
                assembly_warnings.push(file.warnings.clone());
                assembly_nullable.push(file.nullable);
                assemblies.len() - 1
            });
        let Ok(index) = u16::try_from(index) else {
            continue;
        };
        by_path.insert(file.path.as_path(), index);
        owned_files.extend(file.compile.iter().map(|path| (path.clone(), index)));
        if file.sdk.is_some() {
            owned_folders.push((file.directory.clone(), index));
        }
    }

    // A project's references to others of the solution; one that names none
    // still sees only itself.
    let mut assembly_references: Vec<Vec<u16>> = vec![Vec::new(); assemblies.len()];
    for file in &files {
        let Some(&index) = by_path.get(file.path.as_path()) else {
            continue;
        };
        for reference in &file.project_references {
            // A reference to a project outside what was read says nothing
            // about which of these it sees.
            let target = by_path
                .get(reference.as_path())
                .copied()
                .unwrap_or(u16::MAX);
            if !assembly_references[usize::from(index)].contains(&target) {
                assembly_references[usize::from(index)].push(target);
            }
        }
    }

    Project {
        kind: ProjectKind::Msbuild,
        projects: files.len(),
        roots,
        files: compile,
        everything: false,
        references: references.paths,
        symbols,
        generated,
        assemblies,
        owned_files,
        owned_folders,
        language_versions,
        owned_only: false,
        unbuilt: Vec::new(),
        assembly_symbols,
        assembly_references,
        shared_files: Vec::new(),
        assembly_metadata: Vec::new(),
        assembly_warnings,
        assembly_nullable,
    }
}

/// Whether a reference is the one that declares `System.Object`, after which
/// no framework needs adding.
fn is_core_library(path: &Path) -> bool {
    path.file_stem().is_some_and(|stem| {
        let stem = stem.to_string_lossy().to_ascii_lowercase();
        matches!(
            stem.as_str(),
            "mscorlib" | "netstandard" | "system.runtime" | "system.private.corelib"
        )
    })
}

/// Which of several target frameworks to read the framework of: the newest.
fn framework_rank(framework: &str) -> (u32, u32, u32) {
    let framework = framework.to_ascii_lowercase();
    if let Some(version) = framework.strip_prefix("netstandard") {
        let (major, minor) = split_version(version);
        return (1, major, minor);
    }
    if let Some(version) = framework.strip_prefix("netcoreapp") {
        let (major, minor) = split_version(version);
        return (2, major, minor);
    }
    if let Some(version) = framework.strip_prefix("net") {
        if version.contains('.') {
            let (major, minor) = split_version(version);
            return (3, major, minor);
        }
        return (0, version.parse().unwrap_or(0), 0);
    }
    (0, 0, 0)
}

/// Assemblies by name: the first path given for a name is the one kept.
#[derive(Default)]
struct References {
    paths: Vec<PathBuf>,
    names: HashSet<String>,
}

impl References {
    fn add(&mut self, path: &Path, built: &HashSet<String>) {
        let Some(stem) = path.file_stem() else {
            return;
        };
        let name = stem.to_string_lossy().to_ascii_lowercase();
        if built.contains(&name) || !path.is_file() {
            return;
        }
        if self.names.insert(name) {
            self.paths.push(path.to_path_buf());
        }
    }
}

// MARK: - packages

/// The package assemblies a restore resolved for a project, transitively.
///
/// `obj/project.assets.json` is what the build itself reads for this, so it
/// is exactly right, and it exists whenever the project has been restored —
/// which any project that has been built once has been.
fn assets_references(project: &Path) -> Vec<PathBuf> {
    let Ok(text) = std::fs::read_to_string(project.join("obj/project.assets.json")) else {
        return Vec::new();
    };
    let Some(json) = Json::parse(text.as_bytes()) else {
        return Vec::new();
    };
    let folders: Vec<PathBuf> = json
        .get("packageFolders")
        .and_then(Json::as_object)
        .map(|folders| {
            folders
                .iter()
                .map(|(path, _)| PathBuf::from(path))
                .collect()
        })
        .unwrap_or_default();
    let libraries = json.get("libraries").and_then(Json::as_object);
    let Some(targets) = json.get("targets").and_then(Json::as_object) else {
        return Vec::new();
    };
    // Several targets when the project has several frameworks; the first one
    // is as good as any for reading.
    let Some((_, target)) = targets.first() else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for (name, library) in target.as_object().unwrap_or_default() {
        if library.get("type").and_then(Json::as_str) != Some("package") {
            continue;
        }
        let Some(relative) = libraries
            .and_then(|libraries| libraries.iter().find(|(key, _)| key == name))
            .and_then(|(_, library)| library.get("path"))
            .and_then(Json::as_str)
        else {
            continue;
        };
        for (file, _) in library
            .get("compile")
            .and_then(Json::as_object)
            .unwrap_or_default()
        {
            if !file.ends_with(".dll") {
                continue;
            }
            for folder in &folders {
                let path = folder.join(relative).join(file);
                if path.is_file() {
                    found.push(path);
                    break;
                }
            }
        }
    }
    found
}

// MARK: - the framework

/// Where .NET might be installed, in the order a user would expect.
fn dotnet_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    for variable in ["DOTNET_ROOT", "DOTNET_INSTALL_DIR"] {
        if let Some(path) = std::env::var_os(variable) {
            roots.push(PathBuf::from(path));
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        roots.push(PathBuf::from(home).join(".dotnet"));
    }
    for path in [
        "/usr/local/share/dotnet",
        "/opt/homebrew/share/dotnet",
        "/usr/share/dotnet",
        "/usr/lib/dotnet",
        "/opt/dotnet",
    ] {
        roots.push(PathBuf::from(path));
    }
    roots.retain(|root| root.join("packs").is_dir());
    roots
}

/// The reference assemblies of a target framework, or of the newest .NET on
/// the machine when the framework is not known or not installed.
#[must_use]
pub fn framework_references(framework: Option<&str>) -> Vec<PathBuf> {
    let framework = framework.map(str::to_ascii_lowercase);
    let wanted = framework.as_deref().map(framework_rank);
    if let Some(framework) = framework.as_deref()
        && framework.starts_with("netstandard")
        && let Some(found) = netstandard_references(framework)
    {
        return found;
    }

    // `packs/Microsoft.NETCore.App.Ref/<version>/ref/net<major>.<minor>/`.
    let mut candidates: Vec<((u32, u32, u32), PathBuf)> = Vec::new();
    for root in dotnet_roots() {
        for version in read_dir(&root.join("packs/Microsoft.NETCore.App.Ref")) {
            for directory in read_dir(&version.join("ref")) {
                let name = directory
                    .file_name()
                    .map(|name| name.to_string_lossy().into_owned())
                    .unwrap_or_default();
                let patch = version
                    .file_name()
                    .map(|name| {
                        let name = name.to_string_lossy();
                        name.split('.')
                            .nth(2)
                            .and_then(|part| part.parse().ok())
                            .unwrap_or(0)
                    })
                    .unwrap_or(0);
                let rank = framework_rank(&name);
                candidates.push(((rank.1, rank.2, patch), directory));
            }
        }
    }
    // The framework asked for if it is there; otherwise the newest.
    candidates.sort_by_key(|b| std::cmp::Reverse(b.0));
    let chosen = wanted
        .filter(|wanted| wanted.0 >= 2)
        .and_then(|wanted| {
            candidates
                .iter()
                .find(|(rank, _)| (rank.0, rank.1) == (wanted.1, wanted.2))
        })
        .or_else(|| candidates.first());
    chosen
        .map(|(_, directory)| dlls_in(directory))
        .unwrap_or_default()
}

fn netstandard_references(framework: &str) -> Option<Vec<PathBuf>> {
    if framework == "netstandard2.1" {
        for root in dotnet_roots() {
            let directory = root.join("packs/NETStandard.Library.Ref/2.1.0/ref/netstandard2.1");
            if directory.is_dir() {
                return Some(dlls_in(&directory));
            }
        }
    }
    let home = PathBuf::from(std::env::var_os("NUGET_PACKAGES").or_else(|| {
        std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".nuget/packages").into())
    })?);
    for version in read_dir(&home.join("netstandard.library")) {
        let directory = version.join("build/netstandard2.0/ref");
        if directory.is_dir() {
            return Some(dlls_in(&directory));
        }
    }
    None
}

fn dlls_in(directory: &Path) -> Vec<PathBuf> {
    let mut found: Vec<PathBuf> = read_dir(directory)
        .into_iter()
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension.eq_ignore_ascii_case("dll"))
        })
        .collect();
    found.sort();
    found
}

fn dlls_under(directory: &Path, depth: usize, found: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if path.is_dir() {
            if depth < 8 && !is_skipped(&path) {
                dlls_under(&path, depth + 1, found);
            }
        } else if path
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("dll"))
        {
            found.push(path);
        }
    }
}

fn cs_under(directory: &Path, depth: usize, found: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if path.is_dir() {
            if depth < 16 && !is_skipped(&path) {
                cs_under(&path, depth + 1, found);
            }
        } else if path.extension().is_some_and(|extension| extension == "cs") {
            found.push(path);
        }
    }
}

// MARK: - Unity

/// Where Unity leaves what its source generators wrote.
///
/// Unity runs the generators itself, on every script compilation, and does
/// not commit their output anywhere a project file would name. What it does
/// is hand the compiler a folder to write it to: `-generatedfilesout:` in
/// the response files under `Library/Bee`, one per assembly. Where those say
/// nothing, `Temp/GeneratedCode`, which is where Unity has put it all along.
/// Both are read; a folder that is not there is simply empty.
fn unity_generated_folders(unity: &Path) -> Vec<PathBuf> {
    let mut folders = vec![unity.join("Temp/GeneratedCode")];
    let mut responses = Vec::new();
    rsp_under(&unity.join("Library/Bee"), 0, &mut responses);
    // The response files change when Unity compiles: until then, what they
    // say is what they said.
    let stamps: Vec<(PathBuf, (u64, u128))> = responses
        .iter()
        .map(|response| (response.clone(), stamp_of(response)))
        .collect();
    static KEPT: std::sync::Mutex<Option<(Vec<Stamped>, Vec<PathBuf>)>> =
        std::sync::Mutex::new(None);
    if let Ok(kept) = KEPT.lock()
        && let Some((kept_stamps, answer)) = kept.as_ref()
        && *kept_stamps == stamps
        && answer.first() == folders.first()
    {
        return answer.clone();
    }
    let answer = unity_generated_folders_read(folders.remove(0), responses, unity);
    if let Ok(mut kept) = KEPT.lock() {
        *kept = Some((stamps, answer.clone()));
    }
    answer
}

fn unity_generated_folders_read(
    first: PathBuf,
    responses: Vec<PathBuf>,
    unity: &Path,
) -> Vec<PathBuf> {
    let mut folders = vec![first];
    for response in responses {
        let Ok(text) = std::fs::read_to_string(&response) else {
            continue;
        };
        for argument in text.split(['\n', '\r']) {
            let argument = argument.trim();
            let Some(rest) = argument
                .strip_prefix("-generatedfilesout:")
                .or_else(|| argument.strip_prefix("/generatedfilesout:"))
            else {
                continue;
            };
            let folder = PathBuf::from(rest.trim().trim_matches('"'));
            // Unity runs the compiler from the project folder.
            let folder = if folder.is_absolute() {
                folder
            } else {
                unity.join(folder)
            };
            if !folders.contains(&folder) {
                folders.push(folder);
            }
        }
    }
    folders
}

/// The response files Unity's build writes for the compiler.
fn rsp_under(directory: &Path, depth: usize, found: &mut Vec<PathBuf>) {
    for (path, is_dir) in read_dir_kinds(directory) {
        if is_dir {
            if depth < 3 {
                rsp_under(&path, depth + 1, found);
            }
        } else if path.extension().is_some_and(|extension| extension == "rsp") {
            found.push(path);
        }
    }
}

/// Every file Unity's source generators wrote, once each.
///
/// Rustlyn compiles a Unity project as one compilation rather than one per
/// assembly, so a generator that writes the same file into every assembly
/// it runs on would declare everything in it as many times. The same text
/// is kept once; different text declaring the same name in two assemblies
/// is not told apart, and shows as the duplicate it would be in one.
fn unity_generated_files(unity: &Path) -> GeneratedListing {
    let mut files = Vec::new();
    for folder in unity_generated_folders(unity) {
        generated_under(&folder, 0, &mut files);
    }
    files.sort();
    files.dedup();
    // Telling copies apart means reading every file, tens of thousands in a
    // large project, on every compile: the answer is kept for as long as no
    // file is added, removed or written.
    // A file added, removed or renamed changes its folder's time; one
    // written again in place changes only its own, and a copy is a copy
    // still.
    let mut folders: Vec<PathBuf> = files
        .iter()
        .filter_map(|path| path.parent().map(Path::to_path_buf))
        .collect();
    folders.sort();
    folders.dedup();
    let stamps: Vec<(u64, u128)> = folders.iter().map(|folder| stamp_of(folder)).collect();
    static KEPT: std::sync::Mutex<Option<KeptListing>> = std::sync::Mutex::new(None);
    if let Ok(kept) = KEPT.lock()
        && let Some((paths, kept_stamps, answer)) = kept.as_ref()
        && *paths == files
        && *kept_stamps == stamps
    {
        return answer.clone();
    }
    let listed = files.clone();
    let mut seen: HashMap<Vec<u8>, PathBuf> = HashMap::new();
    let mut copies = Vec::new();
    files.retain(|path| {
        let Ok(bytes) = std::fs::read(path) else {
            return false;
        };
        match seen.get(&bytes) {
            Some(first) => {
                copies.push((first.clone(), path.clone()));
                false
            }
            None => {
                seen.insert(bytes, path.clone());
                true
            }
        }
    });
    let answer = (files, copies);
    if let Ok(mut kept) = KEPT.lock() {
        *kept = Some((listed, stamps, answer.clone()));
    }
    answer
}

/// `.cs` files under a folder of generated code. Unlike the project walk,
/// no folder name is skipped: an assembly may be called anything.
fn generated_under(directory: &Path, depth: usize, found: &mut Vec<PathBuf>) {
    for (path, is_dir) in read_dir_kinds(directory) {
        if is_dir {
            if depth < 8 {
                generated_under(&path, depth + 1, found);
            }
        } else if path.extension().is_some_and(|extension| extension == "cs") {
            found.push(path);
        }
    }
}

/// Every C# file under `directory`, at any depth.
pub fn files_under(directory: &Path, found: &mut Vec<PathBuf>) {
    for (path, is_dir) in read_dir_kinds(directory) {
        if is_dir {
            files_under(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "cs") {
            found.push(path);
        }
    }
}

/// The folders under `root` that hold what Unity's source generators wrote:
/// none, when `root` is not a Unity project.
#[must_use]
pub fn generated_folders(root: &Path) -> Vec<PathBuf> {
    unity_root(root).map_or_else(Vec::new, |unity| unity_generated_folders(&unity))
}

/// Whether `path` is source a generator wrote rather than a person:
/// something to read and navigate, never to edit, since the next script
/// compilation writes it again.
#[must_use]
pub fn is_generated(folders: &[PathBuf], path: &Path) -> bool {
    folders.iter().any(|folder| path.starts_with(folder))
}

/// A Unity project that has never had its project files written.
///
/// It compiles everything under `Assets/` and every package, against the
/// engine of the editor it was last opened with — which is the editor's own
/// `Managed/` folder (see `unity_managed`) and the .NET Standard it ships.
fn unity_project(root: &Path) -> Option<Project> {
    let project = unity_root(root)?;

    let built = HashSet::new();
    let mut references = References::default();
    // Plugins the project carries: precompiled, so they are references.
    let mut plugins = Vec::new();
    dlls_under(&project.join("Assets"), 0, &mut plugins);
    dlls_under(&project.join("Packages"), 0, &mut plugins);
    let cache = project.join("Library/PackageCache");
    dlls_under(&cache, 0, &mut plugins);
    plugins.sort();
    // An editor-only native plugin has no metadata and is dropped when read;
    // what is left is managed.
    for path in &plugins {
        references.add(path, &built);
    }
    if let Some(contents) = unity_editor_contents(&project) {
        let managed = unity_managed(&contents).unwrap_or_else(|| contents.join("Managed"));
        for path in dlls_in(&managed.join("UnityEngine"))
            .iter()
            .chain(&dlls_in(&managed))
        {
            references.add(path, &built);
        }
        for relative in [
            "NetStandard/ref/2.1.0",
            "NetStandard/compat/2.1.0/shims/netstandard",
            "Resources/Scripting/NetStandard/ref/2.1.0",
            "Data/NetStandard/ref/2.1.0",
        ] {
            for path in dlls_in(&contents.join(relative)) {
                references.add(&path, &built);
            }
        }
    }
    if !references.names.contains("netstandard") {
        for path in framework_references(Some("netstandard2.1")) {
            references.add(&path, &built);
        }
    }

    // Package sources live in the package cache, which no editor indexes: it
    // is generated. They are compiled all the same.
    let mut files = Vec::new();
    cs_under(&cache, 0, &mut files);
    files.retain(|path| {
        !path.components().any(|component| {
            let name = component.as_os_str().to_string_lossy();
            name.ends_with('~') || name == "Tests"
        })
    });
    files.sort();
    let assemblies = unity_assembly_names(&project);

    Some(Project {
        kind: ProjectKind::Unity,
        projects: 0,
        roots: Vec::new(),
        files,
        everything: true,
        references: references.paths,
        symbols: Vec::new(),
        generated: String::new(),
        language_versions: vec![UNITY_LANGUAGE_VERSION.to_string(); assemblies.len()],
        owned_only: false,
        unbuilt: Vec::new(),
        assembly_symbols: Vec::new(),
        assembly_references: Vec::new(),
        shared_files: Vec::new(),
        assembly_metadata: Vec::new(),
        assembly_warnings: Vec::new(),
        assembly_nullable: Vec::new(),
        assemblies,
        owned_files: Vec::new(),
        owned_folders: Vec::new(),
    })
}

/// The assemblies a Unity project compiles: the predefined ones, and one
/// for each assembly definition in it or in its packages.
fn unity_assembly_names(project: &Path) -> Vec<String> {
    let mut names: Vec<String> = [
        "Assembly-CSharp",
        "Assembly-CSharp-Editor",
        "Assembly-CSharp-firstpass",
        "Assembly-CSharp-Editor-firstpass",
    ]
    .map(str::to_string)
    .to_vec();
    let mut definitions = Vec::new();
    for folder in ["Assets", "Packages", "Library/PackageCache"] {
        asmdefs_under(&project.join(folder), 0, &mut definitions);
    }
    definitions.sort();
    for path in definitions {
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        if let Some(name) = Json::parse(text.as_bytes())
            .and_then(|json| json.get("name").and_then(Json::as_str).map(str::to_string))
            && !names.contains(&name)
        {
            names.push(name);
        }
    }
    names
}

/// What Unity's last compile of each assembly was given: its symbols and
/// the assemblies of the project it referenced — the newest response file
/// of each in the build graphs under `Library/Bee` — and when the newest of
/// those was written.
#[derive(Clone, Default)]
struct UnityBuild {
    assemblies: HashMap<String, (Vec<String>, Vec<String>)>,
    /// Where each assembly's generators were told to write.
    generated: Vec<(String, PathBuf)>,
    /// Precompiled assemblies the compiles named, the project's own and the
    /// engine's.
    plugins: Vec<PathBuf>,
    /// The precompiled assemblies each compile referenced, by lowercased
    /// file stem.
    metadata: HashMap<String, Vec<String>>,
    /// What each compile was told of warnings.
    warnings: HashMap<String, WarningOptions>,
    /// The compiles told `-nullable:enable` or `annotations`.
    nullable: HashSet<String>,
    newest: Option<std::time::SystemTime>,
}

fn unity_build(unity: &Path) -> UnityBuild {
    let mut newest_of: HashMap<String, (PathBuf, std::time::SystemTime)> = HashMap::new();
    for dag in read_dir(&unity.join("Library/Bee/artifacts")) {
        if dag.extension().is_none_or(|extension| extension != "dag") {
            continue;
        }
        for file in read_dir(&dag) {
            let name = file
                .file_name()
                .map(|name| name.to_string_lossy().into_owned())
                .unwrap_or_default();
            let Some(assembly) = name.strip_suffix(".rsp") else {
                continue;
            };
            if assembly.ends_with(".mvfrm") || assembly.ends_with(".dll") {
                continue;
            }
            let written = std::fs::metadata(&file)
                .and_then(|meta| meta.modified())
                .unwrap_or(std::time::UNIX_EPOCH);
            if newest_of
                .get(assembly)
                .is_none_or(|(_, known)| *known < written)
            {
                newest_of.insert(assembly.to_string(), (file, written));
            }
        }
    }
    // Reading them is a few megabytes; they change only when Unity compiles.
    let mut stamps: Vec<Stamped> = newest_of
        .values()
        .map(|(path, _)| (path.clone(), stamp_of(path)))
        .collect();
    stamps.sort();
    static KEPT: std::sync::Mutex<Option<(Vec<Stamped>, UnityBuild)>> = std::sync::Mutex::new(None);
    if let Ok(kept) = KEPT.lock()
        && let Some((kept_stamps, build)) = kept.as_ref()
        && *kept_stamps == stamps
    {
        return build.clone();
    }
    let mut build = UnityBuild {
        newest: newest_of.values().map(|(_, written)| *written).max(),
        ..UnityBuild::default()
    };
    for (assembly, (path, _)) in &newest_of {
        let Ok(text) = std::fs::read_to_string(path) else {
            continue;
        };
        let mut defines = Vec::new();
        let mut references = Vec::new();
        let mut metadata = Vec::new();
        let mut warnings = WarningOptions::default();
        for line in text.lines() {
            let line = line.trim();
            if let Some(folder) = line
                .strip_prefix("-generatedfilesout:")
                .or_else(|| line.strip_prefix("/generatedfilesout:"))
            {
                let folder = PathBuf::from(folder.trim().trim_matches('"'));
                let folder = if folder.is_absolute() {
                    folder
                } else {
                    unity.join(folder)
                };
                build.generated.push((assembly.clone(), folder));
            }
            if let Some(setting) = line
                .strip_prefix("-nullable:")
                .or_else(|| line.strip_prefix("/nullable:"))
            {
                if nullable_annotations(setting) {
                    build.nullable.insert(assembly.clone());
                } else {
                    build.nullable.remove(assembly);
                }
            }
            if let Some(level) = line
                .strip_prefix("-warn:")
                .or_else(|| line.strip_prefix("/warn:"))
                .and_then(|level| level.trim().parse().ok())
            {
                warnings.level = Some(level);
            } else if let Some(codes) = line
                .strip_prefix("-nowarn:")
                .or_else(|| line.strip_prefix("/nowarn:"))
            {
                warnings
                    .suppressed
                    .extend(warning_codes(codes.trim().trim_matches('"')));
            }
            if let Some(symbol) = line
                .strip_prefix("-define:")
                .or_else(|| line.strip_prefix("/define:"))
            {
                defines.extend(
                    symbol
                        .split([';', ','])
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty()),
                );
            } else if let Some(reference) = line
                .strip_prefix("-r:")
                .or_else(|| line.strip_prefix("/reference:"))
            {
                // Another assembly of the project is referenced as Unity
                // built it: `Library/Bee/artifacts/<dag>/<Name>.ref.dll`.
                let reference = reference.trim().trim_matches('"');
                // A precompiled assembly: one of the project's own files, or
                // the engine's — `Unity.CompilationPipeline.Common`, which
                // only an IL post-processor of a package references and no
                // project file names.
                if !reference.contains("Library/Bee/artifacts/") {
                    let path = Path::new(reference);
                    let path = if path.is_absolute() {
                        path.to_path_buf()
                    } else {
                        unity.join(reference)
                    };
                    if path.is_file() {
                        build.plugins.push(path);
                    }
                }
                if reference.contains("Library/Bee/artifacts/")
                    && let Some(file) = reference.rsplit('/').next()
                    && let Some(name) = file
                        .strip_suffix(".ref.dll")
                        .or_else(|| file.strip_suffix(".dll"))
                {
                    references.push(name.to_string());
                } else if let Some(file) = reference.rsplit(['/', '\\']).next()
                    && let Some(stem) = file.strip_suffix(".dll")
                {
                    metadata.push(stem.to_ascii_lowercase());
                }
            }
        }
        build.metadata.insert(assembly.clone(), metadata);
        build.warnings.insert(assembly.clone(), warnings);
        build
            .assemblies
            .insert(assembly.clone(), (defines, references));
    }
    if let Ok(mut kept) = KEPT.lock() {
        *kept = Some((stamps, build.clone()));
    }
    build
}

/// The assembly definitions written after `since`: ones Unity has not
/// compiled yet, which it will.
fn unity_definitions_since(unity: &Path, since: Option<std::time::SystemTime>) -> HashSet<String> {
    let Some(since) = since else {
        return HashSet::new();
    };
    let mut markers = Vec::new();
    asmdefs_under(unity, 0, &mut markers);
    asmdefs_under(&unity.join("Library/PackageCache"), 0, &mut markers);
    markers
        .into_iter()
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "asmdef")
        })
        .filter(|path| {
            std::fs::metadata(path)
                .and_then(|meta| meta.modified())
                .is_ok_and(|written| written > since)
        })
        .filter_map(|path| {
            let json = Json::parse(&std::fs::read(&path).ok()?)?;
            json.get("name").and_then(Json::as_str).map(str::to_string)
        })
        .collect()
}

/// The C# Unity compiles scripts as, 2021.2 to 6000.
const UNITY_LANGUAGE_VERSION: &str = "9.0";

/// The folders whose scripts go into each of `assemblies`, as Unity
/// decides: an assembly definition takes the folder it is in, an assembly
/// reference adds its folder to the definition it names, and what is left
/// under `Assets/` goes into the predefined assemblies — the editor ones
/// for an `Editor` folder, the first-pass ones under `Plugins` and
/// `Standard Assets`.
fn unity_ownership(unity: &Path, assemblies: &[String]) -> Vec<(PathBuf, u16)> {
    let index_of = |name: &str| {
        assemblies
            .iter()
            .position(|known| known == name)
            .and_then(|at| u16::try_from(at).ok())
    };
    let mut markers = Vec::new();
    asmdefs_under(unity, 0, &mut markers);
    asmdefs_under(&unity.join("Library/PackageCache"), 0, &mut markers);
    // An `.asmref` names its definition by the GUID in the definition's
    // `.meta`, or by its name.
    let mut by_guid: HashMap<String, String> = HashMap::new();
    let mut definitions: Vec<(PathBuf, String)> = Vec::new();
    let mut references: Vec<(PathBuf, String)> = Vec::new();
    for path in &markers {
        let Some(json) = std::fs::read_to_string(path)
            .ok()
            .and_then(|text| Json::parse(text.as_bytes()))
        else {
            continue;
        };
        let Some(folder) = path.parent() else {
            continue;
        };
        if path
            .extension()
            .is_some_and(|extension| extension == "asmdef")
        {
            let Some(name) = json.get("name").and_then(Json::as_str) else {
                continue;
            };
            let meta =
                std::fs::read_to_string(path.with_extension("asmdef.meta")).unwrap_or_default();
            if let Some(guid) = meta.lines().find_map(|line| line.strip_prefix("guid:")) {
                by_guid.insert(guid.trim().to_string(), name.to_string());
            }
            definitions.push((folder.to_path_buf(), name.to_string()));
        } else if let Some(reference) = json.get("reference").and_then(Json::as_str) {
            references.push((folder.to_path_buf(), reference.to_string()));
        }
    }
    let mut owned: Vec<(PathBuf, u16)> = Vec::new();
    for (folder, name) in &definitions {
        if let Some(index) = index_of(name) {
            owned.push((folder.clone(), index));
        }
    }
    for (folder, reference) in &references {
        let name = reference
            .strip_prefix("GUID:")
            .and_then(|guid| by_guid.get(guid))
            .map_or(reference.as_str(), String::as_str);
        if let Some(index) = index_of(name) {
            owned.push((folder.clone(), index));
        }
    }
    // The predefined assemblies, for what no definition took.
    let defined: Vec<PathBuf> = definitions
        .iter()
        .map(|(folder, _)| folder.clone())
        .chain(references.iter().map(|(folder, _)| folder.clone()))
        .collect();
    let assets = unity.join("Assets");
    if let Some(index) = index_of("Assembly-CSharp") {
        owned.push((assets.clone(), index));
    }
    for first in ["Plugins", "Standard Assets", "Pro Standard Assets"] {
        if let Some(index) = index_of("Assembly-CSharp-firstpass") {
            owned.push((assets.join(first), index));
        }
    }
    let mut editors = Vec::new();
    editor_folders(&assets, &defined, 0, &mut editors);
    for folder in editors {
        let first_pass = ["Plugins", "Standard Assets", "Pro Standard Assets"]
            .iter()
            .any(|first| folder.starts_with(assets.join(first)));
        let name = if first_pass {
            "Assembly-CSharp-Editor-firstpass"
        } else {
            "Assembly-CSharp-Editor"
        };
        if let Some(index) = index_of(name) {
            owned.push((folder, index));
        }
    }
    owned
}

/// Every `Editor` folder under `directory` that no assembly definition
/// takes.
fn editor_folders(directory: &Path, defined: &[PathBuf], depth: usize, found: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if !path.is_dir() || is_skipped(&path) || depth > 16 || defined.contains(&path) {
            continue;
        }
        if path.file_name().is_some_and(|name| name == "Editor") {
            found.push(path);
        } else {
            editor_folders(&path, defined, depth + 1, found);
        }
    }
}

fn asmdefs_under(directory: &Path, depth: usize, found: &mut Vec<PathBuf>) {
    for path in read_dir(directory) {
        if path.is_dir() {
            if depth < 16 && !is_skipped(&path) {
                asmdefs_under(&path, depth + 1, found);
            }
        } else if path
            .extension()
            .is_some_and(|extension| extension == "asmdef" || extension == "asmref")
        {
            found.push(path);
        }
    }
}

/// The Unity project at `root`, or in the one folder under it that holds
/// one — a game's repository often has the project a level down.
fn unity_root(root: &Path) -> Option<PathBuf> {
    if is_unity(root) {
        return Some(root.to_path_buf());
    }
    let found: Vec<PathBuf> = subdirectories(root)
        .into_iter()
        .filter(|dir| is_unity(dir))
        .collect();
    match found.as_slice() {
        [one] => Some(one.clone()),
        _ => None,
    }
}

fn is_unity(root: &Path) -> bool {
    root.join("ProjectSettings/ProjectVersion.txt").is_file() && root.join("Assets").is_dir()
}

/// The `Contents` folder of the editor a Unity project belongs to.
///
/// Unity writes it to `Library/EditorInstance.json` whenever it opens the
/// project; a project never opened on this machine is found by its version
/// where Unity Hub installs editors.
fn unity_editor_contents(project: &Path) -> Option<PathBuf> {
    if let Ok(text) = std::fs::read_to_string(project.join("Library/EditorInstance.json"))
        && let Some(json) = Json::parse(text.as_bytes())
    {
        let contents = json
            .get("app_contents_path")
            .and_then(Json::as_str)
            .map(PathBuf::from)
            .or_else(|| {
                json.get("app_path")
                    .and_then(Json::as_str)
                    .map(|path| PathBuf::from(path).join("Contents"))
            });
        if let Some(contents) = contents.filter(|contents| contents.is_dir()) {
            return Some(contents);
        }
    }
    let text = std::fs::read_to_string(project.join("ProjectSettings/ProjectVersion.txt")).ok()?;
    let version = text
        .lines()
        .find_map(|line| line.strip_prefix("m_EditorVersion:"))?
        .trim()
        .to_string();
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_default();
    [
        PathBuf::from(format!(
            "/Applications/Unity/Hub/Editor/{version}/Unity.app/Contents"
        )),
        home.join(format!(
            "Applications/Unity/Hub/Editor/{version}/Unity.app/Contents"
        )),
        home.join(format!("Unity/Hub/Editor/{version}/Editor/Data")),
        PathBuf::from(format!("/opt/unity/Editor/{version}/Editor/Data")),
        PathBuf::from("/Applications/Unity/Unity.app/Contents"),
    ]
    .into_iter()
    .find(|contents| unity_managed(contents).is_some())
}

/// The folder of an editor's `Contents` that holds the engine's assemblies.
///
/// Unity 6 moved it from `Contents/Managed` to
/// `Contents/Resources/Scripting/Managed`; an editor has one or the other.
fn unity_managed(contents: &Path) -> Option<PathBuf> {
    ["Managed", "Resources/Scripting/Managed"]
        .into_iter()
        .map(|relative| contents.join(relative))
        .find(|managed| managed.is_dir())
}

// MARK: - a folder

fn folder_project(_root: &Path) -> Project {
    let built = HashSet::new();
    let mut references = References::default();
    for path in framework_references(None) {
        references.add(&path, &built);
    }
    Project {
        kind: ProjectKind::Folder,
        projects: 0,
        roots: Vec::new(),
        files: Vec::new(),
        everything: true,
        references: references.paths,
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
    }
}

/// Every name the project files mention, for tests.
#[cfg(test)]
fn reference_names(project: &Project) -> std::collections::BTreeSet<String> {
    project
        .references
        .iter()
        .filter_map(|path| {
            path.file_stem()
                .map(|stem| stem.to_string_lossy().into_owned())
        })
        .collect()
}

/// Which files of `paths` a project compiles, plus the ones it names that the
/// editor did not.
#[must_use]
pub fn compiled_files(project: &Project, paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut seen: HashSet<&Path> = HashSet::new();
    let mut files = Vec::new();
    let owners = if project.owned_only {
        let list: Vec<&Path> = paths.iter().map(PathBuf::as_path).collect();
        project.owners_of(&list)
    } else {
        Vec::new()
    };
    for (index, path) in paths.iter().enumerate() {
        let built = owners
            .get(index)
            .is_none_or(|owner| *owner != u16::MAX && !project.unbuilt.contains(owner));
        if path.extension().is_some_and(|extension| extension == "cs")
            && project.compiles(path)
            && built
            && seen.insert(path)
        {
            files.push(path.clone());
        }
    }
    // What a project file names is compiled too, but for an assembly Unity
    // does not build.
    let named: Vec<&Path> = project.files.iter().map(PathBuf::as_path).collect();
    let named_owners = if project.unbuilt.is_empty() {
        Vec::new()
    } else {
        project.owners_of(&named)
    };
    for (index, path) in project.files.iter().enumerate() {
        let built = named_owners
            .get(index)
            .is_none_or(|owner| !project.unbuilt.contains(owner));
        if built && seen.insert(path) {
            files.push(path.clone());
        }
    }
    files
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "rustlyn-project-{name}-{}-{:?}",
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
    fn an_old_style_project_names_its_files_references_and_symbols() {
        let dir = TempDir::new("legacy");
        let engine = dir.write("Engine/UnityEngine.CoreModule.dll", "not really");
        dir.write("Library/ScriptAssemblies/Game.dll", "built from source");
        dir.write(
            "Game.csproj",
            &format!(
                r#"<?xml version="1.0" encoding="utf-8"?>
<Project ToolsVersion="4.0" DefaultTargets="Build" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">
  <PropertyGroup Condition=" '$(Configuration)|$(Platform)' == 'Debug|AnyCPU' ">
    <DefineConstants>UNITY_EDITOR;UNITY_2022_3_OR_NEWER;DEBUG</DefineConstants>
  </PropertyGroup>
  <PropertyGroup><AssemblyName>Game</AssemblyName></PropertyGroup>
  <ItemGroup>
    <Compile Include="Assets\Scripts\Player.cs" />
    <!-- <Compile Include="Assets\Scripts\Commented.cs" /> -->
  </ItemGroup>
  <ItemGroup>
    <Reference Include="UnityEngine.CoreModule"><HintPath>{}</HintPath></Reference>
    <Reference Include="Game"><HintPath>Library\ScriptAssemblies\Game.dll</HintPath></Reference>
  </ItemGroup>
</Project>"#,
                engine.display()
            ),
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.kind, ProjectKind::Msbuild);
        assert_eq!(project.projects, 1);
        assert_eq!(project.files, vec![dir.0.join("Assets/Scripts/Player.cs")]);
        assert!(
            project
                .symbols
                .contains(&"UNITY_2022_3_OR_NEWER".to_string())
        );
        // The engine is a reference; the assembly the project itself builds
        // is not, or every type in it would be declared twice.
        let names = reference_names(&project);
        assert!(names.contains("UnityEngine.CoreModule"));
        assert!(!names.contains("Game"));
        assert!(!project.everything);
    }

    #[test]
    fn a_tool_project_in_a_subfolder_does_not_make_a_unity_project_msbuild() {
        let dir = TempDir::new("unity-tools");
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 2022.3.76f1\n",
        );
        dir.write("Assets/Player.cs", "public class Player {}\n");
        dir.write(
            "SourceGenerators/Generator/Generator.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>netstandard2.0</TargetFramework></PropertyGroup></Project>"#,
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.kind, ProjectKind::Unity);
    }

    #[test]
    fn a_unity_6_editor_keeps_the_engine_under_resources() {
        let dir = TempDir::new("unity6");
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 6000.3.14f1\n",
        );
        dir.write("Assets/Player.cs", "public class Player {}\n");
        let contents = dir.0.join("Editor/Unity.app/Contents");
        dir.write(
            "Editor/Unity.app/Contents/Resources/Scripting/Managed/UnityEngine/UnityEngine.CoreModule.dll",
            "not really",
        );
        dir.write(
            "Library/EditorInstance.json",
            // A Windows path's `\` is `\\` in JSON, as Unity writes it.
            &format!(
                r#"{{"app_contents_path": "{}"}}"#,
                contents.display().to_string().replace('\\', "\\\\")
            ),
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.kind, ProjectKind::Unity);
        assert!(reference_names(&project).contains("UnityEngine.CoreModule"));
    }

    /// A Unity project with a script, and what two generators left for it:
    /// one in `Temp/GeneratedCode`, written identically for two assemblies,
    /// and one in the folder a response file names.
    fn unity_with_generated_code(dir: &TempDir) -> PathBuf {
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 6000.0.0f1\n",
        );
        let script = dir.write(
            "Assets/Player.cs",
            "public partial class Player { public int Use() => GeneratedHealth; }\n",
        );
        let shared = "public static class Registry { public static int Count; }\n";
        dir.write("Temp/GeneratedCode/Game/Registry.g.cs", shared);
        dir.write("Temp/GeneratedCode/Game.Editor/Registry.g.cs", shared);
        dir.write(
            "Library/Bee/artifacts/1900b0aE.dag/Game.rsp",
            "-target:library\n-generatedfilesout:\"Library/Bee/artifacts/1900b0aE.dag/Game.gen\"\n",
        );
        dir.write(
            "Library/Bee/artifacts/1900b0aE.dag/Game.gen/Player.Health.g.cs",
            "public partial class Player { public int GeneratedHealth => 100; }\n",
        );
        script
    }

    #[test]
    fn what_unity_generators_wrote_is_compiled_once_and_known_as_generated() {
        let dir = TempDir::new("generated");
        unity_with_generated_code(&dir);
        let project = Project::discover(&dir.0, &[]);
        let names: Vec<String> = project
            .files
            .iter()
            .filter_map(|path| path.strip_prefix(&dir.0).ok())
            .map(|path| path.to_string_lossy().replace('\\', "/"))
            .collect();
        assert!(
            names.contains(
                &"Library/Bee/artifacts/1900b0aE.dag/Game.gen/Player.Health.g.cs".to_owned()
            ),
            "the response file's folder is read: {names:?}"
        );
        let registries = names
            .iter()
            .filter(|name| name.ends_with("Registry.g.cs"))
            .count();
        assert_eq!(
            registries, 1,
            "the same text for two assemblies is one file: {names:?}"
        );

        let folders = generated_folders(&dir.0);
        assert!(is_generated(
            &folders,
            &dir.0.join("Temp/GeneratedCode/Game/Registry.g.cs")
        ));
        assert!(is_generated(
            &folders,
            &dir.0
                .join("Library/Bee/artifacts/1900b0aE.dag/Game.gen/Player.Health.g.cs")
        ));
        assert!(!is_generated(&folders, &dir.0.join("Assets/Player.cs")));
    }

    #[test]
    fn generated_code_is_navigable_but_never_edited() {
        let dir = TempDir::new("generated-session");
        let script = unity_with_generated_code(&dir);
        let session = crate::session::Session::new(&dir.0, None, Vec::new());
        session.reindex(std::slice::from_ref(&script));
        session.compile(std::slice::from_ref(&script));
        let text = std::fs::read_to_string(&script).expect("the script");
        let at = text.find("GeneratedHealth").expect("the use") as u32;

        let found = session
            .definition_in(&script, at, None)
            .expect("the generated property is where the use leads");
        let target = &found.targets[0];
        assert!(
            target
                .path
                .to_string_lossy()
                .ends_with("Player.Health.g.cs"),
            "{target:?}"
        );
        assert!(session.is_generated(dir.0.join(&target.path)));

        let refused = session
            .rename(
                &script,
                at,
                "Health",
                None,
                crate::semantic::RenameOptions::default(),
            )
            .expect("an answer");
        assert!(
            refused.refused.is_some() && refused.changes.changes.is_empty(),
            "what only a generator declares is not renamed: {refused:?}"
        );

        // A partial type is renamed in the project's part; the generator
        // will name its own part as it was told.
        let player = text.find("Player").expect("the class") as u32;
        let renamed = session
            .rename(
                &script,
                player,
                "Hero",
                None,
                crate::semantic::RenameOptions::default(),
            )
            .expect("a rename");
        assert!(renamed.refused.is_none(), "{renamed:?}");
        assert!(
            renamed
                .changes
                .changes
                .iter()
                .any(|change| change.path == script),
            "{renamed:?}"
        );
        assert!(
            renamed
                .changes
                .changes
                .iter()
                .all(|change| !session.is_generated(&change.path)),
            "nothing a generator wrote is edited: {:?}",
            renamed.changes
        );
    }

    #[test]
    fn a_unity_project_compiles_its_scripts_whatever_its_project_files_list() {
        let dir = TempDir::new("stale");
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 2022.3.1f1\n",
        );
        dir.write("Assets/Old.cs", "class Old { }");
        dir.write(
            "Assembly-CSharp.csproj",
            r#"<Project><ItemGroup><Compile Include="Assets\Old.cs" /></ItemGroup></Project>"#,
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.kind, ProjectKind::Msbuild);
        assert!(project.compiles(&dir.0.join("Assets/New.cs")));
    }

    #[test]
    fn a_solution_decides_which_projects_count() {
        let dir = TempDir::new("solution");
        dir.write(
            "src/A/A.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk"></Project>"#,
        );
        dir.write(
            "tools/B/B.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk"></Project>"#,
        );
        dir.write(
            "App.sln",
            "Microsoft Visual Studio Solution File, Format Version 12.00\n\
             Project(\"{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}\") = \"A\", \"src\\A\\A.csproj\", \"{1}\"\n\
             EndProject\n",
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.projects, 1);
        assert_eq!(project.roots, vec![dir.0.join("src/A")]);
        assert!(project.compiles(&dir.0.join("src/A/X.cs")));
        assert!(!project.compiles(&dir.0.join("tools/B/X.cs")));
        assert!(!project.compiles(&dir.0.join("src/A/obj/Debug/X.cs")));
    }

    #[test]
    fn an_sdk_project_gets_the_symbols_and_usings_the_sdk_would_generate() {
        let dir = TempDir::new("sdk");
        dir.write(
            "App/App.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net8.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
    <DefineConstants>$(DefineConstants);FEATURE_X</DefineConstants>
  </PropertyGroup>
  <ItemGroup><Using Include="System.Text" /><Using Include="System.Math" Static="true" /></ItemGroup>
</Project>"#,
        );
        let project = Project::discover(&dir.0, &["EDITOR_SAID".to_string()]);
        for symbol in [
            "NET",
            "NET8_0",
            "NET8_0_OR_GREATER",
            "NET5_0_OR_GREATER",
            "NETCOREAPP",
            "FEATURE_X",
            "EDITOR_SAID",
        ] {
            assert!(project.symbols.contains(&symbol.to_string()), "{symbol}");
        }
        assert!(!project.symbols.contains(&"NET9_0_OR_GREATER".to_string()));
        assert!(
            project
                .generated
                .contains("global using global::System.Linq;")
        );
        assert!(
            project
                .generated
                .contains("global using global::System.Text;")
        );
        assert!(
            project
                .generated
                .contains("global using static global::System.Math;")
        );
    }

    #[test]
    fn what_a_directory_build_props_shares_is_the_projects() {
        let dir = TempDir::new("props");
        dir.write(
            "eng/Common.props",
            r#"<Project>
  <PropertyGroup><ImplicitUsings>enable</ImplicitUsings></PropertyGroup>
</Project>"#,
        );
        dir.write(
            "Directory.Build.props",
            r#"<Project>
  <Import Project="$(MsBuildThisFileDirectory)eng/Common.props" />
  <PropertyGroup>
    <TargetFrameworks>net8.0;netstandard2.0</TargetFrameworks>
  </PropertyGroup>
  <ItemGroup>
    <Using Include="System.ReadOnlySpan&lt;System.Char&gt;" Alias="CharSpan" />
    <Using Remove="System.Net.Http" />
  </ItemGroup>
  <PropertyGroup Condition="'$(CI)' == 'true'">
    <DefineConstants>ONLY_ON_CI</DefineConstants>
  </PropertyGroup>
  <PropertyGroup Condition="'$(TargetFramework)' == 'net471' Or '$(TargetFramework)' == 'net8.0'">
    <DefineConstants>$(DefineConstants);FULL_OR_NET8</DefineConstants>
  </PropertyGroup>
</Project>"#,
        );
        dir.write(
            "Directory.Build.targets",
            r#"<Project>
  <ItemGroup><Using Include="System.Diagnostics" /></ItemGroup>
  <ItemGroup Condition="'$(Extra)' == 'true'"><Using Include="Extra.Namespace" /></ItemGroup>
</Project>"#,
        );
        dir.write(
            "src/Lib/Lib.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>
</Project>"#,
        );
        let project = Project::discover(&dir.0, &[]);
        assert!(
            project
                .generated
                .contains("global using global::System.Collections.Generic;"),
            "{}",
            project.generated
        );
        assert!(
            project
                .generated
                .contains("global using CharSpan = global::System.ReadOnlySpan<System.Char>;"),
            "{}",
            project.generated
        );
        assert!(!project.generated.contains("System.Net.Http"));
        assert!(
            project
                .generated
                .contains("global using global::System.Diagnostics;")
        );
        // What holds only under a condition is not taken to.
        assert!(!project.generated.contains("Extra.Namespace"));
        assert!(!project.symbols.contains(&"ONLY_ON_CI".to_string()));
        assert!(project.symbols.contains(&"FULL_OR_NET8".to_string()));
        // The project's own framework, not the ones it would have shared.
        assert!(project.symbols.contains(&"NET8_0".to_string()));
        assert!(!project.symbols.contains(&"NETSTANDARD2_0".to_string()));
    }

    /// An old-style project — what Unity writes — is not one the SDK
    /// builds, and takes nothing from a `Directory.Build.props` above it.
    #[test]
    fn an_old_style_project_takes_nothing_from_a_directory_build_props() {
        let dir = TempDir::new("props-old");
        dir.write(
            "Directory.Build.props",
            r#"<Project><PropertyGroup><ImplicitUsings>enable</ImplicitUsings>
  <DefineConstants>SHARED</DefineConstants></PropertyGroup></Project>"#,
        );
        dir.write(
            "Game/Assembly-CSharp.csproj",
            r#"<?xml version="1.0" encoding="utf-8"?>
<Project ToolsVersion="4.0" DefaultTargets="Build" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">
  <PropertyGroup><DefineConstants>UNITY_2021_3</DefineConstants></PropertyGroup>
  <ItemGroup><Compile Include="Assets/A.cs" /></ItemGroup>
</Project>"#,
        );
        let project = Project::discover(&dir.0.join("Game"), &[]);
        assert!(project.symbols.contains(&"UNITY_2021_3".to_string()));
        assert!(!project.symbols.contains(&"SHARED".to_string()));
        assert!(project.generated.is_empty(), "{}", project.generated);
    }

    #[test]
    fn framework_symbols_follow_the_sdk() {
        let standard = framework_symbols("netstandard2.0");
        assert!(standard.contains(&"NETSTANDARD2_0".to_string()));
        assert!(standard.contains(&"NETSTANDARD1_6_OR_GREATER".to_string()));
        assert!(!standard.contains(&"NETSTANDARD2_1_OR_GREATER".to_string()));
        let framework = framework_symbols("net472");
        assert!(framework.contains(&"NETFRAMEWORK".to_string()));
        assert!(framework.contains(&"NET472".to_string()));
        assert!(framework.contains(&"NET47_OR_GREATER".to_string()));
        assert!(!framework.contains(&"NET48_OR_GREATER".to_string()));
    }

    #[test]
    fn a_restored_project_brings_its_package_assemblies() {
        let dir = TempDir::new("assets");
        let packages = dir.0.join("nuget");
        dir.write(
            "nuget/newtonsoft.json/13.0.3/lib/net6.0/Newtonsoft.Json.dll",
            "x",
        );
        dir.write(
            "App/App.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk"></Project>"#,
        );
        dir.write(
            "App/obj/project.assets.json",
            &format!(
                r#"{{
  "version": 3,
  "targets": {{
    "net8.0": {{
      "Newtonsoft.Json/13.0.3": {{
        "type": "package",
        "compile": {{ "lib/net6.0/Newtonsoft.Json.dll": {{ "related": ".xml" }} }}
      }},
      "Other/1.0.0": {{ "type": "project" }}
    }}
  }},
  "libraries": {{
    "Newtonsoft.Json/13.0.3": {{ "type": "package", "path": "newtonsoft.json/13.0.3" }}
  }},
  "packageFolders": {{ "{}": {{}} }}
}}"#,
                packages.display().to_string().replace('\\', "\\\\")
            ),
        );
        let project = Project::discover(&dir.0, &[]);
        assert!(reference_names(&project).contains("Newtonsoft.Json"));
    }

    #[test]
    fn a_unity_project_without_project_files_still_has_its_packages_and_plugins() {
        let dir = TempDir::new("unity");
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 6000.0.1f1\n",
        );
        dir.write("Assets/Scripts/Player.cs", "class Player { }");
        dir.write("Assets/Plugins/Thing.dll", "x");
        dir.write(
            "Library/PackageCache/com.unity.ugui@abc/Runtime/Button.cs",
            "class Button { }",
        );
        dir.write(
            "Library/PackageCache/com.unity.ugui@abc/Tests/ButtonTests.cs",
            "class T { }",
        );
        dir.write(
            "Library/PackageCache/com.unity.ugui@abc/Samples~/Sample.cs",
            "class S { }",
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.kind, ProjectKind::Unity);
        assert!(project.everything);
        assert_eq!(
            project.files,
            vec![
                dir.0
                    .join("Library/PackageCache/com.unity.ugui@abc/Runtime/Button.cs")
            ]
        );
        assert!(reference_names(&project).contains("Thing"));
    }

    /// One project of a solution naming the core library is enough for all:
    /// the framework installed beside it would declare its types twice.
    #[test]
    fn a_project_without_a_core_library_shares_the_solutions() {
        let dir = TempDir::new("core-shared");
        dir.write("Refs/netstandard.dll", "x");
        dir.write(
            "Game.csproj",
            r#"<Project><ItemGroup><Reference Include="netstandard"><HintPath>Refs\netstandard.dll</HintPath></Reference></ItemGroup></Project>"#,
        );
        dir.write("Game.Tests.csproj", r#"<Project><ItemGroup /></Project>"#);
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(project.projects, 2);
        assert!(reference_names(&project).contains("netstandard"));
        assert!(
            !reference_names(&project).contains("System.Runtime"),
            "no framework: {:?}",
            reference_names(&project)
        );
    }

    /// Unity compiles a script only into an assembly it builds: not the
    /// generators' own solution beside `Assets/`, not a package's tests it
    /// was not asked for — though it writes them a project file — not a
    /// sample. A script added since the project files were written is in.
    #[test]
    fn a_unity_project_compiles_only_what_goes_into_an_assembly_it_builds() {
        let dir = TempDir::new("unity-built");
        dir.write(
            "ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 2022.3.76f1\n",
        );
        dir.write("Assets/Game/Player.cs", "class Player { }");
        dir.write("Assets/Game/Added.cs", "class Added { }");
        dir.write(
            "Packages/com.p/Runtime/P.asmdef",
            "\u{feff}{\"name\":\"P\"}",
        );
        dir.write("Packages/com.p/Runtime/Thing.cs", "class Thing { }");
        dir.write(
            "Packages/com.p/Tests/P.Tests.asmdef",
            r#"{"name":"P.Tests"}"#,
        );
        dir.write("Packages/com.p/Tests/ThingTests.cs", "class ThingTests { }");
        dir.write("Packages/com.p/Samples~/Sample.cs", "class Sample { }");
        dir.write("Generators/Gen/Generator.cs", "class Generator { }");
        dir.write(
            "Library/PackageCache/com.q@abc/Runtime/Q.asmdef",
            r#"{"name":"Q"}"#,
        );
        dir.write(
            "Library/PackageCache/com.q@abc/Runtime/Lists.cs",
            "class Lists { }",
        );
        dir.write(
            "Library/PackageCache/com.q@abc/Tests/Q.Tests.asmdef",
            r#"{"name":"Q.Tests"}"#,
        );
        dir.write(
            "Library/PackageCache/com.q@abc/Tests/ListsTests.cs",
            "class ListsTests { }",
        );
        dir.write("Library/Bee/artifacts/1.dag/Q.rsp", "");
        dir.write(
            "Assembly-CSharp.csproj",
            r#"<Project><PropertyGroup><AssemblyName>Assembly-CSharp</AssemblyName><LangVersion>9.0</LangVersion></PropertyGroup><ItemGroup><Compile Include="Assets\Game\Player.cs" /><Reference Include="Q"><HintPath>Library\ScriptAssemblies\Q.dll</HintPath></Reference><Reference Include="Other"><HintPath>Library\ScriptAssemblies\Other.dll</HintPath></Reference></ItemGroup></Project>"#,
        );
        dir.write("Library/ScriptAssemblies/Q.dll", "");
        dir.write("Library/ScriptAssemblies/Other.dll", "");
        dir.write(
            "P.Tests.csproj",
            r#"<Project><PropertyGroup><AssemblyName>P.Tests</AssemblyName></PropertyGroup><ItemGroup><Compile Include="Packages\com.p\Tests\ThingTests.cs" /></ItemGroup></Project>"#,
        );
        dir.write(
            "Library/Bee/artifacts/1.dag/Assembly-CSharp.rsp",
            "-target:library\n-define:UNITY_2022_3\n-define:GAME\n-r:\"Library/Bee/artifacts/1.dag/P.ref.dll\"\n-r:\"/Unity/UnityEngine.dll\"\n/nowarn:0169\n/nowarn:0649,CS0618",
        );
        dir.write("Library/Bee/artifacts/1.dag/P.rsp", "-define:PKG\n-warn:0");
        let project = Project::discover(&dir.0, &[]);
        let paths: Vec<PathBuf> = [
            "Assets/Game/Player.cs",
            "Assets/Game/Added.cs",
            "Packages/com.p/Runtime/Thing.cs",
            "Packages/com.p/Tests/ThingTests.cs",
            "Packages/com.p/Samples~/Sample.cs",
            "Generators/Gen/Generator.cs",
        ]
        .iter()
        .map(|path| dir.0.join(path))
        .collect();
        assert_eq!(
            compiled_files(&project, &paths),
            vec![
                dir.0.join("Assets/Game/Player.cs"),
                dir.0.join("Assets/Game/Added.cs"),
                dir.0.join("Packages/com.p/Runtime/Thing.cs"),
                // A package in the cache with no project file of its own.
                dir.0
                    .join("Library/PackageCache/com.q@abc/Runtime/Lists.cs"),
            ]
        );
        assert_eq!(
            project.parse_options(0).language_version,
            rustlyn_syntax::LanguageVersion::CSharp9
        );
        // Each assembly's symbols and references are what Unity compiled it
        // with.
        let index = |name: &str| {
            u16::try_from(
                project
                    .assemblies
                    .iter()
                    .position(|known| known == name)
                    .unwrap(),
            )
            .unwrap()
        };
        let game = index("Assembly-CSharp");
        assert_eq!(
            project.parse_options(game).preprocessor_symbols,
            ["UNITY_2022_3", "GAME"]
        );
        assert_eq!(project.assembly_references[usize::from(game)], [index("P")]);
        assert_eq!(
            project.parse_options(index("P")).preprocessor_symbols,
            ["PKG"]
        );
        // `Q` is compiled here from its source: its build in
        // `Library/ScriptAssemblies` is no reference. `Other` is one.
        let stems: Vec<String> = project
            .references
            .iter()
            .filter_map(|path| Some(path.file_stem()?.to_string_lossy().into_owned()))
            .collect();
        assert!(stems.contains(&"Other".to_string()), "{stems:?}");
        assert!(!stems.contains(&"Q".to_string()), "{stems:?}");
        // The warnings each compile was told to give: a package none.
        let warnings = |name: &str| project.assembly_warnings[usize::from(index(name))].clone();
        assert_eq!(
            warnings("Assembly-CSharp"),
            WarningOptions {
                level: None,
                suppressed: vec![169, 649, 618]
            }
        );
        assert!(warnings("Assembly-CSharp").reports(612));
        assert!(!warnings("Assembly-CSharp").reports(618));
        assert_eq!(warnings("P").level, Some(0));
        assert!(!warnings("P").reports(612));
    }

    #[test]
    fn a_project_file_says_which_warnings_it_gives() {
        let dir = TempDir::new("nowarn");
        dir.write("A.cs", "class A { }");
        dir.write(
            "A.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><WarningLevel>3</WarningLevel><NoWarn>$(NoWarn);CS0618;1591</NoWarn></PropertyGroup></Project>"#,
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(
            project.assembly_warnings,
            [WarningOptions {
                level: Some(3),
                suppressed: vec![618, 1591]
            }]
        );
    }

    #[test]
    fn a_shared_project_that_takes_a_whole_folder_brings_it() {
        let dir = TempDir::new("glob");
        dir.write("Shared/Pool.cs", "class Pool { }");
        dir.write("Shared/Deep/Builder.cs", "class Builder { }");
        dir.write("Shared/readme.md", "");
        dir.write(
            "Shared/Shared.projitems",
            r#"<Project><ItemGroup><Compile Include="$(MSBuildThisFileDirectory)**\*.cs" /></ItemGroup></Project>"#,
        );
        dir.write(
            "App/App.csproj",
            r#"<Project Sdk="Microsoft.NET.Sdk"><Import Project="..\Shared\Shared.projitems" Label="Shared" /></Project>"#,
        );
        let project = Project::discover(&dir.0, &[]);
        assert_eq!(
            project.files,
            vec![
                dir.0.join("Shared/Deep/Builder.cs"),
                dir.0.join("Shared/Pool.cs")
            ]
        );
    }

    #[test]
    fn wildcards_match_file_names() {
        assert!(wildcard("*.cs", "A.cs"));
        assert!(!wildcard("*.cs", "A.csx"));
        assert!(wildcard("Gen*.g.cs", "Generated.g.cs"));
        assert!(!wildcard("Gen*.g.cs", "Other.g.cs"));
        assert!(wildcard("A.cs", "A.cs"));
    }

    #[test]
    fn compiled_files_take_the_editors_list_and_add_what_the_project_names() {
        let project = Project {
            kind: ProjectKind::Msbuild,
            projects: 1,
            roots: vec![PathBuf::from("/p/App")],
            files: vec![PathBuf::from("/p/Legacy/Old.cs")],
            everything: false,
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
        let files = compiled_files(
            &project,
            &[
                PathBuf::from("/p/App/A.cs"),
                PathBuf::from("/p/App/readme.md"),
                PathBuf::from("/p/Other/B.cs"),
            ],
        );
        assert_eq!(
            files,
            vec![
                PathBuf::from("/p/App/A.cs"),
                PathBuf::from("/p/Legacy/Old.cs")
            ]
        );
    }
}
