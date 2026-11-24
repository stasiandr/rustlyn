//! Whether the projects' packages were restored on this machine — with no
//! network and no `dotnet restore`, from what a restore leaves in
//! `obj/project.assets.json`. Rustlyn reads the same file to find package
//! assemblies (`rustlyn_ide::project`): no file, no package in it, or no
//! package folder on disk, and the compilation does not see the package.
//!
//! Projects inside a Unity project are not checked: Unity's packages are its
//! own business, and SDK-style generators and analyzers next to the scripts
//! are built separately and often never restored.

use std::collections::HashSet;
use std::path::Path;

use rustlyn_ide::formats::json::Json;

use super::projects::{self, Project, Reference, file_stem, parent};
use super::text::{compare_ignoring_case, is_newline, trim_spaces, unique_ignoring_case};

/// Where a restore leaves a project's packages, and where Rustlyn looks.
pub const ASSETS_FILE: &str = "obj/project.assets.json";

/// Whether a change to this file on disk is reason to check again.
pub fn is_relevant(path: &str) -> bool {
    projects::is_relevant(path) || is_assets(path)
}

/// Whether a restore wrote a project's packages anew.
pub fn is_assets(path: &str) -> bool {
    path.ends_with(&format!("/{ASSETS_FILE}"))
}

/// Why the compilation does not see packages, most important first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(i32)]
pub enum Reason {
    /// The restore did not find them: not in the feeds, or a feed did not
    /// answer or let it in.
    Failed = 0,
    /// The restore found them, but their folders are no longer on disk.
    Missing = 1,
    /// They were referenced after the last restore.
    Outdated = 2,
    /// The project was never restored here.
    NotRestored = 3,
}

impl Reason {
    /// A stable code for the reason.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Failed => "failed",
            Self::Missing => "missing",
            Self::Outdated => "outdated",
            Self::NotRestored => "not_restored",
        }
    }
}

impl std::fmt::Display for Reason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Failed => "the restore could not find them",
            Self::Missing => "their folders are gone from disk",
            Self::Outdated => "referenced after the last restore",
            Self::NotRestored => "never restored here",
        })
    }
}

/// A project's packages the compilation does not see, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Problem {
    /// From the root: `Server/Server.csproj`.
    pub project: String,
    pub reason: Reason,
    pub packages: Vec<String>,
    /// What the restore itself said: `NU1301: Unable to load the service index…`.
    pub messages: Vec<String>,
}

/// The state of the projects' packages on this machine.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Report {
    /// SDK-style .NET projects: there are packages to show.
    pub project_count: usize,
    pub problems: Vec<Problem>,
    /// At least one checked project was restored: it has been built here.
    pub restored_somewhere: bool,
}

impl Report {
    pub fn has_projects(&self) -> bool {
        self.project_count > 0
    }

    /// Worth telling the user: a restore did not find packages, their folders
    /// are gone, references are newer than the restore — or no project was
    /// restored at all. Unrestored tests and tools next to a restored project
    /// are no reason: evidently they are not built here.
    pub fn needs_attention(&self) -> bool {
        self.problems
            .iter()
            .any(|p| p.reason != Reason::NotRestored)
            || (!self.restored_somewhere && !self.problems.is_empty())
    }

    /// The packages in order of reasons, without repeats.
    pub fn packages(&self) -> Vec<String> {
        unique_ignoring_case(
            self.problems
                .iter()
                .flat_map(|p| p.packages.iter().cloned()),
        )
    }

    /// The projects that need a restore, those where it failed first.
    pub fn projects(&self) -> Vec<String> {
        unique_ignoring_case(self.problems.iter().map(|p| p.project.clone()))
    }

    /// What the restore said: the first two, without repeats.
    pub fn messages(&self) -> Vec<String> {
        unique_ignoring_case(
            self.problems
                .iter()
                .flat_map(|p| p.messages.iter().cloned()),
        )
        .into_iter()
        .take(2)
        .collect()
    }

    /// The names (`Server`) of projects with this reason, without repeats.
    pub fn names(&self, reason: Reason) -> Vec<String> {
        unique_ignoring_case(
            self.problems
                .iter()
                .filter(|p| p.reason == reason)
                .map(|p| file_stem(&p.project)),
        )
    }

    /// A project's packages over all reasons, without repeats.
    pub fn packages_of(&self, project: &str) -> Vec<String> {
        unique_ignoring_case(
            self.problems
                .iter()
                .filter(|p| p.project == project)
                .flat_map(|p| p.packages.iter().cloned()),
        )
    }
}

/// What is the matter with the packages of projects from
/// [`projects::discover`]. Problems are sorted by reason, then by project
/// path.
pub fn check(root: &Path, projects: &[Project]) -> Report {
    let mut report = Report {
        project_count: projects.len(),
        ..Default::default()
    };
    for project in projects
        .iter()
        .filter(|p| !is_in_unity_project(&p.path, root))
    {
        let directory = parent(&project.path);
        let folder = if directory.is_empty() {
            root.to_path_buf()
        } else {
            root.join(directory)
        };
        let file = folder.join(ASSETS_FILE);
        if let Ok(data) = std::fs::read(&file) {
            // A restore was here, even if the file is being written right
            // now; then it is checked again once written.
            report.restored_somewhere = true;
            let Some(assets) = Assets::parse(&data) else {
                continue;
            };
            let edited = is_newer(&root.join(&project.path), &file);
            report.problems.extend(problems(
                &project.path,
                &project.references,
                &assets,
                edited,
                |p| p.exists(),
            ));
        } else {
            let ids = explicit_ids(&project.references);
            if ids.is_empty() || moves_intermediate(&project.path, root) {
                continue;
            }
            report.problems.push(Problem {
                project: project.path.clone(),
                reason: Reason::NotRestored,
                packages: ids,
                messages: Vec::new(),
            });
        }
    }
    report.problems.sort_by(|a, b| {
        a.reason
            .cmp(&b.reason)
            .then_with(|| a.project.cmp(&b.project))
    });
    report
}

/// A project that was restored. `edited_since_restore`: the `.csproj` is
/// newer than the restore's file; otherwise the restore saw exactly this
/// text, and references missing from its file were dropped by the SDK or
/// `Directory.Build.targets`.
pub fn problems(
    project: &str,
    references: &[Reference],
    assets: &Assets,
    edited_since_restore: bool,
    exists: impl Fn(&Path) -> bool,
) -> Vec<Problem> {
    let mut out = Vec::new();
    // Asked for and not found: not in the feeds, or a feed did not answer
    // or wanted a login.
    let mut failed: Vec<String> = assets
        .requested
        .iter()
        .filter(|(key, _)| !assets.found.contains(key))
        .map(|(_, id)| id.clone())
        .collect();
    failed.sort_by(|a, b| compare_ignoring_case(a, b));
    if !failed.is_empty() {
        let ids: HashSet<String> = failed.iter().map(|id| id.to_lowercase()).collect();
        // About the packages first, then the general: a feed did not answer.
        let own = assets.failures.iter().filter(|f| {
            f.library
                .as_ref()
                .is_some_and(|l| ids.contains(&l.to_lowercase()))
        });
        let general = assets.failures.iter().filter(|f| f.library.is_none());
        let messages = unique_ignoring_case(own.chain(general).map(|f| f.message.clone()));
        out.push(Problem {
            project: project.into(),
            reason: Reason::Failed,
            packages: failed,
            messages: messages.into_iter().take(3).collect(),
        });
    }
    // In the project but unknown to the restore: added after it.
    if assets.describes_project && edited_since_restore {
        let outdated: Vec<String> = explicit_ids(references)
            .into_iter()
            .filter(|id| assets.requested_id(id).is_none())
            .collect();
        if !outdated.is_empty() {
            out.push(Problem {
                project: project.into(),
                reason: Reason::Outdated,
                packages: outdated,
                messages: Vec::new(),
            });
        }
    }
    // Found by the restore, but no folder on disk: the NuGet cache was
    // cleared, or the file came from another machine.
    if !assets.folders.is_empty() {
        let missing: Vec<String> = assets
            .packages
            .iter()
            .filter(|package| {
                !assets
                    .folders
                    .iter()
                    .any(|folder| exists(&Path::new(folder).join(&package.path)))
            })
            .map(|p| p.id.clone())
            .collect();
        if !missing.is_empty() {
            out.push(Problem {
                project: project.into(),
                reason: Reason::Missing,
                packages: unique_ignoring_case(missing),
                messages: Vec::new(),
            });
        }
    }
    out
}

/// References to these the SDK turns into framework references or drops from
/// the restore itself (NETSDK1080 and relatives): they are never in the
/// restore's file.
const FRAMEWORK_PACKAGES: [&str; 5] = [
    "microsoft.netcore.app",
    "microsoft.aspnetcore.app",
    "microsoft.aspnetcore.all",
    "microsoft.windowsdesktop.app",
    "netstandard.library",
];

/// Whether a file changed after another; when that cannot be told, yes.
pub fn is_newer(file: &Path, other: &Path) -> bool {
    let modified = |p: &Path| std::fs::metadata(p).and_then(|m| m.modified()).ok();
    match (modified(file), modified(other)) {
        (Some(a), Some(b)) => a > b,
        _ => true,
    }
}

/// The packages a project always asks for, by name: no conditions, no MSBuild
/// properties (`$(Name)`), none the SDK takes over. `A;B` is two packages.
pub fn explicit_ids(references: &[Reference]) -> Vec<String> {
    let mut ids = Vec::new();
    for reference in references.iter().filter(|r| !r.is_conditional) {
        for part in reference.id.split(';').filter(|p| !p.is_empty()) {
            let id = trim_spaces(part);
            if id.is_empty()
                || ["$(", "@(", "%("].iter().any(|m| id.contains(m))
                || FRAMEWORK_PACKAGES.contains(&id.to_lowercase().as_str())
            {
                continue;
            }
            ids.push(id.to_string());
        }
    }
    unique_ignoring_case(ids)
}

/// A Unity project in the folder: `Assets/` and
/// `ProjectSettings/ProjectVersion.txt`.
fn is_unity_project(directory: &Path) -> bool {
    directory
        .join("ProjectSettings/ProjectVersion.txt")
        .exists()
        && directory.join("Assets").is_dir()
}

/// Whether the project is inside a Unity project: in its folder or above, up
/// to the root.
pub fn is_in_unity_project(path: &str, root: &Path) -> bool {
    let mut components: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
    components.pop();
    loop {
        let directory = if components.is_empty() {
            root.to_path_buf()
        } else {
            root.join(components.join("/"))
        };
        if is_unity_project(&directory) {
            return true;
        }
        if components.pop().is_none() {
            return false;
        }
    }
}

/// Whether the project's `obj/` is moved, in the project itself or in a
/// `Directory.Build.props` above. Where the restore left its file cannot be
/// told from the text, and "never restored" would be untrue.
pub fn moves_intermediate(path: &str, root: &Path) -> bool {
    const PROPERTIES: [&str; 5] = [
        "BaseIntermediateOutputPath",
        "MSBuildProjectExtensionsPath",
        "RestoreOutputPath",
        "UseArtifactsOutput",
        "ArtifactsPath",
    ];
    let moves = |relative: &str| -> bool {
        let Ok(text) = std::fs::read_to_string(root.join(relative)) else {
            return false;
        };
        let lower = text.to_lowercase();
        PROPERTIES
            .iter()
            .any(|p| lower.contains(&format!("<{}", p.to_lowercase())))
    };
    if moves(path) {
        return true;
    }
    let mut components: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
    components.pop();
    loop {
        let mut relative = components.join("/");
        if !relative.is_empty() {
            relative.push('/');
        }
        relative.push_str("Directory.Build.props");
        if moves(&relative) {
            return true;
        }
        if components.pop().is_none() {
            return false;
        }
    }
}

// MARK: project.assets.json

/// What the check needs from `project.assets.json`: which packages the project
/// asked for, which the restore found, where their folders are, and what the
/// restore complained about.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Assets {
    /// The packages the project asked for: lowercased id → as written.
    pub requested: Vec<(String, String)>,
    /// The file describes the project, so `requested` is complete.
    pub describes_project: bool,
    /// What the restore found, packages and projects, ids lowercased.
    pub found: HashSet<String>,
    pub packages: Vec<AssetPackage>,
    /// Package folders: `~/.nuget/packages/` and fallbacks.
    pub folders: Vec<String>,
    /// The restore's errors; warnings do not count.
    pub failures: Vec<AssetFailure>,
}

/// A package a restore resolved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssetPackage {
    pub id: String,
    /// From a package folder: `newtonsoft.json/13.0.3`.
    pub path: String,
}

/// An error a restore logged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssetFailure {
    /// Which package; `None` for the restore as a whole (a feed did not
    /// answer).
    pub library: Option<String>,
    /// `NU1101: Unable to find package …`, on one line.
    pub message: String,
}

impl Assets {
    fn requested_id(&self, id: &str) -> Option<&String> {
        let key = id.to_lowercase();
        self.requested
            .iter()
            .find(|(k, _)| *k == key)
            .map(|(_, v)| v)
    }

    /// `None` when not JSON: the file is being written or is broken.
    pub fn parse(data: &[u8]) -> Option<Assets> {
        let json = Json::parse(data).filter(Json::is_object)?;
        let mut assets = Assets::default();
        if let Some(frameworks) = json.object("project").and_then(|p| p.object("frameworks")) {
            assets.describes_project = true;
            for (_, framework) in frameworks.entries() {
                let Some(dependencies) = framework.object("dependencies") else {
                    continue;
                };
                for (id, spec) in dependencies.entries() {
                    if let Some(target) = spec.str("target")
                        && !target.eq_ignore_ascii_case("Package")
                    {
                        continue;
                    }
                    let key = id.to_lowercase();
                    if !assets.requested.iter().any(|(k, _)| *k == key) {
                        assets.requested.push((key, id.to_string()));
                    }
                }
            }
        }
        if let Some(libraries) = json.object("libraries") {
            for (key, value) in libraries.entries() {
                // `Newtonsoft.Json/13.0.3`.
                let id = key.split('/').next().unwrap_or(key);
                assets.found.insert(id.to_lowercase());
                if value
                    .str("type")
                    .is_some_and(|t| t.eq_ignore_ascii_case("package"))
                    && let Some(path) = value.str("path")
                {
                    assets.packages.push(AssetPackage {
                        id: id.to_string(),
                        path: path.to_string(),
                    });
                }
            }
        }
        // Not in the file's order: a report is compared with the last one.
        assets.packages.sort_by_key(|p| p.id.to_lowercase());
        let mut folders: Vec<String> = json
            .object("packageFolders")
            .map(|f| {
                f.entries()
                    .into_iter()
                    .map(|(k, _)| k.to_string())
                    .collect()
            })
            .unwrap_or_default();
        folders.sort();
        assets.folders = folders;
        for log in json
            .get("logs")
            .and_then(Json::as_array)
            .unwrap_or_default()
        {
            if !log.is_object()
                || !log
                    .str("level")
                    .is_some_and(|l| l.eq_ignore_ascii_case("Error"))
            {
                continue;
            }
            let text: Vec<&str> = log
                .str("message")
                .unwrap_or("")
                .split(is_newline)
                .map(trim_spaces)
                .filter(|l| !l.is_empty())
                .collect();
            let text = text.join(" ");
            let code = log.str("code").unwrap_or("");
            let message = [code, text.as_str()]
                .iter()
                .filter(|s| !s.is_empty())
                .copied()
                .collect::<Vec<_>>()
                .join(": ");
            assets.failures.push(AssetFailure {
                library: log.str("libraryId").map(str::to_owned),
                message,
            });
        }
        Some(assets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nuget::projects::discover;
    use crate::nuget::testing::TempDir;
    use std::time::{Duration, SystemTime};

    fn touch(dir: &TempDir, path: &str, seconds_ago: u64) {
        let file = std::fs::File::options()
            .write(true)
            .open(dir.path().join(path))
            .unwrap();
        file.set_modified(SystemTime::now() - Duration::from_secs(seconds_ago))
            .unwrap();
    }

    fn assets_json(packages: &str) -> String {
        // In JSON a Windows path's `\` is `\\`, as NuGet writes it.
        let packages = packages.replace('\\', "\\\\");
        format!(
            r#"{{
  "version": 3,
  "targets": {{ "net8.0": {{ "Newtonsoft.Json/13.0.3": {{ "type": "package" }}, "Lib/1.0.0": {{ "type": "project" }} }} }},
  "libraries": {{
    "Newtonsoft.Json/13.0.3": {{ "type": "package", "path": "newtonsoft.json/13.0.3" }},
    "Gone.Pkg/1.0.0": {{ "type": "package", "path": "gone.pkg/1.0.0" }},
    "Lib/1.0.0": {{ "type": "project", "path": "../Lib/Lib.csproj" }}
  }},
  "packageFolders": {{ "{packages}/": {{}} }},
  "project": {{ "frameworks": {{ "net8.0": {{ "dependencies": {{
    "Newtonsoft.Json": {{ "target": "Package", "version": "[13.0.3, )" }},
    "Missing.Pkg": {{ "target": "Package", "version": "[1.0.0, )" }},
    "gone.pkg": {{ "target": "Package", "version": "[1.0.0, )" }}
  }} }} }} }},
  "logs": [
    {{ "code": "NU1101", "level": "Error", "libraryId": "Missing.Pkg",
      "message": "Unable to find package Missing.Pkg. No packages exist with this id in source(s): nuget.org" }},
    {{ "code": "NU1301", "level": "Error",
      "message": "Unable to load the service index for source https://feed/index.json.\n  Response status code does not indicate success: 401 (Unauthorized)." }},
    {{ "code": "NU1603", "level": "Warning", "libraryId": "Newtonsoft.Json", "message": "approximate best match" }}
  ]
}}"#
        )
    }

    #[test]
    fn explicit_and_relevant() {
        let mut conditional = Reference::new("c");
        conditional.is_conditional = true;
        let refs = [
            Reference::new("A;B"),
            Reference::new("$(Name)"),
            conditional,
            Reference::new("a"),
            Reference::new("Microsoft.AspNetCore.App"),
        ];
        assert_eq!(
            explicit_ids(&refs),
            ["A", "B"],
            "by name: A;B is two packages; no properties, conditions, repeats, or what the SDK takes"
        );
        assert!(
            is_assets("/p/Server/obj/project.assets.json")
                && is_relevant("/p/Server/Server.csproj")
                && is_relevant("/p/Directory.Packages.props")
                && !is_relevant("/p/Server/Program.cs")
                && !is_assets("/p/Temp/obj/Debug/Game/project.assets.json"),
            "what changed: projects, props, and project.assets.json next to a project"
        );
    }

    #[test]
    fn report_on_disk() {
        let dir = TempDir::new("restore");
        let packages = dir.path().join("packages").to_string_lossy().into_owned();
        dir.mkdir("packages/newtonsoft.json/13.0.3");
        let assets = assets_json(&packages);
        let parsed = Assets::parse(assets.as_bytes()).unwrap();
        let ids: Vec<&str> = parsed.packages.iter().map(|p| p.id.as_str()).collect();
        assert!(
            parsed.requested.len() == 3
                && parsed.found
                    == HashSet::from(["newtonsoft.json".into(), "gone.pkg".into(), "lib".into()])
                && ids == ["Gone.Pkg", "Newtonsoft.Json"]
                && parsed.failures.len() == 2,
            "project.assets.json: asked for, found, package folders, errors without warnings"
        );
        assert!(
            Assets::parse(b"{\"version\": 3, \"libr").is_none(),
            "a file half written is None"
        );

        let server = r#"<Project Sdk="Microsoft.NET.Sdk">
  <ItemGroup>
    <PackageReference Include="Newtonsoft.Json" Version="13.0.3" />
    <PackageReference Include="Missing.Pkg" Version="1.0.0" />
    <PackageReference Include="Gone.Pkg" Version="1.0.0" />
    <PackageReference Include="New.Pkg" Version="2.0.0" />
    <PackageReference Include="Windows.Only" Version="1.0.0" Condition="'$(OS)' == 'Windows_NT'" />
    <PackageReference Include="Microsoft.AspNetCore.App" />
  </ItemGroup>
</Project>"#;
        let sdk = |id: &str| {
            format!(
                "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup><PackageReference Include=\"{id}\" Version=\"1.0.0\" /></ItemGroup></Project>"
            )
        };
        dir.put("Server/Server.csproj", server);
        dir.put("Server/obj/project.assets.json", &assets);
        // The .csproj was edited after the restore.
        touch(&dir, "Server/obj/project.assets.json", 60);
        dir.put("Server.Tests/Server.Tests.csproj", &sdk("xunit"));
        dir.put(
            "Plain/Plain.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\"></Project>",
        );
        // obj/ moved: where the restore left its file is unknown.
        dir.put("Artifacts/Tool/Tool.csproj", &sdk("Tool.Pkg"));
        dir.put("Artifacts/Directory.Build.props", "<Project><PropertyGroup><UseArtifactsOutput>true</UseArtifactsOutput></PropertyGroup></Project>");
        // A generator inside a Unity project: not restored here, and no reason.
        dir.put(
            "Client/ProjectSettings/ProjectVersion.txt",
            "m_EditorVersion: 6000.0.1f1\n",
        );
        dir.mkdir("Client/Assets");
        dir.put(
            "Client/Generators/Generators.csproj",
            &sdk("Microsoft.CodeAnalysis.CSharp"),
        );

        let run = || check(dir.path(), &discover(dir.path()));
        let shape = |report: &Report| -> Vec<String> {
            report
                .problems
                .iter()
                .map(|p| format!("{} {:?} {}", p.project, p.reason, p.packages.join(",")))
                .collect()
        };
        let report = run();
        assert!(
            report.project_count == 5 && report.has_projects() && report.restored_somewhere,
            "projects counted ({})",
            report.project_count
        );
        assert_eq!(
            shape(&report),
            [
                "Server/Server.csproj Failed Missing.Pkg",
                "Server/Server.csproj Missing Gone.Pkg",
                "Server/Server.csproj Outdated New.Pkg",
                "Server.Tests/Server.Tests.csproj NotRestored xunit"
            ],
            "not found, gone from disk, added after the restore, never restored; Unity and artifacts do not count"
        );
        assert_eq!(
            report.problems[0].messages,
            [
                "NU1101: Unable to find package Missing.Pkg. No packages exist with this id in source(s): nuget.org",
                "NU1301: Unable to load the service index for source https://feed/index.json. Response status code does not indicate success: 401 (Unauthorized).",
            ],
            "what the restore said: about the package, then the feed, on one line"
        );
        assert!(
            report.needs_attention()
                && report.projects()
                    == ["Server/Server.csproj", "Server.Tests/Server.Tests.csproj"],
            "worth telling; restore first where it failed"
        );
        assert_eq!(
            report.packages(),
            ["Missing.Pkg", "Gone.Pkg", "New.Pkg", "xunit"]
        );
        assert_eq!(report.names(Reason::Failed), ["Server"]);
        assert_eq!(
            report.packages_of("Server/Server.csproj"),
            ["Missing.Pkg", "Gone.Pkg", "New.Pkg"]
        );
        assert_eq!(report.messages().len(), 2);

        // The restore saw exactly this .csproj: a reference missing from its file
        // was dropped by the SDK or Directory.Build.targets, not added after.
        touch(&dir, "Server/Server.csproj", 120);
        let seen: Vec<Reason> = run().problems.iter().map(|p| p.reason).collect();
        assert_eq!(
            seen,
            [Reason::Failed, Reason::Missing, Reason::NotRestored],
            ".csproj older than the restore: references are not outdated"
        );

        // The built project is fine and the tests next to it were never restored:
        // they are not built here. A package found as a project is found too.
        dir.put(
            "Server/obj/project.assets.json",
            &format!(
                r#"{{ "libraries": {{ "Newtonsoft.Json/13.0.3": {{ "type": "package", "path": "newtonsoft.json/13.0.3" }},
                     "Gone.Pkg/1.0.0": {{ "type": "package", "path": "gone.pkg/1.0.0" }},
                     "New.Pkg/2.0.0": {{ "type": "package", "path": "new.pkg/2.0.0" }},
                     "Missing.Pkg/1.0.0": {{ "type": "project", "path": "../Missing/Missing.csproj" }} }},
      "packageFolders": {{ "{packages}/": {{}} }},
      "project": {{ "frameworks": {{ "net8.0": {{ "dependencies": {{
        "Newtonsoft.Json": {{ "target": "Package" }}, "Missing.Pkg": {{ "target": "Package" }},
        "Gone.Pkg": {{ "target": "Package" }}, "New.Pkg": {{ "target": "Package" }} }} }} }} }} }}"#
            ),
        );
        dir.mkdir("packages/gone.pkg/1.0.0");
        dir.mkdir("packages/new.pkg/2.0.0");
        let quiet = run();
        assert!(
            quiet.problems.iter().map(|p| p.reason).collect::<Vec<_>>() == [Reason::NotRestored]
                && !quiet.needs_attention(),
            "only unrestored tests left: no reason"
        );
        std::fs::remove_dir_all(dir.path().join("Server/obj")).unwrap();
        let fresh = run();
        assert!(
            fresh.problems.len() == 2
                && fresh
                    .problems
                    .iter()
                    .all(|p| p.reason == Reason::NotRestored)
                && !fresh.restored_somewhere
                && fresh.needs_attention(),
            "never restored anywhere, a fresh clone: a reason"
        );
        dir.put("Server/obj/project.assets.json", "{\"version\": 3, \"libr");
        let writing = run();
        assert!(
            writing
                .problems
                .iter()
                .map(|p| p.project.as_str())
                .collect::<Vec<_>>()
                == ["Server.Tests/Server.Tests.csproj"]
                && !writing.needs_attention(),
            "the file is being written: the project is skipped, but it was restored"
        );
    }
}
