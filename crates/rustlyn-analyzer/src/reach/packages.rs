//! Unity packages: which ones a project has, which files belong to which,
//! and which a change touched.
//!
//! An update of `com.unity.purchasing` can change how an SDK behaves, and an
//! update of a mesh tool cannot, so a change to the package files is judged
//! per package ([`super::judge::packages`]) and not as one watched file.
//! The project's packages come from `Packages/manifest.json` (what the
//! project asked for) and `Packages/packages-lock.json` (what it got, and
//! what each package depends on). Either may be missing.

use std::collections::{BTreeMap, BTreeSet};

use rustlyn_ide::formats::json::Json;

use crate::blast::diff::{FileDiff, Status};

/// What the project asked for.
pub const MANIFEST: &str = "Packages/manifest.json";
/// What the project got.
pub const LOCK: &str = "Packages/packages-lock.json";

/// A package as one of the two files lists it: what a change to it is
/// noticed by.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Listed {
    pub version: String,
    pub hash: Option<String>,
}

/// A package as the lock describes it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Locked {
    version: String,
    source: String,
    dependencies: Vec<String>,
}

/// The packages of a project.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Packages {
    manifest: BTreeSet<String>,
    locked: BTreeMap<String, Locked>,
    /// Folders of packages that live inside the project, relative to the
    /// root, with the package's name.
    folders: Vec<(String, String)>,
}

impl Packages {
    /// The packages of the project in `root`, as the files on disk list
    /// them. A file that is missing or not JSON lists none.
    #[must_use]
    pub fn read(root: &str) -> Self {
        let read = |path: &str| std::fs::read_to_string(std::path::Path::new(root).join(path)).ok();
        Self::parse(read(MANIFEST).as_deref(), read(LOCK).as_deref())
    }

    /// The packages the texts of the two files list.
    #[must_use]
    pub fn parse(manifest: Option<&str>, lock: Option<&str>) -> Self {
        let mut packages = Self::default();
        if let Some(listing) = manifest.and_then(listing) {
            packages.manifest = listing.into_keys().collect();
        }
        let json = lock.and_then(|text| Json::parse(text.as_bytes()));
        for (name, value) in json
            .as_ref()
            .and_then(|json| json.object("dependencies"))
            .map(Json::entries)
            .unwrap_or_default()
        {
            let version = value.str("version").unwrap_or_default().to_owned();
            let source = value.str("source").unwrap_or_default().to_owned();
            let dependencies = value
                .object("dependencies")
                .map(|deps| {
                    deps.entries()
                        .into_iter()
                        .map(|(n, _)| n.to_owned())
                        .collect()
                })
                .unwrap_or_default();
            if let Some(folder) = folder_of(&source, &version) {
                packages.folders.push((folder, name.to_owned()));
            }
            packages.locked.insert(
                name.to_owned(),
                Locked {
                    version,
                    source,
                    dependencies,
                },
            );
        }
        packages
    }

    /// Every package either file names, sorted.
    #[must_use]
    pub fn names(&self) -> BTreeSet<String> {
        self.manifest
            .iter()
            .chain(self.locked.keys())
            .cloned()
            .collect()
    }

    /// The source the lock gives a package (`registry`, `embedded`, `git`…).
    #[must_use]
    pub fn source_of(&self, name: &str) -> Option<&str> {
        self.locked
            .get(name)
            .map(|locked| locked.source.as_str())
            .filter(|source| !source.is_empty())
    }

    /// The package a file belongs to, by its path relative to the root: the
    /// editor's copy of a registry package, or the folder of one that lives
    /// in the project. A file outside every package has none.
    #[must_use]
    pub fn package_of(&self, path: &str) -> Option<String> {
        if let Some(rest) = path.strip_prefix("Library/PackageCache/") {
            let folder = rest.split('/').next().unwrap_or_default();
            return folder
                .split_once('@')
                .map(|(name, _)| name)
                .filter(|name| !name.is_empty())
                .map(str::to_owned);
        }
        self.folders
            .iter()
            .filter(|(folder, _)| {
                path.strip_prefix(folder.as_str())
                    .is_some_and(|rest| rest.is_empty() || rest.starts_with('/'))
            })
            .max_by_key(|(folder, _)| folder.len())
            .map(|(_, name)| name.clone())
    }

    /// What `name` depends on, directly or not, by the lock.
    #[must_use]
    pub fn depends_on(&self, name: &str) -> BTreeSet<String> {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut todo = vec![name.to_owned()];
        while let Some(next) = todo.pop() {
            for dependency in self
                .locked
                .get(&next)
                .map_or(&[][..], |locked| &locked.dependencies)
            {
                if dependency != name && seen.insert(dependency.clone()) {
                    todo.push(dependency.clone());
                }
            }
        }
        seen
    }

    /// What depends on `name`, directly or not, by the lock.
    #[must_use]
    pub fn dependents_of(&self, name: &str) -> BTreeSet<String> {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut todo = vec![name.to_owned()];
        while let Some(next) = todo.pop() {
            for (other, locked) in &self.locked {
                if other != name
                    && locked.dependencies.contains(&next)
                    && seen.insert(other.clone())
                {
                    todo.push(other.clone());
                }
            }
        }
        seen
    }
}

/// The folder of a package that lives in the project, relative to the root,
/// from the lock's `source` and `version`: an embedded package is
/// `file:<folder under Packages>`, a local one `file:<path relative to
/// Packages>`.
fn folder_of(source: &str, version: &str) -> Option<String> {
    let target = version.strip_prefix("file:")?;
    match source {
        "embedded" | "local" => {
            let joined = format!("Packages/{target}");
            let mut parts: Vec<&str> = Vec::new();
            for part in joined.split('/') {
                match part {
                    "" | "." => {}
                    ".." => {
                        parts.pop()?;
                    }
                    other => parts.push(other),
                }
            }
            (!parts.is_empty()).then(|| parts.join("/"))
        }
        _ => None,
    }
}

/// The packages a manifest or a lock lists, with what a change shows in
/// them. `None` when the text is not JSON; an empty text lists none.
#[must_use]
pub fn listing(text: &str) -> Option<BTreeMap<String, Listed>> {
    if text.trim().is_empty() {
        return Some(BTreeMap::new());
    }
    let json = Json::parse(text.as_bytes())?;
    let mut listed = BTreeMap::new();
    for (name, value) in json
        .object("dependencies")
        .map(Json::entries)
        .unwrap_or_default()
    {
        let entry = match value.as_str() {
            Some(version) => Listed {
                version: version.to_owned(),
                hash: None,
            },
            None => Listed {
                version: value.str("version").unwrap_or_default().to_owned(),
                hash: value.str("hash").map(str::to_owned),
            },
        };
        listed.insert(name.to_owned(), entry);
    }
    Some(listed)
}

/// The names added, removed or changed between two listings, each once.
#[must_use]
pub fn changed(old: &BTreeMap<String, Listed>, new: &BTreeMap<String, Listed>) -> Vec<String> {
    let mut names: BTreeSet<&String> = BTreeSet::new();
    for (name, entry) in new {
        if old.get(name) != Some(entry) {
            names.insert(name);
        }
    }
    for name in old.keys() {
        if !new.contains_key(name) {
            names.insert(name);
        }
    }
    names.into_iter().cloned().collect()
}

/// The line (from zero) where `name` is listed in a manifest or a lock. A
/// lock names a package in the lists of dependencies too: its own entry,
/// which opens an object, is preferred.
#[must_use]
pub fn line_of(text: &str, name: &str) -> Option<usize> {
    let key = format!("\"{name}\"");
    let mut first = None;
    for (index, line) in text.lines().enumerate() {
        let Some(rest) = line.trim_start().strip_prefix(key.as_str()) else {
            continue;
        };
        let Some(rest) = rest.trim_start().strip_prefix(':') else {
            continue;
        };
        if rest.trim() == "{" {
            return Some(index);
        }
        first.get_or_insert(index);
    }
    first
}

/// A package that a change touched, and where its entry is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Changed {
    pub name: String,
    /// The file that lists the change: the manifest, else the lock.
    pub path: String,
    /// The line of the package in the new text of that file, from zero.
    pub line: usize,
}

/// What a change did to the project's packages.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Changes {
    pub packages: Vec<Changed>,
    /// Package files that changed and cannot be read as JSON, before or
    /// after: nothing can be said of them by package.
    pub broken: Vec<String>,
}

impl Changes {
    /// Whether neither package file changed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.packages.is_empty() && self.broken.is_empty()
    }
}

/// The packages the changed files of a patch added, removed or changed.
/// `text_of(path)` is a file's text after the change; the text before is
/// put back from the patch.
#[must_use]
pub fn changes(files: &[FileDiff], text_of: &dyn Fn(&str) -> Option<String>) -> Changes {
    let mut out = Changes::default();
    for path in [MANIFEST, LOCK] {
        let Some(file) = files.iter().find(|file| file.path == path) else {
            continue;
        };
        let new = if file.status == Status::Deleted {
            Some(String::new())
        } else {
            text_of(path)
        };
        let Some(new) = new else {
            out.broken.push(path.to_owned());
            continue;
        };
        let old = file.old_text(&new);
        let (Some(before), Some(after)) = (listing(&old), listing(&new)) else {
            out.broken.push(path.to_owned());
            continue;
        };
        for name in changed(&before, &after) {
            if out.packages.iter().any(|known| known.name == name) {
                continue;
            }
            out.packages.push(Changed {
                line: line_of(&new, &name).unwrap_or(0),
                name,
                path: path.to_owned(),
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::diff::between;

    const LOCK_TEXT: &str = r#"{
  "dependencies": {
    "com.vendor.ads": {
      "version": "file:com.vendor.ads",
      "depth": 0,
      "source": "embedded",
      "dependencies": { "com.vendor.core": "1.0.0" }
    },
    "com.vendor.core": { "version": "1.0.0", "depth": 1, "source": "registry", "hash": "aa", "dependencies": {} },
    "com.vendor.wrap": {
      "version": "2.0.0",
      "depth": 0,
      "source": "registry",
      "dependencies": { "com.vendor.ads": "1.0.0" }
    },
    "com.vendor.local": { "version": "file:../CustomPackages/local", "depth": 0, "source": "local", "dependencies": {} },
    "com.vendor.top": { "version": "1.0.0", "depth": 0, "source": "registry", "dependencies": { "com.vendor.wrap": "2.0.0" } }
  }
}"#;

    #[test]
    fn files_belong_to_packages() {
        let packages = Packages::parse(None, Some(LOCK_TEXT));
        let of = |path: &str| packages.package_of(path);
        assert_eq!(
            of("Packages/com.vendor.ads/Runtime/A.cs").as_deref(),
            Some("com.vendor.ads")
        );
        assert_eq!(
            of("CustomPackages/local/B.cs").as_deref(),
            Some("com.vendor.local")
        );
        assert_eq!(
            of("Library/PackageCache/com.unity.purchasing@4.9.3/Runtime/C.dll").as_deref(),
            Some("com.unity.purchasing")
        );
        // The folder's name must match whole.
        assert_eq!(of("Packages/com.vendor.ads2/D.cs"), None);
        assert_eq!(of("Library/PackageCache/nothing/E.cs"), None);
        assert_eq!(of("Assets/Game/F.cs"), None);
        assert_eq!(packages.source_of("com.vendor.core"), Some("registry"));
    }

    #[test]
    fn folders_of_local_packages() {
        assert_eq!(
            folder_of("embedded", "file:com.x").as_deref(),
            Some("Packages/com.x")
        );
        assert_eq!(
            folder_of("local", "file:../CustomPackages/x").as_deref(),
            Some("CustomPackages/x")
        );
        assert_eq!(folder_of("local", "file:../../../x"), None);
        assert_eq!(folder_of("registry", "1.0.0"), None);
        assert_eq!(folder_of("embedded", "1.0.0"), None);
    }

    #[test]
    fn dependencies_both_ways() {
        let packages = Packages::parse(None, Some(LOCK_TEXT));
        let list = |set: BTreeSet<String>| set.into_iter().collect::<Vec<_>>();
        assert_eq!(
            list(packages.depends_on("com.vendor.top")),
            ["com.vendor.ads", "com.vendor.core", "com.vendor.wrap"]
        );
        assert_eq!(
            list(packages.dependents_of("com.vendor.core")),
            ["com.vendor.ads", "com.vendor.top", "com.vendor.wrap"]
        );
        assert!(packages.depends_on("com.vendor.core").is_empty());
    }

    #[test]
    fn changed_names() {
        let old = listing(r#"{"dependencies": {"a": "1.0", "b": "1.0", "c": "1.0"}}"#).unwrap();
        let new = listing(r#"{"dependencies": {"a": "1.0", "b": "2.0", "d": "1.0"}}"#).unwrap();
        assert_eq!(changed(&old, &new), ["b", "c", "d"]);
        // A lock's hash alone is a change.
        let old = listing(r#"{"dependencies": {"a": {"version": "1", "hash": "x"}}}"#).unwrap();
        let new = listing(r#"{"dependencies": {"a": {"version": "1", "hash": "y"}}}"#).unwrap();
        assert_eq!(changed(&old, &new), ["a"]);
        assert_eq!(listing("").unwrap().len(), 0);
        assert!(listing("{broken").is_none());
    }

    #[test]
    fn a_patch_names_the_packages_it_changed() {
        let old = "{\n  \"dependencies\": {\n    \"com.a\": \"1.0.0\",\n    \"com.b\": \"1.0.0\"\n  }\n}\n";
        let new = old.replace("com.b\": \"1.0.0", "com.b\": \"1.1.0");
        let lock_old = "{\n  \"dependencies\": {\n    \"com.b\": {\n      \"version\": \"1.0.0\"\n    }\n  }\n}\n";
        let lock_new = lock_old.replace("\"1.0.0\"", "\"1.1.0\"");
        let files = vec![
            between(MANIFEST, old, &new),
            between(LOCK, lock_old, &lock_new),
        ];
        let texts = |path: &str| match path {
            MANIFEST => Some(new.clone()),
            LOCK => Some(lock_new.clone()),
            _ => None,
        };
        let found = changes(&files, &texts);
        assert!(found.broken.is_empty());
        // Once, by the manifest, at its line.
        assert_eq!(
            found.packages,
            [Changed {
                name: "com.b".into(),
                path: MANIFEST.into(),
                line: 3
            }]
        );
        // A text that is not JSON is reported, not skipped.
        let broken = changes(&files, &|_| Some("{ nope".to_owned()));
        assert_eq!(broken.broken, [MANIFEST, LOCK]);
    }

    #[test]
    fn lines_of_packages() {
        assert_eq!(line_of(LOCK_TEXT, "com.vendor.core"), Some(8));
        // Its own entry, which opens an object.
        assert_eq!(line_of(LOCK_TEXT, "com.vendor.wrap"), Some(9));
        assert_eq!(line_of(LOCK_TEXT, "com.missing"), None);
    }
}
