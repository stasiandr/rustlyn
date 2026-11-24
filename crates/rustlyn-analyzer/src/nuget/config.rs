//! `NuGet.Config`: where `dotnet` takes package feeds and their passwords
//! from.
//!
//! All the files apply at once: the user's `~/.nuget/NuGet/NuGet.Config` and
//! a `nuget.config` in each folder from the root of the disk down to the
//! project. One nearer the project overrides one further away; `<clear />`
//! drops the feeds of the further ones.
//!
//! Edits are meant for the user's file: a password in a repository's file
//! would end up in git. A feed declared in the repository still works, since
//! NuGet looks credentials up by the feed's name in every file.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rustlyn_ide::formats::xml::{Document, Element, Node};

use super::url;

/// A package feed from `NuGet.Config`: the one `dotnet restore` and the IDEs
/// use.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Source {
    pub name: String,
    /// The address of a v3 feed's `index.json`, or a folder of packages.
    pub url: String,
    pub is_enabled: bool,
    pub username: Option<String>,
    /// `ClearTextPassword` only: NuGet can decrypt `Password` on Windows
    /// only.
    pub password: Option<String>,
    /// The file the feed is declared in.
    pub config_file: Option<String>,
}

impl Source {
    pub fn new(name: &str, url: &str) -> Self {
        Source {
            name: name.into(),
            url: url.into(),
            is_enabled: true,
            username: None,
            password: None,
            config_file: None,
        }
    }

    pub fn id(&self) -> String {
        self.name.to_lowercase()
    }

    pub fn has_credentials(&self) -> bool {
        self.username.as_deref().is_some_and(|u| !u.is_empty())
            && self.password.as_deref().is_some_and(|p| !p.is_empty())
    }

    pub fn is_nuget_org(&self) -> bool {
        is_nuget_org(&self.url)
    }

    /// A feed over http(s) rather than a folder on disk.
    pub fn is_remote(&self) -> bool {
        is_remote(&self.url)
    }
}

pub fn is_nuget_org(url: &str) -> bool {
    url::host(url).is_some_and(|h| h.to_lowercase() == "api.nuget.org")
}

pub fn is_remote(url: &str) -> bool {
    let lower = url.to_lowercase();
    lower.starts_with("http://") || lower.starts_with("https://")
}

/// `~/.nuget/NuGet/NuGet.Config`.
pub fn user_file() -> PathBuf {
    let home = std::env::var_os("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/"));
    home.join(".nuget/NuGet/NuGet.Config")
}

/// A path without `.` and `..`, resolved lexically.
fn standardized(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

/// The files from the furthest to the nearest: the user's, then folders from
/// the root of the disk down to `root`.
pub fn files(root: Option<&Path>, user: &Path) -> Vec<PathBuf> {
    let mut chain = Vec::new();
    let mut directory = root.map(standardized);
    while let Some(current) = directory {
        if let Ok(entries) = std::fs::read_dir(&current) {
            let mut names: Vec<String> = entries
                .filter_map(|e| e.ok()?.file_name().into_string().ok())
                .collect();
            names.sort();
            if let Some(name) = names
                .into_iter()
                .find(|n| n.to_lowercase() == "nuget.config")
            {
                chain.push(current.join(name));
            }
        }
        directory = current.parent().map(Path::to_path_buf);
    }
    let user_path = standardized(user);
    let local = chain
        .into_iter()
        .rev()
        .filter(|f| standardized(f) != user_path);
    let mut out: Vec<PathBuf> = if user.exists() {
        vec![user.to_path_buf()]
    } else {
        Vec::new()
    };
    out.extend(local);
    out
}

/// The feeds `dotnet restore` sees in `root`.
pub fn sources(root: Option<&Path>, user: &Path) -> Vec<Source> {
    let read: Vec<(String, Vec<u8>)> = files(root, user)
        .into_iter()
        .filter_map(|file| {
            std::fs::read(&file)
                .ok()
                .map(|data| (file.to_string_lossy().into_owned(), data))
        })
        .collect();
    merged(
        &read
            .iter()
            .map(|(f, d)| (f.as_str(), d.as_slice()))
            .collect::<Vec<_>>(),
    )
}

/// The files from the furthest to the nearest.
pub fn merged(files: &[(&str, &[u8])]) -> Vec<Source> {
    let mut sources: Vec<Source> = Vec::new();
    let mut credentials: HashMap<String, (Option<String>, Option<String>)> = HashMap::new();
    let mut disabled: HashMap<String, bool> = HashMap::new();
    for (file, data) in files {
        let Some(document) = Document::parse(data) else {
            continue;
        };
        let root = &document.root;
        for section in root.elements_named("packageSources") {
            for element in section.elements() {
                match element.name.as_str() {
                    "clear" => sources.clear(),
                    "add" => {
                        let (Some(key), Some(value)) =
                            (element.attribute("key"), element.attribute("value"))
                        else {
                            continue;
                        };
                        let mut source = Source::new(key, value);
                        source.config_file = Some(file.to_string());
                        if let Some(existing) = sources.iter_mut().find(|s| s.id() == source.id()) {
                            *existing = source;
                        } else {
                            sources.push(source);
                        }
                    }
                    "remove" => {
                        if let Some(key) = element.attribute("key") {
                            let key = key.to_lowercase();
                            sources.retain(|s| s.id() != key);
                        }
                    }
                    _ => {}
                }
            }
        }
        for section in root.elements_named("packageSourceCredentials") {
            for element in section.elements() {
                let values = settings(element);
                credentials.insert(
                    decode_name(&element.name).to_lowercase(),
                    (
                        values.get("username").cloned(),
                        values.get("cleartextpassword").cloned(),
                    ),
                );
            }
        }
        for section in root.elements_named("disabledPackageSources") {
            for element in section.elements() {
                if element.name == "clear" {
                    disabled.clear();
                    continue;
                }
                let Some(key) = element.attribute("key").filter(|_| element.name == "add") else {
                    continue;
                };
                disabled.insert(
                    key.to_lowercase(),
                    element
                        .attribute("value")
                        .is_some_and(|v| v.to_lowercase() == "true"),
                );
            }
        }
    }
    sources
        .into_iter()
        .map(|mut source| {
            source.is_enabled = disabled.get(&source.id()) != Some(&true);
            if let Some((username, password)) = credentials.get(&source.id()) {
                source.username = username.clone();
                source.password = password.clone();
            }
            source
        })
        .collect()
}

/// The `<add key="…" value="…" />` inside an element, keys lowercased.
fn settings(element: &Element) -> HashMap<String, String> {
    element
        .elements_named("add")
        .filter_map(|item| {
            Some((
                item.attribute("key")?.to_lowercase(),
                item.attribute("value")?.to_string(),
            ))
        })
        .collect()
}

// MARK: editing

/// The file is there but is not a `NuGet.Config`: not XML, or a root other
/// than `configuration`. Such a file is not rewritten.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unreadable;

/// A feed's user name and password.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Credentials {
    pub username: String,
    pub password: String,
}

/// Adds a feed or changes its address. `credentials`: `None` leaves the
/// password alone, an empty user name removes it. `url` `None`: the password
/// only, the feed itself being declared in another file.
pub fn upserting(
    name: &str,
    url: Option<&str>,
    credentials: Option<&Credentials>,
    data: Option<&[u8]>,
) -> Result<Vec<u8>, Unreadable> {
    let mut document = document(data)?;
    let root = &mut document.root;
    if let Some(url) = url {
        let sources = section(root, "packageSources");
        if let Some(index) = entry(sources, name) {
            sources
                .element_at(index)
                .set_existing_attribute("value", url);
        } else {
            let mut add = Element::new("add")
                .with_attribute("key", name)
                .with_attribute("value", url);
            if url.to_lowercase().ends_with("index.json") {
                add = add.with_attribute("protocolVersion", "3");
            }
            sources.push(add);
        }
    }
    if let Some(credentials) = credentials {
        let lower = name.to_lowercase();
        let section_index = section_index(root, "packageSourceCredentials");
        let section = root.element_at(section_index);
        section.remove_elements(|e| decode_name(&e.name).to_lowercase() == lower);
        if !credentials.username.is_empty() {
            let mut element = Element::new(&encode_name(name));
            for (key, value) in [
                ("Username", &credentials.username),
                ("ClearTextPassword", &credentials.password),
            ] {
                element.push(
                    Element::new("add")
                        .with_attribute("key", key)
                        .with_attribute("value", value),
                );
            }
            section.push(element);
        }
        if section.children.is_empty() {
            root.children.remove(section_index);
        }
    }
    Ok(document.to_text().into_bytes())
}

/// Removes a feed with its password and its disabled mark.
pub fn removing(name: &str, data: &[u8]) -> Result<Vec<u8>, Unreadable> {
    let mut document = document(Some(data))?;
    let lower = name.to_lowercase();
    for node in document.root.children.iter_mut() {
        let Node::Element(section) = node else {
            continue;
        };
        match section.name.as_str() {
            "packageSources" | "disabledPackageSources" => remove_entry(section, name),
            "packageSourceCredentials" => {
                section.remove_elements(|e| decode_name(&e.name).to_lowercase() == lower)
            }
            _ => {}
        }
    }
    Ok(document.to_text().into_bytes())
}

/// A disabled feed stays listed, but `dotnet` does not ask it.
pub fn setting_enabled(
    enabled: bool,
    name: &str,
    data: Option<&[u8]>,
) -> Result<Vec<u8>, Unreadable> {
    let mut document = document(data)?;
    let root = &mut document.root;
    let index = section_index(root, "disabledPackageSources");
    let section = root.element_at(index);
    remove_entry(section, name);
    if !enabled {
        section.push(
            Element::new("add")
                .with_attribute("key", name)
                .with_attribute("value", "true"),
        );
    }
    if section.children.is_empty() {
        root.children.remove(index);
    }
    Ok(document.to_text().into_bytes())
}

fn document(data: Option<&[u8]>) -> Result<Document, Unreadable> {
    match data {
        Some(data) if !data.is_empty() => Document::parse(data)
            .filter(|d| d.root.name == "configuration")
            .ok_or(Unreadable),
        _ => Ok(Document::new("configuration")),
    }
}

/// A section's index among the root's children, added at the end when
/// missing.
fn section_index(root: &mut Element, name: &str) -> usize {
    if let Some(index) = root.position(|e| e.name == name) {
        return index;
    }
    root.push(Element::new(name));
    root.children.len() - 1
}

fn section<'a>(root: &'a mut Element, name: &str) -> &'a mut Element {
    let index = section_index(root, name);
    root.element_at(index)
}

/// The first `<add key=…>` with this name, case ignored.
fn entry(section: &Element, key: &str) -> Option<usize> {
    let key = key.to_lowercase();
    section.position(|e| {
        e.name == "add" && e.attribute("key").is_some_and(|k| k.to_lowercase() == key)
    })
}

fn remove_entry(section: &mut Element, key: &str) {
    if let Some(index) = entry(section, key) {
        section.children.remove(index);
    }
}

// MARK: element names

/// A feed's name as an XML element name in `packageSourceCredentials`: NuGet
/// writes a space and anything else not allowed as `_x0020_` (XmlConvert).
pub fn encode_name(name: &str) -> String {
    let mut result = String::new();
    for (index, c) in name.chars().enumerate() {
        let allowed = c.is_alphabetic()
            || c == '_'
            || (index > 0 && (c.is_numeric() || c == '-' || c == '.'));
        if allowed {
            result.push(c);
        } else {
            result.push_str(&format!("_x{:04X}_", c as u32));
        }
    }
    result
}

pub fn decode_name(name: &str) -> String {
    if !name.contains("_x") {
        return name.to_string();
    }
    let mut result = String::new();
    let mut rest = name;
    while let Some(at) = rest.find("_x") {
        result.push_str(&rest[..at]);
        let after = &rest[at + 2..];
        let code: Vec<char> = after.chars().take(5).collect();
        if code.len() == 5
            && code[4] == '_'
            && let Ok(value) = u32::from_str_radix(&code[..4].iter().collect::<String>(), 16)
            && let Some(c) = char::from_u32(value)
        {
            result.push(c);
            rest = &after[code.iter().map(|c| c.len_utf8()).sum::<usize>()..];
        } else {
            result.push_str("_x");
            rest = after;
        }
    }
    result.push_str(rest);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nuget::testing::TempDir;

    const USER: &str = r#"<?xml version="1.0" encoding="utf-8"?>
<configuration>
  <packageSources>
    <add key="nuget.org" value="https://api.nuget.org/v3/index.json" protocolVersion="3" />
    <add key="Old" value="https://old.example.com/index.json" />
  </packageSources>
  <packageSourceCredentials>
    <Company_x0020_Feed>
      <add key="Username" value="u.user" />
      <add key="ClearTextPassword" value="secret" />
    </Company_x0020_Feed>
  </packageSourceCredentials>
  <disabledPackageSources>
    <add key="nuget.org" value="true" />
  </disabledPackageSources>
</configuration>"#;

    const REPO: &str = r#"<configuration>
  <packageSources>
    <clear />
    <add key="nuget.org" value="https://api.nuget.org/v3/index.json" />
    <add key="Company Feed" value="https://git.example.com/api/v4/projects/1/packages/nuget/index.json" />
  </packageSources>
  <disabledPackageSources>
    <add key="nuget.org" value="false" />
  </disabledPackageSources>
</configuration>"#;

    const USER_FILE: &str = "/u/NuGet.Config";
    const REPO_FILE: &str = "/r/nuget.config";

    fn names(sources: &[Source]) -> Vec<&str> {
        sources.iter().map(|s| s.name.as_str()).collect()
    }

    #[test]
    fn merging_files() {
        let merged = merged(&[(USER_FILE, USER.as_bytes()), (REPO_FILE, REPO.as_bytes())]);
        assert_eq!(
            names(&merged),
            ["nuget.org", "Company Feed"],
            "<clear /> in a nearer file drops a further one's feeds"
        );
        let last = merged.last().unwrap();
        assert!(
            last.username.as_deref() == Some("u.user")
                && last.password.as_deref() == Some("secret")
                && last.config_file.as_deref() == Some(REPO_FILE),
            "a password from the user's file finds the repository's feed by name (_x0020_ is a space)"
        );
        assert!(
            merged[0].is_enabled && merged[0].is_nuget_org(),
            "a nearer file enables a disabled feed again"
        );
        assert!(
            !super::merged(&[(USER_FILE, USER.as_bytes())])[0].is_enabled,
            "disabledPackageSources disables"
        );
        assert!(
            super::merged(&[(USER_FILE, b"broken")]).is_empty(),
            "a broken file is skipped"
        );
    }

    #[test]
    fn names_like_xml_convert() {
        assert!(
            encode_name("Company Feed") == "Company_x0020_Feed"
                && encode_name("1feed") == "_x0031_feed"
                && decode_name("Company_x0020_Feed") == "Company Feed"
                && decode_name("a_xZZ_b") == "a_xZZ_b",
            "feed names in XML, like XmlConvert"
        );
    }

    #[test]
    fn editing() {
        let creds = |u: &str, p: &str| Credentials {
            username: u.into(),
            password: p.into(),
        };
        let added = upserting(
            "Company Feed",
            Some("https://git.example.com/index.json"),
            Some(&creds("u.user", "tok")),
            None,
        )
        .unwrap();
        let reread = merged(&[(USER_FILE, &added)]);
        assert!(
            reread.len() == 1
                && reread[0].url == "https://git.example.com/index.json"
                && reread[0].password.as_deref() == Some("tok"),
            "a new file: a feed with a user name and token"
        );
        assert!(String::from_utf8_lossy(&added).contains("protocolVersion=\"3\""));
        let only_password = upserting(
            "company feed",
            None,
            Some(&creds("u2", "tok2")),
            Some(USER.as_bytes()),
        )
        .unwrap();
        let both = merged(&[(USER_FILE, &only_password), (REPO_FILE, REPO.as_bytes())]);
        assert!(
            both.last().unwrap().username.as_deref() == Some("u2")
                && both.last().unwrap().password.as_deref() == Some("tok2")
                && merged(&[(USER_FILE, &only_password)]).len() == 2,
            "the password only: the old one replaced, no feed added"
        );
        let cleared = upserting(
            "company feed",
            None,
            Some(&creds("", "")),
            Some(&only_password),
        )
        .unwrap();
        assert!(
            !String::from_utf8_lossy(&cleared).contains("packageSourceCredentials"),
            "an empty user name removes the password and the empty section"
        );
        let moved = upserting(
            "OLD",
            Some("https://new.example.com/index.json"),
            None,
            Some(USER.as_bytes()),
        )
        .unwrap();
        assert_eq!(
            merged(&[(USER_FILE, &moved)])[1].url,
            "https://new.example.com/index.json",
            "the address changes on the same feed"
        );
        let removed = removing("old", USER.as_bytes()).unwrap();
        assert_eq!(
            names(&merged(&[(USER_FILE, &removed)])),
            ["nuget.org"],
            "removal ignores case"
        );
        let enabled = setting_enabled(true, "nuget.org", Some(USER.as_bytes())).unwrap();
        assert!(
            merged(&[(USER_FILE, &enabled)])[0].is_enabled
                && !String::from_utf8_lossy(&enabled).contains("disabledPackageSources"),
            "enabling removes the mark and the empty section"
        );
        let disabled = setting_enabled(false, "Old", Some(USER.as_bytes())).unwrap();
        assert!(!merged(&[(USER_FILE, &disabled)])[1].is_enabled);
        assert_eq!(
            upserting("X", Some("https://x"), None, Some("not xml".as_bytes())),
            Err(Unreadable),
            "a broken file is not rewritten"
        );
        assert_eq!(
            removing("X", b"<other/>"),
            Err(Unreadable),
            "a root other than configuration is not a NuGet.Config"
        );
    }

    #[test]
    fn files_up_the_tree() {
        let dir = TempDir::new("nugetconfig");
        dir.put("NuGet.Config", REPO);
        dir.put("a/b/nuget.config", "<configuration/>");
        dir.put("user/NuGet.Config", USER);
        let user = dir.path().join("user/NuGet.Config");
        let found = files(Some(&dir.path().join("a/b/./")), &user);
        let tail: Vec<PathBuf> = found.iter().rev().take(2).cloned().collect();
        assert_eq!(found[0], user, "the user's first");
        assert_eq!(
            tail,
            [
                dir.path().join("a/b/nuget.config"),
                dir.path().join("NuGet.Config")
            ],
            "then from the root of the disk to the project"
        );
        let missing_user = files(Some(dir.path()), &dir.path().join("nope"));
        assert_eq!(missing_user.last(), Some(&dir.path().join("NuGet.Config")));
        assert!(
            !missing_user.contains(&dir.path().join("nope")),
            "no user file, none listed"
        );
        let sources = sources(Some(&dir.path().join("a/b")), &user);
        assert_eq!(names(&sources), ["nuget.org", "Company Feed"]);
    }
}
