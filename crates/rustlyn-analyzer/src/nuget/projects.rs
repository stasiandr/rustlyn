//! .NET projects and their packages, read from the text of `.csproj` files
//! and `Directory.Packages.props`. Editing them is left to
//! `dotnet add/remove package`, which knows about central versions,
//! conditions and restore.

use std::collections::HashMap;
use std::path::Path;

use super::text::{equal_ignoring_case, trim_spaces};
use super::version::NuGetVersion;

/// A package a project references.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Reference {
    pub id: String,
    /// As written: `13.0.3`, a range `[1.0,2.0)`, `$(Version)`. `None` when
    /// the project gives no version (`Directory.Packages.props` does).
    pub version: Option<String>,
    /// The version comes from `Directory.Packages.props`: central management.
    pub is_central: bool,
    /// Under a condition — its own, an `<ItemGroup Condition>`, a `<When>` — or
    /// inside a `<Target>`: the package is not in every build, and a restore
    /// may not have seen it.
    pub is_conditional: bool,
}

impl Reference {
    pub fn new(id: &str) -> Self {
        Reference {
            id: id.to_string(),
            ..Default::default()
        }
    }

    /// A version to compare with: exact, no range, no properties.
    pub fn resolved(&self) -> Option<NuGetVersion> {
        resolved(self.version.as_deref()?)
    }
}

/// `[1.2.3]` is exactly that version; a range or a property is `None`.
pub fn resolved(version: &str) -> Option<NuGetVersion> {
    let mut text = trim_spaces(version);
    if text.starts_with('[') && text.ends_with(']') && !text.contains(',') && text.len() >= 2 {
        text = &text[1..text.len() - 1];
    }
    NuGetVersion::parse(text)
}

/// An SDK-style .NET project and its packages.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Project {
    /// From the root: `Server/Server.csproj`.
    pub path: String,
    pub references: Vec<Reference>,
    /// `net8.0`, `netstandard2.1;net8.0`.
    pub frameworks: Option<String>,
}

impl Project {
    pub fn name(&self) -> String {
        file_stem(&self.path)
    }

    pub fn reference(&self, id: &str) -> Option<&Reference> {
        self.references
            .iter()
            .find(|r| equal_ignoring_case(&r.id, id))
    }
}

/// `Server/Server.csproj` → `Server`.
pub fn file_stem(path: &str) -> String {
    let name = path.rsplit('/').next().unwrap_or(path);
    match name.rfind('.') {
        Some(dot) if dot > 0 => name[..dot].to_string(),
        _ => name.to_string(),
    }
}

/// A path's folder: `src/App/App.csproj` → `src/App`, `App.csproj` → empty.
pub fn parent(path: &str) -> &str {
    path.rfind('/').map_or("", |slash| &path[..slash])
}

/// The trimmed text of the first `<name>…</name>`, name case ignored.
#[must_use]
pub fn element(name: &str, text: &str) -> Option<String> {
    let open = format!("<{name}>");
    let close = format!("</{name}>");
    let start = find_ignoring_case(text, &open, 0)? + open.len();
    let end = find_ignoring_case(text, &close, start)?;
    Some(text[start..end].trim().to_owned())
}

/// The file that holds central package versions.
pub const CENTRAL_FILE: &str = "Directory.Packages.props";

/// The SDK-style projects under `root` with their packages, sorted by path.
#[must_use]
pub fn discover(root: &Path) -> Vec<Project> {
    let paths: Vec<String> = rustlyn_ide::project::csproj_files(root)
        .into_iter()
        .filter_map(|path| {
            let relative = path.strip_prefix(root).ok()?;
            let parts: Vec<String> = relative
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            Some(parts.join("/"))
        })
        .collect();
    let mut central: HashMap<String, HashMap<String, String>> = HashMap::new();
    let mut out: Vec<Project> = paths
        .into_iter()
        .filter_map(|path| {
            let text = std::fs::read_to_string(root.join(&path)).ok()?;
            if !is_sdk_style(&text) {
                return None;
            }
            let directory = parent(&path).to_string();
            let versions = central
                .entry(directory.clone())
                .or_insert_with(|| central_versions(&directory, root));
            let mut references = package_references(&text);
            for reference in references.iter_mut().filter(|r| r.version.is_none()) {
                if let Some(version) = versions.get(&reference.id.to_lowercase()) {
                    reference.version = Some(version.clone());
                    reference.is_central = true;
                }
            }
            let frameworks =
                element("TargetFrameworks", &text).or_else(|| element("TargetFramework", &text));
            Some(Project {
                path,
                references,
                frameworks,
            })
        })
        .collect();
    out.sort_by(|a, b| a.path.cmp(&b.path));
    out
}

/// Whether a change to this file on disk is reason to read packages again.
pub fn is_relevant(path: &str) -> bool {
    path.ends_with(".csproj")
        || path.ends_with(&format!("/{CENTRAL_FILE}"))
        || path.ends_with(".props")
}

/// `<Project Sdk="Microsoft.NET.Sdk">`. Unity's projects are the old kind:
/// its editor generates them, and NuGet packages are not added to them.
pub fn is_sdk_style(text: &str) -> bool {
    let Some(open) = text.find("<Project") else {
        return false;
    };
    let after = open + "<Project".len();
    let tag_end = text[after..].find('>').map_or(text.len(), |i| after + i);
    text[after..tag_end].contains("Sdk=") || text.contains("<Sdk ")
}

/// `<PackageReference Include="Id" Version="1.0" />` and the same with a
/// `<Version>` inside. `Update=` adds no package and is skipped.
pub fn package_references(text: &str) -> Vec<Reference> {
    let plain = without_comments(text);
    let conditional = conditional_ranges(&plain);
    let mut out: Vec<Reference> = Vec::new();
    for element in elements("PackageReference", &plain) {
        let Some(id) = element
            .attributes
            .get("include")
            .filter(|id| !id.is_empty())
        else {
            continue;
        };
        let version = element
            .attributes
            .get("version")
            .or_else(|| element.attributes.get("versionoverride"))
            .cloned()
            .or_else(|| {
                element
                    .body
                    .as_deref()
                    .and_then(|body| self::element("Version", body))
            });
        let is_conditional = element.attributes.contains_key("condition")
            || conditional.iter().any(|r| r.contains(&element.range.start));
        if let Some(existing) = out.iter_mut().find(|r| equal_ignoring_case(&r.id, id)) {
            // The same reference again, unconditionally: always there.
            if !is_conditional {
                existing.is_conditional = false;
            }
        } else {
            out.push(Reference {
                id: id.clone(),
                version,
                is_central: false,
                is_conditional,
            });
        }
    }
    out
}

/// Where references do not always apply: `<ItemGroup Condition>`, the
/// branches of `<Choose>`, and `<Target>`, whose items appear during a build.
fn conditional_ranges(text: &str) -> Vec<std::ops::Range<usize>> {
    ["ItemGroup", "When", "Otherwise", "Target"]
        .iter()
        .flat_map(|&name| {
            elements(name, text)
                .into_iter()
                .filter(move |e| {
                    name == "Otherwise"
                        || name == "Target"
                        || e.attributes.contains_key("condition")
                })
                .map(|e| e.range)
        })
        .collect()
}

/// `<PackageVersion Include="Id" Version="1.0" />`, keys lowercased: NuGet
/// ids ignore case.
pub fn package_versions(text: &str) -> HashMap<String, String> {
    let mut out = HashMap::new();
    for element in elements("PackageVersion", &without_comments(text)) {
        let Some(id) = element
            .attributes
            .get("include")
            .or_else(|| element.attributes.get("update"))
        else {
            continue;
        };
        let version = element.attributes.get("version").cloned().or_else(|| {
            element
                .body
                .as_deref()
                .and_then(|b| self::element("Version", b))
        });
        if let Some(version) = version {
            out.insert(id.to_lowercase(), version);
        }
    }
    out
}

/// MSBuild takes the nearest `Directory.Packages.props` up from the project.
pub fn central_versions(directory: &str, root: &Path) -> HashMap<String, String> {
    let mut components: Vec<&str> = if directory.is_empty() {
        Vec::new()
    } else {
        directory.split('/').filter(|s| !s.is_empty()).collect()
    };
    loop {
        let mut relative = components.join("/");
        if !relative.is_empty() {
            relative.push('/');
        }
        relative.push_str(CENTRAL_FILE);
        if let Ok(text) = std::fs::read_to_string(root.join(&relative)) {
            return package_versions(&text);
        }
        if components.pop().is_none() {
            return HashMap::new();
        }
    }
}

// MARK: reading

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Element {
    /// Names lowercased: MSBuild ignores their case.
    pub attributes: HashMap<String, String>,
    /// Between the opening and closing tags; `None` when self-closed (`/>`).
    pub body: Option<String>,
    /// The whole element in the text (bytes), from `<` to the closing tag.
    pub range: std::ops::Range<usize>,
}

/// A substring from `from`, ASCII case ignored.
fn find_ignoring_case(text: &str, pattern: &str, from: usize) -> Option<usize> {
    let (hay, needle) = (text.as_bytes(), pattern.as_bytes());
    if needle.is_empty() || from > hay.len() || hay.len() - from < needle.len() {
        return None;
    }
    (from..=hay.len() - needle.len()).find(|&i| {
        hay[i..i + needle.len()].eq_ignore_ascii_case(needle) && text.is_char_boundary(i)
    })
}

pub fn elements(name: &str, text: &str) -> Vec<Element> {
    let mut out = Vec::new();
    let mut cursor = 0;
    let open_tag = format!("<{name}");
    let close_tag = format!("</{name}");
    while let Some(open) = find_ignoring_case(text, &open_tag, cursor) {
        cursor = open + open_tag.len();
        // `<PackageReferences>` is another tag.
        match text[cursor..].chars().next() {
            Some(c) if c.is_whitespace() || c == '/' || c == '>' => {}
            _ => continue,
        }
        let Some(close) = tag_end(text, cursor) else {
            break;
        };
        let inside = &text[cursor..close];
        let self_closing = inside.ends_with('/');
        let attributes = parse_attributes(if self_closing {
            &inside[..inside.len() - 1]
        } else {
            inside
        });
        cursor = close + 1;
        let mut body = None;
        if !self_closing {
            if let Some(end) = find_ignoring_case(text, &close_tag, cursor) {
                body = Some(text[cursor..end].to_string());
                cursor = end + close_tag.len();
            } else {
                body = Some(String::new());
            }
        }
        out.push(Element {
            attributes,
            body,
            range: open..cursor,
        });
    }
    out
}

/// The `>` of a tag, past quoted attribute values.
fn tag_end(text: &str, start: usize) -> Option<usize> {
    let mut quote: Option<u8> = None;
    for (i, &c) in text.as_bytes().iter().enumerate().skip(start) {
        if let Some(q) = quote {
            if c == q {
                quote = None;
            }
        } else if c == b'"' || c == b'\'' {
            quote = Some(c);
        } else if c == b'>' {
            return Some(i);
        }
    }
    None
}

pub fn parse_attributes(text: &str) -> HashMap<String, String> {
    let mut out = HashMap::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        let mut name = String::new();
        while i < chars.len() && chars[i] != '=' && !chars[i].is_whitespace() {
            name.push(chars[i]);
            i += 1;
        }
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() || chars[i] != '=' {
            if name.is_empty() {
                i += 1;
            }
            continue;
        }
        i += 1;
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() || (chars[i] != '"' && chars[i] != '\'') {
            continue;
        }
        let quote = chars[i];
        i += 1;
        let mut value = String::new();
        while i < chars.len() && chars[i] != quote {
            value.push(chars[i]);
            i += 1;
        }
        i += 1;
        if !name.is_empty() {
            out.insert(name.to_lowercase(), unescape(&value));
        }
    }
    out
}

fn unescape(value: &str) -> String {
    if !value.contains('&') {
        return value.to_string();
    }
    value
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&amp;", "&")
}

fn without_comments(text: &str) -> String {
    if !text.contains("<!--") {
        return text.to_string();
    }
    let mut out = String::new();
    let mut cursor = 0;
    while let Some(open) = text[cursor..].find("<!--").map(|i| cursor + i) {
        out.push_str(&text[cursor..open]);
        let Some(close) = text[open + 4..].find("-->").map(|i| open + 4 + i) else {
            return out;
        };
        cursor = close + 3;
    }
    out.push_str(&text[cursor..]);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nuget::testing::TempDir;

    const CSPROJ: &str = r#"<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>
  <ItemGroup>
    <PackageReference Include="Newtonsoft.Json" Version="13.0.3" />
    <PackageReference Include='Serilog'>
      <Version>3.1.1</Version>
    </PackageReference>
    <!-- <PackageReference Include="Old.Package" Version="1.0" /> -->
    <PackageReference Include="Central.Only" />
    <PackageReference Include="Exact" Version="[2.0.0]" PrivateAssets="all" />
    <PackageReference Update="Newtonsoft.Json" Version="99" />
    <PackageReferences Include="Not.A.Reference" Version="1" />
    <ProjectReference Include="../Lib/Lib.csproj" />
  </ItemGroup>
</Project>"#;

    #[test]
    fn references() {
        let refs = package_references(CSPROJ);
        let ids: Vec<&str> = refs.iter().map(|r| r.id.as_str()).collect();
        assert_eq!(
            ids,
            ["Newtonsoft.Json", "Serilog", "Central.Only", "Exact"],
            "package references: no comments, no Update, no other tags"
        );
        assert!(
            refs[0].version.as_deref() == Some("13.0.3")
                && refs[1].version.as_deref() == Some("3.1.1")
                && refs[2].version.is_none(),
            "a version as an attribute and as an element; none is None"
        );
        let mut range = Reference::new("X");
        range.version = Some("[1.0,2.0)".into());
        assert!(
            refs[3].resolved() == NuGetVersion::parse("2.0.0") && range.resolved().is_none(),
            "[2.0.0] is exactly that version, a range is not compared"
        );
        assert!(
            is_sdk_style(CSPROJ)
                && !is_sdk_style(
                    "<?xml version=\"1.0\"?><Project ToolsVersion=\"4.0\"><ItemGroup/></Project>"
                ),
            "SDK style tells apart from Unity projects"
        );
        assert_eq!(
            package_versions(
                "<Project><ItemGroup><PackageVersion Include=\"Central.Only\" Version=\"1.2.3\" /></ItemGroup></Project>"
            ),
            HashMap::from([("central.only".to_string(), "1.2.3".to_string())]),
            "Directory.Packages.props: versions by id"
        );
    }

    #[test]
    fn conditions() {
        let text = r#"<Project Sdk="Microsoft.NET.Sdk">
  <ItemGroup>
    <PackageReference Include="Always" Version="1.0.0" />
    <PackageReference Include="Own" Version="1.0.0" Condition="'$(OS)' == 'Windows_NT'" />
  </ItemGroup>
  <ItemGroup Condition=" '$(Configuration)' == 'Debug' ">
    <PackageReference Include="InGroup" Version="1.0.0" />
    <PackageReference Include="Twice" Version="1.0.0" />
  </ItemGroup>
  <ItemGroup><PackageReference Include="Twice" Version="1.0.0" /></ItemGroup>
  <Choose>
    <When Condition="'$(TargetFramework)' == 'net8.0'">
      <ItemGroup><PackageReference Include="InWhen" Version="1.0.0" /></ItemGroup>
    </When>
    <Otherwise>
      <ItemGroup><PackageReference Include="InOtherwise" Version="1.0.0" /></ItemGroup>
    </Otherwise>
  </Choose>
  <Target Name="Late"><ItemGroup><PackageReference Include="InTarget" Version="1.0.0" /></ItemGroup></Target>
  <ItemGroup><PackageReference Include="After" Version="1.0.0" /></ItemGroup>
</Project>"#;
        let marked = package_references(text);
        let always: Vec<&str> = marked
            .iter()
            .filter(|r| !r.is_conditional)
            .map(|r| r.id.as_str())
            .collect();
        let conditional: Vec<&str> = marked
            .iter()
            .filter(|r| r.is_conditional)
            .map(|r| r.id.as_str())
            .collect();
        assert_eq!(
            always,
            ["Always", "Twice", "After"],
            "a repeat with no condition: always"
        );
        assert_eq!(
            conditional,
            ["Own", "InGroup", "InWhen", "InOtherwise", "InTarget"],
            "conditional: own, ItemGroup, When/Otherwise, Target"
        );
    }

    #[test]
    fn projects_on_disk() {
        let dir = TempDir::new("nuget");
        dir.put("src/App/App.csproj", CSPROJ);
        dir.put("Directory.Packages.props", "<Project><ItemGroup><PackageVersion Include=\"central.only\" Version=\"4.5.6\" /></ItemGroup></Project>");
        dir.put(
            "Unity/Assembly-CSharp.csproj",
            "<Project ToolsVersion=\"4.0\"></Project>",
        );
        dir.put("node_modules/x/X.csproj", CSPROJ);
        let projects = discover(dir.path());
        let paths: Vec<&str> = projects.iter().map(|p| p.path.as_str()).collect();
        assert_eq!(
            paths,
            ["src/App/App.csproj"],
            "only SDK-style projects, node_modules not walked"
        );
        let central = projects[0].reference("CENTRAL.ONLY").unwrap();
        assert!(
            central.version.as_deref() == Some("4.5.6")
                && central.is_central
                && projects[0].frameworks.as_deref() == Some("net8.0"),
            "the version from Directory.Packages.props, the id case ignored"
        );
        assert_eq!(projects[0].name(), "App");
        assert!(
            is_relevant("/p/Server/Server.csproj")
                && is_relevant("/p/Directory.Packages.props")
                && !is_relevant("/p/Server/Program.cs")
        );
    }
}
