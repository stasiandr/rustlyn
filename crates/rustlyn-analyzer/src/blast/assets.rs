//! The scenes and prefabs a change reaches, without Unity: the built-in
//! step of every report. A script in an asset is the GUID from its `.meta`;
//! finding the GUID across scenes, prefabs and other text assets is
//! [`crate::unity::usages`].
//!
//! For changed serialized fields it also shows in which assets their value
//! is set (a rename without `[FormerlySerializedAs]` loses it), and for
//! methods, where a `UnityEvent` calls them by name (`m_MethodName`).

use std::collections::{BTreeMap, HashSet};
use std::path::Path;

use rustlyn_ide::formats::json::{Json, object};
use rustlyn_ide::outline::DeclarationKind;

use super::changes::How;
use super::risk::{Level, Reason, Risk};
use super::walk::{Impact, relative_to};
use super::{BlastStep, Finding, StepContext};
use crate::unity::assets::read_guid;
use crate::unity::usages;

/// An asset where a reached script sits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Asset {
    /// Relative to the project root.
    pub path: String,
    /// The script (a `.cs` path) in it.
    pub script: String,
    /// The line of the first occurrence, from zero.
    pub line: usize,
    /// Where exactly in the scene: `Canvas / Button › PlayerInput`.
    pub context: Option<String>,
    /// The walk's nodes from this script.
    pub nodes: Vec<usize>,
    /// Changed fields whose value this asset sets.
    pub fields: Vec<String>,
    /// Changed methods this asset calls by name.
    pub methods: Vec<String>,
}

impl Asset {
    /// Its entry in the report's JSON (lines from one).
    #[must_use]
    pub fn json(&self) -> Json {
        object(vec![
            ("path", Json::String(self.path.clone())),
            ("script", Json::String(self.script.clone())),
            ("line", Json::Int(self.line as i64 + 1)),
            (
                "context",
                self.context.clone().map_or(Json::Null, Json::String),
            ),
            (
                "fields",
                Json::Array(self.fields.iter().cloned().map(Json::String).collect()),
            ),
            (
                "methods",
                Json::Array(self.methods.iter().cloned().map(Json::String).collect()),
            ),
        ])
    }

    /// The asset back from its JSON entry; the nodes are not in it.
    #[must_use]
    pub fn from_json(json: &Json) -> Option<Self> {
        Some(Self {
            path: json.str("path")?.to_owned(),
            script: json.str("script")?.to_owned(),
            line: usize::try_from(json.int("line")?.max(1) - 1).ok()?,
            context: json.str("context").map(str::to_owned),
            nodes: Vec::new(),
            fields: json.strings("fields").unwrap_or_default(),
            methods: json.strings("methods").unwrap_or_default(),
        })
    }

    /// One line for the text tree.
    #[must_use]
    pub fn text(&self) -> String {
        let mut line = format!("▣ {} — has {}", self.path, self.script);
        if let Some(context) = &self.context {
            line += &format!(" ({context})");
        }
        if !self.fields.is_empty() {
            line += &format!("; sets field {}", self.fields.join(", "));
        }
        if !self.methods.is_empty() {
            line += &format!("; calls {}", self.methods.join(", "));
        }
        line
    }

    /// The reasons for risk it adds: a serialized field set here, a method
    /// called by name from here.
    #[must_use]
    pub fn risks(&self, impact: &Impact) -> Vec<(usize, Risk)> {
        let mut risks = Vec::new();
        let node_named = |name: &str| {
            self.nodes
                .iter()
                .copied()
                .find(|&i| impact.nodes[i].member.short_name() == name)
        };
        for field in &self.fields {
            if let Some(index) = node_named(field) {
                let reason = Reason::SerializedField {
                    asset: self.path.clone(),
                };
                risks.push((
                    index,
                    Risk::new(Level::High, reason).at(self.path.clone(), self.line),
                ));
            }
        }
        for method in &self.methods {
            if let Some(index) = node_named(method) {
                let level = if impact.nodes[index].change == Some(How::Body) {
                    Level::Low
                } else {
                    Level::High
                };
                let reason = Reason::UnityEvent {
                    asset: self.path.clone(),
                };
                risks.push((
                    index,
                    Risk::new(level, reason).at(self.path.clone(), self.line),
                ));
            }
        }
        risks
    }
}

/// A Unity project: there is `Assets/`.
#[must_use]
pub fn is_unity(root: &str) -> bool {
    Path::new(root).join("Assets").is_dir()
}

/// The assets where the scripts of the reached nodes sit.
#[must_use]
pub fn assets(root: &str, impact: &Impact) -> Vec<Asset> {
    if !is_unity(root) {
        return Vec::new();
    }
    // Script → its nodes.
    let mut scripts: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, node) in impact.nodes.iter().enumerate() {
        scripts
            .entry(node.member.path.clone())
            .or_default()
            .push(index);
    }
    let mut paths = Vec::new();
    asset_files(Path::new(root), &Path::new(root).join("Assets"), &mut paths);
    let mut result = Vec::new();
    for (script, nodes) in scripts {
        let Some(guid) = read_guid(&Path::new(root).join(format!("{script}.meta"))) else {
            continue;
        };
        let hits = usages::find(guid, Path::new(root), &paths, &|_| None, &|| false);
        let mut seen = HashSet::new();
        for hit in hits {
            if !seen.insert(hit.rel_path.clone()) {
                continue;
            }
            let text =
                std::fs::read_to_string(Path::new(root).join(&hit.rel_path)).unwrap_or_default();
            let mut fields = Vec::new();
            let mut methods = Vec::new();
            for &index in &nodes {
                let node = &impact.nodes[index];
                let Some(how) = node.change else {
                    continue;
                };
                let name = node.member.short_name();
                match node.member.kind {
                    DeclarationKind::Field if how != How::Body && has_key(&text, name) => {
                        fields.push(name.to_owned());
                    }
                    DeclarationKind::Method
                        if text.contains(&format!("m_MethodName: {name}\n"))
                            || text.contains(&format!("m_MethodName: {name}\r")) =>
                    {
                        methods.push(name.to_owned());
                    }
                    _ => {}
                }
            }
            result.push(Asset {
                path: hit.rel_path,
                script: script.clone(),
                line: hit.line,
                context: hit.context,
                nodes: nodes.clone(),
                fields,
                methods,
            });
        }
    }
    result.sort_by(|a, b| (&a.script, &a.path).cmp(&(&b.script, &b.path)));
    result
}

/// The built-in step: [`assets`] as findings under `assets`.
#[derive(Debug, Clone, Copy, Default)]
pub struct UnityAssets;

impl BlastStep for UnityAssets {
    fn name(&self) -> &'static str {
        "assets"
    }

    fn run(&self, cx: &StepContext<'_>, impact: &Impact) -> Vec<Finding> {
        assets(cx.root, impact)
            .into_iter()
            .map(|asset| Finding {
                json: asset.json(),
                text: vec![asset.text()],
                risks: asset.risks(impact),
                nodes: asset.nodes,
            })
            .collect()
    }
}

/// `  name: …` — the key of a serialized field in Unity's YAML.
fn has_key(text: &str, name: &str) -> bool {
    let needle = format!("{name}:");
    text.lines()
        .any(|l| l.trim_start().starts_with(&needle) && l.starts_with("  "))
}

fn asset_files(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            if !entry.file_name().to_string_lossy().starts_with('.') {
                asset_files(root, &path, out);
            }
        } else {
            let rel = relative_to(&root.to_string_lossy(), &path.to_string_lossy());
            if usages::is_searchable(&rel) {
                out.push(rel);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::changes::changes;
    use crate::blast::diff::parse;
    use crate::blast::testing::{Project, patch};
    use crate::blast::walk::{Limits, walk};

    const DOOR: &str = "using UnityEngine;
public class Door : MonoBehaviour {
    public float speed = 1;
    public void Open() { }
}
";
    const META: &str = "fileFormatVersion: 2\nguid: 0123456789abcdef0123456789abcdef\n";
    const PREFAB: &str = "%YAML 1.1
--- !u!1 &100
GameObject:
  m_Name: Door
--- !u!114 &200
MonoBehaviour:
  m_GameObject: {fileID: 100}
  m_Script: {fileID: 11500000, guid: 0123456789abcdef0123456789abcdef, type: 3}
  speed: 2.5
--- !u!114 &300
MonoBehaviour:
  m_OnClick:
    m_PersistentCalls:
      m_Calls:
      - m_Target: {fileID: 200}
        m_MethodName: Open
";

    #[test]
    fn prefab_with_the_script_a_field_and_a_call_by_name() {
        let project = Project::new(
            "assets",
            &[
                ("Assets/Door.cs", DOOR),
                ("Assets/Door.cs.meta", META),
                ("Assets/Door.prefab", PREFAB),
                ("Assets/Empty.prefab", "%YAML 1.1\n"),
            ],
        );
        let new = DOOR
            .replace("public float speed = 1;", "public float openSpeed = 1;")
            .replace("public void Open() { }", "public void OpenDoor() { }");
        project.write("Assets/Door.cs", &new);
        let session = project.session();
        let files = parse(&patch("Assets/Door.cs", DOOR, &new));
        let changes = changes(&files[0], &new);
        let impact = walk(&project.root(), &session, &changes, Limits::default());
        let found = assets(&project.root(), &impact);
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].path, "Assets/Door.prefab");
        assert_eq!(
            found[0].fields,
            vec!["speed".to_owned()],
            "the field's old name is set in the prefab"
        );
        assert_eq!(
            found[0].methods,
            vec!["Open".to_owned()],
            "the button calls Open by name"
        );
        assert_eq!(
            Asset::from_json(&found[0].json()).map(|a| a.path),
            Some(found[0].path.clone())
        );
    }
}
