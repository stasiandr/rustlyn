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

use super::changes::{How, Member};
use super::risk::{Level, Reason, Risk};
use super::walk::{Impact, Node, relative_to};
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
    /// Changed fields whose value this asset sets and the change loses: the
    /// field is renamed, removed, has another type or is no longer
    /// serialized.
    pub fields: Vec<String>,
    /// Changed fields whose value this asset sets and the change leaves as
    /// it is: a default or an attribute changed.
    pub kept: Vec<String>,
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
                "kept_fields",
                Json::Array(self.kept.iter().cloned().map(Json::String).collect()),
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
            kept: json.strings("kept_fields").unwrap_or_default(),
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
        if !self.kept.is_empty() {
            line += &format!("; sets field {} (kept)", self.kept.join(", "));
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
        for field in &self.kept {
            if let Some(index) = node_named(field) {
                let reason = Reason::SerializedValueKept {
                    asset: self.path.clone(),
                };
                risks.push((
                    index,
                    Risk::new(Level::Low, reason).at(self.path.clone(), self.line),
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
            let mut kept = Vec::new();
            let mut methods = Vec::new();
            for &index in &nodes {
                let node = &impact.nodes[index];
                let Some(how) = node.change else {
                    continue;
                };
                let name = node.member.short_name();
                match node.member.kind {
                    DeclarationKind::Field if how != How::Body && has_key(&text, name) => {
                        match field_effect(impact, node) {
                            Some(FieldEffect::Lost) => fields.push(name.to_owned()),
                            Some(FieldEffect::Kept) => kept.push(name.to_owned()),
                            None => {}
                        }
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
            let path = hit.rel_path.clone();
            result.push(Asset {
                path: hit.rel_path,
                script: script.clone(),
                line: hit.line,
                context: hit.context,
                nodes: nodes.clone(),
                fields: fields.clone(),
                kept: kept.clone(),
                methods,
            });
            // A prefab's scripts are in the scenes and prefabs that place
            // it, with the values they override.
            if (!fields.is_empty() || !kept.is_empty()) && path.ends_with(".prefab") {
                for instance in overriding(root, &paths, &path, guid, &fields, &kept) {
                    if seen.insert(instance.path.clone()) {
                        result.push(Asset {
                            script: script.clone(),
                            nodes: nodes.clone(),
                            ..instance
                        });
                    }
                }
            }
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

/// What a change to a serialized field does to the values stored for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FieldEffect {
    /// Unity no longer finds the stored value: the field is renamed
    /// (without `[FormerlySerializedAs]`), removed, of another type, or no
    /// longer serialized.
    Lost,
    /// The stored values stay: only the default or an attribute changed.
    Kept,
}

/// What the change to the field `node` does to the values assets store for
/// it; `None` when nothing is lost or kept that anyone need look at.
fn field_effect(impact: &Impact, node: &Node) -> Option<FieldEffect> {
    match node.change? {
        How::Removed => {
            let name = node.member.short_name();
            let former = format!("FormerlySerializedAs(\"{name}\")");
            let renamed = impact.nodes.iter().any(|other| {
                other.member.path == node.member.path
                    && other.member.kind == DeclarationKind::Field
                    && matches!(other.change, Some(How::Added | How::Signature))
                    && other.member.signature.contains(&former)
            });
            (!renamed).then_some(FieldEffect::Lost)
        }
        How::Added | How::Body => None,
        How::Signature => {
            let Some(before) = &node.before else {
                return Some(FieldEffect::Lost);
            };
            let now = &node.member;
            if before.type_text != now.type_text || (serialized(before) && !serialized(now)) {
                Some(FieldEffect::Lost)
            } else {
                Some(FieldEffect::Kept)
            }
        }
    }
}

/// Whether Unity serializes the field: public or `[SerializeField]`, and not
/// static, constant, read-only or `[NonSerialized]`.
fn serialized(field: &Member) -> bool {
    let has = |word: &str| field.modifiers.iter().any(|m| m == word);
    let attribute = |name: &str| field.attributes.iter().any(|a| a == name);
    (has("public") || attribute("SerializeField"))
        && !(has("static") || has("const") || has("readonly") || attribute("NonSerialized"))
}

/// The scenes and prefabs that place `prefab` and override the value of
/// one of the fields (`lost` and `kept`) of the script `script` on it: a
/// `PrefabInstance`'s `m_Modifications` names the component by its `fileID`
/// in the prefab and the field by its `propertyPath`.
fn overriding(
    root: &str,
    paths: &[String],
    prefab: &str,
    script: crate::unity::guid::Guid,
    lost: &[String],
    kept: &[String],
) -> Vec<Asset> {
    let Some(prefab_guid) = read_guid(&Path::new(root).join(format!("{prefab}.meta"))) else {
        return Vec::new();
    };
    let Ok(bytes) = std::fs::read(Path::new(root).join(prefab)) else {
        return Vec::new();
    };
    let Some(file) = crate::unity::yaml::UnityFile::parse(&bytes) else {
        return Vec::new();
    };
    let components: Vec<i64> = file
        .objects
        .iter()
        .filter(|object| object.script == Some(script))
        .map(|object| object.file_id)
        .collect();
    if components.is_empty() {
        return Vec::new();
    }
    let needle = prefab_guid.to_string();
    let mut found = Vec::new();
    for hit in usages::find(prefab_guid, Path::new(root), paths, &|_| None, &|| false) {
        if hit.rel_path == prefab || found.iter().any(|a: &Asset| a.path == hit.rel_path) {
            continue;
        }
        let text = std::fs::read_to_string(Path::new(root).join(&hit.rel_path)).unwrap_or_default();
        let mut set_lost = Vec::new();
        let mut set_kept = Vec::new();
        let mut first = None;
        let mut on_component = false;
        for (line, text) in text.lines().enumerate() {
            let text = text.trim();
            if let Some(target) = text.strip_prefix("- target:") {
                on_component = target.contains(&needle)
                    && components
                        .iter()
                        .any(|id| target.contains(&format!("fileID: {id},")));
            } else if on_component && let Some(path) = text.strip_prefix("propertyPath:") {
                let path = path.trim();
                let name = path.split(['.', '[']).next().unwrap_or(path);
                for (list, names) in [(&mut set_lost, lost), (&mut set_kept, kept)] {
                    if names.iter().any(|n| n == name) && !list.iter().any(|n| n == name) {
                        list.push(name.to_owned());
                        first.get_or_insert(line);
                    }
                }
            }
        }
        if let Some(line) = first {
            found.push(Asset {
                path: hit.rel_path.clone(),
                script: String::new(),
                line,
                context: Some(format!("overrides in {prefab}")),
                nodes: Vec::new(),
                fields: set_lost,
                kept: set_kept,
                methods: Vec::new(),
            });
        }
    }
    found
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

    const PLAYER: &str = "using UnityEngine;
public class Player : MonoBehaviour {
    public int health = 5;
    [SerializeField] private float speed = 1f;
}
";
    const PLAYER_META: &str = "fileFormatVersion: 2\nguid: 11111111111111111111111111111111\n";
    const HERO_META: &str = "fileFormatVersion: 2\nguid: 22222222222222222222222222222222\n";
    const HERO: &str = "%YAML 1.1
--- !u!1 &100
GameObject:
  m_Name: Hero
--- !u!114 &200
MonoBehaviour:
  m_GameObject: {fileID: 100}
  m_Script: {fileID: 11500000, guid: 11111111111111111111111111111111, type: 3}
  health: 7
  speed: 2
";
    const LEVEL: &str = "%YAML 1.1
--- !u!1001 &300
PrefabInstance:
  m_Modification:
    m_Modifications:
    - target: {fileID: 200, guid: 22222222222222222222222222222222, type: 3}
      propertyPath: health
      value: 99
      objectReference: {fileID: 0}
  m_SourcePrefab: {fileID: 100100000, guid: 22222222222222222222222222222222, type: 3}
";

    /// The assets and the risks after the player's script changes from
    /// `PLAYER` to `new`.
    fn player_changed(new: &str) -> (Vec<Asset>, Vec<(String, Level)>) {
        let project = Project::new(
            "player",
            &[
                ("Assets/Player.cs", PLAYER),
                ("Assets/Player.cs.meta", PLAYER_META),
                ("Assets/Hero.prefab", HERO),
                ("Assets/Hero.prefab.meta", HERO_META),
                ("Assets/Level.unity", LEVEL),
            ],
        );
        project.write("Assets/Player.cs", new);
        let session = project.session();
        let files = parse(&patch("Assets/Player.cs", PLAYER, new));
        let changes = changes(&files[0], new);
        let impact = walk(&project.root(), &session, &changes, Limits::default());
        let found = assets(&project.root(), &impact);
        let risks = found
            .iter()
            .flat_map(|asset| asset.risks(&impact))
            .map(|(_, risk)| (risk.reason.code().to_owned(), risk.level))
            .collect();
        (found, risks)
    }

    /// A new default, or an attribute, leaves the value stored in an asset
    /// alone: no high risk, only the note that instances keep their own.
    #[test]
    fn a_changed_default_does_not_lose_the_value_a_prefab_sets() {
        for new in [
            PLAYER.replace("health = 5", "health = 6"),
            PLAYER.replace("public int health", "[Range(0, 9)] public int health"),
        ] {
            let (found, risks) = player_changed(&new);
            let hero = found.iter().find(|a| a.path == "Assets/Hero.prefab");
            assert_eq!(hero.map(|a| a.fields.clone()), Some(Vec::new()), "{new}");
            assert_eq!(
                hero.map(|a| a.kept.clone()),
                Some(vec!["health".to_owned()])
            );
            assert!(
                risks.iter().all(|(_, level)| *level < Level::High),
                "{risks:?}"
            );
            assert!(
                risks.contains(&("serialized_value_kept".to_owned(), Level::Low)),
                "{risks:?}"
            );
        }
    }

    /// A rename, a type change and a field that stops being serialized lose
    /// the stored value; `[FormerlySerializedAs]` on the renamed field
    /// keeps it.
    #[test]
    fn a_rename_a_type_change_or_a_private_field_loses_the_value() {
        for new in [
            PLAYER.replace("health", "hp"),
            PLAYER.replace("public int health", "public float health"),
            PLAYER.replace("public int health", "private int health"),
        ] {
            let (found, risks) = player_changed(&new);
            let hero = found.iter().find(|a| a.path == "Assets/Hero.prefab");
            assert_eq!(
                hero.map(|a| a.fields.clone()),
                Some(vec!["health".to_owned()]),
                "{new}"
            );
            assert!(
                risks.contains(&("serialized_field".to_owned(), Level::High)),
                "{new}: {risks:?}"
            );
        }
        let renamed = PLAYER.replace(
            "public int health",
            "[FormerlySerializedAs(\"health\")] public int hp",
        );
        let (found, risks) = player_changed(&renamed);
        let hero = found.iter().find(|a| a.path == "Assets/Hero.prefab");
        assert_eq!(hero.map(|a| a.fields.clone()), Some(Vec::new()));
        assert!(
            risks.iter().all(|(_, level)| *level < Level::High),
            "{risks:?}"
        );
    }

    /// A scene that places the prefab and overrides the field is reached by
    /// the same change.
    #[test]
    fn a_scene_that_overrides_the_field_of_a_prefab_is_listed() {
        let (found, _) = player_changed(&PLAYER.replace("health", "hp"));
        let level = found
            .iter()
            .find(|a| a.path == "Assets/Level.unity")
            .unwrap_or_else(|| panic!("{found:?}"));
        assert_eq!(level.fields, vec!["health".to_owned()]);
        assert_eq!(level.line, 6, "the line of the override");
    }
}
