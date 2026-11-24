//! The Unity analyses on a small scene, a large one and a project on disk.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use super::assets::{AssetIndex, parse_meta};
use super::guid::Guid;
use super::usages;
use super::yaml::{self, Reference, UnityFile, outline_kind};

const PLAYER_GUID: &str = "11111111111111111111111111111111";
const BUTTON_PREFAB_GUID: &str = "22222222222222222222222222222222";
const PACKAGE_SCRIPT_GUID: &str = "33333333333333333333333333333333";

fn guid(text: &str) -> Guid {
    Guid::parse(text).unwrap()
}

fn units(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

/// Asset names as the test project's GUID index would give them.
fn names(g: Guid) -> Option<String> {
    let text = g.to_string();
    match text.as_str() {
        PLAYER_GUID => Some("Player".into()),
        BUTTON_PREFAB_GUID => Some("Button".into()),
        PACKAGE_SCRIPT_GUID => Some("Tool".into()),
        "44444444444444444444444444444444" => Some("Scripts".into()),
        _ => None,
    }
}

fn none(_: Guid) -> Option<String> {
    None
}

/// A test's temporary folder, removed at the end.
struct TempDir(PathBuf);

impl TempDir {
    fn new(label: &str) -> TempDir {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "rustlyn-analyzer-unity-{label}-{}-{}",
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        TempDir(path)
    }

    fn path(&self) -> &Path {
        &self.0
    }

    fn put(&self, rel: &str, text: &str) -> PathBuf {
        let path = self.0.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, text).unwrap();
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Sets a file's modification time, in seconds since 1970.
fn set_modified(path: &Path, seconds: f64) {
    let time = std::time::UNIX_EPOCH + std::time::Duration::from_secs_f64(seconds.max(0.0));
    let file = std::fs::File::options().write(true).open(path).unwrap();
    file.set_modified(time).unwrap();
}

fn now() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs_f64()
}

/// A scene with nested objects, a nested prefab and its stand-ins.
fn scene_text() -> String {
    format!(
        "%YAML 1.1
%TAG !u! tag:unity3d.com,2011:
--- !u!1 &100
GameObject:
  m_ObjectHideFlags: 0
  m_Component:
  - component: {{fileID: 101}}
  m_Name: Canvas
--- !u!224 &101
RectTransform:
  m_GameObject: {{fileID: 100}}
  m_Children:
  - {{fileID: 201}}
  m_Father: {{fileID: 0}}
--- !u!1 &200
GameObject:
  m_Name: 'Play Button'
--- !u!4 &201
Transform:
  m_GameObject: {{fileID: 200}}
  m_Father: {{fileID: 101}}
--- !u!114 &202
MonoBehaviour:
  m_GameObject: {{fileID: 200}}
  m_Enabled: 1
  m_Script: {{fileID: 11500000, guid: {PLAYER_GUID}, type: 3}}
  m_Name:
  m_EditorClassIdentifier: Assembly-CSharp::Game.Player
  speed: 5
--- !u!114 &203
MonoBehaviour:
  m_GameObject: {{fileID: 200}}
  m_Script: {{fileID: 11500000, guid: 99999999999999999999999999999999, type: 3}}
  m_Name:
  m_EditorClassIdentifier: Unity.UI::UnityEngine.UI.Image
--- !u!1001 &300
PrefabInstance:
  m_ObjectHideFlags: 0
  m_Modification:
    serializedVersion: 3
    m_TransformParent: {{fileID: 201}}
    m_Modifications:
    - target: {{fileID: 555, guid: {BUTTON_PREFAB_GUID}, type: 3}}
      propertyPath: m_LocalPosition.x
      value: 0
      objectReference: {{fileID: 0}}
    - target: {{fileID: 556, guid: {BUTTON_PREFAB_GUID}, type: 3}}
      propertyPath: m_Name
      value: Icon
      objectReference: {{fileID: 0}}
  m_SourcePrefab: {{fileID: 100100000, guid: {BUTTON_PREFAB_GUID}, type: 3}}
--- !u!4 &-301 stripped
Transform:
  m_CorrespondingSourceObject: {{fileID: 557, guid: {BUTTON_PREFAB_GUID}, type: 3}}
  m_PrefabInstance: {{fileID: 300}}
--- !u!1 &400
GameObject:
  m_Name: Badge
--- !u!4 &401
Transform:
  m_GameObject: {{fileID: 400}}
  m_Father: {{fileID: -301}}"
    )
}

/// A large scene: 12,500 GameObjects of four objects each, ten children apiece.
fn big_scene() -> String {
    let mut text = String::with_capacity(12_000_000);
    text.push_str("%YAML 1.1\n%TAG !u! tag:unity3d.com,2011:\n");
    for k in 0..12_500i64 {
        let go = 1000 + k * 4;
        let father = if k == 0 { 0 } else { 1001 + (k - 1) / 10 * 4 };
        text.push_str(&format!(
            "--- !u!1 &{go}\nGameObject:\n  m_ObjectHideFlags: 0\n  m_Name: Object{k}\n  m_IsActive: 1\n\
             --- !u!4 &{}\nTransform:\n  m_GameObject: {{fileID: {go}}}\n  m_LocalPosition: {{x: 0, y: 0, z: 0}}\n  m_Father: {{fileID: {father}}}\n\
             --- !u!114 &{}\nMonoBehaviour:\n  m_GameObject: {{fileID: {go}}}\n  m_Script: {{fileID: 11500000, guid: {PLAYER_GUID}, type: 3}}\n  m_Name: \n  value: 1\n\
             --- !u!23 &{}\nMeshRenderer:\n  m_GameObject: {{fileID: {go}}}\n  m_Materials:\n  - {{fileID: 2100000, guid: {BUTTON_PREFAB_GUID}, type: 2}}\n",
            go + 1,
            go + 2,
            go + 3
        ));
    }
    text
}

// MARK: - scenes and prefabs

#[test]
fn parses_scene() {
    let text = scene_text();
    let bytes = text.as_bytes();
    let scene = UnityFile::parse(bytes).expect("the scene parses");
    assert_eq!(scene.objects.len(), 10, "ten objects in the scene");
    let behaviour = scene.object(202).unwrap();
    assert_eq!(
        behaviour.type_name, "MonoBehaviour",
        "the object's type name"
    );
    assert_eq!(behaviour.game_object, Some(200), "m_GameObject");
    assert_eq!(behaviour.script, Some(guid(PLAYER_GUID)), "m_Script");
    assert_eq!(
        scene.object(200).unwrap().name.as_deref(),
        Some("Play Button"),
        "m_Name without quotes"
    );
    assert!(
        scene.object(-301).unwrap().stripped,
        "a stripped object with a negative fileID"
    );
    assert_eq!(
        scene.object(300).unwrap().modified_name.as_deref(),
        Some("Icon"),
        "a nested prefab renamed"
    );
    assert_eq!(
        scene.object(300).unwrap().transform_parent,
        Some(201),
        "a nested prefab's m_TransformParent"
    );
    assert_eq!(
        scene.object(300).unwrap().source_prefab,
        Some(guid(BUTTON_PREFAB_GUID)),
        "m_SourcePrefab"
    );
    assert!(UnityFile::parse(b"class A {}").is_none(), "not Unity: None");

    let resolve = &names;
    assert_eq!(
        scene.path_of_game_object(200, resolve),
        ["Canvas", "Play Button"],
        "the hierarchy through m_Father"
    );
    assert_eq!(
        scene.path_of_game_object(400, resolve),
        ["Canvas", "Play Button", "Icon", "Badge"],
        "the hierarchy goes through a nested prefab"
    );
    assert_eq!(
        scene.path_of_prefab_instance(300, resolve),
        ["Canvas", "Play Button", "Icon"]
    );

    let outline = scene.outline(resolve);
    let by_name = |name: &str| outline.iter().find(|i| i.name == name);
    assert!(
        by_name("Canvas")
            .is_some_and(|i| i.kind == outline_kind::GAME_OBJECT && i.container.is_none())
    );
    assert_eq!(
        by_name("Play Button").unwrap().container.as_deref(),
        Some("Canvas"),
        "the container is the parent's path"
    );
    let player = by_name("Player").unwrap();
    assert!(
        player.kind == outline_kind::COMPONENT
            && player.container.as_deref() == Some("Canvas / Play Button")
    );
    assert_eq!(
        by_name("Image").unwrap().kind,
        outline_kind::COMPONENT,
        "a script outside the project is named by m_EditorClassIdentifier"
    );
    assert_eq!(
        by_name("RectTransform").unwrap().container.as_deref(),
        Some("Canvas"),
        "a built-in component is named by its type"
    );
    let icon = by_name("Icon").unwrap();
    assert!(
        icon.kind == outline_kind::PREFAB
            && icon.container.as_deref() == Some("Canvas / Play Button")
    );
    assert!(
        !outline
            .iter()
            .any(|i| i.name == "Transform" && i.container.as_deref() == Some("Icon")),
        "stand-ins are left out"
    );
    assert!(
        outline
            .windows(2)
            .all(|w| w[0].range.location < w[1].range.location),
        "the outline is in file order"
    );
    assert_eq!(
        &text[player.range.location..player.range.end()],
        "MonoBehaviour",
        "ranges are byte ranges"
    );

    let unnamed = scene.outline(&none);
    assert!(
        unnamed
            .iter()
            .any(|i| i.name == "Game" || i.name == "Player"),
        "a name from m_EditorClassIdentifier"
    );
    assert!(
        unnamed.iter().any(|i| i.name == "Icon"),
        "a nested prefab's name from the overridden m_Name"
    );
    assert_eq!(
        scene.describe(scene.index_of(202).unwrap(), resolve),
        "Canvas / Play Button › Player"
    );
}

#[test]
fn utf16_and_bytes_read_alike() {
    let text = scene_text().replace("Play Button", "Кнопка");
    let from_bytes = UnityFile::parse(text.as_bytes()).unwrap();
    let u = units(&text);
    let from_units = UnityFile::parse(&u).unwrap();
    assert_eq!(from_bytes.objects.len(), from_units.objects.len());
    assert_eq!(
        from_units.object(200).unwrap().name.as_deref(),
        Some("Кнопка")
    );
    assert_eq!(
        from_bytes.object(200).unwrap().name.as_deref(),
        Some("Кнопка")
    );
    let bytes_range = from_bytes.object(202).unwrap().type_name_range;
    let units_range = from_units.object(202).unwrap().type_name_range;
    assert_eq!(
        &text[bytes_range.location..bytes_range.end()],
        "MonoBehaviour"
    );
    assert_eq!(
        String::from_utf16_lossy(&u[units_range.location..units_range.end()]),
        "MonoBehaviour"
    );
    assert!(
        bytes_range.location > units_range.location,
        "after Cyrillic, bytes run ahead of UTF-16 units"
    );
}

#[test]
fn references_under_caret() {
    let text = scene_text();
    let u = text.as_bytes();
    let line_range = |offset: usize| {
        let start = u[..offset]
            .iter()
            .rposition(|&c| c == b'\n')
            .map_or(0, |p| p + 1);
        let end = u[offset..]
            .iter()
            .position(|&c| c == b'\n')
            .map_or(u.len(), |p| offset + p + 1);
        (start, end)
    };
    let ref_at = |needle: &str, delta: usize| -> Option<Reference> {
        let start = text.find(needle)?;
        let offset = start + delta;
        let (ls, le) = line_range(offset);
        yaml::reference_at(u, ls, le, offset).map(|r| r.0)
    };
    assert_eq!(
        ref_at("m_Father: {fileID: 101}", 12),
        Some(Reference::Local(101)),
        "a local reference under the caret"
    );
    assert_eq!(
        ref_at("  m_Script:", 3),
        Some(Reference::Asset(guid(PLAYER_GUID), Some(11500000))),
        "the caret on the key takes the line's only reference"
    );
    assert_eq!(
        ref_at("m_Father: {fileID: 0}", 12),
        None,
        "a zero reference is no reference"
    );
    assert_eq!(
        ref_at("m_Name: Canvas", 2),
        None,
        "a line with no references goes nowhere"
    );

    let meta =
        units("fileFormatVersion: 2\nguid: df5d7f677beac4272a9df58a6db968b3\nMonoImporter:\n");
    assert_eq!(
        yaml::reference_at(&meta, 21, 60, 10).map(|r| r.0),
        Some(Reference::Asset(
            guid("df5d7f677beac4272a9df58a6db968b3"),
            None
        )),
        "the GUID in a .meta is a reference too, in UTF-16 as well"
    );
    let asmdef = format!("{{ \"references\": [\"GUID:{PLAYER_GUID}\"] }}");
    assert_eq!(
        yaml::reference_at(asmdef.as_bytes(), 0, asmdef.len(), 25).map(|r| r.0),
        Some(Reference::Asset(guid(PLAYER_GUID), None)),
        "GUID:… in an .asmdef refers to an assembly"
    );

    assert_eq!(
        yaml::guid_ranges(u, 0, u.len()).len(),
        6,
        "every GUID of the scene"
    );
    let locals = yaml::local_references(u, 0, u.len());
    assert!(
        locals.iter().any(|l| l.1 == -301) && !locals.iter().any(|l| l.1 == 0),
        "negative ones, no zero ones"
    );
    assert!(
        !locals.iter().any(|l| l.1 == 11500000),
        "a reference with a GUID is not local"
    );

    assert_eq!(
        yaml::anchor_line(200, u),
        Some(14),
        "the header &200 in the raw file"
    );
    assert_eq!(
        yaml::anchor_line(-301, u),
        Some(51),
        "a stripped object's header"
    );
    assert_eq!(yaml::anchor_line(20, u), None, "&20 is not &200");
    assert_eq!(
        yaml::anchor_type_line(200, u),
        Some((15, 10)),
        "landing on the type name under the header"
    );
}

#[test]
fn usages_in_scene() {
    let text = scene_text();
    let bytes = text.as_bytes();
    let prefab_hits = usages::hits(
        bytes,
        BUTTON_PREFAB_GUID.as_bytes(),
        "Assets/Main.unity",
        &names,
    );
    assert_eq!(prefab_hits.len(), 2, "a nested prefab: one hit per object");
    assert_eq!(
        prefab_hits[0].context.as_deref(),
        Some("Canvas / Play Button / Icon"),
        "the context is the prefab's path"
    );
    assert_eq!(prefab_hits[0].line, 42, "the first hit's line");
    let script_hits = usages::hits(bytes, PLAYER_GUID.as_bytes(), "Assets/Main.unity", &names);
    assert_eq!(script_hits.len(), 1);
    assert_eq!(
        script_hits[0].context.as_deref(),
        Some("Canvas / Play Button › Player"),
        "the script is used on Play Button"
    );
    assert_eq!(script_hits[0].column, 37, "the GUID's column in its line");
    assert_eq!(
        &bytes[script_hits[0].offset..script_hits[0].offset + 32],
        PLAYER_GUID.as_bytes()
    );

    let dir = TempDir::new("usages");
    dir.put("Assets/Main.unity", &text);
    dir.put(
        "Assets/Game.asmdef",
        &format!("{{ \"references\": [\"GUID:{PLAYER_GUID}\"] }}"),
    );
    dir.put("Assets/Notes.txt", PLAYER_GUID);
    let paths: Vec<String> = [
        "Assets/Main.unity",
        "Assets/Game.asmdef",
        "Assets/Notes.txt",
        "Assets/Missing.prefab",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    let found = usages::find(guid(PLAYER_GUID), dir.path(), &paths, &names, &|| false);
    let mut files: Vec<&str> = found.iter().map(|h| h.rel_path.as_str()).collect();
    files.sort_unstable();
    assert_eq!(
        files,
        ["Assets/Game.asmdef", "Assets/Main.unity"],
        "the scene and the asmdef, not the .txt"
    );
    assert!(
        usages::find(guid(PLAYER_GUID), dir.path(), &paths, &names, &|| true).is_empty(),
        "a search given up finds nothing"
    );
    assert!(usages::is_searchable("Assets/A.PREFAB") && !usages::is_searchable("Assets/A.cs"));
}

#[test]
fn serialized_field_value() {
    let lines = [
        "  m_Script: {fileID: 1}",
        "  speed: 5 ",
        "  points:",
        "  - 1",
        "--- !u!1 &2",
        "  other: 1",
    ];
    assert_eq!(
        yaml::serialized_field("speed", 0, &lines),
        Some((1, "5".into()))
    );
    assert_eq!(
        yaml::serialized_field("points", 0, &lines),
        Some((2, "…".into())),
        "a list is an ellipsis"
    );
    assert_eq!(
        yaml::serialized_field("other", 0, &lines),
        None,
        "another block is not looked at"
    );
}

#[test]
fn big_scene_is_fast() {
    let text = big_scene();
    let started = std::time::Instant::now();
    let file = UnityFile::parse(text.as_bytes()).unwrap();
    let outline = file.outline(&names);
    let ms = started.elapsed().as_millis();
    assert_eq!(file.objects.len(), 50_000, "every one of 50,000 objects");
    assert_eq!(outline.len(), 50_000, "an outline entry for each");
    assert!(
        ms < 1500 * if cfg!(debug_assertions) { 10 } else { 1 },
        "parsed in under 1.5 s (took {ms} ms)"
    );
}

// MARK: - GUIDs and the asset index

#[test]
fn meta_files() {
    let meta = "fileFormatVersion: 2\nguid: df5d7f677beac4272a9df58a6db968b3\nMonoImporter:\n  serializedVersion: 2\n";
    assert_eq!(
        parse_meta(meta.as_bytes())
            .map(|g| g.to_string())
            .as_deref(),
        Some("df5d7f677beac4272a9df58a6db968b3")
    );
    assert_eq!(
        parse_meta(b"fileFormatVersion: 2\n"),
        None,
        "a .meta without a GUID"
    );
}

fn unity_project() -> TempDir {
    let dir = TempDir::new("project");
    dir.put(
        "ProjectSettings/ProjectVersion.txt",
        "m_EditorVersion: 2022.3.10f1\n",
    );
    dir.put(
        "Assets/Scripts/Player.cs",
        "public class Player : MonoBehaviour { }\n",
    );
    dir.put(
        "Assets/Scripts/Player.cs.meta",
        &format!("fileFormatVersion: 2\nguid: {PLAYER_GUID}\n"),
    );
    dir.put(
        "Assets/Scripts.meta",
        "fileFormatVersion: 2\nguid: 44444444444444444444444444444444\nfolderAsset: yes\n",
    );
    dir.put("Assets/UI/Button.prefab", "%YAML 1.1\n");
    dir.put(
        "Assets/UI/Button.prefab.meta",
        &format!("fileFormatVersion: 2\nguid: {BUTTON_PREFAB_GUID}\n"),
    );
    dir.put(
        "Library/PackageCache/com.example.tools@abc123/Runtime/Tool.cs.meta",
        &format!("fileFormatVersion: 2\nguid: {PACKAGE_SCRIPT_GUID}\n"),
    );
    dir.put("Library/junk.bin", "x");
    dir.put("Temp/x.txt", "x");
    dir
}

#[test]
fn asset_index() {
    let dir = unity_project();
    let index = AssetIndex::build(dir.path(), None, None, &|| false);
    assert_eq!(index.count(), 4, "assets, a folder and a package script");
    assert_eq!(
        index.path(guid(PLAYER_GUID)),
        Some("Assets/Scripts/Player.cs"),
        "GUID to a script's path"
    );
    assert_eq!(
        index.display_name(guid(PLAYER_GUID)).as_deref(),
        Some("Player"),
        "a script's name is its class's"
    );
    assert_eq!(
        index.path(guid(PACKAGE_SCRIPT_GUID)),
        Some("Library/PackageCache/com.example.tools@abc123/Runtime/Tool.cs"),
        "package scripts resolve from the PackageCache"
    );
    assert_eq!(
        index.guid("Assets/UI/Button.prefab"),
        Some(guid(BUTTON_PREFAB_GUID)),
        "path to GUID"
    );
    assert_eq!(
        index.path(guid("44444444444444444444444444444444")),
        Some("Assets/Scripts"),
        "folders have GUIDs too"
    );
    assert_eq!(
        index.script_path("Player"),
        Some("Assets/Scripts/Player.cs")
    );
    assert!(
        AssetIndex::build(dir.path(), None, None, &|| true)
            .entries()
            .is_empty(),
        "a build given up is empty"
    );

    // Built again over the last one: an unchanged `.meta` is not read, its GUID
    // comes from the last index; one changed since is read again.
    let other = "55555555555555555555555555555555";
    let meta = dir.put(
        "Assets/UI/Button.prefab.meta",
        &format!("fileFormatVersion: 2\nguid: {other}\n"),
    );
    set_modified(&meta, 1_000_000.0);
    let reused = AssetIndex::build(dir.path(), Some(&index), Some(now()), &|| false);
    assert_eq!(
        reused.guid("Assets/UI/Button.prefab"),
        Some(guid(BUTTON_PREFAB_GUID)),
        "an unchanged .meta is not reread"
    );
    assert_eq!(reused.count(), index.count());
    assert!(
        reused.has_same_entries(&index),
        "nothing changed: the same entries"
    );
    set_modified(&meta, now() + 60.0);
    let reread = AssetIndex::build(dir.path(), Some(&index), Some(now()), &|| false);
    assert_eq!(
        reread.guid("Assets/UI/Button.prefab"),
        Some(guid(other)),
        "a changed .meta is reread"
    );
    assert!(
        !reread.has_same_entries(&index),
        "a GUID changed: the entries differ"
    );

    // The cache on disk answers like the index it was written from.
    let text = index.serialized();
    let back = AssetIndex::deserialize(&text).expect("the cache reads");
    assert_eq!(back.count(), index.count());
    assert_eq!(
        back.path(guid(PLAYER_GUID)),
        Some("Assets/Scripts/Player.cs")
    );
    assert_eq!(
        back.guid("Assets/UI/Button.prefab"),
        Some(guid(BUTTON_PREFAB_GUID))
    );
    assert_eq!(
        back.display_name(guid(PLAYER_GUID)).as_deref(),
        Some("Player")
    );
    assert_eq!(back.assembly_paths(), index.assembly_paths());
    assert_eq!(back.serialized(), text, "and writes back byte for byte");
    assert!(back.has_same_entries(&index));
    assert!(
        AssetIndex::deserialize("unity-assets 0\n").is_none(),
        "another cache version is not read"
    );
    assert!(
        AssetIndex::deserialize("unity-assets 1\nnot-a-guid\tAssets/A.cs\n").is_none(),
        "a damaged cache is not read"
    );
}

#[test]
fn duplicates_and_assemblies() {
    let a = guid(PLAYER_GUID);
    let b = guid(BUTTON_PREFAB_GUID);
    let index = AssetIndex::new(vec![
        (a, "Assets/A.cs".into()),
        (a, "Packages/A.cs".into()),
        (b, "Assets/A.cs".into()),
        (b, "Assets/Plugins/X.dll".into()),
    ]);
    assert_eq!(
        index.path(a),
        Some("Assets/A.cs"),
        "of equal GUIDs the first wins"
    );
    assert_eq!(
        index.guid("Assets/A.cs"),
        Some(b),
        "of equal paths the last"
    );
    assert_eq!(index.assembly_paths(), ["Assets/Plugins/X.dll"]);
    assert_eq!(index.count(), 2);
}
