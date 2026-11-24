//! The text format Unity serializes scenes, prefabs and assets in (`.unity`,
//! `.prefab`, `.asset`, `.mat`, `.controller`…).
//!
//! Not a YAML parser: Unity's format is rigid enough for one pass over the
//! lines that looks only at an object's top-level keys. A scene of hundreds
//! of thousands of lines parses in tens of milliseconds.
//!
//! The parser reads code units of either width: UTF-8 bytes, whose offsets
//! are the byte offsets of the public API, or UTF-16 units for an editor that
//! counts in them. Every key it looks for is ASCII, so both read alike; a
//! [`Span`] is in the units of the text it came from.

use std::collections::HashMap;

use super::guid::{Guid, hex_value};

/// A unit of text the parser reads: a UTF-8 byte or a UTF-16 code unit.
pub trait CodeUnit: Copy + Into<u32> + sealed::Sealed {
    /// The unit as a number, to compare against ASCII.
    fn code(self) -> u32 {
        self.into()
    }

    /// Units back to a string; broken sequences become U+FFFD.
    fn decode(units: &[Self]) -> String;
}

impl CodeUnit for u8 {
    fn decode(units: &[Self]) -> String {
        String::from_utf8_lossy(units).into_owned()
    }
}

impl CodeUnit for u16 {
    fn decode(units: &[Self]) -> String {
        String::from_utf16_lossy(units)
    }
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for u8 {}
    impl Sealed for u16 {}
}

/// Spaces as `CharacterSet.whitespaces` has them: no line breaks.
fn is_space(c: char) -> bool {
    matches!(
        c,
        '\t' | ' ' | '\u{a0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200a}' | '\u{202f}' | '\u{205f}' | '\u{3000}'
    )
}

/// A range of the text in its code units: a start and a length.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub location: usize,
    pub length: usize,
}

impl Span {
    pub fn new(location: usize, length: usize) -> Span {
        Span { location, length }
    }

    pub fn end(&self) -> usize {
        self.location + self.length
    }
}

/// One object of a Unity serialized file: the block from `--- !u!<class> &<fileID>`
/// to the next such header.
#[derive(Debug, Clone, Default)]
pub struct UnityObject {
    /// Unity's numeric class ID: 1 GameObject, 4 Transform, 114 MonoBehaviour…
    pub class_id: i64,
    pub file_id: i64,
    /// A stand-in for an object of a nested prefab: the object lives in the
    /// prefab, and here is only a reference to it.
    pub stripped: bool,
    /// Where the block starts (in code units) and on which line.
    pub start: usize,
    pub start_line: usize,
    pub type_name: String,
    /// The type name at the start of the block: where navigation lands.
    pub type_name_range: Span,
    pub type_name_line: usize,
    pub name: Option<String>,
    pub name_range: Option<Span>,
    pub name_line: Option<usize>,
    /// `m_GameObject`: the component's owner.
    pub game_object: Option<i64>,
    /// `m_Father`: only on Transform and RectTransform.
    pub father: Option<i64>,
    /// `m_PrefabInstance`: on the stand-ins of a nested prefab.
    pub prefab_instance: Option<i64>,
    /// `m_TransformParent` of a PrefabInstance: where in the hierarchy it is.
    pub transform_parent: Option<i64>,
    /// `m_Script` of a MonoBehaviour.
    pub script: Option<Guid>,
    /// `m_SourcePrefab` of a PrefabInstance.
    pub source_prefab: Option<Guid>,
    /// A nested prefab's `m_Name` as the scene overrides it.
    pub modified_name: Option<String>,
    /// `Assembly::Namespace.Class`: Unity 6 writes it on a MonoBehaviour.
    pub editor_class_identifier: Option<String>,
    /// `m_Children` of a Transform and `m_Roots` of SceneRoots: the order of
    /// children in the Hierarchy window, which the file's order is not.
    pub children: Option<Vec<i64>>,
    /// `m_RootOrder`: a scene root's place before Unity 2022 brought
    /// SceneRoots. On a nested prefab, from its overrides.
    pub root_order: Option<i64>,
    /// `m_IsActive: 0`: a GameObject turned off.
    pub is_inactive: bool,
}

impl UnityObject {
    pub fn is_game_object(&self) -> bool {
        self.class_id == 1
    }

    pub fn is_prefab_instance(&self) -> bool {
        self.class_id == 1001
    }
}

/// A reference in a serialized file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reference {
    /// `{fileID: N}`: an object in the same file.
    Local(i64),
    /// `{fileID: N, guid: G, type: T}`: another asset, and maybe an object in it.
    Asset(Guid, Option<i64>),
}

/// An asset's name by its GUID: scripts and nested prefabs are named by it.
pub type Resolver<'a> = &'a dyn Fn(Guid) -> Option<String>;

/// The kind of an outline entry.
pub mod outline_kind {
    pub const GAME_OBJECT: u8 = 9;
    pub const COMPONENT: u8 = 10;
    pub const PREFAB: u8 = 11;
}

/// An entry of a file's outline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutlineEntry {
    pub name: String,
    pub kind: u8,
    pub range: Span,
    pub line: usize,
    pub depth: usize,
    pub container: Option<String>,
}

/// A parsed file; immutable.
#[derive(Debug, Clone)]
pub struct UnityFile {
    pub objects: Vec<UnityObject>,
    index_by_file_id: HashMap<i64, usize>,
    /// GameObject to its Transform: the way up the hierarchy.
    transform_by_game_object: HashMap<i64, i64>,
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum Pending {
    None,
    Name,
    RootOrder,
}

impl UnityFile {
    pub fn new(objects: Vec<UnityObject>) -> UnityFile {
        let mut by_id = HashMap::with_capacity(objects.len());
        let mut transforms = HashMap::new();
        for (i, object) in objects.iter().enumerate() {
            by_id.insert(object.file_id, i);
            if object.father.is_some()
                && !object.stripped
                && let Some(go) = object.game_object
            {
                transforms.insert(go, object.file_id);
            }
        }
        UnityFile {
            objects,
            index_by_file_id: by_id,
            transform_by_game_object: transforms,
        }
    }

    pub fn object(&self, file_id: i64) -> Option<&UnityObject> {
        self.index_by_file_id
            .get(&file_id)
            .map(|&i| &self.objects[i])
    }

    pub fn index_of(&self, file_id: i64) -> Option<usize> {
        self.index_by_file_id.get(&file_id).copied()
    }

    /// The object whose block holds the offset.
    pub fn object_index_containing(&self, offset: usize) -> Option<usize> {
        self.last_index(|o| o.start <= offset)
    }

    pub fn object_index_containing_line(&self, line: usize) -> Option<usize> {
        self.last_index(|o| o.start_line <= line)
    }

    fn last_index(&self, predicate: impl Fn(&UnityObject) -> bool) -> Option<usize> {
        let mut lo: isize = 0;
        let mut hi: isize = self.objects.len() as isize - 1;
        let mut found = None;
        while lo <= hi {
            let mid = (lo + hi) / 2;
            if predicate(&self.objects[mid as usize]) {
                found = Some(mid as usize);
                lo = mid + 1;
            } else {
                hi = mid - 1;
            }
        }
        found
    }

    // MARK: - hierarchy

    /// A GameObject's path from the scene root: `["Canvas", "Panel", "Button"]`.
    /// `resolve` names an asset by GUID: nested prefabs whose name the scene
    /// did not override are named after it.
    pub fn path_of_game_object(&self, id: i64, resolve: Resolver<'_>) -> Vec<String> {
        self.game_object_path(id, resolve, 128)
    }

    /// A nested prefab's path, itself included.
    pub fn path_of_prefab_instance(&self, id: i64, resolve: Resolver<'_>) -> Vec<String> {
        self.prefab_instance_path(id, resolve, 128)
    }

    /// `budget` guards against cycles in a broken file.
    fn game_object_path(&self, id: i64, resolve: Resolver<'_>, budget: i32) -> Vec<String> {
        let Some(go) = self.object(id).filter(|_| budget > 0) else {
            return Vec::new();
        };
        if go.stripped
            && let Some(instance) = go.prefab_instance
        {
            return self.prefab_instance_path(instance, resolve, budget - 1);
        }
        let name = go.name.clone().unwrap_or_else(|| "GameObject".into());
        let father = self
            .transform_by_game_object
            .get(&id)
            .and_then(|&t| self.object(t))
            .and_then(|t| t.father);
        match father {
            Some(father) if father != 0 => {
                let mut path = self.transform_path(father, resolve, budget - 1);
                path.push(name);
                path
            }
            _ => vec![name],
        }
    }

    fn transform_path(&self, id: i64, resolve: Resolver<'_>, budget: i32) -> Vec<String> {
        let Some(transform) = self.object(id).filter(|_| budget > 0) else {
            return Vec::new();
        };
        if transform.stripped
            && let Some(instance) = transform.prefab_instance
        {
            return self.prefab_instance_path(instance, resolve, budget - 1);
        }
        match transform.game_object {
            Some(go) => self.game_object_path(go, resolve, budget - 1),
            None => Vec::new(),
        }
    }

    fn prefab_instance_path(&self, id: i64, resolve: Resolver<'_>, budget: i32) -> Vec<String> {
        let Some(instance) = self.object(id).filter(|_| budget > 0) else {
            return Vec::new();
        };
        let name = self.display_name(instance, resolve);
        match instance.transform_parent {
            Some(parent) if parent != 0 => {
                let mut path = self.transform_path(parent, resolve, budget - 1);
                path.push(name);
                path
            }
            _ => vec![name],
        }
    }

    // MARK: - names

    /// What a person calls the object: the script's name for a
    /// MonoBehaviour, the source prefab's for a nested prefab, else the type.
    pub fn display_name(&self, object: &UnityObject, resolve: Resolver<'_>) -> String {
        if object.is_prefab_instance() {
            return object
                .modified_name
                .clone()
                .or_else(|| object.source_prefab.and_then(resolve))
                .unwrap_or_else(|| "Prefab".into());
        }
        if object.is_game_object() {
            return object.name.clone().unwrap_or_else(|| "GameObject".into());
        }
        self.component_name(object, resolve)
    }

    pub fn component_name(&self, object: &UnityObject, resolve: Resolver<'_>) -> String {
        if let Some(script) = object.script {
            if let Some(name) = resolve(script) {
                return name;
            }
            if let Some(name) =
                class_name_from_editor_identifier(object.editor_class_identifier.as_deref())
            {
                return name;
            }
        }
        if object.type_name.is_empty() {
            "Object".into()
        } else {
            object.type_name.clone()
        }
    }

    /// The object described for a person: `Canvas / Button › Image`.
    pub fn describe(&self, index: usize, resolve: Resolver<'_>) -> String {
        let object = &self.objects[index];
        if object.is_game_object() {
            return self
                .game_object_path(object.file_id, resolve, 128)
                .join(" / ");
        }
        if object.is_prefab_instance() {
            return self
                .prefab_instance_path(object.file_id, resolve, 128)
                .join(" / ");
        }
        let component = self.component_name(object, resolve);
        if let Some(go) = object.game_object
            && go != 0
        {
            let path = self.game_object_path(go, resolve, 128);
            if !path.is_empty() {
                return format!("{} › {}", path.join(" / "), component);
            }
        }
        if let Some(name) = &object.name
            && *name != component
        {
            return format!("{component} \"{name}\"");
        }
        component
    }

    // MARK: - outline

    /// GameObjects, their components and nested prefabs, in file order. The
    /// container is the path in the hierarchy, so a breadcrumb reads
    /// `Canvas / Panel › Image` rather than a bare line number.
    pub fn outline(&self, resolve: Resolver<'_>) -> Vec<OutlineEntry> {
        let mut items = Vec::with_capacity(self.objects.len());
        let mut add = |name: String, kind: u8, range: Span, line: usize, path: &[String]| {
            items.push(OutlineEntry {
                name,
                kind,
                range,
                line,
                depth: path.len(),
                container: if path.is_empty() {
                    None
                } else {
                    Some(path.join(" / "))
                },
            });
        };
        for object in self.objects.iter().filter(|o| !o.stripped) {
            if object.is_game_object() {
                let mut path = self.game_object_path(object.file_id, resolve, 128);
                let name = path.pop().unwrap_or_else(|| "GameObject".into());
                add(
                    name,
                    outline_kind::GAME_OBJECT,
                    object.name_range.unwrap_or(object.type_name_range),
                    object.name_line.unwrap_or(object.type_name_line),
                    &path,
                );
            } else if object.is_prefab_instance() {
                let mut path = self.prefab_instance_path(object.file_id, resolve, 128);
                let name = path.pop().unwrap_or_else(|| "Prefab".into());
                add(
                    name,
                    outline_kind::PREFAB,
                    object.type_name_range,
                    object.type_name_line,
                    &path,
                );
            } else if let Some(go) = object.game_object.filter(|&go| go != 0) {
                let path = self.game_object_path(go, resolve, 128);
                add(
                    self.component_name(object, resolve),
                    outline_kind::COMPONENT,
                    object.type_name_range,
                    object.type_name_line,
                    &path,
                );
            } else {
                // An asset's own object: a material, a clip, an animator
                // state, a ScriptableObject, scene settings.
                let kind = self.component_name(object, resolve);
                match object.name.as_ref().filter(|n| !n.is_empty()) {
                    Some(name) => add(
                        name.clone(),
                        outline_kind::COMPONENT,
                        object.name_range.unwrap_or(object.type_name_range),
                        object.name_line.unwrap_or(object.type_name_line),
                        &[kind],
                    ),
                    None => add(
                        kind,
                        outline_kind::COMPONENT,
                        object.type_name_range,
                        object.type_name_line,
                        &[],
                    ),
                }
            }
        }
        items
    }

    // MARK: - parsing

    /// `None` when this is not a Unity serialized file (no `--- !u!` at all).
    pub fn parse<T: CodeUnit>(u: &[T]) -> Option<UnityFile> {
        let n = u.len();
        let mut objects = Vec::new();
        let mut current: Option<UnityObject> = None;
        let mut expect_type_name = false;
        // An override of a nested prefab whose `value:` is on the next line.
        let mut pending = Pending::None;
        // The items of `m_Children:` / `m_Roots:` are coming.
        let mut collecting_children = false;
        let mut line_number = 0;
        let mut i = 0;

        while i < n {
            let line_start = i;
            let mut line_end = i;
            while line_end < n && u[line_end].code() != 0x0A {
                line_end += 1;
            }
            let mut end = line_end;
            if end > line_start && u[end - 1].code() == 0x0D {
                end -= 1;
            }
            let this_line = line_number;
            i = line_end + 1;
            line_number += 1;

            if has_prefix(u, line_start, end, "--- !u!") {
                if let Some(done) = current.take() {
                    objects.push(done);
                }
                current = parse_header(u, line_start, end, this_line);
                expect_type_name = current.is_some();
                pending = Pending::None;
                collecting_children = false;
                continue;
            }
            let Some(object) = current.as_mut() else {
                continue;
            };

            if expect_type_name {
                expect_type_name = false;
                let mut j = line_start;
                while j < end && u[j].code() != 0x3A {
                    j += 1;
                }
                if j < end && j > line_start && u[line_start].code() != 0x20 {
                    object.type_name = T::decode(&u[line_start..j]);
                    object.type_name_range = Span::new(line_start, j - line_start);
                    object.type_name_line = this_line;
                }
                continue;
            }

            let mut indent = 0;
            while line_start + indent < end && u[line_start + indent].code() == 0x20 {
                indent += 1;
            }
            let k = line_start + indent;

            if pending != Pending::None {
                let was = pending;
                pending = Pending::None;
                if indent != 6 || !has_prefix(u, k, end, "value: ") {
                    continue;
                }
                if was == Pending::Name && object.modified_name.is_none() {
                    let value = scalar(u, k + 7, end);
                    if !value.is_empty() {
                        object.modified_name = Some(value);
                    }
                } else if was == Pending::RootOrder && object.root_order.is_none() {
                    object.root_order = signed_integer(u, k + 7, end).map(|(v, _)| v);
                }
                continue;
            }

            if collecting_children {
                // List items are at the same indentation as their key.
                if indent == 2 && has_prefix(u, k, end, "- ") {
                    if let Some(id) = reference(u, k, end).and_then(|r| r.0) {
                        object.children.get_or_insert_with(Vec::new).push(id);
                    }
                    continue;
                }
                collecting_children = false;
            }

            match indent {
                2 => {
                    if has_prefix(u, k, end, "m_Children:") || has_prefix(u, k, end, "m_Roots:") {
                        object.children = Some(Vec::new());
                        // `m_Children: []`: no children, no items to come.
                        collecting_children = u[end - 1].code() != 0x5D;
                    } else if has_prefix(u, k, end, "m_RootOrder: ") {
                        object.root_order = signed_integer(u, k + 13, end).map(|(v, _)| v);
                    } else if has_prefix(u, k, end, "m_IsActive: ") {
                        object.is_inactive = k + 12 < end && u[k + 12].code() == 0x30;
                    } else if has_prefix(u, k, end, "m_Name: ")
                        || (end - k == 7 && has_prefix(u, k, end, "m_Name:"))
                    {
                        let value_start = (k + 8).min(end);
                        let value = scalar(u, value_start, end);
                        if !value.is_empty() {
                            object.name = Some(value);
                            object.name_range = Some(Span::new(value_start, end - value_start));
                            object.name_line = Some(this_line);
                        }
                    } else if has_prefix(u, k, end, "m_GameObject: ") {
                        object.game_object = reference(u, k, end).and_then(|r| r.0);
                    } else if has_prefix(u, k, end, "m_Father: ") {
                        object.father = reference(u, k, end).and_then(|r| r.0);
                    } else if has_prefix(u, k, end, "m_PrefabInstance: ") {
                        object.prefab_instance = reference(u, k, end).and_then(|r| r.0);
                    } else if has_prefix(u, k, end, "m_Script: ") {
                        object.script = reference(u, k, end).and_then(|r| r.1);
                    } else if has_prefix(u, k, end, "m_SourcePrefab: ") {
                        object.source_prefab = reference(u, k, end).and_then(|r| r.1);
                    } else if has_prefix(u, k, end, "m_EditorClassIdentifier: ") {
                        let value = scalar(u, k + 25, end);
                        if !value.is_empty() {
                            object.editor_class_identifier = Some(value);
                        }
                    }
                }
                4 => {
                    if has_prefix(u, k, end, "m_TransformParent: ") {
                        object.transform_parent = reference(u, k, end).and_then(|r| r.0);
                    }
                }
                6 => {
                    if end - k == 20 && has_prefix(u, k, end, "propertyPath: m_Name") {
                        pending = Pending::Name;
                    } else if end - k == 25 && has_prefix(u, k, end, "propertyPath: m_RootOrder") {
                        pending = Pending::RootOrder;
                    }
                }
                _ => {}
            }
        }
        if let Some(done) = current {
            objects.push(done);
        }
        if objects.is_empty() {
            None
        } else {
            Some(UnityFile::new(objects))
        }
    }

    /// Where an object's block ends: the next one's start or the end of text.
    pub fn object_end(&self, index: usize, length: usize) -> usize {
        self.objects
            .get(index + 1)
            .map_or(length, |next| next.start)
            .min(length)
    }
}

/// `Unity.RenderPipelines.Universal.Runtime::UnityEngine.Rendering.Universal.UniversalAdditionalCameraData`
/// → `UniversalAdditionalCameraData`.
pub fn class_name_from_editor_identifier(identifier: Option<&str>) -> Option<String> {
    let mut id = identifier.filter(|s| !s.is_empty())?;
    if let Some(at) = id.find("::") {
        id = &id[at + 2..];
    }
    if let Some(dot) = id.rfind('.') {
        id = &id[dot + 1..];
    }
    if id.is_empty() {
        None
    } else {
        Some(id.to_string())
    }
}

/// `--- !u!114 &4862123940720277325` or `--- !u!224 &-12345 stripped`.
fn parse_header<T: CodeUnit>(
    u: &[T],
    start: usize,
    end: usize,
    line: usize,
) -> Option<UnityObject> {
    let mut j = start + 7;
    let mut class_id: i64 = 0;
    while j < end && (0x30..=0x39).contains(&u[j].code()) {
        class_id = class_id
            .wrapping_mul(10)
            .wrapping_add(i64::from(u[j].code() - 0x30));
        j += 1;
    }
    while j < end && u[j].code() == 0x20 {
        j += 1;
    }
    if j >= end || u[j].code() != 0x26 {
        return None;
    }
    let (file_id, after) = signed_integer(u, j + 1, end)?;
    let stripped = has_prefix(u, after, end, " stripped");
    let header = Span::new(start, end - start);
    Some(UnityObject {
        class_id,
        file_id,
        stripped,
        start,
        start_line: line,
        type_name_range: header,
        type_name_line: line,
        ..UnityObject::default()
    })
}

// MARK: - references

/// The reference `{fileID: …, guid: …}` in the line `start..end`.
pub fn reference<T: CodeUnit>(
    u: &[T],
    start: usize,
    end: usize,
) -> Option<(Option<i64>, Option<Guid>)> {
    let open = find(u, start, end, "{")?;
    let close = find(u, open, end, "}").unwrap_or(end);
    let file_id = find(u, open, close, "fileID: ")
        .and_then(|key| signed_integer(u, key + 8, close))
        .map(|(v, _)| v);
    let guid = find(u, open, close, "guid: ").and_then(|key| Guid::parse_at(u, key + 6));
    if file_id.is_none() && guid.is_none() {
        return None;
    }
    Some((file_id, guid))
}

/// The reference under the caret. When the caret is not inside braces but
/// the line holds exactly one reference, that one: on `m_Script:` it is
/// easier to go to definition without aiming at the GUID itself.
pub fn reference_at<T: CodeUnit>(
    u: &[T],
    line_start: usize,
    line_end: usize,
    offset: usize,
) -> Option<(Reference, Span)> {
    let mut end = line_end.min(u.len());
    while end > line_start && (u[end - 1].code() == 0x0A || u[end - 1].code() == 0x0D) {
        end -= 1;
    }
    if line_start > end {
        return None;
    }
    let mut spans: Vec<(usize, usize)> = Vec::new();
    let mut j = line_start;
    while let Some(open) = find(u, j, end, "{") {
        let close = find(u, open, end, "}").unwrap_or(end - 1);
        spans.push((open, close));
        j = close + 1;
    }
    let chosen = spans
        .iter()
        .find(|&&(open, close)| offset >= open && offset <= close + 1)
        .copied()
        .or(if spans.len() == 1 {
            Some(spans[0])
        } else {
            None
        });
    if let Some((open, close)) = chosen
        && let Some((file_id, guid)) = reference(u, open, close + 1)
    {
        let range = Span::new(open, close + 1 - open);
        if let Some(guid) = guid {
            return Some((Reference::Asset(guid, file_id), range));
        }
        if let Some(file_id) = file_id
            && file_id != 0
        {
            return Some((Reference::Local(file_id), range));
        }
        return None;
    }

    // A GUID without braces: `guid: …` in a .meta, `"GUID:…"` in an .asmdef,
    // `guid=…` in a .uxml.
    let guids = guid_ranges(u, line_start, end);
    let hit = guids
        .iter()
        .find(|(range, _)| offset >= range.location && offset <= range.end())
        .copied()
        .or(if guids.len() == 1 {
            Some(guids[0])
        } else {
            None
        });
    hit.map(|(range, guid)| (Reference::Asset(guid, None), range))
}

/// Every GUID in the range: 32 hex digits right after `guid: `, `GUID:` or `guid=`.
pub fn guid_ranges<T: CodeUnit>(u: &[T], start: usize, end: usize) -> Vec<(Span, Guid)> {
    let end = end.min(u.len());
    let mut result = Vec::new();
    let mut j = start;
    while j + 36 <= end {
        // `guid`, ignoring case.
        if u[j].code() | 0x20 == 0x67
            && u[j + 1].code() | 0x20 == 0x75
            && u[j + 2].code() | 0x20 == 0x69
            && u[j + 3].code() | 0x20 == 0x64
        {
            let mut k = j + 4;
            if k < end && (u[k].code() == 0x3A || u[k].code() == 0x3D) {
                k += 1;
            } else {
                j += 1;
                continue;
            }
            if k < end && u[k].code() == 0x20 {
                k += 1;
            }
            if k + 32 <= end
                && let Some(guid) = Guid::parse_at(u, k)
            {
                result.push((Span::new(k, 32), guid));
                j = k + 32;
                continue;
            }
        }
        j += 1;
    }
    result
}

/// Every local reference `{fileID: N}` without a GUID: the range of the number.
pub fn local_references<T: CodeUnit>(u: &[T], start: usize, end: usize) -> Vec<(Span, i64)> {
    let end = end.min(u.len());
    let mut result = Vec::new();
    let mut j = start;
    while let Some(key) = find(u, j, end, "{fileID: ") {
        let number_start = key + 9;
        let Some((value, after)) = signed_integer(u, number_start, end) else {
            j = number_start;
            continue;
        };
        if after < end && u[after].code() == 0x7D && value != 0 {
            // `}` right away: no GUID
            result.push((Span::new(number_start, after - number_start), value));
        }
        j = after;
    }
    result
}

/// The line of the header `--- !u!N &fileID` in a raw (UTF-8) file, for a
/// jump into a file that is not open yet.
pub fn anchor_line(file_id: i64, bytes: &[u8]) -> Option<usize> {
    let anchor = format!("&{file_id}").into_bytes();
    let header = b"--- !u!";
    let n = bytes.len();
    let mut line = 0;
    let mut i = 0;
    while i < n {
        if bytes[i..].starts_with(header) {
            let mut j = i + header.len();
            while j < n && bytes[j] != b'&' && bytes[j] != b'\n' {
                j += 1;
            }
            if bytes[j.min(n)..].starts_with(&anchor) {
                let after = j + anchor.len();
                if after == n || matches!(bytes[after], b'\n' | b'\r' | b' ') {
                    return Some(line);
                }
            }
        }
        while i < n && bytes[i] != b'\n' {
            i += 1;
        }
        i += 1;
        line += 1;
    }
    None
}

/// Where to land in a file not open yet: the line after the `&fileID` header,
/// with the type name (`GameObject:`, `Transform:`); its line and length.
pub fn anchor_type_line(file_id: i64, bytes: &[u8]) -> Option<(usize, usize)> {
    let header = anchor_line(file_id, bytes)?;
    let type_line = header + 1;
    let (mut line, mut i) = (0, 0);
    while i < bytes.len() && line < type_line {
        if bytes[i] == b'\n' {
            line += 1;
        }
        i += 1;
    }
    let mut length = 0;
    while i + length < bytes.len() && bytes[i + length] != b':' && bytes[i + length] != b'\n' {
        length += 1;
    }
    Some((type_line, length))
}

// MARK: - a script field's value

/// The value of serialized field `field` on the object whose `m_Script` is
/// on line `script_line`: the line `  field: …` of the same block (up to the
/// next `--- !u!`). Anything nested — a list or a struct on the lines below
/// — is `…`. `lines` are the file's lines.
pub fn serialized_field<S: AsRef<str>>(
    field: &str,
    script_line: usize,
    lines: &[S],
) -> Option<(usize, String)> {
    let key = format!("  {field}:");
    let mut index = script_line + 1;
    while index < lines.len() && !lines[index].as_ref().starts_with("--- ") {
        let line = lines[index].as_ref();
        if let Some(rest) = line.strip_prefix(&key) {
            let value = rest.trim_matches(is_space);
            if !value.is_empty() {
                return Some((index, value.to_string()));
            }
            // The value is below: `  - a` of a list or `    x: 1` of a struct.
            let next = lines.get(index + 1).map_or("", |s| s.as_ref());
            let nested = next.starts_with("  - ") || next.starts_with("    ");
            return Some((index, if nested { "…".into() } else { String::new() }));
        }
        index += 1;
    }
    None
}

// MARK: - primitives

fn has_prefix<T: CodeUnit>(u: &[T], start: usize, end: usize, prefix: &str) -> bool {
    let p = prefix.as_bytes();
    if start + p.len() > end {
        return false;
    }
    p.iter()
        .enumerate()
        .all(|(k, &b)| u[start + k].code() == u32::from(b))
}

fn find<T: CodeUnit>(u: &[T], start: usize, end: usize, needle: &str) -> Option<usize> {
    let count = needle.len();
    if count == 0 || end < start || end - start < count {
        return None;
    }
    let first = u32::from(needle.as_bytes()[0]);
    let mut j = start;
    while j + count <= end {
        if u[j].code() == first && has_prefix(u, j, end, needle) {
            return Some(j);
        }
        j += 1;
    }
    None
}

fn signed_integer<T: CodeUnit>(u: &[T], start: usize, end: usize) -> Option<(i64, usize)> {
    let mut j = start;
    let mut negative = false;
    if j < end && u[j].code() == 0x2D {
        negative = true;
        j += 1;
    }
    let digits_start = j;
    let mut value: i64 = 0;
    while j < end && (0x30..=0x39).contains(&u[j].code()) {
        value = value
            .wrapping_mul(10)
            .wrapping_add(i64::from(u[j].code() - 0x30));
        j += 1;
    }
    if j == digits_start {
        return None;
    }
    Some((
        if negative {
            value.wrapping_neg()
        } else {
            value
        },
        j,
    ))
}

/// A scalar value without surrounding spaces and quotes.
fn scalar<T: CodeUnit>(u: &[T], start: usize, end: usize) -> String {
    let (mut s, mut e) = (start, end);
    while s < e && u[s].code() == 0x20 {
        s += 1;
    }
    while e > s && u[e - 1].code() == 0x20 {
        e -= 1;
    }
    if e - s >= 2
        && ((u[s].code() == 0x27 && u[e - 1].code() == 0x27)
            || (u[s].code() == 0x22 && u[e - 1].code() == 0x22))
    {
        s += 1;
        e -= 1;
    }
    if s < e {
        T::decode(&u[s..e])
    } else {
        String::new()
    }
}

/// Whether a code unit is a hexadecimal digit.
pub fn is_hex<T: CodeUnit>(c: T) -> bool {
    hex_value(c.code()).is_some()
}
