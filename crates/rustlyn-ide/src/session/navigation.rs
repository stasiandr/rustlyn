//! The navigation an editor offers past "go to definition" and "find
//! references", in the editor's units: go to type definition, go to base,
//! go to implementation, find derived types, call hierarchy, type hierarchy
//! and Navigate To.
//!
//! The answers are worked out in [`crate::semantic`] and [`crate::search`],
//! in bytes; this is where they become lines and UTF-16 columns. A hierarchy
//! is asked about in two steps, as LSP does: first the item at the cursor,
//! then — as the tree is expanded — the items around it, named by the item's
//! key. A key names a symbol rather than a place, so an item still expands
//! after the file it is in has been edited and the project compiled again.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rustlyn_text::TextSpan;

use super::{Definition, Location, Refusal, Session};
use crate::outline::DeclarationKind;
use crate::search::{MatchKind, SearchKind, Target, search};
use crate::semantic::{Found, HierarchyItem, Place, Semantic, UseKind};

/// From one line and column to another, in the editor's units: the columns
/// in UTF-16 code units.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct LineRange {
    pub start_line: u32,
    pub start_character: u32,
    pub end_line: u32,
    pub end_character: u32,
}

/// A node of a call or type hierarchy.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Item {
    pub name: String,
    pub kind: DeclarationKind,
    /// The signature: `double Area()`, `class Circle`.
    pub detail: String,
    /// The qualified name of the type or namespace it is in.
    pub container: String,
    /// What to pass back to expand it: [`Session::incoming_calls`] and the
    /// rest.
    pub key: String,
    /// Its name, which is what a jump selects. `None` for what has nowhere
    /// to go.
    pub location: Option<Location>,
    /// The whole declaration, in the same file. For a declaration in an
    /// assembly, the name's line.
    pub range: Option<LineRange>,
}

/// One caller or callee, with where the calls are.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Call {
    /// The member calling, for incoming calls; the member called, for
    /// outgoing ones.
    pub item: Item,
    /// The file the calls are in — the caller's — relative to the root.
    pub path: PathBuf,
    /// The name of each call.
    pub ranges: Vec<LineRange>,
    /// How each of `ranges` uses the member, in the same order: a property's
    /// getter and setter are different code.
    pub uses: Vec<UseKind>,
    /// Whether these calls name a member the one asked about overrides or
    /// implements: they may run it, and may not.
    pub through_base: bool,
}

/// One Navigate To result.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SearchResult {
    /// Where to go. For a file, its first line.
    pub location: Location,
    /// The name as matched: a declaration's own name, or a file's name.
    pub name: String,
    /// The type or namespace it is in, qualified; empty for a file.
    pub container: String,
    pub is_file: bool,
    pub match_kind: MatchKind,
    pub case_sensitive: bool,
    /// The UTF-16 ranges of `name` that matched, for highlighting.
    pub ranges: Vec<(u32, u32)>,
}

impl Session {
    // MARK: - places

    /// Where the type of what is at `offset` is declared: a variable's
    /// type, a member's, a call's result; an array's element type and a
    /// generic type's arguments too.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and off a name.
    pub fn type_definition(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Definition, Refusal> {
        self.semantic_places(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.type_definition(path, byte, text)
        })
    }

    /// What what is at `offset` derives from: a type's base classes and
    /// interfaces, a member's overridden and implemented members. Nearest
    /// first.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and off a name.
    pub fn bases(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Definition, Refusal> {
        self.semantic_places(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.bases(path, byte, text)
        })
    }

    /// What implements what is at `offset`, from the compiler once the
    /// project is compiled: the concrete types that implement an interface
    /// or derive from a class, and the members with a body that override or
    /// implement a member. Before that, the index's guess from
    /// [`Self::implementations`].
    ///
    /// # Errors
    ///
    /// Off a name; before the project is indexed, when the compiler cannot
    /// answer either.
    pub fn implementations_in(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Definition, Refusal> {
        let path = path.as_ref();
        match self.semantic_places(path, offset, text, |semantic, path, byte, text| {
            semantic.implementations(path, byte, text)
        }) {
            Err(Refusal::NotCompiled) => {}
            answer => return answer,
        }
        let edited = text.is_some_and(|text| {
            self.document(path)
                .is_none_or(|document| document.text() != text)
        });
        if edited {
            return Err(Refusal::NotCompiled);
        }
        let targets = self.implementations(path, offset)?;
        Ok(Definition {
            word: String::new(),
            certain: false,
            targets,
        })
    }

    /// The types that derive from the type at `offset`, however
    /// indirectly: its derived classes and implementing types, or with
    /// `interfaces` the interfaces that extend it.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and off a name.
    pub fn derived_types(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
        interfaces: bool,
    ) -> Result<Definition, Refusal> {
        self.semantic_places(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.derived_types(path, byte, text, interfaces)
        })
    }

    /// Asks the compiler a question whose answer is places, and puts them
    /// in the editor's units. An empty answer is an answer: a type with no
    /// derived types has none.
    fn semantic_places(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        question: impl FnOnce(&Semantic, &Path, u32, Option<&str>) -> Option<(String, Vec<Found>)>,
    ) -> Result<Definition, Refusal> {
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = crate::utf16::Utf16Map::new(&here).to_byte(offset);
        let (word, found) = question(&semantic, path, byte, text).ok_or(Refusal::NotAName)?;
        let targets: Vec<Location> = found
            .iter()
            .filter_map(|found| self.place_location(&semantic, path, &here, text.is_some(), found))
            .collect();
        Ok(Definition {
            word,
            certain: targets.len() == 1,
            targets,
        })
    }

    // MARK: - call hierarchy

    /// The method, constructor, property, event or field at `offset`, as
    /// the root of a call hierarchy.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, off a name, and on a name that
    /// is not something called.
    pub fn call_hierarchy(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Item, Refusal> {
        self.hierarchy_root(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.call_hierarchy_item(path, byte, text)
        })
    }

    /// Who calls the member `key` names, and where: every member of the
    /// project whose body calls it, then those that call what it overrides
    /// or implements, marked as such.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and for a key that names
    /// nothing in it any more.
    pub fn incoming_calls(&self, key: &str) -> Result<Vec<Call>, Refusal> {
        let semantic = self.semantic().ok_or(Refusal::NotCompiled)?;
        let symbol = semantic
            .symbol_by_key(key)
            .ok_or_else(|| Refusal::NotInProject(key.to_owned()))?;
        let calls = semantic.incoming_calls(symbol);
        let mut texts = Texts::default();
        Ok(calls
            .into_iter()
            .map(|call| {
                let text = texts.get(self, &semantic, &call.path);
                let (ranges, uses) = call
                    .spans
                    .iter()
                    .zip(&call.uses)
                    .filter_map(|(&span, &kind)| Some((line_range(text, span)?, kind)))
                    .unzip();
                Call {
                    item: self.item(&semantic, &mut texts, &call.from),
                    ranges,
                    uses,
                    path: self.relative(&call.path),
                    through_base: call.through_base,
                }
            })
            .collect())
    }

    /// What the member `key` names calls, and where, in the order first
    /// called.
    ///
    /// # Errors
    ///
    /// As for [`Self::incoming_calls`].
    pub fn outgoing_calls(&self, key: &str) -> Result<Vec<Call>, Refusal> {
        let semantic = self.semantic().ok_or(Refusal::NotCompiled)?;
        let symbol = semantic
            .symbol_by_key(key)
            .ok_or_else(|| Refusal::NotInProject(key.to_owned()))?;
        let calls = semantic.outgoing_calls(symbol);
        let mut texts = Texts::default();
        Ok(calls
            .into_iter()
            .map(|call| {
                let ranges = self.ranges_in(&semantic, &mut texts, &call.path, &call.spans);
                Call {
                    item: self.item(&semantic, &mut texts, &call.to),
                    uses: vec![UseKind::Call; ranges.len()],
                    ranges,
                    path: self.relative(&call.path),
                    through_base: false,
                }
            })
            .collect())
    }

    // MARK: - type hierarchy

    /// The type at `offset` — or the type of the variable or member there —
    /// as the root of a type hierarchy.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled, and off a name.
    pub fn type_hierarchy(
        &self,
        path: impl AsRef<Path>,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Item, Refusal> {
        self.hierarchy_root(path.as_ref(), offset, text, |semantic, path, byte, text| {
            semantic.type_hierarchy_item(path, byte, text)
        })
    }

    /// The base class and interfaces of the type `key` names, one level
    /// up, those in assemblies among them.
    ///
    /// # Errors
    ///
    /// As for [`Self::incoming_calls`].
    pub fn supertypes(&self, key: &str) -> Result<Vec<Item>, Refusal> {
        self.related_items(key, Semantic::supertypes_of)
    }

    /// The types of the project that derive from the type `key` names, or
    /// implement it, one level down.
    ///
    /// # Errors
    ///
    /// As for [`Self::incoming_calls`].
    pub fn subtypes(&self, key: &str) -> Result<Vec<Item>, Refusal> {
        self.related_items(key, Semantic::subtypes_of)
    }

    fn hierarchy_root(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        question: impl FnOnce(&Semantic, &Path, u32, Option<&str>) -> Option<HierarchyItem>,
    ) -> Result<Item, Refusal> {
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let byte = crate::utf16::Utf16Map::new(&here).to_byte(offset);
        let item = question(&semantic, path, byte, text).ok_or(Refusal::NotAName)?;
        let mut texts = Texts::default();
        if text.is_some() {
            texts.0.insert(path.to_path_buf(), here);
        }
        Ok(self.item(&semantic, &mut texts, &item))
    }

    fn related_items(
        &self,
        key: &str,
        question: impl FnOnce(&Semantic, rustlyn_semantics::SymbolId) -> Vec<HierarchyItem>,
    ) -> Result<Vec<Item>, Refusal> {
        let semantic = self.semantic().ok_or(Refusal::NotCompiled)?;
        let symbol = semantic
            .symbol_by_key(key)
            .ok_or_else(|| Refusal::NotInProject(key.to_owned()))?;
        let mut texts = Texts::default();
        Ok(question(&semantic, symbol)
            .iter()
            .map(|item| self.item(&semantic, &mut texts, item))
            .collect())
    }

    /// A hierarchy item in the editor's units.
    fn item(&self, semantic: &Semantic, texts: &mut Texts, item: &HierarchyItem) -> Item {
        let found = item.place.clone().map(|place| Found {
            place,
            kind: item.kind,
            name: if item.container.is_empty() {
                item.name.clone()
            } else {
                format!("{}.{}", item.container, item.name)
            },
        });
        let (location, range) = match &found {
            Some(
                found @ Found {
                    place: Place::Source { path, span },
                    ..
                },
            ) => {
                let text = texts.get(self, semantic, path);
                let location = self.location_in(path, text, *span, found.kind, &found.name);
                let range = line_range(text, item.full.unwrap_or(*span));
                (location, range)
            }
            Some(found) => {
                let location = self.place_location(semantic, Path::new(""), "", false, found);
                let range = location.as_ref().map(|location| LineRange {
                    start_line: location.line,
                    start_character: location.character,
                    end_line: location.line,
                    end_character: location.character + location.length,
                });
                (location, range)
            }
            None => (None, None),
        };
        Item {
            name: item.name.clone(),
            kind: item.kind,
            detail: item.detail.clone(),
            container: item.container.clone(),
            key: item.key.clone(),
            location,
            range,
        }
    }

    fn ranges_in(
        &self,
        semantic: &Semantic,
        texts: &mut Texts,
        path: &Path,
        spans: &[TextSpan],
    ) -> Vec<LineRange> {
        let text = texts.get(self, semantic, path);
        spans
            .iter()
            .filter_map(|&span| line_range(text, span))
            .collect()
    }

    fn relative(&self, path: &Path) -> PathBuf {
        path.strip_prefix(&self.root).unwrap_or(path).to_path_buf()
    }

    // MARK: - navigate to

    /// Declarations and files whose names `pattern` matches, best first, at
    /// most `limit` of them: Roslyn's Navigate To. Answers from the index,
    /// so it works before the project is compiled.
    ///
    /// # Errors
    ///
    /// Fails before the project is indexed.
    pub fn search(
        &self,
        pattern: &str,
        kind: SearchKind,
        limit: usize,
    ) -> Result<Vec<SearchResult>, Refusal> {
        let index = self.index();
        if index.is_empty() {
            return Err(Refusal::NotIndexed);
        }
        let hits = search(&index, pattern, kind, limit);
        // Each file read once, however many results are in it.
        let mut texts: HashMap<u32, Option<String>> = HashMap::new();
        let mut text_of = |file: u32| -> Option<String> {
            texts
                .entry(file)
                .or_insert_with(|| {
                    let absolute = self.root.join(&index.files().get(file as usize)?.path);
                    self.document(&absolute)
                        .map(|document| document.text().to_owned())
                        .or_else(|| std::fs::read_to_string(&absolute).ok())
                })
                .clone()
        };
        let utf16 = |name: &str, ranges: &[(u32, u32)]| -> Vec<(u32, u32)> {
            let at = |byte: u32| {
                name.get(..byte as usize)
                    .map_or(byte, |before| before.encode_utf16().count() as u32)
            };
            ranges
                .iter()
                .map(|&(start, end)| (at(start), at(end)))
                .collect()
        };
        let mut results = Vec::with_capacity(hits.len());
        for hit in hits {
            match hit.target {
                Target::Entry(id) => {
                    let Some(entry) = index.entry(id) else {
                        continue;
                    };
                    let Some(file) = index.files().get(entry.file as usize) else {
                        continue;
                    };
                    let declaration = &entry.declaration;
                    let Some(text) = text_of(entry.file) else {
                        continue;
                    };
                    let Some(location) = self.location_in(
                        &self.root.join(&file.path),
                        &text,
                        declaration.name_span,
                        declaration.kind,
                        &declaration.qualified_name(),
                    ) else {
                        continue;
                    };
                    results.push(SearchResult {
                        location,
                        name: declaration.name.clone(),
                        container: declaration.container.clone().unwrap_or_default(),
                        is_file: false,
                        match_kind: hit.kind,
                        case_sensitive: hit.case_sensitive,
                        ranges: utf16(&declaration.name, &hit.ranges),
                    });
                }
                Target::File(id) => {
                    let Some(file) = index.files().get(id as usize) else {
                        continue;
                    };
                    let name = file
                        .path
                        .file_name()
                        .map(|name| name.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    results.push(SearchResult {
                        location: Location {
                            path: file.path.clone(),
                            line: 0,
                            character: 0,
                            length: 0,
                            kind: DeclarationKind::Namespace,
                            name: file.path.to_string_lossy().into_owned(),
                        },
                        ranges: utf16(&name, &hit.ranges),
                        name,
                        container: String::new(),
                        is_file: true,
                        match_kind: hit.kind,
                        case_sensitive: hit.case_sensitive,
                    });
                }
            }
        }
        Ok(results)
    }
}

/// The texts of the files a hierarchy answer mentions, each read once.
#[derive(Default)]
struct Texts(HashMap<PathBuf, String>);

impl Texts {
    fn get(&mut self, session: &Session, semantic: &Semantic, path: &Path) -> &str {
        self.0
            .entry(path.to_path_buf())
            .or_insert_with(|| session.text_of(semantic, path, None).unwrap_or_default())
    }
}

/// A byte span of `text` as lines and UTF-16 columns.
fn line_range(text: &str, span: TextSpan) -> Option<LineRange> {
    let place = |offset: usize| -> Option<(u32, u32)> {
        let before = text.get(..offset)?;
        let line_start = before.rfind('\n').map_or(0, |at| at + 1);
        Some((
            before.bytes().filter(|&byte| byte == b'\n').count() as u32,
            before[line_start..].encode_utf16().count() as u32,
        ))
    };
    let (start_line, start_character) = place(span.start() as usize)?;
    let (end_line, end_character) = place(span.end() as usize)?;
    Some(LineRange {
        start_line,
        start_character,
        end_line,
        end_character,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "rustlyn-navigation-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).expect("a temporary directory");
            Self(path)
        }

        fn write(&self, name: &str, text: &str) -> PathBuf {
            let path = self.0.join(name);
            std::fs::write(&path, text).expect("writing");
            path
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    // Cyrillic above the code, so that a byte offset and a UTF-16 one differ.
    const SHAPES: &str = "// фигуры\npublic interface IShape { double Area(); }\npublic abstract class Shape : IShape { public abstract double Area(); }\npublic class Circle : Shape\n{\n    public double R;\n    public Circle(double r) { R = r; }\n    public override double Area() { return 3 * R * R; }\n}\n";
    const USE: &str = "// рисунок\npublic class Canvas\n{\n    public double Draw(IShape shape) { var c = new Circle(1); return shape.Area() + c.Area(); }\n}\n";

    fn units(text: &str, marker: &str) -> u32 {
        text[..text.find(marker).expect("marker")]
            .encode_utf16()
            .count() as u32
    }

    fn compiled(dir: &TempDir) -> (Session, PathBuf, PathBuf) {
        let shapes = dir.write("Shapes.cs", SHAPES);
        let canvas = dir.write("Canvas.cs", USE);
        let session = Session::new(&dir.0, None, Vec::new());
        session.reindex(&[shapes.clone(), canvas.clone()]);
        session.compile(&[shapes.clone(), canvas.clone()]);
        (session, shapes, canvas)
    }

    #[test]
    fn places_come_back_in_the_editors_units() {
        let dir = TempDir::new("places");
        let (session, shapes, canvas) = compiled(&dir);

        let found = session
            .type_definition(&canvas, units(USE, "c.Area"), None)
            .expect("an answer");
        assert_eq!(found.targets.len(), 1);
        let target = &found.targets[0];
        assert_eq!(target.path, PathBuf::from("Shapes.cs"));
        assert_eq!(target.name, "Circle");
        assert_eq!(
            (target.line, target.character),
            (3, units("public class Circle", "Circle"))
        );

        let bases = session
            .bases(&shapes, units(SHAPES, "Area() { return"), None)
            .expect("an answer");
        let names: Vec<&str> = bases
            .targets
            .iter()
            .map(|target| target.name.as_str())
            .collect();
        assert_eq!(names, vec!["Shape.Area", "IShape.Area"]);

        let implementations = session
            .implementations_in(&shapes, units(SHAPES, "IShape {"), None)
            .expect("an answer");
        let names: Vec<&str> = implementations
            .targets
            .iter()
            .map(|target| target.name.as_str())
            .collect();
        assert_eq!(names, vec!["Circle"]);

        let derived = session
            .derived_types(&shapes, units(SHAPES, "IShape {"), None, false)
            .expect("an answer");
        assert_eq!(derived.targets.len(), 2);
    }

    #[test]
    fn before_compiling_implementations_come_from_the_index() {
        let dir = TempDir::new("index");
        let shapes = dir.write("Shapes.cs", SHAPES);
        let session = Session::new(&dir.0, None, Vec::new());
        session.reindex(std::slice::from_ref(&shapes));
        session.open(&shapes).expect("open");
        assert_eq!(
            session.bases(&shapes, units(SHAPES, "Circle :"), None),
            Err(Refusal::NotCompiled)
        );
        let found = session
            .implementations_in(&shapes, units(SHAPES, "Shape :"), None)
            .expect("the index's answer");
        assert!(found.targets.iter().any(|target| target.name == "Circle"));
    }

    #[test]
    fn a_call_hierarchy_expands_by_key() {
        let dir = TempDir::new("calls");
        let (session, _, canvas) = compiled(&dir);
        let root = session
            .call_hierarchy(&canvas, units(USE, "c.Area") + 2, None)
            .expect("an item");
        assert_eq!(root.name, "Area");
        assert_eq!(root.container, "Circle");
        let location = root.location.as_ref().expect("a place");
        assert_eq!(location.path, PathBuf::from("Shapes.cs"));
        assert_eq!(location.line, 7);
        let range = root.range.expect("a range");
        assert_eq!((range.start_line, range.end_line), (7, 7));
        assert_eq!(range.start_character, 4);

        let incoming = session.incoming_calls(&root.key).expect("callers");
        assert_eq!(incoming.len(), 2, "{incoming:?}");
        assert_eq!(incoming[0].item.name, "Draw");
        assert!(!incoming[0].through_base);
        assert!(incoming[1].through_base);
        assert_eq!(incoming[0].path, PathBuf::from("Canvas.cs"));
        let call = incoming[0].ranges[0];
        assert_eq!(call.start_line, 3);
        let line = USE.lines().nth(3).expect("line");
        assert_eq!(call.start_character, units(line, "Area(); }"));

        let draw = &incoming[0].item;
        let outgoing = session.outgoing_calls(&draw.key).expect("callees");
        let names: Vec<(&str, usize)> = outgoing
            .iter()
            .map(|call| (call.item.name.as_str(), call.ranges.len()))
            .collect();
        assert_eq!(names, vec![("Circle", 1), ("Area", 1), ("Area", 1)]);

        assert_eq!(
            session.incoming_calls("M:Nowhere|Gone`0()"),
            Err(Refusal::NotInProject("M:Nowhere|Gone`0()".to_string()))
        );
    }

    #[test]
    fn a_type_hierarchy_expands_both_ways() {
        let dir = TempDir::new("types");
        let (session, shapes, _) = compiled(&dir);
        let root = session
            .type_hierarchy(&shapes, units(SHAPES, "Shape :"), None)
            .expect("an item");
        assert_eq!(root.name, "Shape");
        let up: Vec<String> = session
            .supertypes(&root.key)
            .expect("up")
            .into_iter()
            .map(|item| item.name)
            .collect();
        assert_eq!(up, vec!["Object", "IShape"]);
        let down: Vec<String> = session
            .subtypes(&root.key)
            .expect("down")
            .into_iter()
            .map(|item| item.name)
            .collect();
        assert_eq!(down, vec!["Circle"]);
    }

    #[test]
    fn navigate_to_answers_from_the_index_with_utf16_places() {
        let dir = TempDir::new("search");
        let shapes = dir.write("Shapes.cs", SHAPES);
        let session = Session::new(&dir.0, None, Vec::new());
        assert_eq!(
            session.search("ci", SearchKind::All, 10),
            Err(Refusal::NotIndexed)
        );
        session.reindex(std::slice::from_ref(&shapes));
        let results = session
            .search("ci", SearchKind::Types, 10)
            .expect("results");
        assert_eq!(results.len(), 1);
        let circle = &results[0];
        assert_eq!(circle.name, "Circle");
        assert_eq!(circle.match_kind, MatchKind::Prefix);
        assert_eq!(circle.ranges, vec![(0, 2)]);
        assert_eq!(circle.location.path, PathBuf::from("Shapes.cs"));
        assert_eq!((circle.location.line, circle.location.character), (3, 13));

        let files = session
            .search("shap", SearchKind::Files, 10)
            .expect("files");
        assert_eq!(files.len(), 1);
        assert!(files[0].is_file);
        assert_eq!(files[0].name, "Shapes.cs");
    }
}
