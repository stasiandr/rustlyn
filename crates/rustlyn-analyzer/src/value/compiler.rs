//! What the value graph asks the project's compiler, and the shape of the
//! answers. [`rustlyn_ide::Session`] answers it here (`impl Compiler for
//! Session`); a host with its own wrapper around the session implements
//! [`Compiler`] for that.
//!
//! Positions follow [`rustlyn_ide::session::Location`]: a zero-based line
//! and a column in UTF-16 code units, which is how the session counts.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;

use rustlyn_ide::Session;
use rustlyn_ide::session::Location;

use super::flow::Utf16Range;

/// What a declaration declares: [`rustlyn_ide::outline::DeclarationKind`].
pub use rustlyn_ide::outline::DeclarationKind as DeclKind;

/// A kind from its number, as `DeclarationKind` numbers them.
#[must_use]
pub const fn decl_kind(raw: u8) -> Option<DeclKind> {
    use DeclKind::{
        Class, Constructor, Delegate, Destructor, Enum, EnumMember, Event, Extension, Field,
        Indexer, Interface, Method, Namespace, Operator, Property, Record, Struct,
    };
    Some(match raw {
        0 => Namespace,
        1 => Class,
        2 => Struct,
        3 => Interface,
        4 => Enum,
        5 => Record,
        6 => Delegate,
        7 => Method,
        8 => Constructor,
        9 => Destructor,
        10 => Property,
        11 => Indexer,
        12 => Field,
        13 => Event,
        14 => EnumMember,
        15 => Operator,
        16 => Extension,
        _ => return None,
    })
}

/// The kind's name, as `--definition` prints it.
#[must_use]
pub const fn kind_name(kind: DeclKind) -> &'static str {
    match kind {
        DeclKind::Namespace => "namespace",
        DeclKind::Class => "class",
        DeclKind::Struct => "struct",
        DeclKind::Interface => "interface",
        DeclKind::Enum => "enum",
        DeclKind::Record => "record",
        DeclKind::Delegate => "delegate",
        DeclKind::Method => "method",
        DeclKind::Constructor => "constructor",
        DeclKind::Destructor => "destructor",
        DeclKind::Property => "property",
        DeclKind::Indexer => "indexer",
        DeclKind::Field => "field",
        DeclKind::Event => "event",
        DeclKind::EnumMember => "enumMember",
        DeclKind::Operator => "operator",
        DeclKind::Extension => "extensionBlock",
    }
}

/// A declaration one can jump to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    /// Absolute: a project file or an assembly.
    pub path: String,
    /// The full name: `Game.Pawn.Health`.
    pub name: String,
    pub line: usize,
    /// UTF-16 code units from the start of the line.
    pub character: usize,
    pub length: usize,
    pub kind: DeclKind,
}

impl Target {
    /// The short name: `Health` of `Game.Pawn.Health`.
    #[must_use]
    pub fn short_name(&self) -> String {
        self.name
            .split('.')
            .rfind(|p| !p.is_empty())
            .unwrap_or(&self.name)
            .to_owned()
    }

    /// What holds the declaration: `Game.Pawn` of `Game.Pawn.Health`.
    #[must_use]
    pub fn container(&self) -> Option<String> {
        self.name.rfind('.').map(|dot| self.name[..dot].to_owned())
    }
}

/// A declaration in a file's outline, as the parser read it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    pub name: String,
    pub kind: DeclKind,
    /// The enclosing type or namespace, fully qualified.
    pub container: Option<String>,
    /// A field's or property's type, a method's return type, as written.
    pub type_text: Option<String>,
    pub bases: Vec<String>,
    /// Attributes without the `Attribute` suffix.
    pub attributes: Vec<String>,
    /// Parameters, each as `type name`.
    pub parameters: Vec<String>,
    /// The name's range in the document.
    pub name_range: Utf16Range,
    /// The whole declaration.
    pub full_range: Utf16Range,
    pub is_extension_method: bool,
}

/// A file's outline.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Outline {
    pub declarations: Vec<Declaration>,
}

/// The project's compiler. Called on the thread the graph is built on.
pub trait Compiler: Send + Sync {
    /// Where the name at `offset` (UTF-16) leads. `text`: the file's text
    /// when it differs from the disk.
    fn definition(&self, path: &str, offset: usize, text: Option<&str>) -> Vec<Target>;
    /// Every mention of the name.
    fn references(&self, path: &str, offset: usize, text: Option<&str>) -> Vec<Target>;
    /// The implementations and overrides of a member.
    fn implementations(&self, path: &str, offset: usize) -> Vec<Target>;
    /// The outline of an open file; `None`: the file is not open.
    fn outline(&self, path: &str) -> Option<Outline>;
    /// Open a file for the time of an analysis.
    fn open(&self, path: &str) -> bool;
    fn close(&self, path: &str);
}

/// Lines of prefabs and scenes where an inspector field is set — found by
/// whoever knows the Unity project (its GUIDs, its assets). `lines` are the
/// file's lines from number `first`; `line` is among them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InspectorHit {
    pub path: String,
    pub title: String,
    pub line: usize,
    pub first: usize,
    pub lines: Vec<String>,
}

/// Finding the values of a Unity inspector field: the project's root, the
/// script's file, the field's name and how to title it.
pub trait Inspector: Send + Sync {
    fn values(&self, root: &str, script: &str, field: &str, title: &str) -> Vec<InspectorHit>;
}

/// Lines and columns of the session's locations, with absolute paths. A
/// kind the graph does not know counts as a class.
#[must_use]
pub fn targets(root: &Path, locations: &[Location]) -> Vec<Target> {
    locations
        .iter()
        .map(|l| Target {
            path: absolute(root, &l.path),
            name: l.name.clone(),
            line: l.line as usize,
            character: l.character as usize,
            length: l.length as usize,
            kind: l.kind,
        })
        .collect()
}

/// A path the session gave, made absolute: a project file from the root,
/// anything outside it (an assembly) as it is.
#[must_use]
pub fn absolute(root: &Path, path: &Path) -> String {
    if path.is_absolute() {
        path.to_string_lossy().into_owned()
    } else {
        root.join(path).to_string_lossy().into_owned()
    }
}

/// An outline in the graph's terms: ranges in UTF-16, lists without empty
/// items, absent texts `None`.
#[must_use]
pub fn outline_of(file: &rustlyn_ide::FileOutline, document: &rustlyn_ide::Document) -> Outline {
    let map = document.utf16();
    let declarations = file
        .declarations
        .iter()
        .map(|d| {
            let (name_start, name_length) = map.span(d.name_span);
            let (full_start, full_length) = map.span(d.full_span);
            let parameters: Vec<String> = d
                .parameters
                .iter()
                .map(|p| format!("{} {}", p.type_text, p.name))
                .collect();
            Declaration {
                name: d.name.clone(),
                kind: d.kind,
                container: present(d.container.as_deref()),
                type_text: present(d.type_text.as_deref()),
                bases: list(&d.bases),
                attributes: list(&d.attributes),
                parameters: list(&parameters),
                name_range: Utf16Range::new(name_start as usize, name_length as usize),
                full_range: Utf16Range::new(full_start as usize, full_length as usize),
                is_extension_method: d.is_extension_method(),
            }
        })
        .collect();
    Outline { declarations }
}

/// A list without empty items: what joining with `\n` and splitting back
/// leaves of it.
fn list(items: &[String]) -> Vec<String> {
    let joined = items.join("\n");
    if joined.is_empty() {
        Vec::new()
    } else {
        joined.split('\n').map(str::to_owned).collect()
    }
}

/// An empty text is no text.
fn present(text: Option<&str>) -> Option<String> {
    text.filter(|t| !t.is_empty()).map(str::to_owned)
}

/// An offset for the session, whose positions are `u32`.
fn offset32(offset: usize) -> u32 {
    u32::try_from(offset).unwrap_or(u32::MAX)
}

/// Ask the session on a deep stack, a panic turned into no answer.
fn ask<T: Send>(body: impl FnOnce() -> Option<T> + Send) -> Option<T> {
    catch_unwind(AssertUnwindSafe(|| crate::deep::run(body))).ok()?
}

impl Compiler for Session {
    fn definition(&self, path: &str, offset: usize, text: Option<&str>) -> Vec<Target> {
        ask(|| self.definition_in(path, offset32(offset), text).ok())
            .map(|d| targets(self.root(), &d.targets))
            .unwrap_or_default()
    }

    fn references(&self, path: &str, offset: usize, text: Option<&str>) -> Vec<Target> {
        ask(|| self.references(path, offset32(offset), text).ok())
            .map(|u| targets(self.root(), &u.locations))
            .unwrap_or_default()
    }

    fn implementations(&self, path: &str, offset: usize) -> Vec<Target> {
        ask(|| Self::implementations(self, path, offset32(offset)).ok())
            .map(|found| targets(self.root(), &found))
            .unwrap_or_default()
    }

    fn outline(&self, path: &str) -> Option<Outline> {
        ask(|| {
            let file = Self::outline(self, path).ok()?;
            let document = self.document(path)?;
            Some(outline_of(&file, &document))
        })
    }

    fn open(&self, path: &str) -> bool {
        ask(|| Self::open(self, path).ok().map(drop)).is_some()
    }

    fn close(&self, path: &str) {
        Self::close(self, path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::testing::TempDir;

    /// The session answers the graph with absolute paths and UTF-16
    /// positions, and an outline only for an open file.
    #[test]
    fn the_session_as_the_graphs_compiler() {
        let dir = TempDir::new("compiler");
        let text = "namespace Game {\n    // A pawn\n    public class Pawn : Base {\n        [Header(\"x\")] public int Health;\n        public void Heal(int by) { Health += by; }\n    }\n    public class Base { }\n}\n";
        dir.write("Pawn.cs", text);
        let root = dir.canonical();
        let path = Path::new(&root)
            .join("Pawn.cs")
            .to_string_lossy()
            .into_owned();
        let session = Session::new(&root, None, Vec::new());
        session.reindex(&[std::path::PathBuf::from(&path)]);
        let compiler: &dyn Compiler = &session;

        assert!(
            compiler.outline(&path).is_none(),
            "a closed file has no outline"
        );
        assert!(compiler.open(&path));
        let outline = compiler.outline(&path).expect("an outline");
        let health = outline
            .declarations
            .iter()
            .find(|d| d.name == "Health")
            .expect("the field");
        let at = text[..text.find("Health;").expect("present")]
            .encode_utf16()
            .count();
        assert_eq!(health.name_range, Utf16Range::new(at, 6));
        assert_eq!(health.kind, DeclKind::Field);
        assert_eq!(health.container.as_deref(), Some("Game.Pawn"));
        assert_eq!(health.attributes, vec!["Header".to_owned()]);
        assert_eq!(health.type_text.as_deref(), Some("int"));
        let pawn = outline
            .declarations
            .iter()
            .find(|d| d.name == "Pawn")
            .expect("the class");
        assert_eq!(pawn.bases, vec!["Base".to_owned()]);
        assert!(pawn.attributes.is_empty() && pawn.type_text.is_none());
        let heal = outline
            .declarations
            .iter()
            .find(|d| d.name == "Heal")
            .expect("the method");
        assert_eq!(heal.parameters, vec!["int by".to_owned()]);

        let base = text.find(": Base").expect("present") + 2;
        let found = compiler.definition(&path, text[..base].encode_utf16().count(), None);
        let target = found.first().expect("a target");
        assert_eq!(target.path, path, "the path is absolute");
        assert_eq!(
            (target.line, target.kind, target.name.as_str()),
            (6, DeclKind::Class, "Game.Base")
        );
        compiler.close(&path);
        assert!(compiler.outline(&path).is_none());
    }
}
