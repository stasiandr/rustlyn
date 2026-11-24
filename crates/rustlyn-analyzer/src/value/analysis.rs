//! The searches behind the value graph, run in the background on the
//! project compiler's queue. The compiler says where a name is mentioned
//! and what it means; [`super::flow`] whether that is a write or a read and
//! what stands on the right; [`super::origin`] which literals and names are
//! sources already. Hosts add what the code alone does not show through
//! [`EdgeProvider`]s.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::compiler::{Compiler, DeclKind, Declaration, Inspector, Outline, Target};
use super::document::{Document, Excerpt};
use super::ecs;
use super::edges::{EdgeProvider, Member};
use super::flow::{self, Access, Utf16Range as R, string};
use super::origin::{self as origins, Kind, Library, ValueOrigin};
use super::project::{Logger, Project};
use super::symbols::{Symbol, SymbolKind, Symbols, base_key};
use super::text::{
    extension, is_word, last_component, letters, prefix_letters, read_source, stem, trim_spaces,
};
use super::wording::{Note, Unknown};
use super::{LINES_AFTER, UNIVERSAL_MEMBERS};

/// A value's declaration: where it is and its name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Decl {
    pub path: String,
    pub line: usize,
    /// UTF-16 code units from the start of the line, as the compiler's
    /// locations count.
    pub character: usize,
    /// UTF-16.
    pub length: usize,
    /// The full name: `Game.Health.Value`.
    pub name: String,
}

impl Decl {
    #[must_use]
    pub fn short_name(&self) -> String {
        self.name
            .split('.')
            .rfind(|p| !p.is_empty())
            .unwrap_or(&self.name)
            .to_owned()
    }

    /// `Game.Health.Value` → `Health`.
    #[must_use]
    pub fn type_name(&self) -> Option<String> {
        let parts: Vec<&str> = self.name.split('.').filter(|p| !p.is_empty()).collect();
        (parts.len() >= 2).then(|| parts[parts.len() - 2].to_owned())
    }

    #[must_use]
    pub fn title(&self) -> String {
        match self.type_name() {
            // `Box`1` is how metadata names a generic type; in code it is `Box`.
            Some(owner) => format!(
                "{}.{}",
                owner.split('`').next().unwrap_or(&owner),
                self.short_name()
            ),
            None => self.short_name(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SourceKind {
    Value(Decl),
    Call(String, Option<Decl>),
    Parameter(String, Option<Decl>, usize),
    /// A whole ECS component: `_health.Get(e)` without a field.
    Component(String),
    /// A source: a literal, a constant, an enum value, the engine's time…
    /// The `Decl` is the declaration when the source is a name.
    Origin(ValueOrigin, Option<Decl>),
    /// A name the graph went no further than: the compiler did not
    /// recognize it (no reason), or a local whose value cannot be followed.
    Unknown(String, Option<Unknown>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Source {
    pub kind: SourceKind,
    /// The locals the value came through: `dmg ← mult`.
    pub via: Vec<String>,
    /// The compiler did not recognize the name; a field of that name was
    /// found among the project's symbols.
    pub by_name: bool,
    /// The name is an argument of a call to a project method: that call.
    /// The graph does not expand such names by itself — the value comes
    /// through the call's return.
    pub argument_of: Option<String>,
}

impl Source {
    #[must_use]
    pub fn new(kind: SourceKind, via: &[String]) -> Self {
        Self {
            kind,
            via: via.to_vec(),
            by_name: false,
            argument_of: None,
        }
    }
}

/// When a place runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Trigger {
    /// A loop over a host's receiver of a message type: the message arrived.
    Arrival { message: String, receiver: String },
    /// A loop over an ECS filter.
    Filter {
        name: String,
        with: Vec<String>,
        without: Vec<String>,
    },
}

/// A place where a value is written, returned, passed or set.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Site {
    pub path: String,
    /// The UTF-8 byte offset of the place in its file; for a line of data,
    /// the line's number.
    pub offset: usize,
    pub line: usize,
    pub title: String,
    pub notes: Vec<Note>,
    /// The place only reads the value off the wire, in its type's own
    /// reader ([`EdgeProvider::is_read_site`]).
    pub is_bridge_read: bool,
    /// A line of data — a config's JSON, a prefab's YAML — not code.
    pub is_data: bool,
    /// The declaration itself: an initial value, a constant, a getter.
    pub is_declaration: bool,
    /// The place's project, when it is not the one whose node was
    /// expanded.
    pub project: Option<String>,
    pub sources: Vec<Source>,
    pub trigger: Option<Trigger>,
    pub filter_line: Option<usize>,
    /// The lines around the place.
    pub preview: Excerpt,
    /// The lines of the method around the place: first and last, at most
    /// [`LINES_AFTER`] apart.
    pub method_lines: Option<(usize, usize)>,
}

impl Site {
    #[must_use]
    pub fn new(path: &str, offset: usize, line: usize, title: String) -> Self {
        Self {
            path: path.to_owned(),
            offset,
            line,
            title,
            ..Self::default()
        }
    }

    /// A place on a line of data: the preview is the lines themselves,
    /// without a lexer — the file may be a scene of a hundred megabytes.
    /// `lines` are the file's lines from number `shift`; `line` is a number
    /// among them.
    #[must_use]
    pub fn data(path: &str, lines: &[&str], line: usize, shift: usize) -> Self {
        let mut site = Self::new(
            path,
            line + shift,
            line + shift,
            last_component(path).to_owned(),
        );
        site.is_data = true;
        let first = line.saturating_sub(1);
        if !lines.is_empty() {
            let last = (lines.len() - 1).min(line + 1);
            if first <= last {
                site.preview = Excerpt {
                    first: first + shift,
                    lines: lines[first..=last]
                        .iter()
                        .map(|l| l.replace('\r', ""))
                        .collect(),
                };
            }
        }
        site
    }
}

/// Where the graph starts: what is under the cursor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Root {
    /// A field, property or local: who writes it.
    Value(Decl),
    /// A component type: where it is set and removed.
    Component(String),
    /// A method: what it returns.
    Call(Decl),
    /// A method's parameter: what calls pass.
    Parameter {
        method: Decl,
        index: usize,
        name: String,
    },
    /// A source already: an enum value, an assembly member.
    Origin(ValueOrigin, Option<Decl>),
}

/// A write into a local: where, a note, and what from.
struct LocalWrite {
    offset: usize,
    note: Option<Note>,
    sources: Vec<Source>,
}

/// The kinds of member whose declaration encloses a place.
const MEMBER_KINDS: [DeclKind; 7] = [
    DeclKind::Method,
    DeclKind::Constructor,
    DeclKind::Property,
    DeclKind::Indexer,
    DeclKind::Operator,
    DeclKind::Event,
    DeclKind::Destructor,
];

/// One project's analysis: its compiler, symbols and providers, and what it
/// has read so far. Not shared between threads; moved to the one that
/// runs it.
pub struct Context {
    pub root: String,
    compiler: Arc<dyn Compiler>,
    texts: HashMap<String, String>,
    symbols: Option<Arc<dyn Symbols>>,
    inspector: Option<Arc<dyn Inspector>>,
    edges: Vec<Arc<dyn EdgeProvider>>,
    log: Option<Logger>,
    /// Types whose fields continue in the linked project
    /// ([`EdgeProvider::bridged_types`]).
    pub bridged: HashSet<String>,
    models: RefCell<HashMap<String, Arc<Document>>>,
    outlines: RefCell<HashMap<String, Arc<Outline>>>,
    definitions: RefCell<HashMap<String, Option<Target>>>,
}

impl std::fmt::Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("root", &self.root)
            .field("edges", &self.edges.len())
            .finish_non_exhaustive()
    }
}

impl Context {
    /// The context of `project` with its compiler.
    #[must_use]
    pub fn new(project: &Project, compiler: Arc<dyn Compiler>) -> Self {
        let mut context = Self {
            root: project.root.clone(),
            compiler,
            texts: project.texts.clone(),
            symbols: project.symbols.clone(),
            inspector: project.inspector.clone(),
            edges: project.edges.clone(),
            log: project.log.clone(),
            bridged: HashSet::new(),
            models: RefCell::new(HashMap::new()),
            outlines: RefCell::new(HashMap::new()),
            definitions: RefCell::new(HashMap::new()),
        };
        let bridged: HashSet<String> = context
            .edges
            .iter()
            .flat_map(|e| e.bridged_types(&context))
            .collect();
        context.bridged = bridged;
        context
    }

    /// The context of a project of the table; `None` without its compiler.
    #[must_use]
    pub fn for_project(project: &Project) -> Option<Self> {
        let compiler = project.compiler.clone()?;
        Some(Self::new(project, compiler))
    }

    /// The project's symbols, when the host gave them.
    #[must_use]
    pub fn symbols(&self) -> Option<&dyn Symbols> {
        self.symbols.as_deref()
    }

    /// The text of an open file with unsaved changes.
    #[must_use]
    pub fn text_of(&self, path: &str) -> Option<&str> {
        self.texts.get(path).map(String::as_str)
    }

    /// Write a line to the host's log, if it keeps one.
    pub fn log(&self, line: &str) {
        if let Some(log) = &self.log {
            log(line);
        }
    }

    // MARK: What is under the cursor

    /// Where to start the graph for the name under the cursor: a field or
    /// property — who writes it; a local — its writes in the method; a
    /// parameter — the arguments of calls; a method — what it returns; an
    /// enum value or an assembly member — a source right away; a type — a
    /// component. `None`: not a value.
    #[must_use]
    pub fn root_for(&self, target: &Target) -> Option<Root> {
        let declaration = declaration_of(target);
        // An assembly or package member is a source right away: time, random, the engine.
        if is_library(&target.path)
            && matches!(
                target.kind,
                DeclKind::Field | DeclKind::Property | DeclKind::Event | DeclKind::Method
            )
        {
            let call = if target.kind == DeclKind::Method {
                "()"
            } else {
                ""
            };
            let origin = library_origin(
                &target.container().unwrap_or_default(),
                &target.short_name(),
                &format!("{}{call}", declaration.title()),
            );
            return Some(Root::Origin(origin, Some(declaration)));
        }
        match target.kind {
            DeclKind::Field | DeclKind::Property | DeclKind::Event => {
                if target.kind != DeclKind::Field {
                    return Some(Root::Value(declaration));
                }
                let Some(model) = self.model(&target.path) else {
                    return Some(Root::Value(declaration));
                };
                let units = model.units();
                let at = model.offset(target.line, target.character);
                let name = R::new(at, target.length);
                if flow::is_type_parameter(units, name) {
                    return None;
                }
                // The compiler gives locals and parameters as fields: a
                // parameter by its place in the method's parentheses.
                if let Some(method) = self.enclosing_member(&target.path, at)
                    && !method.name_range.contains(at)
                    && let Some(list) = parameters(&method, units)
                    && list.contains(at)
                    && let Some(index) = parameter_index(&target.short_name(), &method)
                {
                    // `out`: the method puts the value itself — its writes, as a local's.
                    // (The outline's parameters have no modifiers; the text tells.)
                    if flow::is_out_argument(units, name) {
                        return Some(Root::Value(declaration));
                    }
                    return Some(Root::Parameter {
                        method: method_declaration(&method, &model, &target.path),
                        index,
                        name: target.short_name(),
                    });
                }
                Some(Root::Value(declaration))
            }
            DeclKind::Method => Some(Root::Call(self.named(&declaration))),
            DeclKind::EnumMember => {
                let title = declaration.title();
                Some(Root::Origin(
                    ValueOrigin::new(Kind::EnumValue, title),
                    Some(declaration),
                ))
            }
            // A project type is a component; `string` and `Vector3` are not.
            DeclKind::Struct | DeclKind::Class => {
                (!is_library(&target.path)).then(|| Root::Component(target.short_name()))
            }
            _ => None,
        }
    }

    // MARK: Writes to a field

    /// The places that write a value. `implementing`: look into the
    /// implementations and overrides of an interface or virtual member too.
    #[must_use]
    pub fn writes(&self, value: &Decl, implementing: bool) -> Vec<Site> {
        let declaration = self.named(value);
        let Some(model) = self.model(&declaration.path) else {
            return Vec::new();
        };
        let units = model.units();
        let offset = model.offset(declaration.line, declaration.character);
        // A local: its writes are in its method.
        if let Some(method) = self.local_scope(&declaration.path, offset) {
            let sites = self.local_sites(&declaration, offset, &method, &model);
            // An out parameter of an interface method: no body, the writes are in the implementations.
            if sites.is_empty()
                && implementing
                && let Some(list) = parameters(&method, units)
                && list.contains(offset)
                && let Some(index) = parameter_index(&declaration.short_name(), &method)
            {
                return self
                    .implementations(&method_declaration(&method, &model, &declaration.path))
                    .iter()
                    .filter_map(|m| self.parameter_of(m, index))
                    .flat_map(|p| self.writes(&p, false))
                    .collect();
            }
            return sites;
        }
        let references = self.references(&declaration.path, offset);
        let mut sites = Vec::new();
        let mut reads = 0;
        for target in &references {
            if target.path == declaration.path
                && target.line == declaration.line
                && target.character == declaration.character
            {
                continue;
            }
            let Some(model) = self.model(&target.path) else {
                continue;
            };
            let units = model.units();
            let at = model.offset(target.line, target.character);
            let name = R::new(at, target.length);
            let Access::Write { rhs, compound } = flow::access(units, name) else {
                // A write into an element of a collection: the field's value is what is put in.
                if let Some(value) = flow::deconstruction(units, name) {
                    // `(x, y) = (1, 2)`, `(x, y) = Pair()`.
                    let method = self.enclosing_member(&target.path, at);
                    let mut site = self.make_site(&target.path, &model, at, method.as_ref());
                    site.notes.push(Note::Deconstruction);
                    site.sources = self.sources(
                        value,
                        &target.path,
                        &model,
                        method.as_ref(),
                        &[],
                        0,
                        Kind::Literal,
                    );
                    sites.push(site);
                } else if flow::is_ref_argument(units, name) {
                    // `Inc(ref x)`: a method changes the value — its writes into the parameter.
                    let method = self.enclosing_member(&target.path, at);
                    let mut site = self.make_site(&target.path, &model, at, method.as_ref());
                    site.notes.push(Note::ByRef);
                    site.sources =
                        self.out_sources(at, name, &target.path, &model, method.as_ref(), &[], 0);
                    sites.push(site);
                } else if let Some((value, method_name)) = flow::element_write(units, name) {
                    let method = self.enclosing_member(&target.path, at);
                    let mut site = self.make_site(&target.path, &model, at, method.as_ref());
                    site.notes.push(Note::AddsTo(method_name));
                    site.sources = self.sources(
                        value,
                        &target.path,
                        &model,
                        method.as_ref(),
                        &[],
                        0,
                        Kind::Literal,
                    );
                    sites.push(site);
                } else {
                    reads += 1;
                }
                continue;
            };
            let method = self.enclosing_member(&target.path, at);
            let mut site = self.make_site(&target.path, &model, at, method.as_ref());
            if compound {
                site.notes.push(Note::Compound);
            }
            site.is_bridge_read = self
                .edges
                .iter()
                .any(|e| e.is_read_site(self, &declaration, method.as_ref()));
            if let Some(rhs) = rhs {
                site.sources = self.sources(
                    rhs,
                    &target.path,
                    &model,
                    method.as_ref(),
                    &[],
                    0,
                    Kind::Literal,
                );
            } else if flow::is_out_argument(units, name) {
                // `Read(out x)`: the call puts the value, as for a local.
                site.notes = vec![Note::OutArgument];
                site.sources =
                    self.out_sources(at, name, &target.path, &model, method.as_ref(), &[], 0);
            }
            sites.push(site);
        }
        sites.extend(self.declared(&declaration, &model));
        let known: HashSet<String> = sites
            .iter()
            .map(|s| format!("{}|{}", s.path, s.offset))
            .collect();
        sites.extend(self.stash_writes(&declaration, known));
        // An interface property: the implementations give the value; a
        // virtual one — the overrides too.
        if implementing
            && (sites.is_empty()
                || self
                    .enclosing_member(&declaration.path, offset)
                    .is_some_and(|member| is_virtual(&member, model.units())))
        {
            sites.extend(
                self.implementations(&declaration)
                    .iter()
                    .flat_map(|d| self.writes(d, false)),
            );
        }
        if self.log.is_some() {
            let unknown = sites
                .iter()
                .flat_map(|s| &s.sources)
                .filter(|s| matches!(s.kind, SourceKind::Unknown(..)))
                .count();
            let listed: Vec<String> = sites
                .iter()
                .map(|s| {
                    format!(
                        "{}:{}{}",
                        s.title,
                        s.line + 1,
                        if s.is_bridge_read { " (read)" } else { "" }
                    )
                })
                .collect();
            self.log(&format!(
                "[graph] {}: mentions {}, writes {}, reads {reads}, unresolved names {unknown} — {}",
                declaration.name,
                references.len(),
                sites.len(),
                listed.join(", ")
            ));
        }
        sites
    }

    /// Where a value the code does not write comes from: a table column, a
    /// field of a config model or JSON, a Unity inspector field, an
    /// assembly member. `None`: not known.
    #[must_use]
    pub fn origin(&self, value: &Decl) -> Option<ValueOrigin> {
        if is_library(&value.path) {
            let parts: Vec<&str> = value.name.split('.').filter(|p| !p.is_empty()).collect();
            let type_name = parts[..parts.len().saturating_sub(1)].join(".");
            return Some(library_origin(
                &type_name,
                &value.short_name(),
                &value.title(),
            ));
        }
        let declaration = self.named(value);
        let model = self.model(&declaration.path)?;
        let units = model.units();
        let offset = model.offset(declaration.line, declaration.character);
        let outline = self.outline(&declaration.path);
        let declarations = &outline.declarations;
        let member = declarations.iter().find(|d| {
            d.name_range.contains(offset) && matches!(d.kind, DeclKind::Field | DeclKind::Property)
        })?;
        let owner = declarations
            .iter()
            .filter(|d| d.kind.is_type() && d.full_range.contains(member.full_range.location))
            .min_by_key(|d| d.full_range.length);
        let short = |a: &String| last_part(a).unwrap_or(a.as_str()).to_owned();
        let own: HashSet<String> = member.attributes.iter().map(short).collect();
        let owner_attributes: HashSet<String> = owner
            .map(|o| o.attributes.iter().map(short).collect())
            .unwrap_or_default();
        let head = head_of(member, units);
        let has = |set: &HashSet<String>, names: &[&str]| names.iter().any(|n| set.contains(*n));
        // A table row's model: attributes, or the name (Dapper's `…DbModel` has none).
        let owner_name = owner.map_or("", |o| o.name.as_str());
        if has(&own, &["Column", "Key", "ForeignKey"])
            || owner_attributes.contains("Table")
            || ["DbModel", "DBModel", "DatabaseModel"]
                .iter()
                .any(|s| owner_name.ends_with(s))
        {
            return Some(ValueOrigin::new(Kind::Database, declaration.title()));
        }
        let facts = Member {
            declaration: &declaration,
            attributes: &own,
            owner_attributes: &owner_attributes,
            head: &head,
        };
        if let Some(found) = self.edges.iter().find_map(|e| e.origin(self, &facts)) {
            return Some(found);
        }
        let key = ["JsonProperty", "JsonPropertyName", "DataMember"]
            .iter()
            .find_map(|a| json_property(&head, a));
        if has(
            &own,
            &[
                "JsonProperty",
                "JsonPropertyName",
                "DataMember",
                "JsonRequired",
            ],
        ) {
            return Some(ValueOrigin::new(
                Kind::Json,
                key.unwrap_or_else(|| declaration.short_name()),
            ));
        }
        if has(&own, &["Injectable", "Inject"]) {
            return Some(ValueOrigin::new(
                Kind::Injection,
                member
                    .type_text
                    .clone()
                    .unwrap_or_else(|| declaration.title()),
            ));
        }
        let unity_object = owner.is_some_and(|o| {
            o.bases.iter().any(|b| {
                ["MonoBehaviour", "ScriptableObject", "NetworkBehaviour"]
                    .contains(&base_key(b).as_str())
            })
        });
        let is_public_field =
            member.kind == DeclKind::Field && head.split([' ', '\t', '\n']).any(|w| w == "public");
        if own.contains("SerializeField")
            || own.contains("SerializeReference")
            || (unity_object && is_public_field)
        {
            // The key in a prefab's YAML is the field's name as it is.
            return Some(ValueOrigin::new(Kind::Inspector, declaration.short_name()));
        }
        None
    }

    /// What the declaration itself gives: a field's initial value, a
    /// constant, an auto-property's initial value, what a getter returns.
    fn declared(&self, declaration: &Decl, model: &Arc<Document>) -> Vec<Site> {
        let units = model.units();
        let offset = model.offset(declaration.line, declaration.character);
        let outline = self.outline(&declaration.path);
        let Some(member) = outline.declarations.iter().find(|d| {
            d.name_range.contains(offset)
                && matches!(
                    d.kind,
                    DeclKind::Field | DeclKind::Property | DeclKind::Indexer
                )
        }) else {
            return Vec::new();
        };
        let mut sites = Vec::new();
        let mut add = |expression: R, note: Note, method: Option<&Declaration>, literal: Kind| {
            let mut site = self.make_site(&declaration.path, model, expression.location, method);
            site.title = declaration.title();
            site.notes.push(note);
            site.is_declaration = true;
            site.sources = self.sources(
                expression,
                &declaration.path,
                model,
                method,
                &[],
                0,
                literal,
            );
            sites.push(site);
        };
        if member.kind == DeclKind::Field {
            if let Access::Write {
                rhs: Some(value), ..
            } = flow::access(units, member.name_range)
            {
                let is_const = head_of(member, units)
                    .split([' ', '\t', '\n'])
                    .any(|w| w == "const");
                add(
                    value,
                    if is_const {
                        Note::Constant
                    } else {
                        Note::Initial
                    },
                    None,
                    if is_const {
                        Kind::Constant
                    } else {
                        Kind::Initial
                    },
                );
            }
        } else {
            for expression in flow::getter_expressions(units, member.full_range, member.name_range)
            {
                add(expression, Note::GetterReturns, Some(member), Kind::Literal);
            }
            if let Some(value) =
                flow::property_initializer(units, member.full_range, member.name_range)
            {
                add(value, Note::Initial, None, Kind::Initial);
            }
        }
        sites
    }

    /// The declaration with its position on the name. The compiler gives a
    /// property or method by the start of its declaration (attributes,
    /// `public`), and finds references to them only from the name.
    #[must_use]
    pub fn named(&self, declaration: &Decl) -> Decl {
        if is_assembly(&declaration.path) {
            return declaration.clone();
        }
        let Some(model) = self.model(&declaration.path) else {
            return declaration.clone();
        };
        let offset = model.offset(declaration.line, declaration.character);
        let name = declaration.short_name();
        let units = model.units();
        let length = name.encode_utf16().count();
        if offset + length <= units.len() && string(units, R::new(offset, length)) == name {
            return declaration.clone();
        }
        let outline = self.outline(&declaration.path);
        let Some(member) = outline
            .declarations
            .iter()
            .filter(|d| {
                d.name == name && d.full_range.contains(offset) && d.name_range.location >= offset
            })
            .min_by_key(|d| d.full_range.length)
        else {
            return declaration.clone();
        };
        let mut fixed = declaration.clone();
        let (line, character) = model.position(member.name_range.location);
        fixed.line = line;
        fixed.character = character;
        fixed.length = member.name_range.length;
        fixed
    }

    // MARK: Locals

    /// The method in whose body the name at `offset` is declared, if it is
    /// a local (or a parameter) rather than a member of a type.
    fn local_scope(&self, path: &str, offset: usize) -> Option<Declaration> {
        let member = self.enclosing_member(path, offset)?;
        (!member.name_range.contains(offset)).then_some(member)
    }

    /// The writes into a local as places, as a field's: a declaration with
    /// an initial value, assignments, `out` in a call, a `foreach` element.
    fn local_sites(
        &self,
        declaration: &Decl,
        offset: usize,
        method: &Declaration,
        model: &Arc<Document>,
    ) -> Vec<Site> {
        let path = &declaration.path;
        let writes = self.local_writes(offset, method, path, model, &[], 0);
        let sites: Vec<Site> = writes
            .into_iter()
            .map(|write| {
                let mut site = self.make_site(path, model, write.offset, Some(method));
                site.notes.extend(write.note);
                site.sources = write.sources;
                site
            })
            .collect();
        self.log(&format!(
            "[graph] local {} in {}: writes {}",
            declaration.short_name(),
            method.name,
            sites.len()
        ));
        sites
    }

    /// The writes into the local declared at `at` of `method`: assignments,
    /// `out` in a call, a `foreach` element, a tuple deconstruction, a
    /// pattern variable, a local function's parameter. `via` is the
    /// "through" of the sources: empty for the local the graph starts at.
    fn local_writes(
        &self,
        at: usize,
        method: &Declaration,
        path: &str,
        model: &Arc<Document>,
        via: &[String],
        depth: usize,
    ) -> Vec<LocalWrite> {
        let units = model.units();
        let next = depth + 1;
        let mut result = Vec::new();
        let references = self.references(path, at);
        // A parameter's declaration (`out string key` in the method's parentheses) is not a write.
        let parameter_list = parameters(method, units);
        let from = |expression: R| {
            self.sources(
                expression,
                path,
                model,
                Some(method),
                via,
                next,
                Kind::Literal,
            )
        };
        for reference in references.iter().filter(|r| r.path == path) {
            let offset = model.offset(reference.line, reference.character);
            let range = R::new(offset, reference.length);
            if parameter_list.is_some_and(|p| p.contains(offset)) {
                continue;
            }
            match flow::access(units, range) {
                Access::Write {
                    rhs: Some(value),
                    compound,
                } => {
                    result.push(LocalWrite {
                        offset,
                        note: compound.then_some(Note::Compound),
                        sources: from(value),
                    });
                }
                _ => {
                    if let Some((value, method_name)) = flow::element_write(units, range) {
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::AddsTo(method_name)),
                            sources: from(value),
                        });
                    } else if flow::is_out_argument(units, range) {
                        let sources =
                            self.out_sources(offset, range, path, model, Some(method), via, next);
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::OutArgument),
                            sources,
                        });
                    } else if offset == at
                        && flow::is_lambda_parameter(units, range)
                        && let Some(found) =
                            self.lambda_sources(range, path, model, Some(method), via, next)
                    {
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::LambdaParameter),
                            sources: found,
                        });
                    } else if offset == at
                        && let Some(collection) = flow::foreach_collection(units, range)
                    {
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::ForeachItem),
                            sources: from(collection),
                        });
                    } else if offset == at
                        && let Some(value) = flow::deconstruction(units, range)
                    {
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::Deconstruction),
                            sources: from(value),
                        });
                    } else if offset == at
                        && let Some(subject) = flow::pattern_subject(units, range)
                    {
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::PatternCheck),
                            sources: from(subject),
                        });
                    } else if offset == at
                        && let Some((function_range, index)) =
                            flow::local_function_parameter(units, range)
                    {
                        // A local function's parameter: the arguments of its calls in this method.
                        let function = string(units, function_range);
                        let arguments: Vec<R> = flow::calls(
                            &function,
                            units,
                            method.full_range,
                            function_range.location,
                        )
                        .into_iter()
                        .filter_map(|call| flow::argument(units, call, index))
                        .collect();
                        let sources = arguments.into_iter().flat_map(from).collect();
                        result.push(LocalWrite {
                            offset,
                            note: Some(Note::LocalFunctionParameter(function)),
                            sources,
                        });
                    }
                }
            }
        }
        result
    }

    /// A lambda given to a library method: its parameter is what that
    /// method gives — the element of `list` in `list.ForEach(x => …)`, a
    /// database row in `QueryAsync`. `None`: a project method, or unclear.
    fn lambda_sources(
        &self,
        parameter: R,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Option<Vec<Source>> {
        let call = flow::lambda_call(model.units(), parameter)?;
        self.library_kind(&call, path)?;
        let found = self.resolve(std::slice::from_ref(&call), path, model, method, via, depth);
        (!found.is_empty()).then_some(found)
    }

    /// `out x` in a call: the call puts the value. An assembly's call is a
    /// transformation (`int.TryParse(s, out x)`, `map.TryGetValue(k, out
    /// x)`): then the value comes from the receiver and the other
    /// arguments.
    #[allow(clippy::too_many_arguments)]
    fn out_sources(
        &self,
        offset: usize,
        local: R,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Vec<Source> {
        let units = model.units();
        let Some(call) = flow::enclosing_call(units, offset) else {
            return Vec::new();
        };
        // A project method puts the value into its out parameter: its writes, not a return.
        if let Some(target) = self.definition(path, call.range.location)
            && target.kind == DeclKind::Method
            && !is_library(&target.path)
            && let Some(index) = (0..16).find(|&k| {
                flow::argument(units, call.range, k).is_some_and(|a| a.contains(local.location))
            })
        {
            let callee = self.named(&declaration_of(&target));
            // `x.M(out y)` of an extension: `x` is the `this` parameter, the numbers shift.
            let shift = usize::from(is_extension_call(
                self.member_declaration(&callee).as_ref(),
                call.range,
                units,
            ));
            if let Some(parameter) = self.parameter_of(&callee, index + shift) {
                return vec![Source::new(SourceKind::Value(parameter), via)];
            }
        }
        let mut result = self.resolve(std::slice::from_ref(&call), path, model, method, via, depth);
        if let Some(kind) = self.library_kind(&call, path)
            && (kind == Library::Transform || kind == Library::Unknown)
            && let Some(arguments) = flow::parameter_list(units, call.range)
        {
            let others: Vec<flow::Source> = flow::sources(units, arguments)
                .into_iter()
                .filter(|s| s.range.intersection(local).length == 0)
                .collect();
            result.extend(self.resolve(&others, path, model, method, via, depth));
        }
        result
    }

    /// The method's parameter number `index`, as a declaration like a
    /// local's: its writes in the method's body are what the method puts
    /// into `out`.
    fn parameter_of(&self, method: &Decl, index: usize) -> Option<Decl> {
        let model = self.model(&method.path)?;
        let units = model.units();
        let offset = model.offset(method.line, method.character);
        let text = flow::argument(units, R::new(offset, method.length), index)?;
        // The name is the last word before `=`: `out string key`, `int n = 5`.
        let mut end = text.end();
        let source = string(units, text);
        if let Some(equals) = source.find('=') {
            end = text.location + source[..equals].encode_utf16().count();
        }
        while end > text.location && !flow::is_ident_part(units[end - 1]) {
            end -= 1;
        }
        let mut start = end;
        while start > text.location && flow::is_ident_part(units[start - 1]) {
            start -= 1;
        }
        if start >= end {
            return None;
        }
        let (line, character) = model.position(start);
        Some(Decl {
            path: method.path.clone(),
            line,
            character,
            length: end - start,
            name: format!(
                "{}.{}",
                method.name,
                string(units, R::new(start, end - start))
            ),
        })
    }

    /// A member's declaration in its file's outline.
    fn member_declaration(&self, declaration: &Decl) -> Option<Declaration> {
        let model = self.model(&declaration.path)?;
        let offset = model.offset(declaration.line, declaration.character);
        self.outline(&declaration.path)
            .declarations
            .iter()
            .find(|d| d.name_range.contains(offset))
            .cloned()
    }

    // MARK: ECS stashes

    /// Writes into a component's field through a stash, which the compiler
    /// does not see: `ref var c = ref _stash.Get(e); c.Field = x` is not a
    /// reference to the field to it, the more so when the stash field is
    /// added by a source generator. The component's stashes come from the
    /// symbols, the writes from the code. `known`: those found already.
    fn stash_writes(&self, declaration: &Decl, known: HashSet<String>) -> Vec<Site> {
        let Some(component) = declaration.type_name() else {
            return Vec::new();
        };
        let mut sites = Vec::new();
        let mut seen = known;
        for (stash, path) in self.stashes(&component) {
            let Some(model) = self.model(&path) else {
                continue;
            };
            let units = model.units();
            let writes =
                ecs::stash_field_writes(units, &stash, &declaration.short_name(), &mut |at| {
                    self.enclosing_member(&path, at).map(|m| m.full_range)
                });
            for write in writes {
                if !seen.insert(format!("{path}|{}", model.byte(write.name.location))) {
                    continue;
                }
                let method = self.enclosing_member(&path, write.name.location);
                let mut site = self.make_site(&path, &model, write.name.location, method.as_ref());
                if write.compound {
                    site.notes.push(Note::Compound);
                }
                if let Some(rhs) = write.rhs {
                    site.sources =
                        self.sources(rhs, &path, &model, method.as_ref(), &[], 0, Kind::Literal);
                }
                sites.push(site);
            }
        }
        sites
    }

    /// A component's stash fields: (name, path), declared and generated.
    fn stashes(&self, component: &str) -> Vec<(String, String)> {
        let Some(symbols) = self.symbols() else {
            return Vec::new();
        };
        let mut found: Vec<(String, String)> = Vec::new();
        for symbol in symbols.stashes(component) {
            if !found
                .iter()
                .any(|(n, p)| *n == symbol.name && *p == symbol.path)
            {
                found.push((symbol.name, symbol.path));
            }
        }
        found
    }

    /// A component's field taken through a stash the compiler does not
    /// see: `c.Field` of `ref var c = ref _stash.Get(e)` and
    /// `_stash.Get(e).Field`.
    fn stash_member(
        &self,
        source: &flow::Source,
        name: &str,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
    ) -> Option<Decl> {
        let mut stash: Option<String> = None;
        if let Some(receiver) = &source.receiver {
            let parts = split_dots(receiver);
            if parts.len() == 2 && (parts[1] == "Get" || parts[1] == "Add") {
                stash = Some(parts[0].to_owned());
            }
        } else if !source.member
            && let Some(method) = method
        {
            let parts = split_dots(&source.chain);
            if parts.len() >= 2 {
                stash = ecs::stash_of_local(
                    model.units(),
                    parts[0],
                    method.full_range,
                    source.range.location,
                );
            }
        }
        let stash = stash?;
        let symbols = self.symbols()?;
        let component = self.component_of_stash(&stash, path, method)?;
        // The component's field is the first link after the stash or the
        // ref local: `Position` of `c.Position.Value`.
        let parts = split_dots(&source.chain);
        let field = if source.receiver.is_some() {
            parts.first().copied().unwrap_or(name).to_owned()
        } else {
            parts.get(1).copied().unwrap_or(name).to_owned()
        };
        let symbol = symbols
            .members_of(&component)
            .into_iter()
            .find(|s| s.name == field && s.is_value())?;
        Some(self.canonical(&symbol))
    }

    /// A call on a stash the compiler does not see (`_health.Get`,
    /// `_health.Has`): that stash's component.
    fn stash_call(&self, chain: &str, path: &str, method: Option<&Declaration>) -> Option<String> {
        let parts = split_dots(chain);
        if parts.len() != 2 {
            return None;
        }
        self.component_of_stash(parts[0], path, method)
    }

    /// The component of the stash `name`: this file's stash, or else one
    /// of the same name in the same class.
    fn component_of_stash(
        &self,
        name: &str,
        path: &str,
        method: Option<&Declaration>,
    ) -> Option<String> {
        let symbols = self.symbols()?;
        let owner = method
            .and_then(|m| m.container.as_deref())
            .and_then(last_part);
        let mut component = None;
        for symbol in symbols.named(name) {
            if symbol.kind != SymbolKind::Field {
                continue;
            }
            let Some(found) = symbol.type_text.as_deref().and_then(ecs::stash_component) else {
                continue;
            };
            if symbol.path == path {
                return Some(found);
            }
            if let Some(owner) = owner
                && symbol.container.as_deref().and_then(last_part) == Some(owner)
            {
                component = Some(found);
            }
        }
        component
    }

    /// `T` in `class Box<T>`: the compiler gives a type parameter as a field.
    fn is_type_parameter(&self, target: &Target) -> bool {
        let Some(model) = self.model(&target.path) else {
            return false;
        };
        let at = model.offset(target.line, target.character);
        flow::is_type_parameter(model.units(), R::new(at, target.length))
    }

    /// A declaration from the symbols, with the name the compiler gives
    /// it: one field must be one node, wherever the graph comes to it from.
    fn canonical(&self, symbol: &Symbol) -> Decl {
        let mut declaration = Decl {
            path: symbol.path.clone(),
            line: symbol.line,
            character: symbol.character,
            length: symbol.length,
            name: symbol.qualified(),
        };
        if let Some(model) = self.model(&symbol.path) {
            let offset = model.offset(declaration.line, declaration.character);
            if let Some(target) = self.definition(&symbol.path, offset)
                && target.short_name() == symbol.name
            {
                declaration = declaration_of(&target);
            }
        }
        declaration
    }

    // MARK: A whole component

    /// `stash.Set(e)`, `.Add(`, `.Remove(`: where a component appears and
    /// where it is removed.
    #[must_use]
    pub fn component_changes(&self, component: &str) -> Vec<Site> {
        let stashes = self.stashes(component);
        let mut sites = Vec::new();
        for (stash, path) in &stashes {
            let Some(model) = self.model(path) else {
                continue;
            };
            for (range, call) in ecs::stash_calls(model.units(), stash) {
                let method = self.enclosing_member(path, range.location);
                let mut site = self.make_site(path, &model, range.location, method.as_ref());
                site.notes.push(match call {
                    ecs::StashCall::Set | ecs::StashCall::SetOrUpdate => Note::ComponentSet,
                    ecs::StashCall::Add => Note::ComponentAdd,
                    ecs::StashCall::Remove => Note::ComponentRemove,
                });
                sites.push(site);
            }
        }
        self.log(&format!(
            "[graph] component {component}: stashes {}, places {}",
            stashes.len(),
            sites.len()
        ));
        sites
    }

    // MARK: Messages and data, from the providers

    /// Where a message is sent in this project ([`EdgeProvider::arrivals`]).
    #[must_use]
    pub fn arrivals(&self, message: &str) -> Vec<Site> {
        self.edges
            .iter()
            .flat_map(|e| e.arrivals(self, message))
            .collect()
    }

    /// The lines of data where a value from a host's origin is set
    /// ([`EdgeProvider::where_set`]).
    #[must_use]
    pub fn where_set(&self, origin: &ValueOrigin, value: &Decl) -> Vec<Site> {
        self.edges
            .iter()
            .find_map(|e| e.where_set(self, origin, value))
            .unwrap_or_default()
    }

    // MARK: Calls and parameters

    /// What a method returns: every `return` is a place with its sources.
    #[must_use]
    pub fn returns(&self, declared: &Decl, implementing: bool) -> Vec<Site> {
        let method = self.named(declared);
        let Some(model) = self.model(&method.path) else {
            return Vec::new();
        };
        let offset = model.offset(method.line, method.character);
        let Some(declaration) = self.enclosing_member(&method.path, offset) else {
            return Vec::new();
        };
        let sites: Vec<Site> = flow::returned_expressions(model.units(), declaration.full_range)
            .into_iter()
            .map(|expression| {
                let mut site = self.make_site(
                    &method.path,
                    &model,
                    expression.location,
                    Some(&declaration),
                );
                site.notes.push(Note::Returns);
                site.sources = self.sources(
                    expression,
                    &method.path,
                    &model,
                    Some(&declaration),
                    &[],
                    0,
                    Kind::Literal,
                );
                site
            })
            .collect();
        // An interface or abstract method: no body, the returns are in the
        // implementations. A virtual one: its own and its overrides' — a call
        // through the base type may land in any.
        if !implementing || (!sites.is_empty() && !is_virtual(&declaration, model.units())) {
            return sites;
        }
        let mut sites = sites;
        sites.extend(
            self.implementations(&method)
                .iter()
                .flat_map(|m| self.returns(m, false)),
        );
        sites
    }

    /// The implementations and overrides of a member in the project (no
    /// more than eight: an interface for everything can have hundreds).
    /// When the compiler knows none, the symbols tell: the types that name
    /// the owner among their bases.
    fn implementations(&self, member: &Decl) -> Vec<Decl> {
        if is_assembly(&member.path) {
            return Vec::new();
        }
        let Some(model) = self.model(&member.path) else {
            return Vec::new();
        };
        let offset = model.offset(member.line, member.character);
        let found: Vec<Decl> = self
            .compiler
            .implementations(&member.path, offset)
            .iter()
            .filter(|t| !is_library(&t.path) && !(t.path == member.path && t.line == member.line))
            .take(8)
            .map(|t| self.named(&declaration_of(t)))
            .collect();
        if !found.is_empty() {
            return found;
        }
        let (Some(symbols), Some(owner), Some(declared)) = (
            self.symbols(),
            member.type_name(),
            self.member_declaration(member),
        ) else {
            return found;
        };
        let mut result = Vec::new();
        let mut queue = vec![owner];
        let mut seen = HashSet::new();
        while !queue.is_empty() && result.len() < 8 {
            let base = queue.remove(0);
            if !seen.insert(base.clone()) || seen.len() >= 32 {
                continue;
            }
            for derived in symbols.derived_from(&base) {
                let name = derived.name.clone();
                // The members come from the compiler's outline of the type's
                // file: an explicit implementation (`Entity
                // IElementService.CreateEntity(…)`) the symbols may not
                // show, the compiler does.
                let path = derived.path.clone();
                let outline = self.outline(&path);
                let own: Vec<&Declaration> = outline
                    .declarations
                    .iter()
                    .filter(|d| {
                        (d.name == declared.name
                            || d.name.ends_with(&format!(".{}", declared.name)))
                            && d.kind == declared.kind
                            && d.parameters.len() == declared.parameters.len()
                            && d.container.as_deref().and_then(last_part) == Some(name.as_str())
                    })
                    .collect();
                if let Some(type_model) = self.model(&path) {
                    result.extend(
                        own.iter()
                            .map(|d| self.named(&method_declaration(d, &type_model, &path))),
                    );
                }
                // An abstract intermediate without its own implementation: further down.
                if own.is_empty() {
                    queue.push(name);
                }
            }
        }
        result.truncate(8);
        result
    }

    /// The argument number `argument` in all calls of a method. When there
    /// are none and the method overrides or implements another (`override
    /// Run` of a command), the calls of that one: it is called through the
    /// base type.
    #[must_use]
    pub fn callers(&self, declared: &Decl, argument: usize, dispatch: bool) -> Vec<Site> {
        let found = self.direct_callers(declared, argument);
        if !found.is_empty() || !dispatch {
            return found;
        }
        // An event handler: `bus.Changed += OnChanged` — the arguments are in `Changed?.Invoke(…)`.
        let found = self.event_callers(declared, argument);
        if !found.is_empty() {
            return found;
        }
        self.base_members(&self.named(declared))
            .iter()
            .flat_map(|base| {
                self.direct_callers(base, argument)
                    .into_iter()
                    .map(move |mut site| {
                        site.notes.push(Note::ThroughBase(base.title()));
                        site
                    })
            })
            .collect()
    }

    /// Where a parameter the code does not pass comes from: there are no
    /// calls because the engine or a code generator calls the method.
    /// `deltaTime` of an ECS system's `OnUpdate` is the frame's time, a
    /// Unity message's parameter (`OnTriggerEnter(Collider other)`) is the
    /// engine. `None`: not known.
    #[must_use]
    pub fn parameter_origin(&self, declared: &Decl, argument: usize) -> Option<ValueOrigin> {
        let method = self.named(declared);
        let member = self.member_declaration(&method)?;
        if argument >= member.parameters.len() {
            return None;
        }
        let name = member.parameters[argument]
            .split(' ')
            .rfind(|p| !p.is_empty())
            .unwrap_or("")
            .to_owned();
        // `Main(string[] args)` is the entry point: command line arguments.
        if member.name == "Main"
            && member.parameters.len() == 1
            && trim_spaces(&member.parameters[0]).starts_with("string[]")
        {
            return Some(ValueOrigin::new(
                Kind::External,
                format!("{}({name})", member.name),
            ));
        }
        if ["deltaTime", "dt", "fixedDeltaTime", "deltaSeconds"].contains(&name.as_str()) {
            return Some(ValueOrigin::new(
                Kind::Time,
                format!("{}({name})", member.name),
            ));
        }
        self.is_unity_message(&method, &member)
            .then(|| ValueOrigin::new(Kind::Engine, format!("{}({name})", member.name)))
    }

    /// Unity calls this method by its name: a message, in a class that
    /// derives (directly or through the project's types) from one Unity
    /// sends messages to.
    fn is_unity_message(&self, method: &Decl, member: &Declaration) -> bool {
        if !rustlyn_ide::semantic::unity::is_message(&member.name) {
            return false;
        }
        let Some(model) = self.model(&method.path) else {
            return false;
        };
        let outline = self.outline(&method.path);
        let Some(owner) = outline
            .declarations
            .iter()
            .filter(|d| d.kind.is_type() && d.full_range.contains(member.full_range.location))
            .min_by_key(|d| d.full_range.length)
        else {
            return false;
        };
        let _ = model;
        let mut queue: Vec<String> = owner.bases.iter().map(|b| base_key(b)).collect();
        let mut seen = HashSet::new();
        while let Some(base) = queue.pop() {
            if rustlyn_ide::semantic::unity::is_message_receiver(&base) {
                return true;
            }
            if !seen.insert(base.clone()) || seen.len() >= 16 {
                continue;
            }
            if let Some(symbols) = self.symbols() {
                for found in symbols.types_named(&base) {
                    queue.extend(found.bases.iter().map(|b| base_key(b)));
                }
            }
        }
        false
    }

    /// Members of base types and interfaces with the same name and number of
    /// parameters as `method` — the nearest, no more than four.
    fn base_members(&self, method: &Decl) -> Vec<Decl> {
        let (Some(symbols), Some(model)) = (self.symbols(), self.model(&method.path)) else {
            return Vec::new();
        };
        let offset = model.offset(method.line, method.character);
        let outline = self.outline(&method.path);
        let declarations = &outline.declarations;
        let Some(member) = declarations.iter().find(|d| d.name_range.contains(offset)) else {
            return Vec::new();
        };
        let Some(owner) = declarations
            .iter()
            .filter(|d| d.kind.is_type() && d.full_range.contains(member.full_range.location))
            .min_by_key(|d| d.full_range.length)
        else {
            return Vec::new();
        };
        let mut result = Vec::new();
        let mut queue: Vec<String> = owner.bases.iter().map(|b| base_key(b)).collect();
        let mut seen = HashSet::new();
        while !queue.is_empty() && result.len() < 4 {
            let base = queue.remove(0);
            if !seen.insert(base.clone()) || seen.len() >= 16 {
                continue;
            }
            let mut found = false;
            for symbol in symbols.members_of(&base) {
                if symbol.name == member.name
                    && symbol.kind == SymbolKind::Method
                    && symbol.parameters == member.parameters.len()
                {
                    result.push(self.canonical(&symbol));
                    found = true;
                }
            }
            // The nearest base with such a method: no further up.
            if !found {
                for symbol in symbols.types_named(&base) {
                    queue.extend(symbol.bases.iter().map(|b| base_key(b)));
                }
            }
        }
        result
    }

    /// A method subscribed to an event or a delegate (`e.Changed += M`) is
    /// called by whoever raises the event: `Changed?.Invoke(5)`,
    /// `Changed(5)`. The argument number `argument` in those calls.
    fn event_callers(&self, declared: &Decl, argument: usize) -> Vec<Site> {
        let method = self.named(declared);
        let Some(model) = self.model(&method.path) else {
            return Vec::new();
        };
        let offset = model.offset(method.line, method.character);
        let mut events: Vec<Target> = Vec::new();
        for reference in self.references(&method.path, offset) {
            let Some(reference_model) = self.model(&reference.path) else {
                continue;
            };
            let units = reference_model.units();
            let at = reference_model.offset(reference.line, reference.character);
            let Some(event_at) = subscribed_event(units, R::new(at, reference.length)) else {
                continue;
            };
            if let Some(event) = self.definition(&reference.path, event_at)
                && matches!(
                    event.kind,
                    DeclKind::Event | DeclKind::Field | DeclKind::Property
                )
                && !events.iter().any(|e| {
                    e.path == event.path && e.line == event.line && e.character == event.character
                })
            {
                events.push(event);
            }
        }
        let mut sites = Vec::new();
        for event in events.iter().take(4) {
            let declaration = self.named(&declaration_of(event));
            let Some(event_model) = self.model(&declaration.path) else {
                continue;
            };
            let event_offset = event_model.offset(declaration.line, declaration.character);
            for reference in self.references(&declaration.path, event_offset) {
                let Some(reference_model) = self.model(&reference.path) else {
                    continue;
                };
                let units = reference_model.units();
                let at = reference_model.offset(reference.line, reference.character);
                let Some(call) = invocation(units, R::new(at, reference.length)) else {
                    continue;
                };
                let Some(expression) = flow::argument(units, call, argument) else {
                    continue;
                };
                let caller = self.enclosing_member(&reference.path, at);
                let mut site =
                    self.make_site(&reference.path, &reference_model, at, caller.as_ref());
                site.notes.push(Note::RaisesEvent(declaration.short_name()));
                site.sources = self.sources(
                    expression,
                    &reference.path,
                    &reference_model,
                    caller.as_ref(),
                    &[],
                    0,
                    Kind::Literal,
                );
                sites.push(site);
            }
        }
        sites
    }

    fn direct_callers(&self, declared: &Decl, argument: usize) -> Vec<Site> {
        let method = self.named(declared);
        let Some(model) = self.model(&method.path) else {
            return Vec::new();
        };
        let offset = model.offset(method.line, method.character);
        let references = self.references(&method.path, offset);
        let callee = self.member_declaration(&method);
        let mut sites = Vec::new();
        let mut omitted = 0;
        for target in &references {
            if target.path == method.path
                && target.line == method.line
                && target.character == method.character
            {
                continue;
            }
            let Some(target_model) = self.model(&target.path) else {
                continue;
            };
            let units = target_model.units();
            let at = target_model.offset(target.line, target.character);
            let name = R::new(at, target.length);
            // `x.M(a)` of an extension: `x` is the `this` parameter, the rest shift.
            let mut index = argument.cast_signed();
            if is_extension_call(callee.as_ref(), name, units) {
                index -= 1;
                if index < 0
                    && let Some(receiver) = flow::receiver_expression(units, name)
                {
                    let caller = self.enclosing_member(&target.path, at);
                    let mut site = self.make_site(&target.path, &target_model, at, caller.as_ref());
                    site.notes.push(Note::Calls(method.short_name()));
                    site.sources = self.sources(
                        receiver,
                        &target.path,
                        &target_model,
                        caller.as_ref(),
                        &[],
                        0,
                        Kind::Literal,
                    );
                    sites.push(site);
                    continue;
                }
            }
            let expression = if index >= 0 {
                flow::argument(units, name, index.cast_unsigned())
            } else {
                None
            };
            let Some(expression) = expression else {
                // A call without this argument: the default value.
                if flow::parameter_list(units, name).is_some() {
                    omitted += 1;
                }
                continue;
            };
            let caller = self.enclosing_member(&target.path, at);
            let mut site = self.make_site(&target.path, &target_model, at, caller.as_ref());
            site.notes.push(Note::Calls(method.short_name()));
            site.sources = self.sources(
                expression,
                &target.path,
                &target_model,
                caller.as_ref(),
                &[],
                0,
                Kind::Literal,
            );
            sites.push(site);
        }
        // `M(int a, List<T> b = null)`: those who did not pass `b` get the default.
        let units = model.units();
        if omitted > 0
            && let Some(parameter) = flow::argument(units, R::new(offset, method.length), argument)
            && let Some(value) = flow::default_value(units, parameter)
        {
            let declaration = self.enclosing_member(&method.path, offset);
            let mut site =
                self.make_site(&method.path, &model, value.location, declaration.as_ref());
            site.notes.push(Note::DefaultFor(omitted));
            site.sources = self.sources(
                value,
                &method.path,
                &model,
                None,
                &[],
                0,
                Kind::DefaultValue,
            );
            sites.push(site);
        }
        sites
    }

    // MARK: Names on the right

    /// The sources of an expression: the literals it may turn out to be
    /// (`0`, the branches of `?:`) and the names in it. `literal` is what a
    /// literal counts as: a constant in a constant's declaration, an
    /// initial value in a field's.
    #[allow(clippy::too_many_arguments)]
    fn sources(
        &self,
        expression: R,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
        literal: Kind,
    ) -> Vec<Source> {
        let units = model.units();
        let mut result: Vec<Source> = flow::literal_alternatives(units, expression)
            .into_iter()
            .map(|range| {
                let text = string(units, range);
                let kind = if literal == Kind::Literal && flow::is_default_literal(&text) {
                    Kind::DefaultValue
                } else {
                    literal
                };
                Source::new(
                    SourceKind::Origin(ValueOrigin::new(kind, clip(&text)), None),
                    via,
                )
            })
            .collect();
        result.extend(self.resolve(
            &flow::sources(units, expression),
            path,
            model,
            method,
            via,
            depth,
        ));
        result
    }

    /// What the names of a right-hand side turn into: a field is a value
    /// node; a local is its declaration (recursively); a parameter and a
    /// call are nodes that expand further; an enum value and an assembly
    /// member are sources. A name that only stands as an argument of a call
    /// to a project method (`entity` in `GetMax(entity)`) is weak: it shows,
    /// but the graph does not go there by itself — the call's value expands
    /// through its return anyway.
    fn resolve(
        &self,
        found: &[flow::Source],
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Vec<Source> {
        let mut result = Vec::new();
        for source in found {
            let resolved = self.resolve_one(source, path, model, method, via, depth);
            if resolved.is_empty() {
                continue;
            }
            if let Some(call) = self.argument_of(source, path, model, method) {
                result.extend(resolved.into_iter().map(|mut weak| {
                    if weak.argument_of.is_none() {
                        weak.argument_of = Some(call.clone());
                    }
                    weak
                }));
            } else {
                result.extend(resolved);
            }
        }
        result
    }

    #[allow(clippy::too_many_lines)]
    fn resolve_one(
        &self,
        source: &flow::Source,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Vec<Source> {
        let units = model.units();
        let name = string(units, source.range);
        // `value` in a setter is what is assigned to the property.
        if source.chain == "value"
            && let Some(method) = method
            && matches!(
                method.kind,
                DeclKind::Property | DeclKind::Indexer | DeclKind::Event
            )
            && let Some(setter) = flow::setter(units, method.full_range, method.name_range)
            && setter.contains(source.range.location)
        {
            return vec![Source::new(
                SourceKind::Value(method_declaration(method, model, path)),
                via,
            )];
        }
        // `new T(…)`: an object made of its arguments, which are sources of their own.
        if source.constructs {
            return Vec::new();
        }
        let target = self.definition(path, source.range.location);
        if source.call {
            // A component's stash — `_health.Get(e)`, `.Has(e)` — is the
            // component, not the ECS library's insides, even when the
            // compiler sees the stash itself.
            if !source.member
                && let Some(component) = self.stash_call(&source.chain, path, method)
            {
                return vec![Source::new(SourceKind::Component(component), via)];
            }
            let declaration = target.as_ref().and_then(|t| {
                matches!(t.kind, DeclKind::Method | DeclKind::Constructor)
                    .then(|| declaration_of(t))
            });
            // An assembly's or package's method: time, a random number — a source; `Math.Max` — not.
            if let (Some(declaration), Some(target)) = (&declaration, &target)
                && is_library(&declaration.path)
            {
                return self.library(
                    source,
                    &target.container().unwrap_or_default(),
                    &target.short_name(),
                    Some(declaration.clone()),
                    path,
                    model,
                    method,
                    via,
                    depth,
                );
            }
            if declaration.is_none() && !source.member {
                // `c.Value.ToObject<T>()` of a ref local from a stash: from the field `Value`.
                if let Some(typed) = self.stash_member(source, &name, path, model, method) {
                    return vec![Source::new(SourceKind::Value(typed), via)];
                }
                // `make()` of a local `Func<int> make = () => 5`: what the lambda returns.
                if depth < 6
                    && !via.contains(&name)
                    && let Some(method) = method
                    && let Some(body) =
                        local_lambda_body(units, &name, method.full_range, source.range.location)
                {
                    let mut deeper = via.to_vec();
                    deeper.push(name.clone());
                    return self.sources(
                        body,
                        path,
                        model,
                        Some(method),
                        &deeper,
                        depth + 1,
                        Kind::Literal,
                    );
                }
                // A call on a local whose type the compiler does not know: from what is in it.
                if let Some(local) = self.head_local(source, path, model, method, via, depth) {
                    return local;
                }
            }
            // The compiler does not know the method, but it is from a known library: `Math.Min` on net8.0.
            if declaration.is_none()
                && let Some((type_name, member)) = self.library_by_name(source, path)
            {
                return self.library(
                    source, &type_name, &member, None, path, model, method, via, depth,
                );
            }
            // A host's call whose value is an origin of its own (a whole config by its key).
            if let Some(origin) = self
                .edges
                .iter()
                .find_map(|e| e.call_origin(self, source, units))
            {
                return vec![Source::new(SourceKind::Origin(origin, None), via)];
            }
            return vec![Source::new(
                SourceKind::Call(source.chain.clone(), declaration),
                via,
            )];
        }
        if let Some(target) = &target {
            // A type in a cast `(Vector3)x`, a namespace and a method group
            // (`Callback` without parentheses) are not sources of a value.
            if target.kind.is_type()
                || matches!(
                    target.kind,
                    DeclKind::Namespace
                        | DeclKind::Method
                        | DeclKind::Constructor
                        | DeclKind::Operator
                )
            {
                return Vec::new();
            }
            if matches!(
                target.kind,
                DeclKind::Field | DeclKind::Property | DeclKind::EnumMember | DeclKind::Event
            ) {
                // The compiler gives a type parameter as a field too.
                if target.kind == DeclKind::Field && self.is_type_parameter(target) {
                    return Vec::new();
                }
                // The compiler gives locals and parameters as fields; their
                // place tells them apart: no field is declared inside a method.
                if source.chain == name
                    && !source.member
                    && let Some(method) = method
                    && let Some(local) = self.local(target, &name, method, path, model, via, depth)
                {
                    return local;
                }
                let declaration = declaration_of(target);
                if target.kind == DeclKind::EnumMember {
                    let title = declaration.title();
                    return vec![Source::new(
                        SourceKind::Origin(
                            ValueOrigin::new(Kind::EnumValue, title),
                            Some(declaration),
                        ),
                        via,
                    )];
                }
                if is_library(&target.path) {
                    return self.library(
                        source,
                        &target.container().unwrap_or_default(),
                        &target.short_name(),
                        Some(declaration),
                        path,
                        model,
                        method,
                        via,
                        depth,
                    );
                }
                return vec![Source::new(SourceKind::Value(declaration), via)];
            }
        }
        // A component's field through a stash the compiler does not see.
        if let Some(typed) = self.stash_member(source, &name, path, model, method) {
            return vec![Source::new(SourceKind::Value(typed), via)];
        }
        // The compiler did not recognize the chain's tail (`v.x` of `var v =
        // …` of an unknown type): the value still comes from its head, a
        // local or a parameter.
        if !source.member
            && let Some(local) = self.head_local(source, path, model, method, via, depth)
        {
            return local;
        }
        // A single name the compiler did not recognize: a local or a parameter.
        if source.chain == name
            && !source.member
            && let Some(method) = method
        {
            if depth < 6
                && let Some(initializer) =
                    flow::local_initializer(units, &name, method.full_range, source.range.location)
            {
                let mut deeper = via.to_vec();
                deeper.push(name.clone());
                return self.sources(
                    initializer,
                    path,
                    model,
                    Some(method),
                    &deeper,
                    depth + 1,
                    Kind::Literal,
                );
            }
            if let Some(index) = parameter_index(&name, method) {
                return vec![Source::new(
                    SourceKind::Parameter(
                        name,
                        Some(method_declaration(method, model, path)),
                        index,
                    ),
                    via,
                )];
            }
        }
        // A name from a known library the compiler does not know: `Stopwatch.Frequency`.
        if let Some((type_name, member)) = self.library_by_name(source, path) {
            return self.library(
                source, &type_name, &member, None, path, model, method, via, depth,
            );
        }
        // The compiler did not recognize it — say, the type of a loop
        // variable over a generated filter. A field of that name, from the
        // symbols.
        if let Some(guess) = self.by_name(&name, units) {
            let mut found = Source::new(SourceKind::Value(guess), via);
            found.by_name = true;
            return vec![found];
        }
        vec![Source::new(
            SourceKind::Unknown(source.chain.clone(), None),
            via,
        )]
    }

    /// The call to a project method an argument of which the name is —
    /// that method's name; `None`: the name is a value itself (or an
    /// argument of a library transformation such as `Mathf.Clamp`, a source
    /// then). An argument of a stash (`_hp.Get(entity)`) is a key, not a
    /// value: weak too.
    fn argument_of(
        &self,
        source: &flow::Source,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
    ) -> Option<String> {
        // The key `data[index]`: the value is from `data`.
        if source.is_index_key {
            return Some("[]".into());
        }
        let units = model.units();
        for &call in source.calls.iter().rev() {
            let chain = flow::chain(units, call);
            if self.stash_call(&chain, path, method).is_some() {
                return Some(chain);
            }
            if let Some(target) = self.definition(path, call.location) {
                if is_library(&target.path) {
                    continue;
                }
                if matches!(target.kind, DeclKind::Method | DeclKind::Constructor) {
                    return Some(chain);
                }
                continue;
            }
            let mut probe = flow::Source::new(call, chain.clone(), true);
            probe.links = flow::chain_links(units, call);
            probe.head = probe.links.first().copied();
            if self.library_by_name(&probe, path).is_some() {
                continue;
            }
            return Some(chain);
        }
        None
    }

    /// The compiler's definition, remembered: the graph asks about the
    /// same name more than once — as a source and as a call around an
    /// argument.
    #[must_use]
    pub fn definition(&self, path: &str, offset: usize) -> Option<Target> {
        let key = format!("{path}|{offset}");
        if let Some(cached) = self.definitions.borrow().get(&key) {
            return cached.clone();
        }
        let found = self
            .compiler
            .definition(path, offset, self.text_of(path))
            .into_iter()
            .next();
        self.definitions.borrow_mut().insert(key, found.clone());
        found
    }

    /// Every mention of the name at `offset` (UTF-16) of `path`.
    #[must_use]
    pub fn references(&self, path: &str, offset: usize) -> Vec<Target> {
        self.compiler.references(path, offset, self.text_of(path))
    }

    // MARK: Libraries

    /// An assembly member. Time, a random number, input, the engine are
    /// sources; a constant (`Vector3.zero`) is a constant source; a
    /// transformation (`Math.Max`, `list.Count`, `ToString()`) is not a
    /// source — the value comes from the receiver, and the arguments are
    /// sources of their own. An unknown member: from the receiver when that
    /// is in the project, or else the source "assembly".
    #[allow(clippy::too_many_arguments)]
    fn library(
        &self,
        source: &flow::Source,
        type_name: &str,
        member: &str,
        at: Option<Decl>,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Vec<Source> {
        let title = format!("{}{}", source.chain, if source.call { "()" } else { "" });
        // `Mathf.Clamp`, `Math.Min`: a member of a type, not of a value — no receiver.
        let cleaned = origins::clean_type(type_name);
        let short_type = split_dots(&cleaned).last().map(|s| (*s).to_owned());
        let is_static = source
            .receiver_chain()
            .is_some_and(|r| split_dots(&r.chain).last().map(|s| (*s).to_owned()) == short_type);
        let received = || {
            if is_static {
                Vec::new()
            } else {
                self.receiver_sources(source, path, model, method, via, depth)
            }
        };
        match origins::classify(type_name, member) {
            Library::Origin(kind) => vec![Source::new(
                SourceKind::Origin(ValueOrigin::new(kind, title), at),
                via,
            )],
            Library::Constant => vec![Source::new(
                SourceKind::Origin(ValueOrigin::new(Kind::Constant, title), at),
                via,
            )],
            Library::Transform => received(),
            Library::Unknown => {
                let found = received();
                if found.is_empty() {
                    vec![Source::new(
                        SourceKind::Origin(ValueOrigin::new(Kind::Library, title), at),
                        via,
                    )]
                } else {
                    found
                }
            }
        }
    }

    /// What a member is taken from: `stats` of `stats.Count`, the call of
    /// `Get(e).Value`. A type (`Mathf` of `Mathf.Clamp`) is not a source:
    /// empty.
    fn receiver_sources(
        &self,
        source: &flow::Source,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Vec<Source> {
        if depth >= 8 {
            return Vec::new();
        }
        if let Some(receiver) = source.receiver_chain() {
            // A capitalized name the compiler does not know is rather a type than a value.
            return self
                .resolve(
                    std::slice::from_ref(&receiver),
                    path,
                    model,
                    method,
                    via,
                    depth + 1,
                )
                .into_iter()
                .filter(|s| match &s.kind {
                    SourceKind::Unknown(chain, None) => {
                        !chain.chars().next().is_some_and(char::is_uppercase)
                    }
                    _ => true,
                })
                .collect();
        }
        if source.member
            && let Some(chain) = &source.receiver
            && let Some(&name) = source.receiver_links.last()
        {
            let mut call = flow::Source::new(name, chain.clone(), true);
            call.links.clone_from(&source.receiver_links);
            call.head = source.receiver_links.first().copied();
            return self.resolve(
                std::slice::from_ref(&call),
                path,
                model,
                method,
                via,
                depth + 1,
            );
        }
        Vec::new()
    }

    /// What kind of assembly member the call `call` is; `None`: not an
    /// assembly's.
    fn library_kind(&self, call: &flow::Source, path: &str) -> Option<Library> {
        if let Some(target) = self.definition(path, call.range.location) {
            if !is_library(&target.path) {
                return None;
            }
            return Some(origins::classify(
                &target.container().unwrap_or_default(),
                &target.short_name(),
            ));
        }
        self.library_by_name(call, path)
            .map(|(t, m)| origins::classify(&t, &m))
    }

    /// A name the compiler does not know, but from a known library:
    /// `Math.Min`, `MathF.Round`, `Stopwatch.Frequency` (which the compiler
    /// on net8.0 may not see), `_random.Next()` of a field of type `Random`,
    /// `x.ToString()`. The type and the member, or `None`.
    fn library_by_name(&self, source: &flow::Source, path: &str) -> Option<(String, String)> {
        let words = split_dots(&source.chain);
        let member = (*words.last()?).to_owned();
        // Members of any value, string and collection: the compiler does not
        // know the receiver's type, but it is a transformation of what they
        // are taken from.
        if UNIVERSAL_MEMBERS.contains(&member.as_str()) && (source.call || member == "Length") {
            return Some(("object".into(), member));
        }
        if words.len() < 2 {
            return None;
        }
        let owner = words[words.len() - 2];
        // `Math.Min`: the type is the capitalized link before last.
        if owner.chars().next().is_some_and(char::is_uppercase)
            && origins::classify(owner, &member) != Library::Unknown
        {
            return Some((owner.to_owned(), member));
        }
        // `_random.Next()`: the field's type is from its declaration.
        if words.len() == 2
            && let Some(head) = source.head
            && let Some(target) = self.definition(path, head.location)
            && matches!(target.kind, DeclKind::Field | DeclKind::Property)
            && !is_library(&target.path)
            && let Some(type_name) = self.declared_type(&target)
            && origins::classify(&type_name, &member) != Library::Unknown
        {
            return Some((type_name, member));
        }
        None
    }

    /// A field's or property's type, as written in its declaration.
    fn declared_type(&self, target: &Target) -> Option<String> {
        let model = self.model(&target.path)?;
        let at = model.offset(target.line, target.character);
        self.outline(&target.path)
            .declarations
            .iter()
            .find(|d| d.name_range.contains(at))?
            .type_text
            .clone()
    }

    /// The head of a chain `a.b.c`, if it is a local or a parameter: where
    /// those come from.
    fn head_local(
        &self,
        source: &flow::Source,
        path: &str,
        model: &Arc<Document>,
        method: Option<&Declaration>,
        via: &[String],
        depth: usize,
    ) -> Option<Vec<Source>> {
        let method = method?;
        let head = source.head?;
        if head == source.range {
            return None;
        }
        let target = self.definition(path, head.location)?;
        if target.kind != DeclKind::Field {
            return None;
        }
        self.local(
            &target,
            &string(model.units(), head),
            method,
            path,
            model,
            via,
            depth,
        )
    }

    /// The local or parameter `target`, if its declaration is inside
    /// `method`. A parameter is a node that expands into the arguments of
    /// calls; a local is what is written into it in this method:
    /// assignments, `out` in a call, a `foreach` element. `None`: not one.
    #[allow(clippy::too_many_arguments)]
    fn local(
        &self,
        target: &Target,
        name: &str,
        method: &Declaration,
        path: &str,
        model: &Arc<Document>,
        via: &[String],
        depth: usize,
    ) -> Option<Vec<Source>> {
        if target.path != path {
            return None;
        }
        let units = model.units();
        let at = model.offset(target.line, target.character);
        if !method.full_range.contains(at) {
            return None;
        }
        if let Some(list) = parameters(method, units)
            && list.contains(at)
        {
            let Some(index) = parameter_index(name, method) else {
                return Some(Vec::new());
            };
            return Some(vec![Source::new(
                SourceKind::Parameter(
                    name.to_owned(),
                    Some(method_declaration(method, model, path)),
                    index,
                ),
                via,
            )]);
        }
        let declared = R::new(at, target.length);
        if flow::is_type_parameter(units, declared) {
            return Some(Vec::new());
        }
        let mut deeper = via.to_vec();
        deeper.push(name.to_owned());
        if flow::is_lambda_parameter(units, declared) {
            if depth < 6
                && let Some(found) =
                    self.lambda_sources(declared, path, model, Some(method), &deeper, depth + 1)
            {
                return Some(found);
            }
            return Some(vec![Source::new(
                SourceKind::Unknown(name.to_owned(), Some(Unknown::LambdaParameter)),
                via,
            )]);
        }
        // A cycle (`a = b; b = a;`) or too long a chain.
        if depth >= 6 || via.iter().any(|v| v == name) {
            return Some(Vec::new());
        }
        let writes = self.local_writes(at, method, path, model, &deeper, depth);
        if writes.is_empty() {
            return Some(vec![Source::new(
                SourceKind::Unknown(name.to_owned(), Some(Unknown::Local)),
                via,
            )]);
        }
        Some(writes.into_iter().flat_map(|w| w.sources).collect())
    }

    /// A field or property of this name: when there are several, the one
    /// whose type is mentioned in the file nearby.
    fn by_name(&self, name: &str, units: &[u16]) -> Option<Decl> {
        let symbols = self.symbols()?;
        let candidates: Vec<Symbol> = symbols
            .named(name)
            .into_iter()
            .filter(Symbol::is_value)
            .collect();
        if candidates.is_empty() {
            return None;
        }
        let text = String::from_utf16_lossy(units);
        let preferred = candidates.iter().find(|s| {
            s.container
                .as_deref()
                .and_then(last_part)
                .is_some_and(|owner| text.contains(owner))
        });
        let symbol = preferred.or(if candidates.len() == 1 {
            candidates.first()
        } else {
            None
        })?;
        Some(Decl {
            path: symbol.path.clone(),
            line: symbol.line,
            character: symbol.character,
            length: symbol.length,
            name: symbol.qualified(),
        })
    }

    // MARK: Where it is set: the Unity inspector

    /// The lines of prefabs, scenes and assets where a script's serialized
    /// field is set. That reads all the project's assets — seconds — so
    /// only on request. Whoever knows the Unity project finds them
    /// ([`Inspector`]).
    #[must_use]
    pub fn inspector_values(&self, value: &Decl) -> Vec<Site> {
        let declaration = self.named(value);
        let Some(inspector) = &self.inspector else {
            return Vec::new();
        };
        inspector
            .values(
                &self.root,
                &declaration.path,
                &declaration.short_name(),
                &declaration.title(),
            )
            .into_iter()
            .map(|hit| {
                let mut site = Site::new(&hit.path, hit.line, hit.line, hit.title.clone());
                site.is_data = true;
                site.preview = Excerpt {
                    first: hit.first,
                    lines: hit.lines.iter().map(|l| l.replace('\r', "")).collect(),
                };
                site
            })
            .collect()
    }

    // MARK: When it runs

    fn trigger(
        &self,
        model: &Arc<Document>,
        offset: usize,
        method: Option<&Declaration>,
    ) -> Option<(Trigger, usize)> {
        let method = method?;
        let units = model.units();
        let looped = flow::enclosing_foreach(units, method.full_range, offset)?;
        let expression = string(units, looped);
        // A filter right in the loop.
        if expression.contains("With<") || expression.contains("Without<") {
            let (with, without) = flow::filter_components(units, looped);
            return Some((
                Trigger::Filter {
                    name: String::new(),
                    with,
                    without,
                },
                model.line(looped.location),
            ));
        }
        // A field: its declaration and assignment.
        if !expression.chars().all(is_word) {
            return None;
        }
        // A host's receiver type (a loop over arriving messages).
        if let Some((trigger, at)) = self
            .edges
            .iter()
            .find_map(|e| e.trigger(self, units, &expression))
        {
            return Some((trigger, model.line(at)));
        }
        let name: Vec<u16> = expression.encode_utf16().collect();
        if let Some(found) = find_filter_assignment(units, &name) {
            let (with, without) = flow::filter_components(units, found);
            return Some((
                Trigger::Filter {
                    name: expression,
                    with,
                    without,
                },
                model.line(found.location),
            ));
        }
        None
    }

    // MARK: Small things

    /// A place at `offset` (UTF-16) of `path`: its line, the lines around
    /// it, the method around it and when it runs.
    #[must_use]
    pub fn make_site(
        &self,
        path: &str,
        model: &Arc<Document>,
        offset: usize,
        method: Option<&Declaration>,
    ) -> Site {
        let line = model.line(offset);
        let first = line.saturating_sub(1);
        let last = (model.line_count().max(1) - 1).min(line + 2);
        let mut site = Site::new(path, model.byte(offset), line, stem(path).to_owned());
        site.preview = model.excerpt(first, last);
        if let Some(method) = method {
            let owner = method.container.as_deref().and_then(last_part);
            site.title = match owner {
                Some(owner) => format!("{owner}.{}", method.name),
                None => method.name.clone(),
            };
            let top = model.line(method.full_range.location);
            let bottom = model.line(
                method
                    .full_range
                    .location
                    .max(method.full_range.end().saturating_sub(1)),
            );
            site.method_lines = Some((top, bottom.min(top + LINES_AFTER)));
        }
        if let Some((trigger, filter_line)) = self.trigger(model, offset, method) {
            site.trigger = Some(trigger);
            site.filter_line = Some(filter_line);
        }
        site
    }

    /// The member whose declaration holds `offset` (UTF-16), innermost.
    #[must_use]
    pub fn enclosing_member(&self, path: &str, offset: usize) -> Option<Declaration> {
        self.outline(path)
            .declarations
            .iter()
            .filter(|d| MEMBER_KINDS.contains(&d.kind) && d.full_range.contains(offset))
            .min_by_key(|d| d.full_range.length)
            .cloned()
    }

    /// The file's text: the unsaved one, or the disk's.
    #[must_use]
    pub fn model(&self, path: &str) -> Option<Arc<Document>> {
        if let Some(model) = self.models.borrow().get(path) {
            return Some(model.clone());
        }
        let text = match self.texts.get(path) {
            Some(text) => text.clone(),
            None => read_source(path)?,
        };
        let model = Arc::new(Document::new(&text));
        self.models
            .borrow_mut()
            .insert(path.to_owned(), model.clone());
        Some(model)
    }

    /// The file's outline from the compiler. A file that is not open is
    /// opened for the time of the question and closed after.
    #[must_use]
    pub fn outline(&self, path: &str) -> Arc<Outline> {
        if let Some(outline) = self.outlines.borrow().get(path) {
            return outline.clone();
        }
        let mut found = self.compiler.outline(path);
        if found.is_none() && self.compiler.open(path) {
            found = self.compiler.outline(path);
            self.compiler.close(path);
        }
        let outline = Arc::new(found.unwrap_or_default());
        self.outlines
            .borrow_mut()
            .insert(path.to_owned(), outline.clone());
        outline
    }
}

/// The text of a member's declaration before its name: attributes,
/// modifiers, the type.
fn head_of(member: &Declaration, units: &[u16]) -> String {
    string(
        units,
        R::new(
            member.full_range.location,
            member
                .name_range
                .location
                .saturating_sub(member.full_range.location),
        ),
    )
}

/// The key of `[JsonProperty("key")]` or `[JsonProperty(PropertyName =
/// "key")]` in a declaration's head; `attribute` is the attribute's name.
#[must_use]
pub fn json_property(head: &str, attribute: &str) -> Option<String> {
    let start = head.find(&format!("{attribute}("))? + attribute.len() + 1;
    let rest = &head[start..];
    let open = rest.find('"')?;
    let tail = &rest[open + 1..];
    let close = tail.find('"')?;
    let key = &tail[..close];
    (!key.is_empty()).then(|| key.to_owned())
}

/// A member declared `virtual` or `abstract`: it is overridden.
fn is_virtual(member: &Declaration, units: &[u16]) -> bool {
    head_of(member, units)
        .split(|c: char| !c.is_alphanumeric())
        .any(|w| w == "virtual" || w == "abstract")
}

/// `x.Changed += Name` (and `-=`): where the event's name `Changed` on the
/// left is. `None`: the name `name` is not a method group in a
/// subscription.
fn subscribed_event(units: &[u16], name: R) -> Option<usize> {
    let space = |c: u16| c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D;
    let mut after = name.end();
    while after < units.len() && space(units[after]) {
        after += 1;
    }
    if after < units.len()
        && ![u16::from(b';'), u16::from(b')'), u16::from(b',')].contains(&units[after])
    {
        return None;
    }
    let mut k = name.location;
    // `this.OnChanged` is a method group too.
    while k > 0
        && (space(units[k - 1])
            || units[k - 1] == u16::from(b'.')
            || flow::is_ident_part(units[k - 1]))
    {
        if units[k - 1] == u16::from(b'.') || flow::is_ident_part(units[k - 1]) {
            let mut w = k;
            while w > 0 && flow::is_ident_part(units[w - 1]) {
                w -= 1;
            }
            if string(units, R::new(w, k - w)) != "this" && w < k {
                break;
            }
            k = w;
            continue;
        }
        k -= 1;
    }
    while k > 0 && space(units[k - 1]) {
        k -= 1;
    }
    if !(k >= 2
        && units[k - 1] == u16::from(b'=')
        && (units[k - 2] == u16::from(b'+') || units[k - 2] == u16::from(b'-')))
    {
        return None;
    }
    let mut end = k - 2;
    while end > 0 && space(units[end - 1]) {
        end -= 1;
    }
    let mut start = end;
    while start > 0 && flow::is_ident_part(units[start - 1]) {
        start -= 1;
    }
    (start < end).then_some(start)
}

/// A call of an event or delegate by its name: `Changed?.Invoke(…)`,
/// `Changed.Invoke(…)`, `Changed(…)` — the name `flow::argument` finds the
/// arguments from.
fn invocation(units: &[u16], name: R) -> Option<R> {
    let space = |c: u16| c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D;
    let skip = |mut i: usize| {
        while i < units.len() && space(units[i]) {
            i += 1;
        }
        i
    };
    let mut i = skip(name.end());
    if i < units.len() && units[i] == u16::from(b'(') {
        return Some(name);
    }
    if i < units.len() && units[i] == u16::from(b'?') {
        i += 1;
    }
    if !(i < units.len() && units[i] == u16::from(b'.')) {
        return None;
    }
    let start = skip(i + 1);
    let mut end = start;
    while end < units.len() && flow::is_ident_part(units[end]) {
        end += 1;
    }
    let after = skip(end);
    (string(units, R::new(start, end - start)) == "Invoke"
        && after < units.len()
        && units[after] == u16::from(b'('))
    .then(|| R::new(start, end - start))
}

/// The body of the expression lambda a local `name` was declared with
/// before `before`: `5` of `Func<int> make = () => 5`. A lambda with a
/// block: `None`.
fn local_lambda_body(units: &[u16], name: &str, method: R, before: usize) -> Option<R> {
    let initializer = flow::local_initializer(units, name, method, before)?;
    let text = string(units, initializer);
    let arrow = text.find("=>")?;
    // The arrow right after the parameters: `x => …`, `(a, b) => …`, `() => …`.
    let head = text[..arrow].trim();
    let parameters = head.strip_prefix("static ").unwrap_or(head).trim();
    let simple = parameters.chars().all(|c| c.is_alphanumeric() || c == '_');
    let listed = parameters.starts_with('(') && parameters.ends_with(')');
    if !(simple || listed) {
        return None;
    }
    let start = initializer.location + text[..arrow + 2].encode_utf16().count();
    let body = R::new(start, initializer.end() - start);
    let skipped = string(units, body);
    let lead = skipped[..skipped.len() - skipped.trim_start().len()]
        .encode_utf16()
        .count();
    let body = R::new(body.location + lead, body.length - lead);
    (body.length > 0 && units[body.location] != u16::from(b'{')).then_some(body)
}

/// An assembly member as a source: time, random, the engine; a constant;
/// otherwise "assembly".
fn library_origin(type_name: &str, member: &str, title: &str) -> ValueOrigin {
    match origins::classify(type_name, member) {
        Library::Origin(kind) => ValueOrigin::new(kind, title),
        Library::Constant => ValueOrigin::new(Kind::Constant, title),
        Library::Transform | Library::Unknown => ValueOrigin::new(Kind::Library, title),
    }
}

/// A compiler's target as a value's declaration.
#[must_use]
pub fn declaration_of(target: &Target) -> Decl {
    Decl {
        path: target.path.clone(),
        line: target.line,
        character: target.character,
        length: target.length,
        name: target.name.clone(),
    }
}

fn method_declaration(method: &Declaration, model: &Document, path: &str) -> Decl {
    let (line, character) = model.position(method.name_range.location);
    Decl {
        path: path.to_owned(),
        line,
        character,
        length: method.name_range.length,
        name: qualified(method.container.as_deref(), &method.name),
    }
}

fn qualified(container: Option<&str>, name: &str) -> String {
    match container {
        Some(container) => format!("{container}.{name}"),
        None => name.to_owned(),
    }
}

/// The last link of a dotted name.
fn last_part(name: &str) -> Option<&str> {
    name.split('.').rfind(|p| !p.is_empty())
}

fn split_dots(text: &str) -> Vec<&str> {
    text.split('.').filter(|p| !p.is_empty()).collect()
}

/// An extension method called on a receiver (`x.M(a)`): `x` is its `this`
/// parameter, and the argument numbers shift by one. `Ext.M(x, a)` is an
/// ordinary static call.
fn is_extension_call(method: Option<&Declaration>, name: R, units: &[u16]) -> bool {
    let Some(method) = method else { return false };
    if !(method.is_extension_method
        || method
            .parameters
            .first()
            .is_some_and(|p| p.starts_with("this ")))
    {
        return false;
    }
    if flow::receiver_expression(units, name).is_none() {
        return false;
    }
    let chain = flow::chain(units, name);
    let parts = split_dots(&chain);
    let owner = method.container.as_deref().and_then(last_part);
    !(parts.len() >= 2 && Some(parts[parts.len() - 2]) == owner)
}

/// A compiled assembly: `.dll` or `.exe`.
#[must_use]
pub fn is_assembly(path: &str) -> bool {
    let extension = extension(path).to_lowercase();
    extension == "dll" || extension == "exe"
}

/// Someone else's code: an assembly, or a Unity package from
/// `Library/PackageCache` — its sources are there, but it is not the
/// project's code, and the graph does not go into it.
#[must_use]
pub fn is_library(path: &str) -> bool {
    is_assembly(path) || path.contains("/Library/PackageCache/")
}

/// The name of an assembly or package: `UnityEngine.CoreModule`,
/// `com.example.ecs`.
#[must_use]
pub fn library_name(path: &str) -> Option<String> {
    if is_assembly(path) {
        return Some(stem(path).to_owned());
    }
    let parts: Vec<&str> = path.split('/').filter(|p| !p.is_empty()).collect();
    let at = parts.iter().position(|&p| p == "PackageCache")?;
    let package = parts.get(at + 1)?;
    package
        .split('@')
        .find(|p| !p.is_empty())
        .map(str::to_owned)
}

/// A literal for a title: a long string is cut.
#[must_use]
pub fn clip(text: &str) -> String {
    let single = text.replace('\n', " ");
    if letters(&single).len() > 48 {
        format!("{}…", prefix_letters(&single, 47))
    } else {
        single
    }
}

/// A member's parameter brackets: `(…)` of a method and `[…]` of an
/// indexer `this[int i]`.
fn parameters(member: &Declaration, units: &[u16]) -> Option<R> {
    if let Some(list) = flow::parameter_list(units, member.name_range) {
        return Some(list);
    }
    if member.kind != DeclKind::Indexer {
        return None;
    }
    let mut i = member.name_range.end();
    while i < units.len() && (units[i] == 0x20 || units[i] == 0x09) {
        i += 1;
    }
    if !(i < units.len() && units[i] == 0x5B) {
        return None;
    }
    let close = flow::matching(units, i);
    (close > i.cast_signed()).then(|| R::new(i + 1, close.cast_unsigned() - i - 1))
}

/// `ref T x`, `in T x = 1`: a parameter's number by its name.
fn parameter_index(name: &str, method: &Declaration) -> Option<usize> {
    method.parameters.iter().position(|parameter| {
        let head = parameter
            .split('=')
            .find(|p| !p.is_empty())
            .unwrap_or(parameter);
        head.split([' ', '\t']).rfind(|p| !p.is_empty()) == Some(name)
    })
}

/// The first occurrence of `needle` in `haystack`.
fn find(haystack: &[u16], needle: &[u16]) -> Option<usize> {
    if needle.is_empty() || needle.len() > haystack.len() {
        return None;
    }
    (0..=haystack.len() - needle.len()).find(|&i| haystack[i..i + needle.len()] == needle[..])
}

/// `\s` of a regular expression.
fn regex_space(c: u16) -> bool {
    char::from_u32(u32::from(c)).is_some_and(char::is_whitespace)
}

/// `\w` of a regular expression.
fn regex_word(c: u16) -> bool {
    char::from_u32(u32::from(c)).is_none_or(|ch| {
        ch.is_alphanumeric()
            || ch == '_'
            || matches!(ch, '\u{300}'..='\u{36f}' | '\u{200c}' | '\u{200d}')
    })
}

/// `\b<name>\s*=\s*[^;]*Filter[^;]*;`: the first match.
fn find_filter_assignment(units: &[u16], name: &[u16]) -> Option<R> {
    let filter: Vec<u16> = "Filter".encode_utf16().collect();
    if name.is_empty() {
        return None;
    }
    let mut p = 0;
    while p + name.len() <= units.len() {
        if units[p..p + name.len()] != name[..] || (p > 0 && regex_word(units[p - 1])) {
            p += 1;
            continue;
        }
        let mut i = p + name.len();
        while i < units.len() && regex_space(units[i]) {
            i += 1;
        }
        if units.get(i) == Some(&0x3D) {
            let rest = i + 1;
            if let Some(semicolon) = (rest..units.len()).find(|&k| units[k] == 0x3B)
                && find(&units[rest..semicolon], &filter).is_some()
            {
                return Some(R::new(p, semicolon + 1 - p));
            }
        }
        p += 1;
    }
    None
}

/// `<receiver>\s*<\s*([\w.]+)\s*>\s+<name>\b`: the first match — where it
/// is and the type in the angle brackets. For hosts whose loops run over a
/// receiver of a message type (`Receiver<T> name`).
#[must_use]
pub fn find_receiver_declaration(
    units: &[u16],
    receiver: &[u16],
    name: &[u16],
) -> Option<(usize, String)> {
    if receiver.is_empty() {
        return None;
    }
    let mut p = 0;
    while p + receiver.len() <= units.len() {
        if units[p..p + receiver.len()] != receiver[..] {
            p += 1;
            continue;
        }
        let mut i = p + receiver.len();
        while i < units.len() && regex_space(units[i]) {
            i += 1;
        }
        let attempt = (|| {
            if units.get(i) != Some(&0x3C) {
                return None;
            }
            i += 1;
            while i < units.len() && regex_space(units[i]) {
                i += 1;
            }
            let type_start = i;
            while i < units.len() && (regex_word(units[i]) || units[i] == 0x2E) {
                i += 1;
            }
            if i == type_start {
                return None;
            }
            let type_end = i;
            while i < units.len() && regex_space(units[i]) {
                i += 1;
            }
            if units.get(i) != Some(&0x3E) {
                return None;
            }
            i += 1;
            let spaces = i;
            while i < units.len() && regex_space(units[i]) {
                i += 1;
            }
            if i == spaces || i + name.len() > units.len() || units[i..i + name.len()] != name[..] {
                return None;
            }
            let end = i + name.len();
            if end < units.len() && regex_word(units[end]) {
                return None;
            }
            Some(String::from_utf16_lossy(&units[type_start..type_end]))
        })();
        if let Some(type_name) = attempt {
            return Some((p, type_name));
        }
        p += 1;
    }
    None
}
