//! The project's own code as a graph: who calls whom, who reads and writes
//! which field, which ECS component a member reads and which it writes, and
//! where the code names a sink.
//!
//! Every own file is read once ([`rustlyn_ide::semantic::Semantic::links`]):
//! each name in it comes with the symbol the compiler settled on. A name
//! that lands in a sink is a hit; one that lands in own code is an edge
//! between two members. What the compiler cannot say — whether a field is
//! read or written there, what is done to a component through its stash —
//! is read off the text around the name.

use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use rustlyn_ide::DeclarationKind;
use rustlyn_ide::semantic::{LinkRole, LinkSymbol, Place, Semantic};

use super::config::Config;
use super::text;
use crate::blast::ask::absolute;
use crate::blast::changes::{Member, Members};
use crate::blast::walk::{relative_to, sources};
use crate::deep;

/// A member or type of the project's own code, by its index in the graph.
pub type NodeId = u32;

/// How one member depends on another.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeKind {
    /// Calls it: a method, a constructor, an operator.
    Calls,
    /// Reads the field or property.
    Reads,
    /// Writes it.
    Writes,
    /// Reads the ECS component: gets it, tests for it, filters by it.
    ReadsComponent,
    /// Sets, adds or removes the component, or writes one of its fields.
    WritesComponent,
    /// Derives from the type or implements the interface.
    Derives,
}

/// A dependency, at the place in the code that shows it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub from: NodeId,
    pub to: NodeId,
    pub kind: EdgeKind,
    /// The line of the name, from zero, in `from`'s file.
    pub line: u32,
    /// The lines of the statement it is in, first and last.
    pub statement: (u32, u32),
    /// The name, in bytes from the start of `from`'s file.
    pub offset: u32,
}

/// A place where own code names a sink.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hit {
    pub from: NodeId,
    /// The sink's index in the configuration.
    pub sink: usize,
    /// What is named: `Store.Pay`, or a type's name.
    pub name: String,
    pub line: u32,
    pub statement: (u32, u32),
    pub offset: u32,
    /// In a base list: the type derives from the sink's.
    pub base: bool,
}

/// One own file.
#[derive(Debug, Clone)]
pub struct OwnFile {
    /// Relative to the root.
    pub path: String,
    pub members: Members,
    first: NodeId,
}

/// The graph of one configuration of the project.
#[derive(Debug, Default)]
pub struct Graph {
    pub files: Vec<OwnFile>,
    by_path: HashMap<String, usize>,
    /// Which file each node is in.
    file_of: Vec<u32>,
    pub edges: Vec<Edge>,
    incoming: Vec<Vec<u32>>,
    outgoing: Vec<Vec<u32>>,
    pub hits: Vec<Hit>,
    /// Types by qualified name.
    types: HashMap<String, NodeId>,
    /// Files the compiler could not answer about.
    pub failed: usize,
}

impl Graph {
    #[must_use]
    pub fn member(&self, node: NodeId) -> &Member {
        let file = &self.files[self.file_of[node as usize] as usize];
        &file.members.list[(node - file.first) as usize]
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.file_of.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.file_of.is_empty()
    }

    /// The edges that end at `node`.
    pub fn incoming(&self, node: NodeId) -> impl Iterator<Item = &Edge> {
        self.incoming[node as usize]
            .iter()
            .map(|&edge| &self.edges[edge as usize])
    }

    /// The edges that start at `node`.
    pub fn outgoing(&self, node: NodeId) -> impl Iterator<Item = &Edge> {
        self.outgoing[node as usize]
            .iter()
            .map(|&edge| &self.edges[edge as usize])
    }

    #[must_use]
    pub fn file(&self, path: &str) -> Option<&OwnFile> {
        self.by_path.get(path).map(|&index| &self.files[index])
    }

    /// The node of a member of `file`, by its index in the file's members.
    #[must_use]
    pub fn node_of(&self, file: &OwnFile, member: &Member) -> Option<NodeId> {
        let index = file
            .members
            .list
            .iter()
            .position(|other| other.key == member.key && other.line == member.line)?;
        Some(file.first + u32::try_from(index).ok()?)
    }

    /// The node of the type `member` is declared in.
    #[must_use]
    pub fn container_of(&self, node: NodeId) -> Option<NodeId> {
        let container = self.member(node).container.as_deref()?;
        let file = &self.files[self.file_of[node as usize] as usize];
        let index = file
            .members
            .list
            .iter()
            .position(|other| other.is_type() && other.name == container)?;
        Some(file.first + u32::try_from(index).ok()?)
    }

    /// The members declared in the type `node`, in its file.
    #[must_use]
    pub fn members_of(&self, node: NodeId) -> Vec<NodeId> {
        let name = &self.member(node).name;
        let file = &self.files[self.file_of[node as usize] as usize];
        file.members
            .list
            .iter()
            .enumerate()
            .filter(|(_, member)| member.container.as_deref() == Some(name.as_str()))
            .filter_map(|(index, _)| Some(file.first + u32::try_from(index).ok()?))
            .collect()
    }

    /// How many own types derive from the type `node` or implement it.
    #[must_use]
    pub fn derived(&self, node: NodeId) -> usize {
        self.incoming(node)
            .filter(|edge| edge.kind == EdgeKind::Derives)
            .count()
    }

    /// The own node a symbol of the compilation is declared as.
    #[must_use]
    pub fn node_of_symbol(
        &self,
        root: &str,
        semantic: &Semantic,
        symbol: LinkSymbol,
    ) -> Option<NodeId> {
        let Some(Place::Source { path, span }) = semantic.link_target(symbol).place else {
            return None;
        };
        let path = relative_to(root, &absolute(root, &path));
        let file = self.file(&path)?;
        let offset = span.start() as usize;
        let index = file
            .members
            .list
            .iter()
            .position(|member| member.offset == offset)?;
        Some(file.first + u32::try_from(index).ok()?)
    }
}

/// What a symbol is to the graph, worked out once per symbol.
#[derive(Debug)]
struct Target {
    kind: DeclarationKind,
    /// Declared in an own file: the file and the offset of its name.
    own: Option<(u32, usize)>,
    /// A sink's: which, and how to call it in a report.
    sink: Option<(usize, String)>,
    /// A stash: the qualified name of its component.
    component: Option<String>,
}

/// An edge before its target is a node: the target's file may not have been
/// read yet.
#[derive(Debug)]
enum RawTarget {
    Own(u32, usize),
    Type(String),
}

#[derive(Debug)]
struct Raw {
    owner: u32,
    target: RawTarget,
    kind: EdgeKind,
    line: u32,
    statement: (u32, u32),
    offset: u32,
}

#[derive(Debug)]
struct RawHit {
    owner: u32,
    sink: usize,
    name: String,
    line: u32,
    statement: (u32, u32),
    offset: u32,
    base: bool,
}

#[derive(Debug, Default)]
struct RawFile {
    members: Option<Members>,
    edges: Vec<Raw>,
    hits: Vec<RawHit>,
}

/// The type names a stash is written as: `Stash<Health>`.
const STASH_TYPES: &[&str] = &["Stash"];

/// What a stash's methods do to its component. Anything else reads.
const STASH_WRITES: &[&str] = &[
    "Set",
    "Add",
    "Remove",
    "RemoveAll",
    "SetOrUpdate",
    "Migrate",
];
/// A stash's methods that hand out the component by reference.
const STASH_REFS: &[&str] = &["Get", "Add", "TryGet", "GetOrAdd"];

/// Generic methods whose type argument is a component they read.
const COMPONENT_READS: &[&str] = &["With", "Without", "Has", "GetComponent", "TryGetComponent"];
/// Generic methods whose type argument is a component they write.
const COMPONENT_WRITES: &[&str] = &["AddComponent", "SetComponent", "RemoveComponent"];

/// Builds the graph of the compiled project in `root`.
#[must_use]
pub fn build(root: &str, semantic: &Semantic, config: &Config) -> Graph {
    let mut paths: Vec<String> = Vec::new();
    sources(Path::new(root), Path::new(root), &mut paths);
    paths.retain(|path| config.is_own(path));
    paths.sort();
    let by_path: HashMap<String, usize> = paths
        .iter()
        .enumerate()
        .map(|(index, path)| (path.clone(), index))
        .collect();

    let targets: Mutex<HashMap<LinkSymbol, Arc<Target>>> = Mutex::new(HashMap::new());
    let next = AtomicUsize::new(0);
    let done: Mutex<Vec<(usize, RawFile)>> = Mutex::new(Vec::with_capacity(paths.len()));
    let failed = AtomicUsize::new(0);
    let context = Context {
        root,
        semantic,
        config,
        by_path: &by_path,
        targets: &targets,
    };
    std::thread::scope(|scope| {
        for _ in 0..threads(paths.len()) {
            let _ = std::thread::Builder::new()
                .name("rustlyn-reach".into())
                .stack_size(deep::SIZE)
                .spawn_scoped(scope, || {
                    let mut local = Vec::new();
                    loop {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some(path) = paths.get(index) else {
                            break;
                        };
                        let read = catch_unwind(AssertUnwindSafe(|| read_file(&context, path)));
                        let file = read.unwrap_or_else(|_| {
                            failed.fetch_add(1, Ordering::Relaxed);
                            RawFile::default()
                        });
                        local.push((index, file));
                    }
                    if let Ok(mut done) = done.lock() {
                        done.append(&mut local);
                    }
                });
        }
    });
    let mut read = done.into_inner().unwrap_or_default();
    read.sort_by_key(|(index, _)| *index);

    let mut graph = Graph {
        by_path,
        failed: failed.into_inner(),
        ..Graph::default()
    };
    // Nodes: every member of every file, in the order of the files.
    let mut raw: Vec<(Vec<Raw>, Vec<RawHit>)> = Vec::with_capacity(read.len());
    for ((_, file), path) in read.into_iter().zip(&paths) {
        let members = file.members.unwrap_or(Members { list: Vec::new() });
        let first = graph.file_of.len() as NodeId;
        let index = graph.files.len() as u32;
        for member in &members.list {
            if member.is_type() {
                graph
                    .types
                    .entry(member.name.clone())
                    .or_insert(graph.file_of.len() as NodeId);
            }
            graph.file_of.push(index);
        }
        graph.files.push(OwnFile {
            path: path.clone(),
            members,
            first,
        });
        raw.push((file.edges, file.hits));
    }
    // Edges: each target found among the nodes.
    let by_offset: Vec<HashMap<usize, u32>> = graph
        .files
        .iter()
        .map(|file| {
            file.members
                .list
                .iter()
                .enumerate()
                .map(|(index, member)| (member.offset, index as u32))
                .collect()
        })
        .collect();
    for (index, (edges, hits)) in raw.into_iter().enumerate() {
        let first = graph.files[index].first;
        for edge in edges {
            let to = match edge.target {
                RawTarget::Own(file, offset) => by_offset[file as usize]
                    .get(&offset)
                    .map(|&member| graph.files[file as usize].first + member),
                RawTarget::Type(name) => graph.types.get(&name).copied(),
            };
            let from = first + edge.owner;
            if let Some(to) = to
                && to != from
            {
                graph.edges.push(Edge {
                    from,
                    to,
                    kind: edge.kind,
                    line: edge.line,
                    statement: edge.statement,
                    offset: edge.offset,
                });
            }
        }
        for hit in hits {
            graph.hits.push(Hit {
                from: first + hit.owner,
                sink: hit.sink,
                name: hit.name,
                line: hit.line,
                statement: hit.statement,
                offset: hit.offset,
                base: hit.base,
            });
        }
    }
    graph.incoming = vec![Vec::new(); graph.file_of.len()];
    graph.outgoing = vec![Vec::new(); graph.file_of.len()];
    for (index, edge) in graph.edges.iter().enumerate() {
        graph.incoming[edge.to as usize].push(index as u32);
        graph.outgoing[edge.from as usize].push(index as u32);
    }
    graph
}

/// Threads for `jobs` files: what `RUSTLYN_THREADS` says, else one per core.
fn threads(jobs: usize) -> usize {
    std::env::var("RUSTLYN_THREADS")
        .ok()
        .and_then(|value| value.parse().ok())
        .filter(|&count: &usize| count > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, usize::from))
        .min(jobs.max(1))
}

struct Context<'a> {
    root: &'a str,
    semantic: &'a Semantic,
    config: &'a Config,
    by_path: &'a HashMap<String, usize>,
    targets: &'a Mutex<HashMap<LinkSymbol, Arc<Target>>>,
}

impl Context<'_> {
    fn target(&self, symbol: LinkSymbol) -> Arc<Target> {
        if let Ok(known) = self.targets.lock()
            && let Some(target) = known.get(&symbol)
        {
            return target.clone();
        }
        let target = Arc::new(self.describe(symbol));
        if let Ok(mut known) = self.targets.lock() {
            known.insert(symbol, target.clone());
        }
        target
    }

    fn describe(&self, symbol: LinkSymbol) -> Target {
        let found = self.semantic.link_target(symbol);
        let mut target = Target {
            kind: found.kind,
            own: None,
            sink: None,
            component: None,
        };
        if found.kind == DeclarationKind::Namespace {
            return target;
        }
        let display = || {
            if found.kind.is_type() {
                found.name.clone()
            } else {
                let holder = found.container.rsplit('.').next().unwrap_or_default();
                format!("{holder}.{}", found.name)
            }
        };
        match &found.place {
            Some(Place::Source { path, span }) => {
                let path = relative_to(self.root, &absolute(self.root, path));
                if let Some(&file) = self.by_path.get(&path) {
                    target.own = Some((file as u32, span.start() as usize));
                } else if let Some(sink) = self.config.sink_of_path(&path) {
                    target.sink = Some((sink, display()));
                }
            }
            Some(Place::Metadata { assembly, .. }) => {
                let stem = assembly
                    .file_stem()
                    .map(|stem| stem.to_string_lossy().into_owned())
                    .unwrap_or_default();
                if let Some(sink) = self.config.sink_of_assembly(&stem) {
                    target.sink = Some((sink, display()));
                }
            }
            None => {}
        }
        if target.own.is_none()
            && target.sink.is_none()
            && let Some(sink) =
                self.config
                    .sink_of_symbol(&found.name, &found.container, found.kind.is_type())
        {
            target.sink = Some((sink, display()));
        }
        if let Some(ty) = &found.type_text {
            target.component = stash_component(ty);
        }
        target
    }
}

/// The component of a stash type as the compiler writes it:
/// `Scellecs.Morpeh.Stash<Game.Health>` → `Game.Health`.
fn stash_component(type_text: &str) -> Option<String> {
    let compact: String = type_text.chars().filter(|&c| c != ' ').collect();
    let (head, rest) = compact.split_once('<')?;
    let name = head.rsplit('.').next()?;
    if !STASH_TYPES.contains(&name) {
        return None;
    }
    let inner = rest.strip_suffix('>')?;
    (!inner.contains([',', '<'])).then(|| inner.trim_start_matches("global::").to_owned())
}

fn read_file(context: &Context<'_>, path: &str) -> RawFile {
    let semantic = context.semantic;
    let full = Path::new(context.root).join(path);
    let (links, source) = match semantic.links(&full) {
        Some(links) => (links, semantic.text(&full)),
        None => match semantic.links(Path::new(path)) {
            Some(links) => (links, semantic.text(Path::new(path))),
            None => return RawFile::default(),
        },
    };
    let Some(source) = source else {
        return RawFile::default();
    };
    let members = Members::of_outline(path, source, &links.outline);
    let bytes = source.as_bytes();
    let mut file = RawFile::default();
    // The innermost member around each line, asked for link after link.
    let mut owners: HashMap<u32, Option<u32>> = HashMap::new();
    let mut owner_at = |line: u32| {
        *owners.entry(line).or_insert_with(|| {
            let inner = members.enclosing(line as usize)?;
            let index = members
                .list
                .iter()
                .position(|member| std::ptr::eq(member, inner))?;
            u32::try_from(index).ok()
        })
    };
    for link in &links.links {
        let Some(owner) = owner_at(link.line) else {
            continue;
        };
        let target = context.target(link.target);
        if let Some((sink, name)) = &target.sink {
            file.hits.push(RawHit {
                owner,
                sink: *sink,
                name: name.clone(),
                line: link.line,
                statement: link.statement,
                offset: link.span.start(),
                base: link.role == LinkRole::Base,
            });
            continue;
        }
        let start = link.span.start() as usize;
        let end = link.span.end() as usize;
        let mut push = |target: RawTarget, kind: EdgeKind| {
            file.edges.push(Raw {
                owner,
                target,
                kind,
                line: link.line,
                statement: link.statement,
                offset: link.span.start(),
            });
        };
        if link.role == LinkRole::Base {
            if let Some((to, offset)) = target.own
                && target.kind.is_type()
            {
                push(RawTarget::Own(to, offset), EdgeKind::Derives);
            }
            continue;
        }
        if link.role != LinkRole::Body {
            continue;
        }
        // A stash: what is done to its component.
        if let Some(component) = &target.component {
            let method = text::method_after(bytes, end);
            let writes = method.is_some_and(|method| STASH_WRITES.contains(&method));
            let by_reference = method.is_some_and(|method| STASH_REFS.contains(&method));
            if writes {
                push(
                    RawTarget::Type(component.clone()),
                    EdgeKind::WritesComponent,
                );
            } else {
                push(RawTarget::Type(component.clone()), EdgeKind::ReadsComponent);
            }
            if by_reference && !writes {
                let limit = members.list[owner as usize].lines.end;
                let limit = text::line_start(bytes, limit);
                if text::writes_through(bytes, start, end, limit) {
                    push(
                        RawTarget::Type(component.clone()),
                        EdgeKind::WritesComponent,
                    );
                }
            }
            // The stash is a field too: fall through to its read.
        }
        let Some((to, offset)) = target.own else {
            continue;
        };
        let own = RawTarget::Own(to, offset);
        match target.kind {
            DeclarationKind::Method
            | DeclarationKind::Constructor
            | DeclarationKind::Destructor
            | DeclarationKind::Operator
            | DeclarationKind::Indexer
            | DeclarationKind::Delegate => push(own, EdgeKind::Calls),
            DeclarationKind::Property
            | DeclarationKind::Event
            | DeclarationKind::Field
            | DeclarationKind::EnumMember => match text::access(bytes, start, end) {
                text::Access::Read => push(own, EdgeKind::Reads),
                text::Access::Write => push(own, EdgeKind::Writes),
                text::Access::Both => {
                    push(RawTarget::Own(to, offset), EdgeKind::Reads);
                    push(own, EdgeKind::Writes);
                }
            },
            kind if kind.is_type() => match text::generic_owner(bytes, start) {
                Some(method) if COMPONENT_READS.contains(&method) => {
                    push(own, EdgeKind::ReadsComponent);
                }
                Some(method) if COMPONENT_WRITES.contains(&method) => {
                    push(own, EdgeKind::WritesComponent);
                }
                _ => {}
            },
            _ => {}
        }
    }
    // `Tracker.Start()` names the type and the method: the method says more.
    let hits = std::mem::take(&mut file.hits);
    for (index, hit) in hits.iter().enumerate() {
        let said_better = hits.get(index + 1).is_some_and(|next| {
            next.owner == hit.owner
                && next.line == hit.line
                && next
                    .name
                    .strip_prefix(hit.name.as_str())
                    .is_some_and(|rest| rest.starts_with('.'))
        });
        if !said_better {
            file.hits.push(RawHit {
                name: hit.name.clone(),
                ..*hit
            });
        }
    }
    file.members = Some(members);
    file
}
