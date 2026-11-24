//! The cone of a set of sinks: every member whose change can alter what
//! reaches them, each with the lines of it that matter. The walk goes
//! backward from the places that name a sink:
//!
//! * a member that names a sink — calls it, reads it, takes its type —
//!   starts the cone, all of it, and so do the members of a type that
//!   derives from a sink's type (the sink calls them);
//! * who calls a member of the cone is in it, by the *slice* of the calling
//!   statement: the statement, the conditions it runs under, what leaves
//!   before it, and what gives the locals those mention their values
//!   ([`rustlyn_ide::semantic::Semantic::slice`]);
//! * a field or property the cone reads on the lines that matter is in it,
//!   and so is who writes it, by the slice of the write;
//! * an ECS component read there is in it, and so is who sets, adds or
//!   removes it: two systems that never call each other are linked by the
//!   component one writes and the other reads;
//! * a method called on the lines that matter, and from the cone only, is
//!   in it, all of it: it exists to serve the cone, and what it returns and
//!   does is part of what reaches the sink.
//!
//! Followed without bound, this reaches most of a project: everything
//! depends on everything through enough hands. These limits keep the cone
//! to the code that is about the sinks:
//!
//! * A member with many callers is the project's own API over the sink
//!   (`Analytics.Track`): its callers are *users* — the slice of the
//!   calling statement concerns the sink, and the walk goes no further
//!   through them. The same holds for the cone's own field or component
//!   with many writers, and for a call through a base or an interface with
//!   several implementations: the caller does not know which one runs.
//! * A field or a component that code outside the cone reads as well is
//!   shared state — the game's phase, a link to a UI object. It is in the
//!   cone as data, since the cone reads it, but who writes it is not: they
//!   write it for everyone.
//! * Only so many steps of a path may go through data
//!   ([`super::Limits::data_hops`]).

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::path::Path;

use rustlyn_ide::DeclarationKind;
use rustlyn_ide::semantic::Semantic;

use super::config::Config;
use super::graph::{EdgeKind, Graph, NodeId};
use crate::value::UNIVERSAL_MEMBERS;

/// What a node is to the cone. Later ones take over earlier ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Role {
    /// Uses the cone through a hub or a base: the walk goes no further
    /// through it.
    User,
    /// A field, property or component read on the way to a sink.
    Data,
    /// A method called on the way: all of it matters.
    Helper,
    /// On a path to a sink.
    Path,
}

impl Role {
    /// The stable English code.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::User => "user",
            Self::Data => "data",
            Self::Helper => "helper",
            Self::Path => "path",
        }
    }
}

/// How a node leads on toward a sink.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Step {
    /// Calls the next node.
    Calls,
    /// Calls what the next node overrides or implements.
    CallsBase,
    /// Writes the next node: a field, a property, a component.
    Writes,
    /// Is read by the next node, at a line of that node's file.
    ReadBy,
    /// Is called by the next node, at a line of that node's file.
    CalledBy,
    /// Is a member of the next node, a type that derives from a sink's.
    MemberOf,
}

impl Step {
    /// The stable English code.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Calls => "calls",
            Self::CallsBase => "calls_base",
            Self::Writes => "writes",
            Self::ReadBy => "read_by",
            Self::CalledBy => "called_by",
            Self::MemberOf => "member_of",
        }
    }
}

/// Where a step shows in the code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Site {
    /// The line of the name, from zero.
    pub line: u32,
    /// The lines of its statement.
    pub statement: (u32, u32),
    /// The name, in bytes from the start of its file.
    pub offset: u32,
}

/// One reason a node is in the cone: the next thing toward a sink.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Via {
    /// Names the sink itself.
    Sink {
        sink: usize,
        name: String,
        site: Site,
        /// Derives from the sink's type.
        base: bool,
    },
    Node {
        next: NodeId,
        step: Step,
        site: Site,
    },
}

impl Via {
    /// The lines of the statement that makes the link, when it is in the
    /// node's own file.
    #[must_use]
    pub const fn own_statement(&self) -> Option<(u32, u32)> {
        match self {
            Self::Sink { site, .. }
            | Self::Node {
                step: Step::Calls | Step::CallsBase | Step::Writes,
                site,
                ..
            } => Some(site.statement),
            Self::Node { .. } => None,
        }
    }
}

/// A node of the cone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub role: Role,
    /// Steps from a sink.
    pub depth: usize,
    /// Of them, through data.
    pub hops: usize,
    /// The first is the shortest way on.
    pub vias: Vec<Via>,
    /// The lines of the member that matter, first and last of each run, in
    /// order; `None` when all of it does.
    pub lines: Option<Vec<(u32, u32)>>,
    /// How many helpers in a row lead to it.
    helpers: usize,
}

impl Entry {
    /// Whether a line of the member matters.
    #[must_use]
    pub fn matters(&self, line: u32) -> bool {
        self.lines.as_ref().is_none_or(|lines| {
            lines
                .iter()
                .any(|&(first, last)| (first..=last).contains(&line))
        })
    }
}

/// A member with too many callers or writers to follow through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hub {
    pub node: NodeId,
    /// How many members call or write it.
    pub users: usize,
}

/// The cone of one configuration.
#[derive(Debug, Default)]
pub struct Cone {
    pub entries: BTreeMap<NodeId, Entry>,
    pub hubs: Vec<Hub>,
    /// The walk stopped at its depth somewhere.
    pub truncated: bool,
}

/// How many ways on a node keeps.
const VIAS: usize = 32;

/// How many helpers in a row the walk goes down: a helper's helper, and no
/// further.
const HELPERS: usize = 2;

struct Walk<'a> {
    root: &'a str,
    semantic: &'a Semantic,
    graph: &'a Graph,
    config: &'a Config,
    cone: Cone,
    queue: VecDeque<NodeId>,
}

/// What a node is added as.
struct Added {
    role: Role,
    depth: usize,
    hops: usize,
    helpers: usize,
    /// All of the member matters, not only the slice of the step's
    /// statement.
    whole: bool,
}

/// Walks backward from the sinks' hits.
#[must_use]
pub fn walk(root: &str, semantic: &Semantic, graph: &Graph, config: &Config) -> Cone {
    let mut walk = Walk {
        root,
        semantic,
        graph,
        config,
        cone: Cone::default(),
        queue: VecDeque::new(),
    };
    let seed = || Added {
        role: Role::Path,
        depth: 0,
        hops: 0,
        helpers: 0,
        whole: true,
    };
    for hit in &graph.hits {
        let via = Via::Sink {
            sink: hit.sink,
            name: hit.name.clone(),
            site: Site {
                line: hit.line,
                statement: hit.statement,
                offset: hit.offset,
            },
            base: hit.base,
        };
        walk.add(hit.from, seed(), via);
        if hit.base && graph.member(hit.from).is_type() {
            // The sink calls what implements its interface.
            for member in graph.members_of(hit.from) {
                let there = graph.member(member);
                let line = there.line as u32;
                let via = Via::Node {
                    next: hit.from,
                    step: Step::MemberOf,
                    site: Site {
                        line,
                        statement: (line, line),
                        offset: there.offset as u32,
                    },
                };
                walk.add(member, seed(), via);
            }
        }
    }
    loop {
        while let Some(node) = walk.queue.pop_front() {
            walk.expand(node);
        }
        if !walk.helpers() {
            break;
        }
    }
    walk.cone
        .hubs
        .sort_by(|a, b| b.users.cmp(&a.users).then(a.node.cmp(&b.node)));
    walk.cone.hubs.dedup_by_key(|hub| hub.node);
    walk.cone
}

/// Two sets of line runs as one.
fn union(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut all: Vec<(u32, u32)> = a.iter().chain(b).copied().collect();
    all.sort_unstable();
    let mut merged: Vec<(u32, u32)> = Vec::new();
    for (first, last) in all {
        match merged.last_mut() {
            Some(run) if first <= run.1 + 1 => run.1 = run.1.max(last),
            _ => merged.push((first, last)),
        }
    }
    merged
}

impl Walk<'_> {
    /// The slice of the statement a step shows at, in `node`'s file.
    fn slice(&self, node: NodeId, site: Site) -> Vec<(u32, u32)> {
        let path = &self.graph.member(node).path;
        let mut lines = self
            .semantic
            .slice(&Path::new(self.root).join(path), site.offset);
        if lines.is_empty() {
            lines = self.semantic.slice(Path::new(path), site.offset);
        }
        if lines.is_empty() {
            lines.push(site.statement);
        }
        lines
    }

    /// Puts a node in the cone, raises its role, or adds lines that matter.
    fn add(&mut self, node: NodeId, added: Added, via: Via) {
        if self.config.ignored(&self.graph.member(node).name) {
            return;
        }
        if let Via::Node { next, .. } = via
            && next == node
        {
            return;
        }
        // The lines the step makes matter: its statement's slice, when the
        // statement is the node's own.
        let lines = if added.whole || matches!(added.role, Role::Data | Role::Helper) {
            None
        } else {
            match &via {
                Via::Sink { site, .. }
                | Via::Node {
                    step: Step::Calls | Step::CallsBase | Step::Writes,
                    site,
                    ..
                } => Some(self.slice(node, *site)),
                Via::Node { .. } => None,
            }
        };
        let Some(entry) = self.cone.entries.get_mut(&node) else {
            self.cone.entries.insert(
                node,
                Entry {
                    role: added.role,
                    depth: added.depth,
                    hops: added.hops,
                    vias: vec![via],
                    lines,
                    helpers: added.helpers,
                },
            );
            if added.role != Role::User {
                self.queue.push_back(node);
            }
            return;
        };
        let grown = match (&entry.lines, &lines) {
            (None, _) => None,
            (Some(_), None) => Some(None),
            (Some(old), Some(new)) => {
                let all = union(old, new);
                (all != *old).then_some(Some(all))
            }
        };
        if added.role > entry.role {
            entry.role = added.role;
            entry.depth = added.depth;
            entry.hops = added.hops;
            entry.helpers = added.helpers;
            entry.vias.insert(0, via);
            if let Some(lines) = grown {
                entry.lines = lines;
            }
            self.queue.push_back(node);
            return;
        }
        if entry.vias.len() < VIAS && !entry.vias.contains(&via) {
            entry.vias.push(via);
        }
        // More of the member matters: a user's for a change to be judged
        // by, anything else's to be walked from as well.
        if added.role == entry.role
            && matches!(entry.role, Role::Path | Role::User)
            && let Some(lines) = grown
        {
            entry.lines = lines;
            if entry.role == Role::Path {
                self.queue.push_back(node);
            }
        }
    }

    fn expand(&mut self, node: NodeId) {
        let Some(entry) = self.cone.entries.get(&node).cloned() else {
            return;
        };
        if entry.depth >= self.config.limits.depth {
            self.cone.truncated = true;
            return;
        }
        let is_type = self.graph.member(node).is_type();
        match entry.role {
            Role::User => {}
            Role::Path => {
                if !is_type {
                    self.callers(node, &entry);
                }
                self.reads(node, &entry);
            }
            Role::Helper => self.reads(node, &entry),
            Role::Data => {
                let kind = if is_type {
                    EdgeKind::WritesComponent
                } else {
                    EdgeKind::Writes
                };
                self.writers(node, kind, &entry);
                // A property's getter reads on.
                if !is_type {
                    self.reads(node, &entry);
                }
            }
        }
    }

    /// The edges through which `node` is called: calls, and for a property
    /// or an event its reads and writes — they run its accessors.
    fn calls_into(&self, node: NodeId) -> Vec<(NodeId, Site)> {
        let accessors = matches!(
            self.graph.member(node).kind,
            DeclarationKind::Property | DeclarationKind::Event | DeclarationKind::Indexer
        );
        self.graph
            .incoming(node)
            .filter(|edge| {
                edge.kind == EdgeKind::Calls
                    || (accessors && matches!(edge.kind, EdgeKind::Reads | EdgeKind::Writes))
            })
            .map(|edge| {
                (
                    edge.from,
                    Site {
                        line: edge.line,
                        statement: edge.statement,
                        offset: edge.offset,
                    },
                )
            })
            .collect()
    }

    fn callers(&mut self, node: NodeId, entry: &Entry) {
        let limit = self.config.limits.hub_callers;
        let next = |role| Added {
            role,
            depth: entry.depth + 1,
            hops: entry.hops,
            helpers: 0,
            whole: false,
        };
        let calls = self.calls_into(node);
        let distinct: HashSet<NodeId> = calls.iter().map(|call| call.0).collect();
        let role = if distinct.len() > limit {
            self.cone.hubs.push(Hub {
                node,
                users: distinct.len(),
            });
            Role::User
        } else {
            Role::Path
        };
        for (from, site) in calls {
            let via = Via::Node {
                next: node,
                step: Step::Calls,
                site,
            };
            self.add(from, next(role), via);
        }
        // Calls to what it overrides or implements may run it. With one
        // implementation they do run it; with several, the caller only
        // uses whichever it is given.
        for base in self.bases(node) {
            let Some(holder) = self.graph.container_of(base) else {
                continue;
            };
            let calls = self.calls_into(base);
            let distinct: HashSet<NodeId> = calls.iter().map(|call| call.0).collect();
            if distinct.len() > limit {
                continue;
            }
            let role = if self.graph.derived(holder) <= 1 {
                Role::Path
            } else {
                Role::User
            };
            for (from, site) in calls {
                let via = Via::Node {
                    next: node,
                    step: Step::CallsBase,
                    site,
                };
                self.add(from, next(role), via);
            }
        }
    }

    /// The own members `node` overrides or implements.
    fn bases(&self, node: NodeId) -> Vec<NodeId> {
        let member = self.graph.member(node);
        if !matches!(
            member.kind,
            DeclarationKind::Method
                | DeclarationKind::Property
                | DeclarationKind::Indexer
                | DeclarationKind::Event
        ) || UNIVERSAL_MEMBERS.contains(&member.short_name())
        {
            return Vec::new();
        }
        let Ok(offset) = u32::try_from(member.offset) else {
            return Vec::new();
        };
        let full = Path::new(self.root).join(&member.path);
        let symbol = self
            .semantic
            .link_declared(&full, offset)
            .or_else(|| self.semantic.link_declared(Path::new(&member.path), offset));
        let Some(symbol) = symbol else {
            return Vec::new();
        };
        self.semantic
            .link_bases(symbol)
            .into_iter()
            .filter_map(|base| self.graph.node_of_symbol(self.root, self.semantic, base))
            .filter(|&base| base != node)
            .collect()
    }

    /// What `node` reads on the lines that matter: fields, properties and
    /// components join the cone as data.
    fn reads(&mut self, node: NodeId, entry: &Entry) {
        if entry.hops >= self.config.limits.data_hops {
            return;
        }
        let read: Vec<(NodeId, Site)> = self
            .graph
            .outgoing(node)
            .filter(|edge| {
                matches!(edge.kind, EdgeKind::Reads | EdgeKind::ReadsComponent)
                    && entry.matters(edge.line)
            })
            .map(|edge| {
                (
                    edge.to,
                    Site {
                        line: edge.line,
                        statement: edge.statement,
                        offset: edge.offset,
                    },
                )
            })
            .collect();
        for (to, site) in read {
            let via = Via::Node {
                next: node,
                step: Step::ReadBy,
                site,
            };
            let added = Added {
                role: Role::Data,
                depth: entry.depth + 1,
                hops: entry.hops + 1,
                helpers: 0,
                whole: true,
            };
            self.add(to, added, via);
        }
    }

    /// The methods the cone calls on the lines that matter, and nobody
    /// outside the cone calls, join it whole. Returns whether any did.
    fn helpers(&mut self) -> bool {
        let callers: Vec<(NodeId, Entry)> = self
            .cone
            .entries
            .iter()
            .filter(|(_, entry)| {
                matches!(entry.role, Role::Path | Role::Helper) && entry.helpers < HELPERS
            })
            .map(|(&node, entry)| (node, entry.clone()))
            .collect();
        let mut found: Vec<(NodeId, Added, Via)> = Vec::new();
        for (node, entry) in callers {
            if self.graph.member(node).is_type() {
                continue;
            }
            for edge in self.graph.outgoing(node) {
                if edge.kind != EdgeKind::Calls || !entry.matters(edge.line) {
                    continue;
                }
                let to = edge.to;
                if self
                    .cone
                    .entries
                    .get(&to)
                    .is_some_and(|known| known.role >= Role::Helper)
                {
                    continue;
                }
                let only_cone = self
                    .graph
                    .incoming(to)
                    .filter(|other| other.kind == EdgeKind::Calls)
                    .all(|other| self.cone.entries.contains_key(&other.from));
                if !only_cone {
                    continue;
                }
                let via = Via::Node {
                    next: node,
                    step: Step::CalledBy,
                    site: Site {
                        line: edge.line,
                        statement: edge.statement,
                        offset: edge.offset,
                    },
                };
                let added = Added {
                    role: Role::Helper,
                    depth: entry.depth + 1,
                    hops: entry.hops,
                    helpers: entry.helpers + 1,
                    whole: true,
                };
                found.push((to, added, via));
            }
        }
        let mut any = false;
        for (node, added, via) in found {
            let known = self.cone.entries.get(&node).map(|entry| entry.role);
            if known.is_none_or(|role| role < Role::Helper) {
                self.add(node, added, via);
                any = true;
            }
        }
        any
    }

    fn writers(&mut self, node: NodeId, kind: EdgeKind, entry: &Entry) {
        // Read outside the cone as well: shared state, written for everyone.
        let reads = if kind == EdgeKind::WritesComponent {
            EdgeKind::ReadsComponent
        } else {
            EdgeKind::Reads
        };
        let outside: HashSet<NodeId> = self
            .graph
            .incoming(node)
            .filter(|edge| edge.kind == reads && !self.cone.entries.contains_key(&edge.from))
            .map(|edge| edge.from)
            .collect();
        if outside.len() > self.config.limits.shared_readers {
            return;
        }
        let writes: Vec<(NodeId, Site)> = self
            .graph
            .incoming(node)
            .filter(|edge| edge.kind == kind)
            .map(|edge| {
                (
                    edge.from,
                    Site {
                        line: edge.line,
                        statement: edge.statement,
                        offset: edge.offset,
                    },
                )
            })
            .collect();
        let distinct: HashSet<NodeId> = writes.iter().map(|write| write.0).collect();
        let role = if distinct.len() > self.config.limits.hub_writers {
            self.cone.hubs.push(Hub {
                node,
                users: distinct.len(),
            });
            Role::User
        } else {
            Role::Path
        };
        for (from, site) in writes {
            let via = Via::Node {
                next: node,
                step: Step::Writes,
                site,
            };
            let added = Added {
                role,
                depth: entry.depth + 1,
                hops: entry.hops,
                helpers: 0,
                whole: false,
            };
            self.add(from, added, via);
        }
    }
}
