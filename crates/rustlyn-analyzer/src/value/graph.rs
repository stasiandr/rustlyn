//! The graph of where a value comes from: the value under the cursor — a
//! field, a property, a local, a parameter, a call's result — the places
//! that write it, and what the written value is made of, further by the
//! same rules until sources are found: a literal or a constant in the
//! code, an enum value, a config's JSON, the Unity inspector, time, a
//! random number, player input. Through the network too, when a host's
//! [`EdgeProvider`](super::EdgeProvider) describes it: a field of a message
//! type in one project continues with the same field in the linked one,
//! where it is filled before sending, and a loop over a receiver runs when
//! the linked project sends the message.
//!
//! It expands lazily: a node asks its project's compiler when expanded.
//! Everything is static, from the code. Without a window (`synchronous`)
//! everything is computed at once; with one, an expansion is a [`Job`] the
//! front end runs on the compiler's queue and hands back ([`Graph::adopt`]).

use std::collections::{HashMap, HashSet};

use super::analysis::{self, Context, Decl, Root, Site, Source, SourceKind, Trigger};
use super::document::Excerpt;
use super::origin::{Kind as OriginKind, ValueOrigin};
use super::project::Projects;
use super::text::{last_component, parent, trim_spaces};
use super::wording::{Failure, Note, Place, Subtitle, Title, Unknown, Wording};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeKind {
    /// A field, property or local: expands into the places that write it.
    Value(Decl),
    /// A whole ECS component: expands into Set, Add and Remove.
    Component(String),
    /// A place in code: a write, Set/Remove, a send, a return, a call.
    Site,
    /// A condition the place runs under: a system's filter.
    Condition,
    /// A message arrives: expands into where the linked project sends it.
    Arrival(String),
    /// Crossing to the same message in the linked project.
    Network,
    /// A call: expands into what the method returns.
    Call(Option<Decl>),
    /// A parameter: expands into the arguments at call sites.
    Parameter { method: Option<Decl>, index: i64 },
    /// A source: a literal, a constant, an enum value, a config, the
    /// inspector, the engine's time — no need to go further. A config and
    /// the inspector expand into the data lines that set the value; the
    /// declaration is the value whose origin this is, or the source's own
    /// name.
    Source(ValueOrigin, Option<Decl>),
    /// A line of data: a config's JSON, a prefab's or scene's YAML.
    Data,
    /// The places that did not fit into the limit: expands into them.
    More,
    /// A name that could not be resolved.
    Unknown,
}

impl NodeKind {
    /// The kind's number for front ends: 0 value, 1 component, 2 code, 3
    /// condition, 4 arrival, 5 network, 6 call, 7 parameter, 8 source, 9
    /// data, 10 more, 11 unknown.
    #[must_use]
    pub const fn code(&self) -> u8 {
        match self {
            Self::Value(_) => 0,
            Self::Component(_) => 1,
            Self::Site => 2,
            Self::Condition => 3,
            Self::Arrival(_) => 4,
            Self::Network => 5,
            Self::Call(_) => 6,
            Self::Parameter { .. } => 7,
            Self::Source(..) => 8,
            Self::Data => 9,
            Self::More => 10,
            Self::Unknown => 11,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    Collapsed,
    Loading,
    Expanded,
    Failed(Failure),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub id: String,
    pub kind: NodeKind,
    pub title: Title,
    pub subtitle: Subtitle,
    pub project: String,
    pub path: Option<String>,
    /// Zero-based.
    pub line: Option<usize>,
    /// The lines of code (or data) around the place.
    pub preview: Excerpt,
    /// The lines of the whole method — first and last — when the preview is
    /// opened up.
    pub method_lines: Option<(usize, usize)>,
    pub shows_full: bool,
    /// Notes: "changes the old value", "through mult".
    pub notes: Vec<Note>,
    /// The compiler did not know the name; the field was found by name.
    pub guessed: bool,
    /// The code does not write the value, and it is known where it comes
    /// from: the database, a config, the inspector.
    pub origin: Option<OriginKind>,
    /// The node is only an argument of a call to a project method (`entity`
    /// in `GetMax(entity)`): it shows, but the graph does not go there by
    /// itself.
    pub weak: bool,
    pub state: State,
    /// The column: 0 is the starting value (on the right), further on —
    /// towards the sources.
    pub depth: usize,
}

impl Node {
    fn new(
        id: String,
        kind: NodeKind,
        title: Title,
        subtitle: Subtitle,
        project: &str,
        depth: usize,
    ) -> Self {
        Self {
            id,
            kind,
            title,
            subtitle,
            project: project.to_owned(),
            path: None,
            line: None,
            preview: Excerpt::default(),
            method_lines: None,
            shows_full: false,
            notes: Vec::new(),
            guessed: false,
            origin: None,
            weak: false,
            state: State::Collapsed,
            depth,
        }
    }

    fn at(mut self, path: Option<&str>, line: Option<usize>) -> Self {
        self.path = path.map(str::to_owned);
        self.line = line;
        self
    }

    #[must_use]
    pub fn is_expandable(&self) -> bool {
        match &self.kind {
            NodeKind::Value(_) | NodeKind::Component(_) | NodeKind::Arrival(_) | NodeKind::More => {
                true
            }
            NodeKind::Call(method) => method.is_some(),
            NodeKind::Parameter { method, index } => method.is_some() && *index >= 0,
            NodeKind::Source(origin, declaration) => {
                declaration.is_some()
                    && matches!(origin.kind, OriginKind::Config | OriginKind::Inspector)
            }
            _ => false,
        }
    }

    /// A leaf the expansion limit does not count: a source or a data line.
    #[must_use]
    pub const fn is_leaf(&self) -> bool {
        matches!(self.kind, NodeKind::Source(..) | NodeKind::Data)
    }

    /// The text of the node's own line, trimmed, when its preview has it.
    #[must_use]
    pub fn code(&self) -> Option<&str> {
        self.preview.line(self.line?).map(trim_spaces)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum EdgeKind {
    Data = 0,
    Network = 1,
    Condition = 2,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub kind: EdgeKind,
}

/// How far the graph expands by itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reach {
    /// While there are fewer nodes (sources and data lines — leaves — do
    /// not count).
    pub nodes: usize,
    /// Columns from the starting value.
    pub depth: usize,
    /// Calls and parameters too, not only values and arrivals: deeper to
    /// the sources. "Who writes" still comes first.
    pub calls: bool,
    /// The Unity inspector: look for the value in prefabs and scenes —
    /// reading all the assets, seconds on a large project.
    pub assets: bool,
    /// No more places for one node; the rest behind a "N more" node. 0:
    /// no limit.
    pub fan_in: usize,
    /// Expand also the values that only stand as an argument of a call to
    /// a project method. A window does not: the call's value shows through
    /// its return anyway; a survey does, to compare with earlier ones.
    pub arguments: bool,
}

impl Default for Reach {
    fn default() -> Self {
        Self {
            nodes: 40,
            depth: 6,
            calls: true,
            assets: false,
            fan_in: 12,
            arguments: false,
        }
    }
}

/// The places behind a "more" node: where to and from.
#[derive(Debug, Clone)]
struct Hidden {
    sites: Vec<Site>,
    into: String,
    project: String,
    bridged: HashSet<String>,
}

/// An expansion the front end runs on the project compiler's queue.
#[derive(Debug)]
pub struct Job {
    pub id: String,
    pub project: String,
    kind: NodeKind,
    context: Context,
}

/// An expansion's answer, for the graph.
#[derive(Debug)]
pub struct Outcome {
    id: String,
    project: String,
    sites: Vec<Site>,
    origin: Option<ValueOrigin>,
    bridged: HashSet<String>,
}

impl Job {
    /// The places, and where the value comes from when data gives it: the
    /// database, a config, the inspector.
    #[must_use]
    pub fn run(self) -> Outcome {
        let (sites, origin) = analyze(&self.context, &self.kind);
        Outcome {
            id: self.id,
            project: self.project,
            sites,
            origin,
            bridged: self.context.bridged,
        }
    }
}

fn analyze(context: &Context, kind: &NodeKind) -> (Vec<Site>, Option<ValueOrigin>) {
    match kind {
        // Where the value comes from is known along with the writes: for an
        // inspector field or a config model the declaration only gives a
        // default.
        NodeKind::Value(declaration) => {
            let sites = context.writes(declaration, true);
            (sites, context.origin(declaration))
        }
        NodeKind::Component(name) => (context.component_changes(name), None),
        NodeKind::Arrival(message) => (context.arrivals(message), None),
        NodeKind::Call(Some(method)) => (context.returns(method, true), None),
        NodeKind::Parameter {
            method: Some(method),
            index,
        } if *index >= 0 => {
            // No calls: maybe the engine calls the method — `OnUpdate(deltaTime)`.
            let index = usize::try_from(*index).unwrap_or(usize::MAX);
            let sites = context.callers(method, index, true);
            let origin = if sites.is_empty() {
                context.parameter_origin(method, index)
            } else {
                None
            };
            (sites, origin)
        }
        NodeKind::Source(origin, Some(declaration)) if origin.kind == OriginKind::Inspector => {
            (context.inspector_values(declaration), None)
        }
        NodeKind::Source(origin, Some(declaration)) => {
            (context.where_set(origin, declaration), None)
        }
        _ => (Vec::new(), None),
    }
}

#[derive(Debug)]
pub struct Graph {
    pub nodes: HashMap<String, Node>,
    /// The order nodes appeared in: the layout follows it.
    pub order: Vec<String>,
    pub edges: Vec<Edge>,
    /// The first expansion is over: nothing is loading — a window fits the
    /// scale to show the whole graph.
    pub settled: bool,
    pub root_id: String,
    pub reach: Reach,
    /// Without a window: everything at once, on this thread.
    synchronous: bool,
    /// The nodes that count towards the limit.
    counted: i64,
    hidden: HashMap<String, Hidden>,
    /// Expansions waiting for the compiler's queue (only with a window).
    jobs: Vec<Job>,
}

impl Graph {
    #[must_use]
    pub fn new(root: Root, projects: &Projects, synchronous: bool, reach: Reach) -> Self {
        let home_root = projects.home.clone();
        let project = home_root.clone().unwrap_or_else(|| "/".to_owned());
        let node = match root {
            Root::Value(declaration) => {
                let project = home_root
                    .clone()
                    .unwrap_or_else(|| parent(&declaration.path));
                value_node(&declaration, &project, 0)
            }
            Root::Component(name) => component_node(&name, &project, 0),
            Root::Call(method) => Node::new(
                format!("call|{project}|{}", method.name),
                NodeKind::Call(Some(method.clone())),
                Title::Name(format!("{}()", method.title())),
                Subtitle::Call(project.clone()),
                &project,
                0,
            )
            .at(Some(&method.path), Some(method.line)),
            Root::Parameter {
                method,
                index,
                name,
            } => Node::new(
                format!("param|{project}|{}|{name}", method.name),
                NodeKind::Parameter {
                    method: Some(method.clone()),
                    index: i64::try_from(index).unwrap_or(i64::MAX),
                },
                Title::Name(name.clone()),
                Subtitle::Parameter(method.title()),
                &project,
                0,
            )
            .at(Some(&method.path), Some(method.line)),
            Root::Origin(origin, declaration) => {
                let id = format!("source|{project}|{}", origin.title);
                source_node(&origin, declaration.as_ref(), id, &project, 0)
            }
        };
        let mut graph = Self {
            nodes: HashMap::new(),
            order: Vec::new(),
            edges: Vec::new(),
            settled: false,
            root_id: node.id.clone(),
            reach,
            synchronous,
            counted: 0,
            hidden: HashMap::new(),
            jobs: Vec::new(),
        };
        let expandable = node.is_expandable();
        graph.add(node);
        let root_id = graph.root_id.clone();
        graph.expand(&root_id, projects);
        if !expandable && !graph.settled {
            graph.settled = true;
        }
        graph
    }

    /// The root's title.
    #[must_use]
    pub fn title(&self, wording: &dyn Wording) -> String {
        self.nodes
            .get(&self.root_id)
            .map_or(String::new(), |n| wording.title(&n.title))
    }

    /// The sources the graph reached, in the order they appeared.
    #[must_use]
    pub fn sources(&self) -> Vec<&Node> {
        self.order
            .iter()
            .filter_map(|id| self.nodes.get(id))
            .filter(|n| matches!(n.kind, NodeKind::Source(..)))
            .collect()
    }

    /// The next expansion to run on the compiler's queue.
    pub fn next_job(&mut self) -> Option<Job> {
        (!self.jobs.is_empty()).then(|| self.jobs.remove(0))
    }

    pub fn toggle_preview(&mut self, id: &str) {
        if let Some(node) = self.nodes.get_mut(id) {
            node.shows_full = !node.shows_full;
        }
    }

    // MARK: - Nodes

    fn add(&mut self, node: Node) {
        if self.nodes.contains_key(&node.id) {
            return;
        }
        if !node.is_leaf() {
            self.counted += 1;
        }
        self.order.push(node.id.clone());
        self.nodes.insert(node.id.clone(), node);
    }

    fn remove(&mut self, id: &str) {
        let Some(node) = self.nodes.remove(id) else {
            return;
        };
        self.order.retain(|o| o != id);
        self.edges.retain(|e| e.from != id && e.to != id);
        if !node.is_leaf() {
            self.counted -= 1;
        }
    }

    fn link(&mut self, from: &str, to: &str, kind: EdgeKind) {
        let edge = Edge {
            from: from.to_owned(),
            to: to.to_owned(),
            kind,
        };
        if !self.edges.contains(&edge) {
            self.edges.push(edge);
        }
    }

    fn set_state(&mut self, id: &str, state: State) {
        if let Some(node) = self.nodes.get_mut(id) {
            node.state = state;
        }
    }

    fn any_loading(&self) -> bool {
        self.nodes.values().any(|n| n.state == State::Loading)
    }

    // MARK: - Expanding

    pub fn expand(&mut self, id: &str, projects: &Projects) {
        let Some(node) = self.nodes.get(id) else {
            return;
        };
        if !node.is_expandable() || projects.home.is_none() {
            return;
        }
        if matches!(node.state, State::Loading | State::Expanded) {
            return;
        }
        // "N more": the places are found already — show them.
        if node.kind == NodeKind::More
            && let Some(pending) = self.hidden.remove(id)
        {
            self.remove(id);
            self.adopt_sites(
                pending.sites,
                &pending.into,
                &pending.project,
                &pending.bridged,
                None,
                true,
                projects,
            );
            return;
        }
        let node = node.clone();
        // A message arrival expands in the linked project: it is sent there.
        let mut project = node.project.clone();
        if let NodeKind::Arrival(_) = node.kind {
            let Some(peer) = peer_of(&node.project, projects) else {
                self.set_state(id, State::Failed(Failure::NoPeer));
                return;
            };
            project = peer;
        }
        let Some(context) = projects.lookup(&project).and_then(Context::for_project) else {
            self.set_state(id, State::Failed(Failure::OpenProject(project)));
            return;
        };
        self.set_state(id, State::Loading);
        if self.synchronous {
            let (sites, origin) = analyze(&context, &node.kind);
            let bridged = context.bridged.clone();
            self.adopt_sites(sites, id, &project, &bridged, origin, false, projects);
            return;
        }
        self.jobs.push(Job {
            id: id.to_owned(),
            project,
            kind: node.kind,
            context,
        });
    }

    /// An expansion's answer from the compiler's queue.
    pub fn adopt(&mut self, outcome: Outcome, projects: &Projects) {
        self.adopt_sites(
            outcome.sites,
            &outcome.id,
            &outcome.project,
            &outcome.bridged,
            outcome.origin,
            false,
            projects,
        );
    }

    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn adopt_sites(
        &mut self,
        found: Vec<Site>,
        id: &str,
        project: &str,
        bridged: &HashSet<String>,
        origin: Option<ValueOrigin>,
        all: bool,
        projects: &Projects,
    ) {
        let Some(node) = self.nodes.get(id).cloned() else {
            return;
        };
        let depth = node.depth;
        let declaration = if let NodeKind::Value(d) = &node.kind {
            Some(d.clone())
        } else {
            None
        };
        let is_bridged = declaration
            .as_ref()
            .and_then(Decl::type_name)
            .is_some_and(|t| bridged.contains(&t));
        let is_arrival = matches!(node.kind, NodeKind::Arrival(_));
        let is_source = matches!(node.kind, NodeKind::Source(..));

        // A read off the wire inside the message type itself is the bridge, not code.
        let sites: Vec<Site> = found
            .into_iter()
            .filter(|s| !(is_bridged && s.is_bridge_read))
            .collect();
        // Many places: identical ones as one node, the first of the rest,
        // others behind "N more" — the graph must stay readable.
        let mut shown = if self.reach.fan_in > 0 {
            grouped(&sites)
        } else {
            sites.clone()
        };
        if !all && self.reach.fan_in > 0 && shown.len() > self.reach.fan_in + 1 {
            let rest: Vec<Site> = shown.split_off(self.reach.fan_in);
            let more_id = format!("more|{id}");
            let titles: Vec<String> = rest.iter().take(3).map(|s| s.title.clone()).collect();
            let mut more = Node::new(
                more_id.clone(),
                NodeKind::More,
                Title::More(rest.len()),
                Subtitle::More(titles),
                project,
                depth + 1,
            );
            more.notes.push(Note::DidNotFit);
            self.hidden.insert(
                more_id.clone(),
                Hidden {
                    sites: rest,
                    into: id.to_owned(),
                    project: project.to_owned(),
                    bridged: bridged.clone(),
                },
            );
            self.add(more);
            self.link(&more_id, id, EdgeKind::Data);
        }
        for site in &shown {
            let site_project = site.project.clone().unwrap_or_else(|| project.to_owned());
            // The call `Sum(2, 3)` is a place for both `a` and `b`, but their
            // sources differ: each its own argument. One node for both
            // parameters would give each both 2 and 3.
            let site_id = match &node.kind {
                NodeKind::Parameter { index, .. } => {
                    format!("site|{}|{}|{index}", site.path, site.offset)
                }
                _ => format!("site|{}|{}", site.path, site.offset),
            };
            let mut site_node = Node::new(
                site_id.clone(),
                if site.is_data {
                    NodeKind::Data
                } else {
                    NodeKind::Site
                },
                Title::Name(site.title.clone()),
                Subtitle::Site {
                    project: site_project.clone(),
                    file: last_component(&site.path).to_owned(),
                    line: site.line,
                },
                &site_project,
                depth + 1,
            )
            .at(Some(&site.path), Some(site.line));
            site_node.preview = site.preview.clone();
            site_node.method_lines = site.method_lines;
            site_node.notes.clone_from(&site.notes);
            site_node.state = State::Expanded;
            self.add(site_node);
            self.link(
                &site_id,
                id,
                if is_arrival {
                    EdgeKind::Network
                } else {
                    EdgeKind::Data
                },
            );

            for source in &site.sources {
                self.adopt_source(source, &site_id, site, &site_project, depth + 2);
            }
            self.adopt_trigger(
                site.trigger.as_ref(),
                &site_id,
                site,
                &site_project,
                depth + 2,
            );
        }

        if let Some(declaration) = &declaration
            && is_bridged
            && sites.is_empty()
            && !all
        {
            // A message field this project only receives continues in the
            // linked project: it is filled there before sending.
            self.bridge(id, declaration, project, depth, projects);
            self.set_state(id, State::Expanded);
        } else if sites.is_empty()
            && let Some(origin) = &origin
        {
            // The code does not write it, and that is the answer: the value
            // is from the database, a config, the inspector.
            self.set_state(id, State::Expanded);
            if declaration.is_some()
                && let Some(node) = self.nodes.get_mut(id)
            {
                node.origin = Some(origin.kind);
            }
            let source = source_node(
                origin,
                declaration.as_ref(),
                format!("source|{id}"),
                project,
                depth + 1,
            );
            let source_id = source.id.clone();
            self.add(source);
            self.link(&source_id, id, EdgeKind::Data);
        } else if sites.is_empty() && is_source {
            // No data lines were found — the source is known all the same.
            self.set_state(id, State::Expanded);
            if let Some(node) = self.nodes.get_mut(id) {
                node.notes = vec![Note::NotFoundWhereSet];
            }
        } else if !all {
            let state = if sites.is_empty() {
                State::Failed(empty_reason(&node.kind))
            } else {
                State::Expanded
            };
            self.set_state(id, state);
            // The value is from data although the code has it: the initial
            // value of an inspector field or a config model's in the
            // declaration is only a default.
            if let Some(origin) = &origin
                && !sites.is_empty()
                && matches!(
                    origin.kind,
                    OriginKind::Inspector
                        | OriginKind::Config
                        | OriginKind::Json
                        | OriginKind::Database
                )
            {
                let mut source = source_node(
                    origin,
                    declaration.as_ref(),
                    format!("source|{id}"),
                    project,
                    depth + 1,
                );
                source.notes = vec![if sites.iter().all(|s| s.is_declaration) {
                    Note::OnlyDefault
                } else {
                    Note::AlsoChangedByCode
                }];
                let source_id = source.id.clone();
                self.add(source);
                self.link(&source_id, id, EdgeKind::Data);
            }
        }
        self.auto_expand(projects);
        if !self.settled && !self.any_loading() {
            self.settled = true;
        }
    }

    /// The graph takes its first steps by itself: values and message
    /// arrivals first ("who writes"), then calls and parameters — deeper to
    /// the sources, then config lines (and prefabs', when allowed), while
    /// the nodes are few. Further on — by request.
    fn auto_expand(&mut self, projects: &Projects) {
        for pass in 0..3 {
            let mut started = false;
            for id in self.order.clone() {
                if self.counted >= i64::try_from(self.reach.nodes).unwrap_or(i64::MAX) {
                    return;
                }
                let Some(node) = self.nodes.get(&id) else {
                    continue;
                };
                if node.state != State::Collapsed
                    || node.depth > self.reach.depth
                    || self.priority(node) != Some(pass)
                {
                    continue;
                }
                self.expand(&id, projects);
                started = true;
            }
            // The next step when the previous one is all expanded.
            if started || self.any_loading() {
                return;
            }
        }
    }

    fn priority(&self, node: &Node) -> Option<u8> {
        match &node.kind {
            NodeKind::Value(_) => (!(node.weak && !self.reach.arguments)).then_some(0),
            NodeKind::Arrival(_) => Some(0),
            NodeKind::Call(_) | NodeKind::Parameter { .. } => {
                (self.reach.calls && !node.weak).then_some(1)
            }
            NodeKind::Source(origin, _) => {
                if origin.kind == OriginKind::Config {
                    return Some(2);
                }
                (origin.kind == OriginKind::Inspector && self.reach.assets).then_some(2)
            }
            _ => None,
        }
    }

    fn adopt_source(
        &mut self,
        source: &Source,
        site_id: &str,
        site: &Site,
        project: &str,
        depth: usize,
    ) {
        let mut source_node = match &source.kind {
            SourceKind::Value(target) => value_node(target, project, depth),
            SourceKind::Call(name, method) => {
                let key = method
                    .as_ref()
                    .map_or(format!("{site_id}|{name}"), |m| m.name.clone());
                Node::new(
                    format!("call|{project}|{key}"),
                    NodeKind::Call(method.clone()),
                    Title::Name(format!("{name}()")),
                    Subtitle::Call(project.to_owned()),
                    project,
                    depth,
                )
                .at(
                    method.as_ref().map(|m| m.path.as_str()),
                    method.as_ref().map(|m| m.line),
                )
            }
            SourceKind::Parameter(name, method, index) => {
                let key = method
                    .as_ref()
                    .map_or(site_id.to_owned(), |m| m.name.clone());
                Node::new(
                    format!("param|{project}|{key}|{name}"),
                    NodeKind::Parameter {
                        method: method.clone(),
                        index: i64::try_from(*index).unwrap_or(i64::MAX),
                    },
                    Title::Name(name.clone()),
                    Subtitle::Parameter(method.as_ref().map_or(site.title.clone(), Decl::title)),
                    project,
                    depth,
                )
                .at(
                    method.as_ref().map(|m| m.path.as_str()),
                    method.as_ref().map(|m| m.line),
                )
            }
            SourceKind::Component(name) => component_node(name, project, depth),
            SourceKind::Origin(origin, at) => {
                // A named source (an enum value, an assembly member) is one
                // per graph; a literal is each place's own.
                let id = at.as_ref().map_or_else(
                    || {
                        format!(
                            "source|{site_id}|{}|{}",
                            origin.kind.raw_name(),
                            origin.title
                        )
                    },
                    |d| format!("source|{project}|{}", d.name),
                );
                source_node(origin, at.as_ref(), id, project, depth)
            }
            SourceKind::Unknown(chain, reason) => Node::new(
                format!("unknown|{site_id}|{chain}"),
                NodeKind::Unknown,
                Title::Name(chain.clone()),
                Subtitle::Unknown(reason.unwrap_or(Unknown::NotRecognized)),
                project,
                depth,
            ),
        };
        let mut notes = Vec::new();
        if let Some(call) = &source.argument_of {
            notes.push(if call == "[]" {
                Note::ElementKey
            } else {
                Note::ArgumentOf(call.clone())
            });
        }
        if !source.via.is_empty() {
            notes.push(Note::Through(source.via.clone()));
        }
        if source.by_name {
            notes.push(Note::ByName);
        }
        if !notes.is_empty() && !self.nodes.contains_key(&source_node.id) {
            source_node.notes = notes;
        }
        source_node.guessed = source.by_name;
        source_node.weak = source.argument_of.is_some();
        // The same node, but a value here rather than an argument: expand it.
        if source.argument_of.is_none()
            && let Some(existing) = self.nodes.get_mut(&source_node.id)
            && existing.weak
        {
            existing.weak = false;
        }
        let id = source_node.id.clone();
        self.add(source_node);
        self.link(&id, site_id, EdgeKind::Data);
    }

    /// When the place runs: a message arrived, or an entity got into a filter.
    fn adopt_trigger(
        &mut self,
        trigger: Option<&Trigger>,
        site_id: &str,
        site: &Site,
        project: &str,
        depth: usize,
    ) {
        match trigger {
            Some(Trigger::Arrival { message, receiver }) => {
                let arrival = Node::new(
                    format!("arrival|{project}|{message}"),
                    NodeKind::Arrival(message.clone()),
                    Title::Arrival(message.clone()),
                    Subtitle::Arrival {
                        receiver: receiver.clone(),
                        message: message.clone(),
                    },
                    project,
                    depth,
                );
                let id = arrival.id.clone();
                self.add(arrival);
                self.link(&id, site_id, EdgeKind::Condition);
            }
            Some(Trigger::Filter {
                name,
                with,
                without,
            }) => {
                let mut condition = Node::new(
                    format!("filter|{}|{name}", site.path),
                    NodeKind::Condition,
                    Title::Filter(name.clone()),
                    Subtitle::Filter {
                        with: with.clone(),
                        without: without.clone(),
                    },
                    project,
                    depth,
                )
                .at(
                    Some(&site.path),
                    Some(site.filter_line.unwrap_or(site.line)),
                );
                condition.state = State::Expanded;
                let id = condition.id.clone();
                self.add(condition);
                self.link(&id, site_id, EdgeKind::Condition);
                for component in with {
                    let node = component_node(component, project, depth + 1);
                    let node_id = node.id.clone();
                    self.add(node);
                    self.link(&node_id, &id, EdgeKind::Condition);
                }
            }
            None => {}
        }
    }

    /// The same message type in the linked project. No linked project: the
    /// source "network".
    fn bridge(
        &mut self,
        id: &str,
        declaration: &Decl,
        project: &str,
        depth: usize,
        projects: &Projects,
    ) {
        let Some(type_name) = declaration.type_name() else {
            return;
        };
        let Some(peer) = peer_of(project, projects) else {
            let source = source_node(
                &ValueOrigin::new(OriginKind::Network, type_name),
                None,
                format!("source|{id}|network"),
                project,
                depth + 1,
            );
            let source_id = source.id.clone();
            self.add(source);
            self.link(&source_id, id, EdgeKind::Network);
            return;
        };
        let bridge_id = format!("net|{id}");
        self.add(Node::new(
            bridge_id.clone(),
            NodeKind::Network,
            Title::Bridge(type_name.clone()),
            Subtitle::Bridge(peer.clone()),
            &peer,
            depth + 1,
        ));
        self.link(&bridge_id, id, EdgeKind::Network);
        let Some(symbols) = projects.lookup(&peer).and_then(|p| p.symbols.clone()) else {
            if let Some(node) = self.nodes.get_mut(&bridge_id) {
                node.notes = vec![Note::OpenToContinue(peer)];
            }
            return;
        };
        let short = declaration.short_name();
        let Some(member) = symbols
            .members_of(&type_name)
            .into_iter()
            .find(|s| s.name == short)
        else {
            if let Some(node) = self.nodes.get_mut(&bridge_id) {
                node.notes = vec![Note::NoField {
                    project: peer,
                    type_name,
                    field: short,
                }];
            }
            return;
        };
        let theirs = Decl {
            path: member.path.clone(),
            line: member.line,
            character: member.character,
            length: member.length,
            name: member.qualified(),
        };
        let value = value_node(&theirs, &peer, depth + 2);
        let value_id = value.id.clone();
        self.add(value);
        self.link(&value_id, &bridge_id, EdgeKind::Network);
    }

    // MARK: - Checking chains

    /// Whether there is a chain of nodes with these titles (substrings, as
    /// `wording` words the titles), each next one a source of the one
    /// before.
    #[must_use]
    pub fn has_path(&self, titles: &[String], wording: &dyn Wording) -> bool {
        let Some(first) = titles.first() else {
            return true;
        };
        let mut incoming: HashMap<&str, Vec<&str>> = HashMap::new();
        for edge in &self.edges {
            incoming
                .entry(edge.to.as_str())
                .or_default()
                .push(edge.from.as_str());
        }
        let matches = |id: &str, title: &str| {
            self.nodes
                .get(id)
                .is_some_and(|n| wording.title(&n.title).contains(title))
        };
        fn search<'a>(
            graph: &'a Graph,
            incoming: &HashMap<&'a str, Vec<&'a str>>,
            matches: &dyn Fn(&str, &str) -> bool,
            id: &'a str,
            rest: &[String],
        ) -> bool {
            let Some(next) = rest.first() else {
                return true;
            };
            // Intermediate nodes (network, conditions) may be passed unnamed.
            let mut seen: HashSet<&str> = HashSet::from([id]);
            let mut queue: Vec<&str> = incoming.get(id).cloned().unwrap_or_default();
            while !queue.is_empty() {
                let candidate = queue.remove(0);
                if !seen.insert(candidate) {
                    continue;
                }
                if matches(candidate, next)
                    && search(graph, incoming, matches, candidate, &rest[1..])
                {
                    return true;
                }
                if graph
                    .nodes
                    .get(candidate)
                    .is_some_and(|n| matches!(n.kind, NodeKind::Network | NodeKind::Condition))
                {
                    queue.extend(incoming.get(candidate).cloned().unwrap_or_default());
                }
            }
            false
        }
        self.order
            .iter()
            .any(|id| matches(id, first) && search(self, &incoming, &matches, id, &titles[1..]))
    }
}

fn value_node(declaration: &Decl, project: &str, depth: usize) -> Node {
    Node::new(
        format!("value|{project}|{}", declaration.name),
        NodeKind::Value(declaration.clone()),
        Title::Name(declaration.title()),
        Subtitle::Project(project.to_owned()),
        project,
        depth,
    )
    .at(Some(&declaration.path), Some(declaration.line))
}

fn component_node(name: &str, project: &str, depth: usize) -> Node {
    Node::new(
        format!("component|{project}|{name}"),
        NodeKind::Component(name.to_owned()),
        Title::Name(name.to_owned()),
        Subtitle::Component(project.to_owned()),
        project,
        depth,
    )
}

/// A source: its subtitle is its kind and where it is (a project or an
/// assembly).
fn source_node(
    origin: &ValueOrigin,
    declaration: Option<&Decl>,
    id: String,
    project: &str,
    depth: usize,
) -> Node {
    let place = declaration
        .and_then(|d| analysis::library_name(&d.path))
        .map_or_else(|| Place::Project(project.to_owned()), Place::Library);
    let mut node = Node::new(
        id,
        NodeKind::Source(origin.clone(), declaration.cloned()),
        Title::Name(origin.title.clone()),
        Subtitle::Source {
            kind: origin.kind,
            place,
        },
        project,
        depth,
    )
    .at(
        declaration.map(|d| d.path.as_str()),
        declaration.map(|d| d.line),
    );
    if !node.is_expandable() {
        node.state = State::Expanded;
    }
    node
}

/// Identical places — the same line of code and the same sources, like
/// `SessionStartTime = Clock.Now()` in twelve systems — as one node: the
/// first one, noting where else.
fn grouped(sites: &[Site]) -> Vec<Site> {
    let mut result: Vec<Site> = Vec::new();
    let mut others: Vec<Vec<String>> = Vec::new();
    let mut positions: HashMap<String, usize> = HashMap::new();
    for site in sites {
        let code = site
            .preview
            .line(site.line)
            .map(|l| trim_spaces(l).to_owned())
            .unwrap_or_default();
        let mut sources: Vec<String> = site
            .sources
            .iter()
            .map(|s| format!("{:?}|{:?}", s.kind, s.via))
            .collect();
        sources.sort();
        let key = [
            code.clone(),
            format!("{:?}", site.notes),
            sources.join(";"),
            if site.is_data {
                "data".into()
            } else {
                String::new()
            },
        ]
        .join("\n");
        if !code.is_empty()
            && let Some(&at) = positions.get(&key)
        {
            others[at].push(site.title.clone());
        } else {
            positions.insert(key, result.len());
            result.push(site.clone());
            others.push(Vec::new());
        }
    }
    for (index, titles) in others.iter().enumerate() {
        if titles.is_empty() {
            continue;
        }
        let shown = format!(
            "{}{}",
            titles
                .iter()
                .take(3)
                .cloned()
                .collect::<Vec<_>>()
                .join(", "),
            if titles.len() > 3 { "…" } else { "" }
        );
        result[index].notes.push(Note::SameIn {
            count: titles.len(),
            titles: shown,
        });
    }
    result
}

const fn empty_reason(kind: &NodeKind) -> Failure {
    match kind {
        NodeKind::Component(_) => Failure::NoComponentChanges,
        NodeKind::Arrival(_) => Failure::NoArrivals,
        NodeKind::Call(_) => Failure::NoReturn,
        NodeKind::Parameter { .. } => Failure::NoCallers,
        _ => Failure::NoWrites,
    }
}

/// The project linked to a node's project: for a node from the linked
/// project, that is the starting one.
fn peer_of(project: &str, projects: &Projects) -> Option<String> {
    projects.home.as_ref()?;
    projects.lookup(project).and_then(|p| p.peer.clone())
}
