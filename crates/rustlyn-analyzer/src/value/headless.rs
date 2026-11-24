//! The value graph without a window: for terminals and scripts. The graph
//! of what the compiler found, printed as a tree or JSON, and a survey of
//! a folder — the graph of every field and property and where it loses
//! the trail. Text goes through a [`Wording`].

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use rustlyn_ide::formats::json::{Format, Json};

use super::analysis::Context;
use super::compiler::{DeclKind, Target};
use super::document::Document;
use super::graph::{Edge, EdgeKind, Graph, Node, NodeKind, Reach, State};
use super::origin::Kind as OriginKind;
use super::project::Projects;
use super::symbols::Symbol;
use super::text::{last_component, read_source};
use super::wording::{Subtitle, Wording};

/// The graph of what the compiler found: a field, property or local — who
/// writes it and where that comes from; a parameter — what is passed to
/// it; a method — what it returns; a class or struct — where the component
/// is set and removed. `None`: not a value.
#[must_use]
pub fn graph_of(found: &Target, projects: &Projects, reach: Reach) -> Option<Graph> {
    let home = projects.home()?;
    let compiler = home.compiler.clone()?;
    let mut project = home.clone();
    project.texts.clear();
    let context = Context::new(&project, compiler);
    let start = context.root_for(found)?;
    Some(Graph::new(start, projects, true, reach))
}

/// The tree from the value to its sources; a node met again is a reference.
#[must_use]
pub fn tree(graph: &Graph, wording: &dyn Wording) -> String {
    let mut incoming: HashMap<&str, Vec<&Edge>> = HashMap::new();
    for edge in &graph.edges {
        incoming.entry(edge.to.as_str()).or_default().push(edge);
    }
    let mut lines = Vec::new();
    let mut printed = HashSet::new();
    #[allow(clippy::too_many_arguments)]
    fn walk<'a>(
        graph: &'a Graph,
        wording: &dyn Wording,
        incoming: &HashMap<&'a str, Vec<&'a Edge>>,
        printed: &mut HashSet<&'a str>,
        lines: &mut Vec<String>,
        id: &'a str,
        prefix: &str,
        edge: Option<EdgeKind>,
    ) {
        let Some(node) = graph.nodes.get(id) else {
            return;
        };
        let arrow = match edge {
            Some(EdgeKind::Network) => "⇠ ",
            Some(EdgeKind::Condition) => "? ",
            Some(EdgeKind::Data) => "← ",
            None => "",
        };
        let mut line = format!("{prefix}{arrow}{}", describe(node, wording));
        if printed.contains(id) {
            lines.push(format!("{line} {}", wording.seen()));
            return;
        }
        printed.insert(id);
        if let Some(notes) = wording.notes(&node.notes) {
            line += &format!(" — {notes}");
        }
        if let State::Failed(why) = &node.state {
            line += &format!(" ✗ {}", wording.failure(why));
        }
        if node.state == State::Collapsed && node.is_expandable() {
            line += " …";
        }
        lines.push(line);
        for child in incoming.get(id).cloned().unwrap_or_default() {
            walk(
                graph,
                wording,
                incoming,
                printed,
                lines,
                &child.from,
                &format!("{prefix}   "),
                Some(child.kind),
            );
        }
    }
    walk(
        graph,
        wording,
        &incoming,
        &mut printed,
        &mut lines,
        &graph.root_id,
        "",
        None,
    );
    lines.join("\n")
}

/// The graph's sources on one line: `constant 1500 · time Time.deltaTime`.
#[must_use]
pub fn sources_summary(graph: &Graph, wording: &dyn Wording) -> String {
    let mut seen = HashSet::new();
    graph
        .sources()
        .iter()
        .filter_map(|node| {
            let NodeKind::Source(origin, _) = &node.kind else {
                return None;
            };
            let text = format!("{} {}", wording.kind(origin.kind), origin.title);
            seen.insert(text.clone()).then_some(text)
        })
        .collect::<Vec<_>>()
        .join(" · ")
}

/// A node on one line: title, kind, project, place and its line of code.
#[must_use]
pub fn describe(node: &Node, wording: &dyn Wording) -> String {
    let mut text = format!(
        "{} [{}, {}]",
        wording.title(&node.title),
        wording.node_kind(&node.kind),
        wording.project(&node.project)
    );
    if let (Some(path), Some(line)) = (&node.path, node.line) {
        text += &format!(" {}:{}", last_component(path), line + 1);
    }
    if let Some(code) = node.code() {
        text += &format!("  │ {code}");
    }
    text
}

/// The graph for `--json`: nodes in the order they appeared, and edges.
#[must_use]
pub fn json(graph: &Graph, wording: &dyn Wording) -> String {
    json_value(graph, wording).to_text_with(Format::PRETTY_SORTED)
}

/// The JSON of [`json`], to write in another format.
#[must_use]
pub fn json_value(graph: &Graph, wording: &dyn Wording) -> Json {
    let nodes: Vec<Json> = graph
        .order
        .iter()
        .filter_map(|id| graph.nodes.get(id))
        .map(|node| {
            let mut entry = vec![
                ("id".to_owned(), Json::String(node.id.clone())),
                ("title".to_owned(), Json::String(wording.title(&node.title))),
                (
                    "subtitle".to_owned(),
                    Json::String(wording.subtitle(&node.subtitle)),
                ),
                ("project".to_owned(), Json::String(node.project.clone())),
                (
                    "depth".to_owned(),
                    Json::Int(i64::try_from(node.depth).unwrap_or(i64::MAX)),
                ),
                (
                    "kind".to_owned(),
                    Json::String(wording.node_kind(&node.kind)),
                ),
            ];
            if let NodeKind::Source(origin, _) = &node.kind {
                entry.push(("source".into(), Json::String(origin.kind.raw_name().into())));
            }
            if let Some(path) = &node.path {
                entry.push(("file".into(), Json::String(path.clone())));
            }
            if let Some(line) = node.line {
                entry.push((
                    "line".into(),
                    Json::Int(i64::try_from(line).unwrap_or(i64::MAX) + 1),
                ));
            }
            if let Some(notes) = wording.notes(&node.notes) {
                entry.push(("note".into(), Json::String(notes)));
            }
            if let State::Failed(why) = &node.state {
                entry.push(("failed".into(), Json::String(wording.failure(why))));
            }
            if !node.preview.is_empty() {
                entry.push((
                    "code".into(),
                    Json::Array(
                        node.preview
                            .lines
                            .iter()
                            .map(|l| Json::String(l.clone()))
                            .collect(),
                    ),
                ));
            }
            Json::Object(entry)
        })
        .collect();
    let edges: Vec<Json> = graph
        .edges
        .iter()
        .map(|edge| {
            let kind = match edge.kind {
                EdgeKind::Data => "data",
                EdgeKind::Network => "network",
                EdgeKind::Condition => "condition",
            };
            Json::Object(vec![
                ("from".into(), Json::String(edge.from.clone())),
                ("to".into(), Json::String(edge.to.clone())),
                ("kind".into(), Json::String(kind.into())),
            ])
        })
        .collect();
    Json::Object(vec![
        ("root".into(), Json::String(graph.root_id.clone())),
        ("nodes".into(), Json::Array(nodes)),
        ("edges".into(), Json::Array(edges)),
    ])
}

// MARK: - Surveying a folder

/// Where the graph loses the trail.
#[derive(Debug, Default)]
pub struct Losses<'a> {
    /// The names the graph went no further than: why (the node's subtitle,
    /// `None` for a call that was not recognized) and where they stand.
    pub unknown: Vec<(String, Option<Subtitle>, Option<&'a Node>)>,
    /// Expansions that gave nothing (except the value itself).
    pub empty: Vec<&'a Node>,
    /// The value itself has no writes.
    pub root_empty: bool,
    /// Fields found by name rather than by the compiler.
    pub guessed: usize,
    /// Nodes that can be expanded, but the graph hit its limit.
    pub unexplored: usize,
    /// Values the code does not write, with a known source: the database,
    /// a config, the inspector.
    pub origins: Vec<OriginKind>,
    /// The sources the graph reached, by kind.
    pub sources: Vec<OriginKind>,
}

impl<'a> Losses<'a> {
    #[must_use]
    pub fn new(graph: &'a Graph) -> Self {
        let mut losses = Losses::default();
        for id in &graph.order {
            let Some(node) = graph.nodes.get(id) else {
                continue;
            };
            if node.kind == NodeKind::Unknown || node.kind == NodeKind::Call(None) {
                let site = graph
                    .edges
                    .iter()
                    .find(|e| &e.from == id)
                    .and_then(|e| graph.nodes.get(&e.to));
                let reason = (node.kind == NodeKind::Unknown).then(|| node.subtitle.clone());
                losses.unknown.push((node.title_name(), reason, site));
            }
            if node.guessed {
                losses.guessed += 1;
            }
            if let State::Failed(_) = node.state {
                if *id == graph.root_id {
                    losses.root_empty = true;
                } else {
                    losses.empty.push(node);
                }
            }
            if node.state == State::Collapsed && node.is_expandable() {
                losses.unexplored += 1;
            }
            if let Some(origin) = node.origin {
                losses.origins.push(origin);
            }
            if let NodeKind::Source(origin, _) = &node.kind {
                losses.sources.push(origin.kind);
            }
        }
        losses
    }

    #[must_use]
    pub fn is_clean(&self) -> bool {
        self.unknown.is_empty() && self.empty.is_empty() && !self.root_empty && self.guessed == 0
    }
}

impl Node {
    /// The title when it is a name; the debug form of other titles.
    fn title_name(&self) -> String {
        match &self.title {
            super::wording::Title::Name(name) => name.clone(),
            other => format!("{other:?}"),
        }
    }
}

/// One member of a surveyed folder.
#[derive(Debug)]
pub enum Surveyed {
    /// The compiler did not recognize the declaration.
    Unresolved {
        title: String,
        path: String,
        line: usize,
    },
    /// Its graph, and how long it took.
    Graph { graph: Graph, seconds: f64 },
}

/// The fields and properties of a folder (`folder` is the project root or
/// a folder under it), in the order of their files and lines.
#[must_use]
pub fn survey_members(folder: &str, projects: &Projects) -> Option<Vec<Symbol>> {
    let home = projects.home()?;
    let symbols = home.symbols.clone()?;
    let prefix = if folder == home.root {
        home.root.clone()
    } else {
        folder.trim_end_matches('/').to_owned()
    };
    let mut members: Vec<Symbol> = symbols
        .values()
        .into_iter()
        .filter(|s| s.path.starts_with(&prefix))
        .collect();
    members.sort_by(|a, b| (&a.path, a.line).cmp(&(&b.path, b.line)));
    Some(members)
}

/// The graph of every member, one by one; `each` gets them as they come.
/// Surveys are compared with earlier ones, so the graphs expand as they
/// did: calls and parameters as `reach` says, arguments always.
pub fn survey(
    members: &[Symbol],
    projects: &Projects,
    reach: Reach,
    each: &mut dyn FnMut(Surveyed),
) {
    let Some(compiler) = projects.home().and_then(|h| h.compiler.clone()) else {
        return;
    };
    let mut models: HashMap<String, Document> = HashMap::new();
    for symbol in members {
        let title = match symbol
            .container
            .as_deref()
            .and_then(|c| c.split('.').rfind(|p| !p.is_empty()))
        {
            Some(owner) => format!("{owner}.{}", symbol.name),
            None => symbol.name.clone(),
        };
        if !models.contains_key(&symbol.path)
            && let Some(text) = read_source(&symbol.path)
        {
            models.insert(symbol.path.clone(), Document::new(&text));
        }
        let Some(model) = models.get(&symbol.path) else {
            continue;
        };
        let offset = model.offset(symbol.line, symbol.character);
        let found = compiler
            .definition(&symbol.path, offset, None)
            .into_iter()
            .next()
            .filter(|f| matches!(f.kind, DeclKind::Field | DeclKind::Property));
        let Some(found) = found else {
            each(Surveyed::Unresolved {
                title,
                path: symbol.path.clone(),
                line: symbol.line,
            });
            continue;
        };
        let begun = Instant::now();
        let Some(graph) = graph_of(&found, projects, reach) else {
            continue;
        };
        each(Surveyed::Graph {
            graph,
            seconds: begun.elapsed().as_secs_f64(),
        });
    }
}

/// A survey printed in English: a line per graph and a summary. `out` is
/// for stdout, `err` for stderr. Exit code 0: it is a survey, not a check.
#[allow(clippy::too_many_lines)]
pub fn print_survey(
    folder: &str,
    projects: &Projects,
    reach: Reach,
    verbose: bool,
    out: &mut dyn FnMut(&str),
    err: &mut dyn FnMut(&str),
) -> i32 {
    let wording = super::wording::English;
    let Some(members) = survey_members(folder, projects) else {
        err("no symbols or no compiler for the project");
        return 2;
    };
    err(&format!(
        "{}: fields and properties {}",
        last_component(folder),
        members.len()
    ));
    let (
        mut graphs,
        mut nodes,
        mut unresolved,
        mut root_empty,
        mut guessed,
        mut cut,
        mut clean,
        mut sourced,
    ) = (0, 0, 0, 0, 0, 0, 0, 0);
    let mut unknown_names: HashMap<String, HashMap<String, usize>> = HashMap::new();
    let mut empty_by_kind: HashMap<String, usize> = HashMap::new();
    let mut origin_counts: HashMap<String, usize> = HashMap::new();
    let mut source_counts: HashMap<String, usize> = HashMap::new();
    let mut slowest: Option<(String, f64)> = None;
    let started = Instant::now();
    survey(&members, projects, reach, &mut |item| match item {
        Surveyed::Unresolved { title, path, line } => {
            unresolved += 1;
            out(&format!(
                "? {title} — the compiler did not recognize the declaration · {}:{}",
                last_component(&path),
                line + 1
            ));
        }
        Surveyed::Graph { graph, seconds } => {
            graphs += 1;
            nodes += graph.nodes.len();
            if seconds > slowest.as_ref().map_or(0.0, |s| s.1) {
                slowest = Some((graph.title(&wording), seconds));
            }
            let losses = Losses::new(&graph);
            root_empty += usize::from(losses.root_empty);
            cut += usize::from(losses.unexplored > 0);
            clean += usize::from(losses.is_clean());
            sourced += usize::from(!losses.sources.is_empty());
            guessed += losses.guessed;
            for (name, reason, _) in &losses.unknown {
                let reason = reason
                    .as_ref()
                    .map_or("call not recognized".to_owned(), |r| wording.subtitle(r));
                *unknown_names
                    .entry(reason)
                    .or_default()
                    .entry(name.clone())
                    .or_default() += 1;
            }
            for origin in &losses.origins {
                *origin_counts.entry(wording.phrase(*origin)).or_default() += 1;
            }
            for kind in &losses.sources {
                *source_counts.entry(wording.kind(*kind)).or_default() += 1;
            }
            let mut line = format!(
                "{} · {} nodes · {seconds:.1} s",
                graph.title(&wording),
                graph.nodes.len()
            );
            if losses.root_empty {
                line += " · no writes";
            }
            if !losses.unknown.is_empty() {
                line += &format!(" · unknown {}", losses.unknown.len());
            }
            if !losses.empty.is_empty() {
                line += &format!(" · empty {}", losses.empty.len());
            }
            if losses.guessed > 0 {
                line += &format!(" · by name {}", losses.guessed);
            }
            if losses.unexplored > 0 {
                line += &format!(" · unexpanded {}", losses.unexplored);
            }
            out(&line);
            if verbose {
                let shown: Vec<String> = tree(&graph, &wording)
                    .split('\n')
                    .map(|l| format!("   │ {l}"))
                    .collect();
                out(&shown.join("\n"));
            }
            for (name, reason, site) in &losses.unknown {
                let reason = reason
                    .as_ref()
                    .map_or("call not recognized".to_owned(), |r| wording.subtitle(r));
                let place = site.map_or(String::new(), |site| {
                    let at = site.path.as_ref().map_or(String::new(), |p| {
                        format!(" · {}:{}", last_component(p), site.line.unwrap_or(0) + 1)
                    });
                    format!(" — in {}{at}", wording.title(&site.title))
                });
                out(&format!("   ? «{name}» — {reason}{place}"));
            }
            for node in &losses.empty {
                *empty_by_kind
                    .entry(wording.node_kind(&node.kind))
                    .or_default() += 1;
            }
            for node in &losses.empty {
                let why = if let State::Failed(reason) = &node.state {
                    wording.failure(reason)
                } else {
                    String::new()
                };
                out(&format!("   ∅ {} — {why}", describe(node, &wording)));
            }
        }
    });
    let by_count = |map: HashMap<String, usize>| -> String {
        let mut sorted: Vec<(String, usize)> = map.into_iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        sorted
            .iter()
            .map(|(key, value)| format!("{key} {value}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    out("");
    out(&format!(
        "fields and properties {}, graphs {graphs}, nodes {nodes}, {:.0} s{}",
        members.len(),
        started.elapsed().as_secs_f64(),
        slowest.map_or(String::new(), |(title, seconds)| format!(
            " · slowest {title} {seconds:.1} s"
        ))
    ));
    out(&format!("clean graphs: {clean} of {graphs}"));
    out(&format!("graphs with sources: {sourced} of {graphs}"));
    if unresolved > 0 {
        out(&format!(
            "declarations the compiler did not recognize: {unresolved}"
        ));
    }
    out(&format!("values without writes: {root_empty}"));
    let mut reasons: Vec<(String, HashMap<String, usize>)> = unknown_names.into_iter().collect();
    reasons.sort_by(|a, b| {
        b.1.values()
            .sum::<usize>()
            .cmp(&a.1.values().sum::<usize>())
            .then_with(|| a.0.cmp(&b.0))
    });
    for (reason, names) in reasons {
        let total: usize = names.values().sum();
        let mut sorted: Vec<(String, usize)> = names.into_iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        let top: Vec<String> = sorted
            .iter()
            .take(12)
            .map(|(name, count)| {
                if *count > 1 {
                    format!("{name} ×{count}")
                } else {
                    name.clone()
                }
            })
            .collect();
        out(&format!("{reason}: {total} — {}", top.join(", ")));
    }
    if !empty_by_kind.is_empty() {
        out(&format!("empty expansions: {}", by_count(empty_by_kind)));
    }
    if !origin_counts.is_empty() {
        out(&format!(
            "not written by code, but known where from: {}",
            by_count(origin_counts)
        ));
    }
    if !source_counts.is_empty() {
        out(&format!("sources: {}", by_count(source_counts)));
    }
    if guessed > 0 {
        out(&format!("found by name: {guessed}"));
    }
    if cut > 0 {
        out(&format!("hit the limit (--limit, --depth): {cut} graphs"));
    }
    0
}
