//! A change against the cone: which of the changed members lead to a sink,
//! and by which way.
//!
//! The lines of the patch land on the members of the files as the
//! configuration reads them. A member of the cone is affected for certain
//! when the change is on the lines of it that matter — all of a member that
//! names a sink, the slice of the statement that leads on for the rest —
//! and only possibly otherwise. Removed lines are read as
//! text: a call that is gone is not in the new code to be found, so a
//! removed line that names a sink is reported by the name.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::Path;

use rustlyn_ide::semantic::Semantic;

use super::Listed;
use super::cone::{Cone, Role, Step, Via};
use super::config::{Config, glob_matches};
use super::graph::{Graph, NodeId};
use super::packages::{Changes, Packages};
use super::text::words;
use crate::blast::changes::{How, Members, changes_by};
use crate::blast::diff::{FileDiff, Status};

/// What a finding is about.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FindingKind {
    /// A changed member of the cone.
    Member,
    /// The header of a type that holds members of the cone.
    Type,
    /// Code that named a sink and is not in the cone now: removed, or
    /// from a revision the code has moved on from.
    Removed,
    /// The sink's own source.
    Sink,
    /// A file the configuration watches.
    Watch,
    /// A scene, prefab or asset with the serialized data of a script whose
    /// fields the cone reads.
    Asset,
    /// A Unity package that was updated, added or removed, and concerns a
    /// sink.
    Package,
    /// A line of a native build file that names a sink.
    Mention,
}

impl FindingKind {
    /// The stable English code.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Member => "member",
            Self::Type => "type",
            Self::Removed => "removed",
            Self::Sink => "sink",
            Self::Watch => "watch",
            Self::Asset => "asset",
            Self::Package => "package",
            Self::Mention => "mention",
        }
    }
}

/// One step of the way from a change to a sink.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hop {
    /// The stable English code: a [`Step`]'s, or `uses`, `derives`,
    /// `removed`, `named`, `holds`, `serializes`.
    pub step: &'static str,
    /// What the step leads to: a member, a component, a sink's API.
    pub target: String,
    /// The sink's name, on the last step.
    pub sink: Option<String>,
    /// Where the step shows.
    pub path: String,
    /// From zero.
    pub line: usize,
}

/// Something of the change that leads to a sink.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Finding {
    pub kind: FindingKind,
    pub path: String,
    /// From zero.
    pub line: usize,
    /// The member's name with its parameter types; a watch entry's name; a
    /// script's path for an asset.
    pub name: String,
    pub role: Option<Role>,
    /// `false` for a member of the cone changed elsewhere than on the lines
    /// that matter to the way on.
    pub certain: bool,
    /// The changed lines, from zero.
    pub lines: Vec<usize>,
    pub chain: Vec<Hop>,
    pub sinks: Vec<String>,
    pub configurations: Vec<String>,
    /// For a package: how many members of the cone use it on lines that
    /// matter. Zero for anything else.
    pub count: usize,
}

/// What a configuration says of a change.
#[derive(Debug, Default)]
pub struct Judged {
    pub findings: Vec<Finding>,
    /// Changed members of own code outside the cone: path and name.
    pub unaffected: Vec<(String, String)>,
}

/// The way from `node` to a sink, and the sinks at its end. `first` is the
/// way to start along, when it is not the node's shortest.
#[must_use]
pub fn chain(
    graph: &Graph,
    cone: &Cone,
    config: &Config,
    node: NodeId,
    first: Option<&Via>,
) -> (Vec<Hop>, Vec<String>) {
    let mut hops = Vec::new();
    let mut sinks = Vec::new();
    let mut seen: HashSet<NodeId> = HashSet::new();
    let mut at = node;
    let mut via = first.or_else(|| cone.entries.get(&node).and_then(|entry| entry.vias.first()));
    while let Some(step) = via {
        if !seen.insert(at) {
            break;
        }
        let here = graph.member(at);
        match step {
            Via::Sink {
                sink,
                name,
                site,
                base,
            } => {
                hops.push(Hop {
                    step: if *base { "derives" } else { "uses" },
                    target: name.clone(),
                    sink: Some(config.sinks[*sink].name.clone()),
                    path: here.path.clone(),
                    line: site.line as usize,
                });
                // Every sink the last member names.
                for other in cone.entries.get(&at).map_or(&[][..], |entry| &entry.vias) {
                    if let Via::Sink { sink, .. } = other {
                        let name = &config.sinks[*sink].name;
                        if !sinks.contains(name) {
                            sinks.push(name.clone());
                        }
                    }
                }
                break;
            }
            Via::Node { next, step, site } => {
                let there = graph.member(*next);
                // A read or a call from the cone shows in the next member's
                // file; everything else in this one's.
                let path = match step {
                    Step::ReadBy | Step::CalledBy => &there.path,
                    _ => &here.path,
                };
                hops.push(Hop {
                    step: step.name(),
                    target: there.key.clone(),
                    sink: None,
                    path: path.clone(),
                    line: site.line as usize,
                });
                at = *next;
                via = cone.entries.get(&at).and_then(|entry| entry.vias.first());
            }
        }
    }
    (hops, sinks)
}

/// Judges the files of a patch against one configuration's cone.
#[must_use]
pub fn judge(
    root: &str,
    graph: &Graph,
    cone: &Cone,
    config: &Config,
    files: &[FileDiff],
) -> Judged {
    let mut judged = Judged::default();
    let words = Words::new(graph, cone);
    for file in files {
        if !file.path.ends_with(".cs") {
            continue;
        }
        let gone: Vec<&str> = file
            .blocks
            .iter()
            .flat_map(|block| block.removed.iter().map(String::as_str))
            .collect();
        let Some(own) = graph.file(&file.path) else {
            if let Some(sink) = config.sink_of_path(&file.path) {
                judged.findings.push(Finding {
                    kind: FindingKind::Sink,
                    path: file.path.clone(),
                    line: first_line(file),
                    name: config.sinks[sink].name.clone(),
                    role: None,
                    certain: true,
                    lines: file.new_lines(),
                    chain: Vec::new(),
                    sinks: vec![config.sinks[sink].name.clone()],
                    configurations: Vec::new(),
                    count: 0,
                });
            } else if file.status == Status::Deleted && config.is_own(&file.path) {
                // A file that is gone: by what its lines named.
                let named = words.named(config, "removed", &gone, &gone.join("\n"));
                settle(
                    &mut judged,
                    graph,
                    cone,
                    config,
                    None,
                    named,
                    &file.path,
                    &file.path,
                    0,
                );
            }
            continue;
        };
        let text = std::fs::read_to_string(Path::new(root).join(&file.path)).unwrap_or_default();
        let lines: Vec<&str> = text.lines().collect();
        // What the removed lines may name a sink by is judged against the
        // whole file, before and after.
        let around = format!("{text}\n{}", gone.join("\n"));
        // The changed lines and the removed text of each member; `None` is
        // the file outside any member.
        let mut changed: BTreeMap<Option<usize>, (Vec<usize>, Vec<&str>)> = BTreeMap::new();
        for block in &file.blocks {
            let touched: Vec<usize> = if block.new_lines.is_empty() {
                vec![block.new_lines.start]
            } else {
                block
                    .new_lines
                    .clone()
                    .filter(|&line| lines.get(line).is_none_or(|text| !text.trim().is_empty()))
                    .collect()
            };
            let index_of = |line: usize| {
                let member = own.members.enclosing(line)?;
                own.members
                    .list
                    .iter()
                    .position(|other| std::ptr::eq(other, member))
            };
            for line in touched {
                let entry = changed.entry(index_of(line)).or_default();
                if !entry.0.contains(&line) {
                    entry.0.push(line);
                }
            }
            changed
                .entry(index_of(block.new_lines.start))
                .or_default()
                .1
                .extend(block.removed.iter().map(String::as_str));
        }
        for (index, (lines, removed)) in &changed {
            let named = words.named(config, "removed", removed, &around);
            let Some(index) = index else {
                let line = lines.first().copied().unwrap_or(0);
                settle(
                    &mut judged,
                    graph,
                    cone,
                    config,
                    None,
                    named,
                    &file.path,
                    &file.path,
                    line,
                );
                continue;
            };
            let member = &own.members.list[*index];
            let verdict = graph
                .node_of(own, member)
                .and_then(|node| verdict(graph, cone, config, node, Evidence::Lines(lines)));
            settle(
                &mut judged,
                graph,
                cone,
                config,
                verdict,
                named,
                &file.path,
                &member.key,
                member.line,
            );
        }
    }
    judged
}

/// The names a line of code may name the cone by, when the line is not in
/// the code to be asked about: a removed call, a past revision.
struct Words<'a> {
    /// The types a sink's API hangs on, as own code has them.
    sinks: HashMap<&'a str, usize>,
    /// Members of the cone by a name nothing outside it has.
    cone: HashMap<&'a str, NodeId>,
}

/// What a line named.
enum Named<'a> {
    Sink(&'a str, usize),
    Member(NodeId),
}

impl<'a> Words<'a> {
    fn new(graph: &'a Graph, cone: &Cone) -> Self {
        let mut sinks: HashMap<&str, usize> = HashMap::new();
        for hit in &graph.hits {
            let word = hit.name.split('.').next().unwrap_or(&hit.name);
            sinks.entry(word).or_insert(hit.sink);
        }
        // A name is the cone's when every member that has it is in the
        // cone: `SendPurchase` is, `OnUpdate` is not.
        let mut outside: HashSet<&str> = HashSet::new();
        let mut inside: HashMap<&str, NodeId> = HashMap::new();
        for node in 0..graph.len() as NodeId {
            let member = graph.member(node);
            if member.is_type() {
                continue;
            }
            let name = member.short_name();
            match cone.entries.get(&node) {
                Some(entry) if matches!(entry.role, Role::Path | Role::Helper) => {
                    inside.entry(name).or_insert(node);
                }
                _ => {
                    outside.insert(name);
                }
            }
        }
        inside.retain(|name, _| !outside.contains(name) && name.len() > 3);
        Self {
            sinks,
            cone: inside,
        }
    }

    /// What `lines` name, as steps of a chain (`step` says how the lines
    /// are known: `removed`, `named`), with the sinks they lead to. A
    /// sink's type counts only where `around` — the file — mentions one of
    /// the sink's namespaces: `Token` is many things.
    fn named(
        &self,
        config: &Config,
        step: &'static str,
        lines: &[&str],
        around: &str,
    ) -> Vec<(&'static str, Named<'a>)> {
        let mut found: Vec<(&'static str, Named<'a>)> = Vec::new();
        let mut seen: HashSet<&str> = HashSet::new();
        for line in lines {
            let code = line.split("//").next().unwrap_or(line);
            for word in words(code) {
                if let Some((&name, &sink)) = self.sinks.get_key_value(word) {
                    let namespaces = &config.sinks[sink].namespaces;
                    let meant = namespaces.is_empty()
                        || namespaces
                            .iter()
                            .any(|namespace| around.contains(namespace.as_str()));
                    if meant && seen.insert(name) {
                        found.push((step, Named::Sink(name, sink)));
                    }
                } else if let Some((&name, &node)) = self.cone.get_key_value(word)
                    && seen.insert(name)
                {
                    found.push((step, Named::Member(node)));
                }
            }
        }
        found
    }
}

/// Puts what is known of one changed member into the judgement: the cone's
/// verdict on it, and what its removed (or past) lines named. A possible
/// finding whose lines named the cone is a certain one; a member outside
/// the cone whose lines named it is a finding of its own.
#[allow(clippy::too_many_arguments)]
fn settle(
    judged: &mut Judged,
    graph: &Graph,
    cone: &Cone,
    config: &Config,
    verdict: Option<Finding>,
    named: Vec<(&'static str, Named<'_>)>,
    path: &str,
    name: &str,
    line: usize,
) {
    if verdict.as_ref().is_some_and(|finding| finding.certain) || named.is_empty() {
        match verdict {
            Some(finding) => judged.findings.push(finding),
            None => judged.unaffected.push((path.to_owned(), name.to_owned())),
        }
        return;
    }
    // The way on from what the lines named.
    let mut hops: Vec<Hop> = Vec::new();
    let mut sinks: Vec<String> = Vec::new();
    for (step, what) in named {
        match what {
            Named::Sink(word, sink) => {
                let sink = &config.sinks[sink].name;
                hops.push(Hop {
                    step,
                    target: word.to_owned(),
                    sink: Some(sink.clone()),
                    path: path.to_owned(),
                    line,
                });
                if !sinks.contains(sink) {
                    sinks.push(sink.clone());
                }
            }
            Named::Member(node) => {
                hops.push(Hop {
                    step,
                    target: graph.member(node).key.clone(),
                    sink: None,
                    path: path.to_owned(),
                    line,
                });
                let (way, leads) = chain(graph, cone, config, node, None);
                // One member's way is enough to show.
                if !hops.iter().any(|hop| hop.sink.is_some()) {
                    hops.extend(way);
                }
                for sink in leads {
                    if !sinks.contains(&sink) {
                        sinks.push(sink);
                    }
                }
            }
        }
    }
    let role = verdict.as_ref().and_then(|finding| finding.role);
    let kind = if verdict.is_some() {
        FindingKind::Member
    } else {
        FindingKind::Removed
    };
    judged.findings.push(Finding {
        kind,
        path: path.to_owned(),
        line,
        name: name.to_owned(),
        role,
        certain: true,
        lines: verdict.map_or_else(|| vec![line], |finding| finding.lines),
        chain: hops,
        sinks,
        configurations: Vec::new(),
        count: 0,
    });
}

fn first_line(file: &FileDiff) -> usize {
    file.blocks.first().map_or(0, |block| block.new_lines.start)
}

/// How a change to a member is known.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Evidence<'a> {
    /// By lines of the code as it is now.
    Lines(&'a [usize]),
    /// By the text of the changed lines, when the code has moved on since:
    /// a past revision's change judged against today's cone. `head` says
    /// the member's signature changed.
    Text { changed: &'a [String], head: bool },
}

/// The name a line of code would mention a step's target by.
fn mention(graph: &Graph, via: &Via) -> String {
    match via {
        Via::Sink { name, .. } => name.rsplit('.').next().unwrap_or(name).to_lowercase(),
        Via::Node { next, .. } => graph.member(*next).short_name().to_lowercase(),
    }
}

/// What the cone says of a changed member.
fn verdict(
    graph: &Graph,
    cone: &Cone,
    config: &Config,
    node: NodeId,
    evidence: Evidence<'_>,
) -> Option<Finding> {
    let member = graph.member(node);
    let lines: &[usize] = match evidence {
        Evidence::Lines(lines) => lines,
        Evidence::Text { .. } => &[],
    };
    let in_head = match evidence {
        Evidence::Lines(lines) => {
            member.head.len() < member.lines.len()
                && lines.iter().any(|line| member.head.contains(line))
        }
        Evidence::Text { head, .. } => head,
    };
    let finding = |kind, role, certain, chain: (Vec<Hop>, Vec<String>)| Finding {
        kind,
        path: member.path.clone(),
        line: member.line,
        name: member.key.clone(),
        role,
        certain,
        lines: lines.to_vec(),
        chain: chain.0,
        sinks: chain.1,
        configurations: Vec::new(),
        count: 0,
    };
    if let Some(entry) = cone.entries.get(&node) {
        // The way on from the statement that changed, when one did.
        let touched = entry.vias.iter().find(|via| match evidence {
            Evidence::Lines(lines) => via.own_statement().is_some_and(|(first, last)| {
                lines
                    .iter()
                    .any(|&line| (first as usize..=last as usize).contains(&line))
            }),
            Evidence::Text { changed, .. } => {
                let name = mention(graph, via);
                via.own_statement().is_some()
                    && changed
                        .iter()
                        .any(|line| line.to_lowercase().contains(&name))
            }
        });
        // For certain when a line that matters changed: all of a helper
        // and of data, the slices of the steps on for the rest. A changed
        // signature matters to everything but a user.
        let matters = match evidence {
            Evidence::Lines(lines) => lines
                .iter()
                .any(|&line| u32::try_from(line).is_ok_and(|line| entry.matters(line))),
            Evidence::Text { .. } => entry.lines.is_none() || touched.is_some(),
        };
        let certain = matters || (entry.role != Role::User && in_head);
        let way = chain(graph, cone, config, node, touched);
        return Some(finding(FindingKind::Member, Some(entry.role), certain, way));
    }
    let inside = |node: NodeId| {
        cone.entries
            .get(&node)
            .filter(|entry| entry.role != Role::User)
    };
    if member.is_type() {
        // The header of a type whose members are on a path: its attributes
        // and bases say how they run.
        if !in_head {
            return None;
        }
        let held = graph
            .members_of(node)
            .into_iter()
            .find(|&held| inside(held).is_some_and(|entry| entry.role != Role::Data))?;
        let there = graph.member(held);
        let (mut hops, sinks) = chain(graph, cone, config, held, None);
        hops.insert(
            0,
            Hop {
                step: "holds",
                target: there.key.clone(),
                sink: None,
                path: there.path.clone(),
                line: there.line,
            },
        );
        return Some(finding(FindingKind::Type, None, true, (hops, sinks)));
    }
    // A member of a type the cone reads as data: a component's field.
    let holder = graph.container_of(node)?;
    let entry = inside(holder)?;
    let there = graph.member(holder);
    let (mut hops, sinks) = chain(graph, cone, config, holder, None);
    hops.insert(
        0,
        Hop {
            step: Step::MemberOf.name(),
            target: there.key.clone(),
            sink: None,
            path: there.path.clone(),
            line: there.line,
        },
    );
    Some(finding(
        FindingKind::Member,
        Some(entry.role),
        true,
        (hops, sinks),
    ))
}

/// Judges a past revision's change against the cone of the code as it is
/// now. `texts` has the revision's text of each changed file, by path.
///
/// A file the same now as in the revision is judged by its lines. One that
/// has moved on is judged by names: the changed members are found by name
/// in today's code, and a member the cone holds only a slice of is
/// affected for certain when the changed lines mention what the slice
/// leads to, or anything else only the cone has.
#[must_use]
pub fn judge_revision(
    root: &str,
    graph: &Graph,
    cone: &Cone,
    config: &Config,
    semantic: &Semantic,
    files: &[FileDiff],
    texts: &HashMap<String, String>,
) -> Judged {
    let mut judged = Judged::default();
    let words = Words::new(graph, cone);
    let mut same: Vec<FileDiff> = Vec::new();
    for file in files {
        if !file.path.ends_with(".cs") {
            continue;
        }
        let then = texts.get(&file.path).map_or("", String::as_str);
        let now = std::fs::read_to_string(Path::new(root).join(&file.path)).ok();
        let exact = file.status != Status::Deleted && now.as_deref() == Some(then);
        if exact || config.sink_of_path(&file.path).is_some() || !config.is_own(&file.path) {
            same.push(file.clone());
            continue;
        }
        let gone: Vec<&str> = file
            .blocks
            .iter()
            .flat_map(|block| block.removed.iter().map(String::as_str))
            .collect();
        let around = format!("{then}\n{}", gone.join("\n"));
        let then_lines: Vec<&str> = then.lines().collect();
        let members_of = |path: &str, text: &str| {
            let outline = semantic.outline_as(&Path::new(root).join(path), text);
            Members::of_outline(path, text, &outline)
        };
        let own = graph.file(&file.path);
        for change in changes_by(file, then, &members_of) {
            // The text of the change inside the member: its new lines, and
            // the removed lines of the blocks that start in it.
            let added: Vec<&str> = change
                .lines
                .iter()
                .filter_map(|&line| then_lines.get(line).copied())
                .collect();
            let removed: Vec<&str> = file
                .blocks
                .iter()
                .filter(|block| change.member.lines.contains(&block.new_lines.start))
                .flat_map(|block| block.removed.iter().map(String::as_str))
                .collect();
            let changed: Vec<String> = added
                .iter()
                .chain(&removed)
                .map(|line| (*line).to_owned())
                .collect();
            let evidence = Evidence::Text {
                changed: &changed,
                head: change.how != How::Body,
            };
            // The member as it is now, by its name.
            let node = own.and_then(|own| {
                own.members
                    .by_key(&change.member.key)
                    .and_then(|member| graph.node_of(own, member))
            });
            let verdict = node.and_then(|node| verdict(graph, cone, config, node, evidence));
            let mut named = words.named(config, "removed", &removed, &around);
            named.extend(words.named(config, "named", &added, &around));
            // A member does not name itself by being changed.
            named.retain(|(_, what)| !matches!(what, Named::Member(other) if Some(*other) == node));
            settle(
                &mut judged,
                graph,
                cone,
                config,
                verdict,
                named,
                &file.path,
                &change.member.key,
                node.map_or(change.member.line, |node| graph.member(node).line),
            );
        }
    }
    // The files that have not changed since: by their lines.
    let exact = judge(root, graph, cone, config, &same);
    judged.findings.extend(exact.findings);
    judged.unaffected.extend(exact.unaffected);
    judged
}

/// The changed files the configuration watches. `others` are the paths a
/// past change touched that have no diff — a scene of hundreds of
/// megabytes, a binary — which a watch needs only by name.
#[must_use]
pub fn watched(config: &Config, files: &[FileDiff], others: &[String]) -> Vec<Finding> {
    let mut findings = Vec::new();
    for path in others {
        for watch in config.watched(path) {
            if findings
                .iter()
                .any(|f: &Finding| &f.path == path && f.name == watch.name)
            {
                continue;
            }
            findings.push(Finding {
                kind: FindingKind::Watch,
                path: path.clone(),
                line: 0,
                name: watch.name.clone(),
                role: None,
                certain: true,
                lines: Vec::new(),
                chain: Vec::new(),
                sinks: Vec::new(),
                configurations: Vec::new(),
                count: 0,
            });
        }
    }
    for file in files {
        let paths = std::iter::once(&file.path).chain(&file.old_path);
        let mut names: Vec<&str> = Vec::new();
        for path in paths {
            for watch in config.watched(path) {
                if !names.contains(&watch.name.as_str()) {
                    names.push(&watch.name);
                }
            }
        }
        for name in names {
            findings.push(Finding {
                kind: FindingKind::Watch,
                path: file.path.clone(),
                line: first_line(file),
                name: name.to_owned(),
                role: None,
                certain: true,
                lines: file.new_lines(),
                chain: Vec::new(),
                sinks: Vec::new(),
                configurations: Vec::new(),
                count: 0,
            });
        }
    }
    findings
}

/// Unity's serialized files: a scene, a prefab, an asset.
fn is_asset(path: &str) -> bool {
    [".prefab", ".unity", ".asset"]
        .iter()
        .any(|extension| path.ends_with(extension))
}

/// The GUID Unity gave a file, from its `.meta`.
fn guid_of(root: &str, path: &str) -> Option<String> {
    let meta = std::fs::read_to_string(Path::new(root).join(format!("{path}.meta"))).ok()?;
    meta.lines()
        .find_map(|line| line.strip_prefix("guid: "))
        .map(|guid| guid.trim().to_owned())
}

/// The changed scenes, prefabs and assets whose change is in the serialized
/// data of a script with fields the cone reads. `cone` is the listing of
/// every configuration's cone.
#[must_use]
pub fn assets(root: &str, files: &[FileDiff], cone: &[&Listed]) -> Vec<Finding> {
    assets_of(
        files,
        cone,
        &|path| std::fs::read_to_string(Path::new(root).join(path)).ok(),
        root,
    )
}

/// [`assets`], with the caller giving the text of each changed file as the
/// patch left it (`text_of(path)`): a past revision's is not on the disk.
#[must_use]
pub fn assets_of(
    files: &[FileDiff],
    cone: &[&Listed],
    text_of: &dyn Fn(&str) -> Option<String>,
    root: &str,
) -> Vec<Finding> {
    let changed: Vec<&FileDiff> = files
        .iter()
        .filter(|file| is_asset(&file.path) && file.status != Status::Deleted)
        .collect();
    if changed.is_empty() {
        return Vec::new();
    }
    // Scripts with data the cone reads, by GUID, and every name the cone
    // reads data by.
    let short = |listed: &Listed| {
        listed
            .name
            .rsplit('.')
            .next()
            .unwrap_or_default()
            .to_owned()
    };
    let mut scripts: HashMap<String, Vec<&Listed>> = HashMap::new();
    let mut guids: HashMap<&str, Option<String>> = HashMap::new();
    let mut data: HashSet<String> = HashSet::new();
    for listed in cone {
        if listed.role != Role::Data {
            continue;
        }
        data.insert(short(listed));
        let guid = guids
            .entry(&listed.path)
            .or_insert_with(|| guid_of(root, &listed.path));
        if let Some(guid) = guid {
            scripts.entry(guid.clone()).or_default().push(listed);
        }
    }
    let mut findings = Vec::new();
    for file in changed {
        let Some(text) = text_of(&file.path) else {
            continue;
        };
        let lines: Vec<&str> = text.lines().collect();
        // Each line's object, and each object's script.
        let mut object_of: Vec<usize> = Vec::with_capacity(lines.len());
        let mut script_of: Vec<Option<&str>> = vec![None];
        for line in &lines {
            if line.starts_with("--- ") {
                script_of.push(None);
            }
            let object = script_of.len() - 1;
            if let Some(rest) = line.trim_start().strip_prefix("m_Script:")
                && let Some(at) = rest.find("guid: ")
            {
                let guid = &rest[at + 6..];
                let end = guid
                    .find(|c: char| !c.is_ascii_hexdigit())
                    .unwrap_or(guid.len());
                script_of[object] = Some(&guid[..end]);
            }
            object_of.push(object);
        }
        let mut reported: HashSet<(usize, String)> = HashSet::new();
        for block in &file.blocks {
            let touched = if block.new_lines.is_empty() {
                block.new_lines.start..block.new_lines.start + 1
            } else {
                block.new_lines.clone()
            };
            for line in touched {
                let Some(&object) = object_of.get(line) else {
                    continue;
                };
                let Some(fields) = script_of[object].and_then(|guid| scripts.get(guid)) else {
                    continue;
                };
                // The field of the script the line is in, and what is
                // nested under it down to the line.
                let keys = key_path(&lines, line);
                let Some(listed) = keys
                    .first()
                    .and_then(|(key, _)| fields.iter().find(|listed| short(listed) == *key))
                else {
                    continue;
                };
                // Deeper down, a key the cone does not read beside one it
                // does is somebody else's setting.
                let beside = keys[1..].iter().any(|(key, siblings)| {
                    !data.contains(*key) && siblings.iter().any(|other| data.contains(*other))
                });
                if beside || !reported.insert((object, listed.name.clone())) {
                    continue;
                }
                let mut chain = vec![Hop {
                    step: "serializes",
                    target: listed.name.clone(),
                    sink: None,
                    path: listed.path.clone(),
                    line: listed.line,
                }];
                chain.extend(listed.chain.iter().cloned());
                findings.push(Finding {
                    kind: FindingKind::Asset,
                    path: file.path.clone(),
                    line,
                    name: listed.path.clone(),
                    role: None,
                    certain: true,
                    lines: vec![line],
                    chain,
                    sinks: listed.sinks.clone(),
                    configurations: Vec::new(),
                    count: 0,
                });
            }
        }
    }
    findings
}

/// A line of Unity's YAML as a key: how deep it is and its name. A list
/// item is as deep as what it holds; a line with no key has an empty name.
fn yaml_key(line: &str) -> (usize, &str) {
    let mut indent = line.len() - line.trim_start().len();
    let mut rest = line.trim_start();
    while let Some(item) = rest.strip_prefix("- ") {
        indent += 2;
        rest = item;
    }
    if rest == "-" {
        return (indent + 2, "");
    }
    let key = rest.split_once(':').map_or("", |(key, _)| key.trim());
    (indent, key)
}

/// The keys a line of Unity's YAML is under, from the field of the object
/// down to the line's own, each with the keys beside it.
fn key_path<'a>(lines: &[&'a str], line: usize) -> Vec<(&'a str, Vec<&'a str>)> {
    // Up from the line: each key less deep than the one before.
    let (mut depth, own) = yaml_key(lines[line]);
    let mut above: Vec<(usize, usize, &str)> = vec![(line, depth, own)];
    for at in (0..line).rev() {
        let text = lines[at];
        if text.starts_with("--- ") {
            break;
        }
        let (indent, key) = yaml_key(text);
        if indent < depth && !key.is_empty() {
            depth = indent;
            above.push((at, indent, key));
        }
    }
    // The outermost is the object's type (`MonoBehaviour:`), not a field.
    above.pop();
    above.reverse();
    above
        .into_iter()
        .filter(|(_, _, key)| !key.is_empty())
        .map(|(at, indent, key)| {
            // Beside it: the keys as deep, up and down, until one less deep.
            let mut siblings: Vec<&str> = Vec::new();
            let mut collect = |range: &mut dyn Iterator<Item = usize>| {
                for other in range {
                    let text = lines[other];
                    if text.starts_with("--- ") {
                        break;
                    }
                    let (depth, name) = yaml_key(text);
                    if depth < indent && !name.is_empty() {
                        break;
                    }
                    if depth == indent && !name.is_empty() && name != key {
                        siblings.push(name);
                    }
                }
            };
            collect(&mut (0..at).rev());
            collect(&mut (at + 1..lines.len()));
            (key, siblings)
        })
        .collect()
}

/// The findings of every configuration as one list: one entry for a member,
/// with the configurations that found it; for certain if any was.
#[must_use]
pub fn merge(findings: Vec<Finding>) -> Vec<Finding> {
    let mut merged: Vec<Finding> = Vec::new();
    for finding in findings {
        let same = merged.iter_mut().find(|other| {
            other.kind == finding.kind && other.path == finding.path && other.name == finding.name
        });
        match same {
            Some(other) => {
                other.count = other.count.max(finding.count);
                if finding.certain && !other.certain {
                    other.certain = true;
                    other.chain.clone_from(&finding.chain);
                    other.role = finding.role;
                }
                for sink in finding.sinks {
                    if !other.sinks.contains(&sink) {
                        other.sinks.push(sink);
                    }
                }
                for configuration in finding.configurations {
                    if !other.configurations.contains(&configuration) {
                        other.configurations.push(configuration);
                    }
                }
                for line in finding.lines {
                    if !other.lines.contains(&line) {
                        other.lines.push(line);
                    }
                }
            }
            None => merged.push(finding),
        }
    }
    merged.sort_by(|a, b| {
        b.certain
            .cmp(&a.certain)
            .then_with(|| a.path.cmp(&b.path))
            .then_with(|| a.line.cmp(&b.line))
            .then_with(|| a.kind.cmp(&b.kind))
    });
    merged
}

/// The packages that are a sink, by name, and the sinks of each: the ones
/// whose code the graph found a sink in, and the ones the configuration
/// names. `known` are the project's packages, which the configuration's
/// globs are matched against; `more` are other names to match, such as the
/// changed ones.
#[must_use]
pub fn providers(
    graph: &Graph,
    config: &Config,
    known: &Packages,
    more: &[&str],
) -> BTreeMap<String, Vec<usize>> {
    let mut found: BTreeMap<String, Vec<usize>> = graph
        .provided
        .iter()
        .map(|(name, sinks)| (name.clone(), sinks.iter().copied().collect()))
        .collect();
    let mut names: Vec<String> = known.names().into_iter().collect();
    names.extend(graph.packages.iter().cloned());
    names.extend(more.iter().map(|name| (*name).to_owned()));
    // A name given whole is a package whether or not the project lists it.
    for sink in &config.sinks {
        names.extend(
            sink.packages
                .iter()
                .filter(|glob| !glob.contains(['*', '?']))
                .cloned(),
        );
    }
    for name in names {
        for (index, sink) in config.sinks.iter().enumerate() {
            if sink.packages.iter().any(|glob| glob_matches(glob, &name)) {
                let sinks = found.entry(name.clone()).or_default();
                if !sinks.contains(&index) {
                    sinks.push(index);
                }
            }
        }
    }
    for sinks in found.values_mut() {
        sinks.sort_unstable();
    }
    found
}

/// Judges the packages a change touched against one configuration's cone.
/// `known` are the project's packages as they are now.
///
/// A package concerns a sink when it provides it, when a package that
/// provides it depends on it, when it depends on one that does, or when the
/// own code on the way to a sink uses it on the lines that matter. What
/// else a package update changes is the project's business, not the
/// sinks'.
#[must_use]
pub fn packages(
    graph: &Graph,
    cone: &Cone,
    config: &Config,
    known: &Packages,
    changes: &Changes,
) -> Judged {
    let mut judged = Judged::default();
    let names: Vec<&str> = changes.packages.iter().map(|c| c.name.as_str()).collect();
    let providers = providers(graph, config, known, &names);
    let sink_name = |sink: usize| config.sinks[sink].name.clone();
    for changed in &changes.packages {
        let finding = |chain: Vec<Hop>, sinks: Vec<String>, count: usize| Finding {
            kind: FindingKind::Package,
            path: changed.path.clone(),
            line: changed.line,
            name: changed.name.clone(),
            role: None,
            certain: true,
            lines: vec![changed.line],
            chain,
            sinks,
            configurations: Vec::new(),
            count,
        };
        let hop = |step: &'static str, target: &str, sink: usize| Hop {
            step,
            target: target.to_owned(),
            sink: Some(sink_name(sink)),
            path: changed.path.clone(),
            line: changed.line,
        };
        // 1. It is the sink's code.
        if let Some(sinks) = providers.get(&changed.name)
            && let Some(&first) = sinks.first()
        {
            judged.findings.push(finding(
                vec![hop("package_of", &changed.name, first)],
                sinks.iter().map(|&sink| sink_name(sink)).collect(),
                0,
            ));
            continue;
        }
        // 2. A package that is the sink's depends on it; 3. it depends on
        // one that is.
        let dependents = known.dependents_of(&changed.name);
        let depends_on = known.depends_on(&changed.name);
        if let Some((package, sinks)) = providers
            .iter()
            .find(|(package, _)| dependents.contains(*package))
        {
            judged.findings.push(finding(
                vec![hop("dependency_of", package, sinks[0])],
                sinks.iter().map(|&sink| sink_name(sink)).collect(),
                0,
            ));
            continue;
        }
        if let Some((package, sinks)) = providers
            .iter()
            .find(|(package, _)| depends_on.contains(*package))
        {
            judged.findings.push(finding(
                vec![hop("depends_on", package, sinks[0])],
                sinks.iter().map(|&sink| sink_name(sink)).collect(),
                0,
            ));
            continue;
        }
        // 4. The code on the way to a sink uses it.
        let used = used_on_the_way(graph, cone, &changed.name);
        if let Some(&(first, line)) = used
            .iter()
            .min_by_key(|(node, _)| (cone.entries[node].depth, *node))
        {
            let (mut chain, mut sinks) = chain(graph, cone, config, first, None);
            for &(other, _) in &used {
                for sink in self::chain(graph, cone, config, other, None).1 {
                    if !sinks.contains(&sink) {
                        sinks.push(sink);
                    }
                }
            }
            let member = graph.member(first);
            chain.insert(
                0,
                Hop {
                    step: "used_by",
                    target: member.key.clone(),
                    sink: None,
                    path: member.path.clone(),
                    line: line as usize,
                },
            );
            judged.findings.push(finding(chain, sinks, used.len()));
            continue;
        }
        // 5. Not the sinks' business.
        judged
            .unaffected
            .push((changed.path.clone(), changed.name.clone()));
    }
    judged
}

/// The members of the cone, on a path or helping it, that use the package
/// on a line that matters, each with the first such line.
#[must_use]
pub fn used_on_the_way(graph: &Graph, cone: &Cone, package: &str) -> Vec<(NodeId, u32)> {
    let Ok(index) = graph
        .packages
        .binary_search_by(|name| name.as_str().cmp(package))
    else {
        return Vec::new();
    };
    let mut users: BTreeMap<NodeId, u32> = BTreeMap::new();
    for used in graph
        .package_uses
        .iter()
        .filter(|used| used.package as usize == index)
    {
        let Some(entry) = cone.entries.get(&used.from) else {
            continue;
        };
        if matches!(entry.role, Role::Path | Role::Helper) && entry.matters(used.line) {
            users.entry(used.from).or_insert(used.line);
        }
    }
    users.into_iter().collect()
}

/// A changed line of a native build file that names a sink: one finding
/// for each file and sink. The added lines are read from the new text
/// (`text_of(path)`), the removed ones from the patch.
#[must_use]
pub fn mentions(
    config: &Config,
    files: &[FileDiff],
    text_of: &dyn Fn(&str) -> Option<String>,
) -> Vec<Finding> {
    let mut findings = Vec::new();
    if config.sinks.iter().all(|sink| sink.mentions.is_empty()) {
        return findings;
    }
    for file in files {
        if !config.is_text_file(&file.path) {
            continue;
        }
        let text = text_of(&file.path).unwrap_or_default();
        let lines: Vec<&str> = text.lines().collect();
        let mut changed: Vec<(usize, &str)> = Vec::new();
        for block in &file.blocks {
            for line in block.new_lines.clone() {
                if let Some(text) = lines.get(line) {
                    changed.push((line, text));
                }
            }
            for removed in &block.removed {
                changed.push((block.new_lines.start, removed));
            }
        }
        for sink in &config.sinks {
            let found = changed.iter().find_map(|&(line, text)| {
                let lower = text.to_lowercase();
                sink.mentions
                    .iter()
                    .find(|mention| !mention.is_empty() && lower.contains(&mention.to_lowercase()))
                    .map(|mention| (line, text, mention))
            });
            let Some((line, text, mention)) = found else {
                continue;
            };
            let shown: String = text.trim().chars().take(120).collect();
            findings.push(Finding {
                kind: FindingKind::Mention,
                path: file.path.clone(),
                line,
                name: mention.clone(),
                role: None,
                certain: true,
                lines: vec![line],
                chain: vec![Hop {
                    step: "mentions",
                    target: shown,
                    sink: Some(sink.name.clone()),
                    path: file.path.clone(),
                    line,
                }],
                sinks: vec![sink.name.clone()],
                configurations: Vec::new(),
                count: 0,
            });
        }
    }
    findings
}
