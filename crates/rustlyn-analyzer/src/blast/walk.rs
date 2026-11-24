//! The forward walk: what a change reaches. A value graph goes from a value
//! to its sources; this goes the other way, from the change to what
//! depends on it:
//!
//! * a method, property or constructor — who calls it (and on up the chain);
//! * a field or property the changed code writes — who reads it;
//! * a field with a new type or initializer — everyone who mentions it;
//! * a type with a new header — who uses it;
//! * a removed member — where its name still appears.
//!
//! The project's compiler answers (a Rustlyn session); whether a place
//! writes or reads is decided by reading the text there
//! ([`crate::value::flow`]).

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustlyn_ide::Session;
use rustlyn_ide::outline::DeclarationKind;
use rustlyn_ide::session::{Call, Uses};

use super::ask::{absolute, ask};
use super::changes::{Change, How, Member, Members, line_starts, utf16_len};
use super::compiler_risks::threads;
use crate::value::UNIVERSAL_MEMBERS;
use crate::value::flow::{self, Access, Utf16Range};

/// How far the walk goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Steps from the change.
    pub depth: usize,
    /// Nodes in all.
    pub nodes: usize,
    /// New nodes from one node.
    pub fan_out: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            depth: 4,
            nodes: 400,
            fan_out: 40,
        }
    }
}

/// Why a node is reached: its link to the node it came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Relation {
    /// Calls it.
    Calls,
    /// Calls what it overrides or implements: may reach it.
    CallsBase,
    /// Reads the field or property.
    Reads,
    /// Writes it.
    Writes,
    /// Mentions the type or member.
    Uses,
    /// The changed code writes this field.
    WrittenBy,
    /// Mentions its name where the compiler no longer sees a link: a removed
    /// member, or a call that does not compile against the new signature.
    Mentions,
}

impl Relation {
    /// The stable English code.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Calls => "calls",
            Self::CallsBase => "calls_base",
            Self::Reads => "reads",
            Self::Writes => "writes",
            Self::Uses => "uses",
            Self::WrittenBy => "written_by",
            Self::Mentions => "mentions",
        }
    }
}

/// Where a node was reached from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Edge {
    /// The index of the node it came from.
    pub from: usize,
    pub relation: Relation,
    /// Where it shows: relative path and line from zero.
    pub path: String,
    pub line: usize,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub member: Member,
    /// Steps from the change; a changed member's is 0.
    pub depth: usize,
    /// How the change touched it.
    pub change: Option<How>,
    pub edges: Vec<Edge>,
    /// How many calls or mentions there were in all, even when not all made
    /// it into the graph.
    pub fan_in: usize,
}

#[derive(Debug, Clone, Default)]
pub struct Impact {
    pub nodes: Vec<Node>,
    /// The walk hit its limits.
    pub truncated: bool,
}

impl Impact {
    #[must_use]
    pub fn index_of(&self, key: &str) -> Option<usize> {
        self.nodes.iter().position(|n| n.member.key == key)
    }
}

/// The texts and members of the files asked about so far.
struct Files<'a> {
    root: &'a str,
    session: &'a Session,
    texts: HashMap<String, Option<(String, Members)>>,
}

impl Files<'_> {
    fn get(&mut self, path: &str) -> Option<&(String, Members)> {
        let root = self.root;
        self.texts
            .entry(path.to_owned())
            .or_insert_with(|| {
                let text = std::fs::read_to_string(Path::new(root).join(path)).ok()?;
                let members = Members::of(path, &text);
                Some((text, members))
            })
            .as_ref()
    }

    fn absolute(&self, path: &str) -> String {
        Path::new(self.root)
            .join(path)
            .to_string_lossy()
            .into_owned()
    }

    /// Opens the file in the session: the compiler does not answer about it
    /// otherwise.
    fn open(&self, path: &str) -> String {
        let absolute = self.absolute(path);
        let _ = ask(|| self.session.open(&absolute));
        absolute
    }

    fn relative(&self, path: &Path) -> String {
        relative_to(self.root, &absolute(self.root, path))
    }
}

/// The path relative to `root`, with `/`.
#[must_use]
pub fn relative_to(root: &str, absolute: &str) -> String {
    let rel = Path::new(absolute)
        .strip_prefix(root)
        .map_or_else(|_| PathBuf::from(absolute), Path::to_path_buf);
    rel.to_string_lossy().replace('\\', "/")
}

/// More callers than this, on a member reached through a call to its base,
/// make it a shared pass-through rather than a dependency of the change.
const DISPATCH_HUB: usize = 8;

/// The walk from the changes. `session` is the compiled project in `root`.
#[must_use]
pub fn walk(root: &str, session: &Session, changes: &[Change], limits: Limits) -> Impact {
    walk_with(root, session, changes, limits, &HashMap::new())
}

/// The same, with the unsaved texts of open files: relative path → text. The
/// compiler knows them already (an editor hands it every edit), and the walk
/// reads them rather than the disk.
#[must_use]
pub fn walk_with(
    root: &str,
    session: &Session,
    changes: &[Change],
    limits: Limits,
    unsaved: &HashMap<String, String>,
) -> Impact {
    let texts = unsaved
        .iter()
        .map(|(path, text)| (path.clone(), Some((text.clone(), Members::of(path, text)))))
        .collect();
    let mut files = Files {
        root,
        session,
        texts,
    };
    let mut impact = Impact::default();
    let mut queue: VecDeque<usize> = VecDeque::new();
    // Nodes that expand as data: their readers are reached.
    let mut data: HashSet<usize> = HashSet::new();
    // Nodes the walk reached through a call to a base.
    let mut dispatched: HashSet<usize> = HashSet::new();

    for change in changes {
        let index = impact.nodes.len();
        impact.nodes.push(Node {
            member: change.member.clone(),
            depth: 0,
            change: Some(change.how),
            edges: Vec::new(),
            fan_in: 0,
        });
        if change.how == How::Removed {
            mentions(&mut files, &mut impact, index, limits);
            continue;
        }
        if is_data(change.member.kind) && change.how == How::Signature {
            data.insert(index);
        }
        queue.push_back(index);
    }
    // What the changed code writes: its fields are reached as data.
    for (k, change) in changes.iter().enumerate() {
        if change.how == How::Removed || change.member.is_type() {
            continue;
        }
        for (field, line) in written_fields(&mut files, change) {
            let edge = Edge {
                from: k,
                relation: Relation::WrittenBy,
                path: change.member.path.clone(),
                line,
            };
            let Some(index) = add(&mut impact, field, 1, edge, limits) else {
                continue;
            };
            if data.insert(index) {
                queue.push_back(index);
            }
        }
    }

    while !queue.is_empty() {
        // One step of the walk at once: questions to the compiler on several
        // threads, nodes in queue order.
        let level: Vec<usize> = queue.drain(..).collect();
        let mut answers = ask_all(root, session, &impact, &level, &data, limits);
        for index in level {
            let node = &impact.nodes[index];
            if node.depth >= limits.depth {
                continue;
            }
            let member = node.member.clone();
            let depth = node.depth + 1;
            let answer = answers.remove(&index).unwrap_or_default();
            let mut found: Vec<(Member, Edge)> = Vec::new();
            if let Some(uses) = answer.uses {
                let only_reads = node.change.is_none();
                for (user, edge) in users(&mut files, &member, index, uses) {
                    if only_reads && edge.relation == Relation::Writes {
                        continue;
                    }
                    found.push((user, edge));
                }
            }
            // A call through an interface or a base was on the path from the
            // change already (`x.Write(w)` on `IWriteable`): a second one is
            // not followed, and a node called from everywhere — a shared
            // pass-through like a generic `Writer.Write<T>` — is not
            // expanded: its callers pass their own types, not the changed
            // one. Otherwise a change to one message's `Write` reaches every
            // message of the project.
            let dispatched_here = dispatched.contains(&index);
            if let Some(calls) = answer.calls {
                found.extend(
                    callers(&mut files, &member, index, calls)
                        .into_iter()
                        .filter(|(_, e)| !dispatched_here || e.relation != Relation::CallsBase),
                );
            }
            impact.nodes[index].fan_in = impact.nodes[index].fan_in.max(found.len());
            if dispatched_here && found.len() > DISPATCH_HUB {
                continue;
            }
            for (user, edge) in found.into_iter().take(limits.fan_out) {
                let known = impact.index_of(&user.key);
                let through_base = edge.relation == Relation::CallsBase;
                match add(&mut impact, user, depth, edge, limits) {
                    Some(next) if known.is_none() => {
                        if dispatched_here || through_base {
                            dispatched.insert(next);
                        }
                        queue.push_back(next);
                    }
                    Some(_) => {}
                    None => impact.truncated = true,
                }
            }
        }
    }
    // A method's new signature: the compiler no longer binds the old calls
    // to it, so they are found by name.
    for (index, change) in changes.iter().enumerate() {
        if change.how == How::Signature
            && matches!(
                change.member.kind,
                DeclarationKind::Method
                    | DeclarationKind::Constructor
                    | DeclarationKind::Indexer
                    | DeclarationKind::Operator
            )
        {
            mentions(&mut files, &mut impact, index, limits);
        }
    }
    impact
}

/// The node with an edge; a node already known gets one more edge. `None`:
/// there are as many nodes as allowed.
fn add(
    impact: &mut Impact,
    member: Member,
    depth: usize,
    edge: Edge,
    limits: Limits,
) -> Option<usize> {
    if let Some(index) = impact.index_of(&member.key) {
        let node = &mut impact.nodes[index];
        if edge.from != index
            && !node
                .edges
                .iter()
                .any(|e| e.from == edge.from && e.relation == edge.relation)
        {
            node.edges.push(edge);
        }
        return Some(index);
    }
    if impact.nodes.len() >= limits.nodes {
        return None;
    }
    impact.nodes.push(Node {
        member,
        depth,
        change: None,
        edges: vec![edge],
        fan_in: 0,
    });
    Some(impact.nodes.len() - 1)
}

const fn is_data(kind: DeclarationKind) -> bool {
    matches!(
        kind,
        DeclarationKind::Field
            | DeclarationKind::Property
            | DeclarationKind::Event
            | DeclarationKind::EnumMember
    )
}

const fn is_callable(kind: DeclarationKind) -> bool {
    matches!(
        kind,
        DeclarationKind::Method
            | DeclarationKind::Constructor
            | DeclarationKind::Property
            | DeclarationKind::Indexer
            | DeclarationKind::Operator
            | DeclarationKind::Event
    )
}

/// What the compiler answered about a node: who calls it and where it is
/// mentioned.
#[derive(Default)]
struct Answer {
    calls: Option<Vec<Call>>,
    uses: Option<Uses>,
}

/// The questions about one step's nodes, on several threads: on a large
/// project a call hierarchy answers in milliseconds, and there are hundreds
/// of nodes.
fn ask_all(
    root: &str,
    session: &Session,
    impact: &Impact,
    level: &[usize],
    data: &HashSet<usize>,
    limits: Limits,
) -> HashMap<usize, Answer> {
    let wanted: Vec<(usize, &Member, bool, bool)> = level
        .iter()
        .filter_map(|&index| {
            let node = &impact.nodes[index];
            if node.depth >= limits.depth {
                return None;
            }
            let uses = data.contains(&index)
                || (node.member.is_type() && node.change == Some(How::Signature));
            Some((index, &node.member, uses, is_callable(node.member.kind)))
        })
        .collect();
    let next = AtomicUsize::new(0);
    let answers = Mutex::new(HashMap::new());
    std::thread::scope(|scope| {
        for _ in 0..threads(wanted.len()) {
            scope.spawn(|| {
                while let Some(&(index, member, want_uses, want_calls)) =
                    wanted.get(next.fetch_add(1, Ordering::Relaxed))
                {
                    let absolute = Path::new(root)
                        .join(&member.path)
                        .to_string_lossy()
                        .into_owned();
                    let _ = ask(|| session.open(&absolute));
                    let offset = member.utf16_offset as u32;
                    let uses = if want_uses {
                        ask(|| session.references(&absolute, offset, None))
                    } else {
                        None
                    };
                    let calls = want_calls.then(|| {
                        ask(|| {
                            let item = session.call_hierarchy(&absolute, offset, None)?;
                            session.incoming_calls(&item.key)
                        })
                        .unwrap_or_default()
                    });
                    if let Ok(mut all) = answers.lock() {
                        all.insert(index, Answer { calls, uses });
                    }
                }
            });
        }
    });
    answers.into_inner().unwrap_or_default()
}

/// Who calls a member: the calls from the compiler's call hierarchy.
fn callers(
    files: &mut Files<'_>,
    member: &Member,
    from: usize,
    calls: Vec<Call>,
) -> Vec<(Member, Edge)> {
    let mut result = Vec::new();
    for call in calls {
        let path = files.relative(&call.path);
        let line = call.ranges.first().map_or(0, |r| r.start_line as usize);
        let Some((_, members)) = files.get(&path) else {
            continue;
        };
        let Some(caller) = members.enclosing(line) else {
            continue;
        };
        if caller.key == member.key {
            continue;
        }
        // `x.ToString()` on any object "may" reach an override of
        // `ToString`: noise, not a dependency.
        if call.through_base && UNIVERSAL_MEMBERS.contains(&member.short_name()) {
            continue;
        }
        let relation = if call.through_base {
            Relation::CallsBase
        } else {
            Relation::Calls
        };
        result.push((
            caller.clone(),
            Edge {
                from,
                relation,
                path,
                line,
            },
        ));
    }
    result
}

/// Who mentions a member, and how: reads, writes or just names it.
fn users(files: &mut Files<'_>, member: &Member, from: usize, uses: Uses) -> Vec<(Member, Edge)> {
    let mut result = Vec::new();
    for location in uses.locations {
        let path = files.relative(&location.path);
        let line = location.line as usize;
        if path == member.path && line == member.line {
            continue;
        }
        let Some((text, members)) = files.get(&path) else {
            continue;
        };
        let Some(user) = members.enclosing(line) else {
            continue;
        };
        if user.key == member.key {
            continue;
        }
        let relation = if member.is_type() {
            Relation::Uses
        } else {
            let units: Vec<u16> = text.encode_utf16().collect();
            let offset = utf16_offset_of_line(text, line) + location.character as usize;
            match flow::access(&units, Utf16Range::new(offset, location.length as usize)) {
                Access::Read => Relation::Reads,
                Access::Write { .. } => Relation::Writes,
            }
        };
        result.push((
            user.clone(),
            Edge {
                from,
                relation,
                path,
                line,
            },
        ));
    }
    result
}

/// The project's fields and properties the changed lines write to.
fn written_fields(files: &mut Files<'_>, change: &Change) -> Vec<(Member, usize)> {
    let path = change.member.path.clone();
    let Some((text, _)) = files.get(&path) else {
        return Vec::new();
    };
    let text = text.clone();
    let units: Vec<u16> = text.encode_utf16().collect();
    let starts = line_starts(&text);
    let absolute = files.open(&path);
    let mut result: Vec<(Member, usize)> = Vec::new();
    for &line in &change.lines {
        let Some(&start) = starts.get(line) else {
            continue;
        };
        let end = starts.get(line + 1).copied().unwrap_or(text.len());
        let line_text = &text[start..end];
        let base = utf16_len(&text[..start]);
        for (column, word) in identifiers(line_text) {
            let offset = base + utf16_len(&line_text[..column]);
            let name = Utf16Range::new(offset, utf16_len(word));
            if !matches!(flow::access(&units, name), Access::Write { .. }) {
                continue;
            }
            let session = files.session;
            let Some(found) = ask(|| session.definition_in(&absolute, offset as u32, None)) else {
                continue;
            };
            for target in found.targets {
                let target_path = files.relative(&target.path);
                let Some((_, members)) = files.get(&target_path) else {
                    continue;
                };
                let Some(field) = members.list.iter().find(|m| {
                    m.line == target.line as usize && is_data(m.kind) && m.short_name() == word
                }) else {
                    continue;
                };
                if !result.iter().any(|(m, _)| m.key == field.key) && field.key != change.member.key
                {
                    result.push((field.clone(), line));
                }
            }
        }
    }
    result
}

/// Where else the member's name appears: as text, over every file of the
/// project. For a removed member the compiler no longer knows it; for a new
/// signature the old calls do not bind to it. Nodes already linked to it
/// are skipped.
fn mentions(files: &mut Files<'_>, impact: &mut Impact, index: usize, limits: Limits) {
    let member = impact.nodes[index].member.clone();
    let name = match member.kind {
        DeclarationKind::Constructor => member
            .container
            .as_deref()
            .and_then(|c| c.rsplit('.').next())
            .unwrap_or(member.short_name())
            .to_owned(),
        _ => member.short_name().to_owned(),
    };
    let mut paths = Vec::new();
    sources(Path::new(files.root), Path::new(files.root), &mut paths);
    let mut count = impact
        .nodes
        .iter()
        .filter(|n| n.edges.iter().any(|e| e.from == index))
        .count();
    for path in paths {
        // Parse only the files the name is in: on a large project, a handful
        // out of thousands.
        if !files.texts.contains_key(&path)
            && !std::fs::read_to_string(Path::new(files.root).join(&path))
                .is_ok_and(|t| t.contains(name.as_str()))
        {
            continue;
        }
        let Some((text, members)) = files.get(&path) else {
            continue;
        };
        if !text.contains(name.as_str()) {
            continue;
        }
        let lines: Vec<usize> = text
            .lines()
            .enumerate()
            .filter(|(_, l)| identifiers(l).any(|(_, w)| w == name))
            .map(|(i, _)| i)
            .collect();
        let mut hits: Vec<(Member, usize)> = Vec::new();
        for line in lines {
            if let Some(user) = members.enclosing(line)
                && user.key != member.key
                && !hits.iter().any(|(m, _)| m.key == user.key)
                && !impact
                    .index_of(&user.key)
                    .is_some_and(|known| impact.nodes[known].edges.iter().any(|e| e.from == index))
            {
                hits.push((user.clone(), line));
            }
        }
        for (user, line) in hits {
            count += 1;
            if count > limits.fan_out {
                impact.truncated = true;
                break;
            }
            let edge = Edge {
                from: index,
                relation: Relation::Mentions,
                path: path.clone(),
                line,
            };
            if add(impact, user, impact.nodes[index].depth + 1, edge, limits).is_none() {
                impact.truncated = true;
            }
        }
    }
    impact.nodes[index].fan_in = impact.nodes[index].fan_in.max(count);
}

/// The project's C# sources, relative to `root`, outside the folders builds
/// and Unity write.
pub fn sources(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            if name.starts_with('.')
                || matches!(
                    name.as_str(),
                    "Library" | "Temp" | "obj" | "bin" | "Logs" | "node_modules" | "PackageCache"
                )
            {
                continue;
            }
            sources(root, &path, out);
        } else if name.ends_with(".cs") {
            out.push(relative_to(
                &root.to_string_lossy(),
                &path.to_string_lossy(),
            ));
        }
    }
}

fn utf16_offset_of_line(text: &str, line: usize) -> usize {
    let starts = line_starts(text);
    starts.get(line).map_or(0, |&s| utf16_len(&text[..s]))
}

/// The names in a line: the byte each starts at, and the name. Strings and
/// comments are not told apart — the compiler drops a name too many.
pub fn identifiers(line: &str) -> impl Iterator<Item = (usize, &str)> {
    let bytes = line.as_bytes();
    let mut i = 0;
    std::iter::from_fn(move || {
        while i < bytes.len() {
            let c = line[i..].chars().next()?;
            if c.is_alphabetic() || c == '_' {
                let start = i;
                while i < bytes.len() {
                    let c = line[i..].chars().next()?;
                    if c.is_alphanumeric() || c == '_' {
                        i += c.len_utf8();
                    } else {
                        break;
                    }
                }
                let before = line[..start].chars().next_back();
                if before.is_some_and(|b| b.is_ascii_digit()) {
                    continue;
                }
                return Some((start, &line[start..i]));
            }
            i += c.len_utf8();
        }
        None
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::changes::changes;
    use crate::blast::diff::parse;
    use crate::blast::testing::{Project, patch};

    const PAWN: &str = "namespace Game {
    public class Pawn {
        public int Health;
        public int Armor;
        public void Heal(int by) {
            Health += by;
        }
        public bool IsDead() {
            return Health <= 0;
        }
    }
}
";
    const GAME: &str = "namespace Game {
    public class Referee {
        Pawn pawn = new Pawn();
        public void Tick() {
            if (pawn.IsDead()) End();
        }
        void End() { }
        public void Bless() {
            pawn.Heal(5);
        }
    }
    public class Hud {
        Referee referee;
        public void Draw() {
            referee.Bless();
        }
    }
}
";

    fn impact_of(new_pawn: &str) -> (Impact, Vec<Change>) {
        let project = Project::new("walk", &[("Pawn.cs", PAWN), ("Game.cs", GAME)]);
        project.write("Pawn.cs", new_pawn);
        let session = project.session();
        let files = parse(&patch("Pawn.cs", PAWN, new_pawn));
        let changes = changes(&files[0], new_pawn);
        (
            walk(&project.root(), &session, &changes, Limits::default()),
            changes,
        )
    }

    fn reached(impact: &Impact) -> Vec<(String, usize)> {
        impact
            .nodes
            .iter()
            .map(|n| (n.member.key.clone(), n.depth))
            .collect()
    }

    #[test]
    fn calls_up_the_chain() {
        let (impact, _) = impact_of(&PAWN.replace(
            "public void Heal(int by) {\n            Health += by;",
            "public void Heal(int by) {\n            Health += by * 2;",
        ));
        let reached = reached(&impact);
        assert!(
            reached.contains(&("Game.Pawn.Heal(int)".to_owned(), 0)),
            "{reached:?}"
        );
        assert!(
            reached.contains(&("Game.Referee.Bless()".to_owned(), 1)),
            "{reached:?}"
        );
        assert!(
            reached.contains(&("Game.Hud.Draw()".to_owned(), 2)),
            "{reached:?}"
        );
    }

    #[test]
    fn readers_of_a_written_field() {
        let (impact, _) = impact_of(&PAWN.replace("Health += by;", "Health += by * 2;"));
        let reached = reached(&impact);
        // Heal writes Health, so IsDead, which reads it, is reached, and
        // Tick, which calls IsDead.
        assert!(
            reached.contains(&("Game.Pawn.Health".to_owned(), 1)),
            "{reached:?}"
        );
        assert!(
            reached.contains(&("Game.Pawn.IsDead()".to_owned(), 2)),
            "{reached:?}"
        );
        assert!(
            reached.contains(&("Game.Referee.Tick()".to_owned(), 3)),
            "{reached:?}"
        );
        let dead = impact.index_of("Game.Pawn.IsDead()").expect("reached");
        assert_eq!(impact.nodes[dead].edges[0].relation, Relation::Reads);
        assert!(
            !reached.iter().any(|(k, _)| k == "Game.Pawn.Armor"),
            "Armor was not touched: {reached:?}"
        );
    }

    #[test]
    fn one_step_through_an_interface() {
        const WIRE_BASE: &str = "namespace Wire {
    public interface IWriteable { void Write(); }
    public interface IPacket { void Put(); }
    public class Cash : IWriteable {
        public int Value;
        public void Write() {
            System.Console.WriteLine(Value);
        }
    }
    public class Packet : IPacket {
        public IWriteable Inner;
        public void Put() { Inner.Write(); }
    }
    public class Queue {
        public IPacket Next;
        public void Flush() { Next.Put(); }
    }
    public interface ISender { void Send(); }
    public class Sender : ISender {
        public Packet Packet;
        public void Send() { Packet.Put(); }
    }
    public class Loop {
        public ISender Sender;
        public void Go() { Sender.Send(); }
    }
    public class Writer {
        public void Put<T>(T value) where T : IWriteable { value.Write(); }
    }
}
";
        // A shared pass-through: nine places call Writer.Put<T>, each with
        // its own type.
        let hub: String = (0..9)
            .map(|i| {
                format!(
                    "    public class Other{i} : IWriteable {{\n        public void Write() {{ new Writer().Put(this); }}\n    }}\n"
                )
            })
            .collect();
        let wire = WIRE_BASE.replacen(
            "namespace Wire {\n",
            &format!("namespace Wire {{\n{hub}"),
            1,
        );
        let project = Project::new("poly", &[("Wire.cs", wire.as_str())]);
        let new = wire.replace("WriteLine(Value)", "WriteLine(Value + 1)");
        project.write("Wire.cs", &new);
        let session = project.session();
        let files = parse(&patch("Wire.cs", &wire, &new));
        let impact = walk(
            &project.root(),
            &session,
            &changes(&files[0], &new),
            Limits::default(),
        );
        let reached = reached(&impact);
        // Packet.Put calls Write on any IWriteable: it may reach Cash.
        assert!(
            reached.contains(&("Wire.Packet.Put()".to_owned(), 1)),
            "{reached:?}"
        );
        // A direct call of Packet.Put is reached; a call of any IPacket is not.
        assert!(
            reached.contains(&("Wire.Sender.Send()".to_owned(), 2)),
            "{reached:?}"
        );
        assert!(
            !reached.iter().any(|(k, _)| k == "Wire.Queue.Flush()"),
            "{reached:?}"
        );
        // And after the direct call, a second call through an interface on
        // the same path is not followed.
        assert!(
            !reached.iter().any(|(k, _)| k == "Wire.Loop.Go()"),
            "{reached:?}"
        );
        // The pass-through is reached, its nine callers are not.
        let put = impact
            .index_of("Wire.Writer.Put(T)")
            .unwrap_or_else(|| panic!("{reached:?}"));
        assert_eq!(impact.nodes[put].fan_in, 9);
        assert!(
            !reached.iter().any(|(k, _)| k.starts_with("Wire.Other")),
            "{reached:?}"
        );
    }

    #[test]
    fn removed_method_still_mentioned() {
        let new = PAWN.replace(
            "        public bool IsDead() {\n            return Health <= 0;\n        }\n",
            "",
        );
        let (impact, changes) = impact_of(&new);
        assert_eq!(
            changes
                .iter()
                .map(|c| (c.member.key.as_str(), c.how))
                .collect::<Vec<_>>(),
            vec![("Game.Pawn.IsDead()", How::Removed)]
        );
        let tick = impact
            .index_of("Game.Referee.Tick()")
            .expect("Tick mentions IsDead");
        assert_eq!(impact.nodes[tick].edges[0].relation, Relation::Mentions);
    }
}
