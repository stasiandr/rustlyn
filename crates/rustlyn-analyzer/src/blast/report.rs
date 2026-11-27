//! The whole report, from the patch to the risks, and how it looks to an
//! agent (JSON) and to a person (a tree).
//!
//! The JSON is a stable schema, `version: 1`: lines in it are from one, as
//! in an editor and in `grep -n`; risk, change and relation codes are
//! English words. The sentences — risk texts and the tree — come from a
//! [`Wording`]: English by default, a host's language otherwise.

use std::collections::HashMap;
use std::path::Path;
use std::time::Instant;

use rustlyn_ide::Session;
use rustlyn_ide::formats::json::{Format, Json, object};
use rustlyn_ide::outline::DeclarationKind;

use super::assets::UnityAssets;
use super::changes::{Change, How, changes};
use super::diff::{FileDiff, Status, between, parse};
use super::risk::{Level, Risk, assess};
use super::walk::{Edge, Impact, Limits, Relation, walk_with};
use super::{BlastStep, Extensions, Finding, StepContext, StepFindings};

/// What is asked.
#[derive(Debug, Clone)]
pub struct Request {
    /// The project root; the patch's paths are relative to it.
    pub root: String,
    pub patch: String,
    pub limits: Limits,
    /// The unsaved texts of open files: relative path → text. Their change
    /// against the disk (or against what the patch compares with) is part
    /// of the report too.
    pub unsaved: HashMap<String, String>,
}

impl Request {
    #[must_use]
    pub fn new(root: impl Into<String>, patch: impl Into<String>) -> Self {
        Self {
            root: root.into(),
            patch: patch.into(),
            limits: Limits::default(),
            unsaved: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Report {
    pub root: String,
    pub files: Vec<FileDiff>,
    pub changes: Vec<Change>,
    pub impact: Impact,
    /// The reasons for risk of the nodes, in node order.
    pub risks: Vec<Vec<Risk>>,
    /// What each step found, in the order the steps ran.
    pub findings: Vec<StepFindings>,
    pub milliseconds: u128,
    /// How many milliseconds each phase took, to see what is slow.
    pub phases: Vec<(&'static str, u128)>,
}

/// The report on a patch. `session` is the compiled project in
/// `request.root`. The host's steps run first, then the built-in Unity
/// step; risks are the walk's and Unity's, then each model's, then the
/// steps'.
#[must_use]
pub fn analyze(request: &Request, session: &Session, extensions: &Extensions<'_>) -> Report {
    let started = Instant::now();
    let mut phases = Vec::new();
    let mut lap = Instant::now();
    let mut phase = |name: &'static str| {
        phases.push((name, lap.elapsed().as_millis()));
        lap = Instant::now();
    };
    let mut files = parse(&request.patch);
    // The unsaved text against what the patch compares with: so the report
    // has both the saved and the unsaved part of the change.
    let mut unsaved: Vec<&String> = request.unsaved.keys().collect();
    unsaved.sort();
    for path in unsaved {
        let buffer = &request.unsaved[path];
        let disk = rustlyn_ide::document::read_source(Path::new(&request.root).join(path))
            .unwrap_or_default();
        let base = match files.iter().position(|f| &f.path == path) {
            Some(i) => files.remove(i).old_text(&disk),
            None => disk,
        };
        let file = between(path, &base, buffer);
        if !file.blocks.is_empty() {
            files.push(file);
        }
    }
    let mut found = Vec::new();
    let mut old_texts = HashMap::new();
    for file in &files {
        if !file.path.ends_with(".cs")
            && !file.old_path.as_deref().is_some_and(|p| p.ends_with(".cs"))
        {
            continue;
        }
        let text = if file.status == Status::Deleted {
            String::new()
        } else if let Some(buffer) = request.unsaved.get(&file.path) {
            buffer.clone()
        } else {
            rustlyn_ide::document::read_source(Path::new(&request.root).join(&file.path))
                .unwrap_or_default()
        };
        found.extend(changes(file, &text));
        old_texts.insert(file.path.clone(), file.old_text(&text));
    }
    phase("diff");
    let impact = walk_with(
        &request.root,
        session,
        &found,
        request.limits,
        &request.unsaved,
    );
    phase("walk");
    let cx = StepContext {
        root: &request.root,
        session,
        old_texts: &old_texts,
    };
    let built_in = UnityAssets;
    let steps = extensions
        .steps
        .iter()
        .copied()
        .chain(std::iter::once(&built_in as &dyn BlastStep));
    let mut findings = Vec::new();
    for step in steps {
        findings.push(StepFindings {
            step: step.name(),
            findings: step.run(&cx, &impact),
        });
        phase(step.name());
    }
    let mut risks = assess(&impact, &extensions.risks, &old_texts);
    for finding in findings.iter().flat_map(|s| &s.findings) {
        for (index, risk) in &finding.risks {
            if let Some(list) = risks.get_mut(*index) {
                list.push(risk.clone());
            }
        }
    }
    phase("risks");
    Report {
        root: request.root.clone(),
        files,
        changes: found,
        impact,
        risks,
        findings,
        milliseconds: started.elapsed().as_millis(),
        phases,
    }
}

/// How a report is put into words: the risk texts in its JSON and the
/// whole text tree. Every method has an English default; a host overrides
/// them to speak its language.
pub trait Wording {
    /// A reason for risk, as a sentence.
    fn risk(&self, risk: &Risk) -> String {
        risk.reason.to_string()
    }

    fn level(&self, level: Option<Level>) -> String {
        level.map_or("none", Level::name).to_owned()
    }

    fn how(&self, how: How) -> String {
        match how {
            How::Body => "body",
            How::Signature => "declaration",
            How::Added => "new",
            How::Removed => "removed",
        }
        .to_owned()
    }

    fn relation(&self, relation: Relation) -> String {
        match relation {
            Relation::Calls => "calls",
            Relation::CallsBase => "calls through a base",
            Relation::Reads => "reads",
            Relation::Writes => "writes",
            Relation::Uses => "uses",
            Relation::WrittenBy => "the change writes it",
            Relation::Mentions => "mentions by name",
        }
        .to_owned()
    }

    /// The first line of the tree.
    fn summary(&self, report: &Report) -> String {
        let changed = report.changed();
        let mut text = format!(
            "Change: {changed} changed members in {} files; {} more reached",
            report.files.len(),
            report.impact.nodes.len() - changed
        );
        for step in &report.findings {
            text += &format!(", {} {}", step.step, step.findings.len());
        }
        text += &format!(". Risk: {}.", self.level(report.level()));
        if report.impact.truncated {
            text += " The walk hit its limits.";
        }
        text
    }

    /// A node printed earlier in the tree.
    fn see_above(&self) -> String {
        "(see above)".to_owned()
    }

    /// The children of a node not shown.
    fn more(&self, count: usize) -> String {
        format!("… {count} more (all of them in --json)")
    }

    /// A step's finding in the tree: a heading line, then detail lines.
    fn finding(&self, _step: &str, finding: &Finding) -> Vec<String> {
        finding.text.clone()
    }
}

/// The default wording.
#[derive(Debug, Clone, Copy, Default)]
pub struct English;

impl Wording for English {}

impl Report {
    /// The highest risk; `None`: no risks.
    #[must_use]
    pub fn level(&self) -> Option<Level> {
        self.risks.iter().flatten().map(|r| r.level).max()
    }

    /// How many nodes the change touched itself.
    #[must_use]
    pub fn changed(&self) -> usize {
        self.impact
            .nodes
            .iter()
            .filter(|n| n.change.is_some())
            .count()
    }

    /// What one step found; empty when it did not run.
    #[must_use]
    pub fn findings_of(&self, step: &str) -> &[Finding] {
        self.findings
            .iter()
            .find(|s| s.step == step)
            .map_or(&[], |s| &s.findings)
    }

    /// The risks of all nodes, highest first: (node, risk).
    #[must_use]
    pub fn top_risks(&self) -> Vec<(usize, &Risk)> {
        let mut all: Vec<(usize, &Risk)> = self
            .risks
            .iter()
            .enumerate()
            .flat_map(|(i, rs)| rs.iter().map(move |r| (i, r)))
            .collect();
        all.sort_by(|a, b| {
            b.1.level.cmp(&a.1.level).then(
                self.impact.nodes[a.0]
                    .depth
                    .cmp(&self.impact.nodes[b.0].depth),
            )
        });
        all
    }

    /// The JSON, in English.
    #[must_use]
    pub fn json(&self) -> Json {
        self.json_with(&English)
    }

    /// The JSON with the risk texts in `wording`.
    #[must_use]
    pub fn json_with(&self, wording: &dyn Wording) -> Json {
        let risk_json = |risk: &Risk| -> Json {
            let mut items = vec![
                ("level", Json::String(risk.level.name().to_owned())),
                ("code", Json::String(risk.code().to_owned())),
                ("text", Json::String(wording.risk(risk))),
            ];
            if let Some((path, line)) = &risk.at {
                items.push(("path", Json::String(path.clone())));
                items.push(("line", Json::Int(*line as i64 + 1)));
            }
            object(items)
        };
        let nodes: Vec<Json> = self
            .impact
            .nodes
            .iter()
            .enumerate()
            .map(|(i, node)| {
                let m = &node.member;
                let mut entry = vec![
                    ("id", Json::Int(i as i64)),
                    ("name", Json::String(m.name.clone())),
                    ("key", Json::String(m.key.clone())),
                    ("kind", Json::String(kind_name(m.kind).to_owned())),
                    ("path", Json::String(m.path.clone())),
                    ("line", Json::Int(m.line as i64 + 1)),
                    ("depth", Json::Int(node.depth as i64)),
                    ("fan_in", Json::Int(node.fan_in as i64)),
                ];
                if let Some(how) = node.change {
                    entry.push(("change", Json::String(how.name().to_owned())));
                }
                entry.push((
                    "via",
                    Json::Array(node.edges.iter().map(edge_json).collect()),
                ));
                entry.push((
                    "risks",
                    Json::Array(self.risks[i].iter().map(risk_json).collect()),
                ));
                object(entry)
            })
            .collect();
        let top: Vec<Json> = self
            .top_risks()
            .into_iter()
            .take(20)
            .map(|(i, r)| {
                let mut entry = risk_json(r);
                if let Json::Object(items) = &mut entry {
                    items.insert(0, ("node".to_owned(), Json::Int(i as i64)));
                    items.insert(
                        1,
                        (
                            "name".to_owned(),
                            Json::String(self.impact.nodes[i].member.name.clone()),
                        ),
                    );
                }
                entry
            })
            .collect();
        let changed = self.changed();
        let mut summary = vec![
            ("files", Json::Int(self.files.len() as i64)),
            ("changed", Json::Int(changed as i64)),
            (
                "affected",
                Json::Int((self.impact.nodes.len() - changed) as i64),
            ),
        ];
        for step in &self.findings {
            summary.push((step.step, Json::Int(step.findings.len() as i64)));
        }
        summary.extend([
            (
                "risk",
                Json::String(self.level().map_or("none", Level::name).to_owned()),
            ),
            ("truncated", Json::Bool(self.impact.truncated)),
            ("milliseconds", Json::Int(self.milliseconds as i64)),
            (
                "phases",
                object(
                    self.phases
                        .iter()
                        .map(|(n, ms)| (*n, Json::Int(*ms as i64)))
                        .collect(),
                ),
            ),
        ]);
        let mut all = vec![
            ("version", Json::Int(1)),
            ("root", Json::String(self.root.clone())),
            ("summary", object(summary)),
            ("top_risks", Json::Array(top)),
            ("nodes", Json::Array(nodes)),
        ];
        for step in &self.findings {
            all.push((
                step.step,
                Json::Array(step.findings.iter().map(|f| f.json.clone()).collect()),
            ));
        }
        object(all)
    }

    /// The JSON as indented text, in English.
    #[must_use]
    pub fn json_text(&self) -> String {
        json_text(&self.json())
    }

    /// The tree for a terminal, in English.
    #[must_use]
    pub fn text(&self) -> String {
        self.text_with(&English)
    }

    /// The tree for a terminal: what changed, and under it what depends on
    /// it.
    #[must_use]
    pub fn text_with(&self, wording: &dyn Wording) -> String {
        let nodes = &self.impact.nodes;
        let mut out = vec![wording.summary(self)];
        let mut printed = vec![false; nodes.len()];
        for (index, node) in nodes.iter().enumerate() {
            if node.change.is_some() {
                self.tree(wording, index, None, "", &mut printed, &mut out);
            }
        }
        for step in &self.findings {
            for finding in &step.findings {
                for (k, line) in wording.finding(step.step, finding).into_iter().enumerate() {
                    out.push(if k == 0 { line } else { format!("   {line}") });
                }
            }
        }
        out.join("\n")
    }

    fn tree(
        &self,
        wording: &dyn Wording,
        index: usize,
        edge: Option<&Edge>,
        prefix: &str,
        printed: &mut Vec<bool>,
        out: &mut Vec<String>,
    ) {
        let node = &self.impact.nodes[index];
        let m = &node.member;
        let head = match (node.change, edge) {
            (Some(how), _) => format!(
                "✎ {} [{}] {}:{}",
                m.key,
                wording.how(how),
                m.path,
                m.line + 1
            ),
            (None, Some(edge)) => format!(
                "← {} — {} {}:{}",
                m.key,
                wording.relation(edge.relation),
                edge.path,
                edge.line + 1
            ),
            (None, None) => format!("· {} {}:{}", m.key, m.path, m.line + 1),
        };
        if printed[index] {
            out.push(format!("{prefix}{head} {}", wording.see_above()));
            return;
        }
        printed[index] = true;
        out.push(format!("{prefix}{head}"));
        for risk in &self.risks[index] {
            out.push(format!(
                "{prefix}   ⚠ {}: {}",
                wording.level(Some(risk.level)),
                wording.risk(risk)
            ));
        }
        let children: Vec<(usize, &Edge)> = self
            .impact
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.change.is_none())
            .filter_map(|(child, n)| n.edges.iter().find(|e| e.from == index).map(|e| (child, e)))
            .collect();
        for &(child, edge) in children.iter().take(CHILDREN) {
            self.tree(
                wording,
                child,
                Some(edge),
                &format!("{prefix}   "),
                printed,
                out,
            );
        }
        if children.len() > CHILDREN {
            out.push(format!(
                "{prefix}   {}",
                wording.more(children.len() - CHILDREN)
            ));
        }
    }
}

/// JSON as indented text, keys in their order, `/` as it is.
#[must_use]
pub fn json_text(json: &Json) -> String {
    json.to_text_with(Format {
        pretty: true,
        sorted_keys: false,
        escape_slashes: false,
    })
}

/// How many dependents to show under a node in the tree.
const CHILDREN: usize = 8;

fn edge_json(edge: &Edge) -> Json {
    object(vec![
        ("from", Json::Int(edge.from as i64)),
        ("relation", Json::String(edge.relation.name().to_owned())),
        ("path", Json::String(edge.path.clone())),
        ("line", Json::Int(edge.line as i64 + 1)),
    ])
}

/// The stable English code of a declaration kind.
#[must_use]
pub const fn kind_name(kind: DeclarationKind) -> &'static str {
    match kind {
        DeclarationKind::Namespace => "namespace",
        DeclarationKind::Class => "class",
        DeclarationKind::Struct => "struct",
        DeclarationKind::Interface => "interface",
        DeclarationKind::Enum => "enum",
        DeclarationKind::Record => "record",
        DeclarationKind::Delegate => "delegate",
        DeclarationKind::Method => "method",
        DeclarationKind::Constructor => "constructor",
        DeclarationKind::Destructor => "destructor",
        DeclarationKind::Property => "property",
        DeclarationKind::Indexer => "indexer",
        DeclarationKind::Field => "field",
        DeclarationKind::Event => "event",
        DeclarationKind::EnumMember => "enum_member",
        DeclarationKind::Operator => "operator",
        DeclarationKind::Extension => "extension",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::testing::{Project, patch};

    const PAWN: &str = "namespace Game {
    public class Pawn {
        public int Health;
        public void Heal(int by) { Health += by; }
        public bool IsDead() { return Health <= 0; }
    }
    public class Referee {
        Pawn pawn;
        void Update() { if (pawn.IsDead()) { } pawn.Heal(1); }
    }
}
";

    #[test]
    fn report_json_and_tree() {
        let project = Project::new("report", &[("Pawn.cs", PAWN)]);
        let new = PAWN.replace("Heal(int by)", "Heal(long by)");
        project.write("Pawn.cs", &new);
        let session = project.session();
        let request = Request::new(project.root(), patch("Pawn.cs", PAWN, &new));
        let report = analyze(&request, &session, &Extensions::default());
        let json = report.json();
        let summary = json.get("summary").expect("summary");
        assert_eq!(summary.int("changed"), Some(1));
        assert_eq!(summary.int("assets"), Some(0));
        assert_eq!(
            summary.str("risk"),
            Some("medium"),
            "{}",
            report.json_text()
        );
        let nodes = json.objects("nodes").expect("nodes");
        let update = nodes
            .iter()
            .find(|n| n.str("key") == Some("Game.Referee.Update()"))
            .expect("Update reached");
        assert_eq!(
            update.objects("via").expect("via")[0].str("relation"),
            Some("calls")
        );
        assert!(
            update
                .objects("risks")
                .expect("risks")
                .iter()
                .any(|r| r.str("code") == Some("per_frame"))
        );
        let text = report.text();
        assert!(
            text.contains("✎ Game.Pawn.Heal(long) [declaration] Pawn.cs:4"),
            "{text}"
        );
        assert!(
            text.contains("← Game.Referee.Update() — calls Pawn.cs:9"),
            "{text}"
        );
    }

    #[test]
    fn unsaved_change_of_a_buffer() {
        let project = Project::new("unsaved", &[("Pawn.cs", PAWN)]);
        let session = project.session();
        let mut request = Request::new(project.root(), "");
        let buffer = PAWN.replace("Health += by;", "Health += by * 2;");
        request.unsaved.insert("Pawn.cs".to_owned(), buffer.clone());
        let _ = session.open_text(format!("{}/Pawn.cs", project.root()), &buffer);
        let report = analyze(&request, &session, &Extensions::default());
        let keys: Vec<(&str, Option<How>)> = report
            .impact
            .nodes
            .iter()
            .map(|n| (n.member.key.as_str(), n.change))
            .collect();
        assert!(
            keys.contains(&("Game.Pawn.Heal(int)", Some(How::Body))),
            "{keys:?}"
        );
        assert!(keys.contains(&("Game.Referee.Update()", None)), "{keys:?}");
    }
}
