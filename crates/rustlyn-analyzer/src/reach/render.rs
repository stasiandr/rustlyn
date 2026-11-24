//! A report as a tree for people and as JSON for scripts and agents. Lines
//! are from one in both, as editors and compilers print them.

use std::fmt::Write as _;

use rustlyn_ide::formats::json::{Format, Json, object};

use super::judge::{Finding, FindingKind, Hop};
use super::{Judgement, Listed, Report, Role};

/// A step of a chain, in English.
fn hop_text(hop: &Hop) -> String {
    let sink = hop
        .sink
        .as_ref()
        .map(|sink| format!(" [{sink}]"))
        .unwrap_or_default();
    match hop.step {
        "calls" => format!("calls {}", hop.target),
        "calls_base" => format!("calls what {} overrides or implements", hop.target),
        "writes" => format!("writes {}", hop.target),
        "read_by" => format!("read by {}", hop.target),
        "called_by" => format!("called by {}", hop.target),
        "member_of" => format!("member of {}", hop.target),
        "holds" => format!("holds {}", hop.target),
        "serializes" => format!("holds the serialized data of {}", hop.target),
        "package_of" => format!("{} is the code of the sink{sink}", hop.target),
        "dependency_of" => format!("a dependency of {}{sink}", hop.target),
        "depends_on" => format!("depends on {}{sink}", hop.target),
        "used_by" => format!("used by {}", hop.target),
        "mentions" => format!("names the sink{sink}: {}", hop.target),
        "uses" => format!("uses {}{sink}", hop.target),
        "derives" => format!("derives from {}{sink}", hop.target),
        "removed" => format!("removed code named {}{sink}", hop.target),
        "named" => format!("the code named {}{sink}", hop.target),
        other => format!("{other} {}", hop.target),
    }
}

fn chain_text(out: &mut String, chain: &[Hop]) {
    for hop in chain {
        let _ = writeln!(out, "   → {}  {}:{}", hop_text(hop), hop.path, hop.line + 1);
    }
}

fn configurations_text(configurations: &[String], all: usize) -> String {
    let named: Vec<&str> = configurations
        .iter()
        .map(String::as_str)
        .filter(|name| !name.is_empty())
        .collect();
    if named.is_empty() || named.len() == all {
        String::new()
    } else {
        format!("  ({} only)", named.join(", "))
    }
}

/// The sinks a list of findings leads to for certain, each once.
fn sinks_of(findings: &[Finding]) -> Vec<&str> {
    let mut sinks: Vec<&str> = Vec::new();
    for finding in findings.iter().filter(|finding| finding.certain) {
        for sink in &finding.sinks {
            if !sinks.contains(&sink.as_str()) {
                sinks.push(sink);
            }
        }
    }
    sinks
}

/// One line for a past change: its id, its title and what it comes to.
#[must_use]
pub fn revision_headline(revision: &Judgement) -> String {
    let id: String = revision.id.chars().take(10).collect();
    let certain = revision.findings.iter().filter(|f| f.certain).count();
    let possible = revision.findings.len() - certain;
    let verdict = if certain > 0 {
        let sinks = sinks_of(&revision.findings);
        let to = if sinks.is_empty() {
            String::new()
        } else {
            format!(" {}", sinks.join(", "))
        };
        format!("AFFECTS{to} ({certain} findings)")
    } else if possible > 0 {
        format!("possibly ({possible})")
    } else {
        "not affected".to_owned()
    };
    format!("{id} {} — {verdict}", revision.title)
}

fn findings_text(out: &mut String, findings: &[Finding], all: usize, possible: bool, indent: &str) {
    for finding in findings {
        if !finding.certain && !possible {
            continue;
        }
        let only = configurations_text(&finding.configurations, all);
        let mut block = String::new();
        match finding.kind {
            FindingKind::Watch => {
                let _ = writeln!(block, "▣ {} — watched: {}", finding.path, finding.name);
            }
            FindingKind::Package => {
                let used = if finding.count > 0 {
                    format!(
                        ", used by {} members on the way, such as {}",
                        finding.count,
                        finding.chain.first().map_or("", |hop| hop.target.as_str())
                    )
                } else {
                    String::new()
                };
                let _ = writeln!(
                    block,
                    "▣ {}:{} — package {}{used}",
                    finding.path,
                    finding.line + 1,
                    finding.name
                );
                chain_text(&mut block, &finding.chain);
            }
            FindingKind::Mention => {
                let _ = writeln!(
                    block,
                    "▣ {}:{} — mentions {}",
                    finding.path,
                    finding.line + 1,
                    finding.name
                );
                chain_text(&mut block, &finding.chain);
            }
            FindingKind::Sink => {
                let _ = writeln!(block, "▣ {} — the source of {}", finding.path, finding.name);
            }
            FindingKind::Asset => {
                let _ = writeln!(block, "▣ {}:{}", finding.path, finding.line + 1);
                chain_text(&mut block, &finding.chain);
            }
            _ => {
                let mark = if finding.certain { '✎' } else { '?' };
                let role = finding
                    .role
                    .map(|role| format!(" [{}]", role.name()))
                    .unwrap_or_default();
                let _ = writeln!(
                    block,
                    "{mark} {}{role}  {}:{}{only}",
                    finding.name,
                    finding.path,
                    finding.line + 1
                );
                if !finding.certain {
                    let _ = writeln!(block, "   the change is not on the lines that lead on:");
                }
                chain_text(&mut block, &finding.chain);
            }
        }
        for line in block.lines() {
            let _ = writeln!(out, "{indent}{line}");
        }
    }
}

impl Report {
    /// The headline: what the change comes to.
    #[must_use]
    pub fn headline(&self) -> String {
        if !self.judged {
            let mut sizes = String::new();
            if !self.revisions.is_empty() {
                let affecting = self.revisions.iter().filter(|r| r.affects()).count();
                return format!(
                    "Reach «{}» over {} changes: {} lead to a sink.",
                    self.name,
                    self.revisions.len(),
                    affecting
                );
            }
            for summary in &self.summaries {
                let name = if summary.configuration.is_empty() {
                    String::new()
                } else {
                    format!("{}: ", summary.configuration)
                };
                let _ = write!(
                    sizes,
                    "\n  {name}{} on a path, {} helpers, {} data, {} users; {} places name a sink",
                    summary.path, summary.helpers, summary.data, summary.users, summary.hits
                );
            }
            return format!(
                "Reach «{}»: the cone of {}.{sizes}",
                self.name,
                self.sinks.join(", ")
            );
        }
        let certain = self.findings.iter().filter(|f| f.certain).count();
        let possible = self.findings.len() - certain;
        let sinks = sinks_of(&self.findings);
        let rest = format!(
            "{} possibly, {} changed members do not lead there",
            possible, self.unaffected
        );
        if certain == 0 {
            return format!("Reach «{}»: not affected. {rest}.", self.name);
        }
        let to = if sinks.is_empty() {
            String::new()
        } else {
            format!(" {}", sinks.join(", "))
        };
        format!(
            "Reach «{}»: AFFECTS{to} — {certain} findings; {rest}.",
            self.name
        )
    }

    /// The report as a tree. `possible` adds the members of the cone changed
    /// elsewhere than on the lines that lead on.
    #[must_use]
    pub fn text(&self, possible: bool) -> String {
        let mut out = String::new();
        let all = self.summaries.len();
        if self.judged || self.revisions.is_empty() {
            out.push_str(&self.headline());
            out.push('\n');
            findings_text(&mut out, &self.findings, all, possible, "");
        }
        if !self.revisions.is_empty() {
            let affecting = self.revisions.iter().filter(|r| r.affects()).count();
            let _ = writeln!(
                out,
                "Reach «{}» over {} changes: {} lead to a sink.",
                self.name,
                self.revisions.len(),
                affecting
            );
            for revision in &self.revisions {
                let mark = if revision.affects() { '●' } else { '○' };
                let _ = writeln!(out, "{mark} {}", revision_headline(revision));
                findings_text(&mut out, &revision.findings, all, possible, "   ");
            }
        }
        for summary in &self.summaries {
            if summary.failed > 0 || summary.truncated {
                let _ = writeln!(
                    out,
                    "note{}: {} files the compiler did not answer about{}",
                    if summary.configuration.is_empty() {
                        String::new()
                    } else {
                        format!(" ({})", summary.configuration)
                    },
                    summary.failed,
                    if summary.truncated {
                        "; the walk stopped at its depth"
                    } else {
                        ""
                    }
                );
            }
        }
        out.trim_end().to_owned()
    }

    /// The cone as a list: every member with its way to a sink, then the
    /// hubs. `users` adds the members that only use the cone through a hub.
    #[must_use]
    pub fn cone_text(&self, users: bool) -> String {
        let mut out = String::new();
        let all = self.summaries.len();
        for listed in &self.cone {
            if listed.role == Role::User && !users {
                continue;
            }
            let _ = writeln!(
                out,
                "{} [{} {}]  {}:{}{}",
                listed.name,
                listed.role.name(),
                listed.depth,
                listed.path,
                listed.line + 1,
                configurations_text(&listed.configurations, all)
            );
            chain_text(&mut out, &listed.chain);
        }
        if !self.hubs.is_empty() {
            let _ = writeln!(out, "hubs (not followed through):");
            for hub in &self.hubs {
                let _ = writeln!(
                    out,
                    "   {} — {} users  {}:{}",
                    hub.name,
                    hub.users,
                    hub.path,
                    hub.line + 1
                );
            }
        }
        if !self.packages.provided.is_empty() || !self.packages.used.is_empty() {
            let _ = writeln!(out, "packages:");
            for (sink, packages) in &self.packages.provided {
                let _ = writeln!(out, "   {sink} is provided by {}", packages.join(", "));
            }
            if !self.packages.used.is_empty() {
                let _ = writeln!(out, "   used by the cone, on lines that matter:");
                for used in &self.packages.used {
                    let _ = writeln!(out, "      {} — {} members", used.name, used.members);
                }
            }
        }
        out.trim_end().to_owned()
    }

    /// The report as the text a tool prints: [`Report::json`] pretty-printed
    /// with sorted keys, so that two runs can be compared as text.
    #[must_use]
    pub fn json_text(&self, cone: bool) -> String {
        self.json(cone).to_text_with(Format::PRETTY_SORTED)
    }

    /// The report for machines (schema `version: 1`). `cone` adds the whole
    /// cone.
    #[must_use]
    pub fn json(&self, cone: bool) -> Json {
        let strings =
            |list: &[String]| Json::Array(list.iter().map(|s| Json::String(s.clone())).collect());
        let hops = |chain: &[Hop]| {
            Json::Array(
                chain
                    .iter()
                    .map(|hop| {
                        let mut items = vec![
                            ("step", Json::String(hop.step.to_owned())),
                            ("target", Json::String(hop.target.clone())),
                            ("path", Json::String(hop.path.clone())),
                            ("line", Json::Int(hop.line as i64 + 1)),
                            ("text", Json::String(hop_text(hop))),
                        ];
                        if let Some(sink) = &hop.sink {
                            items.push(("sink", Json::String(sink.clone())));
                        }
                        object(items)
                    })
                    .collect(),
            )
        };
        let finding = |finding: &Finding| {
            let mut items = vec![
                ("kind", Json::String(finding.kind.name().to_owned())),
                ("certain", Json::Bool(finding.certain)),
                ("path", Json::String(finding.path.clone())),
                ("line", Json::Int(finding.line as i64 + 1)),
                ("name", Json::String(finding.name.clone())),
                (
                    "lines",
                    Json::Array(
                        finding
                            .lines
                            .iter()
                            .map(|&line| Json::Int(line as i64 + 1))
                            .collect(),
                    ),
                ),
                ("chain", hops(&finding.chain)),
                ("sinks", strings(&finding.sinks)),
                ("configurations", strings(&finding.configurations)),
                ("count", Json::Int(finding.count as i64)),
            ];
            if let Some(role) = finding.role {
                items.push(("role", Json::String(role.name().to_owned())));
            }
            object(items)
        };
        let listed = |listed: &Listed| {
            object(vec![
                ("name", Json::String(listed.name.clone())),
                ("role", Json::String(listed.role.name().to_owned())),
                ("depth", Json::Int(listed.depth as i64)),
                ("path", Json::String(listed.path.clone())),
                ("line", Json::Int(listed.line as i64 + 1)),
                ("chain", hops(&listed.chain)),
                ("sinks", strings(&listed.sinks)),
                ("configurations", strings(&listed.configurations)),
            ])
        };
        let mut items = vec![
            ("version", Json::Int(1)),
            ("name", Json::String(self.name.clone())),
            ("sinks", strings(&self.sinks)),
            ("judged", Json::Bool(self.judged)),
            ("affects", Json::Bool(self.affects())),
            ("headline", Json::String(self.headline())),
            (
                "findings",
                Json::Array(self.findings.iter().map(finding).collect()),
            ),
            ("unaffected", Json::Int(self.unaffected as i64)),
            (
                "configurations",
                Json::Array(
                    self.summaries
                        .iter()
                        .map(|summary| {
                            object(vec![
                                ("name", Json::String(summary.configuration.clone())),
                                ("files", Json::Int(summary.files as i64)),
                                ("members", Json::Int(summary.members as i64)),
                                ("hits", Json::Int(summary.hits as i64)),
                                ("path", Json::Int(summary.path as i64)),
                                ("helpers", Json::Int(summary.helpers as i64)),
                                ("data", Json::Int(summary.data as i64)),
                                ("users", Json::Int(summary.users as i64)),
                                ("failed", Json::Int(summary.failed as i64)),
                                ("truncated", Json::Bool(summary.truncated)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ];
        if !self.revisions.is_empty() {
            items.push((
                "revisions",
                Json::Array(
                    self.revisions
                        .iter()
                        .map(|revision| {
                            object(vec![
                                ("id", Json::String(revision.id.clone())),
                                ("title", Json::String(revision.title.clone())),
                                ("affects", Json::Bool(revision.affects())),
                                ("headline", Json::String(revision_headline(revision))),
                                (
                                    "findings",
                                    Json::Array(revision.findings.iter().map(finding).collect()),
                                ),
                                ("unaffected", Json::Int(revision.unaffected as i64)),
                            ])
                        })
                        .collect(),
                ),
            ));
        }
        if cone {
            items.push((
                "packages",
                object(vec![
                    (
                        "provided",
                        Json::Array(
                            self.packages
                                .provided
                                .iter()
                                .map(|(sink, packages)| {
                                    object(vec![
                                        ("sink", Json::String(sink.clone())),
                                        ("packages", strings(packages)),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                    (
                        "used",
                        Json::Array(
                            self.packages
                                .used
                                .iter()
                                .map(|used| {
                                    object(vec![
                                        ("name", Json::String(used.name.clone())),
                                        ("members", Json::Int(used.members as i64)),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                ]),
            ));
            items.push(("cone", Json::Array(self.cone.iter().map(listed).collect())));
            items.push((
                "hubs",
                Json::Array(
                    self.hubs
                        .iter()
                        .map(|hub| {
                            object(vec![
                                ("name", Json::String(hub.name.clone())),
                                ("users", Json::Int(hub.users as i64)),
                                ("path", Json::String(hub.path.clone())),
                                ("line", Json::Int(hub.line as i64 + 1)),
                            ])
                        })
                        .collect(),
                ),
            ));
        }
        object(items)
    }
}
