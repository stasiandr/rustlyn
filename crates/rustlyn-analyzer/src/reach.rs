//! Reach: does a change lead to a given set of APIs.
//!
//! A blast radius ([`crate::blast`]) starts at a change and asks what it
//! reaches. This starts at the other end. A caller names *sinks* — an SDK's
//! namespaces, a vendor folder, an assembly — and the analysis works out the
//! *cone* of the project's own code that leads to them: who calls the sinks,
//! who calls those callers, which fields and ECS components they read and
//! who writes those ([`cone`]). A change is then judged against the cone:
//! it touches a member on a path to a sink, with the chain from the change
//! to the sink to show for it, or it does not ([`judge`]). Past changes —
//! the commits of a release — are judged against the same cone, by the
//! names of the members they changed ([`Revision`]).
//!
//! The cone is worked out for each build of the project a caller asks about
//! ([`Configuration`]): the code that talks to a device SDK usually sits
//! behind `#if UNITY_ANDROID && !UNITY_EDITOR`, which a Unity project's own
//! compile — its editor's — leaves out.
//!
//! Not everything that concerns a sink is code. [`Watch`] lists files to
//! report as they are — a package manifest, a vendor folder — and a changed
//! scene, prefab or asset is reported when the change is in the serialized
//! data of a script whose fields the cone reads. A change to a Unity package
//! is judged per package ([`packages`]): it concerns a sink when it is the
//! sink's code, depends on it or is depended on by it, or when the code on
//! the way to a sink uses it. A changed line of a native build file — a
//! Gradle dependency, a pod — that names a sink is reported by the mention.

pub mod cone;
pub mod config;
pub mod git;
pub mod graph;
pub mod judge;
pub mod packages;
pub mod render;

mod text;
mod uses;

#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::Path;
use std::path::PathBuf;
use std::time::Instant;

pub use cone::{Cone, Role, Step};
pub use config::{Config, Configuration, Limits, Sink, Watch};
pub use judge::{Finding, FindingKind, Hop};
pub use packages::Packages;
pub use render::revision_headline;

use crate::blast::diff::{FileDiff, parse};
use crate::blast::project;

/// A member of the cone, as a listing shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Listed {
    pub path: String,
    /// From zero.
    pub line: usize,
    /// The member's name with its parameter types.
    pub name: String,
    pub role: Role,
    pub depth: usize,
    /// The way from it to a sink.
    pub chain: Vec<Hop>,
    /// The sinks it leads to.
    pub sinks: Vec<String>,
    /// The configurations it is in the cone of.
    pub configurations: Vec<String>,
}

/// A member of the cone the walk did not go through: too many use it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListedHub {
    pub path: String,
    pub line: usize,
    pub name: String,
    /// How many members call or write it.
    pub users: usize,
}

/// What one configuration came to.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Summary {
    pub configuration: String,
    /// Own files read, and members in them.
    pub files: usize,
    pub members: usize,
    /// Places where own code names a sink.
    pub hits: usize,
    /// Members of the cone by role: on a path, helpers, data, users.
    pub path: usize,
    pub helpers: usize,
    pub data: usize,
    pub users: usize,
    /// Files the compiler could not answer about.
    pub failed: usize,
    pub truncated: bool,
}

/// The packages that matter to a configuration's sinks, for `--cone`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PackageSection {
    /// Each sink with the packages that provide it, found in the code or
    /// named in the configuration. Sinks no package provides are left out.
    pub provided: Vec<(String, Vec<String>)>,
    /// The packages the cone uses on lines that matter, with the number of
    /// members that do, most used first. Packages that provide a sink are
    /// in `provided`, not here.
    pub used: Vec<UsedPackage>,
}

/// A package the cone uses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UsedPackage {
    pub name: String,
    pub members: usize,
}

/// The answer.
#[derive(Debug, Clone, Default)]
pub struct Report {
    pub name: String,
    /// The sinks' names, in the configuration's order.
    pub sinks: Vec<String>,
    /// What of the change leads to a sink. Empty without a change.
    pub findings: Vec<Finding>,
    /// Changed members of own code that lead to none.
    pub unaffected: usize,
    /// Changed packages that lead to none.
    pub unaffected_packages: usize,
    /// Whether a change was judged at all.
    pub judged: bool,
    /// The request's past changes, judged, in its order.
    pub revisions: Vec<Judgement>,
    pub cone: Vec<Listed>,
    pub hubs: Vec<ListedHub>,
    pub packages: PackageSection,
    pub summaries: Vec<Summary>,
    /// The time of each phase: (configuration, phase, milliseconds).
    pub phases: Vec<(String, &'static str, u128)>,
}

impl Report {
    /// Whether the change, or any of the past changes, leads to a sink for
    /// certain.
    #[must_use]
    pub fn affects(&self) -> bool {
        self.findings.iter().any(|finding| finding.certain)
            || self.revisions.iter().any(Judgement::affects)
    }
}

/// A past change to judge against the code as it is now: a commit, a
/// merged branch.
#[derive(Debug, Clone, Default)]
pub struct Revision {
    /// What to call it: a commit's hash.
    pub id: String,
    pub title: String,
    /// Its unified diff.
    pub patch: String,
    /// The text of each changed source file after the change, by path.
    pub texts: HashMap<String, String>,
    /// The paths the change touched that have no diff above — a scene, a
    /// binary — which a watch needs only by name.
    pub others: Vec<String>,
}

/// What a past change comes to.
#[derive(Debug, Clone, Default)]
pub struct Judgement {
    pub id: String,
    pub title: String,
    pub findings: Vec<Finding>,
    /// Changed members of own code that lead to no sink.
    pub unaffected: usize,
    /// Changed packages that lead to no sink.
    pub unaffected_packages: usize,
}

impl Judgement {
    /// Whether the change leads to a sink for certain.
    #[must_use]
    pub fn affects(&self) -> bool {
        self.findings.iter().any(|finding| finding.certain)
    }
}

/// What to analyze.
#[derive(Debug, Clone, Default)]
pub struct Request {
    /// The project root, canonical.
    pub root: String,
    /// A unified diff of the code as it is now against an earlier state,
    /// to judge. `None`: no such change.
    pub patch: Option<String>,
    /// Past changes to judge against the cone of the code as it is now.
    pub revisions: Vec<Revision>,
    /// A folder to keep each configuration's compilation in between runs.
    pub cache: Option<PathBuf>,
}

/// Works out the cone of `config`'s sinks in the project and judges the
/// request's change against it.
///
/// # Errors
///
/// When the compiler fails on the project.
pub fn analyze(request: &Request, config: &Config) -> Result<Report, String> {
    let files: Option<Vec<FileDiff>> = request.patch.as_deref().map(parse);
    let mut report = Report {
        name: config.name.clone(),
        sinks: config.sinks.iter().map(|sink| sink.name.clone()).collect(),
        judged: files.is_some(),
        ..Report::default()
    };
    let default = [Configuration::default()];
    let configurations: &[Configuration] = if config.configurations.is_empty() {
        &default
    } else {
        &config.configurations
    };
    let mut cone: BTreeMap<(String, usize, String), Listed> = BTreeMap::new();
    let mut hubs: BTreeMap<(String, usize), ListedHub> = BTreeMap::new();
    let mut findings: Vec<Finding> = Vec::new();
    let mut unaffected: BTreeMap<(String, String), bool> = BTreeMap::new();
    let mut unaffected_packages: BTreeMap<(String, String), bool> = BTreeMap::new();
    let past: Vec<Vec<FileDiff>> = request
        .revisions
        .iter()
        .map(|revision| parse(&revision.patch))
        .collect();
    let mut past_findings: Vec<Vec<Finding>> = vec![Vec::new(); past.len()];
    let mut past_unaffected: Vec<BTreeMap<(String, String), bool>> =
        vec![BTreeMap::new(); past.len()];
    let mut past_unaffected_packages: Vec<BTreeMap<(String, String), bool>> =
        vec![BTreeMap::new(); past.len()];
    let known = Packages::read(&request.root);
    let package_changes = files.as_deref().map(|files| {
        packages::changes(files, &|path| {
            rustlyn_ide::document::read_source(Path::new(&request.root).join(path)).ok()
        })
    });
    let past_changes: Vec<packages::Changes> = request
        .revisions
        .iter()
        .zip(&past)
        .map(|(revision, files)| {
            packages::changes(files, &|path| revision.texts.get(path).cloned())
        })
        .collect();
    let mut provided: BTreeMap<usize, BTreeSet<String>> = BTreeMap::new();
    let mut used: BTreeMap<String, BTreeSet<(String, String)>> = BTreeMap::new();
    for configuration in configurations {
        let name = configuration.name.clone();
        let mut phases = Vec::new();
        let folder = request.cache.as_ref().map(|base| {
            let folder = base.join(if name.is_empty() { "default" } else { &name });
            let _ = std::fs::create_dir_all(&folder);
            folder
        });
        let session = project::compiled_with(
            &request.root,
            folder,
            configuration.symbols.clone(),
            &mut phases,
        )?;
        let semantic = session
            .semantic()
            .ok_or("the project did not compile: no source files found")?;
        let mut lap = Instant::now();
        let graph = graph::build(&request.root, &semantic, config, &known);
        phases.push(("graph", lap.elapsed().as_millis()));
        lap = Instant::now();
        let walked = cone::walk(&request.root, &semantic, &graph, config);
        phases.push(("walk", lap.elapsed().as_millis()));
        lap = Instant::now();

        let mut summary = Summary {
            configuration: name.clone(),
            files: graph.files.len(),
            members: graph.len(),
            hits: graph.hits.len(),
            failed: graph.failed,
            truncated: walked.truncated,
            ..Summary::default()
        };
        for (&node, entry) in &walked.entries {
            match entry.role {
                Role::Path => summary.path += 1,
                Role::Helper => summary.helpers += 1,
                Role::Data => summary.data += 1,
                Role::User => summary.users += 1,
            }
            let member = graph.member(node);
            let (chain, sinks) = judge::chain(&graph, &walked, config, node, None);
            let listed = cone
                .entry((member.path.clone(), member.line, member.key.clone()))
                .or_insert_with(|| Listed {
                    path: member.path.clone(),
                    line: member.line,
                    name: member.key.clone(),
                    role: entry.role,
                    depth: entry.depth,
                    chain,
                    sinks: Vec::new(),
                    configurations: Vec::new(),
                });
            listed.role = listed.role.max(entry.role);
            for sink in sinks {
                if !listed.sinks.contains(&sink) {
                    listed.sinks.push(sink);
                }
            }
            listed.configurations.push(name.clone());
        }
        for hub in &walked.hubs {
            let member = graph.member(hub.node);
            hubs.entry((member.path.clone(), member.line))
                .or_insert_with(|| ListedHub {
                    path: member.path.clone(),
                    line: member.line,
                    name: member.key.clone(),
                    users: hub.users,
                });
        }
        let providers = judge::providers(&graph, config, &known, &[]);
        for (package, sinks) in &providers {
            for &sink in sinks {
                provided.entry(sink).or_default().insert(package.clone());
            }
        }
        for package in &graph.packages {
            if providers.contains_key(package) {
                continue;
            }
            for (node, _) in judge::used_on_the_way(&graph, &walked, package) {
                let member = graph.member(node);
                used.entry(package.clone())
                    .or_default()
                    .insert((member.path.clone(), member.key.clone()));
            }
        }
        if let Some(files) = &files {
            let judged = judge::judge(&request.root, &graph, &walked, config, files);
            for mut finding in judged.findings {
                finding.configurations = vec![name.clone()];
                findings.push(finding);
            }
            for key in judged.unaffected {
                unaffected.entry(key).or_insert(true);
            }
            if let Some(changes) = &package_changes {
                let judged = judge::packages(&graph, &walked, config, &known, changes);
                for mut finding in judged.findings {
                    finding.configurations = vec![name.clone()];
                    findings.push(finding);
                }
                for key in judged.unaffected {
                    unaffected_packages.entry(key).or_insert(true);
                }
            }
            phases.push(("judge", lap.elapsed().as_millis()));
        }
        for (index, revision) in request.revisions.iter().enumerate() {
            let judged = judge::judge_revision(
                &request.root,
                &graph,
                &walked,
                config,
                &semantic,
                &past[index],
                &revision.texts,
            );
            for mut finding in judged.findings {
                finding.configurations = vec![name.clone()];
                past_findings[index].push(finding);
            }
            for key in judged.unaffected {
                past_unaffected[index].entry(key).or_insert(true);
            }
            let judged = judge::packages(&graph, &walked, config, &known, &past_changes[index]);
            for mut finding in judged.findings {
                finding.configurations = vec![name.clone()];
                past_findings[index].push(finding);
            }
            for key in judged.unaffected {
                past_unaffected_packages[index].entry(key).or_insert(true);
            }
        }
        if !request.revisions.is_empty() {
            phases.push(("revisions", lap.elapsed().as_millis()));
        }
        report.summaries.push(summary);
        report.phases.extend(
            phases
                .into_iter()
                .map(|(phase, ms)| (name.clone(), phase, ms)),
        );
    }
    if let Some(files) = &files {
        // What is not code.
        let scripts: Vec<&Listed> = cone.values().collect();
        let text_of = |path: &str| {
            rustlyn_ide::document::read_source(Path::new(&request.root).join(path)).ok()
        };
        findings.extend(judge::watched(config, files, &[]));
        findings.extend(judge::assets(&request.root, files, &scripts));
        findings.extend(judge::mentions(config, files, &text_of));
        findings.extend(package_changes.iter().flat_map(broken_packages));
    }
    // A member one configuration found and another did not is found.
    let left = |findings: &[Finding], unaffected: &BTreeMap<(String, String), bool>| {
        unaffected
            .keys()
            .filter(|(path, name)| {
                !findings
                    .iter()
                    .any(|finding| &finding.path == path && &finding.name == name)
            })
            .count()
    };
    report.findings = judge::merge(findings);
    report.unaffected = left(&report.findings, &unaffected);
    report.unaffected_packages = left(&report.findings, &unaffected_packages);
    let scripts: Vec<&Listed> = cone.values().collect();
    for (index, revision) in request.revisions.iter().enumerate() {
        let mut findings = std::mem::take(&mut past_findings[index]);
        findings.extend(judge::watched(config, &past[index], &revision.others));
        findings.extend(judge::mentions(config, &past[index], &|path| {
            revision.texts.get(path).cloned()
        }));
        findings.extend(broken_packages(&past_changes[index]));
        findings.extend(judge::assets_of(
            &past[index],
            &scripts,
            &|path| revision.texts.get(path).cloned(),
            &request.root,
        ));
        let findings = judge::merge(findings);
        report.revisions.push(Judgement {
            id: revision.id.clone(),
            title: revision.title.clone(),
            unaffected: left(&findings, &past_unaffected[index]),
            unaffected_packages: left(&findings, &past_unaffected_packages[index]),
            findings,
        });
    }
    report.packages = PackageSection {
        provided: provided
            .into_iter()
            .map(|(sink, packages)| {
                (
                    config.sinks[sink].name.clone(),
                    packages.into_iter().collect(),
                )
            })
            .collect(),
        used: {
            let mut used: Vec<UsedPackage> = used
                .into_iter()
                .map(|(name, members)| UsedPackage {
                    name,
                    members: members.len(),
                })
                .collect();
            used.sort_by(|a, b| b.members.cmp(&a.members).then_with(|| a.name.cmp(&b.name)));
            used
        },
    };
    report.cone = cone.into_values().collect();
    report.hubs = hubs.into_values().collect();
    report.hubs.sort_by_key(|hub| std::cmp::Reverse(hub.users));
    Ok(report)
}

/// A package file that changed and is not JSON, as a finding: nothing can
/// be said of it by package, so it is reported whole rather than as
/// nothing.
fn broken_packages(changes: &packages::Changes) -> Vec<Finding> {
    changes
        .broken
        .iter()
        .map(|path| Finding {
            kind: FindingKind::Watch,
            path: path.clone(),
            line: 0,
            name: "packages".to_owned(),
            role: None,
            certain: true,
            lines: Vec::new(),
            chain: Vec::new(),
            sinks: Vec::new(),
            configurations: Vec::new(),
            count: 0,
        })
        .collect()
}
