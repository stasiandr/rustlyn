//! Risks the compiler knows:
//!
//! * failability — where and under what conditions a member fails, and
//!   whether that can happen (`Always`, or `Possible` for some values);
//! * compile errors in changed and reached code — the change broke the
//!   build;
//! * the thread analyzers (`RLN1001`–`RLN1003`): a field raced on without a
//!   lock, Unity's API off its main thread, a shared variable in
//!   `Parallel`.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustlyn_ide::Session;
use rustlyn_ide::outline::DeclarationKind;
use rustlyn_ide::semantic::{Failure, Verdict};
use rustlyn_ide::session::FileDiagnostic;

use super::ask::{absolute, ask};
use super::changes::line_starts;
use super::risk::{Certainty, Context, Level, Reason, Risk, RiskModel};
use super::walk::{Node, relative_to};

/// Failability is not asked deeper than this: further from the change its
/// answer is about the old code, not about what the change did.
const FAILABILITY_DEPTH: usize = 1;
/// Members asked for failability, per report.
const FAILABILITY_MEMBERS: usize = 40;
/// Failures per member in the report.
const FAILURES: usize = 4;
/// The prefix of the thread analyzers' ids.
const THREADS: &str = "RLN1";

/// A diagnostic: line from zero, severity, code, message.
type Found = (usize, u8, String, String);

/// The compiler's reasons for risk, as a [`RiskModel`].
#[derive(Debug)]
pub struct CompilerRisks<'a> {
    root: &'a str,
    session: &'a Session,
    /// A file's diagnostics, by relative path.
    diagnostics: Mutex<HashMap<String, Vec<Found>>>,
    /// Failures of the nodes asked about, by node index.
    failures: Mutex<HashMap<usize, Vec<Failure>>>,
    /// Failures below the highest level already shown: place and exception.
    /// The same place from a hundred callers (an `EndOfStreamException`
    /// reading the network) is one risk at the first, not a hundred.
    shown: Mutex<HashSet<(String, usize, String, Level)>>,
}

impl<'a> CompilerRisks<'a> {
    #[must_use]
    pub fn new(root: &'a str, session: &'a Session) -> Self {
        CompilerRisks {
            root,
            session,
            diagnostics: Mutex::new(HashMap::new()),
            failures: Mutex::new(HashMap::new()),
            shown: Mutex::new(HashSet::new()),
        }
    }

    fn absolute(&self, path: &str) -> String {
        Path::new(self.root)
            .join(path)
            .to_string_lossy()
            .into_owned()
    }

    /// Errors and thread findings in a file. With `old`, only those that
    /// were not in the text before the change.
    fn diagnostics_of(&self, path: &str, old: Option<&str>) -> Vec<Found> {
        let Ok(mut cache) = self.diagnostics.lock() else {
            return Vec::new();
        };
        cache
            .entry(path.to_owned())
            .or_insert_with(|| {
                let absolute = self.absolute(path);
                let session = self.session;
                let _ = ask(|| session.open(&absolute));
                let Ok(text) = std::fs::read_to_string(&absolute) else {
                    return Vec::new();
                };
                let keep = |d: &FileDiagnostic| d.severity == 3 || d.code.starts_with(THREADS);
                let Some(found) = ask(|| session.diagnostics(&absolute, None)) else {
                    return Vec::new();
                };
                // What was there before the change is not its doing: by
                // count of (code, message).
                let mut before: HashMap<(String, String), usize> = HashMap::new();
                if let Some(old) = old
                    && let Some(was) = ask(|| session.diagnostics(&absolute, Some(old)))
                {
                    for d in was.items.iter().filter(|d| keep(d)) {
                        *before
                            .entry((d.code.clone(), d.message.clone()))
                            .or_default() += 1;
                    }
                }
                let starts = utf16_line_starts(&text);
                found
                    .items
                    .into_iter()
                    .filter(|d| keep(d))
                    .filter(
                        |d| match before.get_mut(&(d.code.clone(), d.message.clone())) {
                            Some(count) if *count > 0 => {
                                *count -= 1;
                                false
                            }
                            _ => true,
                        },
                    )
                    .map(|d| {
                        (
                            starts
                                .partition_point(|&s| s <= d.start as usize)
                                .saturating_sub(1),
                            d.severity,
                            d.code,
                            d.message,
                        )
                    })
                    .collect()
            })
            .clone()
    }

    fn ask_failability(&self, node: &Node) -> Vec<Failure> {
        let absolute = self.absolute(&node.member.path);
        let session = self.session;
        let _ = ask(|| session.open(&absolute));
        let offset = node.member.utf16_offset as u32;
        ask(|| session.failability(&absolute, offset))
            .map(|f| f.failures)
            .unwrap_or_default()
    }
}

impl RiskModel for CompilerRisks<'_> {
    /// Failability takes about 0.2 s a member, seconds on large methods: for
    /// the changed members (first in the list) and the nearest, up to the
    /// limit, on several threads.
    fn prepare(&self, context: &Context<'_>) {
        let chosen: Vec<usize> = context
            .impact
            .nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.depth <= FAILABILITY_DEPTH && callable(n.member.kind))
            .map(|(i, _)| i)
            .take(FAILABILITY_MEMBERS)
            .collect();
        let next = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..threads(chosen.len()) {
                scope.spawn(|| {
                    while let Some(&index) = chosen.get(next.fetch_add(1, Ordering::Relaxed)) {
                        let found = self.ask_failability(&context.impact.nodes[index]);
                        if let Ok(mut all) = self.failures.lock() {
                            all.insert(index, found);
                        }
                    }
                });
            }
        });
    }

    fn risks(&self, node: &Node, context: &Context<'_>) -> Vec<Risk> {
        let member = &node.member;
        let mut risks = Vec::new();
        // Errors and races the change introduced. In a changed file —
        // everything new against the text before the change; elsewhere —
        // only on the lines where the node calls or reads what was reached,
        // with its name in the message: the rest was there without the
        // change.
        let old = context.old_texts.get(&member.path);
        if old.is_some() || node.depth <= 1 {
            let names: Vec<&str> = node
                .edges
                .iter()
                .filter_map(|e| context.impact.nodes.get(e.from))
                .map(|n| n.member.short_name())
                .collect();
            let edge_lines: Vec<usize> = node
                .edges
                .iter()
                .filter(|e| e.path == member.path)
                .map(|e| e.line)
                .collect();
            for (line, severity, code, message) in
                self.diagnostics_of(&member.path, old.map(String::as_str))
            {
                if !member.lines.contains(&line) || inner_node_at(context, node, line) {
                    continue;
                }
                if old.is_none()
                    && !(edge_lines.contains(&line) && names.iter().any(|n| message.contains(n)))
                {
                    continue;
                }
                let reason = if code.starts_with(THREADS) {
                    Reason::Threads { code, message }
                } else if severity == 3 {
                    Reason::CompileError { code, message }
                } else {
                    continue;
                };
                risks.push(Risk::new(Level::High, reason).at(member.path.clone(), line));
            }
        }
        let index = context
            .impact
            .nodes
            .iter()
            .position(|n| std::ptr::eq(n, node));
        let found =
            index.and_then(|i| self.failures.lock().ok().and_then(|mut all| all.remove(&i)));
        if let Some(found) = found {
            let mut failures: Vec<Failure> = found
                .into_iter()
                .filter(|f| f.verdict != Verdict::Never)
                .collect();
            failures.sort_by_key(|f| verdict_rank(f.verdict));
            for failure in failures.into_iter().take(FAILURES) {
                let risk = failure_risk(self.root, &failure);
                if risk.level < Level::High
                    && let Some((path, line)) = &risk.at
                    && let Ok(mut shown) = self.shown.lock()
                    && !shown.insert((path.clone(), *line, failure.exception.clone(), risk.level))
                {
                    continue;
                }
                risks.push(risk);
            }
        }
        risks
    }
}

const fn callable(kind: DeclarationKind) -> bool {
    matches!(
        kind,
        DeclarationKind::Method
            | DeclarationKind::Constructor
            | DeclarationKind::Property
            | DeclarationKind::Operator
    )
}

/// Threads for `jobs` questions to the compiler.
pub(crate) fn threads(jobs: usize) -> usize {
    std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .clamp(1, 8)
        .min(jobs.max(1))
}

/// A line inside another node nested in this one (a method in a type): its
/// diagnostic is that node's.
fn inner_node_at(context: &Context<'_>, node: &Node, line: usize) -> bool {
    context.impact.nodes.iter().any(|other| {
        other.member.path == node.member.path
            && other.member.key != node.member.key
            && other.member.lines.contains(&line)
            && other.member.lines.len() < node.member.lines.len()
    })
}

const fn verdict_rank(verdict: Verdict) -> u8 {
    match verdict {
        Verdict::Always => 0,
        Verdict::Possible => 1,
        Verdict::Unknown => 2,
        Verdict::Never => 3,
    }
}

fn failure_risk(root: &str, failure: &Failure) -> Risk {
    let (level, certainty) = match failure.verdict {
        Verdict::Always => (Level::High, Certainty::Always),
        Verdict::Possible => (Level::Medium, Certainty::Possible),
        _ => (Level::Low, Certainty::Unknown),
    };
    let reason = Reason::Failability {
        certainty,
        exception: failure.exception.clone(),
        message: failure.message.clone(),
        conditions: failure.conditions.iter().map(|c| c.text.clone()).collect(),
        via: failure.chain.last().map(|step| step.callee.clone()),
    };
    let path = relative_to(root, &absolute(root, &failure.path));
    let line = std::fs::read_to_string(Path::new(root).join(&path))
        .ok()
        .map_or(0, |t| {
            let starts = line_starts(&t);
            starts
                .partition_point(|&s| s <= failure.span.start() as usize)
                .saturating_sub(1)
        });
    Risk::new(level, reason).at(path, line)
}

/// Line starts in UTF-16, the units diagnostics come in.
fn utf16_line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    let mut at = 0usize;
    for c in text.chars() {
        at += c.len_utf16();
        if c == '\n' {
            starts.push(at);
        }
    }
    starts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::Extensions;
    use crate::blast::report::{Report, Request, analyze};
    use crate::blast::testing::{Project, patch};

    const SHOP: &str = "namespace Game {
    public class Shop {
        int gold;
        public void Pay(int amount) {
            gold -= amount;
        }
        public void Buy() { Pay(10); }
    }
}
";

    fn report_with(project: &Project, request: &Request) -> Report {
        let session = project.session();
        let model = CompilerRisks::new(&request.root, &session);
        let extensions = Extensions {
            risks: vec![&model],
            ..Extensions::default()
        };
        analyze(request, &session, &extensions)
    }

    fn report_of(new: &str) -> Report {
        let project = Project::new("compiler-risks", &[("Shop.cs", new)]);
        let request = Request::new(project.root(), patch("Shop.cs", SHOP, new));
        report_with(&project, &request)
    }

    const THROW: &str = "            if (amount > 5) throw new System.ArgumentException(\"too much\");\n            gold -= amount;";

    #[test]
    fn a_failure_the_change_added() {
        let new = SHOP.replace("            gold -= amount;", THROW);
        let report = report_of(&new);
        let pay = report.impact.index_of("Game.Shop.Pay(int)").expect("Pay");
        let risk = report.risks[pay]
            .iter()
            .find(|r| r.code() == "failability")
            .expect("failability");
        let text = risk.reason.to_string();
        assert!(
            text.contains("ArgumentException") && text.contains("too much"),
            "{risk:?}"
        );
        // Buy calls Pay(10): 10 > 5, so it always fails.
        let buy = report.impact.index_of("Game.Shop.Buy()").expect("Buy");
        let risk = report.risks[buy]
            .iter()
            .find(|r| r.code() == "failability")
            .expect("failability of Buy");
        assert_eq!(risk.level, Level::High, "{risk:?}");
    }

    #[test]
    fn one_failure_place_shown_once_for_many_callers() {
        let new = SHOP.replace("            gold -= amount;", THROW).replace(
            "        public void Buy() { Pay(10); }",
            "        public void Buy(int n) { Pay(n); }\n        public void Sell(int n) { Pay(n); }",
        );
        let report = report_of(&new);
        let shown = report
            .risks
            .iter()
            .flatten()
            .filter(|r| {
                r.code() == "failability" && r.reason.to_string().contains("ArgumentException")
            })
            .count();
        assert_eq!(shown, 1, "{:?}", report.risks);
    }

    #[test]
    fn a_compile_error_in_the_change() {
        let new = SHOP.replace("gold -= amount;", "gold -= amaunt;");
        let report = report_of(&new);
        let pay = report.impact.index_of("Game.Shop.Pay(int)").expect("Pay");
        assert!(
            report.risks[pay].iter().any(|r| matches!(
                &r.reason,
                Reason::CompileError { code, .. } if code == "CS0103"
            )),
            "{:?}",
            report.risks[pay]
        );
    }

    const STUBS: &str = "namespace System { public delegate void Action(); }
namespace System.Threading.Tasks { public class Task { public static Task Run(System.Action a) => null; } }
namespace UnityEngine {
  public class Object { }
  public class Component : Object { }
  public class Behaviour : Component { }
  public class MonoBehaviour : Behaviour { }
  public static class Debug { public static void Log(object o) { } }
}
";
    const LOADER: &str = "using System.Threading.Tasks;
class Loader : UnityEngine.MonoBehaviour {
  int progress;
  void Start() { }
  void Update() { UnityEngine.Debug.Log(progress); }
}
";

    #[test]
    fn a_race_the_change_added() {
        let new = LOADER.replace(
            "void Start() { }",
            "void Start() { Task.Run(() => { progress = 5; }); }",
        );
        let project = Project::new("threads", &[("Loader.cs", &new), ("Stubs.cs", STUBS)]);
        let request = Request::new(project.root(), patch("Loader.cs", LOADER, &new));
        let report = report_with(&project, &request);
        // Update reads a field the change now writes from another thread.
        let update = report
            .impact
            .index_of("Loader.Update()")
            .expect("Update reached");
        assert!(
            report.risks[update].iter().any(|r| matches!(
                &r.reason,
                Reason::Threads { code, .. } if code == "RLN1001"
            )),
            "{}",
            report.text()
        );
    }

    #[test]
    fn a_broken_call_in_another_file_and_old_errors_do_not_count() {
        let a = "class A {\n    public void F() { }\n    void Old() { Missing(); }\n}\n";
        let b = "class B {\n    A a;\n    void G() { a.F(); }\n    void H() { Gone(); }\n}\n";
        let new = a.replace("public void F() { }", "public void F(int x) { }");
        let project = Project::new("broken-call", &[("A.cs", &new), ("B.cs", b)]);
        let request = Request::new(project.root(), patch("A.cs", a, &new));
        let report = report_with(&project, &request);
        let g = report.impact.index_of("B.G()").expect("G calls F");
        assert!(
            report.risks[g].iter().any(|r| r.code() == "compile_error"),
            "{}",
            report.text()
        );
        let errors: Vec<&Risk> = report
            .risks
            .iter()
            .flatten()
            .filter(|r| r.code() == "compile_error")
            .collect();
        assert_eq!(
            errors.len(),
            1,
            "Missing and Gone were there before: {errors:?}"
        );
    }
}
