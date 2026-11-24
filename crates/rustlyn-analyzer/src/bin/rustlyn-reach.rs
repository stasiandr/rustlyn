//! `rustlyn-reach`: does a change lead to a given set of APIs, from a
//! terminal, scripts and agents.
//!
//! ```text
//! rustlyn-reach [ROOT] --config FILE [--diff FILE|-] [--base REV] [--merge-base REV]
//!               [--staged] [--possible] [--json] [--no-cache] [--timings]
//! rustlyn-reach [ROOT] --config FILE --commits RANGE [--possible] [--json]
//! rustlyn-reach [ROOT] --config FILE --cone [--users] [--json]
//! ```
//!
//! The configuration names the sinks (see `reach::config`); without
//! `--config` it is `ROOT/.rustlyn/reach.json`. Without `--diff`, the change
//! is the working copy against `--base` (`HEAD`) from git, or against the
//! commit the branch left `--merge-base REV` at. `--commits RANGE` judges
//! each commit of a git range instead (first parents only, so a merge is its
//! whole branch), against the cone of the code as it is now; it can be given
//! more than once. `--cone` prints
//! the cone itself instead of judging a change: every member that leads to a
//! sink, with its way there. Exit code: 0 — the change leads to no sink,
//! 3 — it does, 2 — an error.

use std::io::Read;

use std::collections::HashMap;

use rustlyn_analyzer::blast::diff::{Status, parse};
use rustlyn_analyzer::blast::setup;
use rustlyn_analyzer::reach::{Config, Request, Revision, analyze};
use rustlyn_ide::formats::json::Format;

const USAGE: &str = "rustlyn-reach [ROOT] --config FILE [--diff FILE|-] [--base REV] [--merge-base REV] [--staged] [--possible] [--json] [--no-cache] [--timings]
rustlyn-reach [ROOT] --config FILE --commits RANGE [--possible] [--json]
rustlyn-reach [ROOT] --config FILE --cone [--users] [--json]

Does a C# change lead to the APIs the configuration names (its sinks): the
changed members on a path to them, each with its way there through calls,
fields and ECS components. Without --diff, the git working copy against
--base (HEAD); --merge-base REV takes the commit the branch left REV at.
--commits RANGE judges each commit of a git range (first parents: a merge is
its whole branch) against the cone of the code as it is now. --possible adds
members of the cone changed elsewhere than on the lines that lead on. --cone
prints the cone instead of judging a change; --users adds the members that
only use it. Without --config, ROOT/.rustlyn/reach.json.
Exit code: 0 leads to no sink, 3 leads to one, 2 error.";

fn main() {
    std::process::exit(match run() {
        Ok(code) => code,
        Err(text) => {
            eprintln!("rustlyn-reach: {text}");
            2
        }
    });
}

fn run() -> Result<i32, String> {
    // A panic inside the compiler is a file it did not answer about, counted
    // in the report; the backtrace is for debugging only.
    if std::env::var_os("RUSTLYN_REACH_DEBUG").is_none() {
        std::panic::set_hook(Box::new(|_| {}));
    }
    let mut args = std::env::args().skip(1);
    let mut root: Option<String> = None;
    let mut config: Option<String> = None;
    let mut diff: Option<String> = None;
    let mut base: Option<String> = None;
    let mut merge_base: Option<String> = None;
    let mut commits: Vec<String> = Vec::new();
    let mut staged = false;
    let mut cone = false;
    let mut users = false;
    let mut possible = false;
    let mut json = false;
    let mut cache = true;
    let mut timings = false;
    let value = |args: &mut dyn Iterator<Item = String>, flag: &str| {
        args.next()
            .ok_or_else(|| format!("{flag}: a value is required"))
    };
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--config" => config = Some(value(&mut args, "--config")?),
            "--diff" => diff = Some(value(&mut args, "--diff")?),
            "--base" => base = Some(value(&mut args, "--base")?),
            "--merge-base" => merge_base = Some(value(&mut args, "--merge-base")?),
            "--commits" => commits.push(value(&mut args, "--commits")?),
            "--staged" => staged = true,
            "--cone" => cone = true,
            "--users" => users = true,
            "--possible" => possible = true,
            "--json" => json = true,
            "--no-cache" => cache = false,
            "--timings" => timings = true,
            "-h" | "--help" => {
                println!("{USAGE}");
                return Ok(0);
            }
            other if other.starts_with('-') => {
                return Err(format!("unknown flag {other}\n{USAGE}"));
            }
            other => root = Some(other.to_owned()),
        }
    }
    let root = setup::canonical_root(&root.unwrap_or_else(|| ".".to_owned()));
    let config_path = config.unwrap_or_else(|| format!("{root}/.rustlyn/reach.json"));
    let config = std::fs::read_to_string(&config_path)
        .map_err(|e| format!("{config_path}: {e}"))
        .and_then(|text| Config::parse(&text).map_err(|e| format!("{config_path}: {e}")))?;
    if let Some(branch) = &merge_base {
        let found = setup::git(&root, &["merge-base", branch, "HEAD"])?;
        base = Some(found.trim().to_owned());
    }
    let mut past = Vec::new();
    for range in &commits {
        past.extend(revisions(&root, range)?);
    }
    let patch = if cone || !commits.is_empty() {
        None
    } else {
        Some(match diff.as_deref() {
            Some("-") => {
                let mut text = String::new();
                std::io::stdin()
                    .read_to_string(&mut text)
                    .map_err(|e| e.to_string())?;
                text
            }
            Some(path) => std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?,
            None => setup::git_patch(&root, base.as_deref(), staged)?,
        })
    };
    let request = Request {
        cache: cache
            .then(|| setup::cache_dir("rustlyn-reach", &root))
            .flatten(),
        root,
        patch,
        revisions: past,
    };
    let report = analyze(&request, &config)?;
    if json {
        println!("{}", report.json(cone).to_text_with(Format::PRETTY_SORTED));
    } else if cone {
        println!("{}\n{}", report.headline(), report.cone_text(users));
    } else {
        println!("{}", report.text(possible));
    }
    if timings {
        let all: Vec<String> = report
            .phases
            .iter()
            .map(|(configuration, phase, ms)| {
                if configuration.is_empty() {
                    format!("{phase} {ms} ms")
                } else {
                    format!("{configuration} {phase} {ms} ms")
                }
            })
            .collect();
        eprintln!("rustlyn-reach: {}", all.join(", "));
    }
    Ok(if report.affects() { 3 } else { 0 })
}

/// The commits of a git range as changes to judge, oldest first. First
/// parents only: a merge commit stands for the whole branch it merged.
///
/// Sources and assets are diffed; everything else — scenes and prefabs of
/// hundreds of megabytes among it — only by name, which is what a watch
/// needs.
fn revisions(root: &str, range: &str) -> Result<Vec<Revision>, String> {
    let log = setup::git(
        root,
        &[
            "log",
            "--first-parent",
            "--reverse",
            "--format=%H%x09%s",
            range,
        ],
    )?;
    let commits: Vec<(&str, &str)> = log
        .lines()
        .filter_map(|line| line.split_once('\t'))
        .collect();
    let mut blobs = Blobs::open(root)?;
    let mut revisions = Vec::new();
    for (index, (id, title)) in commits.iter().enumerate() {
        eprintln!(
            "rustlyn-reach: reading commit {}/{}",
            index + 1,
            commits.len()
        );
        // The first commit of a repository has nothing to be compared with.
        let parent = format!("{id}^1");
        if setup::git(root, &["rev-parse", "--verify", "--quiet", &parent]).is_err() {
            continue;
        }
        let mut patch = setup::git(
            root,
            &[
                "diff",
                "--relative",
                "--no-color",
                "--no-ext-diff",
                &parent,
                id,
                "--",
                "*.cs",
                "*.asset",
            ],
        )?;
        let mut texts: HashMap<String, String> = HashMap::new();
        for file in parse(&patch) {
            if file.status != Status::Deleted
                && let Some(text) = blobs.text(&format!("{id}:./{}", file.path))
            {
                texts.insert(file.path, text);
            }
        }
        // The rest by name: a patch with no lines.
        let names = setup::git(
            root,
            &[
                "diff",
                "--relative",
                "--name-only",
                "--no-renames",
                &parent,
                id,
            ],
        )?;
        for name in names.lines() {
            if !name.is_empty() && !name.ends_with(".cs") && !name.ends_with(".asset") {
                patch += &format!("diff --git a/{name} b/{name}\n--- a/{name}\n+++ b/{name}\n");
            }
        }
        revisions.push(Revision {
            id: (*id).to_owned(),
            title: (*title).to_owned(),
            patch,
            texts,
        });
    }
    Ok(revisions)
}

/// The contents of git objects, from one `git cat-file --batch` kept
/// running: a branch merged into a large repository changes thousands of
/// files, and a process for each is minutes.
struct Blobs {
    child: std::process::Child,
    input: std::process::ChildStdin,
    output: std::io::BufReader<std::process::ChildStdout>,
}

impl Blobs {
    fn open(root: &str) -> Result<Self, String> {
        let mut child = std::process::Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["cat-file", "--batch"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .map_err(|e| format!("git cat-file: {e}"))?;
        let input = child.stdin.take().ok_or("git cat-file: no input")?;
        let output = child.stdout.take().ok_or("git cat-file: no output")?;
        Ok(Self {
            child,
            input,
            output: std::io::BufReader::new(output),
        })
    }

    /// The text of the object `name` (`rev:path`); `None` when there is no
    /// such object or it is not text.
    fn text(&mut self, name: &str) -> Option<String> {
        use std::io::{BufRead, Write};
        writeln!(self.input, "{name}").ok()?;
        self.input.flush().ok()?;
        let mut header = String::new();
        self.output.read_line(&mut header).ok()?;
        // `<object> <type> <size>`, or `<name> missing`.
        let size: usize = header.split_whitespace().nth(2)?.parse().ok()?;
        let mut bytes = vec![0; size + 1];
        self.output.read_exact(&mut bytes).ok()?;
        bytes.pop();
        String::from_utf8(bytes).ok()
    }
}

impl Drop for Blobs {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
