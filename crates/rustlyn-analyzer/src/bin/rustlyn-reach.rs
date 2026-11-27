//! `rustlyn-reach`: does a change lead to a given set of APIs, from a
//! terminal, scripts and agents.
//!
//! ```text
//! rustlyn-reach [ROOT] --config FILE [--diff FILE|-] [--base REV] [--merge-base REV]
//!               [--staged] [--possible] [--json] [--no-cache] [--timings]
//! rustlyn-reach [ROOT] --config FILE --commits RANGE [--commit REV] [--possible] [--json]
//! rustlyn-reach [ROOT] --config FILE --cone [--users] [--json]
//! ```
//!
//! The configuration names the sinks (see `reach::config`); without
//! `--config` it is `ROOT/.rustlyn/reach.json`. Without `--diff`, the change
//! is the working copy against `--base` (`HEAD`) from git, or against the
//! commit the branch left `--merge-base REV` at. `--commits RANGE` judges
//! each commit of a git range instead (first parents only, so a merge is its
//! whole branch), against the cone of the code as it is now; it can be given
//! more than once, as can `--commit REV`, which judges that one commit
//! against its first parent. `--cone` prints
//! the cone itself instead of judging a change: every member that leads to a
//! sink, with its way there. Exit code: 0 — the change leads to no sink,
//! 3 — it does, 2 — an error.

use std::io::Read;

use rustlyn_analyzer::blast::setup;
use rustlyn_analyzer::cli;
use rustlyn_analyzer::reach::{Config, Request, analyze, git};

const USAGE: &str = "rustlyn-reach [ROOT] --config FILE [--diff FILE|-] [--base REV] [--merge-base REV] [--staged] [--possible] [--json] [--no-cache] [--timings]
rustlyn-reach [ROOT] --config FILE --commits RANGE [--commit REV] [--possible] [--json]
rustlyn-reach [ROOT] --config FILE --cone [--users] [--json]

Does a C# change lead to the APIs the configuration names (its sinks): the
changed members on a path to them, each with its way there through calls,
fields and ECS components. Without --diff, the git working copy against
--base (HEAD); --merge-base REV takes the commit the branch left REV at.
--commits RANGE judges each commit of a git range (first parents: a merge is
its whole branch) against the cone of the code as it is now; --commit REV
judges that one commit (against its first parent). --possible adds
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
    let mut single: Vec<String> = Vec::new();
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
            "--commit" => single.push(value(&mut args, "--commit")?),
            "--staged" => staged = true,
            "--cone" => cone = true,
            "--users" => users = true,
            "--possible" => possible = true,
            "--json" => json = true,
            "--no-cache" => cache = false,
            "--timings" => timings = true,
            "-h" | "--help" => {
                cli::say(USAGE);
                return Ok(0);
            }
            other if other.starts_with('-') => {
                return Err(format!("unknown flag {other}\n{USAGE}"));
            }
            other => root = Some(other.to_owned()),
        }
    }
    let root = setup::canonical_root(&root.unwrap_or_else(|| ".".to_owned()));
    setup::existing_root(&root)?;
    let config_path = config.unwrap_or_else(|| format!("{root}/.rustlyn/reach.json"));
    let config = std::fs::read_to_string(&config_path)
        .map_err(|e| format!("{config_path}: {e}"))
        .and_then(|text| Config::parse(&text).map_err(|e| format!("{config_path}: {e}")))?;
    if let Some(branch) = &merge_base {
        let found = setup::git(&root, &["merge-base", setup::revision(branch)?, "HEAD"])?;
        base = Some(found.trim().to_owned());
    }
    let mut past = Vec::new();
    for range in &commits {
        past.extend(git::revisions(&root, range, &config, &|done, total| {
            eprintln!("rustlyn-reach: reading commit {done}/{total}");
        })?);
    }
    for commit in &single {
        past.push(git::revision(&root, commit, &config)?);
    }
    let patch = if cone || !(commits.is_empty() && single.is_empty()) {
        None
    } else {
        Some(match diff.as_deref() {
            Some("-") => {
                let mut bytes = Vec::new();
                std::io::stdin()
                    .read_to_end(&mut bytes)
                    .map_err(|e| e.to_string())?;
                rustlyn_ide::document::decode_lines(&bytes)
            }
            Some(path) => {
                let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
                rustlyn_ide::document::decode_lines(&bytes)
            }
            None => setup::git_patch(&root, base.as_deref(), staged)?,
        })
    };
    if let Some(patch) = &patch {
        setup::valid_patch(patch)?;
    }
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
        cli::say(&report.json_text(cone));
    } else if cone {
        cli::say(&format!(
            "{}\n{}",
            report.headline(),
            report.cone_text(users)
        ));
    } else {
        cli::say(&report.text(possible));
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
