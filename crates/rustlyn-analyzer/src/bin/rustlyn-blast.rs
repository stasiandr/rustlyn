//! `rustlyn-blast`: the blast radius of a change, from a terminal, scripts
//! and agents.
//!
//! ```text
//! rustlyn-blast [ROOT] [--diff FILE|-] [--base REV] [--staged]
//!               [--depth N] [--nodes N] [--json] [--no-cache] [--timings]
//! rustlyn-blast --mcp
//! ```
//!
//! Without `--diff`, the working copy against `--base` (`HEAD`) from git,
//! new `.cs` files included. `--json` is the report for machines (schema
//! `version: 1`), the tree otherwise. `--mcp` serves the `blast_radius`
//! tool over the Model Context Protocol on stdin/stdout. `--timings`
//! prints the time of each phase to stderr. Exit code: 0 — no high risks,
//! 3 — there are, 2 — an error.

use std::io::Read;

use rustlyn_analyzer::blast::compiler_risks::CompilerRisks;
use rustlyn_analyzer::blast::{Extensions, Level, Limits, Request, analyze, mcp, project, setup};
use rustlyn_analyzer::cli;

const USAGE: &str = "rustlyn-blast [ROOT] [--diff FILE|-] [--base REV] [--staged] [--depth N] [--nodes N] [--json] [--no-cache] [--timings]
rustlyn-blast --mcp

The blast radius of a C# change: the members it changes, who calls and reads
them up the chain, the Unity scenes and prefabs using the scripts, and what
of it is risky. Without --diff, the git working copy against --base (HEAD).
Exit code: 0 no high risks, 3 high risks, 2 error.";

fn main() {
    std::process::exit(match run() {
        Ok(code) => code,
        Err(text) => {
            eprintln!("rustlyn-blast: {text}");
            2
        }
    });
}

fn run() -> Result<i32, String> {
    // A panic inside the compiler is caught and the question goes
    // unanswered; the backtrace goes to the terminal only for debugging.
    if std::env::var_os("RUSTLYN_BLAST_DEBUG").is_none() {
        static SEEN: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
        std::panic::set_hook(Box::new(|info| {
            let at = info
                .location()
                .map(|l| format!("{}:{}", l.file(), l.line()))
                .unwrap_or_default();
            let Ok(mut seen) = SEEN.lock() else {
                return;
            };
            if !seen.contains(&at) {
                eprintln!(
                    "rustlyn-blast: the compiler did not answer some questions (a panic at {at}; RUSTLYN_BLAST_DEBUG=1 for the backtrace)"
                );
                seen.push(at);
            }
        }));
    }
    let mut args = std::env::args().skip(1);
    let mut root: Option<String> = None;
    let mut diff: Option<String> = None;
    let mut base: Option<String> = None;
    let mut staged = false;
    let mut limits = Limits::default();
    let mut json = false;
    let mut cache = true;
    let mut serve = false;
    let mut timings = false;
    let value = |args: &mut dyn Iterator<Item = String>, flag: &str| {
        args.next()
            .ok_or_else(|| format!("{flag}: a value is required"))
    };
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--diff" => diff = Some(value(&mut args, "--diff")?),
            "--base" => base = Some(value(&mut args, "--base")?),
            "--staged" => staged = true,
            "--depth" => {
                limits.depth = value(&mut args, "--depth")?
                    .parse()
                    .map_err(|_| "--depth: a number")?;
            }
            "--nodes" => {
                limits.nodes = value(&mut args, "--nodes")?
                    .parse()
                    .map_err(|_| "--nodes: a number")?;
            }
            "--json" => json = true,
            "--no-cache" => cache = false,
            "--mcp" => serve = true,
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
    if serve {
        let mut server = mcp::Server::default();
        server.serve(std::io::stdin().lock(), std::io::stdout().lock());
        return Ok(0);
    }
    let root = setup::canonical_root(&root.unwrap_or_else(|| ".".to_owned()));
    setup::existing_root(&root)?;
    let mut notes = Vec::new();
    let patch = match diff.as_deref() {
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
        None => {
            let (patch, found) = setup::git_patch_noted(&root, base.as_deref(), staged)?;
            notes = found;
            patch
        }
    };
    setup::valid_patch(&patch)?;
    let mut phases = Vec::new();
    let folder = if cache {
        setup::cache_dir("rustlyn-blast", &root)
    } else {
        None
    };
    let session = project::compiled_timed(&root, folder, &mut phases)?;
    let mut request = Request::new(root, patch);
    request.limits = limits;
    request.notes = notes;
    let model = CompilerRisks::new(&request.root, &session);
    let extensions = Extensions {
        risks: vec![&model],
        ..Extensions::default()
    };
    let report = analyze(&request, &session, &extensions);
    cli::say(&if json {
        report.json_text()
    } else {
        report.text()
    });
    if timings {
        let all: Vec<String> = phases
            .iter()
            .chain(&report.phases)
            .map(|(n, ms)| format!("{n} {ms} ms"))
            .collect();
        eprintln!("rustlyn-blast: {}", all.join(", "));
    }
    Ok(if report.level() == Some(Level::High) {
        3
    } else {
        0
    })
}
