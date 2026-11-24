//! `rustlyn-graph`: where a value comes from, from a terminal.
//!
//! ```text
//! rustlyn-graph ROOT File.cs:line:column [--json] [--depth N] [--limit N] [--no-calls]
//!               [--arguments] [--expect "Value <- Code <- Source"]…
//! rustlyn-graph ROOT Folder/ [--calls] [-v]
//! ```
//!
//! At the position: any value — a field, property, local, parameter,
//! method, enum value or component. Prints the graph as a tree from the
//! value to its sources (← data, ⇠ network, ? condition) and a "sources:"
//! line. `--expect` is a chain of node titles (substrings); the exit code
//! is 1 when one is missing. With a folder: a survey — the graph of every
//! field and property, and where it loses the trail.

use std::path::Path;
use std::sync::Arc;

use rustlyn_analyzer::blast::{project, setup};
use rustlyn_analyzer::fail::{line_start_utf16, split_target};
use rustlyn_analyzer::value::headless;
use rustlyn_analyzer::value::{Compiler, English, IndexSymbols, Project, Projects, Reach};

const USAGE: &str = "rustlyn-graph ROOT File.cs:line:column [--json] [--depth N] [--limit N] [--no-calls] [--arguments] [--expect CHAIN]…
rustlyn-graph ROOT Folder/ [--calls] [-v]

Where a C# value comes from: the places that write it and what that is made
of, down to literals, constants, configs, the inspector, time, input.";

fn main() {
    std::process::exit(match run() {
        Ok(code) => code,
        Err(text) => {
            eprintln!("rustlyn-graph: {text}");
            2
        }
    });
}

fn run() -> Result<i32, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() || args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{USAGE}");
        return Ok(0);
    }
    let mut reach = Reach::default();
    let (mut json, mut verbose, mut survey_calls) = (false, false, false);
    let mut expect = Vec::new();
    let mut positional = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let value = |i: usize| args.get(i + 1).cloned().ok_or("a value is missing");
        match args[i].as_str() {
            "--json" => json = true,
            "-v" => verbose = true,
            "--calls" => survey_calls = true,
            "--no-calls" => reach.calls = false,
            "--arguments" => reach.arguments = true,
            "--depth" => {
                reach.depth = value(i)?.parse().map_err(|_| "--depth N")?;
                i += 1;
            }
            "--limit" => {
                reach.nodes = value(i)?.parse().map_err(|_| "--limit N")?;
                i += 1;
            }
            "--expect" => {
                expect.push(value(i)?);
                i += 1;
            }
            other => positional.push(other.to_owned()),
        }
        i += 1;
    }
    let [root, target] = positional.as_slice() else {
        return Err(USAGE.to_owned());
    };
    let root = setup::canonical_root(root);
    let session = Arc::new(project::compiled(
        &root,
        setup::cache_dir("rustlyn-graph", &root),
    )?);
    let mut home = Project::new(root.clone());
    home.symbols = Some(Arc::new(IndexSymbols::new(session.index())));
    home.compiler = Some(session.clone() as Arc<dyn Compiler>);
    let projects = Projects {
        home: Some(root.clone()),
        list: vec![home],
    };

    let (file, line, column) = split_target(target);
    let path = if Path::new(&file).is_absolute() {
        file
    } else {
        Path::new(&root).join(&file).to_string_lossy().into_owned()
    };
    if Path::new(&path).is_dir() {
        reach.calls = survey_calls;
        reach.arguments = true;
        let folder = setup::canonical_root(&path);
        return Ok(headless::print_survey(
            &folder,
            &projects,
            reach,
            verbose,
            &mut |l| println!("{l}"),
            &mut |l| eprintln!("{l}"),
        ));
    }
    let (Some(line), Some(column)) = (line, column) else {
        return Err("a position File.cs:line:column".to_owned());
    };
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}"))?;
    let offset = line_start_utf16(&text, line) as usize + column.saturating_sub(1);
    let compiler: &dyn Compiler = &*session;
    compiler.open(&path);
    let found = compiler
        .definition(&path, offset, None)
        .into_iter()
        .next()
        .ok_or("the compiler does not know the name there")?;
    let Some(graph) = headless::graph_of(&found, &projects, reach) else {
        return Err(format!("{} is not a value", found.name));
    };
    if json {
        println!("{}", headless::json(&graph, &English));
    } else {
        println!("{}", headless::tree(&graph, &English));
        println!("sources: {}", headless::sources_summary(&graph, &English));
    }
    let mut code = 0;
    for chain in &expect {
        let titles: Vec<String> = chain.split("<-").map(|t| t.trim().to_owned()).collect();
        if graph.has_path(&titles, &English) {
            println!("✓ {chain}");
        } else {
            println!("✗ {chain}");
            code = 1;
        }
    }
    Ok(code)
}
