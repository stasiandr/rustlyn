//! Hot reload as the editor drives it, on a Unity project whose editor runs
//! the probe (`tools/unity/PilotProbe.cs`): started, the build loaded into
//! the editor, then each file given on standard input — one path per line,
//! after it was saved — answered and its patch sent to the editor.
//!
//! ```text
//! cargo run --release -p rustlyn-ide --example hot -- <project> <gend.dll> <minigen.dll> <PilotRuntime.dll> [--define "A;B"]
//! ```

use std::io::BufRead;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use rustlyn_ide::Session;
use rustlyn_ide::hot::{Answer, Tools};

fn sources(directory: &Path, found: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            sources(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "cs") {
            found.push(path);
        }
    }
}

/// A command to the probe, and the first line of its log after it that
/// starts with one of `answers`.
fn probe(project: &Path, command: &str, answers: &[&str], wait: Duration) -> Option<String> {
    let log = project.join("Temp/PilotProbe/log.txt");
    let at = std::fs::metadata(&log).map_or(0, |metadata| metadata.len()) as usize;
    let mut commands = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(project.join("Temp/PilotProbe/cmd.txt"))
        .ok()?;
    std::io::Write::write_all(&mut commands, format!("{command}\n").as_bytes()).ok()?;
    let end = Instant::now() + wait;
    while Instant::now() < end {
        let text = std::fs::read_to_string(&log).unwrap_or_default();
        for line in text.get(at..).unwrap_or_default().lines() {
            let said = line.split_once(' ').map(|x| x.1).unwrap_or_default();
            if answers.iter().any(|answer| said.starts_with(answer)) {
                return Some(said.to_string());
            }
        }
        std::thread::sleep(Duration::from_millis(30));
    }
    None
}

fn main() {
    let mut arguments: Vec<String> = std::env::args().skip(1).collect();
    let symbols: Vec<String> = match arguments.iter().position(|argument| argument == "--define") {
        Some(at) => {
            let defines = arguments.remove(at + 1);
            arguments.remove(at);
            defines.split(';').map(str::to_string).collect()
        }
        None => Vec::new(),
    };
    let [project, gend, minigen, runtime] = arguments.as_slice() else {
        eprintln!(
            "usage: hot <project> <gend.dll> <minigen.dll> <PilotRuntime.dll> [--define A;B]"
        );
        std::process::exit(2);
    };
    let project = PathBuf::from(project);
    let mut paths = Vec::new();
    sources(&project.join("Assets"), &mut paths);
    let paths: Vec<PathBuf> = paths
        .into_iter()
        .map(|path| path.strip_prefix(&project).unwrap_or(&path).to_path_buf())
        .collect();
    let tools = Tools {
        dotnet: PathBuf::from("dotnet"),
        gend: PathBuf::from(gend),
        minigen: PathBuf::from(minigen),
        runtime: PathBuf::from(runtime),
    };
    let session = Session::new(&project, None, symbols);
    let started = Instant::now();
    let built = session
        .hot_start(tools.clone(), &paths)
        .unwrap_or_else(|why| panic!("{why}"));
    println!(
        "started in {} ms: {} ({} ms to build, {} stubs)",
        started.elapsed().as_millis(),
        built.assembly.display(),
        built.milliseconds,
        built.stubs
    );
    // An editor not running yet is given the build to start on, where it
    // would take Unity's own; one running reloads on it.
    let running = std::process::Command::new("pgrep")
        .args([
            "-f",
            &format!(
                "Unity.app/Contents/MacOS/Unity .*-projectPath {}",
                project.display()
            ),
        ])
        .output()
        .is_ok_and(|output| !output.stdout.is_empty());
    if running {
        let reloaded = probe(
            &project,
            &format!("reload {}", built.assembly.display()),
            &["reloaded", "failed"],
            Duration::from_secs(600),
        );
        println!("editor: {reloaded:?}");
    } else {
        let bytes = std::fs::read(&built.assembly).expect("the build");
        for place in [
            "Library/ScriptAssemblies/Assembly-CSharp.dll",
            "Library/Bee/artifacts/900b0aEDbg.dag/post-processed/Assembly-CSharp.dll",
        ] {
            let target = project.join(place);
            let staged = target.with_extension("dll.pilot");
            std::fs::write(&staged, &bytes).expect("writable");
            std::fs::rename(&staged, &target).expect("movable");
            let _ = std::fs::remove_file(target.with_extension("pdb"));
        }
        let _ = std::fs::remove_file(project.join("Temp/PilotProbe/log.txt"));
        println!("staged: open the project");
        let log = project.join("Temp/PilotProbe/log.txt");
        while !std::fs::read_to_string(&log)
            .unwrap_or_default()
            .contains("started assembly")
        {
            std::thread::sleep(Duration::from_millis(500));
        }
        println!("editor: started on the build");
    }
    println!(
        "{:?}",
        probe(
            &project,
            &format!("load {}", tools.runtime.display()),
            &["loaded", "failed"],
            Duration::from_secs(60)
        )
    );
    for line in std::io::stdin().lock().lines() {
        let Ok(saved) = line else { break };
        let saved = saved.trim();
        if saved.is_empty() {
            continue;
        }
        let started = Instant::now();
        let answer = session.hot_save(&[PathBuf::from(saved)], &paths);
        let made = started.elapsed().as_millis();
        match answer {
            Ok(Answer::Patch { assembly, methods }) => {
                let applied = probe(
                    &project,
                    &format!("hotpatch {}", assembly.display()),
                    &["hotpatched", "failed hotpatch"],
                    Duration::from_secs(60),
                );
                println!(
                    "{saved}: patch in {made} ms, applied {} ms after the save: {applied:?} ({} methods)",
                    started.elapsed().as_millis(),
                    methods.len()
                );
            }
            other => println!("{saved}: {other:?} in {made} ms"),
        }
    }
}
