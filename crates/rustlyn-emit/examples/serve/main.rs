//! Keeps a compiled assembly in memory and writes it again whenever a file
//! changes, generating only the bodies the change is in.
//!
//! The first build is a whole one; after it, each line on standard input
//! names a source file whose text on disk changed. The file is parsed again,
//! its members are compared with the ones it had, and when only bodies
//! differ the assembly is written again with those bodies alone generated.
//! Anything else — a member added, a signature changed, text between the
//! members — is refused, and the answer says a full build is needed.
//!
//! ```text
//! cargo run --release -p rustlyn-emit --example serve -- \
//!     $REFERENCES out/Assembly-CSharp.dll --define "A;B" < commands
//! ```
//!
//! Every answer is one line on standard output: `ready <ms>` after the first
//! build, `rebuilt <ms> <what>` or `refused <why>` after a change.
//!
//! With `--hot <directory>` the assembly is built for hot patching (every
//! member opened to the assembly, `InternalsVisibleTo("PilotPatch")`), and
//! each change also writes `PilotPatch-<n>.dll` and its manifest there: the
//! changed methods as static methods an editor can send the old ones to
//! (see `patch.rs`). The answer is then `patch <ms> <dll>`, or `nopatch
//! <why>` where a reload is needed.
//!
//! With `--generators <command>` the source generators run too: the command
//! is a process that takes an edited path per line and answers `gen <ms>`
//! followed by a tab and each generated file it wrote again (see
//! `tools/unity/minigen`). Those files change with the edit, in the same
//! compilation and the same patch.

use rustlyn_emit::hot::{self, Session, Tails, broken, find_tree, write_atomically};

use std::io::{BufRead, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;

use rustlyn_semantics::{Compilation, SymbolId};
use rustlyn_syntax::{ParseOptions, SyntaxKind, SyntaxNode, SyntaxTree, parse_with};
use rustlyn_text::{SourceText, TextSpan};

fn main() -> std::process::ExitCode {
    let mut arguments = std::env::args().skip(1);
    let (Some(framework), Some(out)) = (
        arguments.next().map(PathBuf::from),
        arguments.next().map(PathBuf::from),
    ) else {
        eprintln!("usage: serve <references directory> <out.dll> [--define A;B] [--sources list]");
        return std::process::ExitCode::FAILURE;
    };
    let arguments: Vec<String> = arguments.collect();
    let value = |name: &str| {
        arguments
            .iter()
            .position(|argument| argument == name)
            .and_then(|at| arguments.get(at + 1))
            .cloned()
    };
    let hot = value("--hot").map(PathBuf::from);
    let symbols: Vec<String> = value("--define")
        .map(|defines| defines.split(';').map(str::to_string).collect())
        .unwrap_or_default();
    let options = ParseOptions::with_symbols(symbols);

    let mut references: Vec<_> = std::fs::read_dir(&framework)
        .unwrap_or_else(|error| panic!("{}: {error}", framework.display()))
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
        .collect();
    references.sort();
    let bytes: Vec<Vec<u8>> = references
        .iter()
        .filter_map(|path| std::fs::read(path).ok())
        .collect();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();

    // The file list comes from `--sources` so that standard input is left
    // for the commands.
    let Some(list) = value("--sources").and_then(|path| std::fs::read_to_string(path).ok()) else {
        eprintln!("--sources <file listing the sources> is needed");
        return std::process::ExitCode::FAILURE;
    };
    let list_path = value("--sources").expect("read above");
    // `--gatherer`: the generators over the whole assembly (tools/unity/gend),
    // for what one file's generators cannot see — a file added or deleted,
    // many saved at once, a feature the runner lists. It owns the directory
    // of generated files (`--generated`): what it writes there at the start
    // is the list's generated part.
    let generated_dir = value("--generated");
    let gatherer_command = value("--gatherer");
    let mut gatherer = value("--gatherer").map(|command| {
        let started = Instant::now();
        let (gatherer, said) = Generators::start_until(&command, "ready");
        eprintln!("gatherer {said} ({} ms)", started.elapsed().as_millis());
        gatherer
    });
    let list = match (&gatherer, &generated_dir) {
        (Some(_), Some(directory)) => {
            let mut lines: Vec<String> = list
                .lines()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with(directory.as_str()))
                .map(str::to_string)
                .collect();
            let mut made = Vec::new();
            files_under(Path::new(directory), &mut made);
            made.sort();
            lines.extend(made);
            let text: String = lines.iter().map(|line| format!("{line}\n")).collect();
            let _ = std::fs::write(&list_path, &text);
            text
        }
        _ => list,
    };
    // The files listed, kept up to date as files come and go: a daemon
    // started again builds what the editor has.
    let mut listed: Vec<String> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect();
    let mut sources: Vec<SourceText> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter_map(|path| read_source(Path::new(path)).map(|text| SourceText::new(path, text)))
        .collect();
    if let Some(directory) = &hot {
        std::fs::create_dir_all(directory).expect("the patch directory should be makeable");
        sources.push(SourceText::new(
            "PilotPatchAccess.cs",
            "[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"PilotPatch\")]\n",
        ));
    }

    let started = Instant::now();
    let mut arena = Arena::default();
    let mut current: &'static Compilation = arena.hold(Compilation::parse_with_references(
        sources, &options, &images,
    ));
    // An editor's build gives structs a tail for the fields an edit will add
    // to them (see `tails.rs`), written into the files as they are read.
    let mut tailed = Tails::default();
    // RUSTLYN_NO_TAILS, RUSTLYN_NO_WIDEN: an editor's build without the
    // one or the other, to tell what of it an editor trips over.
    if hot.is_some() && std::env::var_os("RUSTLYN_NO_TAILS").is_none() {
        tailed = Tails::choose(current);
        let _ = std::fs::write(out.with_extension("tails.txt"), tailed.listing());
        // The tails are fields the emitter writes (`struct_tails`); the
        // compilation only has to declare their types.
        let mut trees: Vec<SyntaxTree> = (0..current.trees().len())
            .map(|index| current.trees().get(index).expect("every tree").clone())
            .collect();
        trees.push(parse_with(
            SourceText::new("PilotTails.cs", hot::TAIL_SUPPORT),
            &options,
        ));
        current = arena.hold(Compilation::create_with_references(trees, &images));
        arena.keep_only(&[current]);
    }
    let (mut kept, emitted, skipped) = rustlyn_emit::incremental_with(
        current,
        "Assembly-CSharp",
        rustlyn_emit::IncrementalOptions {
            widen_for_patches: hot.is_some() && std::env::var_os("RUSTLYN_NO_WIDEN").is_none(),
            struct_tails: tailed.struct_tails(),
        },
    )
    .expect("the first build");
    write_atomically(&out, &emitted.assembly);
    // What the first build could not make, and made a stub of instead. A
    // later whole build that stubs more than this lost code an edit brought,
    // and the editor would run the stubs: it is refused.
    let first_stubs: std::collections::HashSet<String> =
        skipped.iter().map(|(name, _)| name.clone()).collect();
    println!(
        "ready {} ms, {} bytes, {} stubs",
        started.elapsed().as_millis(),
        emitted.assembly.len(),
        skipped.len()
    );

    let mut rounds = 0usize;
    let mut stale = false;
    // What the editor has loaded: patches are compiled against it, and say
    // what differs from it, every edit since it was built together.
    let mut base: &'static Compilation = current;
    // The compilation the incremental build last worked from, which it
    // keeps: with `base` and `current`, all a round's compilations are
    // still needed for.
    let mut kept_on: &'static Compilation = current;
    let mut base_image = emitted.assembly.clone();
    // `PilotRuntime.dll`, which holds the fields an edit adds to a class.
    let runtime = value("--runtime").and_then(|path| std::fs::read(path).ok());
    let mut generators = value("--generators").map(|command| Generators::start(&command));
    let mut patch_images: Vec<&[u8]> = images.clone();
    if let Some(runtime) = &runtime {
        patch_images.push(runtime);
    }
    // What the editor has been sent since it loaded the base.
    let mut session = hot.as_ref().map(|directory| {
        Session::new(
            base,
            base_image.clone(),
            tailed.clone(),
            patch_images
                .iter()
                .map(|bytes| std::sync::Arc::<[u8]>::from(*bytes))
                .collect(),
            directory.clone(),
            options.clone(),
        )
    });
    for line in std::io::stdin().lock().lines() {
        // Each round makes a compilation of all the files, which is large:
        // what no one holds any longer goes.
        arena.keep_only(&[base, current, kept_on]);
        let Ok(line) = line else { break };
        let path = line.trim();
        if path.is_empty() {
            continue;
        }
        if path == "quit" {
            break;
        }
        // What only a reload brings in: the whole assembly is built again
        // from what the files say now, and becomes what patches are made
        // against once the editor has loaded it.
        if path == "rebuild" {
            let building = Instant::now();
            let (fresh, emitted, skipped) = rustlyn_emit::incremental_with(
                current,
                "Assembly-CSharp",
                rustlyn_emit::IncrementalOptions {
                    widen_for_patches: hot.is_some()
                        && std::env::var_os("RUSTLYN_NO_WIDEN").is_none(),
                    struct_tails: tailed.struct_tails(),
                },
            )
            .expect("a whole build");
            if let Some((name, why)) = skipped.iter().find(|(name, _)| !first_stubs.contains(name))
            {
                println!(
                    "refused the whole build: {name} could not be made: {}",
                    why.replace('\n', " | ")
                );
                continue;
            }
            write_atomically(&out, &emitted.assembly);
            kept = fresh;
            kept_on = current;
            base = current;
            base_image = emitted.assembly;
            if let Some(session) = &mut session {
                session.reloaded(base, base_image.clone());
            }
            stale = false;
            println!(
                "ready {} ms, {} bytes, {} stubs",
                building.elapsed().as_millis(),
                base_image.len(),
                skipped.len()
            );
            continue;
        }
        // `errors <path>`: whether the file as it is now compiles — what the
        // replay of a commit asks, to tell an edit that cannot be patched
        // from one that would not have compiled anyway.
        if let Some(file) = path.strip_prefix("errors ") {
            match find_tree(current, file) {
                Some(index) => {
                    let syntax = current
                        .trees()
                        .get(index)
                        .map(|tree| {
                            tree.diagnostics()
                                .iter()
                                .filter(|entry| entry.is_error())
                                .count()
                        })
                        .unwrap_or(0);
                    let bodies: Vec<_> = rustlyn_semantics::SemanticModel::new(current, index)
                        .body_diagnostics()
                        .into_iter()
                        .filter(|(_, entry)| entry.is_error())
                        .collect();
                    let first = bodies
                        .first()
                        .map(|(_, entry)| entry.message().replace('\n', " "))
                        .unwrap_or_default();
                    println!("errors {} {file}: {first}", syntax + bodies.len());
                }
                None => println!("errors 0 {file}: not a source"),
            }
            continue;
        }
        // `classify <manifest>`: whether an edit someone made — a commit, the
        // manifest naming each file it touched and where the file's text from
        // before it is, or `-` where it added the file — would have been a
        // patch, made the way a round makes one, against the assembly built
        // from the files as they are now. Nothing is loaded or kept.
        if let Some(manifest) = path.strip_prefix("classify ") {
            if let Some(directory) = &hot {
                rounds += 1;
                let answer = classify(
                    current,
                    manifest,
                    &tailed,
                    &options,
                    &images,
                    &patch_images,
                    &base_image,
                    directory,
                    rounds,
                );
                match answer {
                    Ok(dll) if dll.as_os_str().is_empty() => println!("classified patch nothing"),
                    Ok(dll) => println!("classified patch {}", dll.display()),
                    Err(why) => println!("classified nopatch {}", why.replace('\n', " | ")),
                }
            }
            continue;
        }
        let round = Instant::now();
        // What the generators write for the edit changes with it. Several
        // files saved together — a branch checked out — come on one line,
        // a tab between each two, and are one round.
        let saved: Vec<String> = path.split('\t').map(str::to_string).collect();
        let mut paths = saved.clone();
        let mut generated_ms = 0;
        // The gatherer hears of every save; it runs for a round that adds or
        // deletes a file or saves many, and one file's generators do not.
        let structural = saved.len() > 1
            || saved
                .iter()
                .any(|file| !Path::new(file).exists() || !listed.contains(file));
        if let Some(gatherer) = &mut gatherer {
            let generating = Instant::now();
            let mut told = Ok(());
            for file in &saved {
                let line = if !Path::new(file).exists() {
                    format!("- {file}")
                } else if listed.contains(file) {
                    file.clone()
                } else {
                    format!("+ {file}")
                };
                told = told.and_then(|_| gatherer.send(&line));
            }
            if structural {
                let mut ran = told
                    .and_then(|_| gatherer.send("run"))
                    .and_then(|_| gatherer.until("generated"));
                // Generators that threw — Roslyn's driver holding a tree the
                // compilation no longer has — kept what they wrote before:
                // they start again on the files as they are, and what they
                // write then is the round's.
                if let (Ok(said), Some(command)) = (&ran, &gatherer_command)
                    && said
                        .split('\t')
                        .next()
                        .is_some_and(|head| head.contains("threw:"))
                {
                    let earlier: Vec<String> =
                        said.split('\t').skip(1).map(str::to_string).collect();
                    // The list it starts from has the files this round
                    // added or deleted.
                    relist(&mut listed, &saved, &list_path);
                    let _ = gatherer.send("quit");
                    let (fresh, ready) = Generators::start_until(command, "ready");
                    *gatherer = fresh;
                    eprintln!(
                        "gatherer started again: {}",
                        ready.split('\t').next().unwrap_or_default()
                    );
                    let mut all = earlier;
                    all.extend(ready.split('\t').skip(1).map(str::to_string));
                    ran = Ok(std::iter::once("generated again".to_string())
                        .chain(all)
                        .collect::<Vec<_>>()
                        .join("\t"));
                }
                match ran {
                    Ok(said) => {
                        for written in said.split('\t').skip(1) {
                            if !paths.iter().any(|seen| seen == written) {
                                paths.push(written.to_string());
                            }
                        }
                        eprintln!("gathered {}", said.split('\t').next().unwrap_or_default());
                    }
                    Err(why) => {
                        println!("refused the generators: {why}");
                        continue;
                    }
                }
                // One file's generators read the directory again.
                if let Some(generators) = &mut generators {
                    let rescan = std::iter::once("rescan".to_string())
                        .chain(saved.iter().cloned())
                        .collect::<Vec<_>>()
                        .join("\t");
                    if let Err(why) = generators
                        .send(&rescan)
                        .and_then(|_| generators.until("gen"))
                    {
                        println!("refused the generators: {why}");
                        continue;
                    }
                }
                generated_ms = generating.elapsed().as_millis();
            }
        }
        if let Some(generators) = generators
            .as_mut()
            .filter(|_| !(structural && gatherer.is_some()))
        {
            let generating = Instant::now();
            let mut refused = None;
            for file in &saved {
                match generators.run(file) {
                    Ok(written) => {
                        for written in written {
                            if !paths.contains(&written) {
                                paths.push(written);
                            }
                        }
                    }
                    Err(why) => {
                        refused = Some(why);
                        break;
                    }
                }
            }
            if let Some(why) = refused {
                println!("refused the generators: {why}");
                continue;
            }
            generated_ms = generating.elapsed().as_millis();
        }
        let declaring = Instant::now();
        let (compilation, bodies) =
            match change(&mut arena, current, &options, &images, &paths, &tailed) {
                Ok(found) => found,
                Err(why) => {
                    println!("refused {why}");
                    continue;
                }
            };
        let declared = declaring.elapsed().as_millis();
        // A file saved halfway through an edit: a patch of it would be
        // refused anyway, but the whole build would take what the parser
        // made of it — a class missing the methods after an unclosed brace.
        // Nothing of it goes anywhere; the next save is read again.
        if let Some(why) = broken(compilation, &paths) {
            println!("broken {}", why.replace('\n', " | "));
            continue;
        }
        // What a deleted file declared the running code may still use, and
        // its types go only with a reload.
        if let Some(deleted) = paths
            .iter()
            .find(|path| path.starts_with('-') || !Path::new(path.as_str()).exists())
        {
            let deleted = deleted.trim_start_matches('-').to_string();
            if let Some(session) = &mut session {
                session.forget(&deleted);
            }
            if hot.is_some() {
                println!(
                    "nopatch {deleted}: the file was deleted, and what it declared goes with a reload"
                );
            }
            stale = true;
            println!("stale {deleted}: deleted; the assembly on disk waits for a whole build");
            current = compilation;
            relist(&mut listed, &paths, &list_path);
            continue;
        }
        if let Some(session) = &mut session {
            let patching = Instant::now();
            match session.patch(base, compilation, &paths) {
                Ok(None) => println!("unchanged {path}"),
                Ok(Some(dll)) => println!(
                    "patch {} ms (generate {generated_ms} ms, declare {declared} ms, patch {} ms) {}",
                    round.elapsed().as_millis(),
                    patching.elapsed().as_millis(),
                    dll.display()
                ),
                Err(why) => println!("nopatch {}", why.replace('\n', " | ")),
            }
        }
        // The assembly on disk, once the patch is out, follows bodies alone; once a declaration has
        // changed it waits for a whole build, which nothing here makes yet.
        match bodies {
            Some(changed) if !stale && !changed.is_empty() => {
                // It holds what it is given even when it fails.
                kept_on = compilation;
                match kept.rebuild(compilation, &changed) {
                    Ok(rebuilt) => {
                        write_atomically(&out, &rebuilt.assembly);
                        let names: Vec<String> = changed
                            .iter()
                            .map(|symbol| compilation.symbols().qualified_name(*symbol))
                            .collect();
                        println!(
                            "rebuilt {} ms, {} bodies: {}",
                            round.elapsed().as_millis(),
                            rebuilt.bodies,
                            names.join(", ")
                        );
                    }
                    Err(error) => {
                        stale = true;
                        println!("stale {error}");
                    }
                }
            }
            Some(_) if !stale => println!("unchanged {path}"),
            _ => {
                stale = true;
                println!(
                    "stale {path}: declarations changed; the assembly on disk waits for a whole build"
                );
            }
        }
        current = compilation;
        relist(&mut listed, &paths, &list_path);
    }
    std::process::ExitCode::SUCCESS
}

/// What `classify` answers: the patch an edit from the files' texts in the
/// manifest to what they are now would have been, or why there is none.
#[allow(clippy::too_many_arguments)]
fn classify(
    current: &'static Compilation,
    manifest: &str,
    tailed: &Tails,
    options: &ParseOptions,
    images: &[&[u8]],
    patch_images: &[&[u8]],
    base_image: &[u8],
    directory: &Path,
    round: usize,
) -> Result<PathBuf, String> {
    let listed = std::fs::read_to_string(manifest).map_err(|error| error.to_string())?;
    let trees = current.trees();
    let mut before: Vec<Option<SyntaxTree>> = (0..trees.len())
        .map(|index| trees.get(index).cloned())
        .collect();
    let mut paths = Vec::new();
    for line in listed.lines().filter(|line| !line.trim().is_empty()) {
        let (path, was) = line
            .split_once('\t')
            .ok_or_else(|| format!("{line}: a path and where its old text is"))?;
        let index = find_tree(current, path).ok_or_else(|| format!("{path} is not a source"))?;
        before[index] = if was == "-" {
            None
        } else {
            let text =
                read_source(Path::new(was)).ok_or_else(|| format!("{was} cannot be read"))?;
            Some(with_tails(
                tailed,
                parse_with(SourceText::new(path, text), options),
                options,
            ))
        };
        paths.push(path.to_string());
    }
    let before =
        Compilation::create_with_references(before.into_iter().flatten().collect(), images);
    let before = &before;
    hot::patch_between(
        before,
        current,
        &paths,
        tailed,
        round,
        options,
        patch_images,
        base_image,
        directory,
    )
}

/// The compilation with `paths` read again, and the members whose bodies
/// are all that changed in them.
fn change(
    arena: &mut Arena,
    current: &'static Compilation,
    options: &ParseOptions,
    images: &[&[u8]],
    paths: &[String],
    tailed: &Tails,
) -> Result<(&'static Compilation, Option<Vec<SymbolId>>), String> {
    let cloning = Instant::now();
    let trees = current.trees();
    let mut all: Vec<SyntaxTree> = (0..trees.len())
        .map(|index| trees.get(index).expect("every tree").clone())
        .collect();
    // Each replaced tree by its index, with the one it replaces.
    let mut replaced: Vec<(usize, SyntaxTree)> = Vec::new();
    let mut added = false;
    let mut gone: Vec<usize> = Vec::new();
    for path in paths {
        // A file deleted, or a generated one its source took along: its tree
        // goes, which nothing but a reload follows.
        let deleted = path.strip_prefix('-').unwrap_or(path);
        if path.starts_with('-') || !Path::new(path).exists() {
            if let Some(index) = find_tree(current, deleted) {
                gone.push(index);
            }
            continue;
        }
        let text = read_source(Path::new(path)).ok_or_else(|| format!("{path} cannot be read"))?;
        match find_tree(current, path) {
            Some(index) => {
                let name = trees.source(index).expect("found above").name().to_string();
                let tree = with_tails(
                    tailed,
                    parse_with(SourceText::new(name, text), options),
                    options,
                );
                replaced.push((index, all[index].clone()));
                all[index] = tree;
            }
            // A file that was not there: its tree joins the others.
            None => {
                all.push(parse_with(SourceText::new(path.as_str(), text), options));
                added = true;
            }
        }
    }
    gone.sort_unstable();
    for &index in gone.iter().rev() {
        all.remove(index);
    }
    eprintln!("trees {} ms", cloning.elapsed().as_millis());
    let creating = Instant::now();
    // An edit inside bodies changes no declaration: the compilation is the
    // current one with those files' trees in it (`with_trees_replaced`),
    // without declaring the other thirty thousand again.
    let edited: Vec<(usize, SyntaxTree)> = replaced
        .iter()
        .filter(|(index, old)| old.text() != all[*index].text())
        .map(|(index, _)| (*index, all[*index].clone()))
        .collect();
    let quick = if added || !gone.is_empty() {
        None
    } else if edited.is_empty() {
        Some(None)
    } else {
        current.with_trees_replaced(edited).map(Some)
    };
    let was_quick = quick.is_some();
    let compilation = match quick {
        Some(Some(made)) => arena.hold(made),
        Some(None) => current,
        None => arena.hold(Compilation::create_with_references(all.clone(), images)),
    };
    eprintln!(
        "create {} ms{}",
        creating.elapsed().as_millis(),
        if was_quick { " (bodies only)" } else { "" }
    );
    if added || !gone.is_empty() {
        return Ok((compilation, None));
    }
    let comparing = Instant::now();
    let mut bodies = Some(Vec::new());
    for (index, old) in &replaced {
        bodies = match (
            bodies,
            bodies_only(old, &all[*index], current, compilation, *index),
        ) {
            (Some(mut all), Some(more)) => {
                all.extend(more);
                Some(all)
            }
            _ => None,
        };
    }
    eprintln!("bodies {} ms", comparing.elapsed().as_millis());
    Ok((compilation, bodies))
}

/// The tree as it is: a struct's tail is a field the emitter writes
/// (`IncrementalOptions::struct_tails`), not text in its file.
fn with_tails(_tailed: &Tails, tree: SyntaxTree, _options: &ParseOptions) -> SyntaxTree {
    tree
}

/// The process that runs the source generators on an edited file.
struct Generators {
    /// Kept so that the process lives as long as the daemon does.
    _process: std::process::Child,
    input: std::process::ChildStdin,
    output: std::io::BufReader<std::process::ChildStdout>,
}

impl Generators {
    fn start(command: &str) -> Self {
        let mut child = std::process::Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("the generators should start");
        let input = child.stdin.take().expect("piped above");
        let mut output = std::io::BufReader::new(child.stdout.take().expect("piped above"));
        let mut ready = String::new();
        output
            .read_line(&mut ready)
            .expect("the generators should answer");
        eprintln!("generators {}", ready.trim());
        Self {
            _process: child,
            input,
            output,
        }
    }

    /// A process that answers once it is ready: what it said then.
    fn start_until(command: &str, ready: &str) -> (Self, String) {
        let mut child = std::process::Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("the gatherer should start");
        let input = child.stdin.take().expect("piped above");
        let output = std::io::BufReader::new(child.stdout.take().expect("piped above"));
        let mut started = Self {
            _process: child,
            input,
            output,
        };
        let said = started.until(ready).expect("the gatherer should be ready");
        (started, said)
    }

    /// Sends a line, answered or not.
    fn send(&mut self, line: &str) -> Result<(), String> {
        writeln!(self.input, "{line}").map_err(|error| error.to_string())?;
        self.input.flush().map_err(|error| error.to_string())
    }

    /// The first line that starts with `head`, or one saying what failed.
    fn until(&mut self, head: &str) -> Result<String, String> {
        loop {
            let mut line = String::new();
            if self
                .output
                .read_line(&mut line)
                .map_err(|error| error.to_string())?
                == 0
            {
                return Err("the process ended".to_string());
            }
            if line.starts_with(head) {
                return Ok(line.trim_end().to_string());
            }
            if line.starts_with("failed") {
                return Err(line.trim().to_string());
            }
        }
    }

    /// The generated files the edit of `path` wrote, or, for a file that is
    /// gone, the ones it took along, each with a `-` before it.
    fn run(&mut self, path: &str) -> Result<Vec<String>, String> {
        if Path::new(path).exists() {
            writeln!(self.input, "{path}").map_err(|error| error.to_string())?;
        } else {
            writeln!(self.input, "delete {path}").map_err(|error| error.to_string())?;
        }
        self.input.flush().map_err(|error| error.to_string())?;
        let mut answer = String::new();
        self.output
            .read_line(&mut answer)
            .map_err(|error| error.to_string())?;
        let mut parts = answer.trim_end().split('\t');
        match parts.next() {
            Some(head) if head.starts_with("gen ") => Ok(parts.map(str::to_string).collect()),
            _ => Err(answer.trim().to_string()),
        }
    }
}

/// The members whose bodies changed, where nothing else in the file did and
/// the compilation declares what it did: what an incremental rebuild of the
/// assembly can take.
fn bodies_only(
    old: &SyntaxTree,
    tree: &SyntaxTree,
    current: &Compilation,
    compilation: &Compilation,
    index: usize,
) -> Option<Vec<SymbolId>> {
    let before = members(old);
    let after = members(tree);
    if before.len() != after.len()
        || skeleton(old, &before) != skeleton(tree, &after)
        || compilation.symbols().len() != current.symbols().len()
    {
        return None;
    }
    before
        .iter()
        .zip(&after)
        .filter(|(was, now)| {
            slice(old.source().text(), was.span()) != slice(tree.source().text(), now.span())
        })
        .map(|(_, now)| compilation.declared_symbol(index, now.span()))
        .collect()
}

/// The members with bodies of a file, outermost first: a method, a
/// constructor, an accessor — not the local functions inside one, which are
/// part of its body.
fn members(tree: &SyntaxTree) -> Vec<SyntaxNode> {
    let mut found: Vec<SyntaxNode> = Vec::new();
    for node in tree.root().descendants() {
        let with_body = matches!(
            node.kind(),
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::DestructorDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
                | SyntaxKind::GetAccessorDeclaration
                | SyntaxKind::SetAccessorDeclaration
                | SyntaxKind::InitAccessorDeclaration
                | SyntaxKind::AddAccessorDeclaration
                | SyntaxKind::RemoveAccessorDeclaration
        );
        let inside = found.iter().any(|outer| {
            outer.span().start() <= node.span().start() && node.span().end() <= outer.span().end()
        });
        if with_body && !inside {
            found.push(node);
        }
    }
    found
}

/// The file's text with every member's body taken out: two files with the
/// same skeleton differ only inside bodies. A member's head — its
/// attributes, modifiers and signature — stays, so changing one is a change
/// to the skeleton.
fn skeleton(tree: &SyntaxTree, members: &[SyntaxNode]) -> String {
    let text = tree.source().text();
    let mut out = String::with_capacity(text.len());
    let mut at = 0usize;
    for member in members {
        let span = member.span();
        out.push_str(&text[at..span.start() as usize]);
        // The head of the member, up to where its body starts, stays.
        let body = member
            .children()
            .find(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                )
            })
            .map_or(span.end(), |body| body.span().start());
        out.push_str(&text[span.start() as usize..body as usize]);
        out.push('\u{1}');
        at = span.end() as usize;
    }
    out.push_str(&text[at..]);
    out
}

fn slice(text: &str, span: TextSpan) -> &str {
    &text[span.start() as usize..span.end() as usize]
}

/// The compilations a round makes, each given out for as long as the
/// program runs — the incremental build and the base hold on to theirs —
/// and dropped once none of those holds it.
#[derive(Default)]
struct Arena {
    held: Vec<*mut Compilation>,
}

impl Arena {
    fn hold(&mut self, compilation: Compilation) -> &'static Compilation {
        let held = Box::into_raw(Box::new(compilation));
        self.held.push(held);
        // SAFETY: freed only by `keep_only`, once nothing that is still
        // used refers to it.
        unsafe { &*held }
    }

    /// Drops every compilation but `kept`. Nothing else may still refer to
    /// the others.
    fn keep_only(&mut self, kept: &[&'static Compilation]) {
        self.held.retain(|&held| {
            let keep = kept
                .iter()
                .any(|&compilation| std::ptr::eq(compilation, held));
            if !keep {
                // SAFETY: made by `hold`, and no longer referred to.
                drop(unsafe { Box::from_raw(held) });
            }
            keep
        });
    }
}

/// Every C# file under `directory`.
fn files_under(directory: &Path, found: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            files_under(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "cs") {
            found.push(path.to_string_lossy().into_owned());
        }
    }
}

/// The source list with the files a round added or deleted, written again
/// when it changed.
fn relist(listed: &mut Vec<String>, paths: &[String], list_path: &str) {
    let mut changed = false;
    for path in paths {
        let file = path.trim_start_matches('-');
        let there = !path.starts_with('-') && Path::new(file).exists();
        let known = listed.iter().position(|entry| entry == file);
        match (there, known) {
            // In the order Unity lists the files to csc — by path, case
            // ignored — among the project's own: the fields of a partial
            // type are laid out in the order of its files, and an editor's
            // reload reads them back in the order it wrote them.
            (true, None) => {
                let key = file.to_uppercase();
                let at = listed
                    .iter()
                    .position(|entry| !Path::new(entry).is_absolute() && entry.to_uppercase() > key)
                    .or_else(|| {
                        listed
                            .iter()
                            .position(|entry| Path::new(entry).is_absolute())
                    })
                    .unwrap_or(listed.len());
                let at = if Path::new(file).is_absolute() {
                    listed.len()
                } else {
                    at
                };
                listed.insert(at, file.to_string());
                changed = true;
            }
            (false, Some(at)) => {
                listed.remove(at);
                changed = true;
            }
            _ => {}
        }
    }
    if changed {
        let text: String = listed.iter().map(|entry| format!("{entry}\n")).collect();
        let temporary = format!("{list_path}.writing");
        if std::fs::write(&temporary, text).is_ok() {
            let _ = std::fs::rename(&temporary, list_path);
        }
    }
}

/// A source file as text: UTF-8, or each byte as the Latin-1 character it is.
fn read_source(path: &Path) -> Option<String> {
    let bytes = std::fs::read(path).ok()?;
    Some(String::from_utf8(bytes).unwrap_or_else(|error| {
        error
            .into_bytes()
            .iter()
            .map(|&byte| byte as char)
            .collect()
    }))
}
