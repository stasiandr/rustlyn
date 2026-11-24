//! Past changes from git: the commits of a range, or one commit, as
//! [`Revision`]s to judge. A caller that holds a repository needs no git
//! plumbing of its own.

use std::collections::{HashMap, HashSet};
use std::io::Read;

use crate::blast::diff::{Status, parse};
use crate::blast::setup;

use super::Revision;
use super::config::Config;
use super::packages::{LOCK, MANIFEST};

/// The commits of a git range as changes to judge, oldest first. First
/// parents only: a merge commit stands for the whole branch it merged.
/// `progress(done, total)` is called before each commit is read, so a
/// caller can show that a long range is not stuck; the library itself prints
/// nothing.
///
/// Sources, assets, the two package files and the files the configuration
/// reads as text ([`Config::text_files`]) are diffed and their text kept;
/// everything else — scenes and prefabs of hundreds of megabytes among it —
/// only by name ([`Revision::others`]), which is what a watch needs.
///
/// # Errors
///
/// When git cannot be run or does not know the range.
pub fn revisions(
    root: &str,
    range: &str,
    config: &Config,
    progress: &dyn Fn(usize, usize),
) -> Result<Vec<Revision>, String> {
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
        progress(index + 1, commits.len());
        // The first commit of a repository has nothing to be compared with.
        if !has_parent(root, id) {
            continue;
        }
        revisions.push(read(root, &mut blobs, id, title, config)?);
    }
    Ok(revisions)
}

/// One commit as a change to judge: against its first parent, read the way
/// [`revisions`] reads a range.
///
/// # Errors
///
/// When git does not know the commit, or it has no parent to be compared
/// with.
pub fn revision(root: &str, commit: &str, config: &Config) -> Result<Revision, String> {
    let log = setup::git(root, &["log", "-1", "--format=%H%x09%s", commit])?;
    let (id, title) = log
        .trim_end()
        .split_once('\t')
        .ok_or_else(|| format!("{commit}: not a commit"))?;
    if !has_parent(root, id) {
        return Err(format!("{commit}: the commit has no parent"));
    }
    read(root, &mut Blobs::open(root)?, id, title, config)
}

fn has_parent(root: &str, id: &str) -> bool {
    let parent = format!("{id}^1");
    setup::git(root, &["rev-parse", "--verify", "--quiet", &parent]).is_ok()
}

/// The change of commit `id` against its first parent.
fn read(
    root: &str,
    blobs: &mut Blobs,
    id: &str,
    title: &str,
    config: &Config,
) -> Result<Revision, String> {
    let parent = format!("{id}^1");
    // `*.cs` matches in every folder; a glob is asked for as one.
    let mut specs: Vec<String> = vec![
        "*.cs".to_owned(),
        "*.asset".to_owned(),
        MANIFEST.to_owned(),
        LOCK.to_owned(),
    ];
    specs.extend(
        config
            .text_files
            .iter()
            .map(|glob| format!(":(glob){glob}")),
    );
    let mut args: Vec<&str> = vec![
        "diff",
        "--relative",
        "--no-color",
        "--no-ext-diff",
        &parent,
        id,
        "--",
    ];
    args.extend(specs.iter().map(String::as_str));
    let patch = setup::git(root, &args)?;
    let mut texts: HashMap<String, String> = HashMap::new();
    let mut diffed: HashSet<String> = HashSet::new();
    for file in parse(&patch) {
        if file.status != Status::Deleted
            && let Some(text) = blobs.text(&format!("{id}:./{}", file.path))
        {
            texts.insert(file.path.clone(), text);
        }
        diffed.insert(file.path);
    }
    // What no diff above names: by name only.
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
    let others: Vec<String> = names
        .lines()
        .filter(|name| !name.is_empty() && !diffed.contains(*name))
        .map(str::to_owned)
        .collect();
    Ok(Revision {
        id: id.to_owned(),
        title: title.to_owned(),
        patch,
        texts,
        others,
    })
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::testing::Project;

    fn commit(root: &str, message: &str) {
        let run = |args: &[&str]| {
            let mut all = vec!["-c", "user.email=t@example.com", "-c", "user.name=t"];
            all.extend_from_slice(args);
            setup::git(root, &all).expect("git");
        };
        run(&["add", "."]);
        run(&["commit", "-qm", message]);
    }

    fn config() -> Config {
        Config::parse(
            r#"{"sinks": [{"name": "Ads", "types": ["Tracker"]}],
                "watch": [{"name": "notes", "paths": ["notes.txt"]}]}"#,
        )
        .expect("config")
    }

    #[test]
    fn one_commit_and_a_range_read_the_same() {
        let project = Project::new(
            "reach-git",
            &[
                ("A.cs", "class A {\n}\n"),
                ("notes.txt", "one\n"),
                (
                    "Packages/manifest.json",
                    "{\"dependencies\": {\"com.a\": \"1.0.0\"}}\n",
                ),
                ("Game/Editor/AdsDependencies.xml", "<a/>\n"),
            ],
        );
        let root = project.root();
        setup::git(&root, &["init", "-q"]).expect("git");
        commit(&root, "first");
        project.write("A.cs", "class A {\n    void F() { }\n}\n");
        project.write("notes.txt", "two\n");
        project.write(
            "Packages/manifest.json",
            "{\"dependencies\": {\"com.a\": \"1.1.0\"}}\n",
        );
        project.write("Game/Editor/AdsDependencies.xml", "<a>\n</a>\n");
        commit(&root, "second");

        let config = config();
        let one = revision(&root, "HEAD", &config).expect("revision");
        assert_eq!(one.title, "second");
        // The sources, the package file and the build file are diffed, with
        // their text; the text file is not diffed and is named in `others`.
        let files = parse(&one.patch);
        let mut paths: Vec<&str> = files.iter().map(|f| f.path.as_str()).collect();
        paths.sort_unstable();
        assert_eq!(
            paths,
            vec![
                "A.cs",
                "Game/Editor/AdsDependencies.xml",
                "Packages/manifest.json"
            ]
        );
        assert_eq!(one.others, ["notes.txt"]);
        assert_eq!(
            one.texts.get("A.cs").map(String::as_str),
            Some("class A {\n    void F() { }\n}\n")
        );
        assert!(one.texts.contains_key("Packages/manifest.json"));
        assert!(one.texts.contains_key("Game/Editor/AdsDependencies.xml"));
        assert!(!one.texts.contains_key("notes.txt"));

        let seen = std::cell::RefCell::new(Vec::new());
        let range = revisions(&root, "HEAD~1..HEAD", &config, &|done, total| {
            seen.borrow_mut().push((done, total));
        })
        .expect("revisions");
        assert_eq!(range.len(), 1);
        assert_eq!(range[0].id, one.id);
        assert_eq!(range[0].others, one.others);
        assert_eq!(*seen.borrow(), vec![(1, 1)]);

        assert!(
            revision(&root, "HEAD~1", &config).is_err(),
            "the first commit has no parent"
        );
        assert!(revision(&root, "nonsense", &config).is_err());
    }
}
