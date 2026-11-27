//! What a report needs besides the patch, with no editor around: the
//! working copy's patch from git, the cache folder, the root as the session
//! sees it.

use std::path::{Path, PathBuf};
use std::process::Command;

use super::diff::split_lines;

/// The working copy's patch against `base` (`HEAD` by default): staged and
/// unstaged, plus new `.cs` files git does not track yet. `staged`: only
/// what is staged. Paths are relative to `root`.
///
/// # Errors
///
/// When git cannot be run or refuses.
pub fn git_patch(root: &str, base: Option<&str>, staged: bool) -> Result<String, String> {
    git_patch_noted(root, base, staged).map(|(patch, _)| patch)
}

/// [`git_patch`], with what could not be put into the patch: a source file
/// that git calls binary is compared here, and one that cannot be read is
/// named.
///
/// # Errors
///
/// When git cannot be run or refuses.
pub fn git_patch_noted(
    root: &str,
    base: Option<&str>,
    staged: bool,
) -> Result<(String, Vec<String>), String> {
    let mut args = vec!["diff", "--relative", "--no-color", "--no-ext-diff"];
    if staged {
        args.push("--cached");
    }
    let base = revision(base.unwrap_or("HEAD"))?;
    // A fresh repository without commits: nothing to compare with, all new.
    let has_head = git(root, &["rev-parse", "--verify", "--quiet", "HEAD"]).is_ok();
    if has_head || base != "HEAD" {
        args.push(base);
    }
    // What stands before `--` is a revision and nothing else: a `base` that
    // is also the name of a file is not taken for a path to compare.
    args.push("--");
    let mut patch = git(root, &args)?;
    let mut notes = Vec::new();
    if patch.contains("\nBinary files ") || patch.starts_with("Binary files ") {
        patch = mend_binary(root, &patch, base, staged, has_head, &mut notes);
    }
    if !staged {
        let untracked = git(
            root,
            &["ls-files", "--others", "--exclude-standard", "--", "*.cs"],
        )?;
        for path in untracked.lines().filter(|l| !l.is_empty()) {
            let Ok(text) = rustlyn_ide::document::read_source(Path::new(root).join(path)) else {
                continue;
            };
            patch += &added_file_patch(path, &text);
        }
    }
    Ok((patch, notes))
}

/// The patch with each source file git calls binary compared as text: a
/// UTF-16 file has NUL bytes in it, and `git diff` prints "Binary files …
/// differ" for it, with no line to find a member by. Both versions are read
/// through git and decoded as the compiler decodes them.
fn mend_binary(
    root: &str,
    patch: &str,
    base: &str,
    staged: bool,
    has_head: bool,
    notes: &mut Vec<String>,
) -> String {
    // What the two sides of the patch are: a range says both, a single
    // revision compares with the index or the working copy.
    let (old_rev, new_rev) = if let Some((a, b)) = base.split_once("...") {
        let b = if b.is_empty() { "HEAD" } else { b };
        let a = if a.is_empty() { "HEAD" } else { a };
        let merged = git(root, &["merge-base", a, b])
            .map(|out| out.trim().to_owned())
            .unwrap_or_else(|_| a.to_owned());
        (Some(merged), Some(b.to_owned()))
    } else if let Some((a, b)) = base.split_once("..") {
        let a = if a.is_empty() { "HEAD" } else { a };
        let b = if b.is_empty() { "HEAD" } else { b };
        (Some(a.to_owned()), Some(b.to_owned()))
    } else {
        (has_head.then(|| base.to_owned()), None)
    };
    let mut out = String::new();
    let mut section = String::new();
    let mut flush = |section: &mut String, out: &mut String| {
        if section.is_empty() {
            return;
        }
        let binary = section
            .lines()
            .find_map(|line| line.strip_prefix("Binary files ")?.strip_suffix(" differ"));
        let mended = binary.and_then(|sides| {
            let (a, b) = sides.split_once(" and ")?;
            let path = [b, a]
                .into_iter()
                .filter(|side| *side != "/dev/null")
                .map(|side| {
                    let side = side.trim_matches('"');
                    side.strip_prefix("b/")
                        .or_else(|| side.strip_prefix("a/"))
                        .unwrap_or(side)
                })
                .next()?;
            if !std::path::Path::new(path)
                .extension()
                .is_some_and(|extension| extension.eq_ignore_ascii_case("cs"))
            {
                return None;
            }
            let old = if a == "/dev/null" {
                Ok(String::new())
            } else {
                match &old_rev {
                    Some(rev) => show(root, &format!("{rev}:./{path}")),
                    None => Ok(String::new()),
                }
            };
            let new = if b == "/dev/null" {
                Ok(String::new())
            } else if let Some(rev) = &new_rev {
                show(root, &format!("{rev}:./{path}"))
            } else if staged {
                show(root, &format!(":./{path}"))
            } else {
                rustlyn_ide::document::read_source(Path::new(root).join(path))
                    .map_err(|e| e.to_string())
            };
            match (old, new) {
                (Ok(old), Ok(new)) => Some(text_patch(path, &old, &new, a == "/dev/null", b == "/dev/null")),
                (Err(error), _) | (_, Err(error)) => {
                    notes.push(format!(
                        "{path}: git calls it binary and it could not be read as text ({error}); its change is not analyzed"
                    ));
                    None
                }
            }
        });
        out.push_str(mended.as_deref().unwrap_or(section));
        section.clear();
    };
    for line in patch.split_inclusive('\n') {
        if line.starts_with("diff --git ") {
            flush(&mut section, &mut out);
        }
        section.push_str(line);
    }
    flush(&mut section, &mut out);
    out
}

/// A file's text at `object` (`rev:./path`), as the compiler reads a file.
fn show(root: &str, object: &str) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["show", object])
        .output()
        .map_err(|e| format!("git: {e}"))?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).trim().to_owned());
    }
    Ok(rustlyn_ide::document::decode_source(&output.stdout))
}

/// A unified patch with no lines of context for the change from `old` to
/// `new`.
fn text_patch(path: &str, old: &str, new: &str, added: bool, deleted: bool) -> String {
    let old_lines = split_lines(old);
    let new_lines = split_lines(new);
    let mut out = format!("diff --git a/{path} b/{path}\n");
    out.push_str(&if added {
        format!("new file mode 100644\n--- /dev/null\n+++ b/{path}\n")
    } else if deleted {
        format!("deleted file mode 100644\n--- a/{path}\n+++ /dev/null\n")
    } else {
        format!("--- a/{path}\n+++ b/{path}\n")
    });
    for change in crate::diff::changes(old, new, crate::diff::MAX_EDITS) {
        let (old_range, new_range) = (change.old_lines, change.lines);
        // git counts from the line before for an empty range.
        let start = |range: &std::ops::Range<usize>| {
            if range.is_empty() {
                range.start
            } else {
                range.start + 1
            }
        };
        out.push_str(&format!(
            "@@ -{},{} +{},{} @@\n",
            start(&old_range),
            old_range.len(),
            start(&new_range),
            new_range.len()
        ));
        for line in old_range {
            out.push('-');
            out.push_str(old_lines.get(line).copied().unwrap_or_default());
            out.push('\n');
        }
        for line in new_range {
            out.push('+');
            out.push_str(new_lines.get(line).copied().unwrap_or_default());
            out.push('\n');
        }
    }
    out
}

/// A revision (or a range of them) as git may be handed one: `base` comes
/// from whoever calls the tool, an MCP client among them, and git reads an
/// argument that starts with `-` as an option — `--output=<file>` makes
/// `git diff` write over any file the process can reach. A revision never
/// starts with one (`git check-ref-format`), so such a `base` is refused
/// rather than passed on.
///
/// # Errors
///
/// When `text` is empty, starts with `-` or holds a control character.
pub fn revision(text: &str) -> Result<&str, String> {
    if text.is_empty() || text.starts_with('-') || text.chars().any(char::is_control) {
        return Err(format!("{text:?} is not a revision"));
    }
    Ok(text)
}

/// The patch of a whole new file.
#[must_use]
pub fn added_file_patch(path: &str, text: &str) -> String {
    let lines: Vec<&str> = split_lines(text);
    let mut out = format!(
        "diff --git a/{path} b/{path}\nnew file mode 100644\n--- /dev/null\n+++ b/{path}\n@@ -0,0 +1,{} @@\n",
        lines.len()
    );
    for line in lines {
        out.push('+');
        out.push_str(line);
        out.push('\n');
    }
    out
}

/// Runs git in `root` and returns what it printed.
///
/// # Errors
///
/// When git cannot be run or exits with an error.
pub fn git(root: &str, args: &[&str]) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(args)
        .output()
        .map_err(|e| format!("git: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "git {}: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(rustlyn_ide::document::decode_lines(&output.stdout))
}

/// The project's compilation cache folder under `tool`'s cache: the second
/// run on a large project takes the compilation from there. The base is
/// `$<TOOL>_CACHE` (the tool's name upper-cased, `-` as `_`), else the
/// platform's cache folder.
#[must_use]
pub fn cache_dir(tool: &str, root: &str) -> Option<PathBuf> {
    let variable = format!("{}_CACHE", tool.to_uppercase().replace('-', "_"));
    let base = std::env::var_os(variable)
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("LOCALAPPDATA").map(|d| PathBuf::from(d).join(tool)))
        .or_else(|| std::env::var_os("XDG_CACHE_HOME").map(|d| PathBuf::from(d).join(tool)))
        .or_else(|| std::env::var_os("HOME").map(|d| PathBuf::from(d).join(".cache").join(tool)))?;
    let name = Path::new(root)
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    let dir = base.join(format!("{name}-{:016x}", fnv(root)));
    std::fs::create_dir_all(&dir).ok()?;
    Some(dir)
}

fn fnv(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The project root without links and with `/` (except on Windows), as the
/// session sees it.
#[must_use]
pub fn canonical_root(root: &str) -> String {
    let path = Path::new(root)
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(root));
    let text = path.to_string_lossy().into_owned();
    // `\\?\C:\…` on Windows: in such a path `/` is not a separator.
    text.strip_prefix(r"\\?\")
        .map_or(text.clone(), str::to_owned)
}

/// The project root, which must be a folder: a root that is not there is an
/// error, not a project with no changes.
///
/// # Errors
///
/// When `root` is not an existing folder.
pub fn existing_root(root: &str) -> Result<(), String> {
    if Path::new(root).is_dir() {
        Ok(())
    } else {
        Err(format!("{root}: not a folder"))
    }
}

/// A patch that is a patch: unified diff text, git's or plain. A text with no
/// line a diff is made of is not a patch with no changes but a wrong file.
///
/// # Errors
///
/// When the text is not empty and none of its lines belongs to a diff.
pub fn valid_patch(patch: &str) -> Result<(), String> {
    const MARKS: [&str; 12] = [
        "diff --git ",
        "diff ",
        "--- ",
        "+++ ",
        "@@ ",
        "@@@ ",
        "Binary files ",
        "GIT binary patch",
        "old mode ",
        "new mode ",
        "rename from ",
        "similarity index ",
    ];
    if patch.trim().is_empty()
        || patch
            .lines()
            .any(|line| MARKS.iter().any(|mark| line.starts_with(mark)))
    {
        return Ok(());
    }
    Err("the diff is not a unified diff (no ---, +++ or @@ lines)".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::diff::{Status, parse};
    use crate::blast::testing::Project;

    /// A root that is not a folder, and a patch with no line of a diff, are
    /// errors; an empty patch, and one of lines that are, are not.
    #[test]
    fn a_missing_root_and_a_garbage_patch_are_errors() {
        assert!(existing_root("/nowhere/at/all").is_err());
        let project = Project::new("setup-root", &[("A.cs", "class A { }\n")]);
        assert!(existing_root(&project.root()).is_ok());
        assert!(valid_patch("this is not a diff\nat all\n").is_err());
        assert!(valid_patch("").is_ok());
        assert!(valid_patch("  \n").is_ok());
        assert!(
            valid_patch("diff --git a/A.cs b/A.cs\nBinary files a/A.cs and b/A.cs differ\n")
                .is_ok()
        );
        assert!(valid_patch("--- a/A.cs\n+++ b/A.cs\n@@ -1 +1 @@\n-a\n+b\n").is_ok());
    }

    /// A patch is read by line: the lines that are not UTF-8 are Latin-1, as
    /// the file they are from is.
    #[test]
    fn a_patch_with_latin_1_lines_is_read() {
        let bytes = b"--- a/A.cs\n+++ b/A.cs\n@@ -1 +1 @@\n-// caf\xe9 \xc3\xa9\n+// caf\xe9 x\n";
        let text = rustlyn_ide::document::decode_lines(bytes);
        assert!(text.contains("// caf\u{e9} \u{c3}\u{a9}"), "{text:?}");
        let valid = b"-// caf\xc3\xa9\n";
        assert_eq!(
            rustlyn_ide::document::decode_lines(valid),
            "-// caf\u{e9}\n"
        );
    }

    #[test]
    fn working_copy_patch_with_new_files() {
        let project = Project::new("git", &[("A.cs", "class A {\n    void F() { }\n}\n")]);
        let root = project.root();
        let run = |args: &[&str]| git(&root, args).expect("git");
        run(&["init", "-q"]);
        run(&[
            "-c",
            "user.email=t@example.com",
            "-c",
            "user.name=t",
            "add",
            ".",
        ]);
        run(&[
            "-c",
            "user.email=t@example.com",
            "-c",
            "user.name=t",
            "commit",
            "-qm",
            "a",
        ]);
        project.write("A.cs", "class A {\n    void F() { G(); }\n}\n");
        project.write("B.cs", "class B { }\n");
        let files = parse(&git_patch(&root, None, false).expect("patch"));
        let summary: Vec<(&str, Status)> =
            files.iter().map(|f| (f.path.as_str(), f.status)).collect();
        assert_eq!(
            summary,
            vec![("A.cs", Status::Modified), ("B.cs", Status::Added)]
        );
    }

    /// `base` is the caller's, and an option in its place is not a revision:
    /// `--output=<file>` would have `git diff` write the file.
    #[test]
    fn a_base_that_is_an_option_is_refused() {
        let project = Project::new("git-option", &[("A.cs", "class A { }\n")]);
        let root = project.root();
        git(&root, &["init", "-q"]).expect("git");
        let target = format!("{root}/written.txt");
        let base = format!("--output={target}");
        assert!(git_patch(&root, Some(&base), false).is_err());
        assert!(!Path::new(&target).exists());
        assert!(revision("HEAD~2").is_ok());
        assert!(revision("main..feature").is_ok());
        assert!(revision("").is_err());
        assert!(revision("-n").is_err());
        assert!(revision("HEAD\n--output=x").is_err());
    }

    fn utf16(text: &str) -> Vec<u8> {
        let mut bytes = vec![0xFF, 0xFE];
        bytes.extend(text.encode_utf16().flat_map(u16::to_le_bytes));
        bytes
    }

    fn commit(root: &str, message: &str) {
        let run = |args: &[&str]| git(root, args).expect("git");
        run(&[
            "-c",
            "user.email=t@example.com",
            "-c",
            "user.name=t",
            "add",
            ".",
        ]);
        run(&[
            "-c",
            "user.email=t@example.com",
            "-c",
            "user.name=t",
            "commit",
            "-qm",
            message,
        ]);
    }

    const WIDE: &str =
        "class B {\n    public int M() { return 1; }\n    public int N() { return M(); }\n}\n";

    /// A source file git calls binary (UTF-16 has NUL bytes) is compared as
    /// text, in the working copy, in the index and between revisions.
    #[test]
    fn a_utf_16_source_is_compared_as_text() {
        let project = Project::new("git-wide", &[("A.cs", "class A { }\n")]);
        let root = project.root();
        git(&root, &["init", "-q"]).expect("git");
        project.write_bytes("W.cs", &utf16(WIDE));
        commit(&root, "one");
        let changed = WIDE.replace("return 1;", "return 2;");
        project.write_bytes("W.cs", &utf16(&changed));
        let summary = |patch: &str| -> Vec<(String, Vec<usize>)> {
            parse(patch)
                .into_iter()
                .map(|file| (file.path.clone(), file.new_lines()))
                .collect()
        };
        // The working copy.
        let (patch, notes) = git_patch_noted(&root, None, false).expect("patch");
        assert_eq!(
            summary(&patch),
            vec![("W.cs".to_owned(), vec![1])],
            "{patch}"
        );
        assert!(notes.is_empty(), "{notes:?}");
        // Staged, and nothing else staged.
        git(&root, &["add", "W.cs"]).expect("git");
        let (patch, _) = git_patch_noted(&root, None, true).expect("patch");
        assert_eq!(
            summary(&patch),
            vec![("W.cs".to_owned(), vec![1])],
            "{patch}"
        );
        // Between two revisions.
        commit(&root, "two");
        let (patch, _) = git_patch_noted(&root, Some("HEAD~1..HEAD"), false).expect("patch");
        let files = parse(&patch);
        assert_eq!(files.len(), 1, "{patch}");
        assert_eq!(
            files[0].blocks[0].removed,
            vec!["    public int M() { return 1; }"]
        );
        // A file that is new, and one that is gone.
        project.write_bytes("V.cs", &utf16("class V { }\n"));
        std::fs::remove_file(Path::new(&root).join("W.cs")).expect("removed");
        let (patch, _) = git_patch_noted(&root, None, false).expect("patch");
        let files = parse(&patch);
        let status: Vec<(&str, Status)> =
            files.iter().map(|f| (f.path.as_str(), f.status)).collect();
        assert_eq!(
            status,
            vec![("W.cs", Status::Deleted), ("V.cs", Status::Added)],
            "{patch}"
        );
    }

    /// Text that is not source stays what git says of it.
    #[test]
    fn a_binary_file_that_is_not_source_is_left_alone() {
        let project = Project::new("git-bin", &[("A.cs", "class A { }\n")]);
        let root = project.root();
        git(&root, &["init", "-q"]).expect("git");
        project.write_bytes("data.bin", &[0, 1, 2, 3]);
        commit(&root, "one");
        project.write_bytes("data.bin", &[0, 1, 2, 4]);
        let (patch, notes) = git_patch_noted(&root, None, false).expect("patch");
        assert!(parse(&patch).is_empty(), "{patch}");
        assert!(notes.is_empty());
    }

    /// The patch of two texts says what the lines were and are.
    #[test]
    fn a_text_patch_is_read_back_as_the_change() {
        let old = "a\nb\nc\nd\n";
        let new = "a\nB\nc\nd\ne\n";
        let files = parse(&text_patch("X.cs", old, new, false, false));
        assert_eq!(files.len(), 1);
        assert_eq!(files[0].new_lines(), vec![1, 4]);
        assert_eq!(files[0].old_text(new), old);
        let files = parse(&text_patch("X.cs", "", new, true, false));
        assert_eq!(files[0].status, Status::Added);
        assert_eq!(files[0].old_text(new), "");
        let files = parse(&text_patch("X.cs", old, "", false, true));
        assert_eq!(files[0].status, Status::Deleted);
        assert_eq!(files[0].old_text(""), old);
    }
}
