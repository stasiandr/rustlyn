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
    if !staged {
        let untracked = git(
            root,
            &["ls-files", "--others", "--exclude-standard", "--", "*.cs"],
        )?;
        for path in untracked.lines().filter(|l| !l.is_empty()) {
            let Ok(text) = std::fs::read_to_string(Path::new(root).join(path)) else {
                continue;
            };
            patch += &added_file_patch(path, &text);
        }
    }
    Ok(patch)
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
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::diff::{Status, parse};
    use crate::blast::testing::Project;

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
}
