//! A change as the blast radius sees it: the files of a patch and the lines
//! that changed in them. The patch is a unified diff of several files, as
//! `git diff` prints it; each file is parsed by [`crate::diff::unified`].

use crate::diff::{Block, MAX_EDITS, UnifiedDiff, changes};

/// What happened to a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Added,
    Deleted,
    Modified,
}

impl Status {
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Added => "added",
            Self::Deleted => "deleted",
            Self::Modified => "modified",
        }
    }
}

/// One file of a patch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileDiff {
    /// Relative to the repository root, `/` between folders. A deleted
    /// file's is its old path.
    pub path: String,
    /// The path before a rename, when it differs.
    pub old_path: Option<String>,
    pub status: Status,
    pub blocks: Vec<Block>,
}

impl FileDiff {
    /// Lines of the new text the change added or replaced, from zero.
    #[must_use]
    pub fn new_lines(&self) -> Vec<usize> {
        self.blocks
            .iter()
            .flat_map(|b| b.new_lines.clone())
            .collect()
    }

    /// The old text from the new one: each block put back. Lines end in
    /// `\n`.
    #[must_use]
    pub fn old_text(&self, new_text: &str) -> String {
        if self.status == Status::Added {
            return String::new();
        }
        let lines: Vec<&str> = split_lines(new_text);
        let mut out: Vec<String> = Vec::with_capacity(lines.len());
        let mut at = 0usize;
        for block in &self.blocks {
            let start = block.new_lines.start.min(lines.len());
            out.extend(lines[at.min(start)..start].iter().map(|l| (*l).to_owned()));
            out.extend(block.removed.iter().cloned());
            at = block.new_lines.end.max(start);
        }
        if at < lines.len() {
            out.extend(lines[at..].iter().map(|l| (*l).to_owned()));
        }
        let mut text = out.join("\n");
        if new_text.ends_with('\n') || self.status == Status::Deleted {
            text.push('\n');
        }
        text
    }
}

/// The diff of two texts of one file: a change not on disk yet.
#[must_use]
pub fn between(path: &str, old: &str, new: &str) -> FileDiff {
    let old_lines = split_lines(old);
    let blocks = changes(old, new, MAX_EDITS)
        .into_iter()
        .map(|c| Block {
            kind: c.kind,
            new_lines: c.lines,
            removed: c
                .old_lines
                .clone()
                .filter_map(|i| old_lines.get(i).map(|l| (*l).to_owned()))
                .collect(),
            old_lines: c.old_lines,
        })
        .collect();
    FileDiff {
        path: path.to_owned(),
        old_path: None,
        status: if old.is_empty() {
            Status::Added
        } else {
            Status::Modified
        },
        blocks,
    }
}

/// Lines without their line break; a `\r` before `\n` is part of the break.
#[must_use]
pub fn split_lines(text: &str) -> Vec<&str> {
    let body = text.strip_suffix('\n').unwrap_or(text);
    if text.is_empty() {
        return Vec::new();
    }
    body.split('\n')
        .map(|l| l.strip_suffix('\r').unwrap_or(l))
        .collect()
}

/// A patch of several files. Files without a single changed line (a mode
/// change, a binary file) are skipped.
#[must_use]
pub fn parse(patch: &str) -> Vec<FileDiff> {
    let mut files = Vec::new();
    let mut section: Vec<&str> = Vec::new();
    let flush = |section: &mut Vec<&str>, files: &mut Vec<FileDiff>| {
        if let Some(file) = file_of(section) {
            files.push(file);
        }
        section.clear();
    };
    let lines: Vec<&str> = patch.split('\n').collect();
    for (i, raw) in lines.iter().enumerate() {
        let line = raw.strip_suffix('\r').unwrap_or(raw);
        // A new file: `diff --git`, or — in a patch without them — `--- `
        // before `+++ ` after the hunks of the previous file.
        let git = line.starts_with("diff --git ");
        let plain =
            line.starts_with("--- ") && lines.get(i + 1).is_some_and(|n| n.starts_with("+++ "));
        let has_hunk = section.iter().any(|l| l.starts_with("@@"));
        if (git && !section.is_empty()) || (plain && has_hunk) {
            flush(&mut section, &mut files);
        }
        section.push(line);
    }
    flush(&mut section, &mut files);
    files
}

fn file_of(section: &[&str]) -> Option<FileDiff> {
    let mut old: Option<String> = None;
    let mut new: Option<String> = None;
    let mut git_paths: Option<(String, String)> = None;
    for line in section {
        if line.starts_with("@@") {
            break;
        }
        if let Some(rest) = line.strip_prefix("diff --git ") {
            git_paths = git_header_paths(rest);
        } else if let Some(rest) = line.strip_prefix("--- ") {
            old = header_path(rest);
        } else if let Some(rest) = line.strip_prefix("+++ ") {
            new = header_path(rest);
        } else if let Some(rest) = line.strip_prefix("rename from ") {
            old = Some(rest.to_owned());
        } else if let Some(rest) = line.strip_prefix("rename to ") {
            new = Some(rest.to_owned());
        }
    }
    let saw_old_header = section.iter().any(|l| l.starts_with("--- "));
    let (old, new) = match (old, new, git_paths) {
        (None, None, Some((a, b))) => (Some(a), Some(b)),
        (old, new, _) => (old, new),
    };
    let status = match (&old, &new) {
        (None, Some(_)) if saw_old_header => Status::Added,
        (Some(_), None) => Status::Deleted,
        _ => Status::Modified,
    };
    let path = new.clone().or_else(|| old.clone())?;
    let old_path = old.filter(|o| Some(o) != new.as_ref() && new.is_some());
    let body = section.join("\n");
    let diff = UnifiedDiff::parse(&body);
    if diff.blocks.is_empty() {
        return None;
    }
    Some(FileDiff {
        path,
        old_path,
        status,
        blocks: diff.blocks,
    })
}

/// `a/x b/x` in a `diff --git` header — paths without quotes or spaces.
fn git_header_paths(rest: &str) -> Option<(String, String)> {
    let (a, b) = rest.split_once(" b/")?;
    Some((a.strip_prefix("a/").unwrap_or(a).to_owned(), b.to_owned()))
}

/// The path from `--- a/x` / `+++ b/x`; `/dev/null` is no file.
fn header_path(rest: &str) -> Option<String> {
    let rest = rest.split('\t').next().unwrap_or(rest).trim_end();
    if rest == "/dev/null" {
        return None;
    }
    let rest = rest.trim_matches('"');
    Some(
        rest.strip_prefix("a/")
            .or_else(|| rest.strip_prefix("b/"))
            .unwrap_or(rest)
            .to_owned(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const PATCH: &str = "diff --git a/Game/Pawn.cs b/Game/Pawn.cs
index 1111111..2222222 100644
--- a/Game/Pawn.cs
+++ b/Game/Pawn.cs
@@ -2,3 +2,3 @@ namespace Game {
     public class Pawn {
-        public int Health;
+        public long Health;
         public void Heal(int by) { Health += by; }
diff --git a/Game/New.cs b/Game/New.cs
new file mode 100644
--- /dev/null
+++ b/Game/New.cs
@@ -0,0 +1,2 @@
+class New {
+}
diff --git a/Game/Old.cs b/Game/Old.cs
deleted file mode 100644
--- a/Game/Old.cs
+++ /dev/null
@@ -1,2 +0,0 @@
-class Old {
-}
";

    #[test]
    fn patch_of_several_files() {
        let files = parse(PATCH);
        let summary: Vec<(&str, Status)> =
            files.iter().map(|f| (f.path.as_str(), f.status)).collect();
        assert_eq!(
            summary,
            vec![
                ("Game/Pawn.cs", Status::Modified),
                ("Game/New.cs", Status::Added),
                ("Game/Old.cs", Status::Deleted)
            ]
        );
        assert_eq!(files[0].new_lines(), vec![2]);
        assert_eq!(files[1].new_lines(), vec![0, 1]);
        assert_eq!(
            files[2].blocks[0].removed,
            vec!["class Old {".to_owned(), "}".to_owned()]
        );
    }

    #[test]
    fn old_text_from_new_text_and_blocks() {
        let files = parse(PATCH);
        let new = "namespace Game {\n    public class Pawn {\n        public long Health;\n        public void Heal(int by) { Health += by; }\n    }\n}\n";
        let old = files[0].old_text(new);
        assert_eq!(old, new.replace("long Health", "int Health"));
        assert_eq!(files[2].old_text(""), "class Old {\n}\n");
        assert_eq!(files[1].old_text("class New {\n}\n"), "");
    }

    #[test]
    fn diff_of_two_texts() {
        let old = "a\nb\nc\n";
        let new = "a\nB\nc\nd\n";
        let file = between("x.cs", old, new);
        assert_eq!(file.new_lines(), vec![1, 3]);
        assert_eq!(file.old_text(new), old);
    }

    #[test]
    fn patch_without_git_headers() {
        let patch = "--- a/A.cs\n+++ b/A.cs\n@@ -1 +1 @@\n-a\n+b\n--- a/B.cs\n+++ b/B.cs\n@@ -1 +1 @@\n-c\n+d\n";
        let files = parse(patch);
        assert_eq!(
            files.iter().map(|f| f.path.as_str()).collect::<Vec<_>>(),
            vec!["A.cs", "B.cs"]
        );
    }
}
