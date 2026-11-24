//! A file's diff parsed from the unified format git and code review services
//! print.
//!
//! Parsed rather than recomputed: line numbers in review comments are tied to
//! the service's own diff, and change bars should match what a reviewer sees
//! there. Neither version of the file is needed — the removed lines are in
//! the diff.

use std::ops::Range;

use super::lines::Kind;

/// A change: old lines replaced by new ones. Lines from zero; a `Deleted`
/// block has an empty new range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    pub kind: Kind,
    pub new_lines: Range<usize>,
    pub old_lines: Range<usize>,
    pub removed: Vec<String>,
}

/// A parsed diff of one file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UnifiedDiff {
    pub blocks: Vec<Block>,
    /// The ranges of new lines the diff shows, context included.
    pub hunks: Vec<Range<usize>>,
}

impl UnifiedDiff {
    pub fn additions(&self) -> usize {
        self.blocks.iter().map(|b| b.new_lines.len()).sum()
    }

    pub fn deletions(&self) -> usize {
        self.blocks.iter().map(|b| b.old_lines.len()).sum()
    }

    /// Lines split on `\n`, a trailing `\r` dropped.
    #[must_use]
    pub fn parse(text: &str) -> UnifiedDiff {
        let mut result = UnifiedDiff::default();
        let (mut old_pos, mut new_pos) = (0usize, 0usize);
        let mut hunk_start = 0usize;
        let mut in_hunk = false;

        let mut pending_old: Option<usize> = None;
        let mut pending_new = 0usize;
        let mut removed: Vec<String> = Vec::new();
        let mut added = 0usize;

        fn flush(
            result: &mut UnifiedDiff,
            pending_old: &mut Option<usize>,
            pending_new: usize,
            removed: &mut Vec<String>,
            added: &mut usize,
        ) {
            let Some(old_start) = pending_old.take() else {
                return;
            };
            let new_lines = pending_new..pending_new + *added;
            let old_lines = old_start..old_start + removed.len();
            let kind = if new_lines.is_empty() {
                Kind::Deleted
            } else if old_lines.is_empty() {
                Kind::Added
            } else {
                Kind::Modified
            };
            result.blocks.push(Block {
                kind,
                new_lines,
                old_lines,
                removed: std::mem::take(removed),
            });
            *added = 0;
        }

        for raw in text.split('\n') {
            let line = raw.strip_suffix('\r').unwrap_or(raw);
            let Some(marker) = line.chars().next() else {
                continue;
            };
            match marker {
                '@' => {
                    let Some((old_start, new_start)) = hunk_header(line) else {
                        continue;
                    };
                    // Close the previous hunk.
                    flush(
                        &mut result,
                        &mut pending_old,
                        pending_new,
                        &mut removed,
                        &mut added,
                    );
                    if in_hunk {
                        result.hunks.push(hunk_start..hunk_start.max(new_pos));
                    }
                    old_pos = old_start;
                    new_pos = new_start;
                    hunk_start = new_pos;
                    in_hunk = true;
                }
                ' ' => {
                    flush(
                        &mut result,
                        &mut pending_old,
                        pending_new,
                        &mut removed,
                        &mut added,
                    );
                    old_pos += 1;
                    new_pos += 1;
                }
                '-' => {
                    if !in_hunk {
                        continue;
                    }
                    if pending_old.is_none() {
                        pending_old = Some(old_pos);
                        pending_new = new_pos;
                    }
                    removed.push(line[1..].to_owned());
                    old_pos += 1;
                }
                '+' => {
                    if !in_hunk {
                        continue;
                    }
                    if pending_old.is_none() {
                        pending_old = Some(old_pos);
                        pending_new = new_pos;
                    }
                    added += 1;
                    new_pos += 1;
                }
                // "\ No newline at end of file" and file headers
                _ => continue,
            }
        }
        flush(
            &mut result,
            &mut pending_old,
            pending_new,
            &mut removed,
            &mut added,
        );
        if in_hunk {
            result.hunks.push(hunk_start..hunk_start.max(new_pos));
        }
        result
    }

    // MARK: Mapping lines

    /// The block a new line belongs to: the one holding it when it changed, or
    /// a `Deleted` one removed right before it.
    pub fn block_at_new_line(&self, line: usize) -> Option<usize> {
        self.blocks
            .iter()
            .position(|b| b.new_lines.contains(&line))
            .or_else(|| {
                self.blocks
                    .iter()
                    .position(|b| b.new_lines.is_empty() && b.new_lines.start == line)
            })
    }

    /// The old number of an unchanged line; `None` when it was added or changed.
    pub fn old_line(&self, line: usize) -> Option<usize> {
        let mut delta: isize = 0;
        for block in &self.blocks {
            if block.new_lines.contains(&line) {
                return None;
            }
            if block.new_lines.end > line
                || (block.new_lines.is_empty() && block.new_lines.start > line)
            {
                break;
            }
            delta += block.old_lines.len() as isize - block.new_lines.len() as isize;
        }
        Some((line as isize + delta) as usize)
    }

    /// Where in the new text to show what is tied to an old line: an unchanged
    /// line at its new place, a removed one where its block was.
    pub fn new_line(&self, line: usize) -> isize {
        let mut delta: isize = 0;
        for block in &self.blocks {
            if block.old_lines.contains(&line) {
                return block.new_lines.start as isize;
            }
            if block.old_lines.start > line {
                break;
            }
            delta += block.new_lines.len() as isize - block.old_lines.len() as isize;
        }
        line as isize + delta
    }
}

/// `@@ -a,b +c,d @@ …`, the counts optional. Returns zero-based starts: for
/// an empty side (`-0,0`, `+5,0`) the number is the line the insertion
/// follows.
fn hunk_header(line: &str) -> Option<(usize, usize)> {
    let parts: Vec<&str> = line.split(' ').filter(|part| !part.is_empty()).collect();
    if parts.len() < 3 || parts[0] != "@@" {
        return None;
    }
    let (old_start, old_count) = range(parts[1], '-')?;
    let (new_start, new_count) = range(parts[2], '+')?;
    let start =
        |start: i64, count: i64| (if count == 0 { start } else { start - 1 }).max(0) as usize;
    Some((start(old_start, old_count), start(new_start, new_count)))
}

/// An optionally signed run of digits, nothing else.
fn integer(text: &str) -> Option<i64> {
    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

fn range(token: &str, sign: char) -> Option<(i64, i64)> {
    let rest = token.strip_prefix(sign)?;
    let numbers: Vec<&str> = rest.split(',').filter(|part| !part.is_empty()).collect();
    let start = integer(numbers.first()?)?;
    let count = if numbers.len() > 1 {
        integer(numbers[1]).unwrap_or(1)
    } else {
        1
    };
    Some((start, count))
}

#[cfg(test)]
mod tests {
    use super::*;
    use Kind::*;

    #[test]
    fn merge_request_diff() {
        // Old file: a b c d e f g h i j (lines 1–10).
        // New:      a b C d e X f g h Y j  — c→C, X inserted, i replaced by Y.
        let text = "@@ -1,6 +1,7 @@\n a\n b\n-c\n+C\n d\n e\n+X\n f\n@@ -7,4 +8,4 @@ fn context\n g\n h\n-i\n+Y\n j\n\\ No newline at end of file";
        let diff = UnifiedDiff::parse(text);
        assert_eq!(
            diff.blocks.iter().map(|b| b.kind).collect::<Vec<_>>(),
            [Modified, Added, Modified],
            "block kinds"
        );
        assert_eq!(
            diff.blocks
                .iter()
                .map(|b| b.new_lines.clone())
                .collect::<Vec<_>>(),
            [2..3, 5..6, 9..10]
        );
        assert_eq!(
            diff.blocks
                .iter()
                .map(|b| b.old_lines.clone())
                .collect::<Vec<_>>(),
            [2..3, 5..5, 8..9]
        );
        assert_eq!(
            diff.blocks[0].removed,
            ["c"],
            "a removed line keeps its text"
        );
        assert_eq!((diff.additions(), diff.deletions()), (3, 2), "+3 -2");
        assert_eq!(diff.hunks, [0..7, 7..11], "lines the diff shows");

        assert_eq!(
            diff.old_line(0),
            Some(0),
            "an unchanged line before the edits keeps its number"
        );
        assert_eq!(diff.old_line(2), None, "a changed line has no old number");
        assert_eq!(
            diff.old_line(6),
            Some(5),
            "after X was inserted, new f(6) is old f(5)"
        );
        assert_eq!(diff.old_line(10), Some(9), "the last line, j");
        assert_eq!(diff.new_line(5), 6, "old f shows at its new place");
        assert_eq!(
            diff.new_line(8),
            9,
            "removed i shows at the block that replaced it"
        );
        assert_eq!(diff.block_at_new_line(5), Some(1));
        assert_eq!(diff.block_at_new_line(0), None);

        let new_file = UnifiedDiff::parse("@@ -0,0 +1,3 @@\n+x\n+y\n+z\n");
        assert_eq!(
            new_file.blocks,
            [Block {
                kind: Added,
                new_lines: 0..3,
                old_lines: 0..0,
                removed: vec![]
            }],
            "a new file"
        );
        let deleted = UnifiedDiff::parse("@@ -1,2 +0,0 @@\n-x\n-y\n");
        assert!(
            deleted.blocks[0].removed == ["x", "y"] && deleted.blocks[0].kind == Deleted,
            "a deleted file"
        );
        assert!(
            UnifiedDiff::parse("").blocks.is_empty(),
            "an empty diff has no blocks"
        );
        let crlf = UnifiedDiff::parse("@@ -1,2 +1,2 @@\r\n a\r\n-b\r\n+B\r\n");
        assert!(
            crlf.blocks.len() == 1
                && crlf.blocks[0].removed == ["b"]
                && crlf.blocks[0].new_lines == (1..2),
            "CRLF"
        );
    }
}
