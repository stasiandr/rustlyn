//! Which lines of a text changed against another, for change bars beside
//! the line numbers and for mapping positions across an edit.
//!
//! Lines are split on `\n`, a trailing `\r` dropped, so a file with CRLF on
//! disk and LF in the repository is not all changed. Common leading and
//! trailing lines are cut first; what is left goes through Myers' greedy
//! algorithm, capped at [`MAX_EDITS`].

use std::collections::HashMap;
use std::ops::Range;

/// How lines changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Kind {
    Added = 0,
    Modified = 1,
    Deleted = 2,
}

/// A change in the new text's coordinates, lines from zero. A `Deleted`
/// change has an empty range: its lines were removed before `lines.start`.
/// `old_lines` are the lines of the old text the change replaced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    pub kind: Kind,
    pub lines: Range<usize>,
    pub old_lines: Range<usize>,
}

/// How many edits Myers may look for: past this, time O((N+M)·D) and memory
/// O(D²) stop being cheap. Beyond it everything that differs is one change —
/// a file rewritten from scratch looks rewritten from scratch.
pub const MAX_EDITS: usize = 2000;

/// The changes that turn `old` into `new`.
#[must_use]
pub fn changes(old: &str, new: &str, max_edits: usize) -> Vec<Change> {
    changes_of_lines(&lines(old.as_bytes()), &lines(new.as_bytes()), max_edits)
}

/// Lines split on `\n`, the way an editor numbers them. A trailing `\r` is
/// dropped: a file with CRLF on disk and LF in the repository
/// (`core.autocrlf`) is not all changed.
#[must_use]
pub fn lines(text: &[u8]) -> Vec<&[u8]> {
    let mut result = Vec::with_capacity(text.len() / 32 + 1);
    let mut start = 0;
    for (i, &byte) in text.iter().enumerate() {
        if byte == b'\n' {
            result.push(trimming_cr(&text[start..i]));
            start = i + 1;
        }
    }
    result.push(trimming_cr(&text[start..]));
    result
}

fn trimming_cr(line: &[u8]) -> &[u8] {
    match line.split_last() {
        Some((b'\r', rest)) => rest,
        _ => line,
    }
}

/// The changes that turn lines `a` into lines `b`.
#[must_use]
pub fn changes_of_lines<A: AsRef<[u8]>, B: AsRef<[u8]>>(
    a: &[A],
    b: &[B],
    max_edits: usize,
) -> Vec<Change> {
    // Cut the common start and end first: an edit is usually a couple of
    // places in a large file, and only a few lines reach Myers.
    let mut prefix = 0;
    while prefix < a.len() && prefix < b.len() && a[prefix].as_ref() == b[prefix].as_ref() {
        prefix += 1;
    }
    let mut suffix = 0;
    while suffix < a.len() - prefix
        && suffix < b.len() - prefix
        && a[a.len() - 1 - suffix].as_ref() == b[b.len() - 1 - suffix].as_ref()
    {
        suffix += 1;
    }

    let n = a.len() - prefix - suffix;
    let m = b.len() - prefix - suffix;
    if n == 0 && m == 0 {
        return Vec::new();
    }

    // Lines to numbers: Myers then compares i32s, not bytes.
    let mut ids: HashMap<&[u8], i32> = HashMap::new();
    let x: Vec<i32> = a[prefix..prefix + n]
        .iter()
        .map(|line| {
            let next = ids.len() as i32;
            *ids.entry(line.as_ref()).or_insert(next)
        })
        .collect();
    let y: Vec<i32> = b[prefix..prefix + m]
        .iter()
        .map(|line| {
            let next = ids.len() as i32;
            *ids.entry(line.as_ref()).or_insert(next)
        })
        .collect();

    let mut deleted = vec![false; n];
    let mut inserted = vec![false; m];
    if !myers(&x, &y, max_edits, &mut deleted, &mut inserted) {
        deleted = vec![true; n];
        inserted = vec![true; m];
    }
    hunks(&deleted, &inserted, prefix)
}

// MARK: Myers

/// Myers' greedy algorithm (1986): the shortest path through the edit grid,
/// where a step right deletes a line of the old text, a step down inserts a
/// line of the new one, and a diagonal is a match. Marks the deleted and
/// inserted lines; `false` when more than `limit` edits are needed.
fn myers(a: &[i32], b: &[i32], limit: usize, deleted: &mut [bool], inserted: &mut [bool]) -> bool {
    let n = a.len() as isize;
    let m = b.len() as isize;
    let max_d = (n + m).min(limit as isize);
    let offset = max_d + 1;
    // v[k]: the furthest x on diagonal k = x - y; -1 when unreachable.
    let mut v = vec![-1isize; (2 * max_d + 3) as usize];
    // v[-d..=d] after every step d, for the way back.
    let mut trace: Vec<Vec<i32>> = Vec::new();
    let mut total: isize = -1;

    'search: for d in 0..=max_d {
        let mut k = -d;
        while k <= d {
            if k >= -m && k <= n {
                let mut x: isize;
                if d == 0 {
                    x = 0;
                } else if let Some((px, _)) = step(k, d, n, m, |k| v[(offset + k) as usize]) {
                    x = px;
                } else {
                    v[(offset + k) as usize] = -1;
                    k += 2;
                    continue;
                }
                let mut y = x - k;
                while x < n && y < m && a[x as usize] == b[y as usize] {
                    x += 1;
                    y += 1;
                }
                v[(offset + k) as usize] = x;
                if x == n && y == m {
                    total = d;
                    break 'search;
                }
            }
            k += 2;
        }
        trace.push(
            v[(offset - d) as usize..=(offset + d) as usize]
                .iter()
                .map(|&x| x as i32)
                .collect(),
        );
    }
    if total < 0 {
        return false;
    }

    // Back from (n, m) to (0, 0), making the same choice of move.
    let (mut x, mut y) = (n, m);
    let mut d = total;
    while d > 0 {
        let k = x - y;
        let previous = &trace[(d - 1) as usize];
        let Some((px, down)) = step(k, d, n, m, |k| previous[(k + d - 1) as usize] as isize) else {
            return false;
        };
        if down {
            inserted[(px - k - 1) as usize] = true;
            x = px;
            y = px - k - 1;
        } else {
            deleted[(px - 1) as usize] = true;
            x = px - 1;
            y = px - k;
        }
        d -= 1;
    }
    let _ = (x, y);
    true
}

/// Which move reaches diagonal k at step d: down from k+1 or right from k-1,
/// whichever goes further. Moves off the grid are discarded, or the
/// "furthest" point could lie past the end of the text. `at(k)` is v[k]
/// after step d-1. Returns x right after the move.
#[inline(always)]
fn step(
    k: isize,
    d: isize,
    n: isize,
    m: isize,
    at: impl Fn(isize) -> isize,
) -> Option<(isize, bool)> {
    let mut best: Option<(isize, bool)> = None;
    if k != d && k < n {
        let px = at(k + 1);
        if px >= 0 && px - k <= m {
            best = Some((px, true));
        }
    }
    if k != -d && k > -m {
        let px = at(k - 1);
        if px >= 0 && px < n && px + 1 > best.map_or(-1, |b| b.0) {
            best = Some((px + 1, false));
        }
    }
    best
}

// MARK: Changes

/// Between two matching lines the deleted and inserted ones come in runs;
/// each such gap is one change.
fn hunks(deleted: &[bool], inserted: &[bool], offset: usize) -> Vec<Change> {
    let mut result = Vec::new();
    let (n, m) = (deleted.len(), inserted.len());
    let (mut i, mut j) = (0, 0);
    while i < n || j < m {
        let is_deleted = i < n && deleted[i];
        let is_inserted = j < m && inserted[j];
        if !is_deleted && !is_inserted {
            i += 1;
            j += 1;
            continue;
        }
        let (i0, j0) = (i, j);
        while i < n && deleted[i] {
            i += 1;
        }
        while j < m && inserted[j] {
            j += 1;
        }
        let lines = (offset + j0)..(offset + j);
        let kind = if lines.is_empty() {
            Kind::Deleted
        } else if i == i0 {
            Kind::Added
        } else {
            Kind::Modified
        };
        result.push(Change {
            kind,
            lines,
            old_lines: (offset + i0)..(offset + i),
        });
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Old ranges are checked separately; this is the kind and the new lines.
    fn diff(old: &str, new: &str) -> Vec<(Kind, Range<usize>)> {
        diff_limited(old, new, MAX_EDITS)
    }
    fn diff_limited(old: &str, new: &str, max: usize) -> Vec<(Kind, Range<usize>)> {
        changes(old, new, max)
            .into_iter()
            .map(|c| (c.kind, c.lines))
            .collect()
    }
    use Kind::*;

    #[test]
    fn line_changes() {
        let with_old = changes("1\n2\n3\n4\n5\n6\n7\n", "1\nX\n3\n4\n5\n7\nY\n", MAX_EDITS);
        assert_eq!(
            with_old
                .iter()
                .map(|c| c.old_lines.clone())
                .collect::<Vec<_>>(),
            [1..2, 5..6, 7..7],
            "old lines: the replaced one, the deleted one, none for an addition"
        );
        assert!(
            diff("a\nb\nc\n", "a\nb\nc\n").is_empty(),
            "equal texts: no changes"
        );
        assert_eq!(
            diff("a\nc\n", "a\nb\nc\n"),
            [(Added, 1..2)],
            "an inserted line is added"
        );
        assert_eq!(
            diff("a\nb\nc\n", "a\nc\n"),
            [(Deleted, 1..1)],
            "a removed line is deleted before line 1"
        );
        assert_eq!(
            diff("a\nb\nc\n", "a\nB\nc\n"),
            [(Modified, 1..2)],
            "an edited line is modified"
        );
        assert_eq!(
            diff("a\nb", "a"),
            [(Deleted, 1..1)],
            "removing the last line is deleted past the end"
        );
        assert_eq!(
            diff("", "x\ny\n"),
            [(Added, 0..2)],
            "a new file is all added"
        );
        assert!(
            diff("a\r\nb\r\n", "a\nb\n").is_empty(),
            "CRLF against LF is not a change"
        );
        assert_eq!(
            diff("1\n2\n3\n4\n5\n6\n7\n", "1\nX\n3\n4\n5\n7\nY\n"),
            [(Modified, 1..2), (Deleted, 5..5), (Added, 6..7)],
            "several changes of different kinds"
        );
        assert_eq!(
            diff("a\nb\n", "a\nb\nc\nd\n"),
            [(Added, 2..4)],
            "appended at the end"
        );
        assert_eq!(
            diff_limited("a\nb\nc\nd\n", "x\ny\n", 2),
            [(Modified, 0..2)],
            "more edits than the limit: one change for everything that differs"
        );
    }

    fn lcs_length(a: &[&str], b: &[&str]) -> usize {
        let mut dp = vec![0; b.len() + 1];
        for x in a {
            let mut prev = 0;
            for j in 0..b.len() {
                let saved = dp[j + 1];
                dp[j + 1] = if *x == b[j] {
                    prev + 1
                } else {
                    dp[j + 1].max(dp[j])
                };
                prev = saved;
            }
        }
        dp[b.len()]
    }

    /// Minimality: the unchanged lines of the new text are a common
    /// subsequence with the old one, and the longest (checked against an LCS
    /// by dynamic programming on random texts).
    #[test]
    fn minimal_on_random_texts() {
        let mut seed: u64 = 0x2545F4914F6CDD1D;
        let mut next = |bound: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % bound
        };
        let alphabet = ["a", "b", "c"];
        let mut mismatches = 0;
        for _ in 0..400 {
            let a: Vec<&str> = (0..next(13)).map(|_| alphabet[next(3) as usize]).collect();
            let b: Vec<&str> = (0..next(13)).map(|_| alphabet[next(3) as usize]).collect();
            let found = changes(&a.join("\n"), &b.join("\n"), MAX_EDITS);
            let mut changed = std::collections::HashSet::new();
            for c in &found {
                changed.extend(c.lines.clone());
            }
            let kept: Vec<&str> = (0..b.len().max(1))
                .filter(|i| !changed.contains(i))
                .map(|i| if b.is_empty() { "" } else { b[i] })
                .collect();
            let a_lines: Vec<&str> = if a.is_empty() { vec![""] } else { a.clone() };
            let b_lines: Vec<&str> = if b.is_empty() { vec![""] } else { b.clone() };
            let mut it = a_lines.iter();
            let is_subsequence = kept.iter().all(|line| it.any(|next| next == line));
            if !is_subsequence || kept.len() != lcs_length(&a_lines, &b_lines) {
                mismatches += 1;
            }
        }
        assert_eq!(
            mismatches, 0,
            "on 400 random pairs the diff is minimal and correct"
        );
    }

    #[test]
    fn large_file_is_fast() {
        let old: Vec<String> = (0..100_000)
            .map(|i| format!("let value{i} = compute({i})"))
            .collect();
        let mut new = old.clone();
        for i in (5_000..100_000).step_by(10_000) {
            new[i] = format!("// changed {i}");
        }
        new.insert(50_000, "// inserted".into());
        let started = std::time::Instant::now();
        let found = changes(&old.join("\n"), &new.join("\n"), MAX_EDITS);
        let elapsed = started.elapsed();
        assert_eq!(found.len(), 11, "11 changes found in a large file");
        assert!(
            elapsed.as_millis() < 1000,
            "a diff of 100k lines takes under a second ({elapsed:?})"
        );
    }
}
