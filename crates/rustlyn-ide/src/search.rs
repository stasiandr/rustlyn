//! Navigate To: finding a declaration by typing some of its name.
//!
//! What a person types into a "go to symbol" box is rarely the name. It is
//! the start of it, or its capitals — `GTD` for `GoToDefinition` — or the
//! start of each word — `goToDef`, `gtDef` — or a word from the middle, or
//! the name with a letter wrong. Roslyn's pattern matcher accepts all of
//! these and, as important, ranks them: an exact match above a prefix,
//! a prefix above a match of the capitals, the capitals above a run of
//! letters from the middle, and all of those above a near miss. Within one
//! kind of match, a match in the case typed goes first. This is that
//! matcher, over the project index.
//!
//! A pattern with dots in it — `Canvas.Draw` — matches the last part
//! against the name and each part before it against the containing type
//! or namespace. A pattern with spaces is several words, each of which has
//! to match.
//!
//! The index can hold a few hundred thousand declarations, and the list is
//! filtered again on every keystroke. So nothing is allocated per name:
//! each is compared as bytes where it lies, cheapest test first, and the
//! character ranges to highlight are worked out only for the few results
//! that will be shown.

use std::cell::RefCell;

use crate::index::ProjectIndex;
use crate::outline::DeclarationKind;

/// What to search among.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(u8)]
pub enum SearchKind {
    /// Types, members and files.
    #[default]
    All = 0,
    Types = 1,
    /// Methods, properties, fields, events and the rest of what is inside a
    /// type.
    Members = 2,
    /// The project's files, by file name.
    Files = 3,
}

/// How well a pattern matched a name, best first. The order is Roslyn's.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u8)]
pub enum MatchKind {
    /// The whole name: `Canvas` for `Canvas`.
    Exact = 0,
    /// The start of the name: `Can` for `Canvas`.
    Prefix,
    /// The start of a word inside the name: `Def` for `GoToDefinition`.
    StartOfWord,
    /// The start of every word: `GTD` for `GoToDefinition`.
    CamelCaseExact,
    /// The start of the first words: `GoT` for `GoToDefinition`.
    CamelCasePrefix,
    /// The start of some words from the first on, skipping others: `GD`
    /// for `GoToDefinition`.
    CamelCaseNonContiguousPrefix,
    /// The start of consecutive words from the middle: `TD` for
    /// `GoToDefinition`.
    CamelCaseSubstring,
    /// The start of some words from the middle, skipping others.
    CamelCaseNonContiguousSubstring,
    /// Letters from anywhere in the name: `efin` for `GoToDefinition`.
    Substring,
    /// The name with one letter wrong, missing, extra or swapped: `Canvsa`
    /// for `Canvas`.
    Fuzzy,
}

/// What a result is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Target {
    /// An entry of the index, by its id.
    Entry(u32),
    /// A file of the index, by its position in [`ProjectIndex::files`].
    File(u32),
}

/// One result.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Hit {
    pub target: Target,
    pub kind: MatchKind,
    /// Whether every letter matched in the case it was typed in.
    pub case_sensitive: bool,
    /// The byte ranges of the name that matched, for highlighting: start
    /// and end, in order, not overlapping. Empty for a fuzzy match.
    pub ranges: Vec<(u32, u32)>,
}

/// How a pattern matched one name.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Quality {
    kind: MatchKind,
    case_sensitive: bool,
}

impl Quality {
    /// Lower is better.
    const fn rank(self) -> u16 {
        (self.kind as u16) * 2 + !self.case_sensitive as u16
    }
}

/// A pattern, split up once so that matching each name does not have to.
#[derive(Clone, Debug)]
pub struct Pattern {
    /// The words the name has to match, each as typed.
    words: Vec<Word>,
    /// What comes before the last dot, one part per dot, innermost last.
    containers: Vec<Word>,
    /// Room to work in, kept from one name to the next so that matching a
    /// name allocates nothing.
    scratch: RefCell<Scratch>,
}

#[derive(Clone, Debug, Default)]
struct Scratch {
    humps: Vec<(usize, usize)>,
    matched: Vec<(usize, usize, usize)>,
}

#[derive(Clone, Debug)]
struct Word {
    text: Vec<u8>,
    lower: Vec<u8>,
}

impl Word {
    fn new(text: &str) -> Self {
        Self {
            text: text.as_bytes().to_vec(),
            lower: text.to_ascii_lowercase().into_bytes(),
        }
    }
}

impl Pattern {
    /// The pattern as typed. `None` when there is nothing in it to match.
    #[must_use]
    pub fn new(text: &str) -> Option<Self> {
        let text = text.trim();
        let (containers, name) = match text.rsplit_once('.') {
            Some((containers, name)) => (containers, name),
            None => ("", text),
        };
        let words: Vec<Word> = name.split_whitespace().map(Word::new).collect();
        let containers: Vec<Word> = containers
            .split('.')
            .map(str::trim)
            .filter(|part| !part.is_empty())
            .map(Word::new)
            .collect();
        if words.is_empty() && containers.is_empty() {
            return None;
        }
        Some(Self {
            words,
            containers,
            scratch: RefCell::new(Scratch::default()),
        })
    }

    /// How the pattern matches a name in a container, with the ranges of
    /// the name that matched pushed onto `ranges`. The container is the
    /// qualified name of the type or namespace the name is in, and only
    /// matters to a dotted pattern.
    fn matches(
        &self,
        name: &str,
        container: Option<&str>,
        ranges: Option<&mut Vec<(u32, u32)>>,
    ) -> Option<Quality> {
        let mut scratch = self.scratch.borrow_mut();
        let scratch = &mut *scratch;
        let mut worst: Option<Quality> = None;
        let mut ranges = ranges;
        // The name first: it rules out far more than the container does.
        for word in &self.words {
            let quality = match_word(word, name.as_bytes(), ranges.as_deref_mut(), scratch)?;
            worst = Some(match worst {
                Some(worst) if worst.rank() >= quality.rank() => worst,
                _ => quality,
            });
        }
        if !self.containers.is_empty() && !self.containers_match(container.unwrap_or(""), scratch) {
            return None;
        }
        if let Some(ranges) = ranges {
            ranges.sort_unstable();
            // Two words can match the same letters; a highlight is once.
            let mut merged: Vec<(u32, u32)> = Vec::with_capacity(ranges.len());
            for &(start, end) in ranges.iter() {
                match merged.last_mut() {
                    Some(last) if start <= last.1 => last.1 = last.1.max(end),
                    _ => merged.push((start, end)),
                }
            }
            *ranges = merged;
        }
        // `Canvas.` with nothing after the dot: everything in `Canvas`.
        Some(worst.unwrap_or(Quality {
            kind: MatchKind::Exact,
            case_sensitive: true,
        }))
    }

    /// Whether each part before the last dot matches a part of the
    /// container, innermost to outermost, in that order.
    fn containers_match(&self, container: &str, scratch: &mut Scratch) -> bool {
        let mut parts = container.rsplit('.');
        'pattern: for word in self.containers.iter().rev() {
            for part in parts.by_ref() {
                if match_word(word, part.as_bytes(), None, scratch)
                    .is_some_and(|quality| quality.kind != MatchKind::Fuzzy)
                {
                    continue 'pattern;
                }
            }
            return false;
        }
        true
    }
}

// MARK: - matching one name, for completion filtering

/// How a pattern matched one name: the kind of match, whether the case
/// matched too, and the byte ranges of the name that matched.
pub type NameMatch = (MatchKind, bool, Vec<(u32, u32)>);

impl Pattern {
    /// How the pattern matches `name` on its own: the kind of match,
    /// whether the case matched too, and the byte ranges of `name` that
    /// matched. `None` when it does not match. What completion filters and
    /// orders its items by, as Roslyn's pattern matcher does.
    #[must_use]
    pub fn match_name(&self, name: &str) -> Option<NameMatch> {
        let mut ranges = Vec::new();
        let quality = self.matches(name, None, Some(&mut ranges))?;
        Some((quality.kind, quality.case_sensitive, ranges))
    }
}

/// Searches the index: every declaration, or file, whose name the pattern
/// matches, best first, at most `limit` of them.
#[must_use]
pub fn search(index: &ProjectIndex, pattern: &str, kind: SearchKind, limit: usize) -> Vec<Hit> {
    let Some(pattern) = Pattern::new(pattern) else {
        return Vec::new();
    };
    if limit == 0 {
        return Vec::new();
    }

    // First, which names match and how well — without the ranges, which
    // cost an allocation each and matter only for what is shown.
    let mut found: Vec<Found> = Vec::new();
    if kind != SearchKind::Files {
        for (id, entry) in index.entries().iter().enumerate() {
            let declaration = &entry.declaration;
            let is_type = declaration.kind.is_type();
            let wanted = match kind {
                SearchKind::All => declaration.kind != DeclarationKind::Namespace,
                SearchKind::Types => is_type,
                SearchKind::Members => !is_type && declaration.kind != DeclarationKind::Namespace,
                SearchKind::Files => false,
            };
            if !wanted {
                continue;
            }
            if let Some(quality) =
                pattern.matches(&declaration.name, declaration.container.as_deref(), None)
            {
                found.push(Found {
                    rank: quality.rank(),
                    length: declaration.name.len() as u32,
                    quality,
                    target: Target::Entry(id as u32),
                });
            }
        }
    }
    if matches!(kind, SearchKind::All | SearchKind::Files) && pattern.containers.is_empty() {
        for (id, file) in index.files().iter().enumerate() {
            let Some(name) = file.path.file_name() else {
                continue;
            };
            let name = name.to_string_lossy();
            if let Some(quality) = pattern.matches(&name, None, None) {
                found.push(Found {
                    rank: quality.rank(),
                    length: name.len() as u32,
                    quality,
                    target: Target::File(id as u32),
                });
            }
        }
    }

    // Then the best `limit`, in order: how well, then the shorter name —
    // `Canvas` before `CanvasRenderer` for `Can` — then the name itself.
    let name_of = |target: Target| -> std::borrow::Cow<'_, str> {
        match target {
            Target::Entry(id) => index
                .entry(id)
                .map_or(std::borrow::Cow::Borrowed(""), |entry| {
                    std::borrow::Cow::Borrowed(entry.declaration.name.as_str())
                }),
            Target::File(id) => index
                .files()
                .get(id as usize)
                .and_then(|file| file.path.file_name())
                .map_or(std::borrow::Cow::Borrowed(""), |name| {
                    name.to_string_lossy()
                }),
        }
    };
    let order = |a: &Found, b: &Found| {
        (a.rank, a.length)
            .cmp(&(b.rank, b.length))
            .then_with(|| name_of(a.target).cmp(&name_of(b.target)))
            .then_with(|| target_order(a.target).cmp(&target_order(b.target)))
    };
    if found.len() > limit {
        found.select_nth_unstable_by(limit - 1, order);
        found.truncate(limit);
    }
    found.sort_by(order);

    found
        .into_iter()
        .map(
            |Found {
                 quality, target, ..
             }| {
                let mut ranges = Vec::new();
                match target {
                    Target::Entry(id) => {
                        if let Some(entry) = index.entry(id) {
                            pattern.matches(
                                &entry.declaration.name,
                                entry.declaration.container.as_deref(),
                                Some(&mut ranges),
                            );
                        }
                    }
                    Target::File(_) => {
                        pattern.matches(&name_of(target), None, Some(&mut ranges));
                    }
                }
                Hit {
                    target,
                    kind: quality.kind,
                    case_sensitive: quality.case_sensitive,
                    ranges,
                }
            },
        )
        .collect()
}

/// A name that matched, with what it is sorted by worked out once.
struct Found {
    rank: u16,
    length: u32,
    quality: Quality,
    target: Target,
}

/// Entries before files, each in index order.
const fn target_order(target: Target) -> (u8, u32) {
    match target {
        Target::Entry(id) => (0, id),
        Target::File(id) => (1, id),
    }
}

/// How one word of a pattern matches a name, trying each kind of match
/// from the best down and stopping at the first that fits.
fn match_word(
    word: &Word,
    name: &[u8],
    ranges: Option<&mut Vec<(u32, u32)>>,
    scratch: &mut Scratch,
) -> Option<Quality> {
    let pattern = &word.lower;
    let length = pattern.len();
    if length == 0 || name.is_empty() {
        return None;
    }
    let sensitive = |at: usize| name.get(at..at + length) == Some(&word.text[..]);
    let push = |ranges: Option<&mut Vec<(u32, u32)>>, start: usize, end: usize| {
        if let Some(ranges) = ranges {
            ranges.push((start as u32, end as u32));
        }
    };

    // Every letter has to be in the name, in order, for anything but a
    // near miss. Most names fail this, and it is the cheapest test there is.
    if !is_subsequence(pattern, name) {
        return fuzzy(word, name);
    }

    if starts_with_ignoring_case(name, pattern) {
        let kind = if name.len() == length {
            MatchKind::Exact
        } else {
            MatchKind::Prefix
        };
        push(ranges, 0, length);
        return Some(Quality {
            kind,
            case_sensitive: sensitive(0),
        });
    }

    // A word inside the name, from its start. The first in the case typed,
    // if there is one.
    let mut word_start: Option<usize> = None;
    for at in 1..=name.len().saturating_sub(length) {
        if name[at].to_ascii_lowercase() == pattern[0]
            && starts_word(name, at)
            && starts_with_ignoring_case(&name[at..], pattern)
        {
            if sensitive(at) {
                word_start = Some(at);
                break;
            }
            word_start.get_or_insert(at);
        }
    }
    if let Some(start) = word_start {
        push(ranges, start, start + length);
        return Some(Quality {
            kind: MatchKind::StartOfWord,
            case_sensitive: sensitive(start),
        });
    }

    // One letter that starts no word can only be a substring.
    if length > 1 {
        humps_into(name, &mut scratch.humps);
    } else {
        scratch.humps.clear();
    }
    let humps = &scratch.humps;
    let matched = &mut scratch.matched;
    matched.clear();
    if length > 1 && camel_case(word, name, humps, 0, 0, matched) {
        let first = matched[0].0;
        let contiguous = matched.windows(2).all(|pair| pair[1].0 == pair[0].0 + 1);
        let kind = match (first == 0, contiguous) {
            (true, true) if matched.len() == humps.len() => MatchKind::CamelCaseExact,
            (true, true) => MatchKind::CamelCasePrefix,
            (true, false) => MatchKind::CamelCaseNonContiguousPrefix,
            (false, true) => MatchKind::CamelCaseSubstring,
            (false, false) => MatchKind::CamelCaseNonContiguousSubstring,
        };
        let mut offset = 0;
        let mut case_sensitive = true;
        let mut ranges = ranges;
        for &(hump, _, taken) in matched.iter() {
            let start = humps[hump].0;
            case_sensitive &= name[start..start + taken] == word.text[offset..offset + taken];
            offset += taken;
            push(ranges.as_deref_mut(), start, start + taken);
        }
        return Some(Quality {
            kind,
            case_sensitive,
        });
    }

    if let Some(start) = find_ignoring_case(name, pattern) {
        push(ranges, start, start + length);
        return Some(Quality {
            kind: MatchKind::Substring,
            case_sensitive: sensitive(start),
        });
    }
    fuzzy(word, name)
}

/// Where each word of a name starts and ends, in bytes: `GoToDefinition`
/// is `Go`, `To`, `Definition`; `XMLReader` is `XML`, `Reader`; `max_count`
/// is `max`, `count`; `Vector3` is `Vector`, `3`.
#[cfg(test)]
fn humps(name: &[u8]) -> Vec<(usize, usize)> {
    let mut humps = Vec::new();
    humps_into(name, &mut humps);
    humps
}

/// [`humps`], into a buffer that is cleared first.
fn humps_into(name: &[u8], humps: &mut Vec<(usize, usize)>) {
    humps.clear();
    let mut start: Option<usize> = None;
    for at in 0..name.len() {
        if name[at] == b'_' {
            if let Some(from) = start.take() {
                humps.push((from, at));
            }
        } else if starts_word(name, at) {
            if let Some(from) = start {
                humps.push((from, at));
            }
            start = Some(at);
        } else if start.is_none() {
            start = Some(at);
        }
    }
    if let Some(from) = start {
        humps.push((from, name.len()));
    }
}

/// Whether a word of the name starts at `at`: at the start, after an
/// underscore, at a capital after a small letter or a digit, at the last
/// capital of a run followed by a small letter (`XMLReader`), and where
/// digits start or stop.
fn starts_word(name: &[u8], at: usize) -> bool {
    let byte = name[at];
    if byte == b'_' {
        return false;
    }
    let Some(previous) = at.checked_sub(1).map(|at| name[at]) else {
        return true;
    };
    if previous == b'_' {
        return true;
    }
    let next = name.get(at + 1).copied();
    (byte.is_ascii_uppercase() && (previous.is_ascii_lowercase() || previous.is_ascii_digit()))
        || (byte.is_ascii_uppercase()
            && previous.is_ascii_uppercase()
            && next.is_some_and(|next| next.is_ascii_lowercase()))
        || (byte.is_ascii_digit() != previous.is_ascii_digit()
            && byte.is_ascii_alphanumeric()
            && previous.is_ascii_alphanumeric())
}

/// Whether the rest of the pattern, from `from`, can be split into pieces
/// each of which starts a word of the name, the words in order, from word
/// `hump` on. Records `(word, pattern offset, length)` for each piece.
///
/// Longer pieces are tried first, and earlier words, so that `goToDef`
/// takes `go`, `To` and `Def` rather than `g`, `o`...: the first split
/// found is the one a reader would have meant.
fn camel_case(
    word: &Word,
    name: &[u8],
    humps: &[(usize, usize)],
    from: usize,
    hump: usize,
    matched: &mut Vec<(usize, usize, usize)>,
) -> bool {
    let pattern = &word.lower;
    if from == pattern.len() {
        return true;
    }
    // Too many pieces left for the words there are: give up early.
    for index in hump..humps.len() {
        let (start, end) = humps[index];
        let mut longest = 0;
        while from + longest < pattern.len()
            && start + longest < end
            && name[start + longest].to_ascii_lowercase() == pattern[from + longest]
        {
            longest += 1;
        }
        for taken in (1..=longest).rev() {
            matched.push((index, from, taken));
            if camel_case(word, name, humps, from + taken, index + 1, matched) {
                return true;
            }
            matched.pop();
        }
    }
    false
}

/// A near miss: the name with one letter changed, added, removed, or two
/// neighbours swapped. Only for patterns of four letters or more — below
/// that, one letter is too much of the word for a guess to be worth
/// showing.
fn fuzzy(word: &Word, name: &[u8]) -> Option<Quality> {
    let pattern = &word.lower;
    if pattern.len() < 4 || pattern.len().abs_diff(name.len()) > 1 {
        return None;
    }
    within_one_edit(pattern, name).then_some(Quality {
        kind: MatchKind::Fuzzy,
        case_sensitive: false,
    })
}

/// Whether `a` (lower case) and `b` are at most one edit apart, an edit
/// being a substitution, an insertion, a deletion or a transposition of
/// neighbours, ignoring case.
fn within_one_edit(a: &[u8], b: &[u8]) -> bool {
    let lower = |byte: u8| byte.to_ascii_lowercase();
    let prefix = a
        .iter()
        .zip(b)
        .take_while(|(x, y)| **x == lower(**y))
        .count();
    let (a, b) = (&a[prefix..], &b[prefix..]);
    let same =
        |x: &[u8], y: &[u8]| x.len() == y.len() && x.iter().zip(y).all(|(p, q)| *p == lower(*q));
    match (a.len(), b.len()) {
        (0, 0) => true,
        (x, y) if x == y => {
            same(&a[1..], &b[1..])
                || (x >= 2 && a[0] == lower(b[1]) && a[1] == lower(b[0]) && same(&a[2..], &b[2..]))
        }
        (x, y) if x + 1 == y => same(a, &b[1..]),
        (x, y) if y + 1 == x => same(&a[1..], b),
        _ => false,
    }
}

fn is_subsequence(pattern: &[u8], name: &[u8]) -> bool {
    let mut wanted = pattern.iter();
    let mut next = wanted.next();
    for &byte in name {
        match next {
            None => return true,
            Some(&want) if byte.to_ascii_lowercase() == want => next = wanted.next(),
            Some(_) => {}
        }
    }
    next.is_none()
}

fn starts_with_ignoring_case(name: &[u8], lower: &[u8]) -> bool {
    name.len() >= lower.len()
        && name
            .iter()
            .zip(lower)
            .all(|(byte, want)| byte.to_ascii_lowercase() == *want)
}

fn find_ignoring_case(name: &[u8], lower: &[u8]) -> Option<usize> {
    (0..=name.len().checked_sub(lower.len())?)
        .find(|&at| starts_with_ignoring_case(&name[at..], lower))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rustlyn_text::TextSpan;

    use super::*;
    use crate::index::outline_of_text;
    use crate::outline::{Declaration, FileOutline};

    fn quality(pattern: &str, name: &str) -> Option<(MatchKind, bool)> {
        Pattern::new(pattern)?
            .matches(name, None, None)
            .map(|quality| (quality.kind, quality.case_sensitive))
    }

    fn ranges(pattern: &str, name: &str) -> Vec<(u32, u32)> {
        let mut ranges = Vec::new();
        Pattern::new(pattern)
            .expect("a pattern")
            .matches(name, None, Some(&mut ranges))
            .expect("a match");
        ranges
    }

    #[test]
    fn each_kind_of_match_is_told_apart() {
        use MatchKind::*;
        assert_eq!(quality("Canvas", "Canvas"), Some((Exact, true)));
        assert_eq!(quality("canvas", "Canvas"), Some((Exact, false)));
        assert_eq!(quality("Can", "Canvas"), Some((Prefix, true)));
        assert_eq!(quality("Def", "GoToDefinition"), Some((StartOfWord, true)));
        assert_eq!(
            quality("GTD", "GoToDefinition"),
            Some((CamelCaseExact, true))
        );
        assert_eq!(
            quality("GoTD", "GoToDefinition"),
            Some((CamelCaseExact, true))
        );
        // Typed without the capitals, the start of every word is also the
        // start of the name, and that is the better match.
        assert_eq!(quality("goToDef", "GoToDefinition"), Some((Prefix, false)));
        assert_eq!(
            quality("goTDef", "GoToDefinition"),
            Some((CamelCaseExact, false))
        );
        assert_eq!(
            quality("gtDef", "GoToDefinition"),
            Some((CamelCaseExact, false))
        );
        assert_eq!(quality("GoT", "GoToDefinition"), Some((Prefix, true)));
        assert_eq!(
            quality("GT", "GoToDefinition"),
            Some((CamelCasePrefix, true))
        );
        assert_eq!(
            quality("GD", "GoToDefinition"),
            Some((CamelCaseNonContiguousPrefix, true))
        );
        assert_eq!(
            quality("TD", "GoToDefinition"),
            Some((CamelCaseSubstring, true))
        );
        assert_eq!(
            quality("GDN", "GetTheDefinitionName"),
            Some((CamelCaseNonContiguousPrefix, true))
        );
        assert_eq!(
            quality("TN", "GetTheDefinitionName"),
            Some((CamelCaseNonContiguousSubstring, true))
        );
        assert_eq!(quality("efin", "GoToDefinition"), Some((Substring, true)));
        assert_eq!(quality("Canvsa", "Canvas"), Some((Fuzzy, false)));
        assert_eq!(quality("Canvs", "Canvas"), Some((Fuzzy, false)));
        assert_eq!(quality("Cnvas", "Canvas"), Some((Fuzzy, false)));
        assert_eq!(quality("xyz", "Canvas"), None);
        // Three letters are too few to guess from.
        assert_eq!(quality("Cna", "Can"), None);
    }

    #[test]
    fn the_ranges_are_the_letters_that_matched() {
        assert_eq!(ranges("Can", "Canvas"), vec![(0, 3)]);
        assert_eq!(
            ranges("GTD", "GoToDefinition"),
            vec![(0, 1), (2, 3), (4, 5)]
        );
        assert_eq!(
            ranges("gtDef", "GoToDefinition"),
            vec![(0, 1), (2, 3), (4, 7)]
        );
        assert_eq!(ranges("def", "GoToDefinition"), vec![(4, 7)]);
        assert_eq!(ranges("fin", "GoToDefinition"), vec![(6, 9)]);
        assert_eq!(ranges("XR", "XMLReader"), vec![(0, 1), (3, 4)]);
        assert_eq!(ranges("mc", "max_count"), vec![(0, 1), (4, 5)]);
        assert_eq!(ranges("Canvsa", "Canvas"), Vec::<(u32, u32)>::new());
        // Two words, each highlighted once.
        assert_eq!(ranges("go def", "GoToDefinition"), vec![(0, 2), (4, 7)]);
    }

    #[test]
    fn words_start_where_a_reader_sees_them_start() {
        let words = |name: &str| -> Vec<String> {
            humps(name.as_bytes())
                .into_iter()
                .map(|(start, end)| name[start..end].to_string())
                .collect()
        };
        assert_eq!(words("GoToDefinition"), vec!["Go", "To", "Definition"]);
        assert_eq!(words("XMLReader"), vec!["XML", "Reader"]);
        assert_eq!(words("max_count"), vec!["max", "count"]);
        assert_eq!(words("_field"), vec!["field"]);
        assert_eq!(words("Vector3D"), vec!["Vector", "3", "D"]);
        assert_eq!(words("getHTTP2Client"), vec!["get", "HTTP", "2", "Client"]);
    }

    fn index(files: &[(&str, &str)]) -> ProjectIndex {
        ProjectIndex::from_outlines(
            "/project",
            files
                .iter()
                .map(|(name, text)| (PathBuf::from(name), outline_of_text(text))),
        )
    }

    fn named(index: &ProjectIndex, hits: &[Hit]) -> Vec<String> {
        hits.iter()
            .map(|hit| match hit.target {
                Target::Entry(id) => index
                    .entry(id)
                    .expect("an entry")
                    .declaration
                    .qualified_name(),
                Target::File(id) => index.files()[id as usize]
                    .path
                    .to_string_lossy()
                    .into_owned(),
            })
            .collect()
    }

    #[test]
    fn results_come_best_first_and_are_filtered_by_kind() {
        let index = index(&[
            (
                "Navigation.cs",
                "namespace Ide { class Navigator { void GoToDefinition() { } void GoToBase() { } int goal; } class Go { } }",
            ),
            ("Go.cs", "class Other { void Undergo() { } }"),
        ]);
        let hits = search(&index, "Go", SearchKind::All, 10);
        assert_eq!(
            named(&index, &hits),
            vec![
                "Ide.Go",
                "Go.cs",
                "Ide.Navigator.GoToBase",
                "Ide.Navigator.GoToDefinition",
                "Ide.Navigator.goal",
                "Other.Undergo"
            ]
        );
        assert_eq!(hits[0].kind, MatchKind::Exact);
        assert_eq!(hits.last().expect("a hit").kind, MatchKind::Substring);
        let types = search(&index, "Go", SearchKind::Types, 10);
        assert_eq!(named(&index, &types), vec!["Ide.Go"]);
        let members = search(&index, "gtd", SearchKind::Members, 10);
        assert_eq!(
            named(&index, &members),
            vec!["Ide.Navigator.GoToDefinition"]
        );
        let files = search(&index, "go", SearchKind::Files, 10);
        assert_eq!(named(&index, &files), vec!["Go.cs"]);
        assert_eq!(files[0].ranges, vec![(0, 2)]);
        // At most as many as asked for, and still the best of them.
        let one = search(&index, "Go", SearchKind::All, 1);
        assert_eq!(named(&index, &one), vec!["Ide.Go"]);
    }

    #[test]
    fn a_dotted_pattern_matches_the_container_too() {
        let index = index(&[(
            "A.cs",
            "namespace Shapes { class Circle { void Draw() { } } class Square { void Draw() { } } }",
        )]);
        let hits = search(&index, "Circle.Draw", SearchKind::All, 10);
        assert_eq!(named(&index, &hits), vec!["Shapes.Circle.Draw"]);
        assert_eq!(hits[0].ranges, vec![(0, 4)]);
        let hits = search(&index, "sh.sq.dr", SearchKind::All, 10);
        assert_eq!(named(&index, &hits), vec!["Shapes.Square.Draw"]);
        let hits = search(&index, "Shapes.", SearchKind::Types, 10);
        assert_eq!(named(&index, &hits), vec!["Shapes.Circle", "Shapes.Square"]);
    }

    #[test]
    fn a_match_in_the_case_typed_goes_first() {
        let index = index(&[("A.cs", "class A { int count; int Count; }")]);
        let hits = search(&index, "Count", SearchKind::Members, 10);
        assert_eq!(named(&index, &hits), vec!["A.Count", "A.count"]);
        assert!(hits[0].case_sensitive && !hits[1].case_sensitive);
    }

    /// A hundred thousand declarations, as a large solution has.
    fn synthetic(count: usize) -> ProjectIndex {
        let words = [
            "Get",
            "Set",
            "Update",
            "Render",
            "Syntax",
            "Node",
            "Token",
            "Tree",
            "Semantic",
            "Model",
            "Symbol",
            "Binder",
            "Compilation",
            "Definition",
            "Reference",
            "Find",
            "Go",
            "To",
            "Base",
            "Derived",
            "Async",
            "Cache",
            "Index",
            "Entry",
            "Walker",
            "Visitor",
        ];
        let template = Declaration {
            name: String::new(),
            kind: DeclarationKind::Method,
            keyword: "void".to_string(),
            name_span: TextSpan::new(0, 0),
            full_span: TextSpan::new(0, 0),
            line: 0,
            depth: 1,
            container: None,
            type_text: None,
            bases: Vec::new(),
            type_parameters: Vec::new(),
            parameters: Vec::new(),
            attributes: Vec::new(),
            is_static: false,
            is_abstract: false,
            is_override: false,
            is_partial: false,
        };
        let mut seed: u64 = 0x2545_F491_4F6C_DD1D;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let files = (0..count / 100).map(|file| {
            let declarations = (0..100)
                .map(|_| {
                    let parts = 2 + (next() % 3) as usize;
                    let name: String = (0..parts)
                        .map(|_| words[(next() % words.len() as u64) as usize])
                        .collect();
                    Declaration {
                        name,
                        container: Some(format!("Project.Type{file}")),
                        ..template.clone()
                    }
                })
                .collect();
            (
                PathBuf::from(format!("File{file}.cs")),
                FileOutline {
                    declarations,
                    namespaces: Vec::new(),
                    usings: Vec::new(),
                    parse_errors: 0,
                },
            )
        });
        ProjectIndex::from_outlines("/project", files)
    }

    #[test]
    fn a_hundred_thousand_names_are_searched_in_a_frame() {
        let index = synthetic(100_000);
        assert_eq!(index.len(), 100_000);
        for pattern in [
            "gtd",
            "GoToDef",
            "SyntaxNodeWalker",
            "e",
            "Semantc",
            "type.find",
        ] {
            // The best of five: under a full test run the machine is busy,
            // and one measurement says more about the other tests than about
            // this search.
            let mut elapsed = std::time::Duration::MAX;
            for _ in 0..5 {
                let started = std::time::Instant::now();
                let hits = search(&index, pattern, SearchKind::All, 100);
                elapsed = elapsed.min(started.elapsed());
                assert!(!hits.is_empty(), "{pattern} should find something");
            }
            // Twenty milliseconds in a release build; a debug build is
            // several times slower, and this only has to catch the search
            // becoming quadratic.
            let budget = if cfg!(debug_assertions) { 400 } else { 20 };
            assert!(elapsed.as_millis() < budget, "{pattern} took {elapsed:?}");
        }
    }
}
