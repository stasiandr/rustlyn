//! Which members a change touched, and how: the lines of the patch laid on
//! the structure of the file before and after. The structure comes from
//! Rustlyn's parser, straight from the text — no compiler is needed here,
//! and the old text is rebuilt from the new one and the patch.

use std::collections::{BTreeMap, HashMap};
use std::ops::Range;

use rustlyn_ide::outline::{Declaration, DeclarationKind, outline};

use super::diff::{FileDiff, Status, split_lines};

/// A member or type in a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Member {
    /// Relative to the project root, `/` between folders.
    pub path: String,
    /// The qualified name: `Game.Pawn.Heal`.
    pub name: String,
    pub kind: DeclarationKind,
    /// The name and parameter types, which tell overloads apart:
    /// `Game.Pawn.Heal(int)`.
    pub key: String,
    /// The line of the name, from zero.
    pub line: usize,
    /// The start of the name, in bytes from the start of the file.
    pub offset: usize,
    /// The same in UTF-16 code units, which is what the compiler session is
    /// asked in.
    pub(crate) utf16_offset: usize,
    /// The lines of the whole declaration.
    pub lines: Range<usize>,
    /// The bytes of the whole declaration, from the start of the file: what
    /// tells apart two members written on one line.
    pub span: Range<usize>,
    /// The lines before the body: attributes, modifiers, the signature.
    pub head: Range<usize>,
    /// A type's bases as written.
    pub bases: Vec<String>,
    pub attributes: Vec<String>,
    /// The words before the name, outside attribute lists: `public`,
    /// `static`, `readonly`, the type.
    pub modifiers: Vec<String>,
    /// A field's or property's type, a method's return type.
    pub type_text: Option<String>,
    pub container: Option<String>,
    /// The declaration up to the body, without whitespace; a field's is the
    /// whole declaration. Equal before and after means the change is only
    /// in the body, even when the body is on the same line.
    pub signature: String,
}

impl Member {
    #[must_use]
    pub fn short_name(&self) -> &str {
        self.name.rsplit('.').next().unwrap_or(&self.name)
    }

    #[must_use]
    pub const fn is_type(&self) -> bool {
        self.kind.is_type()
    }
}

/// How a member changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum How {
    /// The body only: behaviour, not the contract.
    Body,
    /// The signature, the type, attributes, a field's initializer.
    Signature,
    Added,
    Removed,
}

impl How {
    /// The stable English code.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Body => "body",
            Self::Signature => "signature",
            Self::Added => "added",
            Self::Removed => "removed",
        }
    }
}

/// Which code of a property or an indexer a change touched. A getter and a
/// setter are different code: whoever only assigns the property does not run
/// the getter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Touched {
    /// The whole member, or a part that every use runs.
    All,
    /// The getter alone.
    Getter,
    /// The setter (or the `init`) alone.
    Setter,
}

/// A member the change touched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    /// For a removed one, what it was.
    pub member: Member,
    pub how: How,
    /// The changed lines inside the member: new lines, a removed member's
    /// old ones.
    pub lines: Vec<usize>,
    /// For a property or an indexer whose body changed: the accessor it
    /// changed in.
    pub touched: Touched,
    /// What the member was before, for one that still exists.
    pub before: Option<Member>,
    /// The member is in code the project's build leaves out (an `#if` that
    /// is not on): the compiler does not see it, and nothing says who calls
    /// it.
    pub inactive: bool,
}

/// The members of one text.
#[derive(Debug, Clone)]
pub struct Members {
    pub list: Vec<Member>,
}

impl Members {
    #[must_use]
    pub fn of(path: &str, text: &str) -> Self {
        let parsed = outline(text);
        let starts = line_starts(text);
        let list = parsed
            .declarations
            .iter()
            .filter(|d| {
                d.kind != DeclarationKind::Namespace && d.kind != DeclarationKind::Extension
            })
            .map(|d| member(path, text, &starts, d))
            .collect();
        Self { list }
    }

    /// The same from an outline made elsewhere: the compiler's, which read
    /// the file with its project's preprocessor symbols, so that code behind
    /// an `#if` the project turns on is there.
    #[must_use]
    pub fn of_outline(path: &str, text: &str, parsed: &rustlyn_ide::FileOutline) -> Self {
        let starts = line_starts(text);
        let list = parsed
            .declarations
            .iter()
            .filter(|d| {
                d.kind != DeclarationKind::Namespace && d.kind != DeclarationKind::Extension
            })
            .map(|d| member(path, text, &starts, d))
            .collect();
        Self { list }
    }

    /// The innermost member whose lines hold `line`. A type's line outside
    /// its members counts as the type's only in its header.
    #[must_use]
    pub fn at_line(&self, line: usize) -> Option<&Member> {
        let inner = self.enclosing(line)?;
        if inner.is_type() && !inner.head.contains(&line) {
            return None;
        }
        Some(inner)
    }

    /// The innermost member whose lines hold `line`; a type's line outside
    /// its members is the type's. Of members written on one line, the
    /// narrowest in bytes.
    #[must_use]
    pub fn enclosing(&self, line: usize) -> Option<&Member> {
        self.list
            .iter()
            .filter(|m| m.lines.contains(&line))
            .min_by_key(|m| (m.lines.len(), m.span.len()))
    }

    /// The innermost member whose bytes hold `offset`: the one a name at
    /// `offset` is in, which a line cannot say where several members share
    /// it.
    #[must_use]
    pub fn enclosing_at(&self, offset: usize) -> Option<&Member> {
        self.list
            .iter()
            .filter(|m| m.span.contains(&offset))
            .min_by_key(|m| m.span.len())
    }

    /// The innermost member that holds `line` and, when `columns` (bytes
    /// from the start of the file) says where on the line the change is,
    /// holds all of it.
    #[must_use]
    pub fn enclosing_columns(
        &self,
        line: usize,
        columns: Option<&Range<usize>>,
    ) -> Option<&Member> {
        let holds = |m: &&Member| m.lines.contains(&line);
        let within =
            |m: &&Member| columns.is_some_and(|c| m.span.start <= c.start && c.end <= m.span.end);
        self.list
            .iter()
            .filter(holds)
            .filter(within)
            .min_by_key(|m| (m.lines.len(), m.span.len()))
            .or_else(|| self.enclosing(line))
    }

    /// The member whose name is at `line` and `character` (UTF-16 code units
    /// from the start of the line) of `text`: the member the compiler named,
    /// which is not always the innermost one on a line.
    #[must_use]
    pub fn named_at(&self, text: &str, line: usize, character: usize) -> Option<&Member> {
        let starts = line_starts(text);
        let start = *starts.get(line)?;
        let end = starts.get(line + 1).copied().unwrap_or(text.len());
        let mut units = 0;
        let mut at = None;
        for (index, c) in text[start..end].char_indices() {
            if units >= character {
                at = Some(start + index);
                break;
            }
            units += c.len_utf16();
        }
        let at = at.or((units == character).then_some(end))?;
        self.list.iter().find(|m| m.offset == at)
    }

    /// Whether the bytes `at` of `line` are inside a member that is not a
    /// type: where text was put into a name, as against between two members.
    fn in_member(&self, line: usize, at: &Range<usize>) -> bool {
        self.list.iter().any(|m| {
            !m.is_type()
                && m.lines.contains(&line)
                && m.span.start <= at.start
                && at.end <= m.span.end
        })
    }

    /// The members a change at `line` and `columns` is in. Where the bytes
    /// say which member holds all of it, that one; where they do not (the
    /// line was not replaced by one, or the change spans two members), every
    /// member written on the line that the bytes touch — a change that
    /// cannot be told apart is not given to one of them by luck, nor to the
    /// type around them.
    fn at_columns_all(&self, line: usize, columns: Option<&Range<usize>>) -> Vec<&Member> {
        let holds = |m: &&Member| m.lines.contains(&line);
        if let Some(c) = columns
            && let Some(one) = self
                .list
                .iter()
                .filter(holds)
                .filter(|m| m.span.start <= c.start && c.end <= m.span.end)
                .min_by_key(|m| (m.lines.len(), m.span.len()))
        {
            // A type holds a change in its body that no member holds (a
            // comment after a member on its line): that is for the members
            // written there, below.
            if !one.is_type() || one.head.contains(&line) {
                return vec![one];
            }
        }
        let on: Vec<&Member> = self.list.iter().filter(holds).collect();
        let Some(least) = on.iter().map(|m| m.lines.len()).min() else {
            return Vec::new();
        };
        let mut tight: Vec<&Member> = on.into_iter().filter(|m| m.lines.len() == least).collect();
        if let Some(c) = columns {
            let touching: Vec<&Member> = tight
                .iter()
                .copied()
                .filter(|m| m.span.start <= c.end && c.start <= m.span.end)
                .collect();
            if !touching.is_empty() {
                tight = touching;
            }
        }
        // The type around members written on its line is not what changed
        // when one of them can have been.
        if tight.iter().any(|m| !m.is_type()) {
            tight.retain(|m| !m.is_type());
        }
        tight.retain(|m| !m.is_type() || m.head.contains(&line));
        tight
    }

    #[must_use]
    pub fn by_key(&self, key: &str) -> Option<&Member> {
        self.list.iter().find(|m| m.key == key)
    }

    /// The only member with this qualified name and kind.
    fn unique(&self, name: &str, kind: DeclarationKind) -> Option<&Member> {
        let mut found = self
            .list
            .iter()
            .filter(|m| m.name == name && m.kind == kind);
        let first = found.next()?;
        found.next().is_none().then_some(first)
    }
}

/// The changed members of a file, by its new text (empty for a deleted one).
#[must_use]
pub fn changes(file: &FileDiff, new_text: &str) -> Vec<Change> {
    changes_by(file, new_text, &Members::of)
}

/// The same, with the caller reading the structure of each text
/// (`members_of(path, text)`): a compiled project reads a file with its
/// preprocessor symbols, and a member behind an `#if` it turns on is there
/// only then.
#[must_use]
pub fn changes_by(
    file: &FileDiff,
    new_text: &str,
    members_of: &dyn Fn(&str, &str) -> Members,
) -> Vec<Change> {
    let old_text = file.old_text(new_text);
    let new = if file.status == Status::Deleted {
        Members { list: Vec::new() }
    } else {
        members_of(&file.path, new_text)
    };
    let old = members_of(file.old_path.as_deref().unwrap_or(&file.path), &old_text);
    let new_lines = split_lines(new_text);
    let mut found: BTreeMap<String, Change> = BTreeMap::new();
    let mut note = |member: &Member, how: How, line: usize| {
        let entry = found.entry(member.key.clone()).or_insert_with(|| Change {
            member: member.clone(),
            how,
            lines: Vec::new(),
            touched: Touched::All,
            before: None,
            inactive: false,
        });
        entry.how = entry.how.max(how);
        if !entry.lines.contains(&line) {
            entry.lines.push(line);
        }
    };
    // A key on one side only is added or removed; the same member with
    // other parameters is a signature change.
    let renamed_from: HashMap<&str, &Member> = old
        .list
        .iter()
        .filter(|o| new.by_key(&o.key).is_none())
        .filter_map(|o| {
            new.unique(&o.name, o.kind)
                .filter(|n| old.unique(&n.name, n.kind).is_some())
                .map(|n| (n.key.as_str(), o))
        })
        .collect();

    let new_starts = line_starts(new_text);
    let old_starts = line_starts(&old_text);
    let old_lines = split_lines(&old_text);
    // Where on a line a change is, when the line was replaced by one: the
    // bytes between what the two lines share at the start and at the end.
    let columns = |starts: &[usize], line: usize, own: &str, other: &str| {
        let (from, to) = differing(own, other);
        starts.get(line).map(|&s| s + from..s + to)
    };
    for block in &file.blocks {
        let paired = block.new_lines.len() == block.old_lines.len();
        for (k, line) in block.new_lines.clone().enumerate() {
            if new_lines.get(line).is_some_and(|l| l.trim().is_empty()) {
                continue;
            }
            let at = paired
                .then(|| old_lines.get(block.old_lines.start + k))
                .flatten()
                .zip(new_lines.get(line))
                .and_then(|(old, now)| columns(&new_starts, line, now, old));
            // Text only the other side has changed this one in no byte.
            let theirs = paired
                .then(|| old_lines.get(block.old_lines.start + k))
                .flatten()
                .zip(new_lines.get(line))
                .and_then(|(old, now)| columns(&old_starts, block.old_lines.start + k, old, now));
            if at
                .as_ref()
                .is_some_and(|r| r.is_empty() && !new.in_member(line, r))
                && theirs.as_ref().is_some_and(|r| !r.is_empty())
            {
                continue;
            }
            for member in new.at_columns_all(line, at.as_ref()) {
                let before = old.by_key(&member.key);
                let how = if before.is_none() && !renamed_from.contains_key(member.key.as_str()) {
                    How::Added
                } else if renamed_from.contains_key(member.key.as_str())
                    || !has_body(member)
                    || (member.head.contains(&line)
                        && before.is_none_or(|b| b.signature != member.signature))
                {
                    How::Signature
                } else {
                    How::Body
                };
                note(member, how, line);
            }
        }
        for (k, line) in block.old_lines.clone().enumerate() {
            if block.removed.get(k).is_some_and(|l| l.trim().is_empty()) {
                continue;
            }
            let at = paired
                .then(|| new_lines.get(block.new_lines.start + k))
                .flatten()
                .zip(old_lines.get(line))
                .and_then(|(now, old)| columns(&old_starts, line, old, now));
            let theirs = paired
                .then(|| new_lines.get(block.new_lines.start + k))
                .flatten()
                .zip(old_lines.get(line))
                .and_then(|(now, old)| columns(&new_starts, block.new_lines.start + k, now, old));
            if at
                .as_ref()
                .is_some_and(|r| r.is_empty() && !old.in_member(line, r))
                && theirs.as_ref().is_some_and(|r| !r.is_empty())
            {
                continue;
            }
            for was in old.at_columns_all(line, at.as_ref()) {
                let now = new.by_key(&was.key).or_else(|| {
                    renamed_from
                        .iter()
                        .find(|(_, o)| o.key == was.key)
                        .and_then(|(n, _)| new.by_key(n))
                });
                match now {
                    Some(now) => {
                        let how = if (was.head.contains(&line) && was.signature != now.signature)
                            || !has_body(was)
                            || now.key != was.key
                        {
                            How::Signature
                        } else {
                            How::Body
                        };
                        // Lines are new ones: a removed line lands on the line
                        // that replaced it, or on the member's name.
                        let replaced = block.new_lines.start + k;
                        let at = if paired && now.lines.contains(&replaced) {
                            replaced
                        } else {
                            now.line
                        };
                        note(now, how, at);
                    }
                    None => note(was, How::Removed, line),
                }
            }
        }
    }
    // A change in code the build leaves out is in no member of the compiled
    // structure: it is found in the structure with the file's own switches
    // on, and said to be in code that is not built.
    let lone: Vec<(usize, bool)> = file
        .blocks
        .iter()
        .flat_map(|block| {
            let new = block.new_lines.clone().map(|line| (line, true));
            let old = block.old_lines.clone().map(|line| (line, false));
            new.chain(old)
        })
        .filter(|&(line, is_new)| {
            let text = if is_new {
                new_lines.get(line)
            } else {
                old_lines.get(line)
            };
            let members = if is_new { &new } else { &old };
            text.is_some_and(|text| !text.trim().is_empty() && !text.trim_start().starts_with('#'))
                && members
                    .enclosing(line)
                    .is_none_or(|m| m.is_type() && !m.head.contains(&line))
        })
        .collect();
    if !lone.is_empty() {
        let all_new = Members::of_outline(
            &file.path,
            new_text,
            &rustlyn_ide::outline::outline_with_conditions_active(new_text),
        );
        let all_old = Members::of_outline(
            file.old_path.as_deref().unwrap_or(&file.path),
            &old_text,
            &rustlyn_ide::outline::outline_with_conditions_active(&old_text),
        );
        for (line, is_new) in lone {
            let (members, other) = if is_new {
                (&all_new, &all_old)
            } else {
                (&all_old, &all_new)
            };
            let Some(member) = members.at_line(line) else {
                continue;
            };
            let known = if is_new { &new } else { &old };
            if known.by_key(&member.key).is_some() {
                continue;
            }
            let survives = other.by_key(&member.key);
            let how = match (is_new, survives.is_some()) {
                (_, true) => How::Body,
                (true, false) => How::Added,
                (false, false) => How::Removed,
            };
            // A member that is still there is told by its new place.
            let at = if is_new {
                member
            } else {
                survives.unwrap_or(member)
            };
            let entry = found.entry(at.key.clone()).or_insert_with(|| Change {
                member: at.clone(),
                how,
                lines: Vec::new(),
                touched: Touched::All,
                before: None,
                inactive: true,
            });
            let line = if is_new { line } else { at.line };
            if !entry.lines.contains(&line) {
                entry.lines.push(line);
            }
        }
    }
    // A removed type: its members are removed with it.
    let removed_types: Vec<String> = found
        .values()
        .filter(|c| c.how == How::Removed && c.member.is_type())
        .map(|c| c.member.name.clone())
        .collect();
    for member in &old.list {
        if removed_types
            .iter()
            .any(|t| member.container.as_deref() == Some(t.as_str()))
            && new.by_key(&member.key).is_none()
        {
            found.entry(member.key.clone()).or_insert_with(|| Change {
                member: member.clone(),
                how: How::Removed,
                lines: vec![member.line],
                touched: Touched::All,
                before: None,
                inactive: false,
            });
        }
    }
    let mut list: Vec<Change> = found.into_values().collect();
    for change in &mut list {
        change.lines.sort_unstable();
        if change.how != How::Removed && change.how != How::Added {
            change.before = old
                .by_key(&change.member.key)
                .or_else(|| renamed_from.get(change.member.key.as_str()).copied())
                .cloned();
        }
        if change.how == How::Body
            && matches!(
                change.member.kind,
                DeclarationKind::Property | DeclarationKind::Indexer
            )
        {
            change.touched = touched_accessor(new_text, &new_starts, &change.member, &change.lines);
        }
    }
    list.sort_by(|a, b| {
        (a.member.path.as_str(), a.member.line).cmp(&(b.member.path.as_str(), b.member.line))
    });
    list
}

/// The accessor all of a property's changed lines are in: the getter or the
/// setter; anything else, a line outside the accessors or one both share, is
/// the whole member.
fn touched_accessor(text: &str, starts: &[usize], member: &Member, lines: &[usize]) -> Touched {
    use rustlyn_ide::outline::{AccessorKind, accessors};
    let accessors = accessors(text, member.span.clone());
    if accessors.is_empty() {
        return Touched::All;
    }
    let mut touched: Option<Touched> = None;
    for &line in lines {
        let Some(&start) = starts.get(line) else {
            return Touched::All;
        };
        let end = starts.get(line + 1).copied().unwrap_or(text.len());
        let mut hit: Vec<AccessorKind> = accessors
            .iter()
            .filter(|(_, span)| span.start < end && span.end > start)
            .map(|(kind, _)| *kind)
            .collect();
        hit.dedup();
        let now = match hit.as_slice() {
            [AccessorKind::Get] => Touched::Getter,
            [AccessorKind::Set | AccessorKind::Init] => Touched::Setter,
            _ => return Touched::All,
        };
        if touched.is_some_and(|before| before != now) {
            return Touched::All;
        }
        touched = Some(now);
    }
    touched.unwrap_or(Touched::All)
}

/// Where two lines differ: the bytes of `own` from the first it does not
/// share with `other` to the last that is not part of what they share at the
/// end.
pub(crate) fn differing(own: &str, other: &str) -> (usize, usize) {
    let start = own
        .bytes()
        .zip(other.bytes())
        .take_while(|(a, b)| a == b)
        .count();
    let start = (0..=start)
        .rev()
        .find(|&i| own.is_char_boundary(i))
        .unwrap_or(0);
    let shared = own
        .bytes()
        .rev()
        .zip(other.bytes().rev())
        .take_while(|(a, b)| a == b)
        .count()
        .min(own.len() - start)
        .min(other.len().saturating_sub(start));
    let mut end = own.len() - shared;
    while !own.is_char_boundary(end) {
        end += 1;
    }
    // The blank that one line has more than the other is shared by either
    // side of it: `{ } }` and `{ } = 3; }` differ by `= 3;`, not by `= 3; `.
    let (mut start, mut end) = (start, end.max(start));
    while start < end && own.as_bytes()[start].is_ascii_whitespace() {
        start += 1;
    }
    while end > start && own.as_bytes()[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    (start, end)
}

/// A field, an event or an enum member has no body: any change to it is a
/// change to its declaration.
const fn has_body(member: &Member) -> bool {
    matches!(
        member.kind,
        DeclarationKind::Method
            | DeclarationKind::Constructor
            | DeclarationKind::Destructor
            | DeclarationKind::Property
            | DeclarationKind::Indexer
            | DeclarationKind::Operator
            | DeclarationKind::Class
            | DeclarationKind::Struct
            | DeclarationKind::Record
            | DeclarationKind::Interface
    )
}

fn member(path: &str, text: &str, starts: &[usize], d: &Declaration) -> Member {
    let full_start = d.full_span.start() as usize;
    let full_end = (d.full_span.end() as usize).min(text.len());
    let name_start = d.name_span.start() as usize;
    let name_end = (d.name_span.end() as usize).min(text.len());
    let body = body_start(text, name_end, full_end);
    let first = line_of(starts, full_start);
    let last = line_of(starts, full_end.saturating_sub(1).max(full_start));
    let head_last = line_of(
        starts,
        body.unwrap_or(full_end).saturating_sub(1).max(full_start),
    );
    // A `{` at the end of the signature's line leaves that line in the
    // header; a `{` on a line of its own is the body already.
    let head_end = head_last + 1;
    let name = explicit_name(text, name_start, d.qualified_name());
    let key = match d.kind {
        DeclarationKind::Method
        | DeclarationKind::Constructor
        | DeclarationKind::Operator
        | DeclarationKind::Indexer
        | DeclarationKind::Delegate => {
            let types: Vec<&str> = d.parameters.iter().map(|p| p.type_text.as_str()).collect();
            format!("{name}({})", types.join(", "))
        }
        _ => name.clone(),
    };
    let offset = name_start.min(text.len());
    Member {
        path: path.to_owned(),
        name,
        kind: d.kind,
        key,
        line: line_of(starts, name_start),
        offset,
        utf16_offset: utf16_len(&text[..offset]),
        lines: first..last + 1,
        span: full_start.min(text.len())..full_end.max(full_start.min(text.len())),
        head: first..head_end.min(last + 1),
        bases: d.bases.clone(),
        attributes: d.attributes.clone(),
        modifiers: words_outside_brackets(&text[full_start.min(name_start)..name_start]),
        type_text: d.type_text.clone(),
        container: d.container.clone(),
        signature: text
            [full_start.min(text.len())..body.unwrap_or(full_end).max(full_start).min(text.len())]
            .split_whitespace()
            .collect(),
    }
}

/// The qualified name of a member, with the interface of an explicit
/// implementation in it: `double IShape.Area()` and `public double Area()`
/// are two members of a type, and a key that told them apart by nothing
/// would be the first one's for both.
fn explicit_name(text: &str, name_start: usize, name: String) -> String {
    let bytes = text.as_bytes();
    if name_start == 0 || bytes.get(name_start - 1) != Some(&b'.') {
        return name;
    }
    // Back over the interface, `IShape` or `IDictionary<string, JToken?>`:
    // spaces inside its type arguments are part of it.
    let mut start = name_start - 1;
    let mut depth = 0usize;
    while start > 0 {
        let byte = bytes[start - 1];
        match byte {
            b'>' => depth += 1,
            b'<' => depth = depth.saturating_sub(1),
            b if depth == 0
                && (b.is_ascii_whitespace()
                    || matches!(b, b'(' | b'{' | b'}' | b';' | b'[' | b']')) =>
            {
                break;
            }
            _ => {}
        }
        start -= 1;
    }
    let interface = text.get(start..name_start - 1).unwrap_or_default();
    let short = name.rsplit('.').next().unwrap_or(&name);
    if interface.is_empty() || short.is_empty() {
        return name;
    }
    format!("{}{interface}.{short}", &name[..name.len() - short.len()])
}

/// The words of `head` that are not inside `[…]`: an attribute's name and
/// arguments are not modifiers.
fn words_outside_brackets(head: &str) -> Vec<String> {
    let mut depth = 0usize;
    let mut outside = String::new();
    for c in head.chars() {
        match c {
            '[' => depth += 1,
            ']' => depth = depth.saturating_sub(1),
            c if depth == 0 => outside.push(c),
            _ => {}
        }
    }
    outside
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|word| !word.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Where the body starts: the first `{` or `=>` after the name outside the
/// parentheses of the parameters and brackets.
fn body_start(text: &str, from: usize, end: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 0i32;
    let mut i = from;
    while i < end {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'{' if depth <= 0 => return Some(i),
            b'=' if depth <= 0 && bytes.get(i + 1) == Some(&b'>') => return Some(i),
            b';' if depth <= 0 => return None,
            _ => {}
        }
        i += 1;
    }
    None
}

/// The byte offset of each line's start.
#[must_use]
pub fn line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    starts.extend(
        text.bytes()
            .enumerate()
            .filter(|(_, b)| *b == b'\n')
            .map(|(i, _)| i + 1),
    );
    starts
}

/// The line, from zero, that holds the byte at `offset`.
#[must_use]
pub fn line_of(starts: &[usize], offset: usize) -> usize {
    starts.partition_point(|&s| s <= offset).saturating_sub(1)
}

pub(crate) fn utf16_len(text: &str) -> usize {
    text.encode_utf16().count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::diff::parse;
    use crate::blast::testing::patch;

    const OLD: &str = "namespace Game {
    public class Pawn : MonoBehaviour {
        public int Health;
        public void Heal(int by) {
            Health += by;
        }
        public void Hit(int by) {
            Health -= by;
        }
        void Update() { }
    }
}
";

    fn summary(old: &str, new: &str) -> Vec<(String, How)> {
        let files = parse(&patch("Pawn.cs", old, new));
        changes(&files[0], new)
            .into_iter()
            .map(|c| (c.member.key, c.how))
            .collect()
    }

    #[test]
    fn method_body() {
        let new = OLD.replace("Health += by;", "Health += by * 2;");
        assert_eq!(
            summary(OLD, &new),
            vec![("Game.Pawn.Heal(int)".to_owned(), How::Body)]
        );
    }

    #[test]
    fn method_signature_and_field_type() {
        let new = OLD
            .replace("Heal(int by)", "Heal(long by)")
            .replace("int Health", "long Health");
        assert_eq!(
            summary(OLD, &new),
            vec![
                ("Game.Pawn.Health".to_owned(), How::Signature),
                ("Game.Pawn.Heal(long)".to_owned(), How::Signature)
            ]
        );
    }

    #[test]
    fn added_and_removed() {
        let new = OLD.replace(
            "        void Update() { }\n",
            "        void LateUpdate() { }\n",
        );
        assert_eq!(
            summary(OLD, &new),
            vec![
                ("Game.Pawn.LateUpdate()".to_owned(), How::Added),
                ("Game.Pawn.Update()".to_owned(), How::Removed)
            ]
        );
    }

    #[test]
    fn body_on_the_signature_line() {
        let old = "class A {\n    void F() { int x = 1; }\n}\n";
        let new = old.replace("x = 1", "x = 2");
        assert_eq!(summary(old, &new), vec![("A.F()".to_owned(), How::Body)]);
    }

    #[test]
    fn type_header() {
        let new = OLD.replace("Pawn : MonoBehaviour", "Pawn : NetworkBehaviour");
        assert_eq!(
            summary(OLD, &new),
            vec![("Game.Pawn".to_owned(), How::Signature)]
        );
    }

    #[test]
    fn deleted_file_removes_its_members() {
        let patch = format!(
            "--- a/Pawn.cs\n+++ /dev/null\n@@ -1,{} +0,0 @@\n{}",
            OLD.lines().count(),
            OLD.lines().map(|l| format!("-{l}\n")).collect::<String>()
        );
        let files = parse(&patch);
        let found: Vec<(String, How)> = changes(&files[0], "")
            .into_iter()
            .map(|c| (c.member.key, c.how))
            .collect();
        assert!(
            found.contains(&("Game.Pawn".to_owned(), How::Removed)),
            "{found:?}"
        );
        assert!(
            found.contains(&("Game.Pawn.Heal(int)".to_owned(), How::Removed)),
            "{found:?}"
        );
    }
}
