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
    /// The lines before the body: attributes, modifiers, the signature.
    pub head: Range<usize>,
    /// A type's bases as written.
    pub bases: Vec<String>,
    pub attributes: Vec<String>,
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

/// A member the change touched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    /// For a removed one, what it was.
    pub member: Member,
    pub how: How,
    /// The changed lines inside the member: new lines, a removed member's
    /// old ones.
    pub lines: Vec<usize>,
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
    /// its members is the type's.
    #[must_use]
    pub fn enclosing(&self, line: usize) -> Option<&Member> {
        self.list
            .iter()
            .filter(|m| m.lines.contains(&line))
            .min_by_key(|m| m.lines.len())
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

    for block in &file.blocks {
        for line in block.new_lines.clone() {
            if new_lines.get(line).is_some_and(|l| l.trim().is_empty()) {
                continue;
            }
            let Some(member) = new.at_line(line) else {
                continue;
            };
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
        for (k, line) in block.old_lines.clone().enumerate() {
            if block.removed.get(k).is_some_and(|l| l.trim().is_empty()) {
                continue;
            }
            let Some(was) = old.at_line(line) else {
                continue;
            };
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
                    // Lines are new ones: a removed line lands on the
                    // member's name.
                    note(now, how, now.line);
                }
                None => note(was, How::Removed, line),
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
            });
        }
    }
    let mut list: Vec<Change> = found.into_values().collect();
    for change in &mut list {
        change.lines.sort_unstable();
    }
    list.sort_by(|a, b| {
        (a.member.path.as_str(), a.member.line).cmp(&(b.member.path.as_str(), b.member.line))
    });
    list
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
    let name = d.qualified_name();
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
        head: first..head_end.min(last + 1),
        bases: d.bases.clone(),
        attributes: d.attributes.clone(),
        type_text: d.type_text.clone(),
        container: d.container.clone(),
        signature: text
            [full_start.min(text.len())..body.unwrap_or(full_end).max(full_start).min(text.len())]
            .split_whitespace()
            .collect(),
    }
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
