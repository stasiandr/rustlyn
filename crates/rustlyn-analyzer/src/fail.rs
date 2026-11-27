//! A failability report in words: how a member can fail, when, and
//! whether it can happen — for terminals (`rustlyn-fail`) and anyone who
//! wants text.
//!
//! The analysis itself is `rustlyn-ide`'s (`Semantic::failability`): the
//! failures, the conditions on the way to them, and the values of the
//! inputs across the project. Here: places as lines and columns, the
//! verdict and where the values came from, through a [`Wording`] (English
//! by default).

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rustlyn_ide::outline::DeclarationKind;
use rustlyn_ide::semantic::{Failability, Failure, FailureKind, Origin, Verdict};

/// The report's files: places in the answer are bytes, and a person reads
/// a line and a column.
#[derive(Debug, Default)]
pub struct Lines {
    files: HashMap<PathBuf, (String, Vec<usize>)>,
}

impl Lines {
    /// The line and column (one-based, the column in UTF-16 code units, as
    /// an editor and `csc` count it) of byte `offset`.
    pub fn at(&mut self, path: &Path, offset: u32) -> (usize, usize) {
        let (text, starts) = self.file(path);
        let offset = (offset as usize).min(text.len());
        let line = starts.partition_point(|&s| s <= offset).saturating_sub(1);
        let column = text
            .get(starts[line]..offset)
            .map_or(0, |t| t.encode_utf16().count());
        (line + 1, column + 1)
    }

    /// The text of a place, on one line.
    pub fn text(&mut self, path: &Path, start: u32, end: u32) -> String {
        let (text, _) = self.file(path);
        text.get(start as usize..end as usize)
            .map(|t| t.split_whitespace().collect::<Vec<_>>().join(" "))
            .unwrap_or_default()
    }

    fn file(&mut self, path: &Path) -> &(String, Vec<usize>) {
        self.files.entry(path.to_path_buf()).or_insert_with(|| {
            let text = rustlyn_ide::document::read_source(path).unwrap_or_default();
            let mut starts = vec![0];
            starts.extend(text.match_indices('\n').map(|(i, _)| i + 1));
            (text, starts)
        })
    }
}

/// The words of a report. Every method has an English default.
pub trait Wording {
    fn verdict(&self, verdict: Verdict) -> String {
        match verdict {
            Verdict::Always => "fails always, once it gets here",
            Verdict::Possible => "possible",
            Verdict::Never => "impossible",
            Verdict::Unknown => "unknown — not every input can be computed",
        }
        .to_owned()
    }

    fn kind(&self, kind: FailureKind) -> String {
        match kind {
            FailureKind::Throw => "throw",
            FailureKind::DivideByZero => "division by zero",
            FailureKind::NullReference => "null reference",
            FailureKind::IndexOutOfRange => "index out of range",
            FailureKind::Library => "library",
        }
        .to_owned()
    }

    fn origin(&self, origin: Origin) -> String {
        match origin {
            Origin::Constant => "constant".to_owned(),
            Origin::Argument => "call argument".to_owned(),
            Origin::Callers { count: 1 } => "the only call in the project".to_owned(),
            Origin::Callers { count } => format!("all calls in the project ({count})"),
            Origin::NoCallers => "no calls in the project — what comes is unknown".to_owned(),
            Origin::Escapes => {
                "the method is virtual, an override or implements an interface — calls reach it without naming it"
                    .to_owned()
            }
            Origin::EntryPoint => {
                "the runtime or a framework calls the method — what it gets is not known"
                    .to_owned()
            }
            Origin::Delegate => {
                "the method is passed as a delegate — not every call is seen".to_owned()
            }
            Origin::NamedAsDelegate => {
                "a method of this name is passed as a delegate — not every call is seen".to_owned()
            }
            Origin::ByName => {
                "called by name at run time (dynamic or reflection) — not every call is seen"
                    .to_owned()
            }
            Origin::Unread => {
                "code that may call it does not compile — not every call is seen".to_owned()
            }
            Origin::Writes { readonly: true } => "readonly: initializer and constructor".to_owned(),
            Origin::Writes { readonly: false } => "all writes in the project".to_owned(),
            Origin::NeverWritten => "never assigned — the default value".to_owned(),
            Origin::Serialized => "set by the Unity inspector".to_owned(),
            Origin::Local => "local variable".to_owned(),
            Origin::Unknown => "not computed".to_owned(),
        }
    }

    /// A condition as the analysis writes it: code as it is, and what code
    /// cannot say (`key is not in prices`) in English.
    fn condition(&self, text: &str) -> String {
        text.to_owned()
    }

    /// The labels of a failure's lines: where, through, when, and "always".
    fn where_(&self) -> String {
        "where".to_owned()
    }

    fn through(&self) -> String {
        "through".to_owned()
    }

    fn when(&self) -> String {
        "when".to_owned()
    }

    fn always(&self) -> String {
        "always".to_owned()
    }

    fn value_unknown(&self) -> String {
        "— value unknown".to_owned()
    }

    /// The head of a report of a member that cannot fail.
    fn cannot_fail(&self, member: &str) -> String {
        format!("{member} — nothing to fail with")
    }

    /// The head of a report: places that can fail, and how many of them are
    /// possible.
    fn summary(&self, member: &str, places: usize, possible: usize) -> String {
        format!("{member} — places that can fail: {places}, possible: {possible}")
    }

    /// A file without methods that can fail.
    fn nothing_in_file(&self) -> String {
        "No methods in the file can fail.".to_owned()
    }
}

/// The default words.
#[derive(Debug, Clone, Copy, Default)]
pub struct English;

impl Wording for English {}

/// Paths from the project root where possible.
fn relative(path: &Path, root: &str) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .trim_start_matches(['/', '\\'])
        .to_owned()
}

fn place(lines: &mut Lines, root: &str, path: &Path, start: u32) -> String {
    let (line, column) = lines.at(path, start);
    format!("{}:{line}:{column}", relative(path, root))
}

/// One failure: several lines of a report.
pub fn failure_text(
    failure: &Failure,
    root: &str,
    lines: &mut Lines,
    wording: &dyn Wording,
) -> String {
    let mut out = String::new();
    let message = failure
        .message
        .as_ref()
        .map(|m| format!(" «{m}»"))
        .unwrap_or_default();
    out.push_str(&format!(
        "{}{} ({}) — {}\n",
        failure.exception,
        message,
        wording.kind(failure.kind),
        wording.verdict(failure.verdict)
    ));
    out.push_str(&format!(
        "   {}: {}  {}\n",
        wording.where_(),
        place(lines, root, &failure.path, failure.span.start()),
        lines.text(&failure.path, failure.span.start(), failure.span.end())
    ));
    for step in &failure.chain {
        out.push_str(&format!(
            "   {}: {}  {}\n",
            wording.through(),
            place(lines, root, &step.path, step.span.start()),
            step.text
        ));
    }
    if failure.conditions.is_empty() {
        out.push_str(&format!("   {}: {}\n", wording.when(), wording.always()));
    } else {
        let several = failure.conditions.len() > 1;
        let all: Vec<String> = failure
            .conditions
            .iter()
            .map(|c| {
                let text = wording.condition(&c.text);
                // Joined by `&&`, a `||` or a `?:` in one would take the
                // others in.
                if several && binds_looser_than_and(&c.text) {
                    format!("({text})")
                } else {
                    text
                }
            })
            .collect();
        out.push_str(&format!("   {}: {}\n", wording.when(), all.join(" && ")));
    }
    for input in &failure.inputs {
        let values = match &input.values {
            Some(values) if values.len() == 1 => format!("= {}", values[0]),
            Some(values) => format!("∈ {{{}}}", values.join(", ")),
            None => wording.value_unknown(),
        };
        let places: Vec<String> = input
            .places
            .iter()
            .take(4)
            .map(|(p, s)| place(lines, root, p, s.start()))
            .collect();
        let places = if places.is_empty() {
            String::new()
        } else {
            format!(": {}", places.join(", "))
        };
        out.push_str(&format!(
            "   {} {values} — {}{places}\n",
            input.name,
            wording.origin(input.origin)
        ));
    }
    out
}

/// The whole report of a member.
pub fn report(found: &Failability, root: &str, lines: &mut Lines, wording: &dyn Wording) -> String {
    if found.failures.is_empty() {
        return format!("{}\n", wording.cannot_fail(&found.member));
    }
    let possible = found
        .failures
        .iter()
        .filter(|f| f.verdict != Verdict::Never)
        .count();
    let mut out = format!(
        "{}\n",
        wording.summary(&found.member, found.failures.len(), possible)
    );
    // What will happen first, then the possible, the unknown, the impossible.
    let mut order: Vec<&Failure> = found.failures.iter().collect();
    order.sort_by_key(|f| match f.verdict {
        Verdict::Always => 0,
        Verdict::Possible => 1,
        Verdict::Unknown => 2,
        Verdict::Never => 3,
    });
    for (index, failure) in order.into_iter().enumerate() {
        out.push_str(&format!(
            "{}. {}",
            index + 1,
            failure_text(failure, root, lines, wording)
        ));
    }
    out
}

// MARK: - What to ask about, from a command line

/// `File.cs:12:5`: the file, its line and column (one-based); a Windows
/// path with `C:` too.
#[must_use]
pub fn split_target(target: &str) -> (String, Option<usize>, Option<usize>) {
    let mut parts: Vec<&str> = target.rsplitn(3, ':').collect();
    parts.reverse();
    let number = |s: &str| s.parse::<usize>().ok();
    match parts.as_slice() {
        [file, line, column] if number(line).is_some() && number(column).is_some() => {
            ((*file).to_owned(), number(line), number(column))
        }
        [head, file_tail, line] if number(line).is_some() => {
            (format!("{head}:{file_tail}"), number(line), None)
        }
        [file, line] if number(line).is_some() => ((*file).to_owned(), number(line), None),
        _ => (target.to_owned(), None, None),
    }
}

/// The start of line `line` (one-based) in UTF-16.
#[must_use]
pub fn line_start_utf16(text: &str, line: usize) -> u32 {
    let byte = if line <= 1 {
        0
    } else {
        text.match_indices('\n')
            .nth(line - 2)
            .map_or(text.len(), |(i, _)| i + 1)
    };
    u32::try_from(text[..byte].encode_utf16().count()).unwrap_or(u32::MAX)
}

/// Whether a member of this kind runs code that can fail.
#[must_use]
pub const fn is_callable(kind: DeclarationKind) -> bool {
    matches!(
        kind,
        DeclarationKind::Method
            | DeclarationKind::Constructor
            | DeclarationKind::Property
            | DeclarationKind::Operator
    )
}

/// The UTF-16 offsets of the members to ask about in a file: the one on
/// `line` (at `column`, or the first callable declaration on the line), or
/// every callable one without a line. `declarations` are the outline's
/// kinds and UTF-16 name starts.
#[must_use]
pub fn offsets(
    text: &str,
    line: Option<usize>,
    column: Option<usize>,
    declarations: &[(DeclarationKind, u32)],
) -> Vec<u32> {
    let callable = declarations
        .iter()
        .filter(|(kind, _)| is_callable(*kind))
        .map(|&(_, at)| at);
    match line {
        Some(line) => {
            let start = line_start_utf16(text, line);
            if let Some(column) = column {
                return vec![start + u32::try_from(column.saturating_sub(1)).unwrap_or(0)];
            }
            let end = line_start_utf16(text, line + 1);
            vec![
                callable
                    .into_iter()
                    .find(|&at| at >= start && at < end)
                    .unwrap_or(start),
            ]
        }
        None => callable.collect(),
    }
}

/// Whether C# code has a `||`, `??`, `?:`, assignment or lambda arrow at its
/// top level, outside brackets and literals: whatever binds more loosely than
/// `&&`.
fn binds_looser_than_and(code: &str) -> bool {
    let chars: Vec<char> = code.chars().collect();
    let mut depth = 0usize;
    let mut at = 0;
    while at < chars.len() {
        let (c, next) = (chars[at], chars.get(at + 1).copied());
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            '"' | '\'' => {
                at += 1;
                while at < chars.len() && chars[at] != c {
                    at += if chars[at] == '\\' { 2 } else { 1 };
                }
            }
            '|' if depth == 0 && next == Some('|') => return true,
            '?' if depth == 0 && !matches!(next, Some('.' | '[')) => return true,
            '=' if depth == 0 && next == Some('>') => return true,
            '=' if depth == 0 && next != Some('=') => {
                // `==`, `!=`, `<=`, `>=` are comparisons; a lone `=` is not.
                let before = at.checked_sub(1).map(|i| chars[i]);
                if !matches!(before, Some('=' | '!' | '<' | '>')) {
                    return true;
                }
            }
            _ => {}
        }
        at += 1;
    }
    false
}

/// The project's `.cs` files, except tool folders.
pub fn sources(folder: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(folder) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if path.is_dir() {
            if name.starts_with('.')
                || matches!(
                    name.as_str(),
                    "Library" | "Temp" | "obj" | "bin" | "Logs" | "node_modules"
                )
            {
                continue;
            }
            sources(&path, out);
        } else if name.ends_with(".cs") {
            out.push(path);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::value::testing::TempDir;

    #[test]
    fn a_report_from_the_projects_calls() {
        let dir = TempDir::new("failability");
        let text = "class Account {\n    int balance;\n    public void Withdraw(int amount) {\n        if (amount > balance) throw new System.InvalidOperationException(\"low\");\n        balance -= amount;\n    }\n    void Use() { Withdraw(5); }\n}\n";
        dir.write("Account.cs", text);
        let root = dir.canonical();
        let path = Path::new(&root).join("Account.cs");
        let session = crate::blast::project::compiled(&root, None).expect("compiled");
        let _ = session.open(&path);
        let at = text[..text.find("Withdraw(int").expect("present")]
            .encode_utf16()
            .count();
        let found = session
            .failability(&path, u32::try_from(at).expect("small"))
            .expect("an answer");
        let report = report(&found, &root, &mut Lines::default(), &English);
        assert!(report.contains("InvalidOperationException"), "{report}");
        assert!(report.contains("where: Account.cs:4:"), "{report}");
        assert!(report.contains("when: amount > balance"), "{report}");
    }

    #[test]
    fn targets_and_offsets() {
        assert_eq!(
            split_target("A.cs:3:5"),
            ("A.cs".to_owned(), Some(3), Some(5))
        );
        assert_eq!(
            split_target("C:/a/A.cs:3"),
            ("C:/a/A.cs".to_owned(), Some(3), None)
        );
        assert_eq!(split_target("A.cs"), ("A.cs".to_owned(), None, None));
        let text = "a\nb c\n";
        assert_eq!(line_start_utf16(text, 2), 2);
        let declarations = [(DeclarationKind::Field, 0), (DeclarationKind::Method, 4)];
        assert_eq!(offsets(text, Some(2), None, &declarations), vec![4]);
        assert_eq!(offsets(text, None, None, &declarations), vec![4]);
    }

    #[test]
    fn columns_count_utf16_code_units() {
        let dir = TempDir::new("failability-columns");
        let text =
            "class C {\n    void M() { var s = \"\u{1F600}\"; throw new System.Exception(); }\n}\n";
        dir.write("C.cs", text);
        let root = dir.canonical();
        let path = Path::new(&root).join("C.cs");
        let session = crate::blast::project::compiled(&root, None).expect("compiled");
        let _ = session.open(&path);
        let at = text.find("void M").expect("present") + 5;
        let at = text[..at].encode_utf16().count();
        let found = session
            .failability(&path, u32::try_from(at).expect("small"))
            .expect("an answer");
        let report = report(&found, &root, &mut Lines::default(), &English);
        let line = text.lines().nth(1).expect("line");
        let before = &line[..line.find("throw").expect("throw")];
        let column = before.encode_utf16().count() + 1;
        assert_eq!(column, before.chars().count() + 2, "an emoji is two units");
        assert!(
            report.contains(&format!("where: C.cs:2:{column}  ")),
            "{report}"
        );
    }

    #[test]
    fn conditions_are_joined_without_one_taking_in_another() {
        let dir = TempDir::new("failability-join");
        let text = "class C {\n    void M(bool a, bool b, int c) {\n        if (a || b) { if (c > 0) throw new System.Exception(); }\n    }\n}\n";
        dir.write("C.cs", text);
        let root = dir.canonical();
        let path = Path::new(&root).join("C.cs");
        let session = crate::blast::project::compiled(&root, None).expect("compiled");
        let _ = session.open(&path);
        let at = text.find("void M").expect("present") + 5;
        let found = session
            .failability(&path, u32::try_from(at).expect("small"))
            .expect("an answer");
        let report = report(&found, &root, &mut Lines::default(), &English);
        assert!(report.contains("when: (a || b) && c > 0"), "{report}");
    }

    #[test]
    fn what_binds_looser_than_and() {
        for code in [
            "a || b",
            "a ? b : c",
            "x = y",
            "f => f",
            "a ?? b",
            "(a) || (b)",
        ] {
            assert!(binds_looser_than_and(code), "{code}");
        }
        for code in [
            "a == b",
            "a <= b",
            "a != b",
            "f(a || b)",
            "s == \"||\"",
            "a?.b",
            "xs[a ? 1 : 2]",
            "!(a || b)",
            "a && b",
            "c == '?'",
        ] {
            assert!(!binds_looser_than_and(code), "{code}");
        }
    }
}
