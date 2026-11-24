//! Changes to text, as the layers that make them describe them.
//!
//! Everything an editor is asked to *do* rather than to show — format,
//! rename, fix, refactor — comes back as edits. Below the session they are
//! byte spans of the text the question was asked about, because that is what
//! the tree counts in; the session turns them into the editor's units once,
//! the same way it does every other offset.
//!
//! Edits to one file never overlap, and are kept in order. Applying them is
//! then one pass from the end, so that no edit moves the text another one
//! points at.

use std::path::PathBuf;

use rustlyn_text::TextSpan;

/// Replace `span` with `text`. An insertion is an empty span; a deletion is
/// empty text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub span: TextSpan,
    pub text: String,
}

impl TextEdit {
    #[must_use]
    pub fn new(span: TextSpan, text: impl Into<String>) -> Self {
        Self {
            span,
            text: text.into(),
        }
    }

    #[must_use]
    pub fn insert(at: u32, text: impl Into<String>) -> Self {
        Self::new(TextSpan::new(at, 0), text)
    }

    #[must_use]
    pub fn delete(span: TextSpan) -> Self {
        Self::new(span, String::new())
    }
}

/// The edits to one file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileEdit {
    pub path: PathBuf,
    pub edits: Vec<TextEdit>,
}

/// Edits across the project, and files to rename.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct WorkspaceEdit {
    pub files: Vec<FileEdit>,
    /// `(from, to)`: a file whose name should follow the type it declares.
    pub renames: Vec<(PathBuf, PathBuf)>,
}

impl WorkspaceEdit {
    /// Edits to a single file.
    #[must_use]
    pub fn single(path: impl Into<PathBuf>, edits: Vec<TextEdit>) -> Self {
        let mut edit = Self::default();
        edit.add_all(path, edits);
        edit
    }

    /// Adds one edit to `path`, keeping every file's edits in order.
    pub fn add(&mut self, path: impl Into<PathBuf>, edit: TextEdit) {
        self.add_all(path, vec![edit]);
    }

    /// Adds edits to `path`, keeping every file's edits in order. An edit
    /// that is exactly the same as one already there is dropped; one that
    /// overlaps another is kept, and it is the maker's business not to.
    pub fn add_all(&mut self, path: impl Into<PathBuf>, edits: Vec<TextEdit>) {
        let path = path.into();
        let file = match self.files.iter().position(|file| file.path == path) {
            Some(at) => &mut self.files[at],
            None => {
                self.files.push(FileEdit {
                    path,
                    edits: Vec::new(),
                });
                self.files.last_mut().expect("just pushed")
            }
        };
        for edit in edits {
            if !file.edits.contains(&edit) {
                file.edits.push(edit);
            }
        }
        file.edits
            .sort_by_key(|edit| (edit.span.start(), edit.span.end()));
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.files.iter().all(|file| file.edits.is_empty()) && self.renames.is_empty()
    }

    /// The edits to `path`, if any.
    #[must_use]
    pub fn edits_of(&self, path: &std::path::Path) -> &[TextEdit] {
        self.files
            .iter()
            .find(|file| file.path == path)
            .map_or(&[], |file| &file.edits)
    }
}

/// `text` with `edits` applied. The edits are byte spans of `text`, in any
/// order, and must not overlap.
#[must_use]
pub fn apply(text: &str, edits: &[TextEdit]) -> String {
    let mut sorted: Vec<&TextEdit> = edits.iter().collect();
    sorted.sort_by_key(|edit| (edit.span.start(), edit.span.end()));
    let mut out = String::with_capacity(text.len());
    let mut at = 0usize;
    for edit in sorted {
        let start = (edit.span.start() as usize).clamp(at, text.len());
        let end = (edit.span.end() as usize).clamp(start, text.len());
        out.push_str(&text[at..start]);
        out.push_str(&edit.text);
        at = end;
    }
    out.push_str(&text[at..]);
    out
}

/// The smallest set of edits that turns `old` into `new`: the common prefix
/// and suffix are kept, and what is between them replaced. Enough for a
/// formatter that rewrites whitespace, whose changes are many and small, to
/// be reported as one edit per changed stretch.
#[must_use]
pub fn diff(old: &str, new: &str) -> Vec<TextEdit> {
    if old == new {
        return Vec::new();
    }
    let prefix = old
        .char_indices()
        .zip(new.chars())
        .find(|((_, a), b)| a != b)
        .map_or_else(|| old.len().min(new.len()), |((at, _), _)| at);
    let old_rest = &old[prefix..];
    let new_rest = &new[prefix..];
    let suffix = old_rest
        .chars()
        .rev()
        .zip(new_rest.chars().rev())
        .take_while(|(a, b)| a == b)
        .map(|(a, _)| a.len_utf8())
        .sum::<usize>();
    let old_end = old.len() - suffix;
    let new_end = new.len() - suffix;
    vec![TextEdit::new(
        TextSpan::from_bounds(prefix as u32, old_end as u32),
        &new[prefix..new_end],
    )]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edits_apply_from_any_order() {
        let text = "int a = 1;";
        let edits = vec![
            TextEdit::new(TextSpan::new(8, 1), "2"),
            TextEdit::new(TextSpan::new(4, 1), "b"),
        ];
        assert_eq!(apply(text, &edits), "int b = 2;");
    }

    #[test]
    fn a_diff_is_one_edit_around_what_changed() {
        let edits = diff("a  = 1;", "a = 1;");
        assert_eq!(edits.len(), 1);
        assert_eq!(apply("a  = 1;", &edits), "a = 1;");
        assert!(diff("same", "same").is_empty());
    }

    #[test]
    fn a_workspace_edit_keeps_each_file_in_order() {
        let mut edit = WorkspaceEdit::default();
        edit.add("/p/A.cs", TextEdit::insert(5, "x"));
        edit.add("/p/A.cs", TextEdit::insert(1, "y"));
        edit.add("/p/A.cs", TextEdit::insert(1, "y"));
        let edits = edit.edits_of(std::path::Path::new("/p/A.cs"));
        assert_eq!(edits.len(), 2);
        assert_eq!(edits[0].span.start(), 1);
    }
}
