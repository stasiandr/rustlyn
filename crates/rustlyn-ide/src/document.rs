//! Layer 1: open the file.
//!
//! The first thing an editor owes is the text, and it owes it before it knows
//! anything else about it. So this layer does exactly one thing — turn bytes
//! into text that can be shown and edited — and deliberately does not parse,
//! index or even lex. Everything above is allowed to be slow because this is
//! not.
//!
//! What it does have to get right is what the bytes mean. A file is not a
//! string until something decides its encoding, and a file written back in
//! the wrong one is a corrupted file, so the decisions are recorded on the
//! document and handed back out when it is saved: the byte order mark, the
//! line ending, and the indentation the file already uses.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_text::SourceText;

use crate::fingerprint::Fingerprint;
use crate::utf16::Utf16Map;

/// How a file's bytes were read, so they can be written back the same way.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Encoding {
    /// UTF-8 with no byte order mark. The default, and what nearly everything
    /// is.
    #[default]
    Utf8,
    /// UTF-8 with a mark. Visual Studio writes these, and dropping the mark
    /// on save would show up as a whole-file change in `git diff`.
    Utf8Bom,
    /// UTF-16, little or big endian, as written by older Windows tools.
    Utf16Le,
    Utf16Be,
    /// Not valid UTF-8 and no mark to say what it is. Read as Latin-1, which
    /// cannot fail and keeps every byte distinct, so a save round-trips even
    /// though the characters shown may be wrong.
    Latin1,
}

impl Encoding {
    /// The bytes that introduce a file in this encoding.
    #[must_use]
    pub const fn mark(self) -> &'static [u8] {
        match self {
            Self::Utf8Bom => &[0xEF, 0xBB, 0xBF],
            Self::Utf16Le => &[0xFF, 0xFE],
            Self::Utf16Be => &[0xFE, 0xFF],
            Self::Utf8 | Self::Latin1 => &[],
        }
    }
}

/// What ends a line in this file.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum LineEnding {
    #[default]
    Lf,
    Crlf,
}

impl LineEnding {
    #[must_use]
    pub const fn text(self) -> &'static str {
        match self {
            Self::Lf => "\n",
            Self::Crlf => "\r\n",
        }
    }
}

/// The indentation the file already uses, which is what a new line should use
/// too — whatever any setting says.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Indent {
    pub tabs: bool,
    pub width: u32,
}

impl Default for Indent {
    fn default() -> Self {
        Self {
            tabs: false,
            width: 4,
        }
    }
}

/// An open file.
///
/// Immutable: an edit produces a new document rather than changing this one,
/// which is what lets background work hold on to the version it started with
/// and notice, at the end, that it is looking at an old one.
#[derive(Debug)]
pub struct Document {
    path: PathBuf,
    text: SourceText,
    /// Bumped by every edit, so an answer computed in the background can be
    /// checked against the document it was asked about.
    version: u64,
    print: Fingerprint,
    encoding: Encoding,
    line_ending: LineEnding,
    indent: Indent,
    utf16: Utf16Map,
}

impl Document {
    /// Opens a file from disk.
    pub fn open(path: impl AsRef<Path>) -> std::io::Result<Arc<Self>> {
        let path = path.as_ref();
        let (print, bytes) = Fingerprint::of_file(path)?;
        Ok(Self::from_bytes(path, &bytes, print, 0))
    }

    /// Builds a document from bytes already in hand — an editor buffer that
    /// was never on disk, or one that has moved on from what is.
    #[must_use]
    pub fn from_bytes(
        path: impl Into<PathBuf>,
        bytes: &[u8],
        print: Fingerprint,
        version: u64,
    ) -> Arc<Self> {
        let path = path.into();
        let (text, encoding) = decode(bytes);
        let line_ending = detect_line_ending(&text);
        let indent = detect_indent(&text);
        let utf16 = Utf16Map::new(&text);
        let name = path.file_name().map_or_else(
            || path.display().to_string(),
            |name| name.to_string_lossy().into_owned(),
        );
        Arc::new(Self {
            path,
            text: SourceText::new(name, text),
            version,
            print,
            encoding,
            line_ending,
            indent,
            utf16,
        })
    }

    /// The same document with different text: what an edit produces.
    #[must_use]
    pub fn with_text(&self, text: String) -> Arc<Self> {
        let print = Fingerprint::of_bytes(text.as_bytes());
        let utf16 = Utf16Map::new(&text);
        Arc::new(Self {
            path: self.path.clone(),
            text: SourceText::new(self.text.name(), text),
            version: self.version + 1,
            print,
            encoding: self.encoding,
            line_ending: self.line_ending,
            indent: self.indent,
            utf16,
        })
    }

    #[must_use]
    pub fn path(&self) -> &Path {
        &self.path
    }

    #[must_use]
    pub const fn source(&self) -> &SourceText {
        &self.text
    }

    #[must_use]
    pub fn text(&self) -> &str {
        self.text.text()
    }

    #[must_use]
    pub const fn version(&self) -> u64 {
        self.version
    }

    #[must_use]
    pub const fn fingerprint(&self) -> Fingerprint {
        self.print
    }

    #[must_use]
    pub const fn encoding(&self) -> Encoding {
        self.encoding
    }

    #[must_use]
    pub const fn line_ending(&self) -> LineEnding {
        self.line_ending
    }

    #[must_use]
    pub const fn indent(&self) -> Indent {
        self.indent
    }

    #[must_use]
    pub const fn utf16(&self) -> &Utf16Map {
        &self.utf16
    }

    #[must_use]
    pub fn line_count(&self) -> u32 {
        self.text.line_count()
    }

    /// Whether this is C#, which is the only language the layers above can
    /// speak. Everything else an editor opens is still a document; it just
    /// gets no outline, no index and no navigation from here.
    #[must_use]
    pub fn is_csharp(&self) -> bool {
        matches!(
            self.path
                .extension()
                .and_then(|extension| extension.to_str())
                .map(str::to_ascii_lowercase)
                .as_deref(),
            Some("cs" | "csx")
        )
    }

    /// The bytes to write this text back as, in the encoding it came in.
    #[must_use]
    pub fn encode(&self, text: &str) -> Vec<u8> {
        let mut bytes = self.encoding.mark().to_vec();
        match self.encoding {
            Encoding::Utf16Le => {
                for unit in text.encode_utf16() {
                    bytes.extend_from_slice(&unit.to_le_bytes());
                }
            }
            Encoding::Utf16Be => {
                for unit in text.encode_utf16() {
                    bytes.extend_from_slice(&unit.to_be_bytes());
                }
            }
            Encoding::Latin1 => {
                // Every character came from one byte, so every one goes back
                // to one. A character the editor added that does not fit
                // becomes `?`, which is what every Latin-1 encoder does.
                bytes.extend(
                    text.chars()
                        .map(|ch| u8::try_from(ch as u32).unwrap_or(b'?')),
                );
            }
            Encoding::Utf8 | Encoding::Utf8Bom => bytes.extend_from_slice(text.as_bytes()),
        }
        bytes
    }
}

/// Turns bytes into text, and says how it read them.
fn decode(bytes: &[u8]) -> (String, Encoding) {
    if let Some(rest) = bytes.strip_prefix(Encoding::Utf8Bom.mark()) {
        return (
            String::from_utf8_lossy(rest).into_owned(),
            Encoding::Utf8Bom,
        );
    }
    if let Some(rest) = bytes.strip_prefix(Encoding::Utf16Le.mark()) {
        return (decode_utf16(rest, u16::from_le_bytes), Encoding::Utf16Le);
    }
    if let Some(rest) = bytes.strip_prefix(Encoding::Utf16Be.mark()) {
        return (decode_utf16(rest, u16::from_be_bytes), Encoding::Utf16Be);
    }
    match std::str::from_utf8(bytes) {
        Ok(text) => (text.to_owned(), Encoding::Utf8),
        // Not UTF-8 and nothing said what it is. Latin-1 is the reading that
        // cannot fail and loses nothing on the way back out.
        Err(_) => (
            bytes.iter().map(|&byte| byte as char).collect(),
            Encoding::Latin1,
        ),
    }
}

fn decode_utf16(bytes: &[u8], word: fn([u8; 2]) -> u16) -> String {
    let units: Vec<u16> = bytes
        .chunks_exact(2)
        .map(|pair| word([pair[0], pair[1]]))
        .collect();
    String::from_utf16_lossy(&units)
}

/// What ends a line here, decided by which ending is in the majority rather
/// than by the first one seen: one stray `\r\n` pasted into an LF file should
/// not change how the rest of it is written.
fn detect_line_ending(text: &str) -> LineEnding {
    let mut lf = 0usize;
    let mut crlf = 0usize;
    let bytes = text.as_bytes();
    for (index, &byte) in bytes.iter().enumerate() {
        if byte == b'\n' {
            if index > 0 && bytes[index - 1] == b'\r' {
                crlf += 1;
            } else {
                lf += 1;
            }
        }
        // A thousand lines is a large enough sample to call a majority.
        if lf + crlf >= 1000 {
            break;
        }
    }
    if crlf > lf {
        LineEnding::Crlf
    } else {
        LineEnding::Lf
    }
}

/// The indentation the file uses, from the lines that are indented.
///
/// The width is the commonest positive step between one line's indentation and
/// the next's, which is what a "two spaces here, four there" file should
/// answer: the step people actually type, not the deepest line in the file.
fn detect_indent(text: &str) -> Indent {
    let mut tabs = 0usize;
    let mut spaces = 0usize;
    let mut steps = [0usize; 9];
    let mut previous = 0usize;

    for line in text.lines().take(5000) {
        let indentation: &str = &line[..line.len() - line.trim_start().len()];
        if line.trim().is_empty() {
            continue;
        }
        if indentation.starts_with('\t') {
            tabs += 1;
        } else if !indentation.is_empty() {
            spaces += 1;
        }
        let width = indentation.len();
        if width > previous
            && let Some(slot) = steps.get_mut(width - previous)
        {
            *slot += 1;
        }
        previous = width;
    }

    let width = steps
        .iter()
        .enumerate()
        .skip(2) // a one-space step is nearly always a continuation line
        .max_by_key(|&(_, count)| *count)
        .filter(|&(_, count)| *count > 0)
        .map_or(4, |(width, _)| width as u32);

    Indent {
        tabs: tabs > spaces,
        width,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn document(text: &str) -> Arc<Document> {
        Document::from_bytes("Program.cs", text.as_bytes(), Fingerprint::default(), 0)
    }

    #[test]
    fn plain_utf8_reads_as_itself() {
        let doc = document("class A {}\n");
        assert_eq!(doc.text(), "class A {}\n");
        assert_eq!(doc.encoding(), Encoding::Utf8);
    }

    #[test]
    fn a_byte_order_mark_is_remembered_rather_than_shown() {
        let mut bytes = vec![0xEF, 0xBB, 0xBF];
        bytes.extend_from_slice(b"class A {}");
        let doc = Document::from_bytes("A.cs", &bytes, Fingerprint::default(), 0);
        assert_eq!(doc.text(), "class A {}", "the mark must not be in the text");
        assert_eq!(doc.encoding(), Encoding::Utf8Bom);
        assert_eq!(doc.encode(doc.text()), bytes, "and must come back on save");
    }

    #[test]
    fn utf16_is_read_and_written_back_the_same_way() {
        for (encoding, mark, order) in [
            (Encoding::Utf16Le, [0xFF, 0xFE], true),
            (Encoding::Utf16Be, [0xFE, 0xFF], false),
        ] {
            let mut bytes = mark.to_vec();
            for unit in "class Ünïcödé {}".encode_utf16() {
                bytes.extend_from_slice(&if order {
                    unit.to_le_bytes()
                } else {
                    unit.to_be_bytes()
                });
            }
            let doc = Document::from_bytes("A.cs", &bytes, Fingerprint::default(), 0);
            assert_eq!(doc.encoding(), encoding);
            assert_eq!(doc.text(), "class Ünïcödé {}");
            assert_eq!(doc.encode(doc.text()), bytes);
        }
    }

    #[test]
    fn bytes_that_are_not_utf8_survive_a_round_trip() {
        // A Latin-1 file: `é` as one byte, which is not valid UTF-8.
        let bytes = b"// caf\xE9\nclass A {}".to_vec();
        let doc = Document::from_bytes("A.cs", &bytes, Fingerprint::default(), 0);
        assert_eq!(doc.encoding(), Encoding::Latin1);
        assert_eq!(
            doc.encode(doc.text()),
            bytes,
            "a file we cannot name the encoding of must still save unchanged",
        );
    }

    #[test]
    fn the_majority_line_ending_wins() {
        assert_eq!(detect_line_ending("a\nb\nc\r\nd\n"), LineEnding::Lf);
        assert_eq!(detect_line_ending("a\r\nb\r\nc\nd\r\n"), LineEnding::Crlf);
        assert_eq!(detect_line_ending("no line endings"), LineEnding::Lf);
    }

    #[test]
    fn indentation_is_read_from_the_file() {
        let four = "class A\n{\n    void M()\n    {\n        return;\n    }\n}\n";
        assert_eq!(
            detect_indent(four),
            Indent {
                tabs: false,
                width: 4
            }
        );

        let two = "class A\n{\n  void M()\n  {\n    return;\n  }\n}\n";
        assert_eq!(
            detect_indent(two),
            Indent {
                tabs: false,
                width: 2
            }
        );

        let tabbed = "class A\n{\n\tvoid M()\n\t{\n\t\treturn;\n\t}\n}\n";
        assert!(detect_indent(tabbed).tabs);
    }

    #[test]
    fn an_edit_makes_a_new_version_and_leaves_the_old_one_alone() {
        let first = document("class A {}");
        let second = first.with_text("class B {}".into());
        assert_eq!(first.text(), "class A {}");
        assert_eq!(second.text(), "class B {}");
        assert_eq!(second.version(), first.version() + 1);
        assert_ne!(first.fingerprint().hash, second.fingerprint().hash);
    }

    #[test]
    fn only_csharp_goes_up_the_layers() {
        for (name, csharp) in [
            ("Program.cs", true),
            ("Script.csx", true),
            ("Program.CS", true),
            ("main.rs", false),
            ("View.swift", false),
            ("noextension", false),
        ] {
            let doc = Document::from_bytes(name, b"", Fingerprint::default(), 0);
            assert_eq!(doc.is_csharp(), csharp, "{name}");
        }
    }

    #[test]
    fn a_file_with_no_text_is_still_a_document() {
        let doc = document("");
        assert_eq!(doc.text(), "");
        assert_eq!(doc.line_count(), 1);
        assert!(doc.utf16().is_ascii());
    }
}
