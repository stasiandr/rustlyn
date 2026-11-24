//! Fuzzing what an editor asks of Rustlyn.
//!
//! ```text
//! cargo run --release -p rustlyn-ide --example fuzz -- \
//!     --corpus <dir> [--corpus <dir>…] --out <dir> [--jobs 4] [--minutes 30] [--semantic]
//! cargo run --release -p rustlyn-ide --example fuzz -- --replay <out>/findings/<id>
//! cargo run --release -p rustlyn-ide --example fuzz -- --minimize <out>/findings/<id>
//! ```
//!
//! An editor hands the compiler whatever is in the buffer: half a statement,
//! an unclosed string, a paste into the middle of a generic. Every question
//! it asks has to come back. A panic is caught at the boundary and costs the
//! answer; a stack overflow or an endless loop costs the editor.
//!
//! So real C# is taken as seed — every `*.cs` under the corpus directories —
//! and broken the ways typing breaks it, and some ways typing does not:
//! deletions, duplications, splices from other files, stray tokens and
//! directives, deep nesting, truncation, odd characters. Then every question
//! of the editor surface is asked about it:
//!
//! * without a compilation: parsing (the tree must give its text back byte
//!   for byte), decoding, colouring, outline, folding, braces, selection,
//!   formatting, comments, indentation;
//! * with `--semantic`, over a compiled project: the seed and a few files
//!   beside it are compiled as they are on disk, and the broken text is the
//!   unsaved buffer, as while someone is typing — diagnostics, completion,
//!   navigation, references, hints, lenses, highlights, code actions, rename.
//!
//! A supervisor runs the workers (this program again, with `--worker`) and
//! watches them. A panic is caught in the worker. A worker that dies — a
//! stack overflow, an abort — or that stops reporting past the time limit is
//! restarted, and what it was running is kept. Each distinct failure is kept
//! once under `findings/`, with the smallest input seen for it; `--replay`
//! runs it alone, and `--minimize` shrinks it.
//!
//! Workers run on 64 MB stacks, as the editor's calls into Rustlyn do: a
//! recursion that only a 2 MB stack would not survive is not a finding.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use rustlyn_ide::semantic::{InlayHintOptions, RenameOptions};
use rustlyn_ide::session::Session;
use rustlyn_ide::structure::StructureOptions;
use rustlyn_ide::{Document, Fingerprint};
use rustlyn_syntax::{ParseOptions, parse_with};
use rustlyn_text::SourceText;

/// The stack the editor gives every call into Rustlyn.
const STACK: usize = 64 << 20;
/// Seeds larger than this make every question slow and find nothing more.
const MAX_SEED: u64 = 48 << 10;
/// A worker using more than this is stopped and its input kept.
const MEMORY_LIMIT_MB: u64 = 4096;
/// A buffer is cut to this: the size of a large hand-written file. Past it,
/// what is found is how the cost grows, which is a different question.
const MAX_BUFFER: usize = 128 << 10;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = match args.first().map(String::as_str) {
        Some("--worker") => worker(&args[1..]),
        Some("--replay") => replay(Path::new(args.get(1).expect("--replay <finding>"))),
        Some("--minimize") => minimize(Path::new(args.get(1).expect("--minimize <finding>"))),
        _ => supervise(&Options::parse(&args)),
    };
    std::process::exit(code);
}

// MARK: - options

#[derive(Debug)]
struct Options {
    corpus: Vec<PathBuf>,
    out: PathBuf,
    jobs: usize,
    limit: Duration,
    seed: u64,
    semantic: bool,
    timeout: Duration,
}

impl Options {
    fn parse(args: &[String]) -> Self {
        let mut options = Self {
            corpus: Vec::new(),
            out: PathBuf::from("fuzz-out"),
            jobs: 4,
            limit: Duration::from_secs(30 * 60),
            seed: now_seed(),
            semantic: false,
            timeout: Duration::from_secs(20),
        };
        let mut i = 0;
        while i < args.len() {
            let value = || args.get(i + 1).cloned().unwrap_or_default();
            match args[i].as_str() {
                "--corpus" => options.corpus.push(PathBuf::from(value())),
                "--out" => options.out = PathBuf::from(value()),
                "--jobs" => options.jobs = value().parse().expect("--jobs <n>"),
                "--minutes" => {
                    options.limit = Duration::from_secs_f64(
                        value().parse::<f64>().expect("--minutes <n>") * 60.0,
                    );
                }
                "--seed" => options.seed = value().parse().expect("--seed <n>"),
                "--timeout" => {
                    options.timeout =
                        Duration::from_secs(value().parse().expect("--timeout <seconds>"))
                }
                "--semantic" => {
                    options.semantic = true;
                    i += 1;
                    continue;
                }
                other => panic!("unknown option {other}"),
            }
            i += 2;
        }
        assert!(!options.corpus.is_empty(), "at least one --corpus <dir>");
        options
    }
}

fn now_seed() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(1, |since| since.as_nanos() as u64)
}

// MARK: - randomness

/// SplitMix64: small, fast, and good enough to choose what to break.
#[derive(Clone, Debug)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n`; zero when `n` is.
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() % n as u64) as usize
        }
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }

    /// Mostly small, sometimes large: the length of a range to cut or copy.
    fn span(&mut self, limit: usize) -> usize {
        let cap = match self.below(10) {
            0..=5 => 8,
            6..=8 => 64,
            _ => 4096,
        };
        1 + self.below(cap.min(limit.max(1)))
    }
}

// MARK: - the corpus

/// Every seed file, listed once by the supervisor and read by the workers
/// as they need it.
struct Corpus {
    paths: Vec<PathBuf>,
    cache: HashMap<usize, Arc<str>>,
}

impl Corpus {
    fn list(roots: &[PathBuf]) -> Vec<PathBuf> {
        let mut found = Vec::new();
        let mut stack: Vec<PathBuf> = roots.to_vec();
        while let Some(directory) = stack.pop() {
            let Ok(entries) = fs::read_dir(&directory) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let Ok(kind) = entry.file_type() else {
                    continue;
                };
                if kind.is_dir() {
                    // A Unity project's own caches and a repository's
                    // history hold nothing a person wrote.
                    let name = entry.file_name();
                    if !matches!(
                        name.to_str(),
                        Some(".git" | "Library" | "Temp" | "obj" | "bin" | "node_modules")
                    ) {
                        stack.push(path);
                    }
                } else if path.extension().is_some_and(|ext| ext == "cs")
                    && entry
                        .metadata()
                        .is_ok_and(|meta| meta.len() > 0 && meta.len() <= MAX_SEED)
                {
                    found.push(path);
                }
            }
        }
        found.sort();
        found
    }

    fn text(&mut self, index: usize) -> Arc<str> {
        if let Some(text) = self.cache.get(&index) {
            return text.clone();
        }
        let bytes = fs::read(&self.paths[index]).unwrap_or_default();
        let text: Arc<str> = String::from_utf8_lossy(&bytes).into();
        if self.cache.len() > 2000 {
            self.cache.clear();
        }
        self.cache.insert(index, text.clone());
        text
    }

    fn random(&mut self, rng: &mut Rng) -> (usize, Arc<str>) {
        let index = rng.below(self.paths.len());
        (index, self.text(index))
    }

    /// Up to `count` other files from the seed's own folder: files beside
    /// each other usually name each other. The list is sorted, so they are
    /// near the seed in it.
    fn neighbours(&self, index: usize, count: usize) -> Vec<PathBuf> {
        let Some(folder) = self.paths[index].parent() else {
            return Vec::new();
        };
        let from = index.saturating_sub(64);
        let to = (index + 64).min(self.paths.len());
        self.paths[from..to]
            .iter()
            .filter(|path| path.parent() == Some(folder) && **path != self.paths[index])
            .take(count)
            .cloned()
            .collect()
    }
}

// MARK: - breaking text

/// Pieces of C# and not-quite-C# to drop into the middle of anything.
const TOKENS: &[&str] = &[
    "{",
    "}",
    "(",
    ")",
    "[",
    "]",
    "<",
    ">",
    ";",
    ",",
    ".",
    "?",
    "??",
    "?.",
    "!",
    "=>",
    "::",
    ":",
    "=",
    "==",
    "+=",
    "??=",
    "->",
    "*",
    "&",
    "|",
    "^",
    "~",
    "..",
    "...",
    "@",
    "#",
    "$",
    "\\",
    "'",
    "\"",
    "\"\"\"",
    "$\"",
    "$@\"",
    "@$\"",
    "$$\"\"\"",
    "{{",
    "}}",
    "/*",
    "*/",
    "//",
    "///",
    "\n",
    "\r\n",
    "\r",
    "\t",
    " ",
    "class ",
    "struct ",
    "record ",
    "interface ",
    "enum ",
    "namespace N;",
    "namespace N { ",
    "using ",
    "using static ",
    "global using ",
    "static ",
    "public ",
    "partial ",
    "readonly ",
    "ref ",
    "out ",
    "in ",
    "params ",
    "this ",
    "base.",
    "new ",
    "new()",
    "new[] {",
    "stackalloc ",
    "var ",
    "void ",
    "int ",
    "string ",
    "object ",
    "dynamic ",
    "async ",
    "await ",
    "yield return ",
    "return ",
    "throw ",
    "if (",
    "else ",
    "for (;;)",
    "foreach (var x in ",
    "while (",
    "do ",
    "switch ",
    "case ",
    "default:",
    "when ",
    "is ",
    "as ",
    "not ",
    "and ",
    "or ",
    "with { ",
    "typeof(",
    "sizeof(",
    "nameof(",
    "default(",
    "checked(",
    "unchecked(",
    "delegate ",
    "operator ",
    "implicit ",
    "explicit ",
    "event ",
    "get; ",
    "set; ",
    "init; ",
    "value",
    "where T : ",
    "<T>",
    "<T, U>",
    "T?",
    "int[]",
    "int[,]",
    "(int, string)",
    "x => x",
    "(a, b) => ",
    "static () => ",
    "[Obsolete]",
    "[System.Obsolete(\"m\", true)]",
    "[OverloadResolutionPriority(1)]",
    "#if A\n",
    "#if !DEBUG && (A || B)\n",
    "#elif B\n",
    "#else\n",
    "#endif\n",
    "#define A\n",
    "#undef A\n",
    "#region r\n",
    "#endregion\n",
    "#nullable enable\n",
    "#pragma warning disable\n",
    "#line 10 \"f.cs\"\n",
    "#line hidden\n",
    "#error e\n",
    "0x",
    "0b",
    "1_000",
    "1e999",
    "1.5m",
    "99999999999999999999999999999",
    "'\\u0041'",
    "'\\x'",
    "\"\\u{",
    "\u{0}",
    "\u{FEFF}",
    "\u{200B}",
    "\u{2028}",
    "\u{2029}",
    "\u{202E}",
    "é",
    "𝒳",
    "😀",
    "\u{FFFD}",
    "__arglist",
    "unsafe { ",
    "fixed (",
    "lock (",
    "using (",
    "try { } catch ",
    "finally { }",
    "goto ",
    "extern ",
    "file ",
    "required ",
    "scoped ",
    "field",
    "extension(",
    "allows ref struct",
    "params ReadOnlySpan<int> ",
    "[.. ",
    "[1, 2, ..x]",
    "x switch { _ => 0 }",
    "x is { P: > 0 }",
    "(x, _) = ",
    "@class",
    "\u{3000}",
];

/// Openers and closers to nest a thousand deep.
const NESTS: &[(&str, &str)] = &[
    ("(", ")"),
    ("[", "]"),
    ("{", "}"),
    ("new[] { ", " }"),
    ("new List<", ">()"),
    ("$\"{", "}\""),
    ("$@\"{", "}\""),
    ("a ? b : ", ""),
    ("-", ""),
    ("!", ""),
    ("(int)", ""),
    ("x => ", ""),
    ("if (a) ", ""),
    ("#if A\n", "#endif\n"),
    ("a.", "b"),
    ("a + ", "b"),
    ("a ?? ", "b"),
    ("await ", ""),
    ("typeof(", ")"),
    ("f(", ")"),
    ("{ ", " }"),
    ("class C { ", " }"),
    ("namespace N { ", " }"),
    ("x switch { _ => ", " }"),
    ("/*", "*/"),
    ("\"", "\""),
];

/// A byte offset of `text` that is a character boundary.
fn boundary(text: &str, mut offset: usize) -> usize {
    offset = offset.min(text.len());
    while !text.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

/// The first character boundary of `text` at or after `offset`.
fn ceiling(text: &str, mut offset: usize) -> usize {
    offset = offset.min(text.len());
    while !text.is_char_boundary(offset) {
        offset += 1;
    }
    offset
}

/// A random range of `text`, on character boundaries.
fn range(text: &str, rng: &mut Rng) -> (usize, usize) {
    let start = boundary(text, rng.below(text.len() + 1));
    let end = boundary(text, start + rng.span(text.len() - start));
    (start, end.max(start))
}

/// Breaks `seed` with one to a dozen edits, and says which.
fn mutate(seed: &str, corpus: &mut Corpus, rng: &mut Rng) -> (String, Vec<String>) {
    let mut text = seed.to_string();
    let mut done = Vec::new();
    let edits = if rng.chance(15) {
        4 + rng.below(12)
    } else {
        1 + rng.below(3)
    };
    for _ in 0..edits {
        let at = boundary(&text, rng.below(text.len() + 1));
        match rng.below(12) {
            0 | 1 => {
                let token = *rng.pick(TOKENS);
                text.insert_str(at, token);
                done.push(format!("insert {token:?} at {at}"));
            }
            2 => {
                let (start, end) = range(&text, rng);
                text.replace_range(start..end, "");
                done.push(format!("delete {start}..{end}"));
            }
            3 => {
                let (start, end) = range(&text, rng);
                let copy = text[start..end].to_string();
                let to = boundary(&text, rng.below(text.len() + 1));
                text.insert_str(to, &copy);
                done.push(format!("copy {start}..{end} to {to}"));
            }
            4 => {
                let (_, other) = corpus.random(rng);
                let (start, end) = range(&other, rng);
                text.insert_str(at, &other[start..end]);
                done.push(format!("splice {} bytes at {at}", end - start));
            }
            5 => {
                text.truncate(at);
                done.push(format!("truncate at {at}"));
            }
            6 => {
                let (open, close) = *rng.pick(NESTS);
                // Mostly deep enough to matter, now and then deep enough to
                // find where it stops mattering.
                // Mostly what code has, sometimes what generated code has,
                // rarely deeper. Tens of thousands deep finds every slow
                // path at once and says nothing about which matters.
                let depth = match rng.below(20) {
                    0..=13 => 1 + rng.below(32),
                    14..=18 => 32 + rng.below(300),
                    _ => 300 + rng.below(2700),
                };
                let (start, end) = if rng.chance(50) {
                    range(&text, rng)
                } else {
                    (at, at)
                };
                let inner = text[start..end].to_string();
                let wrapped = format!("{}{}{}", open.repeat(depth), inner, close.repeat(depth));
                text.replace_range(start..end, &wrapped);
                done.push(format!(
                    "nest {open:?}{close:?} x{depth} around {start}..{end}"
                ));
            }
            7 => {
                // Whole lines: what a cut and paste in an editor moves.
                let mut lines: Vec<&str> = text.split_inclusive('\n').collect();
                if lines.len() > 1 {
                    let a = rng.below(lines.len());
                    let b = rng.below(lines.len());
                    match rng.below(3) {
                        0 => {
                            lines.remove(a);
                        }
                        1 => lines.insert(b, lines[a]),
                        _ => lines.swap(a, b),
                    }
                    text = lines.concat();
                    done.push(format!("lines {a} {b}"));
                }
            }
            8 => {
                let odd = *rng.pick(&[
                    "\u{0}",
                    "\u{FEFF}",
                    "\u{200B}",
                    "\u{2028}",
                    "\r",
                    "𝒳",
                    "\u{FFFD}",
                    "\u{D7FF}",
                    "\u{10FFFF}",
                    "\u{1D11E}",
                ]);
                text.insert_str(at, odd);
                done.push(format!("odd {odd:?} at {at}"));
            }
            9 => {
                // A character that means something, changed for another.
                let swaps = [
                    ("{", "("),
                    (";", ","),
                    ("(", "<"),
                    (")", ">"),
                    ("\"", "'"),
                    (".", "?."),
                    ("=", "=>"),
                    (" ", ""),
                ];
                let (from, to) = *rng.pick(&swaps);
                if let Some(found) = text[at..].find(from).map(|offset| offset + at) {
                    text.replace_range(found..found + from.len(), to);
                    done.push(format!("swap {from:?}->{to:?} at {found}"));
                }
            }
            10 => {
                let (start, end) = range(&text, rng);
                let most = if rng.chance(10) { 100 } else { 8 };
                let count = 2 + rng.below(most);
                let copy = text[start..end].repeat(count);
                text.replace_range(start..end, &copy);
                done.push(format!("repeat {start}..{end} x{count}"));
            }
            _ => {
                let numbers = [
                    "0",
                    "-1",
                    "2147483648",
                    "9223372036854775808",
                    "1e308",
                    "0.0000001m",
                    "0xFFFFFFFFFFFFFFFFF",
                    "1_",
                    "0b2",
                ];
                let number = *rng.pick(&numbers);
                text.insert_str(at, number);
                done.push(format!("number {number} at {at}"));
            }
        }
        if text.len() > MAX_BUFFER {
            text.truncate(boundary(&text, MAX_BUFFER));
        }
    }
    (text, done)
}

// MARK: - questions

/// One question to the editor surface: what, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Query {
    name: String,
    a: u32,
    b: u32,
    c: u32,
}

impl Query {
    fn line(&self) -> String {
        format!("{} {} {} {}", self.name, self.a, self.b, self.c)
    }

    fn parse(line: &str) -> Option<Self> {
        let mut parts = line.split_whitespace();
        let name = parts.next()?.to_string();
        let mut number = || parts.next().and_then(|part| part.parse().ok()).unwrap_or(0);
        Some(Self {
            name,
            a: number(),
            b: number(),
            c: number(),
        })
    }

    fn needs_compilation(&self) -> bool {
        SEMANTIC.contains(&self.name.as_str())
    }
}

/// Questions with no compilation behind them: what the editor asks of a file
/// the moment it is open.
const EDITOR: &[&str] = &[
    "parse",
    "decode",
    "classify",
    "warm",
    "outline",
    "structure",
    "brace",
    "selection",
    "format",
    "format_range",
    "format_on_type",
    "indent",
    "line_comment",
    "block_comment",
    "doc_typed",
    "doc_enter",
    "doc_insert",
    "trigger",
];

/// Questions over a compiled project, asked with the unsaved buffer.
const SEMANTIC: &[&str] = &[
    "diagnostics",
    "completions",
    "definition",
    "references",
    "describe",
    "quick_info",
    "signatures",
    "documentation",
    "inlay",
    "lens",
    "actions",
    "highlights",
    "semantic_tokens",
    "type_definition",
    "bases",
    "implementations",
    "derived",
    "calls",
    "types",
    "prepare_rename",
    "rename",
    "references_detailed",
    "signature_info",
    "completion_description",
];

/// Where to ask: mostly at places a person would put the caret — after a
/// dot, at a name, before a parenthesis — and sometimes anywhere.
fn caret(text: &str, rng: &mut Rng) -> u32 {
    let length = text.encode_utf16().count() as u32;
    if length == 0 {
        return 0;
    }
    if rng.chance(35) {
        return rng.below(length as usize + 1) as u32;
    }
    for _ in 0..8 {
        let at = boundary(text, rng.below(text.len()));
        let byte = text.as_bytes().get(at).copied().unwrap_or(b' ');
        let before = at
            .checked_sub(1)
            .and_then(|i| text.as_bytes().get(i))
            .copied()
            .unwrap_or(b' ');
        let interesting = before == b'.'
            || byte == b'('
            || byte == b'<'
            || (byte.is_ascii_alphabetic() && !before.is_ascii_alphanumeric());
        if interesting {
            return text[..at].encode_utf16().count() as u32;
        }
    }
    rng.below(length as usize + 1) as u32
}

fn question(name: &str, text: &str, rng: &mut Rng) -> Query {
    let a = caret(text, rng);
    let b = if rng.chance(50) {
        a
    } else {
        caret(text, rng).max(a)
    };
    let typed = *rng.pick(&['}', ';', '\n', '/', '.', '(', '<', '"', '$', '{', ' ']);
    let lines = text.matches('\n').count() as u32 + 1;
    match name {
        "classify" => {
            let first = rng.below(lines as usize) as u32;
            Query {
                name: name.into(),
                a: first,
                b: first + rng.below(80) as u32,
                c: 0,
            }
        }
        "decode" | "parse" => Query {
            name: name.into(),
            a: rng.next() as u32,
            b: 0,
            c: 0,
        },
        _ => Query {
            name: name.into(),
            a,
            b,
            c: typed as u32,
        },
    }
}

/// Parse options for `parse`: none, or the symbols a Unity project defines.
fn parse_options(which: u32) -> ParseOptions {
    match which % 3 {
        0 => ParseOptions::default(),
        1 => ParseOptions::with_symbols(["DEBUG", "UNITY_EDITOR", "UNITY_2022_3_OR_NEWER"]),
        _ => ParseOptions::with_symbols(["A", "B", "NET8_0_OR_GREATER"]),
    }
}

/// What asking came to, beyond not dying: an answer that breaks a promise.
enum Broken {
    None,
    Invariant(String),
}

/// Asks one question. `path` is the buffer's file in `session`'s project.
fn ask(session: &Session, path: &Path, text: &str, query: &Query) -> Broken {
    let buffer = Some(text);
    let (a, b) = (query.a, query.b);
    let typed = char::from_u32(query.c).unwrap_or(';');
    match query.name.as_str() {
        "parse" => {
            let tree = parse_with(SourceText::new("F.cs", text), &parse_options(query.a));
            if tree.text() != text {
                return Broken::Invariant("parse: the tree does not give its text back".into());
            }
        }
        "decode" => {
            // What a file on disk can be and a buffer cannot: bytes that are
            // not UTF-8, with or without a BOM.
            let mut bytes = text.as_bytes().to_vec();
            let mut rng = Rng(u64::from(query.a));
            for _ in 0..1 + rng.below(8) {
                if bytes.is_empty() {
                    break;
                }
                let at = rng.below(bytes.len());
                bytes[at] = *rng.pick(&[0xFF, 0xFE, 0xC0, 0x80, 0xEF, 0xBB, 0xBF, 0x00, 0xE2]);
            }
            if rng.chance(30) {
                let boms: [&[u8]; 3] = [&[0xEF, 0xBB, 0xBF], &[0xFF, 0xFE], &[0xFE, 0xFF]];
                bytes.splice(0..0, rng.pick(&boms).iter().copied());
            }
            let _ = Document::from_bytes(path, &bytes, Fingerprint::of_bytes(&bytes), 0);
        }
        "classify" => {
            session.open_text(path, text);
            let _ = session.classify(path, a, b);
        }
        "warm" => {
            session.open_text(path, text);
            let _ = session.warm(path);
        }
        "outline" => {
            session.open_text(path, text);
            let _ = session.outline(path);
        }
        "structure" => drop(session.block_structure(path, buffer, StructureOptions::default())),
        "brace" => drop(session.brace_match(path, a, buffer)),
        "selection" => drop(session.selection_ranges(path, a, b, buffer)),
        "format" => drop(session.format_document(path, buffer)),
        "format_range" => drop(session.format_range(path, a, b, buffer)),
        "format_on_type" => drop(session.format_on_type(path, a, typed, buffer)),
        "indent" => drop(session.indentation_for_new_line(path, a, buffer)),
        "line_comment" => drop(session.toggle_line_comment(path, a, b, buffer)),
        "block_comment" => drop(session.toggle_block_comment(path, a, b, buffer)),
        "doc_typed" => drop(session.doc_comment_on_typed(path, a, buffer)),
        "doc_enter" => drop(session.doc_comment_on_enter(path, a, buffer)),
        "doc_insert" => drop(session.insert_doc_comment(path, a, buffer)),
        "trigger" => drop(session.completion_trigger(text, a, typed)),
        "diagnostics" => drop(session.diagnostics(path, buffer)),
        "completions" => drop(session.completions(path, a, buffer)),
        "definition" => drop(session.definition_in(path, a, buffer)),
        "references" => drop(session.references(path, a, buffer)),
        "describe" => drop(session.describe(path, a, buffer)),
        "quick_info" => drop(session.quick_info(path, a, buffer)),
        "signatures" => drop(session.signatures(path, a, buffer)),
        "documentation" => drop(session.documentation(path, a, buffer)),
        "inlay" => {
            drop(session.inlay_hints(path, a, b.max(a), buffer, &InlayHintOptions::default()))
        }
        "lens" => drop(session.code_lens(path, buffer)),
        "actions" => drop(session.code_actions(path, a, b.max(a), buffer)),
        "highlights" => drop(session.document_highlights(path, a, buffer)),
        "semantic_tokens" => drop(session.semantic_tokens(path, a, b.max(a), buffer)),
        "type_definition" => drop(session.type_definition(path, a, buffer)),
        "bases" => drop(session.bases(path, a, buffer)),
        "implementations" => drop(session.implementations_in(path, a, buffer)),
        "derived" => drop(session.derived_types(path, a, buffer, query.c.is_multiple_of(2))),
        "calls" => {
            if let Ok(item) = session.call_hierarchy(path, a, buffer) {
                let _ = session.incoming_calls(&item.key);
                let _ = session.outgoing_calls(&item.key);
            }
        }
        "types" => {
            if let Ok(item) = session.type_hierarchy(path, a, buffer) {
                let _ = session.supertypes(&item.key);
                let _ = session.subtypes(&item.key);
            }
        }
        "prepare_rename" => drop(session.prepare_rename(path, a, buffer)),
        "rename" => drop(session.rename(path, a, "Renamed", buffer, RenameOptions::default())),
        "references_detailed" => drop(session.references_detailed(path, a, buffer)),
        "signature_info" => drop(session.signature_info(path, a, buffer)),
        "completion_description" => {
            if let Ok(list) = session.completions(path, a, buffer)
                && let Some(first) = list.items.first()
            {
                let _ = session.completion_description(path, a, buffer, &first.label);
            }
        }
        other => panic!("no such question: {other}"),
    }
    Broken::None
}

// MARK: - panics

/// The last panic anywhere in this process, as the hook saw it: Rustlyn
/// runs parts of a compile on its own threads, and a panic there reaches
/// the caller only as "a scoped thread panicked".
static LAST_PANIC: Mutex<Option<(String, String)>> = Mutex::new(None);

fn install_panic_hook(quiet: bool) {
    panic::set_hook(Box::new(move |info| {
        let location = info.location().map_or_else(
            || "?".to_string(),
            |at| format!("{}:{}", at.file(), at.line()),
        );
        let message = info
            .payload()
            .downcast_ref::<&str>()
            .map(|text| (*text).to_string())
            .or_else(|| info.payload().downcast_ref::<String>().cloned())
            .unwrap_or_default();
        // The first panic is the cause; a scope re-raising it is not news.
        let mut last = LAST_PANIC.lock().unwrap_or_else(|error| error.into_inner());
        if last.is_none() || !message.contains("a scoped thread panicked") {
            *last = Some((location.clone(), message.clone()));
        }
        if !quiet {
            eprintln!("panicked at {location}: {message}");
            // A panic in a helper — `TextSpan::from_bounds` — says nothing
            // of who called it; a replay can be asked for the stack.
            if std::env::var_os("RUST_BACKTRACE").is_some() {
                eprintln!("{}", std::backtrace::Backtrace::force_capture());
            }
        }
    }));
}

/// How one question ended.
enum Outcome {
    Fine,
    Panicked { location: String, message: String },
    Invariant(String),
}

fn run(session: &Session, path: &Path, text: &str, query: &Query) -> Outcome {
    *LAST_PANIC.lock().unwrap_or_else(|error| error.into_inner()) = None;
    match panic::catch_unwind(AssertUnwindSafe(|| ask(session, path, text, query))) {
        Ok(Broken::None) => Outcome::Fine,
        Ok(Broken::Invariant(what)) => Outcome::Invariant(what),
        Err(_) => {
            let (location, message) = LAST_PANIC
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .take()
                .unwrap_or_else(|| ("?".into(), String::new()));
            Outcome::Panicked { location, message }
        }
    }
}

// MARK: - findings

/// A failure, and the name it is kept under: one folder per distinct
/// failure, however many inputs find it.
fn signature_of(outcome: &Outcome, query: &Query) -> Option<String> {
    match outcome {
        Outcome::Fine => None,
        // A panic is known by where it happened: that is where the fix goes.
        Outcome::Panicked { location, .. } => Some(format!("panic@{}", short_location(location))),
        Outcome::Invariant(what) => Some(format!("invariant@{}@{what}", query.name)),
    }
}

/// `crates/rustlyn-semantics/src/body/calls.rs:120` — without the checkout.
fn short_location(location: &str) -> String {
    location
        .find("crates/")
        .map_or(location, |at| &location[at..])
        .to_string()
}

fn folder_name(signature: &str) -> String {
    let mut name: String = signature
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '.' {
                c
            } else {
                '-'
            }
        })
        .collect();
    name.truncate(120);
    name
}

/// Keeps a failure under `out/findings`: the buffer, the files on disk, the
/// question, and what happened. A second input for a failure already kept
/// replaces the first only if it is smaller.
fn keep(out: &Path, signature: &str, case: &Path, query: &Query, detail: &str) -> bool {
    let folder = out.join("findings").join(folder_name(signature));
    let buffer = fs::read(case.join("buffer.cs")).unwrap_or_default();
    let fresh = !folder.exists();
    if !fresh {
        let kept = fs::metadata(folder.join("buffer.cs")).map_or(u64::MAX, |meta| meta.len());
        let _ = append(&folder.join("count"), "+\n");
        if buffer.len() as u64 >= kept {
            return false;
        }
    }
    let _ = fs::create_dir_all(folder.join("disk"));
    let _ = fs::write(folder.join("buffer.cs"), &buffer);
    let _ = fs::write(folder.join("query.txt"), query.line() + "\n");
    if let Ok(entries) = fs::read_dir(folder.join("disk")) {
        for entry in entries.flatten() {
            let _ = fs::remove_file(entry.path());
        }
    }
    if let Ok(entries) = fs::read_dir(case.join("project")) {
        for entry in entries.flatten() {
            let _ = fs::copy(entry.path(), folder.join("disk").join(entry.file_name()));
        }
    }
    let _ = fs::copy(case.join("edits.txt"), folder.join("edits.txt"));
    let report = format!(
        "signature: {signature}\nquestion: {}\n{detail}\n",
        query.line()
    );
    let _ = fs::write(folder.join("report.txt"), report);
    fresh
}

fn append(path: &Path, text: &str) -> std::io::Result<()> {
    fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?
        .write_all(text.as_bytes())
}

// MARK: - the worker

/// Runs cases until told to stop, on a 64 MB stack.
fn worker(args: &[String]) -> i32 {
    let id: usize = args[0].parse().expect("worker id");
    let out = PathBuf::from(&args[1]);
    let seed: u64 = args[2].parse().expect("seed");
    let semantic = args.get(3).is_some_and(|flag| flag == "semantic");
    install_panic_hook(true);
    // The supervisor holds our stdin. When it goes, so do we: a fuzzer left
    // running with nobody reading its findings is only heat.
    std::thread::spawn(|| {
        let mut sink = [0u8; 64];
        while std::io::stdin().read(&mut sink).is_ok_and(|read| read > 0) {}
        std::process::exit(0);
    });
    let body = move || work(id, &out, seed, semantic);
    std::thread::Builder::new()
        .name("fuzz".into())
        .stack_size(STACK)
        .spawn(body)
        .expect("a worker thread")
        .join()
        .map_or(3, |()| 0)
}

fn work(id: usize, out: &Path, seed: u64, semantic: bool) {
    let mut rng = Rng(seed ^ (id as u64).wrapping_mul(0x9E37_79B9));
    let paths: Vec<PathBuf> = fs::read_to_string(out.join("corpus.txt"))
        .unwrap_or_default()
        .lines()
        .map(PathBuf::from)
        .collect();
    let mut corpus = Corpus {
        paths,
        cache: HashMap::new(),
    };
    let case = out.join("work").join(id.to_string());
    let project = case.join("project");
    let _ = fs::remove_dir_all(&case);
    fs::create_dir_all(&project).expect("a work folder");
    let session = Session::new(&project, None, Vec::new());
    let mut stdout = std::io::stdout().lock();
    let mut asked = 0u64;
    let mut last_report = Instant::now();

    loop {
        // A project: the seed and, for questions of meaning, a few files
        // from its folder — compiled as they are on disk.
        let (index, seed_text) = corpus.random(&mut rng);
        if let Ok(entries) = fs::read_dir(&project) {
            for entry in entries.flatten() {
                session.close(entry.path());
                let _ = fs::remove_file(entry.path());
            }
        }
        let path = project.join("F.cs");
        let _ = fs::write(&path, seed_text.as_bytes());
        let mut files = vec![path.clone()];
        if semantic {
            for (n, neighbour) in corpus.neighbours(index, 3).into_iter().enumerate() {
                let copy = project.join(format!("N{n}.cs"));
                if fs::copy(&neighbour, &copy).is_ok() {
                    files.push(copy);
                }
            }
            let _ = writeln!(stdout, "B compile 0 0 0");
            let _ = stdout.flush();
            let _ = fs::write(case.join("buffer.cs"), seed_text.as_bytes());
            let _ = fs::write(case.join("edits.txt"), "compile\n");
            let compiled = panic::catch_unwind(AssertUnwindSafe(|| {
                session.reindex(&files);
                session.compile(&files)
            }));
            if compiled.is_err() {
                let (location, message) = LAST_PANIC
                    .lock()
                    .unwrap_or_else(|error| error.into_inner())
                    .take()
                    .unwrap_or_default();
                let query = Query {
                    name: "compile".into(),
                    a: 0,
                    b: 0,
                    c: 0,
                };
                let outcome = Outcome::Panicked {
                    location,
                    message: message.clone(),
                };
                if let Some(signature) = signature_of(&outcome, &query)
                    && keep(
                        out,
                        &signature,
                        &case,
                        &query,
                        &format!("message: {message}"),
                    )
                {
                    let _ = writeln!(stdout, "F {signature}");
                }
                continue;
            }
        }

        // Many broken versions of the seed against the one compilation.
        let rounds = if semantic { 25 } else { 4 };
        for _ in 0..rounds {
            let (text, edits) = mutate(&seed_text, &mut corpus, &mut rng);
            let _ = fs::write(case.join("buffer.cs"), text.as_bytes());
            let _ = fs::write(case.join("edits.txt"), edits.join("\n") + "\n");
            let mut names: Vec<&str> = EDITOR.to_vec();
            if semantic {
                // All of the editor's questions are cheap; of the others a
                // handful per buffer, so that there are many buffers.
                names = EDITOR.iter().filter(|_| rng.chance(30)).copied().collect();
                for _ in 0..6 {
                    names.push(*rng.pick(SEMANTIC));
                }
            }
            for name in names {
                let query = question(name, &text, &mut rng);
                // Where we are, before we are there: if this is the question
                // that never comes back, the supervisor knows which it was.
                let _ = writeln!(stdout, "B {}", query.line());
                let _ = stdout.flush();
                let outcome = run(&session, &path, &text, &query);
                asked += 1;
                if let Some(signature) = signature_of(&outcome, &query) {
                    let detail = match &outcome {
                        Outcome::Panicked { location, message } => {
                            format!("location: {location}\nmessage: {message}")
                        }
                        Outcome::Invariant(what) => format!("invariant: {what}"),
                        Outcome::Fine => String::new(),
                    };
                    if keep(out, &signature, &case, &query, &detail) {
                        let _ = writeln!(stdout, "F {signature}");
                    }
                }
            }
            if last_report.elapsed() > Duration::from_secs(2) {
                let _ = writeln!(stdout, "S {asked}");
                let _ = stdout.flush();
                last_report = Instant::now();
            }
        }
    }
}

// MARK: - the supervisor

struct Watched {
    child: Child,
    started: Instant,
    /// The question it last said it was starting, and when.
    beat: Arc<Mutex<(String, Instant)>>,
    asked: Arc<Mutex<u64>>,
}

fn spawn_worker(
    id: usize,
    options: &Options,
    restarts: u64,
    found: &Arc<Mutex<Vec<String>>>,
) -> Watched {
    let work = options.out.join("work");
    let _ = fs::create_dir_all(&work);
    let stderr = fs::File::create(work.join(format!("{id}.err"))).expect("a stderr file");
    let seed = options.seed ^ restarts.wrapping_mul(0xA5A5_5A5A_1234_5678);
    let mut command = Command::new(std::env::current_exe().expect("this program"));
    command
        .arg("--worker")
        .arg(id.to_string())
        .arg(&options.out)
        .arg(seed.to_string());
    if options.semantic {
        command.arg("semantic");
    }
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::from(stderr))
        .spawn()
        .expect("a worker");
    let beat = Arc::new(Mutex::new(("start 0 0 0".to_string(), Instant::now())));
    let asked = Arc::new(Mutex::new(0u64));
    let stdout = child.stdout.take().expect("piped");
    let (beat_in, asked_in, found_in) = (beat.clone(), asked.clone(), found.clone());
    std::thread::spawn(move || {
        for line in BufReader::new(stdout).lines().map_while(Result::ok) {
            if let Some(query) = line.strip_prefix("B ") {
                *beat_in.lock().unwrap_or_else(|error| error.into_inner()) =
                    (query.to_string(), Instant::now());
            } else if let Some(count) = line.strip_prefix("S ") {
                *asked_in.lock().unwrap_or_else(|error| error.into_inner()) =
                    count.parse().unwrap_or(0);
            } else if let Some(signature) = line.strip_prefix("F ") {
                found_in
                    .lock()
                    .unwrap_or_else(|error| error.into_inner())
                    .push(signature.to_string());
            }
        }
    });
    Watched {
        child,
        started: Instant::now(),
        beat,
        asked,
    }
}

/// What killed a worker, from how it ended and what it printed.
fn death(status: Option<ExitStatus>, stderr: &str) -> &'static str {
    let signal = status.and_then(signal);
    if stderr.contains("has overflowed its stack") {
        "stack-overflow"
    } else if stderr.contains("memory allocation of") || stderr.contains("capacity overflow") {
        "allocation"
    } else if stderr.contains("fatal runtime error") || signal == Some(SIGABRT) {
        "abort"
    } else if signal.is_some() {
        "signal"
    } else {
        "exit"
    }
}

const SIGABRT: i32 = 6;

/// The signal that ended the worker.
#[cfg(unix)]
fn signal(status: ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;
    status.signal()
}

/// Windows has no signals: a crash ends the process with an NTSTATUS error
/// code (0xC…). `abort` is a fast fail, STATUS_STACK_BUFFER_OVERRUN.
#[cfg(windows)]
fn signal(status: ExitStatus) -> Option<i32> {
    const STATUS_STACK_BUFFER_OVERRUN: u32 = 0xC000_0409;
    let code = status.code()? as u32;
    match code {
        STATUS_STACK_BUFFER_OVERRUN => Some(SIGABRT),
        _ if code >= 0xC000_0000 => Some(code as i32),
        _ => None,
    }
}

#[cfg(not(any(unix, windows)))]
fn signal(_: ExitStatus) -> Option<i32> {
    None
}

/// Where a hung worker is, from macOS's `sample`: the function of Rustlyn
/// its stack holds most often, and the stack itself.
///
/// The innermost frame is where the time is spent, not why: a blow-up in
/// the parser spends it in allocation, spans, clones — a new finding for
/// each. The function that recurs is the one doing the blowing up; when
/// nothing recurs, the innermost function of Rustlyn is the loop.
fn stuck_in(pid: u32) -> (Option<String>, String) {
    let Ok(out) = Command::new("sample")
        .args([&pid.to_string(), "1", "-mayDie"])
        .output()
    else {
        return (None, String::new());
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut stack: Vec<String> = Vec::new();
    let mut in_fuzz = false;
    for line in text.lines() {
        if line.contains("Thread_") {
            in_fuzz = line.contains("fuzz");
            continue;
        }
        if !in_fuzz {
            continue;
        }
        let Some(name) = line
            .split_whitespace()
            .find(|word| word.starts_with("_RN") || word.contains("rustlyn"))
        else {
            continue;
        };
        let readable = demangle(name);
        let ours = readable.starts_with("rustlyn_") && !readable.contains("fuzz");
        if ours && stack.last() != Some(&readable) {
            stack.push(readable);
        }
    }
    let mut counts: HashMap<&str, usize> = HashMap::new();
    for frame in &stack {
        *counts.entry(frame.as_str()).or_default() += 1;
    }
    let most = counts.values().copied().max().unwrap_or(0);
    let place = if most > 1 {
        // The outermost of the functions that recur most: the recursion's
        // entry, which is where a fix goes.
        stack
            .iter()
            .find(|frame| counts[frame.as_str()] == most)
            .cloned()
    } else {
        stack.last().cloned()
    };
    let place = place.map(|name| name.replace("rustlyn_", "").replace("::", "."));
    (place, stack.join("\n"))
}

/// Enough of Rust's v0 mangling to read a path: `_RNvMs_NtCs…_11rustlyn_ide6format6Engine3run`
/// is `rustlyn_ide::format::Engine::run`. Hashes and generics are left out.
fn demangle(symbol: &str) -> String {
    let bytes = symbol.as_bytes();
    let mut parts: Vec<&str> = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        // `Cs` starts a crate's disambiguating hash and `B` a back-reference;
        // both run to `_` and have digits in them that are not lengths.
        if symbol[i..].starts_with("Cs") || bytes[i] == b'B' {
            i = symbol[i..].find('_').map_or(bytes.len(), |end| i + end + 1);
            continue;
        }
        if bytes[i].is_ascii_digit() && (i == 0 || !bytes[i - 1].is_ascii_digit()) {
            let mut j = i;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            let length: usize = symbol[i..j].parse().unwrap_or(0);
            // A leading `_` separates a length from an identifier that
            // starts with a digit or an underscore.
            let start = if bytes.get(j) == Some(&b'_') {
                j + 1
            } else {
                j
            };
            if length > 0 && start + length <= bytes.len() {
                let word = &symbol[start..start + length];
                if word.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                    parts.push(word);
                }
                i = start + length;
                continue;
            }
            i = j;
        } else {
            i += 1;
        }
    }
    if parts.is_empty() {
        symbol.to_string()
    } else {
        parts.join("::")
    }
}

fn resident_mb(pid: u32) -> u64 {
    Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()
        .and_then(|out| {
            String::from_utf8_lossy(&out.stdout)
                .trim()
                .parse::<u64>()
                .ok()
        })
        .map_or(0, |kb| kb / 1024)
}

fn supervise(options: &Options) -> i32 {
    fs::create_dir_all(options.out.join("findings")).expect("an output folder");
    let corpus = Corpus::list(&options.corpus);
    assert!(!corpus.is_empty(), "no *.cs under the corpus folders");
    let list: String = corpus
        .iter()
        .map(|path| format!("{}\n", path.display()))
        .collect();
    fs::write(options.out.join("corpus.txt"), list).expect("the corpus list");
    println!(
        "fuzz: {} seed files, {} workers, {}, {:?} per question, seed {}",
        corpus.len(),
        options.jobs,
        if options.semantic {
            "editor and meaning"
        } else {
            "editor"
        },
        options.timeout,
        options.seed
    );

    let found = Arc::new(Mutex::new(Vec::new()));
    let mut restarts = 0u64;
    let mut workers: Vec<Watched> = (0..options.jobs)
        .map(|id| spawn_worker(id, options, 0, &found))
        .collect();
    let started = Instant::now();
    let mut last_status = Instant::now();
    let mut last_memory_check = Instant::now();
    let mut asked_before_restart = 0u64;
    let mut kept: HashSet<String> = HashSet::new();

    while started.elapsed() < options.limit {
        std::thread::sleep(Duration::from_millis(250));
        // Memory is asked of `ps`, which is a process of its own: every few
        // seconds is often enough to catch a worker running away.
        let check_memory = last_memory_check.elapsed() > Duration::from_secs(5);
        if check_memory {
            last_memory_check = Instant::now();
        }
        for (id, watched) in workers.iter_mut().enumerate() {
            let mut hang_place: Option<String> = None;
            let (query_line, since) = watched
                .beat
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .clone();
            let query = Query::parse(&query_line).unwrap_or(Query {
                name: "start".into(),
                a: 0,
                b: 0,
                c: 0,
            });
            let case = options.out.join("work").join(id.to_string());
            // Compiling a project for the first time reads every reference;
            // it gets longer than a question does.
            let limit = if query.name == "compile" {
                options.timeout * 6
            } else {
                options.timeout
            };
            let exited = watched.child.try_wait().ok().flatten();
            let verdict = if let Some(status) = exited {
                let stderr = fs::read_to_string(options.out.join("work").join(format!("{id}.err")))
                    .unwrap_or_default();
                let tail: String = stderr
                    .lines()
                    .rev()
                    .take(12)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev()
                    .collect::<Vec<_>>()
                    .join("\n");
                Some((
                    death(Some(status), &stderr),
                    format!("status: {status}\nstderr:\n{tail}"),
                ))
            } else if since.elapsed() > limit {
                // Where it is stuck, before it goes: two hangs in the same
                // function are one finding, whichever question led there.
                let (place, stack) = stuck_in(watched.child.id());
                let _ = watched.child.kill();
                let _ = watched.child.wait();
                hang_place = place;
                Some((
                    "hang",
                    format!("no answer in {:?}\nstack:\n{stack}", since.elapsed()),
                ))
            } else if check_memory && resident_mb(watched.child.id()) > MEMORY_LIMIT_MB {
                let _ = watched.child.kill();
                let _ = watched.child.wait();
                Some(("memory", format!("over {MEMORY_LIMIT_MB} MB")))
            } else {
                None
            };
            if let Some((kind, detail)) = verdict {
                let signature = match hang_place.take() {
                    Some(place) => format!("{kind}@{place}"),
                    None => format!("{kind}@{}", query.name),
                };
                if keep(&options.out, &signature, &case, &query, &detail) {
                    found
                        .lock()
                        .unwrap_or_else(|error| error.into_inner())
                        .push(signature);
                }
                asked_before_restart += *watched
                    .asked
                    .lock()
                    .unwrap_or_else(|error| error.into_inner());
                restarts += 1;
                // A worker that dies at once, again and again, is a broken
                // setup, not a finding: stop rather than spin.
                if watched.started.elapsed() < Duration::from_secs(2) && kind == "exit" {
                    eprintln!("fuzz: worker {id} exits at start:\n{detail}");
                    return 2;
                }
                *watched = spawn_worker(id, options, restarts, &found);
            }
        }
        for signature in found
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .drain(..)
        {
            if kept.insert(signature.clone()) {
                println!("fuzz: new finding {signature}");
            }
        }
        if last_status.elapsed() > Duration::from_secs(10) {
            let asked: u64 = asked_before_restart
                + workers
                    .iter()
                    .map(|w| *w.asked.lock().unwrap_or_else(|error| error.into_inner()))
                    .sum::<u64>();
            let seconds = started.elapsed().as_secs();
            println!(
                "fuzz: {seconds}/{} s, {asked} questions ({}/s), {} findings, {restarts} restarts",
                options.limit.as_secs(),
                asked / seconds.max(1),
                kept.len()
            );
            last_status = Instant::now();
        }
    }
    for watched in &mut workers {
        let _ = watched.child.kill();
        let _ = watched.child.wait();
    }
    println!(
        "fuzz: done, {} findings under {}",
        kept.len(),
        options.out.join("findings").display()
    );
    0
}

// MARK: - replay and minimize

/// Runs one kept finding again, alone: 0 when it no longer fails, 101 with
/// `PANIC <signature>` or `INVARIANT <signature>` on stdout when it does. A
/// crash or a hang is not reported — this process simply dies or does not
/// come back, which is what `--minimize` looks for.
fn replay(finding: &Path) -> i32 {
    install_panic_hook(false);
    let finding = finding.to_path_buf();
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || replay_here(&finding))
        .expect("a replay thread")
        .join()
        .unwrap_or(3)
}

fn replay_here(finding: &Path) -> i32 {
    let text = fs::read_to_string(finding.join("buffer.cs")).unwrap_or_default();
    let query = fs::read_to_string(finding.join("query.txt"))
        .ok()
        .and_then(|line| Query::parse(line.trim()))
        .expect("a query.txt");
    let project = std::env::temp_dir().join(format!("rustlyn-fuzz-replay-{}", std::process::id()));
    let _ = fs::remove_dir_all(&project);
    fs::create_dir_all(&project).expect("a replay folder");
    let mut files = Vec::new();
    if let Ok(entries) = fs::read_dir(finding.join("disk")) {
        for entry in entries.flatten() {
            let copy = project.join(entry.file_name());
            let _ = fs::copy(entry.path(), &copy);
            files.push(copy);
        }
    }
    let path = project.join("F.cs");
    if !path.exists() {
        let _ = fs::write(&path, &text);
        files.push(path.clone());
    }
    let session = Session::new(&project, None, Vec::new());
    let code = if query.name == "compile" || query.needs_compilation() {
        let compiled = panic::catch_unwind(AssertUnwindSafe(|| {
            session.reindex(&files);
            session.compile(&files)
        }));
        match compiled {
            Err(_) => report(
                &Outcome::Panicked {
                    location: LAST_PANIC
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .take()
                        .unwrap_or_default()
                        .0,
                    message: String::new(),
                },
                &query,
            ),
            Ok(_) if query.name == "compile" => 0,
            Ok(_) => report(&run(&session, &path, &text, &query), &query),
        }
    } else {
        report(&run(&session, &path, &text, &query), &query)
    };
    let _ = fs::remove_dir_all(&project);
    code
}

fn report(outcome: &Outcome, query: &Query) -> i32 {
    match (outcome, signature_of(outcome, query)) {
        (Outcome::Panicked { .. }, Some(signature)) => {
            println!("PANIC {signature}");
            101
        }
        (Outcome::Invariant(_), Some(signature)) => {
            println!("INVARIANT {signature}");
            101
        }
        _ => {
            println!("OK");
            0
        }
    }
}

/// Shrinks a finding's buffer while it still fails the same way, by
/// replaying each candidate in a child: a crash or a hang cannot be caught
/// in-process. Offsets in the question move with the text they point into.
fn minimize(finding: &Path) -> i32 {
    let report = fs::read_to_string(finding.join("report.txt")).unwrap_or_default();
    let signature = report
        .lines()
        .find_map(|line| line.strip_prefix("signature: "))
        .expect("a report.txt with a signature")
        .to_string();
    let kind = signature.split('@').next().unwrap_or("").to_string();
    let query = fs::read_to_string(finding.join("query.txt"))
        .ok()
        .and_then(|line| Query::parse(line.trim()))
        .expect("a query.txt");
    let mut text = fs::read_to_string(finding.join("buffer.cs")).expect("a buffer.cs");
    let mut query = query;
    let scratch = std::env::temp_dir().join(format!("rustlyn-fuzz-min-{}", std::process::id()));
    let _ = fs::remove_dir_all(&scratch);
    fs::create_dir_all(scratch.join("disk")).expect("a scratch folder");
    if let Ok(entries) = fs::read_dir(finding.join("disk")) {
        for entry in entries.flatten() {
            let _ = fs::copy(entry.path(), scratch.join("disk").join(entry.file_name()));
        }
    }
    // A hang is confirmed by waiting; a shorter wait than the fuzzer's keeps
    // this finite, and what still hangs for it hangs for the fuzzer.
    let timeout = Duration::from_secs(if kind == "hang" { 8 } else { 30 });
    let fails = |candidate: &str, query: &Query| -> bool {
        let _ = fs::write(scratch.join("buffer.cs"), candidate);
        let _ = fs::write(scratch.join("query.txt"), query.line() + "\n");
        still_fails(&scratch, &kind, &signature, timeout)
    };
    if !fails(&text, &query) {
        println!("minimize: {signature} does not fail on replay");
        return 1;
    }
    let started = Instant::now();
    // Lines first, then characters, halving the chunk each time nothing
    // more can be cut.
    for by_lines in [true, false] {
        let mut chunk = (text.len() / 2).max(1);
        while chunk >= 1 {
            let mut cut_any = false;
            let mut at = 0;
            while at < text.len() {
                let (start, end) = if by_lines {
                    let lines: Vec<usize> = std::iter::once(0)
                        .chain(text.match_indices('\n').map(|(i, _)| i + 1))
                        .collect();
                    let lines_per = (chunk / 40).max(1);
                    let first = lines.partition_point(|&start| start < at);
                    let Some(&start) = lines.get(first) else {
                        break;
                    };
                    let end = lines.get(first + lines_per).copied().unwrap_or(text.len());
                    (start, end)
                } else {
                    // Rounded down at the start and up at the end, so that
                    // a cut is never empty short of the end of the text:
                    // rounding both down stalled inside a multi-byte
                    // character.
                    let start = boundary(&text, at);
                    (start, ceiling(&text, start + chunk))
                };
                if start >= end {
                    break;
                }
                let mut candidate = text.clone();
                candidate.replace_range(start..end, "");
                let moved = shift(&query, &text, start, end);
                if fails(&candidate, &moved) {
                    text = candidate;
                    query = moved;
                    cut_any = true;
                } else {
                    at = end;
                }
            }
            if !cut_any {
                if chunk == 1 {
                    break;
                }
                chunk /= 2;
            }
            if started.elapsed() > Duration::from_secs(600) {
                break;
            }
        }
    }
    let _ = fs::write(finding.join("buffer.min.cs"), &text);
    let _ = fs::write(finding.join("query.min.txt"), query.line() + "\n");
    let _ = fs::remove_dir_all(&scratch);
    println!(
        "minimize: {signature}: {} bytes, {}",
        text.len(),
        query.line()
    );
    0
}

/// The question after `start..end` (bytes) is cut from `text`: an offset
/// past the cut moves back by its length in UTF-16, one inside it goes to
/// where it began.
fn shift(query: &Query, text: &str, start: usize, end: usize) -> Query {
    if matches!(query.name.as_str(), "classify" | "parse" | "decode") {
        return query.clone();
    }
    let from = text[..start].encode_utf16().count() as u32;
    let length = text[start..end].encode_utf16().count() as u32;
    let moved = |offset: u32| {
        if offset >= from + length {
            offset - length
        } else if offset > from {
            from
        } else {
            offset
        }
    };
    Query {
        name: query.name.clone(),
        a: moved(query.a),
        b: moved(query.b),
        c: query.c,
    }
}

/// Replays `scratch` in a child and says whether it failed as `signature`.
fn still_fails(scratch: &Path, kind: &str, signature: &str, timeout: Duration) -> bool {
    let Ok(mut child) = Command::new(std::env::current_exe().expect("this program"))
        .arg("--replay")
        .arg(scratch)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    else {
        return false;
    };
    let started = Instant::now();
    let mut checked = Instant::now();
    loop {
        // Memory that runs away runs away fast: a quarter of the limit the
        // fuzzer uses is proof enough, and keeps the machine usable.
        if kind == "memory" && checked.elapsed() > Duration::from_millis(100) {
            checked = Instant::now();
            if resident_mb(child.id()) > MEMORY_LIMIT_MB / 4 {
                let _ = child.kill();
                let _ = child.wait();
                return true;
            }
        }
        match child.try_wait() {
            Ok(Some(status)) => {
                let mut stdout = String::new();
                let mut stderr = String::new();
                if let Some(mut out) = child.stdout.take() {
                    let _ = out.read_to_string(&mut stdout);
                }
                if let Some(mut err) = child.stderr.take() {
                    let _ = err.read_to_string(&mut stderr);
                }
                return match kind {
                    "panic" | "invariant" => stdout.lines().any(|line| line.ends_with(signature)),
                    "hang" | "memory" => false,
                    _ => death(Some(status), &stderr) == kind,
                };
            }
            Ok(None) if started.elapsed() > timeout => {
                let _ = child.kill();
                let _ = child.wait();
                return kind == "hang";
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(_) => return false,
        }
    }
}
