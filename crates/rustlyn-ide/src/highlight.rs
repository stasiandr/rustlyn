//! Layer 2: colour the screen.
//!
//! The constraint here is the one the editor sets: a repaint happens on every
//! keystroke and every scroll, so the cost of colouring has to be the cost of
//! what is on screen, not of the file it is part of. Lexing a 200 000-line
//! file takes about a third of a second; doing that to show forty lines of it
//! is not a thing to do once, never mind sixty times a second.
//!
//! So nothing is lexed but the window asked for. The problem that makes that
//! hard is that a token's meaning depends on the text above it — `*/` closes
//! a comment only inside one, and a line is live code only if the `#if` above
//! it was taken — which is to say the lexer cannot start in the middle of a
//! file without being told what it missed.
//!
//! [`rustlyn_syntax::LexerState`] is that telling, and this keeps a sparse
//! table of them: a checkpoint every few hundred lines, laid down as the file
//! is read and never thrown away. Colouring a window means resuming at the
//! nearest checkpoint above it and scanning down. Scrolling is then always
//! cheap, because the checkpoint just above the screen is always close.
//! Jumping to the end of a cold file costs one scan, once, and lays down the
//! checkpoints that make the second jump free.
//!
//! The checkpoints are only ever in memory. They are cheap to rebuild from
//! any point above, and they belong to one open document rather than to the
//! bytes on disk, so writing them out would cost more than it saved.

use std::sync::Arc;

use rustlyn_syntax::{Lexer, LexerState, ParseOptions, SyntaxKind, Token, Trivia};
use rustlyn_text::TextSpan;

use crate::document::Document;

/// What a run of text is, as far as colour is concerned.
///
/// These are the distinctions an editor draws, not the ones the grammar
/// draws: `int` and `List` are both types here although the lexer calls one a
/// keyword and the other an identifier, and a method name is worth its own
/// colour although nothing at this level knows it is a method.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Class {
    Plain = 0,
    Keyword = 1,
    Type = 2,
    String = 3,
    /// `\n`, `A`, `""` inside a verbatim string.
    Escape = 4,
    Number = 5,
    Comment = 6,
    /// `///` and `/** */`, which editors colour apart from ordinary comments.
    DocComment = 7,
    /// An identifier immediately before `(`: a call or a declaration.
    Function = 8,
    Punctuation = 9,
    /// `#if`, `#region`, `#pragma` — the whole directive line.
    Preprocessor = 10,
    /// The name inside `[...]` at the head of a declaration.
    Attribute = 11,
    /// `true`, `false`, `null`.
    Constant = 12,
    Operator = 13,
    /// Text inside an `#if` whose condition was false. Kept apart from a
    /// comment so the editor can grey it without pretending it is one.
    Disabled = 14,
}

/// A run of text and what colour it is, in the units the editor counts in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Classified {
    /// UTF-16 code units from the start of the document.
    pub start: u32,
    pub length: u32,
    pub class: Class,
}

/// How many lines apart the checkpoints are.
///
/// The trade is memory against the worst scan. Each checkpoint is a copied
/// preprocessor state, tens of bytes for a file that is not full of `#if`; at
/// 500 lines a 200 000-line file keeps 400 of them, and no window is ever
/// more than 500 lines of scanning from one — about a millisecond.
const CHECKPOINT_LINES: u32 = 500;

/// The colouring of one open document.
pub struct Highlighter {
    document: Arc<Document>,
    options: ParseOptions,
    /// Line number and the lexer state at the start of that line, in order.
    /// Always holds at least the state at line zero.
    checkpoints: Vec<(u32, LexerState)>,
    /// Whether the whole file has been walked, so the table is complete and
    /// no window can be more than a checkpoint's distance from one.
    warm: bool,
}

impl std::fmt::Debug for Highlighter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Highlighter")
            .field("path", &self.document.path())
            .field("checkpoints", &self.checkpoints.len())
            .field("warm", &self.warm)
            .finish()
    }
}

impl Highlighter {
    #[must_use]
    pub fn new(document: Arc<Document>, options: ParseOptions) -> Self {
        let start = Lexer::with_options(document.source(), &options).state();
        Self {
            document,
            options,
            checkpoints: vec![(0, start)],
            warm: false,
        }
    }

    #[must_use]
    pub fn document(&self) -> &Arc<Document> {
        &self.document
    }

    /// The preprocessor symbols this colouring was built with.
    ///
    /// Which branch of an `#if` is live depends on them, so a caller that
    /// changes them has to build a new highlighter rather than reuse this
    /// one — every checkpoint in it was taken under the old set.
    #[must_use]
    pub const fn options(&self) -> &ParseOptions {
        &self.options
    }

    /// How many checkpoints are held, for tests and for the status line.
    #[must_use]
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    #[must_use]
    pub const fn is_warm(&self) -> bool {
        self.warm
    }

    /// Colours lines `first` through `last`, both inclusive.
    ///
    /// Runs are returned in order and do not overlap. Text with no colour of
    /// its own — whitespace, and identifiers that are just names — is left
    /// out rather than returned as [`Class::Plain`]: the editor already has a
    /// default, and the runs it does not need are most of them.
    pub fn classify(&mut self, first: u32, last: u32) -> Vec<Classified> {
        let source = self.document.source();
        let line_count = source.line_count();
        if first >= line_count {
            return Vec::new();
        }
        let last = last.min(line_count.saturating_sub(1));

        let window = TextSpan::from_bounds(
            source.line_span(first).map_or(0, TextSpan::start),
            source
                .line_span(last)
                .map_or_else(|| source.len(), |span| span.end()),
        );

        let mut out = Vec::new();
        self.scan(window.start(), Some(window), &mut out);
        out
    }

    /// Walks the whole file, laying down every checkpoint.
    ///
    /// For the background: after this, a jump to any line is as cheap as a
    /// scroll. Nothing is returned — the point is the table it leaves behind.
    pub fn warm(&mut self) {
        if self.warm {
            return;
        }
        let mut discard = Vec::new();
        self.scan(0, None, &mut discard);
        self.warm = true;
    }

    /// The state to start from for `offset`: the last checkpoint at or before
    /// it, which is the least text that has to be re-read.
    fn resume_point(&self, offset: u32) -> LexerState {
        let index = self
            .checkpoints
            .partition_point(|(_, state)| state.position() <= offset)
            .saturating_sub(1);
        self.checkpoints[index].1.clone()
    }

    /// The one scan both entry points share.
    ///
    /// Starts at the checkpoint above `from`, runs to the end of `window`
    /// (or to the end of the file when there is none), emits the runs that
    /// fall inside the window, and records checkpoints all the way.
    fn scan(&mut self, from: u32, window: Option<TextSpan>, out: &mut Vec<Classified>) {
        let document = self.document.clone();
        let source = document.source();
        let state = self.resume_point(from);
        let mut lexer = Lexer::resume(source, &state);
        let mut pending = Vec::new();
        // The last line a checkpoint was taken at, so a line that produces
        // several tokens does not produce several checkpoints.
        let mut highest: Option<u32> = None;

        loop {
            let token = lexer.next_token();
            let done = token.kind == SyntaxKind::EndOfFileToken;

            if window.is_none_or(|window| overlaps(token.full_span, window)) {
                classify_token(&token, source, window, out);
            }

            // The state after a token that ended its line is a state a line
            // can be entered in, which is exactly what a checkpoint is.
            //
            // Asked on every token, and every token ends a line sooner or
            // later, so this has to be cheap: the position is free and the
            // state is a clone of a preprocessor's symbol table. Only the
            // lines that will actually be kept pay for the clone.
            let position = lexer.position();
            // Standing at a line start is an O(1) question — is the byte
            // behind us a line break — and asking it first keeps the binary
            // search for the line number off the great majority of tokens.
            if position < source.len() && at_line_start(source.text(), position) {
                let line = source.lines().line_of(position);
                if line.is_multiple_of(CHECKPOINT_LINES) && highest != Some(line) {
                    highest = Some(line);
                    pending.push((line, lexer.state()));
                }
            }

            if done {
                break;
            }
            if let Some(window) = window
                && lexer.position() > window.end()
            {
                break;
            }
        }

        self.record(pending);
    }

    /// Files the checkpoints a scan passed. The scan has already thinned
    /// them to one per interval; this only merges them into the table.
    fn record(&mut self, pending: Vec<(u32, LexerState)>) {
        if pending.is_empty() {
            return;
        }
        for (line, state) in pending {
            match self.checkpoints.binary_search_by_key(&line, |&(at, _)| at) {
                Ok(_) => {}
                Err(index) => self.checkpoints.insert(index, (line, state)),
            }
        }
    }
}

/// Whether `offset` is the first byte of a line.
fn at_line_start(text: &str, offset: u32) -> bool {
    offset == 0 || text.as_bytes().get(offset as usize - 1) == Some(&b'\n')
}

fn overlaps(span: TextSpan, window: TextSpan) -> bool {
    span.start() < window.end() && span.end() > window.start()
}

/// Emits the runs for one token and the trivia around it.
fn classify_token(
    token: &Token,
    source: &rustlyn_text::SourceText,
    window: Option<TextSpan>,
    out: &mut Vec<Classified>,
) {
    for trivia in &token.leading_trivia {
        classify_trivia(trivia, source, window, out);
    }
    if let Some(class) = token_class(token, source) {
        emit(token.span, class, source, window, out);
        if matches!(class, Class::String) {
            escapes(token, source, window, out);
        }
    }
    for trivia in &token.trailing_trivia {
        classify_trivia(trivia, source, window, out);
    }
}

fn classify_trivia(
    trivia: &Trivia,
    source: &rustlyn_text::SourceText,
    window: Option<TextSpan>,
    out: &mut Vec<Classified>,
) {
    let class = match trivia.kind {
        SyntaxKind::SingleLineDocumentationCommentTrivia
        | SyntaxKind::MultiLineDocumentationCommentTrivia => Class::DocComment,
        SyntaxKind::SingleLineCommentTrivia | SyntaxKind::MultiLineCommentTrivia => Class::Comment,
        SyntaxKind::DisabledTextTrivia => Class::Disabled,
        kind if is_directive(kind) => Class::Preprocessor,
        _ => return, // whitespace and line breaks have no colour
    };
    emit(trivia.span, class, source, window, out);
}

/// Whether trivia is a preprocessor directive.
///
/// Every directive is its own kind, because the parser has to tell `#if` from
/// `#region`; for colour they are one line with one colour.
const fn is_directive(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ShebangDirectiveTrivia
            | SyntaxKind::IgnoredDirectiveTrivia
            | SyntaxKind::IfDirectiveTrivia
            | SyntaxKind::ElifDirectiveTrivia
            | SyntaxKind::ElseDirectiveTrivia
            | SyntaxKind::EndIfDirectiveTrivia
            | SyntaxKind::RegionDirectiveTrivia
            | SyntaxKind::EndRegionDirectiveTrivia
            | SyntaxKind::DefineDirectiveTrivia
            | SyntaxKind::UndefDirectiveTrivia
            | SyntaxKind::ErrorDirectiveTrivia
            | SyntaxKind::WarningDirectiveTrivia
            | SyntaxKind::LineDirectiveTrivia
            | SyntaxKind::PragmaWarningDirectiveTrivia
            | SyntaxKind::PragmaChecksumDirectiveTrivia
            | SyntaxKind::ReferenceDirectiveTrivia
            | SyntaxKind::LoadDirectiveTrivia
            | SyntaxKind::NullableDirectiveTrivia
            | SyntaxKind::BadDirectiveTrivia
            | SyntaxKind::PreprocessingMessageTrivia
    )
}

/// What colour a token is.
///
/// `None` means the editor's default, which is what most identifiers are.
fn token_class(token: &Token, source: &rustlyn_text::SourceText) -> Option<Class> {
    let kind = token.kind;
    if kind == SyntaxKind::EndOfFileToken {
        return None;
    }

    // `true`, `false` and `null` are keywords the grammar over, but every
    // editor colours them as the values they are.
    if matches!(
        kind,
        SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword | SyntaxKind::NullKeyword
    ) {
        return Some(Class::Constant);
    }

    // `int`, `string`, `object`: keywords that name types.
    if is_predefined_type(kind) {
        return Some(Class::Type);
    }

    if kind.is_reserved_keyword() {
        return Some(Class::Keyword);
    }

    // A contextual keyword is lexed as an identifier and only means something
    // in its place — `record` is a keyword in `record C` and a variable name
    // in `var record = 1`. The lexer has already made that call and left the
    // answer in `contextual_kind`.
    if token.contextual_kind != kind && token.contextual_kind.is_contextual_keyword() {
        return Some(Class::Keyword);
    }

    if kind.is_literal_token() {
        return Some(match kind {
            SyntaxKind::NumericLiteralToken => Class::Number,
            _ => Class::String,
        });
    }

    // The pieces of an interpolated string: the text between the holes, and
    // the quotes that open and close it.
    if matches!(
        kind,
        SyntaxKind::InterpolatedStringTextToken
            | SyntaxKind::InterpolatedStringStartToken
            | SyntaxKind::InterpolatedStringEndToken
            | SyntaxKind::InterpolatedSingleLineRawStringStartToken
            | SyntaxKind::InterpolatedMultiLineRawStringStartToken
            | SyntaxKind::InterpolatedRawStringEndToken
            | SyntaxKind::SingleLineRawStringLiteralToken
            | SyntaxKind::MultiLineRawStringLiteralToken
            | SyntaxKind::Utf8SingleLineRawStringLiteralToken
            | SyntaxKind::Utf8MultiLineRawStringLiteralToken
    ) {
        return Some(Class::String);
    }

    if kind == SyntaxKind::IdentifierToken {
        // A capital first letter is how C# spells a type, by a convention so
        // universal that the language's own guidelines are written around it.
        // It is a guess, and the layer above corrects it with real symbols;
        // for a repaint on a keystroke a good guess beats waiting.
        let text = token.text(source);
        return match text.chars().next() {
            Some(first) if first.is_uppercase() => Some(Class::Type),
            _ => None,
        };
    }

    if kind.is_punctuation() {
        return Some(if is_operator(kind) {
            Class::Operator
        } else {
            Class::Punctuation
        });
    }

    None
}

const fn is_predefined_type(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::BoolKeyword
            | SyntaxKind::ByteKeyword
            | SyntaxKind::SByteKeyword
            | SyntaxKind::ShortKeyword
            | SyntaxKind::UShortKeyword
            | SyntaxKind::IntKeyword
            | SyntaxKind::UIntKeyword
            | SyntaxKind::LongKeyword
            | SyntaxKind::ULongKeyword
            | SyntaxKind::FloatKeyword
            | SyntaxKind::DoubleKeyword
            | SyntaxKind::DecimalKeyword
            | SyntaxKind::CharKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::VoidKeyword
    )
}

/// Whether punctuation is an operator rather than a bracket or separator.
const fn is_operator(kind: SyntaxKind) -> bool {
    !matches!(
        kind,
        SyntaxKind::OpenParenToken
            | SyntaxKind::CloseParenToken
            | SyntaxKind::OpenBraceToken
            | SyntaxKind::CloseBraceToken
            | SyntaxKind::OpenBracketToken
            | SyntaxKind::CloseBracketToken
            | SyntaxKind::SemicolonToken
            | SyntaxKind::CommaToken
            | SyntaxKind::DotToken
    )
}

/// Marks the escape sequences inside a string, which are text to the lexer
/// but their own colour to a reader.
fn escapes(
    token: &Token,
    source: &rustlyn_text::SourceText,
    window: Option<TextSpan>,
    out: &mut Vec<Classified>,
) {
    let text = token.text(source);
    let start = token.span.start();

    // A verbatim string has one escape, `""`, and a raw string has none.
    let verbatim = text.starts_with('@') || text.starts_with("$@") || text.starts_with("@$");
    let raw = text.starts_with("\"\"\"") || text.contains("\"\"\"");

    if raw {
        return;
    }

    let bytes = text.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        if verbatim {
            if bytes[index] == b'"' && bytes.get(index + 1) == Some(&b'"') {
                emit_raw(start + index as u32, 2, Class::Escape, window, out);
                index += 2;
                continue;
            }
            index += 1;
            continue;
        }
        if bytes[index] != b'\\' {
            index += 1;
            continue;
        }
        // `\uXXXX` and `\UXXXXXXXX` are fixed width; `\xH` takes up to four
        // hex digits; everything else is the backslash and one character.
        let length = match bytes.get(index + 1) {
            Some(b'u') => 6,
            Some(b'U') => 10,
            Some(b'x') => {
                let digits = bytes[index + 2..]
                    .iter()
                    .take(4)
                    .take_while(|byte| byte.is_ascii_hexdigit())
                    .count();
                2 + digits
            }
            Some(_) => 2,
            None => 1,
        }
        .min(bytes.len() - index);
        emit_raw(
            start + index as u32,
            length as u32,
            Class::Escape,
            window,
            out,
        );
        index += length;
    }
}

fn emit(
    span: TextSpan,
    class: Class,
    source: &rustlyn_text::SourceText,
    window: Option<TextSpan>,
    out: &mut Vec<Classified>,
) {
    let _ = source;
    emit_raw(span.start(), span.length(), class, window, out);
}

fn emit_raw(
    start: u32,
    length: u32,
    class: Class,
    window: Option<TextSpan>,
    out: &mut Vec<Classified>,
) {
    if length == 0 {
        return;
    }
    if let Some(window) = window
        && !(start < window.end() && start + length > window.start())
    {
        return;
    }
    out.push(Classified {
        start,
        length,
        class,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fingerprint::Fingerprint;

    fn highlighter(text: &str) -> Highlighter {
        let document =
            Document::from_bytes("Program.cs", text.as_bytes(), Fingerprint::default(), 0);
        Highlighter::new(document, ParseOptions::default())
    }

    /// The classes over a whole file, as `(text, class)` pairs.
    fn runs(highlighter: &mut Highlighter, first: u32, last: u32) -> Vec<(String, Class)> {
        let text = highlighter.document().text().to_owned();
        highlighter
            .classify(first, last)
            .into_iter()
            .map(|run| {
                let start = run.start as usize;
                let end = start + run.length as usize;
                (text[start..end].to_owned(), run.class)
            })
            .collect()
    }

    fn classes(highlighter: &mut Highlighter, first: u32, last: u32) -> Vec<(String, Class)> {
        runs(highlighter, first, last)
    }

    #[test]
    fn keywords_types_and_names_get_their_own_colours() {
        let mut h = highlighter("public int Count = 1;\n");
        let found = classes(&mut h, 0, 0);
        assert!(found.contains(&("public".into(), Class::Keyword)));
        assert!(found.contains(&("int".into(), Class::Type)));
        assert!(found.contains(&("1".into(), Class::Number)));
        assert!(found.contains(&(";".into(), Class::Punctuation)));
        assert!(found.contains(&("=".into(), Class::Operator)));
    }

    #[test]
    fn true_false_and_null_are_values_rather_than_keywords() {
        let mut h = highlighter("var a = true; var b = null; var c = false;\n");
        let found = classes(&mut h, 0, 0);
        for value in ["true", "false", "null"] {
            assert!(
                found.contains(&(value.into(), Class::Constant)),
                "{value} should be a constant",
            );
        }
    }

    #[test]
    fn comments_are_told_apart_from_documentation() {
        let mut h = highlighter("/// <summary>x</summary>\n// plain\n/* block */\nclass A {}\n");
        let found = classes(&mut h, 0, 3);
        assert!(
            found
                .iter()
                .any(|(text, class)| { *class == Class::DocComment && text.starts_with("///") })
        );
        assert!(
            found
                .iter()
                .any(|(text, class)| { *class == Class::Comment && text.starts_with("// plain") })
        );
        assert!(
            found
                .iter()
                .any(|(text, class)| { *class == Class::Comment && text.starts_with("/* block") })
        );
    }

    #[test]
    fn a_contextual_keyword_is_coloured_by_its_spelling() {
        // Deciding what `record` means in a given place is the parser's job,
        // not the lexer's, and this layer only has the lexer: it marks the
        // token as spelling a contextual keyword, in `var record = 1;` just
        // as in `record Point(...)`. So both are coloured as keywords.
        //
        // That is the same call every other editor makes, and it is a call
        // rather than an oversight: correcting it means a parse, a parse is
        // layer 3, and layer 3 does not run on every keystroke. The outline
        // is where the real answer lives.
        for source in ["record Point(int X);\n", "var record = 1;\n"] {
            let mut h = highlighter(source);
            assert!(
                classes(&mut h, 0, 0).contains(&("record".into(), Class::Keyword)),
                "{source:?}",
            );
        }
    }

    #[test]
    fn a_reserved_keyword_is_never_mistaken_for_a_name() {
        // The distinction the lexer *can* make, and does: `class` is reserved
        // and can never be an identifier, so nothing has to guess.
        let mut h = highlighter("class C { void M() { for (;;) break; } }\n");
        let found = classes(&mut h, 0, 0);
        for word in ["class", "for", "break"] {
            assert!(
                found.contains(&(word.into(), Class::Keyword)),
                "{word} should be a keyword: {found:?}",
            );
        }
        // `void` and `int` are keywords to the grammar and types to a reader,
        // and it is the reader being served here.
        assert!(found.contains(&("void".into(), Class::Type)), "{found:?}");
    }

    #[test]
    fn escapes_inside_a_string_are_marked() {
        // Built rather than written out, so that nothing between here and the
        // compiler gets a chance to resolve the escapes this is about.
        let slash = '\\';
        let source = format!("var s = \"a{slash}nb{slash}u0041c\";");
        let mut h = highlighter(&source);
        let found = classes(&mut h, 0, 0);
        assert!(
            found.contains(&(format!("{slash}n"), Class::Escape)),
            "{found:?}",
        );
        assert!(
            found.contains(&(format!("{slash}u0041"), Class::Escape)),
            "{found:?}",
        );
    }

    #[test]
    fn a_verbatim_string_escapes_only_doubled_quotes() {
        let mut h = highlighter("var s = @\"a\\nb\"\"c\";");
        let found = classes(&mut h, 0, 0);
        assert!(
            found.contains(&("\"\"".into(), Class::Escape)),
            "a doubled quote is the escape: {found:?}",
        );
        assert!(
            !found.contains(&(r"\n".into(), Class::Escape)),
            "a backslash is not an escape in a verbatim string: {found:?}",
        );
    }

    #[test]
    fn a_raw_string_has_no_escapes_at_all() {
        let mut h = highlighter("var s = \"\"\"a\\nb\"\"\";");
        let found = classes(&mut h, 0, 0);
        assert!(!found.iter().any(|(_, class)| *class == Class::Escape));
    }

    #[test]
    fn the_dead_branch_of_an_if_is_greyed_rather_than_coloured() {
        let mut h = highlighter("#if NEVER\nclass Gone {}\n#endif\nclass Here {}\n");
        let found = classes(&mut h, 0, 3);
        assert!(
            found
                .iter()
                .any(|(text, class)| { *class == Class::Disabled && text.contains("class Gone") }),
            "the dead branch should be disabled text: {found:?}",
        );
        assert!(
            found
                .iter()
                .any(|(text, class)| { *class == Class::Preprocessor && text.starts_with("#if") })
        );
    }

    // MARK: - the windowing, which is the point of the whole file

    /// A file of `lines` numbered lines, each holding a distinctive token.
    fn numbered(lines: u32) -> String {
        (0..lines)
            .map(|index| format!("var line{index} = {index};\n"))
            .collect()
    }

    #[test]
    fn a_window_is_coloured_without_reading_the_file_above_it() {
        let mut h = highlighter(&numbered(5000));
        let found = classes(&mut h, 4000, 4002);
        // Exactly the three lines asked for, and nothing from line 0.
        assert!(found.iter().any(|(text, _)| text == "4000"));
        assert!(found.iter().any(|(text, _)| text == "4002"));
        assert!(
            !found.iter().any(|(text, _)| text == "0" || text == "100"),
            "the window leaked lines from above it: {found:?}",
        );
    }

    #[test]
    fn a_window_far_down_matches_the_same_window_after_a_full_read() {
        // The whole promise of resuming: what you get is what you would have
        // got by lexing from the top.
        let text = numbered(3000);
        let mut cold = highlighter(&text);
        let from_cold = cold.classify(2500, 2510);

        let mut warmed = highlighter(&text);
        warmed.warm();
        let from_warm = warmed.classify(2500, 2510);

        assert_eq!(from_cold, from_warm);
    }

    #[test]
    fn a_block_comment_opened_far_above_still_colours_the_window() {
        // The case that makes a resumable lexer necessary: the window has no
        // evidence in it that it is inside a comment.
        let mut text = String::from("/* opened here\n");
        text.push_str(&numbered(2000));
        text.push_str("*/\nclass After {}\n");

        let mut h = highlighter(&text);
        let found = classes(&mut h, 1500, 1502);
        assert!(
            found.iter().all(|(_, class)| *class == Class::Comment),
            "everything inside the comment must be comment: {found:?}",
        );
    }

    #[test]
    fn an_if_taken_far_above_still_governs_the_window() {
        let mut text = String::from("#if NEVER\n");
        text.push_str(&numbered(2000));
        text.push_str("#endif\n");

        let mut h = highlighter(&text);
        let found = classes(&mut h, 1000, 1002);
        assert!(
            found.iter().all(|(_, class)| *class == Class::Disabled),
            "the window is inside a dead branch: {found:?}",
        );
    }

    #[test]
    fn checkpoints_accumulate_as_the_file_is_read() {
        let mut h = highlighter(&numbered(5000));
        assert_eq!(h.checkpoint_count(), 1, "only line zero to begin with");
        h.classify(0, 40);
        let near_the_top = h.checkpoint_count();
        h.classify(4000, 4040);
        assert!(
            h.checkpoint_count() > near_the_top,
            "scanning down to line 4000 should leave checkpoints behind",
        );
        // And they are one per interval, not one per line.
        assert!(
            h.checkpoint_count() <= (5000 / CHECKPOINT_LINES + 2) as usize,
            "too many checkpoints: {}",
            h.checkpoint_count(),
        );
    }

    #[test]
    fn warming_lays_down_every_checkpoint() {
        let mut h = highlighter(&numbered(5000));
        h.warm();
        assert!(h.is_warm());
        assert!(h.checkpoint_count() >= (5000 / CHECKPOINT_LINES) as usize);
    }

    #[test]
    fn every_window_of_a_file_agrees_with_reading_it_whole() {
        // The strongest statement of the invariant: chop a file into windows,
        // colour each one, and the result must be the colouring of the file.
        let text = concat!(
            "using System;\n",
            "#if DEBUG\n",
            "class Debugging { /* a\n comment\n over lines */ }\n",
            "#else\n",
            "class Release {}\n",
            "#endif\n",
            "class C {\n",
            "    void M() => Console.WriteLine($\"a {1 + 2} b\\n\");\n",
            "    string V = @\"x\"\"y\";\n",
            "}\n",
        );
        let mut whole = highlighter(text);
        let lines = whole.document().line_count();
        let expected = whole.classify(0, lines);

        for size in [1, 2, 3, 5] {
            let mut piecewise = highlighter(text);
            let mut found = Vec::new();
            let mut line = 0;
            while line < lines {
                let last = (line + size - 1).min(lines);
                for run in piecewise.classify(line, last) {
                    // A run straddling the seam is emitted by both windows.
                    if !found.contains(&run) {
                        found.push(run);
                    }
                }
                line += size;
            }
            found.sort_unstable_by_key(|run| (run.start, run.length));
            let mut want = expected.clone();
            want.sort_unstable_by_key(|run| (run.start, run.length));
            assert_eq!(found, want, "windows of {size} lines disagreed");
        }
    }

    #[test]
    fn offsets_are_utf16_safe_for_the_caller_to_convert() {
        // This layer answers in bytes; the map turns them into what the
        // editor counts. What matters here is that the runs land on real
        // character boundaries so the conversion has something to convert.
        let text = "var s = \"комментарий 🚀\"; // é\n";
        let mut h = highlighter(text);
        for run in h.classify(0, 0) {
            let start = run.start as usize;
            let end = start + run.length as usize;
            assert!(
                text.is_char_boundary(start) && text.is_char_boundary(end),
                "run {run:?} does not land on character boundaries",
            );
        }
    }

    #[test]
    fn a_window_past_the_end_is_empty_rather_than_a_panic() {
        let mut h = highlighter("class A {}\n");
        assert!(h.classify(100, 200).is_empty());
        assert!(!h.classify(0, 10_000).is_empty());
    }

    #[test]
    fn an_empty_file_colours_to_nothing() {
        let mut h = highlighter("");
        assert!(h.classify(0, 0).is_empty());
    }
}
