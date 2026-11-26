//! The C# parser.
//!
//! A hand-written recursive-descent parser that builds green nodes bottom up,
//! the way Roslyn's does. Three properties matter more than speed here:
//!
//! * **It never fails.** Broken input still produces a tree, because an IDE has
//!   to keep working while you are halfway through typing a statement. Missing
//!   pieces become zero-width tokens and stray ones are kept as skipped tokens,
//!   so the grammar's shape survives and no text is lost.
//! * **It keeps every byte.** Whatever the parser does with a token, the token
//!   stays in the tree, so the root still prints back as the original file.
//! * **It looks ahead by backtracking.** C# is not LL(k): telling `(x)` the
//!   cast from `(x)` the parenthesised expression, or `a < b` from `a<b>()`,
//!   needs a real attempt at parsing. The parser takes a reset point, tries,
//!   and rewinds — which is what Roslyn's `ResetPoint` does.

mod declarations;
mod expressions;
mod facts;
mod patterns;
mod query;
mod statements;
mod types;

use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

use rustlyn_diagnostics::{Diagnostic, DiagnosticBag, ErrorCode};
use rustlyn_text::{SourceText, TextSpan};

use facts::Precedence;

use crate::green::{GreenCache, GreenElement, GreenNode, GreenToken, green_token, green_token_as};
use crate::{ParseOptions, SyntaxKind, SyntaxTree, Token, tokenize_with};

/// Parses a source file into a syntax tree.
///
/// Always succeeds: syntax errors come back in
/// [`SyntaxTree::diagnostics`](crate::SyntaxTree::diagnostics), not as a
/// failure.
#[must_use]
pub fn parse(source: SourceText) -> SyntaxTree {
    parse_with(source, &ParseOptions::default())
}

/// Parses a source file with the given options.
#[must_use]
pub fn parse_with(source: SourceText, options: &ParseOptions) -> SyntaxTree {
    let lexed = tokenize_with(&source, options);
    let definitions = lexed.definitions;
    let mut parser = Parser::new(source.clone(), lexed.tokens, lexed.diagnostics);
    // The trivia and tokens one file shares, the next file on this thread
    // can share too: `;` and a newline are the same everywhere.
    if let Some(cache) = GREEN.with(|green| green.borrow_mut().take()) {
        parser.cache = cache;
    }
    let root = parser.parse_compilation_unit();
    GREEN.with(|green| *green.borrow_mut() = Some(std::mem::take(&mut parser.cache)));
    // Without the replays, each diagnostic has the one owner to move out of.
    parser.replays.clear();
    let mut diagnostics = DiagnosticBag::new();
    // Said here and not where the parse stopped: that may have been inside
    // a look ahead, whose diagnostics are thrown away with it.
    let too_deep = parser.too_deep.then(|| {
        Diagnostic::new(
            ErrorCode::ErrInsufficientStack,
            parser.tokens[parser.end].span,
            &[],
        )
    });
    diagnostics.extend(parser.diagnostics.into_iter().map(Rc::unwrap_or_clone));
    diagnostics.extend(too_deep);
    diagnostics.sort();
    SyntaxTree::with_defined(
        source,
        root,
        diagnostics.into_vec(),
        options.preprocessor_symbols.clone(),
    )
    .with_definitions(definitions)
    .with_language_version(options.language_version)
}

/// How deep the parser's own recursion goes before it stops reading the
/// file: nested parentheses, blocks, type arguments, patterns and types
/// declared inside types each take a level. The parser recurses as the
/// source nests, and source that nests without end — a file of a hundred
/// thousand `(`, which a fuzzer or a broken generator writes and nobody
/// else — ran the thread out of stack, which no caller can catch. Roslyn
/// asks the runtime whether stack is left and reports CS8078; a fixed depth
/// gives the same file the same answer on every machine and in every build,
/// and an optimized parser takes this many levels in under a megabyte of
/// stack, a main thread's on any system (an unoptimized one, several times
/// that). A thousand levels is what the editor's own tests nest blocks to;
/// nothing written by hand comes near. What is long and not nested — a chain
/// of operators or calls, a ladder of `else if` or `?:` — is read in a loop
/// and costs no level here, only depth in the tree ([`MAX_DEPTH`]).
pub(crate) const MAX_NESTING: u32 = 1024;

/// How deep a tree the parser hands out ([`GreenNode::height`]). A chain
/// — `a + b + c + …`, `a.b().c().d()…` — and a ladder — `if … else if …`,
/// `a ? x : b ? y : …` — take no recursion to read and still make a tree as
/// deep as they are long, which everything after the parser walks by
/// recursion: binding, lowering, the emitter, the editor. Generated code
/// writes thousands of rungs and terms in one statement (Roslyn compiles
/// five thousand), so this is well above [`MAX_NESTING`]: 12,288 levels are
/// about 6,100 rungs of an `else if` or links of a call chain, which take
/// two levels each, and 12,200 terms of a sum or links of a `?:` ladder.
///
/// What walks trees runs on a stack sized for it
/// (`rustlyn_semantics::parallel::STACK`). An unoptimized build binds and
/// emits a tree this deep on 480 MB of stack at most, measured on a `?:`
/// ladder of 12,281 links (a sum of as many terms takes 395 MB, a chain of
/// 6,141 calls 287 MB, 6,140 rungs of an `else if` 90 MB; the bulk is 29 KB
/// for each level of `bind_expression_core`), in a stack of 1 GB. The
/// editor's formatter and the other walks of the syntax tree itself take a
/// few hundred bytes a level.
pub(crate) const MAX_DEPTH: u32 = 12288;

/// A saved position, so a speculative parse can be undone.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResetPoint {
    index: usize,
    diagnostics: usize,
    splits: usize,
}

pub(crate) struct Parser {
    source: SourceText,
    tokens: Vec<Token>,
    index: usize,
    /// Where the file ends as far as the parse is concerned: the index of
    /// the end-of-file token, or of the token the parse gave up at
    /// ([`Self::give_up`]), from which on every look sees the end of the
    /// file. The tokens themselves stay where they are — a look ahead that
    /// gave up is rewound like any other — and the ones past this point go
    /// into the tree as skipped text ([`Self::cut_off`]).
    end: usize,
    /// How many levels of the parser's recursion are open; see
    /// [`MAX_NESTING`].
    depth: u32,
    /// Whether the parse gave up on source nested too deep (CS8078). Nothing
    /// else is reported from then on: every level on the way out misses its
    /// closing token, and none of that is the mistake.
    too_deep: bool,
    cache: GreenCache,
    /// What has been reported, each shared so that a replay can keep what a
    /// stretch reported without copying it: stretches nest, and each keeping
    /// a copy of everything inside it was quadratic — 876 MB for 2,500
    /// nested parentheses (found by fuzzing).
    diagnostics: Vec<Rc<Diagnostic>>,
    /// Tokens that were split in two, and what they were before.
    ///
    /// Closing `List<List<int>>` takes the lexer's `>>` apart, which rewrites
    /// the stream. A speculative parse may do that and then be thrown away, so
    /// the originals are kept to put back.
    splits: Vec<(usize, Token)>,
    /// How many query expressions enclose the cursor. Inside one, the query
    /// keywords are reserved, so `select` cannot also be a variable name.
    query_depth: usize,
    /// How tightly the pattern being parsed binds, which decides whether an
    /// operator after a type continues an expression: `x is T | y` ends the
    /// pattern at `T`, but the `(_, A | B)` of a switch arm does not.
    pattern_precedence: Precedence,
    /// Whether the parameter list being parsed is an extension block's,
    /// where `extension(C)` names a type and not an untyped parameter.
    pub(crate) extension_receiver: bool,
    /// Whether the `?` at a token starts a conditional, for each `?` asked
    /// about, with what else decides it: whether a query encloses it and how
    /// tightly the pattern around it binds. Asking reads the whole branch
    /// after it, and a branch holding `?[` of its own asked again, once for
    /// the look and once for real — twice per level, `2ⁿ` for n levels
    /// (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide). The tokens do
    /// not move, so an answer stands for the parse.
    conditionals: HashMap<(usize, usize, Precedence), bool>,
    /// Whether the `<` at a token opens a type argument list, for each `<`
    /// asked about, with what else decides it: whether an expression is
    /// being read, and the surroundings a type is read in. Asking reads the
    /// arguments as types, and an argument that is generic itself asked
    /// again, once for the look and once for real — twice per level, `2ⁿ`
    /// for `A<A<A<…>>>` n deep: thirty levels did not finish. As with
    /// [`Self::conditionals`], an answer stands for the parse.
    type_arguments: HashMap<(usize, bool, usize, Precedence, bool), bool>,
    /// For each token, the index of the `)` closing it if it is a `(` the
    /// file closes, `u32::MAX` otherwise; built the first time a question
    /// needs it. See [`Self::closing_paren`].
    closing_parens: Option<Vec<u32>>,
    /// Stretches of the parse already made, by where they started and what
    /// else decided them, as for [`Self::conditionals`]. See
    /// [`Self::replayed`].
    replays: HashMap<ReplayKey, Replay>,
    /// The keys of `replays`, oldest first, and how many tokens their
    /// stretches cover between them. What a replay keeps alive — its tree
    /// and its diagnostics — grows with what it covers, and stretches nest:
    /// kept for the whole parse, 2,500 nested parentheses, each read as an
    /// expression of its own, kept 962 MB of trees (found by fuzzing). A
    /// second reading follows the first closely, so once the cover passes
    /// four times the file, the oldest go.
    replay_order: VecDeque<ReplayKey>,
    replay_cover: usize,
}

/// Where a replayable stretch starts, and the surroundings that decide it:
/// the enclosing queries, the pattern's binding and the extension receiver.
type ReplayKey = (usize, usize, Precedence, bool);

/// What a stretch of the parse did, to do again without reading the tokens
/// again: what it built, where it stopped, what it reported, and the `>>` it
/// took apart — each as it was before and as it was left.
struct Replay {
    green: GreenElement,
    end: usize,
    diagnostics: Vec<Rc<Diagnostic>>,
    splits: Vec<(usize, Token)>,
    split_tokens: Vec<(usize, Token)>,
}

impl Parser {
    fn new(source: SourceText, tokens: Vec<Token>, diagnostics: DiagnosticBag) -> Self {
        debug_assert!(
            tokens.last().is_some_and(Token::is_end_of_file),
            "the token stream must end with end-of-file",
        );
        Self {
            source,
            end: tokens.len() - 1,
            tokens,
            index: 0,
            depth: 0,
            too_deep: false,
            cache: GreenCache::new(),
            diagnostics: diagnostics.into_iter().map(Rc::new).collect(),
            splits: Vec::new(),
            query_depth: 0,
            pattern_precedence: Precedence::Conditional,
            extension_receiver: false,
            conditionals: HashMap::new(),
            type_arguments: HashMap::new(),
            closing_parens: None,
            replays: HashMap::new(),
            replay_order: VecDeque::new(),
            replay_cover: 0,
        }
    }

    // -- looking -----------------------------------------------------------

    fn current(&self) -> &Token {
        &self.tokens[self.slot(0)]
    }

    /// The index of the token `offset` places after the cursor: the end of
    /// the file for everything from [`Self::end`] on.
    fn slot(&self, offset: usize) -> usize {
        let index = self.index + offset;
        if index >= self.end {
            self.tokens.len() - 1
        } else {
            index
        }
    }

    fn kind(&self) -> SyntaxKind {
        self.current().kind
    }

    /// The contextual keyword the current token spells, if it spells one.
    fn contextual_kind(&self) -> SyntaxKind {
        self.current().contextual_kind
    }

    fn nth_kind(&self, offset: usize) -> SyntaxKind {
        self.tokens[self.slot(offset)].kind
    }

    /// The kind of the token `back` places before the cursor, or
    /// end-of-file where there is none.
    fn kind_before(&self, back: usize) -> SyntaxKind {
        match self.index.checked_sub(back) {
            Some(index) => self.tokens[index].kind,
            None => SyntaxKind::EndOfFileToken,
        }
    }

    fn nth_contextual_kind(&self, offset: usize) -> SyntaxKind {
        self.tokens[self.slot(offset)].contextual_kind
    }

    fn at(&self, kind: SyntaxKind) -> bool {
        self.kind() == kind
    }

    /// Whether the current token is an identifier spelling `contextual`.
    fn at_contextual(&self, contextual: SyntaxKind) -> bool {
        self.kind() == SyntaxKind::IdentifierToken && self.contextual_kind() == contextual
    }

    fn at_end(&self) -> bool {
        self.at(SyntaxKind::EndOfFileToken)
    }

    /// The index of the `)` that closes the `(` at `open`, counting nothing
    /// but parentheses — where walking to the matching parenthesis would
    /// stop — or `None` when the file never closes it.
    ///
    /// Several questions about a `(` start with that walk, and asked again at
    /// each of `n` nested ones it made reading them quadratic; a pattern,
    /// which rereads its parentheses as an expression, cubic: six hundred
    /// unclosed `(` after `is` took twenty seconds (found by fuzzing). One
    /// pass answers it for every parenthesis in the file, and the answer
    /// stands for the parse: the only rewrite of the stream is taking `>>`
    /// apart, which never touches a parenthesis.
    fn closing_paren(&mut self, open: usize) -> Option<usize> {
        let tokens = &self.tokens;
        let closing = self.closing_parens.get_or_insert_with(|| {
            let mut closing = vec![u32::MAX; tokens.len()];
            let mut unclosed = Vec::new();
            for (index, token) in tokens.iter().enumerate() {
                match token.kind {
                    SyntaxKind::OpenParenToken => unclosed.push(index),
                    SyntaxKind::CloseParenToken => {
                        if let Some(at) = unclosed.pop() {
                            closing[at] = index as u32;
                        }
                    }
                    _ => {}
                }
            }
            closing
        });
        let close = closing[open];
        (close != u32::MAX).then_some(close as usize)
    }

    /// The kind of the token after the `)` that closes the `(` at the cursor,
    /// or `None` when the file never closes it.
    fn kind_after_closing_paren(&mut self) -> Option<SyntaxKind> {
        let close = self.closing_paren(self.index)?;
        Some(self.tokens[close + 1].kind)
    }

    /// The text of the current token, for diagnostics.
    fn current_text(&self) -> String {
        let token = self.current();
        if token.kind == SyntaxKind::EndOfFileToken {
            "end of file".to_string()
        } else {
            token.text(&self.source).to_string()
        }
    }

    // -- consuming ---------------------------------------------------------

    /// Consumes the current token. At end of file this returns the end-of-file
    /// token without advancing, so a caller that forgets to check cannot run
    /// off the end.
    ///
    /// The end of the file is not handed out: it belongs to the compilation
    /// unit, which takes it once ([`Self::end_of_file`]). Asked for it, this
    /// returns an empty stand-in — the real token carries the trivia in
    /// front of it, a comment on the last line, and handing it to anything
    /// else put that trivia in the tree twice (found by fuzzing,
    /// `examples/fuzz.rs` in rustlyn-ide).
    fn eat_token(&mut self) -> GreenElement {
        let index = self.index;
        if self.at_end() {
            return Self::missing(SyntaxKind::EndOfFileToken);
        }
        let green = green_token(&self.tokens[index], &self.source, &mut self.cache);
        self.index += 1;
        GreenElement::Token(green)
    }

    /// Consumes the current token but records it as `kind`, which turns a
    /// contextual keyword into a keyword. At the end of the file, a missing
    /// `kind`, as with [`Self::eat_token`].
    fn eat_token_as(&mut self, kind: SyntaxKind) -> GreenElement {
        let index = self.index;
        if self.at_end() {
            return Self::missing(kind);
        }
        let green = green_token_as(&self.tokens[index], kind, &self.source, &mut self.cache);
        self.index += 1;
        GreenElement::Token(green)
    }

    /// The end-of-file token with the trivia in front of it: the last thing
    /// in every tree, and taken nowhere else.
    fn end_of_file(&mut self) -> GreenElement {
        debug_assert!(self.at_end(), "the end of the file is taken at the end");
        GreenElement::Token(green_token(
            &self.tokens[self.tokens.len() - 1],
            &self.source,
            &mut self.cache,
        ))
    }

    // -- depth -------------------------------------------------------------

    /// One level of recursion deeper; [`Self::leave`] is its other half.
    /// Past [`MAX_NESTING`] the parse gives up, and what was entered reads
    /// the end of the file and comes back out.
    fn enter(&mut self) {
        self.depth += 1;
        if self.depth > MAX_NESTING {
            self.give_up();
        }
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Asked by everything that grows a tree without recursing, before each
    /// step: whether `built`, where it stands, is still within
    /// [`MAX_DEPTH`]. Where it is not, the parse gives up.
    fn fits(&mut self, built: &GreenElement) {
        self.fits_under(built, 0);
    }

    /// [`Self::fits`] for what is built inside `levels` nodes still to be
    /// made: the conditionals and `if` statements of a ladder that is read
    /// in a loop, whose nodes do not exist until the end of it is reached.
    fn fits_under(&mut self, built: &GreenElement, levels: usize) {
        let levels = u32::try_from(levels).unwrap_or(u32::MAX);
        if self
            .depth
            .saturating_add(levels)
            .saturating_add(u32::from(built.height()))
            >= MAX_DEPTH
        {
            self.give_up();
        }
    }

    /// Stops reading the file here: source nested deeper than can be
    /// compiled (CS8078, which Roslyn reports when it runs out of stack).
    /// From here on every look sees the end of the file, so each level
    /// comes back out the way it does when a file is cut short, and the
    /// rest of the text goes into the tree unread ([`Self::cut_off`]).
    fn give_up(&mut self) {
        self.too_deep = true;
        self.end = self.end.min(self.index);
        // What was remembered read tokens that are past the end now.
        self.conditionals.clear();
        self.type_arguments.clear();
        self.replays.clear();
        self.replay_order.clear();
        self.replay_cover = 0;
    }

    /// The tokens the parse gave up before reading, as skipped text: they
    /// are still part of the file.
    fn cut_off(&mut self) -> Option<GreenElement> {
        let last = self.tokens.len() - 1;
        if self.end >= last {
            return None;
        }
        let skipped = (self.end..last)
            .map(|index| {
                GreenElement::Token(green_token(
                    &self.tokens[index],
                    &self.source,
                    &mut self.cache,
                ))
            })
            .collect();
        Some(GreenElement::Node(GreenNode::new(
            SyntaxKind::SkippedTokensTrivia,
            skipped,
        )))
    }

    fn eat_if(&mut self, kind: SyntaxKind) -> Option<GreenElement> {
        self.at(kind).then(|| self.eat_token())
    }

    /// Consumes an identifier that spells `contextual`, recording it as the
    /// keyword it is.
    fn eat_contextual(&mut self, contextual: SyntaxKind) -> Option<GreenElement> {
        self.at_contextual(contextual)
            .then(|| self.eat_token_as(contextual))
    }

    /// Consumes `kind`, or reports it missing and inserts a zero-width stand-in.
    fn expect(&mut self, kind: SyntaxKind) -> GreenElement {
        if self.at(kind) {
            return self.eat_token();
        }
        let code = expected_error_code(kind);
        let text = kind.describe();
        self.error_before_current(code, &[&text]);
        Self::missing(kind)
    }

    /// Consumes an identifier, accepting contextual keywords as the identifiers
    /// they are.
    fn expect_identifier(&mut self) -> GreenElement {
        if self.at(SyntaxKind::IdentifierToken) {
            return self.eat_token();
        }
        // A reserved keyword in a name position is a better error than a bare
        // "identifier expected": say which keyword is in the way.
        if self.kind().is_reserved_keyword() {
            let text = self.current_text();
            self.error_at_current(ErrorCode::ErrIdentifierExpectedKW, &[&text]);
            return Self::missing(SyntaxKind::IdentifierToken);
        }
        self.error_before_current(ErrorCode::ErrIdentifierExpected, &[]);
        Self::missing(SyntaxKind::IdentifierToken)
    }

    /// At a `.`: whether the name after it is the start of the next
    /// statement rather than the rest of this one, as Roslyn reads `A.` at
    /// the end of a line before `B c` on the next — someone in the middle of
    /// typing `A.`, and a declaration of `c` after it.
    pub(crate) fn dot_ends_the_line(&self) -> bool {
        let at = |offset: usize| self.tokens.get(self.index + offset);
        let breaks = |trivia: &[crate::token::Trivia]| {
            trivia
                .iter()
                .any(|piece| piece.kind == SyntaxKind::EndOfLineTrivia)
        };
        matches!(
            (at(0), at(1), at(2)),
            (Some(dot), Some(name), Some(next))
                if dot.kind == SyntaxKind::DotToken
                    && name.kind == SyntaxKind::IdentifierToken
                    && next.kind == SyntaxKind::IdentifierToken
                    && (breaks(&dot.trailing_trivia) || breaks(&name.leading_trivia))
        )
    }

    /// The name missing after a `.` that ends the line (see
    /// [`Self::dot_ends_the_line`]); the `.` has been eaten.
    pub(crate) fn missing_name_after_dot(&mut self) -> GreenElement {
        self.error_before_current(ErrorCode::ErrIdentifierExpected, &[]);
        node(
            SyntaxKind::IdentifierName,
            vec![Self::missing(SyntaxKind::IdentifierToken)],
        )
    }

    fn missing(kind: SyntaxKind) -> GreenElement {
        GreenElement::Token(Arc::new(GreenToken::missing(kind)))
    }

    /// Consumes tokens that have no place in the grammar here, collecting them
    /// into a node so their text stays in the tree.
    ///
    /// Reports one diagnostic for the whole run rather than one per token.
    fn skip_tokens(
        &mut self,
        code: ErrorCode,
        mut stop: impl FnMut(&Self) -> bool,
    ) -> Option<GreenElement> {
        if self.at_end() || stop(self) {
            return None;
        }
        let text = self.current_text();
        self.error_at_current(code, &[&text]);

        let mut skipped = Vec::new();
        while !self.at_end() && !stop(self) {
            skipped.push(self.eat_token());
        }
        Some(node(SyntaxKind::SkippedTokensTrivia, skipped))
    }

    // -- errors ------------------------------------------------------------

    fn error_at_current(&mut self, code: ErrorCode, args: &[&str]) {
        if self.too_deep {
            return;
        }
        let span = self.current().span;
        self.diagnostics
            .push(Rc::new(Diagnostic::new(code, span, args)));
    }

    /// Reports at the point where something was expected: the end of the
    /// previous token, which is where a user would put the missing text.
    fn error_before_current(&mut self, code: ErrorCode, args: &[&str]) {
        if self.too_deep {
            return;
        }
        let span = if self.index > 0 {
            TextSpan::at(self.tokens[self.index - 1].span.end())
        } else {
            TextSpan::at(self.current().span.start())
        };
        self.diagnostics
            .push(Rc::new(Diagnostic::new(code, span, args)));
    }

    // -- speculation -------------------------------------------------------

    fn mark(&self) -> ResetPoint {
        ResetPoint {
            index: self.index,
            diagnostics: self.diagnostics.len(),
            splits: self.splits.len(),
        }
    }

    /// Rewinds to `point`, discarding anything reported since.
    fn reset(&mut self, point: ResetPoint) {
        while self.splits.len() > point.splits {
            let (index, token) = self.splits.pop().expect("just checked the length");
            self.tokens[index] = token;
        }
        self.index = point.index;
        self.diagnostics.truncate(point.diagnostics);
    }

    /// Runs `attempt` and rewinds afterwards, returning what it decided.
    ///
    /// Used for the questions that cannot be answered by lookahead alone, such
    /// as whether `(A)` is a cast.
    fn speculate<T>(&mut self, attempt: impl FnOnce(&mut Self) -> T) -> T {
        let point = self.mark();
        let result = attempt(self);
        self.reset(point);
        result
    }

    /// Runs `parse` from the cursor, or does again what it did the last time
    /// it ran from here in the same surroundings.
    ///
    /// For what both readings of an enclosing ambiguity read: parentheses in
    /// a pattern are read as a pattern and, when they hold none, again as an
    /// expression, and an `is` inside them starts another pattern each time
    /// — two readings per level, `2ⁿ` for `(r is (r is (… MeshRenderer)`
    /// (found by fuzzing). What `parse` does depends on the tokens from here
    /// on, which are as the lexer made them until the parse gets there (a
    /// `>>` is only taken apart where the cursor is, and backing up puts it
    /// together again), and on the surroundings in the key: the enclosing
    /// queries, the pattern's binding and the extension receiver. So the
    /// second reading can have the first one's result: the same tree, the
    /// same stop, the same diagnostics and the same tokens taken apart.
    fn replayed(&mut self, parse: impl FnOnce(&mut Self) -> GreenElement) -> GreenElement {
        let key = (
            self.index,
            self.query_depth,
            self.pattern_precedence,
            self.extension_receiver,
        );
        if let Some(replay) = self.replays.get(&key) {
            self.index = replay.end;
            self.diagnostics.extend(replay.diagnostics.iter().cloned());
            self.splits.extend(replay.splits.iter().cloned());
            for (index, token) in &replay.split_tokens {
                self.tokens[*index] = token.clone();
            }
            return replay.green.clone();
        }
        let start = self.mark();
        let green = parse(self);
        let splits = self.splits[start.splits..].to_vec();
        let split_tokens = splits
            .iter()
            .map(|(index, _)| (*index, self.tokens[*index].clone()))
            .collect();
        let replay = Replay {
            green: green.clone(),
            end: self.index,
            diagnostics: self.diagnostics[start.diagnostics..].to_vec(),
            splits,
            split_tokens,
        };
        self.replays.insert(key, replay);
        self.replay_order.push_back(key);
        self.replay_cover += self.index - start.index;
        let budget = 4 * self.tokens.len() + 1024;
        while self.replay_cover > budget {
            let Some(oldest) = self.replay_order.pop_front() else {
                break;
            };
            if let Some(old) = self.replays.remove(&oldest) {
                self.replay_cover -= old.end - oldest.0;
            }
        }
        green
    }
}

/// Wraps children into a green node.
///
/// A small node made of children that are themselves shared — `x` as a name,
/// `int` as a type, `a.b` — is shared too, as Roslyn's `SyntaxNodeCache`
/// does: a green node knows no position, so the one `IdentifierName` over the
/// shared `x` token serves every place `x` is written with the same trivia.
fn node(kind: SyntaxKind, children: Vec<GreenElement>) -> GreenElement {
    if children.is_empty() || children.len() > 3 {
        return GreenElement::Node(GreenNode::new(kind, children));
    }
    GreenElement::Node(NODES.with(|nodes| nodes.borrow_mut().node(kind, children)))
}

thread_local! {
    static GREEN: std::cell::RefCell<Option<GreenCache>> = const { std::cell::RefCell::new(None) };
    static NODES: std::cell::RefCell<crate::green::NodeCache> =
        std::cell::RefCell::new(crate::green::NodeCache::default());
}

/// The diagnostic that fits a missing token best.
const fn expected_error_code(kind: SyntaxKind) -> ErrorCode {
    match kind {
        SyntaxKind::SemicolonToken => ErrorCode::ErrSemicolonExpected,
        SyntaxKind::IdentifierToken => ErrorCode::ErrIdentifierExpected,
        SyntaxKind::CloseBraceToken => ErrorCode::ErrRbraceExpected,
        SyntaxKind::OpenBraceToken => ErrorCode::ErrLbraceExpected,
        SyntaxKind::CloseParenToken => ErrorCode::ErrCloseParenExpected,
        _ => ErrorCode::ErrSyntaxError,
    }
}
