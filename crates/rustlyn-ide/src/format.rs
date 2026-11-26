//! Formatting: the whitespace between tokens, decided the way Roslyn's C#
//! formatter decides it with no `.editorconfig` in sight.
//!
//! The formatter never touches a token. It looks at each gap between two
//! tokens — the trailing trivia of one and the leading trivia of the next —
//! and decides what whitespace belongs there: a number of spaces when the two
//! stay on one line, or a line break and an indentation when the second
//! starts a line. Comments, directives and disabled `#if` text inside a gap
//! are kept exactly as written; only the whitespace around them moves. That
//! is also why a string, a verbatim or raw string, or the inside of a comment
//! can never change: they are tokens or trivia, never gaps.
//!
//! What Roslyn's defaults amount to, and so what this does:
//!
//! * **Lines are the user's.** A line break that is there stays, blank lines
//!   included; one that is not there is added only where a brace demands it.
//!   Roslyn's "preserve single-line blocks and statements" options are on by
//!   default, so `int P { get; set; }` and `if (x) return;` stay on one line.
//! * **Allman braces.** When a construct spans lines, its `{` goes on a line
//!   of its own: namespaces, types, members, accessors, lambdas, anonymous
//!   methods, control blocks, initializers. `else`, `catch` and `finally`
//!   start their own line after a `}`.
//! * **Indentation is structural.** A member, a statement, an accessor, an
//!   enum member, an initializer's element sits one level inside its braces;
//!   case labels one level inside the switch and their statements one more;
//!   an embedded statement without braces one level inside its `if`; a label
//!   one level out. Stacked `using (...)` statements share one level.
//! * **Wrapped lines keep their shape.** A line that continues an expression
//!   or an argument list moves by as much as the line it continues moved, the
//!   way Roslyn keeps relative indentation for anything it has no rule for.
//! * **Spacing** follows Roslyn's default table: a space after control-flow
//!   keywords, around binary and assignment operators, `=>`, and the `?` and
//!   `:` of a conditional, after `,` and after `;` in a `for`; none inside
//!   parentheses and brackets, before `(` in calls and declarations, around
//!   `.`, `?.`, `->` and `::`, after a cast, or after a unary operator.
//!
//! Deviations, stated so nobody has to discover them: the text inside an
//! interpolated string, holes included, is left exactly as it is (Roslyn
//! formats the expressions in the holes); a multi-line block whose first
//! statement shares the line of its `{` gets that statement moved to a line
//! of its own, and likewise a `}` that shares the line of the last statement
//! (Roslyn leaves such user-written lines alone); and a multi-line switch
//! expression gets its `{` on a line of its own, which Roslyn has no option
//! for but is how its own code base is laid out.

use rustlyn_syntax::{SyntaxElement, SyntaxKind as K, SyntaxNode, SyntaxToken, SyntaxTrivia};
use rustlyn_text::{LineIndex, TextSpan};

use crate::document::{Indent, LineEnding};
use crate::edit::TextEdit;

/// How to lay out whitespace. The defaults are Roslyn's: four spaces, no
/// tabs; the line break is `\n` where Roslyn would use the platform's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormatOptions {
    /// Columns per indentation level.
    pub indent_size: u32,
    /// Columns a tab advances to, for measuring and for indenting with tabs.
    pub tab_size: u32,
    /// Indent with tabs (topped up with spaces), rather than spaces alone.
    pub use_tabs: bool,
    /// What a line break the formatter adds is spelled as. Existing breaks
    /// are never rewritten.
    pub newline: String,
    /// `.editorconfig`'s `insert_final_newline`: whether formatting the
    /// whole file makes it end in a line break (`Some(true)`), makes it not
    /// (`Some(false)`), or leaves the end alone.
    pub insert_final_newline: Option<bool>,
    /// Roslyn's C# formatting options, its defaults unless an
    /// `.editorconfig` says otherwise.
    pub style: FormatStyle,
}

impl Default for FormatOptions {
    fn default() -> Self {
        Self {
            indent_size: 4,
            tab_size: 4,
            use_tabs: false,
            newline: "\n".to_owned(),
            insert_final_newline: None,
            style: FormatStyle::default(),
        }
    }
}

/// Which constructs put their `{` on a line of its own, as Roslyn's
/// `csharp_new_line_before_open_brace` lists them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)]
pub struct BraceNewLines {
    /// Types, and namespaces with them.
    pub types: bool,
    /// Methods, constructors, operators, local functions.
    pub methods: bool,
    /// The `{ get; set; }` of properties, indexers and events.
    pub properties: bool,
    /// The body of a `get`, `set`, `add` or `remove`.
    pub accessors: bool,
    pub anonymous_methods: bool,
    pub lambdas: bool,
    pub control_blocks: bool,
    pub anonymous_types: bool,
    pub object_collection_array_initializers: bool,
}

impl BraceNewLines {
    /// Every kind of brace on its own line or none: `all` is Roslyn's
    /// default.
    #[must_use]
    pub const fn all(on: bool) -> Self {
        Self {
            types: on,
            methods: on,
            properties: on,
            accessors: on,
            anonymous_methods: on,
            lambdas: on,
            control_blocks: on,
            anonymous_types: on,
            object_collection_array_initializers: on,
        }
    }

    /// `all`, `none`, or a comma-separated list of the kinds.
    #[must_use]
    pub fn parse(value: &str) -> Self {
        let mut found = Self::all(false);
        for part in value.split(',') {
            match part.trim().to_ascii_lowercase().as_str() {
                "all" => found = Self::all(true),
                "types" => found.types = true,
                "methods" | "local_functions" => found.methods = true,
                "properties" => found.properties = true,
                "accessors" => found.accessors = true,
                "anonymous_methods" => found.anonymous_methods = true,
                "lambdas" => found.lambdas = true,
                "control_blocks" => found.control_blocks = true,
                "anonymous_types" => found.anonymous_types = true,
                "object_collection_array_initializers" | "object_collection" => {
                    found.object_collection_array_initializers = true;
                }
                _ => {}
            }
        }
        found
    }

    /// Whether the `{` of `container` goes on its own line.
    #[must_use]
    pub fn wants(&self, container: &SyntaxNode) -> bool {
        let parent = container.parent().map(SyntaxNode::kind);
        match container.kind() {
            kind if is_type_declaration(kind) => self.types,
            K::NamespaceDeclaration | K::ExtensionBlockDeclaration => self.types,
            K::AccessorList => self.properties,
            K::AnonymousObjectCreationExpression => self.anonymous_types,
            kind if is_initializer(kind) => self.object_collection_array_initializers,
            K::SwitchStatement | K::SwitchExpression => self.control_blocks,
            K::Block => match parent {
                Some(
                    K::MethodDeclaration
                    | K::ConstructorDeclaration
                    | K::DestructorDeclaration
                    | K::OperatorDeclaration
                    | K::ConversionOperatorDeclaration
                    | K::LocalFunctionStatement,
                ) => self.methods,
                Some(
                    K::GetAccessorDeclaration
                    | K::SetAccessorDeclaration
                    | K::InitAccessorDeclaration
                    | K::AddAccessorDeclaration
                    | K::RemoveAccessorDeclaration
                    | K::UnknownAccessorDeclaration,
                ) => self.accessors,
                Some(K::AnonymousMethodExpression) => self.anonymous_methods,
                Some(K::SimpleLambdaExpression | K::ParenthesizedLambdaExpression) => self.lambdas,
                _ => self.control_blocks,
            },
            _ => true,
        }
    }
}

/// `csharp_space_around_binary_operators`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpaceAroundOperators {
    BeforeAndAfter,
    None,
    /// Whatever is there stays.
    Ignore,
}

/// Roslyn's C# formatting options that the formatter honours. The defaults
/// are Roslyn's own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)]
pub struct FormatStyle {
    pub new_line_before_open_brace: BraceNewLines,
    pub new_line_before_else: bool,
    pub new_line_before_catch: bool,
    pub new_line_before_finally: bool,
    /// The statements of a `case` a level inside its label.
    pub indent_case_contents: bool,
    /// The `case` labels a level inside the `switch`.
    pub indent_switch_labels: bool,
    pub space_after_cast: bool,
    /// `if (x)` rather than `if(x)`.
    pub space_after_control_flow_keywords: bool,
    /// `M( a, b )`.
    pub space_within_call_parentheses: bool,
    /// `void M( int a )`.
    pub space_within_declaration_parentheses: bool,
    /// `M (a)`.
    pub space_before_call_parenthesis: bool,
    /// `void M (int a)`.
    pub space_before_declaration_parenthesis: bool,
    pub space_after_comma: bool,
    pub space_before_inheritance_colon: bool,
    pub space_after_inheritance_colon: bool,
    pub space_around_binary_operators: SpaceAroundOperators,
    /// `int a; int b;` may stay on one line.
    pub preserve_single_line_statements: bool,
    /// `{ get; set; }` and `{ return; }` may stay on one line.
    pub preserve_single_line_blocks: bool,
}

impl Default for FormatStyle {
    fn default() -> Self {
        Self {
            new_line_before_open_brace: BraceNewLines::all(true),
            new_line_before_else: true,
            new_line_before_catch: true,
            new_line_before_finally: true,
            indent_case_contents: true,
            indent_switch_labels: true,
            space_after_cast: false,
            space_after_control_flow_keywords: true,
            space_within_call_parentheses: false,
            space_within_declaration_parentheses: false,
            space_before_call_parenthesis: false,
            space_before_declaration_parenthesis: false,
            space_after_comma: true,
            space_before_inheritance_colon: true,
            space_after_inheritance_colon: true,
            space_around_binary_operators: SpaceAroundOperators::BeforeAndAfter,
            preserve_single_line_statements: true,
            preserve_single_line_blocks: true,
        }
    }
}

impl FormatStyle {
    /// The spaces between two tokens on one line once these options have
    /// had their say about `spaces`, Roslyn's default. `existing` is how
    /// many there are now, for an option that says to leave them.
    fn adjust(
        &self,
        previous: &SyntaxToken,
        token: &SyntaxToken,
        spaces: u32,
        existing: u32,
    ) -> u32 {
        let (before, after) = (previous.kind(), token.kind());
        let (before_parent, after_parent) = (previous.parent().kind(), token.parent().kind());
        if before == K::CloseParenToken && before_parent == K::CastExpression {
            return u32::from(self.space_after_cast);
        }
        if after == K::OpenParenToken && is_control_flow_keyword(before) {
            return u32::from(self.space_after_control_flow_keywords);
        }
        let call_list = |kind: K, node: &SyntaxNode| {
            kind == K::ArgumentList
                && node
                    .parent()
                    .is_some_and(|call| call.kind() == K::InvocationExpression)
        };
        let declaration_list = |kind: K, node: &SyntaxNode| {
            kind == K::ParameterList
                && node.parent().is_some_and(|owner| {
                    !matches!(
                        owner.kind(),
                        K::ParenthesizedLambdaExpression | K::AnonymousMethodExpression
                    )
                })
        };
        if after == K::OpenParenToken {
            if call_list(after_parent, token.parent()) {
                return u32::from(self.space_before_call_parenthesis);
            }
            if declaration_list(after_parent, token.parent()) {
                return u32::from(self.space_before_declaration_parenthesis);
            }
        }
        // Inside the parentheses, when they hold something.
        if before == K::OpenParenToken && after != K::CloseParenToken {
            if call_list(before_parent, previous.parent()) {
                return u32::from(self.space_within_call_parentheses);
            }
            if declaration_list(before_parent, previous.parent()) {
                return u32::from(self.space_within_declaration_parentheses);
            }
        }
        if after == K::CloseParenToken && before != K::OpenParenToken {
            if call_list(after_parent, token.parent()) {
                return u32::from(self.space_within_call_parentheses);
            }
            if declaration_list(after_parent, token.parent()) {
                return u32::from(self.space_within_declaration_parentheses);
            }
        }
        if before == K::CommaToken && spaces == 1 {
            return u32::from(self.space_after_comma);
        }
        if after == K::ColonToken && after_parent == K::BaseList {
            return u32::from(self.space_before_inheritance_colon);
        }
        if before == K::ColonToken && before_parent == K::BaseList {
            return u32::from(self.space_after_inheritance_colon);
        }
        if is_binary_operator(token) || is_binary_operator(previous) {
            return match self.space_around_binary_operators {
                SpaceAroundOperators::BeforeAndAfter => spaces,
                SpaceAroundOperators::None => 0,
                SpaceAroundOperators::Ignore => existing,
            };
        }
        spaces
    }
}

fn is_control_flow_keyword(kind: K) -> bool {
    matches!(
        kind,
        K::IfKeyword
            | K::WhileKeyword
            | K::ForKeyword
            | K::ForEachKeyword
            | K::SwitchKeyword
            | K::CatchKeyword
            | K::UsingKeyword
            | K::LockKeyword
            | K::FixedKeyword
    )
}

/// Whether `token` is the operator of a binary expression: the `+` of
/// `a + b`, not the `is` of `a is B`.
fn is_binary_operator(token: &SyntaxToken) -> bool {
    token.kind().is_punctuation()
        && matches!(
            token.parent().kind(),
            K::AddExpression
                | K::SubtractExpression
                | K::MultiplyExpression
                | K::DivideExpression
                | K::ModuloExpression
                | K::LeftShiftExpression
                | K::RightShiftExpression
                | K::UnsignedRightShiftExpression
                | K::LogicalOrExpression
                | K::LogicalAndExpression
                | K::BitwiseOrExpression
                | K::BitwiseAndExpression
                | K::ExclusiveOrExpression
                | K::EqualsExpression
                | K::NotEqualsExpression
                | K::LessThanExpression
                | K::LessThanOrEqualExpression
                | K::GreaterThanExpression
                | K::GreaterThanOrEqualExpression
                | K::CoalesceExpression
        )
}

impl FormatOptions {
    /// Options that match what a file already does: its indentation and its
    /// line breaks, as [`Document`](crate::Document) detected them.
    #[must_use]
    pub fn from_document(indent: Indent, line_ending: LineEnding) -> Self {
        let width = indent.width.max(1);
        Self {
            indent_size: width,
            tab_size: width,
            use_tabs: indent.tabs,
            newline: line_ending.text().to_owned(),
            ..Self::default()
        }
    }
}

/// The edits that format the whole file.
#[must_use]
pub fn format_document(root: &SyntaxNode, text: &str, options: &FormatOptions) -> Vec<TextEdit> {
    let mut edits = Engine::new(root, text, options, None).run();
    edits.extend(final_newline(text, options, &edits));
    edits
}

/// The edit `insert_final_newline` asks for at the end of the file, when
/// the end is not already as it says and the formatter has not touched it.
fn final_newline(text: &str, options: &FormatOptions, edits: &[TextEdit]) -> Option<TextEdit> {
    let wanted = options.insert_final_newline?;
    let end = text.len() as u32;
    let trimmed = text.trim_end_matches(['\n', '\r']).len() as u32;
    if text.is_empty() || edits.iter().any(|edit| edit.span.end() >= trimmed) {
        return None;
    }
    let ends_with_break = trimmed < end;
    if wanted && !ends_with_break {
        return Some(TextEdit::new(TextSpan::at(end), options.newline.clone()));
    }
    if !wanted && ends_with_break {
        return Some(TextEdit::delete(TextSpan::from_bounds(trimmed, end)));
    }
    None
}

/// The edits that format `span`: only whitespace on the lines the span
/// touches changes, and everything outside is taken as it is.
#[must_use]
pub fn format_range(
    root: &SyntaxNode,
    text: &str,
    span: TextSpan,
    options: &FormatOptions,
) -> Vec<TextEdit> {
    let lines = LineIndex::new(text);
    let from = lines
        .line_start(lines.line_of(span.start()))
        .unwrap_or_default();
    let to = line_end(text, &lines, span.end());
    Engine::new(root, text, options, Some((from, to))).run()
}

/// What typing `typed` should reformat, Roslyn's on-type triggers: `;`
/// formats the statement or member it ends, `{` the construct it opens, `}`
/// the construct it closes,
/// a line break re-indents the new line and the one before it, and `#` puts
/// a directive where directives go. `position` is the caret after the typed
/// character, and `text` already holds it. Any other character formats
/// nothing.
#[must_use]
pub fn format_on_type(
    root: &SyntaxNode,
    text: &str,
    position: u32,
    typed: char,
    options: &FormatOptions,
) -> Vec<TextEdit> {
    let typed_at = position.saturating_sub(typed.len_utf8() as u32);
    match typed {
        ';' => {
            let Some(token) = token_at(root, typed_at, K::SemicolonToken) else {
                return Vec::new();
            };
            let owner = token.parent().clone();
            if owner.kind() == K::ForStatement {
                return Vec::new();
            }
            format_range(root, text, owner.span(), options)
        }
        '}' => {
            let Some(token) = token_at(root, typed_at, K::CloseBraceToken) else {
                return Vec::new();
            };
            let container = token.parent().clone();
            if !is_container(container.kind()) {
                return Vec::new();
            }
            let start = construct_start(&container);
            format_range(
                root,
                text,
                TextSpan::from_bounds(start.min(token.span().end()), token.span().end()),
                options,
            )
        }
        // A `{` that opens a block formats the construct up to it: its line
        // gets its indentation, and the brace its place before or after
        // the line break as the options say.
        '{' => {
            let Some(token) = token_at(root, typed_at, K::OpenBraceToken) else {
                return Vec::new();
            };
            let container = token.parent().clone();
            if !is_container(container.kind()) {
                return Vec::new();
            }
            let start = construct_start(&container).min(token.span().start());
            format_range(
                root,
                text,
                TextSpan::from_bounds(start, token.span().end()),
                options,
            )
        }
        '\n' => {
            let lines = LineIndex::new(text);
            let line = lines.line_of(position.min(text.len() as u32));
            let previous = lines.line_start(line.saturating_sub(1)).unwrap_or_default();
            let current = lines.line_start(line).unwrap_or_default();
            let end = line_end(text, &lines, current);
            let blank = text[current as usize..end as usize].trim().is_empty();
            let mut edits = format_range(
                root,
                text,
                TextSpan::from_bounds(previous, end.max(previous)),
                options,
            );
            // An empty new line keeps what the editor put on it: smart
            // indentation owns the caret, and trimming it would undo that.
            if blank {
                edits.retain(|edit| edit.span.end() < current || edit.span.start() > end);
            }
            edits
        }
        '#' => {
            let lines = LineIndex::new(text);
            let line = lines.line_of(typed_at);
            let start = lines.line_start(line).unwrap_or_default();
            let end = line_end(text, &lines, start);
            format_range(root, text, TextSpan::from_bounds(start, end), options)
        }
        _ => Vec::new(),
    }
}

/// The token of `kind` that ends at or covers `offset`.
fn token_at(root: &SyntaxNode, offset: u32, kind: K) -> Option<SyntaxToken> {
    root.find_token(offset)
        .filter(|token| token.kind() == kind && token.span().contains(offset))
}

/// Where the line holding `offset` ends, before its line break.
fn line_end(text: &str, lines: &LineIndex, offset: u32) -> u32 {
    let line = lines.line_of(offset.min(text.len() as u32));
    let start = lines.line_start(line).unwrap_or_default() as usize;
    let rest = &text[start..];
    let length = rest.find(['\n', '\r']).unwrap_or(rest.len());
    (start + length) as u32
}

// MARK: - the engine

/// A token that is really there, and the trivia between it and the one
/// before it.
struct Placed {
    token: SyntaxToken,
    gap_start: u32,
    gap: Vec<SyntaxTrivia>,
}

struct Engine<'a> {
    text: &'a str,
    lines: LineIndex,
    options: &'a FormatOptions,
    tokens: Vec<Placed>,
    /// For each token, the index of the first token on its line once
    /// formatted.
    line_first: Vec<usize>,
    /// For each token, the column it starts at once formatted.
    new_col: Vec<u32>,
    /// The token whose gap is being decided; nothing at or after it has a
    /// formatted column yet.
    current: usize,
    /// When formatting a range: the bytes an edit must touch to be kept.
    range: Option<(u32, u32)>,
    edits: Vec<TextEdit>,
    /// Where each container's braces go, once that is final: see
    /// [`Self::brace_base`].
    brace_bases: std::cell::RefCell<std::collections::HashMap<(TextSpan, K), u32>>,
    /// The interpolated strings, by where they start, each with the one it
    /// is inside of: see [`Self::string_around`].
    strings: Vec<(TextSpan, Option<usize>)>,
}

impl<'a> Engine<'a> {
    fn new(
        root: &SyntaxNode,
        text: &'a str,
        options: &'a FormatOptions,
        range: Option<(u32, u32)>,
    ) -> Self {
        let mut tokens = Vec::new();
        let mut pending: Vec<SyntaxTrivia> = Vec::new();
        let mut gap_start = 0;
        for token in root.descendant_tokens() {
            pending.extend(token.leading_trivia());
            // A token the parser invented to repair an error has no text,
            // and no place of its own to format: its trivia joins the gap
            // around it.
            if token.span().is_empty() && token.kind() != K::EndOfFileToken {
                pending.extend(token.trailing_trivia());
                continue;
            }
            let end = token.span().end();
            let trailing = token.trailing_trivia();
            tokens.push(Placed {
                token,
                gap_start,
                gap: std::mem::take(&mut pending),
            });
            pending.extend(trailing);
            gap_start = end;
        }
        let count = tokens.len();
        // Strings nest only inside the holes of others, so a stack of the
        // ones still open, in the order they start, says which is around
        // which.
        let mut strings: Vec<(TextSpan, Option<usize>)> = Vec::new();
        let mut open: Vec<usize> = Vec::new();
        for node in root
            .descendants()
            .filter(|node| node.kind() == K::InterpolatedStringExpression)
        {
            let span = node.span();
            while open
                .last()
                .is_some_and(|&around| !strings[around].0.contains_span(span))
            {
                open.pop();
            }
            strings.push((span, open.last().copied()));
            open.push(strings.len() - 1);
        }
        Self {
            text,
            lines: LineIndex::new(text),
            options,
            tokens,
            line_first: vec![0; count],
            new_col: vec![0; count],
            current: 0,
            range,
            edits: Vec::new(),
            brace_bases: std::cell::RefCell::default(),
            strings,
        }
    }

    fn run(mut self) -> Vec<TextEdit> {
        for index in 0..self.tokens.len() {
            self.current = index;
            self.format_gap(index);
        }
        self.edits
    }

    // MARK: columns

    /// The column `offset` is at in the original text.
    fn old_col(&self, offset: u32) -> u32 {
        let line = self.lines.line_of(offset);
        let start = self.lines.line_start(line).unwrap_or_default();
        self.width(0, &self.text[start as usize..offset as usize])
    }

    /// The column after `text`, starting at `column`.
    fn width(&self, column: u32, text: &str) -> u32 {
        let tab = self.options.tab_size.max(1);
        text.chars().fold(column, |column, ch| {
            if ch == '\t' {
                column + tab - column % tab
            } else {
                column + 1
            }
        })
    }

    /// The column a token ends at once formatted.
    fn end_col(&self, index: usize) -> u32 {
        let token = &self.tokens[index].token;
        let text = token.text();
        if text.contains(['\n', '\r']) {
            // Inside a multi-line token nothing moves, so its last line ends
            // where it always did.
            self.old_col(token.span().end())
        } else {
            self.width(self.new_col[index], text)
        }
    }

    fn indent_text(&self, columns: u32) -> String {
        if self.options.use_tabs {
            let tab = self.options.tab_size.max(1);
            let mut text = "\t".repeat((columns / tab) as usize);
            text.push_str(&" ".repeat((columns % tab) as usize));
            text
        } else {
            " ".repeat(columns as usize)
        }
    }

    fn unit(&self) -> u32 {
        self.options.indent_size
    }

    /// Replaces `span` with `text`, unless that changes nothing or falls
    /// outside the range being formatted. Whether the text is now `text`.
    fn replace(&mut self, span: TextSpan, text: &str) -> bool {
        if &self.text[span.start() as usize..span.end() as usize] == text {
            return true;
        }
        if let Some((from, to)) = self.range
            && (span.end() < from || span.start() > to)
        {
            return false;
        }
        self.edits.push(TextEdit::new(span, text));
        true
    }

    // MARK: gaps

    fn format_gap(&mut self, index: usize) {
        let token = self.tokens[index].token.clone();
        let gap_start = self.tokens[index].gap_start;
        let gap_end = token.span().start();
        let gap_text = &self.text[gap_start as usize..gap_end as usize];
        let broken = index == 0 || gap_text.contains(['\n', '\r']);

        // Inside an interpolated string the gaps are part of what the string
        // says, or close enough to it that they are left alone.
        if index > 0 && self.same_interpolation(&self.tokens[index - 1].token, &token) {
            self.keep_gap(index, broken);
            return;
        }
        if broken && index > 0 && self.joins_previous_line(index) {
            let span = TextSpan::from_bounds(gap_start, gap_end);
            if self.replace(span, " ") {
                self.line_first[index] = self.line_first[index - 1];
                self.new_col[index] = self.end_col(index - 1) + 1;
                return;
            }
        }
        if broken {
            self.format_broken_gap(index);
            return;
        }

        let previous = self.tokens[index - 1].token.clone();
        let plain = self.tokens[index]
            .gap
            .iter()
            .all(|trivia| trivia.kind() == K::WhitespaceTrivia);
        if !plain {
            // A comment between two tokens on one line stays where it is.
            self.keep_gap(index, false);
            return;
        }
        let span = TextSpan::from_bounds(gap_start, gap_end);
        if self.forced_newline(&previous, &token) {
            let indent = self.indent_of(index);
            let text = format!("{}{}", self.options.newline, self.indent_text(indent));
            if self.replace(span, &text) {
                self.line_first[index] = index;
                self.new_col[index] = indent;
                return;
            }
            self.keep_gap(index, false);
            return;
        }
        let mut spaces = spacing(&previous, &token);
        let existing = gap_end - gap_start;
        spaces = self
            .options
            .style
            .adjust(&previous, &token, spaces, existing);
        if spaces == 0 && would_merge(previous.text(), token.text()) {
            spaces = 1;
        }
        let text = " ".repeat(spaces as usize);
        if self.replace(span, &text) {
            self.line_first[index] = self.line_first[index - 1];
            self.new_col[index] = self.end_col(index - 1) + spaces;
        } else {
            self.keep_gap(index, false);
        }
    }

    /// Records where a token lands when its gap is left as it was.
    fn keep_gap(&mut self, index: usize, broken: bool) {
        if broken || index == 0 {
            self.line_first[index] = index;
            self.new_col[index] = self.old_col(self.tokens[index].token.span().start());
        } else {
            let gap_start = self.tokens[index].gap_start;
            let gap_end = self.tokens[index].token.span().start();
            self.line_first[index] = self.line_first[index - 1];
            self.new_col[index] = self.width(
                self.end_col(index - 1),
                &self.text[gap_start as usize..gap_end as usize],
            );
        }
    }

    /// A gap with a line break in it: trailing whitespace goes, comments and
    /// `#region` lines take the indentation of what follows them, other
    /// directives go to the first column, and the token gets its own
    /// indentation.
    fn format_broken_gap(&mut self, index: usize) {
        let token_start = self.tokens[index].token.span().start();
        let pieces = self.tokens[index].gap.clone();
        let target = self.indent_of(index);
        let comment_target = self.comment_indent(index, target);
        let mut at_line_start = index == 0;
        let mut whitespace: Option<TextSpan> = None;
        for piece in pieces {
            let kind = piece.kind();
            if kind == K::WhitespaceTrivia {
                whitespace = Some(match whitespace {
                    Some(before) => before.union(piece.span()),
                    None => piece.span(),
                });
                continue;
            }
            let slot = whitespace
                .take()
                .unwrap_or_else(|| TextSpan::at(piece.span().start()));
            let wanted: Option<String> = match kind {
                K::EndOfLineTrivia => Some(String::new()),
                K::SingleLineCommentTrivia
                | K::MultiLineCommentTrivia
                | K::SingleLineDocumentationCommentTrivia
                | K::MultiLineDocumentationCommentTrivia
                | K::RegionDirectiveTrivia
                | K::EndRegionDirectiveTrivia
                    if at_line_start =>
                {
                    Some(self.indent_text(comment_target))
                }
                kind if is_directive(kind) && at_line_start => Some(String::new()),
                _ => None,
            };
            if let Some(wanted) = wanted {
                self.replace(slot, &wanted);
            }
            at_line_start = match kind {
                K::EndOfLineTrivia => true,
                K::DisabledTextTrivia => piece.text().ends_with(['\n', '\r']),
                _ => false,
            };
        }
        let slot = whitespace.unwrap_or_else(|| TextSpan::at(token_start));
        self.line_first[index] = index;
        if at_line_start {
            let indent = if self.tokens[index].token.kind() == K::EndOfFileToken {
                0
            } else {
                target
            };
            let text = self.indent_text(indent);
            self.new_col[index] = if self.replace(slot, &text) {
                indent
            } else {
                self.old_col(token_start)
            };
        } else {
            self.new_col[index] = self.old_col(token_start);
        }
    }

    /// The indentation for a comment or `#region` line in front of token
    /// `index`: the token's own, except before a closing brace, where it is
    /// the indentation of what the braces hold.
    fn comment_indent(&self, index: usize, target: u32) -> u32 {
        let token = &self.tokens[index].token;
        match token.kind() {
            K::EndOfFileToken => 0,
            K::CloseBraceToken if is_container(token.parent().kind()) => {
                self.brace_base(token.parent()) + self.unit()
            }
            _ => target,
        }
    }

    // MARK: indentation

    /// The first formatted token at or after `offset`.
    fn index_at(&self, offset: u32) -> usize {
        self.tokens
            .partition_point(|placed| placed.token.span().start() < offset)
    }

    /// The formatted indentation of the line holding the token at `offset`.
    /// A line not reached yet has its original indentation.
    fn line_indent_at(&self, offset: u32) -> u32 {
        let index = self.index_at(offset);
        if index < self.current {
            self.new_col[self.line_first[index]]
        } else {
            original_indent(self.text, &self.lines, offset, self.options.tab_size)
        }
    }

    /// The formatted indentation of the line a declaration or statement
    /// starts on, its attributes aside.
    fn node_line_indent(&self, node: &SyntaxNode) -> u32 {
        self.line_indent_at(start_after_attributes(node))
    }

    /// Whether two tokens are both inside one interpolated string.
    fn same_interpolation(&self, previous: &SyntaxToken, token: &SyntaxToken) -> bool {
        match (self.string_around(previous), self.string_around(token)) {
            (Some(one), Some(other)) => one.contains_span(other) || other.contains_span(one),
            _ => false,
        }
    }

    /// The innermost interpolated string a token is in.
    ///
    /// Found among the strings rather than among the token's ancestors:
    /// walked for every token, two thousand nested blocks made that the
    /// square of the depth (found by fuzzing). The last string to start
    /// before the token is around it or inside one that is — strings nest
    /// and do not overlap — so the ones around that are all there is to ask.
    fn string_around(&self, token: &SyntaxToken) -> Option<TextSpan> {
        let span = token.span();
        let after = self
            .strings
            .partition_point(|(string, _)| string.start() <= span.start());
        let mut at = after.checked_sub(1)?;
        loop {
            let (string, around) = self.strings[at];
            if string.contains_span(span) {
                return Some(string);
            }
            at = around?;
        }
    }

    /// Where the `{` and `}` of a container go.
    ///
    /// Worked out from the containers around it, each from the ones around
    /// it: asked for every line, that was every container out to the file
    /// for each, and two thousand nested blocks never finished formatting
    /// (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide). What it reads
    /// is on the line of the `{` or before, and a line once formatted stays
    /// so: from then on the answer is kept.
    fn brace_base(&self, container: &SyntaxNode) -> u32 {
        let key = (container.span(), container.kind());
        if let Some(&known) = self.brace_bases.borrow().get(&key) {
            return known;
        }
        let base = self.brace_base_uncached(container);
        let settled = container
            .child_token_of_kind(K::OpenBraceToken)
            .is_some_and(|open| self.index_at(open.span().start()) < self.current);
        if settled {
            self.brace_bases.borrow_mut().insert(key, base);
        }
        base
    }

    fn brace_base_uncached(&self, container: &SyntaxNode) -> u32 {
        if let Some(outer) = item_container(container) {
            return self.item_indent(container, &outer);
        }
        let Some(parent) = container.parent() else {
            return 0;
        };
        match container.kind() {
            K::Block => {
                if parent.kind() == K::GlobalStatement {
                    return 0;
                }
                self.node_line_indent(parent)
            }
            K::AccessorList => self.node_line_indent(parent),
            kind if is_initializer(kind) => self.line_indent_at(parent.span().start()),
            _ => self.node_line_indent(container),
        }
    }

    /// Where an item of a container starts: a member, a statement, an
    /// accessor, a case label, an element.
    fn item_indent(&self, item: &SyntaxNode, container: &SyntaxNode) -> u32 {
        match container.kind() {
            K::CompilationUnit => 0,
            K::FileScopedNamespaceDeclaration => self.node_line_indent(container),
            K::SwitchSection => {
                let base = container
                    .parent()
                    .map_or(0, |switch| self.brace_base(switch));
                let style = &self.options.style;
                let labels = base + u32::from(style.indent_switch_labels) * self.unit();
                if is_switch_label(item.kind()) {
                    labels
                } else {
                    labels + u32::from(style.indent_case_contents) * self.unit()
                }
            }
            _ => self.brace_base(container) + self.unit(),
        }
    }

    /// The indentation token `index` gets when it starts a line.
    fn indent_of(&self, index: usize) -> u32 {
        let token = &self.tokens[index].token;
        if token.kind() == K::EndOfFileToken {
            return 0;
        }
        let parent = token.parent().clone();
        if matches!(token.kind(), K::OpenBraceToken | K::CloseBraceToken)
            && is_container(parent.kind())
        {
            return self.brace_base(&parent);
        }
        let start = token.span().start();
        let mut node = Some(parent);
        while let Some(current) = node {
            if current.span().start() != start {
                // Attribute lists after the first are part of the head of
                // the declaration they decorate.
                break;
            }
            match current.kind() {
                K::ElseClause => {
                    if let Some(statement) = current.parent() {
                        return self.node_line_indent(statement);
                    }
                }
                K::CatchClause | K::FinallyClause => {
                    if let Some(statement) = current.parent() {
                        return self.node_line_indent(statement);
                    }
                }
                K::AttributeList => {
                    if let Some(declaration) = current.parent()
                        && is_decorated(declaration.kind())
                        && declaration.span().start() != start
                    {
                        return self.line_indent_at(declaration.span().start());
                    }
                }
                _ => {}
            }
            if let Some(container) = item_container(&current) {
                let indent = self.item_indent(&current, &container);
                return if current.kind() == K::LabeledStatement {
                    indent.saturating_sub(self.unit())
                } else {
                    indent
                };
            }
            if let Some(owner) = embedded_owner(&current) {
                return self.embedded_indent(&current, &owner);
            }
            if let Some(labeled) = current.parent()
                && labeled.kind() == K::LabeledStatement
                && current.kind().is_statement_node()
            {
                return self.node_line_indent(labeled) + self.unit();
            }
            node = current.parent().cloned();
        }
        // Query clauses line up under the query's first `from`.
        if query_clause_at(token).is_some()
            && let Some(query) = token
                .parent()
                .ancestors()
                .find(|node| node.kind() == K::QueryExpression)
        {
            let first = self.index_at(query.span().start());
            if first < index {
                return self.new_col[first];
            }
        }
        if token.kind() == K::WhileKeyword && token.parent().kind() == K::DoStatement {
            return self.node_line_indent(token.parent());
        }
        // The declaration after its attributes: `[Test]` on one line,
        // `public void M()` on the next.
        if index > 0 {
            let previous = &self.tokens[index - 1].token;
            if previous.kind() == K::CloseBracketToken
                && previous.parent().kind() == K::AttributeList
                && let Some(declaration) = previous.parent().parent()
                && is_decorated(declaration.kind())
                && declaration.span().contains(start)
            {
                return self.line_indent_at(declaration.span().start());
            }
        }
        self.continuation_indent(index)
    }

    /// An embedded statement: one level inside the statement that owns it,
    /// except `using` inside `using` (and `fixed` inside `fixed`), which
    /// Roslyn stacks, and the `if` of an `else if`.
    fn embedded_indent(&self, statement: &SyntaxNode, owner: &SyntaxNode) -> u32 {
        let base = self.node_line_indent(owner);
        let stacked = matches!(
            (owner.kind(), statement.kind()),
            (K::UsingStatement, K::UsingStatement)
                | (K::FixedStatement, K::FixedStatement)
                | (K::ElseClause, K::IfStatement)
        );
        if stacked { base } else { base + self.unit() }
    }

    /// A line that continues an expression: it moves by as much as the
    /// statement or declaration it belongs to moved.
    fn continuation_indent(&self, index: usize) -> u32 {
        let token = &self.tokens[index].token;
        let start = token.span().start();
        let old = self.old_col(start);
        let anchor = std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find(|node| node.span().start() < start && is_anchor(node));
        let Some(anchor) = anchor else {
            return old;
        };
        let anchor_index = self.index_at(start_after_attributes(&anchor));
        if anchor_index >= index {
            return old;
        }
        let anchor_start = self.tokens[anchor_index].token.span().start();
        let moved = i64::from(self.new_col[anchor_index]) - i64::from(self.old_col(anchor_start));
        u32::try_from((i64::from(old) + moved).max(0)).unwrap_or_default()
    }

    // MARK: line breaks

    /// Whether token `index`, which starts a line, belongs at the end of the
    /// line before instead: a `{` whose kind the options want on the line
    /// of its construct, or an `else`, `catch` or `finally` they want after
    /// the `}`. Only a gap of whitespace and line breaks is closed; one with
    /// a comment or a directive in it stays as written.
    fn joins_previous_line(&self, index: usize) -> bool {
        let token = &self.tokens[index].token;
        let previous = &self.tokens[index - 1].token;
        let plain = self.tokens[index]
            .gap
            .iter()
            .all(|trivia| matches!(trivia.kind(), K::WhitespaceTrivia | K::EndOfLineTrivia));
        if !plain {
            return false;
        }
        let style = &self.options.style;
        match token.kind() {
            K::OpenBraceToken => {
                let container = token.parent();
                is_container(container.kind())
                    && wants_own_line(container)
                    && !style.new_line_before_open_brace.wants(container)
                    && !matches!(
                        previous.kind(),
                        K::OpenBraceToken | K::CloseBraceToken | K::SemicolonToken
                    )
            }
            K::ElseKeyword => previous.kind() == K::CloseBraceToken && !style.new_line_before_else,
            K::CatchKeyword => {
                previous.kind() == K::CloseBraceToken && !style.new_line_before_catch
            }
            K::FinallyKeyword => {
                previous.kind() == K::CloseBraceToken && !style.new_line_before_finally
            }
            _ => false,
        }
    }

    /// Whether a line break must go between two tokens that share a line.
    fn forced_newline(&self, previous: &SyntaxToken, token: &SyntaxToken) -> bool {
        let spans_lines = |from: u32, to: u32| self.lines.line_of(from) != self.lines.line_of(to);
        let style = &self.options.style;
        // `csharp_preserve_single_line_blocks = false`: a block or an
        // accessor list is laid out over lines even when written on one.
        let unfolds = |container: &SyntaxNode| {
            !style.preserve_single_line_blocks
                && matches!(container.kind(), K::Block | K::AccessorList)
        };

        // Allman: a multi-line construct's `{` on its own line.
        if token.kind() == K::OpenBraceToken
            && is_container(token.parent().kind())
            && wants_own_line(token.parent())
            && style.new_line_before_open_brace.wants(token.parent())
        {
            let container = token.parent();
            let end = braces(container).map_or(container.span().end(), |(_, close)| close);
            if spans_lines(construct_start(container), end) || unfolds(container) {
                return true;
            }
        }
        // A multi-line pair of braces holds its contents on lines of their
        // own.
        if previous.kind() == K::OpenBraceToken
            && is_container(previous.parent().kind())
            && (token.kind() != K::CloseBraceToken || unfolds(previous.parent()))
            && let Some((open, close)) = braces(previous.parent())
            && (spans_lines(open, close) || unfolds(previous.parent()))
        {
            return true;
        }
        if token.kind() == K::CloseBraceToken
            && is_container(token.parent().kind())
            && previous.kind() != K::OpenBraceToken
            && let Some((open, close)) = braces(token.parent())
            && (spans_lines(open, close) || unfolds(token.parent()))
        {
            return true;
        }
        // `else`, `catch` and `finally` after a `}`.
        if previous.kind() == K::CloseBraceToken
            && match token.kind() {
                K::ElseKeyword => style.new_line_before_else,
                K::CatchKeyword => style.new_line_before_catch,
                K::FinallyKeyword => style.new_line_before_finally,
                _ => false,
            }
            && let Some(statement) = token.parent().parent()
            && spans_lines(statement.span().start(), token.span().end())
        {
            return true;
        }
        // `csharp_preserve_single_line_statements = false`: one statement
        // to a line.
        if !style.preserve_single_line_statements
            && previous.kind() == K::SemicolonToken
            && previous.parent().kind().is_statement_node()
            && previous
                .parent()
                .parent()
                .is_some_and(|holder| matches!(holder.kind(), K::Block | K::SwitchSection))
            && token.kind() != K::CloseBraceToken
        {
            return true;
        }
        // A member of an object initializer or an anonymous type on each
        // line, once the initializer spans lines.
        if previous.kind() == K::CommaToken
            && matches!(
                previous.parent().kind(),
                K::ObjectInitializerExpression
                    | K::AnonymousObjectCreationExpression
                    | K::WithInitializerExpression
            )
            && token.kind() != K::CloseBraceToken
            && let Some((open, close)) = braces(previous.parent())
            && spans_lines(open, close)
        {
            return true;
        }
        // Each clause of a multi-line query on its own line.
        if let Some(clause) = query_clause_at(token)
            && let Some(query) = clause
                .ancestors()
                .find(|node| node.kind() == K::QueryExpression)
            && spans_lines(query.span().start(), query.span().end())
        {
            return true;
        }
        false
    }
}

// MARK: - spacing

/// The spaces between two tokens that stay on one line.
fn spacing(previous: &SyntaxToken, token: &SyntaxToken) -> u32 {
    let (before, after) = (previous.kind(), token.kind());
    let (before_parent, after_parent) = (previous.parent().kind(), token.parent().kind());
    if after == K::EndOfFileToken {
        return 0;
    }
    // `for (int i = 0; i < n; i++)`, and Roslyn's `for (; ; )`.
    if before == K::SemicolonToken && before_parent == K::ForStatement {
        return 1;
    }
    if matches!(after, K::SemicolonToken | K::CommaToken) {
        return 0;
    }
    if matches!(before, K::OpenParenToken | K::OpenBracketToken)
        || matches!(after, K::CloseParenToken | K::CloseBracketToken)
    {
        return 0;
    }
    if (after == K::GreaterThanToken && is_generic_list(after_parent))
        || (matches!(before, K::LessThanToken) && is_generic_list(before_parent))
        || (after == K::LessThanToken && is_generic_list(after_parent))
    {
        return 0;
    }
    if matches!(before, K::CommaToken | K::SemicolonToken) {
        return 1;
    }
    if matches!(
        before,
        K::DotToken | K::MinusGreaterThanToken | K::ColonColonToken
    ) || matches!(
        after,
        K::DotToken | K::MinusGreaterThanToken | K::ColonColonToken
    ) {
        return 0;
    }
    if before == K::QuestionToken && before_parent == K::ConditionalAccessExpression {
        return 0;
    }
    if after == K::QuestionToken
        && matches!(
            after_parent,
            K::ConditionalAccessExpression | K::NullableType
        )
    {
        return 0;
    }
    if (after == K::ExclamationToken && after_parent == K::SuppressNullableWarningExpression)
        || (matches!(after, K::PlusPlusToken | K::MinusMinusToken)
            && matches!(
                after_parent,
                K::PostIncrementExpression | K::PostDecrementExpression
            ))
    {
        return 0;
    }
    if is_prefix_operator(previous) {
        return 0;
    }
    if before == K::TildeToken && before_parent == K::DestructorDeclaration {
        return 0;
    }
    if after == K::AsteriskToken && matches!(after_parent, K::PointerType | K::FunctionPointerType)
    {
        return 0;
    }
    if before == K::CloseParenToken && before_parent == K::CastExpression {
        return 0;
    }
    if (after == K::DotDotToken && after_parent == K::RangeExpression)
        || (before == K::DotDotToken && before_parent == K::RangeExpression)
    {
        return 0;
    }
    if after == K::ColonToken {
        return u32::from(matches!(
            after_parent,
            K::ConditionalExpression
                | K::BaseList
                | K::TypeParameterConstraintClause
                | K::BaseConstructorInitializer
                | K::ThisConstructorInitializer
        ));
    }
    if after == K::OpenParenToken {
        return space_before_paren(previous, token);
    }
    if after == K::OpenBracketToken {
        return match after_parent {
            K::ArrayRankSpecifier
            | K::BracketedArgumentList
            | K::BracketedParameterList
            | K::ImplicitArrayCreationExpression
            | K::ImplicitStackAllocArrayCreationExpression
            | K::FunctionPointerUnmanagedCallingConventionList => 0,
            K::AttributeList => u32::from(before != K::CloseBracketToken),
            _ => 1,
        };
    }
    1
}

/// Before `(`: none in a call or a declaration, one after a control-flow
/// keyword and anywhere an expression in parentheses begins.
fn space_before_paren(previous: &SyntaxToken, paren: &SyntaxToken) -> u32 {
    match paren.parent().kind() {
        K::ArgumentList
        | K::AttributeArgumentList
        | K::TypeOfExpression
        | K::SizeOfExpression
        | K::DefaultExpression
        | K::CheckedExpression
        | K::UncheckedExpression
        | K::MakeRefExpression
        | K::RefTypeExpression
        | K::RefValueExpression
        | K::ConstructorConstraint => 0,
        K::ParameterList => match paren.parent().parent().map(SyntaxNode::kind) {
            Some(K::ParenthesizedLambdaExpression | K::AnonymousMethodExpression) => 1,
            _ => 0,
        },
        K::PositionalPatternClause => u32::from(!matches!(
            previous.kind(),
            K::IdentifierToken | K::GreaterThanToken
        )),
        _ => 1,
    }
}

fn is_prefix_operator(token: &SyntaxToken) -> bool {
    matches!(
        token.parent().kind(),
        K::UnaryPlusExpression
            | K::UnaryMinusExpression
            | K::BitwiseNotExpression
            | K::LogicalNotExpression
            | K::PreIncrementExpression
            | K::PreDecrementExpression
            | K::AddressOfExpression
            | K::PointerIndirectionExpression
            | K::IndexExpression
    ) && token.span().start() == token.parent().span().start()
        && token.kind().is_punctuation()
}

/// Whether two tokens written with nothing between them would lex as
/// something else: two words, or two operators that make a longer one.
fn would_merge(before: &str, after: &str) -> bool {
    let (Some(last), Some(first)) = (before.chars().last(), after.chars().next()) else {
        return false;
    };
    let word = |ch: char| ch.is_alphanumeric() || ch == '_' || ch == '@';
    if word(last) && word(first) {
        return true;
    }
    matches!(
        (last, first),
        ('+', '+' | '=')
            | ('-', '-' | '=' | '>')
            | ('&', '&' | '=')
            | ('|', '|' | '=')
            | ('<', '<' | '=')
            | ('=', '=' | '>')
            | ('!', '=')
            | ('?', '?')
            | (':', ':')
            | ('.', '.')
            | ('/', '/' | '*' | '=')
            | ('*', '/' | '=')
            | ('%' | '^', '=')
    )
}

// MARK: - the shape of the tree

/// Nodes whose `{ }` hold items a level further in.
pub(crate) fn is_container(kind: K) -> bool {
    is_type_declaration(kind)
        || is_initializer(kind)
        || matches!(
            kind,
            K::Block
                | K::NamespaceDeclaration
                | K::AccessorList
                | K::SwitchStatement
                | K::SwitchExpression
                | K::AnonymousObjectCreationExpression
                | K::ExtensionBlockDeclaration
        )
}

pub(crate) fn is_type_declaration(kind: K) -> bool {
    matches!(
        kind,
        K::ClassDeclaration
            | K::StructDeclaration
            | K::InterfaceDeclaration
            | K::EnumDeclaration
            | K::RecordDeclaration
            | K::RecordStructDeclaration
    )
}

pub(crate) fn is_initializer(kind: K) -> bool {
    matches!(
        kind,
        K::ObjectInitializerExpression
            | K::CollectionInitializerExpression
            | K::ArrayInitializerExpression
            | K::ComplexElementInitializerExpression
            | K::WithInitializerExpression
    )
}

fn is_switch_label(kind: K) -> bool {
    matches!(
        kind,
        K::CaseSwitchLabel | K::CasePatternSwitchLabel | K::DefaultSwitchLabel
    )
}

fn is_generic_list(kind: K) -> bool {
    matches!(
        kind,
        K::TypeArgumentList | K::TypeParameterList | K::FunctionPointerParameterList
    )
}

fn is_directive(kind: K) -> bool {
    matches!(
        kind,
        K::IfDirectiveTrivia
            | K::ElifDirectiveTrivia
            | K::ElseDirectiveTrivia
            | K::EndIfDirectiveTrivia
            | K::RegionDirectiveTrivia
            | K::EndRegionDirectiveTrivia
            | K::DefineDirectiveTrivia
            | K::UndefDirectiveTrivia
            | K::ErrorDirectiveTrivia
            | K::WarningDirectiveTrivia
            | K::LineDirectiveTrivia
            | K::PragmaWarningDirectiveTrivia
            | K::PragmaChecksumDirectiveTrivia
            | K::ReferenceDirectiveTrivia
            | K::LoadDirectiveTrivia
            | K::NullableDirectiveTrivia
            | K::BadDirectiveTrivia
            | K::IgnoredDirectiveTrivia
    )
}

/// Declarations whose attributes come first and belong to their head.
fn is_decorated(kind: K) -> bool {
    kind.is_declaration_node() || kind == K::LocalFunctionStatement
}

/// A container's `{` and `}`, as the start of one and the end of the other.
pub(crate) fn braces(container: &SyntaxNode) -> Option<(u32, u32)> {
    let open = container.child_token_of_kind(K::OpenBraceToken)?;
    let close = container
        .child_tokens()
        .filter(|token| token.kind() == K::CloseBraceToken)
        .last()
        .filter(|token| !token.is_missing())
        .map_or(container.span().end(), |token| token.span().end());
    Some((open.span().start(), close))
}

/// Where a declaration or statement starts once its attributes are passed.
pub(crate) fn start_after_attributes(node: &SyntaxNode) -> u32 {
    for child in node.children_with_tokens() {
        if let SyntaxElement::Node(inner) = &child
            && inner.kind() == K::AttributeList
        {
            continue;
        }
        if child.span().is_empty() {
            continue;
        }
        return child.span().start();
    }
    node.span().start()
}

/// Where the construct a container's braces belong to starts: the `if` of
/// an `if` block, the name of a method, the `new` of an initializer.
pub(crate) fn construct_start(container: &SyntaxNode) -> u32 {
    let Some(parent) = container.parent() else {
        return container.span().start();
    };
    match container.kind() {
        K::Block => {
            if matches!(
                parent.kind(),
                K::Block | K::SwitchSection | K::GlobalStatement
            ) {
                container.span().start()
            } else {
                start_after_attributes(parent)
            }
        }
        K::AccessorList => start_after_attributes(parent),
        kind if is_initializer(kind) => {
            if item_container(container).is_some() {
                container.span().start()
            } else {
                parent.span().start()
            }
        }
        _ => start_after_attributes(container),
    }
}

/// Whether a multi-line construct wants its `{` on a line of its own.
fn wants_own_line(container: &SyntaxNode) -> bool {
    let parent = container.parent().map(SyntaxNode::kind);
    match container.kind() {
        // A block inside a block starts its own line already, or is meant
        // to share one; a case's block goes under its label.
        K::Block => !matches!(
            parent,
            Some(K::Block | K::LabeledStatement | K::GlobalStatement) | None
        ),
        // `{ 1, 2 }` inside `new[] { ... }` is an element, not a construct.
        kind if is_initializer(kind) => parent.is_none_or(|parent| !is_initializer(parent)),
        _ => true,
    }
}

/// The container `node` is an item of, if it is one.
pub(crate) fn item_container(node: &SyntaxNode) -> Option<SyntaxNode> {
    let parent = node.parent()?.clone();
    let inside_braces =
        |parent: &SyntaxNode| braces(parent).is_some_and(|(open, _)| node.span().start() > open);
    let item = match parent.kind() {
        K::CompilationUnit => true,
        K::FileScopedNamespaceDeclaration => parent
            .child_token_of_kind(K::SemicolonToken)
            .is_some_and(|semicolon| node.span().start() >= semicolon.span().end()),
        K::SwitchStatement => node.kind() == K::SwitchSection,
        K::SwitchSection => true,
        K::SwitchExpression => node.kind() == K::SwitchExpressionArm,
        kind if is_container(kind) => inside_braces(&parent),
        _ => false,
    };
    item.then_some(parent)
}

/// The statement an embedded statement belongs to: the `if` whose body it
/// is when that body has no braces.
pub(crate) fn embedded_owner(node: &SyntaxNode) -> Option<SyntaxNode> {
    if !node.kind().is_statement_node() {
        return None;
    }
    let parent = node.parent()?;
    matches!(
        parent.kind(),
        K::IfStatement
            | K::ElseClause
            | K::WhileStatement
            | K::ForStatement
            | K::ForEachStatement
            | K::ForEachVariableStatement
            | K::DoStatement
            | K::UsingStatement
            | K::LockStatement
            | K::FixedStatement
    )
    .then(|| parent.clone())
}

/// Nodes a wrapped line keeps its position relative to.
fn is_anchor(node: &SyntaxNode) -> bool {
    let kind = node.kind();
    kind.is_statement_node()
        || kind.is_declaration_node()
        || is_switch_label(kind)
        || matches!(
            kind,
            K::SwitchExpressionArm
                | K::AnonymousObjectMemberDeclarator
                | K::ElseClause
                | K::CatchClause
                | K::FinallyClause
        )
        || item_container(node).is_some()
}

/// The query clause `token` starts, other than a query's first `from`.
fn query_clause_at(token: &SyntaxToken) -> Option<SyntaxNode> {
    let start = token.span().start();
    std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| node.span().start() == start)
        .find(|node| {
            matches!(
                node.kind(),
                K::FromClause
                    | K::LetClause
                    | K::WhereClause
                    | K::JoinClause
                    | K::OrderByClause
                    | K::SelectClause
                    | K::GroupClause
                    | K::QueryContinuation
            ) && node
                .parent()
                .is_some_and(|parent| matches!(parent.kind(), K::QueryBody | K::QueryContinuation))
        })
}

/// The indentation, in columns, of the line holding `offset`, as written.
pub(crate) fn original_indent(text: &str, lines: &LineIndex, offset: u32, tab_size: u32) -> u32 {
    let line = lines.line_of(offset.min(text.len() as u32));
    let start = lines.line_start(line).unwrap_or_default() as usize;
    let tab = tab_size.max(1);
    let mut column = 0;
    for ch in text[start..].chars() {
        match ch {
            ' ' => column += 1,
            '\t' => column += tab - column % tab,
            _ => break,
        }
    }
    column
}

// MARK: - smart indentation

/// The indentation a new line should get when Enter is pressed at `offset`
/// of `text` (the text before the line break goes in): what the caret sits
/// at on the new line. `None` when there is no opinion to give, as inside a
/// string that spans lines, whose content is the user's.
///
/// Like Roslyn's smart indenter, this reads the indentation the lines above
/// already have rather than what formatting them would give.
#[must_use]
pub fn indentation_for_new_line(
    root: &SyntaxNode,
    text: &str,
    offset: u32,
    options: &FormatOptions,
) -> Option<String> {
    let columns = SmartIndent {
        root,
        text,
        lines: LineIndex::new(text),
        options,
    }
    .columns(offset.min(text.len() as u32))?;
    let engine_indent = |columns: u32| {
        if options.use_tabs {
            let tab = options.tab_size.max(1);
            let mut text = "\t".repeat((columns / tab) as usize);
            text.push_str(&" ".repeat((columns % tab) as usize));
            text
        } else {
            " ".repeat(columns as usize)
        }
    };
    Some(engine_indent(columns))
}

struct SmartIndent<'a> {
    root: &'a SyntaxNode,
    text: &'a str,
    lines: LineIndex,
    options: &'a FormatOptions,
}

impl SmartIndent<'_> {
    fn indent_at(&self, offset: u32) -> u32 {
        original_indent(self.text, &self.lines, offset, self.options.tab_size)
    }

    fn column_of(&self, offset: u32) -> u32 {
        let line = self.lines.line_of(offset);
        let start = self.lines.line_start(line).unwrap_or_default();
        let tab = self.options.tab_size.max(1);
        self.text[start as usize..offset as usize]
            .chars()
            .fold(0, |column, ch| {
                if ch == '\t' {
                    column + tab - column % tab
                } else {
                    column + 1
                }
            })
    }

    fn unit(&self) -> u32 {
        self.options.indent_size
    }

    fn columns(&self, offset: u32) -> Option<u32> {
        // Inside a token that spans lines, or a comment: the content's own.
        if let Some(holder) = self.root.find_token(offset) {
            if holder.span().start() < offset && offset < holder.span().end() {
                let kind = holder.kind();
                if kind.is_literal_token() || kind == K::InterpolatedStringTextToken {
                    return None;
                }
            }
            for trivia in holder
                .leading_trivia()
                .into_iter()
                .chain(holder.trailing_trivia())
            {
                let span = trivia.span();
                let inside = span.start() < offset && offset <= span.end();
                match trivia.kind() {
                    K::SingleLineDocumentationCommentTrivia
                    | K::MultiLineDocumentationCommentTrivia
                    | K::MultiLineCommentTrivia
                        if inside
                            && (offset < span.end()
                                || trivia.kind() != K::MultiLineCommentTrivia) =>
                    {
                        return Some(self.indent_at(offset));
                    }
                    K::DisabledTextTrivia if span.contains(offset) => {
                        return Some(self.indent_at(offset));
                    }
                    _ => {}
                }
            }
        }

        let line_end = line_end(self.text, &self.lines, offset);
        let rest = self
            .root
            .descendant_tokens()
            .find(|token| {
                !token.span().is_empty()
                    && token.span().start() >= offset
                    && token.span().start() < line_end.max(offset + 1)
                    && token.kind() != K::EndOfFileToken
            })
            .filter(|token| token.span().start() <= line_end);
        let previous = self
            .root
            .descendant_tokens()
            .filter(|token| !token.span().is_empty() && token.span().end() <= offset)
            .last();

        if let Some(rest) = &rest
            && let Some(columns) = self.for_leading(rest)
        {
            return Some(columns);
        }
        let Some(previous) = previous else {
            return Some(0);
        };
        Some(self.after(&previous, offset))
    }

    /// When the text after the caret starts with a token that has its own
    /// place: a closing brace, an `else`.
    fn for_leading(&self, token: &SyntaxToken) -> Option<u32> {
        let parent = token.parent();
        match token.kind() {
            K::CloseBraceToken | K::OpenBraceToken if is_container(parent.kind()) => {
                let (open, _) = braces(parent)?;
                if token.kind() == K::CloseBraceToken {
                    Some(self.indent_at(open))
                } else {
                    Some(self.indent_at(construct_start(parent)))
                }
            }
            K::ElseKeyword | K::CatchKeyword | K::FinallyKeyword => {
                Some(self.indent_at(parent.parent()?.span().start()))
            }
            _ => None,
        }
    }

    /// The indentation for a line that follows `previous`.
    fn after(&self, previous: &SyntaxToken, offset: u32) -> u32 {
        let parent = previous.parent().clone();
        match previous.kind() {
            K::OpenBraceToken if is_container(parent.kind()) => {
                return self.indent_at(previous.span().start()) + self.unit();
            }
            K::ColonToken
                if is_switch_label(parent.kind()) || parent.kind() == K::LabeledStatement =>
            {
                return self.indent_at(previous.span().start()) + self.unit();
            }
            K::CloseParenToken
                if matches!(
                    parent.kind(),
                    K::IfStatement
                        | K::WhileStatement
                        | K::ForStatement
                        | K::ForEachStatement
                        | K::ForEachVariableStatement
                        | K::UsingStatement
                        | K::LockStatement
                        | K::FixedStatement
                ) =>
            {
                // The header is done and its body has not begun: the body
                // goes one level in.
                if embedded_body(&parent)
                    .is_none_or(|body| body.span().is_empty() || body.span().start() >= offset)
                {
                    return self.indent_at(parent.span().start()) + self.unit();
                }
            }
            K::ElseKeyword | K::DoKeyword => {
                return self.indent_at(previous.span().start()) + self.unit();
            }
            K::CloseBracketToken
                if parent.kind() == K::AttributeList
                    && parent
                        .parent()
                        .is_some_and(|owner| is_decorated(owner.kind())) =>
            {
                return self.indent_at(parent.span().start());
            }
            _ => {}
        }
        if matches!(previous.kind(), K::SemicolonToken | K::CloseBraceToken)
            && let Some(done) = self.completed(previous)
        {
            return self.item_indent(&done);
        }
        self.continuation(previous, offset)
    }

    /// The statement or declaration `last` completes, widened to the
    /// statements that end with it too: the `if` whose body just ended.
    fn completed(&self, last: &SyntaxToken) -> Option<SyntaxNode> {
        let end = last.span().end();
        let ends_here = |node: &SyntaxNode| node.span().end() == end;
        let mut done = std::iter::once(last.parent().clone())
            .chain(last.parent().ancestors())
            .find(|node| {
                ends_here(node)
                    && (node.kind().is_statement_node()
                        || node.kind().is_declaration_node()
                        || item_container(node).is_some())
            })?;
        while let Some(parent) = done.parent().cloned() {
            let climbs = ends_here(&parent)
                && (embedded_owner(&done).is_some()
                    || matches!(
                        parent.kind(),
                        K::ElseClause
                            | K::CatchClause
                            | K::FinallyClause
                            | K::TryStatement
                            | K::IfStatement
                    )
                    || (done.kind() == K::Block && !is_container_parent(&parent))
                    || (done.kind() == K::AccessorList));
            if !climbs {
                break;
            }
            done = parent;
        }
        // A lambda's body ending is not the end of the statement around it.
        if !done.kind().is_statement_node()
            && !done.kind().is_declaration_node()
            && item_container(&done).is_none()
        {
            return None;
        }
        Some(done)
    }

    /// Where an item that has just been completed sits, so that the next one
    /// lines up with it.
    fn item_indent(&self, item: &SyntaxNode) -> u32 {
        let start = start_after_attributes(item);
        let line_start = self
            .lines
            .line_start(self.lines.line_of(start))
            .unwrap_or_default();
        let first_on_line = self.text[line_start as usize..start as usize]
            .trim()
            .is_empty();
        if first_on_line && item.kind() != K::LabeledStatement {
            return self.indent_at(start);
        }
        match item_container(item) {
            Some(container) if container.kind() == K::SwitchSection => {
                self.indent_at(container.span().start()) + self.unit()
            }
            Some(container) => match braces(&container) {
                Some((open, _)) => self.indent_at(open) + self.unit(),
                None => self.indent_at(start),
            },
            None => self.indent_at(start),
        }
    }

    /// A line that continues something unfinished: aligned with the first
    /// argument of an open list, or one level in from the statement.
    fn continuation(&self, previous: &SyntaxToken, offset: u32) -> u32 {
        if matches!(previous.kind(), K::OpenParenToken | K::OpenBracketToken) {
            return self.indent_at(previous.span().start()) + self.unit();
        }
        // An open list around the caret.
        let list = std::iter::once(previous.parent().clone())
            .chain(previous.parent().ancestors())
            .find(|node| {
                matches!(
                    node.kind(),
                    K::ArgumentList
                        | K::ParameterList
                        | K::BracketedArgumentList
                        | K::BracketedParameterList
                        | K::AttributeArgumentList
                        | K::TupleExpression
                        | K::TypeArgumentList
                        | K::TypeParameterList
                ) && node
                    .last_token()
                    .is_none_or(|close| close.is_missing() || close.span().start() >= offset)
            });
        if let Some(list) = list {
            let open = list
                .first_token()
                .map_or(list.span().start(), |open| open.span().end());
            let first = list
                .descendant_tokens()
                .find(|token| token.span().start() >= open && !token.span().is_empty());
            if let Some(first) = first
                && first.span().start() < offset
            {
                let same_line =
                    self.lines.line_of(first.span().start()) == self.lines.line_of(open);
                return if same_line {
                    self.column_of(first.span().start())
                } else {
                    self.indent_at(first.span().start())
                };
            }
            return self.indent_at(open) + self.unit();
        }
        // Inside a container's braces, between items: the items' indentation.
        if previous.kind() == K::CommaToken
            && is_container(previous.parent().kind())
            && let Some((open, _)) = braces(previous.parent())
        {
            return self.indent_at(open) + self.unit();
        }
        let statement = std::iter::once(previous.parent().clone())
            .chain(previous.parent().ancestors())
            .find(|node| {
                node.kind().is_statement_node()
                    || node.kind().is_declaration_node()
                    || item_container(node).is_some()
            });
        match statement {
            Some(statement) if statement.kind() != K::CompilationUnit => {
                self.indent_at(start_after_attributes(&statement)) + self.unit()
            }
            _ => self.indent_at(previous.span().start()),
        }
    }
}

/// A statement's embedded body, if it has one yet.
fn embedded_body(statement: &SyntaxNode) -> Option<SyntaxNode> {
    statement
        .children()
        .filter(|child| child.kind().is_statement_node())
        .last()
}

fn is_container_parent(node: &SyntaxNode) -> bool {
    matches!(
        node.kind(),
        K::Block | K::SwitchSection | K::GlobalStatement
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_text::SourceText;

    fn parse(text: &str) -> SyntaxNode {
        rustlyn_syntax::parse(SourceText::new("A.cs", text)).root()
    }

    /// Formats `text`, checking on the way that nothing but whitespace
    /// changed and that formatting the result again changes nothing.
    fn format(text: &str) -> String {
        let edits = format_document(&parse(text), text, &FormatOptions::default());
        let formatted = crate::edit::apply(text, &edits);
        let squeeze = |text: &str| text.split_whitespace().collect::<String>();
        assert_eq!(
            squeeze(text),
            squeeze(&formatted),
            "only whitespace may change"
        );
        let again = format_document(&parse(&formatted), &formatted, &FormatOptions::default());
        assert!(
            again.is_empty(),
            "formatting is not stable:\n{formatted}\nthen:\n{}",
            crate::edit::apply(&formatted, &again)
        );
        formatted
    }

    /// Formats a method body: `body` goes inside `void M()` in a class, and
    /// comes back with that frame taken off again.
    fn in_method(body: &str) -> String {
        let text = format!("class C\n{{\n    void M()\n    {{\n{body}\n    }}\n}}\n");
        let formatted = format(&text);
        let inner = formatted
            .strip_prefix("class C\n{\n    void M()\n    {\n")
            .and_then(|rest| rest.strip_suffix("\n    }\n}\n"))
            .unwrap_or_else(|| panic!("the frame moved:\n{formatted}"));
        inner.to_owned()
    }

    /// Each case: a statement as written, and as Roslyn formats it, eight
    /// columns in.
    fn check_statements(cases: &[(&str, &str)]) {
        for (written, expected) in cases {
            let got = in_method(&format!("        {written}"));
            assert_eq!(got, format!("        {expected}"), "formatting `{written}`");
        }
    }

    #[test]
    fn space_after_control_flow_keywords() {
        check_statements(&[
            ("if(a) b();", "if (a) b();"),
            ("while(a) b();", "while (a) b();"),
            (
                "for(int i=0;i<n;i++) b();",
                "for (int i = 0; i < n; i++) b();",
            ),
            ("foreach(var x in xs) b();", "foreach (var x in xs) b();"),
            ("switch(a) { }", "switch (a) { }"),
            ("using(var s = f()) b();", "using (var s = f()) b();"),
            ("lock(this) b();", "lock (this) b();"),
            ("fixed(int* p = &a) b();", "fixed (int* p = &a) b();"),
            (
                "try { } catch(E e) when(e != null) { }",
                "try { } catch (E e) when (e != null) { }",
            ),
            ("return(a);", "return (a);"),
        ]);
    }

    #[test]
    fn no_space_before_argument_and_parameter_lists() {
        check_statements(&[
            ("M (1, 2);", "M(1, 2);"),
            ("a.M<int> ( );", "a.M<int>();"),
            ("var c = new C ( 1 );", "var c = new C(1);"),
            ("C c = new ( );", "C c = new();"),
            ("var t = typeof (int);", "var t = typeof(int);"),
            (
                "var s = sizeof (int) + default (int);",
                "var s = sizeof(int) + default(int);",
            ),
            ("var n = nameof (M);", "var n = nameof(M);"),
            ("var x = checked (a + b);", "var x = checked(a + b);"),
            ("int Local (int a) => a;", "int Local(int a) => a;"),
        ]);
    }

    #[test]
    fn nothing_inside_parentheses_and_brackets() {
        check_statements(&[
            ("M( a, b );", "M(a, b);"),
            ("var x = ( a + b ) * c;", "var x = (a + b) * c;"),
            ("var y = a[ 0 ][ 1 ];", "var y = a[0][1];"),
            ("int[ ] z = new int[ 3 ];", "int[] z = new int[3];"),
            ("var w = new int[ , ] { };", "var w = new int[,] { };"),
            ("var e = new [ ] { 1 , 2 };", "var e = new[] { 1, 2 };"),
            ("M();", "M();"),
        ]);
    }

    #[test]
    fn spaces_around_binary_and_assignment_operators() {
        check_statements(&[
            ("x=a+b*c-d/e%f;", "x = a + b * c - d / e % f;"),
            ("x+=1; y-=2; z??=w;", "x += 1; y -= 2; z ??= w;"),
            (
                "var b=a==c&&d!=e||f<g&&h>=i;",
                "var b = a == c && d != e || f < g && h >= i;",
            ),
            ("var s=a<<2|b>>1&c^d;", "var s = a << 2 | b >> 1 & c ^ d;"),
            ("var v=a??b;", "var v = a ?? b;"),
            (
                "var t=a is string&&b as object!=null;",
                "var t = a is string && b as object != null;",
            ),
            ("var c=a?b:c;", "var c = a ? b : c;"),
        ]);
    }

    #[test]
    fn lambdas_and_expression_bodies() {
        check_statements(&[
            ("Func<int,int> f=x=>x+1;", "Func<int, int> f = x => x + 1;"),
            ("Func<int> g=()=>1;", "Func<int> g = () => 1;"),
            (
                "var h=async(a,b)=>await a;",
                "var h = async (a, b) => await a;",
            ),
            (
                "Action d=delegate(int x){ };",
                "Action d = delegate (int x) { };",
            ),
        ]);
    }

    #[test]
    fn unary_operators_are_tight() {
        check_statements(&[
            ("var a=! b;", "var a = !b;"),
            ("var n=- x + + y;", "var n = -x + +y;"),
            ("i ++; -- j; ++ k;", "i++; --j; ++k;"),
            ("var m=~ bits;", "var m = ~bits;"),
            ("var p=& x; * p=1;", "var p = &x; *p = 1;"),
            ("var q=- -x;", "var q = - -x;"),
            ("var r=a - -b;", "var r = a - -b;"),
            ("var s=x !.Length;", "var s = x!.Length;"),
        ]);
    }

    #[test]
    fn member_access_and_casts() {
        check_statements(&[
            ("var a=b . c ?. d ?[ 0 ];", "var a = b.c?.d?[0];"),
            ("var p=q -> r;", "var p = q->r;"),
            (
                "var g=global :: System . Int32 . MaxValue;",
                "var g = global::System.Int32.MaxValue;",
            ),
            ("var y=( int ) x;", "var y = (int)x;"),
            ("var z=(object)(a);", "var z = (object)(a);"),
        ]);
    }

    #[test]
    fn commas_semicolons_and_for() {
        check_statements(&[
            ("M(a ,b ,c) ;", "M(a, b, c);"),
            ("for(;;) { }", "for (; ; ) { }"),
            (
                "for (int i=0,j=1 ; i<j ; i++,j--) { }",
                "for (int i = 0, j = 1; i < j; i++, j--) { }",
            ),
        ]);
    }

    #[test]
    fn generics_nullable_and_pointers() {
        check_statements(&[
            ("List < int > a;", "List<int> a;"),
            (
                "Dictionary<string , List<int>> b;",
                "Dictionary<string, List<int>> b;",
            ),
            ("int ? c = null;", "int? c = null;"),
            ("int * d;", "int* d;"),
            ("var t=typeof(List< >);", "var t = typeof(List<>);"),
            ("var l=a < b;", "var l = a < b;"),
        ]);
    }

    #[test]
    fn colons() {
        check_statements(&[
            ("M(name : 1);", "M(name: 1);"),
            ("var t=(a : 1, b : 2);", "var t = (a: 1, b: 2);"),
            (
                "var ok=s is { Length : > 0 };",
                "var ok = s is { Length: > 0 };",
            ),
        ]);
        let text = "class C:B,I where T:class { C(int a):base(a) { } }\n";
        assert_eq!(
            format(text),
            "class C : B, I where T : class { C(int a) : base(a) { } }\n"
        );
    }

    #[test]
    fn patterns_ranges_and_collections() {
        check_statements(&[
            ("var a=x is not null;", "var a = x is not null;"),
            ("var b=x is >5 and <10;", "var b = x is > 5 and < 10;"),
            ("var c=xs[..^1];", "var c = xs[..^1];"),
            ("var d=xs[1 .. 3];", "var d = xs[1..3];"),
            ("int[] e=[1,2,..rest];", "int[] e = [1, 2, .. rest];"),
            ("var (f,g)=t;", "var (f, g) = t;"),
            ("if(o is Point(1,2)) { }", "if (o is Point(1, 2)) { }"),
        ]);
    }

    /// Blocks inside blocks, hundreds deep. Each line's indentation was
    /// worked out from every container out to the file, and each token
    /// looked through all its ancestors for an interpolated string: two
    /// thousand nested blocks took half a minute (found by fuzzing,
    /// `examples/fuzz.rs` in rustlyn-ide).
    #[test]
    fn blocks_hundreds_deep_are_formatted_in_time() {
        let formatting = std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let body = format!(
                    "{}x++;{}",
                    "{ x++; x++; x++; x++;\n".repeat(1000),
                    "}\n".repeat(1000)
                );
                let started = std::time::Instant::now();
                let formatted = in_method(&body);
                assert!(
                    started.elapsed().as_secs() < 5,
                    "took {:?}",
                    started.elapsed()
                );
                // The innermost statement is a thousand levels in, past
                // the two of the frame.
                let innermost = formatted
                    .lines()
                    .find(|line| line.trim() == "x++;" && line.len() > 4000);
                assert!(innermost.is_some_and(|line| line.len() - 4 == 4 * 1002));
            })
            .expect("a thread to format on");
        formatting.join().expect("the formatting");
    }

    /// What generated code is full of: a table written as an `else if` for
    /// each case, a call for each step, a term for each piece. The tree is
    /// as deep as the ladder is long, and the formatter walks it on the
    /// stack the editor gives it.
    #[test]
    fn ladders_and_chains_of_thousands_are_formatted() {
        let formatting = std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let n = 5000;
                // Not `assert_eq!`: the text is long.
                let ladder = format!(
                    "        if (a) b();{}",
                    "\n        else if (a) b();".repeat(n)
                );
                assert!(in_method(&ladder) == ladder, "the ladder moved");
                let ternary = format!("        x = {}0;", "a ? 1 : ".repeat(n));
                assert!(in_method(&ternary) == ternary, "the ternary moved");
                let calls = format!("        x = a{};", ".B()".repeat(n));
                assert!(in_method(&calls) == calls, "the calls moved");
                let terms = format!("        x = a{};", " + b".repeat(n));
                assert!(in_method(&terms) == terms, "the terms moved");
            })
            .expect("a thread to format on");
        formatting.join().expect("the formatting");
    }

    #[test]
    fn braces_on_one_line_stay_on_one_line() {
        assert_eq!(format("class C{}\n"), "class C { }\n");
        assert_eq!(
            format("class C { int P{get;set;} void M(){ return; } }\n"),
            "class C { int P { get; set; } void M() { return; } }\n"
        );
        check_statements(&[
            (
                "if (a) { b(); } else { c(); }",
                "if (a) { b(); } else { c(); }",
            ),
            ("var o=new C{A=1,B=2};", "var o = new C { A = 1, B = 2 };"),
            (
                "var l=new List<int>{1,2};",
                "var l = new List<int> { 1, 2 };",
            ),
        ]);
    }

    #[test]
    fn allman_braces_for_multi_line_constructs() {
        let text = "namespace N {\nclass C : B {\nint x;\nvoid M() {\nif (a) {\nb();\n} else if (c) {\nd();\n} else {\ne();\n}\n}\n}\n}\n";
        let expected = "namespace N
{
    class C : B
    {
        int x;
        void M()
        {
            if (a)
            {
                b();
            }
            else if (c)
            {
                d();
            }
            else
            {
                e();
            }
        }
    }
}
";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn statements_on_a_brace_line_get_their_own() {
        let text = "class C\n{\n    void M() { a();\n        b(); }\n}\n";
        let expected = "class C\n{\n    void M()\n    {\n        a();\n        b();\n    }\n}\n";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn loops_try_and_do() {
        let body = "        do {\nx++;\n} while (x < 10);\n        try {\na();\n} catch (E e) {\n} finally {\nb();\n}\n        while (a) {\n}";
        let expected = "        do
        {
            x++;
        } while (x < 10);
        try
        {
            a();
        }
        catch (E e)
        {
        }
        finally
        {
            b();
        }
        while (a)
        {
        }";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn embedded_statements_are_indented_once() {
        let body = "if (a)\nb();\nelse\nc();\nif (a)\nif (b)\nc();\nwhile (x)\nx--;\nfor (;;)\nbreak;\nforeach (var i in xs)\nuse(i);\nusing (var a = f())\nusing (var b = g())\n{\n}";
        let expected = "        if (a)
            b();
        else
            c();
        if (a)
            if (b)
                c();
        while (x)
            x--;
        for (; ; )
            break;
        foreach (var i in xs)
            use(i);
        using (var a = f())
        using (var b = g())
        {
        }";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn switch_sections_labels_and_goto() {
        let body = "switch (a) {\ncase 1:\ncase 2:\nb();\nbreak;\ncase int n when n > 3:\n{\nc();\n}\nbreak;\ndefault:\nreturn;\n}\nretry:\nif (d) goto retry;";
        let expected = "        switch (a)
        {
            case 1:
            case 2:
                b();
                break;
            case int n when n > 3:
                {
                    c();
                }
                break;
            default:
                return;
        }
    retry:
        if (d) goto retry;";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn initializers_and_anonymous_types() {
        let body = "var o = new C {\nA = 1, B = 2,\nInner = { X = 3 } };\nvar list = new List<int> {\n1, 2,\n3 };\nvar a = new { Name = n,\nAge = 1 };\nint[] xs = { 1,\n2 };\nvar d = new Dictionary<int, string> {\n{ 1, \"one\" },\n[2] = \"two\" };";
        let expected = "        var o = new C
        {
            A = 1,
            B = 2,
            Inner = { X = 3 }
        };
        var list = new List<int>
        {
            1, 2,
            3
        };
        var a = new
        {
            Name = n,
            Age = 1
        };
        int[] xs =
        {
            1,
            2
        };
        var d = new Dictionary<int, string>
        {
            { 1, \"one\" },
            [2] = \"two\"
        };";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn lambdas_with_blocks_follow_their_line() {
        let body = "xs.ForEach(x => {\nuse(x);\n});\nTask.Run(\n    () => {\n        work();\n    });\nAction a = delegate {\nwork();\n};";
        let expected = "        xs.ForEach(x =>
        {
            use(x);
        });
        Task.Run(
            () =>
            {
                work();
            });
        Action a = delegate
        {
            work();
        };";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn switch_expressions() {
        let body = "var s = x switch {\n1 => \"one\",\n_ => \"many\",\n};";
        let expected = "        var s = x switch
        {
            1 => \"one\",
            _ => \"many\",
        };";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn wrapped_lines_keep_their_shape() {
        let text = "class C\n{\nvoid M()\n{\nvar x = Compute(first,\n                second)\n    .Where(y => y > 0)\n    .ToList();\nvar b = a &&\n    c;\n}\n}\n";
        let expected = "class C\n{\n    void M()\n    {\n        var x = Compute(first,\n                        second)\n            .Where(y => y > 0)\n            .ToList();\n        var b = a &&\n            c;\n    }\n}\n";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn members_accessors_and_attributes() {
        let text = "class C {
[Obsolete]
    [Serializable]
      public int P {
get {
return p;
}
  set => p = value;
}
public int Q => 1;
public event EventHandler E { add { } remove { } }
public int this [int i] => i;
public static C operator + (C a, C b) => a;
public static implicit operator int (C c) => 0;
~C () { }
public C () : this (1) { }
}
";
        let expected = "class C
{
    [Obsolete]
    [Serializable]
    public int P
    {
        get
        {
            return p;
        }
        set => p = value;
    }
    public int Q => 1;
    public event EventHandler E { add { } remove { } }
    public int this[int i] => i;
    public static C operator +(C a, C b) => a;
    public static implicit operator int(C c) => 0;
    ~C() { }
    public C() : this(1) { }
}
";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn records_enums_constraints_and_generics() {
        let text = "record R ( int X , string Y ) : B ( X ) ;
enum E : byte {
A = 1,
B,
}
interface I<in T> where T : new ( ) { T Get<U> ( U u ) where U : struct; }
";
        let expected = "record R(int X, string Y) : B(X);
enum E : byte
{
    A = 1,
    B,
}
interface I<in T> where T : new() { T Get<U>(U u) where U : struct; }
";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn local_functions_and_nested_blocks() {
        let body = "int Twice(int x) {\nreturn x * 2;\n}\n{\nvar scoped = 1;\n}\nchecked {\nx++;\n}\nunsafe {\n}";
        let expected = "        int Twice(int x)
        {
            return x * 2;
        }
        {
            var scoped = 1;
        }
        checked
        {
            x++;
        }
        unsafe
        {
        }";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn file_scoped_namespaces_and_top_level_code() {
        let text = "using System;\n  namespace N;\n  class C {\n  }\n";
        assert_eq!(format(text), "using System;\nnamespace N;\nclass C\n{\n}\n");
        let script = "  using System;\n   Console.WriteLine( 1 );\nif (x) {\n  y();\n}\n";
        assert_eq!(
            format(script),
            "using System;\nConsole.WriteLine(1);\nif (x)\n{\n    y();\n}\n"
        );
    }

    #[test]
    fn queries_put_each_clause_on_a_line() {
        let body = "var q = from x in xs where x > 1\n    orderby x select x;\nvar one = from y in ys select y;";
        let expected = "        var q = from x in xs
                where x > 1
                orderby x
                select x;
        var one = from y in ys select y;";
        assert_eq!(in_method(body), expected);
    }

    #[test]
    fn comments_blank_lines_and_trailing_whitespace() {
        let text = "class C   \n{\n  // leading comment\n      int x;    // trailing   comment\n\n\n  /* block\n     comment */\n        int y;/*inline*/int z;\n      /// <summary>doc</summary>\n  void M() {\n      a();\n          // before the brace\n  }\n}\n";
        let expected = "class C\n{\n    // leading comment\n    int x;    // trailing   comment\n\n\n    /* block\n     comment */\n    int y;/*inline*/int z;\n    /// <summary>doc</summary>\n    void M()\n    {\n        a();\n        // before the brace\n    }\n}\n";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn strings_are_never_touched() {
        let text = "class C\n{\nstring a = @\"  two\n   lines  \";\n  string b = \"\"\"\n      raw   text\n      \"\"\";\nstring c = $\"{ x  +  y }  and {z,3:F2}\";\nchar d = ' ';\n}\n";
        let expected = "class C\n{\n    string a = @\"  two\n   lines  \";\n    string b = \"\"\"\n      raw   text\n      \"\"\";\n    string c = $\"{ x  +  y }  and {z,3:F2}\";\n    char d = ' ';\n}\n";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn directives_and_disabled_text() {
        let text = "class C\n{\n    #if DEBUG\n       int   disabled  ;\n  #else\n  int live;\n    #endif\n  #region Fields\n  int x;\n      #endregion\n    #pragma warning disable CS0168\n}\n";
        let expected = "class C\n{\n#if DEBUG\n       int   disabled  ;\n#else\n    int live;\n#endif\n    #region Fields\n    int x;\n    #endregion\n#pragma warning disable CS0168\n}\n";
        assert_eq!(format(text), expected);
    }

    #[test]
    fn tabs_and_line_breaks_follow_the_options() {
        let options = FormatOptions::from_document(
            Indent {
                tabs: true,
                width: 4,
            },
            LineEnding::Crlf,
        );
        let text = "class C {\r\nvoid M() {\r\nx();\r\n}\r\n}\r\n";
        let edits = format_document(&parse(text), text, &options);
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\r\n{\r\n\tvoid M()\r\n\t{\r\n\t\tx();\r\n\t}\r\n}\r\n"
        );
    }

    #[test]
    fn edits_are_small_and_only_whitespace() {
        let text = "class C {\n  int x=1;\n}\n";
        let edits = format_document(&parse(text), text, &FormatOptions::default());
        assert!(edits.len() >= 3, "{edits:?}");
        for edit in &edits {
            let replaced = &text[edit.span.start() as usize..edit.span.end() as usize];
            assert!(replaced.trim().is_empty(), "replaced {replaced:?}");
            assert!(edit.text.trim().is_empty(), "inserted {:?}", edit.text);
        }
        assert!(
            format_document(
                &parse("class C { }\n"),
                "class C { }\n",
                &FormatOptions::default()
            )
            .is_empty()
        );
    }

    #[test]
    fn a_large_file_is_stable() {
        let mut text = String::new();
        for index in 0..40 {
            text.push_str(&format!(
                "namespace N{index} {{
using System;
/// <summary>Type {index}.</summary>
[Serializable]
public sealed class Thing{index}<T> : Base<T>, IDisposable where T : class, new() {{
private readonly List<T> items=new List<T>();
public int Count {{ get {{ return items.Count; }} }}
public T this[int i] {{ get => items[i]; set {{ items[i]=value; }} }}
public event EventHandler Changed;
public Thing{index}(IEnumerable<T> source) : base(source) {{
foreach(var item in source) {{
if(item==null) continue;
items.Add(item);
}}
}}
public IEnumerable<U> Map<U>(Func<T,U> f) {{
for(int i=0;i<items.Count;i++) yield return f(items[i]);
}}
public void Dispose() {{
try {{
Changed?.Invoke(this, EventArgs.Empty);
}} catch(InvalidOperationException e) when(e.Message!=null) {{
throw;
}} finally {{
items.Clear();
}}
var summary = items.Count switch {{
0 => \"none\",
1 => \"one\",
_ => $\"{{items.Count}} items\",
}};
var totals = items.Select(x => {{
return x.GetHashCode();
}}).Where(h => h > 0)
  .ToList();
#if TRACE
    Trace.WriteLine(summary);
#endif
}}
}}
}}
"
            ));
        }
        let once = format(&text);
        assert!(once.contains("    public sealed class Thing7<T> : Base<T>, IDisposable where T : class, new()\n    {\n"));
        assert!(once.contains("            foreach (var item in source)\n            {\n                if (item == null) continue;\n"));
        let twice = crate::edit::apply(
            &once,
            &format_document(&parse(&once), &once, &FormatOptions::default()),
        );
        assert_eq!(once, twice);
    }

    #[test]
    fn code_being_typed_formats_without_harm() {
        let broken = [
            "class C { void M() { if (x) { Foo(a, ",
            "class C {\nvoid M() {\nvar x = new List<int> {\n1,\n",
            "namespace N {\nclass C : {\nint P { get; set\n}\n",
            "class C { void M() { switch (x) { case 1: case",
            "class C { void M() { x = a ? : ; } }",
            "class C { int[] a = { 1, 2 ",
            "#if A\nclass C {\n#else\n}\n",
            "class C { string s = $\"{a +",
            "}}}{{{)))(((",
            "",
            "\n\n   \n",
        ];
        for text in broken {
            let edits = format_document(&parse(text), text, &FormatOptions::default());
            let formatted = crate::edit::apply(text, &edits);
            let squeeze = |text: &str| text.split_whitespace().collect::<String>();
            assert_eq!(squeeze(text), squeeze(&formatted), "formatting {text:?}");
            for position in 0..=text.len() as u32 {
                if !text.is_char_boundary(position as usize) {
                    continue;
                }
                let _ = indentation_for_new_line(
                    &parse(text),
                    text,
                    position,
                    &FormatOptions::default(),
                );
                for typed in [';', '}', '\n', '#'] {
                    let edits = format_on_type(
                        &parse(text),
                        text,
                        position,
                        typed,
                        &FormatOptions::default(),
                    );
                    let after = crate::edit::apply(text, &edits);
                    assert_eq!(
                        squeeze(text),
                        squeeze(&after),
                        "typing {typed:?} at {position} of {text:?}"
                    );
                }
            }
        }
    }

    // MARK: ranges and typing

    fn offset_of(text: &str, needle: &str) -> u32 {
        text.find(needle)
            .unwrap_or_else(|| panic!("no {needle:?} in {text:?}")) as u32
    }

    #[test]
    fn a_range_formats_only_its_lines() {
        let text = "class C\n{\n    void M()\n    {\n        int a=1;\n        int b=2;\n    int c=3;\n    }\n}\n";
        let start = offset_of(text, "int b");
        let edits = format_range(
            &parse(text),
            text,
            TextSpan::new(start, 3),
            &FormatOptions::default(),
        );
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    void M()\n    {\n        int a=1;\n        int b = 2;\n    int c=3;\n    }\n}\n"
        );
        // A range over the badly indented line moves it, and only it.
        let start = offset_of(text, "int c");
        let edits = format_range(
            &parse(text),
            text,
            TextSpan::at(start),
            &FormatOptions::default(),
        );
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    void M()\n    {\n        int a=1;\n        int b=2;\n        int c = 3;\n    }\n}\n"
        );
    }

    #[test]
    fn typing_a_semicolon_formats_the_statement() {
        let text =
            "class C\n{\n    void M()\n    {\n        int  y=2;\n            int x=1;\n    }\n}\n";
        let position = offset_of(text, "x=1;") + 4;
        let edits = format_on_type(&parse(text), text, position, ';', &FormatOptions::default());
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    void M()\n    {\n        int  y=2;\n        int x = 1;\n    }\n}\n"
        );
        // A semicolon inside a `for` header formats nothing.
        let text = "class C { void M() { for (int i=0;";
        let edits = format_on_type(
            &parse(text),
            text,
            text.len() as u32,
            ';',
            &FormatOptions::default(),
        );
        assert!(edits.is_empty(), "{edits:?}");
    }

    #[test]
    fn typing_a_close_brace_formats_the_construct() {
        let text = "class C\n{\n    int  y=2;\n    void M()\n    {\n        if(a){\n        b( );\n        }\n    }\n}\n";
        let position = offset_of(text, "}\n    }") + 1;
        let edits = format_on_type(&parse(text), text, position, '}', &FormatOptions::default());
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    int  y=2;\n    void M()\n    {\n        if (a)\n        {\n            b();\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn typing_enter_reindents_the_new_line() {
        let text = "class C\n{\n    void M()\n    {\n        a();\n}\n}\n";
        let position = offset_of(text, "a();\n") + 5;
        let edits = format_on_type(
            &parse(text),
            text,
            position,
            '\n',
            &FormatOptions::default(),
        );
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    void M()\n    {\n        a();\n    }\n}\n"
        );
        // A blank new line keeps the indentation the editor gave it.
        let text = "class C\n{\n    void M()\n    {\n        a();   \n        \n    }\n}\n";
        let position = offset_of(text, "a();   \n") + 8;
        let edits = format_on_type(
            &parse(text),
            text,
            position,
            '\n',
            &FormatOptions::default(),
        );
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    void M()\n    {\n        a();\n        \n    }\n}\n"
        );
    }

    #[test]
    fn typing_a_hash_places_the_directive() {
        let text = "class C\n{\n        #region A\n    int x;\n      #if B\n    #endregion\n}\n";
        let position = offset_of(text, "#region") + 1;
        let edits = format_on_type(&parse(text), text, position, '#', &FormatOptions::default());
        assert_eq!(
            crate::edit::apply(text, &edits),
            "class C\n{\n    #region A\n    int x;\n      #if B\n    #endregion\n}\n"
        );
        let position = offset_of(text, "#if") + 1;
        let edits = format_on_type(&parse(text), text, position, '#', &FormatOptions::default());
        assert!(crate::edit::apply(text, &edits).contains("\n#if B\n"));
        assert!(format_on_type(&parse(text), text, 3, 'x', &FormatOptions::default()).is_empty());
    }

    // MARK: smart indentation

    /// The indentation after pressing Enter where `|` is.
    fn smart(marked: &str) -> Option<String> {
        let offset = offset_of(marked, "|");
        let text = marked.replace('|', "");
        indentation_for_new_line(&parse(&text), &text, offset, &FormatOptions::default())
    }

    #[test]
    fn smart_indent_inside_blocks_and_after_statements() {
        assert_eq!(smart("class C\n{|\n}").as_deref(), Some("    "));
        assert_eq!(smart("class C {|}").as_deref(), Some(""));
        assert_eq!(
            smart("class C\n{\n    void M()\n    {|\n    }\n}").as_deref(),
            Some("        ")
        );
        assert_eq!(
            smart("class C\n{\n    void M()\n    {\n        a();|\n    }\n}").as_deref(),
            Some("        ")
        );
        assert_eq!(
            smart("class C\n{\n    void M()\n    {\n    }|\n}").as_deref(),
            Some("    ")
        );
        assert_eq!(smart("class C\n{\n    int x;|\n}").as_deref(), Some("    "));
        assert_eq!(smart("|class C { }").as_deref(), Some(""));
    }

    #[test]
    fn smart_indent_for_embedded_statements_and_labels() {
        let method = |body: &str| format!("class C\n{{\n    void M()\n    {{\n{body}\n    }}\n}}");
        assert_eq!(
            smart(&method("        if (a)|")).as_deref(),
            Some("            ")
        );
        assert_eq!(
            smart(&method("        else|")).as_deref(),
            Some("            ")
        );
        assert_eq!(
            smart(&method("        if (a)\n            b();|")).as_deref(),
            Some("        ")
        );
        assert_eq!(
            smart(&method(
                "        switch (a)\n        {\n            case 1:|\n        }"
            ))
            .as_deref(),
            Some("                ")
        );
        assert_eq!(
            smart(&method(
                "        switch (a)\n        {\n            case 1: b();|\n        }"
            ))
            .as_deref(),
            Some("                ")
        );
    }

    #[test]
    fn smart_indent_in_argument_lists_and_expressions() {
        let method = |body: &str| format!("class C\n{{\n    void M()\n    {{\n{body}\n    }}\n}}");
        // Lined up with the first argument, twelve columns in.
        assert_eq!(
            smart(&method("        Foo(first,|")).as_deref(),
            Some("            ")
        );
        assert_eq!(
            smart(&method("        Foo(first, second,|")).as_deref(),
            Some("            ")
        );
        assert_eq!(
            smart(&method("        Foo(\n            first,|")).as_deref(),
            Some("            ")
        );
        assert_eq!(
            smart(&method("        Foo(|")).as_deref(),
            Some("            ")
        );
        assert_eq!(
            smart(&method("        var x = a +|")).as_deref(),
            Some("            ")
        );
        assert_eq!(smart(&method("        var s = @\"one|\";")), None);
    }

    #[test]
    fn smart_indent_in_comments() {
        assert_eq!(
            smart("class C\n{\n    /// <summary>|\n    void M() { }\n}").as_deref(),
            Some("    ")
        );
        assert_eq!(
            smart("class C\n{\n      /* one|\n    */\n}").as_deref(),
            Some("      ")
        );
    }

    // MARK: - .editorconfig options

    /// `text` formatted with `style` changed by `change`, checked to be
    /// whitespace-only and stable like [`format`].
    fn format_with(text: &str, change: impl Fn(&mut FormatOptions)) -> String {
        let mut options = FormatOptions::default();
        change(&mut options);
        let edits = format_document(&parse(text), text, &options);
        let formatted = crate::edit::apply(text, &edits);
        let squeeze = |text: &str| text.split_whitespace().collect::<String>();
        assert_eq!(
            squeeze(text),
            squeeze(&formatted),
            "only whitespace may change"
        );
        let again = format_document(&parse(&formatted), &formatted, &options);
        assert!(
            again.is_empty(),
            "formatting is not stable:\n{formatted}\nthen:\n{}",
            crate::edit::apply(&formatted, &again)
        );
        formatted
    }

    #[test]
    fn braces_stay_on_their_line_when_the_options_say() {
        let text = "class C\n{\n    void M()\n    {\n        if (a)\n        {\n            b();\n        }\n        else\n        {\n            c();\n        }\n        try\n        {\n        }\n        catch\n        {\n        }\n    }\n}\n";
        let formatted = format_with(text, |options| {
            options.style.new_line_before_open_brace = BraceNewLines::parse("types");
            options.style.new_line_before_else = false;
            options.style.new_line_before_catch = false;
        });
        assert_eq!(
            formatted,
            "class C\n{\n    void M() {\n        if (a) {\n            b();\n        } else {\n            c();\n        }\n        try {\n        } catch {\n        }\n    }\n}\n"
        );
        // And K&R code goes back to Allman under the defaults.
        assert_eq!(format(&formatted), text);
    }

    #[test]
    fn switch_indentation_follows_the_options() {
        let text = "class C\n{\n    void M(int x)\n    {\n        switch (x)\n        {\n            case 1:\n                a();\n                break;\n        }\n    }\n}\n";
        let flat = format_with(text, |options| {
            options.style.indent_switch_labels = false;
            options.style.indent_case_contents = false;
        });
        assert!(
            flat.contains("        {\n        case 1:\n        a();\n        break;\n        }"),
            "{flat}"
        );
        let labels_only = format_with(text, |options| options.style.indent_case_contents = false);
        assert!(
            labels_only.contains("            case 1:\n            a();"),
            "{labels_only}"
        );
    }

    #[test]
    fn spacing_follows_the_options() {
        let text = "class C : B\n{\n    void M(int a, int b)\n    {\n        if (a == b) M((int)a, b);\n    }\n}\n";
        let formatted = format_with(text, |options| {
            let style = &mut options.style;
            style.space_after_cast = true;
            style.space_after_control_flow_keywords = false;
            style.space_within_call_parentheses = true;
            style.space_before_declaration_parenthesis = true;
            style.space_around_binary_operators = SpaceAroundOperators::None;
            style.space_before_inheritance_colon = false;
        });
        assert_eq!(
            formatted,
            "class C: B\n{\n    void M (int a, int b)\n    {\n        if(a==b) M( (int) a, b );\n    }\n}\n"
        );
    }

    #[test]
    fn single_line_blocks_and_statements_can_be_unfolded() {
        let text = "class C\n{\n    int P { get; set; }\n    void M() { a(); b(); }\n}\n";
        let formatted = format_with(text, |options| {
            options.style.preserve_single_line_blocks = false;
            options.style.preserve_single_line_statements = false;
        });
        assert_eq!(
            formatted,
            "class C\n{\n    int P\n    {\n        get; set;\n    }\n    void M()\n    {\n        a();\n        b();\n    }\n}\n"
        );
    }

    #[test]
    fn the_final_line_break_is_added_or_taken_away() {
        let text = "class C { }";
        let added = format_with(text, |options| options.insert_final_newline = Some(true));
        assert_eq!(added, "class C { }\n");
        let removed = format_with("class C { }\n\n", |options| {
            options.insert_final_newline = Some(false);
        });
        assert_eq!(removed, "class C { }");
        assert_eq!(format_with(text, |_| {}), text);
    }

    #[test]
    fn typing_an_open_brace_formats_the_construct() {
        let text = "class C\n{\n    void M()\n    {\n          if(a) {\n    }\n}\n";
        let position = offset_of(text, "{\n    }\n}") + 1;
        let edits = format_on_type(&parse(text), text, position, '{', &FormatOptions::default());
        let typed = crate::edit::apply(text, &edits);
        assert!(typed.contains("        if (a)\n        {"), "{typed}");
    }
}
