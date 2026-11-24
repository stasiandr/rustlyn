//! Block structure: what an editor can fold, and the guides it draws down
//! the side of each block. Roslyn's `BlockStructureService`, from the parse
//! alone.
//!
//! Every construct that spans lines gives one [`FoldingRange`]. The span to
//! fold starts at the end of the construct's header — after the `)` of a
//! method or an `if`, after the name of a class — so that the header stays
//! on screen, and runs to the closing brace. The hint span is the whole
//! construct, for the tooltip over a folded block; the banner is what stands
//! in for the folded text.
//!
//! Beyond the braces, the same trivia Roslyn looks at: runs of `//`
//! comments, `/* */` comments over several lines, `///` documentation,
//! `#region`, text an `#if` switched off, and strings over several lines.
//!
//! Deviations: only constructs that span lines are reported, since nothing
//! folds a single line; the group of `using` directives folds from after
//! its first `using`, so what stays on screen reads `using ...`; and a
//! lambda's block folds to its `}`, without the `)` or `;` after it.

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken, SyntaxTrivia};
use rustlyn_text::{LineIndex, TextSpan};

use crate::format::{braces, is_initializer, is_type_declaration, start_after_attributes};

/// What sort of thing a block is, as Roslyn's `BlockTypes` name them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FoldKind {
    /// The `using` directives at the top of a file or namespace.
    Imports = 0,
    Namespace,
    Type,
    /// Methods, constructors, properties, accessors, operators, events,
    /// local functions.
    Member,
    /// `using`, `lock`, `try`, `catch`, `finally`, `fixed`, `unsafe`,
    /// `checked`, a bare block, a switch section.
    Statement,
    /// `if`, `else`, `switch`.
    Conditional,
    /// `for`, `foreach`, `while`, `do`.
    Loop,
    /// Lambdas, anonymous methods, initializers, switch expressions, strings.
    Expression,
    Comment,
    /// `#region` to `#endregion`.
    Region,
    /// Text an `#if` switched off.
    Nonstructural,
}

/// One foldable block. Spans are byte offsets of the text asked about.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldingRange {
    /// What folds away.
    pub span: TextSpan,
    /// The whole construct, for a tooltip over the folded block.
    pub hint: TextSpan,
    /// What stands in for the folded text.
    pub banner: String,
    pub kind: FoldKind,
    /// Whether the editor may fold it. Every block reported spans lines, so
    /// this is always true today; a guide that cannot fold would say false.
    pub collapsible: bool,
    /// Whether it starts folded when the file opens: regions, and the
    /// `using` directives when the options say so.
    pub collapsed_by_default: bool,
}

/// Roslyn's outlining options.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StructureOptions {
    /// Fold the `using` directives when a file opens. Off by default.
    pub collapse_imports: bool,
    /// Fold `#region` blocks when a file opens. On by default.
    pub collapse_regions: bool,
}

impl Default for StructureOptions {
    fn default() -> Self {
        Self {
            collapse_imports: false,
            collapse_regions: true,
        }
    }
}

const ELLIPSIS: &str = "...";

/// Every foldable block of a file, in order of where it starts.
#[must_use]
pub fn block_structure(
    root: &SyntaxNode,
    text: &str,
    options: StructureOptions,
) -> Vec<FoldingRange> {
    let mut collector = Collector {
        lines: LineIndex::new(text),
        tokens: root
            .descendant_tokens()
            .filter(|token| !token.span().is_empty())
            .collect(),
        options,
        found: Vec::new(),
    };
    for node in root.descendants() {
        collector.node(&node);
    }
    collector.trivia(root);
    let mut found = collector.found;
    found.sort_by_key(|range| (range.span.start(), std::cmp::Reverse(range.span.end())));
    found.dedup_by(|one, other| one.span == other.span);
    found
}

struct Collector {
    lines: LineIndex,
    tokens: Vec<SyntaxToken>,
    options: StructureOptions,
    found: Vec<FoldingRange>,
}

impl Collector {
    /// Adds a block, if it spans lines.
    fn push(&mut self, span: TextSpan, hint: TextSpan, banner: String, kind: FoldKind) {
        if span.is_empty() || self.lines.line_of(span.start()) == self.lines.line_of(span.end()) {
            return;
        }
        let collapsed_by_default = match kind {
            FoldKind::Region => self.options.collapse_regions,
            FoldKind::Imports => self.options.collapse_imports,
            _ => false,
        };
        self.found.push(FoldingRange {
            span,
            hint,
            banner,
            kind,
            collapsible: true,
            collapsed_by_default,
        });
    }

    /// The end of the last token before `offset`: where a header ends.
    fn header_end(&self, offset: u32) -> u32 {
        let index = self
            .tokens
            .partition_point(|token| token.span().end() <= offset);
        index
            .checked_sub(1)
            .map_or(offset, |previous| self.tokens[previous].span().end())
    }

    /// A construct folded from the end of its header to its closing brace.
    fn braced(&mut self, container: &SyntaxNode, owner: &SyntaxNode, kind: FoldKind) {
        let Some((open, close)) = braces(container) else {
            return;
        };
        let start = self.header_end(open);
        let hint = TextSpan::from_bounds(start_after_attributes(owner).min(close), close);
        self.push(
            TextSpan::from_bounds(start.min(close), close),
            hint,
            ELLIPSIS.to_owned(),
            kind,
        );
    }

    fn node(&mut self, node: &SyntaxNode) {
        let kind = node.kind();
        match kind {
            K::CompilationUnit | K::NamespaceDeclaration | K::FileScopedNamespaceDeclaration => {
                self.imports(node);
                if kind == K::NamespaceDeclaration {
                    self.braced(node, node, FoldKind::Namespace);
                }
            }
            _ if is_type_declaration(kind) || kind == K::ExtensionBlockDeclaration => {
                self.braced(node, node, FoldKind::Type);
            }
            K::Block => self.block(node),
            K::AccessorList => {
                if let Some(owner) = node.parent().cloned() {
                    self.braced(node, &owner, FoldKind::Member);
                }
            }
            K::ArrowExpressionClause => {
                // An expression body over several lines folds from the
                // arrow to the end of the member.
                if let Some(owner) = node.parent().cloned()
                    && let Some(arrow) = node.first_token()
                {
                    let start = self.header_end(arrow.span().start());
                    let end = owner.span().end();
                    self.push(
                        TextSpan::from_bounds(start, end),
                        TextSpan::from_bounds(start_after_attributes(&owner), end),
                        ELLIPSIS.to_owned(),
                        if owner.kind().is_declaration_node()
                            || owner.kind() == K::LocalFunctionStatement
                        {
                            FoldKind::Member
                        } else {
                            FoldKind::Expression
                        },
                    );
                }
            }
            K::SwitchStatement => self.braced(node, node, FoldKind::Conditional),
            K::SwitchSection => {
                let last_label = node
                    .children()
                    .filter(|child| {
                        matches!(
                            child.kind(),
                            K::CaseSwitchLabel | K::CasePatternSwitchLabel | K::DefaultSwitchLabel
                        )
                    })
                    .last();
                if let Some(label) = last_label {
                    let start = label.span().end();
                    self.push(
                        TextSpan::from_bounds(start, node.span().end()),
                        node.span(),
                        ELLIPSIS.to_owned(),
                        FoldKind::Statement,
                    );
                }
            }
            K::SwitchExpression | K::AnonymousObjectCreationExpression => {
                self.braced(node, node, FoldKind::Expression);
            }
            _ if is_initializer(kind) => {
                let owner = node
                    .parent()
                    .filter(|parent| !is_initializer(parent.kind()))
                    .cloned()
                    .unwrap_or_else(|| node.clone());
                if owner == *node {
                    self.push(
                        node.span(),
                        node.span(),
                        ELLIPSIS.to_owned(),
                        FoldKind::Expression,
                    );
                } else {
                    self.braced(node, &owner, FoldKind::Expression);
                }
            }
            K::StringLiteralExpression
            | K::InterpolatedStringExpression
            | K::Utf8StringLiteralExpression => {
                self.push(
                    node.span(),
                    node.span(),
                    ELLIPSIS.to_owned(),
                    FoldKind::Expression,
                );
            }
            _ => {}
        }
    }

    fn block(&mut self, block: &SyntaxNode) {
        let Some(parent) = block.parent().cloned() else {
            return;
        };
        let kind = match parent.kind() {
            K::Block | K::SwitchSection | K::GlobalStatement | K::LabeledStatement => {
                self.push(
                    block.span(),
                    block.span(),
                    ELLIPSIS.to_owned(),
                    FoldKind::Statement,
                );
                return;
            }
            K::IfStatement | K::ElseClause | K::SwitchStatement => FoldKind::Conditional,
            K::ForStatement
            | K::ForEachStatement
            | K::ForEachVariableStatement
            | K::WhileStatement
            | K::DoStatement => FoldKind::Loop,
            K::ParenthesizedLambdaExpression
            | K::SimpleLambdaExpression
            | K::AnonymousMethodExpression => FoldKind::Expression,
            kind if kind.is_declaration_node() || kind == K::LocalFunctionStatement => {
                FoldKind::Member
            }
            _ => FoldKind::Statement,
        };
        self.braced(block, &parent, kind);
    }

    /// The `using` directives of a file or namespace, as one block.
    fn imports(&mut self, container: &SyntaxNode) {
        let directives: Vec<SyntaxNode> = container
            .children()
            .filter(|child| matches!(child.kind(), K::UsingDirective | K::ExternAliasDirective))
            .collect();
        let (Some(first), Some(last)) = (directives.first(), directives.last()) else {
            return;
        };
        let start = first
            .first_token()
            .map_or(first.span().start(), |token| token.span().end());
        let end = last.span().end();
        self.push(
            TextSpan::from_bounds(start, end),
            TextSpan::from_bounds(first.span().start(), end),
            ELLIPSIS.to_owned(),
            FoldKind::Imports,
        );
    }

    // MARK: trivia

    fn trivia(&mut self, root: &SyntaxNode) {
        let mut all: Vec<SyntaxTrivia> = Vec::new();
        for token in root.descendant_tokens() {
            all.extend(token.leading_trivia());
            all.extend(token.trailing_trivia());
        }
        let mut regions: Vec<SyntaxTrivia> = Vec::new();
        let mut index = 0;
        while index < all.len() {
            let trivia = &all[index];
            match trivia.kind() {
                K::SingleLineCommentTrivia | K::SingleLineDocumentationCommentTrivia => {
                    let kind = trivia.kind();
                    let run = run_of(&all, index, kind);
                    let (first, last) = (&all[index], &all[run[run.len() - 1]]);
                    let span = TextSpan::from_bounds(first.span().start(), last.span().end());
                    let banner = if kind == K::SingleLineCommentTrivia {
                        comment_banner(first.text())
                    } else {
                        let lines: Vec<&str> = run.iter().map(|&at| all[at].text()).collect();
                        documentation_banner(&lines)
                    };
                    self.push(span, span, banner, FoldKind::Comment);
                    index = run[run.len() - 1] + 1;
                    continue;
                }
                K::MultiLineCommentTrivia | K::MultiLineDocumentationCommentTrivia => {
                    let span = trivia.span();
                    let banner = block_comment_banner(trivia.text());
                    self.push(span, span, banner, FoldKind::Comment);
                }
                K::RegionDirectiveTrivia => regions.push(trivia.clone()),
                K::EndRegionDirectiveTrivia => {
                    if let Some(start) = regions.pop() {
                        let span = TextSpan::from_bounds(start.span().start(), trivia.span().end());
                        let name = start
                            .text()
                            .trim_start_matches('#')
                            .trim_start()
                            .trim_start_matches("region")
                            .trim();
                        let banner = if name.is_empty() { "#region" } else { name };
                        self.push(span, span, banner.to_owned(), FoldKind::Region);
                    }
                }
                K::DisabledTextTrivia => {
                    let text = trivia.text();
                    let trimmed = text.trim_end_matches(['\n', '\r']);
                    let span = TextSpan::new(trivia.span().start(), trimmed.len() as u32);
                    self.push(span, span, ELLIPSIS.to_owned(), FoldKind::Nonstructural);
                }
                _ => {}
            }
            index += 1;
        }
    }
}

/// The indices of a run of line comments of one kind starting at `start`:
/// each on the line after the last, with nothing but whitespace between.
fn run_of(all: &[SyntaxTrivia], start: usize, kind: K) -> Vec<usize> {
    let mut run = vec![start];
    let mut index = start + 1;
    let mut breaks = 0;
    while index < all.len() {
        match all[index].kind() {
            K::WhitespaceTrivia => {}
            K::EndOfLineTrivia => {
                breaks += 1;
                if breaks > 1 {
                    break;
                }
            }
            found if found == kind && breaks == 1 => {
                run.push(index);
                breaks = 0;
            }
            _ => break,
        }
        index += 1;
    }
    run
}

/// `// first line ...`, Roslyn's banner for a run of line comments.
fn comment_banner(first: &str) -> String {
    format!("// {} {ELLIPSIS}", first.trim_start_matches('/').trim())
}

/// `/* first line ... */`.
fn block_comment_banner(text: &str) -> String {
    let (open, close) = if text.starts_with("/**") {
        ("/**", "*/")
    } else {
        ("/*", "*/")
    };
    let inner = text
        .trim_start_matches(open)
        .trim_end_matches(close)
        .lines()
        .map(|line| line.trim().trim_start_matches('*').trim())
        .find(|line| !line.is_empty())
        .unwrap_or_default();
    if inner.is_empty() {
        format!("{open} {ELLIPSIS} {close}")
    } else {
        format!("{open} {inner} {ELLIPSIS} {close}")
    }
}

/// `/// <summary> The first line of the summary ...`: what Roslyn shows for
/// folded documentation.
fn documentation_banner(lines: &[&str]) -> String {
    let body: Vec<&str> = lines
        .iter()
        .map(|line| line.trim_start_matches('/').trim())
        .collect();
    let joined = body.join("\n");
    if let Some(start) = joined.find("<summary>") {
        let after = &joined[start + "<summary>".len()..];
        let text = after
            .split("</summary>")
            .next()
            .unwrap_or_default()
            .lines()
            .map(str::trim)
            .find(|line| !line.is_empty());
        return match text {
            Some(text) => format!("/// <summary> {text} {ELLIPSIS}"),
            None => format!("/// <summary> {ELLIPSIS}"),
        };
    }
    let first = body
        .iter()
        .find(|line| !line.is_empty())
        .copied()
        .unwrap_or_default();
    format!("/// {first} {ELLIPSIS}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_text::SourceText;

    const FILE: &str = r#"using System;
using System.Collections.Generic;
using System.Linq;

namespace Game
{
    // A run of comments
    // over two lines.
    /// <summary>
    /// A pawn on the board.
    /// </summary>
    public class Pawn : IDisposable
    {
        #region Fields
        private int health;
        private readonly List<int> moves = new List<int>
        {
            1, 2,
        };
        #endregion

        public int Health
        {
            get { return health; }
            set
            {
                health = value;
            }
        }

        public Pawn(int health)
        {
            this.health = health;
        }

        public int Twice(int x) =>
            x * 2;

        public void Move(int steps)
        {
            if (steps > 0)
            {
                Step();
            }
            else
            {
                Stay();
            }
            for (var i = 0; i < steps; i++)
            {
                Step();
            }
            try
            {
                Step();
            }
            catch (Exception)
            {
            }
            switch (steps)
            {
                case 1:
                    Step();
                    break;
            }
            moves.ForEach(m =>
            {
                Step();
            });
            var name = steps switch
            {
                1 => "one",
                _ => "many",
            };
            var text = @"first
second";
            /* a block
               comment */
#if NEVER
            Step();
            Step();
#endif
            void Local()
            {
            }
        }

        public void Dispose() { }
    }

    enum Color
    {
        Red,
        Green,
    }
}
"#;

    fn structure(text: &str) -> Vec<FoldingRange> {
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", text)).root();
        block_structure(&root, text, StructureOptions::default())
    }

    /// The fold that starts right after `header`.
    fn fold<'a>(found: &'a [FoldingRange], text: &str, header: &str) -> &'a FoldingRange {
        let at = text.find(header).unwrap_or_else(|| panic!("no {header:?}")) as u32
            + header.len() as u32;
        found
            .iter()
            .find(|range| range.span.start() == at)
            .unwrap_or_else(|| panic!("nothing folds after {header:?}: {found:#?}"))
    }

    fn folded<'a>(text: &'a str, range: &FoldingRange) -> &'a str {
        &text[range.span.start() as usize..range.span.end() as usize]
    }

    #[test]
    fn declarations_fold_from_the_end_of_their_header() {
        let found = structure(FILE);
        let namespace = fold(&found, FILE, "namespace Game");
        assert_eq!(namespace.kind, FoldKind::Namespace);
        assert!(folded(FILE, namespace).ends_with("}\n}"));
        let class = fold(&found, FILE, "class Pawn : IDisposable");
        assert_eq!(class.kind, FoldKind::Type);
        assert_eq!(class.banner, "...");
        assert!(FILE[class.hint.start() as usize..].starts_with("public class Pawn"));
        assert_eq!(
            fold(&found, FILE, "public int Health").kind,
            FoldKind::Member
        );
        assert_eq!(fold(&found, FILE, "            set").kind, FoldKind::Member);
        assert_eq!(
            fold(&found, FILE, "public Pawn(int health)").kind,
            FoldKind::Member
        );
        assert_eq!(
            fold(&found, FILE, "public void Move(int steps)").kind,
            FoldKind::Member
        );
        assert_eq!(
            fold(&found, FILE, "public int Twice(int x)").kind,
            FoldKind::Member
        );
        assert_eq!(fold(&found, FILE, "void Local()").kind, FoldKind::Member);
        assert_eq!(fold(&found, FILE, "enum Color").kind, FoldKind::Type);
        // What fits on one line has nothing to fold.
        let dispose = FILE.find("Dispose() { }").unwrap_or_default() as u32;
        let getter = FILE.find("get { return").unwrap_or_default() as u32;
        assert!(!found.iter().any(|range| range.span.start() > dispose
            && range.span.start() < dispose + 20
            || range.span.start() > getter && range.span.start() < getter + 20));
    }

    #[test]
    fn statements_fold_by_kind() {
        let found = structure(FILE);
        assert_eq!(
            fold(&found, FILE, "if (steps > 0)").kind,
            FoldKind::Conditional
        );
        assert_eq!(
            fold(&found, FILE, "            else").kind,
            FoldKind::Conditional
        );
        assert_eq!(
            fold(&found, FILE, "for (var i = 0; i < steps; i++)").kind,
            FoldKind::Loop
        );
        assert_eq!(
            fold(&found, FILE, "            try").kind,
            FoldKind::Statement
        );
        assert_eq!(
            fold(&found, FILE, "catch (Exception)").kind,
            FoldKind::Statement
        );
        assert_eq!(
            fold(&found, FILE, "switch (steps)").kind,
            FoldKind::Conditional
        );
        assert_eq!(fold(&found, FILE, "case 1:").kind, FoldKind::Statement);
        let lambda = fold(&found, FILE, "moves.ForEach(m =>");
        assert_eq!(lambda.kind, FoldKind::Expression);
        assert!(folded(FILE, lambda).ends_with('}'));
        assert_eq!(
            fold(&found, FILE, "var name = steps switch").kind,
            FoldKind::Expression
        );
        assert_eq!(
            fold(&found, FILE, "new List<int>").kind,
            FoldKind::Expression
        );
    }

    #[test]
    fn trivia_folds() {
        let found = structure(FILE);
        let usings = fold(&found, FILE, "using");
        assert_eq!(usings.kind, FoldKind::Imports);
        assert!(!usings.collapsed_by_default);
        assert!(folded(FILE, usings).ends_with("System.Linq;"));

        let region = found
            .iter()
            .find(|range| range.kind == FoldKind::Region)
            .expect("a region");
        assert_eq!(region.banner, "Fields");
        assert!(region.collapsed_by_default);
        assert!(folded(FILE, region).starts_with("#region Fields"));
        assert!(folded(FILE, region).ends_with("#endregion"));

        let banners: Vec<&str> = found
            .iter()
            .filter(|range| range.kind == FoldKind::Comment)
            .map(|range| range.banner.as_str())
            .collect();
        assert_eq!(
            banners,
            [
                "// A run of comments ...",
                "/// <summary> A pawn on the board. ...",
                "/* a block ... */"
            ]
        );
        let disabled = found
            .iter()
            .find(|range| range.kind == FoldKind::Nonstructural)
            .expect("disabled text");
        assert_eq!(
            folded(FILE, disabled).trim(),
            "Step();\n            Step();"
        );
        let string = found
            .iter()
            .find(|range| folded(FILE, range).starts_with("@\"first"))
            .expect("the verbatim string");
        assert_eq!(string.kind, FoldKind::Expression);
    }

    #[test]
    fn options_decide_what_starts_folded() {
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", FILE)).root();
        let found = block_structure(
            &root,
            FILE,
            StructureOptions {
                collapse_imports: true,
                collapse_regions: false,
            },
        );
        for range in &found {
            assert_eq!(
                range.collapsed_by_default,
                range.kind == FoldKind::Imports,
                "{range:?}"
            );
            assert!(range.collapsible);
        }
    }

    #[test]
    fn single_lines_and_lone_comments_do_not_fold() {
        let text = "using System;\n// one\n\n// two\nclass C { void M() { } }\n";
        assert!(structure(text).is_empty(), "{:#?}", structure(text));
    }
}
