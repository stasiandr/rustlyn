//! The IDE's own analyzers: what Roslyn reports beyond what the compiler
//! does, most of it code that can go.
//!
//! The compiler says what is wrong. The editor also says what is pointless:
//! a private method nobody calls, a value assigned and never read, a
//! parameter nobody uses, a cast to the type the value already has, a
//! qualification the name does not need, code after a `return`. Roslyn
//! reports these under `IDE` ids at a severity that does not squiggle —
//! hidden or a suggestion — and tags most of them *unnecessary*, which is
//! what makes an editor draw the code faded rather than underlined.
//!
//! The analyzers, each in the module named for what it looks at:
//!
//! * [`members`]: IDE0051 unused private member, IDE0052 private member
//!   written but never read, IDE0044 field that could be `readonly`,
//!   IDE0060 unused parameter, and CS0612/CS0618/CS0619 for uses of what
//!   is marked `[Obsolete]`, which the binder does not report.
//! * [`flow`]: IDE0059 value assigned and never read, CS0168 local declared
//!   and never used, CS0219 local given a constant and never read, and
//!   CS0162/IDE0035 unreachable code — again, not reported by the binder.
//! * [`style`]: IDE0001/IDE0002 name or member access that can be
//!   simplified, IDE0049 framework type name where a keyword is preferred,
//!   IDE0003 `this.` that is not needed, IDE0004 cast that is not needed.
//! * [`threads`]: RLN1001 a field two threads touch with no lock between
//!   them, RLN1002 Unity's main-thread API reached from a background
//!   thread, RLN1003 a local every iteration of `Parallel.For` writes.
//! * IDE0005, a `using` directive nothing needs, from
//!   [`usings`](super::usings).
//!
//! They run separately from [`Semantic::diagnostics`], which stays what the
//! compiler says, and they skip a body the binder could not make sense of:
//! with an error in it, "unused" is as likely to mean "misspelled".

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;

use rustlyn_diagnostics::Severity;
use rustlyn_semantics::{BoundBody, SymbolId, is_body_owner};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::references::declares;
use super::{Resolved, Semantic, View};

mod flow;
mod members;
mod style;
mod threads;

/// Something an IDE analyzer found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalyzerDiagnostic {
    /// `IDE0051`, or the compiler's `CS0168` where Roslyn's compiler would
    /// have said it.
    pub id: &'static str,
    /// Roslyn's default: hidden for what only fades, info (a suggestion)
    /// for what is worth a look, warning for what the compiler warns about.
    pub severity: Severity,
    /// In bytes of the text asked about: the part that is unnecessary, where
    /// the diagnostic is one of those.
    pub span: TextSpan,
    pub message: String,
    /// The code can go: an editor draws it faded.
    pub unnecessary: bool,
    /// A use of something marked obsolete: an editor strikes it through.
    pub deprecated: bool,
}

impl AnalyzerDiagnostic {
    fn new(
        id: &'static str,
        severity: Severity,
        span: TextSpan,
        message: impl Into<String>,
    ) -> Self {
        Self {
            id,
            severity,
            span,
            message: message.into(),
            unnecessary: false,
            deprecated: false,
        }
    }

    const fn unnecessary(mut self) -> Self {
        self.unnecessary = true;
        self
    }

    const fn deprecated(mut self) -> Self {
        self.deprecated = true;
        self
    }
}

impl Semantic {
    /// What the IDE analyzers find in `path` as it reads now. Sorted by
    /// place.
    #[must_use]
    pub fn analyzer_diagnostics(
        &self,
        path: &Path,
        text: Option<&str>,
    ) -> Option<Vec<AnalyzerDiagnostic>> {
        // The analyzers walk the tree and the bound bodies, as deep as they
        // go: on a stack made for it, where the caller's may not be.
        rustlyn_semantics::parallel::deep(|| self.analyzer_diagnostics_here(path, text))
    }

    fn analyzer_diagnostics_here(
        &self,
        path: &Path,
        text: Option<&str>,
    ) -> Option<Vec<AnalyzerDiagnostic>> {
        let tree = self.tree_index(path)?;
        let mut view = self.view_of(path, text)?;
        let mut found = view.analyze();
        // What the analyzers report under a compiler's code is the
        // compiler's warning, and off where the project turned it off.
        found.retain(|item| {
            item.severity != Severity::Warning
                || item
                    .id
                    .strip_prefix("CS")
                    .and_then(|code| code.parse().ok())
                    .is_none_or(|code| self.reports_warning(tree, code))
        });
        Some(found)
    }
}

/// One analyzer: what it reads is the file and what [`Facts`] gathered
/// about it once for all of them.
type Analyzer = fn(&mut View<'_>, &Facts, &mut Vec<AnalyzerDiagnostic>);

/// Every analyzer, in the order they run.
const ANALYZERS: &[Analyzer] = &[
    members::unused_members,
    members::readonly_fields,
    members::unused_parameters,
    members::obsolete_uses,
    flow::unused_values,
    flow::unreachable_code,
    style::simplify_names,
    style::this_qualification,
    style::unnecessary_casts,
    unnecessary_usings,
    threads::threads,
];

/// IDE0005: `using` directives nothing in the file needs, as
/// [`usings`](super::usings) works them out. Removing them is the light
/// bulb's "Remove unnecessary usings", which the refactorings offer.
fn unnecessary_usings(view: &mut View<'_>, _: &Facts, found: &mut Vec<AnalyzerDiagnostic>) {
    for span in super::usings::unnecessary_usings(view) {
        found.push(
            AnalyzerDiagnostic::new(
                "IDE0005",
                Severity::Hidden,
                span,
                "Using directive is unnecessary.",
            )
            .unnecessary(),
        );
    }
}

impl View<'_> {
    /// Runs every analyzer over the file.
    pub(super) fn analyze(&mut self) -> Vec<AnalyzerDiagnostic> {
        let facts = Facts::gather(self);
        let mut found = Vec::new();
        for analyzer in ANALYZERS {
            analyzer(self, &facts, &mut found);
        }
        found.sort_by_key(|diagnostic| (diagnostic.span.start(), diagnostic.span.end()));
        found.dedup_by(|a, b| a.span == b.span && a.id == b.id);
        found
    }
}

/// A body of the file, bound.
struct Body {
    owner: SyntaxNode,
    bound: Arc<BoundBody>,
    /// Whether binding it reported an error, or its syntax is broken: the
    /// analyzers that reason about what is used leave such a body alone.
    broken: bool,
}

/// How a name is used where it is written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Access {
    Read,
    /// Assigned, passed as `out`, or changed by `+=` or `++` whose value
    /// nothing reads: the old value does not matter to anyone.
    Write,
    /// Read and written: `ref`, or `x++` inside an expression.
    ReadWrite,
}

/// One use of a symbol.
#[derive(Clone, Debug)]
struct Use {
    token: SyntaxToken,
    access: Access,
}

/// What every analyzer wants to know about the file, gathered once: its
/// bodies, bound, and every name in it resolved.
struct Facts {
    bodies: Vec<Body>,
    /// Each symbol the file uses, with where and how. Declarations are not
    /// uses.
    uses: HashMap<SymbolId, Vec<Use>>,
    /// Names that resolved to nothing. A member with a name among these
    /// might be what was meant, so is not called unused.
    unresolved: HashSet<String>,
    /// Constructors called without a name that says so: `new(...)`,
    /// `: this(...)`, `: base(...)`.
    constructed: HashSet<SymbolId>,
}

impl Facts {
    fn gather(view: &mut View<'_>) -> Self {
        let mut owners: Vec<SyntaxNode> = view
            .root
            .descendants()
            .filter(|node| is_body_owner(node.kind()) && node.kind() != SyntaxKind::CompilationUnit)
            .collect();
        if view
            .root
            .children()
            .any(|child| child.kind() == SyntaxKind::GlobalStatement)
        {
            owners.push(view.root.clone());
        }
        let tree = view.tree;
        let mut bodies = Vec::new();
        let mut constructed = HashSet::new();
        for owner in owners {
            let Some(bound) = view.body_for(&owner) else {
                continue;
            };
            let broken = bound
                .diagnostics
                .iter()
                .any(|(at, diagnostic)| *at == tree && diagnostic.is_error())
                || has_broken_syntax(&owner);
            super::walk::walk_body(&bound, &mut |visited| match visited {
                super::walk::Visited::Expression(expression) => {
                    if let rustlyn_semantics::BoundExpressionKind::ObjectCreation {
                        constructor: Some(constructor),
                        ..
                    } = &expression.kind
                    {
                        constructed.insert(*constructor);
                    }
                }
                super::walk::Visited::Statement(statement) => {
                    if let rustlyn_semantics::BoundStatementKind::ConstructorInitializer {
                        constructor: Some(constructor),
                        ..
                    } = &statement.kind
                    {
                        constructed.insert(*constructor);
                    }
                }
            });
            bodies.push(Body {
                owner,
                bound,
                broken,
            });
        }

        let mut uses: HashMap<SymbolId, Vec<Use>> = HashMap::new();
        let mut unresolved = HashSet::new();
        let tokens: Vec<SyntaxToken> = view
            .root
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .collect();
        for token in tokens {
            // `var` stands for a type without naming it.
            if token.value_text() == "var" && is_var_keyword(&token) {
                continue;
            }
            // `Add(b: 4)` names the parameter to pass to; it does not read it.
            // `p is { a: 1 }` does read `a`: the name in a property pattern
            // is the member the pattern looks at.
            if std::iter::once(token.parent().clone())
                .chain(token.parent().parent().cloned())
                .any(|node| {
                    node.kind() == SyntaxKind::NameColon
                        && node
                            .parent()
                            .is_none_or(|holder| holder.kind() != SyntaxKind::Subpattern)
                })
            {
                continue;
            }
            match view.resolve_use(&token) {
                Some(resolved @ Resolved::Symbol(symbol)) => {
                    if !declares(&token, &resolved) {
                        let access = access_of(&token);
                        uses.entry(symbol).or_default().push(Use { token, access });
                    }
                }
                Some(Resolved::Local { .. }) => {}
                None => {
                    unresolved.insert(token.value_text().to_string());
                }
            }
        }
        Self {
            bodies,
            uses,
            unresolved,
            constructed,
        }
    }

    /// The body `node` is in, if the file has one around it.
    fn body_around(&self, node: &SyntaxNode) -> Option<&Body> {
        let span = node.span();
        self.bodies
            .iter()
            .filter(|body| body.owner.span().contains_span(span))
            .min_by_key(|body| body.owner.span().length())
    }
}

/// Whether a `var` is the keyword of a declaration rather than a name.
fn is_var_keyword(token: &SyntaxToken) -> bool {
    let parent = token.parent();
    parent.kind() == SyntaxKind::IdentifierName
        && parent.parent().is_some_and(|grand| {
            matches!(
                grand.kind(),
                SyntaxKind::VariableDeclaration
                    | SyntaxKind::ForEachStatement
                    | SyntaxKind::ForEachVariableStatement
                    | SyntaxKind::DeclarationExpression
                    | SyntaxKind::DeclarationPattern
            )
        })
}

/// Whether `callee`, what a call calls, is written `nameof`. The length is
/// asked first: a callee can be a chain of thousands of calls, and its text
/// is not worth building to find that it is not six letters long.
fn is_nameof(callee: &SyntaxNode) -> bool {
    callee.span().length() == 6 && callee.text() == "nameof"
}

/// Whether the syntax of `node` has something missing or skipped in it.
fn has_broken_syntax(node: &SyntaxNode) -> bool {
    node.descendant_tokens().any(|token| {
        token.is_missing()
            || token
                .leading_trivia()
                .iter()
                .chain(token.trailing_trivia().iter())
                .any(|trivia| trivia.kind() == SyntaxKind::SkippedTokensTrivia)
    })
}

/// How the name `token` is used where it stands.
fn access_of(token: &SyntaxToken) -> Access {
    let mut node = token.parent().clone();
    if !matches!(
        node.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) {
        return Access::Read;
    }
    loop {
        let Some(parent) = node.parent().cloned() else {
            return Access::Read;
        };
        match parent.kind() {
            SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::PointerMemberAccessExpression
            | SyntaxKind::MemberBindingExpression => {
                if parent.children().last().as_ref() != Some(&node) {
                    return Access::Read;
                }
                node = parent;
            }
            SyntaxKind::ParenthesizedExpression => node = parent,
            SyntaxKind::SimpleAssignmentExpression => {
                return if parent.children().next().as_ref() == Some(&node) {
                    Access::Write
                } else {
                    Access::Read
                };
            }
            kind if is_compound_assignment(kind) => {
                if parent.children().next().as_ref() != Some(&node) {
                    return Access::Read;
                }
                return value_discarded(&parent);
            }
            SyntaxKind::PreIncrementExpression
            | SyntaxKind::PreDecrementExpression
            | SyntaxKind::PostIncrementExpression
            | SyntaxKind::PostDecrementExpression => return value_discarded(&parent),
            SyntaxKind::Argument => {
                let by = parent
                    .child_tokens()
                    .find(|token| {
                        matches!(
                            token.kind(),
                            SyntaxKind::OutKeyword | SyntaxKind::RefKeyword
                        )
                    })
                    .map(|token| token.kind());
                match by {
                    Some(SyntaxKind::OutKeyword) => return Access::Write,
                    Some(_) => return Access::ReadWrite,
                    None => {}
                }
                // `(a, b) = pair`: an element of a tuple on the left.
                match parent.parent() {
                    Some(tuple) if tuple.kind() == SyntaxKind::TupleExpression => {
                        node = tuple.clone();
                    }
                    _ => return Access::Read,
                }
            }
            SyntaxKind::TupleExpression => node = parent,
            // `ref int r = ref field;`, `return ref field;` and `&field` hand
            // out the variable itself: whoever holds it may write it.
            SyntaxKind::RefExpression | SyntaxKind::AddressOfExpression => {
                return Access::ReadWrite;
            }
            _ => return Access::Read,
        }
    }
}

/// A `+=` or `++` whose value nothing reads is a write; one inside a larger
/// expression is a read too.
fn value_discarded(expression: &SyntaxNode) -> Access {
    if expression
        .parent()
        .is_some_and(|parent| parent.kind() == SyntaxKind::ExpressionStatement)
    {
        Access::Write
    } else {
        Access::ReadWrite
    }
}

const fn is_compound_assignment(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AddAssignmentExpression
            | SyntaxKind::SubtractAssignmentExpression
            | SyntaxKind::MultiplyAssignmentExpression
            | SyntaxKind::DivideAssignmentExpression
            | SyntaxKind::ModuloAssignmentExpression
            | SyntaxKind::AndAssignmentExpression
            | SyntaxKind::ExclusiveOrAssignmentExpression
            | SyntaxKind::OrAssignmentExpression
            | SyntaxKind::LeftShiftAssignmentExpression
            | SyntaxKind::RightShiftAssignmentExpression
            | SyntaxKind::UnsignedRightShiftAssignmentExpression
            | SyntaxKind::CoalesceAssignmentExpression
    )
}

/// Whether a name is one of the discards Roslyn never reports: `_`, `__`,
/// `_1`.
fn is_discard_name(name: &str) -> bool {
    name.starts_with('_') && name[1..].chars().all(|c| c == '_' || c.is_ascii_digit())
}

#[cfg(test)]
pub(super) mod tests {
    use std::path::Path;

    use super::super::tests::compile;
    use super::*;

    /// Every analyzer diagnostic of `text`, as `ID@the text it covers`.
    pub(in super::super) fn found(text: &str) -> Vec<String> {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        semantic
            .analyzer_diagnostics(Path::new("/p/C.cs"), None)
            .expect("analyzed")
            .iter()
            .map(|diagnostic| {
                format!(
                    "{}@{}",
                    diagnostic.id,
                    &text[diagnostic.span.start() as usize..diagnostic.span.end() as usize]
                )
            })
            .collect()
    }

    /// The same, only the ones with `id`.
    pub(in super::super) fn found_with(text: &str, id: &str) -> Vec<String> {
        found(text)
            .into_iter()
            .filter(|entry| entry.split('@').next() == Some(id))
            .map(|entry| {
                entry
                    .split_once('@')
                    .map(|(_, at)| at.to_string())
                    .unwrap_or_default()
            })
            .collect()
    }

    #[test]
    fn a_clean_file_has_nothing_to_say() {
        let text = "\
                    public class Counter {\n\
                      private readonly int step;\n\
                      private int total;\n\
                      public Counter(int step) { this.step = step; }\n\
                      public int Next() { total += step; return total; }\n\
                    }\n";
        assert!(found(text).is_empty(), "{:?}", found(text));
    }

    #[test]
    fn severities_and_tags_are_roslyns() {
        let text = "class C {\n  private int unused;\n  public int M() { int x = 1; return 2; x = 3; }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let all = semantic
            .analyzer_diagnostics(Path::new("/p/C.cs"), None)
            .expect("analyzed");
        let by = |id: &str| {
            all.iter()
                .find(|diagnostic| diagnostic.id == id)
                .unwrap_or_else(|| panic!("{id} in {all:?}"))
        };
        assert_eq!(by("IDE0051").severity, Severity::Info);
        assert!(by("IDE0051").unnecessary);
        assert_eq!(by("CS0219").severity, Severity::Warning);
        assert_eq!(by("CS0162").severity, Severity::Warning);
        assert!(!by("CS0162").unnecessary);
        assert_eq!(by("IDE0035").severity, Severity::Hidden);
        assert!(by("IDE0035").unnecessary);
    }

    #[test]
    fn var_standing_for_an_obsolete_type_is_no_use_of_it() {
        let text = "[System.Obsolete(\"no\")] class Old { public static Old Make() => null; }\n\
                    class C { void M() { var made = Old.Make(); System.Console.WriteLine(made); } }\n";
        assert_eq!(found_with(text, "CS0618"), ["Old"]);
    }

    #[test]
    fn a_private_field_only_written_is_cs0414_as_well() {
        // `private bool success = false;` never read: the compiler's CS0414
        // beside the IDE's IDE0052, as Rider and Unity show it. A field
        // that is read, or one with an attribute (Unity's `[SerializeField]`
        // is read by the engine), is neither.
        let text = "class Attr : System.Attribute { }\n\
                    class Loader {\n\
                      private bool success = false;\n\
                      private int count;\n\
                      [Attr] private int shown = 1;\n\
                      private string kept;\n\
                      private int progressive = 256;\n\
                      public Loader(string name) { kept = name; }\n\
                      public void Run() { success = true; count = 2; System.Console.WriteLine(count); }\n\
                    }\n";
        // `kept` holds a constructor's argument: no constant, no CS0414,
        // though nobody reads it either.
        assert_eq!(found_with(text, "CS0414"), ["success", "progressive"]);
        assert_eq!(found_with(text, "IDE0052"), ["success", "kept"]);
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let all = semantic
            .analyzer_diagnostics(Path::new("/p/C.cs"), None)
            .expect("analyzed");
        let warning = all
            .iter()
            .find(|found| found.id == "CS0414")
            .expect("CS0414");
        assert_eq!(warning.severity, Severity::Warning);
        assert_eq!(
            warning.message,
            "The field 'Loader.success' is assigned but its value is never used"
        );
    }

    #[test]
    fn a_using_nothing_needs_fades() {
        let text = "using System;\nusing System.Collections.Generic;\n\
                    public class C { public void M() { Console.WriteLine(1); } }\n";
        assert_eq!(
            found_with(text, "IDE0005"),
            vec!["using System.Collections.Generic;"]
        );
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let all = semantic
            .analyzer_diagnostics(Path::new("/p/C.cs"), None)
            .expect("analyzed");
        let using = all
            .iter()
            .find(|found| found.id == "IDE0005")
            .expect("IDE0005");
        assert_eq!(using.severity, Severity::Hidden);
        assert!(using.unnecessary);
    }

    #[test]
    fn a_body_with_an_error_is_left_alone() {
        let text = "class C { public void M() { int x = Missing(); } }\n";
        assert!(found_with(text, "IDE0059").is_empty());
        assert!(found_with(text, "CS0219").is_empty());
    }

    /// The text of a class whose one method returns `chain`.
    fn returning(chain: &str) -> String {
        format!("class C {{ C M(C a) {{ return {chain}; }} }}\n")
    }

    /// How long the analyzers and the classifier take over `text`.
    fn analyzed_in(text: &str) -> std::time::Duration {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let path = Path::new("/p/C.cs");
        let started = std::time::Instant::now();
        semantic.analyzer_diagnostics(path, None).expect("analyzed");
        semantic
            .semantic_tokens(path, TextSpan::new(0, text.len() as u32), None)
            .expect("classified");
        started.elapsed()
    }

    #[test]
    fn a_long_chain_costs_what_its_length_does() {
        // What the analyzers ask of a node about the nodes above it is the
        // depth of the tree, and a chain of calls, a sum or a ladder of
        // `else if` is as deep as it is long: asked of each of them, the
        // diagnostics of a thousand calls took a minute and a half, though
        // the compiler read the same text in less than a second.
        let calls = analyzed_in(&returning(&format!("a{}", ".M(a)".repeat(2000))));
        assert!(
            calls < std::time::Duration::from_secs(120),
            "{calls:?} for two thousand calls"
        );
        // Four times the length takes about four times as long, not sixteen:
        // a margin for the machine being busy, which two timings share.
        let sum = |terms: usize| {
            format!(
                "class C {{ int M(int a) => {}; }}\n",
                vec!["a"; terms].join(" + ")
            )
        };
        let short = analyzed_in(&sum(2000));
        let long = analyzed_in(&sum(8000));
        assert!(
            long < short * 10 + std::time::Duration::from_secs(2),
            "{short:?} for two thousand terms, {long:?} for eight thousand"
        );
        let ladder = |rungs: usize| {
            format!(
                "class C {{ int M(int a) {{ int x = 0; if (a == 0) x = 0;\n{}else x = -1; return x; }} }}\n",
                (1..rungs)
                    .map(|i| format!("else if (a == {i}) x = {i};\n"))
                    .collect::<String>()
            )
        };
        let short = analyzed_in(&ladder(1000));
        let long = analyzed_in(&ladder(4000));
        assert!(
            long < short * 10 + std::time::Duration::from_secs(2),
            "{short:?} for a thousand rungs, {long:?} for four thousand"
        );
    }

    #[test]
    fn a_deep_tree_needs_no_deep_stack_of_the_caller() {
        // The analyzers and the classifier walk the tree as deep as it is,
        // which the parser lets be twelve thousand levels, and an
        // unoptimized build takes kilobytes of stack for each. They are
        // asked from the editor's own thread, which has a megabyte or two.
        let text = format!(
            "class C {{ int M(int a) => {}0; }}\n",
            (0..9000)
                .map(|i| format!("a == {i} ? {i} : "))
                .collect::<String>()
        );
        let semantic = compile(&[("C.cs", &text)], false).expect("compiled");
        let length = text.len() as u32;
        let small = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(move || {
                let path = Path::new("/p/C.cs");
                let found = semantic.analyzer_diagnostics(path, None);
                let tokens = semantic.semantic_tokens(path, TextSpan::new(0, length), None);
                (found.is_some(), tokens.map(|tokens| tokens.len()))
            })
            .expect("a thread");
        let (analyzed, tokens) = small.join().expect("no overflow");
        assert!(analyzed);
        assert!(tokens.is_some_and(|count| count > 9000));
    }

    #[test]
    fn access_is_read_write_or_both() {
        let text = "class C { int a, b, c, d, e, f; void M(ref int r) { a = 1; b += 1; var x = c++; M(ref d); e.ToString(); (f, a) = (1, 2); } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let view = semantic
            .view(semantic.tree_index(Path::new("/p/C.cs")).unwrap())
            .unwrap();
        let access = |marker: &str| {
            let offset = text.find(marker).unwrap() as u32;
            access_of(&view.root.find_token(offset).unwrap())
        };
        assert_eq!(access("a = 1"), Access::Write);
        assert_eq!(access("b += 1"), Access::Write);
        assert_eq!(access("c++"), Access::ReadWrite);
        assert_eq!(access("d)"), Access::ReadWrite);
        assert_eq!(access("e."), Access::Read);
        assert_eq!(access("f, a)"), Access::Write);
    }
}
