//! Resolving names to symbols and type syntax to types.
//!
//! Everything here needs the whole declaration table, which is why it is a
//! second pass: `class A { B field; }` cannot be resolved while `B` is still
//! being declared.
//!
//! Lookup walks outwards through the scopes the syntax sits in — the enclosing
//! types, then the enclosing namespaces, each with the `using` directives
//! written in it — and stops at the first name that fits. Arity is part of the
//! question: `List<int>` looks for a `List` with one type parameter and will
//! not settle for one with none.

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, TokenValue};
use rustlyn_text::TextSpan;

use crate::bound::{BoundAttribute, BoundExpressionKind};
use crate::compilation::Compilation;
use crate::corlib::SpecialType;
use crate::symbol::{Detail, Modifiers, RefKind, SymbolId, SymbolKind, TypeSyntaxRef};
use crate::types::{TupleElement, Type};

/// Where diagnostics go. Queries that only want an answer pass an empty one
/// and throw it away.
pub type Diagnostics = Vec<(usize, Diagnostic)>;

/// What a `using` directive brought into scope.
#[derive(Clone, Debug)]
pub(crate) enum Import {
    /// `using System;`
    Namespace(SymbolId),
    /// `using static System.Math;`
    Static(SymbolId),
    /// `using Alias = System.Collections.Generic.List<int>;`
    Alias { name: String, target: SyntaxNode },
}

/// One level of the scope chain.
#[derive(Clone, Debug, Default)]
struct Scope {
    namespace: Option<SymbolId>,
    ty: Option<SymbolId>,
    /// The method or property the syntax sits in, which owns its type
    /// parameters.
    member: Option<SymbolId>,
    imports: Vec<Import>,
}

/// What a name turned out to mean.
///
/// An alias comes back as the syntax it stands for rather than as a symbol,
/// because `using Numbers = List<int>;` names a constructed type, and a symbol
/// alone would lose the `int`.
#[derive(Clone, Debug)]
pub enum Resolution {
    Symbol(SymbolId),
    AliasTo(SyntaxNode),
}

/// The scopes a piece of syntax sits in, innermost first.
#[derive(Clone, Debug)]
pub struct Context {
    tree: usize,
    scopes: Vec<Scope>,
}

impl Context {
    /// Which file this context belongs to.
    #[must_use]
    pub const fn tree(&self) -> usize {
        self.tree
    }

    /// The innermost enclosing type, if any.
    #[must_use]
    pub fn enclosing_type(&self) -> Option<SymbolId> {
        self.scopes.iter().find_map(|scope| scope.ty)
    }

    /// Every enclosing type, innermost first.
    ///
    /// A nested type sits inside another, and what that one declares is in
    /// scope: `Parser` inside `DocumentationCommentId` writes `EncodeName`
    /// with nothing in front of it.
    #[must_use]
    pub fn enclosing_types(&self) -> Vec<SymbolId> {
        self.scopes.iter().filter_map(|scope| scope.ty).collect()
    }

    /// The innermost enclosing method or property, if any.
    #[must_use]
    pub fn enclosing_member(&self) -> Option<SymbolId> {
        self.scopes.iter().find_map(|scope| scope.member)
    }
}

/// Resolves names against a compilation.
///
/// Resolving a base type needs name lookup, and name lookup needs base types
/// to find inherited nested types, so the two can chase each other. The cache
/// that breaks the cycle lives on the compilation rather than here: a binder
/// is made per file, and the answer is the same for all of them.
#[derive(Debug)]
pub struct Binder<'a> {
    compilation: &'a Compilation,
    /// A file being edited, which the compilation has the old text of.
    speculation: Option<std::sync::Arc<Speculation>>,
}

/// One file of a compilation as it is now, rather than as it was compiled.
///
/// An editor asks about the text on screen, and the compilation is of the
/// text as it was last saved; compiling again for every keystroke costs what
/// declaring the whole project costs. But typing changes a few places, and
/// between them the text is the same, shifted by how much was typed before.
/// So a node of the new tree whose ends are in text the edits left alone —
/// the method being typed in, its class, its namespace — is the same
/// declaration as the node of the old tree at the mapped span, and has the
/// same symbol; and the body being typed in can be bound against everything
/// else as compiled.
///
/// What this cannot do is see a declaration the edit itself introduced: a
/// method typed a moment ago is not in the symbol table yet. Everything that
/// was is.
#[derive(Clone, Debug)]
pub struct Speculation {
    /// Which tree of the compilation this is a new version of.
    pub tree: usize,
    /// The new tree's root.
    pub root: SyntaxNode,
    /// The stretches of text the edits left alone, in order: where each
    /// starts in the old text, where in the new one, and how long it is.
    same: Vec<Same>,
    /// What the `using`s of each scope of the new tree bring in, by the
    /// scope: see [`Binder::speculative_imports`].
    imports: std::sync::Arc<std::sync::Mutex<SpeculativeImports>>,
}

/// A stretch of text an edit left alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Same {
    old: u32,
    new: u32,
    len: u32,
}

/// How far ahead, in lines, the text after a change is looked for: a change
/// longer than this is taken to run on to the next one found.
const RESYNC_LINES: usize = 256;

/// The imports of scopes of a speculation's tree, by the scope's span and
/// kind and the namespace it is in.
type SpeculativeImports =
    std::collections::HashMap<(TextSpan, SyntaxKind, Option<SymbolId>), Vec<Import>>;

impl Speculation {
    /// The speculation that turns tree `tree`, with text `old`, into `new`.
    #[must_use]
    pub fn new(tree: usize, old: &str, new: &rustlyn_syntax::SyntaxTree) -> Self {
        Self {
            tree,
            root: new.root(),
            same: same_stretches(old, new.source().text()),
            imports: std::sync::Arc::default(),
        }
    }

    /// Where a span of the new text was in the old one, if it was anywhere:
    /// a span that starts or ends inside a change has no counterpart.
    #[must_use]
    pub fn map(&self, span: TextSpan) -> Option<TextSpan> {
        translate(&self.same, span, |same| (same.new, same.old))
    }

    /// Where a span of the old text is in the new one: the other direction
    /// of [`Self::map`], for answers that point into the compiled file.
    #[must_use]
    pub fn unmap(&self, span: TextSpan) -> Option<TextSpan> {
        translate(&self.same, span, |same| (same.old, same.new))
    }

    /// Whether `node` is from the new tree rather than the compiled one.
    fn owns(&self, node: &SyntaxNode) -> bool {
        let root = node.ancestors().last().unwrap_or_else(|| node.clone());
        root == self.root
    }
}

/// The stretches two texts have in common around their differences.
///
/// What the two begin and end with is the same; between, lines are matched
/// up again past each change, nearest first, and the lines of a change are
/// trimmed of what they begin and end with alike: `ex.Message` cut to `ex.`
/// leaves the declaration it is in starting in text that did not change.
fn same_stretches(old: &str, new: &str) -> Vec<Same> {
    fn push(same: &mut Vec<Same>, old: usize, new: usize, len: usize) {
        if len == 0 {
            return;
        }
        let (old, new, len) = (old as u32, new as u32, len as u32);
        match same.last_mut() {
            Some(last) if last.old + last.len == old && last.new + last.len == new => {
                last.len += len;
            }
            _ => same.push(Same { old, new, len }),
        }
    }
    // A change: trimmed of what both sides of it begin and end with.
    fn changed(same: &mut Vec<Same>, old: &str, new: &str, at: (usize, usize, usize, usize)) {
        let (old_start, old_end, new_start, new_end) = at;
        let (prefix, suffix) = common_ends(old, new, old_start, old_end, new_start, new_end);
        push(same, old_start, new_start, prefix);
        push(same, old_end - suffix, new_end - suffix, suffix);
    }

    let (a, b) = (old.as_bytes(), new.as_bytes());
    let mut same = Vec::new();
    let (start, suffix) = common_ends(old, new, 0, a.len(), 0, b.len());
    let (old_end, new_end) = (a.len() - suffix, b.len() - suffix);
    push(&mut same, 0, 0, start);
    if start < old_end && start < new_end {
        let old_lines = line_starts(old, start, old_end);
        let new_lines = line_starts(new, start, new_end);
        let old_at = |index: usize| old_lines.get(index).copied().unwrap_or(old_end);
        let new_at = |index: usize| new_lines.get(index).copied().unwrap_or(new_end);
        let same_line =
            |i: usize, j: usize| a[old_at(i)..old_at(i + 1)] == b[new_at(j)..new_at(j + 1)];
        let (mut i, mut j) = (0, 0);
        while i < old_lines.len() && j < new_lines.len() {
            if same_line(i, j) {
                push(&mut same, old_at(i), new_at(j), old_at(i + 1) - old_at(i));
                i += 1;
                j += 1;
                continue;
            }
            // Where the lines agree again: the nearest pair, counting the
            // lines skipped on both sides.
            let found = (1..=2 * RESYNC_LINES).find_map(|distance| {
                (0..=distance).find_map(|skipped| {
                    let (oi, nj) = (i + skipped, j + distance - skipped);
                    (oi < old_lines.len() && nj < new_lines.len() && same_line(oi, nj))
                        .then_some((oi, nj))
                })
            });
            let (oi, nj) = found.unwrap_or((old_lines.len(), new_lines.len()));
            changed(
                &mut same,
                old,
                new,
                (old_at(i), old_at(oi), new_at(j), new_at(nj)),
            );
            (i, j) = (oi, nj);
        }
        if i < old_lines.len() || j < new_lines.len() {
            changed(
                &mut same,
                old,
                new,
                (old_at(i), old_end, new_at(j), new_end),
            );
        }
    }
    push(&mut same, old_end, new_end, suffix);
    same
}

/// A span carried across the stretches an edit left alone, `ends` saying
/// where each stretch starts on the side the span is from and on the other.
///
/// Where two stretches meet with a change between them on the other side —
/// text deleted — a span's start is of the stretch after, whose first
/// character it is, and its end of the stretch before.
fn translate(
    same: &[Same],
    span: TextSpan,
    ends: impl Fn(&Same) -> (u32, u32),
) -> Option<TextSpan> {
    let across = |at: u32, starts: bool| -> Option<u32> {
        let inside = |stretch: &&Same| {
            let (from, _) = ends(stretch);
            if starts {
                from <= at && at < from + stretch.len
            } else {
                from < at && at <= from + stretch.len
            }
        };
        let touching = |stretch: &&Same| {
            let (from, _) = ends(stretch);
            from <= at && at <= from + stretch.len
        };
        let stretch = same
            .iter()
            .find(inside)
            .or_else(|| same.iter().find(touching))?;
        let (from, to) = ends(stretch);
        Some(at - from + to)
    };
    let start = across(span.start(), true)?;
    let end = if span.is_empty() {
        start
    } else {
        across(span.end(), false)?
    };
    Some(TextSpan::new(start, end.checked_sub(start)?))
}

/// How many bytes `old[old_start..old_end]` and `new[new_start..new_end]`
/// begin with alike, and how many of the rest they end with alike, on
/// character boundaries.
fn common_ends(
    old: &str,
    new: &str,
    old_start: usize,
    old_end: usize,
    new_start: usize,
    new_end: usize,
) -> (usize, usize) {
    let (a, b) = (
        &old.as_bytes()[old_start..old_end],
        &new.as_bytes()[new_start..new_end],
    );
    let limit = a.len().min(b.len());
    let mut prefix = a.iter().zip(b).take_while(|(x, y)| x == y).count();
    let mut suffix = a
        .iter()
        .rev()
        .zip(b.iter().rev())
        .take(limit - prefix)
        .take_while(|(x, y)| x == y)
        .count();
    // Keep both ends on character boundaries, so a span never starts in
    // the middle of one.
    while prefix > 0 && !new.is_char_boundary(new_start + prefix) {
        prefix -= 1;
    }
    while suffix > 0 && !new.is_char_boundary(new_end - suffix) {
        suffix -= 1;
    }
    (prefix, suffix)
}

/// Where each line of `text[start..end]` starts.
fn line_starts(text: &str, start: usize, end: usize) -> Vec<usize> {
    let mut starts = vec![start];
    starts.extend(
        text.as_bytes()[start..end]
            .iter()
            .enumerate()
            .filter(|(_, byte)| **byte == b'\n')
            .map(|(at, _)| start + at + 1)
            .filter(|at| *at < end),
    );
    starts
}

impl<'a> Binder<'a> {
    #[must_use]
    pub const fn new(compilation: &'a Compilation) -> Self {
        Self {
            compilation,
            speculation: None,
        }
    }

    /// A binder for which tree `speculation.tree` is the new text.
    #[must_use]
    pub fn speculative(compilation: &'a Compilation, speculation: Speculation) -> Self {
        Self {
            compilation,
            speculation: Some(std::sync::Arc::new(speculation)),
        }
    }

    /// The root of tree `tree` as this binder sees it: the new one for the
    /// file being speculated about.
    #[must_use]
    pub fn tree_root(&self, tree: usize) -> Option<SyntaxNode> {
        match &self.speculation {
            Some(speculation) if speculation.tree == tree => Some(speculation.root.clone()),
            _ => Some(self.compilation.trees().get(tree)?.root()),
        }
    }

    /// The symbol a declaration node declares.
    #[must_use]
    pub fn declared_symbol_at(&self, tree: usize, node: &SyntaxNode) -> Option<SymbolId> {
        let speculation = self
            .speculation
            .as_deref()
            .filter(|speculation| speculation.tree == tree && speculation.owns(node));
        self.declared_symbol_in(tree, node, speculation)
    }

    /// The same for a node already known to be, or not to be, of the
    /// speculation — which is a walk to the root to find out.
    fn declared_symbol_in(
        &self,
        tree: usize,
        node: &SyntaxNode,
        speculation: Option<&Speculation>,
    ) -> Option<SymbolId> {
        let Some(speculation) = speculation else {
            return self.compilation.declared_symbol(tree, node.span());
        };
        // The file is the file, whatever was typed at its very start.
        if node.kind() == SyntaxKind::CompilationUnit {
            let root = self.compilation.trees().get(tree)?.root();
            return self.compilation.declared_symbol(tree, root.span());
        }
        if let Some(symbol) = speculation
            .map(node.span())
            .and_then(|span| self.compilation.declared_symbol(tree, span))
        {
            return Some(symbol);
        }
        // Where the edit moved where a declaration ends — an initializer cut
        // short, which the next lines then run into — it is still the one of
        // its kind that starts where it did. Only a declaration is looked
        // for so: a context asks of every node around a name.
        if !matches!(
            node.kind(),
            SyntaxKind::ClassDeclaration
                | SyntaxKind::StructDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::RecordDeclaration
                | SyntaxKind::RecordStructDeclaration
                | SyntaxKind::UnionDeclaration
                | SyntaxKind::EnumDeclaration
                | SyntaxKind::DelegateDeclaration
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::DestructorDeclaration
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::IndexerDeclaration
                | SyntaxKind::EventDeclaration
                | SyntaxKind::GetAccessorDeclaration
                | SyntaxKind::SetAccessorDeclaration
                | SyntaxKind::InitAccessorDeclaration
                | SyntaxKind::AddAccessorDeclaration
                | SyntaxKind::RemoveAccessorDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
                | SyntaxKind::VariableDeclarator
                | SyntaxKind::EnumMemberDeclaration
                | SyntaxKind::NamespaceDeclaration
                | SyntaxKind::FileScopedNamespaceDeclaration
        ) {
            return None;
        }
        let start = speculation
            .map(TextSpan::new(node.span().start(), 0))?
            .start();
        let token = self
            .compilation
            .trees()
            .get(tree)?
            .root()
            .find_token(start)?;
        let compiled = std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .take_while(|ancestor| ancestor.span().start() == start)
            .find(|ancestor| ancestor.kind() == node.kind())?;
        self.compilation.declared_symbol(tree, compiled.span())
    }

    #[must_use]
    pub const fn compilation(&self) -> &'a Compilation {
        self.compilation
    }

    // -- context -----------------------------------------------------------

    /// The scopes `node` sits in, read off its ancestors.
    #[must_use]
    pub fn context_at(&self, tree: usize, node: &SyntaxNode) -> Context {
        let mut scopes = Vec::new();

        // Every ancestor is in the tree `node` is in, so whether that is the
        // speculation's is asked once. Asked of each ancestor — a walk to the
        // root each time — it made a context cost the square of the depth,
        // and a chain of two thousand calls hung the editor's questions
        // (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide).
        let speculation = self
            .speculation
            .as_deref()
            .filter(|speculation| speculation.tree == tree && speculation.owns(node));

        // The namespaces the innermost declaration so far implies, still to
        // be put in scope: see `push_implied`.
        let mut implied: Option<SymbolId> = None;

        // The node's own declaration counts: a method's type parameters are in
        // scope inside its signature.
        for ancestor in std::iter::once(node.clone()).chain(node.ancestors()) {
            let symbol = self.declared_symbol_in(tree, &ancestor, speculation);
            match ancestor.kind() {
                SyntaxKind::ClassDeclaration
                | SyntaxKind::StructDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::RecordDeclaration
                | SyntaxKind::RecordStructDeclaration
                | SyntaxKind::UnionDeclaration
                | SyntaxKind::EnumDeclaration
                | SyntaxKind::DelegateDeclaration => scopes.push(Scope {
                    ty: symbol,
                    ..Scope::default()
                }),
                SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::IndexerDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
                // A local function is a method, with parameters and type
                // parameters of its own, and it sits inside the scope of the
                // method that holds it rather than replacing it.
                | SyntaxKind::LocalFunctionStatement
                // An extension block (C# 14) is where its type parameters
                // are in scope, on the holder its syntax names.
                | SyntaxKind::ExtensionBlockDeclaration => scopes.push(Scope {
                    member: symbol,
                    ..Scope::default()
                }),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration => {
                    // What the declaration inside implied stops at this one.
                    self.push_implied(implied.take(), symbol, &mut scopes);
                    scopes.push(Scope {
                        namespace: symbol,
                        imports: self.imports_at(tree, &ancestor, symbol, speculation),
                        ..Scope::default()
                    });
                    implied = symbol.and_then(|symbol| self.compilation.symbols().get(symbol).container);
                }
                SyntaxKind::CompilationUnit => {
                    self.push_implied(implied.take(), None, &mut scopes);
                    // A file of top-level statements is the body of
                    // `Program.<Main>$`: its local functions and `args` are
                    // that method's, and the class is in scope around it.
                    if let Some(main) = symbol.filter(|main| {
                        self.compilation.symbols().get(*main).kind == SymbolKind::Method
                    }) {
                        scopes.push(Scope {
                            member: Some(main),
                            ..Scope::default()
                        });
                        scopes.push(Scope {
                            ty: self.compilation.symbols().get(main).container,
                            ..Scope::default()
                        });
                    }
                    let global = Some(self.compilation.global_namespace());
                    let mut imports = self.imports_at(tree, &ancestor, global, speculation);
                    // `global using` in any file reaches every file.
                    imports.extend(self.global_imports());
                    scopes.push(Scope {
                        namespace: Some(self.compilation.global_namespace()),
                        imports,
                        ..Scope::default()
                    });
                }
                _ => {}
            }
        }
        self.push_implied(implied, None, &mut scopes);

        Context { tree, scopes }
    }

    /// Puts in scope the namespaces a declaration of `from`'s member implies,
    /// out to the declaration around it, which is of `until`.
    ///
    /// `namespace System.Diagnostics.CodeAnalysis` is three namespaces, and
    /// all three are in scope: that is what makes `Attribute` mean
    /// `System.Attribute` inside it without a `using`. Its `using`s belong to
    /// the innermost alone. A declaration around it is of a namespace with
    /// `using`s of its own, which come right after that namespace's members
    /// (§7.8.1) — so the implied ones stop there. Each declaration pushing
    /// every namespace out to the global one put an outer namespace's
    /// members ahead of an inner declaration's `using`s, and made `n` nested
    /// declarations `n²` scopes (found by fuzzing).
    fn push_implied(
        &self,
        from: Option<SymbolId>,
        until: Option<SymbolId>,
        scopes: &mut Vec<Scope>,
    ) {
        let symbols = self.compilation.symbols();
        let mut enclosing = from;
        while let Some(namespace) = enclosing {
            if Some(namespace) == until || symbols.get(namespace).name.is_empty() {
                break;
            }
            scopes.push(Scope {
                namespace: Some(namespace),
                ..Scope::default()
            });
            enclosing = symbols.get(namespace).container;
        }
    }

    /// The `using` directives of one scope, worked out once.
    ///
    /// A context is built afresh for every name that has to be resolved, and
    /// resolving a `using` is itself name resolution — so without a cache the
    /// same handful of directives is resolved thousands of times per file.
    ///
    /// `speculation` is the edit when `container` is of its tree, as
    /// `context_at` found once for all the scopes: asked of each scope, a
    /// walk to the root each time, two thousand nested namespaces made every
    /// name cost the square of the depth (found by fuzzing).
    fn imports_at(
        &self,
        tree: usize,
        container: &SyntaxNode,
        namespace: Option<SymbolId>,
        speculation: Option<&Speculation>,
    ) -> Vec<Import> {
        // A scope the edit is inside of may have different `using`s from
        // the compiled one, and is worked out afresh for the edit.
        let compiled = match speculation {
            Some(speculation) => speculation.map(container.span()),
            None => Some(container.span()),
        };
        let Some(span) = compiled else {
            return self.speculative_imports(tree, container, namespace);
        };
        let key = (tree, span, container.kind());
        if let Some(cached) = self.compilation.cached_imports(key) {
            return cached;
        }
        let imports = self.imports_of(tree, container, namespace);
        self.compilation.cache_imports(key, imports.clone());
        imports
    }

    /// The imports of a scope of the edit, worked out once for it.
    ///
    /// Not kept with the compilation's — the scope is not the compiled one —
    /// but kept with the edit: asked once for every name bound inside it,
    /// every name of a file being typed in cost a resolution of every
    /// `using` above it — thirty seconds of code actions for a file of
    /// 25 KB (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide).
    fn speculative_imports(
        &self,
        tree: usize,
        container: &SyntaxNode,
        namespace: Option<SymbolId>,
    ) -> Vec<Import> {
        let Some(speculation) = &self.speculation else {
            return self.imports_of(tree, container, namespace);
        };
        let key = (container.span(), container.kind(), namespace);
        let cache = || {
            speculation
                .imports
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
        };
        if let Some(cached) = cache().get(&key) {
            return cached.clone();
        }
        // Worked out with the cache unlocked: resolving a `using` asks for
        // the imports around it.
        let imports = self.imports_of(tree, container, namespace);
        cache().insert(key, imports.clone());
        imports
    }

    fn imports_of(
        &self,
        tree: usize,
        container: &SyntaxNode,
        namespace: Option<SymbolId>,
    ) -> Vec<Import> {
        container
            .children()
            .filter(|child| child.kind() == SyntaxKind::UsingDirective)
            .filter_map(|directive| self.import_of(tree, &directive, namespace))
            .collect()
    }

    /// The `global using` directives of every file in the compilation.
    ///
    /// Every file's, for every name in every file: this is the one lookup in
    /// the binder whose cost is the size of the whole compilation, so it is
    /// worked out once and kept.
    fn global_imports(&self) -> Vec<Import> {
        if let Some(cached) = self.compilation.cached_global_imports() {
            return cached;
        }
        let imports = self.global_imports_uncached();
        self.compilation.cache_global_imports(imports.clone());
        imports
    }

    fn global_imports_uncached(&self) -> Vec<Import> {
        // Only the files known to hold one: parsing every file of the
        // compilation to find out would cost more than the question.
        self.compilation
            .global_using_trees()
            .iter()
            .filter_map(|&index| Some((index, self.compilation.trees().get(index)?)))
            .flat_map(|(index, tree)| {
                tree.root()
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::UsingDirective)
                    .filter(|directive| {
                        directive
                            .child_tokens()
                            .any(|token| token.kind() == SyntaxKind::GlobalKeyword)
                    })
                    .map(|directive| (index, directive))
                    .collect::<Vec<_>>()
            })
            .filter_map(|(tree, directive)| {
                self.import_of(tree, &directive, Some(self.compilation.global_namespace()))
            })
            .collect()
    }

    fn import_of(
        &self,
        tree: usize,
        directive: &SyntaxNode,
        namespace: Option<SymbolId>,
    ) -> Option<Import> {
        let target = directive
            .children()
            .find(|child| child.kind().is_type_node())?;

        if let Some(alias) = directive.child_of_kind(SyntaxKind::NameEquals) {
            let name = alias
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)?
                .value_text()
                .to_string();
            return Some(Import::Alias { name, target });
        }

        // The target of a `using` is resolved against the namespace the
        // directive sits in and the ones around it: inside `namespace N`,
        // `using static Kind;` names `N.Kind`. A `using` cannot lean on
        // another beside it, but one inside a namespace declaration is in
        // the scope of the declarations around it, and of their `using`s:
        // `using N.Constants;` at the top of a file and `using static
        // Keys;` inside `namespace N.Systems` import `N.Constants.Keys`.
        let around = match directive.parent() {
            Some(declaration)
                if matches!(
                    declaration.kind(),
                    SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
                ) && let Some(outer) = declaration.parent() =>
            {
                let mut scopes = Vec::new();
                let until = match outer.kind() {
                    SyntaxKind::CompilationUnit => None,
                    _ => self.declared_symbol_at(tree, outer),
                };
                self.push_implied(namespace, until, &mut scopes);
                scopes.extend(self.context_at(tree, outer).scopes);
                Context { tree, scopes }
            }
            _ => {
                let symbols = self.compilation.symbols();
                let mut scopes = Vec::new();
                let mut enclosing = namespace;
                while let Some(current) = enclosing {
                    scopes.push(Scope {
                        namespace: Some(current),
                        ..Scope::default()
                    });
                    if symbols.get(current).name.is_empty() {
                        break;
                    }
                    enclosing = symbols.get(current).container;
                }
                if scopes.is_empty() {
                    scopes.push(Scope {
                        namespace: Some(self.compilation.global_namespace()),
                        ..Scope::default()
                    });
                }
                Context { tree, scopes }
            }
        };
        let symbol = self.resolve_namespace_or_type(&target, &around)?;

        let is_static = directive
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::StaticKeyword);
        Some(if is_static {
            Import::Static(symbol)
        } else {
            Import::Namespace(symbol)
        })
    }

    // -- name lookup -------------------------------------------------------

    /// Resolves a name that may denote either a namespace or a type.
    #[must_use]
    pub fn resolve_namespace_or_type(
        &self,
        name: &SyntaxNode,
        context: &Context,
    ) -> Option<SymbolId> {
        match name.kind() {
            SyntaxKind::IdentifierName => {
                let text = identifier_text(name)?;
                self.lookup(&text, 0, context)
            }
            SyntaxKind::GenericName => {
                let text = identifier_text(name)?;
                let arity = type_argument_count(name);
                self.lookup(&text, arity, context)
            }
            SyntaxKind::QualifiedName => {
                let mut children = name.children();
                let left = children.next()?;
                let right = children.next()?;
                let container = self.resolve_namespace_or_type(&left, context)?;
                self.lookup_in(container, &right, context.tree)
            }
            SyntaxKind::AliasQualifiedName => {
                let mut children = name.children();
                let alias = children.next()?;
                let right = children.next()?;
                let written = identifier_text(&alias);
                let container = if written.as_deref() == Some("global") {
                    self.compilation.global_namespace()
                } else if let Some(root) = written
                    .as_deref()
                    .and_then(|name| self.compilation.extern_alias(name))
                {
                    // `extern alias A;` and then `A::N.T`: the root the
                    // reference given that alias was declared under.
                    root
                } else {
                    self.resolve_namespace_or_type(&alias, context)?
                };
                self.lookup_in(container, &right, context.tree)
            }
            _ => None,
        }
    }

    /// Looks a name up inside one container, which is what a `.` means.
    fn lookup_in(&self, container: SymbolId, name: &SyntaxNode, tree: usize) -> Option<SymbolId> {
        let text = identifier_text(name)?;
        let arity = type_argument_count(name);
        let symbols = self.compilation.symbols();
        // A type nested in a base type is nested in the derived one as far as
        // a name is concerned: `Derived.Inner` finds what `Base<int>` declares.
        if symbols.get(container).kind == SymbolKind::NamedType
            && let Some(found) = self.lookup_type_in_hierarchy(container, &text, arity, 0)
        {
            return Some(found);
        }
        self.compilation
            .lookup_type_from(container, &text, arity, tree)
            .or_else(|| {
                (arity == 0)
                    .then(|| symbols.lookup_namespace(container, &text))
                    .flatten()
                    .filter(|found| self.compilation.sees_namespace(*found, tree))
            })
    }

    /// Looks a name up through the scope chain, collapsing an alias to what it
    /// ultimately names.
    #[must_use]
    pub fn lookup(&self, name: &str, arity: usize, context: &Context) -> Option<SymbolId> {
        match self.lookup_resolution(name, arity, context)? {
            Resolution::Symbol(symbol) => Some(symbol),
            Resolution::AliasTo(target) => {
                self.resolve_namespace_or_type(&target, &self.alias_context(name, context))
            }
        }
    }

    /// Where the target of the alias `name` seen from `context` is read: the
    /// scope that declares the alias and those around it, as if that scope
    /// had no `using` directives (§14.5.2). `using Task =
    /// System.Threading.Tasks.Task;` at the top of a file names that `Task`
    /// inside `namespace A.B` beside an `A.System`.
    #[must_use]
    pub fn alias_context(&self, name: &str, context: &Context) -> Context {
        let declared = context.scopes.iter().position(|scope| {
            scope
                .imports
                .iter()
                .any(|import| matches!(import, Import::Alias { name: alias, .. } if alias == name))
        });
        let Some(at) = declared else {
            return context.clone();
        };
        let mut scopes = context.scopes[at..].to_vec();
        scopes[0].imports.clear();
        Context {
            tree: context.tree,
            scopes,
        }
    }

    /// Looks a name up through the scope chain.
    #[must_use]
    pub fn lookup_resolution(
        &self,
        name: &str,
        arity: usize,
        context: &Context,
    ) -> Option<Resolution> {
        let symbols = self.compilation.symbols();

        for scope in &context.scopes {
            // Type parameters of the enclosing method, then of the enclosing
            // type: `T` inside `void M<T>()` is the method's.
            if arity == 0 {
                for owner in [scope.member, scope.ty].into_iter().flatten() {
                    if let Some(found) = symbols
                        .lookup(owner, name)
                        .iter()
                        .copied()
                        .find(|id| symbols.get(*id).kind == SymbolKind::TypeParameter)
                    {
                        return Some(Resolution::Symbol(found));
                    }
                }
            }

            // Nested types, including ones inherited from a base type.
            if let Some(ty) = scope.ty
                && let Some(found) = self.lookup_type_in_hierarchy(ty, name, arity, 0)
            {
                return Some(Resolution::Symbol(found));
            }

            if let Some(namespace) = scope.namespace {
                if let Some(found) =
                    self.compilation
                        .lookup_type_from(namespace, name, arity, context.tree)
                {
                    return Some(Resolution::Symbol(found));
                }
                if arity == 0
                    && let Some(found) = symbols.lookup_namespace(namespace, name)
                    && self.compilation.sees_namespace(found, context.tree)
                {
                    return Some(Resolution::Symbol(found));
                }
            }

            // `using` directives of this scope, which are consulted after its
            // own declarations and before the enclosing scope's. An alias is
            // asked before the namespaces imported beside it (§7.8.1): `using
            // AnalyzerOptions = ImmutableDictionary<string, string>;` wins
            // over the `AnalyzerOptions` class that `using
            // Microsoft.CodeAnalysis.Diagnostics;` would bring in.
            if arity == 0
                && let Some(target) = scope.imports.iter().find_map(|import| match import {
                    Import::Alias {
                        name: alias,
                        target,
                    } if alias == name => Some(target.clone()),
                    _ => None,
                })
            {
                return Some(Resolution::AliasTo(target));
            }
            for import in &scope.imports {
                match import {
                    Import::Namespace(namespace) => {
                        if let Some(found) =
                            self.compilation
                                .lookup_type_from(*namespace, name, arity, context.tree)
                        {
                            return Some(Resolution::Symbol(found));
                        }
                    }
                    // `using static C;` brings in the types nested in C too.
                    Import::Static(ty) => {
                        if let Some(found) = self.lookup_type_in_hierarchy(*ty, name, arity, 0) {
                            return Some(Resolution::Symbol(found));
                        }
                    }
                    Import::Alias { .. } => {}
                }
            }
        }

        // `extern alias A;` names the root namespace of the reference given
        // that alias, after everything declared under the same name: `using
        // A;` imports what that reference declares globally.
        if arity == 0
            && let Some(root) = self.compilation.extern_alias(name)
        {
            return Some(Resolution::Symbol(root));
        }
        None
    }

    /// Cuts an overload set down the way §12.6.4.5 does.
    ///
    /// An `override` is not a candidate: the declaration it overrides stands
    /// in for it, and the call is virtual anyway, so dispatch finds the
    /// override at run time. And once a type contributes a method of its own,
    /// the ones its bases declare are out — which is what makes
    /// `CSharpCompilation.GetSpecialType(ExtendedSpecialType)` win over
    /// `Compilation.GetSpecialType(SpecialType)` for a call that could reach
    /// either.
    #[must_use]
    pub fn reduce_overloads(&self, candidates: Vec<SymbolId>) -> Vec<SymbolId> {
        if candidates.len() < 2 {
            return candidates;
        }
        let symbols = self.compilation.symbols();
        let kept: Vec<SymbolId> = candidates
            .iter()
            .copied()
            .filter(|id| !symbols.get(*id).modifiers.contains(Modifiers::OVERRIDE))
            .collect();
        // An override with nothing behind it — which happens where the base is
        // a type this compilation does not have — is better than nothing.
        let kept = if kept.is_empty() { candidates } else { kept };

        // The containers, nearest first: the list was built that way.
        let mut containers: Vec<SymbolId> = Vec::new();
        for id in &kept {
            if let Some(container) = symbols.get(*id).container
                && !containers.contains(&container)
            {
                containers.push(container);
            }
        }
        let Some(nearest) = containers.first().copied() else {
            return kept;
        };
        if containers.len() < 2 {
            return kept;
        }
        // Only the ones a base of the nearest declares are dropped; an
        // interface the nearest also implements is not a base of it in the
        // sense that matters here, and its members stay.
        // By definition: `Base2<A> : Base<A>` derives from `Base`, whatever
        // either is constructed with.
        let shadowed: Vec<SymbolId> = containers
            .into_iter()
            .skip(1)
            .filter(|container| {
                symbols.get(*container).type_kind() != Some(crate::symbol::TypeKind::Interface)
                    && self.derives_from_definition(nearest, *container, 0)
            })
            .collect();
        if shadowed.is_empty() {
            return kept;
        }
        kept.into_iter()
            .filter(|id| {
                symbols
                    .get(*id)
                    .container
                    .is_none_or(|container| !shadowed.contains(&container))
            })
            .collect()
    }

    /// Whether `derived`'s definition has `base`'s among the types it
    /// inherits from.
    pub(crate) fn derives_from_definition(
        &self,
        derived: SymbolId,
        base: SymbolId,
        depth: usize,
    ) -> bool {
        if derived == base {
            return true;
        }
        depth < 16
            && self
                .direct_bases(&Type::named(derived))
                .iter()
                .filter_map(Type::symbol)
                .any(|symbol| self.derives_from_definition(symbol, base, depth + 1))
    }

    /// A static member a `using static` brought into scope.
    ///
    /// `using static BinaryOperatorKind;` makes `LessThan` mean
    /// `BinaryOperatorKind.LessThan` with nothing written in front of it —
    /// which is what a `switch` over an enum in Roslyn's value-set code is
    /// made of.
    #[must_use]
    pub fn static_import(&self, context: &Context, name: &str) -> Option<SymbolId> {
        self.static_imports(context, name).into_iter().next()
    }

    /// All of them, which is what an overload set needs.
    #[must_use]
    pub fn static_imports(&self, context: &Context, name: &str) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let mut found = Vec::new();
        for scope in &context.scopes {
            for import in &scope.imports {
                let Import::Static(ty) = import else {
                    continue;
                };
                found.extend(
                    self.lookup_member(*ty, name)
                        .into_iter()
                        .filter(|id| symbols.get(*id).modifiers.contains(Modifiers::STATIC)),
                );
            }
        }
        found
    }

    /// The extension methods called `name` that this piece of syntax can see.
    ///
    /// A member is found on the type of the receiver; an extension method is
    /// found the other way round — by name, among the static classes the file
    /// imported — and only then checked against the receiver. That is why
    /// `using System.Linq;` is what makes `Where` exist.
    #[must_use]
    pub fn extensions_in_scope(&self, context: &Context, name: &str) -> Vec<SymbolId> {
        self.visible_extensions(context, self.compilation.extension_methods(name))
    }

    /// The members of extension blocks (C# 14) called `name` that `using`s
    /// and namespaces bring into scope here: properties, indexers (by
    /// `this[]`) and static methods, which no `this` parameter marks.
    #[must_use]
    pub fn extension_members_in_scope(&self, context: &Context, name: &str) -> Vec<SymbolId> {
        self.visible_extensions(context, self.compilation.extension_members(name))
    }

    /// The extension methods called `name` in scope, a set per place they
    /// are looked for, nearest first (§12.8.10.3): at each enclosing
    /// namespace, the ones its own classes declare, and then the ones its
    /// `using`s import. The first set with an applicable method decides.
    #[must_use]
    pub fn extension_levels(&self, context: &Context, name: &str) -> Vec<Vec<SymbolId>> {
        let all = self.compilation.extension_methods(name);
        if all.is_empty() {
            return Vec::new();
        }
        let symbols = self.compilation.symbols();
        let namespace_of = |method: &SymbolId| {
            symbols
                .get(*method)
                .container
                .and_then(|container| symbols.get(container).container)
        };
        let mut seen: Vec<SymbolId> = Vec::new();
        let mut levels = Vec::new();
        for scope in &context.scopes {
            let own: Vec<SymbolId> = all
                .iter()
                .copied()
                .filter(|method| {
                    scope.namespace.is_some() && namespace_of(method) == scope.namespace
                })
                .filter(|method| !seen.contains(method))
                .collect();
            seen.extend(&own);
            levels.push(own);
            let mut namespaces: Vec<SymbolId> = Vec::new();
            let mut classes: Vec<SymbolId> = Vec::new();
            for import in &scope.imports {
                match import {
                    Import::Namespace(namespace) => namespaces.push(*namespace),
                    Import::Static(ty) => classes.push(*ty),
                    Import::Alias { .. } => {}
                }
            }
            let imported: Vec<SymbolId> = all
                .iter()
                .copied()
                .filter(|method| {
                    symbols
                        .get(*method)
                        .container
                        .is_some_and(|container| classes.contains(&container))
                        || namespace_of(method).is_some_and(|ns| namespaces.contains(&ns))
                })
                .filter(|method| !seen.contains(method))
                .collect();
            seen.extend(&imported);
            levels.push(imported);
        }
        levels.retain(|level| !level.is_empty());
        levels
    }

    /// How far out the place is that brings an extension member into view,
    /// counted as [`extension_levels`](Self::extension_levels) lists them: a
    /// smaller number is nearer. A property of an extension block and a
    /// method of another static class in the same place are equally near,
    /// which Roslyn calls ambiguous; a nearer one wins outright.
    #[must_use]
    pub fn extension_level(&self, context: &Context, member: SymbolId) -> Option<usize> {
        let symbols = self.compilation.symbols();
        let container = symbols.get(member).container?;
        let namespace = symbols.get(container).container;
        context.scopes.iter().enumerate().find_map(|(at, scope)| {
            if scope.namespace.is_some() && namespace == scope.namespace {
                return Some(at * 2);
            }
            scope
                .imports
                .iter()
                .any(|import| match import {
                    Import::Namespace(imported) => Some(*imported) == namespace,
                    Import::Static(ty) => *ty == container,
                    Import::Alias { .. } => false,
                })
                .then_some(at * 2 + 1)
        })
    }

    fn visible_extensions(&self, context: &Context, all: &[SymbolId]) -> Vec<SymbolId> {
        if all.is_empty() {
            return Vec::new();
        }
        let symbols = self.compilation.symbols();
        let mut found: Vec<SymbolId> = Vec::new();
        for scope in &context.scopes {
            let mut namespaces: Vec<SymbolId> = scope.namespace.into_iter().collect();
            let mut classes: Vec<SymbolId> = Vec::new();
            for import in &scope.imports {
                match import {
                    Import::Namespace(namespace) => namespaces.push(*namespace),
                    // `using static Enumerable;` brings in its extension
                    // methods as well as its ordinary statics.
                    Import::Static(ty) => classes.push(*ty),
                    Import::Alias { .. } => {}
                }
            }
            for method in all {
                let Some(container) = symbols.get(*method).container else {
                    continue;
                };
                let visible = classes.contains(&container)
                    || symbols
                        .get(container)
                        .container
                        .is_some_and(|namespace| namespaces.contains(&namespace));
                if visible && !found.contains(method) {
                    found.push(*method);
                }
            }
        }
        found
    }

    /// Looks for a nested type on `ty` or anything it inherits from.
    pub(crate) fn lookup_type_in_hierarchy(
        &self,
        ty: SymbolId,
        name: &str,
        arity: usize,
        depth: usize,
    ) -> Option<SymbolId> {
        self.lookup_type_in_hierarchy_from(ty, name, arity, depth, &mut Vec::new())
    }

    /// `visited`: the types looked in already. A type reached again — through
    /// a diamond, or round a circle of bases in broken code — held nothing
    /// the first time, or the search would have stopped there; walking it
    /// again only multiplied the paths (see `collect_members`).
    fn lookup_type_in_hierarchy_from(
        &self,
        ty: SymbolId,
        name: &str,
        arity: usize,
        depth: usize,
        visited: &mut Vec<SymbolId>,
    ) -> Option<SymbolId> {
        // Base types can be circular in broken code; stop rather than hang.
        if depth > 16 || visited.contains(&ty) {
            return None;
        }
        visited.push(ty);
        let symbols = self.compilation.symbols();
        // A base's private type is not there for a derived class, and hides
        // nothing (§12.5): `Styles` in a `MarkerInspector` subclass is the
        // namespace's, not the base's own `private static class Styles`.
        if let Some(found) = symbols.lookup_type(ty, name, arity)
            && (depth == 0
                || symbols.get(found).accessibility != crate::symbol::Accessibility::Private)
        {
            return Some(found);
        }
        for base in self.base_types_of(ty) {
            if let Some(symbol) = base.symbol()
                && let Some(found) =
                    self.lookup_type_in_hierarchy_from(symbol, name, arity, depth + 1, visited)
            {
                return Some(found);
            }
        }
        None
    }

    /// Looks a member up on a type and everything it inherits from.
    #[must_use]
    pub fn lookup_member(&self, ty: SymbolId, name: &str) -> Vec<SymbolId> {
        self.lookup_member_where(ty, name, &|_| true)
    }

    /// The same, seeing only the members `visible` accepts: a member the
    /// code looking cannot access hides nothing (§12.5), so `base.P` past a
    /// `private new P` of the class in between is the one further up.
    #[must_use]
    pub fn lookup_member_where(
        &self,
        ty: SymbolId,
        name: &str,
        visible: &dyn Fn(SymbolId) -> bool,
    ) -> Vec<SymbolId> {
        let mut found = Vec::new();
        self.collect_members(ty, name, 0, visible, &mut found, &mut Vec::new());
        // On a type parameter, what `object` declares is hidden by what its
        // interface constraints declare (§12.5): `u.ToString()` where `U :
        // C, IGoo` and `IGoo` declares `ToString` calls the interface's,
        // even where `C` overrides `object`'s.
        let symbols = self.compilation.symbols();
        if symbols.get(ty).kind == SymbolKind::TypeParameter && found.len() > 1 {
            let object = self.compilation.special_type(crate::SpecialType::Object);
            let interface_members: Vec<SymbolId> = found
                .iter()
                .copied()
                .filter(|member| {
                    symbols.get(*member).container.is_some_and(|container| {
                        symbols.get(container).type_kind() == Some(crate::TypeKind::Interface)
                    })
                })
                .collect();
            let mut sink = crate::Diagnostics::new();
            let mut parameters = |member: SymbolId| -> Vec<Type> {
                symbols
                    .get(member)
                    .as_method()
                    .map(|detail| {
                        detail
                            .parameters
                            .iter()
                            .map(|parameter| self.type_of(*parameter, &mut sink))
                            .collect()
                    })
                    .unwrap_or_default()
            };
            let interface_shapes: Vec<Vec<Type>> = interface_members
                .iter()
                .map(|member| parameters(*member))
                .collect();
            let root_is_object = |member: SymbolId| {
                let symbol = symbols.get(member);
                symbol.kind == SymbolKind::Method
                    && (symbol.container == object
                        || (symbol.modifiers.contains(Modifiers::OVERRIDE)
                            && object.is_some_and(|object| {
                                symbols
                                    .lookup(object, &symbol.name)
                                    .iter()
                                    .any(|base| symbols.get(*base).kind == SymbolKind::Method)
                            })))
            };
            if !interface_shapes.is_empty() {
                found.retain(|member| {
                    !root_is_object(*member) || !interface_shapes.contains(&parameters(*member))
                });
            }
        }
        found
    }

    /// `visited` is every type looked in already. Through a diamond — `I4 :
    /// I2, I1` with `I2 : I1` — a base is reached twice, and in code being
    /// edited the bases can go round in a circle (`I2 : I4` in one file, `I4
    /// : I2` in another); without it every path was walked to the depth
    /// limit, three bases a level made that millions of lookups for one
    /// operator, and a rename never came back (found by fuzzing,
    /// `examples/fuzz.rs` in rustlyn-ide). The first visit is the nearest in
    /// the order members come back, so nothing but repeats is lost.
    fn collect_members(
        &self,
        ty: SymbolId,
        name: &str,
        depth: usize,
        visible: &dyn Fn(SymbolId) -> bool,
        found: &mut Vec<SymbolId>,
        visited: &mut Vec<SymbolId>,
    ) {
        if depth > 16 || visited.contains(&ty) {
            return;
        }
        visited.push(ty);
        let symbols = self.compilation.symbols();
        let here = symbols.lookup(ty, name);
        found.extend(here.iter().copied().filter(|member| visible(*member)));
        // A field or a property declared closer wins outright: there is one of
        // it, and the nearer one hides the rest. Methods do not work that way
        // — a derived type that overrides two of forty overloads does not hide
        // the other thirty-eight — so the search keeps going and the whole set
        // comes back, nearest first.
        // An indexer is overloaded by its parameters the way a method is:
        // `this[string]` on a keyed collection leaves the `this[int]` of the
        // collection under it reachable.
        if found
            .iter()
            .any(|id| symbols.get(*id).kind != SymbolKind::Method && name != "this[]")
        {
            return;
        }
        // The bases a declaration wrote, and the one it did not: every enum
        // has `ToString`, every struct has `Equals`, and no source in the
        // world says so.
        // §12.5: what a class has comes from its base classes. An interface
        // it implements says what it must have, not what it has: the member
        // answering `Cci.INamespace.ContainingNamespace` is a member of that
        // interface and not of the class, and finding it here types
        // `symbol.ContainingNamespace` as the interface's.
        // A type parameter is the other way round: what it has is what its
        // constraints promise, interfaces and all.
        let concrete = symbols
            .get(ty)
            .type_kind()
            .is_some_and(|kind| kind != crate::TypeKind::Interface);
        let mut bases = self.direct_bases(&Type::named(ty));
        // On a type parameter the members of its effective base class come
        // before those of its interfaces (§12.5), whichever constraint was
        // written first: `T6 : T1, T2` with `T1 : I` and `T2 : A` reaches
        // `A.M` over `I.M`.
        if symbols.get(ty).kind == SymbolKind::TypeParameter {
            bases.sort_by_key(|base| !self.leads_to_a_class(base, 0));
        }
        for base in bases {
            let Some(symbol) = base.symbol() else {
                continue;
            };
            if concrete && symbols.get(symbol).type_kind() == Some(crate::TypeKind::Interface) {
                continue;
            }
            self.collect_members(symbol, name, depth + 1, visible, found, visited);
            if found
                .iter()
                .any(|id| symbols.get(*id).kind != SymbolKind::Method)
            {
                return;
            }
        }
    }

    /// Whether a type parameter is known to be a reference type: `where T :
    /// class`, or a class constraint however indirect (`System.Enum` and
    /// `System.ValueType` allow value types, and say nothing).
    #[must_use]
    pub fn is_reference_type_parameter(&self, parameter: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        if symbols
            .get(parameter)
            .as_type_parameter()
            .is_some_and(|detail| detail.reference_type)
        {
            return true;
        }
        self.direct_bases(&Type::TypeParameter(parameter))
            .iter()
            .any(|base| match base {
                Type::TypeParameter(inner) if *inner != parameter => {
                    self.is_reference_type_parameter(*inner)
                }
                Type::Named { symbol, .. } => {
                    let name = symbols.qualified_name(*symbol);
                    name != "System.Enum"
                        && name != "System.ValueType"
                        && self.leads_to_a_class(base, 0)
                }
                _ => false,
            })
    }

    /// Whether a constraint is a class, or a type parameter constrained,
    /// however indirectly, to one.
    fn leads_to_a_class(&self, ty: &Type, depth: usize) -> bool {
        let Some(symbol) = ty.symbol() else {
            return false;
        };
        let symbols = self.compilation.symbols();
        if symbols.get(symbol).kind != SymbolKind::TypeParameter {
            // Every type parameter has `object` behind it, which is no class
            // constraint.
            return symbols.get(symbol).type_kind() != Some(crate::TypeKind::Interface)
                && self.compilation.special_type(crate::SpecialType::Object) != Some(symbol);
        }
        depth < 8
            && self
                .direct_bases(ty)
                .iter()
                .any(|base| self.leads_to_a_class(base, depth + 1))
    }

    // -- type resolution ---------------------------------------------------

    /// The class a type derives from, which is what `base` names.
    ///
    /// The list after the `:` holds interfaces too, and `BoundCall :
    /// BoundExpression, IBoundInvalidNode` chains its constructor to the
    /// first of those and reads `base.Type` off it — never off the interface
    /// beside it. A type that lists no class has `object` behind it, which
    /// is where `base.ToString()` goes.
    #[must_use]
    pub fn base_class_of(&self, ty: SymbolId) -> Option<Type> {
        let symbols = self.compilation.symbols();
        self.base_types_of(ty)
            .into_iter()
            .find(|base| {
                base.symbol().is_none_or(|symbol| {
                    symbols.get(symbol).type_kind() != Some(crate::TypeKind::Interface)
                })
            })
            .or_else(|| {
                // A struct derives from `ValueType` and an enum from `Enum`,
                // which neither writes: `base.Equals(other)` in a struct is
                // `ValueType.Equals`, and it is what compares the fields.
                let implicit = match symbols.get(ty).type_kind() {
                    Some(crate::TypeKind::Struct | crate::TypeKind::RecordStruct) => {
                        self.compilation.type_by_metadata_name("System.ValueType")
                    }
                    Some(crate::TypeKind::Enum) => {
                        self.compilation.type_by_metadata_name("System.Enum")
                    }
                    _ => None,
                };
                implicit
                    .or_else(|| self.compilation.special_type(SpecialType::Object))
                    .filter(|object| *object != ty)
                    .map(Type::named)
            })
    }

    /// The types a type declaration lists after its `:`.
    #[must_use]
    pub fn base_types_of(&self, ty: SymbolId) -> Vec<Type> {
        if let Some(bases) = self.compilation.metadata_bases(ty) {
            return bases.to_vec();
        }
        // Either the answer, or — for a type already on the stack — an empty
        // list, which breaks the cycle without breaking the lookup.
        if let Some(answer) = self.compilation.cached_base_types(ty) {
            return answer;
        }

        // A type parameter's "base types" are its constraints: `where T :
        // IShape` is the only reason `item.Area()` resolves on a `T`. An
        // override writes none and has the overridden method's.
        let symbol = self.compilation.symbols().get(ty);
        let refs = match &symbol.detail {
            Detail::NamedType(detail) => detail.base_types.clone(),
            Detail::TypeParameter(detail) if detail.constraints.is_empty() => {
                if let Some((overridden, substitution)) = self.overridden_type_parameter_mapped(ty)
                {
                    // In the override's terms: `A<S>.Goo<S2>() where S2 : T`
                    // is `where S2 : S` in `B : A<S>`.
                    let inherited: Vec<Type> = self
                        .base_types_of(overridden)
                        .iter()
                        .map(|base| base.substitute(&substitution))
                        .collect();
                    self.compilation.cache_base_types(ty, inherited.clone());
                    return inherited;
                }
                Vec::new()
            }
            Detail::TypeParameter(detail) => detail.constraints.clone(),
            _ => Vec::new(),
        };
        let mut sink = Diagnostics::new();
        // Each base once, in the order first written. A type declared in
        // several files — `partial`, or a copy of the same file — lists its
        // bases once per declaration, and every walk up the hierarchy took
        // each copy: three copies of a file whose interfaces go round in a
        // circle made a walk of depth sixteen `3¹⁶` paths (found by fuzzing,
        // `examples/fuzz.rs` in rustlyn-ide).
        let mut resolved: Vec<Type> = Vec::with_capacity(refs.len());
        for reference in &refs {
            let base = self.resolve_type_ref(*reference, &mut sink);
            if !resolved.contains(&base) {
                resolved.push(base);
            }
        }
        // A record implements `IEquatable<R>` without saying so: its
        // `Equals(R)` is that interface's method.
        if matches!(
            symbol.type_kind(),
            Some(crate::symbol::TypeKind::Record | crate::symbol::TypeKind::RecordStruct)
        ) && let Some(equatable) = self
            .compilation
            .type_by_metadata_name("System.IEquatable`1")
        {
            let interface = Type::Named {
                symbol: equatable,
                type_arguments: vec![self.self_type(ty)],
            };
            if !resolved.contains(&interface) {
                resolved.push(interface);
            }
        }

        // A union declaration implements `IUnion`, whose `Value` its own is.
        if symbol
            .as_named_type()
            .is_some_and(|detail| detail.union_declaration)
            && let Some(interface) = self
                .compilation
                .type_by_metadata_name("System.Runtime.CompilerServices.IUnion")
        {
            let interface = Type::Named {
                symbol: interface,
                type_arguments: Vec::new(),
            };
            if !resolved.contains(&interface) {
                resolved.push(interface);
            }
        }

        self.compilation.cache_base_types(ty, resolved.clone());
        resolved
    }

    /// Whether a type parameter is held to a value type: by its own `where T
    /// : struct`, or, for an override that may not restate constraints, by
    /// that of the method it overrides.
    #[must_use]
    pub fn is_struct_constrained(&self, ty: SymbolId) -> bool {
        let mut current = ty;
        for _ in 0..32 {
            if self
                .compilation
                .symbols()
                .get(current)
                .as_type_parameter()
                .is_some_and(|detail| detail.value_type)
            {
                return true;
            }
            match self.overridden_type_parameter(current) {
                Some(next) => current = next,
                None => return false,
            }
        }
        false
    }

    /// The type parameter an override's type parameter stands in for.
    ///
    /// `public override SyntaxList<TNode> VisitList<TNode>(SyntaxList<TNode>
    /// list)` may not restate `where TNode : SyntaxNode`; the constraint is
    /// the overridden method's, found by name and shape in the class the
    /// override's type derives from.
    #[must_use]
    pub fn overridden_type_parameter(&self, ty: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let method = symbols.get(ty).container?;
        let detail = symbols.get(method).as_method()?;
        if !symbols.get(method).modifiers.contains(Modifiers::OVERRIDE) {
            return None;
        }
        let index = detail
            .type_parameters
            .iter()
            .position(|parameter| *parameter == ty)?;
        let (arity, parameters) = (detail.type_parameters.len(), detail.parameters.len());
        let name = symbols.get(method).name.clone();
        let mut base = self.base_class_of(symbols.get(method).container?);
        let mut depth = 0;
        while let Some(current) = base.as_ref().and_then(Type::symbol) {
            if depth > 32 {
                break;
            }
            let found = symbols
                .lookup(current, &name)
                .iter()
                .copied()
                .filter_map(|candidate| symbols.get(candidate).as_method())
                .find(|candidate| {
                    candidate.type_parameters.len() == arity
                        && candidate.parameters.len() == parameters
                })
                .and_then(|candidate| candidate.type_parameters.get(index).copied());
            if found.is_some() {
                return found;
            }
            base = self.base_class_of(current);
            depth += 1;
        }
        None
    }

    /// The same, with what turns the overridden method's constraints into
    /// the override's: the base class's arguments for its type's
    /// parameters, and the override's own type parameters for the
    /// overridden method's.
    fn overridden_type_parameter_mapped(
        &self,
        ty: SymbolId,
    ) -> Option<(SymbolId, std::collections::HashMap<SymbolId, Type>)> {
        let symbols = self.compilation.symbols();
        let method = symbols.get(ty).container?;
        let detail = symbols.get(method).as_method()?;
        let index = detail
            .type_parameters
            .iter()
            .position(|parameter| *parameter == ty)?;
        let own = detail.type_parameters.clone();
        let (arity, parameters) = (own.len(), detail.parameters.len());
        let name = symbols.get(method).name.clone();
        // An explicit implementation writes no constraints either, and has
        // the interface method's: `void IVisitor.Visit<TList, TElement>()`
        // reads `TList` as the `IList<TElement>` the interface says.
        if let Some((_, short)) = name.rsplit_once('.')
            && let Some(interface) = self.explicit_interface(method)
            && let Some(interface_symbol) = interface.symbol()
        {
            let found = symbols
                .lookup(interface_symbol, short)
                .iter()
                .copied()
                .filter_map(|candidate| symbols.get(candidate).as_method())
                .find(|candidate| {
                    candidate.type_parameters.len() == arity
                        && candidate.parameters.len() == parameters
                })?;
            let overridden = found.type_parameters.get(index).copied()?;
            let mut map = self.type_substitution(&interface);
            for (theirs, mine) in found.type_parameters.iter().zip(&own) {
                map.insert(*theirs, Type::TypeParameter(*mine));
            }
            return Some((overridden, map));
        }
        if !symbols.get(method).modifiers.contains(Modifiers::OVERRIDE) {
            return None;
        }
        let mut base = self.base_class_of(symbols.get(method).container?);
        let mut depth = 0;
        while let Some(current_type) = base.clone() {
            let Some(current) = current_type.symbol() else {
                break;
            };
            if depth > 32 {
                break;
            }
            let substitution = self.type_substitution(&current_type);
            let found = symbols
                .lookup(current, &name)
                .iter()
                .copied()
                .filter_map(|candidate| symbols.get(candidate).as_method())
                .find(|candidate| {
                    candidate.type_parameters.len() == arity
                        && candidate.parameters.len() == parameters
                });
            if let Some(found) = found
                && let Some(overridden) = found.type_parameters.get(index).copied()
            {
                let mut map = substitution;
                for (theirs, mine) in found.type_parameters.iter().zip(&own) {
                    map.insert(*theirs, Type::TypeParameter(*mine));
                }
                return Some((overridden, map));
            }
            base = self
                .base_class_of(current)
                .map(|next| next.substitute(&substitution));
            depth += 1;
        }
        None
    }

    /// Resolves type syntax recorded during the declaration pass.
    #[must_use]
    pub fn resolve_type_ref(
        &self,
        reference: TypeSyntaxRef,
        diagnostics: &mut Diagnostics,
    ) -> Type {
        // A member read from metadata has the type its assembly gave it, and
        // no syntax to resolve.
        if let Some(symbol) = reference.loaded_symbol() {
            return self
                .compilation
                .loaded_extended(symbol)
                .cloned()
                .unwrap_or(Type::Error);
        }
        let location = reference.0;
        let Some(node) = self.node_at(location.tree, location.span) else {
            return Type::Error;
        };
        let context = self.context_at(location.tree, &node);
        self.resolve_type(&node, &context, diagnostics)
    }

    /// The node at an exact span, which is how a symbol gets back to its
    /// syntax.
    #[must_use]
    pub fn node_at(&self, tree: usize, span: TextSpan) -> Option<SyntaxNode> {
        self.compilation.trees().get(tree)?.root().find_node(span)
    }

    /// The interface a member names in front of itself, where it names one.
    ///
    /// `string IFormattable.ToString(...)` is an explicit implementation: the
    /// member is reachable only through `IFormattable`, and the interface has
    /// to be resolved from the syntax, the way any type is — `Type.Method`
    /// under `using Type = Interface;` implements `Interface.Method`, which
    /// the name alone does not say.
    #[must_use]
    pub fn explicit_interface(&self, member: SymbolId) -> Option<Type> {
        let (tree, span) = *self.compilation.declaration_nodes(member).first()?;
        let node = self.node_at(tree, span)?;
        let specifier = node.child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier)?;
        let name = specifier.children().next()?;
        // In the type's terms, not the method's: `void I<X>.M<X>()` in
        // `D<X>` implements `I` of the class's `X`.
        let scope = node.parent().cloned().unwrap_or_else(|| node.clone());
        let context = self.context_at(tree, &scope);
        let mut sink = Diagnostics::new();
        match self.resolve_type(&name, &context, &mut sink) {
            Type::Error => None,
            ty => Some(ty),
        }
    }

    /// Binds an attribute written on a declaration: which constructor of
    /// which attribute class it calls, with what, and what it sets by name.
    #[must_use]
    pub fn bind_attribute(
        &self,
        tree: usize,
        declaration: &SyntaxNode,
        attribute: &SyntaxNode,
    ) -> Option<BoundAttribute> {
        crate::body::BodyBinder::bind_attribute(self, tree, declaration, attribute)
    }

    /// The element type and length of an inline array type (C# 12): a
    /// struct with one instance field and `[InlineArray(n)]` on it, which
    /// the runtime lays out as `n` of that field. `None` for anything else.
    #[must_use]
    pub fn inline_array_of(&self, ty: &Type) -> Option<(Type, i32)> {
        let symbol = ty.symbol()?;
        let symbols = self.compilation.symbols();
        if symbols.get(symbol).type_kind() != Some(crate::TypeKind::Struct) {
            return None;
        }
        let fields: Vec<SymbolId> = symbols
            .get(symbol)
            .members
            .iter()
            .copied()
            .filter(|member| {
                let candidate = symbols.get(*member);
                candidate.kind == SymbolKind::Field
                    && !candidate.modifiers.contains(Modifiers::STATIC)
                    && !candidate.modifiers.contains(Modifiers::CONST)
            })
            .collect();
        let [field] = fields[..] else {
            return None;
        };
        let length = self
            .compilation
            .declaration_nodes(symbol)
            .iter()
            .filter_map(|(tree, span)| self.compilation.trees().get(*tree)?.root().find_node(*span))
            .find_map(|node| inline_array_length(&node))?;
        let mut sink = Diagnostics::new();
        let element = self
            .type_of(field, &mut sink)
            .substitute(&self.type_substitution(ty));
        Some((element, length))
    }

    /// The symbols a `[Conditional("...")]` on a method names, if any.
    ///
    /// A call to such a method is kept only where one of them is defined.
    /// Everything about it is decided here rather than at the call: the
    /// attribute is on the declaration, and a declaration out of a referenced
    /// assembly has no syntax to read it from.
    #[must_use]
    pub fn conditional_symbols(&self, method: SymbolId) -> Option<Vec<String>> {
        if let Some(found) = self.compilation.metadata_conditions(method) {
            return Some(found.to_vec());
        }
        let node = self.compilation.declaration_node(method)?;
        let mut found = Vec::new();
        for list in node.children() {
            if list.kind() != SyntaxKind::AttributeList {
                continue;
            }
            for attribute in list.children() {
                if attribute.kind() != SyntaxKind::Attribute {
                    continue;
                }
                let Some(name) = attribute.children().next() else {
                    continue;
                };
                let name = name.text();
                let name = name.trim().rsplit('.').next().unwrap_or_default();
                if name != "Conditional" && name != "ConditionalAttribute" {
                    continue;
                }
                // The one argument is a string literal, which is all a
                // `[Conditional]` ever takes.
                for argument in attribute
                    .child_of_kind(SyntaxKind::AttributeArgumentList)
                    .into_iter()
                    .flat_map(|list| list.children())
                {
                    if let Some(text) = string_literal_text(&argument) {
                        found.push(text);
                    }
                }
            }
        }
        (!found.is_empty()).then_some(found)
    }

    /// The name an indexer has in metadata: what an `[IndexerName("...")]`
    /// on its declaration says, and `Item` otherwise.
    #[must_use]
    pub fn indexer_metadata_name(&self, indexer: SymbolId) -> String {
        let Some(&(tree, span)) = self.compilation.declaration_nodes(indexer).first() else {
            return "Item".to_string();
        };
        let Some(node) = self
            .compilation
            .trees()
            .get(tree)
            .and_then(|syntax| syntax.root().find_node(span))
        else {
            return "Item".to_string();
        };
        let Some(attribute) = node
            .children()
            .filter(|list| list.kind() == SyntaxKind::AttributeList)
            .flat_map(|list| list.children())
            .filter(|attribute| attribute.kind() == SyntaxKind::Attribute)
            .find(|attribute| {
                attribute.children().next().is_some_and(|name| {
                    matches!(
                        name.text().trim().rsplit(['.', ':']).next(),
                        Some("IndexerName" | "IndexerNameAttribute")
                    )
                })
            })
        else {
            return "Item".to_string();
        };
        let lone_literal = attribute
            .child_of_kind(SyntaxKind::AttributeArgumentList)
            .and_then(|arguments| arguments.child_of_kind(SyntaxKind::AttributeArgument))
            .and_then(|argument| {
                argument
                    .children()
                    .find(|child| child.kind().is_expression())
            })
            .is_some_and(|value| value.kind() == SyntaxKind::StringLiteralExpression);
        if lone_literal
            && let Some(text) = attribute
                .child_of_kind(SyntaxKind::AttributeArgumentList)
                .and_then(|arguments| string_literal_text(&arguments))
        {
            return text;
        }
        // `[IndexerName("_" + nameof(Other))]` is a constant all the same.
        self.bind_attribute(tree, &node, &attribute)
            .and_then(|bound| bound.arguments.first().and_then(|value| self.folded(value)))
            .and_then(|value| match value {
                crate::bound::ConstantValue::String(text) => Some(text),
                _ => None,
            })
            .unwrap_or_else(|| "Item".to_string())
    }

    /// Whether a type declared here is `[ComImport]`: a call to a method of
    /// one may leave out the `ref` on an argument (§12.6.2.? of the COM
    /// interop rules Roslyn keeps), which then goes by a copy's address.
    #[must_use]
    pub fn is_com_import(&self, ty: SymbolId) -> bool {
        if self.compilation.is_from_metadata(ty) {
            return self.compilation.metadata_com_import(ty).is_some();
        }
        self.compilation
            .declaration_nodes(ty)
            .iter()
            .filter_map(|(tree, span)| {
                self.compilation
                    .trees()
                    .get(*tree)
                    .and_then(|tree| tree.root().find_node(*span))
            })
            .any(|node| {
                node.children()
                    .filter(|child| child.kind() == SyntaxKind::AttributeList)
                    .flat_map(|list| list.children())
                    .filter(|child| child.kind() == SyntaxKind::Attribute)
                    .filter_map(|attribute| attribute.children().next())
                    .any(|name| {
                        let name = name.text();
                        matches!(
                            name.trim().rsplit(['.', ':']).next(),
                            Some("ComImport" | "ComImportAttribute")
                        )
                    })
            })
    }

    /// The class `new I()` makes where `I` is a `[ComImport]` interface
    /// with a `[CoClass(typeof(C))]`: `C`, where it is a class and not an
    /// open generic one (Roslyn's `ComImportCoClass`).
    #[must_use]
    pub fn co_class(&self, interface: SymbolId) -> Option<Type> {
        let symbols = self.compilation.symbols();
        if symbols.get(interface).type_kind() != Some(crate::TypeKind::Interface) {
            return None;
        }
        let found = if self.compilation.is_from_metadata(interface) {
            let name = self.compilation.metadata_com_import(interface)??;
            self.type_from_serialized_name(name)?
        } else {
            if !self.is_com_import(interface) {
                return None;
            }
            let mut found = None;
            for (tree, span) in self.compilation.declaration_nodes(interface).to_vec() {
                let Some(node) = self
                    .compilation
                    .trees()
                    .get(tree)
                    .and_then(|tree| tree.root().find_node(span))
                else {
                    continue;
                };
                let attributes = node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::AttributeList)
                    .flat_map(|list| list.children())
                    .filter(|child| child.kind() == SyntaxKind::Attribute);
                for attribute in attributes {
                    let named = attribute.children().next().is_some_and(|name| {
                        matches!(
                            name.text().trim().rsplit(['.', ':']).next(),
                            Some("CoClass" | "CoClassAttribute")
                        )
                    });
                    if !named {
                        continue;
                    }
                    if let Some(bound) = self.bind_attribute(tree, &node, &attribute)
                        && let Some(BoundExpressionKind::TypeOf(ty)) =
                            bound.arguments.first().map(|argument| &argument.kind)
                    {
                        found = Some(ty.clone());
                    }
                }
            }
            found?
        };
        let symbol = found.symbol()?;
        let detail = symbols.get(symbol).as_named_type()?;
        let open = match &found {
            Type::Named { type_arguments, .. } => {
                type_arguments.len() < detail.type_parameters.len()
            }
            _ => true,
        };
        (matches!(detail.type_kind, Some(crate::TypeKind::Class)) && !open).then_some(found)
    }

    /// The type a serialized type name spells (§II.23.3): what a
    /// `System.Type` argument of an attribute is written as, such as
    /// `Outer+Inner` or ``Pair`2[[System.Int32, mscorlib],[System.String,
    /// mscorlib]]``, with the assembly after a comma where it is given.
    #[must_use]
    pub fn type_from_serialized_name(&self, text: &str) -> Option<Type> {
        let (ty, _) = self.serialized_type(text.trim())?;
        Some(ty)
    }

    /// One type of a serialized name, and what is left after it: its own
    /// assembly, or the rest of a list of type arguments.
    fn serialized_type<'t>(&self, text: &'t str) -> Option<(Type, &'t str)> {
        let end = text.find(['[', ']', ',', '*', '&']).unwrap_or(text.len());
        let symbol = self.compilation.type_by_metadata_name(text[..end].trim())?;
        let mut rest = &text[end..];
        let mut type_arguments = Vec::new();
        // `[[A, a],[B, b]]` or `[A,B]`: the arguments, each in brackets of
        // its own where it names its assembly. `[]` and `[,]` are arrays.
        if let Some(inner) = rest.strip_prefix('[')
            && !inner.starts_with(']')
            && !inner.starts_with(',')
        {
            let mut inner = inner;
            loop {
                inner = inner.trim_start();
                let (argument, after) = if let Some(bracketed) = inner.strip_prefix('[') {
                    let (argument, after) = self.serialized_type(bracketed)?;
                    let close = after.find(']')?;
                    (argument, &after[close + 1..])
                } else {
                    self.serialized_type(inner)?
                };
                type_arguments.push(argument);
                let after = after.trim_start();
                if let Some(after) = after.strip_prefix(',') {
                    inner = after;
                } else {
                    rest = after.strip_prefix(']')?;
                    break;
                }
            }
        }
        let mut ty = Type::Named {
            symbol,
            type_arguments,
        };
        loop {
            if let Some(after) = rest.strip_prefix('*') {
                ty = Type::Pointer(Box::new(ty));
                rest = after;
            } else if let Some(after) = rest.strip_prefix('&') {
                ty = Type::ByRef(Box::new(ty));
                rest = after;
            } else if let Some(after) = rest.strip_prefix('[')
                && let Some(close) = after.find(']')
                && after[..close].chars().all(|c| c == ',' || c == '*')
            {
                ty = Type::Array {
                    element: Box::new(ty),
                    rank: after[..close].matches(',').count() + 1,
                };
                rest = &after[close + 1..];
            } else {
                break;
            }
        }
        // The assembly a name gives after a comma is where the type is,
        // and this looks it up by name alone.
        if let Some(assembly) = rest.strip_prefix(',')
            && !assembly.trim_start().starts_with('[')
        {
            let end = assembly.find(']').unwrap_or(assembly.len());
            rest = &assembly[end..];
        }
        Some((ty, rest))
    }

    /// The builder a task-like type names (§15.15.1): the `B` of the
    /// `[AsyncMethodBuilder(typeof(B))]` on it, which an `async` method
    /// returning the type is built with. The `typeof` is resolved where the
    /// attribute was written, and for a type read from an assembly the name
    /// the blob gives is looked up; `typeof(B<>)` names the generic
    /// definition, which the task's own type argument constructs.
    #[must_use]
    pub fn async_method_builder(&self, task: SymbolId) -> Option<SymbolId> {
        self.compilation
            .declaration_nodes(task)
            .iter()
            .find_map(|&(tree, span)| {
                let node = self.compilation.trees().get(tree)?.root().find_node(span)?;
                let written = crate::declare::parameter_attribute(&node, "AsyncMethodBuilder")?
                    .child_of_kind(SyntaxKind::AttributeArgumentList)?
                    .child_of_kind(SyntaxKind::AttributeArgument)?
                    .child_of_kind(SyntaxKind::TypeOfExpression)?
                    .children()
                    .find(|child| child.kind().is_type_node())?;
                let context = self.context_at(tree, &node);
                self.resolve_type(&written, &context, &mut Diagnostics::new())
                    .symbol()
            })
            .or_else(|| {
                let name = self.compilation.metadata_async_method_builder(task)?;
                self.compilation.type_by_metadata_name(name)
            })
    }

    /// Turns type syntax into a type.
    #[must_use]
    pub fn resolve_type(
        &self,
        node: &SyntaxNode,
        context: &Context,
        diagnostics: &mut Diagnostics,
    ) -> Type {
        match node.kind() {
            SyntaxKind::PredefinedType => {
                let Some(token) = node.child_tokens().next() else {
                    return Type::Error;
                };
                let Some(special) = SpecialType::from_keyword(token.kind()) else {
                    return Type::Error;
                };
                if special == SpecialType::Void {
                    return Type::Void;
                }
                self.compilation
                    .special_type(special)
                    .map_or(Type::Error, Type::named)
            }
            SyntaxKind::IdentifierName
            | SyntaxKind::GenericName
            | SyntaxKind::QualifiedName
            | SyntaxKind::AliasQualifiedName => self.resolve_named_type(node, context, diagnostics),
            SyntaxKind::NullableType => {
                let Some(inner) = node.children().next() else {
                    return Type::Error;
                };
                let underlying = self.resolve_type(&inner, context, diagnostics);
                // `string?` is the same type with an annotation this compiler
                // does not track; `int?` is a different type. `T?` is the
                // annotation unless `T` is known to be a value type, and
                // without constraints the annotation is the common case.
                // `T?` is `Nullable<T>` only under `where T : struct`;
                // otherwise it is the annotation, which this does not track.
                let annotation = match &underlying {
                    Type::TypeParameter(symbol) => !self.is_struct_constrained(*symbol),
                    other => other.is_reference_type(self.compilation.symbols()),
                };
                if annotation {
                    return underlying;
                }
                match self.compilation.type_by_metadata_name("System.Nullable`1") {
                    Some(symbol) => Type::Named {
                        symbol,
                        type_arguments: vec![underlying],
                    },
                    None => underlying,
                }
            }
            SyntaxKind::ArrayType => {
                let mut children = node.children();
                let Some(element) = children.next() else {
                    return Type::Error;
                };
                let mut ty = self.resolve_type(&element, context, diagnostics);
                // The leftmost rank is the outermost array, so the type is
                // built from the rightmost inwards: `int[][,]` is a vector of
                // two-dimensional arrays, not a two-dimensional array of
                // vectors (§17.1).
                let ranks: Vec<_> = children
                    .filter(|child| child.kind() == SyntaxKind::ArrayRankSpecifier)
                    .collect();
                for rank in ranks.into_iter().rev() {
                    // The commas are what say how many dimensions there are:
                    // `[,]` writes no sizes at all, and the nodes standing
                    // where they would be are empty.
                    let dimensions = rank
                        .child_tokens()
                        .filter(|token| token.kind() == SyntaxKind::CommaToken)
                        .count()
                        + 1;
                    ty = Type::Array {
                        element: Box::new(ty),
                        rank: dimensions,
                    };
                }
                ty
            }
            SyntaxKind::PointerType => {
                let Some(inner) = node.children().next() else {
                    return Type::Error;
                };
                Type::Pointer(Box::new(self.resolve_type(&inner, context, diagnostics)))
            }
            SyntaxKind::FunctionPointerType => {
                let (convention, modifiers) = function_pointer_convention(node);
                let mut parameters = Vec::new();
                if let Some(list) = node.child_of_kind(SyntaxKind::FunctionPointerParameterList) {
                    for parameter in list
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::FunctionPointerParameter)
                    {
                        let mut kind = RefKind::None;
                        for token in parameter.child_tokens() {
                            kind = match (token.kind(), kind) {
                                (SyntaxKind::RefKeyword, RefKind::None) => RefKind::Ref,
                                (SyntaxKind::OutKeyword, _) => RefKind::Out,
                                (SyntaxKind::InKeyword | SyntaxKind::ReadOnlyKeyword, _) => {
                                    RefKind::In
                                }
                                (_, kind) => kind,
                            };
                        }
                        let ty = parameter
                            .children()
                            .find(|child| child.kind().is_type_node())
                            .map_or(Type::Error, |ty| {
                                self.resolve_type(&ty, context, diagnostics)
                            });
                        parameters.push((kind, ty));
                    }
                }
                // The last is what the method returns, and may be `void`.
                let (returns_ref, returns) =
                    parameters.pop().unwrap_or((RefKind::None, Type::Void));
                Type::FunctionPointer(Box::new(crate::types::FunctionPointer {
                    convention,
                    modifiers,
                    returns,
                    returns_ref,
                    parameters,
                }))
            }
            SyntaxKind::RefType | SyntaxKind::ScopedType => {
                let Some(inner) = node.children().find(|child| child.kind().is_type_node()) else {
                    return Type::Error;
                };
                let ty = self.resolve_type(&inner, context, diagnostics);
                if node.kind() == SyntaxKind::RefType {
                    Type::ByRef(Box::new(ty))
                } else {
                    ty
                }
            }
            SyntaxKind::TupleType => {
                let elements = node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::TupleElement)
                    .map(|element| {
                        let ty = element
                            .children()
                            .find(|child| child.kind().is_type_node())
                            .map_or(Type::Error, |ty| {
                                self.resolve_type(&ty, context, diagnostics)
                            });
                        let name = element
                            .child_tokens()
                            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                            .map(|token| token.value_text().to_string());
                        TupleElement { name, ty }
                    })
                    .collect();
                Type::Tuple(elements)
            }
            _ => Type::Error,
        }
    }

    fn resolve_named_type(
        &self,
        node: &SyntaxNode,
        context: &Context,
        diagnostics: &mut Diagnostics,
    ) -> Type {
        // An alias stands for a whole type, arguments and all.
        if node.kind() == SyntaxKind::IdentifierName
            && let Some(name) = identifier_text(node)
            && let Some(Resolution::AliasTo(target)) = self.lookup_resolution(&name, 0, context)
        {
            return self.resolve_type(&target, &self.alias_context(&name, context), diagnostics);
        }

        // `nint` and `nuint` are spellings of two framework types rather than
        // keywords, and only where nothing else answers to the name. Only a
        // simple name can be one: a dotted name's text is not built to ask.
        let native = match node.kind() {
            SyntaxKind::IdentifierName => match node.text().trim() {
                "nint" => self.compilation.type_by_metadata_name("System.IntPtr"),
                "nuint" => self.compilation.type_by_metadata_name("System.UIntPtr"),
                _ => None,
            },
            _ => None,
        };
        // `dynamic` is a keyword only where no type is called that.
        if node.kind() == SyntaxKind::IdentifierName
            && node.text().trim() == "dynamic"
            && self.resolve_namespace_or_type(node, context).is_none()
        {
            return Type::Dynamic;
        }

        let Some(symbol) = self.resolve_namespace_or_type(node, context).or(native) else {
            // A type the parser had to make up where one was missing has
            // been complained about as a syntax error already.
            let missing = self.unresolved_name(node, context);
            if !missing.span().is_empty() {
                diagnostics.push((context.tree, missing));
            }
            return Type::Error;
        };
        if let Some(ambiguous) = self.same_type_elsewhere(symbol, node, context.tree) {
            diagnostics.push((context.tree, ambiguous));
            return Type::Error;
        }

        if node.kind() == SyntaxKind::QualifiedName {
            self.check_nested_type_access(node, context, diagnostics);
        }

        let symbols = self.compilation.symbols();
        match symbols.get(symbol).kind {
            SymbolKind::TypeParameter => Type::TypeParameter(symbol),
            SymbolKind::NamedType => Type::Named {
                symbol,
                type_arguments: self.resolve_type_arguments(symbol, node, context, diagnostics),
            },
            // A namespace is not a type, but saying so here would report the
            // same mistake twice; the caller knows what it asked for.
            _ => Type::Error,
        }
    }

    /// CS0433, where `found` is one of two referenced assemblies' types of
    /// the same full name: which one the name meant cannot be told, and
    /// taking either makes the other's members fail to convert later on,
    /// with a message naming the same type twice.
    pub fn same_type_elsewhere(
        &self,
        found: SymbolId,
        name: &SyntaxNode,
        tree: usize,
    ) -> Option<Diagnostic> {
        let other = self.compilation.same_type_elsewhere(found, tree)?;
        let first = self.compilation.assembly_of(found)?.to_string();
        let second = self.compilation.assembly_of(other)?.to_string();
        // At the rightmost name, as Roslyn has it: `T` of `global::N.T`.
        let span = match name.kind() {
            SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => name
                .children()
                .nth(1)
                .map_or(name.span(), |right| right.span()),
            _ => name.span(),
        };
        let ty = crate::types::Type::named(found).display(self.compilation.symbols());
        Some(Diagnostic::new(
            ErrorCode::ErrSameFullNameAggAgg,
            span,
            &[&first, &ty, &second],
        ))
    }

    /// CS0122 for each dotted part of a type name that is a nested type the
    /// code here may not name: `Outer.Inner` where `Inner` is private to
    /// `Outer`, or protected and written outside any type derived from it.
    /// The error is at the part itself, as Roslyn has it.
    ///
    /// Only dotted parts are judged. A bare name was found by walking out
    /// through the types around the code, or through a base of one of them,
    /// which is the very thing that makes it accessible.
    fn check_nested_type_access(
        &self,
        node: &SyntaxNode,
        context: &Context,
        diagnostics: &mut Diagnostics,
    ) {
        let symbols = self.compilation.symbols();
        let in_base_list = node
            .ancestors()
            .any(|ancestor| ancestor.kind() == SyntaxKind::BaseList);
        let mut part = node.clone();
        // A long dotted name is not worth the lookups it would take; the
        // parts that matter are the last few.
        for _ in 0..6 {
            if part.kind() != SyntaxKind::QualifiedName {
                return;
            }
            let mut children = part.children();
            let (Some(left), Some(right)) = (children.next(), children.next()) else {
                return;
            };
            if let Some(found) = self.resolve_namespace_or_type(&part, context)
                && symbols.get(found).kind == SymbolKind::NamedType
                && !self.nested_type_accessible(found, context, in_base_list)
            {
                let name = Type::named(found).display(symbols);
                diagnostics.push((
                    context.tree,
                    Diagnostic::new(ErrorCode::ErrBadAccess, right.span(), &[&name]),
                ));
            }
            part = left;
        }
    }

    /// Whether code written in `context` may name the nested type `ty`; true
    /// whenever this cannot tell.
    ///
    /// In the base list of a type its bases are what is being worked out, so
    /// that type is not asked whether it derives from the owner, which would
    /// ask the very question being answered.
    fn nested_type_accessible(&self, ty: SymbolId, context: &Context, in_base_list: bool) -> bool {
        use crate::symbol::Accessibility;
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(ty);
        let Some(owner) = symbol
            .container
            .filter(|owner| symbols.get(*owner).kind == SymbolKind::NamedType)
        else {
            return true;
        };
        if symbols.get(owner).type_kind() == Some(crate::TypeKind::Interface) {
            return true;
        }
        let from_metadata = self.compilation.is_from_metadata(ty);
        let protected = match symbol.accessibility {
            Accessibility::Private => false,
            Accessibility::Protected => true,
            // `private protected` is for the assembly's own derived types,
            // and a friend's; from any other assembly it is for none.
            Accessibility::ProtectedAndInternal => {
                if from_metadata && !self.compilation.befriended_by(ty, context.tree) {
                    return false;
                }
                true
            }
            // Inside the assembly (or a friend's) `protected internal` is
            // internal; from any other it is protected and no more.
            Accessibility::ProtectedOrInternal => {
                if !from_metadata || self.compilation.befriended_by(ty, context.tree) {
                    return true;
                }
                true
            }
            _ => return true,
        };
        let enclosing = context.enclosing_types();
        let inside = enclosing.iter().any(|around| {
            let mut current = Some(*around);
            let mut depth = 0;
            while let Some(id) = current {
                if id == owner || depth > 64 {
                    return true;
                }
                current = symbols
                    .get(id)
                    .container
                    .filter(|outer| symbols.get(*outer).kind == SymbolKind::NamedType);
                depth += 1;
            }
            false
        });
        if inside {
            return true;
        }
        if !protected {
            return false;
        }
        // A protected type is for what derives from its owner; the types
        // around the code are among `enclosing`, each judged by its bases.
        // In a base list the type declared is left out: it is no more
        // derived from its owner for listing the owner beside the name
        // (Roslyn reports `class C : Owner, I<Owner.Prot>`).
        enclosing
            .iter()
            .skip(usize::from(in_base_list))
            .any(|around| {
                let mut current = Some(*around);
                let mut depth = 0;
                while let Some(id) = current {
                    if id == owner || depth > 32 {
                        return true;
                    }
                    current = self.base_class_of(id).and_then(|base| base.symbol());
                    depth += 1;
                }
                false
            })
    }

    /// Says why a type name did not resolve, the way Roslyn words it: the
    /// leftmost part that is missing, and what it was missing from.
    ///
    /// `Nonesuch` is not in scope at all (CS0246); `System.Nonesuch` is not
    /// in a namespace that exists (CS0234); `Outer.Nonesuch` is not in a type
    /// that exists (CS0426); `List<int, int>` names a type that exists with
    /// another number of type arguments (CS0305).
    fn unresolved_name(&self, node: &SyntaxNode, context: &Context) -> Diagnostic {
        // What each dotted part of the name resolves to, worked out once from
        // the left: asking the whole left side again at each part, and then
        // going into it, made a name of `n` parts cost `n²` lookups, and
        // thousands of parts never finished (found by fuzzing,
        // `examples/fuzz.rs` in rustlyn-ide).
        let mut spine = Vec::new();
        let mut part = Some(node.clone());
        while let Some(current) = part.filter(|current| {
            matches!(
                current.kind(),
                SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName
            )
        }) {
            part = current.children().next();
            spine.push(current);
        }
        let mut resolved = std::collections::HashMap::new();
        let mut below: Option<Option<SymbolId>> = None;
        for current in spine.iter().rev() {
            // The innermost part's left side is not dotted; every other part
            // is `left.right` with the left one just resolved.
            let found = match below {
                None => self.resolve_namespace_or_type(current, context),
                Some(container) => container.and_then(|container| {
                    let right = current.children().nth(1)?;
                    self.lookup_in(container, &right, context.tree)
                }),
            };
            resolved.insert(current.span(), found);
            below = Some(found);
        }
        self.unresolved_name_among(node, context, &resolved)
    }

    /// [`Self::unresolved_name`], with what the dotted parts resolve to.
    fn unresolved_name_among(
        &self,
        node: &SyntaxNode,
        context: &Context,
        resolved: &std::collections::HashMap<TextSpan, Option<SymbolId>>,
    ) -> Diagnostic {
        let symbols = self.compilation.symbols();
        let written = |name: &SyntaxNode| {
            let text = identifier_text(name).unwrap_or_else(|| name.text().trim().to_string());
            match name.kind() {
                SyntaxKind::GenericName => {
                    let arity = type_argument_count(name).max(1);
                    format!("{text}<{}>", ",".repeat(arity - 1))
                }
                _ => text,
            }
        };
        match node.kind() {
            SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => {
                let mut children = node.children();
                if let (Some(left), Some(right)) = (children.next(), children.next()) {
                    let global = node.kind() == SyntaxKind::AliasQualifiedName
                        && identifier_text(&left).as_deref() == Some("global");
                    let container = if global {
                        Some(self.compilation.global_namespace())
                    } else {
                        match resolved.get(&left.span()) {
                            Some(known) => *known,
                            None => self.resolve_namespace_or_type(&left, context),
                        }
                    };
                    let Some(container) = container else {
                        return self.unresolved_name_among(&left, context, resolved);
                    };
                    let name = written(&right);
                    return if global {
                        Diagnostic::new(
                            ErrorCode::ErrGlobalSingleTypeNameNotFound,
                            right.span(),
                            &[&name],
                        )
                    } else if symbols.get(container).kind == SymbolKind::Namespace {
                        let namespace = symbols.qualified_name(container);
                        Diagnostic::new(
                            ErrorCode::ErrDottedTypeNameNotFoundInNS,
                            right.span(),
                            &[&name, &namespace],
                        )
                    } else {
                        let ty = crate::types::Type::named(container).display(symbols);
                        Diagnostic::new(
                            ErrorCode::ErrDottedTypeNameNotFoundInAgg,
                            right.span(),
                            &[&name, &ty],
                        )
                    };
                }
            }
            SyntaxKind::GenericName => {
                // The same name with another number of arguments is the
                // type that was meant, written wrong.
                if let Some(text) = identifier_text(node) {
                    let arity = type_argument_count(node);
                    let other = (1..=8)
                        .filter(|candidate| *candidate != arity)
                        .find_map(|candidate| self.lookup(&text, candidate, context))
                        .filter(|found| symbols.get(*found).kind == SymbolKind::NamedType);
                    if let Some(found) = other {
                        let parameters: Vec<String> = symbols
                            .get(found)
                            .as_named_type()
                            .map(|detail| {
                                detail
                                    .type_parameters
                                    .iter()
                                    .map(|parameter| symbols.get(*parameter).name.clone())
                                    .collect()
                            })
                            .unwrap_or_default();
                        let generic = format!("{text}<{}>", parameters.join(", "));
                        return Diagnostic::new(
                            ErrorCode::ErrBadArity,
                            node.span(),
                            &[&generic, "type", &parameters.len().to_string()],
                        );
                    }
                }
            }
            _ => {}
        }
        Diagnostic::new(
            ErrorCode::ErrSingleTypeNameNotFound,
            node.span(),
            &[&written(node)],
        )
    }

    fn resolve_type_arguments(
        &self,
        symbol: SymbolId,
        node: &SyntaxNode,
        context: &Context,
        diagnostics: &mut Diagnostics,
    ) -> Vec<Type> {
        // For `A.B<int>` the arguments are on the right-hand part.
        let generic = match node.kind() {
            SyntaxKind::GenericName => Some(node.clone()),
            SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => node
                .children()
                .last()
                .filter(|child: &SyntaxNode| child.kind() == SyntaxKind::GenericName),
            _ => None,
        };
        let written = generic
            .and_then(|generic| generic.child_of_kind(SyntaxKind::TypeArgumentList))
            .map(|list| self.type_argument_list(&list, context, diagnostics))
            .unwrap_or_default();

        let declared = self
            .compilation
            .symbols()
            .get(symbol)
            .as_named_type()
            .map_or(0, |detail| detail.type_parameters.len());
        if written.len() == declared {
            return written;
        }

        // A type read out of metadata repeats its enclosing type's parameters
        // as its own, and nothing after its name says so: the one argument of
        // `ImmutableArray<T>.Builder` is spelled to the left of the dot. Every
        // list in the dotted name counts, outside in, which is the order the
        // parameters are numbered in.
        let mut all = Vec::new();
        self.collect_type_arguments(node, context, diagnostics, &mut all);
        if all.len() == declared {
            return all;
        }

        let symbols = self.compilation.symbols();

        // `EmbeddedTypesManager.CommonEmbeddedType` names a type nested in a
        // *base* of what is written, and the arguments are the ones that base
        // was constructed with — which nothing in the name says, because the
        // derived type said it once and for all.
        if node.kind() == SyntaxKind::QualifiedName
            && let Some(left) = node.children().next()
            && let Some(container) = symbols.get(symbol).container
            && symbols.get(container).kind == SymbolKind::NamedType
        {
            let mut ignored = Diagnostics::new();
            let outer = self.resolve_type(&left, context, &mut ignored);
            if let Some(Type::Named { type_arguments, .. }) =
                self.constructed_from(&outer, container)
                && type_arguments.len() + written.len() == declared
            {
                let mut all = type_arguments;
                all.extend(written);
                return all;
            }
        }

        // A bare name found on a *base* type rather than an enclosing one:
        // `ILocalState` written inside
        // `ControlFlowPass : AbstractFlowPass<LocalState, LocalFunctionState>`
        // means `AbstractFlowPass<LocalState, LocalFunctionState>.ILocalState`,
        // and the arguments are the ones that base was constructed with. The
        // enclosing-parameter rule below would answer `!0` here, where there
        // is no `!0` to have.
        if let Some(container) = symbols.get(symbol).container
            && symbols.get(container).kind == SymbolKind::NamedType
            && !self.is_enclosed_by(context, container)
            && let Some(Type::Named { type_arguments, .. }) = context
                .enclosing_types()
                .into_iter()
                .find_map(|enclosing| self.constructed_from(&Type::named(enclosing), container))
            && type_arguments.len() + written.len() == declared
        {
            let mut all = type_arguments;
            all.extend(written);
            return all;
        }

        // A bare `Enumerator` written inside `ArrayBuilder<T>` means
        // `ArrayBuilder<T>.Enumerator`, and from anywhere else it cannot be
        // written bare at all — so the ones nothing named are the enclosing
        // type's own, as the very same parameters.
        let inherited: Vec<Type> = symbols
            .get(symbol)
            .as_named_type()
            .map(|detail| {
                detail
                    .type_parameters
                    .iter()
                    .take(declared.saturating_sub(written.len()))
                    .copied()
                    .map(Type::TypeParameter)
                    .collect()
            })
            .unwrap_or_default();
        if inherited.len() + written.len() == declared {
            let mut all = inherited;
            all.extend(written);
            return all;
        }
        written
    }

    /// Whether a type sits, at any depth, inside one of the types the context
    /// is written in.
    ///
    /// That is what decides whether its parameters are in scope: `Enumerator`
    /// inside `ArrayBuilder<T>` can say `T`, and `ILocalState` written from
    /// outside `AbstractFlowPass<..>` cannot.
    fn is_enclosed_by(&self, context: &Context, container: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        context.enclosing_types().into_iter().any(|enclosing| {
            let mut current = Some(enclosing);
            let mut depth = 0;
            while let Some(at) = current {
                if at == container {
                    return true;
                }
                depth += 1;
                if depth > 16 {
                    return false;
                }
                current = symbols.get(at).container;
            }
            false
        })
    }

    /// Every type argument written anywhere in a dotted name, left to right.
    fn collect_type_arguments(
        &self,
        node: &SyntaxNode,
        context: &Context,
        diagnostics: &mut Diagnostics,
        into: &mut Vec<Type>,
    ) {
        match node.kind() {
            SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => {
                for part in node.children() {
                    self.collect_type_arguments(&part, context, diagnostics, into);
                }
            }
            SyntaxKind::GenericName => {
                if let Some(list) = node.child_of_kind(SyntaxKind::TypeArgumentList) {
                    into.extend(self.type_argument_list(&list, context, diagnostics));
                }
            }
            _ => {}
        }
    }

    /// The types one `<...>` names.
    fn type_argument_list(
        &self,
        list: &SyntaxNode,
        context: &Context,
        diagnostics: &mut Diagnostics,
    ) -> Vec<Type> {
        list.children()
            .filter(|child| child.kind().is_type_node())
            .map(|argument| {
                if argument.kind() == SyntaxKind::OmittedTypeArgument {
                    Type::Error
                } else {
                    self.resolve_type(&argument, context, diagnostics)
                }
            })
            .collect()
    }

    // -- symbol types ------------------------------------------------------

    /// The type a type refers to itself as.
    ///
    /// Inside `Box<T>`, `this` is a `Box<T>` and not a `Box`: a generic type
    /// with no arguments is not a type at all, and a signature that says one
    /// names nothing the runtime can load.
    #[must_use]
    pub fn self_type(&self, symbol: SymbolId) -> Type {
        let arguments = self
            .compilation
            .symbols()
            .get(symbol)
            .as_named_type()
            .map(|detail| {
                detail
                    .type_parameters
                    .iter()
                    .copied()
                    .map(Type::TypeParameter)
                    .collect()
            })
            .unwrap_or_default();
        Type::Named {
            symbol,
            type_arguments: arguments,
        }
    }

    /// Whether a property has no accessor bodies and so needs a field.
    ///
    /// `int X { get; set; }` is storage with two methods around it; `int X =>
    /// e;` is a method and nothing else. Which one a property is decides
    /// whether reading it runs code, so both backends have to agree, and the
    /// only way to be sure of that is for both to ask here.
    pub fn is_automatic_property(&self, property: SymbolId) -> bool {
        // A record's `EqualityContract` has a body the language writes:
        // `typeof` the record, and no field.
        if self
            .compilation
            .symbols()
            .get(property)
            .as_property()
            .is_some_and(|detail| {
                detail.synthesized == Some(crate::symbol::SynthesizedType::SystemType)
            })
        {
            return false;
        }
        let Some(node) = self.compilation.declaration_node(property) else {
            return true;
        };
        let Some(list) = node.child_of_kind(SyntaxKind::AccessorList) else {
            // `int X => e;` is expression-bodied, which is a getter with a body.
            return false;
        };
        list.children().all(|accessor| {
            !accessor.children().any(|part| {
                matches!(
                    part.kind(),
                    SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                )
            })
        })
    }

    /// Whether a property was written `int X => e;`.
    #[must_use]
    pub fn declaration_has_arrow_body(&self, property: SymbolId) -> bool {
        self.compilation
            .declaration_node(property)
            .is_some_and(|node| {
                node.child_of_kind(SyntaxKind::ArrowExpressionClause)
                    .is_some()
            })
    }

    /// The type of what a symbol holds: a field's type, a parameter's type, a
    /// method's return type.
    pub fn type_of(&self, symbol: SymbolId, diagnostics: &mut Diagnostics) -> Type {
        // A symbol out of a referenced assembly has no syntax to resolve: its
        // type was worked out when the assembly was read, because that is the
        // only moment the tokens in its signature meant anything.
        if let Some(ty) = self.compilation.metadata_type(symbol) {
            return ty.clone();
        }
        // A source symbol's type is resolved once, when resolving it had
        // nothing to say. One that reported something — a type that does not
        // exist — is resolved again each time, so that every file asking
        // about its declarations hears it, not only the first.
        if let Some(ty) = self.compilation.cached_symbol_type(symbol) {
            return ty;
        }
        let before = diagnostics.len();
        let ty = self.type_of_uncached(symbol, diagnostics);
        if diagnostics.len() == before {
            self.compilation.cache_symbol_type(symbol, ty.clone());
        }
        ty
    }

    fn type_of_uncached(&self, symbol: SymbolId, diagnostics: &mut Diagnostics) -> Type {
        let symbols = self.compilation.symbols();
        // An enum member writes no type because it has none to write: its type
        // is the enum it is a member of.
        if symbols.get(symbol).kind == crate::symbol::SymbolKind::Field
            && let Some(container) = symbols.get(symbol).container
            && symbols.get(container).type_kind() == Some(crate::symbol::TypeKind::Enum)
        {
            // Nested in `Outer<T>`, that is `Outer<T>.E`.
            return self.self_type(container);
        }

        // A setter writes no return type because C# gives it nowhere to write
        // one; it returns nothing all the same.
        if symbols
            .get(symbol)
            .as_method()
            .is_some_and(|detail| detail.method_kind == crate::symbol::MethodKind::PropertySet)
        {
            return Type::Void;
        }

        // A member the language synthesised has a type the language decides,
        // because nothing in the source wrote one down.
        let synthesized = match &symbols.get(symbol).detail {
            Detail::Method(detail) => detail.synthesized_return,
            Detail::Parameter(detail) => detail.synthesized,
            Detail::Property(detail) => detail.synthesized,
            _ => None,
        };
        if let Some(synthesized) = synthesized {
            return match synthesized {
                // `void` is not a type a value can have, so it is its own
                // answer rather than the `System.Void` symbol's.
                crate::symbol::SynthesizedType::Special(SpecialType::Void) => Type::Void,
                crate::symbol::SynthesizedType::Special(special) => self
                    .compilation
                    .special_type(special)
                    .map_or(Type::Error, Type::named),
                // The type the *member* belongs to: a parameter's own
                // container is the method that takes it.
                crate::symbol::SynthesizedType::Containing => {
                    let mut current = symbols.get(symbol).container;
                    while let Some(container) = current {
                        if symbols.get(container).kind == SymbolKind::NamedType {
                            return self.self_type(container);
                        }
                        current = symbols.get(container).container;
                    }
                    Type::Error
                }
                crate::symbol::SynthesizedType::TypeParameter(index) => {
                    let mut current = symbols.get(symbol).container;
                    while let Some(container) = current {
                        if let Some(detail) = symbols.get(container).as_named_type() {
                            return detail
                                .type_parameters
                                .get(index)
                                .map_or(Type::Error, |parameter| Type::TypeParameter(*parameter));
                        }
                        current = symbols.get(container).container;
                    }
                    Type::Error
                }
                crate::symbol::SynthesizedType::StringArray => self
                    .compilation
                    .special_type(SpecialType::String)
                    .map_or(Type::Error, |string| Type::Array {
                        element: Box::new(Type::named(string)),
                        rank: 1,
                    }),
                crate::symbol::SynthesizedType::Task => self
                    .compilation
                    .type_by_metadata_name("System.Threading.Tasks.Task")
                    .map_or(Type::Error, Type::named),
                crate::symbol::SynthesizedType::SystemType => self
                    .compilation
                    .type_by_metadata_name("System.Type")
                    .map_or(Type::Error, Type::named),
                crate::symbol::SynthesizedType::StringBuilder => self
                    .compilation
                    .type_by_metadata_name("System.Text.StringBuilder")
                    .map_or(Type::Error, Type::named),
                crate::symbol::SynthesizedType::TaskOfInt32 => {
                    match (
                        self.compilation
                            .type_by_metadata_name("System.Threading.Tasks.Task`1"),
                        self.compilation.special_type(SpecialType::Int32),
                    ) {
                        (Some(task), Some(int)) => Type::Named {
                            symbol: task,
                            type_arguments: vec![Type::named(int)],
                        },
                        _ => Type::Error,
                    }
                }
            };
        }

        let reference = match &self.compilation.symbols().get(symbol).detail {
            Detail::Field(detail) => detail.ty,
            Detail::Property(detail) => detail.ty,
            Detail::Event(detail) => detail.ty,
            Detail::Parameter(detail) => detail.ty,
            Detail::Local(detail) => detail.ty,
            Detail::Method(detail) => detail.return_type,
            Detail::NamedType(_) => return Type::named(symbol),
            Detail::TypeParameter(_) => return Type::TypeParameter(symbol),
            Detail::Namespace => return Type::Error,
        };
        reference.map_or(Type::Error, |reference| {
            self.resolve_type_ref(reference, diagnostics)
        })
    }
}

/// The name an `IdentifierName` or `GenericName` node carries.
fn identifier_text(node: &SyntaxNode) -> Option<String> {
    node.child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
}

/// How many type arguments a name was written with.
fn type_argument_count(node: &SyntaxNode) -> usize {
    node.child_of_kind(SyntaxKind::TypeArgumentList)
        .map_or(0, |list| {
            list.children()
                .filter(|child| child.kind().is_type_node())
                .count()
        })
}

/// The text of a string literal written somewhere inside `node`.
fn string_literal_text(node: &SyntaxNode) -> Option<String> {
    if node.kind() == SyntaxKind::StringLiteralExpression
        && let Some(token) = node.child_tokens().next()
    {
        return match token.value() {
            TokenValue::String(text) => Some(text.to_string()),
            _ => None,
        };
    }
    node.children()
        .find_map(|child| string_literal_text(&child))
}

/// The `n` of an `[InlineArray(n)]` on a declaration, if one is written.
fn inline_array_length(declaration: &SyntaxNode) -> Option<i32> {
    for list in declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
    {
        for attribute in list
            .children()
            .filter(|child| child.kind() == SyntaxKind::Attribute)
        {
            let name = attribute.children().next()?.text();
            let name = name.trim().rsplit('.').next().unwrap_or_default();
            if name != "InlineArray" && name != "InlineArrayAttribute" {
                continue;
            }
            let argument = attribute
                .child_of_kind(SyntaxKind::AttributeArgumentList)?
                .child_of_kind(SyntaxKind::AttributeArgument)?;
            let text = argument.text();
            let text = text.trim().replace('_', "");
            return text.parse::<i32>().ok();
        }
    }
    None
}

/// The calling convention a `delegate*` names, as a signature spells it,
/// and the `CallConv*` types it names beyond that.
///
/// `managed` (or nothing) is 0. `unmanaged[Cdecl]` alone is the old
/// convention byte for it; `unmanaged` alone, or with anything else in the
/// list, is the extensible one (9) with each name as a `modopt` on the return.
fn function_pointer_convention(node: &SyntaxNode) -> (u8, Vec<String>) {
    let Some(convention) = node.child_of_kind(SyntaxKind::FunctionPointerCallingConvention) else {
        return (0, Vec::new());
    };
    if !convention
        .child_tokens()
        .any(|token| token.text() == "unmanaged")
    {
        return (0, Vec::new());
    }
    let names: Vec<String> = convention
        .child_of_kind(SyntaxKind::FunctionPointerUnmanagedCallingConventionList)
        .map(|list| {
            list.children()
                .filter(|child| {
                    child.kind() == SyntaxKind::FunctionPointerUnmanagedCallingConvention
                })
                .filter_map(|child| {
                    child
                        .child_tokens()
                        .next()
                        .map(|token| token.text().to_string())
                })
                .collect()
        })
        .unwrap_or_default();
    match names.as_slice() {
        [single] => match single.as_str() {
            "Cdecl" => (1, Vec::new()),
            "Stdcall" => (2, Vec::new()),
            "Thiscall" => (3, Vec::new()),
            "Fastcall" => (4, Vec::new()),
            _ => (9, names),
        },
        _ => (9, names),
    }
}
