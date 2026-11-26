//! A compilation made from another with one file edited, without declaring
//! the whole program again.
//!
//! Declaring every file of a large project — the walk over all its trees,
//! then loading its references — takes a second or more, and most edits
//! change no declaration at all: they are inside a method's body. Such an
//! edit leaves the symbol table as it was but for where things are in the
//! edited file, since what comes after the edit has moved.
//!
//! So the edited file is declared on its own, before and after the edit, and
//! the two tables compared with every place in the old one moved to where
//! the same tokens are in the new one. Where they agree, the new compilation
//! is the old one with that file's places moved, and nothing else declared
//! again; where they do not, the caller builds the whole compilation.

use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, RwLock};

use rustlyn_syntax::{SyntaxKind, SyntaxTree};
use rustlyn_text::TextSpan;

use crate::compilation::{Compilation, CompilationDiagnostic, SymbolCache, has_global_using};
use crate::declare::{Declared, Declarer, TreeFacts, TreeSource};
use crate::symbol::{Location, Symbols};

/// Where each token of a file went in its edited text.
struct Moves {
    /// Each old token by where it starts, and by where it ends.
    by_start: HashMap<u32, usize>,
    by_end: HashMap<u32, usize>,
    /// The new token each old one is, where it is still there.
    to: Vec<Option<usize>>,
    new_spans: Vec<TextSpan>,
}

impl Moves {
    /// The tokens of `old` matched to those of `new` — the longest run of
    /// them that both have in order — or `None` where the edit is too large
    /// to match cheaply.
    fn between(old: &SyntaxTree, new: &SyntaxTree) -> Option<Self> {
        let (old_spans, old_keys) = tokens(old);
        let (new_spans, new_keys) = tokens(new);
        let mut to = vec![None; old_keys.len()];
        let prefix = old_keys
            .iter()
            .zip(&new_keys)
            .take_while(|(a, b)| a == b)
            .count();
        let suffix = old_keys[prefix..]
            .iter()
            .rev()
            .zip(new_keys[prefix..].iter().rev())
            .take_while(|(a, b)| a == b)
            .count();
        for (at, slot) in to.iter_mut().enumerate().take(prefix) {
            *slot = Some(at);
        }
        for back in 0..suffix {
            to[old_keys.len() - 1 - back] = Some(new_keys.len() - 1 - back);
        }
        let old_middle = &old_keys[prefix..old_keys.len() - suffix];
        let new_middle = &new_keys[prefix..new_keys.len() - suffix];
        if !old_middle.is_empty() && !new_middle.is_empty() {
            // The longest common subsequence of what is left, by a table
            // only as large as the edit.
            if old_middle.len().saturating_mul(new_middle.len()) > 4_000_000 {
                return None;
            }
            let (rows, columns) = (old_middle.len(), new_middle.len());
            let mut table = vec![0u32; (rows + 1) * (columns + 1)];
            for row in (0..rows).rev() {
                for column in (0..columns).rev() {
                    let at = row * (columns + 1) + column;
                    table[at] = if old_middle[row] == new_middle[column] {
                        table[at + columns + 2] + 1
                    } else {
                        table[at + columns + 1].max(table[at + 1])
                    };
                }
            }
            let (mut row, mut column) = (0, 0);
            while row < rows && column < columns {
                if old_middle[row] == new_middle[column] {
                    to[prefix + row] = Some(prefix + column);
                    row += 1;
                    column += 1;
                } else if table[(row + 1) * (columns + 1) + column]
                    >= table[row * (columns + 1) + column + 1]
                {
                    row += 1;
                } else {
                    column += 1;
                }
            }
        }
        let by_start = old_spans
            .iter()
            .enumerate()
            .map(|(at, span)| (span.start(), at))
            .collect();
        let by_end = old_spans
            .iter()
            .enumerate()
            .map(|(at, span)| (span.end(), at))
            .collect();
        Some(Self {
            by_start,
            by_end,
            to,
            new_spans,
        })
    }

    /// Where an old span is now: from the token it starts at to the one it
    /// ends at, both of which must still be there.
    fn span(&self, span: TextSpan) -> Option<TextSpan> {
        let first = self.to[*self.by_start.get(&span.start())?]?;
        if span.is_empty() {
            return Some(TextSpan::new(self.new_spans[first].start(), 0));
        }
        let last = self.to[*self.by_end.get(&span.end())?]?;
        if last < first {
            return None;
        }
        let start = self.new_spans[first].start();
        Some(TextSpan::new(start, self.new_spans[last].end() - start))
    }
}

/// Each token of a tree that is in its text, with its kind and text.
fn tokens(tree: &SyntaxTree) -> (Vec<TextSpan>, Vec<(SyntaxKind, String)>) {
    tree.root()
        .descendant_tokens()
        .filter(|token| !token.is_missing() && !token.span().is_empty())
        .map(|token| (token.span(), (token.kind(), token.text().to_string())))
        .unzip()
}

/// What declaring one file alone makes of it.
fn declared_alone(tree: &SyntaxTree) -> Declared {
    let trees = [tree.clone()];
    let facts = [TreeFacts::of(tree)];
    let mut declarer = Declarer::new(TreeSource::Parsed(&trees, &facts));
    declarer.declare_all();
    Declared::from(declarer)
}

/// The places of `tree` in `symbols` moved, or `None` where one of them is
/// not where any token now is.
fn move_symbols(symbols: &mut [crate::symbol::Symbol], tree: usize, moves: &Moves) -> Option<()> {
    let mut lost = false;
    for symbol in symbols {
        symbol.for_each_location(&mut |location: &mut Location| {
            if location.tree == tree {
                match moves.span(location.span) {
                    Some(span) => location.span = span,
                    None => lost = true,
                }
            }
        });
        if lost {
            return None;
        }
    }
    Some(())
}

/// Whether the edit from `old` to `new` declares nothing other than the old
/// text did, every place moved with its tokens.
fn declares_the_same(old: &SyntaxTree, new: &SyntaxTree, moves: &Moves) -> bool {
    let before = declared_alone(old);
    let after = declared_alone(new);
    let mut moved = before.symbols.symbols.clone();
    if move_symbols(&mut moved, 0, moves).is_none() {
        return false;
    }
    if format!("{moved:?}") != format!("{:?}", after.symbols.symbols) {
        return false;
    }
    let declarations: Option<HashMap<(usize, TextSpan), _>> = before
        .declarations
        .iter()
        .map(|(&(tree, span), &symbol)| Some(((tree, moves.span(span)?), symbol)))
        .collect();
    if declarations.as_ref() != Some(&after.declarations) {
        return false;
    }
    let diagnostics: Option<Vec<_>> = before
        .diagnostics
        .iter()
        .map(|(tree, diagnostic)| {
            Some((
                *tree,
                diagnostic.clone().with_span(moves.span(diagnostic.span())?),
            ))
        })
        .collect();
    diagnostics
        .is_some_and(|diagnostics| format!("{diagnostics:?}") == format!("{:?}", after.diagnostics))
        && before.anonymous.keys().collect::<HashSet<_>>()
            == after.anonymous.keys().collect::<HashSet<_>>()
}

impl Compilation {
    /// This compilation with file `index` given by `tree`, made without
    /// declaring the program again when the edit declares nothing new — an
    /// edit inside bodies — or `None` where it does, and the whole
    /// compilation has to be built.
    ///
    /// What is worked out as it is asked for (the types of symbols, the
    /// imports of a scope) starts again empty.
    #[must_use]
    pub fn with_tree_replaced(&self, index: usize, tree: SyntaxTree) -> Option<Self> {
        self.with_trees_replaced(vec![(index, tree)])
    }

    /// The same for several files at once: a file and what the generators
    /// wrote for it. Each must declare what it did before.
    #[must_use]
    pub fn with_trees_replaced(&self, replaced: Vec<(usize, SyntaxTree)>) -> Option<Self> {
        if replaced.is_empty() {
            return None;
        }
        // A compilation read back from disk has trees not parsed yet, and
        // what their syntax says is not to be had without parsing them all.
        if (0..self.trees.len()).any(|at| !self.trees.is_parsed(at)) {
            return None;
        }
        let timing = crate::timing::phase("redeclare");
        let mut moves: HashMap<usize, Moves> = HashMap::new();
        for (index, tree) in &replaced {
            let old = self.trees.get(*index)?;
            if *index < self.corlib_trees || moves.contains_key(index) {
                return None;
            }
            let moved = Moves::between(old, tree)?;
            if !declares_the_same(old, tree, &moved) {
                return None;
            }
            moves.insert(*index, moved);
        }
        let span_in = |tree: usize, span: TextSpan| -> Option<TextSpan> {
            match moves.get(&tree) {
                Some(moved) => moved.span(span),
                None => Some(span),
            }
        };

        let mut kept = self.symbols.symbols.clone();
        let mut lost = false;
        for symbol in &mut kept[..self.metadata_floor] {
            symbol.for_each_location(&mut |location: &mut Location| {
                if moves.contains_key(&location.tree) {
                    match span_in(location.tree, location.span) {
                        Some(span) => location.span = span,
                        None => lost = true,
                    }
                }
            });
            if lost {
                return None;
            }
        }
        let symbols = Symbols::from_parts(kept, self.symbols.index.clone());

        let mut declarations = HashMap::with_capacity(self.declarations.len());
        for (&(at, span), &symbol) in &self.declarations {
            declarations.insert((at, span_in(at, span)?), symbol);
        }
        let mut declaration_nodes = self.declaration_nodes.clone();
        for nodes in declaration_nodes.values_mut() {
            for (at, span) in nodes.iter_mut() {
                if moves.contains_key(at) {
                    *span = span_in(*at, *span)?;
                }
            }
        }

        let new_trees: HashMap<usize, &SyntaxTree> = replaced
            .iter()
            .map(|(index, tree)| (*index, tree))
            .collect();
        // Syntax first, file by file, then what declaring found — as the
        // whole compilation lists them.
        let syntax: usize = (0..self.trees.len())
            .map(|at| {
                self.trees
                    .get(at)
                    .map_or(0, |tree| tree.diagnostics().len())
            })
            .sum();
        // The old syntax diagnostics of untouched files, in their places:
        // rebuilt file by file, the edited ones from their new trees.
        let mut diagnostics = Vec::with_capacity(self.diagnostics.len());
        let mut old_syntax = self.diagnostics[..syntax.min(self.diagnostics.len())]
            .iter()
            .peekable();
        for at in 0..self.trees.len() {
            let mut own = Vec::new();
            while old_syntax.peek().is_some_and(|entry| entry.tree == at) {
                own.push(old_syntax.next().expect("peeked").clone());
            }
            match new_trees.get(&at) {
                Some(tree) => diagnostics.extend(new_syntax(tree, at)),
                None => diagnostics.extend(own),
            }
        }
        for entry in self.diagnostics.iter().skip(syntax) {
            if moves.contains_key(&entry.tree) {
                let span = span_in(entry.tree, entry.diagnostic.span())?;
                diagnostics.push(CompilationDiagnostic {
                    tree: entry.tree,
                    diagnostic: entry.diagnostic.clone().with_span(span),
                });
            } else {
                diagnostics.push(entry.clone());
            }
        }

        let mut global_using_trees: Vec<usize> = self
            .global_using_trees
            .iter()
            .copied()
            .filter(|at| !moves.contains_key(at))
            .collect();
        global_using_trees.extend(
            replaced
                .iter()
                .filter(|(_, tree)| has_global_using(tree))
                .map(|(at, _)| *at),
        );
        global_using_trees.sort_unstable();

        let mut trees = None::<crate::trees::Trees>;
        for (index, tree) in replaced {
            trees = Some(
                trees
                    .as_ref()
                    .unwrap_or(&self.trees)
                    .with_replaced(index, tree),
            );
        }

        let compilation = Self {
            trees: trees.expect("a tree was replaced"),
            global_using_trees,
            symbols,
            global: self.global,
            diagnostics,
            special_types: self.special_types,
            well_known: self.well_known,
            declarations,
            declaration_nodes,
            anonymous_types: self.anonymous_types.clone(),
            corlib_trees: self.corlib_trees,
            loaded: self.loaded.clone(),
            metadata_floor: self.metadata_floor,
            base_types: SymbolCache::new(self.metadata_floor),
            resolving: Mutex::new(HashSet::new()),
            extensions: self.extensions.clone(),
            extension_members: self.extension_members.clone(),
            conversions: RwLock::new(HashMap::new()),
            constants: RwLock::new(HashMap::new()),
            circular_constants: RwLock::new(std::collections::BTreeSet::new()),
            imports: RwLock::new(HashMap::new()),
            global_imports: RwLock::new(None),
            obsolete: std::sync::OnceLock::new(),
            metadata_names: RwLock::new(HashMap::new()),
            inheritance: RwLock::new(HashMap::new()),
            implicit_conversions: RwLock::new(HashMap::new()),
            symbol_types: SymbolCache::new(self.metadata_floor),
            anonymous_delegates: Mutex::new(crate::delegates::AnonymousDelegates::default()),
            options: self.options.clone(),
            priorities: std::sync::OnceLock::new(),
            assembly_references: self.assembly_references.clone(),
            namespaces_seen: RwLock::new(HashMap::new()),
            source_friends: self.source_friends.clone(),
            metadata_references: self.metadata_references.clone(),
            assembly_nullable: self.assembly_nullable.clone(),
            tree_assemblies_also: self.tree_assemblies_also.clone(),
            tree_assemblies: self.tree_assemblies.clone(),
        };
        drop(timing);
        Some(compilation)
    }
}

impl Compilation {
    /// The first way two compilations differ in what was declared — a
    /// symbol, where something is declared, a diagnostic — or `None`: what
    /// a compilation made by [`Self::with_tree_replaced`] is checked against
    /// the whole build of the same files.
    #[doc(hidden)]
    #[must_use]
    pub fn first_declaration_difference(&self, other: &Self) -> Option<String> {
        if self.symbols.symbols.len() != other.symbols.symbols.len() {
            return Some(format!(
                "{} symbols against {}",
                self.symbols.symbols.len(),
                other.symbols.symbols.len()
            ));
        }
        for (mine, theirs) in self.symbols.symbols.iter().zip(&other.symbols.symbols) {
            let (mine, theirs) = (format!("{mine:?}"), format!("{theirs:?}"));
            if mine != theirs {
                return Some(format!("symbol\n  {mine}\n  {theirs}"));
            }
        }
        if self.declarations != other.declarations {
            let missing = self
                .declarations
                .iter()
                .find(|(key, value)| other.declarations.get(key) != Some(value));
            return Some(format!("declarations differ: {missing:?}"));
        }
        let sorted = |nodes: &HashMap<crate::symbol::SymbolId, Vec<(usize, TextSpan)>>| {
            let mut all: Vec<_> = nodes
                .iter()
                .map(|(id, spans)| (id.0, spans.clone()))
                .collect();
            all.sort_unstable();
            all
        };
        if sorted(&self.declaration_nodes) != sorted(&other.declaration_nodes) {
            return Some("declaration nodes differ".to_string());
        }
        let (mine, theirs) = (
            format!("{:?}", self.diagnostics),
            format!("{:?}", other.diagnostics),
        );
        if mine != theirs {
            let at = self
                .diagnostics
                .iter()
                .zip(&other.diagnostics)
                .position(|(a, b)| format!("{a:?}") != format!("{b:?}"));
            return Some(format!(
                "diagnostics differ ({} against {}) first at {at:?}: {:?} / {:?}",
                self.diagnostics.len(),
                other.diagnostics.len(),
                at.and_then(|at| self.diagnostics.get(at)),
                at.and_then(|at| other.diagnostics.get(at))
            ));
        }
        if self.global_using_trees != other.global_using_trees
            || self.special_types != other.special_types
            || self.well_known != other.well_known
            || self.metadata_floor != other.metadata_floor
        {
            return Some("indexes differ".to_string());
        }
        None
    }
}

fn new_syntax(tree: &SyntaxTree, index: usize) -> impl Iterator<Item = CompilationDiagnostic> + '_ {
    tree.diagnostics()
        .iter()
        .map(move |diagnostic| CompilationDiagnostic {
            tree: index,
            diagnostic: diagnostic.clone(),
        })
}
