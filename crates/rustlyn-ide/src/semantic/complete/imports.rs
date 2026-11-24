//! Import completion: types, and extension methods after a `.`, from
//! namespaces the file does not import yet — Roslyn's "show items from
//! unimported namespaces". Choosing one also adds the `using` it needs,
//! placed where a sorted list of them would have it.
//!
//! Every type of every assembly is a long list, so it is made once per
//! compilation and kept: a name, its namespace, and its symbol. A
//! completion then only walks it, and only for the names the typed word
//! could start — with nothing typed yet nothing is offered, as the list
//! would be the whole framework.

use std::collections::HashSet;

use rustlyn_semantics::{Accessibility, Compilation, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::context::Site;
use super::{Completion, View, matches_word, newline_of};
use crate::edit::TextEdit;

/// Every type outside the global namespace and every extension method,
/// with the namespace each is in.
#[derive(Debug, Default)]
pub(in crate::semantic) struct ImportIndex {
    types: Vec<Imported>,
    extensions: Vec<Imported>,
}

#[derive(Debug)]
struct Imported {
    namespace: SymbolId,
    symbol: SymbolId,
}

impl ImportIndex {
    fn build(compilation: &Compilation) -> Self {
        let symbols = compilation.symbols();
        let global = compilation.global_namespace();
        let mut index = Self::default();
        for ty in compilation.all_types() {
            let Some(container) = ty.container else {
                continue;
            };
            if container == global || symbols.get(container).kind != SymbolKind::Namespace {
                continue;
            }
            if ty.name.is_empty() || ty.name.contains('<') {
                continue;
            }
            if compilation.is_from_metadata(ty.id)
                && !matches!(
                    ty.accessibility,
                    Accessibility::Public | Accessibility::ProtectedOrInternal
                )
            {
                continue;
            }
            index.types.push(Imported {
                namespace: container,
                symbol: ty.id,
            });
        }
        let names: Vec<&str> = compilation.extension_method_names().collect();
        for name in names {
            for &method in compilation.extension_methods(name) {
                let namespace = namespace_of(compilation, method);
                if let Some(namespace) = namespace
                    && namespace != global
                {
                    index.extensions.push(Imported {
                        namespace,
                        symbol: method,
                    });
                }
            }
        }
        index
    }
}

/// The namespace a symbol is declared in.
fn namespace_of(compilation: &Compilation, symbol: SymbolId) -> Option<SymbolId> {
    let symbols = compilation.symbols();
    let mut current = symbols.get(symbol).container;
    while let Some(container) = current {
        if symbols.get(container).kind == SymbolKind::Namespace {
            return Some(container);
        }
        current = symbols.get(container).container;
    }
    None
}

impl View<'_> {
    fn import_index(&self) -> std::sync::Arc<ImportIndex> {
        self.semantic
            .completion_index
            .get_or_init(|| std::sync::Arc::new(ImportIndex::build(self.compilation())))
            .clone()
    }

    /// The namespaces whose types the code at `node` can name without a
    /// `using`: the global one, the ones it is in, and the ones imported.
    fn imported_namespaces(&self, node: &SyntaxNode) -> HashSet<SymbolId> {
        let mut found: HashSet<SymbolId> = self.namespaces_in_scope(node).into_iter().collect();
        found.insert(self.compilation().global_namespace());
        found
    }
}

/// Types from namespaces not imported, whose names the typed word could
/// start. `types_only` leaves out static classes, which only a member
/// access can use.
pub(super) fn complete_types(
    view: &View<'_>,
    site: &Site,
    text: &str,
    types_only: bool,
    items: &mut Vec<Completion>,
) {
    if site.word.is_empty() {
        return;
    }
    let node = anchor(view, site.start);
    let imported = view.imported_namespaces(&node);
    let index = view.import_index();
    let usings = Usings::of(&view.root, text);
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    for entry in &index.types {
        if imported.contains(&entry.namespace) {
            continue;
        }
        let ty = symbols.get(entry.symbol);
        if !matches_word(&site.word, &ty.name) {
            continue;
        }
        if types_only && ty.modifiers.contains(rustlyn_semantics::Modifiers::STATIC) {
            continue;
        }
        let namespace = symbols.qualified_name(entry.namespace);
        let mut item = Completion {
            label: ty.name.clone(),
            kind: super::super::completion_kind(compilation, entry.symbol),
            detail: format!(
                "{} ({namespace})",
                super::super::describe_symbol(compilation, entry.symbol)
            ),
            rank: 35,
            symbol: Some(entry.symbol),
            ..Completion::default()
        };
        if let Some(edit) = usings.edit(&namespace) {
            item.additional_edits.push(edit);
        }
        items.push(item);
    }
}

/// After `x.`: extension methods from namespaces not imported that take
/// what `x` is.
pub(super) fn complete_extensions(
    view: &mut View<'_>,
    site: &Site,
    dot: &SyntaxToken,
    items: &mut Vec<Completion>,
) {
    if site.word.is_empty() {
        return;
    }
    let parent = dot.parent().clone();
    let receiver = match parent.kind() {
        K::SimpleMemberAccessExpression => parent.children().next(),
        K::MemberBindingExpression => parent
            .ancestors()
            .find(|ancestor| ancestor.kind() == K::ConditionalAccessExpression)
            .and_then(|access| access.children().next()),
        _ => None,
    };
    let Some(receiver) = receiver else {
        return;
    };
    // A type or namespace to the left has no extension methods.
    if view.named(&receiver).is_some() {
        return;
    }
    let ty = view.type_of(&receiver);
    if matches!(ty, Type::Error | Type::Void | Type::Null) {
        return;
    }
    let receiver_types = view.types_of(&ty);
    let imported = view.imported_namespaces(&receiver);
    let index = view.import_index();
    let text = view.root.full_text();
    let usings = Usings::of(&view.root, &text);
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    for entry in &index.extensions {
        if imported.contains(&entry.namespace) {
            continue;
        }
        let method = symbols.get(entry.symbol);
        if !matches_word(&site.word, &method.name) {
            continue;
        }
        let Some(&first) = method.as_method().and_then(|m| m.parameters.first()) else {
            continue;
        };
        let takes = match view.model.type_of_symbol(first) {
            Type::TypeParameter(_) => true,
            Type::Named { symbol, .. } => receiver_types.contains(&symbol),
            other => view.model.binder().converts_implicitly(&ty, &other),
        };
        if !takes {
            continue;
        }
        let namespace = symbols.qualified_name(entry.namespace);
        let mut item = Completion {
            label: method.name.clone(),
            kind: super::CompletionKind::Method,
            detail: format!(
                "{} ({namespace})",
                super::super::describe_symbol(compilation, entry.symbol)
            ),
            rank: 36,
            symbol: Some(entry.symbol),
            ..Completion::default()
        };
        if let Some(edit) = usings.edit(&namespace) {
            item.additional_edits.push(edit);
        }
        items.push(item);
    }
}

/// A node at `offset` for asking what is in scope there.
fn anchor(view: &View<'_>, offset: u32) -> SyntaxNode {
    view.root
        .find_token(offset.saturating_sub(1))
        .map_or_else(|| view.root.clone(), |token| token.parent().clone())
}

/// How `using`s are ordered: `System` and its children first, then the
/// rest, alphabetically — Visual Studio's default.
fn using_order(name: &str) -> (bool, String) {
    let system = name == "System" || name.starts_with("System.");
    (!system, name.to_ascii_lowercase())
}

/// Where a file's `using`s are, read once for all the items that add one.
pub(super) struct Usings<'t> {
    newline: &'static str,
    /// Each plain `using`: its name's order, where its line starts, and its
    /// indentation.
    existing: Vec<((bool, String), u32, &'t str)>,
    /// Where the line after the last one starts, and whether there is
    /// one: the last may end the file.
    after_last: Option<(u32, bool)>,
    /// Where the first line of code starts, for a file with no `using`s.
    top: u32,
}

impl<'t> Usings<'t> {
    /// The `using`s of the file, or of its namespace when they are there.
    pub(super) fn of(root: &SyntaxNode, text: &'t str) -> Self {
        let is_plain_using = |using: &SyntaxNode| {
            using.kind() == K::UsingDirective
                && using.child_token_of_kind(K::GlobalKeyword).is_none()
                && using.child_token_of_kind(K::StaticKeyword).is_none()
                && using.child_of_kind(K::NameEquals).is_none()
        };
        let line_start = |at: u32| -> u32 {
            text[..at as usize].rfind('\n').map_or(0, |found| found + 1) as u32
        };
        let mut container = root.clone();
        if !root.children().any(|child| is_plain_using(&child)) {
            let namespace = root
                .children()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        K::NamespaceDeclaration | K::FileScopedNamespaceDeclaration
                    )
                })
                .find(|node| node.children().any(|child| is_plain_using(&child)));
            if let Some(found) = namespace {
                container = found;
            }
        }
        let usings: Vec<SyntaxNode> = container
            .children()
            .filter(|child| is_plain_using(child))
            .collect();
        let existing = usings
            .iter()
            .map(|using| {
                let name = using
                    .children()
                    .find(|child| child.kind().is_type_node())
                    .map(|name| name.text().trim().to_string())
                    .unwrap_or_default();
                let start = line_start(using.span().start());
                let indent = &text[start as usize..using.span().start() as usize];
                (using_order(&name), start, indent)
            })
            .collect();
        let after_last = usings.last().map(|last| {
            let end = last.span().end();
            match text[end as usize..].find('\n') {
                Some(newline) => (end + newline as u32 + 1, true),
                None => (end, false),
            }
        });
        let top = root
            .first_token()
            .filter(|first| first.kind() != K::EndOfFileToken)
            .map_or(0, |first| line_start(first.span().start()));
        Self {
            newline: newline_of(text),
            existing,
            after_last,
            top,
        }
    }

    /// The edit that adds `using namespace;` where a sorted list of them
    /// would have it, or at the top of the file when there are none.
    pub(super) fn edit(&self, namespace: &str) -> Option<TextEdit> {
        let wanted = using_order(namespace);
        if self.existing.iter().any(|(order, ..)| *order == wanted) {
            return None;
        }
        let newline = self.newline;
        let line = format!("using {namespace};{newline}");
        if let Some((_, start, indent)) = self.existing.iter().find(|(order, ..)| *order > wanted) {
            return Some(TextEdit::insert(*start, format!("{indent}{line}")));
        }
        if let (Some(after_last), Some((_, _, indent))) = (self.after_last, self.existing.last()) {
            let (at, next_line) = after_last;
            return Some(if next_line {
                TextEdit::insert(at, format!("{indent}{line}"))
            } else {
                TextEdit::insert(at, format!("{newline}{indent}using {namespace};"))
            });
        }
        Some(TextEdit::new(
            TextSpan::new(self.top, 0),
            format!("{line}{newline}"),
        ))
    }
}
