//! Find all references the way a results window shows them.
//!
//! [`Semantic::references`] answers "where is this used" with places. A
//! results window wants more for each one: whether it declares the thing,
//! writes it or only reads it, which member it is in, and the line it is on,
//! so that the list can be read without opening a single file. It also wants
//! the places a spelling search does not find, because nothing there is
//! spelled like the name:
//!
//! * **`new()`**, which calls a constructor without naming its type;
//! * **`<see cref="X"/>`**, which is in a comment, not in the code;
//! * **overrides and implementations**, which are other symbols with the same
//!   name: asking about an interface method is asking about every method
//!   that implements it, and each of those is listed as a definition.
//!
//! The same machinery — find by spelling, then bind — serves the highlights
//! of one file and the reference counts over declarations, so it lives here
//! and they use it.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use rustlyn_semantics::{
    BoundSymbol, MethodKind, Modifiers, SemanticModel, SymbolId, SymbolKind, Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::{Resolved, Semantic, View, attribute_stem, contains_word, names_declaration, parallel};

/// How a reference touches what it names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ReferenceKind {
    /// The name of a declaration of it.
    Definition = 0,
    /// Assigned, incremented, passed by `ref` or `out`, or deconstructed
    /// into.
    Write = 1,
    /// Everything else: read, called, named as a type.
    Read = 2,
}

/// One reference, with what a results window shows beside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reference {
    pub path: PathBuf,
    /// The name, in bytes of the file as searched.
    pub span: TextSpan,
    pub kind: ReferenceKind,
    /// The member or type the reference is written in: `Game.Run`.
    pub container: String,
    /// The line it is on, without its indentation.
    pub preview: String,
}

/// One place a file names something, found by spelling and bound.
#[derive(Clone, Debug)]
pub(super) struct Use {
    /// The name, or the `new` of a `new()`.
    pub span: TextSpan,
    pub resolved: Resolved,
    pub kind: ReferenceKind,
    /// Set for a target-typed `new(...)`: the number of arguments it passes.
    /// `resolved` is then the type it makes, since the binder records no
    /// constructor for a creation that writes no name.
    pub creation: Option<usize>,
}

impl Semantic {
    /// Every reference to what is at `offset`, classified, with the member
    /// each is in and the line it is on. Overrides and implementations of a
    /// member are included, their declarations as definitions, as are
    /// target-typed `new()` calls of a type or constructor and `cref`s in
    /// documentation comments.
    #[must_use]
    pub fn references_detailed(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(String, Vec<Reference>)> {
        let tree = self.tree_index(path)?;
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        let target = view.resolve_use(&token)?;
        let word = token.value_text().to_string();

        let (name, targets) = match &target {
            Resolved::Symbol(symbol) => (
                self.search_name(*symbol),
                self.cascade(*symbol)
                    .into_iter()
                    .map(Resolved::Symbol)
                    .collect::<Vec<_>>(),
            ),
            Resolved::Local { name, .. } => (name.clone(), vec![target.clone()]),
        };
        let creations = targets.iter().any(|target| self.is_made_by_new(target));
        let names: HashSet<String> = std::iter::once(name.clone()).collect();

        // A local cannot be named outside the body that declared it, and the
        // file being edited is searched as it is now.
        let mut found: Vec<Reference> = Vec::new();
        let local = matches!(target, Resolved::Local { .. });
        if local || view.speculation.is_some() {
            let here = view.root.full_text();
            found.extend(view.references_to(&names, creations, &targets, path, &here));
        }
        if !local {
            let candidates: Vec<usize> = self
                .paths
                .keys()
                .copied()
                .filter(|&other| other != tree || view.speculation.is_none())
                .collect();
            let per_file = parallel(candidates.len(), |index| {
                let tree = candidates[index];
                let Some(text) = self.compilation.trees().source(tree).map(|s| s.text()) else {
                    return Vec::new();
                };
                if !mentions(text, &name, creations) {
                    return Vec::new();
                }
                let Some(mut view) = self.view(tree) else {
                    return Vec::new();
                };
                let path = self.paths[&tree].clone();
                view.references_to(&names, creations, &targets, &path, text)
            });
            found.extend(per_file.into_iter().flatten());
        }
        found.sort_by(|a, b| {
            a.path
                .cmp(&b.path)
                .then(a.span.start().cmp(&b.span.start()))
        });
        found.dedup_by(|a, b| a.path == b.path && a.span == b.span);
        Some((word, found))
    }

    /// A member and every member that is the same member seen from
    /// elsewhere, as Roslyn's find-all-references cascades: what it
    /// overrides or implements, what overrides or implements those, and so
    /// on until nothing new turns up. Asking about one implementation of an
    /// interface member is asking about the interface member, and so about
    /// every other implementation of it.
    pub(super) fn cascade(&self, symbol: SymbolId) -> Vec<SymbolId> {
        self.cascade_where(symbol, &mut None, &|_| true)
    }

    /// [`Semantic::cascade`] through the members `keep` lets in only: one
    /// it turns away is neither in the answer nor looked past. `derived` is
    /// worked out on the first member that can have overrides, and kept for
    /// the next question.
    pub(super) fn cascade_where(
        &self,
        symbol: SymbolId,
        derived: &mut Option<Derived>,
        keep: &dyn Fn(SymbolId) -> bool,
    ) -> Vec<SymbolId> {
        let mut related = vec![symbol];
        let mut next = 0;
        // A hierarchy is small; the bound is against a cycle the binder
        // might produce in broken code.
        while next < related.len() && related.len() < 256 {
            for found in self.cascade_once(related[next], derived) {
                if keep(found) && !related.contains(&found) {
                    related.push(found);
                }
            }
            next += 1;
        }
        related
    }

    /// One step of [`Semantic::cascade`]: a member, what it overrides or
    /// implements, and — when it can be — what overrides or implements it
    /// in the project.
    fn cascade_once(&self, symbol: SymbolId, derived: &mut Option<Derived>) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let mut related = vec![symbol];
        if !matches!(
            found.kind,
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
        ) || found.modifiers.contains(Modifiers::STATIC)
            || found.as_method().is_some_and(|method| {
                !matches!(
                    method.method_kind,
                    MethodKind::Ordinary | MethodKind::PropertyGet | MethodKind::PropertySet
                )
            })
        {
            return related;
        }
        let Some(container) = found.container else {
            return related;
        };
        let model = SemanticModel::new(&self.compilation, 0);
        let short = short_name(&found.name).to_string();
        let same_member = |other: SymbolId| {
            other != symbol
                && symbols.get(other).kind == found.kind
                && short_name(&symbols.get(other).name) == short
                && same_signature(&model, symbol, other)
        };

        // Up: what it overrides, and the interface members it implements.
        for base in all_bases(&model, container) {
            let is_interface = symbols.get(base).type_kind() == Some(TypeKind::Interface);
            if !is_interface && !found.modifiers.contains(Modifiers::OVERRIDE) {
                continue;
            }
            related.extend(
                symbols
                    .get(base)
                    .members
                    .iter()
                    .copied()
                    .filter(|&member| same_member(member)),
            );
        }

        // Down: overrides and implementations, where there can be any.
        let in_interface = symbols.get(container).type_kind() == Some(TypeKind::Interface);
        let overridable = in_interface
            || found.modifiers.contains(Modifiers::VIRTUAL)
            || found.modifiers.contains(Modifiers::ABSTRACT)
            || found.modifiers.contains(Modifiers::OVERRIDE);
        if overridable {
            let derived = derived.get_or_insert_with(|| Derived::new(self, &model));
            for &ty in derived.from(container) {
                related.extend(symbols.get(ty).members.iter().copied().filter(|&member| {
                    same_member(member)
                        && (in_interface
                            || symbols.get(member).modifiers.contains(Modifiers::OVERRIDE))
                }));
            }
        }
        let mut seen = HashSet::new();
        related.retain(|symbol| seen.insert(*symbol));
        related
    }

    /// Whether a `new()` with no type written can make, or call, `target`.
    pub(super) fn is_made_by_new(&self, target: &Resolved) -> bool {
        let Resolved::Symbol(symbol) = target else {
            return false;
        };
        let found = self.compilation.symbols().get(*symbol);
        match found.kind {
            SymbolKind::NamedType => matches!(
                found.type_kind(),
                Some(
                    TypeKind::Class | TypeKind::Struct | TypeKind::Record | TypeKind::RecordStruct
                ) | None
            ),
            SymbolKind::Method => found
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor),
            _ => false,
        }
    }

    /// Whether a found use is of `target`: the same symbol, a constructor and
    /// its type, or a `new()` that makes the type or calls that constructor.
    pub(super) fn use_is_of(&self, found: &Use, target: &Resolved) -> bool {
        let Some(arguments) = found.creation else {
            return same(self, &found.resolved, target);
        };
        let (Resolved::Symbol(made), Resolved::Symbol(target)) = (&found.resolved, target) else {
            return false;
        };
        if made == target {
            return true;
        }
        let symbols = self.compilation.symbols();
        let constructor = symbols.get(*target);
        constructor.container == Some(*made)
            && constructor.as_method().is_some_and(|method| {
                method.method_kind == MethodKind::Constructor
                    && (method.parameters.len() == arguments
                        || method.parameters.iter().any(|&parameter| {
                            symbols
                                .get(parameter)
                                .as_parameter()
                                .is_some_and(|parameter| {
                                    parameter.is_params || parameter.has_default
                                })
                        }))
            })
    }
}

/// Whether a use resolved to `resolved` is a use of `target`: the same
/// symbol, or a call of a constructor when the target is its type. Not the
/// other way round, as [`View::same`] has it: asking about a constructor is
/// asking where it is called, not where its type is named.
pub(super) fn same(semantic: &Semantic, resolved: &Resolved, target: &Resolved) -> bool {
    match (resolved, target) {
        (Resolved::Symbol(a), Resolved::Symbol(b)) => {
            if a == b {
                return true;
            }
            let symbols = semantic.compilation.symbols();
            let is_constructor = |symbol: SymbolId| {
                symbols
                    .get(symbol)
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::Constructor)
            };
            is_constructor(*a) && symbols.get(*a).container == Some(*b)
        }
        (Resolved::Local { span: a, .. }, Resolved::Local { span: b, .. }) => a == b,
        _ => false,
    }
}

/// Whether a file's text can hold a use: the word, an attribute written
/// without its suffix, or — for a type or constructor — a `new(`, `base(`
/// or `this(` that names nothing.
pub(super) fn mentions(text: &str, name: &str, creations: bool) -> bool {
    contains_word(text, name)
        || attribute_stem(name).is_some_and(|stem| contains_word(text, stem))
        || (creations
            && ["new(", "new (", "base(", "base (", "this(", "this ("]
                .iter()
                .any(|call| text.contains(call)))
}

impl View<'_> {
    /// What a name refers to, as [`View::resolve`] has it — except for a
    /// delegate called through a variable. The binder records the `Invoke`
    /// the call settled on against the variable's name, since that is the
    /// method called; but `twice(3)` is a use of `twice`, and what the
    /// variable is, is recorded against the same name as a reference.
    pub fn resolve_use(&mut self, token: &SyntaxToken) -> Option<Resolved> {
        let resolved = self.resolve(token)?;
        if let Resolved::Symbol(symbol) = resolved {
            let found = self.compilation().symbols().get(symbol);
            if found.kind == SymbolKind::Method
                && found.name == "Invoke"
                && token.value_text() != "Invoke"
                && let Some(body) = self.body_for(token.parent())
            {
                match body.reference_at(token.span()) {
                    Some(BoundSymbol::Local(local)) => {
                        let local = body.locals.get(local.0 as usize)?;
                        return Some(Resolved::Local {
                            tree: self.tree,
                            span: local.span,
                            name: local.name.clone(),
                            ty: local.ty.clone(),
                        });
                    }
                    Some(BoundSymbol::Declared(variable)) => {
                        return Some(Resolved::Symbol(variable));
                    }
                    None => {}
                }
            }
        }
        Some(resolved)
    }

    /// What a name leads to, as go-to-definition and hover have it: a
    /// virtual member called on a type that overrides it is that override,
    /// as Roslyn's `GetSymbolInfo` says — `node.Destroy()` on a
    /// `PropertyNode` goes to `PropertyNode.Destroy`, not to the base's
    /// declaration. Finding uses keeps the declaration, which the overrides'
    /// uses are uses of.
    pub fn resolve_definition(&mut self, token: &SyntaxToken) -> Option<Resolved> {
        let resolved = self.resolve_use(token)?;
        let Resolved::Symbol(symbol) = resolved else {
            return Some(resolved);
        };
        Some(Resolved::Symbol(
            self.nearest_override(token, symbol).unwrap_or(symbol),
        ))
    }

    fn nearest_override(&mut self, token: &SyntaxToken, member: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation().symbols();
        let found = symbols.get(member);
        if !matches!(found.kind, SymbolKind::Method | SymbolKind::Property)
            || !(found.modifiers.contains(Modifiers::VIRTUAL)
                || found.modifiers.contains(Modifiers::ABSTRACT)
                || found.modifiers.contains(Modifiers::OVERRIDE))
        {
            return None;
        }
        let declaring = found.container?;
        let name = token.parent().clone();
        let access = name
            .parent()
            .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
            .filter(|access| access.children().last().as_ref() == Some(&name))
            .cloned();
        let receiver = match access {
            Some(access) => {
                let left = access.children().next()?;
                // `base.M()` is the base's, which binding has chosen.
                if left.kind() == SyntaxKind::BaseExpression {
                    return None;
                }
                let body = self.body_for(&left)?;
                body.type_at(left.span())?.symbol()?
            }
            // `a?.M()`: the receiver is what is before the `?`, of the
            // type it has once it is not null.
            None if name
                .parent()
                .is_some_and(|parent| parent.kind() == SyntaxKind::MemberBindingExpression) =>
            {
                let conditional = name
                    .ancestors()
                    .find(|ancestor| ancestor.kind() == SyntaxKind::ConditionalAccessExpression)?;
                let left = conditional.children().next()?;
                let body = self.body_for(&left)?;
                let ty = body.type_at(left.span())?.clone();
                let ty = self.model.binder().nullable_underlying(&ty).unwrap_or(ty);
                ty.symbol()?
            }
            // A bare name is a member of the type the code is in; one
            // anywhere else has a receiver this does not see.
            None if name.parent().is_some_and(|parent| {
                matches!(
                    parent.kind(),
                    SyntaxKind::PointerMemberAccessExpression
                        | SyntaxKind::QualifiedName
                        | SyntaxKind::AliasQualifiedName
                        | SyntaxKind::SimpleMemberAccessExpression
                )
            }) =>
            {
                return None;
            }
            None => self
                .model
                .binder()
                .context_at(self.tree, &name)
                .enclosing_type()?,
        };
        let parameters = |id: SymbolId| {
            symbols
                .get(id)
                .as_method()
                .map(|method| method.parameters.len())
        };
        let mut current = Some(receiver);
        for _ in 0..32 {
            let ty = current?;
            if ty == declaring {
                return None;
            }
            if let Some(found_override) =
                symbols
                    .lookup(ty, &found.name)
                    .iter()
                    .copied()
                    .find(|&candidate| {
                        let candidate_symbol = symbols.get(candidate);
                        candidate_symbol.kind == found.kind
                            && candidate_symbol.modifiers.contains(Modifiers::OVERRIDE)
                            && parameters(candidate) == parameters(member)
                    })
            {
                return Some(found_override);
            }
            current = self
                .model
                .binder()
                .base_class_of(ty)
                .and_then(|base| base.symbol());
        }
        None
    }

    /// The uses in this file of any of `targets`, as references.
    fn references_to(
        &mut self,
        names: &HashSet<String>,
        creations: bool,
        targets: &[Resolved],
        path: &Path,
        text: &str,
    ) -> Vec<Reference> {
        let uses = self.uses_of(names, creations);
        uses.into_iter()
            .filter(|found| {
                targets
                    .iter()
                    .any(|target| self.semantic.use_is_of(found, target))
            })
            .map(|found| Reference {
                path: path.to_path_buf(),
                span: found.span,
                kind: found.kind,
                container: self.container_name(found.span.start()),
                preview: line_preview(text, found.span.start()),
            })
            .collect()
    }

    /// Every use in this file of a name in `names`: each identifier spelled
    /// so, or spelled as an attribute's short form, bound; each `cref` in a
    /// documentation comment that ends in one; and, with `creations`, every
    /// target-typed `new()`.
    pub(super) fn uses_of(&mut self, names: &HashSet<String>, creations: bool) -> Vec<Use> {
        let stems: HashSet<&str> = names
            .iter()
            .filter_map(|name| attribute_stem(name))
            .collect();
        let root = self.root.clone();
        let with_crefs = root.full_text().contains("cref");
        let mut tokens = Vec::new();
        let mut comments = Vec::new();
        let mut news = Vec::new();
        let mut initializers = Vec::new();
        for token in root.descendant_tokens() {
            // `: base(…)` and `: this(…)` call a constructor without naming
            // its type either.
            if creations
                && matches!(
                    token.kind(),
                    SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword
                )
                && matches!(
                    token.parent().kind(),
                    SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer
                )
            {
                initializers.push(token.clone());
            }
            if token.kind() == SyntaxKind::IdentifierToken
                && (names.contains(token.value_text()) || stems.contains(token.value_text()))
            {
                tokens.push(token.clone());
            }
            if creations
                && token.kind() == SyntaxKind::NewKeyword
                && token.parent().kind() == SyntaxKind::ImplicitObjectCreationExpression
            {
                news.push(token.clone());
            }
            if with_crefs && token.full_span().start() < token.span().start() {
                for trivia in token.leading_trivia() {
                    if matches!(
                        trivia.kind(),
                        SyntaxKind::SingleLineDocumentationCommentTrivia
                            | SyntaxKind::MultiLineDocumentationCommentTrivia
                    ) && trivia.text().contains("cref")
                    {
                        comments.push((
                            trivia.span().start(),
                            trivia.text().to_string(),
                            token.clone(),
                        ));
                    }
                }
            }
        }

        let mut found = Vec::new();
        for token in tokens {
            let Some(resolved) = self.resolve_use(&token) else {
                continue;
            };
            let kind = if declares(&token, &resolved) {
                ReferenceKind::Definition
            } else if is_written(&token) {
                ReferenceKind::Write
            } else {
                ReferenceKind::Read
            };
            found.push(Use {
                span: token.span(),
                resolved,
                kind,
                creation: None,
            });
        }
        for keyword in news {
            let creation = keyword.parent().clone();
            let Some(body) = self.body_for(&creation) else {
                continue;
            };
            if let Some(Type::Named { symbol, .. }) = body.type_at(creation.span()) {
                let arguments =
                    creation
                        .child_of_kind(SyntaxKind::ArgumentList)
                        .map_or(0, |list| {
                            list.children()
                                .filter(|child| child.kind() == SyntaxKind::Argument)
                                .count()
                        });
                found.push(Use {
                    span: keyword.span(),
                    resolved: Resolved::Symbol(*symbol),
                    kind: ReferenceKind::Read,
                    creation: Some(arguments),
                });
            }
        }
        for keyword in initializers {
            let initializer = keyword.parent().clone();
            let Some(body) = self.body_for(&initializer) else {
                continue;
            };
            let constructor = body
                .statements
                .iter()
                .find_map(|statement| match &statement.kind {
                    rustlyn_semantics::BoundStatementKind::ConstructorInitializer {
                        constructor: Some(constructor),
                        ..
                    } => Some(*constructor),
                    _ => None,
                });
            if let Some(constructor) = constructor {
                found.push(Use {
                    span: keyword.span(),
                    resolved: Resolved::Symbol(constructor),
                    kind: ReferenceKind::Read,
                    creation: None,
                });
            }
        }
        for (start, comment, documented) in comments {
            for (at, cref) in crefs(&comment) {
                let parts = cref_parts(cref);
                for (index, &(offset, name, _)) in parts.iter().enumerate() {
                    if !names.contains(name) {
                        continue;
                    }
                    if let Some(symbol) = self.resolve_cref(&documented, &parts[..=index]) {
                        found.push(Use {
                            span: TextSpan::new(start + (at + offset) as u32, name.len() as u32),
                            resolved: Resolved::Symbol(symbol),
                            kind: ReferenceKind::Read,
                            creation: None,
                        });
                    }
                }
            }
        }
        found.sort_by_key(|found| found.span.start());
        found
    }

    /// What the path of a `cref` names, looked up from the declaration it
    /// documents: `Name`, `Type.Member`, `Namespace.Type`, `Type{T}`.
    fn resolve_cref(
        &self,
        documented: &SyntaxToken,
        parts: &[(usize, &str, usize)],
    ) -> Option<SymbolId> {
        let compilation = self.compilation();
        let symbols = compilation.symbols();
        let binder = self.model.binder();
        let mut declaration = documented.parent().clone();
        if declaration.kind() == SyntaxKind::AttributeList
            && let Some(parent) = declaration.parent().cloned()
        {
            declaration = parent;
        }
        let context = binder.context_at(self.tree, &declaration);

        let &(_, first, first_arity) = parts.first()?;
        // The first part: a namespace from the global one, a type in scope, or
        // a member of the type being documented or one around it.
        let mut current = symbols
            .lookup_namespace(compilation.global_namespace(), first)
            .or_else(|| binder.lookup(first, first_arity, &context));
        if current.is_none() {
            let mut scopes: Vec<SymbolId> = Vec::new();
            if let Some(declared) = self.model.declared_symbol(&declaration)
                && symbols.get(declared).kind == SymbolKind::NamedType
            {
                scopes.push(declared);
            }
            scopes.extend(context.enclosing_types());
            current = scopes
                .into_iter()
                .find_map(|scope| binder.lookup_member(scope, first).first().copied());
        }
        let mut current = current?;
        for &(_, part, arity) in &parts[1..] {
            let found = symbols.get(current);
            current = match found.kind {
                SymbolKind::Namespace => symbols
                    .lookup_namespace(current, part)
                    .or_else(|| symbols.lookup_type(current, part, arity))?,
                SymbolKind::NamedType => symbols
                    .lookup_type(current, part, arity)
                    .or_else(|| binder.lookup_member(current, part).first().copied())?,
                _ => return None,
            };
        }
        Some(current)
    }

    /// The member or type the text at `offset` is written in, as a results
    /// window names it: `Game.Run`, `Outer.Inner`.
    pub(super) fn container_name(&self, offset: u32) -> String {
        let Some(token) = self.root.find_token(offset) else {
            return String::new();
        };
        container_name(token.parent())
    }
}

/// Whether `token` is the name its declaration gives, rather than a use.
pub(super) fn declares(token: &SyntaxToken, resolved: &Resolved) -> bool {
    match resolved {
        Resolved::Local { span, .. } => *span == token.span(),
        Resolved::Symbol(_) => names_declaration(token.parent(), token),
    }
}

/// Whether the name `token` is written to where it stands: the target of an
/// assignment, compound or not; incremented or decremented; passed by `ref`
/// or `out`; or one of the variables a deconstruction assigns.
pub(super) fn is_written(token: &SyntaxToken) -> bool {
    let mut node = token.parent().clone();
    if !matches!(
        node.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) {
        return false;
    }
    loop {
        let Some(parent) = node.parent().cloned() else {
            return false;
        };
        match parent.kind() {
            // `this.count = 0` writes `count`; `a.b = 1` writes `b`, not `a`.
            SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::PointerMemberAccessExpression
            | SyntaxKind::MemberBindingExpression
            | SyntaxKind::QualifiedName => {
                if parent.children().last().as_ref() != Some(&node) {
                    return false;
                }
                node = parent;
            }
            SyntaxKind::ParenthesizedExpression => node = parent,
            kind if is_assignment(kind) => {
                return parent.children().next().as_ref() == Some(&node);
            }
            SyntaxKind::PreIncrementExpression
            | SyntaxKind::PreDecrementExpression
            | SyntaxKind::PostIncrementExpression
            | SyntaxKind::PostDecrementExpression => return true,
            SyntaxKind::Argument => {
                if parent.child_tokens().any(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::OutKeyword | SyntaxKind::RefKeyword
                    )
                }) {
                    return true;
                }
                // `(a, b) = pair`: an element of a tuple on the left.
                match parent.parent() {
                    Some(tuple) if tuple.kind() == SyntaxKind::TupleExpression => {
                        node = tuple.clone();
                    }
                    _ => return false,
                }
            }
            _ => return false,
        }
    }
}

const fn is_assignment(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::SimpleAssignmentExpression
            | SyntaxKind::AddAssignmentExpression
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

/// The member or type `node` is in, named from the syntax so that it works on
/// text nobody compiled: the enclosing types and member, dotted.
pub(super) fn container_name(node: &SyntaxNode) -> String {
    let mut parts = Vec::new();
    let mut member_found = false;
    for ancestor in std::iter::once(node.clone()).chain(node.ancestors()) {
        let kind = ancestor.kind();
        let is_type = matches!(
            kind,
            SyntaxKind::ClassDeclaration
                | SyntaxKind::StructDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::RecordDeclaration
                | SyntaxKind::RecordStructDeclaration
                | SyntaxKind::EnumDeclaration
        );
        let is_member = matches!(
            kind,
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::DestructorDeclaration
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::EventDeclaration
                | SyntaxKind::DelegateDeclaration
                | SyntaxKind::EnumMemberDeclaration
                | SyntaxKind::VariableDeclarator
        ) && !member_found;
        // A local's declarator is not a member; a field's is.
        if kind == SyntaxKind::VariableDeclarator
            && !ancestor.ancestors().any(|outer| {
                matches!(
                    outer.kind(),
                    SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                )
            })
        {
            continue;
        }
        if kind == SyntaxKind::IndexerDeclaration && !member_found {
            member_found = true;
            parts.push("this[]".to_string());
            continue;
        }
        if kind == SyntaxKind::OperatorDeclaration && !member_found {
            member_found = true;
            parts.push("operator".to_string());
            continue;
        }
        if (is_type || is_member)
            && let Some(name) = ancestor
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        {
            if is_member {
                member_found = true;
            }
            parts.push(name.value_text().to_string());
        }
    }
    parts.reverse();
    parts.join(".")
}

/// The line of `text` that `offset` is on, without indentation or line end.
pub(super) fn line_preview(text: &str, offset: u32) -> String {
    let offset = (offset as usize).min(text.len());
    let start = text[..offset].rfind('\n').map_or(0, |at| at + 1);
    let end = text[offset..]
        .find('\n')
        .map_or(text.len(), |at| offset + at);
    text[start..end].trim().to_string()
}

/// Every `cref="..."` in a comment: where its value starts in the comment,
/// and the value.
fn crefs(comment: &str) -> Vec<(usize, &str)> {
    let mut found = Vec::new();
    let mut from = 0;
    while let Some(at) = comment[from..].find("cref") {
        let mut index = from + at + 4;
        let bytes = comment.as_bytes();
        while index < bytes.len() && bytes[index].is_ascii_whitespace() {
            index += 1;
        }
        if index < bytes.len() && bytes[index] == b'=' {
            index += 1;
            while index < bytes.len() && bytes[index].is_ascii_whitespace() {
                index += 1;
            }
            if index < bytes.len() && (bytes[index] == b'"' || bytes[index] == b'\'') {
                let quote = bytes[index];
                let start = index + 1;
                if let Some(length) = comment[start..].find(quote as char) {
                    found.push((start, &comment[start..start + length]));
                    index = start + length;
                }
            }
        }
        from = index.max(from + at + 4);
    }
    found
}

/// The names a cref's dotted path spells, each with where it starts in the
/// cref and its arity: `N.List{T}.Add(T)` is `N`, `List` of one and `Add`.
/// A `T:` prefix and a parameter list are left out.
fn cref_parts<'a>(cref: &'a str) -> Vec<(usize, &'a str, usize)> {
    let bytes = cref.as_bytes();
    let from = if bytes.len() > 2 && bytes[1] == b':' && bytes[0].is_ascii_uppercase() {
        2
    } else {
        0
    };
    let end = cref.find('(').unwrap_or(cref.len());
    let mut parts = Vec::new();
    let push = |start: usize, end: usize, parts: &mut Vec<(usize, &'a str, usize)>| {
        let segment = &cref[start..end];
        let (name, arity) = match segment.find(['{', '<']) {
            Some(open) => (&segment[..open], segment[open..].matches(',').count() + 1),
            None => (segment, 0),
        };
        let leading = name.len() - name.trim_start().len();
        let name = name.trim();
        let (skip, name) = match name.strip_prefix('@') {
            Some(rest) => (1, rest),
            None => (0, name),
        };
        if !name.is_empty() {
            parts.push((start + leading + skip, name, arity));
        }
    };
    let mut depth = 0usize;
    let mut start = from;
    for (index, &byte) in bytes.iter().enumerate().take(end).skip(from) {
        match byte {
            b'{' | b'<' => depth += 1,
            b'}' | b'>' => depth = depth.saturating_sub(1),
            b'.' if depth == 0 => {
                push(start, index, &mut parts);
                start = index + 1;
            }
            _ => {}
        }
    }
    if start < end {
        push(start, end, &mut parts);
    }
    parts
}

/// A member's name without the interface an explicit implementation puts in
/// front of it.
pub(super) fn short_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// The types of the project that derive from each type or implement it,
/// all the way down: where the overrides and implementations of a member
/// can be. One walk over the project's types answers it for every member a
/// question cascades from, rather than one walk per member.
#[derive(Debug, Default)]
pub(super) struct Derived {
    by_base: HashMap<SymbolId, Vec<SymbolId>>,
}

impl Derived {
    fn new(semantic: &Semantic, model: &SemanticModel<'_>) -> Self {
        let mut by_base: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
        for ty in semantic.compilation.symbols().iter().filter(|candidate| {
            candidate.kind == SymbolKind::NamedType
                && !candidate.locations.is_empty()
                && !semantic.compilation.is_from_metadata(candidate.id)
        }) {
            for base in all_bases(model, ty.id) {
                by_base.entry(base).or_default().push(ty.id);
            }
        }
        Self { by_base }
    }

    /// The project's types below `ty`.
    fn from(&self, ty: SymbolId) -> &[SymbolId] {
        self.by_base.get(&ty).map_or(&[], Vec::as_slice)
    }
}

/// Every type `ty` derives from or implements, all the way up.
fn all_bases(model: &SemanticModel<'_>, ty: SymbolId) -> Vec<SymbolId> {
    let mut found = Vec::new();
    let mut queue = vec![ty];
    let mut seen = HashSet::new();
    while let Some(current) = queue.pop() {
        if !seen.insert(current) {
            continue;
        }
        if current != ty {
            found.push(current);
        }
        for base in model.base_types_of(current) {
            if let Type::Named { symbol, .. } = base {
                queue.push(symbol);
            }
        }
    }
    found
}

/// Whether two members take the same parameters, as far as it can be told
/// without substituting type arguments: a type parameter on either side
/// matches anything.
fn same_signature(model: &SemanticModel<'_>, a: SymbolId, b: SymbolId) -> bool {
    let symbols = model.compilation().symbols();
    let parameters = |symbol: SymbolId| -> Vec<SymbolId> {
        let found = symbols.get(symbol);
        found
            .as_method()
            .map(|method| method.parameters.clone())
            .or_else(|| {
                found
                    .as_property()
                    .map(|property| property.parameters.clone())
            })
            .unwrap_or_default()
    };
    let arity = |symbol: SymbolId| {
        symbols
            .get(symbol)
            .as_method()
            .map_or(0, |method| method.arity)
    };
    let (left, right) = (parameters(a), parameters(b));
    if left.len() != right.len() || arity(a) != arity(b) {
        return false;
    }
    left.iter().zip(&right).all(|(&left, &right)| {
        let (left, right) = (model.type_of_symbol(left), model.type_of_symbol(right));
        matches!(left, Type::TypeParameter(_))
            || matches!(right, Type::TypeParameter(_))
            || left.display(symbols) == right.display(symbols)
    })
}

#[cfg(test)]
mod tests {
    use super::super::tests::{at, compile};
    use super::*;

    /// The references at `marker`, as `(file, text at the span, kind)`.
    fn references(
        semantic: &Semantic,
        files: &[(&str, &str)],
        file: &str,
        marker: &str,
        into: usize,
    ) -> Vec<(String, String, ReferenceKind)> {
        let text = files
            .iter()
            .find(|(name, _)| *name == file)
            .map(|(_, text)| *text)
            .expect("the file");
        let (_, found) = semantic
            .references_detailed(
                Path::new(&format!("/p/{file}")),
                at(text, marker, into),
                None,
            )
            .expect("resolved");
        found
            .iter()
            .map(|reference| {
                let name = reference
                    .path
                    .file_name()
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                let text = files.iter().find(|(file, _)| *file == name).unwrap().1;
                let spelled = text[reference.span.start() as usize..reference.span.end() as usize]
                    .to_string();
                (name, spelled, reference.kind)
            })
            .collect()
    }

    #[test]
    fn each_reference_says_whether_it_declares_writes_or_reads() {
        let text = "class Counter {\n  int count;\n  void Up() { count++; count += 2; this.count = 0; }\n  int Get() => count;\n  void Pass() { Set(ref count); Out(out count); (count, count) = (1, 2); }\n  void Set(ref int x) { }\n  void Out(out int x) { x = 0; }\n}\n";
        let files = [("C.cs", text)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "C.cs", "count;", 0);
        let kinds: Vec<ReferenceKind> = found.iter().map(|(_, _, kind)| *kind).collect();
        use ReferenceKind::{Definition, Read, Write};
        assert_eq!(
            kinds,
            vec![
                Definition, Write, Write, Write, Read, Write, Write, Write, Write
            ],
            "{found:?}"
        );
    }

    #[test]
    fn a_reference_knows_its_member_and_its_line() {
        let a = "namespace Game {\n  class Pawn { public int Health; }\n}\n";
        let b = "namespace Game {\n  class Arena {\n    void Fight(Pawn p) {\n      p.Health -= 1;\n    }\n  }\n}\n";
        let semantic = compile(&[("A.cs", a), ("B.cs", b)], false).expect("compiled");
        let (word, found) = semantic
            .references_detailed(Path::new("/p/A.cs"), at(a, "Health", 0), None)
            .expect("resolved");
        assert_eq!(word, "Health");
        assert_eq!(found.len(), 2, "{found:?}");
        assert_eq!(found[0].container, "Pawn.Health");
        assert_eq!(found[0].kind, ReferenceKind::Definition);
        assert_eq!(found[1].container, "Arena.Fight");
        assert_eq!(found[1].preview, "p.Health -= 1;");
        assert_eq!(found[1].kind, ReferenceKind::Write);
    }

    #[test]
    fn an_interface_method_brings_its_implementations() {
        let shapes = "interface IShape { double Area(); }\n\
                      class Square : IShape { public double Area() => 4; }\n\
                      class Circle : IShape { public double Area() => 3; double Twice() => Area() * 2; }\n\
                      class Other { public double Area() => 0; }\n";
        let user = "class User { double Sum(IShape s, Square q) => s.Area() + q.Area(); }\n";
        let files = [("Shapes.cs", shapes), ("User.cs", user)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "Shapes.cs", "Area()", 0);
        let definitions = found
            .iter()
            .filter(|(_, _, kind)| *kind == ReferenceKind::Definition)
            .count();
        // The interface's and the two implementations', not `Other`'s.
        assert_eq!(definitions, 3, "{found:?}");
        let reads: Vec<&(String, String, ReferenceKind)> = found
            .iter()
            .filter(|(_, _, kind)| *kind == ReferenceKind::Read)
            .collect();
        assert_eq!(reads.len(), 3, "{found:?}");
    }

    #[test]
    fn an_override_brings_the_method_it_overrides() {
        let text = "abstract class Animal { public abstract string Speak(); public virtual int Legs => 4; }\n\
                    class Dog : Animal { public override string Speak() => \"woof\"; public override int Legs => 4; }\n\
                    class Use { string U(Animal a) => a.Speak(); }\n";
        let files = [("A.cs", text)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "A.cs", "Speak() => \"woof\"", 0);
        assert_eq!(found.len(), 3, "{found:?}");
        let found = references(&semantic, &files, "A.cs", "Legs", 0);
        assert_eq!(found.len(), 2, "{found:?}");
    }

    /// `void IWidget.Pick()` is named `IWidget.Pick`, but nothing spells
    /// that: it is found as `Pick`, and with the interface's member.
    #[test]
    fn an_explicit_implementation_is_found_by_its_short_name() {
        let text = "interface IWidget { void Pick(); }\n\
                    class Widget : IWidget { void IWidget.Pick() { } }\n\
                    class Use { void U(IWidget w) => w.Pick(); }\n";
        let files = [("A.cs", text)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "A.cs", "Pick() { }", 0);
        use ReferenceKind::{Definition, Read};
        assert_eq!(
            found,
            vec![
                ("A.cs".to_string(), "Pick".to_string(), Definition),
                ("A.cs".to_string(), "Pick".to_string(), Definition),
                ("A.cs".to_string(), "Pick".to_string(), Read),
            ]
        );
    }

    #[test]
    fn target_typed_new_calls_the_constructor() {
        let a = "class Thing { public Thing() { } public Thing(int size) { } }\n";
        let b =
            "class User { Thing t = new(); void M() { Take(new(3)); } void Take(Thing t) { } }\n";
        let files = [("A.cs", a), ("B.cs", b)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "A.cs", "Thing(int", 0);
        let news: Vec<_> = found.iter().filter(|(_, text, _)| text == "new").collect();
        assert_eq!(news.len(), 1, "{found:?}");
        let found = references(&semantic, &files, "A.cs", "Thing {", 0);
        let news: Vec<_> = found.iter().filter(|(_, text, _)| text == "new").collect();
        assert_eq!(news.len(), 2, "{found:?}");
    }

    #[test]
    fn base_and_this_initializers_call_the_constructor() {
        let a = "class Unit { public Unit(int hp) { } public Unit() : this(10) { } }\n";
        let b = "class Tank : Unit { public Tank() : base(500) { } }\n";
        let files = [("A.cs", a), ("B.cs", b)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "A.cs", "Unit(int", 0);
        let spelled: Vec<&str> = found.iter().map(|(_, text, _)| text.as_str()).collect();
        assert_eq!(spelled, vec!["Unit", "this", "base"], "{found:?}");
        let found = references(&semantic, &files, "A.cs", "Unit() :", 0);
        assert!(
            !found
                .iter()
                .any(|(_, text, _)| text == "base" || text == "this"),
            "{found:?}"
        );
    }

    #[test]
    fn nameof_crefs_and_attributes_are_references() {
        let text = "using System;\n\
                    class MarkAttribute : Attribute { }\n\
                    /// <summary>Uses <see cref=\"Helper.Run\"/> and <see cref=\"Helper\"/>.</summary>\n\
                    [Mark]\n\
                    class Helper { public static void Run() { } string N() => nameof(Run); }\n\
                    [MarkAttribute] class Other { }\n";
        let files = [("H.cs", text)];
        let semantic = compile(&files, false).expect("compiled");
        let run = references(&semantic, &files, "H.cs", "Run()", 0);
        let spelled: Vec<&str> = run.iter().map(|(_, text, _)| text.as_str()).collect();
        assert_eq!(spelled, vec!["Run", "Run", "Run"], "{run:?}");
        let helper = references(&semantic, &files, "H.cs", "Helper {", 0);
        assert_eq!(helper.len(), 3, "{helper:?}");
        let mark = references(&semantic, &files, "H.cs", "MarkAttribute :", 0);
        assert_eq!(mark.len(), 3, "{mark:?}");
    }

    #[test]
    fn crefs_are_found_and_split() {
        assert_eq!(
            crefs("/// <see cref=\"A.B\"/> <see cref='C'/>"),
            vec![(15, "A.B"), (33, "C")]
        );
        assert_eq!(
            cref_parts("N.List{T}.Add(T)"),
            vec![(0, "N", 0), (2, "List", 1), (10, "Add", 0)]
        );
        assert_eq!(
            cref_parts("T:System.String"),
            vec![(2, "System", 0), (9, "String", 0)]
        );
    }

    #[test]
    fn a_local_is_searched_in_its_body_only() {
        let text = "class C { void M() { int n = 1; n = n + 1; } void O() { int n = 2; } }\n";
        let files = [("C.cs", text)];
        let semantic = compile(&files, false).expect("compiled");
        let found = references(&semantic, &files, "C.cs", "n = 1", 0);
        let kinds: Vec<ReferenceKind> = found.iter().map(|(_, _, kind)| *kind).collect();
        assert_eq!(
            kinds,
            vec![
                ReferenceKind::Definition,
                ReferenceKind::Write,
                ReferenceKind::Read
            ]
        );
    }

    // MARK: - cascading, and delegates called through a variable

    #[test]
    fn an_implementation_reaches_the_other_implementations() {
        let text = "interface IShape { double Area(); }\n\
                    class Square : IShape { public double Area() => 1; }\n\
                    class Circle : IShape { public double Area() => 2; }\n\
                    class User { double M(IShape s, Square q) => s.Area() + q.Area(); }\n";
        let files = [("C.cs", text)];
        let semantic = compile(&files, false).expect("compiled");
        // From Square's `Area`: the interface's, Circle's, and both calls.
        let found = references(&semantic, &files, "C.cs", "Area() => 1", 0);
        let definitions = found
            .iter()
            .filter(|(_, _, kind)| *kind == ReferenceKind::Definition)
            .count();
        assert_eq!(definitions, 3, "{found:?}");
        assert_eq!(found.len(), 5, "{found:?}");
    }

    #[test]
    fn a_delegate_called_through_a_variable_is_the_variable() {
        let text = "using System;\n\
                    class C {\n\
                      Func<int, int> twice = x => x * 2;\n\
                      int M(Func<int, int> apply) { Func<int, int> local = apply; return twice(3) + apply(1) + local(2); }\n\
                    }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let path = Path::new("/p/C.cs");
        let definition = |marker: &str| {
            let (_, found) = semantic
                .definition(path, at(text, marker, 0), None)
                .expect("resolved");
            match &found[0].place {
                super::super::Place::Source { span, .. } => {
                    text[span.start() as usize..span.end() as usize].to_string()
                }
                super::super::Place::Metadata { .. } => "metadata".to_string(),
            }
        };
        assert!(definition("twice(3)").starts_with("twice"));
        assert!(definition("apply(1)").contains("apply"));
        assert!(definition("local(2)").contains("local"));
        let info = semantic
            .quick_info(path, at(text, "twice(3)", 0), None)
            .expect("quick info");
        assert!(info.description.contains("twice"), "{}", info.description);
        // And it is counted as a use of the field, not left unread.
        let unread: Vec<String> = semantic
            .analyzer_diagnostics(path, None)
            .unwrap()
            .into_iter()
            .filter(|found| found.id == "IDE0052")
            .map(|found| found.message)
            .collect();
        assert!(unread.is_empty(), "{unread:?}");
    }
}
