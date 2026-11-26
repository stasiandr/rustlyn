//! CS0612, CS0618 and CS0619: a body naming something declared
//! `[Obsolete]`.
//!
//! A declaration in the source says so with its attribute, an assembly's
//! type or member with the one the loader read (see `Loaded::obsolete`).
//! Code that is itself obsolete may use obsolete things freely, as Roslyn
//! has it, and so is not looked at either.

use std::collections::HashMap;

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, TokenValue};
use rustlyn_text::TextSpan;

use crate::binder::{Binder, Diagnostics};
use crate::bound::{BoundBody, BoundSymbol};
use crate::checks::member_display;
use crate::compilation::Compilation;
use crate::fxhash::FxHashMap;
use crate::symbol::{SymbolId, SymbolKind};
use crate::types::Type;

/// What an `[Obsolete]` says: its message, if it gave one, and whether it
/// makes a use an error.
#[derive(Clone, Debug)]
pub(crate) struct Obsolete {
    message: Option<String>,
    error: bool,
}

/// Adds a diagnostic for every name in `body` that means an obsolete member
/// or type of the source.
pub(crate) fn check(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    member: Option<SymbolId>,
    body: &mut BoundBody,
) {
    let compilation = binder.compilation();
    if within_obsolete(compilation, member) {
        return;
    }
    let mut uses: Vec<(TextSpan, SymbolId)> = body
        .references
        .iter()
        .filter_map(|(span, symbol)| match symbol {
            BoundSymbol::Declared(symbol) => Some((*span, *symbol)),
            BoundSymbol::Local(_) => None,
        })
        .filter(|(_, symbol)| {
            matches!(
                compilation.symbols().get(*symbol).kind,
                SymbolKind::NamedType
                    | SymbolKind::Method
                    | SymbolKind::Field
                    | SymbolKind::Property
                    | SymbolKind::Event
            )
        })
        .collect();
    // `new Popup("title")` uses the constructor it calls as well as the type
    // it names, and is reported from its `new` (Roslyn's location).
    body.each_expression(&mut |expression| {
        if let crate::bound::BoundExpressionKind::ObjectCreation {
            constructor: Some(constructor),
            ..
        } = expression.kind
        {
            uses.push((expression.span, constructor));
        }
    });
    uses.sort_by_key(|(span, _)| (span.start(), span.end()));
    uses.dedup();
    for (span, symbol) in uses {
        // The declaration's own name is not a use of it.
        if compilation
            .symbols()
            .get(symbol)
            .locations
            .iter()
            .any(|location| location.tree == tree && location.span == span)
        {
            continue;
        }
        let Some(obsolete) = obsolete(compilation, symbol) else {
            continue;
        };
        // `nameof` names a member without using it; a type it names is
        // used all the same, and Roslyn warns about it.
        let is_type = compilation.symbols().get(symbol).kind == SymbolKind::NamedType;
        if (!is_type && in_nameof(declaration, span))
            || names_a_type_too(binder, tree, declaration, span, symbol)
        {
            continue;
        }
        // A type as the use constructs it, without its namespace, as Roslyn
        // words it: `'UiInstance<GuiRewardCellComponent>' is obsolete`.
        let name = if compilation.symbols().get(symbol).kind == SymbolKind::NamedType {
            body.type_at(span)
                .filter(|ty| ty.symbol() == Some(symbol))
                .cloned()
                .or_else(|| written_type(binder, tree, declaration, span, symbol))
                .unwrap_or_else(|| Type::named(symbol))
                .display(compilation.symbols())
        } else {
            member_display(compilation, symbol, &Default::default(), None)
        };
        let span = whole_access(declaration, span);
        body.diagnostics
            .push((tree, diagnostic(&obsolete, span, &name)));
    }
}

/// The same for what a file declares outside its bodies: the types its
/// signatures, field types, base lists and constraints name, and what its
/// attributes and parameters' default values use. `[IncludeStash(typeof(
/// UiInstanceLink))]` and `List<UiInstance<T>> items` warn as a body would.
pub(crate) fn check_declarations(binder: &Binder<'_>, tree: usize, found: &mut Diagnostics) {
    let compilation = binder.compilation();
    let Some(syntax) = compilation.trees().get(tree) else {
        return;
    };
    let root = syntax.root();
    // Nothing obsolete anywhere: nothing to look for.
    if !compilation.has_obsolete() {
        return;
    }
    let in_a_body = |node: &SyntaxNode| {
        node.ancestors().any(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
            )
        })
    };
    let mut signature_memo = FxHashMap::default();
    for node in root.descendants() {
        if matches!(
            node.kind(),
            SyntaxKind::Attribute | SyntaxKind::EqualsValueClause
        ) && in_a_body(&node)
        {
            continue;
        }
        match node.kind() {
            SyntaxKind::IdentifierName
            | SyntaxKind::GenericName
            | SyntaxKind::QualifiedName
            | SyntaxKind::AliasQualifiedName
                if in_a_signature(&node, &mut signature_memo) =>
            {
                type_named(binder, tree, &node, found);
            }
            SyntaxKind::Attribute => {
                let Some(declaration) = node.parent().and_then(|list| list.parent()).cloned()
                else {
                    continue;
                };
                let member = declared_at(binder, tree, &declaration);
                if !within_obsolete(compilation, member) {
                    attribute_used(binder, tree, &declaration, &node, found);
                }
                let mut body = crate::body::BodyBinder::bind_attribute_for_editor(
                    binder,
                    tree,
                    &declaration,
                    &node,
                );
                body.diagnostics.clear();
                check(binder, tree, &node, member, &mut body);
                found.extend(body.diagnostics);
            }
            SyntaxKind::EqualsValueClause
                if node
                    .parent()
                    .is_some_and(|parent| parent.kind() == SyntaxKind::Parameter) =>
            {
                let Some(value) = node.children().find(|child| child.kind().is_expression()) else {
                    continue;
                };
                let Some(declaration) = node.ancestors().find(|ancestor| {
                    !matches!(
                        ancestor.kind(),
                        SyntaxKind::Parameter
                            | SyntaxKind::ParameterList
                            | SyntaxKind::BracketedParameterList
                    )
                }) else {
                    continue;
                };
                if declaration.kind().is_expression() {
                    // A lambda's parameter: its body binds it.
                    continue;
                }
                let member = declared_at(binder, tree, &declaration);
                let mut body = crate::body::BodyBinder::bind_default_for_editor(
                    binder,
                    tree,
                    &declaration,
                    &value,
                );
                body.diagnostics.clear();
                check(binder, tree, &node, member, &mut body);
                found.extend(body.diagnostics);
            }
            _ => {}
        }
    }
}

/// `[LocalEvent("x")]` uses the attribute class and the constructor it
/// calls: either may be obsolete. Reported at the attribute's name.
fn attribute_used(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    attribute: &SyntaxNode,
    found: &mut Diagnostics,
) {
    let compilation = binder.compilation();
    let Some(name) = attribute
        .children()
        .find(|child| child.kind().is_type_node())
    else {
        return;
    };
    let Some(bound) = crate::body::BodyBinder::bind_attribute(binder, tree, declaration, attribute)
    else {
        return;
    };
    let span = match name.kind() {
        SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => name
            .children()
            .nth(1)
            .map_or(name.span(), |right| right.span()),
        _ => name.span(),
    };
    // `[Drawer(Expanded = true)]` sets a property that may be obsolete,
    // reported at its name.
    for (member, _) in &bound.named {
        let Some(obsolete) = obsolete(compilation, *member) else {
            continue;
        };
        let wanted = &compilation.symbols().get(*member).name;
        let Some(at) = attribute
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::NameEquals)
            .filter_map(|equals| equals.descendant_tokens().next())
            .find(|token| token.value_text() == wanted.as_str())
        else {
            continue;
        };
        let shown = member_display(compilation, *member, &Default::default(), None);
        found.push((tree, diagnostic(&obsolete, at.span(), &shown)));
    }
    if let Some(ty) = bound.ty.symbol()
        && let Some(obsolete) = obsolete(compilation, ty)
    {
        let shown = bound.ty.display(compilation.symbols());
        found.push((tree, diagnostic(&obsolete, span, &shown)));
    } else if let Some(constructor) = bound.constructor
        && let Some(obsolete) = obsolete(compilation, constructor)
    {
        let shown = member_display(compilation, constructor, &Default::default(), None);
        found.push((tree, diagnostic(&obsolete, span, &shown)));
    }
}

/// A type named outside any body, by the whole of its name: not a part of a
/// qualified one, a `using`, a namespace's name or an attribute, which are
/// looked at otherwise or not at all.
///
/// `seen` holds what the nodes passed on the way up came to, by where they
/// are in the tree: a name deep in a long chain climbs the whole chain, and
/// the next name climbs only as far as the first node already answered for.
fn in_a_signature(node: &SyntaxNode, seen: &mut FxHashMap<(usize, u32), bool>) -> bool {
    if node.parent().is_some_and(|parent| {
        matches!(
            parent.kind(),
            SyntaxKind::QualifiedName
                | SyntaxKind::AliasQualifiedName
                | SyntaxKind::NamespaceDeclaration
                | SyntaxKind::FileScopedNamespaceDeclaration
                | SyntaxKind::Attribute
        )
    }) {
        return false;
    }
    // Nearest first: a local function's signature is reached before the
    // body around it, its own body before the function.
    let mut passed = Vec::new();
    let mut answer = true;
    for ancestor in node.ancestors() {
        let at = (
            std::sync::Arc::as_ptr(ancestor.green()) as usize,
            ancestor.full_span().start(),
        );
        if let Some(&known) = seen.get(&at) {
            answer = known;
            break;
        }
        if ancestor.kind() == SyntaxKind::LocalFunctionStatement {
            answer = true;
            break;
        }
        if matches!(
            ancestor.kind(),
            SyntaxKind::Block
                | SyntaxKind::ArrowExpressionClause
                | SyntaxKind::EqualsValueClause
                | SyntaxKind::AttributeList
                | SyntaxKind::UsingDirective
                | SyntaxKind::ExternAliasDirective
                | SyntaxKind::ArgumentList
                | SyntaxKind::BracketedArgumentList
        ) {
            answer = false;
            break;
        }
        passed.push(at);
    }
    for at in passed {
        seen.insert(at, answer);
    }
    answer
}

/// CS0612, CS0618 or CS0619 for a type named in a signature, where it is
/// obsolete and what names it is not.
fn type_named(binder: &Binder<'_>, tree: usize, node: &SyntaxNode, found: &mut Diagnostics) {
    let compilation = binder.compilation();
    let context = binder.context_at(tree, node);
    let Some(symbol) = binder.resolve_namespace_or_type(node, &context) else {
        return;
    };
    if compilation.symbols().get(symbol).kind != SymbolKind::NamedType {
        return;
    }
    let Some(obsolete) = obsolete(compilation, symbol) else {
        return;
    };
    let declaration = node
        .ancestors()
        .find(|ancestor| declared_at(binder, tree, ancestor).is_some());
    if within_obsolete(
        compilation,
        declaration.and_then(|declaration| declared_at(binder, tree, &declaration)),
    ) {
        return;
    }
    // The whole name, as Roslyn has it: `A.B` from `A`.
    let span = node.span();
    let mut sink = crate::binder::Diagnostics::new();
    let ty = match binder.resolve_type(node, &context, &mut sink) {
        resolved if resolved.symbol() == Some(symbol) => resolved,
        _ => Type::named(symbol),
    };
    let name = ty.display(compilation.symbols());
    found.push((tree, diagnostic(&obsolete, span, &name)));
}

/// The symbol a declaration node declares, if it declares one: a field's
/// declarator rather than its declaration.
fn declared_at(binder: &Binder<'_>, tree: usize, node: &SyntaxNode) -> Option<SymbolId> {
    let node = match node.kind() {
        SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => node
            .descendants()
            .find(|child| child.kind() == SyntaxKind::VariableDeclarator)?,
        _ => node.clone(),
    };
    binder.declared_symbol_at(tree, &node)
}

fn diagnostic(obsolete: &Obsolete, span: TextSpan, name: &str) -> Diagnostic {
    match (&obsolete.message, obsolete.error) {
        (Some(message), true) => {
            Diagnostic::new(ErrorCode::ErrDeprecatedSymbolStr, span, &[name, message])
        }
        (None, true) => Diagnostic::new(ErrorCode::ErrDeprecatedSymbolStr, span, &[name, ""]),
        (Some(message), false) => {
            Diagnostic::new(ErrorCode::WrnDeprecatedSymbolStr, span, &[name, message])
        }
        (None, false) => Diagnostic::new(ErrorCode::WrnDeprecatedSymbol, span, &[name]),
    }
}

/// Whether the code being bound is inside something obsolete itself: the
/// member, or a type around it.
fn within_obsolete(compilation: &Compilation, member: Option<SymbolId>) -> bool {
    let mut current = member;
    while let Some(symbol) = current {
        if obsolete(compilation, symbol).is_some() {
            return true;
        }
        current = compilation.symbols().get(symbol).container;
    }
    false
}

/// The `[Obsolete]` on a symbol's declaration.
fn obsolete(compilation: &Compilation, symbol: SymbolId) -> Option<Obsolete> {
    if compilation.is_from_metadata(symbol) {
        return compilation
            .loaded
            .obsolete
            .get(&symbol)
            .map(|(message, error)| Obsolete {
                message: message.clone(),
                error: *error,
            });
    }
    compilation
        .obsolete
        .get_or_init(|| declared_obsolete(compilation))
        .get(&symbol)
        .cloned()
}

/// Every declaration in the source with an `[Obsolete]` on it. A file that
/// never says `Obsolete` is neither parsed nor walked.
///
/// The text is asked before the tree: a compilation read back from disk
/// parses a tree the first time it is asked for, and asking for every tree
/// here parsed the whole project to find the handful of files that say
/// `Obsolete` — seconds on a large one, and every tree kept after.
fn declared_obsolete(compilation: &Compilation) -> HashMap<SymbolId, Obsolete> {
    let mut found = HashMap::new();
    for tree in compilation.corlib_trees..compilation.trees().len() {
        if !says(compilation, tree, "Obsolete") {
            continue;
        }
        let Some(syntax) = compilation.trees().get(tree) else {
            continue;
        };
        for list in syntax
            .root()
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::AttributeList)
        {
            let Some(declaration) = list.parent() else {
                continue;
            };
            let Some(obsolete) = attribute_of(declaration) else {
                continue;
            };
            // A field's attributes are on the declaration that holds its
            // declarators, and each declarator is a symbol.
            let declared: Vec<SyntaxNode> = match declaration.kind() {
                SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => declaration
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                    .collect(),
                _ => vec![declaration.clone()],
            };
            for node in declared {
                if let Some(symbol) = compilation.declared_symbol(tree, node.span()) {
                    found.insert(symbol, obsolete.clone());
                }
            }
        }
    }
    found
}

/// Whether the text of file `tree` has `word` in it, read without parsing it.
pub(crate) fn says(compilation: &Compilation, tree: usize, word: &str) -> bool {
    compilation
        .trees()
        .source(tree)
        .is_some_and(|source| source.text().contains(word))
}

fn attribute_of(node: &SyntaxNode) -> Option<Obsolete> {
    let attribute = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
        .flat_map(|list| list.children())
        .filter(|child| child.kind() == SyntaxKind::Attribute)
        .find(|attribute| {
            attribute
                .children()
                .find(|child| child.kind().is_type_node())
                .is_some_and(|name| {
                    matches!(
                        name.text().trim(),
                        "Obsolete"
                            | "ObsoleteAttribute"
                            | "System.Obsolete"
                            | "System.ObsoleteAttribute"
                            | "global::System.Obsolete"
                            | "global::System.ObsoleteAttribute"
                    )
                })
        })?;
    let arguments: Vec<SyntaxNode> = attribute
        .child_of_kind(SyntaxKind::AttributeArgumentList)
        .map(|list| {
            list.children()
                .filter(|child| {
                    child.kind() == SyntaxKind::AttributeArgument
                        && child.child_of_kind(SyntaxKind::NameEquals).is_none()
                })
                .filter_map(|argument| argument.children().last())
                .collect()
        })
        .unwrap_or_default();
    let message = arguments.first().and_then(|value| {
        (value.kind() == SyntaxKind::StringLiteralExpression)
            .then(|| value.first_token())
            .flatten()
            .and_then(|token| match token.value() {
                TokenValue::String(text) => Some(text.to_string()),
                _ => None,
            })
    });
    let error = arguments
        .get(1)
        .is_some_and(|value| value.kind() == SyntaxKind::TrueLiteralExpression);
    Some(Obsolete { message, error })
}

/// Whether a field or property is named where its name also names a type:
/// `CancellationToken.None` inside a type with a `CancellationToken`
/// property reads the type's static member (§12.8.7.2), whatever the
/// property says about itself.
fn names_a_type_too(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    span: TextSpan,
    symbol: SymbolId,
) -> bool {
    if !matches!(
        binder.compilation().symbols().get(symbol).kind,
        SymbolKind::Field | SymbolKind::Property
    ) {
        return false;
    }
    let Some(name) = declaration
        .find_token(span.start())
        .map(|token| token.parent().clone())
        .filter(|name| name.kind() == SyntaxKind::IdentifierName && name.span() == span)
    else {
        return false;
    };
    let context = binder.context_at(tree, &name);
    binder.resolve_namespace_or_type(&name, &context).is_some()
}

/// Whether `span` is inside a `nameof(...)`, which names without using.
/// The type a generic name at `span` spells, with its arguments: the
/// `UiInstance<H>` of `new List<UiInstance<H>>()`, which no expression's
/// type records.
fn written_type(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    span: TextSpan,
    symbol: SymbolId,
) -> Option<Type> {
    let token = declaration.find_token(span.start())?;
    let name = token.parent().clone();
    let name = match name.parent() {
        Some(parent) if parent.kind() == SyntaxKind::GenericName => parent.clone(),
        _ => name,
    };
    if name.kind() != SyntaxKind::GenericName {
        return None;
    }
    let context = binder.context_at(tree, &name);
    let mut sink = crate::binder::Diagnostics::new();
    Some(binder.resolve_type(&name, &context, &mut sink)).filter(|ty| ty.symbol() == Some(symbol))
}

/// Where Roslyn reports a use: the whole member access the name ends, from
/// its receiver — `Flags.Navigation`, `entity.GetComponent<T>` — and the
/// name alone where it is written alone.
fn whole_access(declaration: &SyntaxNode, span: TextSpan) -> TextSpan {
    let Some(token) = declaration.find_token(span.start()) else {
        return span;
    };
    let mut name = token.parent().clone();
    if name.kind() != SyntaxKind::IdentifierName && name.kind() != SyntaxKind::GenericName {
        return span;
    }
    if let Some(parent) = name.parent()
        && parent.kind() == SyntaxKind::GenericName
    {
        name = parent.clone();
    }
    match name.parent() {
        Some(access)
            if matches!(
                access.kind(),
                SyntaxKind::SimpleMemberAccessExpression
                    | SyntaxKind::PointerMemberAccessExpression
                    | SyntaxKind::QualifiedName
            ) && access
                .children()
                .last()
                .is_some_and(|last| last.span() == name.span()) =>
        {
            TextSpan::new(access.span().start(), name.span().end())
        }
        _ => span,
    }
}

fn in_nameof(declaration: &SyntaxNode, span: TextSpan) -> bool {
    let Some(token) = declaration.find_token(span.start()) else {
        return false;
    };
    token.parent().ancestors().any(|node| {
        node.kind() == SyntaxKind::InvocationExpression
            && node
                .children()
                .next()
                .is_some_and(|callee| callee.text().trim() == "nameof")
    })
}

impl Compilation {
    /// Whether anything at all is obsolete: a declaration of the source, or
    /// a type or member of a reference.
    pub(crate) fn has_obsolete(&self) -> bool {
        !self.loaded.obsolete.is_empty()
            || !self
                .obsolete
                .get_or_init(|| declared_obsolete(self))
                .is_empty()
    }

    /// What an `[Obsolete]` on `symbol` says, in the source or in an
    /// assembly: its message, if it gave one, and whether a use is an error.
    #[must_use]
    pub fn obsolete_of(&self, symbol: SymbolId) -> Option<(Option<String>, bool)> {
        obsolete(self, symbol).map(|found| (found.message, found.error))
    }
}

#[cfg(test)]
mod tests {
    use rustlyn_syntax::parse;
    use rustlyn_text::SourceText;

    use super::*;

    #[test]
    fn only_a_file_that_says_obsolete_is_parsed_to_find_it() {
        let compilation = Compilation::create(vec![
            parse(SourceText::new(
                "Old.cs",
                "public class Old { [System.Obsolete(\"gone\")] public void M() { } }",
            )),
            parse(SourceText::new(
                "Plain.cs",
                "public class Plain { public void N() { } }",
            )),
        ]);
        let read =
            Compilation::read_snapshot(&compilation.write_snapshot()).expect("it reads back");
        let (old, plain) = (read.corlib_trees, read.corlib_trees + 1);
        assert!(!read.trees().is_parsed(old) && !read.trees().is_parsed(plain));

        let class = read.type_by_metadata_name("Old").expect("Old");
        let method = read.symbols().lookup(class, "M")[0];
        let found = obsolete(&read, method).expect("M is obsolete");
        assert_eq!(found.message.as_deref(), Some("gone"));
        assert!(read.trees().is_parsed(old), "the file that says it is read");
        assert!(
            !read.trees().is_parsed(plain),
            "a file that never says Obsolete stays unparsed"
        );
    }
}
