//! Object initializers: in `new C { | }`, the fields and properties of `C`
//! that can be set and have not been — Roslyn's
//! `ObjectInitializerCompletionProvider`. Nothing else is offered there:
//! the left of an assignment in an initializer can only be a member.

use std::collections::HashSet;

use rustlyn_semantics::{Accessibility, Modifiers, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind as K, SyntaxNode};

use super::context::{Site, previous_token};
use super::{Completion, View, symbols};

pub(super) fn complete(
    view: &mut View<'_>,
    site: &Site,
    initializer: &SyntaxNode,
    items: &mut Vec<Completion>,
) {
    let Some(creation) = initializer.parent().cloned() else {
        return;
    };
    let ty = match creation.kind() {
        K::ObjectCreationExpression => creation
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| view.model.type_of_syntax(&ty)),
        // `new() { … }` is whatever the place expects.
        _ => creation
            .first_token()
            .and_then(|new| previous_token(&view.root, &new))
            .and_then(|before| symbols::expected_type(view, &before)),
    };
    let Some(Type::Named { symbol, .. }) = ty else {
        return;
    };

    // Already assigned, except the one being typed.
    let assigned: HashSet<String> = initializer
        .children()
        .filter(|element| element.kind() == K::SimpleAssignmentExpression)
        .filter(|element| {
            !(element.span().start() <= site.start && site.start <= element.span().end())
        })
        .filter_map(|element| element.children().next())
        .map(|left| left.text().trim().to_string())
        .collect();

    let enclosing = view.enclosing_types(initializer);
    let symbols = view.compilation().symbols();
    let mut queue = vec![symbol];
    let mut visited = HashSet::new();
    let mut offered = HashSet::new();
    while let Some(current) = queue.pop() {
        if !visited.insert(current) {
            continue;
        }
        for &member in &symbols.get(current).members {
            if settable(view, member, &enclosing, current)
                && !assigned.contains(&symbols.get(member).name)
                && offered.insert(symbols.get(member).name.clone())
            {
                view.push_symbol(member, 5, items);
            }
        }
        for base in view.model.base_types_of(current) {
            if let Type::Named { symbol, .. } = base {
                queue.push(symbol);
            }
        }
    }
}

/// Whether an initializer can assign `member`: an instance field that is
/// not read-only, or a property with a setter or `init`, that the code
/// creating the object can see.
fn settable(
    view: &View<'_>,
    member: SymbolId,
    enclosing: &HashSet<SymbolId>,
    owner: SymbolId,
) -> bool {
    let symbols = view.compilation().symbols();
    let found = symbols.get(member);
    if !view.offerable(member)
        || found.modifiers.contains(Modifiers::STATIC)
        || found.modifiers.contains(Modifiers::CONST)
    {
        return false;
    }
    let visible = match found.accessibility {
        Accessibility::Private => enclosing.contains(&owner),
        Accessibility::Protected | Accessibility::ProtectedAndInternal => !enclosing.is_empty(),
        _ => true,
    };
    if !visible {
        return false;
    }
    match found.kind {
        SymbolKind::Field => !found.modifiers.contains(Modifiers::READONLY),
        SymbolKind::Property => found.as_property().is_some_and(|property| {
            !property.is_indexer && (property.has_set || property.has_init)
        }),
        _ => false,
    }
}
