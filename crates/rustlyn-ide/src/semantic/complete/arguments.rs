//! Named arguments: inside a call's parentheses, `name:` for each parameter
//! of the overloads it could be calling that no argument has named yet —
//! Roslyn's `NamedParameterCompletionProvider`. The same overloads say what
//! type an argument is expected to have, which is what enum completion
//! needs inside a call.

use std::collections::HashSet;

use rustlyn_semantics::{MethodKind, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};

use super::{Completion, CompletionKind, View};

/// `name:` for the parameters not named yet, after `(` or `,`.
pub(super) fn complete(view: &mut View<'_>, target: &SyntaxToken, items: &mut Vec<Completion>) {
    let list = target.parent().clone();
    if list.kind() != K::ArgumentList {
        return;
    }
    let candidates = candidates(view, &list);
    if candidates.is_empty() {
        return;
    }
    let named: HashSet<String> = list
        .children()
        .filter_map(|argument| argument.child_of_kind(K::NameColon))
        .filter_map(|colon| {
            colon
                .descendant_tokens()
                .find(|token| token.kind() == K::IdentifierToken)
                .map(|token| token.value_text().to_string())
        })
        .collect();
    let symbols = view.compilation().symbols();
    let mut offered = HashSet::new();
    for method in candidates {
        let Some(detail) = symbols.get(method).as_method() else {
            continue;
        };
        for &parameter in &detail.parameters {
            let name = symbols.get(parameter).name.clone();
            if name.is_empty() || named.contains(&name) || !offered.insert(name.clone()) {
                continue;
            }
            let ty = view.model.type_of_symbol(parameter).display(symbols);
            items.push(Completion {
                label: format!("{name}:"),
                kind: CompletionKind::Parameter,
                detail: format!("{ty} {name}"),
                rank: 1,
                filter_text: Some(name),
                symbol: Some(parameter),
                ..Completion::default()
            });
        }
    }
}

/// The type the argument at `position` of `list` — or the one named `name`
/// — is expected to have, when every overload agrees.
pub(super) fn expected_parameter_type(
    view: &mut View<'_>,
    list: &SyntaxNode,
    position: u32,
    name: Option<&str>,
) -> Option<Type> {
    let candidates = candidates(view, list);
    let index = list
        .child_tokens()
        .filter(|comma| comma.kind() == K::CommaToken && comma.span().end() <= position)
        .count();
    let symbols = view.compilation().symbols();
    let mut found: Option<Type> = None;
    for method in candidates {
        let detail = symbols.get(method).as_method()?;
        let parameter = match name {
            Some(name) => detail
                .parameters
                .iter()
                .copied()
                .find(|&p| symbols.get(p).name == name),
            None => detail.parameters.get(index).copied(),
        };
        let Some(parameter) = parameter else {
            continue;
        };
        let ty = view.model.type_of_symbol(parameter);
        match &found {
            None => found = Some(ty),
            Some(previous) if *previous == ty => {}
            Some(_) => return None,
        }
    }
    found
}

/// The methods or constructors a call's argument list could be for.
fn candidates(view: &mut View<'_>, list: &SyntaxNode) -> Vec<SymbolId> {
    let Some(call) = list.parent().cloned() else {
        return Vec::new();
    };
    match call.kind() {
        K::InvocationExpression => {
            let Some(callee) = call.children().next() else {
                return Vec::new();
            };
            let name_of = |node: &SyntaxNode| {
                node.descendant_tokens()
                    .filter(|token| token.kind() == K::IdentifierToken)
                    .last()
                    .map(|token| token.value_text().to_string())
            };
            match callee.kind() {
                K::SimpleMemberAccessExpression => {
                    let (Some(receiver), Some(member)) =
                        (callee.children().next(), callee.children().last())
                    else {
                        return Vec::new();
                    };
                    let Some(name) = name_of(&member) else {
                        return Vec::new();
                    };
                    let types: Vec<SymbolId> = match view.named(&receiver) {
                        Some(symbol)
                            if view.compilation().symbols().get(symbol).kind
                                == SymbolKind::NamedType =>
                        {
                            vec![symbol]
                        }
                        _ => {
                            let ty = view.type_of(&receiver);
                            view.types_of(&ty).into_iter().collect()
                        }
                    };
                    methods_named(view, &types, &name)
                }
                K::IdentifierName | K::GenericName => {
                    let Some(name) = name_of(&callee) else {
                        return Vec::new();
                    };
                    let enclosing: Vec<SymbolId> =
                        view.enclosing_types(&callee).into_iter().collect();
                    let mut all = Vec::new();
                    for ty in enclosing {
                        let mut types: Vec<SymbolId> =
                            view.types_of(&Type::named(ty)).into_iter().collect();
                        types.sort_by_key(|id| id.index());
                        all.extend(methods_named(view, &types, &name));
                    }
                    all
                }
                _ => Vec::new(),
            }
        }
        K::ObjectCreationExpression => {
            let Some(ty) = call.children().find(|child| child.kind().is_type_node()) else {
                return Vec::new();
            };
            match view.model.type_of_syntax(&ty) {
                Type::Named { symbol, .. } => constructors(view, symbol),
                _ => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}

/// The methods called `name` declared by any of `types`, one per
/// signature.
fn methods_named(view: &View<'_>, types: &[SymbolId], name: &str) -> Vec<SymbolId> {
    let symbols = view.compilation().symbols();
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    for &ty in types {
        for &member in symbols.lookup(ty, name) {
            if symbols.get(member).kind != SymbolKind::Method {
                continue;
            }
            if seen.insert(super::super::describe_symbol(view.compilation(), member)) {
                found.push(member);
            }
        }
    }
    found
}

fn constructors(view: &View<'_>, ty: SymbolId) -> Vec<SymbolId> {
    let symbols = view.compilation().symbols();
    symbols
        .get(ty)
        .members
        .iter()
        .copied()
        .filter(|&member| {
            symbols
                .get(member)
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor)
        })
        .collect()
}
