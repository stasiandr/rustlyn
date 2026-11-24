//! What is in scope, narrowed to what the place allows, and the items a
//! place adds because it knows the type it wants.
//!
//! Roslyn's symbol provider asks the binder what names are visible and then
//! filters by position: after `new` only types, in a static method no
//! instance members, after `using` only namespaces, in `[` only attribute
//! classes — spelled without their `Attribute`. Where the position expects a
//! type, two more providers chime in: after `new` the expected type itself is
//! preselected (`List<int> x = new |` offers `List<int>`), and where an enum
//! is expected its members are offered whole (`Color.Red`) and preselected.

use rustlyn_semantics::{Modifiers, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind as K, SyntaxToken};

use super::context::{Code, Site, previous_token};
use super::{Completion, CompletionKind, View, arguments, imports};

/// Whether an item names a type or a namespace: what a type-only place
/// keeps.
pub(super) const fn is_type_like(kind: CompletionKind) -> bool {
    matches!(
        kind,
        CompletionKind::Class
            | CompletionKind::Struct
            | CompletionKind::Interface
            | CompletionKind::Enum
            | CompletionKind::Delegate
            | CompletionKind::Namespace
            | CompletionKind::TypeParameter
    )
}

/// Whether an item is a member that needs an instance: what a static
/// member cannot use without one.
pub(super) fn is_instance_member(view: &View<'_>, item: &Completion) -> bool {
    let Some(symbol) = item.symbol else {
        return false;
    };
    let symbols = view.compilation().symbols();
    let found = symbols.get(symbol);
    if !matches!(
        found.kind,
        SymbolKind::Field | SymbolKind::Property | SymbolKind::Method | SymbolKind::Event
    ) {
        return false;
    }
    if found.modifiers.contains(Modifiers::STATIC) || found.modifiers.contains(Modifiers::CONST) {
        return false;
    }
    found.container.is_some_and(|container| {
        let container = symbols.get(container);
        container.kind == SymbolKind::NamedType && container.type_kind() != Some(TypeKind::Enum)
    })
}

/// After `using`: the namespaces, and the types too after `using static`
/// or `using A =`.
pub(super) fn using_items(view: &View<'_>, with_types: bool, items: &mut Vec<Completion>) {
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    for &member in &symbols.get(compilation.global_namespace()).members {
        let kind = symbols.get(member).kind;
        if kind == SymbolKind::Namespace || (with_types && kind == SymbolKind::NamedType) {
            if kind == SymbolKind::NamedType && !view.offerable(member) {
                continue;
            }
            view.push_symbol(member, 20, items);
        }
    }
}

/// In `[`: the attribute classes in scope, by the name an attribute is
/// written with, and the namespaces that hold more.
pub(super) fn attribute_items(view: &mut View<'_>, site: &Site, items: &mut Vec<Completion>) {
    let mut found = Vec::new();
    view.scope_completions(site.start, &mut found);
    let text = view.root.full_text();
    imports::complete_types(view, site, &text, true, &mut found);
    for mut item in found {
        match item.kind {
            CompletionKind::Namespace => items.push(item),
            CompletionKind::Class => {
                let Some(symbol) = item.symbol else {
                    continue;
                };
                if !is_attribute(view, symbol) {
                    continue;
                }
                if let Some(short) = item.label.strip_suffix("Attribute")
                    && !short.is_empty()
                {
                    item.filter_text = Some(short.to_string());
                    item.label = short.to_string();
                }
                items.push(item);
            }
            _ => {}
        }
    }
}

/// Whether a class derives from `System.Attribute`.
fn is_attribute(view: &View<'_>, symbol: rustlyn_semantics::SymbolId) -> bool {
    let symbols = view.compilation().symbols();
    let mut current = symbol;
    for _ in 0..32 {
        if symbols.qualified_name(current) == "System.Attribute" {
            return true;
        }
        let base = view
            .model
            .base_types_of(current)
            .into_iter()
            .find_map(|base| match base {
                Type::Named { symbol, .. }
                    if symbols.get(symbol).type_kind() != Some(TypeKind::Interface) =>
                {
                    Some(symbol)
                }
                _ => None,
            });
        match base {
            Some(base) if base != current => current = base,
            _ => return false,
        }
    }
    false
}

/// The items a place adds because it expects a type: the members of the
/// enum it wants, or the type after `new`.
pub(super) fn target_typed(
    view: &mut View<'_>,
    site: &Site,
    code: &Code,
    items: &mut Vec<Completion>,
) {
    let Some(target) = &site.target else {
        return;
    };
    let Some(Type::Named {
        symbol,
        type_arguments,
    }) = expected_type(view, target)
    else {
        return;
    };
    let symbols = view.compilation().symbols();
    let found = symbols.get(symbol);
    let display = Type::Named {
        symbol,
        type_arguments: type_arguments.clone(),
    }
    .display(symbols);

    if code.after_new {
        // Only something that can be created.
        let creatable = matches!(
            found.type_kind(),
            Some(TypeKind::Class | TypeKind::Struct | TypeKind::Record | TypeKind::RecordStruct)
        ) && !found.modifiers.contains(Modifiers::ABSTRACT)
            && !found.modifiers.contains(Modifiers::STATIC);
        if !creatable {
            return;
        }
        if type_arguments.is_empty()
            && let Some(item) = items.iter_mut().find(|item| item.symbol == Some(symbol))
        {
            item.preselect = true;
            return;
        }
        let mut item = Completion {
            label: display.clone(),
            kind: super::super::completion_kind(view.compilation(), symbol),
            detail: super::super::describe_symbol(view.compilation(), symbol),
            rank: 3,
            preselect: true,
            symbol: Some(symbol),
            ..Completion::default()
        };
        if !type_arguments.is_empty() {
            item.insert_text = Some(display);
            item.filter_text = Some(found.name.clone());
        }
        items.push(item);
        return;
    }

    if found.type_kind() == Some(TypeKind::Enum) {
        for &member in &found.members {
            let field = symbols.get(member);
            if field.kind != SymbolKind::Field || field.name.is_empty() {
                continue;
            }
            items.push(Completion {
                label: format!("{display}.{}", field.name),
                kind: CompletionKind::EnumMember,
                detail: super::super::describe_symbol(view.compilation(), member),
                rank: 2,
                preselect: true,
                symbol: Some(member),
                ..Completion::default()
            });
        }
    }
}

/// The type an expression written right after `token` is expected to have:
/// the declared type after `=`, the other side of `==`, the governing type
/// after `case`, the return type after `return`, the parameter's type in an
/// argument list.
pub(super) fn expected_type(view: &mut View<'_>, token: &SyntaxToken) -> Option<Type> {
    let parent = token.parent().clone();
    let declared = |view: &View<'_>, owner: &rustlyn_syntax::SyntaxNode| -> Option<Type> {
        let ty = owner.children().find(|child| child.kind().is_type_node())?;
        if ty.text().trim() == "var" {
            return None;
        }
        Some(view.model.type_of_syntax(&ty))
    };
    let ty = match token.kind() {
        K::EqualsToken => match parent.kind() {
            K::EqualsValueClause => {
                let owner = parent.parent()?.clone();
                match owner.kind() {
                    K::VariableDeclarator => declared(view, owner.parent()?),
                    K::Parameter | K::PropertyDeclaration => declared(view, &owner),
                    _ => None,
                }
            }
            K::SimpleAssignmentExpression => {
                let left = parent.children().next()?;
                Some(view.type_of(&left))
            }
            _ => None,
        },
        K::EqualsEqualsToken | K::ExclamationEqualsToken => {
            let left = parent.children().next()?;
            Some(view.type_of(&left))
        }
        K::CaseKeyword => {
            let switch = parent
                .ancestors()
                .find(|node| node.kind() == K::SwitchStatement)?;
            let governing = switch.children().next()?;
            Some(view.type_of(&governing))
        }
        K::ReturnKeyword => {
            let member = parent.ancestors().find(|node| {
                matches!(
                    node.kind(),
                    K::MethodDeclaration
                        | K::LocalFunctionStatement
                        | K::PropertyDeclaration
                        | K::ParenthesizedLambdaExpression
                        | K::SimpleLambdaExpression
                        | K::AnonymousMethodExpression
                        | K::GetAccessorDeclaration
                )
            })?;
            match member.kind() {
                K::MethodDeclaration | K::LocalFunctionStatement => declared(view, &member),
                K::GetAccessorDeclaration => {
                    let property = member.ancestors().find(|node| {
                        matches!(node.kind(), K::PropertyDeclaration | K::IndexerDeclaration)
                    })?;
                    declared(view, &property)
                }
                _ => None,
            }
        }
        K::OpenParenToken | K::CommaToken if parent.kind() == K::ArgumentList => {
            arguments::expected_parameter_type(view, &parent, token.span().end(), None)
        }
        K::ColonToken if parent.kind() == K::NameColon => {
            let name = parent
                .descendant_tokens()
                .find(|t| t.kind() == K::IdentifierToken)?
                .value_text()
                .to_string();
            let list = parent
                .ancestors()
                .find(|node| node.kind() == K::ArgumentList)?;
            arguments::expected_parameter_type(view, &list, token.span().end(), Some(&name))
        }
        K::NewKeyword => {
            let before = previous_token(&view.root, token)?;
            expected_type(view, &before)
        }
        _ => None,
    }?;
    match ty {
        Type::Error => None,
        // `Color?` expects a `Color`.
        Type::Named {
            symbol,
            type_arguments,
        } if view.compilation().symbols().qualified_name(symbol) == "System.Nullable`1" => {
            type_arguments.into_iter().next()
        }
        other => Some(other),
    }
}
