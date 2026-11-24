//! Warnings a file's syntax and declarations give, outside what binding a
//! body finds: CS0105, a `using` written twice; CS0693, a type parameter
//! named as one of a type around it; CS1998, an `async` function that
//! never waits; CS8632, a reference type annotated `?` where annotations
//! are off.

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};

use crate::binder::{Binder, Diagnostics};
use crate::symbol::SymbolKind;

/// Adds this file's CS0105, CS0693 and CS1998.
pub(crate) fn check(binder: &Binder<'_>, tree: usize, found: &mut Diagnostics) {
    let compilation = binder.compilation();
    let Some(syntax) = compilation.trees().get(tree) else {
        return;
    };
    let root = syntax.root();
    duplicate_usings(&root, tree, found);
    let annotated = compilation.nullable_annotations_in(tree);
    let contexts = crate::nullable::NullableContexts::of(&root);
    for node in root.descendants() {
        match node.kind() {
            SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration => {
                duplicate_usings(&node, tree, found);
            }
            SyntaxKind::TypeParameter => outer_type_parameter(binder, tree, &node, found),
            SyntaxKind::NullableType => {
                annotation_outside_context(binder, tree, &node, &contexts, annotated, found);
            }
            SyntaxKind::MethodDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression => never_waits(&node, tree, found),
            _ => {}
        }
    }
}

/// CS0105: the same namespace or type imported twice in one scope, at the
/// second one's name. `using A;` and `using global::A;` are one.
fn duplicate_usings(scope: &SyntaxNode, tree: usize, found: &mut Diagnostics) {
    let mut seen: Vec<(bool, String)> = Vec::new();
    for directive in scope
        .children()
        .filter(|child| child.kind() == SyntaxKind::UsingDirective)
    {
        if directive.child_of_kind(SyntaxKind::NameEquals).is_some() {
            continue;
        }
        let Some(name) = directive
            .children()
            .filter(|child| child.kind().is_type_node())
            .last()
        else {
            continue;
        };
        let is_static = directive
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::StaticKeyword);
        let written: String = name.text().chars().filter(|c| !c.is_whitespace()).collect();
        let key = (
            is_static,
            written.trim_start_matches("global::").to_string(),
        );
        if seen.contains(&key) {
            found.push((
                tree,
                Diagnostic::new(ErrorCode::WrnDuplicateUsing, name.span(), &[&key.1]),
            ));
        } else {
            seen.push(key);
        }
    }
}

/// CS0693: `T GetComponent<T>()` inside `UiInstance<T>` — the method's `T`
/// hides the type's.
fn outer_type_parameter(
    binder: &Binder<'_>,
    tree: usize,
    node: &SyntaxNode,
    found: &mut Diagnostics,
) {
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    let Some(parameter) = compilation.declared_symbol(tree, node.span()) else {
        return;
    };
    let name = &symbols.get(parameter).name;
    let Some(owner) = symbols.get(parameter).container else {
        return;
    };
    let mut outer = symbols.get(owner).container;
    while let Some(ty) = outer {
        if symbols.get(ty).kind != SymbolKind::NamedType {
            break;
        }
        let shadowed = symbols.get(ty).as_named_type().is_some_and(|detail| {
            detail
                .type_parameters
                .iter()
                .any(|other| &symbols.get(*other).name == name)
        });
        if shadowed {
            let Some(token) = node
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            else {
                return;
            };
            let shown = binder.self_type(ty).display(symbols);
            found.push((
                tree,
                Diagnostic::new(
                    ErrorCode::WrnTypeParameterSameAsOuterTypeParameter,
                    token.span(),
                    &[name, &shown],
                ),
            ));
            return;
        }
        outer = symbols.get(ty).container;
    }
}

/// CS1998: an `async` method, local function, lambda or anonymous method
/// whose body has no `await` of its own — one in a function inside it is
/// that function's. Reported at the method's name, a lambda's `=>`, an
/// anonymous method's `delegate`. An `async` iterator is left alone.
fn never_waits(node: &SyntaxNode, tree: usize, found: &mut Diagnostics) {
    let is_async = node.child_tokens().any(|token| token.text() == "async");
    if !is_async {
        return;
    }
    let Some(body) = node
        .children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
            ) || (child.kind().is_expression() && is_lambda(node.kind()))
        })
        .last()
    else {
        return;
    };
    let mut waits = false;
    let mut yields = false;
    visit_own(&body, &mut |inner: &SyntaxNode| match inner.kind() {
        SyntaxKind::AwaitExpression => waits = true,
        SyntaxKind::YieldReturnStatement | SyntaxKind::YieldBreakStatement => yields = true,
        _ => {
            // `await foreach` and `await using` wait as well.
            if inner.child_tokens().any(|token| token.text() == "await") {
                waits = true;
            }
        }
    });
    if waits || yields {
        return;
    }
    let at: Option<SyntaxToken> = match node.kind() {
        SyntaxKind::MethodDeclaration | SyntaxKind::LocalFunctionStatement => node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken),
        SyntaxKind::AnonymousMethodExpression => node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::DelegateKeyword),
        _ => node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::EqualsGreaterThanToken),
    };
    if let Some(at) = at {
        found.push((
            tree,
            Diagnostic::new(ErrorCode::WrnAsyncLacksAwaits, at.span(), &[]),
        ));
    }
}

fn is_lambda(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
    )
}

/// Every node under `node` that is not inside a function of its own.
fn visit_own(node: &SyntaxNode, visit: &mut impl FnMut(&SyntaxNode)) {
    visit(node);
    for child in node.children() {
        if is_lambda(child.kind()) || child.kind() == SyntaxKind::LocalFunctionStatement {
            continue;
        }
        visit_own(&child, visit);
    }
}

/// CS8632: `string?` where annotations are off — Unity's default, and
/// whatever `#nullable disable` covers. A value type's `?` is `Nullable<T>`
/// and says nothing of annotations; a type parameter not known to be one
/// is annotated as a reference type would be. Reported at the `?`.
fn annotation_outside_context(
    binder: &Binder<'_>,
    tree: usize,
    node: &SyntaxNode,
    contexts: &crate::nullable::NullableContexts,
    annotated: bool,
    found: &mut Diagnostics,
) {
    let Some(question) = node
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::QuestionToken)
    else {
        return;
    };
    if contexts.annotations_at(question.span().start(), annotated) {
        return;
    }
    let Some(element) = node.children().find(|child| child.kind().is_type_node()) else {
        return;
    };
    let context = binder.context_at(tree, &element);
    let mut sink = Diagnostics::new();
    let ty = binder.resolve_type(&element, &context, &mut sink);
    let symbols = binder.compilation().symbols();
    let reference = match &ty {
        crate::types::Type::TypeParameter(parameter) => symbols
            .get(*parameter)
            .as_type_parameter()
            .is_some_and(|detail| !detail.value_type),
        crate::types::Type::Error => false,
        other => binder.held_by_reference(other) || other.is_reference_type(symbols),
    };
    if reference {
        found.push((
            tree,
            Diagnostic::new(
                ErrorCode::WrnMissingNonNullTypesContextForAnnotation,
                question.span(),
                &[],
            ),
        ));
    }
}
