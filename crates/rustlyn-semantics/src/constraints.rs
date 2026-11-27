//! Whether the type arguments a program writes meet the constraints of the
//! type parameters they are for: CS0311 and CS0315 where one does not convert
//! to a constraint type, CS0452 where a `class` constraint is given a value
//! type and CS0453 where a `struct` constraint is given a reference type or
//! a nullable one.
//!
//! The arguments of a constructed type are read off its syntax, one
//! diagnostic at each argument that fails; those of a generic method, off the
//! call the body bound, at the method's name. Only what is certain is
//! reported. An argument that is, or holds, a type parameter, a constraint
//! that still names one, a type that did not resolve and a nullable value
//! type under an interface constraint are all taken as met, and so is a type
//! argument list this does not know how to line up with the parameters it is
//! for.

use std::collections::HashMap;

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use crate::binder::{Binder, Diagnostics};
use crate::bound::{BoundBody, BoundExpressionKind};
use crate::symbol::{SymbolId, SymbolKind};
use crate::types::Type;

/// What the types a file's declarations write, outside any body, get wrong
/// against the constraints of the types they construct.
pub(crate) fn check_declarations(binder: &Binder<'_>, tree: usize, found: &mut Diagnostics) {
    let Some(syntax) = binder.compilation().trees().get(tree) else {
        return;
    };
    if declares_the_core_library(binder) {
        return;
    }
    for node in syntax.root().descendants() {
        if node.kind() == SyntaxKind::GenericName && !in_a_body_or_attribute(&node, None) {
            constructed(binder, tree, &node, true, found);
        }
    }
}

/// What the body of one member gets wrong: the types it writes, and the
/// generic methods it calls.
pub(crate) fn check_body(
    binder: &Binder<'_>,
    tree: usize,
    declaration: &SyntaxNode,
    body: &mut BoundBody,
) {
    if declares_the_core_library(binder) {
        return;
    }
    let mut found = Diagnostics::new();
    for node in declaration.descendants() {
        if node.kind() == SyntaxKind::GenericName
            && in_a_body_or_attribute(&node, Some(declaration))
        {
            constructed(binder, tree, &node, false, &mut found);
        }
    }
    let mut calls = Vec::new();
    body.each_expression(&mut |expression| {
        if let BoundExpressionKind::Call {
            method,
            type_arguments,
            ..
        } = &expression.kind
            && !type_arguments.is_empty()
        {
            calls.push((expression.span, *method, type_arguments.clone()));
        }
    });
    for (span, method, arguments) in calls {
        generic_call(binder, tree, span, method, &arguments, &mut found);
    }
    found.sort_by_key(|(_, diagnostic)| (diagnostic.span().start(), diagnostic.span().end()));
    found.dedup_by(|(_, second), (_, first)| {
        first.span() == second.span()
            && first.code() == second.code()
            && first.message() == second.message()
    });
    body.diagnostics.extend(found);
}

/// Whether a node is written in a body, which is bound with the member and
/// reports there, or in an attribute, which this leaves alone. `within` is
/// the member whose body is looked for, and the walk stops at it; none looks
/// for any.
fn in_a_body_or_attribute(node: &SyntaxNode, within: Option<&SyntaxNode>) -> bool {
    // The members of a type are bound each with its own body, even when the
    // file's top-level statements are what is asked about.
    if within.is_some_and(|member| member.kind() == SyntaxKind::CompilationUnit)
        && node.ancestors().any(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::StructDeclaration
                    | SyntaxKind::InterfaceDeclaration
                    | SyntaxKind::RecordDeclaration
                    | SyntaxKind::RecordStructDeclaration
            )
        })
    {
        return false;
    }
    for ancestor in node.ancestors() {
        if within.is_some_and(|member| {
            member.kind() == ancestor.kind() && member.span() == ancestor.span()
        }) {
            return false;
        }
        match ancestor.kind() {
            SyntaxKind::Attribute => return within.is_none(),
            SyntaxKind::Block
            | SyntaxKind::ArrowExpressionClause
            | SyntaxKind::EqualsValueClause => return true,
            _ => {}
        }
    }
    false
}

/// The type a generic name writes, where it writes one, checked against its
/// definition's constraints.
fn constructed(
    binder: &Binder<'_>,
    tree: usize,
    name: &SyntaxNode,
    declaration_phase: bool,
    found: &mut Diagnostics,
) {
    // `A.B<int>` is resolved from the whole dotted name.
    let mut top = name.clone();
    while let Some(parent) = top.parent()
        && matches!(
            parent.kind(),
            SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName
        )
        && parent
            .children()
            .last()
            .is_some_and(|last| last.span() == top.span())
    {
        top = parent.clone();
    }
    // Only where the name is a type for certain: `Foo<int>()` and a bare
    // `Foo<int>` may be a method as well.
    let Some(parent) = top.parent() else {
        return;
    };
    let in_type_position = matches!(
        parent.kind(),
        SyntaxKind::VariableDeclaration
            | SyntaxKind::ObjectCreationExpression
            | SyntaxKind::TypeOfExpression
            | SyntaxKind::DefaultExpression
            | SyntaxKind::SizeOfExpression
            | SyntaxKind::CastExpression
            | SyntaxKind::TypeArgumentList
            | SyntaxKind::Parameter
            | SyntaxKind::SimpleBaseType
            | SyntaxKind::PrimaryConstructorBaseType
            | SyntaxKind::TypeConstraint
            | SyntaxKind::ArrayType
            | SyntaxKind::NullableType
            | SyntaxKind::PointerType
            | SyntaxKind::RefType
            | SyntaxKind::DeclarationPattern
            | SyntaxKind::TypePattern
            | SyntaxKind::CatchDeclaration
            | SyntaxKind::TupleElement
            | SyntaxKind::AsExpression
            | SyntaxKind::IsExpression
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::DelegateDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::ForEachStatement
    ) || (parent.kind() == SyntaxKind::SimpleMemberAccessExpression
        && parent
            .children()
            .next()
            .is_some_and(|left| left.span() == top.span()));
    if !in_type_position {
        return;
    }
    let written: Vec<SyntaxNode> = name
        .child_of_kind(SyntaxKind::TypeArgumentList)
        .map(|list| list.children().collect())
        .unwrap_or_default();
    if written.is_empty()
        || written
            .iter()
            .any(|argument| !argument.kind().is_type_node())
    {
        return;
    }
    let mut sink = Diagnostics::new();
    let context = binder.context_at(tree, &top);
    let Type::Named {
        symbol,
        type_arguments,
    } = binder.resolve_type(&top, &context, &mut sink)
    else {
        return;
    };
    let symbols = binder.compilation().symbols();
    let Some(detail) = symbols.get(symbol).as_named_type() else {
        return;
    };
    // A nested type counts the parameters of what it is nested in as its
    // own, which the list does not: lining those up is not attempted.
    if detail.type_parameters.len() != written.len() || type_arguments.len() != written.len() {
        return;
    }
    let parameters = detail.type_parameters.clone();
    let owner = binder.self_type(symbol).display(symbols);
    let substitution: HashMap<SymbolId, Type> = parameters
        .iter()
        .copied()
        .zip(type_arguments.iter().cloned())
        .collect();
    let anchors = if declaration_phase {
        anchors(&top)
    } else {
        Vec::new()
    };
    for (at, parameter) in parameters.iter().enumerate() {
        if let Some((code, arguments)) = violation(
            binder,
            *parameter,
            &type_arguments[at],
            &substitution,
            &owner,
            true,
        ) {
            let arguments: Vec<&str> = arguments.iter().map(String::as_str).collect();
            // A type a member's signature writes is reported at the member's
            // name, as Roslyn does; one written anywhere else, at the
            // argument.
            let places = if anchors.is_empty() {
                vec![written[at].span()]
            } else {
                anchors.clone()
            };
            for place in places {
                found.push((tree, Diagnostic::new(code, place, &arguments)));
            }
        }
    }
}

/// Where Roslyn reports what a type written in a declaration gets wrong:
/// at the name of the field, property, event, method or parameter it is
/// the type of, of the type it is a base of, and of the type parameter whose
/// constraint it is. None for a type written anywhere else, which is
/// reported at the type argument.
fn anchors(written: &SyntaxNode) -> Vec<rustlyn_text::TextSpan> {
    // The whole type the argument is part of: `List<C<int>>[]` is one.
    let mut outer = written.clone();
    while let Some(parent) = outer.parent()
        && matches!(
            parent.kind(),
            SyntaxKind::TypeArgumentList
                | SyntaxKind::GenericName
                | SyntaxKind::QualifiedName
                | SyntaxKind::AliasQualifiedName
                | SyntaxKind::ArrayType
                | SyntaxKind::NullableType
                | SyntaxKind::PointerType
                | SyntaxKind::RefType
                | SyntaxKind::TupleElement
                | SyntaxKind::TupleType
        )
    {
        outer = parent.clone();
    }
    let name_of = |node: &SyntaxNode| {
        node.child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| token.span())
    };
    let Some(owner) = outer.parent().cloned() else {
        return Vec::new();
    };
    match owner.kind() {
        SyntaxKind::Parameter => {
            let in_delegate = owner
                .ancestors()
                .any(|ancestor| ancestor.kind() == SyntaxKind::DelegateDeclaration);
            if in_delegate {
                Vec::new()
            } else {
                name_of(&owner).into_iter().collect()
            }
        }
        SyntaxKind::VariableDeclaration => {
            let field = owner.parent().is_some_and(|parent| {
                matches!(
                    parent.kind(),
                    SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                )
            });
            if field {
                owner
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                    .filter_map(|declarator| name_of(&declarator))
                    .collect()
            } else {
                Vec::new()
            }
        }
        SyntaxKind::MethodDeclaration
        | SyntaxKind::PropertyDeclaration
        | SyntaxKind::EventDeclaration => {
            // The type before the name, not an explicit interface's.
            name_of(&owner).into_iter().collect()
        }
        SyntaxKind::SimpleBaseType | SyntaxKind::PrimaryConstructorBaseType => owner
            .parent()
            .and_then(|list| list.parent())
            .and_then(name_of)
            .into_iter()
            .collect(),
        SyntaxKind::TypeConstraint => {
            // The clause names the parameter it constrains; the report is on
            // that parameter where the declaration lists it.
            let Some(clause) = owner.parent() else {
                return Vec::new();
            };
            let Some(constrained) = clause
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
            else {
                return Vec::new();
            };
            clause
                .parent()
                .and_then(|declaration| declaration.child_of_kind(SyntaxKind::TypeParameterList))
                .into_iter()
                .flat_map(|list| list.children())
                .filter(|parameter| parameter.kind() == SyntaxKind::TypeParameter)
                .find(|parameter| {
                    parameter
                        .child_tokens()
                        .any(|token| token.value_text() == constrained)
                })
                .and_then(|parameter| name_of(&parameter))
                .into_iter()
                .collect()
        }
        _ => Vec::new(),
    }
}

/// The generic method a call bound, checked against the constraints of its
/// type parameters, at the name the call wrote.
fn generic_call(
    binder: &Binder<'_>,
    tree: usize,
    span: rustlyn_text::TextSpan,
    method: SymbolId,
    arguments: &[Type],
    found: &mut Diagnostics,
) {
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    let Some(detail) = symbols.get(method).as_method() else {
        return;
    };
    if symbols.get(method).kind != SymbolKind::Method
        || detail.type_parameters.len() != arguments.len()
    {
        return;
    }
    let Some(call) = compilation
        .trees()
        .get(tree)
        .and_then(|syntax| syntax.root().find_node(span))
        .filter(|node| node.kind() == SyntaxKind::InvocationExpression)
    else {
        return;
    };
    let Some(callee) = call.children().next() else {
        return;
    };
    let name = match callee.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => callee,
        SyntaxKind::SimpleMemberAccessExpression => match callee.children().last() {
            Some(name) => name,
            None => return,
        },
        _ => return,
    };
    let explicit = name.kind() == SyntaxKind::GenericName;
    let owner = crate::checks::member_display(compilation, method, &HashMap::new(), None);
    let parameters = detail.type_parameters.clone();
    let substitution: HashMap<SymbolId, Type> = parameters
        .iter()
        .copied()
        .zip(arguments.iter().cloned())
        .collect();
    for (at, parameter) in parameters.iter().enumerate() {
        if let Some((code, arguments)) = violation(
            binder,
            *parameter,
            &arguments[at],
            &substitution,
            &owner,
            explicit,
        ) {
            let arguments: Vec<&str> = arguments.iter().map(String::as_str).collect();
            found.push((tree, Diagnostic::new(code, name.span(), &arguments)));
        }
    }
}

/// Whether a type is, or holds, something a constraint cannot be settled
/// for: a type parameter, a type that is not one, or one nothing here
/// converts reliably.
fn undecidable(ty: &Type) -> bool {
    match ty {
        Type::TypeParameter(_)
        | Type::Error
        | Type::Null
        | Type::Void
        | Type::Dynamic
        | Type::Pointer(_)
        | Type::ByRef(_)
        | Type::Tuple(_)
        | Type::FunctionPointer(_) => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(undecidable),
        Type::Array { element, .. } => undecidable(element),
    }
}

/// Whether the program is the core library itself: its sources declare
/// `System.Object`, and every built-in type of theirs has a twin in the
/// library they are bound against, which a constraint is never met by.
fn declares_the_core_library(binder: &Binder<'_>) -> bool {
    let compilation = binder.compilation();
    compilation
        .type_by_metadata_name("System.Object")
        .is_some_and(|object| {
            !compilation.is_from_metadata(object) && !compilation.is_from_corlib(object)
        })
}

/// Whether every named type in a type is the only one of its name. Where a
/// program declares a type the framework has — the core library's own
/// sources are bound against the core library — two of them are in play and
/// a type of one never converts to a type of the other, whatever the
/// program means. A tuple is one of them: a library's `ITest<(int, int)>` is
/// read as a `ValueTuple` where the program writes a tuple, and neither is
/// taken to be the other here.
fn unambiguous(binder: &Binder<'_>, ty: &Type) -> bool {
    let compilation = binder.compilation();
    match ty {
        Type::Named {
            symbol,
            type_arguments,
        } => {
            let name = compilation.symbols().metadata_qualified_name(*symbol);
            !name.starts_with("System.ValueTuple`")
                && compilation.type_by_metadata_name(&name) == Some(*symbol)
                && type_arguments
                    .iter()
                    .all(|argument| unambiguous(binder, argument))
        }
        Type::Array { element, .. } => unambiguous(binder, element),
        _ => true,
    }
}

/// The error a type argument earns for the type parameter it is given to,
/// and what its message says; `None` where it meets the constraints, or
/// where that cannot be settled.
fn violation(
    binder: &Binder<'_>,
    parameter: SymbolId,
    argument: &Type,
    substitution: &HashMap<SymbolId, Type>,
    owner: &str,
    written: bool,
) -> Option<(ErrorCode, Vec<String>)> {
    let symbols = binder.compilation().symbols();
    if undecidable(argument) || !unambiguous(binder, argument) {
        return None;
    }
    // A `ref struct` meets an interface constraint by implementing it and
    // never converts to it.
    let ref_like = argument.symbol().is_some_and(|symbol| {
        symbols
            .get(symbol)
            .as_named_type()
            .is_some_and(|detail| detail.ref_like)
    });
    let nullable_value = binder.nullable_underlying(argument).is_some();
    let detail = symbols.get(parameter).as_type_parameter()?;
    let name = symbols.get(parameter).name.clone();
    let shown = shown(binder, argument);
    if detail.reference_type && !argument.is_reference_type(symbols) {
        return Some((
            ErrorCode::ErrRefConstraintNotSatisfied,
            vec![owner.to_string(), name, shown],
        ));
    }
    // `unmanaged` is a `struct` constraint with more to say, and says it
    // with a code of its own.
    if detail.value_type
        && !detail.unmanaged
        && (argument.is_reference_type(symbols) || nullable_value)
    {
        return Some((
            ErrorCode::ErrValConstraintNotSatisfied,
            vec![owner.to_string(), name, shown],
        ));
    }
    if ref_like || nullable_value {
        return None;
    }
    for constraint in binder.base_types_of(parameter) {
        // What inference fixes from another type parameter's constraint
        // is not what Rustlyn infers: a constraint that names the call's
        // other type parameters binds only arguments that were written out.
        if !written && names_any(&constraint, substitution, parameter) {
            continue;
        }
        let constraint = constraint.substitute(substitution);
        if undecidable(&constraint)
            || !unambiguous(binder, &constraint)
            || binder.converts_implicitly(argument, &constraint)
        {
            continue;
        }
        let shown_constraint = self::shown(binder, &constraint);
        let code = if argument.is_reference_type(symbols) {
            ErrorCode::ErrGenericConstraintNotSatisfiedRefType
        } else {
            ErrorCode::ErrGenericConstraintNotSatisfiedValType
        };
        return Some((code, vec![owner.to_string(), shown_constraint, name, shown]));
    }
    None
}

/// How a type reads in a message: `int?` for a `Nullable<int>`.
fn shown(binder: &Binder<'_>, ty: &Type) -> String {
    ty.display_by(binder.compilation().symbols(), &|symbol, arguments| {
        let named = Type::Named {
            symbol,
            type_arguments: arguments.to_vec(),
        };
        binder
            .nullable_underlying(&named)
            .map(|inner| format!("{}?", shown(binder, &inner)))
    })
}

/// Whether a type names any of the type parameters given but one.
fn names_any(ty: &Type, parameters: &HashMap<SymbolId, Type>, except: SymbolId) -> bool {
    match ty {
        Type::TypeParameter(symbol) => *symbol != except && parameters.contains_key(symbol),
        Type::Named { type_arguments, .. } => type_arguments
            .iter()
            .any(|argument| names_any(argument, parameters, except)),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            names_any(element, parameters, except)
        }
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| names_any(&element.ty, parameters, except)),
        _ => false,
    }
}
