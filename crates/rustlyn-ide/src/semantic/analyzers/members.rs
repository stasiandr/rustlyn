//! Members nobody needs, and members used that should not be.
//!
//! A private member can only be used inside its type, so whether it is used
//! at all is a question about the files that declare the type — usually one.
//! That is what makes IDE0051 and IDE0052 cheap enough to run as the user
//! types, and why they are limited to private members: an internal one
//! would need the whole project searched.
//!
//! A private member is also used by a construct of the language that looks it
//! up by name and writes none: `await this` runs `GetAwaiter`, `var (a, b) =
//! this` runs `Deconstruct`, a collection initializer `Add`, a query
//! `Select`, `this[^1]` and `this[1..2]` `Length` or `Count` and `Slice`. The
//! binder says which member such a construct runs; where it does not resolve
//! the construct (queries, ranges, interpolated string handlers, `fixed`) or
//! the body did not bind, a member with one of those names is taken to be
//! used if the file holds the construct at all.
//!
//! IDE0044 does not offer `readonly` for a field whose value is a struct that
//! is not `readonly`, a tuple, or a type parameter that may be a struct, where
//! a member is called or written on it outside a constructor: on a `readonly`
//! field that acts on a copy, or does not compile (CS1648).

use std::collections::{HashMap, HashSet};

use rustlyn_diagnostics::Severity;
use rustlyn_semantics::{
    Accessibility, MethodKind, Modifiers, SpecialType, SymbolId, SymbolKind, Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};

use super::super::View;
use super::{Access, AnalyzerDiagnostic, Facts, Use, access_of, is_discard_name};
use crate::semantic::Resolved;

/// A member the file declares, with its name.
struct Declared {
    /// The declaration: the method, the property, the field's declarator.
    node: SyntaxNode,
    name: SyntaxToken,
    symbol: SymbolId,
}

/// Every type member the file declares that has a name of its own.
fn declared_members(view: &View<'_>) -> Vec<Declared> {
    let mut found = Vec::new();
    for node in view.root.descendants() {
        let named: Vec<SyntaxNode> = match node.kind() {
            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => node
                .child_of_kind(SyntaxKind::VariableDeclaration)
                .map(|declaration| {
                    declaration
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                        .collect()
                })
                .unwrap_or_default(),
            SyntaxKind::MethodDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::ConstructorDeclaration => vec![node.clone()],
            _ => continue,
        };
        for declaration in named {
            let Some(name) = declaration.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                continue;
            };
            let Some(symbol) = view.model.declared_symbol(&declaration) else {
                continue;
            };
            found.push(Declared {
                node: declaration,
                name,
                symbol,
            });
        }
    }
    found
}

/// The declaration that carries a member's attributes and modifiers: a
/// field's is the whole `FieldDeclaration`, not its declarator.
pub(in crate::semantic) fn outer_declaration(node: &SyntaxNode) -> SyntaxNode {
    if node.kind() == SyntaxKind::VariableDeclarator
        && let Some(outer) = node.ancestors().nth(1)
    {
        return outer;
    }
    node.clone()
}

fn has_attributes(declaration: &SyntaxNode) -> bool {
    outer_declaration(declaration)
        .children()
        .any(|child| child.kind() == SyntaxKind::AttributeList)
}

/// Every use of `symbol`: in this file, and — for a partial type — in the
/// other files that declare it.
fn uses_of(view: &View<'_>, facts: &Facts, symbol: SymbolId) -> Vec<Use> {
    let mut found = facts.uses.get(&symbol).cloned().unwrap_or_default();
    let symbols = view.compilation().symbols();
    let Some(container) = symbols.get(symbol).container else {
        return found;
    };
    let name = symbols.get(symbol).name.clone();
    let mut trees: Vec<usize> = symbols
        .get(container)
        .locations
        .iter()
        .map(|location| location.tree)
        .filter(|&tree| tree != view.tree)
        .collect();
    trees.sort_unstable();
    trees.dedup();
    for tree in trees {
        let Some(mut other) = view.semantic.view(tree) else {
            continue;
        };
        let tokens: Vec<SyntaxToken> = other
            .root
            .descendant_tokens()
            .filter(|token| {
                token.kind() == SyntaxKind::IdentifierToken && token.value_text() == name
            })
            .collect();
        for token in tokens {
            if let Some(resolved @ Resolved::Symbol(found_symbol)) = other.resolve(&token)
                && found_symbol == symbol
                && !super::declares(&token, &resolved)
            {
                let access = access_of(&token);
                found.push(Use { token, access });
            }
        }
    }
    found
}

/// The constructs of the language that look a member up by its name in the
/// type of what they are given, which then runs it without the program
/// writing the name: `await x` finds `GetAwaiter`, `from a in x select a`
/// finds `Select`, `var (a, b) = x` `Deconstruct`.
fn constructs_looking_for(name: &str) -> &'static [SyntaxKind] {
    match name {
        "Deconstruct" => &[
            SyntaxKind::DeclarationExpression,
            SyntaxKind::TupleExpression,
            SyntaxKind::ParenthesizedVariableDesignation,
            SyntaxKind::PositionalPatternClause,
            SyntaxKind::ForEachVariableStatement,
        ],
        "Add" => &[
            SyntaxKind::CollectionInitializerExpression,
            SyntaxKind::ComplexElementInitializerExpression,
            SyntaxKind::CollectionExpression,
        ],
        "GetAwaiter" | "IsCompleted" | "GetResult" | "OnCompleted" | "UnsafeOnCompleted" => {
            &[SyntaxKind::AwaitExpression]
        }
        "Select" | "SelectMany" | "Where" | "OrderBy" | "OrderByDescending" | "ThenBy"
        | "ThenByDescending" | "GroupBy" | "Join" | "GroupJoin" | "Cast" | "OfType" => {
            &[SyntaxKind::QueryExpression]
        }
        "Slice" => &[SyntaxKind::RangeExpression, SyntaxKind::SlicePattern],
        "Length" | "Count" => &[
            SyntaxKind::RangeExpression,
            SyntaxKind::IndexExpression,
            SyntaxKind::ListPattern,
            SyntaxKind::SlicePattern,
        ],
        "GetEnumerator" | "MoveNext" | "Current" | "GetAsyncEnumerator" | "MoveNextAsync" => &[
            SyntaxKind::ForEachStatement,
            SyntaxKind::ForEachVariableStatement,
        ],
        "Dispose" | "DisposeAsync" => &[
            SyntaxKind::UsingStatement,
            SyntaxKind::LocalDeclarationStatement,
            SyntaxKind::ForEachStatement,
            SyntaxKind::ForEachVariableStatement,
        ],
        "GetPinnableReference" => &[SyntaxKind::FixedStatement],
        "AppendLiteral" | "AppendFormatted" | "ToStringAndClear" => {
            &[SyntaxKind::InterpolatedStringExpression]
        }
        _ => &[],
    }
}

/// The members the file's bodies run through a construct that writes no name
/// for them, as the binder resolved the construct.
fn run_by_constructs(view: &View<'_>, facts: &Facts) -> HashSet<SymbolId> {
    let text = view.root.full_text();
    let mut reached = HashSet::new();
    for body in facts.bodies.iter().filter(|body| !body.broken) {
        for (_, symbol, _, _) in
            view.semantic
                .implicit_symbols(&view.model, &body.bound, &body.owner, &text)
        {
            reached.insert(symbol);
        }
    }
    reached
}

/// Whether the file holds a construct that may run `member` by its name
/// where the binder's answer cannot be trusted or the construct is one the
/// binder does not resolve: a body that did not bind cleanly, or a query, an
/// interpolated string, a `fixed`, a collection expression. A member of a
/// partial type may be run from the parts in other files.
fn may_be_run_by_a_construct(view: &View<'_>, facts: &Facts, member: &Declared) -> bool {
    let symbols = view.compilation().symbols();
    let name = symbols.get(member.symbol).name.as_str();
    let kinds = constructs_looking_for(name);
    if kinds.is_empty() {
        return false;
    }
    let partial = symbols
        .get(member.symbol)
        .container
        .is_some_and(|container| {
            let mut trees: Vec<usize> = symbols
                .get(container)
                .locations
                .iter()
                .map(|location| location.tree)
                .collect();
            trees.sort_unstable();
            trees.dedup();
            trees.len() > 1
        });
    if partial {
        return true;
    }
    let unresolved_kind = matches!(
        name,
        "Select"
            | "SelectMany"
            | "Where"
            | "OrderBy"
            | "OrderByDescending"
            | "ThenBy"
            | "ThenByDescending"
            | "GroupBy"
            | "Join"
            | "GroupJoin"
            | "Cast"
            | "OfType"
            | "Slice"
            | "Length"
            | "Count"
            | "GetPinnableReference"
            | "AppendLiteral"
            | "AppendFormatted"
            | "ToStringAndClear"
    );
    if !unresolved_kind && !facts.bodies.iter().any(|body| body.broken) {
        return false;
    }
    view.root
        .descendants()
        .any(|node| kinds.contains(&node.kind()))
}

/// A member as a message names it: `Player.health`, `Player.Heal(int)`.
fn member_name(view: &View<'_>, symbol: SymbolId) -> String {
    let symbols = view.compilation().symbols();
    let found = symbols.get(symbol);
    let container = found
        .container
        .map(|container| symbols.get(container).name.clone())
        .unwrap_or_default();
    match found.as_method() {
        Some(method) => {
            let name = if method.method_kind == MethodKind::Constructor {
                container.clone()
            } else {
                found.name.clone()
            };
            let parameters: Vec<String> = method
                .parameters
                .iter()
                .map(|&parameter| view.model.type_of_symbol(parameter).display(symbols))
                .collect();
            format!("{container}.{name}({})", parameters.join(", "))
        }
        None if container.is_empty() => found.name.clone(),
        None => format!("{container}.{}", found.name),
    }
}

/// Whether `ty` derives from one of Unity's classes that are sent messages.
fn is_unity_behaviour(view: &View<'_>, ty: SymbolId) -> bool {
    let symbols = view.compilation().symbols();
    let mut current = Some(ty);
    let mut steps = 0;
    while let Some(at) = current {
        if crate::semantic::unity::is_message_receiver(&symbols.get(at).name) {
            return true;
        }
        steps += 1;
        if steps > 32 {
            return false;
        }
        current = match view.model.binder().base_class_of(at) {
            Some(Type::Named { symbol, .. }) => Some(symbol),
            _ => None,
        };
    }
    false
}

/// Whether a private member is one IDE0051 and IDE0052 look at.
fn is_candidate(view: &View<'_>, facts: &Facts, member: &Declared) -> bool {
    let symbols = view.compilation().symbols();
    let found = symbols.get(member.symbol);
    if found.accessibility != Accessibility::Private
        || has_attributes(&member.node)
        || facts.unresolved.contains(&found.name)
        || member
            .node
            .child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier)
            .is_some()
    {
        return false;
    }
    let Some(container) = found.container else {
        return false;
    };
    if matches!(
        symbols.get(container).type_kind(),
        Some(TypeKind::Interface) | None
    ) {
        return false;
    }
    let inherited = Modifiers::ABSTRACT
        .union(Modifiers::VIRTUAL)
        .union(Modifiers::OVERRIDE)
        .union(Modifiers::EXTERN)
        .union(Modifiers::PARTIAL);
    if found.modifiers.bits() & inherited.bits() != 0 {
        return false;
    }
    match found.as_method() {
        Some(method) => match method.method_kind {
            // A private constructor with no parameters is how a type says it
            // is not to be made.
            MethodKind::Constructor => !method.parameters.is_empty(),
            MethodKind::Ordinary => {
                let entry_point =
                    found.name == "Main" && found.modifiers.contains(Modifiers::STATIC);
                let unity_message = crate::semantic::unity::is_message(&found.name)
                    && is_unity_behaviour(view, container);
                !entry_point && !unity_message
            }
            _ => false,
        },
        None => true,
    }
}

/// IDE0051 and IDE0052: private members nobody uses, and private fields
/// nobody reads.
pub(super) fn unused_members(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let mut reached: Option<HashSet<SymbolId>> = None;
    for member in declared_members(view) {
        if !is_candidate(view, facts, &member) {
            continue;
        }
        let symbols = view.compilation().symbols();
        let uses = uses_of(view, facts, member.symbol);
        let constructed = facts.constructed.contains(&member.symbol);
        let name = member_name(view, member.symbol);
        if uses.is_empty() && !constructed {
            // A construct of the language may run it without the name.
            if !constructs_looking_for(&symbols.get(member.symbol).name).is_empty() {
                let reached = reached.get_or_insert_with(|| run_by_constructs(view, facts));
                if reached.contains(&member.symbol)
                    || may_be_run_by_a_construct(view, facts, &member)
                {
                    continue;
                }
            }
            // Written only where it is declared, with a constant: CS0414 to
            // the compiler (the initializer is an assignment), beside the
            // IDE's "unused".
            if symbols.get(member.symbol).kind == SymbolKind::Field
                && outer_declaration(&member.node).kind() == SyntaxKind::FieldDeclaration
                && !symbols
                    .get(member.symbol)
                    .modifiers
                    .contains(Modifiers::CONST)
                && member
                    .node
                    .child_of_kind(SyntaxKind::EqualsValueClause)
                    .and_then(|clause| clause.children().next())
                    .is_some_and(|value| is_constant(&value))
            {
                found.push(AnalyzerDiagnostic::new(
                    "CS0414",
                    Severity::Warning,
                    member.name.span(),
                    format!("The field '{name}' is assigned but its value is never used"),
                ));
            }
            found.push(
                AnalyzerDiagnostic::new(
                    "IDE0051",
                    Severity::Info,
                    member.name.span(),
                    format!("Private member '{name}' is unused"),
                )
                .unnecessary(),
            );
        } else if symbols.get(member.symbol).kind == SymbolKind::Field
            && member.node.kind() == SyntaxKind::VariableDeclarator
            && outer_declaration(&member.node).kind() == SyntaxKind::FieldDeclaration
            && !symbols
                .get(member.symbol)
                .modifiers
                .contains(Modifiers::CONST)
            && uses.iter().all(|found| found.access == Access::Write)
        {
            // The compiler says the same of a field, as a warning (CS0414),
            // where everything written to it is a constant, as it does of a
            // local (CS0219): `private bool done = false;` and not a field
            // a filter or a constructor's argument is kept in.
            let initializer = member
                .node
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().next());
            let values: Vec<Option<SyntaxNode>> = initializer
                .into_iter()
                .map(Some)
                .chain(uses.iter().map(|found| assigned_value(&found.token)))
                .collect();
            if !values.is_empty()
                && values
                    .iter()
                    .all(|value| value.as_ref().is_some_and(is_constant))
            {
                found.push(AnalyzerDiagnostic::new(
                    "CS0414",
                    Severity::Warning,
                    member.name.span(),
                    format!("The field '{name}' is assigned but its value is never used"),
                ));
            }
            found.push(
                AnalyzerDiagnostic::new(
                    "IDE0052",
                    Severity::Info,
                    member.name.span(),
                    format!(
                        "Private member '{name}' can be removed as the value assigned to it is never read"
                    ),
                )
                .unnecessary(),
            );
        }
    }
}

/// What `name = value` assigns, where the token is the name written to —
/// alone or after `this.`.
fn assigned_value(token: &SyntaxToken) -> Option<SyntaxNode> {
    let mut target = token.parent().clone();
    if let Some(access) = target
        .parent()
        .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
        .filter(|access| access.children().last().as_ref() == Some(&target))
    {
        target = access.clone();
    }
    let assignment = target
        .parent()
        .filter(|parent| parent.kind() == SyntaxKind::SimpleAssignmentExpression)?;
    let mut sides = assignment.children();
    (sides.next().as_ref() == Some(&target))
        .then(|| sides.next())
        .flatten()
}

/// Whether a value is a constant as the compiler sees one written: a
/// literal, `null`, `default`, a negated number.
fn is_constant(value: &SyntaxNode) -> bool {
    let mut value = value.clone();
    while value.kind() == SyntaxKind::ParenthesizedExpression {
        let Some(inner) = value.children().next() else {
            return false;
        };
        value = inner;
    }
    match value.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression
        | SyntaxKind::DefaultLiteralExpression
        | SyntaxKind::DefaultExpression => true,
        SyntaxKind::UnaryMinusExpression => value
            .children()
            .next()
            .is_some_and(|operand| operand.kind() == SyntaxKind::NumericLiteralExpression),
        _ => false,
    }
}

/// IDE0044: a private field written only where it is initialized — its
/// declaration, and the constructors of its type — can be `readonly`.
pub(super) fn readonly_fields(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let already: Vec<(u32, &'static str)> = found
        .iter()
        .map(|diagnostic| (diagnostic.span.start(), diagnostic.id))
        .collect();
    for member in declared_members(view) {
        let symbols = view.compilation().symbols();
        let field = symbols.get(member.symbol);
        if field.kind != SymbolKind::Field
            || field.accessibility != Accessibility::Private
            || outer_declaration(&member.node).kind() != SyntaxKind::FieldDeclaration
            || has_attributes(&member.node)
        {
            continue;
        }
        let fixed = Modifiers::CONST
            .union(Modifiers::READONLY)
            .union(Modifiers::VOLATILE)
            .union(Modifiers::FIXED);
        if field.modifiers.bits() & fixed.bits() != 0 {
            continue;
        }
        let Some(container) = field.container else {
            continue;
        };
        let may_change = may_be_mutable_value(view, &view.model.type_of_symbol(member.symbol));
        // Said already: a field nobody reads is better removed than frozen.
        if already.iter().any(|&(start, id)| {
            start == member.name.span().start() && matches!(id, "IDE0051" | "IDE0052")
        }) {
            continue;
        }
        let is_static = field.modifiers.contains(Modifiers::STATIC);
        let uses = uses_of(view, facts, member.symbol);
        let mut frozen = uses
            .iter()
            .filter(|found| found.access != Access::Read)
            .all(|found| written_while_constructing(view, &found.token, container, is_static));
        // A member called or written on a value type that is not `readonly`
        // would act on a copy of a `readonly` field, or not compile.
        if frozen && may_change {
            frozen = uses.iter().all(|found| {
                copied_only(&found.token)
                    || written_while_constructing(view, &found.token, container, is_static)
            });
        }
        if frozen {
            found.push(AnalyzerDiagnostic::new(
                "IDE0044",
                Severity::Info,
                member.name.span(),
                "Make field readonly",
            ));
        }
    }
}

/// Whether a value of `ty` could be changed through a `readonly` field
/// without anyone noticing: a struct that is not `readonly`, other than the
/// language's own and enums and `Nullable`; a tuple; a type parameter that
/// is not known to be a reference type, which may be such a struct. An array
/// is a reference: its elements are not the field.
fn may_be_mutable_value(view: &View<'_>, ty: &Type) -> bool {
    let symbols = view.compilation().symbols();
    match ty {
        Type::Named { symbol, .. } => {
            let found = symbols.get(*symbol);
            if !matches!(
                found.type_kind(),
                Some(TypeKind::Struct | TypeKind::RecordStruct)
            ) {
                return false;
            }
            let special = SpecialType::ALL
                .iter()
                .any(|&special| view.compilation().special_type(special) == Some(*symbol));
            // `Nullable<T>` has no member that changes it: what is inside
            // is read through a copy.
            let nullable = symbols
                .qualified_name(*symbol)
                .starts_with("System.Nullable");
            !special && !nullable && !found.modifiers.contains(Modifiers::READONLY)
        }
        Type::Tuple(_) => true,
        Type::TypeParameter(parameter) => {
            !view.model.binder().is_reference_type_parameter(*parameter)
        }
        _ => false,
    }
}

/// Whether the field named by `token` is only copied where it is used: handed
/// over as an argument, returned, assigned to something, used as an
/// initializer. Anything else — `t.Inc()`, `t.Item1 = 5`, `t[0]`, `foreach`
/// over it — works on the field itself.
fn copied_only(token: &SyntaxToken) -> bool {
    let mut node = token.parent().clone();
    // `this.t`.
    if let Some(access) = node
        .parent()
        .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
        && access.children().last().as_ref() == Some(&node)
        && access
            .children()
            .next()
            .is_some_and(|receiver| receiver.kind() == SyntaxKind::ThisExpression)
    {
        node = access.clone();
    }
    loop {
        let Some(parent) = node.parent().cloned() else {
            return false;
        };
        match parent.kind() {
            SyntaxKind::ParenthesizedExpression => node = parent,
            SyntaxKind::Argument
            | SyntaxKind::ReturnStatement
            | SyntaxKind::ArrowExpressionClause
            | SyntaxKind::EqualsValueClause => return true,
            SyntaxKind::SimpleAssignmentExpression => {
                return parent.children().next().as_ref() != Some(&node);
            }
            _ => return false,
        }
    }
}

/// Whether a write of a field happens while its object is being made: in a
/// constructor of its type — the static one for a static field — and not
/// inside a lambda or local function there, which could run later.
fn written_while_constructing(
    view: &View<'_>,
    token: &SyntaxToken,
    container: SymbolId,
    is_static: bool,
) -> bool {
    // `other.count = 1` writes some other object's field.
    let name = token.parent();
    if let Some(access) = name
        .parent()
        .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
        && access.children().last().as_ref() == Some(name)
        && access
            .children()
            .next()
            .is_none_or(|receiver| receiver.kind() != SyntaxKind::ThisExpression)
        && !is_static
    {
        return false;
    }
    for ancestor in name.ancestors() {
        match ancestor.kind() {
            SyntaxKind::ConstructorDeclaration => {
                let constructor_static = ancestor
                    .child_token_of_kind(SyntaxKind::StaticKeyword)
                    .is_some();
                let symbols = view.compilation().symbols();
                let ours = view
                    .model
                    .declared_symbol(&ancestor)
                    .and_then(|constructor| symbols.get(constructor).container)
                    == Some(container);
                return ours && constructor_static == is_static;
            }
            SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::FieldDeclaration
            | SyntaxKind::GlobalStatement => return false,
            _ => {}
        }
    }
    false
}

/// IDE0060: a parameter of a private or internal method that the method
/// never reads. Not where the signature is not the method's to choose: an
/// override, an interface's, an event handler's, a method handed out as a
/// delegate, one with no body worth the name.
pub(super) fn unused_parameters(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    for member in declared_members(view) {
        if !matches!(
            member.node.kind(),
            SyntaxKind::MethodDeclaration | SyntaxKind::ConstructorDeclaration
        ) {
            continue;
        }
        let Some(parameters) = unused_parameter_candidates(view, facts, &member) else {
            continue;
        };
        let symbols = view.compilation().symbols();
        for parameter in parameters {
            if facts
                .uses
                .get(&parameter)
                .is_some_and(|uses| !uses.is_empty())
            {
                continue;
            }
            let Some(token) = parameter_token(&member.node, &symbols.get(parameter).name) else {
                continue;
            };
            let name = symbols.get(parameter).name.clone();
            found.push(
                AnalyzerDiagnostic::new(
                    "IDE0060",
                    Severity::Info,
                    token.span(),
                    format!("Remove unused parameter '{name}'"),
                )
                .unnecessary(),
            );
        }
    }
}

/// The name token of the parameter `name` in a method's parameter list.
fn parameter_token(method: &SyntaxNode, name: &str) -> Option<SyntaxToken> {
    method
        .child_of_kind(SyntaxKind::ParameterList)?
        .children()
        .filter(|parameter| parameter.kind() == SyntaxKind::Parameter)
        .filter_map(|parameter| parameter.child_token_of_kind(SyntaxKind::IdentifierToken))
        .find(|token| token.value_text() == name)
}

/// The parameters of a method IDE0060 may report, or `None` when the method
/// is not one it looks at.
fn unused_parameter_candidates(
    view: &View<'_>,
    facts: &Facts,
    member: &Declared,
) -> Option<Vec<SymbolId>> {
    let symbols = view.compilation().symbols();
    let found = symbols.get(member.symbol);
    let method = found.as_method()?;
    if !matches!(
        found.accessibility,
        Accessibility::Private | Accessibility::Internal | Accessibility::ProtectedAndInternal
    ) || has_attributes(&member.node)
        || member
            .node
            .child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier)
            .is_some()
        || (found.name == "Main" && found.modifiers.contains(Modifiers::STATIC))
    {
        return None;
    }
    let inherited = Modifiers::ABSTRACT
        .union(Modifiers::VIRTUAL)
        .union(Modifiers::OVERRIDE)
        .union(Modifiers::EXTERN)
        .union(Modifiers::PARTIAL);
    if found.modifiers.bits() & inherited.bits() != 0 {
        return None;
    }
    let container = found.container?;
    if symbols.get(container).type_kind() == Some(TypeKind::Interface)
        || implements_by_name(view, container, &found.name)
    {
        return None;
    }
    // `void OnClick(object sender, EventArgs e)`: the event decides.
    if method.parameters.len() == 2
        && view
            .model
            .type_of_symbol(method.parameters[1])
            .display(symbols)
            .ends_with("EventArgs")
    {
        return None;
    }
    // Handed out as a delegate: its signature is the delegate's.
    if facts
        .uses
        .get(&member.symbol)
        .is_some_and(|uses| uses.iter().any(|found| !is_called(&found.token)))
    {
        return None;
    }
    // A body that does nothing, or only throws, is a placeholder.
    if is_placeholder_body(&member.node) {
        return None;
    }
    let body = facts.body_around(&member.node)?;
    if body.broken || body.owner.span() != member.node.span() {
        return None;
    }
    Some(
        method
            .parameters
            .iter()
            .enumerate()
            .filter(|&(index, &parameter)| {
                // An extension method's `this` is what makes it one.
                let receiver = index == 0 && method.is_extension;
                !receiver && !is_discard_name(&symbols.get(parameter).name)
            })
            .map(|(_, &parameter)| parameter)
            .collect(),
    )
}

/// Whether a type implements, through an interface, something named `name`:
/// its method then has the interface's signature.
fn implements_by_name(view: &View<'_>, ty: SymbolId, name: &str) -> bool {
    let symbols = view.compilation().symbols();
    let mut queue: Vec<SymbolId> = vec![ty];
    let mut seen = std::collections::HashSet::new();
    while let Some(current) = queue.pop() {
        if !seen.insert(current) {
            continue;
        }
        if current != ty
            && symbols.get(current).type_kind() == Some(TypeKind::Interface)
            && !symbols.lookup(current, name).is_empty()
        {
            return true;
        }
        for base in view.model.base_types_of(current) {
            if let Type::Named { symbol, .. } = base {
                queue.push(symbol);
            }
        }
    }
    false
}

/// Whether the name `token` is what an invocation calls.
fn is_called(token: &SyntaxToken) -> bool {
    let mut node = token.parent().clone();
    loop {
        let Some(parent) = node.parent().cloned() else {
            return false;
        };
        match parent.kind() {
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
                if parent.children().last().as_ref() == Some(&node) =>
            {
                node = parent;
            }
            SyntaxKind::InvocationExpression => {
                return parent.children().next().as_ref() == Some(&node);
            }
            SyntaxKind::ConditionalAccessExpression => node = parent,
            // `nameof(M)` names the method without taking it.
            SyntaxKind::Argument => {
                return parent
                    .ancestors()
                    .find(|ancestor| ancestor.kind() == SyntaxKind::InvocationExpression)
                    .and_then(|call| call.children().next())
                    .is_some_and(|callee| super::is_nameof(&callee));
            }
            _ => return false,
        }
    }
}

/// `{ }`, `{ throw ...; }` and `=> throw ...`.
fn is_placeholder_body(method: &SyntaxNode) -> bool {
    if let Some(block) = method.child_of_kind(SyntaxKind::Block) {
        let statements: Vec<SyntaxNode> = block.children().collect();
        return match statements.as_slice() {
            [] => true,
            [only] => only.kind() == SyntaxKind::ThrowStatement,
            _ => false,
        };
    }
    if let Some(arrow) = method.child_of_kind(SyntaxKind::ArrowExpressionClause) {
        return arrow
            .children()
            .next()
            .is_some_and(|expression| expression.kind() == SyntaxKind::ThrowExpression);
    }
    true
}

/// What `[Obsolete]` on a declaration says: its message, and whether using
/// it is an error.
fn obsolete(declaration: &SyntaxNode) -> Option<(Option<String>, bool)> {
    let outer = outer_declaration(declaration);
    let attribute = outer
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
        .flat_map(|list| list.children())
        .filter(|child| child.kind() == SyntaxKind::Attribute)
        .find(|attribute| {
            attribute.children().next().is_some_and(|name| {
                let written = name.text();
                let last = written.trim().rsplit(['.', ':']).next().unwrap_or("");
                matches!(last.trim(), "Obsolete" | "ObsoleteAttribute")
            })
        })?;
    let arguments: Vec<SyntaxNode> = attribute
        .child_of_kind(SyntaxKind::AttributeArgumentList)
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
                .collect()
        })
        .unwrap_or_default();
    let message = arguments.first().and_then(|argument| {
        let literal = argument
            .children()
            .find(|child| child.kind() == SyntaxKind::StringLiteralExpression)?;
        match literal.first_token()?.value() {
            rustlyn_syntax::TokenValue::String(value) => Some(value.to_string()),
            _ => None,
        }
    });
    let error = arguments.get(1).is_some_and(|argument| {
        argument
            .children()
            .any(|child| child.kind() == SyntaxKind::TrueLiteralExpression)
    });
    Some((message, error))
}

/// CS0612, CS0618 and CS0619: a use of a type or member marked
/// `[Obsolete]`, outside code that is obsolete itself.
pub(super) fn obsolete_uses(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    let mut known: HashMap<SymbolId, Option<(Option<String>, bool)>> = HashMap::new();
    let mut marked = |symbol: SymbolId| -> Option<(Option<String>, bool)> {
        known
            .entry(symbol)
            .or_insert_with(|| {
                // An assembly's `[Obsolete]`, as its loader read it.
                if compilation.is_from_metadata(symbol) {
                    return compilation.obsolete_of(symbol);
                }
                compilation
                    .declaration_node(symbol)
                    .and_then(|node| obsolete(&node))
            })
            .clone()
    };
    let mut entries: Vec<(&SymbolId, &Vec<Use>)> = facts.uses.iter().collect();
    entries.sort_by_key(|(symbol, _)| symbol.index());
    for (&symbol, uses) in entries {
        // A constructor of an obsolete type is a use of the type.
        let mut subject = symbol;
        let mut mark = marked(symbol);
        if mark.is_none()
            && symbols
                .get(symbol)
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor)
            && let Some(container) = symbols.get(symbol).container
        {
            subject = container;
            mark = marked(container);
        }
        let Some((message, error)) = mark else {
            continue;
        };
        let name = if symbols.get(subject).kind == SymbolKind::NamedType {
            symbols.qualified_name(subject)
        } else {
            member_name(view, subject)
        };
        for found_use in uses {
            // `var` stands for the type without naming it, and Roslyn says
            // nothing of it.
            if found_use.token.value_text() == "var"
                && symbols.get(subject).kind == SymbolKind::NamedType
            {
                continue;
            }
            let inside_obsolete = found_use.token.parent().ancestors().any(|ancestor| {
                (ancestor.kind().is_declaration_node()
                    || ancestor.kind() == SyntaxKind::VariableDeclarator)
                    && obsolete(&ancestor).is_some()
            });
            if inside_obsolete {
                continue;
            }
            let (id, severity, text) = match (&message, error) {
                (Some(message), true) => (
                    "CS0619",
                    Severity::Error,
                    format!("'{name}' is obsolete: '{message}'"),
                ),
                (Some(message), false) => (
                    "CS0618",
                    Severity::Warning,
                    format!("'{name}' is obsolete: '{message}'"),
                ),
                (None, _) => ("CS0612", Severity::Warning, format!("'{name}' is obsolete")),
            };
            found.push(
                AnalyzerDiagnostic::new(id, severity, found_use.token.span(), text).deprecated(),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::found_with;

    #[test]
    fn private_members_nobody_uses() {
        let text = "class Player {\n\
                      private int health;\n\
                      private int armor = 3;\n\
                      private const int Max = 10;\n\
                      private static int instances;\n\
                      private int Score { get; set; }\n\
                      private void Heal() { }\n\
                      private void Recurse() { Recurse(); }\n\
                      private Player() { }\n\
                      private Player(int level) { }\n\
                      public int Used() => armor + Max;\n\
                      void Implicit() { }\n\
                      public void Public() { }\n\
                      private event System.Action Died;\n\
                    }\n";
        assert_eq!(
            found_with(text, "IDE0051"),
            vec![
                "health",
                "instances",
                "Score",
                "Heal",
                "Player",
                "Implicit",
                "Died"
            ]
        );
    }

    #[test]
    fn what_is_reached_another_way_is_used() {
        let text = "using System;\n\
                    class C {\n\
                      private int named;\n\
                      private void Handler() { }\n\
                      private C(int x) { }\n\
                      private C(string s) : this(1) { }\n\
                      private static int Parse(string s) => 0;\n\
                      public string Name() => nameof(named);\n\
                      public Action Take() => Handler;\n\
                      public static C Make() { C c = new(\"a\"); return c; }\n\
                      public Func<string, int> Parser() => Parse;\n\
                      [Obsolete] private void Attributed() { }\n\
                      static void Main() { }\n\
                    }\n";
        assert!(
            found_with(text, "IDE0051").is_empty(),
            "{:?}",
            found_with(text, "IDE0051")
        );
    }

    #[test]
    fn a_member_of_a_partial_type_used_in_another_file_is_used() {
        let a = "partial class P { private int shared; private void Helper() { } }\n";
        let b = "partial class P { public int Read() { Helper(); return shared; } }\n";
        let semantic = super::super::super::tests::compile(&[("C.cs", a), ("D.cs", b)], false)
            .expect("compiled");
        let found = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .expect("analyzed");
        assert!(
            found.iter().all(|diagnostic| diagnostic.id != "IDE0051"),
            "{found:?}"
        );
    }

    #[test]
    fn unity_messages_are_not_unused() {
        let text = "class MonoBehaviour { }\n\
                    class Mover : MonoBehaviour { private void Update() { } private void Helper() { } }\n";
        assert_eq!(found_with(text, "IDE0051"), vec!["Helper"]);
    }

    #[test]
    fn fields_written_and_never_read() {
        let text = "class C {\n\
                      private int written;\n\
                      private int counted;\n\
                      private int read;\n\
                      private int both;\n\
                      public void M() { written = 1; counted++; counted += 2; read = 2; System.Console.WriteLine(read); both = both + 1; }\n\
                    }\n";
        assert_eq!(found_with(text, "IDE0052"), vec!["written", "counted"]);
    }

    #[test]
    fn fields_only_set_while_constructing_can_be_readonly() {
        let text = "struct Mutable { public int X; }\n\
                    readonly struct Frozen { public readonly int X; }\n\
                    class C {\n\
                      private int size;\n\
                      private int count;\n\
                      private string name = \"n\";\n\
                      private static int shared;\n\
                      private int later;\n\
                      private int lambda;\n\
                      private Mutable mutable;\n\
                      private Frozen frozen;\n\
                      private readonly int already;\n\
                      public int other;\n\
                      static C() { shared = 1; }\n\
                      public C(int size, C copy) {\n\
                        this.size = size; count = 2; copy.count = 3;\n\
                        System.Action a = () => lambda = 1;\n\
                      }\n\
                      public void Reset() { later = 0; }\n\
                      public int Sum() => size + count + name.Length + shared + later + lambda + mutable.X + frozen.X + already;\n\
                    }\n";
        assert_eq!(
            found_with(text, "IDE0044"),
            vec!["size", "name", "shared", "frozen"]
        );
    }

    #[test]
    fn parameters_nobody_reads() {
        let text = "using System;\n\
                    interface IRun { void Run(int speed); }\n\
                    class EventArgs { }\n\
                    class C : IRun {\n\
                      private int Add(int a, int b, int _) => a;\n\
                      internal void Log(string message, int level) { Console.WriteLine(message); }\n\
                      public void Public(int unused) { Console.WriteLine(1); }\n\
                      public void Run(int speed) { Console.WriteLine(1); }\n\
                      private void OnClick(object sender, EventArgs e) { Console.WriteLine(1); }\n\
                      private void Todo(int later) { }\n\
                      private void Throws(int x) => throw new InvalidOperationException();\n\
                      private void Given(int x) { Console.WriteLine(2); }\n\
                      public Action<int> Hand() => Given;\n\
                      private C(int seed) { Console.WriteLine(3); }\n\
                      public C() : this(1) { }\n\
                      public int Use() => Add(1, 2, 3);\n\
                    }\n";
        assert_eq!(found_with(text, "IDE0060"), vec!["b", "level", "seed"]);
    }

    #[test]
    fn obsolete_members_and_types() {
        let text = "using System;\n\
                    [Obsolete(\"Use New\")] class Old { }\n\
                    class C {\n\
                      [Obsolete] public static void Gone() { }\n\
                      [Obsolete(\"Never\", true)] public static void Banned() { }\n\
                      public static void Fine() { }\n\
                      void M() { Gone(); Banned(); Fine(); var o = new Old(); }\n\
                      [Obsolete] void AlsoOld() { Gone(); }\n\
                    }\n";
        assert_eq!(found_with(text, "CS0612"), vec!["Gone"]);
        assert_eq!(found_with(text, "CS0619"), vec!["Banned"]);
        assert_eq!(found_with(text, "CS0618"), vec!["Old"]);
        let semantic =
            super::super::super::tests::compile(&[("C.cs", text)], false).expect("compiled");
        let all = semantic
            .analyzer_diagnostics(std::path::Path::new("/p/C.cs"), None)
            .expect("analyzed");
        let old = all
            .iter()
            .find(|found| found.id == "CS0618")
            .expect("CS0618");
        assert!(old.deprecated);
        assert_eq!(old.message, "'Old' is obsolete: 'Use New'");
        let gone = all
            .iter()
            .find(|found| found.id == "CS0612")
            .expect("CS0612");
        assert_eq!(gone.message, "'C.Gone()' is obsolete");
    }

    /// The name in a property pattern is a read of the member: `p is { a:
    /// 1 }` reads `a`. It was passed over as the name of an argument is,
    /// and a field read only so was reported unused — and offered for
    /// removal.
    #[test]
    fn a_member_read_in_a_property_pattern_is_used() {
        let text = "class P {\n\
                      private int a; private int b; private string c;\n\
                      private int E { get; }\n\
                      private int gone;\n\
                      public P(int x, string s) { a = x; b = x; c = s; E = x; }\n\
                      static bool One(P p) => p is { a: 1 };\n\
                      public bool Two(P p) => One(p) && p switch { { b: > 3 } => true, _ => false };\n\
                      public bool Three(P p) => p is { c: \"x\" or \"y\" } or { E: 3 };\n\
                      public void Call(int a) { Take(a: a); }\n\
                      static void Take(int a) { System.Console.WriteLine(a); }\n\
                    }\n";
        assert_eq!(found_with(text, "IDE0051"), vec!["gone"]);
        assert!(found_with(text, "IDE0052").is_empty());
    }

    /// A field handed out by reference may be written by whoever holds the
    /// reference: `ref int r = ref count; r = 3;`. Made `readonly` it would
    /// not compile (CS0192).
    #[test]
    fn a_field_handed_out_by_reference_cannot_be_readonly() {
        let text = "class C {\n\
                      private int count = 1;\n\
                      private int slot = 2;\n\
                      private int fixedOne = 3;\n\
                      public int Bump() { ref int r = ref count; r = 3; return r; }\n\
                      public ref int Slot() => ref slot;\n\
                      public int Read() => fixedOne;\n\
                    }\n";
        assert_eq!(found_with(text, "IDE0044"), vec!["fixedOne"]);
    }

    /// A member called or written on a copy would not do what it does on the
    /// field, or not compile: a `readonly` tuple, struct or type parameter
    /// that may be one (CS1648 and a counter that stays 0).
    #[test]
    fn a_field_of_a_value_type_a_member_changes_cannot_be_readonly() {
        let none = |code: &str| {
            let text = format!(
                "interface IInc {{ void Inc(); int V {{ get; }} }}\n\
                 struct MS : IInc {{ int v; public void Inc() {{ v++; }} public int V => v; }}\n{code}"
            );
            assert!(
                found_with(&text, "IDE0044").is_empty(),
                "{:?} in\n{code}",
                found_with(&text, "IDE0044")
            );
        };
        none(
            "class Y { private (int, int) t; public Y() { t = (1, 2); } public void G() { t.Item1 = 5; } }",
        );
        none(
            "class Y { private (int a, int b) t; public Y() { t = (1, 2); } public void G() { t.a = 5; } }",
        );
        none(
            "class Y<T> where T : struct, IInc { private T t; public Y() { t = default; } public int G() { t.Inc(); t.Inc(); return t.V; } }",
        );
        none(
            "class Y<T> where T : IInc { private T t; public Y(T x) { t = x; } public int G() { t.Inc(); t.Inc(); return t.V; } }",
        );
        none(
            "class Y { private MS m; public Y() { m = new MS(); } public int G() { m.Inc(); return m.V; } }",
        );
        none(
            "struct W<A> { public int n; public void Bump() { n++; } } class Y { private W<int> w; public Y() { w = new W<int>(); } public int G() { w.Bump(); return w.n; } }",
        );
        none(
            "class Y<T> { private T t; public Y(T x) { t = x; } public int G() { return this.t.GetHashCode(); } }",
        );
    }

    /// What is only copied, or a reference, or changed where the object is
    /// made, is the same `readonly`.
    #[test]
    fn a_field_of_a_value_type_that_is_only_copied_can_be_readonly() {
        let all = |code: &str, names: &[&str]| {
            let text = format!(
                "interface IInc {{ void Inc(); int V {{ get; }} }}\n\
                 struct MS : IInc {{ int v; public void Inc() {{ v++; }} public int V => v; }}\n\
                 class Base : IInc {{ int v; public void Inc() {{ v++; }} public int V => v; }}\n{code}"
            );
            assert_eq!(found_with(&text, "IDE0044"), names, "in\n{code}");
        };
        all(
            "class Y { private (int, int) t; public Y() { t = (1, 2); } public (int, int) G() { return t; } }",
            &["t"],
        );
        all(
            "class Y { private (int, int) t; public Y() { t = (1, 2); } static int F((int, int) p) => p.Item1; public int G() => F(t); }",
            &["t"],
        );
        all(
            "class Y<T> { private T t; public Y(T x) { t = x; } public T G() => t; }",
            &["t"],
        );
        all(
            "class Y<T> where T : class, IInc { private T t; public Y(T x) { t = x; } public int G() { t.Inc(); return t.V; } }",
            &["t"],
        );
        all(
            "class Y<T> where T : Base { private T t; public Y(T x) { t = x; } public int G() { t.Inc(); return t.V; } }",
            &["t"],
        );
        all(
            "class Y { private int? n; public Y() { n = 3; } public int G() { return n.Value + 1; } }",
            &["n"],
        );
        all(
            "class Y { private MS[] arr; public Y() { arr = new MS[2]; } public int G() { arr[0].Inc(); return arr[0].V; } }",
            &["arr"],
        );
        all(
            "class Y { private MS m; public Y() { m = new MS(); m.Inc(); } public int G() { return Take(m); } static int Take(MS x) => x.V; }",
            &["m"],
        );
        all(
            "class Y { private (int, int) t; public Y() { t = (1, 2); t.Item1 = 7; } public (int, int) G() { return this.t; } }",
            &["t"],
        );
    }

    /// A construct of the language runs a member by its name in the type of
    /// what it is given: removing the member breaks the build.
    #[test]
    fn a_member_a_language_construct_runs_is_used() {
        let code = "using System; using System.Collections; using System.Threading.Tasks; using System.Runtime.CompilerServices;\n\
            class A { private void Deconstruct(out int a, out int b) { a = 1; b = 2; } public int G() { var (x, y) = this; return x + y; } }\n\
            class B { private void Deconstruct(out int a, out int b) { a = 1; b = 2; } public int G() { int x, y; (x, y) = this; return x + y; } }\n\
            class C { private void Deconstruct(out int a, out int b) { a = 1; b = 2; } public int G() => this is (1, var q) ? q : 0; }\n\
            class D : IEnumerable { private void Add(int x) { } public IEnumerator GetEnumerator() => null; public static D Make() => new D { 1, 2 }; }\n\
            class E { private Aw GetAwaiter() => new Aw(); public async Task G() { await this; } public struct Aw : INotifyCompletion { public bool IsCompleted => true; public void GetResult() { } public void OnCompleted(Action a) { } } }\n\
            class F { private F Select(Func<int, int> f) => this; public F G() => from x in this select x; }\n\
            class H { private H Where(Func<int, bool> f) => this; private H Select(Func<int, int> f) => this; public H G() => from x in this where x > 0 select x; }\n\
            class I { public int Length => 3; private int this[int i] => i; public int G() => this[^1]; }\n\
            class J { public int Length => 3; private int Slice(int a, int b) => 0; public int this[int i] => i; public int G() => this[1..2]; }\n\
            class K { private int Length => 3; public int this[int i] => i; public int G() => this[^1]; }\n\
            class L { private int Count => 3; public int this[int i] => i; public int G() => this[^1]; }\n\
            class M { public int Count => 3; private int this[int i] => i; public int G() => this is [1, ..] ? 1 : 0; }\n\
            class N { private int this[int i] { set { } } public static N Make() => new N { [1] = 2 }; }\n\
            ref struct O { private void Dispose() { } public static void G() { using (var u = new O()) { } } }\n";
        assert!(
            found_with(code, "IDE0051").is_empty(),
            "{:?}",
            found_with(code, "IDE0051")
        );
    }

    /// The same names where no construct reaches them are as unused as any
    /// other.
    #[test]
    fn a_member_with_a_pattern_name_that_no_construct_runs_is_unused() {
        let code = "using System.Collections;\n\
            class A { private void Deconstruct(out int a) { a = 0; } }\n\
            class B : IEnumerable { private void Add(int x) { } public IEnumerator GetEnumerator() => null; }\n\
            class C { private int Count => 3; private int Length => 4; private int Slice(int a, int b) => 0; }\n\
            class E { private System.Threading.Tasks.Task GetAwaiter() => null; }\n";
        assert_eq!(
            found_with(code, "IDE0051"),
            vec![
                "Deconstruct",
                "Add",
                "Count",
                "Length",
                "Slice",
                "GetAwaiter"
            ]
        );
    }
}
