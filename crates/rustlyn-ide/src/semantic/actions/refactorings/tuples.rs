//! Anonymous types and tuples made into each other, and into types with
//! names.
//!
//! * "Convert to tuple" (Roslyn's `ConvertAnonymousTypeToTuple`): `new {
//!   A = 1, B = x }` becomes `(A: 1, B: x)` — every anonymous creation of
//!   the same shape in the member, since they are one type and must stay
//!   one. Reading `v.A` reads the tuple's element the same way.
//! * "Convert to record" (`ConvertAnonymousTypeToClass`, which writes a
//!   record from C# 9 on): the anonymous type becomes `internal record
//!   NewRecord(int A, string B);` after the type the code is in, and each
//!   creation `new NewRecord(1, x)`.
//! * "Convert to struct" (`ConvertTupleToStruct`), "updating usages in
//!   containing member" or "... in containing type": the tuple type becomes
//!   `internal record struct NewStruct(int A, string B);`, each tuple of it
//!   in that scope `new NewStruct(1, x)`, and each tuple type written for
//!   it `NewStruct`. A record struct deconstructs and compares as the tuple
//!   did. Not offered when a signature outside the scope — a member of the
//!   type others can call, for the member scope any signature — has the
//!   tuple in it, since its callers would still pass tuples.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::text::{fresh_name, is_type_declaration};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let around: Vec<SyntaxNode> = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| !super::super::text::is_member(node.kind()))
        .collect();
    let Some(member) = super::super::text::enclosing_member(&token.parent().clone()) else {
        return;
    };
    if let Some(creation) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::AnonymousObjectCreationExpression)
    {
        anonymous(context, &member, creation, found);
    }
    if let Some(tuple) = around.iter().find(|node| {
        matches!(
            node.kind(),
            SyntaxKind::TupleExpression | SyntaxKind::TupleType
        )
    }) {
        to_struct(context, &member, tuple, found);
    }
}

/// An anonymous creation's members: each name, and its value.
fn anonymous_members(creation: &SyntaxNode) -> Option<Vec<(String, SyntaxNode)>> {
    let initializer = creation.child_of_kind(SyntaxKind::ObjectInitializerExpression)?;
    let mut members = Vec::new();
    for declarator in initializer
        .children()
        .filter(|child| child.kind() == SyntaxKind::AnonymousObjectMemberDeclarator)
    {
        let value = declarator.children().last()?;
        let name = match declarator.child_of_kind(SyntaxKind::NameEquals) {
            Some(equals) => equals
                .child_token_of_kind(SyntaxKind::IdentifierToken)?
                .value_text()
                .to_string(),
            // `new { x.Name }` is named after what it reads.
            None => value
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .last()?
                .value_text()
                .to_string(),
        };
        members.push((name, value));
    }
    Some(members)
}

fn anonymous(
    context: &mut Context<'_, '_>,
    member: &SyntaxNode,
    creation: &SyntaxNode,
    found: &mut Vec<CodeAction>,
) {
    let Some(members) = anonymous_members(creation) else {
        return;
    };
    if members.len() < 2 {
        return;
    }
    let Some(ty) = context.view.expression_type(creation) else {
        return;
    };
    // Every creation of the same anonymous type in the member.
    let creations: Vec<SyntaxNode> = member
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::AnonymousObjectCreationExpression)
        .collect();
    let mut same = Vec::new();
    for other in creations {
        if context.view.expression_type(&other).as_ref() == Some(&ty) {
            same.push(other);
        }
    }
    // Nested creations would need edits inside edits.
    if same.iter().any(|outer| {
        same.iter()
            .any(|inner| inner != outer && outer.span().contains(inner.span().start()))
    }) {
        return;
    }
    let mut tuple_edits = Vec::new();
    let mut record_edits = Vec::new();
    for other in &same {
        let Some(parts) = anonymous_members(other) else {
            return;
        };
        let written: Vec<String> = parts
            .iter()
            .map(|(name, value)| {
                // A name the tuple would infer the same way needs no label.
                if value.text() == *name || value.text().ends_with(&format!(".{name}")) {
                    value.text()
                } else {
                    format!("{name}: {}", value.text())
                }
            })
            .collect();
        tuple_edits.push(TextEdit::new(
            other.span(),
            format!("({})", written.join(", ")),
        ));
        let values: Vec<String> = parts.iter().map(|(_, value)| value.text()).collect();
        record_edits.push((other.clone(), values));
    }
    found.push(context.local("Convert to tuple", ActionKind::Refactor, None, tuple_edits));

    // A record for it, after the outermost type the code is in.
    let Some(outer) = member
        .ancestors()
        .filter(|node| is_type_declaration(node.kind()))
        .last()
    else {
        return;
    };
    let mut parameters = Vec::new();
    for (name, value) in &members {
        let Some(value_type) = context.view.expression_type(value) else {
            return;
        };
        let Some(written) = context.view.display_type(&value_type, &outer) else {
            return;
        };
        parameters.push(format!("{written} {name}"));
    }
    let taken = context.view.names_near(&outer);
    let mut taken_types = taken.clone();
    if let Some(symbol) = context.view.declared(&outer)
        && let Some(container) = context.view.compiled().symbols().get(symbol).container
    {
        let symbols = context.view.compiled().symbols();
        taken_types.extend(
            symbols
                .get(container)
                .members
                .iter()
                .map(|&id| symbols.get(id).name.clone()),
        );
    }
    let name = fresh_name("NewRecord", &taken_types);
    let mut edits: Vec<TextEdit> = record_edits
        .into_iter()
        .map(|(node, values)| {
            TextEdit::new(node.span(), format!("new {name}({})", values.join(", ")))
        })
        .collect();
    let nl = context.newline();
    let indent = context.indentation_at(outer.span().start());
    edits.push(TextEdit::insert(
        outer.span().end(),
        format!(
            "{nl}{nl}{indent}internal record {name}({});",
            parameters.join(", ")
        ),
    ));
    found.push(context.local("Convert to record", ActionKind::Refactor, None, edits));
}

/// Whether `node` is in a member's signature — its type, its parameters —
/// rather than in its body or initializer.
fn in_signature(node: &SyntaxNode) -> bool {
    for ancestor in node.ancestors() {
        match ancestor.kind() {
            SyntaxKind::Block
            | SyntaxKind::ArrowExpressionClause
            | SyntaxKind::AccessorList
            | SyntaxKind::EqualsValueClause => return false,
            kind if super::super::text::is_member(kind) && !is_type_declaration(kind) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

fn to_struct(
    context: &mut Context<'_, '_>,
    member: &SyntaxNode,
    tuple: &SyntaxNode,
    found: &mut Vec<CodeAction>,
) {
    let ty = if tuple.kind() == SyntaxKind::TupleType {
        context.view.model.type_of_syntax(tuple)
    } else {
        match context.view.expression_type(tuple) {
            Some(ty) => ty,
            None => return,
        }
    };
    let Type::Tuple(elements) = &ty else {
        return;
    };
    let Some(outer) = member
        .ancestors()
        .filter(|node| is_type_declaration(node.kind()))
        .last()
    else {
        return;
    };
    let mut parameters = Vec::new();
    for (index, element) in elements.iter().enumerate() {
        let Some(written) = context.view.display_type(&element.ty, &outer) else {
            return;
        };
        let name = element
            .name
            .clone()
            .unwrap_or_else(|| format!("Item{}", index + 1));
        parameters.push(format!("{written} {name}"));
    }
    let mut taken = context.view.names_near(&outer);
    if let Some(symbol) = context.view.declared(&outer)
        && let Some(container) = context.view.compiled().symbols().get(symbol).container
    {
        let symbols = context.view.compiled().symbols();
        taken.extend(
            symbols
                .get(container)
                .members
                .iter()
                .map(|&id| symbols.get(id).name.clone()),
        );
    }
    let name = fresh_name("NewStruct", &taken);
    let containing_type = member.parent().cloned();
    for (scope_name, scope) in [("member", Some(member.clone())), ("type", containing_type)] {
        let Some(scope) = scope else {
            continue;
        };
        let Some(edits) = struct_edits(context, &scope, &ty, &name, scope_name == "member") else {
            continue;
        };
        let mut edits = edits;
        let nl = context.newline();
        let indent = context.indentation_at(outer.span().start());
        edits.push(TextEdit::insert(
            outer.span().end(),
            format!(
                "{nl}{nl}{indent}internal record struct {name}({});",
                parameters.join(", ")
            ),
        ));
        found.push(context.local(
            format!("Convert to struct (updating usages in containing {scope_name})"),
            ActionKind::Refactor,
            None,
            edits,
        ));
    }
}

/// The edits replacing the tuple type `ty` in `scope`, or `None` when a
/// signature callers outside it use has the type.
fn struct_edits(
    context: &mut Context<'_, '_>,
    scope: &SyntaxNode,
    ty: &Type,
    name: &str,
    member_scope: bool,
) -> Option<Vec<TextEdit>> {
    let mut edits = Vec::new();
    let nodes: Vec<SyntaxNode> = scope
        .descendants()
        .filter(|node| {
            matches!(
                node.kind(),
                SyntaxKind::TupleExpression | SyntaxKind::TupleType
            )
        })
        .collect();
    for node in &nodes {
        // The outermost tuple of the type only.
        if nodes.iter().any(|other| {
            other != node
                && other.span().contains(node.span().start())
                && edits
                    .iter()
                    .any(|edit: &TextEdit| edit.span == other.span())
        }) {
            continue;
        }
        if node.kind() == SyntaxKind::TupleType {
            let written = context.view.model.type_of_syntax(node);
            if !same_shape(&written, ty) {
                continue;
            }
            // Another tuple of the same types, named otherwise: its names
            // would be lost.
            if written != *ty && names_of(&written).iter().any(Option::is_some) {
                return None;
            }
            if in_signature(node) {
                let signature_owner = node
                    .ancestors()
                    .find(|ancestor| super::super::text::is_member(ancestor.kind()));
                let callable_outside = signature_owner.as_ref().is_some_and(|owner| {
                    member_scope
                        || [
                            SyntaxKind::PublicKeyword,
                            SyntaxKind::InternalKeyword,
                            SyntaxKind::ProtectedKeyword,
                        ]
                        .iter()
                        .any(|keyword| owner.child_token_of_kind(*keyword).is_some())
                });
                if callable_outside {
                    return None;
                }
            }
            edits.push(TextEdit::new(node.span(), name.to_string()));
        } else {
            if !context
                .view
                .expression_type(node)
                .is_some_and(|found| same_shape(&found, ty))
            {
                continue;
            }
            // `var (a, b) = ...` and `(a, b) = ...` take a tuple apart.
            if node.parent().is_some_and(|parent| {
                parent.kind() == SyntaxKind::SimpleAssignmentExpression
                    && parent.children().next().as_ref() == Some(node)
            }) {
                continue;
            }
            let values: Vec<String> = node
                .children()
                .filter(|child| child.kind() == SyntaxKind::Argument)
                .filter_map(|argument| argument.children().last().map(|value| value.text()))
                .collect();
            edits.push(TextEdit::new(
                node.span(),
                format!("new {name}({})", values.join(", ")),
            ));
        }
    }
    (!edits.is_empty()).then_some(edits)
}

/// Whether two tuple types have the same element types, whatever their
/// names: `(0, 0)` is the `(int X, int Y)` it is converted to.
fn same_shape(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| a.ty == b.ty)
        }
        _ => false,
    }
}

fn names_of(ty: &Type) -> Vec<Option<String>> {
    match ty {
        Type::Tuple(elements) => elements
            .iter()
            .map(|element| element.name.clone())
            .collect(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::support::apply;

    #[test]
    fn anonymous_types_become_tuples_or_records() {
        let source = "class Report\n{\n    int M(string name, int count)\n    {\n        var first = $$new { Name = name, Total = count * 2 };\n        var second = new { Name = \"b\", Total = 1 };\n        return first.Total + second.Total;\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to tuple"),
            "class Report\n{\n    int M(string name, int count)\n    {\n        var first = (Name: name, Total: count * 2);\n        var second = (Name: \"b\", Total: 1);\n        return first.Total + second.Total;\n    }\n}\n"
        );
        assert_eq!(
            apply(source, "Convert to record"),
            "class Report\n{\n    int M(string name, int count)\n    {\n        var first = new NewRecord(name, count * 2);\n        var second = new NewRecord(\"b\", 1);\n        return first.Total + second.Total;\n    }\n}\n\ninternal record NewRecord(string Name, int Total);\n"
        );
    }

    #[test]
    fn a_tuple_becomes_a_record_struct() {
        let source = "class Geometry\n{\n    int M()\n    {\n        (int X, int Y) point = $$(X: 1, Y: 2);\n        var (x, y) = point;\n        return point.X + x;\n    }\n}\n";
        assert_eq!(
            apply(
                source,
                "Convert to struct (updating usages in containing member)"
            ),
            "class Geometry\n{\n    int M()\n    {\n        NewStruct point = new NewStruct(1, 2);\n        var (x, y) = point;\n        return point.X + x;\n    }\n}\n\ninternal record struct NewStruct(int X, int Y);\n"
        );
        let source = "class Geometry\n{\n    public (int X, int Y) Origin() => $$(0, 0);\n}\n";
        let offered = super::super::support::titles(source);
        assert!(
            !offered
                .iter()
                .any(|title| title.starts_with("Convert to struct")),
            "{offered:?}"
        );
    }
}
