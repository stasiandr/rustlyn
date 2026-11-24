//! Convert to full property, use auto property: `int X { get; set; }` and
//! the same property with a field behind it, each into the other.
//!
//! Roslyn's `ConvertAutoPropertyToFullProperty` refactoring and the fix for
//! IDE0032. A full property gets a private field named the way the type's
//! other fields are named, the auto-property's initializer, and accessors
//! that read and write it — with the accessors' own modifiers kept. A
//! getter-only property becomes a `readonly` field's, and is not converted
//! when something writes to it, since a full property without a setter
//! cannot be written.
//!
//! The other way, a property whose getter only returns a private field of
//! the same type (and whose setter, if any, only assigns it) becomes an
//! auto-property; the field goes, and its other uses become uses of the
//! property. Not when something passes the field by `ref`, or writes it
//! outside a constructor when the property has no setter.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    camel_case, declaration_lines, fresh_name, is_type_declaration, is_written, line_start,
    skip_parentheses, statements_of,
};
use super::super::{ActionKind, CodeAction, Context};
use super::{across_files, references_at};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let Some(property) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| node.kind() == SyntaxKind::PropertyDeclaration)
    else {
        return;
    };
    let body_start = property
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::AccessorList | SyntaxKind::ArrowExpressionClause
            )
        })
        .map_or(property.span().end(), |body| body.span().start());
    if context.trimmed_span().start() > body_start {
        return;
    }
    let Some(ty) = property
        .parent()
        .cloned()
        .filter(|ty| is_type_declaration(ty.kind()))
    else {
        return;
    };
    if ty.kind() == SyntaxKind::InterfaceDeclaration
        || property.child_tokens().any(|token| {
            matches!(
                token.kind(),
                SyntaxKind::AbstractKeyword
                    | SyntaxKind::ExternKeyword
                    | SyntaxKind::PartialKeyword
            )
        })
    {
        return;
    }
    if let Some(edits) = to_full(context, &ty, &property) {
        found.push(context.local(
            "Convert to full property",
            ActionKind::Refactor,
            None,
            edits,
        ));
    }
    if let Some(action) = to_auto(context, &ty, &property) {
        found.push(action);
    }
}

/// The accessors of a property, each with its modifiers' text.
fn accessors(property: &SyntaxNode) -> Vec<(SyntaxNode, String)> {
    property
        .child_of_kind(SyntaxKind::AccessorList)
        .map(|list| {
            list.children()
                .map(|accessor| {
                    let modifiers: Vec<String> = accessor
                        .child_tokens()
                        .filter(|token| token.kind().is_reserved_keyword())
                        .map(|token| token.text().to_string())
                        .collect();
                    let modifiers = if modifiers.is_empty() {
                        String::new()
                    } else {
                        format!("{} ", modifiers.join(" "))
                    };
                    (accessor, modifiers)
                })
                .collect()
        })
        .unwrap_or_default()
}

fn to_full(
    context: &mut Context<'_, '_>,
    ty: &SyntaxNode,
    property: &SyntaxNode,
) -> Option<Vec<TextEdit>> {
    let list = property.child_of_kind(SyntaxKind::AccessorList)?;
    let accessors = accessors(property);
    if accessors.iter().any(|(accessor, _)| {
        accessor.child_of_kind(SyntaxKind::Block).is_some()
            || accessor
                .child_of_kind(SyntaxKind::ArrowExpressionClause)
                .is_some()
    }) || !accessors
        .iter()
        .any(|(accessor, _)| accessor.kind() == SyntaxKind::GetAccessorDeclaration)
    {
        return None;
    }
    let name = property.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let writable = accessors.iter().any(|(accessor, _)| {
        matches!(
            accessor.kind(),
            SyntaxKind::SetAccessorDeclaration | SyntaxKind::InitAccessorDeclaration
        )
    });
    if !writable {
        // A getter-only full property cannot be assigned, where the
        // auto-property could be in a constructor.
        let root = context.view.syntax_root().clone();
        let written =
            references_at(context, name.span().start())
                .into_iter()
                .any(|(path, span)| {
                    path == context.path
                        && root
                            .find_token(span.start())
                            .is_some_and(|token| is_written(token.parent()))
                });
        if written {
            return None;
        }
    }
    let underscore = ty.children().any(|member| {
        member.kind() == SyntaxKind::FieldDeclaration
            && member.descendant_tokens().any(|token| {
                token.kind() == SyntaxKind::IdentifierToken && token.value_text().starts_with('_')
            })
    });
    let base = if underscore {
        format!("_{}", camel_case(name.value_text()).trim_start_matches('@'))
    } else {
        camel_case(name.value_text())
    };
    let field = fresh_name(&base, &context.view.names_near(property));
    let written_type = property
        .children()
        .find(|child| child.kind().is_type_node())?
        .text();
    let is_static = property
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some();
    let initializer = property
        .child_of_kind(SyntaxKind::EqualsValueClause)
        .map(|clause| format!(" {}", clause.text()))
        .unwrap_or_default();
    let declaration = format!(
        "private {}{}{written_type} {field}{initializer};",
        if is_static { "static " } else { "" },
        if writable { "" } else { "readonly " },
    );
    let parts: Vec<String> = accessors
        .iter()
        .map(|(accessor, modifiers)| match accessor.kind() {
            SyntaxKind::GetAccessorDeclaration => format!("{modifiers}get => {field};"),
            SyntaxKind::InitAccessorDeclaration => format!("{modifiers}init => {field} = value;"),
            _ => format!("{modifiers}set => {field} = value;"),
        })
        .collect();
    let newline = context.newline();
    let indent = context.indentation_at(property.span().start());
    let at = property.full_span().start();
    let insert = if line_start(&context.text, at) == at {
        TextEdit::insert(at, format!("{indent}{declaration}{newline}{newline}"))
    } else {
        TextEdit::insert(
            property.span().start(),
            format!("{declaration}{newline}{newline}{indent}"),
        )
    };
    Some(vec![
        insert,
        TextEdit::new(
            TextSpan::from_bounds(list.span().start(), property.span().end()),
            format!("{{ {} }}", parts.join(" ")),
        ),
    ])
}

/// The expression an accessor or an arrow gives back, or the value its one
/// assignment stores: `x` of `get { return x; }`, `x` of `set => x =
/// value;` — with the assignment's value, which must be `value`.
fn accessor_expression(accessor: &SyntaxNode) -> Option<SyntaxNode> {
    if let Some(arrow) = accessor.child_of_kind(SyntaxKind::ArrowExpressionClause) {
        return arrow.children().next();
    }
    let body = accessor.child_of_kind(SyntaxKind::Block)?;
    let statements = statements_of(&body);
    let [statement] = statements.as_slice() else {
        return None;
    };
    match statement.kind() {
        SyntaxKind::ReturnStatement | SyntaxKind::ExpressionStatement => statement
            .children()
            .find(|child| child.kind().is_expression()),
        _ => None,
    }
}

/// `x` or `this.x`: the name of the field it reads.
fn field_name_of(expression: &SyntaxNode) -> Option<SyntaxNode> {
    let expression = skip_parentheses(expression);
    match expression.kind() {
        SyntaxKind::IdentifierName => Some(expression),
        SyntaxKind::SimpleMemberAccessExpression => {
            let mut parts = expression.children();
            let receiver = parts.next()?;
            let name = parts.next()?;
            (receiver.kind() == SyntaxKind::ThisExpression
                && name.kind() == SyntaxKind::IdentifierName)
                .then_some(name)
        }
        _ => None,
    }
}

fn to_auto(
    context: &mut Context<'_, '_>,
    ty: &SyntaxNode,
    property: &SyntaxNode,
) -> Option<CodeAction> {
    let name = property.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let accessors = accessors(property);
    let (getter, setter) =
        if let Some(arrow) = property.child_of_kind(SyntaxKind::ArrowExpressionClause) {
            (arrow.children().next()?, None)
        } else {
            let mut getter = None;
            let mut setter = None;
            for (accessor, modifiers) in &accessors {
                match accessor.kind() {
                    SyntaxKind::GetAccessorDeclaration if modifiers.is_empty() => {
                        getter = Some(accessor_expression(accessor)?);
                    }
                    SyntaxKind::SetAccessorDeclaration | SyntaxKind::InitAccessorDeclaration => {
                        let assignment = accessor_expression(accessor)?;
                        if assignment.kind() != SyntaxKind::SimpleAssignmentExpression {
                            return None;
                        }
                        let mut sides = assignment.children();
                        let target = sides.next()?;
                        if sides.next()?.text() != "value" {
                            return None;
                        }
                        setter = Some((target, accessor.kind(), modifiers.clone()));
                    }
                    _ => return None,
                }
            }
            (getter?, setter)
        };
    let read = field_name_of(&getter)?;
    if let Some((target, _, _)) = &setter
        && field_name_of(target)?.text() != read.text()
    {
        return None;
    }
    let token = read.first_token()?;
    let Resolved::Symbol(field_symbol) = context.view.resolve(&token)? else {
        return None;
    };
    let property_symbol = context.view.declared(property)?;
    if context.view.symbol_type(field_symbol) != context.view.symbol_type(property_symbol) {
        return None;
    }
    // The field: declared alone, privately, in this type.
    let field = ty.children().find(|member| {
        member.kind() == SyntaxKind::FieldDeclaration
            && member
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                .any(|declarator| context.view.declared(&declarator) == Some(field_symbol))
    })?;
    let declarators: Vec<SyntaxNode> = field
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let [declarator] = declarators.as_slice() else {
        return None;
    };
    if field.child_tokens().any(|token| {
        matches!(
            token.kind(),
            SyntaxKind::PublicKeyword
                | SyntaxKind::InternalKeyword
                | SyntaxKind::ProtectedKeyword
                | SyntaxKind::VolatileKeyword
                | SyntaxKind::ConstKeyword
        )
    }) || field.child_of_kind(SyntaxKind::AttributeList).is_some()
    {
        return None;
    }
    let field_static = field
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some();
    let property_static = property
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some();
    let readonly = field
        .child_token_of_kind(SyntaxKind::ReadOnlyKeyword)
        .is_some();
    if field_static != property_static || (readonly && setter.is_some()) {
        return None;
    }
    let field_token = declarator.child_token_of_kind(SyntaxKind::IdentifierToken)?;

    // Every other use of the field becomes the property.
    let constructors: Vec<TextSpan> = ty
        .children()
        .filter(|member| member.kind() == SyntaxKind::ConstructorDeclaration)
        .map(|member| member.span())
        .collect();
    let root = context.view.syntax_root().clone();
    let mut edits = Vec::new();
    for (path, span) in references_at(context, field_token.span().start()) {
        if path == context.path
            && (span == field_token.span() || property.span().contains_span(span))
        {
            continue;
        }
        if path == context.path
            && let Some(token) = root.find_token(span.start())
        {
            let node = token.parent().clone();
            let passed = node.parent().is_some_and(|parent| {
                parent.kind() == SyntaxKind::Argument && parent.child_tokens().next().is_some()
            });
            if passed {
                return None;
            }
            if is_written(&node)
                && setter.is_none()
                && !constructors.iter().any(|ctor| ctor.contains_span(span))
            {
                return None;
            }
        } else if path != context.path {
            // A private field is only used in its type's own files; one
            // of those being changed elsewhere is beyond checking here.
            return None;
        }
        edits.push((path, TextEdit::new(span, name.value_text().to_string())));
    }

    let initializer = declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)
        .map(|clause| format!(" {};", clause.text()))
        .unwrap_or_default();
    let mut parts = vec!["get;".to_string()];
    if let Some((_, kind, modifiers)) = &setter {
        let keyword = if *kind == SyntaxKind::InitAccessorDeclaration {
            "init"
        } else {
            "set"
        };
        parts.push(format!("{modifiers}{keyword};"));
    }
    let start = name.span().end();
    edits.push((
        context.path.clone(),
        TextEdit::new(
            TextSpan::from_bounds(start, property.span().end()),
            format!(" {{ {} }}{initializer}", parts.join(" ")),
        ),
    ));
    edits.push((
        context.path.clone(),
        TextEdit::delete(declaration_lines(&context.text, field.span())),
    ));
    Some(across_files(
        "Use auto property",
        ActionKind::Refactor,
        edits,
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn an_auto_property_gets_a_field() {
        let source = "class C\n{\n    public int $$Count { get; private set; } = 3;\n}\n";
        assert_eq!(
            apply(source, "Convert to full property"),
            "class C\n{\n    private int count = 3;\n\n    public int Count { get => count; private set => count = value; }\n}\n"
        );
    }

    #[test]
    fn a_getter_only_property_written_in_a_constructor_stays() {
        refuses(
            "class C\n{\n    public int $$Count { get; }\n    public C() { Count = 1; }\n}\n",
            "Convert to full property",
        );
        let unwritten = "class C\n{\n    int _other;\n    public int $$Count { get; }\n}\n";
        assert_eq!(
            apply(unwritten, "Convert to full property"),
            "class C\n{\n    int _other;\n    private readonly int _count;\n\n    public int Count { get => _count; }\n}\n"
        );
    }

    #[test]
    fn a_property_over_a_field_becomes_automatic() {
        let source = "class C\n{\n    private string name = \"x\";\n\n    public string $$Name\n    {\n        get { return name; }\n        set { name = value; }\n    }\n\n    void Reset() { name = null; }\n}\n";
        assert_eq!(
            apply(source, "Use auto property"),
            "class C\n{\n    public string Name { get; set; } = \"x\";\n\n    void Reset() { Name = null; }\n}\n"
        );
        refuses(
            "class C\n{\n    private int n;\n    public int $$N => n;\n    void Bump() { n++; }\n}\n",
            "Use auto property",
        );
    }
}
