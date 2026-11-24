//! Use primary constructor, and convert to record: a type whose one
//! constructor only stores its parameters, written the C# 12 and C# 9 way.
//!
//! * "Use primary constructor" (IDE0290): the constructor's parameters go
//!   after the type's name, the constructor goes, and each field or
//!   property it assigned is initialized from its parameter instead; a
//!   `: base(...)` call becomes the base type's arguments in the base
//!   list. "Use primary constructor (and remove fields)" also removes the
//!   private fields that only held a parameter, every use of one reading
//!   the parameter.
//! * "Convert to record": a class or struct whose constructor assigns each
//!   of its public `get;` or `get; init;` auto-properties from a parameter
//!   becomes a positional `record` (or `record struct`), those properties
//!   its parameters.
//!
//! Only offered with the cursor on the type's name, for a type with one
//! instance constructor that has nothing but those assignments in it — no
//! comments, attributes or `: this(...)` — and is as accessible as the
//! type, since a primary constructor is.

use std::collections::HashMap;

use rustlyn_semantics::{Modifiers, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{has_comments, is_written, skip_parentheses, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use super::members::{has_modifier, remove_members, type_named_at_cursor};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(declaration) = type_named_at_cursor(context) else {
        return;
    };
    if !matches!(
        declaration.kind(),
        SyntaxKind::ClassDeclaration | SyntaxKind::StructDeclaration
    ) || declaration
        .child_of_kind(SyntaxKind::ParameterList)
        .is_some()
        || has_modifier(&declaration, SyntaxKind::StaticKeyword)
        || has_modifier(&declaration, SyntaxKind::PartialKeyword)
    {
        return;
    }
    let Some(shape) = constructor_shape(context, &declaration) else {
        return;
    };
    if let Some(edits) = primary(context, &declaration, &shape, false) {
        found.push(context.local("Use primary constructor", ActionKind::Refactor, None, edits));
    }
    if let Some(edits) = primary(context, &declaration, &shape, true) {
        found.push(context.local(
            "Use primary constructor (and remove fields)",
            ActionKind::Refactor,
            None,
            edits,
        ));
    }
    if let Some(edits) = record(context, &declaration, &shape) {
        found.push(context.local("Convert to record", ActionKind::Refactor, None, edits));
    }
}

/// The one constructor, and what it assigns: each member's declaration by
/// the parameter that goes into it.
struct Shape {
    constructor: SyntaxNode,
    parameters: Vec<SyntaxNode>,
    /// `(member declaration, member name, parameter name)`, in the order of
    /// the assignments.
    assigned: Vec<(SyntaxNode, String, String)>,
    /// The arguments of `: base(...)`.
    base_arguments: Option<String>,
}

fn constructor_shape(context: &mut Context<'_, '_>, declaration: &SyntaxNode) -> Option<Shape> {
    let constructors: Vec<SyntaxNode> = declaration
        .children()
        .filter(|child| {
            child.kind() == SyntaxKind::ConstructorDeclaration
                && !has_modifier(child, SyntaxKind::StaticKeyword)
        })
        .collect();
    let [constructor] = constructors.as_slice() else {
        return None;
    };
    if has_comments(constructor)
        || constructor
            .child_of_kind(SyntaxKind::AttributeList)
            .is_some()
        || constructor
            .child_of_kind(SyntaxKind::ThisConstructorInitializer)
            .is_some()
    {
        return None;
    }
    // As accessible as the type.
    let public_type = has_modifier(declaration, SyntaxKind::PublicKeyword);
    let public_constructor = has_modifier(constructor, SyntaxKind::PublicKeyword);
    let internal_constructor = has_modifier(constructor, SyntaxKind::InternalKeyword);
    if !(public_constructor || (!public_type && internal_constructor)) {
        return None;
    }
    let parameters: Vec<SyntaxNode> = constructor
        .child_of_kind(SyntaxKind::ParameterList)?
        .children()
        .filter(|child| child.kind() == SyntaxKind::Parameter)
        .collect();
    if parameters.is_empty()
        || parameters.iter().any(|parameter| {
            parameter.child_tokens().any(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::RefKeyword | SyntaxKind::OutKeyword | SyntaxKind::InKeyword
                )
            })
        })
    {
        return None;
    }
    let names: Vec<String> = parameters
        .iter()
        .filter_map(|parameter| {
            parameter
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
        })
        .collect();
    let statements = match constructor.child_of_kind(SyntaxKind::Block) {
        Some(block) => statements_of(&block),
        None => {
            let arrow = constructor.child_of_kind(SyntaxKind::ArrowExpressionClause)?;
            vec![arrow]
        }
    };
    let type_symbol = context.view.declared(declaration)?;
    let mut assigned: Vec<(SyntaxNode, String, String)> = Vec::new();
    for statement in &statements {
        let expression = match statement.kind() {
            SyntaxKind::ExpressionStatement | SyntaxKind::ArrowExpressionClause => {
                statement.children().next()?
            }
            _ => return None,
        };
        if expression.kind() != SyntaxKind::SimpleAssignmentExpression {
            return None;
        }
        let mut sides = expression.children();
        let (target, value) = (sides.next()?, skip_parentheses(&sides.next()?));
        let parameter = value.text();
        if value.kind() != SyntaxKind::IdentifierName || !names.contains(&parameter) {
            return None;
        }
        let member_name = match target.kind() {
            SyntaxKind::IdentifierName => target.clone(),
            SyntaxKind::SimpleMemberAccessExpression
                if target
                    .children()
                    .next()
                    .is_some_and(|this| this.kind() == SyntaxKind::ThisExpression) =>
            {
                target.children().nth(1)?
            }
            _ => return None,
        };
        let token = member_name.child_token_of_kind(SyntaxKind::IdentifierToken)?;
        let Some(Resolved::Symbol(member)) = context.view.resolve(&token) else {
            return None;
        };
        let symbols = context.view.compiled().symbols();
        let found = symbols.get(member);
        if found.container != Some(type_symbol)
            || found.modifiers.contains(Modifiers::STATIC)
            || !matches!(found.kind, SymbolKind::Field | SymbolKind::Property)
            || assigned.iter().any(|(_, name, _)| *name == found.name)
        {
            return None;
        }
        // The member's declaration, in this declaration, with no value of
        // its own and one variable.
        let member_declaration = declaration.children().find(|child| match child.kind() {
            SyntaxKind::FieldDeclaration => {
                child
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                    .count()
                    == 1
                    && child.descendants().any(|node| {
                        node.kind() == SyntaxKind::VariableDeclarator
                            && context.view.declared(&node) == Some(member)
                    })
            }
            SyntaxKind::PropertyDeclaration => context.view.declared(child) == Some(member),
            _ => false,
        })?;
        if member_declaration
            .descendants()
            .any(|node| node.kind() == SyntaxKind::EqualsValueClause)
            || (member_declaration.kind() == SyntaxKind::PropertyDeclaration
                && !is_auto_property(&member_declaration))
        {
            return None;
        }
        assigned.push((member_declaration, found.name.clone(), parameter));
    }
    let base_arguments = constructor
        .child_of_kind(SyntaxKind::BaseConstructorInitializer)
        .and_then(|initializer| initializer.child_of_kind(SyntaxKind::ArgumentList))
        .map(|list| list.text());
    Some(Shape {
        constructor: constructor.clone(),
        parameters,
        assigned,
        base_arguments,
    })
}

/// Whether a property's accessors are all `get;`, `set;` or `init;`.
fn is_auto_property(property: &SyntaxNode) -> bool {
    property
        .child_of_kind(SyntaxKind::AccessorList)
        .is_some_and(|list| {
            list.children().all(|accessor| {
                accessor.child_of_kind(SyntaxKind::Block).is_none()
                    && accessor
                        .child_of_kind(SyntaxKind::ArrowExpressionClause)
                        .is_none()
            })
        })
}

/// Where a primary constructor's parameter list goes: after the name and
/// type parameters.
fn header_end(declaration: &SyntaxNode) -> Option<u32> {
    declaration
        .child_of_kind(SyntaxKind::TypeParameterList)
        .map(|list| list.span().end())
        .or_else(|| {
            declaration
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.span().end())
        })
}

fn primary(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    shape: &Shape,
    remove_fields: bool,
) -> Option<Vec<TextEdit>> {
    let parameter_list = shape
        .constructor
        .child_of_kind(SyntaxKind::ParameterList)?
        .text();
    let mut edits = vec![TextEdit::insert(header_end(declaration)?, parameter_list)];
    if let Some(arguments) = &shape.base_arguments {
        let base = declaration
            .child_of_kind(SyntaxKind::BaseList)?
            .children()
            .find(|child| child.kind() == SyntaxKind::SimpleBaseType)?;
        edits.push(TextEdit::insert(base.span().end(), arguments.clone()));
    }
    // The fields that go: private, and written nowhere but the constructor.
    let mut removed: Vec<SyntaxNode> = vec![shape.constructor.clone()];
    let mut renamed: HashMap<String, String> = HashMap::new();
    for (member, name, parameter) in &shape.assigned {
        let removable = remove_fields
            && member.kind() == SyntaxKind::FieldDeclaration
            && !has_modifier(member, SyntaxKind::PublicKeyword)
            && !has_modifier(member, SyntaxKind::ProtectedKeyword)
            && !has_modifier(member, SyntaxKind::InternalKeyword)
            && !declaration.descendants().any(|node| {
                node.kind() == SyntaxKind::IdentifierName
                    && node.text() == *name
                    && !shape.constructor.span().contains(node.span().start())
                    && is_written(&node)
            });
        if removable {
            removed.push(member.clone());
            renamed.insert(name.clone(), parameter.clone());
            continue;
        }
        // An initializer from the parameter.
        let at = match member.kind() {
            SyntaxKind::FieldDeclaration => member
                .descendants()
                .find(|node| node.kind() == SyntaxKind::VariableDeclarator)?
                .span()
                .end(),
            _ => member.child_of_kind(SyntaxKind::AccessorList)?.span().end(),
        };
        let text = if member.kind() == SyntaxKind::FieldDeclaration {
            format!(" = {parameter}")
        } else {
            format!(" = {parameter};")
        };
        edits.push(TextEdit::insert(at, text));
    }
    if remove_fields && renamed.is_empty() {
        return None;
    }
    if !renamed.is_empty() {
        // A parameter named like something else in the type would change
        // what the name means.
        for node in declaration.descendants() {
            if removed
                .iter()
                .any(|gone| gone.span().contains(node.span().start()))
            {
                continue;
            }
            let name = node.text();
            let Some(parameter) = renamed.get(&name) else {
                continue;
            };
            if node.kind() != SyntaxKind::IdentifierName {
                continue;
            }
            let parent = node.parent()?;
            if parent.kind() == SyntaxKind::SimpleMemberAccessExpression
                && parent.children().nth(1).as_ref() == Some(&node)
            {
                // `this._name`; `other._name` is another instance's.
                let receiver = parent.children().next()?;
                if receiver.kind() != SyntaxKind::ThisExpression {
                    continue;
                }
                edits.push(TextEdit::new(parent.span(), parameter.clone()));
            } else {
                edits.push(TextEdit::new(node.span(), parameter.clone()));
            }
        }
    }
    edits.extend(remove_members(&context.text, &removed));
    // Edits inside what is removed go with it.
    let removals: Vec<TextSpan> = edits
        .iter()
        .filter(|edit| edit.text.is_empty())
        .map(|edit| edit.span)
        .collect();
    edits.retain(|edit| {
        edit.text.is_empty()
            || !removals
                .iter()
                .any(|span| span.start() <= edit.span.start() && edit.span.end() <= span.end())
    });
    Some(edits)
}

fn record(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    shape: &Shape,
) -> Option<Vec<TextEdit>> {
    if declaration.child_of_kind(SyntaxKind::BaseList).is_some() || shape.base_arguments.is_some() {
        return None;
    }
    // Every parameter goes into a public `get;`/`init;` auto-property, in
    // order, and nothing else is assigned.
    if shape.assigned.len() != shape.parameters.len() {
        return None;
    }
    let mut positional = Vec::new();
    for (parameter, (member, name, value)) in shape.parameters.iter().zip(&shape.assigned) {
        let parameter_name = parameter.child_token_of_kind(SyntaxKind::IdentifierToken)?;
        if parameter_name.value_text() != value
            || member.kind() != SyntaxKind::PropertyDeclaration
            || !has_modifier(member, SyntaxKind::PublicKeyword)
            || member.child_of_kind(SyntaxKind::AttributeList).is_some()
            || has_comments(member)
        {
            return None;
        }
        let accessors: Vec<SyntaxKind> = member
            .child_of_kind(SyntaxKind::AccessorList)?
            .children()
            .map(|accessor| accessor.kind())
            .collect();
        if !(accessors == [SyntaxKind::GetAccessorDeclaration]
            || accessors
                == [
                    SyntaxKind::GetAccessorDeclaration,
                    SyntaxKind::InitAccessorDeclaration,
                ])
        {
            return None;
        }
        let ty = member
            .children()
            .find(|child| child.kind().is_type_node())?
            .text();
        let default = parameter
            .child_of_kind(SyntaxKind::EqualsValueClause)
            .map(|clause| format!(" {}", clause.text()))
            .unwrap_or_default();
        positional.push(format!("{ty} {name}{default}"));
    }
    let keyword = declaration.child_token_of_kind(match declaration.kind() {
        SyntaxKind::ClassDeclaration => SyntaxKind::ClassKeyword,
        _ => SyntaxKind::StructKeyword,
    })?;
    let written = if declaration.kind() == SyntaxKind::ClassDeclaration {
        "record"
    } else {
        "record struct"
    };
    let mut edits = vec![
        TextEdit::new(keyword.span(), written),
        TextEdit::insert(
            header_end(declaration)?,
            format!("({})", positional.join(", ")),
        ),
    ];
    let mut removed: Vec<SyntaxNode> = vec![shape.constructor.clone()];
    removed.extend(shape.assigned.iter().map(|(member, _, _)| member.clone()));
    let remaining = declaration
        .children()
        .filter(|child| super::super::text::is_member(child.kind()))
        .any(|child| !removed.contains(&child));
    if remaining {
        edits.extend(remove_members(&context.text, &removed));
    } else {
        // Nothing left: `record Point(int X, int Y);`.
        let open = declaration.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
        let close = declaration.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
        let before = declaration
            .descendant_tokens()
            .take_while(|token| token.span().start() < open.span().start())
            .last()?
            .span()
            .end();
        edits.push(TextEdit::new(
            TextSpan::from_bounds(before, close.span().end()),
            ";",
        ));
    }
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    const SERVICE: &str = "class Base { public Base(int id) { } }\n\npublic class $$Service : Base\n{\n    private readonly string _name;\n    public int Size { get; }\n\n    public Service(string name, int size) : base(size)\n    {\n        _name = name;\n        this.Size = size;\n    }\n\n    public string Describe() => _name + this._name;\n}\n";

    #[test]
    fn a_storing_constructor_becomes_a_primary_constructor() {
        assert_eq!(
            apply(SERVICE, "Use primary constructor"),
            "class Base { public Base(int id) { } }\n\npublic class Service(string name, int size) : Base(size)\n{\n    private readonly string _name = name;\n    public int Size { get; } = size;\n\n    public string Describe() => _name + this._name;\n}\n"
        );
        assert_eq!(
            apply(SERVICE, "Use primary constructor (and remove fields)"),
            "class Base { public Base(int id) { } }\n\npublic class Service(string name, int size) : Base(size)\n{\n    public int Size { get; } = size;\n\n    public string Describe() => name + name;\n}\n"
        );
    }

    #[test]
    fn a_constructor_that_does_more_stays() {
        refuses(
            "class $$C\n{\n    int x;\n    public C(int x)\n    {\n        this.x = x;\n        System.Console.WriteLine(x);\n    }\n}\n",
            "Use primary constructor",
        );
        refuses(
            "public class $$C\n{\n    int x;\n    private C(int x) { this.x = x; }\n}\n",
            "Use primary constructor",
        );
    }

    #[test]
    fn properties_set_by_the_constructor_make_a_record() {
        let source = "public class $$Point\n{\n    public int X { get; }\n    public int Y { get; init; }\n\n    public Point(int X, int Y = 0)\n    {\n        this.X = X;\n        this.Y = Y;\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to record"),
            "public record Point(int X, int Y = 0);\n"
        );
        let source = "struct $$Size\n{\n    public int Width { get; }\n\n    public Size(int Width) => this.Width = Width;\n\n    public int Twice() => Width * 2;\n}\n";
        assert_eq!(
            apply(source, "Convert to record"),
            "record struct Size(int Width)\n{\n    public int Twice() => Width * 2;\n}\n"
        );
    }
}
