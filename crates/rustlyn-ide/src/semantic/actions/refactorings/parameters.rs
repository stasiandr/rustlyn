//! What can be done with a parameter from its declaration: check it for
//! `null`, and keep a constructor's parameter in a field or property.
//!
//! Roslyn's `AddParameterCheck` and `InitializeParameter` providers.
//!
//! * "Add null check" throws `ArgumentNullException` when a parameter of a
//!   reference or nullable type is `null`: `ArgumentNullException
//!   .ThrowIfNull(x);` where the compilation has it (.NET 6 on), an `if`
//!   otherwise. It goes after the checks of the parameters before it.
//! * "Create and assign field" / "Create and assign property" declares a
//!   member for a constructor parameter and assigns it at the end of the
//!   constructor. The field is named the way the type's other private fields
//!   are: `_name` when they start with an underscore, `name` otherwise.
//! * "Initialize field" / "Initialize property" assigns a member that
//!   already exists under the parameter's name, and is not assigned yet.

use rustlyn_semantics::{Modifiers, SpecialType, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::text::{camel_case, is_member, pascal_case, starts_line, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let Some(parameter) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| node.kind() == SyntaxKind::Parameter)
    else {
        return;
    };
    let Some(owner) = parameter.parent().and_then(SyntaxNode::parent).cloned() else {
        return;
    };
    if !matches!(
        owner.kind(),
        SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
    ) {
        return;
    }
    let Some(body) = owner.child_of_kind(SyntaxKind::Block) else {
        return;
    };
    let Some(name) = parameter.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let name = name.value_text().to_string();
    let Some(symbol) = context.view.declared(&parameter) else {
        return;
    };
    let ty = context.view.symbol_type(symbol);
    if parameter
        .child_tokens()
        .any(|token| token.kind() == SyntaxKind::OutKeyword)
    {
        return;
    }
    if let Some(edit) = null_check(context, &owner, &body, &name, &ty) {
        found.push(context.local("Add null check", ActionKind::Refactor, None, vec![edit]));
    }
    if owner.kind() == SyntaxKind::ConstructorDeclaration {
        keep(context, &owner, &body, &name, &ty, found);
    }
}

/// The indentation of a body's statements.
fn statement_indent(context: &Context<'_, '_>, owner: &SyntaxNode, body: &SyntaxNode) -> String {
    statements_of(body)
        .first()
        .filter(|first| starts_line(&context.text, first.span().start()))
        .map_or_else(
            || {
                format!(
                    "{}{}",
                    context.indentation_at(owner.span().start()),
                    context.indent_unit()
                )
            },
            |first| context.indentation_at(first.span().start()),
        )
}

/// Whether `null` is a value of `ty`.
fn can_be_null(context: &Context<'_, '_>, ty: &Type) -> bool {
    match ty {
        Type::Array { .. } => true,
        Type::Named { symbol, .. } => {
            let symbols = context.view.compiled().symbols();
            let qualified = symbols.qualified_name(*symbol);
            qualified == "System.Nullable`1"
                || qualified == SpecialType::String.metadata_name()
                || qualified == SpecialType::Object.metadata_name()
                || matches!(
                    symbols.get(*symbol).type_kind(),
                    Some(TypeKind::Class | TypeKind::Interface | TypeKind::Delegate)
                )
        }
        _ => false,
    }
}

fn null_check(
    context: &mut Context<'_, '_>,
    owner: &SyntaxNode,
    body: &SyntaxNode,
    name: &str,
    ty: &Type,
) -> Option<TextEdit> {
    if !can_be_null(context, ty) {
        return None;
    }
    let statements = statements_of(body);
    let checks = |statement: &SyntaxNode| {
        let text = statement.text();
        text.contains("ThrowIfNull") || text.contains("ArgumentNullException")
    };
    if statements.iter().any(|statement| {
        checks(statement)
            && statement.descendant_tokens().any(|token| {
                token.kind() == SyntaxKind::IdentifierToken && token.value_text() == name
            })
    }) {
        return None;
    }
    let exception = context
        .view
        .compiled()
        .type_by_metadata_name("System.ArgumentNullException")?;
    let written = context.view.display_type(&Type::named(exception), body)?;
    let has_throw_if_null = {
        let symbols = context.view.compiled().symbols();
        symbols.get(exception).members.iter().any(|&member| {
            let found = symbols.get(member);
            found.name == "ThrowIfNull" && found.modifiers.contains(Modifiers::STATIC)
        })
    };
    let newline = context.newline();
    let unit = context.indent_unit();
    let indent = statement_indent(context, owner, body);
    let check = if has_throw_if_null {
        format!("{written}.ThrowIfNull({name});")
    } else {
        format!(
            "if ({name} is null){newline}{indent}{{{newline}{indent}{unit}throw new {written}(nameof({name}));{newline}{indent}}}"
        )
    };
    // After the checks of the parameters before this one.
    let parameters: Vec<String> = owner
        .child_of_kind(SyntaxKind::ParameterList)?
        .children()
        .filter_map(|parameter| {
            parameter
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
        })
        .collect();
    let ours = parameters.iter().position(|other| other == name)?;
    let mut after = None;
    for statement in &statements {
        if !checks(statement) {
            break;
        }
        let checked = parameters.iter().position(|parameter| {
            statement.descendant_tokens().any(|token| {
                token.kind() == SyntaxKind::IdentifierToken && token.value_text() == parameter
            })
        });
        match checked {
            Some(index) if index < ours => after = Some(statement.span().end()),
            _ => break,
        }
    }
    let at = match after {
        Some(at) => at,
        None => body
            .child_token_of_kind(SyntaxKind::OpenBraceToken)?
            .span()
            .end(),
    };
    Some(TextEdit::insert(at, format!("{newline}{indent}{check}")))
}

/// Offers to keep a constructor parameter in a member: a new one, or one
/// there already.
fn keep(
    context: &mut Context<'_, '_>,
    constructor: &SyntaxNode,
    body: &SyntaxNode,
    name: &str,
    ty: &Type,
    found: &mut Vec<CodeAction>,
) {
    let Some(declaration) = constructor.parent().cloned() else {
        return;
    };
    // Already assigned to something.
    let assigned = body.descendants().any(|node| {
        node.kind() == SyntaxKind::SimpleAssignmentExpression
            && node
                .children()
                .last()
                .is_some_and(|value| value.text() == name)
    });
    if assigned {
        return;
    }
    let Some(type_symbol) = context.view.declared(&declaration) else {
        return;
    };
    let newline = context.newline();
    let statement_indent = statement_indent(context, constructor, body);
    let assign_at = match statements_of(body).last() {
        Some(last) => last.span().end(),
        None => match body.child_token_of_kind(SyntaxKind::OpenBraceToken) {
            Some(open) => open.span().end(),
            None => return,
        },
    };
    let assignment = |target: &str| {
        let target = if target == name {
            format!("this.{target}")
        } else {
            target.to_string()
        };
        TextEdit::insert(
            assign_at,
            format!("{newline}{statement_indent}{target} = {name};"),
        )
    };

    // A member there already, of the same type, called what the parameter
    // is.
    let existing: Vec<(String, SymbolKind)> = {
        let symbols = context.view.compiled().symbols();
        symbols
            .get(type_symbol)
            .members
            .iter()
            .map(|&member| symbols.get(member))
            .filter(|member| {
                matches!(member.kind, SymbolKind::Field | SymbolKind::Property)
                    && !member.modifiers.contains(Modifiers::STATIC)
                    && !member.modifiers.contains(Modifiers::CONST)
                    && camel_case(&member.name) == camel_case(name)
            })
            .map(|member| (member.name.clone(), member.kind))
            .collect()
    };
    if !existing.is_empty() {
        for (member, kind) in existing {
            let symbols_ty = {
                let symbols = context.view.compiled().symbols();
                symbols
                    .get(type_symbol)
                    .members
                    .iter()
                    .copied()
                    .find(|&id| symbols.get(id).name == member)
            };
            let Some(id) = symbols_ty else {
                continue;
            };
            if context.view.symbol_type(id) != *ty {
                continue;
            }
            let noun = if kind == SymbolKind::Field {
                "field"
            } else {
                "property"
            };
            found.push(context.local(
                format!("Initialize {noun} '{member}'"),
                ActionKind::Refactor,
                None,
                vec![assignment(&member)],
            ));
        }
        return;
    }

    let Some(written) = context.view.display_type(ty, &declaration) else {
        return;
    };
    let members: Vec<SyntaxNode> = declaration
        .children()
        .filter(|child| is_member(child.kind()))
        .collect();
    let member_indent = context.indentation_at(constructor.span().start());
    let underscore = members.iter().any(|member| {
        member.kind() == SyntaxKind::FieldDeclaration
            && member.descendant_tokens().any(|token| {
                token.kind() == SyntaxKind::IdentifierToken && token.value_text().starts_with('_')
            })
    });
    let field = if underscore {
        format!("_{}", camel_case(name).trim_start_matches('@'))
    } else {
        name.to_string()
    };
    let property = pascal_case(name);
    let place = |kinds: &[SyntaxKind]| {
        members
            .iter()
            .rev()
            .find(|member| kinds.contains(&member.kind()))
            .map(|member| (member.span().end(), false))
    };
    let first = members.first().map(|member| (member.span().start(), true));

    let field_at = place(&[SyntaxKind::FieldDeclaration]).or(first);
    let property_at = place(&[SyntaxKind::PropertyDeclaration])
        .or_else(|| place(&[SyntaxKind::FieldDeclaration]))
        .or(first);
    let declare = |at: (u32, bool), text: String| {
        if at.1 {
            TextEdit::insert(at.0, format!("{text}{newline}{newline}{member_indent}"))
        } else {
            TextEdit::insert(at.0, format!("{newline}{member_indent}{text}"))
        }
    };
    if let Some(at) = field_at {
        found.push(context.local(
            format!("Create and assign field '{field}'"),
            ActionKind::Refactor,
            None,
            vec![
                declare(at, format!("private readonly {written} {field};")),
                assignment(&field),
            ],
        ));
    }
    if let Some(at) = property_at {
        found.push(context.local(
            format!("Create and assign property '{property}'"),
            ActionKind::Refactor,
            None,
            vec![
                declare(at, format!("public {written} {property} {{ get; }}")),
                assignment(&property),
            ],
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn a_null_check_is_an_if_without_throw_if_null() {
        let source = "class C\n{\n    void M(string $$s)\n    {\n        System.Console.WriteLine(s);\n    }\n}\n";
        assert_eq!(
            apply(source, "Add null check"),
            "class C\n{\n    void M(string s)\n    {\n        if (s is null)\n        {\n            throw new System.ArgumentNullException(nameof(s));\n        }\n        System.Console.WriteLine(s);\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    void M(int $$n)\n    {\n    }\n}\n",
            "Add null check",
        );
    }

    #[test]
    fn throw_if_null_is_used_where_there_is_one() {
        let source = "namespace System { public class ArgumentNullException : Exception { public static void ThrowIfNull(object argument) { } } }\nclass C\n{\n    void M(object a, object $$b)\n    {\n        System.ArgumentNullException.ThrowIfNull(a);\n        a.ToString();\n    }\n}\n";
        assert_eq!(
            apply(source, "Add null check"),
            "namespace System { public class ArgumentNullException : Exception { public static void ThrowIfNull(object argument) { } } }\nclass C\n{\n    void M(object a, object b)\n    {\n        System.ArgumentNullException.ThrowIfNull(a);\n        System.ArgumentNullException.ThrowIfNull(b);\n        a.ToString();\n    }\n}\n"
        );
    }

    #[test]
    fn a_constructor_parameter_becomes_a_field_or_a_property() {
        let source =
            "class C\n{\n    private int _count;\n\n    public C(string $$name)\n    {\n    }\n}\n";
        assert_eq!(
            apply(source, "Create and assign field '_name'"),
            "class C\n{\n    private int _count;\n    private readonly string _name;\n\n    public C(string name)\n    {\n        _name = name;\n    }\n}\n"
        );
        assert_eq!(
            apply(source, "Create and assign property 'Name'"),
            "class C\n{\n    private int _count;\n    public string Name { get; }\n\n    public C(string name)\n    {\n        Name = name;\n    }\n}\n"
        );
    }

    #[test]
    fn a_member_there_already_is_initialized() {
        let source = "class C\n{\n    public string Name { get; }\n\n    public C(string $$name)\n    {\n    }\n}\n";
        assert_eq!(
            apply(source, "Initialize property 'Name'"),
            "class C\n{\n    public string Name { get; }\n\n    public C(string name)\n    {\n        Name = name;\n    }\n}\n"
        );
        refuses(source, "Create and assign property 'Name'");
    }
}
