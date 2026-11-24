//! Generate constructor, generate `Equals` and `GetHashCode`, from the
//! fields and properties a selection covers (or, with the cursor on a
//! type's name, from all of them).
//!
//! Roslyn's `GenerateConstructorFromMembers` and
//! `GenerateEqualsAndGetHashCodeFromMembers`, without their dialogs: what
//! would have been picked in the dialog is what was selected. The members
//! are instance fields and auto-properties.
//!
//! The constructor takes one parameter per member, named as a local would
//! be (`_count` gives `count`), and assigns each, with `this.` where the
//! names are the same. It goes after the last constructor, or after the
//! last field or property, and is not offered when one with the same
//! parameter types exists.
//!
//! `Equals` compares each member with `==` where the type has a built-in
//! one and through `EqualityComparer<T>.Default` otherwise. `GetHashCode`
//! is `HashCode.Combine` where the compilation has it and the members are
//! few enough, and the multiply-and-add Roslyn wrote before that otherwise.

use rustlyn_semantics::{MethodKind, Modifiers, SpecialType, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::text::{camel_case, fresh_name, is_member, is_type_declaration};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some((ty, members)) = picked(context) else {
        return;
    };
    if members.is_empty() {
        return;
    }
    constructor(context, &ty, &members, found);
    equality(context, &ty, &members, found);
}

/// One field or auto-property picked.
struct Member {
    name: String,
    ty: Type,
    written: String,
}

/// The type declaration and the members picked in it.
fn picked(context: &mut Context<'_, '_>) -> Option<(SyntaxNode, Vec<Member>)> {
    let span = context.trimmed_span();
    let root = context.view.syntax_root().clone();
    let (ty, declarations): (SyntaxNode, Vec<SyntaxNode>) = if span.is_empty() {
        let token = context.token_at_cursor()?;
        let ty = token.parent().clone();
        if !is_type_declaration(ty.kind())
            || ty.child_token_of_kind(SyntaxKind::IdentifierToken).as_ref() != Some(&token)
        {
            return None;
        }
        let all = ty
            .children()
            .filter(|child| is_member(child.kind()))
            .collect();
        (ty, all)
    } else {
        let covering = root.find_node(span)?;
        let ty = std::iter::once(covering.clone())
            .chain(covering.ancestors())
            .find(|node| is_type_declaration(node.kind()))?;
        let touched: Vec<SyntaxNode> = ty
            .children()
            .filter(|child| is_member(child.kind()))
            .filter(|child| child.span().overlaps_with(span) || span.contains_span(child.span()))
            .collect();
        // A selection inside one member's body is about that body.
        if touched.len() == 1 && !span.contains_span(touched[0].span()) {
            let only = &touched[0];
            let head_end = only
                .children()
                .find(|child| {
                    matches!(
                        child.kind(),
                        SyntaxKind::VariableDeclaration | SyntaxKind::AccessorList
                    )
                })
                .map_or(only.span().end(), |child| child.span().end());
            if span.start() > head_end {
                return None;
            }
        }
        (ty, touched)
    };
    let mut members = Vec::new();
    for declaration in &declarations {
        if declaration.child_tokens().any(|token| {
            matches!(
                token.kind(),
                SyntaxKind::StaticKeyword | SyntaxKind::ConstKeyword
            )
        }) {
            continue;
        }
        match declaration.kind() {
            SyntaxKind::FieldDeclaration => {
                let variables = declaration.child_of_kind(SyntaxKind::VariableDeclaration)?;
                for declarator in variables
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                {
                    let symbol = context.view.declared(&declarator)?;
                    let ty = context.view.symbol_type(symbol);
                    let written = context.view.display_type(&ty, &declarator)?;
                    members.push(Member {
                        name: context.view.compiled().symbols().get(symbol).name.clone(),
                        ty,
                        written,
                    });
                }
            }
            SyntaxKind::PropertyDeclaration => {
                let Some(accessors) = declaration.child_of_kind(SyntaxKind::AccessorList) else {
                    continue;
                };
                let automatic = accessors.children().all(|accessor| {
                    accessor.child_of_kind(SyntaxKind::Block).is_none()
                        && accessor
                            .child_of_kind(SyntaxKind::ArrowExpressionClause)
                            .is_none()
                });
                if !automatic {
                    continue;
                }
                let symbol = context.view.declared(declaration)?;
                let ty = context.view.symbol_type(symbol);
                let written = context.view.display_type(&ty, declaration)?;
                members.push(Member {
                    name: context.view.compiled().symbols().get(symbol).name.clone(),
                    ty,
                    written,
                });
            }
            _ => {}
        }
    }
    Some((ty, members))
}

/// The indentation of the type's members.
fn member_indent(context: &Context<'_, '_>, ty: &SyntaxNode) -> String {
    match ty.children().find(|child| is_member(child.kind())) {
        Some(first) => context.indentation_at(first.span().start()),
        None => format!(
            "{}{}",
            context.indentation_at(ty.span().start()),
            context.indent_unit()
        ),
    }
}

/// Inserts `text`, a member, after `after` or, when there is nothing to
/// put it after, first in the type.
fn insert_member(
    context: &Context<'_, '_>,
    ty: &SyntaxNode,
    after: Option<&SyntaxNode>,
    text: &str,
) -> Option<TextEdit> {
    let newline = context.newline();
    let indent = member_indent(context, ty);
    match after {
        Some(after) => Some(TextEdit::insert(
            after.span().end(),
            format!("{newline}{newline}{indent}{text}"),
        )),
        None => {
            let open = ty.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
            Some(TextEdit::insert(
                open.span().end(),
                format!("{newline}{indent}{text}"),
            ))
        }
    }
}

fn constructor(
    context: &mut Context<'_, '_>,
    ty: &SyntaxNode,
    members: &[Member],
    found: &mut Vec<CodeAction>,
) {
    let Some(type_name) = ty.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let type_name = type_name.value_text().to_string();
    let mut parameters = Vec::new();
    let mut assignments = Vec::new();
    for member in members {
        let parameter = camel_case(&member.name);
        if parameters
            .iter()
            .any(|(name, _): &(String, String)| *name == parameter)
        {
            return;
        }
        let target = if parameter == member.name {
            format!("this.{}", member.name)
        } else {
            member.name.clone()
        };
        assignments.push(format!("{target} = {parameter};"));
        parameters.push((parameter, member.written.clone()));
    }

    // Not when one with these parameter types is there.
    let Some(symbol) = context.view.declared(ty) else {
        return;
    };
    let wanted: Vec<&str> = parameters.iter().map(|(_, ty)| ty.as_str()).collect();
    // Only the constructor C# gives a type with none written: the new one
    // takes it away, and `new T()` somewhere would stop compiling.
    let implicit_only = matches!(
        ty.kind(),
        SyntaxKind::ClassDeclaration | SyntaxKind::RecordDeclaration
    ) && ty.child_token_of_kind(SyntaxKind::StaticKeyword).is_none()
        && ty.child_of_kind(SyntaxKind::ParameterList).is_none()
        && !ty
            .children()
            .any(|child| child.kind() == SyntaxKind::ConstructorDeclaration);
    let keeps_default = implicit_only && !parameters.is_empty() && {
        let semantic = context.view.semantic;
        let calls = [
            format!("new {type_name}()"),
            format!("new {type_name} {{"),
            format!("new {type_name}{{"),
        ];
        semantic.paths.values().any(|path| {
            semantic
                .text(path)
                .is_some_and(|text| calls.iter().any(|call| text.contains(call.as_str())))
        }) || calls
            .iter()
            .any(|call| context.text.contains(call.as_str()))
    };
    let existing: Vec<Vec<String>> = {
        let symbols = context.view.compiled().symbols();
        let constructors: Vec<Vec<rustlyn_semantics::SymbolId>> = symbols
            .get(symbol)
            .members
            .iter()
            .filter_map(|&member| symbols.get(member).as_method())
            .filter(|method| method.method_kind == MethodKind::Constructor)
            .map(|method| method.parameters.clone())
            .collect();
        constructors
            .into_iter()
            .map(|parameters| {
                parameters
                    .into_iter()
                    .map(|parameter| {
                        let parameter_type = context.view.symbol_type(parameter);
                        context
                            .view
                            .display_type(&parameter_type, ty)
                            .unwrap_or_default()
                    })
                    .collect()
            })
            .collect()
    };
    if existing
        .iter()
        .any(|types| types.iter().map(String::as_str).eq(wanted.iter().copied()))
    {
        return;
    }

    let newline = context.newline();
    let indent = member_indent(context, ty);
    let unit = context.indent_unit();
    let access = if ty
        .child_token_of_kind(SyntaxKind::AbstractKeyword)
        .is_some()
    {
        "protected"
    } else {
        "public"
    };
    let list: Vec<String> = parameters
        .iter()
        .map(|(name, ty)| format!("{ty} {name}"))
        .collect();
    let body: String = assignments
        .iter()
        .map(|line| format!("{indent}{unit}{line}{newline}"))
        .collect();
    let mut text = format!(
        "{access} {type_name}({}){newline}{indent}{{{newline}{body}{indent}}}",
        list.join(", ")
    );
    if keeps_default {
        text = format!(
            "{access} {type_name}(){newline}{indent}{{{newline}{indent}}}{newline}{newline}{indent}{text}"
        );
    }
    let children: Vec<SyntaxNode> = ty
        .children()
        .filter(|child| is_member(child.kind()))
        .collect();
    let after = children
        .iter()
        .rev()
        .find(|child| child.kind() == SyntaxKind::ConstructorDeclaration)
        .or_else(|| {
            children.iter().rev().find(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::FieldDeclaration | SyntaxKind::PropertyDeclaration
                )
            })
        });
    let Some(edit) = insert_member(context, ty, after, &text) else {
        return;
    };
    let types: Vec<&str> = parameters.iter().map(|(_, ty)| ty.as_str()).collect();
    found.push(context.local(
        format!("Generate constructor '{type_name}({})'", types.join(", ")),
        ActionKind::Generate,
        None,
        vec![edit],
    ));
}

fn equality(
    context: &mut Context<'_, '_>,
    ty: &SyntaxNode,
    members: &[Member],
    found: &mut Vec<CodeAction>,
) {
    if matches!(
        ty.kind(),
        SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::InterfaceDeclaration
    ) {
        return;
    }
    let Some(symbol) = context.view.declared(ty) else {
        return;
    };
    let Some(type_name) = ty.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let type_name = match ty.child_of_kind(SyntaxKind::TypeParameterList) {
        Some(list) => format!("{}{}", type_name.value_text(), list.text()),
        None => type_name.value_text().to_string(),
    };
    let (has_equals, has_hash) = {
        let symbols = context.view.compiled().symbols();
        let methods: Vec<_> = symbols
            .get(symbol)
            .members
            .iter()
            .map(|&member| symbols.get(member))
            .filter(|member| member.kind == SymbolKind::Method)
            .collect();
        (
            methods.iter().any(|method| {
                method.name == "Equals"
                    && method.modifiers.contains(Modifiers::OVERRIDE)
                    && method.as_method().is_some_and(|m| m.parameters.len() == 1)
            }),
            methods.iter().any(|method| {
                method.name == "GetHashCode"
                    && method.as_method().is_some_and(|m| m.parameters.is_empty())
            }),
        )
    };
    let equals = equals_method(context, ty, &type_name, members);
    let hash = hash_method(context, ty, members);
    let last = ty.children().filter(|child| is_member(child.kind())).last();
    let newline = context.newline();
    let indent = member_indent(context, ty);
    let mut offer = |title: &str, methods: Vec<&str>| {
        let text = methods.join(&format!("{newline}{newline}{indent}"));
        if let Some(edit) = insert_member(context, ty, last.as_ref(), &text) {
            found.push(context.local(title, ActionKind::Generate, None, vec![edit]));
        }
    };
    if !has_equals && let Some(equals) = &equals {
        offer("Generate Equals(object)", vec![equals]);
        if !has_hash && let Some(hash) = &hash {
            offer("Generate Equals and GetHashCode", vec![equals, hash]);
        }
    }
    if has_equals
        && !has_hash
        && let Some(hash) = &hash
    {
        offer("Generate GetHashCode()", vec![hash]);
    }
}

/// Whether values of `ty` compare with a built-in `==`: the primitive
/// types, `string`, enums.
fn has_builtin_equality(context: &Context<'_, '_>, ty: &Type) -> bool {
    let Type::Named { symbol, .. } = ty else {
        return false;
    };
    let symbols = context.view.compiled().symbols();
    let qualified = symbols.qualified_name(*symbol);
    symbols.get(*symbol).type_kind() == Some(TypeKind::Enum)
        || SpecialType::ALL.iter().any(|special| {
            special.metadata_name() == qualified && !matches!(special, SpecialType::Object)
        })
}

/// Whether `ty` is a value type, whose `GetHashCode` can be called
/// directly.
fn is_value_type(context: &Context<'_, '_>, ty: &Type) -> bool {
    let Type::Named { symbol, .. } = ty else {
        return false;
    };
    let symbols = context.view.compiled().symbols();
    matches!(
        symbols.get(*symbol).type_kind(),
        Some(TypeKind::Struct | TypeKind::Enum)
    )
}

/// Whether `object.Equals(object, object)` is there to fall back on.
fn has_static_equals(context: &Context<'_, '_>) -> bool {
    let Some(object) = context
        .view
        .compiled()
        .type_by_metadata_name("System.Object")
    else {
        return false;
    };
    let symbols = context.view.compiled().symbols();
    symbols.get(object).members.iter().any(|&member| {
        let found = symbols.get(member);
        found.name == "Equals"
            && found.modifiers.contains(Modifiers::STATIC)
            && found
                .as_method()
                .is_some_and(|method| method.parameters.len() == 2)
    })
}

/// `EqualityComparer<T>.Default`, spelled for here, if the compilation has
/// it.
fn comparer(context: &Context<'_, '_>, at: &SyntaxNode, member: &Member) -> Option<String> {
    let found = context
        .view
        .compiled()
        .type_by_metadata_name("System.Collections.Generic.EqualityComparer`1")?;
    let written = context.view.display_type(
        &Type::Named {
            symbol: found,
            type_arguments: vec![member.ty.clone()],
        },
        at,
    )?;
    Some(format!("{written}.Default"))
}

fn equals_method(
    context: &mut Context<'_, '_>,
    ty: &SyntaxNode,
    type_name: &str,
    members: &[Member],
) -> Option<String> {
    let newline = context.newline();
    let indent = member_indent(context, ty);
    let unit = context.indent_unit();
    let taken: std::collections::HashSet<String> = members
        .iter()
        .map(|member| member.name.clone())
        .chain(["obj".to_string()])
        .collect();
    let simple = type_name.split('<').next().unwrap_or(type_name);
    let other = fresh_name(&camel_case(simple), &taken);
    let mut terms = vec![format!("obj is {type_name} {other}")];
    for member in members {
        terms.push(if has_builtin_equality(context, &member.ty) {
            format!("{0} == {other}.{0}", member.name)
        } else if let Some(comparer) = comparer(context, ty, member) {
            format!("{comparer}.Equals({0}, {other}.{0})", member.name)
        } else if has_static_equals(context) {
            format!("Equals({0}, {other}.{0})", member.name)
        } else {
            return None;
        });
    }
    let align = format!("{indent}{unit}       ");
    let body = terms.join(&format!(" &&{newline}{align}"));
    Some(format!(
        "public override bool Equals(object obj){newline}{indent}{{{newline}{indent}{unit}return {body};{newline}{indent}}}"
    ))
}

fn hash_method(
    context: &mut Context<'_, '_>,
    ty: &SyntaxNode,
    members: &[Member],
) -> Option<String> {
    let newline = context.newline();
    let indent = member_indent(context, ty);
    let unit = context.indent_unit();
    let inner = format!("{indent}{unit}");
    let combine = context
        .view
        .compiled()
        .type_by_metadata_name("System.HashCode")
        .filter(|&found| {
            let symbols = context.view.compiled().symbols();
            symbols
                .get(found)
                .members
                .iter()
                .any(|&member| symbols.get(member).name == "Combine")
        });
    let body = match combine {
        Some(found) if members.len() <= 8 => {
            let written = context.view.display_type(&Type::named(found), ty)?;
            let names: Vec<&str> = members.iter().map(|member| member.name.as_str()).collect();
            format!("{inner}return {written}.Combine({});", names.join(", "))
        }
        _ => {
            // Roslyn's seed comes from the names too, so that two types with
            // the same members do not start alike.
            let seed = members
                .iter()
                .flat_map(|member| member.name.bytes())
                .fold(0x811c_9dc5_u32, |hash, byte| {
                    (hash ^ u32::from(byte)).wrapping_mul(0x0100_0193)
                }) as i32;
            let mut lines = vec![format!("{inner}int hashCode = {seed};")];
            for member in members {
                let term = if is_value_type(context, &member.ty) {
                    format!("{}.GetHashCode()", member.name)
                } else if let Some(comparer) = comparer(context, ty, member) {
                    format!("{comparer}.GetHashCode({})", member.name)
                } else {
                    format!("({}?.GetHashCode() ?? 0)", member.name)
                };
                lines.push(format!(
                    "{inner}hashCode = hashCode * -1521134295 + {term};"
                ));
            }
            lines.push(format!("{inner}return hashCode;"));
            lines.join(newline)
        }
    };
    Some(format!(
        "public override int GetHashCode(){newline}{indent}{{{newline}{body}{newline}{indent}}}"
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses, titles};

    #[test]
    fn selected_members_become_a_constructor() {
        let source = "class Point\n{\n    [|private readonly int _x;\n    public string Name { get; }|]\n\n    public void Move() { }\n}\n";
        assert_eq!(
            apply(source, "Generate constructor 'Point(int, string)'"),
            "class Point\n{\n    private readonly int _x;\n    public string Name { get; }\n\n    public Point(int x, string name)\n    {\n        _x = x;\n        Name = name;\n    }\n\n    public void Move() { }\n}\n"
        );
    }

    #[test]
    fn a_constructor_that_exists_is_not_generated_again() {
        refuses(
            "class P\n{\n    [|int count;|]\n    public P(int other) { }\n}\n",
            "Generate constructor 'P(int)'",
        );
        let same_names = "class P\n{\n    [|int count;|]\n}\n";
        assert_eq!(
            apply(same_names, "Generate constructor 'P(int)'"),
            "class P\n{\n    int count;\n\n    public P(int count)\n    {\n        this.count = count;\n    }\n}\n"
        );
    }

    #[test]
    fn a_default_constructor_in_use_is_kept() {
        let source = "class P\n{\n    [|int count;|]\n    static P Make() => new P();\n}\n";
        assert_eq!(
            apply(source, "Generate constructor 'P(int)'"),
            "class P\n{\n    int count;\n\n    public P()\n    {\n    }\n\n    public P(int count)\n    {\n        this.count = count;\n    }\n    static P Make() => new P();\n}\n"
        );
    }

    #[test]
    fn equals_and_hash_code_use_what_the_compilation_has() {
        let source = "namespace System { public struct HashCode { public static int Combine<T1, T2>(T1 a, T2 b) => 0; } }\nclass $$Point\n{\n    int x;\n    string name;\n}\n";
        assert_eq!(
            apply(source, "Generate Equals and GetHashCode"),
            "namespace System { public struct HashCode { public static int Combine<T1, T2>(T1 a, T2 b) => 0; } }\nclass Point\n{\n    int x;\n    string name;\n\n    public override bool Equals(object obj)\n    {\n        return obj is Point point &&\n               x == point.x &&\n               name == point.name;\n    }\n\n    public override int GetHashCode()\n    {\n        return System.HashCode.Combine(x, name);\n    }\n}\n"
        );
    }

    #[test]
    fn without_hash_code_combine_the_classic_form_is_written() {
        let source = "class Box { }\nclass $$Pair\n{\n    int count;\n    Box box;\n    public override bool Equals(object obj) => false;\n}\n";
        let offered = titles(source);
        assert!(
            offered.contains(&"Generate GetHashCode()".to_string()),
            "{offered:?}"
        );
        assert!(
            !offered.contains(&"Generate Equals(object)".to_string()),
            "{offered:?}"
        );
        let text = apply(source, "Generate GetHashCode()");
        assert!(
            text.contains("hashCode = hashCode * -1521134295 + count.GetHashCode();"),
            "{text}"
        );
        assert!(
            text.contains("hashCode = hashCode * -1521134295 + (box?.GetHashCode() ?? 0);"),
            "{text}"
        );
    }
}
