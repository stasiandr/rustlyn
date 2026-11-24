//! Encapsulate field: put a property in front of a field, and make the
//! field private.
//!
//! Roslyn's `EncapsulateField`, in both of its variants: "and use property"
//! points every use of the field in the project at the property instead —
//! except those in the type's constructors, which go on initializing the
//! field directly, as Roslyn has them — and "but still use field" leaves
//! them. A field whose name is already a property's (`public int Count;`)
//! is renamed to the camel-case name, and then the uses that keep reading
//! the field are renamed with it.
//!
//! The property has the field's accessibility unless that was `private`,
//! then `public`; a `readonly` field gets only a getter.

use rustlyn_syntax::SyntaxKind;
use rustlyn_text::TextSpan;

use super::super::text::{camel_case, is_type_declaration, pascal_case};
use super::super::{ActionKind, CodeAction, Context};
use super::{across_files, references_at};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let declarator = token.parent().clone();
    if token.kind() != SyntaxKind::IdentifierToken
        || declarator.kind() != SyntaxKind::VariableDeclarator
    {
        return;
    }
    let Some(declaration) = declarator.parent().cloned() else {
        return;
    };
    let Some(field) = declaration.parent().cloned() else {
        return;
    };
    if field.kind() != SyntaxKind::FieldDeclaration
        || declaration
            .children()
            .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
            .count()
            != 1
        || field.child_tokens().any(|token| {
            matches!(
                token.kind(),
                SyntaxKind::ConstKeyword | SyntaxKind::FixedKeyword
            )
        })
    {
        return;
    }
    let Some(ty) = field
        .parent()
        .cloned()
        .filter(|ty| is_type_declaration(ty.kind()))
    else {
        return;
    };
    let Some(type_text) = declaration.children().next().map(|ty| ty.text()) else {
        return;
    };
    let name = token.value_text().to_string();
    let starts_upper = name.chars().next().is_some_and(char::is_uppercase);
    let (field_name, property) = if starts_upper {
        (camel_case(&name), name.clone())
    } else {
        (name.clone(), pascal_case(&name))
    };
    if field_name == property || property.is_empty() {
        return;
    }
    // Neither new name may be taken in the type.
    let taken = context.view.names_near(&field);
    if (taken.contains(&property) && property != name)
        || (starts_upper && taken.contains(&field_name))
    {
        return;
    }

    let access: Vec<&str> = field
        .child_tokens()
        .filter_map(|token| match token.kind() {
            SyntaxKind::PublicKeyword => Some("public"),
            SyntaxKind::InternalKeyword => Some("internal"),
            SyntaxKind::ProtectedKeyword => Some("protected"),
            SyntaxKind::PrivateKeyword => Some("private"),
            _ => None,
        })
        .collect();
    let property_access = if access.is_empty() || access == ["private"] {
        "public".to_string()
    } else {
        access.join(" ")
    };
    let is_static = field
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some();
    let is_readonly = field
        .child_token_of_kind(SyntaxKind::ReadOnlyKeyword)
        .is_some();
    let accessors = if is_readonly {
        format!("get => {field_name};")
    } else {
        format!("get => {field_name}; set => {field_name} = value;")
    };
    let static_text = if is_static { "static " } else { "" };
    let text = format!("{property_access} {static_text}{type_text} {property} {{ {accessors} }}");
    let newline = context.newline();
    let indent = context.indentation_at(field.span().start());

    // The field's own edits: private, maybe renamed, and the property
    // after it.
    let mut own = Vec::new();
    let access_tokens: Vec<_> = field
        .child_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::PublicKeyword
                    | SyntaxKind::InternalKeyword
                    | SyntaxKind::ProtectedKeyword
                    | SyntaxKind::PrivateKeyword
            )
        })
        .collect();
    match access_tokens.as_slice() {
        [] => {}
        [first, rest @ ..] => {
            let end = rest
                .last()
                .map_or(first.span().end(), |last| last.span().end());
            own.push(TextEdit::new(
                TextSpan::from_bounds(first.span().start(), end),
                "private",
            ));
        }
    }
    if field_name != name {
        own.push(TextEdit::new(token.span(), field_name.clone()));
    }
    own.push(TextEdit::insert(
        field.span().end(),
        format!("{newline}{newline}{indent}{text}"),
    ));

    let constructors: Vec<TextSpan> = ty
        .children()
        .filter(|member| member.kind() == SyntaxKind::ConstructorDeclaration)
        .map(|member| member.span())
        .collect();
    let references: Vec<_> = references_at(context, token.span().start())
        .into_iter()
        .filter(|(path, span)| !(*path == context.path && *span == token.span()))
        .collect();
    let in_constructor = |path: &std::path::Path, span: TextSpan| {
        path == context.path && constructors.iter().any(|ctor| ctor.contains_span(span))
    };
    // The field turns private: code outside the type can only reach it
    // through the property, whichever variant was chosen.
    let type_span = ty.span();
    let outside = |path: &std::path::Path, span: TextSpan| {
        path != context.path || !type_span.contains_span(span)
    };

    for use_property in [true, false] {
        let mut edits: Vec<(std::path::PathBuf, TextEdit)> = own
            .iter()
            .map(|edit| (context.path.clone(), edit.clone()))
            .collect();
        for (path, span) in &references {
            let to = if (use_property && !in_constructor(path, *span)) || outside(path, *span) {
                &property
            } else if field_name != name {
                &field_name
            } else {
                continue;
            };
            edits.push((path.clone(), TextEdit::new(*span, to.clone())));
        }
        let title = if use_property {
            format!("Encapsulate field: '{name}' (and use property)")
        } else {
            format!("Encapsulate field: '{name}' (but still use field)")
        };
        found.push(across_files(title, ActionKind::Refactor, edits));
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::support::apply_in;

    #[test]
    fn a_private_field_gets_a_property_used_everywhere() {
        let a = "class Counter\n{\n    private int $$count;\n\n    public Counter() { count = 1; }\n    public void Add() { count++; }\n}\n";
        let b = "class User\n{\n    void Use(Counter c) { }\n}\n";
        let changed = apply_in(
            &[("A.cs", a), ("B.cs", b)],
            "Encapsulate field: 'count' (and use property)",
        );
        let text = &changed
            .iter()
            .find(|(path, _)| path == Path::new("/p/A.cs"))
            .unwrap()
            .1;
        assert_eq!(
            text,
            "class Counter\n{\n    private int count;\n\n    public int Count { get => count; set => count = value; }\n\n    public Counter() { count = 1; }\n    public void Add() { Count++; }\n}\n"
        );
    }

    #[test]
    fn a_public_field_is_renamed_behind_its_property() {
        let a = "class Box\n{\n    public readonly string $$Label;\n}\n";
        let b = "class User\n{\n    string Read(Box box) => box.Label;\n}\n";
        let changed = apply_in(
            &[("A.cs", a), ("B.cs", b)],
            "Encapsulate field: 'Label' (but still use field)",
        );
        let text = |name: &str| {
            changed
                .iter()
                .find(|(path, _)| path == Path::new(name))
                .unwrap()
                .1
                .clone()
        };
        assert_eq!(
            text("/p/A.cs"),
            "class Box\n{\n    private readonly string label;\n\n    public string Label { get => label; }\n}\n"
        );
        assert_eq!(
            text("/p/B.cs"),
            // Outside the type the field is private now: the property it is.
            "class User\n{\n    string Read(Box box) => box.Label;\n}\n"
        );
        let used = apply_in(
            &[("A.cs", a), ("B.cs", b)],
            "Encapsulate field: 'Label' (and use property)",
        );
        assert_eq!(
            used.iter()
                .find(|(path, _)| path == Path::new("/p/B.cs"))
                .unwrap()
                .1,
            b
        );
    }
}
