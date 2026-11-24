//! Make static: a method that uses nothing of the instance it is called on
//! becomes `static`, and a class with nothing but static members becomes a
//! `static class`.
//!
//! Roslyn's "Make static" (the fix of CA1822, offered as a refactoring with
//! the cursor on the method's name) and "Make class static". A method
//! qualifies when its body names no `this`, no `base`, and no instance
//! member of its type or the types it derives from without a receiver of
//! its own; and when it is not virtual, abstract, an override or an
//! interface's implementation. Every call made through an instance is
//! rewritten to name the type — `shape.Scale(2)` becomes
//! `Shape.Scale(2)`, written as the receiver's type is written there — and
//! `this.M()` loses its `this.`.
//!
//! A class qualifies when it declares no instance member and no
//! constructor, derives from nothing, is not abstract, and is never used as
//! a type — constructed, declared, cast to — only named to reach its
//! members.

use rustlyn_semantics::{MethodKind, Modifiers, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};

use super::super::{ActionKind, CodeAction, Context};
use super::members::{has_modifier, type_named_at_cursor};
use super::sources::{token_at, with_view};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::{ReferenceKind, Resolved};

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    if let Some(declaration) = type_named_at_cursor(context) {
        if let Some(edit) = make_class_static(context, &declaration) {
            found.push(CodeAction {
                title: "Make class static".to_string(),
                kind: ActionKind::Refactor,
                fixes: None,
                edit,
            });
        }
        return;
    }
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let method = token.parent().clone();
    if token.kind() != SyntaxKind::IdentifierToken
        || method.kind() != SyntaxKind::MethodDeclaration
        || method
            .child_token_of_kind(SyntaxKind::IdentifierToken)
            .as_ref()
            != Some(&token)
    {
        return;
    }
    if let Some(edit) = make_method_static(context, &method, &token) {
        found.push(CodeAction {
            title: "Make static".to_string(),
            kind: ActionKind::Refactor,
            fixes: None,
            edit,
        });
    }
}

/// Where `static` goes among a declaration's modifiers: after its
/// accessibility, or first.
fn static_edit(declaration: &SyntaxNode) -> Option<TextEdit> {
    let access = declaration
        .child_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::PublicKeyword
                    | SyntaxKind::PrivateKeyword
                    | SyntaxKind::ProtectedKeyword
                    | SyntaxKind::InternalKeyword
                    | SyntaxKind::NewKeyword
            )
        })
        .last();
    Some(match access {
        Some(token) => TextEdit::insert(token.span().end(), " static"),
        None => {
            let first = declaration
                .children_with_tokens()
                .find(|element| element.kind() != SyntaxKind::AttributeList)?;
            TextEdit::insert(first.span().start(), "static ")
        }
    })
}

fn make_method_static(
    context: &mut Context<'_, '_>,
    method: &SyntaxNode,
    name: &SyntaxToken,
) -> Option<WorkspaceEdit> {
    let symbol = context.view.declared(method)?;
    let semantic = context.view.project();
    let symbols = semantic.compilation.symbols();
    let found = symbols.get(symbol);
    let modifiers = found.modifiers;
    if modifiers.contains(Modifiers::STATIC)
        || modifiers.contains(Modifiers::VIRTUAL)
        || modifiers.contains(Modifiers::ABSTRACT)
        || modifiers.contains(Modifiers::OVERRIDE)
        || modifiers.contains(Modifiers::EXTERN)
        || modifiers.contains(Modifiers::PARTIAL)
        || found.as_method()?.method_kind != MethodKind::Ordinary
        || semantic.cascade(symbol).len() > 1
    {
        return None;
    }
    let class = found.container?;
    if symbols.get(class).type_kind() == Some(rustlyn_semantics::TypeKind::Interface) {
        return None;
    }
    // A body, and nothing of the instance in it.
    let body = method
        .child_of_kind(SyntaxKind::Block)
        .or_else(|| method.child_of_kind(SyntaxKind::ArrowExpressionClause))?;
    let tokens: Vec<SyntaxToken> = body.descendant_tokens().collect();
    for token in tokens {
        match token.kind() {
            SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword => return None,
            SyntaxKind::IdentifierToken => {}
            _ => continue,
        }
        let name_node = token.parent().clone();
        let qualified = name_node.parent().is_some_and(|parent| {
            matches!(
                parent.kind(),
                SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
            ) && parent.children().last().as_ref() == Some(&name_node)
        });
        if qualified {
            continue;
        }
        let Some(Resolved::Symbol(used)) = context.view.resolve(&token) else {
            continue;
        };
        let symbols = context.view.compiled().symbols();
        let used_symbol = symbols.get(used);
        let is_instance_member = matches!(
            used_symbol.kind,
            SymbolKind::Method | SymbolKind::Field | SymbolKind::Property | SymbolKind::Event
        ) && !used_symbol.modifiers.contains(Modifiers::STATIC)
            && !used_symbol.modifiers.contains(Modifiers::CONST)
            && used_symbol
                .container
                .is_some_and(|container| symbols.get(container).kind == SymbolKind::NamedType)
            && used_symbol
                .as_method()
                .is_none_or(|detail| detail.method_kind != MethodKind::LocalFunction);
        if is_instance_member {
            return None;
        }
    }
    let mut edit = WorkspaceEdit::default();
    edit.add(context.path.clone(), static_edit(method)?);
    let (_, references) =
        semantic.references_detailed(&context.path, name.span().start(), Some(&context.text))?;
    for reference in references {
        if reference.kind == ReferenceKind::Definition {
            continue;
        }
        let Some(token) = token_at(context, &reference.path, reference.span) else {
            continue;
        };
        let name_node = token.parent().clone();
        let Some(access) = name_node.parent().cloned() else {
            continue;
        };
        if access.kind() == SyntaxKind::MemberBindingExpression {
            // `x?.M()`: the receiver is a value, and a static call has none.
            return None;
        }
        if access.kind() != SyntaxKind::SimpleMemberAccessExpression
            || access.children().last().as_ref() != Some(&name_node)
        {
            continue;
        }
        let receiver = access.children().next()?;
        let replacement = if receiver.kind() == SyntaxKind::ThisExpression {
            // `this.M()` becomes `M()`.
            TextEdit::delete(rustlyn_text::TextSpan::from_bounds(
                receiver.span().start(),
                name_node.span().start(),
            ))
        } else {
            let written = with_view(context, &reference.path, |view| {
                if receiver.kind() == SyntaxKind::BaseExpression {
                    return view.display_type(&Type::named(class), &receiver);
                }
                // A type named already stays as it is.
                if let Some(last) = receiver
                    .descendant_tokens()
                    .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .last()
                    && let Some(Resolved::Symbol(named)) = view.resolve(&last)
                    && view.compiled().symbols().get(named).kind == SymbolKind::NamedType
                {
                    return Some(receiver.text());
                }
                let ty = view.expression_type(&receiver)?;
                view.display_type(&ty, &receiver)
            })
            .flatten()?;
            if written == receiver.text() {
                continue;
            }
            TextEdit::new(receiver.span(), written)
        };
        edit.add(reference.path.clone(), replacement);
    }
    Some(edit)
}

fn make_class_static(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
) -> Option<WorkspaceEdit> {
    if declaration.kind() != SyntaxKind::ClassDeclaration
        || has_modifier(declaration, SyntaxKind::StaticKeyword)
        || has_modifier(declaration, SyntaxKind::AbstractKeyword)
        || declaration.child_of_kind(SyntaxKind::BaseList).is_some()
        || declaration
            .child_of_kind(SyntaxKind::TypeParameterList)
            .is_some()
        || declaration
            .child_of_kind(SyntaxKind::ParameterList)
            .is_some()
        || has_modifier(declaration, SyntaxKind::PartialKeyword)
    {
        return None;
    }
    let mut any = false;
    for member in declaration.children() {
        match member.kind() {
            SyntaxKind::ConstructorDeclaration => {
                if !has_modifier(&member, SyntaxKind::StaticKeyword) {
                    return None;
                }
            }
            SyntaxKind::FieldDeclaration => {
                if !(has_modifier(&member, SyntaxKind::StaticKeyword)
                    || has_modifier(&member, SyntaxKind::ConstKeyword))
                {
                    return None;
                }
                any = true;
            }
            SyntaxKind::MethodDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::EventFieldDeclaration => {
                if !has_modifier(&member, SyntaxKind::StaticKeyword) {
                    return None;
                }
                any = true;
            }
            SyntaxKind::IndexerDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::DestructorDeclaration => return None,
            _ => {}
        }
    }
    if !any {
        return None;
    }
    // Only ever named to reach its members.
    let name = declaration.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let semantic = context.view.project();
    let (_, references) =
        semantic.references_detailed(&context.path, name.span().start(), Some(&context.text))?;
    for reference in references {
        if reference.kind == ReferenceKind::Definition {
            continue;
        }
        let token = token_at(context, &reference.path, reference.span)?;
        let name_node = token.parent().clone();
        let parent = name_node.parent()?;
        let reaches_member = matches!(
            parent.kind(),
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName
        ) && parent.children().next().as_ref() == Some(&name_node);
        let named = matches!(
            parent.kind(),
            SyntaxKind::TypeOfExpression | SyntaxKind::UsingDirective
        ) || parent.parent().is_some_and(|grand| {
            grand.kind() == SyntaxKind::InvocationExpression && grand.text().starts_with("nameof")
        });
        if !(reaches_member || named) {
            return None;
        }
    }
    let mut edits = vec![static_edit(declaration)?];
    if let Some(sealed) = declaration
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::SealedKeyword)
    {
        let end = sealed.full_span().end().max(sealed.span().end());
        edits.push(TextEdit::delete(rustlyn_text::TextSpan::from_bounds(
            sealed.span().start(),
            end,
        )));
    }
    Some(WorkspaceEdit::single(context.path.clone(), edits))
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::support::{apply, apply_in, refuses};

    fn file<'a>(files: &'a [(PathBuf, String)], name: &str) -> &'a str {
        &files
            .iter()
            .find(|(path, _)| path == Path::new(name))
            .expect("the file")
            .1
    }

    #[test]
    fn a_method_without_instance_state_becomes_static_with_its_calls() {
        let shape = "namespace Draw\n{\n    public class Shape\n    {\n        public int Sides;\n\n        public double $$Scale(double size, double factor) => size * factor;\n\n        public double Grow() => this.Scale(Sides, 2) + Scale(1, 1);\n    }\n}\n";
        let canvas = "namespace Draw\n{\n    class Canvas\n    {\n        double M(Shape shape) => shape.Scale(3, 4);\n    }\n}\n";
        let changed = apply_in(&[("A.cs", shape), ("B.cs", canvas)], "Make static");
        assert_eq!(
            file(&changed, "/p/A.cs"),
            "namespace Draw\n{\n    public class Shape\n    {\n        public int Sides;\n\n        public static double Scale(double size, double factor) => size * factor;\n\n        public double Grow() => Scale(Sides, 2) + Scale(1, 1);\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/B.cs"),
            "namespace Draw\n{\n    class Canvas\n    {\n        double M(Shape shape) => Shape.Scale(3, 4);\n    }\n}\n"
        );
    }

    #[test]
    fn instance_state_keeps_it_an_instance_method() {
        refuses(
            "class C\n{\n    int count;\n    int $$Next() => count + 1;\n}\n",
            "Make static",
        );
        refuses(
            "class B { public virtual int $$V() => 1; }\n",
            "Make static",
        );
    }

    #[test]
    fn a_class_of_static_members_becomes_static() {
        let source = "sealed class $$Maths\n{\n    public const double Pi = 3.14;\n    public static double Twice(double x) => x * 2;\n}\n\nclass User\n{\n    double M() => Maths.Twice(Maths.Pi);\n}\n";
        assert_eq!(
            apply(source, "Make class static"),
            "static class Maths\n{\n    public const double Pi = 3.14;\n    public static double Twice(double x) => x * 2;\n}\n\nclass User\n{\n    double M() => Maths.Twice(Maths.Pi);\n}\n"
        );
        refuses(
            "class $$Maths\n{\n    public static int One() => 1;\n}\n\nclass User\n{\n    Maths m = new Maths();\n}\n",
            "Make class static",
        );
    }
}
