//! Add explicit cast: a value that does not convert implicitly to where it
//! goes, but does with a cast.
//!
//! Roslyn's fix answers CS0266 and CS1503. Rustlyn reports CS0266 only for
//! the casts it is sure of and CS0029 for the rest, so the provider answers
//! both and checks that a cast would do, as §10.3 has it: between numeric types and enums, from a class
//! down to one derived from it, from `object` or an interface, from `T?` to
//! `T`, or through a user-defined `explicit operator`.

use rustlyn_semantics::{SpecialType, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::support::{Namer, expected_type};
use crate::edit::TextEdit;
use crate::semantic::View;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let reported: Vec<(String, rustlyn_text::TextSpan, String)> = context
        .diagnostics_with(&["CS0029", "CS0266", "CS1503"])
        .map(|diagnostic| {
            (
                diagnostic.code().to_string(),
                diagnostic.span(),
                diagnostic.message().to_string(),
            )
        })
        .collect();
    for (code, span, message) in reported {
        let Some(mut node) = context.view.root.find_node(span) else {
            continue;
        };
        // CS1503 is reported on the method's name: `Argument 2:` says which
        // argument.
        if code == "CS1503"
            && !node
                .ancestors()
                .any(|ancestor| ancestor.kind() == SyntaxKind::Argument)
            && let Some(argument) = argument_named_by(&node, &message)
        {
            node = argument;
        }
        if node.kind() == SyntaxKind::Argument
            && let Some(value) = node.children().last()
        {
            node = value;
        }
        let from = context.view.type_of(&node);
        if from.is_error() {
            continue;
        }
        let mut to = if code == "CS0029" || code == "CS0266" {
            expected_type(context.view, &node)
        } else {
            Type::Error
        };
        if to.is_error() || to == Type::Void {
            let Some(written) = message.rsplit('\'').nth(1) else {
                continue;
            };
            to = named(context.view, &node, written);
        }
        let view = &*context.view;
        if to.is_error() || !converts_explicitly(view, &from, &to) {
            continue;
        }
        let namer = Namer::at(view, &node);
        let value = node.text().trim().to_string();
        let value = if is_primary(node.kind()) {
            value
        } else {
            format!("({value})")
        };
        found.push(context.local(
            "Add explicit cast",
            ActionKind::QuickFix,
            Some(&code),
            vec![TextEdit::new(
                node.span(),
                format!("({}){value}", namer.name(&to)),
            )],
        ));
    }
}

/// The argument `Argument 2: cannot convert ...` is about, in the call
/// whose name is `name`.
fn argument_named_by(name: &SyntaxNode, message: &str) -> Option<SyntaxNode> {
    let index: usize = message
        .strip_prefix("Argument ")?
        .split(':')
        .next()?
        .trim()
        .parse()
        .ok()?;
    let call = name.ancestors().find(|ancestor| {
        matches!(
            ancestor.kind(),
            SyntaxKind::InvocationExpression | SyntaxKind::ObjectCreationExpression
        )
    })?;
    call.child_of_kind(SyntaxKind::ArgumentList)?
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
        .nth(index.checked_sub(1)?)
}

/// The type a diagnostic names, `int` or `Widget`, looked up where the
/// value is.
fn named(view: &View<'_>, at: &SyntaxNode, written: &str) -> Type {
    if let Some(special) = SpecialType::ALL
        .iter()
        .find(|special| special.keyword() == written)
    {
        return view
            .compilation()
            .special_type(*special)
            .map_or(Type::Error, Type::named);
    }
    let binder = view.model.binder();
    let context = binder.context_at(view.tree, at);
    binder
        .lookup(written, 0, &context)
        .map_or(Type::Error, Type::named)
}

/// Whether a cast takes `from` to `to` (§10.3).
fn converts_explicitly(view: &View<'_>, from: &Type, to: &Type) -> bool {
    let binder = view.model.binder();
    let symbols = view.compilation().symbols();
    let numeric = |ty: &Type| binder.special_of(ty).is_some_and(SpecialType::is_numeric);
    let is_enum = |ty: &Type| {
        ty.symbol()
            .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Enum))
    };
    if (numeric(from) || is_enum(from)) && (numeric(to) || is_enum(to)) {
        return true;
    }
    if binder.nullable_underlying(from).as_ref() == Some(to) {
        return true;
    }
    if binder.explicit_operator(from, to).is_some() {
        return true;
    }
    // Down a reference type's chain, or from `object` or an interface.
    if from.is_reference_type(symbols) && to.is_reference_type(symbols) {
        if binder.special_of(from) == Some(SpecialType::Object) {
            return true;
        }
        if let Some(symbol) = from.symbol()
            && view.types_of(to).contains(&symbol)
        {
            return true;
        }
        let interface = |ty: &Type| {
            ty.symbol()
                .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Interface))
        };
        let sealed = |ty: &Type| {
            ty.symbol().is_some_and(|symbol| {
                symbols
                    .get(symbol)
                    .modifiers
                    .contains(rustlyn_semantics::Modifiers::SEALED)
            })
        };
        if interface(from) && !sealed(to) || interface(to) && !sealed(from) {
            return true;
        }
    }
    // Unboxing.
    binder.special_of(from) == Some(SpecialType::Object) && !to.is_reference_type(symbols)
}

/// Whether an expression can take a cast in front of it without
/// parentheses.
const fn is_primary(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::IdentifierName
            | SyntaxKind::GenericName
            | SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::InvocationExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::ParenthesizedExpression
            | SyntaxKind::NumericLiteralExpression
            | SyntaxKind::StringLiteralExpression
            | SyntaxKind::CharacterLiteralExpression
            | SyntaxKind::TrueLiteralExpression
            | SyntaxKind::FalseLiteralExpression
            | SyntaxKind::ThisExpression
            | SyntaxKind::ObjectCreationExpression
    )
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    #[test]
    fn a_narrowing_number_is_cast() {
        let source = "class C\n{\n    void M(long big, double d)\n    {\n        int i = $$big;\n        int j = d * 2;\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Add explicit cast"),
            "class C\n{\n    void M(long big, double d)\n    {\n        int i = (int)big;\n        int j = d * 2;\n    }\n}\n"
        );
        let product =
            "class C\n{\n    void M(double d)\n    {\n        int j = $$d * 2;\n    }\n}\n";
        assert_eq!(
            fix(&[product], "Add explicit cast"),
            "class C\n{\n    void M(double d)\n    {\n        int j = (int)(d * 2);\n    }\n}\n"
        );
    }

    #[test]
    fn a_base_class_is_cast_down_and_an_argument_too() {
        let source = "class Animal { }\nclass Dog : Animal { }\nclass C\n{\n    void Walk(Dog dog) { }\n\n    void M(Animal a)\n    {\n        Walk($$a);\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Add explicit cast"),
            "class Animal { }\nclass Dog : Animal { }\nclass C\n{\n    void Walk(Dog dog) { }\n\n    void M(Animal a)\n    {\n        Walk((Dog)a);\n    }\n}\n"
        );
    }

    #[test]
    fn unrelated_types_are_not_cast() {
        let source = "class C\n{\n    void M(string s)\n    {\n        int i = $$s;\n    }\n}\n";
        assert!(!titles(&[source]).contains(&"Add explicit cast".to_string()));
    }
}
