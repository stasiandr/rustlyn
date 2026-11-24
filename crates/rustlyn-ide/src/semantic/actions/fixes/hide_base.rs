//! Hide base member, and add `override`: a member that has the name of an
//! inherited one and does not say what it means by it.
//!
//! The binder reports neither CS0108 (a member hides an inherited one) nor
//! CS0114 (it hides a virtual one, which it could override instead), so the
//! provider looks with the cursor on a member's name: a class it derives
//! from has a member of the same name that it can see — for a method, with
//! the same parameters — and the member says neither `new` nor `override`.
//! "Hide base member" is Roslyn's fix, adding `new`; for CS0114 adding
//! `override` is offered as well. Either goes where Roslyn's default
//! modifier order puts it.

use std::collections::HashMap;

use rustlyn_semantics::{Accessibility, Modifiers, SymbolId, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::implement::same_signature;
use crate::edit::TextEdit;
use crate::semantic::View;

/// Roslyn's default `csharp_preferred_modifier_order`.
const ORDER: &[&str] = &[
    "public",
    "private",
    "protected",
    "internal",
    "file",
    "static",
    "extern",
    "new",
    "virtual",
    "abstract",
    "sealed",
    "override",
    "readonly",
    "unsafe",
    "required",
    "volatile",
    "async",
];

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.view.name_token_at(context.span.start()) else {
        return;
    };
    let declared = token.parent().clone();
    let holder = match declared.kind() {
        SyntaxKind::MethodDeclaration
        | SyntaxKind::PropertyDeclaration
        | SyntaxKind::EventDeclaration => declared.clone(),
        SyntaxKind::VariableDeclarator => {
            match declared
                .parent()
                .and_then(|declaration| declaration.parent())
            {
                Some(field)
                    if matches!(
                        field.kind(),
                        SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                    ) =>
                {
                    field.clone()
                }
                _ => return,
            }
        }
        _ => return,
    };
    let view = &*context.view;
    let Some(member) = view.model.declared_symbol(&declared) else {
        return;
    };
    let symbols = view.compilation().symbols();
    let modifiers = symbols.get(member).modifiers;
    if modifiers.contains(Modifiers::NEW) || modifiers.contains(Modifiers::OVERRIDE) {
        return;
    }
    let Some(class) = symbols.get(member).container else {
        return;
    };
    let Some(hidden) = hidden_member(view, class, member) else {
        return;
    };
    let hidden_modifiers = symbols.get(hidden).modifiers;
    let overridable = symbols.get(hidden).kind == symbols.get(member).kind
        && matches!(
            symbols.get(member).kind,
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
        )
        && !modifiers.contains(Modifiers::STATIC)
        && (hidden_modifiers.contains(Modifiers::VIRTUAL)
            || hidden_modifiers.contains(Modifiers::ABSTRACT)
            || hidden_modifiers.contains(Modifiers::OVERRIDE))
        && !hidden_modifiers.contains(Modifiers::SEALED);
    let code = if overridable { "CS0114" } else { "CS0108" };
    if let Some(edit) = add_modifier(&holder, "new") {
        found.push(context.local(
            "Hide base member",
            ActionKind::QuickFix,
            Some(code),
            vec![edit],
        ));
    }
    if overridable {
        let virtual_token = holder
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::VirtualKeyword);
        let edit = match virtual_token {
            Some(token) => Some(TextEdit::new(token.span(), "override")),
            None => add_modifier(&holder, "override"),
        };
        if let Some(edit) = edit {
            found.push(context.local(
                "Add 'override' modifier",
                ActionKind::QuickFix,
                Some(code),
                vec![edit],
            ));
        }
    }
}

/// The member of a class `class` derives from that `member` hides.
fn hidden_member(view: &View<'_>, class: SymbolId, member: SymbolId) -> Option<SymbolId> {
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let name = &symbols.get(member).name;
    let mut current = class;
    let mut map: HashMap<SymbolId, rustlyn_semantics::Type> = HashMap::new();
    for _ in 0..32 {
        let base = binder.base_class_of(current)?.substitute(&map);
        let symbol = base.symbol()?;
        map = binder.type_substitution(&base);
        for &candidate in symbols.lookup(symbol, name) {
            let found = symbols.get(candidate);
            if found.accessibility == Accessibility::Private
                || !matches!(
                    found.kind,
                    SymbolKind::Method
                        | SymbolKind::Property
                        | SymbolKind::Event
                        | SymbolKind::Field
                )
            {
                continue;
            }
            let both_methods =
                found.kind == SymbolKind::Method && symbols.get(member).kind == SymbolKind::Method;
            if !both_methods || same_signature(view, member, &HashMap::new(), candidate, &map) {
                return Some(candidate);
            }
        }
        current = symbol;
    }
    None
}

/// The edit that adds `modifier` to a declaration, in Roslyn's order among
/// the modifiers it has.
fn add_modifier(holder: &SyntaxNode, modifier: &str) -> Option<TextEdit> {
    let rank = |word: &str| ORDER.iter().position(|known| *known == word);
    let wanted = rank(modifier)?;
    let modifiers: Vec<_> = holder
        .child_tokens()
        .filter(|token| rank(token.text()).is_some() || token.text() == "partial")
        .collect();
    if let Some(after) = modifiers
        .iter()
        .find(|token| rank(token.text()).is_some_and(|at| at > wanted))
    {
        return Some(TextEdit::insert(
            after.span().start(),
            format!("{modifier} "),
        ));
    }
    if let Some(last) = modifiers.last() {
        return Some(TextEdit::insert(last.span().end(), format!(" {modifier}")));
    }
    // No modifiers: in front of what follows the attributes.
    let first = holder
        .children_with_tokens()
        .find(|element| element.kind() != SyntaxKind::AttributeList)?;
    Some(TextEdit::insert(
        first.span().start(),
        format!("{modifier} "),
    ))
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    const BASE: &str = "class Base\n{\n    public virtual void Run() { }\n    public void Stop() { }\n    protected int count;\n}\n";

    #[test]
    fn a_virtual_member_can_be_hidden_or_overridden() {
        let source = "class Derived : Base\n{\n    public void $$Run() { }\n}\n";
        assert_eq!(
            fix(&[source, BASE], "Hide base member"),
            "class Derived : Base\n{\n    public new void Run() { }\n}\n"
        );
        assert_eq!(
            fix(&[source, BASE], "Add 'override' modifier"),
            "class Derived : Base\n{\n    public override void Run() { }\n}\n"
        );
    }

    #[test]
    fn a_plain_member_or_field_can_only_be_hidden() {
        let source = "class Derived : Base\n{\n    void $$Stop() { }\n}\n";
        // `Stop` is also a private member nobody calls, which IDE0051 offers
        // to remove; what matters here is that it is not offered an override.
        let offered: Vec<String> = titles(&[source, BASE])
            .into_iter()
            .filter(|title| title != "Remove unused member" && title != "Make static")
            .collect();
        assert_eq!(offered, ["Hide base member"]);
        assert_eq!(
            fix(&[source, BASE], "Hide base member"),
            "class Derived : Base\n{\n    new void Stop() { }\n}\n"
        );
        let field = "class Derived : Base\n{\n    private static string $$count;\n}\n";
        assert_eq!(
            fix(&[field, BASE], "Hide base member"),
            "class Derived : Base\n{\n    private static new string count;\n}\n"
        );
    }

    #[test]
    fn an_overload_or_a_member_that_says_so_is_not_hiding() {
        let overload = "class Derived : Base\n{\n    public void $$Run(int times) { }\n}\n";
        // Refactorings of the method aside.
        assert!(
            titles(&[overload, BASE])
                .iter()
                .all(|title| title == "Make static")
        );
        let said = "class Derived : Base\n{\n    public override void $$Run() { }\n}\n";
        assert!(titles(&[said, BASE]).is_empty());
    }
}
