//! Add missing cases, add default case, add both: a `switch` over an enum
//! that does not name every member.
//!
//! Roslyn's populate-switch fix, which answers its own analyzer (IDE0010
//! for a statement, IDE0072 for an expression) rather than a compiler
//! error, and so is offered on any such `switch` with the cursor on its
//! head. The missing members, in declaration order, become one section of
//! stacked `case` labels ending in `break;` before the `default` section, or
//! one arm each throwing `NotImplementedException` before the discard arm;
//! a `default:` or `_` arm is added last.

use rustlyn_semantics::{SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::support::{Namer, indent_unit, indentation_at, line_start, newline, starts_line};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.view.root.find_token(context.span.start()) else {
        return;
    };
    let Some(switch) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| {
            matches!(
                node.kind(),
                SyntaxKind::SwitchStatement | SyntaxKind::SwitchExpression
            )
        })
    else {
        return;
    };
    // The head only: from the start to the opening brace.
    let Some(open) = switch.child_token_of_kind(SyntaxKind::OpenBraceToken) else {
        return;
    };
    if context.span.start() > open.span().start() {
        return;
    }
    let Some(governing) = switch.children().find(|child| {
        !matches!(
            child.kind(),
            SyntaxKind::SwitchSection | SyntaxKind::SwitchExpressionArm
        )
    }) else {
        return;
    };
    let ty = context.view.type_of(&governing);
    let view = &*context.view;
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let ty = binder.nullable_underlying(&ty).unwrap_or(ty);
    let Some(enumeration) = ty.symbol() else {
        return;
    };
    if symbols.get(enumeration).type_kind() != Some(TypeKind::Enum) {
        return;
    }
    let members: Vec<String> = symbols
        .get(enumeration)
        .members
        .iter()
        .filter(|member| symbols.get(**member).kind == SymbolKind::Field)
        .map(|member| symbols.get(*member).name.clone())
        .collect();
    let namer = Namer::at(view, &switch);
    let enum_name = namer.name(&Type::named(enumeration));
    let statement = switch.kind() == SyntaxKind::SwitchStatement;
    let (named, has_default) = if statement {
        covered_by_sections(&switch)
    } else {
        covered_by_arms(&switch)
    };
    let missing: Vec<String> = members
        .into_iter()
        .filter(|member| !named.contains(member))
        .collect();
    let code = if statement { "IDE0010" } else { "IDE0072" };
    let text = &context.text;
    let throw = namer.not_implemented_expression();
    let mut choices: Vec<(&str, bool, bool)> = Vec::new();
    if !missing.is_empty() {
        choices.push(("Add missing cases", true, false));
    }
    if !has_default {
        choices.push(("Add default case", false, true));
    }
    if !missing.is_empty() && !has_default {
        choices.push(("Add both", true, true));
    }
    for (title, cases, default) in choices {
        let cases = if cases { missing.as_slice() } else { &[] };
        let edits = if statement {
            section_edits(&switch, text, &enum_name, cases, default)
        } else {
            arm_edits(&switch, text, &enum_name, cases, default, &throw)
        };
        if let Some(edits) = edits {
            found.push(context.local(title, ActionKind::QuickFix, Some(code), edits));
        }
    }
}

/// The last identifier of a label's value: `Red` of `Color.Red`.
fn member_name(node: &SyntaxNode) -> Option<String> {
    node.descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .last()
        .map(|token| token.value_text().to_string())
}

fn covered_by_sections(switch: &SyntaxNode) -> (Vec<String>, bool) {
    let mut named = Vec::new();
    let mut has_default = false;
    for section in switch
        .children()
        .filter(|child| child.kind() == SyntaxKind::SwitchSection)
    {
        for label in section.children() {
            match label.kind() {
                SyntaxKind::DefaultSwitchLabel => has_default = true,
                SyntaxKind::CaseSwitchLabel => named.extend(member_name(&label)),
                SyntaxKind::CasePatternSwitchLabel
                    if label.child_of_kind(SyntaxKind::WhenClause).is_none() =>
                {
                    if label
                        .children()
                        .any(|child| child.kind() == SyntaxKind::DiscardPattern)
                    {
                        has_default = true;
                    } else {
                        named.extend(member_name(&label));
                    }
                }
                _ => {}
            }
        }
    }
    (named, has_default)
}

fn covered_by_arms(switch: &SyntaxNode) -> (Vec<String>, bool) {
    let mut named = Vec::new();
    let mut has_default = false;
    for arm in switch
        .children()
        .filter(|child| child.kind() == SyntaxKind::SwitchExpressionArm)
    {
        if arm.child_of_kind(SyntaxKind::WhenClause).is_some() {
            continue;
        }
        let Some(pattern) = arm.children().next() else {
            continue;
        };
        match pattern.kind() {
            SyntaxKind::DiscardPattern => has_default = true,
            SyntaxKind::VarPattern | SyntaxKind::DeclarationPattern => has_default = true,
            _ => named.extend(member_name(&pattern)),
        }
    }
    (named, has_default)
}

fn section_edits(
    switch: &SyntaxNode,
    text: &str,
    enum_name: &str,
    cases: &[String],
    default: bool,
) -> Option<Vec<TextEdit>> {
    let close = switch.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
    let nl = newline(text);
    let unit = indent_unit(text);
    let sections: Vec<SyntaxNode> = switch
        .children()
        .filter(|child| child.kind() == SyntaxKind::SwitchSection)
        .collect();
    let switch_indent = indentation_at(text, switch.span().start());
    let section_indent = sections.first().map_or_else(
        || format!("{switch_indent}{unit}"),
        |section| indentation_at(text, section.span().start()),
    );
    let body_indent = format!("{section_indent}{unit}");
    let mut edits = Vec::new();
    if !cases.is_empty() {
        let mut block = String::new();
        for case in cases {
            block.push_str(&format!("{section_indent}case {enum_name}.{case}:{nl}"));
        }
        block.push_str(&format!("{body_indent}break;{nl}"));
        let default_section = sections.iter().find(|section| {
            section
                .children()
                .any(|label| label.kind() == SyntaxKind::DefaultSwitchLabel)
        });
        edits.push(match default_section {
            Some(section) => TextEdit::insert(line_start(text, section.span().start()), block),
            None => before_close(text, &close, &switch_indent, block, nl),
        });
    }
    if default {
        let block = format!("{section_indent}default:{nl}{body_indent}break;{nl}");
        edits.push(before_close(text, &close, &switch_indent, block, nl));
    }
    // Two insertions at the same place go in the order made: cases, then
    // `default`.
    if edits.len() == 2 && edits[0].span == edits[1].span {
        let second = edits.pop()?;
        edits[0].text.push_str(&second.text);
    }
    Some(edits)
}

/// Lines inserted before a closing brace: at the start of its line, or on
/// a line of their own when something is in front of it.
fn before_close(
    text: &str,
    close: &rustlyn_syntax::SyntaxToken,
    indent: &str,
    block: String,
    nl: &str,
) -> TextEdit {
    if starts_line(text, close.span().start()) {
        TextEdit::insert(line_start(text, close.span().start()), block)
    } else {
        TextEdit::insert(close.span().start(), format!("{nl}{block}{indent}"))
    }
}

fn arm_edits(
    switch: &SyntaxNode,
    text: &str,
    enum_name: &str,
    cases: &[String],
    default: bool,
    throw: &str,
) -> Option<Vec<TextEdit>> {
    let nl = newline(text);
    let unit = indent_unit(text);
    let arms: Vec<SyntaxNode> = switch
        .children()
        .filter(|child| child.kind() == SyntaxKind::SwitchExpressionArm)
        .collect();
    let close = switch.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
    let open = switch.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
    let multiline = text[open.span().end() as usize..close.span().start() as usize].contains('\n');
    let arm_indent = arms.first().map_or_else(
        || format!("{}{unit}", indentation_at(text, switch.span().start())),
        |arm| indentation_at(text, arm.span().start()),
    );
    let new_arms: Vec<String> = cases
        .iter()
        .map(|case| format!("{enum_name}.{case} => {throw}"))
        .collect();
    let mut edits = Vec::new();
    let discard = arms.iter().find(|arm| {
        arm.children()
            .next()
            .is_some_and(|pattern| pattern.kind() == SyntaxKind::DiscardPattern)
    });
    // The cases go before a discard arm when there is one.
    if let Some(discard) = discard
        && !new_arms.is_empty()
    {
        let inserted = if multiline {
            let lines: Vec<String> = new_arms
                .iter()
                .map(|arm| format!("{arm_indent}{arm},{nl}"))
                .collect();
            TextEdit::insert(line_start(text, discard.span().start()), lines.concat())
        } else {
            let arms: Vec<String> = new_arms.iter().map(|arm| format!("{arm}, ")).collect();
            TextEdit::insert(discard.span().start(), arms.concat())
        };
        return Some(vec![inserted]);
    }
    let mut appended = new_arms;
    if default {
        appended.push(format!("_ => {throw}"));
    }
    if appended.is_empty() {
        return None;
    }
    // Appended after the last arm, which needs a comma after it.
    let last_comma = switch
        .child_tokens()
        .filter(|token| token.kind() == SyntaxKind::CommaToken)
        .last()
        .filter(|comma| {
            arms.last()
                .is_none_or(|arm| comma.span().start() >= arm.span().end())
        });
    let trailing = last_comma.is_some();
    let after = match (&last_comma, arms.last()) {
        (Some(comma), _) => comma.span().end(),
        (None, Some(arm)) => {
            edits.push(TextEdit::insert(arm.span().end(), ","));
            arm.span().end()
        }
        (None, None) => open.span().end(),
    };
    let count = appended.len();
    if multiline {
        let lines: Vec<String> = appended
            .iter()
            .enumerate()
            .map(|(index, arm)| {
                let comma = if index + 1 < count || trailing {
                    ","
                } else {
                    ""
                };
                format!("{nl}{arm_indent}{arm}{comma}")
            })
            .collect();
        edits.push(TextEdit::insert(after, lines.concat()));
    } else {
        let joined = appended.join(", ");
        edits.push(TextEdit::insert(after, format!(" {joined}")));
    }
    // A comma added after the last arm and the new arms at the same place
    // are one insertion.
    if edits.len() == 2 && edits[0].span == edits[1].span {
        let second = edits.pop()?;
        edits[0].text.push_str(&second.text);
    }
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    const COLOR: &str = "enum Color { Red, Green, Blue }\n";

    #[test]
    fn missing_cases_go_before_default() {
        let source = "class C\n{\n    void M(Color c)\n    {\n        $$switch (c)\n        {\n            case Color.Red:\n                break;\n            default:\n                break;\n        }\n    }\n}\n";
        assert_eq!(titles(&[source, COLOR]), ["Add missing cases"]);
        assert_eq!(
            fix(&[source, COLOR], "Add missing cases"),
            "class C\n{\n    void M(Color c)\n    {\n        switch (c)\n        {\n            case Color.Red:\n                break;\n            case Color.Green:\n            case Color.Blue:\n                break;\n            default:\n                break;\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn both_are_added_to_an_incomplete_switch() {
        let source = "class C\n{\n    void M(Color c)\n    {\n        switch ($$c)\n        {\n            case Color.Blue:\n                return;\n        }\n    }\n}\n";
        assert_eq!(
            fix(&[source, COLOR], "Add both"),
            "class C\n{\n    void M(Color c)\n    {\n        switch (c)\n        {\n            case Color.Blue:\n                return;\n            case Color.Red:\n            case Color.Green:\n                break;\n            default:\n                break;\n        }\n    }\n}\n"
        );
        assert_eq!(
            fix(&[source, COLOR], "Add default case"),
            "class C\n{\n    void M(Color c)\n    {\n        switch (c)\n        {\n            case Color.Blue:\n                return;\n            default:\n                break;\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_switch_expression_gets_throwing_arms() {
        let source = "using System;\n\nclass C\n{\n    int M(Color c) => c $$switch\n    {\n        Color.Red => 1,\n        _ => 0,\n    };\n}\n";
        assert_eq!(
            fix(&[source, COLOR], "Add missing cases"),
            "using System;\n\nclass C\n{\n    int M(Color c) => c switch\n    {\n        Color.Red => 1,\n        Color.Green => throw new NotImplementedException(),\n        Color.Blue => throw new NotImplementedException(),\n        _ => 0,\n    };\n}\n"
        );
        let open = "class C\n{\n    int M(Color c) => c $$switch\n    {\n        Color.Red => 1\n    };\n}\n";
        assert_eq!(
            fix(&[open, COLOR], "Add both"),
            "class C\n{\n    int M(Color c) => c switch\n    {\n        Color.Red => 1,\n        Color.Green => throw new System.NotImplementedException(),\n        Color.Blue => throw new System.NotImplementedException(),\n        _ => throw new System.NotImplementedException()\n    };\n}\n"
        );
    }

    #[test]
    fn a_complete_switch_or_one_not_over_an_enum_offers_nothing() {
        let source = "class C\n{\n    void M(Color c)\n    {\n        $$switch (c)\n        {\n            case Color.Red:\n            case Color.Green:\n            case Color.Blue:\n                break;\n            default:\n                break;\n        }\n    }\n}\n";
        assert!(titles(&[source, COLOR]).is_empty());
        let number = "class C\n{\n    void M(int c)\n    {\n        $$switch (c)\n        {\n            case 1:\n                break;\n        }\n    }\n}\n";
        assert!(titles(&[number]).is_empty());
    }
}
