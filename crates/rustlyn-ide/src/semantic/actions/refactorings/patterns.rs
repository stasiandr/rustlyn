//! Type checks, null checks and comparisons written as patterns.
//!
//! Roslyn's pattern-matching code styles and its "Use recursive patterns"
//! refactoring, offered with the cursor in the code they rewrite:
//!
//! * "Use pattern matching" (IDE0019): `var s = o as string;` followed by
//!   `if (s != null)` becomes `if (o is string s)`; followed by
//!   `if (s == null) return;`, it becomes `if (o is not string s) return;`;
//! * "Use pattern matching" (IDE0020, IDE0038): `if (o is Shape) { var s =
//!   (Shape)o; ... }` becomes `if (o is Shape s) { ... }`, and casts of `o`
//!   to the type inside become the new variable;
//! * "Use pattern matching" (IDE0083): `!(o is Shape)` becomes
//!   `o is not Shape`, `!(o is null)` becomes `o is not null`;
//! * "Use pattern matching" (IDE0078): `x == 1 || x == 2` becomes
//!   `x is 1 or 2`, `x >= 0 && x <= 9` becomes `x is >= 0 and <= 9`;
//! * "Use 'is null' check" (IDE0041): `ReferenceEquals(o, null)` and
//!   `(object)o == null` become `o is null`;
//! * "Use recursive patterns": `p != null && p.X == 1 && p.Name == "a"`
//!   becomes `p is { X: 1, Name: "a" }`.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    camel_case, fresh_name, parenthesized_for, same_tokens, skip_parentheses, statements_of,
};
use super::super::{ActionKind, CodeAction, Context};
use super::null_checks::null_test;
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let around: Vec<SyntaxNode> = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| !super::super::text::is_member(node.kind()))
        .collect();
    let offer_once = |context: &Context<'_, '_>,
                      found: &mut Vec<CodeAction>,
                      title: &str,
                      edits: Vec<TextEdit>| {
        if !found.iter().any(|action| action.title == title) {
            found.push(context.local(title, ActionKind::Rewrite, None, edits));
        }
    };
    for node in &around {
        let edits = match node.kind() {
            SyntaxKind::LocalDeclarationStatement => as_then_null_check(context, node),
            SyntaxKind::IfStatement => {
                as_then_null_check_from_if(context, node).or_else(|| is_then_cast(context, node))
            }
            SyntaxKind::LogicalNotExpression => negated_is(node).map(|edit| vec![edit]),
            SyntaxKind::LogicalOrExpression | SyntaxKind::LogicalAndExpression => {
                comparisons(context, node).map(|edit| vec![edit])
            }
            _ => None,
        };
        if let Some(edits) = edits {
            offer_once(context, found, "Use pattern matching", edits);
            break;
        }
    }
    if let Some(edit) = around.iter().find_map(is_null_check) {
        offer_once(context, found, "Use 'is null' check", vec![edit]);
    }
    if let Some(chain) = around
        .iter()
        .rev()
        .find(|node| node.kind() == SyntaxKind::LogicalAndExpression)
        && let Some(edit) = recursive(context, chain)
    {
        offer_once(context, found, "Use recursive patterns", vec![edit]);
    }
}

/// The names in `node` spelled `name`.
fn mentions(node: &SyntaxNode, name: &str) -> bool {
    node.descendant_tokens()
        .any(|token| token.kind() == SyntaxKind::IdentifierToken && token.value_text() == name)
}

/// Whether a statement always leaves: a `return`, `throw`, `break` or
/// `continue`, or a block that ends with one.
fn always_leaves(statement: &SyntaxNode) -> bool {
    match statement.kind() {
        SyntaxKind::ReturnStatement
        | SyntaxKind::ThrowStatement
        | SyntaxKind::BreakStatement
        | SyntaxKind::ContinueStatement => true,
        SyntaxKind::Block => statements_of(statement).last().is_some_and(always_leaves),
        _ => false,
    }
}

/// `var s = o as string;` then `if (s != null)` or `if (s == null)
/// return;`.
fn as_then_null_check(
    context: &Context<'_, '_>,
    declaration: &SyntaxNode,
) -> Option<Vec<TextEdit>> {
    let block = declaration.parent()?;
    let statements = statements_of(block);
    let at = statements
        .iter()
        .position(|statement| statement == declaration)?;
    let next = statements.get(at + 1)?;
    as_pair(context, declaration, next, &statements[at + 2..])
}

fn as_then_null_check_from_if(
    context: &Context<'_, '_>,
    statement: &SyntaxNode,
) -> Option<Vec<TextEdit>> {
    let block = statement.parent()?;
    let statements = statements_of(block);
    let at = statements.iter().position(|other| other == statement)?;
    let declaration = statements.get(at.checked_sub(1)?)?;
    if declaration.kind() != SyntaxKind::LocalDeclarationStatement {
        return None;
    }
    as_pair(context, declaration, statement, &statements[at + 1..])
}

fn as_pair(
    context: &Context<'_, '_>,
    declaration: &SyntaxNode,
    statement: &SyntaxNode,
    after: &[SyntaxNode],
) -> Option<Vec<TextEdit>> {
    if statement.kind() != SyntaxKind::IfStatement {
        return None;
    }
    let variable = declaration.child_of_kind(SyntaxKind::VariableDeclaration)?;
    let declarators: Vec<SyntaxNode> = variable
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let [declarator] = declarators.as_slice() else {
        return None;
    };
    let name = declarator
        .child_token_of_kind(SyntaxKind::IdentifierToken)?
        .value_text()
        .to_string();
    let value = skip_parentheses(
        &declarator
            .child_of_kind(SyntaxKind::EqualsValueClause)?
            .children()
            .next()?,
    );
    if value.kind() != SyntaxKind::AsExpression {
        return None;
    }
    let mut sides = value.children();
    let (tested, ty) = (sides.next()?, sides.next()?);
    if ty.kind() == SyntaxKind::NullableType {
        return None;
    }
    let condition = statement.children().next()?;
    let (checked, is_equal) = null_test(&condition)?;
    if skip_parentheses(&checked).text() != name {
        return None;
    }
    let operand = parenthesized_for(&tested.text(), skip_parentheses(&tested).kind(), &condition);
    let pattern = if is_equal {
        // `if (s == null) return;`: `s` is assigned after it.
        let body = statement.children().nth(1)?;
        if !always_leaves(&body) || statement.child_of_kind(SyntaxKind::ElseClause).is_some() {
            return None;
        }
        format!("{operand} is not {} {name}", ty.text())
    } else {
        // `if (s != null) { ... }`: `s` is assigned only inside it.
        if after.iter().any(|later| mentions(later, &name))
            || statement
                .child_of_kind(SyntaxKind::ElseClause)
                .is_some_and(|clause| mentions(&clause, &name))
        {
            return None;
        }
        format!("{operand} is {} {name}", ty.text())
    };
    let _ = context;
    Some(vec![
        TextEdit::delete(TextSpan::from_bounds(
            declaration.span().start(),
            statement.span().start(),
        )),
        TextEdit::new(condition.span(), pattern),
    ])
}

/// `if (o is Shape) { var s = (Shape)o; ... ((Shape)o).M(); }` → `if (o is
/// Shape s) { ... s.M(); }`.
fn is_then_cast(context: &mut Context<'_, '_>, statement: &SyntaxNode) -> Option<Vec<TextEdit>> {
    let condition = statement.children().next()?;
    if condition.kind() != SyntaxKind::IsExpression {
        return None;
    }
    let mut sides = condition.children();
    let (tested, ty) = (sides.next()?, sides.next()?);
    if tested.kind() != SyntaxKind::IdentifierName || ty.kind() == SyntaxKind::NullableType {
        return None;
    }
    let body = statement.children().nth(1)?;
    // `o` is not assigned in the body: the variable stands for it there.
    if body.descendants().any(|node| {
        node.kind() == SyntaxKind::IdentifierName
            && node.text() == tested.text()
            && super::super::text::is_written(&node)
    }) {
        return None;
    }
    let casts: Vec<SyntaxNode> = body
        .descendants()
        .filter(|node| {
            node.kind() == SyntaxKind::CastExpression
                && node
                    .children()
                    .next()
                    .is_some_and(|cast_to| same_tokens(&cast_to, &ty))
                && node
                    .children()
                    .nth(1)
                    .is_some_and(|value| same_tokens(&skip_parentheses(&value), &tested))
        })
        .collect();
    if casts.is_empty() {
        return None;
    }
    let mut edits = Vec::new();
    // `var s = (Shape)o;` as the first statement names the variable.
    let first = statements_of(&body).first().cloned().filter(|first| {
        first.kind() == SyntaxKind::LocalDeclarationStatement
            && first
                .descendants()
                .find(|node| node.kind() == SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().next())
                .is_some_and(|value| casts.contains(&skip_parentheses(&value)))
            && first
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                .count()
                == 1
    });
    let name = match &first {
        Some(declaration) => {
            let name = declaration
                .descendants()
                .find(|node| node.kind() == SyntaxKind::VariableDeclarator)?
                .child_token_of_kind(SyntaxKind::IdentifierToken)?
                .value_text()
                .to_string();
            let next = statements_of(&body).get(1).map_or_else(
                || {
                    body.child_token_of_kind(SyntaxKind::CloseBraceToken)
                        .map(|brace| brace.span().start())
                },
                |next| Some(next.span().start()),
            )?;
            edits.push(TextEdit::delete(TextSpan::from_bounds(
                declaration.span().start(),
                next,
            )));
            // The brace's own line keeps its indentation.
            if statements_of(&body).len() == 1 {
                let text = &context.text;
                let line = super::super::text::line_start(text, declaration.span().start());
                edits.pop();
                edits.push(TextEdit::delete(TextSpan::from_bounds(
                    line,
                    super::super::text::line_start(text, next),
                )));
            }
            name
        }
        None => {
            let taken = context.view.names_near(statement);
            let base = camel_case(ty.text().rsplit('.').next().unwrap_or("value"));
            fresh_name(&base, &taken)
        }
    };
    for cast in &casts {
        if first
            .as_ref()
            .is_some_and(|declaration| declaration.span().contains(cast.span().start()))
        {
            continue;
        }
        let at = if cast
            .parent()
            .is_some_and(|parent| parent.kind() == SyntaxKind::ParenthesizedExpression)
        {
            cast.parent()?.span()
        } else {
            cast.span()
        };
        edits.push(TextEdit::new(at, name.clone()));
    }
    edits.push(TextEdit::insert(ty.span().end(), format!(" {name}")));
    Some(edits)
}

/// `!(o is Shape)` → `o is not Shape`; `!(o is null)` → `o is not null`.
fn negated_is(node: &SyntaxNode) -> Option<TextEdit> {
    let inner = node.children().next()?;
    if inner.kind() != SyntaxKind::ParenthesizedExpression {
        return None;
    }
    let test = skip_parentheses(&inner);
    let mut sides = test.children();
    let (tested, pattern) = (sides.next()?, sides.next()?);
    let rewritten = match test.kind() {
        SyntaxKind::IsExpression => format!("{} is not {}", tested.text(), pattern.text()),
        SyntaxKind::IsPatternExpression
            if matches!(
                pattern.kind(),
                SyntaxKind::ConstantPattern | SyntaxKind::TypePattern
            ) =>
        {
            format!("{} is not {}", tested.text(), pattern.text())
        }
        _ => return None,
    };
    Some(TextEdit::new(
        node.span(),
        parenthesized_for(&rewritten, SyntaxKind::IsPatternExpression, node),
    ))
}

/// A constant a pattern can hold: a literal, a negated number, or a name
/// the binder says is a constant.
fn is_constant(context: &mut Context<'_, '_>, node: &SyntaxNode) -> bool {
    let node = skip_parentheses(node);
    match node.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression => true,
        SyntaxKind::UnaryMinusExpression => node
            .children()
            .next()
            .is_some_and(|operand| operand.kind() == SyntaxKind::NumericLiteralExpression),
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::IdentifierName => {
            let Some(name) = node
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .last()
            else {
                return false;
            };
            let Some(crate::semantic::Resolved::Symbol(symbol)) = context.view.resolve(&name)
            else {
                return false;
            };
            let symbols = context.view.compiled().symbols();
            let found = symbols.get(symbol);
            found
                .modifiers
                .contains(rustlyn_semantics::Modifiers::CONST)
                || (found.kind == rustlyn_semantics::SymbolKind::Field
                    && found.container.is_some_and(|container| {
                        symbols.get(container).type_kind()
                            == Some(rustlyn_semantics::TypeKind::Enum)
                    }))
        }
        _ => false,
    }
}

/// The operands of a chain of `op`: `a || b || c` → `[a, b, c]`.
fn chain(node: &SyntaxNode, kind: SyntaxKind) -> Vec<SyntaxNode> {
    let node = skip_parentheses(node);
    if node.kind() != kind {
        return vec![node];
    }
    node.children()
        .flat_map(|child| chain(&child, kind))
        .collect()
}

/// The relational pattern one comparison of `tested` with a constant is:
/// `x == 1` → `1`, `x >= 0` → `>= 0`, `0 < x` → `> 0`.
fn relational(
    context: &mut Context<'_, '_>,
    comparison: &SyntaxNode,
) -> Option<(SyntaxNode, String)> {
    let comparison = skip_parentheses(comparison);
    let operator = match comparison.kind() {
        SyntaxKind::EqualsExpression => "",
        SyntaxKind::LessThanExpression => "<",
        SyntaxKind::LessThanOrEqualExpression => "<=",
        SyntaxKind::GreaterThanExpression => ">",
        SyntaxKind::GreaterThanOrEqualExpression => ">=",
        _ => return None,
    };
    let mut sides = comparison.children();
    let (left, right) = (sides.next()?, sides.next()?);
    if is_constant(context, &right) && !is_constant(context, &left) {
        let pattern = if operator.is_empty() {
            right.text()
        } else {
            format!("{operator} {}", right.text())
        };
        return Some((left, pattern));
    }
    if is_constant(context, &left) && !is_constant(context, &right) {
        let flipped = match operator {
            "<" => ">",
            "<=" => ">=",
            ">" => "<",
            ">=" => "<=",
            other => other,
        };
        let pattern = if flipped.is_empty() {
            left.text()
        } else {
            format!("{flipped} {}", left.text())
        };
        return Some((right, pattern));
    }
    None
}

/// `x == 1 || x == 2` → `x is 1 or 2`; `x >= 0 && x <= 9` → `x is >= 0 and
/// <= 9`.
fn comparisons(context: &mut Context<'_, '_>, node: &SyntaxNode) -> Option<TextEdit> {
    // The whole chain of the operator, not a part of it.
    if node
        .parent()
        .is_some_and(|parent| parent.kind() == node.kind())
    {
        return None;
    }
    let operands = chain(node, node.kind());
    if operands.len() < 2 {
        return None;
    }
    let mut tested: Option<SyntaxNode> = None;
    let mut patterns = Vec::new();
    for operand in &operands {
        let (left, pattern) = relational(context, operand)?;
        match &tested {
            Some(first) if !same_tokens(first, &left) => return None,
            Some(_) => {}
            None => {
                // Evaluated once instead of once per comparison: only a
                // name or a member access, which reading twice does not
                // change.
                if !matches!(
                    skip_parentheses(&left).kind(),
                    SyntaxKind::IdentifierName | SyntaxKind::SimpleMemberAccessExpression
                ) {
                    return None;
                }
                tested = Some(left);
            }
        }
        patterns.push(pattern);
    }
    let joiner = if node.kind() == SyntaxKind::LogicalOrExpression {
        " or "
    } else {
        " and "
    };
    let rewritten = format!("{} is {}", tested?.text(), patterns.join(joiner));
    Some(TextEdit::new(
        node.span(),
        parenthesized_for(&rewritten, SyntaxKind::IsPatternExpression, node),
    ))
}

/// `ReferenceEquals(o, null)`, `object.ReferenceEquals(null, o)` and
/// `(object)o == null` → `o is null`; `!=` → `o is not null`.
fn is_null_check(node: &SyntaxNode) -> Option<TextEdit> {
    match node.kind() {
        SyntaxKind::InvocationExpression => {
            let callee = node.children().next()?;
            let name = callee
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .last()?;
            if name.value_text() != "ReferenceEquals"
                || !(callee.kind() == SyntaxKind::IdentifierName
                    || callee.text().replace(' ', "") == "object.ReferenceEquals")
            {
                return None;
            }
            let arguments: Vec<SyntaxNode> = node
                .child_of_kind(SyntaxKind::ArgumentList)?
                .children()
                .filter(|child| child.kind() == SyntaxKind::Argument)
                .filter_map(|argument| argument.children().last())
                .collect();
            let [first, second] = arguments.as_slice() else {
                return None;
            };
            let null = |node: &SyntaxNode| {
                skip_parentheses(node).kind() == SyntaxKind::NullLiteralExpression
            };
            let tested = if null(second) {
                first
            } else if null(first) {
                second
            } else {
                return None;
            };
            let (at, negated) = match node.parent() {
                Some(parent) if parent.kind() == SyntaxKind::LogicalNotExpression => {
                    (parent.clone(), true)
                }
                _ => (node.clone(), false),
            };
            let rewritten = format!(
                "{} is {}null",
                parenthesized_for(&tested.text(), skip_parentheses(tested).kind(), &at),
                if negated { "not " } else { "" }
            );
            Some(TextEdit::new(
                at.span(),
                parenthesized_for(&rewritten, SyntaxKind::IsPatternExpression, &at),
            ))
        }
        SyntaxKind::EqualsExpression | SyntaxKind::NotEqualsExpression => {
            let (tested, is_equal) = null_test(node)?;
            let tested = skip_parentheses(&tested);
            if tested.kind() != SyntaxKind::CastExpression
                || tested
                    .children()
                    .next()
                    .is_none_or(|ty| ty.text() != "object")
            {
                return None;
            }
            let value = tested.children().nth(1)?;
            let rewritten = format!(
                "{} is {}null",
                value.text(),
                if is_equal { "" } else { "not " }
            );
            Some(TextEdit::new(
                node.span(),
                parenthesized_for(&rewritten, SyntaxKind::IsPatternExpression, node),
            ))
        }
        _ => None,
    }
}

/// `p != null && p.X == 1 && p.Name == "a"` → `p is { X: 1, Name: "a" }`.
fn recursive(context: &mut Context<'_, '_>, node: &SyntaxNode) -> Option<TextEdit> {
    let operands = chain(node, SyntaxKind::LogicalAndExpression);
    if operands.len() < 2 {
        return None;
    }
    let mut receiver: Option<SyntaxNode> = None;
    let mut properties: Vec<String> = Vec::new();
    let mut not_null = false;
    for operand in &operands {
        // `p != null` checks the receiver; `p.Name != null` is a property.
        if let Some((tested, false)) = null_test(operand)
            && skip_parentheses(&tested).kind() != SyntaxKind::SimpleMemberAccessExpression
        {
            let tested = skip_parentheses(&tested);
            match &receiver {
                Some(first) if !same_tokens(first, &tested) => return None,
                Some(_) => {}
                None => receiver = Some(tested),
            }
            not_null = true;
            continue;
        }
        let comparison = skip_parentheses(operand);
        let (left, pattern) = match comparison.kind() {
            SyntaxKind::EqualsExpression => relational(context, &comparison)?,
            SyntaxKind::NotEqualsExpression => match null_test(&comparison)? {
                (tested, false) => (tested, "not null".to_string()),
                _ => return None,
            },
            SyntaxKind::IsPatternExpression => {
                let mut parts = comparison.children();
                (parts.next()?, parts.next()?.text())
            }
            _ => return None,
        };
        let left = skip_parentheses(&left);
        if left.kind() != SyntaxKind::SimpleMemberAccessExpression {
            return None;
        }
        let mut parts = left.children();
        let (object, member) = (parts.next()?, parts.next()?);
        if member.kind() != SyntaxKind::IdentifierName {
            return None;
        }
        match &receiver {
            Some(first) if !same_tokens(first, &skip_parentheses(&object)) => return None,
            Some(_) => {}
            None => receiver = Some(skip_parentheses(&object)),
        }
        properties.push(format!("{}: {pattern}", member.text()));
    }
    let receiver = receiver?;
    if properties.is_empty() || (properties.len() < 2 && !not_null) {
        return None;
    }
    if !matches!(
        receiver.kind(),
        SyntaxKind::IdentifierName
            | SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::ThisExpression
    ) {
        return None;
    }
    let rewritten = format!("{} is {{ {} }}", receiver.text(), properties.join(", "));
    Some(TextEdit::new(
        node.span(),
        parenthesized_for(&rewritten, SyntaxKind::IsPatternExpression, node),
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn as_and_a_null_check_become_a_pattern() {
        let source = "class C\n{\n    int M(object o)\n    {\n        var s = o $$as string;\n        if (s != null)\n        {\n            return s.Length;\n        }\n        return 0;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use pattern matching"),
            "class C\n{\n    int M(object o)\n    {\n        if (o is string s)\n        {\n            return s.Length;\n        }\n        return 0;\n    }\n}\n"
        );
        let source = "class C\n{\n    int M(object o)\n    {\n        string s = o as string;\n        $$if (s == null) return 0;\n        return s.Length;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use pattern matching"),
            "class C\n{\n    int M(object o)\n    {\n        if (o is not string s) return 0;\n        return s.Length;\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    int M(object o)\n    {\n        var s = o $$as string;\n        if (s != null) { }\n        return s.Length;\n    }\n}\n",
            "Use pattern matching",
        );
    }

    #[test]
    fn a_type_check_and_casts_become_a_pattern() {
        let source = "class Shape { public int Sides; }\nclass C\n{\n    int M(object o)\n    {\n        $$if (o is Shape)\n        {\n            var shape = (Shape)o;\n            return shape.Sides + ((Shape)o).Sides;\n        }\n        return 0;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use pattern matching"),
            "class Shape { public int Sides; }\nclass C\n{\n    int M(object o)\n    {\n        if (o is Shape shape)\n        {\n            return shape.Sides + shape.Sides;\n        }\n        return 0;\n    }\n}\n"
        );
    }

    #[test]
    fn negations_comparisons_and_reference_checks() {
        assert_eq!(
            apply(
                "class C\n{\n    bool M(object o) => $$!(o is string);\n}\n",
                "Use pattern matching"
            ),
            "class C\n{\n    bool M(object o) => o is not string;\n}\n"
        );
        assert_eq!(
            apply(
                "class C\n{\n    bool M(int x) => x == 1 $$|| x == 2 || x == 3;\n}\n",
                "Use pattern matching"
            ),
            "class C\n{\n    bool M(int x) => x is 1 or 2 or 3;\n}\n"
        );
        assert_eq!(
            apply(
                "class C\n{\n    bool M(char c) => c >= 'a' $$&& c <= 'z';\n}\n",
                "Use pattern matching"
            ),
            "class C\n{\n    bool M(char c) => c is >= 'a' and <= 'z';\n}\n"
        );
        assert_eq!(
            apply(
                "class C\n{\n    bool M(C c) => !$$ReferenceEquals(c, null);\n}\n",
                "Use 'is null' check"
            ),
            "class C\n{\n    bool M(C c) => c is not null;\n}\n"
        );
        assert_eq!(
            apply(
                "class C\n{\n    bool M(C c) => (object)c $$== null;\n}\n",
                "Use 'is null' check"
            ),
            "class C\n{\n    bool M(C c) => c is null;\n}\n"
        );
    }

    #[test]
    fn member_checks_become_a_recursive_pattern() {
        assert_eq!(
            apply(
                "class P\n{\n    public string Name;\n    bool M(P p) => p != null $$&& p.Name != null;\n}\n",
                "Use recursive patterns"
            ),
            "class P\n{\n    public string Name;\n    bool M(P p) => p is { Name: not null };\n}\n"
        );
        let source = "enum Kind { A, B }\nclass P\n{\n    public int X;\n    public Kind K;\n    public string Name;\n    bool M(P p) => p != null && p.X == 1 $$&& p.K == Kind.B && p.Name is not null;\n}\n";
        assert_eq!(
            apply(source, "Use recursive patterns"),
            "enum Kind { A, B }\nclass P\n{\n    public int X;\n    public Kind K;\n    public string Name;\n    bool M(P p) => p is { X: 1, K: Kind.B, Name: not null };\n}\n"
        );
        refuses(
            "class P\n{\n    public int X;\n    bool M(P p, int y) => p.X == 1 $$&& p.X == y;\n}\n",
            "Use recursive patterns",
        );
    }
}
