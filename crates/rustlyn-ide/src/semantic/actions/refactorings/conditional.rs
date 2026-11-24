//! Convert to conditional expression, convert to 'if' statement: an `if`
//! that returns or assigns one of two values, and `c ? a : b` doing the
//! same.
//!
//! Roslyn's `UseConditionalExpressionForReturn` and
//! `UseConditionalExpressionForAssignment` (IDE0045, IDE0046), and
//! `ConvertConditionalOperatorToIf` the other way. An `if` converts when
//! both branches are one statement returning a value, or both assign to the
//! same target with `=`; an `if` without an `else` followed by a `return`
//! counts as one with it. A conditional converts where it is the whole of a
//! `return`, of the right of an assignment statement, or of a local's
//! initializer — the local is then declared first, with its type written
//! out, and assigned in each branch.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{precedence, reindent, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use super::expression_body::block;
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    if let Some(statement) = super::invert_if::if_at_cursor(context)
        && let Some(edit) = to_conditional(&statement)
    {
        found.push(context.local(
            "Convert to conditional expression",
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
    if let Some(edits) = to_if(context) {
        found.push(context.local(
            "Convert to 'if' statement",
            ActionKind::Refactor,
            None,
            edits,
        ));
    }
}

/// The one statement a branch is, braces or not.
fn single(statement: &SyntaxNode) -> Option<SyntaxNode> {
    if statement.kind() == SyntaxKind::Block {
        let statements = statements_of(statement);
        match statements.as_slice() {
            [only] => Some(only.clone()),
            _ => None,
        }
    } else {
        Some(statement.clone())
    }
}

/// What a branch does: returns a value, or assigns one to a target.
enum Branch {
    Return(SyntaxNode),
    Assign(String, SyntaxNode),
}

fn branch(statement: &SyntaxNode) -> Option<Branch> {
    let statement = single(statement)?;
    let expression = statement
        .children()
        .find(|child| child.kind().is_expression())?;
    match statement.kind() {
        SyntaxKind::ReturnStatement => Some(Branch::Return(expression)),
        SyntaxKind::ExpressionStatement
            if expression.kind() == SyntaxKind::SimpleAssignmentExpression =>
        {
            let mut sides = expression.children();
            let target = sides.next()?;
            Some(Branch::Assign(target.text(), sides.next()?))
        }
        _ => None,
    }
}

/// An operand of `?:`, in parentheses where it would otherwise bind
/// differently: an assignment, a lambda, another conditional as the test.
fn operand(node: &SyntaxNode, is_condition: bool) -> String {
    let limit = if is_condition {
        precedence(SyntaxKind::CoalesceExpression)
    } else {
        precedence(SyntaxKind::ConditionalExpression)
    };
    if precedence(node.kind()) < limit {
        format!("({})", node.text())
    } else {
        node.text()
    }
}

fn to_conditional(statement: &SyntaxNode) -> Option<TextEdit> {
    let condition = statement
        .children()
        .find(|child| child.kind().is_expression())?;
    let consequence = statement
        .children()
        .find(|child| super::super::text::is_statement(child.kind()))?;
    let mut end = statement.span().end();
    let alternative = match statement.child_of_kind(SyntaxKind::ElseClause) {
        Some(clause) => clause.children().next()?,
        None => {
            let parent = statement.parent()?;
            let statements = statements_of(parent);
            let at = statements.iter().position(|other| other == statement)?;
            let next = statements.get(at + 1)?.clone();
            end = next.span().end();
            next
        }
    };
    let condition = operand(&condition, true);
    let text = match (branch(&consequence)?, branch(&alternative)?) {
        (Branch::Return(yes), Branch::Return(no)) => {
            format!(
                "return {condition} ? {} : {};",
                operand(&yes, false),
                operand(&no, false)
            )
        }
        (Branch::Assign(target, yes), Branch::Assign(other, no))
            if target == other && statement.child_of_kind(SyntaxKind::ElseClause).is_some() =>
        {
            format!(
                "{target} = {condition} ? {} : {};",
                operand(&yes, false),
                operand(&no, false)
            )
        }
        _ => return None,
    };
    Some(TextEdit::new(
        TextSpan::from_bounds(statement.span().start(), end),
        text,
    ))
}

fn to_if(context: &mut Context<'_, '_>) -> Option<Vec<TextEdit>> {
    let token = context.token_at_cursor()?;
    let conditional = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| node.kind() == SyntaxKind::ConditionalExpression)?;
    let parts: Vec<SyntaxNode> = conditional.children().collect();
    let [condition, yes, no] = parts.as_slice() else {
        return None;
    };
    let parent = conditional.parent()?;
    let indent = context.indentation_at(conditional.span().start());
    let newline = context.newline();
    let unit = context.indent_unit();
    let inner = format!("{indent}{unit}");
    let arm = |text: String| reindent(&text, &indent, &inner);
    let (statement, prefix, before) = match parent.kind() {
        SyntaxKind::ReturnStatement => (parent.clone(), "return ".to_string(), String::new()),
        SyntaxKind::SimpleAssignmentExpression
            if parent.children().last().as_ref() == Some(&conditional)
                && parent.parent().is_some_and(|statement| {
                    statement.kind() == SyntaxKind::ExpressionStatement
                }) =>
        {
            let target = parent.children().next()?.text();
            (
                parent.parent()?.clone(),
                format!("{target} = "),
                String::new(),
            )
        }
        SyntaxKind::EqualsValueClause => {
            let declarator = parent.parent()?;
            let declaration = declarator.parent()?;
            let statement = declaration.parent()?;
            let declarators = declaration
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                .count();
            if declarator.kind() != SyntaxKind::VariableDeclarator
                || statement.kind() != SyntaxKind::LocalDeclarationStatement
                || declarators != 1
                || statement.child_tokens().any(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::ConstKeyword | SyntaxKind::UsingKeyword
                    )
                })
            {
                return None;
            }
            let name = declarator.child_token_of_kind(SyntaxKind::IdentifierToken)?;
            let Resolved::Local { ty, .. } = context.view.resolve(&name)? else {
                return None;
            };
            let written = context.view.display_type(&ty, declarator)?;
            (
                statement.clone(),
                format!("{} = ", name.value_text()),
                format!("{written} {};{newline}{indent}", name.value_text()),
            )
        }
        _ => return None,
    };
    let yes = block(context, &indent, &format!("{prefix}{};", arm(yes.text())));
    let no = block(context, &indent, &format!("{prefix}{};", arm(no.text())));
    let text = format!(
        "{before}if ({}){yes}{newline}{indent}else{no}",
        condition.text()
    );
    Some(vec![TextEdit::new(statement.span(), text)])
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn returns_on_both_branches_become_one() {
        let source = "class C\n{\n    int M(bool b)\n    {\n        $$if (b)\n        {\n            return 1;\n        }\n        else\n        {\n            return 2;\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to conditional expression"),
            "class C\n{\n    int M(bool b)\n    {\n        return b ? 1 : 2;\n    }\n}\n"
        );
        let following = "class C\n{\n    int M(int a)\n    {\n        $$if (a > 0) return a;\n        return -a;\n    }\n}\n";
        assert_eq!(
            apply(following, "Convert to conditional expression"),
            "class C\n{\n    int M(int a)\n    {\n        return a > 0 ? a : -a;\n    }\n}\n"
        );
    }

    #[test]
    fn assignments_to_one_target_become_one() {
        let source = "class C\n{\n    void M(bool b)\n    {\n        string s;\n        $$if (b) s = \"yes\"; else s = \"no\";\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to conditional expression"),
            "class C\n{\n    void M(bool b)\n    {\n        string s;\n        s = b ? \"yes\" : \"no\";\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    void M(bool b)\n    {\n        int x, y;\n        $$if (b) x = 1; else y = 2;\n    }\n}\n",
            "Convert to conditional expression",
        );
    }

    #[test]
    fn a_conditional_becomes_an_if() {
        let source =
            "class C\n{\n    int M(bool b)\n    {\n        return b $$? 1 : 2;\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to 'if' statement"),
            "class C\n{\n    int M(bool b)\n    {\n        if (b)\n        {\n            return 1;\n        }\n        else\n        {\n            return 2;\n        }\n    }\n}\n"
        );
        let declared = "class C\n{\n    void M(bool b)\n    {\n        var s = b $$? \"yes\" : \"no\";\n    }\n}\n";
        assert_eq!(
            apply(declared, "Convert to 'if' statement"),
            "class C\n{\n    void M(bool b)\n    {\n        string s;\n        if (b)\n        {\n            s = \"yes\";\n        }\n        else\n        {\n            s = \"no\";\n        }\n    }\n}\n"
        );
    }
}
