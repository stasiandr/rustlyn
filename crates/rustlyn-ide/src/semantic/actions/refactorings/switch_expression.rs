//! `switch` rewrites: a `switch` statement into a `switch` expression, and
//! a chain of `if`s testing one value into a `switch` statement or
//! expression.
//!
//! Roslyn's `ConvertSwitchStatementToExpression` (the fix for IDE0066) and
//! `ConvertIfToSwitch`. A `switch` statement becomes an expression when
//! every section does the same one thing with a value — returns it, or
//! assigns it to the same target and breaks — or throws. Without a
//! `default`, the statement after a returning `switch` is what happens when
//! nothing matched, and it becomes the `_` arm; an assigning `switch`
//! without one would throw where it did nothing, and is left alone.
//!
//! An `if` chain converts when each condition compares the same plain value
//! with constants (`x == 1 || x == 2`) or matches it against patterns
//! (`x is > 5`). Branches become sections, each ending in `break` unless it
//! cannot fall off its end; a branch with a `break` of its own, which would
//! then leave the `switch` instead of a loop, is not converted.

use rustlyn_semantics::{Modifiers, SymbolKind, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    is_statement, precedence, reindent, same_tokens, skip_parentheses, starts_line, statements_of,
};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let parent = token.parent().clone();
    if token.kind() == SyntaxKind::SwitchKeyword
        && parent.kind() == SyntaxKind::SwitchStatement
        && let Some(edit) = switch_to_expression(context, &parent)
    {
        found.push(context.local(
            "Convert switch statement to expression",
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
    if let Some(statement) = super::invert_if::if_at_cursor(context)
        && statement
            .parent()
            .is_none_or(|parent| parent.kind() != SyntaxKind::ElseClause)
        && let Some(chain) = if_chain(context, &statement)
    {
        if let Some(edit) = chain_to_statement(context, &statement, &chain) {
            found.push(context.local(
                "Convert to 'switch' statement",
                ActionKind::Refactor,
                None,
                vec![edit],
            ));
        }
        if let Some(edit) = chain_to_expression(context, &statement, &chain) {
            found.push(context.local(
                "Convert to 'switch' expression",
                ActionKind::Refactor,
                None,
                vec![edit],
            ));
        }
    }
}

/// What one branch does with its value.
#[derive(Clone, Debug, PartialEq)]
enum Outcome {
    Return(String),
    Assign(String, String),
    Throw(String),
}

/// The one thing `statements` do, as a switch arm can: `return e;`,
/// `throw e;`, or `x = e;` then `break;` (`break` only where `breaks` says
/// it is expected).
fn outcome(statements: &[SyntaxNode], breaks: bool) -> Option<Outcome> {
    let statements: Vec<SyntaxNode> = match statements {
        [block] if block.kind() == SyntaxKind::Block => statements_of(block),
        _ => statements.to_vec(),
    };
    let value = |statement: &SyntaxNode| {
        statement
            .children()
            .find(|child| child.kind().is_expression())
    };
    match statements.as_slice() {
        [single] if single.kind() == SyntaxKind::ReturnStatement => {
            Some(Outcome::Return(value(single)?.text()))
        }
        [single] if single.kind() == SyntaxKind::ThrowStatement => {
            Some(Outcome::Throw(format!("throw {}", value(single)?.text())))
        }
        [assignment, stop]
            if breaks
                && assignment.kind() == SyntaxKind::ExpressionStatement
                && stop.kind() == SyntaxKind::BreakStatement =>
        {
            let expression = value(assignment)?;
            if expression.kind() != SyntaxKind::SimpleAssignmentExpression {
                return None;
            }
            let mut sides = expression.children();
            let (target, value) = (sides.next()?, sides.next()?);
            Some(Outcome::Assign(target.text(), value.text()))
        }
        _ => None,
    }
}

/// `arms` as a switch expression on `subject`, preceded by what does
/// something with its value: `return ` or `x = `.
fn switch_expression(
    context: &Context<'_, '_>,
    indent: &str,
    subject: &str,
    arms: &[(String, Outcome)],
) -> Option<String> {
    let newline = context.newline();
    let unit = context.indent_unit();
    let mut prefix = None;
    for (_, outcome) in arms {
        let this = match outcome {
            Outcome::Return(_) => "return ".to_string(),
            Outcome::Assign(target, _) => format!("{target} = "),
            Outcome::Throw(_) => continue,
        };
        if prefix.as_ref().is_some_and(|prefix| *prefix != this) {
            return None;
        }
        prefix = Some(this);
    }
    let prefix = prefix?;
    let mut out = format!("{prefix}{subject} switch{newline}{indent}{{{newline}");
    for (pattern, outcome) in arms {
        let value = match outcome {
            Outcome::Return(value) | Outcome::Assign(_, value) | Outcome::Throw(value) => value,
        };
        out.push_str(&format!("{indent}{unit}{pattern} => {value},{newline}"));
    }
    out.push_str(indent);
    out.push_str("};");
    Some(out)
}

// MARK: - switch statement

fn switch_to_expression(context: &mut Context<'_, '_>, switch: &SyntaxNode) -> Option<TextEdit> {
    let subject = switch
        .children()
        .find(|child| child.kind().is_expression())?;
    let mut arms = Vec::new();
    let mut default = None;
    for section in switch
        .children()
        .filter(|child| child.kind() == SyntaxKind::SwitchSection)
    {
        let mut patterns = Vec::new();
        let mut is_default = false;
        let labels: Vec<SyntaxNode> = section
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::CaseSwitchLabel
                        | SyntaxKind::CasePatternSwitchLabel
                        | SyntaxKind::DefaultSwitchLabel
                )
            })
            .collect();
        for label in &labels {
            match label.kind() {
                SyntaxKind::DefaultSwitchLabel => is_default = true,
                SyntaxKind::CaseSwitchLabel => patterns.push(label.children().next()?.text()),
                _ => {
                    let pattern = label.children().next()?.text();
                    match label.child_of_kind(SyntaxKind::WhenClause) {
                        Some(_) if labels.len() > 1 => return None,
                        Some(when) => patterns.push(format!("{pattern} {}", when.text())),
                        None => patterns.push(pattern),
                    }
                }
            }
        }
        let statements: Vec<SyntaxNode> = section
            .children()
            .filter(|child| is_statement(child.kind()))
            .collect();
        let outcome = outcome(&statements, true)?;
        if is_default {
            default = Some(outcome);
        } else {
            arms.push((patterns.join(" or "), outcome));
        }
    }
    let mut end = switch.span().end();
    let default = match default {
        Some(default) => default,
        None => {
            // A returning switch falls through to what follows it.
            let block = switch.parent()?;
            let statements = statements_of(block);
            let at = statements
                .iter()
                .position(|statement| statement == switch)?;
            let next = statements.get(at + 1)?;
            let outcome = outcome(std::slice::from_ref(next), false)?;
            if matches!(outcome, Outcome::Assign(..)) {
                return None;
            }
            if !arms
                .iter()
                .any(|(_, arm)| matches!(arm, Outcome::Return(_)))
            {
                return None;
            }
            end = next.span().end();
            outcome
        }
    };
    arms.push(("_".to_string(), default));
    if arms
        .iter()
        .all(|(_, outcome)| matches!(outcome, Outcome::Throw(_)))
    {
        return None;
    }
    let indent = context.indentation_at(switch.span().start());
    // `x switch` binds tighter than anything but a primary or unary
    // expression: `(score / 10) switch`.
    let subject = skip_parentheses(&subject);
    let subject = if precedence(subject.kind()) < precedence(SyntaxKind::SwitchExpression) {
        format!("({})", subject.text())
    } else {
        subject.text()
    };
    let text = switch_expression(context, &indent, &subject, &arms)?;
    Some(TextEdit::new(
        TextSpan::from_bounds(switch.span().start(), end),
        text,
    ))
}

// MARK: - if chains

/// One test of an `if` chain, as a `case` would write it.
#[derive(Clone, Debug)]
enum Label {
    /// `case 1:`, compared with `==`.
    Constant(String),
    /// `case > 5:`, matched with `is`.
    Pattern(String),
}

impl Label {
    fn pattern(&self) -> &str {
        match self {
            Self::Constant(text) | Self::Pattern(text) => text,
        }
    }
}

/// An `if` chain on one value: the value, then each branch's labels and
/// statement, then the final `else`'s statement if there is one.
struct Chain {
    subject: SyntaxNode,
    branches: Vec<(Vec<Label>, SyntaxNode)>,
    otherwise: Option<SyntaxNode>,
}

fn if_chain(context: &mut Context<'_, '_>, first: &SyntaxNode) -> Option<Chain> {
    let mut subject: Option<SyntaxNode> = None;
    let mut branches = Vec::new();
    let mut current = first.clone();
    let otherwise = loop {
        let condition = current
            .children()
            .find(|child| child.kind().is_expression())?;
        let statement = current
            .children()
            .find(|child| is_statement(child.kind()))?;
        let labels = labels_of(context, &condition, &mut subject)?;
        branches.push((labels, statement));
        match current.child_of_kind(SyntaxKind::ElseClause) {
            None => break None,
            Some(clause) => {
                let next = clause.children().next()?;
                if next.kind() == SyntaxKind::IfStatement {
                    current = next;
                } else {
                    break Some(next);
                }
            }
        }
    };
    if branches.len() < 2 {
        return None;
    }
    let subject = subject?;
    if !is_plain(&subject) {
        return None;
    }
    Some(Chain {
        subject,
        branches,
        otherwise,
    })
}

fn is_plain(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::ThisExpression => true,
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::ParenthesizedExpression => {
            node.children().all(|child| is_plain(&child))
        }
        _ => false,
    }
}

/// The labels a condition is: `x == 1` one, `x == 1 || x is > 5` two. The
/// first condition decides what `x` is; every other has to test the same.
fn labels_of(
    context: &mut Context<'_, '_>,
    condition: &SyntaxNode,
    subject: &mut Option<SyntaxNode>,
) -> Option<Vec<Label>> {
    let condition = skip_parentheses(condition);
    let children: Vec<SyntaxNode> = condition.children().collect();
    let mut same = |node: &SyntaxNode| match subject {
        Some(known) => same_tokens(known, node),
        None => {
            *subject = Some(node.clone());
            true
        }
    };
    match condition.kind() {
        SyntaxKind::LogicalOrExpression => {
            let mut labels = labels_of(context, children.first()?, subject)?;
            labels.extend(labels_of(context, children.get(1)?, subject)?);
            Some(labels)
        }
        SyntaxKind::EqualsExpression => {
            let (left, right) = (children.first()?, children.get(1)?);
            let (value, constant) = if is_constant(context, right) {
                (left, right)
            } else if is_constant(context, left) {
                (right, left)
            } else {
                return None;
            };
            same(value).then(|| vec![Label::Constant(constant.text())])
        }
        SyntaxKind::IsPatternExpression => {
            let (value, pattern) = (children.first()?, children.get(1)?);
            same(value).then(|| vec![Label::Pattern(pattern.text())])
        }
        _ => None,
    }
}

/// Whether `node` is a constant a `case` can test: a literal, or a `const`
/// field or enum member.
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
        SyntaxKind::IdentifierName | SyntaxKind::SimpleMemberAccessExpression => {
            let Some(token) = node
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .last()
            else {
                return false;
            };
            let Some(Resolved::Symbol(symbol)) = context.view.resolve(&token) else {
                return false;
            };
            let symbols = context.view.compiled().symbols();
            let found = symbols.get(symbol);
            found.kind == SymbolKind::Field
                && (found.modifiers.contains(Modifiers::CONST)
                    || found.container.is_some_and(|container| {
                        symbols.get(container).type_kind() == Some(TypeKind::Enum)
                    }))
        }
        _ => false,
    }
}

/// The statements of a branch, and the indentation they were written at.
fn branch_statements(
    context: &Context<'_, '_>,
    statement: &SyntaxNode,
) -> (Vec<SyntaxNode>, String) {
    let statements = if statement.kind() == SyntaxKind::Block {
        statements_of(statement)
    } else {
        vec![statement.clone()]
    };
    let indent = statements
        .first()
        .filter(|first| starts_line(&context.text, first.span().start()))
        .map(|first| context.indentation_at(first.span().start()));
    (
        statements,
        indent.unwrap_or_else(|| {
            format!(
                "{}{}",
                context.indentation_at(statement.span().start()),
                context.indent_unit()
            )
        }),
    )
}

/// Whether a `break` in `statements` would leave the switch instead of
/// what it left before.
fn breaks_out(statements: &[SyntaxNode]) -> bool {
    statements.iter().any(|statement| {
        std::iter::once(statement.clone())
            .chain(statement.descendants())
            .filter(|node| node.kind() == SyntaxKind::BreakStatement)
            .any(|found| {
                !found
                    .ancestors()
                    .take_while(|ancestor| {
                        ancestor != statement && statement.span().contains_span(ancestor.span())
                    })
                    .any(|ancestor| {
                        matches!(
                            ancestor.kind(),
                            SyntaxKind::WhileStatement
                                | SyntaxKind::DoStatement
                                | SyntaxKind::ForStatement
                                | SyntaxKind::ForEachStatement
                                | SyntaxKind::ForEachVariableStatement
                                | SyntaxKind::SwitchStatement
                        )
                    })
            })
    })
}

fn chain_to_statement(
    context: &mut Context<'_, '_>,
    first: &SyntaxNode,
    chain: &Chain,
) -> Option<TextEdit> {
    let newline = context.newline();
    let unit = context.indent_unit();
    let indent = context.indentation_at(first.span().start());
    let label_indent = format!("{indent}{unit}");
    let body_indent = format!("{label_indent}{unit}");
    let mut out = format!(
        "switch ({}){newline}{indent}{{{newline}",
        skip_parentheses(&chain.subject).text()
    );
    let mut sections: Vec<(Vec<String>, &SyntaxNode)> = chain
        .branches
        .iter()
        .map(|(labels, statement)| {
            (
                labels
                    .iter()
                    .map(|label| format!("case {}:", label.pattern()))
                    .collect(),
                statement,
            )
        })
        .collect();
    if let Some(otherwise) = &chain.otherwise {
        sections.push((vec!["default:".to_string()], otherwise));
    }
    for (labels, statement) in sections {
        for label in labels {
            out.push_str(&format!("{label_indent}{label}{newline}"));
        }
        let (statements, from) = branch_statements(context, statement);
        if breaks_out(&statements) {
            return None;
        }
        for statement in &statements {
            out.push_str(&body_indent);
            out.push_str(&reindent(&statement.text(), &from, &body_indent));
            out.push_str(newline);
        }
        let ends = statements.last().is_some_and(|last| {
            matches!(
                last.kind(),
                SyntaxKind::ReturnStatement
                    | SyntaxKind::ThrowStatement
                    | SyntaxKind::ContinueStatement
                    | SyntaxKind::GotoStatement
            )
        });
        if !ends {
            out.push_str(&format!("{body_indent}break;{newline}"));
        }
    }
    out.push_str(&indent);
    out.push('}');
    Some(TextEdit::new(first.span(), out))
}

fn chain_to_expression(
    context: &mut Context<'_, '_>,
    first: &SyntaxNode,
    chain: &Chain,
) -> Option<TextEdit> {
    let mut arms = Vec::new();
    for (labels, statement) in &chain.branches {
        let outcome = outcome(std::slice::from_ref(statement), false)?;
        let patterns: Vec<&str> = labels.iter().map(Label::pattern).collect();
        arms.push((patterns.join(" or "), outcome));
    }
    let mut end = first.span().end();
    let otherwise = match &chain.otherwise {
        Some(otherwise) => outcome(std::slice::from_ref(otherwise), false)?,
        None => {
            let block = first.parent()?;
            let statements = statements_of(block);
            let at = statements.iter().position(|statement| statement == first)?;
            let next = statements.get(at + 1)?;
            end = next.span().end();
            outcome(std::slice::from_ref(next), false)?
        }
    };
    arms.push(("_".to_string(), otherwise));
    if arms
        .iter()
        .any(|(_, outcome)| matches!(outcome, Outcome::Assign(..)))
    {
        return None;
    }
    let indent = context.indentation_at(first.span().start());
    let text = switch_expression(
        context,
        &indent,
        &skip_parentheses(&chain.subject).text(),
        &arms,
    )?;
    Some(TextEdit::new(
        TextSpan::from_bounds(first.span().start(), end),
        text,
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn a_returning_switch_becomes_an_expression() {
        let source = "class C\n{\n    string M(int x)\n    {\n        $$switch (x)\n        {\n            case 1:\n            case 2:\n                return \"small\";\n            case > 9 when x < 20:\n                return \"teen\";\n            default:\n                throw new System.ArgumentException();\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert switch statement to expression"),
            "class C\n{\n    string M(int x)\n    {\n        return x switch\n        {\n            1 or 2 => \"small\",\n            > 9 when x < 20 => \"teen\",\n            _ => throw new System.ArgumentException(),\n        };\n    }\n}\n"
        );
    }

    #[test]
    fn the_statement_after_is_the_default() {
        let source = "class C\n{\n    int M(string s)\n    {\n        $$switch (s)\n        {\n            case \"a\": return 1;\n        }\n        return 0;\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert switch statement to expression"),
            "class C\n{\n    int M(string s)\n    {\n        return s switch\n        {\n            \"a\" => 1,\n            _ => 0,\n        };\n    }\n}\n"
        );
    }

    #[test]
    fn an_assigning_switch_needs_a_default() {
        let source = "class C\n{\n    void M(int x)\n    {\n        int y;\n        $$switch (x)\n        {\n            case 1:\n                y = 10;\n                break;\n            default:\n                y = 0;\n                break;\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert switch statement to expression"),
            "class C\n{\n    void M(int x)\n    {\n        int y;\n        y = x switch\n        {\n            1 => 10,\n            _ => 0,\n        };\n    }\n}\n"
        );
        refuses(
            "class C\n{\n    void M(int x)\n    {\n        int y = 0;\n        $$switch (x)\n        {\n            case 1:\n                y = 10;\n                break;\n        }\n    }\n}\n",
            "Convert switch statement to expression",
        );
    }

    #[test]
    fn an_if_chain_becomes_a_switch_statement() {
        let source = "class C\n{\n    void M(int x)\n    {\n        $$if (x == 1 || x == 2)\n        {\n            System.Console.WriteLine(\"low\");\n        }\n        else if (x is > 9)\n            System.Console.WriteLine(\"high\");\n        else\n        {\n            return;\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Convert to 'switch' statement"),
            "class C\n{\n    void M(int x)\n    {\n        switch (x)\n        {\n            case 1:\n            case 2:\n                System.Console.WriteLine(\"low\");\n                break;\n            case > 9:\n                System.Console.WriteLine(\"high\");\n                break;\n            default:\n                return;\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_returning_if_chain_becomes_a_switch_expression() {
        let source = "enum Color { Red, Green }\nclass C\n{\n    string M(Color c)\n    {\n        $$if (c == Color.Red) return \"r\";\n        if (c == Color.Green) return \"g\";\n        return \"?\";\n    }\n}\n";
        refuses(source, "Convert to 'switch' expression");
        let chained = "enum Color { Red, Green }\nclass C\n{\n    string M(Color c)\n    {\n        $$if (c == Color.Red) return \"r\";\n        else if (c == Color.Green) return \"g\";\n        return \"?\";\n    }\n}\n";
        assert_eq!(
            apply(chained, "Convert to 'switch' expression"),
            "enum Color { Red, Green }\nclass C\n{\n    string M(Color c)\n    {\n        return c switch\n        {\n            Color.Red => \"r\",\n            Color.Green => \"g\",\n            _ => \"?\",\n        };\n    }\n}\n"
        );
    }

    #[test]
    fn a_branch_that_breaks_a_loop_stays() {
        refuses(
            "class C\n{\n    void M(int[] xs)\n    {\n        foreach (var x in xs)\n        {\n            $$if (x == 1) break;\n            else if (x == 2) continue;\n        }\n    }\n}\n",
            "Convert to 'switch' statement",
        );
    }
}
