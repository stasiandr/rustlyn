//! Use object initializer, use collection initializer: the assignments or
//! `Add` calls that follow a `new` folded into it.
//!
//! Roslyn's fixes for IDE0017 and IDE0028. With the cursor on a `new`
//! whose value is stored in a local (declared there or assigned), the
//! statements right after it that set a member of that local — `c.X = 1;`
//! — become `X = 1` in an object initializer; the ones that call `Add` on
//! it become elements of a collection initializer, for a type that is
//! enumerable. Folding stops at the first statement that does something
//! else, sets a member a second time, or uses the local in the value it
//! stores: inside the initializer the local is not assigned yet.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::statements_of;
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(creation) = context.ancestor_of_kind(&[SyntaxKind::ObjectCreationExpression]) else {
        return;
    };
    if creation.children().any(|child| {
        matches!(
            child.kind(),
            SyntaxKind::ObjectInitializerExpression | SyntaxKind::CollectionInitializerExpression
        )
    }) {
        return;
    }
    let Some((statement, name)) = stored_in(&creation) else {
        return;
    };
    let Some(block) = statement.parent().cloned() else {
        return;
    };
    if !matches!(block.kind(), SyntaxKind::Block | SyntaxKind::SwitchSection) {
        return;
    }
    let statements = statements_of(&block);
    let Some(at) = statements.iter().position(|other| *other == statement) else {
        return;
    };
    let following = &statements[at + 1..];
    if let Some((last, items)) = object_items(following, &name) {
        push(
            context,
            found,
            "Use object initializer",
            &creation,
            &statement,
            &last,
            &items,
        );
    } else if is_collection(context, &creation)
        && let Some((last, items)) = collection_items(following, &name)
    {
        push(
            context,
            found,
            "Use collection initializer",
            &creation,
            &statement,
            &last,
            &items,
        );
    }
}

/// The statement storing the new object, and the name it is stored in:
/// `var c = new C();` or `c = new C();`.
fn stored_in(creation: &SyntaxNode) -> Option<(SyntaxNode, String)> {
    let parent = creation.parent()?;
    match parent.kind() {
        SyntaxKind::EqualsValueClause => {
            let declarator = parent.parent()?;
            let declaration = declarator.parent()?;
            let statement = declaration.parent()?;
            let count = declaration
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                .count();
            (statement.kind() == SyntaxKind::LocalDeclarationStatement && count == 1)
                .then(|| {
                    declarator
                        .child_token_of_kind(SyntaxKind::IdentifierToken)
                        .map(|token| (statement.clone(), token.value_text().to_string()))
                })
                .flatten()
        }
        SyntaxKind::SimpleAssignmentExpression => {
            let statement = parent.parent()?;
            let target = parent.children().next()?;
            (statement.kind() == SyntaxKind::ExpressionStatement
                && target.kind() == SyntaxKind::IdentifierName
                && parent.children().last().as_ref() == Some(creation))
            .then(|| (statement.clone(), target.text()))
        }
        _ => None,
    }
}

/// Whether `node` names `name` anywhere.
fn mentions(node: &SyntaxNode, name: &str) -> bool {
    node.descendant_tokens()
        .any(|token| token.kind() == SyntaxKind::IdentifierToken && token.value_text() == name)
}

/// The expression of an expression statement.
fn expression_of(statement: &SyntaxNode) -> Option<SyntaxNode> {
    (statement.kind() == SyntaxKind::ExpressionStatement)
        .then(|| statement.children().next())
        .flatten()
}

/// `name.X = value;` statements as `X = value`, up to the first that is
/// not one; with the last statement taken.
fn object_items(statements: &[SyntaxNode], name: &str) -> Option<(SyntaxNode, Vec<String>)> {
    let mut items = Vec::new();
    let mut members: Vec<String> = Vec::new();
    let mut last = None;
    for statement in statements {
        let Some(assignment) = expression_of(statement)
            .filter(|expression| expression.kind() == SyntaxKind::SimpleAssignmentExpression)
        else {
            break;
        };
        let mut sides = assignment.children();
        let (Some(target), Some(value)) = (sides.next(), sides.next()) else {
            break;
        };
        if target.kind() != SyntaxKind::SimpleMemberAccessExpression {
            break;
        }
        let mut parts = target.children();
        let (Some(receiver), Some(member)) = (parts.next(), parts.next()) else {
            break;
        };
        let member = member.text();
        if receiver.text() != name || mentions(&value, name) || members.contains(&member) {
            break;
        }
        members.push(member.clone());
        items.push(format!("{member} = {}", value.text()));
        last = Some(statement.clone());
    }
    Some((last?, items))
}

/// `name.Add(x);` statements as `x` (or `{ x, y }`), up to the first that
/// is not one.
fn collection_items(statements: &[SyntaxNode], name: &str) -> Option<(SyntaxNode, Vec<String>)> {
    let mut items = Vec::new();
    let mut last = None;
    for statement in statements {
        let Some(call) = expression_of(statement)
            .filter(|expression| expression.kind() == SyntaxKind::InvocationExpression)
        else {
            break;
        };
        let Some(callee) = call.children().next() else {
            break;
        };
        let parts: Vec<SyntaxNode> = callee.children().collect();
        if callee.kind() != SyntaxKind::SimpleMemberAccessExpression
            || parts.len() != 2
            || parts[0].text() != name
            || parts[1].text() != "Add"
        {
            break;
        }
        let Some(list) = call.child_of_kind(SyntaxKind::ArgumentList) else {
            break;
        };
        let arguments: Vec<SyntaxNode> = list
            .children()
            .filter(|child| child.kind() == SyntaxKind::Argument)
            .collect();
        if arguments.is_empty()
            || arguments.iter().any(|argument| {
                mentions(argument, name)
                    || argument.child_tokens().next().is_some()
                    || argument.child_of_kind(SyntaxKind::NameColon).is_some()
            })
        {
            break;
        }
        let texts: Vec<String> = arguments.iter().map(SyntaxNode::text).collect();
        items.push(if texts.len() == 1 {
            texts[0].clone()
        } else {
            format!("{{ {} }}", texts.join(", "))
        });
        last = Some(statement.clone());
    }
    Some((last?, items))
}

/// Whether what `creation` makes can have a collection initializer: it is
/// enumerable.
fn is_collection(context: &mut Context<'_, '_>, creation: &SyntaxNode) -> bool {
    let Some(Type::Named { symbol, .. }) = context.view.expression_type(creation) else {
        return false;
    };
    let mut pending = vec![symbol];
    let mut seen = std::collections::HashSet::new();
    while let Some(current) = pending.pop() {
        if !seen.insert(current) {
            continue;
        }
        if context.view.compiled().symbols().qualified_name(current)
            == "System.Collections.IEnumerable"
        {
            return true;
        }
        for base in context.view.base_types(current) {
            if let Type::Named { symbol, .. } = base {
                pending.push(symbol);
            }
        }
    }
    false
}

fn push(
    context: &Context<'_, '_>,
    found: &mut Vec<CodeAction>,
    title: &str,
    creation: &SyntaxNode,
    statement: &SyntaxNode,
    last: &SyntaxNode,
    items: &[String],
) {
    let newline = context.newline();
    let indent = context.indentation_at(statement.span().start());
    let unit = context.indent_unit();
    let body = items.join(&format!(",{newline}{indent}{unit}"));
    let text = format!("{newline}{indent}{{{newline}{indent}{unit}{body}{newline}{indent}}};");
    found.push(context.local(
        title,
        ActionKind::Refactor,
        None,
        vec![TextEdit::new(
            TextSpan::from_bounds(creation.span().end(), last.span().end()),
            text,
        )],
    ));
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn member_assignments_fold_into_the_new() {
        let source = "class Point { public int X; public int Y { get; set; } }\nclass C\n{\n    Point M(int y)\n    {\n        var p = $$new Point();\n        p.X = 1;\n        p.Y = y;\n        System.Console.WriteLine(p.X);\n        return p;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use object initializer"),
            "class Point { public int X; public int Y { get; set; } }\nclass C\n{\n    Point M(int y)\n    {\n        var p = new Point()\n        {\n            X = 1,\n            Y = y\n        };\n        System.Console.WriteLine(p.X);\n        return p;\n    }\n}\n"
        );
    }

    #[test]
    fn a_value_that_reads_the_object_stops_the_fold() {
        refuses(
            "class Point { public int X; public int Y; }\nclass C\n{\n    void M()\n    {\n        var p = $$new Point();\n        p.X = p.Y;\n    }\n}\n",
            "Use object initializer",
        );
    }

    #[test]
    fn adds_fold_into_a_collection_initializer() {
        let source = "using System.Collections.Generic;\nclass C\n{\n    List<int> M()\n    {\n        List<int> list;\n        list = $$new List<int>();\n        list.Add(1);\n        list.Add(2);\n        return list;\n    }\n}\n";
        assert_eq!(
            apply(source, "Use collection initializer"),
            "using System.Collections.Generic;\nclass C\n{\n    List<int> M()\n    {\n        List<int> list;\n        list = new List<int>()\n        {\n            1,\n            2\n        };\n        return list;\n    }\n}\n"
        );
    }
}
