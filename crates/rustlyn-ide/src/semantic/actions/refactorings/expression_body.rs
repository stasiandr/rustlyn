//! Use expression body, use block body: `int M() { return 1; }` and
//! `int M() => 1;`, both ways, for every kind of member that can be either.
//!
//! Roslyn's `UseExpressionBody` refactoring. A block becomes an expression
//! body when it is one statement: a `return` of a value, an expression
//! statement where nothing is returned, or a `throw`. An expression body
//! becomes a block with the matching statement. Whether nothing is returned
//! is what the declaration says: `void`, a constructor, a setter; for a
//! lambda, the delegate it was bound to.
//!
//! The innermost declaration around the cursor is the one rewritten: a
//! lambda inside a method, an accessor inside a property.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxElement, SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{has_comments, reindent, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let at = context.trimmed_span().start();
    let Some(node) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| noun(node).is_some() && header_end(node).is_some_and(|end| at <= end))
    else {
        return;
    };
    let noun = noun(&node).expect("found by it");
    if let Some(edit) = to_expression(context, &node) {
        found.push(context.local(
            format!("Use expression body for {noun}"),
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
    if let Some(edit) = to_block(context, &node) {
        found.push(context.local(
            format!("Use block body for {noun}"),
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
}

/// Where the header of a declaration ends and its body starts: the cursor
/// has to be in the header, as in Roslyn, so that a method does not offer
/// to rewrite itself from anywhere in its body.
fn header_end(node: &SyntaxNode) -> Option<u32> {
    use SyntaxKind as K;
    if matches!(
        node.kind(),
        K::SimpleLambdaExpression | K::ParenthesizedLambdaExpression
    ) {
        return node
            .child_token_of_kind(K::EqualsGreaterThanToken)
            .map(|arrow| arrow.span().end());
    }
    node.children()
        .find(|child| {
            matches!(
                child.kind(),
                K::Block | K::ArrowExpressionClause | K::AccessorList
            )
        })
        .map(|body| body.span().start())
}

/// What Roslyn's titles call a declaration of this kind, for the kinds that
/// can have either body.
fn noun(node: &SyntaxNode) -> Option<&'static str> {
    use SyntaxKind as K;
    Some(match node.kind() {
        K::MethodDeclaration => "method",
        K::ConstructorDeclaration => "constructor",
        K::OperatorDeclaration => "operator",
        K::ConversionOperatorDeclaration => "conversion operator",
        K::PropertyDeclaration => "property",
        K::IndexerDeclaration => "indexer",
        K::GetAccessorDeclaration
        | K::SetAccessorDeclaration
        | K::InitAccessorDeclaration
        | K::AddAccessorDeclaration
        | K::RemoveAccessorDeclaration => "accessor",
        K::LocalFunctionStatement => "local function",
        K::SimpleLambdaExpression | K::ParenthesizedLambdaExpression => "lambda expression",
        _ => return None,
    })
}

/// Whether the body of `node` gives nothing back, so that its one statement
/// is an expression statement rather than a `return`. `None` when that
/// cannot be told.
pub(super) fn returns_nothing(context: &mut Context<'_, '_>, node: &SyntaxNode) -> Option<bool> {
    use SyntaxKind as K;
    Some(match node.kind() {
        K::ConstructorDeclaration
        | K::SetAccessorDeclaration
        | K::InitAccessorDeclaration
        | K::AddAccessorDeclaration
        | K::RemoveAccessorDeclaration => true,
        K::GetAccessorDeclaration
        | K::OperatorDeclaration
        | K::ConversionOperatorDeclaration
        | K::PropertyDeclaration
        | K::IndexerDeclaration => false,
        K::MethodDeclaration | K::LocalFunctionStatement => {
            let written = node
                .children()
                .find(|child| child.kind().is_type_node())?
                .text();
            let is_async = node.child_token_of_kind(K::AsyncKeyword).is_some();
            written == "void"
                || (is_async
                    && matches!(
                        written.as_str(),
                        "Task" | "ValueTask" | "System.Threading.Tasks.Task"
                    ))
        }
        K::SimpleLambdaExpression | K::ParenthesizedLambdaExpression => {
            if node.child_token_of_kind(K::AsyncKeyword).is_some() {
                return None;
            }
            let body = context.view.bound_body(node)?;
            let lambda = body
                .lambdas
                .iter()
                .find(|lambda| lambda.span == node.span())?;
            match lambda.return_type {
                Type::Void => true,
                Type::Error => return None,
                _ => false,
            }
        }
        _ => return None,
    })
}

/// The end of whatever comes just before `child` in `parent`: where a body
/// that replaces `child` starts.
pub(super) fn end_before(parent: &SyntaxNode, child: TextSpan) -> Option<u32> {
    let mut end = None;
    for element in parent.children_with_tokens() {
        if element.span().start() >= child.start() {
            break;
        }
        let span = match &element {
            SyntaxElement::Node(node) => node.span(),
            SyntaxElement::Token(token) => token.span(),
        };
        end = Some(span.end());
    }
    end
}

/// A block holding one statement, laid out the way the file lays blocks
/// out.
pub(super) fn block(context: &Context<'_, '_>, indent: &str, statement: &str) -> String {
    let newline = context.newline();
    let unit = context.indent_unit();
    format!("{newline}{indent}{{{newline}{indent}{unit}{statement}{newline}{indent}}}")
}

// MARK: - block to expression

/// The expression a one-statement block is the same as, and whether it is
/// a `throw`.
fn single_expression(
    context: &mut Context<'_, '_>,
    owner: &SyntaxNode,
    body: &SyntaxNode,
) -> Option<String> {
    if has_comments(body) {
        return None;
    }
    let statements = statements_of(body);
    let [statement] = statements.as_slice() else {
        return None;
    };
    let expression = statement
        .children()
        .find(|child| child.kind().is_expression());
    match statement.kind() {
        SyntaxKind::ReturnStatement => {
            let expression = expression?;
            (returns_nothing(context, owner) == Some(false)).then(|| expression.text())
        }
        SyntaxKind::ExpressionStatement => {
            let expression = expression?;
            (returns_nothing(context, owner) == Some(true)).then(|| expression.text())
        }
        SyntaxKind::ThrowStatement => Some(format!("throw {}", expression?.text())),
        _ => None,
    }
}

fn to_expression(context: &mut Context<'_, '_>, node: &SyntaxNode) -> Option<TextEdit> {
    use SyntaxKind as K;
    let unit = context.indent_unit();
    match node.kind() {
        K::SimpleLambdaExpression | K::ParenthesizedLambdaExpression => {
            let body = node.child_of_kind(K::Block)?;
            let expression = single_expression(context, node, &body)?;
            Some(TextEdit::new(body.span(), expression))
        }
        K::PropertyDeclaration | K::IndexerDeclaration => {
            let accessors = node.child_of_kind(K::AccessorList)?;
            if node.child_of_kind(K::EqualsValueClause).is_some() {
                return None;
            }
            let all: Vec<SyntaxNode> = accessors.children().collect();
            let [getter] = all.as_slice() else {
                return None;
            };
            if getter.kind() != K::GetAccessorDeclaration
                || getter
                    .child_tokens()
                    .any(|token| !matches!(token.kind(), K::GetKeyword | K::SemicolonToken))
                || getter.child_of_kind(K::AttributeList).is_some()
                || has_comments(&accessors)
            {
                return None;
            }
            let expression = match getter.child_of_kind(K::ArrowExpressionClause) {
                Some(arrow) => arrow.children().next()?.text(),
                None => single_expression(context, getter, &getter.child_of_kind(K::Block)?)?,
            };
            let start = end_before(node, accessors.span())?;
            let indent = context.indentation_at(node.span().start());
            let expression = reindent(
                &expression,
                &format!("{indent}{unit}{unit}"),
                &format!("{indent}{unit}"),
            );
            Some(TextEdit::new(
                TextSpan::from_bounds(start, accessors.span().end()),
                format!(" => {expression};"),
            ))
        }
        _ => {
            let body = node.child_of_kind(K::Block)?;
            let expression = single_expression(context, node, &body)?;
            let indent = context.indentation_at(node.span().start());
            let expression = reindent(
                &expression,
                &format!("{indent}{unit}"),
                &format!("{indent}{unit}"),
            );
            if matches!(
                node.kind(),
                K::GetAccessorDeclaration
                    | K::SetAccessorDeclaration
                    | K::InitAccessorDeclaration
                    | K::AddAccessorDeclaration
                    | K::RemoveAccessorDeclaration
            ) {
                // An accessor's body is on its own line or on the
                // property's: either way, it is just the block that goes.
                let start = end_before(node, body.span())?;
                return Some(TextEdit::new(
                    TextSpan::from_bounds(start, body.span().end()),
                    format!(" => {expression};"),
                ));
            }
            let start = end_before(node, body.span())?;
            Some(TextEdit::new(
                TextSpan::from_bounds(start, body.span().end()),
                format!(" => {expression};"),
            ))
        }
    }
}

// MARK: - expression to block

fn to_block(context: &mut Context<'_, '_>, node: &SyntaxNode) -> Option<TextEdit> {
    use SyntaxKind as K;
    let unit = context.indent_unit();
    let indent = context.indentation_at(node.span().start());
    match node.kind() {
        K::SimpleLambdaExpression | K::ParenthesizedLambdaExpression => {
            let body = node.children().last()?;
            if !body.kind().is_expression() {
                return None;
            }
            let statement = statement_for(context, node, &body)?;
            let statement = reindent(&statement, &indent, &format!("{indent}{unit}"));
            let arrow = node.child_token_of_kind(K::EqualsGreaterThanToken)?;
            Some(TextEdit::new(
                TextSpan::from_bounds(arrow.span().end(), body.span().end()),
                block(context, &indent, &statement),
            ))
        }
        _ => {
            let arrow = node.child_of_kind(K::ArrowExpressionClause)?;
            let semicolon = node.child_token_of_kind(K::SemicolonToken)?;
            let expression = arrow.children().next()?;
            let start = end_before(node, arrow.span())?;
            let span = TextSpan::from_bounds(start, semicolon.span().end());
            if matches!(node.kind(), K::PropertyDeclaration | K::IndexerDeclaration) {
                let inner = format!("{indent}{unit}");
                let statement = format!("return {};", expression.text());
                let statement = reindent(&statement, &inner, &format!("{inner}{unit}"));
                let getter = format!("get{}", block(context, &inner, &statement));
                return Some(TextEdit::new(span, block(context, &indent, &getter)));
            }
            let statement = statement_for(context, node, &expression)?;
            let statement = reindent(&statement, &indent, &format!("{indent}{unit}"));
            Some(TextEdit::new(span, block(context, &indent, &statement)))
        }
    }
}

/// The statement an expression body stands for.
fn statement_for(
    context: &mut Context<'_, '_>,
    owner: &SyntaxNode,
    expression: &SyntaxNode,
) -> Option<String> {
    if expression.kind() == SyntaxKind::ThrowExpression {
        let thrown = expression.children().next()?;
        return Some(format!("throw {};", thrown.text()));
    }
    let nothing = match returns_nothing(context, owner) {
        Some(nothing) => nothing,
        None => context
            .view
            .expression_type(expression)
            .is_some_and(|ty| ty == Type::Void)
            .then_some(true)?,
    };
    Some(if nothing {
        format!("{};", expression.text())
    } else {
        format!("return {};", expression.text())
    })
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn a_method_goes_both_ways() {
        let block = "class C\n{\n    int $$M(int a)\n    {\n        return a + 1;\n    }\n}\n";
        let expression = "class C\n{\n    int $$M(int a) => a + 1;\n}\n";
        assert_eq!(
            apply(block, "Use expression body for method"),
            expression.replace("$$", "")
        );
        assert_eq!(
            apply(expression, "Use block body for method"),
            block.replace("$$", "")
        );
    }

    #[test]
    fn a_void_method_and_a_constructor_keep_their_statement() {
        let block = "class C\n{\n    int x;\n    $$C()\n    {\n        x = 1;\n    }\n}\n";
        let expression = "class C\n{\n    int x;\n    $$C() => x = 1;\n}\n";
        assert_eq!(
            apply(block, "Use expression body for constructor"),
            expression.replace("$$", "")
        );
        assert_eq!(
            apply(expression, "Use block body for constructor"),
            block.replace("$$", "")
        );
        let thrown = "class C\n{\n    void $$M() => throw new System.NotSupportedException();\n}\n";
        assert_eq!(
            apply(thrown, "Use block body for method"),
            "class C\n{\n    void M()\n    {\n        throw new System.NotSupportedException();\n    }\n}\n"
        );
    }

    #[test]
    fn a_property_goes_both_ways() {
        let block = "class C\n{\n    int $$P\n    {\n        get\n        {\n            return 1;\n        }\n    }\n}\n";
        let expression = "class C\n{\n    int $$P => 1;\n}\n";
        assert_eq!(
            apply(block, "Use expression body for property"),
            expression.replace("$$", "")
        );
        assert_eq!(
            apply(expression, "Use block body for property"),
            block.replace("$$", "")
        );
    }

    #[test]
    fn an_accessor_and_a_lambda_are_rewritten_on_their_own() {
        let source =
            "class C\n{\n    int x;\n    int P { $$get { return x; } set { x = value; } }\n}\n";
        assert_eq!(
            apply(source, "Use expression body for accessor"),
            "class C\n{\n    int x;\n    int P { get => x; set { x = value; } }\n}\n"
        );
        let lambda = "class C\n{\n    void M()\n    {\n        System.Func<int, int> f = x $$=> { return x * 2; };\n    }\n}\n";
        assert_eq!(
            apply(lambda, "Use expression body for lambda expression"),
            "class C\n{\n    void M()\n    {\n        System.Func<int, int> f = x => x * 2;\n    }\n}\n"
        );
        let back = "class C\n{\n    void M()\n    {\n        System.Action<int> f = x $$=> System.Console.WriteLine(x);\n    }\n}\n";
        assert_eq!(
            apply(back, "Use block body for lambda expression"),
            "class C\n{\n    void M()\n    {\n        System.Action<int> f = x =>\n        {\n            System.Console.WriteLine(x);\n        };\n    }\n}\n"
        );
    }

    #[test]
    fn a_block_of_two_statements_stays() {
        refuses(
            "class C\n{\n    int $$M(int a)\n    {\n        a++;\n        return a;\n    }\n}\n",
            "Use expression body for method",
        );
    }
}
