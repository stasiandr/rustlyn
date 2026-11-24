//! Convert a `foreach` to LINQ, and simple LINQ back to a `foreach`.
//!
//! Roslyn's `ConvertForEachToLinqQuery` ("Convert to LINQ", "Convert to
//! LINQ (call form)") and `ConvertLinqQueryToForEach`, for the loops that
//! say one thing each:
//!
//! * filtering — `foreach (var x in xs) { if (c) { ... } }` loops over
//!   `from x in xs where c select x`, or `xs.Where(x => c)`;
//! * counting — `int n = 0;` then a loop that only does `n++` (under an
//!   `if`, perhaps) becomes `int n = xs.Count(x => c);`;
//! * summing — `int total = 0;` then a loop that only does `total += e;`
//!   becomes `int total = xs.Sum(x => e);`;
//! * collecting — `var list = new List<T>();` then a loop that only does
//!   `list.Add(e)` becomes `var list = xs.Select(x => e).ToList();`.
//!
//! `System.Linq` has to be there, and a `using` for it is added when the
//! file has none. The loop variable must be declared `var`, or as the
//! element type itself: a `foreach` with another type casts, and LINQ
//! would not.
//!
//! "Convert to 'foreach'" turns `int n = xs.Count(x => c);` and `int total
//! = xs.Sum(x => e);` back into the loop.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{skip_parentheses, statements_of};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let around: Vec<SyntaxNode> = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| !super::super::text::is_member(node.kind()))
        .collect();
    if context
        .view
        .compiled()
        .type_by_metadata_name("System.Linq.Enumerable")
        .is_none()
    {
        return;
    }
    if let Some(loop_statement) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::ForEachStatement)
    {
        // The header only.
        let header = loop_statement
            .child_token_of_kind(SyntaxKind::CloseParenToken)
            .is_some_and(|close| context.trimmed_span().start() <= close.span().end());
        if header && let Some(forms) = to_linq(context, loop_statement) {
            for (title, mut edits) in forms {
                edits.extend(using_linq(context, loop_statement));
                found.push(context.local(title, ActionKind::Refactor, None, edits));
            }
        }
    }
    if let Some(declaration) = around
        .iter()
        .find(|node| node.kind() == SyntaxKind::LocalDeclarationStatement)
        && let Some(edit) = to_foreach(context, declaration)
    {
        found.push(context.local(
            "Convert to 'foreach'",
            ActionKind::Refactor,
            None,
            vec![edit],
        ));
    }
}

/// `using System.Linq;` when the file does not have it.
fn using_linq(context: &Context<'_, '_>, at: &SyntaxNode) -> Option<TextEdit> {
    let root = context.view.syntax_root();
    if super::super::fixes::support::Namer::at(context.view, at).imports("System.Linq") {
        return None;
    }
    super::super::fixes::support::add_using(root, &context.text, "System.Linq")
}

/// The parts of a `foreach`: its variable's type and name, the collection
/// and the body.
struct Loop {
    variable: String,
    source: SyntaxNode,
    body: Vec<SyntaxNode>,
}

fn loop_parts(context: &mut Context<'_, '_>, statement: &SyntaxNode) -> Option<Loop> {
    let ty = statement
        .children()
        .find(|child| child.kind().is_type_node())?;
    let variable = statement.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let children: Vec<SyntaxNode> = statement.children().collect();
    let source = children
        .iter()
        .find(|child| child.kind().is_expression() && **child != ty)?
        .clone();
    let body = children.last()?.clone();
    let body = if body.kind() == SyntaxKind::Block {
        statements_of(&body)
    } else {
        vec![body]
    };
    if ty.text() != "var" {
        // Declared as the element type: nothing is cast.
        let element = element_type(context.view.expression_type(&source)?)?;
        if context.view.model.type_of_syntax(&ty) != element {
            return None;
        }
    }
    Some(Loop {
        variable: variable.value_text().to_string(),
        source,
        body,
    })
}

/// What a collection of `ty` holds, for arrays and generic collections.
fn element_type(ty: Type) -> Option<Type> {
    match ty {
        Type::Array { element, rank: 1 } => Some(*element),
        Type::Named { type_arguments, .. } if type_arguments.len() == 1 => {
            type_arguments.into_iter().next()
        }
        _ => None,
    }
}

/// The body's one statement under an optional `if` without `else`: the
/// condition, and what runs.
fn filtered(body: &[SyntaxNode]) -> (Option<SyntaxNode>, Vec<SyntaxNode>) {
    if let [only] = body
        && only.kind() == SyntaxKind::IfStatement
        && only.child_of_kind(SyntaxKind::ElseClause).is_none()
    {
        let mut children = only.children();
        if let (Some(condition), Some(inner)) = (children.next(), children.next()) {
            let inner = if inner.kind() == SyntaxKind::Block {
                statements_of(&inner)
            } else {
                vec![inner]
            };
            return (Some(condition), inner);
        }
    }
    (None, body.to_vec())
}

/// Every form a loop converts to, with its edits.
fn to_linq(
    context: &mut Context<'_, '_>,
    statement: &SyntaxNode,
) -> Option<Vec<(&'static str, Vec<TextEdit>)>> {
    let parts = loop_parts(context, statement)?;
    let x = &parts.variable;
    let source = parts.source.text();
    let (condition, inner) = filtered(&parts.body);
    let condition_text = condition
        .as_ref()
        .map(|condition| skip_parentheses(condition).text());

    // What the loop does with each element, when it is one of the
    // aggregates.
    if let [only] = inner.as_slice()
        && only.kind() == SyntaxKind::ExpressionStatement
        && let Some(expression) = only.children().next()
        && let Some(forms) = aggregate(
            context,
            statement,
            x,
            &source,
            condition_text.as_deref(),
            &expression,
        )
    {
        return Some(forms);
    }

    // Filtering: the loop stays, over the elements that pass.
    let condition = condition_text?;
    let body_statement = parts.body.first()?;
    let if_statement = body_statement.clone();
    let inner_body = if_statement.children().nth(1)?;
    let query = format!("from {x} in {source} where {condition} select {x}");
    let call = format!("{source}.Where({x} => {condition})");
    let replace_body = |context: &Context<'_, '_>| -> Option<TextEdit> {
        // The `if`'s body takes the place of the loop's.
        let loop_body = statement.children().last()?;
        let text = if inner_body.kind() == SyntaxKind::Block {
            let indent = context.indentation_at(inner_body.span().start());
            let target = context.indentation_at(loop_body.span().start());
            super::super::text::reindent(&inner_body.text(), &indent, &target)
        } else {
            inner_body.text()
        };
        Some(TextEdit::new(loop_body.span(), text))
    };
    let body_edit = replace_body(context)?;
    let source_span = parts.source.span();
    Some(vec![
        (
            "Convert to LINQ",
            vec![TextEdit::new(source_span, query), body_edit.clone()],
        ),
        (
            "Convert to LINQ (call form)",
            vec![TextEdit::new(source_span, call), body_edit],
        ),
    ])
}

/// `n++`, `total += e` or `list.Add(e)` of a local declared just before
/// the loop: the declaration takes the query, and the loop goes.
fn aggregate(
    context: &mut Context<'_, '_>,
    statement: &SyntaxNode,
    x: &str,
    source: &str,
    condition: Option<&str>,
    expression: &SyntaxNode,
) -> Option<Vec<(&'static str, Vec<TextEdit>)>> {
    let block = statement.parent()?;
    let statements = statements_of(block);
    let at = statements.iter().position(|other| other == statement)?;
    let declaration = statements.get(at.checked_sub(1)?)?;
    if declaration.kind() != SyntaxKind::LocalDeclarationStatement {
        return None;
    }
    let declarator = declaration
        .descendants()
        .find(|node| node.kind() == SyntaxKind::VariableDeclarator)?;
    let local = declarator
        .child_token_of_kind(SyntaxKind::IdentifierToken)?
        .value_text()
        .to_string();
    let initial = declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)?
        .children()
        .next()?;
    let target_of = |node: &SyntaxNode| node.children().next().map(|target| target.text());
    let where_clause = condition
        .map(|condition| format!(" where {condition}"))
        .unwrap_or_default();
    let where_call = condition
        .map(|condition| format!(".Where({x} => {condition})"))
        .unwrap_or_default();
    let (query, call) = match expression.kind() {
        SyntaxKind::PostIncrementExpression | SyntaxKind::PreIncrementExpression => {
            let operand = expression.children().next()?.text();
            if operand != local || initial.text() != "0" {
                return None;
            }
            let call = match condition {
                Some(condition) => format!("{source}.Count({x} => {condition})"),
                None => format!("{source}.Count()"),
            };
            (
                format!("(from {x} in {source}{where_clause} select {x}).Count()"),
                call,
            )
        }
        SyntaxKind::AddAssignmentExpression => {
            if target_of(expression)? != local || initial.text() != "0" {
                return None;
            }
            let value = expression.children().nth(1)?;
            let value = skip_parentheses(&value).text();
            (
                format!("(from {x} in {source}{where_clause} select {value}).Sum()"),
                format!("{source}{where_call}.Sum({x} => {value})"),
            )
        }
        SyntaxKind::InvocationExpression => {
            // `list.Add(e)` into `var list = new List<T>();`.
            let callee = expression.children().next()?;
            if callee.kind() != SyntaxKind::SimpleMemberAccessExpression
                || callee.children().next()?.text() != local
                || callee.children().nth(1)?.text() != "Add"
            {
                return None;
            }
            let initial = skip_parentheses(&initial);
            let empty_list = initial.kind() == SyntaxKind::ObjectCreationExpression
                && initial
                    .child_of_kind(SyntaxKind::ArgumentList)
                    .is_some_and(|list| list.children().next().is_none())
                && initial
                    .child_of_kind(SyntaxKind::CollectionInitializerExpression)
                    .is_none()
                && context.view.expression_type(&initial).is_some_and(|ty| {
                    ty.symbol().is_some_and(|symbol| {
                        context.view.compiled().symbols().qualified_name(symbol)
                            == "System.Collections.Generic.List`1"
                    })
                });
            if !empty_list {
                return None;
            }
            let arguments: Vec<SyntaxNode> = expression
                .child_of_kind(SyntaxKind::ArgumentList)?
                .children()
                .filter(|child| child.kind() == SyntaxKind::Argument)
                .collect();
            let [argument] = arguments.as_slice() else {
                return None;
            };
            let value = argument.children().last()?.text();
            let select_call = if value == x {
                String::new()
            } else {
                format!(".Select({x} => {value})")
            };
            (
                format!("(from {x} in {source}{where_clause} select {value}).ToList()"),
                format!("{source}{where_call}{select_call}.ToList()"),
            )
        }
        _ => return None,
    };
    let remove = TextSpan::from_bounds(declaration.span().end(), statement.span().end());
    let forms = [
        ("Convert to LINQ", query),
        ("Convert to LINQ (call form)", call),
    ]
    .into_iter()
    .map(|(title, value)| {
        (
            title,
            vec![
                TextEdit::new(initial.span(), value),
                TextEdit::delete(remove),
            ],
        )
    })
    .collect();
    Some(forms)
}

/// `int n = xs.Count(x => c);` → `int n = 0; foreach (var x in xs) { if (c)
/// { n++; } }`, and `Sum` the same way.
fn to_foreach(context: &mut Context<'_, '_>, declaration: &SyntaxNode) -> Option<TextEdit> {
    let variable = declaration.child_of_kind(SyntaxKind::VariableDeclaration)?;
    let declarators: Vec<SyntaxNode> = variable
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let [declarator] = declarators.as_slice() else {
        return None;
    };
    let local = declarator
        .child_token_of_kind(SyntaxKind::IdentifierToken)?
        .value_text()
        .to_string();
    let clause = declarator.child_of_kind(SyntaxKind::EqualsValueClause)?;
    let call = skip_parentheses(&clause.children().next()?);
    if call.kind() != SyntaxKind::InvocationExpression {
        return None;
    }
    let callee = call.children().next()?;
    if callee.kind() != SyntaxKind::SimpleMemberAccessExpression {
        return None;
    }
    let name_node = callee.children().nth(1)?;
    let method = name_node.text();
    if method != "Count" && method != "Sum" {
        return None;
    }
    // The call binds to `Enumerable`'s.
    let name_token = name_node.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let Some(Resolved::Symbol(bound)) = context.view.resolve(&name_token) else {
        return None;
    };
    let symbols = context.view.compiled().symbols();
    if symbols
        .get(bound)
        .container
        .map(|container| symbols.qualified_name(container))
        .as_deref()
        != Some("System.Linq.Enumerable")
    {
        return None;
    }
    let source = callee.children().next()?.text();
    let arguments: Vec<SyntaxNode> = call
        .child_of_kind(SyntaxKind::ArgumentList)?
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
        .filter_map(|argument| argument.children().last())
        .collect();
    let [lambda] = arguments.as_slice() else {
        return None;
    };
    if lambda.kind() != SyntaxKind::SimpleLambdaExpression {
        return None;
    }
    let parameter = lambda
        .descendant_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
    let parameter = parameter.value_text().to_string();
    let body = lambda.children().last()?;
    if !body.kind().is_expression() {
        return None;
    }
    let nl = context.newline();
    let unit = context.indent_unit();
    let indent = context.indentation_at(declaration.span().start());
    let ty = variable
        .children()
        .find(|child| child.kind().is_type_node())?
        .text();
    let ty = if ty == "var" { "int".to_string() } else { ty };
    let inner = if method == "Count" {
        format!(
            "{indent}{unit}if ({})\n{indent}{unit}{{\n{indent}{unit}{unit}{local}++;\n{indent}{unit}}}",
            body.text()
        )
    } else {
        format!("{indent}{unit}{local} += {};", body.text())
    };
    let written = format!(
        "{ty} {local} = 0;\n{indent}foreach (var {parameter} in {source})\n{indent}{{\n{inner}\n{indent}}}"
    )
    .replace('\n', nl);
    Some(TextEdit::new(declaration.span(), written))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::support::{actions_in, apply_in};

    const LINQ: &str = "namespace System.Linq\n{\n    using System.Collections.Generic;\n    public static class Enumerable\n    {\n        public static IEnumerable<T> Where<T>(this IEnumerable<T> s, Func<T, bool> p) => s;\n        public static IEnumerable<R> Select<T, R>(this IEnumerable<T> s, Func<T, R> p) => null;\n        public static int Count<T>(this IEnumerable<T> s) => 0;\n        public static int Count<T>(this IEnumerable<T> s, Func<T, bool> p) => 0;\n        public static int Sum<T>(this IEnumerable<T> s, Func<T, int> p) => 0;\n        public static int Sum(this IEnumerable<int> s) => 0;\n        public static List<T> ToList<T>(this IEnumerable<T> s) => null;\n    }\n}\n";

    /// A file of `usings` and a class with `body`.
    fn file(usings: &str, body: &str) -> String {
        format!("{usings}\nnamespace App\n{{\n    class C\n    {{\n{body}    }}\n}}\n")
    }

    fn apply(source: &str, title: &str) -> String {
        apply_in(&[("A.cs", source), ("Linq.cs", LINQ)], title)
            .into_iter()
            .find(|(path, _)| path == Path::new("/p/A.cs"))
            .expect("the file")
            .1
    }

    const PLAIN: &str = "using System.Collections.Generic;\n";
    const WITH_LINQ: &str = "using System.Collections.Generic;\nusing System.Linq;\n";

    #[test]
    fn a_filtering_loop_loops_over_a_query() {
        let source = file(
            PLAIN,
            "        void M(List<int> xs)\n        {\n            $$foreach (var x in xs)\n            {\n                if (x > 0)\n                {\n                    System.Console.WriteLine(x);\n                }\n            }\n        }\n",
        );
        assert_eq!(
            apply(&source, "Convert to LINQ (call form)"),
            file(
                WITH_LINQ,
                "        void M(List<int> xs)\n        {\n            foreach (var x in xs.Where(x => x > 0))\n            {\n                System.Console.WriteLine(x);\n            }\n        }\n"
            )
        );
        assert_eq!(
            apply(&source, "Convert to LINQ"),
            file(
                WITH_LINQ,
                "        void M(List<int> xs)\n        {\n            foreach (var x in from x in xs where x > 0 select x)\n            {\n                System.Console.WriteLine(x);\n            }\n        }\n"
            )
        );
    }

    #[test]
    fn counting_summing_and_collecting_become_one_call() {
        let source = file(
            WITH_LINQ,
            "        int M(List<int> xs)\n        {\n            int count = 0;\n            $$foreach (var x in xs)\n            {\n                if (x > 2)\n                {\n                    count++;\n                }\n            }\n            return count;\n        }\n",
        );
        assert_eq!(
            apply(&source, "Convert to LINQ (call form)"),
            file(
                WITH_LINQ,
                "        int M(List<int> xs)\n        {\n            int count = xs.Count(x => x > 2);\n            return count;\n        }\n"
            )
        );
        let source = file(
            WITH_LINQ,
            "        int M(int[] xs)\n        {\n            int total = 0;\n            $$foreach (int x in xs)\n                total += x * 2;\n            return total;\n        }\n",
        );
        assert_eq!(
            apply(&source, "Convert to LINQ"),
            file(
                WITH_LINQ,
                "        int M(int[] xs)\n        {\n            int total = (from x in xs select x * 2).Sum();\n            return total;\n        }\n"
            )
        );
        let source = file(
            WITH_LINQ,
            "        List<string> M(List<int> xs)\n        {\n            var names = new List<string>();\n            $$foreach (var x in xs)\n            {\n                names.Add(x.ToString());\n            }\n            return names;\n        }\n",
        );
        assert_eq!(
            apply(&source, "Convert to LINQ (call form)"),
            file(
                WITH_LINQ,
                "        List<string> M(List<int> xs)\n        {\n            var names = xs.Select(x => x.ToString()).ToList();\n            return names;\n        }\n"
            )
        );
        let source = file(
            WITH_LINQ,
            "        void M(List<int> xs)\n        {\n            $$foreach (var x in xs)\n            {\n                System.Console.WriteLine(x);\n            }\n        }\n",
        );
        let (_, actions) = actions_in(&[("A.cs", &source), ("Linq.cs", LINQ)]);
        assert!(
            !actions
                .iter()
                .any(|action| action.title.starts_with("Convert to LINQ"))
        );
    }

    #[test]
    fn a_count_becomes_a_loop_again() {
        let source = file(
            WITH_LINQ,
            "        int M(List<int> xs)\n        {\n            int $$count = xs.Count(x => x > 2);\n            return count;\n        }\n",
        );
        assert_eq!(
            apply(&source, "Convert to 'foreach'"),
            file(
                WITH_LINQ,
                "        int M(List<int> xs)\n        {\n            int count = 0;\n            foreach (var x in xs)\n            {\n                if (x > 2)\n                {\n                    count++;\n                }\n            }\n            return count;\n        }\n"
            )
        );
    }
}
