//! Introduce parameter: a selected expression in a method becomes a new
//! parameter of the method, and its callers pass it.
//!
//! Roslyn's `IntroduceParameter` refactoring, with its three ways of
//! keeping the callers compiling:
//!
//! * "... and update call sites directly": every call passes the
//!   expression, written with the arguments the call passed for the
//!   parameters it uses;
//! * "... into extracted method": the expression becomes a method of its
//!   own, `GetName(a, b)`, which every call passes the result of;
//! * "... into new overload": the method keeps its old signature as an
//!   overload that passes the expression on, and no call changes.
//!
//! The expression may use the method's parameters and nothing else a call
//! could not see — no locals, no `this`, no names of the type — and must
//! not assign anything. The parameter goes before any optional ones. A
//! method with overrides or implementations is left alone: they would all
//! have to change together, which is change signature's job.

use std::collections::HashSet;

use rustlyn_semantics::{MethodKind, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{fresh_name, one_line, pascal_case};
use super::super::{ActionKind, CodeAction, Context};
use super::change_signature::{
    AddedParameter, CallSite, ChangeParam, Target, change_with, rewrite_declaration,
};
use super::members::{accessibility_text, append_members};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(expression) = context.selected_node() else {
        return;
    };
    // `int` of `int.Parse(s)` is a type, not a value.
    if !expression.kind().is_expression()
        || expression.kind().is_type_node()
        || super::super::text::is_written(&expression)
    {
        return;
    }
    let Some(member) = super::super::text::enclosing_member(&expression) else {
        return;
    };
    if !matches!(
        member.kind(),
        SyntaxKind::MethodDeclaration | SyntaxKind::ConstructorDeclaration
    ) || member
        .child_token_of_kind(SyntaxKind::PartialKeyword)
        .is_some()
    {
        return;
    }
    // In the body, not in a lambda or local function in it.
    let in_body = expression
        .ancestors()
        .take_while(|ancestor| *ancestor != member)
        .all(|ancestor| {
            !matches!(
                ancestor.kind(),
                SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
                    | SyntaxKind::LocalFunctionStatement
                    | SyntaxKind::ParameterList
                    | SyntaxKind::AttributeList
                    | SyntaxKind::BaseConstructorInitializer
                    | SyntaxKind::ThisConstructorInitializer
            )
        });
    if !in_body {
        return;
    }
    let Some(method) = context.view.declared(&member) else {
        return;
    };
    let semantic = context.view.project();
    let symbols = semantic.compilation.symbols();
    let Some(detail) = symbols.get(method).as_method() else {
        return;
    };
    if !matches!(
        detail.method_kind,
        MethodKind::Ordinary | MethodKind::Constructor
    ) || detail.is_extension
        || semantic.cascade(method).len() > 1
    {
        return;
    }
    let Some(uses) = parameters_used(context, &expression, method) else {
        return;
    };
    // Just a parameter: it is one already.
    if expression.kind() == SyntaxKind::IdentifierName {
        return;
    }
    let Some(ty) = context.view.expression_type(&expression) else {
        return;
    };
    if matches!(ty, Type::Void | Type::Null | Type::Error) {
        return;
    }
    let Some(type_text) = context.view.display_type(&ty, &expression) else {
        return;
    };
    let Some(list) = member.child_of_kind(SyntaxKind::ParameterList) else {
        return;
    };
    let declared: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == SyntaxKind::Parameter)
        .collect();
    let names: Vec<String> = declared
        .iter()
        .map(|parameter| {
            parameter
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
                .unwrap_or_default()
        })
        .collect();
    let mut taken = context.view.names_near(&expression);
    taken.extend(names.iter().cloned());
    let name = fresh_name(
        &super::introduce_variable::suggested_name(&expression),
        &taken,
    );
    // Before the first optional or `params` parameter.
    let at = declared
        .iter()
        .position(|parameter| {
            parameter
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .is_some()
                || parameter
                    .child_token_of_kind(SyntaxKind::ParamsKeyword)
                    .is_some()
        })
        .unwrap_or(declared.len());
    let mut order: Vec<ChangeParam> = (0..at).map(ChangeParam::Existing).collect();
    order.push(ChangeParam::Added(AddedParameter {
        ty: type_text.clone(),
        name: name.clone(),
        default: None,
        call_site: None,
    }));
    order.extend((at..declared.len()).map(ChangeParam::Existing));
    let defaults: Vec<Option<String>> = declared
        .iter()
        .map(|parameter| {
            parameter
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().next())
                .map(|value| value.text())
        })
        .collect();
    let Some(name_token) = member.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let target = Target {
        symbol: method,
        name_offset: name_token.span().start(),
    };
    let shown = one_line(&expression);
    let replace = TextEdit::new(expression.span(), name.clone());
    let expression_start = expression.span().start();
    let expression_text = expression.text();

    // The expression as a call writes it: each parameter it uses replaced
    // by what the call passed for it.
    let written_at = |site: &CallSite| -> Option<String> {
        let mut edits = Vec::new();
        for (span, index, parenthesize) in &uses {
            let argument = site
                .arguments
                .get(*index)
                .cloned()
                .flatten()
                .or_else(|| defaults.get(*index).cloned().flatten())?;
            let simple = is_simple(&argument);
            let text = if *parenthesize && !simple {
                format!("({argument})")
            } else {
                argument
            };
            edits.push(TextEdit::new(
                TextSpan::new(span.start() - expression_start, span.end() - span.start()),
                text,
            ));
        }
        Some(crate::edit::apply(&expression_text, &edits))
    };

    // Directly.
    if let Ok(mut edit) = change_with(context, &target, &order, Some(&written_at))
        && !overlaps(&edit, context, expression.span())
    {
        edit.add(context.path.clone(), replace.clone());
        found.push(CodeAction {
            title: format!("Introduce parameter for '{shown}' and update call sites directly"),
            kind: ActionKind::Extract,
            fixes: None,
            edit,
        });
    }

    // Into an extracted method.
    let Some(declaration) = member.parent().cloned() else {
        return;
    };
    let type_name = declaration
        .child_token_of_kind(SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
        .unwrap_or_default();
    let is_constructor = member.kind() == SyntaxKind::ConstructorDeclaration;
    let is_static = member
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some()
        || is_constructor;
    let used: Vec<usize> = {
        let mut seen: Vec<usize> = uses.iter().map(|(_, index, _)| *index).collect();
        seen.sort_unstable();
        seen.dedup();
        seen
    };
    let helper = fresh_name(&format!("Get{}", pascal_case(&name)), &taken);
    let helper_parameters: Vec<String> = used.iter().map(|&index| declared[index].text()).collect();
    let access = accessibility_text(&member);
    let modifiers = [access.as_str(), if is_static { "static" } else { "" }]
        .into_iter()
        .filter(|word| !word.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    let modifiers = if modifiers.is_empty() {
        String::new()
    } else {
        format!("{modifiers} ")
    };
    let helper_text = format!(
        "{modifiers}{type_text} {helper}({})\n{{\n    return {expression_text};\n}}",
        helper_parameters.join(", ")
    );
    let helper_call = |site: &CallSite| -> Option<String> {
        let mut arguments = Vec::new();
        for &index in &used {
            let argument = site
                .arguments
                .get(index)
                .cloned()
                .flatten()
                .or_else(|| defaults.get(index).cloned().flatten())?;
            let modifier = declared[index]
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::RefKeyword | SyntaxKind::OutKeyword | SyntaxKind::InKeyword
                    )
                })
                .map(|token| format!("{} ", token.text()))
                .unwrap_or_default();
            arguments.push(format!("{modifier}{argument}"));
        }
        let prefix = if is_constructor {
            format!("{type_name}.")
        } else {
            site.receiver
                .as_ref()
                .map(|receiver| format!("{receiver}."))
                .unwrap_or_default()
        };
        Some(format!("{prefix}{helper}({})", arguments.join(", ")))
    };
    if let Ok(mut edit) = change_with(context, &target, &order, Some(&helper_call))
        && !overlaps(&edit, context, expression.span())
        && let Some(insert) = after_member(context, &member, &helper_text)
    {
        edit.add(context.path.clone(), replace.clone());
        edit.add(context.path.clone(), insert);
        found.push(CodeAction {
            title: format!("Introduce parameter for '{shown}' into extracted method"),
            kind: ActionKind::Extract,
            fixes: None,
            edit,
        });
    }

    // Into a new overload.
    let Ok(declaration_edits) = rewrite_declaration(&member, &context.text, &order) else {
        return;
    };
    let forwarded: Vec<String> = (0..declared.len())
        .map(|index| {
            let modifier = declared[index]
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::RefKeyword | SyntaxKind::OutKeyword | SyntaxKind::InKeyword
                    )
                })
                .map(|token| format!("{} ", token.text()))
                .unwrap_or_default();
            format!("{modifier}{}", names[index])
        })
        .collect();
    let mut arguments: Vec<String> = forwarded[..at].to_vec();
    arguments.push(expression_text.clone());
    arguments.extend(forwarded[at..].iter().cloned());
    let head_modifiers: Vec<String> = member
        .child_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::PublicKeyword
                    | SyntaxKind::PrivateKeyword
                    | SyntaxKind::ProtectedKeyword
                    | SyntaxKind::InternalKeyword
                    | SyntaxKind::StaticKeyword
                    | SyntaxKind::UnsafeKeyword
            )
        })
        .map(|token| token.text().to_string())
        .collect();
    let head = if head_modifiers.is_empty() {
        String::new()
    } else {
        format!("{} ", head_modifiers.join(" "))
    };
    let parameters_text = list.text();
    let overload = if is_constructor {
        format!(
            "{head}{type_name}{parameters_text} : this({})\n{{\n}}",
            arguments.join(", ")
        )
    } else {
        let Some(return_type) = member.children().find(|child| child.kind().is_type_node()) else {
            return;
        };
        let return_type = return_type.text();
        let type_parameters = member
            .child_of_kind(SyntaxKind::TypeParameterList)
            .map(|list| list.text())
            .unwrap_or_default();
        let constraints: Vec<String> = member
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
            .map(|clause| clause.text())
            .collect();
        let constraints = if constraints.is_empty() {
            String::new()
        } else {
            format!(" {}", constraints.join(" "))
        };
        let call = format!(
            "{}{type_parameters}({})",
            name_token.text(),
            arguments.join(", ")
        );
        let body = if return_type == "void" {
            format!("{call};")
        } else {
            format!("return {call};")
        };
        format!(
            "{head}{return_type} {}{type_parameters}{parameters_text}{constraints}\n{{\n    {body}\n}}",
            name_token.text()
        )
    };
    if let Some(insert) = after_member(context, &member, &overload) {
        let mut edit = WorkspaceEdit::default();
        edit.add_all(context.path.clone(), declaration_edits);
        edit.add(context.path.clone(), replace);
        edit.add(context.path.clone(), insert);
        found.push(CodeAction {
            title: format!("Introduce parameter for '{shown}' into new overload"),
            kind: ActionKind::Extract,
            fixes: None,
            edit,
        });
    }
}

/// The edit putting `text`, a member written without indentation, right
/// after `member`.
fn after_member(context: &Context<'_, '_>, member: &SyntaxNode, text: &str) -> Option<TextEdit> {
    let declaration = member.parent()?;
    super::super::fixes::support::insert_members(
        declaration,
        &context.text,
        &[text.to_string()],
        &super::super::fixes::support::MemberPlace::After(member.span()),
    )
    .or_else(|| append_members(declaration, &context.text, &[text.to_string()]))
}

/// Whether one of the edits to the file asked about touches `span`: a call
/// of the method inside the expression itself.
fn overlaps(edit: &WorkspaceEdit, context: &Context<'_, '_>, span: TextSpan) -> bool {
    edit.edits_of(&context.path)
        .iter()
        .any(|one| one.span.start() < span.end() && span.start() < one.span.end())
}

/// Whether an argument can stand where a parameter's name stood without
/// parentheses: a name, a literal, a member access, a call.
fn is_simple(argument: &str) -> bool {
    argument
        .chars()
        .all(|c| c.is_alphanumeric() || matches!(c, '_' | '.' | '"' | '@'))
        || (argument.ends_with(')') && !argument.contains(' '))
}

/// The parameters of `method` the expression uses: each use's span, the
/// parameter's index, and whether an argument put there needs parentheses.
/// `None` when the expression uses anything else a caller could not see,
/// or writes anything.
fn parameters_used(
    context: &mut Context<'_, '_>,
    expression: &SyntaxNode,
    method: SymbolId,
) -> Option<Vec<(TextSpan, usize, bool)>> {
    let parameters = context
        .view
        .compiled()
        .symbols()
        .get(method)
        .as_method()?
        .parameters
        .clone();
    let mut uses = Vec::new();
    for node in std::iter::once(expression.clone()).chain(expression.descendants()) {
        if matches!(
            node.kind(),
            SyntaxKind::ThisExpression
                | SyntaxKind::BaseExpression
                | SyntaxKind::SimpleLambdaExpression
                | SyntaxKind::ParenthesizedLambdaExpression
                | SyntaxKind::AnonymousMethodExpression
                | SyntaxKind::DeclarationExpression
                | SyntaxKind::AwaitExpression
        ) || super::super::fixes::support::is_assignment(node.kind())
            || matches!(
                node.kind(),
                SyntaxKind::PreIncrementExpression
                    | SyntaxKind::PreDecrementExpression
                    | SyntaxKind::PostIncrementExpression
                    | SyntaxKind::PostDecrementExpression
            )
        {
            return None;
        }
    }
    let tokens: Vec<_> = expression
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .collect();
    let mut seen = HashSet::new();
    for token in tokens {
        let name = token.parent().clone();
        let is_member_name = name.parent().is_some_and(|parent| {
            matches!(
                parent.kind(),
                SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
            ) && parent.children().last().as_ref() == Some(&name)
        });
        if is_member_name {
            continue;
        }
        let resolved = context.view.resolve(&token)?;
        let Resolved::Symbol(symbol) = resolved else {
            return None;
        };
        let found = context.view.compiled().symbols().get(symbol);
        if found.kind != SymbolKind::Parameter {
            return None;
        }
        let index = parameters
            .iter()
            .position(|&parameter| parameter == symbol)?;
        seen.insert(index);
        // Where an operator binds it, a longer argument needs parentheses.
        let parenthesize = name.parent().is_some_and(|parent| {
            !matches!(
                parent.kind(),
                SyntaxKind::Argument | SyntaxKind::ParenthesizedExpression
            )
        });
        uses.push((name.span(), index, parenthesize));
    }
    Some(uses)
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::support::{apply_in, refuses};

    fn file<'a>(files: &'a [(PathBuf, String)], name: &str) -> &'a str {
        &files
            .iter()
            .find(|(path, _)| path == Path::new(name))
            .expect("the file")
            .1
    }

    const PRICING: &str = "class Pricing\n{\n    public double Total(double price, int count, double rate = 0.2)\n    {\n        return [|price * count|] * (1 + rate);\n    }\n}\n";
    const CART: &str = "class Cart\n{\n    double Sum(Pricing p) => p.Total(10.5, 3) + p.Total(2, 1 + 1, 0.1);\n}\n";

    #[test]
    fn call_sites_pass_the_expression() {
        let changed = apply_in(
            &[("A.cs", PRICING), ("B.cs", CART)],
            "Introduce parameter for 'price * count' and update call sites directly",
        );
        assert_eq!(
            file(&changed, "/p/A.cs"),
            "class Pricing\n{\n    public double Total(double price, int count, double v, double rate = 0.2)\n    {\n        return v * (1 + rate);\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/B.cs"),
            "class Cart\n{\n    double Sum(Pricing p) => p.Total(10.5, 3, 10.5 * 3) + p.Total(2, 1 + 1, 2 * (1 + 1), 0.1);\n}\n"
        );
    }

    #[test]
    fn call_sites_call_an_extracted_method() {
        let changed = apply_in(
            &[("A.cs", PRICING), ("B.cs", CART)],
            "Introduce parameter for 'price * count' into extracted method",
        );
        assert_eq!(
            file(&changed, "/p/A.cs"),
            "class Pricing\n{\n    public double Total(double price, int count, double v, double rate = 0.2)\n    {\n        return v * (1 + rate);\n    }\n\n    public double GetV(double price, int count)\n    {\n        return price * count;\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/B.cs"),
            "class Cart\n{\n    double Sum(Pricing p) => p.Total(10.5, 3, p.GetV(10.5, 3)) + p.Total(2, 1 + 1, p.GetV(2, 1 + 1), 0.1);\n}\n"
        );
    }

    #[test]
    fn a_new_overload_keeps_the_callers() {
        let changed = apply_in(
            &[("A.cs", PRICING), ("B.cs", CART)],
            "Introduce parameter for 'price * count' into new overload",
        );
        assert_eq!(
            file(&changed, "/p/A.cs"),
            "class Pricing\n{\n    public double Total(double price, int count, double v, double rate = 0.2)\n    {\n        return v * (1 + rate);\n    }\n\n    public double Total(double price, int count, double rate = 0.2)\n    {\n        return Total(price, count, price * count, rate);\n    }\n}\n"
        );
        assert_eq!(file(&changed, "/p/B.cs"), CART);
    }

    #[test]
    fn locals_and_fields_keep_it_away() {
        refuses(
            "class C\n{\n    int f;\n    int M(int a)\n    {\n        return [|a + f|];\n    }\n}\n",
            "Introduce parameter for 'a + f' and update call sites directly",
        );
        refuses(
            "class C\n{\n    int M(int a)\n    {\n        int b = 2;\n        return [|a + b|];\n    }\n}\n",
            "Introduce parameter for 'a + b' into new overload",
        );
    }
}
