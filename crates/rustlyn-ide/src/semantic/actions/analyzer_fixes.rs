//! Fixes for what the IDE analyzers report: take out what is not needed.
//!
//! Each answers one of [`analyzers`](super::super::analyzers)' diagnostics
//! at the cursor — an unused member or variable, a value nobody reads, a
//! parameter nobody uses, a cast, a qualification, a field that could be
//! `readonly`, code nobody reaches — with Roslyn's title for it. A fix that
//! cannot be made without guessing is not offered: removing an assignment
//! whose right-hand side does something is only offered as `_ = ...`, and a
//! parameter is only removed where every call to its method can be seen.

use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::references::is_written;
use super::super::{AnalyzerDiagnostic, Resolved};
use super::{ActionKind, CodeAction, Context};
use crate::edit::{TextEdit, WorkspaceEdit};

/// Asks every analyzer fix about the diagnostics at the place.
pub(super) fn collect(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let span = context.span;
    let diagnostics: Vec<AnalyzerDiagnostic> = context
        .view
        .analyze()
        .into_iter()
        .filter(|diagnostic| {
            let at = diagnostic.span;
            at.overlaps_with(span)
                || at.contains(span.start())
                || span.contains(at.start())
                || at.end() == span.start()
        })
        .collect();
    for diagnostic in diagnostics {
        found.extend(fix(context, &diagnostic));
    }
}

/// The fix for one analyzer diagnostic, if it has one: what the light bulb
/// offers for it, and what fixing every occurrence applies to each.
pub(super) fn fix(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    match diagnostic.id {
        "IDE0051" | "IDE0052" => remove_member(context, diagnostic),
        "CS0168" | "CS0219" => remove_variable(context, diagnostic),
        "IDE0059" => remove_value(context, diagnostic),
        "IDE0060" => remove_parameter(context, diagnostic),
        "IDE0004" => Some(context.local(
            "Remove unnecessary cast",
            ActionKind::QuickFix,
            Some("IDE0004"),
            vec![TextEdit::delete(diagnostic.span)],
        )),
        "IDE0001" | "IDE0002" => simplify(context, diagnostic),
        "IDE0049" => use_keyword(context, diagnostic),
        "IDE0003" => Some(context.local(
            "Remove 'this' qualification",
            ActionKind::QuickFix,
            Some("IDE0003"),
            vec![TextEdit::delete(diagnostic.span)],
        )),
        "IDE0044" => make_readonly(context, diagnostic),
        "IDE0035" => remove_unreachable(context, diagnostic),
        _ => None,
    }
}

/// The token a diagnostic starts at.
fn token_at(context: &Context<'_, '_>, diagnostic: &AnalyzerDiagnostic) -> Option<SyntaxToken> {
    context
        .view
        .root
        .find_token(diagnostic.span.start())
        .filter(|token| token.span().start() == diagnostic.span.start())
}

/// Deleting one declarator of several: it and the comma that goes with it.
fn remove_declarator(declarator: &SyntaxNode) -> Option<TextEdit> {
    let declaration = declarator.parent()?;
    let declarators: Vec<SyntaxNode> = declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .collect();
    let at = declarators.iter().position(|other| other == declarator)?;
    let span = if at + 1 < declarators.len() {
        TextSpan::from_bounds(
            declarator.span().start(),
            declarators[at + 1].span().start(),
        )
    } else {
        let previous = declarators.get(at.checked_sub(1)?)?;
        TextSpan::from_bounds(previous.span().end(), declarator.span().end())
    };
    Some(TextEdit::delete(span))
}

/// Deleting an argument or a parameter of a list: it and a comma.
fn remove_from_list(item: &SyntaxNode) -> Option<TextEdit> {
    let list = item.parent()?;
    let items: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == item.kind())
        .collect();
    let at = items.iter().position(|other| other == item)?;
    let span = if at + 1 < items.len() {
        TextSpan::from_bounds(item.span().start(), items[at + 1].span().start())
    } else if at > 0 {
        TextSpan::from_bounds(items[at - 1].span().end(), item.span().end())
    } else {
        item.span()
    };
    Some(TextEdit::delete(span))
}

/// Whether evaluating an expression can do anything but produce its value:
/// a call, a `new`, an assignment, an `await` can; a literal, a name, a
/// member of one, and arithmetic on those cannot.
fn is_side_effect_free(expression: &SyntaxNode) -> bool {
    match expression.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression
        | SyntaxKind::DefaultLiteralExpression
        | SyntaxKind::DefaultExpression
        | SyntaxKind::TypeOfExpression
        | SyntaxKind::SizeOfExpression
        | SyntaxKind::IdentifierName
        | SyntaxKind::ThisExpression
        | SyntaxKind::BaseExpression
        | SyntaxKind::PredefinedType => true,
        SyntaxKind::InvocationExpression => expression
            .children()
            .next()
            .is_some_and(|callee| callee.text().trim() == "nameof"),
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::CastExpression
        | SyntaxKind::UnaryMinusExpression
        | SyntaxKind::UnaryPlusExpression
        | SyntaxKind::LogicalNotExpression
        | SyntaxKind::BitwiseNotExpression
        | SyntaxKind::AddExpression
        | SyntaxKind::SubtractExpression
        | SyntaxKind::MultiplyExpression
        | SyntaxKind::LogicalAndExpression
        | SyntaxKind::LogicalOrExpression
        | SyntaxKind::EqualsExpression
        | SyntaxKind::NotEqualsExpression
        | SyntaxKind::LessThanExpression
        | SyntaxKind::GreaterThanExpression
        | SyntaxKind::ConditionalExpression => expression
            .children()
            .filter(|child| child.kind().is_expression() || child.kind().is_type_node())
            .all(|child| is_side_effect_free(&child)),
        _ => false,
    }
}

/// Whether an expression can stand as a statement by itself.
fn is_statement_expression(expression: &SyntaxNode) -> bool {
    matches!(
        expression.kind(),
        SyntaxKind::InvocationExpression
            | SyntaxKind::ObjectCreationExpression
            | SyntaxKind::AwaitExpression
            | SyntaxKind::SimpleAssignmentExpression
            | SyntaxKind::PreIncrementExpression
            | SyntaxKind::PostIncrementExpression
            | SyntaxKind::PreDecrementExpression
            | SyntaxKind::PostDecrementExpression
    )
}

// MARK: - members

/// IDE0051 and IDE0052: the member goes, and for a field nobody reads, the
/// statements that only write it go with it.
fn remove_member(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    let token = token_at(context, diagnostic)?;
    let declaration = token.parent().clone();
    let mut edits = Vec::new();
    if declaration.kind() == SyntaxKind::VariableDeclarator {
        let variables = declaration.parent()?;
        let count = variables
            .children()
            .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
            .count();
        if count == 1 {
            edits.push(TextEdit::delete(variables.parent()?.full_span()));
        } else {
            edits.push(remove_declarator(&declaration)?);
        }
    } else {
        edits.push(TextEdit::delete(declaration.full_span()));
    }
    if diagnostic.id == "IDE0052" {
        let target = context.view.resolve(&token)?;
        let name = token.value_text().to_string();
        for span in context.view.matching_tokens(&name, &target) {
            if span == token.span() {
                continue;
            }
            let written = context.view.root.find_token(span.start())?;
            if !is_written(&written) {
                return None;
            }
            edits.push(remove_write(&written)?);
        }
    }
    let title = if diagnostic.id == "IDE0052" {
        "Remove unread private member"
    } else {
        "Remove unused member"
    };
    Some(context.local(title, ActionKind::QuickFix, Some(diagnostic.id), edits))
}

/// The statement that writes the name `token` and does nothing else,
/// removed; or, where the value it writes does something, kept as just
/// that.
fn remove_write(token: &SyntaxToken) -> Option<TextEdit> {
    let statement = token
        .parent()
        .ancestors()
        .find(|ancestor| ancestor.kind().is_statement_node())?;
    if statement.kind() != SyntaxKind::ExpressionStatement {
        return None;
    }
    let expression = statement.children().next()?;
    if !expression.span().contains_span(token.span()) {
        return None;
    }
    let value = match expression.kind() {
        SyntaxKind::PreIncrementExpression
        | SyntaxKind::PostIncrementExpression
        | SyntaxKind::PreDecrementExpression
        | SyntaxKind::PostDecrementExpression => None,
        _ => Some(expression.children().last()?),
    };
    match value {
        Some(value) if !is_side_effect_free(&value) => {
            if !is_statement_expression(&value) {
                return None;
            }
            Some(TextEdit::new(
                statement.span(),
                format!("{};", value.text().trim()),
            ))
        }
        _ => Some(TextEdit::delete(statement.full_span())),
    }
}

/// IDE0044: `readonly` in front of the field's type.
fn make_readonly(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    let token = token_at(context, diagnostic)?;
    let declarator = token.parent();
    let variables = declarator.parent()?;
    let single = variables
        .children()
        .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        .count()
        == 1;
    if !single {
        return None;
    }
    let ty = variables.children().next()?;
    Some(context.local(
        "Add readonly modifier",
        ActionKind::QuickFix,
        Some("IDE0044"),
        vec![TextEdit::insert(ty.span().start(), "readonly ")],
    ))
}

/// IDE0060: the parameter goes, and so does its argument at every call.
fn remove_parameter(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    let token = token_at(context, diagnostic)?;
    let parameter = token.parent().clone();
    let list = parameter.parent()?;
    let method = list.parent()?;
    if method.kind() != SyntaxKind::MethodDeclaration {
        return None;
    }
    let index = list
        .children()
        .filter(|child| child.kind() == SyntaxKind::Parameter)
        .position(|other| other == parameter)?;
    let name = token.value_text().to_string();
    let method_name = method.child_token_of_kind(SyntaxKind::IdentifierToken)?;
    let symbol = match context.view.resolve(&method_name)? {
        Resolved::Symbol(symbol) => symbol,
        Resolved::Local { .. } => return None,
    };
    let semantic = context.view.semantic;
    let is_extension = semantic
        .compilation
        .symbols()
        .get(symbol)
        .as_method()
        .is_some_and(|detail| detail.is_extension);

    let mut edit = WorkspaceEdit::default();
    edit.add(context.path.clone(), remove_from_list(&parameter)?);
    let text = context.text.clone();
    let (_, uses) = semantic.references(&context.path, method_name.span().start(), Some(&text))?;
    for (file, span) in uses {
        if file == context.path && span == method_name.span() {
            continue;
        }
        let root = if file == context.path {
            context.view.root.clone()
        } else {
            semantic.view(semantic.tree_index(&file)?)?.root.clone()
        };
        let called = root.find_token(span.start())?;
        let (arguments, reduced) = call_arguments(&called)?;
        let shift = usize::from(is_extension && reduced);
        let named = arguments.iter().find(|argument| {
            argument
                .child_of_kind(SyntaxKind::NameColon)
                .is_some_and(|colon| colon.text().trim().trim_end_matches(':').trim() == name)
        });
        let argument = match named {
            Some(argument) => Some(argument.clone()),
            None if arguments
                .iter()
                .any(|argument| argument.child_of_kind(SyntaxKind::NameColon).is_some()) =>
            {
                // Named arguments out of order: which one is which is more
                // than a positional count can say.
                return None;
            }
            None => index
                .checked_sub(shift)
                .and_then(|at| arguments.get(at))
                .cloned(),
        };
        if let Some(argument) = argument {
            edit.add(file.clone(), remove_from_list(&argument)?);
        }
    }
    Some(CodeAction {
        title: format!("Remove unused parameter '{name}'"),
        kind: ActionKind::QuickFix,
        fixes: Some("IDE0060".to_string()),
        edit,
    })
}

/// The arguments of the call whose method the name `token` is, and whether
/// it is called on a receiver — which, for an extension method, fills its
/// first parameter. `None` when the name is not called there.
fn call_arguments(token: &SyntaxToken) -> Option<(Vec<SyntaxNode>, bool)> {
    let mut node = token.parent().clone();
    let mut reduced = false;
    loop {
        let parent = node.parent()?.clone();
        match parent.kind() {
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
                if parent.children().last().as_ref() == Some(&node) =>
            {
                reduced = true;
                node = parent;
            }
            SyntaxKind::InvocationExpression
                if parent.children().next().as_ref() == Some(&node) =>
            {
                let arguments = parent
                    .child_of_kind(SyntaxKind::ArgumentList)?
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::Argument)
                    .collect();
                return Some((arguments, reduced));
            }
            _ => return None,
        }
    }
}

// MARK: - locals

/// CS0168 and CS0219: the declaration goes.
fn remove_variable(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    let token = token_at(context, diagnostic)?;
    let parent = token.parent().clone();
    let edit = match parent.kind() {
        SyntaxKind::VariableDeclarator => {
            let variables = parent.parent()?;
            let statement = variables.parent()?;
            if statement.kind() != SyntaxKind::LocalDeclarationStatement {
                return None;
            }
            let count = variables
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                .count();
            if count == 1 {
                TextEdit::delete(statement.full_span())
            } else {
                remove_declarator(&parent)?
            }
        }
        // `catch (Exception e)` keeps catching, without the name.
        SyntaxKind::CatchDeclaration => {
            let ty = parent
                .children()
                .find(|child| child.kind().is_type_node())?;
            TextEdit::delete(TextSpan::from_bounds(ty.span().end(), token.span().end()))
        }
        _ => return None,
    };
    Some(context.local(
        "Remove unused variable",
        ActionKind::QuickFix,
        Some(diagnostic.id),
        vec![edit],
    ))
}

/// IDE0059: the assignment goes, or where its value does something, the
/// value goes to `_`.
fn remove_value(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    let token = token_at(context, diagnostic)?;
    let parent = token.parent().clone();
    let discard = |context: &Context<'_, '_>, span: TextSpan| {
        context.local(
            "Use discard '_'",
            ActionKind::QuickFix,
            Some("IDE0059"),
            vec![TextEdit::new(span, "_")],
        )
    };
    let redundant = |context: &Context<'_, '_>, edits: Vec<TextEdit>| {
        context.local(
            "Remove redundant assignment",
            ActionKind::QuickFix,
            Some("IDE0059"),
            edits,
        )
    };
    match parent.kind() {
        // `int x = Compute();`
        SyntaxKind::VariableDeclarator => {
            let variables = parent.parent()?;
            let statement = variables.parent()?;
            let single = variables
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                .count()
                == 1;
            if statement.kind() != SyntaxKind::LocalDeclarationStatement || !single {
                return None;
            }
            let value = parent
                .child_of_kind(SyntaxKind::EqualsValueClause)?
                .children()
                .last()?;
            let target = context.view.resolve(&token)?;
            let mentions = context
                .view
                .matching_tokens(token.value_text(), &target)
                .len();
            let free = is_side_effect_free(&value);
            if mentions <= 1 {
                if free {
                    return Some(redundant(
                        context,
                        vec![TextEdit::delete(statement.full_span())],
                    ));
                }
                return Some(context.local(
                    "Use discard '_'",
                    ActionKind::QuickFix,
                    Some("IDE0059"),
                    vec![TextEdit::new(
                        statement.span(),
                        format!("_ = {};", value.text().trim()),
                    )],
                ));
            }
            if !free {
                return None;
            }
            // Used later: keep the declaration, without the value.
            let mut edits = vec![TextEdit::delete(TextSpan::from_bounds(
                token.span().end(),
                parent.span().end(),
            ))];
            let ty = variables.children().next()?;
            if ty.text().trim() == "var" {
                let Resolved::Local { ty: local, .. } = target else {
                    return None;
                };
                let shown = local.display(context.view.compilation().symbols());
                edits.push(TextEdit::new(ty.span(), shown));
            }
            Some(redundant(context, edits))
        }
        // `x = Compute();`, `out x`, `out var x`, `var (a, b)`.
        SyntaxKind::IdentifierName => {
            let holder = parent.parent()?.clone();
            match holder.kind() {
                SyntaxKind::SimpleAssignmentExpression
                    if holder.children().next().as_ref() == Some(&parent) =>
                {
                    let statement = holder
                        .parent()
                        .filter(|statement| statement.kind() == SyntaxKind::ExpressionStatement)?;
                    let value = holder.children().last()?;
                    if is_side_effect_free(&value) {
                        Some(redundant(
                            context,
                            vec![TextEdit::delete(statement.full_span())],
                        ))
                    } else {
                        Some(discard(context, parent.span()))
                    }
                }
                SyntaxKind::Argument => Some(discard(context, parent.span())),
                _ => None,
            }
        }
        SyntaxKind::SingleVariableDesignation => {
            let holder = parent.parent()?.clone();
            match holder.kind() {
                SyntaxKind::DeclarationExpression
                    if holder
                        .parent()
                        .is_some_and(|argument| argument.kind() == SyntaxKind::Argument) =>
                {
                    Some(discard(context, holder.span()))
                }
                SyntaxKind::ParenthesizedVariableDesignation => {
                    Some(discard(context, parent.span()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

// MARK: - names

/// IDE0001 and IDE0002: the qualifier goes.
fn simplify(context: &mut Context<'_, '_>, diagnostic: &AnalyzerDiagnostic) -> Option<CodeAction> {
    let token = token_at(context, diagnostic)?;
    let whole = token.parent().ancestors().find(|ancestor| {
        matches!(
            ancestor.kind(),
            SyntaxKind::QualifiedName | SyntaxKind::SimpleMemberAccessExpression
        ) && ancestor.span().start() == diagnostic.span.start()
            && ancestor
                .children()
                .last()
                .is_some_and(|right| right.span().start() == diagnostic.span.end())
    })?;
    let written = whole.text().trim().to_string();
    let title = if diagnostic.id == "IDE0002" {
        format!("Simplify member access '{written}'")
    } else {
        format!("Simplify name '{written}'")
    };
    Some(context.local(
        title,
        ActionKind::QuickFix,
        Some(diagnostic.id),
        vec![TextEdit::delete(diagnostic.span)],
    ))
}

/// IDE0049: the keyword for the framework name.
fn use_keyword(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    // The message names the keyword: `Name can be simplified to 'string'`.
    let keyword = diagnostic.message.split('\'').nth(1)?.to_string();
    let is_type_keyword = rustlyn_semantics::SpecialType::ALL
        .iter()
        .any(|special| special.keyword() == keyword);
    if !is_type_keyword {
        return None;
    }
    Some(context.local(
        format!("Use '{keyword}'"),
        ActionKind::QuickFix,
        Some("IDE0049"),
        vec![TextEdit::new(diagnostic.span, keyword)],
    ))
}

// MARK: - unreachable code

/// IDE0035: every unreachable statement goes, with its line.
fn remove_unreachable(
    context: &mut Context<'_, '_>,
    diagnostic: &AnalyzerDiagnostic,
) -> Option<CodeAction> {
    let first = context
        .view
        .root
        .find_token(diagnostic.span.start())?
        .parent()
        .ancestors()
        .find(|ancestor| {
            ancestor.kind().is_statement_node()
                && ancestor.span().start() == diagnostic.span.start()
        })?;
    let list = first.parent()?;
    let statements: Vec<SyntaxNode> = list
        .children()
        .filter(|child| {
            child.kind().is_statement_node() && diagnostic.span.contains_span(child.span())
        })
        .collect();
    let last = statements.last()?;
    Some(context.local(
        "Remove unreachable code",
        ActionKind::QuickFix,
        Some("IDE0035"),
        vec![TextEdit::delete(TextSpan::from_bounds(
            first.full_span().start(),
            last.full_span().end(),
        ))],
    ))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::super::tests::{at, compile};
    use crate::edit::apply;
    use rustlyn_text::TextSpan;

    /// The text after the action titled `title` at `marker`, and what it fixes.
    fn fixed(text: &str, marker: &str, title: &str) -> String {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let offset = at(text, marker, 0);
        let actions = semantic
            .code_actions(Path::new("/p/C.cs"), TextSpan::new(offset, 0), None)
            .expect("actions");
        let action = actions
            .iter()
            .find(|action| action.title == title)
            .unwrap_or_else(|| {
                panic!(
                    "{title} in {:?}",
                    actions.iter().map(|a| &a.title).collect::<Vec<_>>()
                )
            });
        apply(text, action.edit.edits_of(Path::new("/p/C.cs")))
    }

    fn offered(text: &str, marker: &str) -> Vec<String> {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let offset = at(text, marker, 0);
        semantic
            .code_actions(Path::new("/p/C.cs"), TextSpan::new(offset, 0), None)
            .expect("actions")
            .into_iter()
            .map(|action| action.title)
            .collect()
    }

    #[test]
    fn unused_members_are_removed_with_their_lines() {
        let text = "class C {\n    private int a, b;\n    private void Unused() { }\n    public int M() => b;\n}\n";
        assert_eq!(
            fixed(text, "Unused", "Remove unused member"),
            "class C {\n    private int a, b;\n    public int M() => b;\n}\n"
        );
        assert_eq!(
            fixed(text, "a, b", "Remove unused member"),
            "class C {\n    private int b;\n    private void Unused() { }\n    public int M() => b;\n}\n"
        );
    }

    #[test]
    fn an_unread_field_goes_with_its_writes() {
        let text = "class C {\n    private int last;\n    int Next() => 1;\n    public void M() {\n        last = 1;\n        last = Next();\n    }\n}\n";
        assert_eq!(
            fixed(text, "last;", "Remove unread private member"),
            "class C {\n    int Next() => 1;\n    public void M() {\n        Next();\n    }\n}\n"
        );
    }

    #[test]
    fn unused_variables_and_values() {
        let text = "class C {\n    int Compute() => 1;\n    public void M() {\n        int unused;\n        int five = 5;\n        var result = Compute();\n        int x = 1;\n        x = 2;\n        System.Console.WriteLine(x);\n        try { } catch (System.Exception e) { }\n    }\n}\n";
        assert!(
            fixed(text, "unused", "Remove unused variable")
                .contains("public void M() {\n        int five")
        );
        assert!(!fixed(text, "five", "Remove unused variable").contains("five"));
        assert!(fixed(text, "result", "Use discard '_'").contains("        _ = Compute();\n"));
        assert!(
            fixed(text, "x = 1", "Remove redundant assignment")
                .contains("        int x;\n        x = 2;")
        );
        assert!(fixed(text, "e)", "Remove unused variable").contains("catch (System.Exception)"));
    }

    #[test]
    fn out_values_nobody_reads_become_discards() {
        let text = "class C { public void M() { int.TryParse(\"1\", out var parsed); } }\n";
        assert!(fixed(text, "parsed", "Use discard '_'").contains("out _)"));
    }

    #[test]
    fn an_unused_parameter_goes_from_every_call() {
        let text = "class C {\n    private int Add(int a, int b) => a;\n    public int M() => Add(1, 2) + Add(a: 3, b: 4);\n}\n";
        assert_eq!(
            fixed(text, "b) =>", "Remove unused parameter 'b'"),
            "class C {\n    private int Add(int a) => a;\n    public int M() => Add(1) + Add(a: 3);\n}\n"
        );
    }

    #[test]
    fn casts_names_this_and_readonly() {
        let text = "using System;\nclass C {\n    private int size;\n    C(int s) { size = s; }\n    int M(int i) { System.Console.WriteLine(1); String t = null; return (int)i + this.size; }\n}\n";
        assert!(fixed(text, "(int)i", "Remove unnecessary cast").contains("return i + "));
        assert!(
            fixed(
                text,
                "System.Console",
                "Simplify member access 'System.Console'"
            )
            .contains("{ Console.WriteLine(1);")
        );
        assert!(fixed(text, "String t", "Use 'string'").contains("string t = null"));
        assert!(fixed(text, "this.size", "Remove 'this' qualification").contains("(int)i + size;"));
        assert!(
            fixed(text, "size;", "Add readonly modifier").contains("private readonly int size;")
        );
    }

    #[test]
    fn unreachable_code_is_removed() {
        let text =
            "class C {\n    int M() {\n        return 1;\n        M();\n        M();\n    }\n}\n";
        assert_eq!(
            fixed(text, "M();", "Remove unreachable code"),
            "class C {\n    int M() {\n        return 1;\n    }\n}\n"
        );
    }

    #[test]
    fn nothing_is_offered_where_nothing_is_wrong() {
        let text = "class C { public int M(int a) { return a; } }\n";
        assert!(
            offered(text, "return").is_empty(),
            "{:?}",
            offered(text, "return")
        );
    }
}
