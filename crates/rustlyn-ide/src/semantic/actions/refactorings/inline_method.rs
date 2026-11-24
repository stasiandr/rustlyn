//! Inline method: every call of a method replaced by what the method
//! computes, and the method removed — or kept.
//!
//! Roslyn's `InlineMethod` refactoring, offered with the cursor on a call of
//! the method or on its name where it is declared: "Inline 'M'" and "Inline
//! and keep 'M'". It applies to a method whose body is one expression —
//! `=> expression`, `{ return expression; }`, or for a `void` method one
//! expression statement — and replaces every call in the project:
//!
//! * each parameter in the expression becomes the argument the call passed
//!   for it (its default when the call left it out), in parentheses where
//!   an operator around it needs them;
//! * a member of the method's type the expression uses unqualified is
//!   qualified with what the call was made on — `p.Total()` inlines
//!   `count * price` as `p.count * p.price` — or with the type's name for a
//!   static member called from another type;
//! * the whole replacement is parenthesized where the call's place needs it.
//!
//! Not offered for a method that is virtual, overrides or implements
//! something, is generic, recursive or an extension; takes `ref`, `out` or
//! `params`; or is called with an argument that has side effects — or is
//! not a plain value — for a parameter used other than exactly once, since
//! inlining would run it a different number of times. "Inline 'M'" is not
//! offered when the method is used other than by calling it.

use std::path::PathBuf;

use rustlyn_semantics::{Accessibility, MethodKind, Modifiers, SymbolId, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::text::{parenthesized_for, skip_parentheses};
use super::super::{ActionKind, CodeAction, Context};
use super::change_signature::{call_arguments, receiver_of};
use super::members::remove_members;
use super::sources::{root_of, text_of, token_at, with_view};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::{ReferenceKind, Resolved};

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    if token.kind() != SyntaxKind::IdentifierToken {
        return;
    }
    let parent = token.parent().clone();
    let on_declaration = parent.kind() == SyntaxKind::MethodDeclaration;
    let on_call = matches!(
        parent.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) && call_arguments(context, &context.path.clone(), &token).is_some();
    if !on_declaration && !on_call {
        return;
    }
    let Some(Resolved::Symbol(method)) = context.view.resolve(&token) else {
        return;
    };
    let Some(plan) = plan(context, method, token.span().start()) else {
        return;
    };
    let name = context.view.compiled().symbols().get(method).name.clone();
    if plan.calls.is_empty() {
        return;
    }
    let mut keep = WorkspaceEdit::default();
    for (path, edit) in &plan.calls {
        keep.add(path.clone(), edit.clone());
    }
    if !plan.other_uses {
        let mut remove = keep.clone();
        remove.add_all(plan.declaration_path.clone(), plan.removal.clone());
        found.push(CodeAction {
            title: format!("Inline '{name}'"),
            kind: ActionKind::Inline,
            fixes: None,
            edit: remove,
        });
    }
    found.push(CodeAction {
        title: format!("Inline and keep '{name}'"),
        kind: ActionKind::Inline,
        fixes: None,
        edit: keep,
    });
}

/// Every edit of inlining a method.
struct Plan {
    /// Each call replaced.
    calls: Vec<(PathBuf, TextEdit)>,
    /// Removing the declaration.
    removal: Vec<TextEdit>,
    declaration_path: PathBuf,
    /// Whether the method is named other than in a call: then it stays.
    other_uses: bool,
}

/// The one expression a method computes, and whether it is a statement of
/// a `void` method rather than a value.
fn body_expression(declaration: &SyntaxNode) -> Option<(SyntaxNode, bool)> {
    if let Some(arrow) = declaration.child_of_kind(SyntaxKind::ArrowExpressionClause) {
        return Some((arrow.children().next()?, false));
    }
    let block = declaration.child_of_kind(SyntaxKind::Block)?;
    let statements = super::super::text::statements_of(&block);
    let [only] = statements.as_slice() else {
        return None;
    };
    match only.kind() {
        SyntaxKind::ReturnStatement => Some((only.children().next()?, false)),
        SyntaxKind::ExpressionStatement => Some((only.children().next()?, true)),
        _ => None,
    }
}

fn plan(context: &mut Context<'_, '_>, method: SymbolId, offset: u32) -> Option<Plan> {
    let semantic = context.view.project();
    let symbols = semantic.compilation.symbols();
    let symbol = symbols.get(method);
    let detail = symbol.as_method()?;
    if detail.method_kind != MethodKind::Ordinary
        || detail.is_extension
        || detail.arity > 0
        || symbol.modifiers.contains(Modifiers::VIRTUAL)
        || symbol.modifiers.contains(Modifiers::ABSTRACT)
        || symbol.modifiers.contains(Modifiers::OVERRIDE)
        || symbol.modifiers.contains(Modifiers::EXTERN)
        || semantic.compilation.is_from_metadata(method)
        || semantic.cascade(method).len() > 1
    {
        return None;
    }
    let class = symbol.container?;
    let location = *symbol.locations.first()?;
    let declaration_path = semantic.path_of(location.tree)?.to_path_buf();
    let declaration = super::change_signature::declaration_node(context, method)?;
    if declaration.kind() != SyntaxKind::MethodDeclaration {
        return None;
    }
    let (expression, is_statement) = body_expression(&declaration)?;
    let parameters: Vec<SyntaxNode> = declaration
        .child_of_kind(SyntaxKind::ParameterList)?
        .children()
        .filter(|child| child.kind() == SyntaxKind::Parameter)
        .collect();
    if parameters.iter().any(|parameter| {
        parameter.child_tokens().any(|token| {
            matches!(
                token.kind(),
                SyntaxKind::RefKeyword
                    | SyntaxKind::OutKeyword
                    | SyntaxKind::ParamsKeyword
                    | SyntaxKind::ThisKeyword
            )
        })
    }) {
        return None;
    }
    let names: Vec<String> = parameters
        .iter()
        .map(|parameter| {
            parameter
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
                .unwrap_or_default()
        })
        .collect();
    let defaults: Vec<Option<String>> = parameters
        .iter()
        .map(|parameter| {
            parameter
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().next())
                .map(|value| value.text())
        })
        .collect();

    // What each name in the expression is: a parameter, a member of the
    // type (instance or static), or something any caller can name.
    let tokens: Vec<SyntaxToken> = expression
        .descendant_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::IdentifierToken | SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword
            )
        })
        .collect();
    let mut uses: Vec<Use> = Vec::new();
    for token in &tokens {
        if token.kind() == SyntaxKind::BaseKeyword {
            return None;
        }
        if token.kind() == SyntaxKind::ThisKeyword {
            uses.push(Use::This(token.parent().span()));
            continue;
        }
        let name = token.parent().clone();
        let qualified = name.parent().is_some_and(|parent| {
            matches!(
                parent.kind(),
                SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
            ) && parent.children().last().as_ref() == Some(&name)
        });
        if qualified {
            continue;
        }
        let resolved =
            with_view(context, &declaration_path, |view| view.resolve(token)).flatten()?;
        let Resolved::Symbol(used) = resolved else {
            // A lambda's own parameter.
            continue;
        };
        let symbols = context.view.compiled().symbols();
        let found = symbols.get(used);
        if used == method {
            return None;
        }
        match found.kind {
            SymbolKind::Parameter => {
                if let Some(index) = detail
                    .parameters
                    .iter()
                    .position(|&parameter| parameter == used)
                {
                    uses.push(Use::Parameter(name.clone(), index));
                }
            }
            // A member of the type or of a type it derives from, named
            // without a receiver.
            SymbolKind::Method | SymbolKind::Field | SymbolKind::Property | SymbolKind::Event
                if found.container.is_some_and(|container| {
                    symbols.get(container).kind == SymbolKind::NamedType
                }) && found
                    .as_method()
                    .is_none_or(|detail| detail.method_kind != MethodKind::LocalFunction) =>
            {
                uses.push(Use::Member {
                    span: name.span(),
                    is_static: found.modifiers.contains(Modifiers::STATIC)
                        || found.modifiers.contains(Modifiers::CONST),
                    private: found.accessibility == Accessibility::Private,
                    owner: found
                        .container
                        .map(|container| symbols.get(container).name.clone())
                        .unwrap_or_default(),
                });
            }
            _ => {}
        }
    }
    let times = |index: usize| {
        uses.iter()
            .filter(|found| matches!(found, Use::Parameter(_, used) if *used == index))
            .count()
    };

    let (_, references) =
        semantic.references_detailed(&context.path, offset, Some(&context.text))?;
    let mut calls = Vec::new();
    let mut other_uses = false;
    let expression_start = expression.span().start();
    let expression_text = expression.text();
    for reference in references {
        if reference.kind == ReferenceKind::Definition {
            continue;
        }
        let Some(token) = token_at(context, &reference.path, reference.span) else {
            continue;
        };
        let Some((list, _)) = call_arguments(context, &reference.path, &token) else {
            other_uses = true;
            continue;
        };
        let Some(invocation) = list.parent().cloned() else {
            other_uses = true;
            continue;
        };
        if invocation.kind() != SyntaxKind::InvocationExpression {
            other_uses = true;
            continue;
        }
        // A call inside the method itself.
        if reference.path == declaration_path && declaration.span().contains(reference.span.start())
        {
            return None;
        }
        let receiver = receiver_of(&token);
        // Whether the call is made from inside the type.
        let inside = root_of(context, &reference.path).is_some_and(|_| {
            invocation.ancestors().any(|ancestor| {
                super::super::text::is_type_declaration(ancestor.kind())
                    && with_view(context, &reference.path, |view| view.declared(&ancestor))
                        .flatten()
                        == Some(class)
            })
        });
        // The argument each parameter gets.
        let mut passed: Vec<Option<SyntaxNode>> = vec![None; names.len()];
        let mut position = 0;
        for argument in list
            .children()
            .filter(|child| child.kind() == SyntaxKind::Argument)
        {
            let value = argument
                .children()
                .filter(|child| child.kind() != SyntaxKind::NameColon)
                .last()?;
            let index = match argument
                .child_of_kind(SyntaxKind::NameColon)
                .and_then(|colon| colon.child_token_of_kind(SyntaxKind::IdentifierToken))
            {
                Some(named) => names.iter().position(|name| name == named.value_text())?,
                None => {
                    position += 1;
                    position - 1
                }
            };
            *passed.get_mut(index)? = Some(value);
        }
        let mut edits: Vec<TextEdit> = Vec::new();
        for found in &uses {
            match found {
                Use::Parameter(name, index) => {
                    let text = match &passed[*index] {
                        Some(value) => {
                            if times(*index) != 1 && !is_plain(value) {
                                return None;
                            }
                            parenthesized_for(&value.text(), skip_parentheses(value).kind(), name)
                        }
                        None => defaults[*index].clone()?,
                    };
                    edits.push(TextEdit::new(shift(name.span(), expression_start), text));
                }
                Use::Member {
                    span,
                    is_static,
                    private,
                    owner,
                } => {
                    if *private && !inside {
                        return None;
                    }
                    let prefix = if *is_static {
                        (!inside).then(|| format!("{owner}."))
                    } else {
                        receiver.as_ref().map(|receiver| format!("{receiver}."))
                    };
                    if let Some(prefix) = prefix {
                        edits.push(TextEdit::insert(span.start() - expression_start, prefix));
                    }
                }
                Use::This(span) => {
                    if let Some(receiver) = &receiver {
                        edits.push(TextEdit::new(
                            shift(*span, expression_start),
                            receiver.clone(),
                        ));
                    }
                }
            }
        }
        // An argument for a parameter the expression does not use still
        // has to run, unless it is only a value.
        for (index, value) in passed.iter().enumerate() {
            if times(index) == 0 && value.as_ref().is_some_and(|value| !is_plain(value)) {
                return None;
            }
        }
        let inlined = crate::edit::apply(&expression_text, &edits);
        if is_statement
            && invocation
                .parent()
                .is_none_or(|parent| parent.kind() != SyntaxKind::ExpressionStatement)
        {
            return None;
        }
        let replacement =
            parenthesized_for(&inlined, skip_parentheses(&expression).kind(), &invocation);
        calls.push((
            reference.path.clone(),
            TextEdit::new(invocation.span(), replacement),
        ));
    }
    let declaration_text = text_of(context, &declaration_path)?;
    let removal = remove_members(&declaration_text, std::slice::from_ref(&declaration));
    Some(Plan {
        calls,
        removal,
        declaration_path,
        other_uses,
    })
}

fn shift(span: TextSpan, by: u32) -> TextSpan {
    TextSpan::new(span.start() - by, span.end() - span.start())
}

/// A name in the inlined expression that changes with the call.
enum Use {
    /// A parameter, by its index.
    Parameter(SyntaxNode, usize),
    /// A member of the method's type, named without a receiver.
    Member {
        span: TextSpan,
        is_static: bool,
        private: bool,
        /// The type it is declared in, which names it from outside.
        owner: String,
    },
    /// `this`.
    This(TextSpan),
}

/// Whether an argument is only a value — a literal or a name — so that
/// evaluating it twice, or not at all, changes nothing.
fn is_plain(value: &SyntaxNode) -> bool {
    let value = skip_parentheses(value);
    matches!(
        value.kind(),
        SyntaxKind::NumericLiteralExpression
            | SyntaxKind::StringLiteralExpression
            | SyntaxKind::CharacterLiteralExpression
            | SyntaxKind::TrueLiteralExpression
            | SyntaxKind::FalseLiteralExpression
            | SyntaxKind::NullLiteralExpression
    ) || matches!(
        value.kind(),
        SyntaxKind::IdentifierName
            | SyntaxKind::ThisExpression
            | SyntaxKind::DefaultLiteralExpression
    )
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::support::{apply, apply_in, refuses, titles};

    fn file<'a>(files: &'a [(PathBuf, String)], name: &str) -> &'a str {
        &files
            .iter()
            .find(|(path, _)| path == Path::new(name))
            .expect("the file")
            .1
    }

    #[test]
    fn every_call_gets_the_expression_and_the_method_goes() {
        let order = "class Order\n{\n    public int count;\n    public double price;\n\n    public double Total(double discount = 0) => count * price - discount;\n\n    public double Twice() => $$Total() * 2;\n}\n";
        let shop = "class Shop\n{\n    double M(Order o) => o.Total(1 + 1) / 2;\n}\n";
        let changed = apply_in(&[("A.cs", order), ("B.cs", shop)], "Inline 'Total'");
        assert_eq!(
            file(&changed, "/p/A.cs"),
            "class Order\n{\n    public int count;\n    public double price;\n\n    public double Twice() => (count * price - 0) * 2;\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/B.cs"),
            "class Shop\n{\n    double M(Order o) => (o.count * o.price - (1 + 1)) / 2;\n}\n"
        );
    }

    #[test]
    fn keeping_the_method_and_a_block_body() {
        let source = "class C\n{\n    static int Square(int x)\n    {\n        return x * x;\n    }\n\n    int M(int a) => $$Square(a) + 1;\n}\n";
        assert_eq!(
            apply(source, "Inline and keep 'Square'"),
            "class C\n{\n    static int Square(int x)\n    {\n        return x * x;\n    }\n\n    int M(int a) => a * a + 1;\n}\n"
        );
        // `a + 1` would run twice.
        refuses(
            "class C\n{\n    static int Square(int x) => x * x;\n    int M(int a) => $$Square(a + 1);\n}\n",
            "Inline 'Square'",
        );
    }

    #[test]
    fn a_method_group_keeps_the_method() {
        let source = "class C\n{\n    static int One() => 1;\n    int M() => $$One();\n    System.Func<int> F() => One;\n}\n";
        let offered = titles(source);
        assert!(
            offered.contains(&"Inline and keep 'One'".to_string()),
            "{offered:?}"
        );
        assert!(
            !offered.contains(&"Inline 'One'".to_string()),
            "{offered:?}"
        );
        refuses(
            "class B { public virtual int V() => 1; }\nclass C : B { int M() => $$V(); }\n",
            "Inline and keep 'V'",
        );
    }
}
