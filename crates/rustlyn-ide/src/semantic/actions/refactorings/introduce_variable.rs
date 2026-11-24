//! Introduce local, introduce constant: give a selected expression a name.
//!
//! Roslyn's `IntroduceVariable` provider. The expression becomes the value
//! of a new declaration put just before the statement it is in, and the
//! expression — or every expression spelled and bound the same way, for
//! the "all occurrences" variant — becomes the name. An expression made of
//! literals only becomes a constant instead: a `const` local, or a `const`
//! field of the type.
//!
//! Moving an expression earlier changes when it is evaluated, which is only
//! the same program when it would have been evaluated there anyway. So an
//! expression is not moved out of a lambda (which runs later, or never), out
//! of the right of `&&`, `||` or `??` or a branch of `?:` (which might not
//! run), out of a loop's condition (which runs every time round), or out of
//! a statement that is the body of an `if` or a loop without braces.

use rustlyn_semantics::{Modifiers, SpecialType, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{
    camel_case, fresh_name, is_type_declaration, is_written, one_line, pascal_case, same_tokens,
    skip_parentheses,
};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(expression) = context.selected_node() else {
        return;
    };
    if !is_value_expression(context, &expression) {
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
    let Some(anchor) = anchor_statement(&expression) else {
        in_expression_body(context, &expression, &ty, &type_text, found);
        return;
    };
    let bindings = bindings_of(context, &expression);
    if bindings.is_none() {
        return;
    }
    if declares_inside(context, &expression, &anchor) {
        return;
    }
    let shown = one_line(&expression);
    let constant = is_constant(&expression, &ty, context);

    // Every expression in the same body spelled and bound the same way, and
    // movable to the same place.
    let owner = body_owner(&expression);
    let mut occurrences: Vec<SyntaxNode> = owner
        .descendants()
        .filter(|candidate| {
            candidate.span() != expression.span()
                && same_tokens(candidate, &expression)
                && anchor_statement(candidate).is_some()
                && !is_written(candidate)
        })
        .filter(|candidate| bindings_of(context, candidate) == bindings)
        .collect();
    occurrences.push(expression.clone());
    occurrences.sort_by_key(|node| node.span().start());

    let taken = context.view.names_near(&expression);
    let base = suggested_name(&expression);
    let value = skip_parentheses(&expression).text();

    let single = vec![expression.clone()];
    let mut variants: Vec<(&str, &Vec<SyntaxNode>)> = vec![("", &single)];
    if occurrences.len() > 1
        && common_anchor(&occurrences).is_some()
        && !written_between(context, &owner, &expression, &occurrences)
    {
        variants.push((" all occurrences of", &occurrences));
    }

    for (all, nodes) in variants {
        let Some(anchor) = common_anchor(nodes) else {
            continue;
        };
        if !locals_declared_before(context, &expression, &anchor) {
            continue;
        }
        if constant {
            let name = fresh_name(&pascal_case(&base), &taken);
            if let Some(edits) = constant_field(context, &expression, &type_text, &name, &value) {
                let mut edits = vec![edits];
                edits.extend(replacements(nodes, &name));
                found.push(context.local(
                    format!("Introduce constant for{all} '{shown}'"),
                    ActionKind::Extract,
                    None,
                    edits,
                ));
            }
            let name = fresh_name(&base, &taken);
            let declaration = format!("const {type_text} {name} = {value};");
            let edits = local_edits(context, nodes, &anchor, &declaration, &name);
            found.push(context.local(
                format!("Introduce local constant for{all} '{shown}'"),
                ActionKind::Extract,
                None,
                edits,
            ));
        } else {
            let name = fresh_name(&base, &taken);
            let declaration = format!("{type_text} {name} = {value};");
            let edits = local_edits(context, nodes, &anchor, &declaration, &name);
            found.push(context.local(
                format!("Introduce local for{all} '{shown}'"),
                ActionKind::Extract,
                None,
                edits,
            ));
        }
    }
}

/// An expression in an expression body (`int M() => a * b + 1;`): the
/// body becomes a block, the declaration its first statement, as Roslyn
/// does it.
fn in_expression_body(
    context: &mut Context<'_, '_>,
    expression: &SyntaxNode,
    ty: &Type,
    type_text: &str,
    found: &mut Vec<CodeAction>,
) {
    use SyntaxKind as K;
    // Nothing between the expression and the arrow may delay or skip it.
    let mut child = expression.clone();
    let mut arrow = None;
    for ancestor in expression.ancestors() {
        let first = ancestor.children().next().as_ref() == Some(&child);
        match ancestor.kind() {
            K::ArrowExpressionClause => {
                arrow = Some(ancestor.clone());
                break;
            }
            K::SimpleLambdaExpression
            | K::ParenthesizedLambdaExpression
            | K::AnonymousMethodExpression
            | K::QueryExpression
            | K::SwitchExpressionArm => return,
            K::LogicalAndExpression
            | K::LogicalOrExpression
            | K::CoalesceExpression
            | K::ConditionalExpression
            | K::ConditionalAccessExpression
                if !first =>
            {
                return;
            }
            _ => {}
        }
        child = ancestor.clone();
    }
    let Some(arrow) = arrow else {
        return;
    };
    let Some(owner) = arrow.parent().cloned() else {
        return;
    };
    if !matches!(
        owner.kind(),
        K::MethodDeclaration
            | K::LocalFunctionStatement
            | K::ConstructorDeclaration
            | K::OperatorDeclaration
            | K::ConversionOperatorDeclaration
            | K::GetAccessorDeclaration
            | K::SetAccessorDeclaration
            | K::InitAccessorDeclaration
    ) {
        return;
    }
    let (Some(body), Some(semicolon)) = (
        arrow.children().next(),
        owner.child_token_of_kind(K::SemicolonToken),
    ) else {
        return;
    };
    let Some(nothing) = super::expression_body::returns_nothing(context, &owner) else {
        return;
    };
    let Some(start) = super::expression_body::end_before(&owner, arrow.span()) else {
        return;
    };
    let constant = is_constant(expression, ty, context);
    let name = fresh_name(
        &suggested_name(expression),
        &context.view.names_near(expression),
    );
    let value = skip_parentheses(expression).text();
    let relative = TextSpan::from_bounds(
        expression.span().start() - body.span().start(),
        expression.span().end() - body.span().start(),
    );
    let rest = crate::edit::apply(&body.text(), &[TextEdit::new(relative, name.clone())]);
    let statement = if nothing {
        format!("{rest};")
    } else {
        format!("return {rest};")
    };
    let newline = context.newline();
    let indent = context.indentation_at(owner.span().start());
    let inner = format!("{indent}{}", context.indent_unit());
    let (title, declaration) = if constant {
        (
            "Introduce local constant for",
            format!("const {type_text} {name} = {value};"),
        )
    } else {
        (
            "Introduce local for",
            format!("{type_text} {name} = {value};"),
        )
    };
    let text = format!(
        "{newline}{indent}{{{newline}{inner}{declaration}{newline}{inner}{statement}{newline}{indent}}}"
    );
    found.push(context.local(
        format!("{title} '{}'", one_line(expression)),
        ActionKind::Extract,
        None,
        vec![TextEdit::new(
            TextSpan::from_bounds(start, semicolon.span().end()),
            text,
        )],
    ));
}

/// Whether `node` is an expression with a value that can be named: not a
/// type, not a method group, not something being assigned to.
pub(super) fn is_value_expression(context: &mut Context<'_, '_>, node: &SyntaxNode) -> bool {
    use SyntaxKind as K;
    let kind = node.kind();
    if !kind.is_expression()
        || matches!(
            kind,
            K::SimpleLambdaExpression
                | K::ParenthesizedLambdaExpression
                | K::AnonymousMethodExpression
                | K::DeclarationExpression
                | K::ThrowExpression
                | K::ArrayInitializerExpression
                | K::CollectionExpression
                | K::DefaultLiteralExpression
                | K::NullLiteralExpression
                | K::RefExpression
                | K::PreIncrementExpression
                | K::PreDecrementExpression
                | K::PostIncrementExpression
                | K::PostDecrementExpression
        )
        || super::super::text::precedence(kind) == 1
        || kind.is_type_node() && !is_name_expression(node)
    {
        return false;
    }
    if is_written(node) {
        return false;
    }
    let Some(parent) = node.parent() else {
        return false;
    };
    match parent.kind() {
        // `a.B`: `B` alone is no expression; `F(x)`: `F` is a method group.
        K::SimpleMemberAccessExpression | K::PointerMemberAccessExpression
            if parent.children().last().as_ref() == Some(node) =>
        {
            return false;
        }
        K::InvocationExpression if parent.children().next().as_ref() == Some(node) => {
            return false;
        }
        K::NameColon | K::NameEquals | K::ConditionalAccessExpression => return false,
        _ => {}
    }
    // A name that is a type or a namespace names no value, and one that is
    // a local or a parameter has a name already.
    if matches!(
        kind,
        K::IdentifierName | K::SimpleMemberAccessExpression | K::GenericName
    ) && let Some(token) = node
        .descendant_tokens()
        .filter(|token| token.kind() == K::IdentifierToken)
        .last()
    {
        match context.view.resolve(&token) {
            Some(Resolved::Symbol(symbol)) => {
                if matches!(
                    context.view.compiled().symbols().get(symbol).kind,
                    SymbolKind::NamedType
                        | SymbolKind::Namespace
                        | SymbolKind::Method
                        | SymbolKind::Parameter
                ) {
                    return false;
                }
            }
            Some(Resolved::Local { .. }) if kind == K::IdentifierName => return false,
            _ => {}
        }
    }
    // `Kind.Melee` where `Kind` is both a property and its enum type: what
    // is to the left of a static member is the type, not the property.
    if parent.kind() == K::SimpleMemberAccessExpression
        && parent.children().next().as_ref() == Some(node)
        && let Some(member) = parent.children().last()
        && let Some(token) = member
            .descendant_tokens()
            .find(|token| token.kind() == K::IdentifierToken)
        && let Some(Resolved::Symbol(symbol)) = context.view.resolve(&token)
    {
        let symbols = context.view.compiled().symbols();
        let found = symbols.get(symbol);
        let in_enum = found
            .container
            .is_some_and(|container| symbols.get(container).type_kind() == Some(TypeKind::Enum));
        if found.modifiers.contains(Modifiers::STATIC)
            || found.modifiers.contains(Modifiers::CONST)
            || found.kind == SymbolKind::NamedType
            || in_enum
        {
            return false;
        }
    }
    true
}

fn is_name_expression(node: &SyntaxNode) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) && node.parent().is_some_and(|parent| {
        parent.kind().is_expression_node()
            || matches!(
                parent.kind(),
                SyntaxKind::Argument | SyntaxKind::EqualsValueClause | SyntaxKind::ReturnStatement
            )
    })
}

/// The statement a declaration for `node` goes in front of: the statement
/// `node` is in, when nothing between them makes moving it earlier change
/// when or whether it runs.
pub(super) fn anchor_statement(node: &SyntaxNode) -> Option<SyntaxNode> {
    use SyntaxKind as K;
    let mut child = node.clone();
    for ancestor in node.ancestors() {
        let first = ancestor.children().next().as_ref() == Some(&child);
        match ancestor.kind() {
            K::SimpleLambdaExpression
            | K::ParenthesizedLambdaExpression
            | K::AnonymousMethodExpression
            | K::LocalFunctionStatement
            | K::ArrowExpressionClause
            | K::QueryExpression
            | K::SwitchExpressionArm
            | K::WhenClause
            | K::CatchFilterClause => return None,
            K::LogicalAndExpression | K::LogicalOrExpression | K::CoalesceExpression if !first => {
                return None;
            }
            K::ConditionalExpression if !first => return None,
            K::ConditionalAccessExpression if !first => return None,
            kind if super::super::text::is_statement(kind) => {
                if matches!(kind, K::WhileStatement | K::DoStatement | K::ForStatement) {
                    return None;
                }
                let parent = ancestor.parent()?;
                return matches!(parent.kind(), K::Block | K::SwitchSection).then_some(ancestor);
            }
            _ => {}
        }
        child = ancestor.clone();
    }
    None
}

/// The statement in front of which one declaration serves every node: in
/// the innermost block holding them all, the statement that holds the
/// first.
fn common_anchor(nodes: &[SyntaxNode]) -> Option<SyntaxNode> {
    let anchors: Vec<SyntaxNode> = nodes.iter().map(anchor_statement).collect::<Option<_>>()?;
    let first = anchors.first()?;
    let block = std::iter::once(first.clone())
        .chain(first.ancestors())
        .filter(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::Block | SyntaxKind::SwitchSection
            )
        })
        .find(|block| {
            anchors
                .iter()
                .all(|anchor| block.span().contains_span(anchor.span()))
        })?;
    let earliest = nodes.iter().map(|node| node.span().start()).min()?;
    block
        .children()
        .find(|child| child.span().contains(earliest))
        .filter(|child| super::super::text::is_statement(child.kind()))
}

/// What each name in `node` binds to, in order; `None` when one of them
/// does not bind.
fn bindings_of(context: &mut Context<'_, '_>, node: &SyntaxNode) -> Option<Vec<Resolved>> {
    let tokens: Vec<_> = node
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .collect();
    tokens
        .iter()
        .map(|token| context.view.resolve(token))
        .collect()
}

/// Whether something `expression` reads is written anywhere from the first
/// occurrence to the last: then the later ones would see a value the first
/// did not.
fn written_between(
    context: &mut Context<'_, '_>,
    owner: &SyntaxNode,
    expression: &SyntaxNode,
    occurrences: &[SyntaxNode],
) -> bool {
    let (Some(first), Some(last)) = (occurrences.first(), occurrences.last()) else {
        return false;
    };
    let range = TextSpan::from_bounds(first.span().start(), last.span().end());
    let read: Vec<Resolved> = expression
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .filter_map(|token| context.view.resolve(&token))
        .collect();
    let writes: Vec<_> = owner
        .descendant_tokens()
        .filter(|token| {
            token.kind() == SyntaxKind::IdentifierToken
                && range.contains_span(token.span())
                && is_written(token.parent())
        })
        .collect();
    // A call can write anything; only a body without calls between the
    // occurrences is known not to.
    let calls = owner.descendants().any(|node| {
        range.contains_span(node.span())
            && matches!(
                node.kind(),
                SyntaxKind::InvocationExpression | SyntaxKind::ObjectCreationExpression
            )
            && !occurrences
                .iter()
                .any(|occurrence| occurrence.span().contains_span(node.span()))
    });
    let symbols = context.view.compiled().symbols();
    let reads_state = read.iter().any(|resolved| {
        matches!(resolved, Resolved::Symbol(symbol)
            if matches!(symbols.get(*symbol).kind, SymbolKind::Field | SymbolKind::Property))
    });
    if calls && reads_state {
        return true;
    }
    writes.iter().any(|token| {
        context
            .view
            .resolve(token)
            .is_some_and(|written| read.contains(&written))
    })
}

/// Whether `node` uses a local declared inside the statement it would move
/// in front of: `o is int n && n + 1 > 2`, where `n + 1` needs `n`.
fn declares_inside(context: &mut Context<'_, '_>, node: &SyntaxNode, anchor: &SyntaxNode) -> bool {
    let tokens: Vec<_> = node
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .collect();
    tokens.iter().any(|token| {
        matches!(
            context.view.resolve(token),
            Some(Resolved::Local { span, .. }) if anchor.span().contains_span(span)
        )
    })
}

/// Whether every local `node` reads is declared before `anchor`, in a
/// block that `anchor` is inside.
fn locals_declared_before(
    context: &mut Context<'_, '_>,
    node: &SyntaxNode,
    anchor: &SyntaxNode,
) -> bool {
    let tokens: Vec<_> = node
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .collect();
    let root = context.view.syntax_root().clone();
    tokens
        .iter()
        .all(|token| match context.view.resolve(token) {
            Some(Resolved::Local { span, .. }) => {
                if span.start() >= anchor.span().start() {
                    return false;
                }
                let Some(declared) = root.find_token(span.start()) else {
                    return false;
                };
                let scope = declared.parent().ancestors().find(|ancestor| {
                    matches!(
                        ancestor.kind(),
                        SyntaxKind::Block
                            | SyntaxKind::SwitchSection
                            | SyntaxKind::ParenthesizedLambdaExpression
                            | SyntaxKind::SimpleLambdaExpression
                            | SyntaxKind::LocalFunctionStatement
                            | SyntaxKind::MethodDeclaration
                    )
                });
                scope.is_none_or(|scope| scope.span().contains_span(anchor.span()))
            }
            _ => true,
        })
}

/// The member, lambda or local function whose body holds `node`: where
/// other occurrences are looked for.
fn body_owner(node: &SyntaxNode) -> SyntaxNode {
    node.ancestors()
        .find(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
                    | SyntaxKind::LocalFunctionStatement
            ) || ancestor
                .parent()
                .is_some_and(|parent| is_type_declaration(parent.kind()))
                || ancestor.kind() == SyntaxKind::GlobalStatement
        })
        .unwrap_or_else(|| node.clone())
}

/// Whether `node` is a constant: literals and operators only, of a type a
/// `const` can have.
fn is_constant(node: &SyntaxNode, ty: &Type, context: &Context<'_, '_>) -> bool {
    let only_literals = node.descendant_tokens().all(|token| {
        let kind = token.kind();
        kind.is_literal_token()
            || kind.is_punctuation()
            || kind == SyntaxKind::TrueKeyword
            || kind == SyntaxKind::FalseKeyword
    }) && node
        .descendant_tokens()
        .any(|token| token.kind().is_literal_token());
    if !only_literals {
        return false;
    }
    let Type::Named { symbol, .. } = ty else {
        return false;
    };
    let qualified = context.view.compiled().symbols().qualified_name(*symbol);
    SpecialType::ALL.iter().any(|special| {
        special.metadata_name() == qualified
            && !matches!(special, SpecialType::Object | SpecialType::Void)
    })
}

/// A name for the value of `node`, after what it calls or reads: `length`
/// for `text.Length`, `name` for `GetName()`, `builder` for
/// `new Builder()`, `v` for anything else.
pub(super) fn suggested_name(node: &SyntaxNode) -> String {
    let node = skip_parentheses(node);
    let last_name = |node: &SyntaxNode| {
        node.descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .last()
            .map(|token| token.value_text().to_string())
    };
    let word = match node.kind() {
        SyntaxKind::InvocationExpression => node.children().next().and_then(|callee| {
            let name = match callee.kind() {
                SyntaxKind::SimpleMemberAccessExpression => callee.children().last(),
                _ => Some(callee),
            }?;
            let name = name
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
            let name = name.value_text();
            Some(match name.strip_prefix("Get") {
                Some(rest) if rest.starts_with(char::is_uppercase) => rest.to_string(),
                _ => name.to_string(),
            })
        }),
        SyntaxKind::SimpleMemberAccessExpression => {
            node.children().last().and_then(|name| last_name(&name))
        }
        SyntaxKind::ObjectCreationExpression => node
            .children()
            .find(|child| child.kind().is_type_node())
            .and_then(|ty| {
                ty.descendant_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| token.value_text().to_string())
            }),
        _ => None,
    };
    word.map(|word| camel_case(&word))
        .filter(|word| super::super::text::is_identifier(word))
        .unwrap_or_else(|| "v".to_string())
}

/// Each of `nodes` replaced by `name`.
fn replacements(nodes: &[SyntaxNode], name: &str) -> Vec<TextEdit> {
    nodes
        .iter()
        .map(|node| TextEdit::new(node.span(), name))
        .collect()
}

/// The declaration put in front of `anchor` and every node replaced by the
/// name; when the only node is the whole of an expression statement, that
/// statement becomes the declaration.
fn local_edits(
    context: &Context<'_, '_>,
    nodes: &[SyntaxNode],
    anchor: &SyntaxNode,
    declaration: &str,
    name: &str,
) -> Vec<TextEdit> {
    if let [only] = nodes
        && let Some(statement) = only.parent()
        && statement.kind() == SyntaxKind::ExpressionStatement
    {
        return vec![TextEdit::new(statement.span(), declaration)];
    }
    let indent = context.indentation_at(anchor.span().start());
    let mut edits = vec![TextEdit::insert(
        anchor.span().start(),
        format!("{declaration}{}{indent}", context.newline()),
    )];
    edits.extend(replacements(nodes, name));
    edits
}

/// A `private const` field declared first in the type around `node`.
fn constant_field(
    context: &Context<'_, '_>,
    node: &SyntaxNode,
    type_text: &str,
    name: &str,
    value: &str,
) -> Option<TextEdit> {
    let ty = node
        .ancestors()
        .find(|ancestor| is_type_declaration(ancestor.kind()))?;
    let first = ty
        .children()
        .find(|child| super::super::text::is_member(child.kind()))?;
    let at = first.full_span().start();
    let at = if context
        .slice(TextSpan::from_bounds(
            super::super::text::line_start(&context.text, at),
            at,
        ))
        .trim()
        .is_empty()
    {
        super::super::text::line_start(&context.text, at)
    } else {
        at
    };
    let indent = context.indentation_at(first.span().start());
    let newline = context.newline();
    let gap = if first.kind() == SyntaxKind::FieldDeclaration {
        ""
    } else {
        newline
    };
    Some(TextEdit::insert(
        at,
        format!("{indent}private const {type_text} {name} = {value};{newline}{gap}"),
    ))
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses, titles};

    #[test]
    fn a_selected_expression_becomes_a_local_before_its_statement() {
        let source =
            "class C\n{\n    int M(int a, int b)\n    {\n        return [|a * b|] + 1;\n    }\n}\n";
        assert_eq!(
            apply(source, "Introduce local for 'a * b'"),
            "class C\n{\n    int M(int a, int b)\n    {\n        int v = a * b;\n        return v + 1;\n    }\n}\n"
        );
    }

    #[test]
    fn every_occurrence_is_replaced_when_asked() {
        let source = "class C\n{\n    void M(string s)\n    {\n        System.Console.WriteLine([|s.Length|]);\n        System.Console.WriteLine(s.Length + 1);\n    }\n}\n";
        assert_eq!(
            apply(source, "Introduce local for all occurrences of 's.Length'"),
            "class C\n{\n    void M(string s)\n    {\n        int length = s.Length;\n        System.Console.WriteLine(length);\n        System.Console.WriteLine(length + 1);\n    }\n}\n"
        );
    }

    #[test]
    fn a_literal_becomes_a_constant() {
        let source = "class C\n{\n    double Area(double r)\n    {\n        return [|3.14|] * r * r;\n    }\n}\n";
        assert_eq!(
            apply(source, "Introduce constant for '3.14'"),
            "class C\n{\n    private const double V = 3.14;\n\n    double Area(double r)\n    {\n        return V * r * r;\n    }\n}\n"
        );
        assert_eq!(
            apply(source, "Introduce local constant for '3.14'"),
            "class C\n{\n    double Area(double r)\n    {\n        const double v = 3.14;\n        return v * r * r;\n    }\n}\n"
        );
        refuses(source, "Introduce local for '3.14'");
    }

    #[test]
    fn a_whole_expression_statement_becomes_the_declaration() {
        let source = "class C\n{\n    int Count() => 1;\n    void M()\n    {\n        [|Count()|];\n    }\n}\n";
        assert_eq!(
            apply(source, "Introduce local for 'Count()'"),
            "class C\n{\n    int Count() => 1;\n    void M()\n    {\n        int count = Count();\n    }\n}\n"
        );
    }

    #[test]
    fn nothing_is_moved_out_of_a_condition_that_guards_it() {
        refuses(
            "class C\n{\n    bool M(string s)\n    {\n        return s != null && [|s.Length|] > 0;\n    }\n}\n",
            "Introduce local for 's.Length'",
        );
        refuses(
            "class C\n{\n    void M(int n)\n    {\n        while ([|n * 2|] < 10) n++;\n    }\n}\n",
            "Introduce local for 'n * 2'",
        );
        let offered = titles(
            "class C\n{\n    void M()\n    {\n        [|System.Console|].WriteLine();\n    }\n}\n",
        );
        assert!(offered.is_empty(), "{offered:?}");
    }

    #[test]
    fn an_expression_body_becomes_a_block() {
        let source = "class C\n{\n    int M(int a, int b) => [|a * b|] + 1;\n}\n";
        assert_eq!(
            apply(source, "Introduce local for 'a * b'"),
            "class C\n{\n    int M(int a, int b)\n    {\n        int v = a * b;\n        return v + 1;\n    }\n}\n"
        );
    }

    #[test]
    fn a_new_object_is_named_after_its_type() {
        let source = "class Builder { }\nclass C\n{\n    object M()\n    {\n        return [|new Builder()|];\n    }\n}\n";
        assert_eq!(
            apply(source, "Introduce local for 'new Builder()'"),
            "class Builder { }\nclass C\n{\n    object M()\n    {\n        Builder builder = new Builder();\n        return builder;\n    }\n}\n"
        );
    }
}
