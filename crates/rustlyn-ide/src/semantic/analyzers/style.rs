//! What the code says twice: a namespace the `using`s already bring in,
//! `this.` in front of a name nothing hides, a cast to the type the value
//! already has, `String` where C# has `string`.
//!
//! Roslyn reports each of these hidden — no squiggle — and all but the
//! keyword one as unnecessary, so the part that can go is drawn faded. The
//! test is always the same one: would the shorter form bind to the same
//! thing where it is written?

use rustlyn_diagnostics::Severity;
use rustlyn_semantics::{SpecialType, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::{Resolved, View};
use super::{AnalyzerDiagnostic, Facts};

/// The keyword C# has for a type, where it has one: `string` for
/// `System.String`.
pub(in crate::semantic) fn keyword_for(view: &View<'_>, symbol: SymbolId) -> Option<&'static str> {
    SpecialType::ALL
        .iter()
        .copied()
        .filter(|&special| special != SpecialType::Void)
        .find(|&special| view.compilation().special_type(special) == Some(symbol))
        .map(SpecialType::keyword)
}

/// What the nodes above one say of it, passed down from each node to its
/// children: asking each node of its ancestors costs the depth of the tree,
/// and a chain of ten thousand calls is that deep.
#[derive(Clone, Default)]
struct Written {
    /// Inside a `using` directive, where a name is written in full on
    /// purpose.
    in_using: bool,
    /// Inside the name a namespace declaration is given, which is written
    /// in full as well.
    names: std::rc::Rc<Vec<TextSpan>>,
    /// Inside the argument of a `nameof`, which names what is written
    /// rather than what it binds to.
    in_nameof: bool,
}

impl Written {
    /// Whether `node`, below what this says, is written as it is on
    /// purpose.
    fn covers(&self, node: &SyntaxNode) -> bool {
        self.in_using
            || self.in_nameof
            || self
                .names
                .iter()
                .any(|name| name.contains_span(node.span()))
    }

    /// What this says of the children of `node`.
    fn below(&self, node: &SyntaxNode) -> Self {
        let mut below = self.clone();
        match node.kind() {
            SyntaxKind::UsingDirective => below.in_using = true,
            SyntaxKind::ExternAliasDirective
            | SyntaxKind::NamespaceDeclaration
            | SyntaxKind::FileScopedNamespaceDeclaration => {
                if let Some(name) = node.children().find(|child| child.kind().is_type_node()) {
                    let mut names = (*self.names).clone();
                    names.push(name.span());
                    below.names = std::rc::Rc::new(names);
                }
            }
            SyntaxKind::InvocationExpression
                if node
                    .children()
                    .next()
                    .is_some_and(|callee| super::is_nameof(&callee)) =>
            {
                below.in_nameof = true;
            }
            _ => {}
        }
        below
    }
}

/// How many type arguments a simple name has: `List<int>` one.
fn arity(name: &SyntaxNode) -> usize {
    name.child_of_kind(SyntaxKind::TypeArgumentList)
        .map_or(0, |list| {
            list.children()
                .filter(|child| {
                    child.kind().is_type_node() || child.kind() == SyntaxKind::OmittedTypeArgument
                })
                .count()
        })
}

/// IDE0001, IDE0002 and IDE0049: names written longer than they need to
/// be.
pub(super) fn simplify_names(view: &mut View<'_>, _: &Facts, found: &mut Vec<AnalyzerDiagnostic>) {
    let mut nodes: Vec<SyntaxNode> = Vec::new();
    let mut pending = vec![(view.root.clone(), Written::default())];
    while let Some((node, above)) = pending.pop() {
        if matches!(
            node.kind(),
            SyntaxKind::QualifiedName
                | SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::IdentifierName
        ) && !above.covers(&node)
        {
            nodes.push(node.clone());
        }
        let below = above.below(&node);
        let start = pending.len();
        pending.extend(node.children().map(|child| (child, below.clone())));
        pending[start..].reverse();
    }
    for node in nodes {
        match node.kind() {
            SyntaxKind::QualifiedName => qualified_name(view, &node, found),
            SyntaxKind::SimpleMemberAccessExpression => member_access(view, &node, found),
            _ => framework_name(view, &node, found),
        }
    }
}

/// `System.String` in a type: `string`; `System.Text.StringBuilder`
/// where `using System.Text;` is there: `StringBuilder`.
fn qualified_name(view: &mut View<'_>, node: &SyntaxNode, found: &mut Vec<AnalyzerDiagnostic>) {
    // The outermost name only: `A.B.C` is one name, not two.
    if node
        .parent()
        .is_some_and(|parent| parent.kind() == SyntaxKind::QualifiedName)
    {
        return;
    }
    let Some(right) = node.children().last() else {
        return;
    };
    let Some(token) = right.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let Some(Resolved::Symbol(symbol)) = view.resolve(&token) else {
        return;
    };
    let symbols = view.compilation().symbols();
    if symbols.get(symbol).kind != SymbolKind::NamedType {
        return;
    }
    if let Some(keyword) = keyword_for(view, symbol) {
        found.push(AnalyzerDiagnostic::new(
            "IDE0049",
            Severity::Hidden,
            node.span(),
            format!("Name can be simplified to '{keyword}'"),
        ));
        return;
    }
    let context = view.context_at(node);
    let shorter = view
        .model
        .binder()
        .lookup(token.value_text(), arity(&right), &context);
    if shorter == Some(symbol) {
        found.push(
            AnalyzerDiagnostic::new(
                "IDE0001",
                Severity::Hidden,
                TextSpan::from_bounds(node.span().start(), right.span().start()),
                "Name can be simplified",
            )
            .unnecessary(),
        );
    }
}

/// `System.Console` in an expression: `Console`; `Game.Max` inside
/// `Game`: `Max`; `System.Int32.Parse`: `int.Parse`.
fn member_access(view: &mut View<'_>, node: &SyntaxNode, found: &mut Vec<AnalyzerDiagnostic>) {
    let (Some(left), Some(right)) = (node.children().next(), node.children().last()) else {
        return;
    };
    if !matches!(
        right.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) {
        return;
    }
    let Some(token) = right.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let Some(qualifier) = view.named(&left) else {
        return;
    };
    let symbols = view.compilation().symbols();
    let Some(Resolved::Symbol(symbol)) = view.resolve(&token) else {
        return;
    };
    let qualifier_kind = symbols.get(qualifier).kind;
    let fading = TextSpan::from_bounds(node.span().start(), right.span().start());
    match (qualifier_kind, symbols.get(symbol).kind) {
        // A type through its namespace.
        (SymbolKind::Namespace, SymbolKind::NamedType) => {
            if let Some(keyword) = keyword_for(view, symbol) {
                found.push(AnalyzerDiagnostic::new(
                    "IDE0049",
                    Severity::Hidden,
                    node.span(),
                    format!("Name can be simplified to '{keyword}'"),
                ));
                return;
            }
            let context = view.context_at(node);
            let shorter = view
                .model
                .binder()
                .lookup(token.value_text(), arity(&right), &context);
            if shorter == Some(symbol) {
                found.push(
                    AnalyzerDiagnostic::new(
                        "IDE0002",
                        Severity::Hidden,
                        fading,
                        "Member access can be simplified",
                    )
                    .unnecessary(),
                );
            }
        }
        // A static member of the type the code is in, through the type.
        (
            SymbolKind::NamedType,
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Method | SymbolKind::Event,
        ) => {
            let context = view.context_at(node);
            if context.enclosing_type() != Some(qualifier)
                || symbols.get(symbol).container != Some(qualifier)
                || left.kind() != SyntaxKind::IdentifierName
                || is_hidden_by_variable(view, node, token.value_text())
            {
                return;
            }
            let members = view
                .model
                .binder()
                .lookup_member(qualifier, token.value_text());
            if members.contains(&symbol) {
                found.push(
                    AnalyzerDiagnostic::new(
                        "IDE0002",
                        Severity::Hidden,
                        fading,
                        "Member access can be simplified",
                    )
                    .unnecessary(),
                );
            }
        }
        _ => {}
    }
}

/// `String`, `Int32` where C# has a keyword for it.
fn framework_name(view: &mut View<'_>, node: &SyntaxNode, found: &mut Vec<AnalyzerDiagnostic>) {
    // The right of `A.B` is the business of the name around it.
    if let Some(parent) = node.parent()
        && matches!(
            parent.kind(),
            SyntaxKind::QualifiedName | SyntaxKind::SimpleMemberAccessExpression
        )
        && parent.children().last().as_ref() == Some(node)
    {
        return;
    }
    let Some(token) = node.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    if !token
        .value_text()
        .starts_with(|c: char| c.is_ascii_uppercase())
    {
        return;
    }
    let Some(Resolved::Symbol(symbol)) = view.resolve(&token) else {
        return;
    };
    if let Some(keyword) = keyword_for(view, symbol) {
        found.push(AnalyzerDiagnostic::new(
            "IDE0049",
            Severity::Hidden,
            node.span(),
            format!("Name can be simplified to '{keyword}'"),
        ));
    }
}

/// Whether a local or a parameter called `name` is in scope at `node`, so
/// that the name alone would mean it rather than a member.
fn is_hidden_by_variable(view: &mut View<'_>, node: &SyntaxNode, name: &str) -> bool {
    if let Some(body) = view.body_for(node)
        && body.locals.iter().any(|local| local.name == name)
    {
        return true;
    }
    let context = view.context_at(node);
    let symbols = view.compilation().symbols();
    context.enclosing_member().is_some_and(|member| {
        symbols.get(member).members.iter().any(|&child| {
            symbols.get(child).kind == SymbolKind::Parameter && symbols.get(child).name == name
        })
    })
}

/// IDE0003: `this.` in front of a member that the name alone reaches.
pub(super) fn this_qualification(
    view: &mut View<'_>,
    _: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let accesses: Vec<SyntaxNode> = view
        .root
        .descendants()
        .filter(|node| {
            node.kind() == SyntaxKind::SimpleMemberAccessExpression
                && node
                    .children()
                    .next()
                    .is_some_and(|left| left.kind() == SyntaxKind::ThisExpression)
        })
        .collect();
    for access in accesses {
        let Some(right) = access.children().last() else {
            continue;
        };
        let Some(token) = right.child_token_of_kind(SyntaxKind::IdentifierToken) else {
            continue;
        };
        let Some(Resolved::Symbol(member)) = view.resolve(&token) else {
            continue;
        };
        let symbols = view.compilation().symbols();
        if !matches!(
            symbols.get(member).kind,
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Method | SymbolKind::Event
        ) || is_hidden_by_variable(view, &access, token.value_text())
        {
            continue;
        }
        let context = view.context_at(&access);
        let Some(ty) = context.enclosing_type() else {
            continue;
        };
        if !view
            .model
            .binder()
            .lookup_member(ty, token.value_text())
            .contains(&member)
        {
            continue;
        }
        found.push(
            AnalyzerDiagnostic::new(
                "IDE0003",
                Severity::Hidden,
                TextSpan::from_bounds(access.span().start(), right.span().start()),
                "Name can be simplified",
            )
            .unnecessary(),
        );
    }
}

/// IDE0004: a cast to the type its operand already has.
pub(super) fn unnecessary_casts(
    view: &mut View<'_>,
    facts: &Facts,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    let casts: Vec<SyntaxNode> = view
        .root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::CastExpression)
        .collect();
    for cast in casts {
        let Some(operand) = cast.children().last() else {
            continue;
        };
        if is_target_typed(&operand) {
            continue;
        }
        let Some(body) = facts.body_around(&cast) else {
            continue;
        };
        if body.broken {
            continue;
        }
        let (Some(result), Some(original)) = (
            body.bound.type_at(cast.span()),
            body.bound.type_at(operand.span()),
        ) else {
            continue;
        };
        if result != original || matches!(result, Type::Error | Type::Null | Type::Void) {
            continue;
        }
        let Some(close) = cast.child_token_of_kind(SyntaxKind::CloseParenToken) else {
            continue;
        };
        found.push(
            AnalyzerDiagnostic::new(
                "IDE0004",
                Severity::Hidden,
                TextSpan::from_bounds(cast.span().start(), close.span().end()),
                "Cast is redundant",
            )
            .unnecessary(),
        );
    }
}

/// Whether an expression takes its type from where it goes — a lambda, a
/// `null`, a `new()` — so that a cast is what gives it one.
fn is_target_typed(expression: &SyntaxNode) -> bool {
    let mut inner = expression.clone();
    while inner.kind() == SyntaxKind::ParenthesizedExpression {
        let Some(next) = inner.children().next() else {
            return true;
        };
        inner = next;
    }
    matches!(
        inner.kind(),
        SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::NullLiteralExpression
            | SyntaxKind::DefaultLiteralExpression
            | SyntaxKind::ImplicitObjectCreationExpression
            | SyntaxKind::CollectionExpression
            | SyntaxKind::ConditionalExpression
            | SyntaxKind::SwitchExpression
            | SyntaxKind::InterpolatedStringExpression
            | SyntaxKind::TupleExpression
            | SyntaxKind::StackAllocArrayCreationExpression
    )
}

#[cfg(test)]
mod tests {
    use super::super::tests::found_with;

    #[test]
    fn qualified_names_that_using_already_covers() {
        let text = "using System;\nusing System.Collections.Generic;\n\
                    namespace Game { class Item { } }\n\
                    class C {\n\
                      System.Collections.Generic.List<int> list;\n\
                      Game.Item item;\n\
                      System.String name;\n\
                      void M() { System.Console.WriteLine(1); var n = System.Int32.Parse(\"1\"); String s = null; Int32.Parse(\"2\"); }\n\
                    }\n";
        assert_eq!(
            found_with(text, "IDE0001"),
            vec!["System.Collections.Generic."]
        );
        assert_eq!(found_with(text, "IDE0002"), vec!["System."]);
        assert_eq!(
            found_with(text, "IDE0049"),
            vec!["System.String", "System.Int32", "String", "Int32"]
        );
    }

    #[test]
    fn a_static_member_through_its_own_type() {
        let text = "class C {\n\
                      static int count;\n\
                      static void Log() { }\n\
                      void M(int count) { C.Log(); var x = C.count; }\n\
                      void N() { var y = C.count; }\n\
                    }\n\
                    class D { void M() { var z = C.Equals(null, null); } }\n";
        assert_eq!(found_with(text, "IDE0002"), vec!["C.", "C."]);
    }

    #[test]
    fn this_that_nothing_needs() {
        let text = "class C {\n\
                      int size; int count;\n\
                      int Size() => this.size;\n\
                      C(int count) { this.count = count; this.Reset(); }\n\
                      void Reset() { int size = 0; this.size = size; }\n\
                    }\n";
        assert_eq!(found_with(text, "IDE0003"), vec!["this.", "this."]);
    }

    #[test]
    fn casts_to_what_the_value_already_is() {
        let text = "class C {\n\
                      void M(int i, object o, string s) {\n\
                        int a = (int)i;\n\
                        long b = (long)i;\n\
                        string c = (string)s;\n\
                        string d = (string)o;\n\
                        object e = (object)s;\n\
                        System.Func<int> f = (System.Func<int>)(() => 1);\n\
                        object g = (object)null;\n\
                        int h = (int)(i + 1);\n\
                      }\n\
                    }\n";
        assert_eq!(
            found_with(text, "IDE0004"),
            vec!["(int)", "(string)", "(int)"]
        );
    }
}
