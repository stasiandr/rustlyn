//! Which `using` directives a file does not need: what IDE0005 fades and
//! "Remove unnecessary usings" removes.
//!
//! A `using` is needed when some name in the file binds through it: a type
//! written without its namespace that lives in the namespace the directive
//! names, an extension method called on a value and declared in a class of
//! that namespace, a member of the type a `using static` names, or the
//! alias a `using X =` declares. Every identifier in the file is resolved
//! and credited to the directives it could have come through.
//!
//! Where the answer is not certain, the directive is kept. A name that does
//! not bind keeps every directive whose namespace has a type (or an
//! extension method) of that name. A query expression, a `foreach`, an
//! `await`, a collection initializer or a deconstruction can call extension
//! methods no identifier names, and keeps every namespace that declares
//! one of the methods those need. A file with code that the preprocessor
//! left out keeps everything, since that code is not in the tree to be
//! looked at. And a directive the binder cannot resolve is not this
//! analysis's to judge.

use std::collections::HashSet;

use rustlyn_semantics::{MethodKind, SymbolId, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::{Resolved, View};

/// What a directive brings into scope.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Brings {
    /// `using System.Text;`
    Namespace(SymbolId),
    /// `using static System.Math;`
    Static(SymbolId),
    /// `using Map = System.Collections.Generic.Dictionary<int, int>;`
    Alias(String),
}

struct Directive {
    span: TextSpan,
    brings: Brings,
    /// Where it applies: the file, or the namespace block it is in.
    scope: TextSpan,
    needed: bool,
}

/// The spans of the `using` directives of the file `view` shows that no
/// name in it needs, in order.
pub(crate) fn unnecessary_usings(view: &mut View<'_>) -> Vec<TextSpan> {
    let root = view.root.clone();
    if root.descendant_tokens().any(|token| {
        token
            .leading_trivia()
            .iter()
            .any(|trivia| trivia.kind() == SyntaxKind::DisabledTextTrivia)
    }) {
        return Vec::new();
    }

    let mut directives: Vec<Directive> = Vec::new();
    let mut duplicates: Vec<TextSpan> = Vec::new();
    for using in root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::UsingDirective)
    {
        if using
            .child_token_of_kind(SyntaxKind::GlobalKeyword)
            .is_some()
        {
            continue;
        }
        let Some(scope) = using.parent().map(SyntaxNode::span) else {
            continue;
        };
        let Some(brings) = brings(view, &using) else {
            continue;
        };
        // The same directive twice in one scope: the second is not needed.
        if directives
            .iter()
            .any(|other| other.brings == brings && other.scope == scope)
        {
            duplicates.push(using.span());
            continue;
        }
        directives.push(Directive {
            span: using.span(),
            brings,
            scope,
            needed: false,
        });
    }
    if directives.is_empty() && duplicates.is_empty() {
        return Vec::new();
    }

    let tokens: Vec<SyntaxToken> = root
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .filter(|token| {
            !token
                .parent()
                .ancestors()
                .any(|ancestor| ancestor.kind() == SyntaxKind::UsingDirective)
        })
        .collect();
    for token in &tokens {
        credit(view, token, &mut directives);
    }
    implicit_extensions(view, &root, &mut directives);

    let mut unnecessary: Vec<TextSpan> = directives
        .iter()
        .filter(|directive| !directive.needed)
        .map(|directive| directive.span)
        .chain(duplicates)
        .collect();
    unnecessary.sort_by_key(|span| span.start());
    unnecessary
}

/// What `using` brings in, when the binder can say.
fn brings(view: &mut View<'_>, using: &SyntaxNode) -> Option<Brings> {
    if let Some(alias) = using.child_of_kind(SyntaxKind::NameEquals) {
        let name = alias
            .descendant_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
        return Some(Brings::Alias(name.value_text().to_string()));
    }
    let name = using.children().find(|child| child.kind().is_type_node())?;
    if using
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some()
    {
        let last = name
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .last()?;
        return match view.model.symbol_at(last.parent()) {
            Some(symbol)
                if view.compilation().symbols().get(symbol).kind == SymbolKind::NamedType =>
            {
                Some(Brings::Static(symbol))
            }
            _ => None,
        };
    }
    let symbols = view.compilation().symbols();
    let mut current = view.compilation().global_namespace();
    let text = name.text();
    for part in text.trim().trim_start_matches("global::").split('.') {
        current = symbols.lookup_namespace(current, part.trim())?;
    }
    Some(Brings::Namespace(current))
}

/// Whether the name `token` is written after a `.` (or `::`): looked up in
/// what is to its left, not through any directive.
fn is_qualified(token: &SyntaxToken) -> bool {
    let name = token.parent();
    let Some(parent) = name.parent() else {
        return false;
    };
    match parent.kind() {
        SyntaxKind::QualifiedName
        | SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::AliasQualifiedName => parent.children().last().as_ref() == Some(name),
        SyntaxKind::MemberBindingExpression => true,
        _ => false,
    }
}

/// The namespaces the code at `node` is declared in, outward: what it sees
/// without any directive.
fn enclosing_namespaces(view: &View<'_>, node: &SyntaxNode) -> HashSet<SymbolId> {
    let symbols = view.compilation().symbols();
    let global = view.compilation().global_namespace();
    let mut found = HashSet::from([global]);
    let mut declarations: Vec<SyntaxNode> = node
        .ancestors()
        .filter(|ancestor| ancestor.kind() == SyntaxKind::NamespaceDeclaration)
        .collect();
    declarations.extend(
        view.root
            .children()
            .filter(|child| child.kind() == SyntaxKind::FileScopedNamespaceDeclaration),
    );
    for declaration in declarations {
        let Some(name) = declaration
            .children()
            .find(|child| child.kind().is_type_node())
        else {
            continue;
        };
        let mut current = global;
        for part in name.text().trim().split('.') {
            match symbols.lookup_namespace(current, part.trim()) {
                Some(next) => {
                    current = next;
                    found.insert(current);
                }
                None => break,
            }
        }
    }
    found
}

/// Marks what `token` needs: the directive its type came through, the
/// `using static` its member came through, the alias it is.
fn credit(view: &mut View<'_>, token: &SyntaxToken, directives: &mut [Directive]) {
    let span = token.span();
    let text = token.value_text().to_string();
    let in_scope = |directive: &Directive| directive.scope.contains_span(span);
    // An alias is needed wherever its name is written.
    for directive in directives.iter_mut() {
        if directive.brings == Brings::Alias(text.clone()) && in_scope(directive) {
            directive.needed = true;
        }
    }
    let qualified = is_qualified(token);
    let resolved = view.resolve(token);
    let symbols = view.compilation().symbols();
    let Some(resolved) = resolved else {
        // Nothing bound: keep whatever could have supplied the name.
        for directive in directives
            .iter_mut()
            .filter(|directive| in_scope(directive))
        {
            let could = match &directive.brings {
                Brings::Namespace(namespace) => {
                    if qualified {
                        view.compilation()
                            .extension_methods(&text)
                            .iter()
                            .any(|&method| namespace_of(view, method) == Some(*namespace))
                    } else {
                        symbols
                            .lookup(*namespace, &text)
                            .iter()
                            .any(|&member| symbols.get(member).kind == SymbolKind::NamedType)
                            || symbols
                                .lookup(*namespace, &format!("{text}Attribute"))
                                .iter()
                                .any(|&member| symbols.get(member).kind == SymbolKind::NamedType)
                    }
                }
                Brings::Static(ty) => !symbols.lookup(*ty, &text).is_empty(),
                Brings::Alias(_) => false,
            };
            if could {
                directive.needed = true;
            }
        }
        return;
    };
    let Resolved::Symbol(symbol) = resolved else {
        return;
    };
    let found = symbols.get(symbol);
    let is_constructor = found
        .as_method()
        .is_some_and(|method| method.method_kind == MethodKind::Constructor);
    let is_extension = found.as_method().is_some_and(|method| method.is_extension);
    if found.kind == SymbolKind::NamedType || is_constructor {
        if qualified {
            return;
        }
        let ty = if is_constructor {
            match found.container {
                Some(container) => container,
                None => return,
            }
        } else {
            symbol
        };
        let Some(namespace) = namespace_of(view, ty) else {
            return;
        };
        // Declared where the code is: no directive was needed for it.
        if enclosing_namespaces(view, token.parent()).contains(&namespace) {
            return;
        }
        for directive in directives.iter_mut() {
            if in_scope(directive) && directive.brings == Brings::Namespace(namespace) {
                directive.needed = true;
            }
            // `using static Outer;` brings in its nested types too.
            if in_scope(directive)
                && found
                    .container
                    .is_some_and(|container| directive.brings == Brings::Static(container))
            {
                directive.needed = true;
            }
        }
        return;
    }
    if !matches!(
        found.kind,
        SymbolKind::Method | SymbolKind::Field | SymbolKind::Property | SymbolKind::Event
    ) {
        return;
    }
    let Some(container) = found.container else {
        return;
    };
    if is_extension && qualified {
        // `values.Where(...)`: through the namespace of the class that
        // declares it, or a `using static` of that class.
        let namespace = namespace_of(view, container);
        for directive in directives
            .iter_mut()
            .filter(|directive| in_scope(directive))
        {
            if Some(&directive.brings) == namespace.map(Brings::Namespace).as_ref()
                || directive.brings == Brings::Static(container)
            {
                directive.needed = true;
            }
        }
        return;
    }
    if !qualified {
        for directive in directives
            .iter_mut()
            .filter(|directive| in_scope(directive))
        {
            if directive.brings == Brings::Static(container) {
                directive.needed = true;
            }
        }
    }
}

/// The namespace a type (or a member of one) is in, past any types it is
/// nested in.
fn namespace_of(view: &View<'_>, symbol: SymbolId) -> Option<SymbolId> {
    let symbols = view.compilation().symbols();
    let mut current = symbols.get(symbol).container;
    while let Some(container) = current {
        if symbols.get(container).kind == SymbolKind::Namespace {
            return Some(container);
        }
        current = symbols.get(container).container;
    }
    None
}

/// Keeps the namespaces whose extension methods the file can call without
/// naming them.
fn implicit_extensions(view: &View<'_>, root: &SyntaxNode, directives: &mut [Directive]) {
    let mut names: Vec<&str> = Vec::new();
    let mut query = false;
    for node in root.descendants() {
        match node.kind() {
            SyntaxKind::QueryExpression => query = true,
            SyntaxKind::ForEachStatement | SyntaxKind::ForEachVariableStatement => {
                names.push("GetEnumerator");
                names.push("GetAsyncEnumerator");
                if node.kind() == SyntaxKind::ForEachVariableStatement {
                    names.push("Deconstruct");
                }
            }
            SyntaxKind::AwaitExpression => names.push("GetAwaiter"),
            SyntaxKind::CollectionInitializerExpression | SyntaxKind::CollectionExpression => {
                names.push("Add");
            }
            SyntaxKind::TupleExpression
                if node.parent().is_some_and(|parent| {
                    parent.kind() == SyntaxKind::SimpleAssignmentExpression
                }) =>
            {
                names.push("Deconstruct");
            }
            SyntaxKind::PositionalPatternClause | SyntaxKind::ParenthesizedVariableDesignation => {
                names.push("Deconstruct");
            }
            SyntaxKind::UsingStatement | SyntaxKind::FixedStatement => {
                names.push("Dispose");
                names.push("GetPinnableReference");
            }
            _ => {}
        }
    }
    let compilation = view.compilation();
    let candidates: Vec<&str> = if query {
        compilation.extension_method_names().collect()
    } else {
        names
    };
    let mut namespaces = HashSet::new();
    for name in candidates {
        for &method in compilation.extension_methods(name) {
            if let Some(namespace) = namespace_of(view, method) {
                namespaces.insert(namespace);
            }
        }
    }
    for directive in directives.iter_mut() {
        if let Brings::Namespace(namespace) = directive.brings
            && namespaces.contains(&namespace)
        {
            directive.needed = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::semantic::tests::compile;

    fn unnecessary(files: &[(&str, &str)]) -> Vec<String> {
        let semantic = compile(files, false).expect("compiles");
        let mut view = semantic
            .view_of(Path::new("/p/A.cs"), None)
            .expect("a view");
        let text = files[0].1;
        unnecessary_usings(&mut view)
            .into_iter()
            .map(|span| text[span.start() as usize..span.end() as usize].to_string())
            .collect()
    }

    #[test]
    fn a_using_nothing_binds_through_is_unnecessary() {
        let text = "using System;\nusing System.Collections.Generic;\nusing System.Text;\nclass C\n{\n    List<int> items = new List<int>();\n}\n";
        let found = unnecessary(&[
            ("A.cs", text),
            ("B.cs", "namespace System.Text { class Builder { } }\n"),
        ]);
        assert_eq!(found, ["using System;", "using System.Text;"]);
    }

    #[test]
    fn a_type_from_the_namespace_keeps_it() {
        let text = "using System;\nclass C\n{\n    void M() { Console.WriteLine(1); }\n}\n";
        assert!(unnecessary(&[("A.cs", text)]).is_empty());
    }

    #[test]
    fn extension_methods_keep_their_namespace() {
        let text = "using Tools;\nclass C\n{\n    int M(string s) => s.Twice();\n}\n";
        let tools = "namespace Tools { static class Extensions { public static int Twice(this string s) => 2; } }\n";
        assert!(unnecessary(&[("A.cs", text), ("B.cs", tools)]).is_empty());
        let unused = "using Tools;\nclass C\n{\n    int M(string s) => s.Length;\n}\n";
        assert_eq!(
            unnecessary(&[("A.cs", unused), ("B.cs", tools)]),
            ["using Tools;"]
        );
    }

    #[test]
    fn static_usings_aliases_and_duplicates() {
        let text = "using static System.Math;\nusing M = System.Math;\nusing N = System.Console;\nusing System;\nusing System;\nclass C\n{\n    int A() => Abs(-1) + M.Max(1, 2);\n    void B() => Console.WriteLine();\n}\n";
        assert_eq!(
            unnecessary(&[("A.cs", text)]),
            ["using N = System.Console;", "using System;"]
        );
    }

    #[test]
    fn a_namespace_the_code_is_in_needs_no_using() {
        let text = "using Game;\nnamespace Game\n{\n    class C { Player p; }\n}\n";
        let other = "namespace Game { class Player { } }\n";
        assert_eq!(
            unnecessary(&[("A.cs", text), ("B.cs", other)]),
            ["using Game;"]
        );
    }

    #[test]
    fn a_name_that_does_not_bind_keeps_what_could_supply_it() {
        let text = "using System.Text;\nclass C\n{\n    Builder b = Missing.Make();\n}\n";
        let other = "namespace System.Text { class Builder { } }\n";
        assert!(unnecessary(&[("A.cs", text), ("B.cs", other)]).is_empty());
    }
}
