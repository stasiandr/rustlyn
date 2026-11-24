//! `override` and `partial` completion: members written out whole.
//!
//! After `override` in a class, Roslyn's `OverrideCompletionProvider` lists
//! what the base classes let it override and has not been yet, and choosing
//! one writes the member — its accessibility, signature, and a body that
//! calls the base (or throws, for an abstract one). The modifiers typed so
//! far are rewritten with it, so `override Eq` becomes
//! `public override bool Equals(object obj) { … }` and not
//! `override public override …`.
//!
//! After `partial`, `PartialMethodCompletionProvider` does the same for the
//! partial methods declared in some part of the type and not yet
//! implemented in any.

use std::collections::HashSet;

use rustlyn_semantics::{Accessibility, Modifiers, RefKind, SymbolId, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::context::{Site, is_modifier, is_type_declaration};
use super::{Completion, CompletionKind, View, indentation_at, newline_of};
use crate::edit::TextEdit;

/// The overridable members of the base classes, after `override`.
pub(super) fn complete(
    view: &mut View<'_>,
    text: &str,
    site: &Site,
    first: &SyntaxToken,
    items: &mut Vec<Completion>,
) {
    let Some(declaration) = first
        .parent()
        .ancestors()
        .find(|node| is_type_declaration(node.kind()))
    else {
        return;
    };
    let Some(ty) = type_symbol(view, &declaration) else {
        return;
    };
    let written = modifiers_between(view, first, site.start);
    let accessibility = typed_accessibility(view, first, site.start);
    let simple_system = view
        .namespaces_in_scope(&declaration)
        .into_iter()
        .any(|namespace| view.compilation().symbols().qualified_name(namespace) == "System");
    let layout = Layout {
        indent: indentation_at(text, first.span().start()).to_string(),
        newline: newline_of(text),
    };
    let symbols = view.compilation().symbols();

    // Already overridden here, by signature.
    let mut seen: HashSet<String> = symbols
        .get(ty)
        .members
        .iter()
        .filter(|&&member| symbols.get(member).modifiers.contains(Modifiers::OVERRIDE))
        .map(|&member| signature_key(view, member))
        .collect();

    // The base classes, nearest first.
    let mut current = ty;
    let mut visited = HashSet::new();
    while let Some(base) = base_class(view, current) {
        if !visited.insert(base) {
            break;
        }
        let from_metadata = view.compilation().is_from_metadata(base);
        for &member in &symbols.get(base).members {
            let found = symbols.get(member);
            let overridable = found.modifiers.contains(Modifiers::VIRTUAL)
                || found.modifiers.contains(Modifiers::ABSTRACT)
                || found.modifiers.contains(Modifiers::OVERRIDE);
            let kind_fits = match found.kind {
                SymbolKind::Method => found.as_method().is_some_and(|method| {
                    method.method_kind == rustlyn_semantics::MethodKind::Ordinary
                }),
                SymbolKind::Property | SymbolKind::Event => true,
                _ => false,
            };
            if !overridable || !kind_fits || found.modifiers.contains(Modifiers::STATIC) {
                continue;
            }
            let key = signature_key(view, member);
            if !seen.insert(key) {
                continue;
            }
            // A sealed override ends the line: nothing further down it can
            // be overridden, and it is not offered itself.
            if found.modifiers.contains(Modifiers::SEALED) {
                continue;
            }
            let visible = match found.accessibility {
                Accessibility::Private | Accessibility::NotApplicable => false,
                Accessibility::Internal | Accessibility::ProtectedAndInternal => !from_metadata,
                _ => true,
            };
            // An accessibility already written picks the members that have it.
            if !visible || accessibility.is_some_and(|wanted| wanted != found.accessibility) {
                continue;
            }
            if let Some(item) = override_item(view, member, &written, simple_system, &layout) {
                let mut item = item;
                item.additional_edits.push(TextEdit::delete(TextSpan::new(
                    first.span().start(),
                    site.start - first.span().start(),
                )));
                items.push(item);
            }
        }
        current = base;
    }
}

/// How the text written out is laid out.
struct Layout {
    /// The indentation of the line the member starts on.
    indent: String,
    newline: &'static str,
}

impl Layout {
    /// `lines` as a block under a header: `{`, each line one level in, `}`.
    fn block(&self, header: &str, lines: &[String]) -> (String, u32) {
        let Self { indent, newline } = self;
        let mut out = format!("{header}{newline}{indent}{{{newline}");
        let mut caret = 0;
        for (index, line) in lines.iter().enumerate() {
            out.push_str(indent);
            out.push_str("    ");
            if index == 0 {
                caret = out.len() as u32;
            }
            out.push_str(line);
            out.push_str(newline);
        }
        if lines.is_empty() {
            out.push_str(indent);
            out.push_str("    ");
            caret = out.len() as u32;
            out.push_str(newline);
        }
        out.push_str(indent);
        out.push('}');
        (out, caret)
    }
}

/// The symbol of a type declaration.
fn type_symbol(view: &View<'_>, declaration: &SyntaxNode) -> Option<SymbolId> {
    view.model.declared_symbol(declaration).or_else(|| {
        // Declared in text the compilation has not seen: find it by name.
        let name = declaration
            .child_token_of_kind(K::IdentifierToken)?
            .value_text()
            .to_string();
        let context = view.model.binder().context_at(view.tree, declaration);
        context
            .enclosing_types()
            .into_iter()
            .find(|&ty| view.compilation().symbols().get(ty).name == name)
    })
}

/// The class a type derives from, if it names one.
fn base_class(view: &View<'_>, ty: SymbolId) -> Option<SymbolId> {
    let symbols = view.compilation().symbols();
    let found = view
        .model
        .base_types_of(ty)
        .into_iter()
        .find_map(|base| match base {
            Type::Named { symbol, .. }
                if matches!(
                    symbols.get(symbol).type_kind(),
                    Some(TypeKind::Class | TypeKind::Record)
                ) =>
            {
                Some(symbol)
            }
            _ => None,
        });
    found.or_else(|| {
        // Every class but `object` derives from it, whether or not it says.
        let object = view
            .compilation()
            .special_type(rustlyn_semantics::SpecialType::Object)?;
        (ty != object
            && matches!(
                symbols.get(ty).type_kind(),
                Some(TypeKind::Class | TypeKind::Record)
            ))
        .then_some(object)
    })
}

/// The modifiers between `first` and the word, besides `override`,
/// `partial` and accessibility, which the written member supplies.
fn modifiers_between(view: &View<'_>, first: &SyntaxToken, end: u32) -> Vec<String> {
    let start = first.span().start();
    let Some(around) = view
        .root
        .find_node(TextSpan::new(start, end.saturating_sub(start)))
    else {
        return Vec::new();
    };
    around
        .descendant_tokens()
        .filter(|token| token.span().start() >= start && token.span().end() <= end)
        .map(|token| token.text().to_string())
        .filter(|word| {
            is_modifier(word)
                && !matches!(
                    word.as_str(),
                    "override" | "partial" | "public" | "private" | "protected" | "internal"
                )
        })
        .collect()
}

/// The accessibility written between `first` and the word, if any.
fn typed_accessibility(view: &View<'_>, first: &SyntaxToken, end: u32) -> Option<Accessibility> {
    let start = first.span().start();
    let around = view
        .root
        .find_node(TextSpan::new(start, end.saturating_sub(start)))?;
    let words: Vec<String> = around
        .descendant_tokens()
        .filter(|token| token.span().start() >= start && token.span().end() <= end)
        .map(|token| token.text().to_string())
        .collect();
    let has = |word: &str| words.iter().any(|w| w == word);
    match (
        has("public"),
        has("protected"),
        has("internal"),
        has("private"),
    ) {
        (true, ..) => Some(Accessibility::Public),
        (_, true, true, _) => Some(Accessibility::ProtectedOrInternal),
        (_, true, _, true) => Some(Accessibility::ProtectedAndInternal),
        (_, true, ..) => Some(Accessibility::Protected),
        (_, _, true, _) => Some(Accessibility::Internal),
        (.., true) => Some(Accessibility::Private),
        _ => None,
    }
}

/// A member's name and parameter types: what makes an override the same
/// member as what it overrides.
fn signature_key(view: &View<'_>, member: SymbolId) -> String {
    let symbols = view.compilation().symbols();
    let found = symbols.get(member);
    let parameters: Vec<String> = match &found.detail {
        rustlyn_semantics::Detail::Method(method) => method
            .parameters
            .iter()
            .map(|&p| view.model.type_of_symbol(p).display(symbols))
            .collect(),
        rustlyn_semantics::Detail::Property(property) => property
            .parameters
            .iter()
            .map(|&p| view.model.type_of_symbol(p).display(symbols))
            .collect(),
        _ => Vec::new(),
    };
    format!("{:?} {}({})", found.kind, found.name, parameters.join(","))
}

/// A parameter list as C# writes it, and the arguments that pass it on.
fn parameters(view: &View<'_>, list: &[SymbolId]) -> (String, String) {
    let symbols = view.compilation().symbols();
    let mut declared = Vec::new();
    let mut passed = Vec::new();
    for &parameter in list {
        let found = symbols.get(parameter);
        let ty = view.model.type_of_symbol(parameter);
        let ty = match ty {
            Type::ByRef(inner) => inner.display(symbols),
            other => other.display(symbols),
        };
        let (prefix, pass) = match found.as_parameter().map(|p| (p.ref_kind, p.is_params)) {
            Some((RefKind::Ref, _)) => ("ref ", "ref "),
            Some((RefKind::Out, _)) => ("out ", "out "),
            Some((RefKind::In, _)) => ("in ", ""),
            Some((_, true)) => ("params ", ""),
            _ => ("", ""),
        };
        let name = escape(&found.name);
        declared.push(format!("{prefix}{ty} {name}"));
        passed.push(format!("{pass}{name}"));
    }
    (declared.join(", "), passed.join(", "))
}

/// A name, with `@` if it is a keyword.
fn escape(name: &str) -> String {
    if rustlyn_syntax::kind_from_text(name).is_some_and(K::is_reserved_keyword) {
        format!("@{name}")
    } else {
        name.to_string()
    }
}

fn accessibility_text(accessibility: Accessibility) -> &'static str {
    match accessibility {
        Accessibility::Public => "public",
        Accessibility::Protected => "protected",
        Accessibility::Internal => "internal",
        Accessibility::ProtectedOrInternal => "protected internal",
        Accessibility::ProtectedAndInternal => "private protected",
        Accessibility::Private | Accessibility::NotApplicable => "private",
    }
}

/// The item for overriding `member`.
fn override_item(
    view: &View<'_>,
    member: SymbolId,
    written: &[String],
    simple_system: bool,
    layout: &Layout,
) -> Option<Completion> {
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    let found = symbols.get(member);
    let is_abstract = found.modifiers.contains(Modifiers::ABSTRACT);
    let throw = if simple_system {
        "throw new NotImplementedException()"
    } else {
        "throw new System.NotImplementedException()"
    };
    let mut head = accessibility_text(found.accessibility).to_string();
    for word in written {
        head.push(' ');
        head.push_str(word);
    }
    head.push_str(" override");
    let ty = view.model.type_of_symbol(member);
    let ty_text = ty.display(symbols);
    let name = escape(&found.name);

    let (label, text, caret) = match found.kind {
        SymbolKind::Method => {
            let method = found.as_method()?;
            let (declared, passed) = parameters(view, &method.parameters);
            let generics = if method.type_parameters.is_empty() {
                String::new()
            } else {
                let names: Vec<&str> = method
                    .type_parameters
                    .iter()
                    .map(|&p| symbols.get(p).name.as_str())
                    .collect();
                format!("<{}>", names.join(", "))
            };
            let header = format!("{head} {ty_text} {name}{generics}({declared})");
            let call = format!("base.{name}{generics}({passed})");
            let line = if is_abstract {
                format!("{throw};")
            } else if ty == Type::Void {
                format!("{call};")
            } else {
                format!("return {call};")
            };
            let (text, caret) = layout.block(&header, &[line]);
            let types: Vec<String> = method
                .parameters
                .iter()
                .map(|&p| view.model.type_of_symbol(p).display(symbols))
                .collect();
            (format!("{}({})", found.name, types.join(", ")), text, caret)
        }
        SymbolKind::Property => {
            let property = found.as_property()?;
            let (declared, passed) = parameters(view, &property.parameters);
            let (header, target) = if property.is_indexer {
                (
                    format!("{head} {ty_text} this[{declared}]"),
                    format!("base[{passed}]"),
                )
            } else {
                (format!("{head} {ty_text} {name}"), format!("base.{name}"))
            };
            let mut lines = Vec::new();
            if property.has_get {
                lines.push(if is_abstract {
                    format!("get => {throw};")
                } else {
                    format!("get => {target};")
                });
            }
            if property.has_set || property.has_init {
                let keyword = if property.has_init { "init" } else { "set" };
                lines.push(if is_abstract {
                    format!("{keyword} => {throw};")
                } else {
                    format!("{keyword} => {target} = value;")
                });
            }
            let (text, caret) = layout.block(&header, &lines);
            let label = if property.is_indexer {
                "this[]".to_string()
            } else {
                found.name.clone()
            };
            (label, text, caret)
        }
        SymbolKind::Event => {
            let text = format!("{head} event {ty_text} {name};");
            let caret = text.len() as u32;
            (found.name.clone(), text, caret)
        }
        _ => return None,
    };
    Some(Completion {
        kind: super::super::completion_kind(compilation, member),
        detail: super::super::describe_symbol(compilation, member),
        filter_text: Some(found.name.clone()),
        insert_text: Some(text),
        caret: Some(caret),
        label,
        rank: 10,
        symbol: Some(member),
        ..Completion::default()
    })
}

/// Partial methods declared without a body in some part of the type and
/// implemented in none, after `partial`.
pub(super) fn complete_partial(
    view: &mut View<'_>,
    text: &str,
    site: &Site,
    first: &SyntaxToken,
    items: &mut Vec<Completion>,
) {
    let Some(declaration) = first
        .parent()
        .ancestors()
        .find(|node| is_type_declaration(node.kind()))
    else {
        return;
    };
    // Every part of the type: this one as it is being edited, and the
    // others as compiled.
    let mut parts = vec![declaration.clone()];
    if let Some(ty) = type_symbol(view, &declaration) {
        for &(tree, span) in view.compilation().declaration_nodes(ty) {
            if tree == view.tree {
                continue;
            }
            if let Some(node) = view
                .compilation()
                .trees()
                .get(tree)
                .and_then(|tree| tree.root().find_node(span))
            {
                parts.push(node);
            }
        }
    }
    let mut definitions: Vec<SyntaxNode> = Vec::new();
    let mut implemented: HashSet<String> = HashSet::new();
    for part in &parts {
        for method in part
            .children()
            .filter(|child| child.kind() == K::MethodDeclaration)
        {
            if !method.child_tokens().any(|token| token.text() == "partial") {
                continue;
            }
            let key = partial_key(&method);
            if method.child_of_kind(K::Block).is_some()
                || method.child_of_kind(K::ArrowExpressionClause).is_some()
            {
                implemented.insert(key);
            } else {
                definitions.push(method);
            }
        }
    }
    let layout = Layout {
        indent: indentation_at(text, first.span().start()).to_string(),
        newline: newline_of(text),
    };
    let written = modifiers_between(view, first, site.start);
    let mut offered = HashSet::new();
    for method in definitions {
        let key = partial_key(&method);
        if implemented.contains(&key) || !offered.insert(key) {
            continue;
        }
        let Some(name) = method.child_token_of_kind(K::IdentifierToken) else {
            continue;
        };
        let return_type = method
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| ty.text().trim().to_string())
            .unwrap_or_else(|| "void".to_string());
        let generics = method
            .child_of_kind(K::TypeParameterList)
            .map(|list| list.text().trim().to_string())
            .unwrap_or_default();
        let parameters = method
            .child_of_kind(K::ParameterList)
            .map(|list| list.text().trim().to_string())
            .unwrap_or_else(|| "()".to_string());
        let accessibility: Vec<String> = method
            .child_tokens()
            .filter(|token| {
                matches!(
                    token.text(),
                    "public" | "private" | "protected" | "internal"
                )
            })
            .map(|token| token.text().to_string())
            .collect();
        let mut head: Vec<String> = accessibility;
        head.extend(written.iter().cloned());
        head.push("partial".to_string());
        let header = format!(
            "{} {return_type} {}{generics}{parameters}",
            head.join(" "),
            name.text()
        );
        let (insert, caret) = layout.block(&header, &[]);
        items.push(Completion {
            label: format!("{}{parameters}", name.text()),
            kind: CompletionKind::Method,
            detail: header.clone(),
            rank: 10,
            insert_text: Some(insert),
            filter_text: Some(name.text().to_string()),
            caret: Some(caret),
            additional_edits: vec![TextEdit::delete(TextSpan::new(
                first.span().start(),
                site.start - first.span().start(),
            ))],
            ..Completion::default()
        });
    }
}

/// A partial method's name and parameter types, spelled as written.
fn partial_key(method: &SyntaxNode) -> String {
    let name = method
        .child_token_of_kind(K::IdentifierToken)
        .map(|token| token.text().to_string())
        .unwrap_or_default();
    let types: Vec<String> = method
        .child_of_kind(K::ParameterList)
        .map(|list| {
            list.children()
                .filter(|parameter| parameter.kind() == K::Parameter)
                .filter_map(|parameter| {
                    parameter
                        .children()
                        .find(|child| child.kind().is_type_node())
                        .map(|ty| ty.text().trim().to_string())
                })
                .collect()
        })
        .unwrap_or_default();
    format!("{name}({})", types.join(","))
}
