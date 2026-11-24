//! Add `using`, and fully qualify: a name that is right but not imported.
//!
//! Roslyn's `AddImport` and `FullyQualify` fixes. Every namespace of the
//! compilation is searched, the referenced assemblies' included, for a type
//! of the name and arity written that the file may use; an attribute is
//! looked for with `Attribute` on the end as well. Each namespace found is
//! offered twice: `using System.Text;`, and the name written out in full,
//! `System.Text.StringBuilder`.
//!
//! A method called on a value that has no member of that name may be an
//! extension method in a namespace the file does not import; each such
//! namespace whose method takes the value is offered as a `using`.

use std::collections::BTreeSet;

use rustlyn_semantics::{SymbolKind, Type};

use super::super::{ActionKind, CodeAction, Context};
use super::Unresolved;
use super::support::{Namer, add_using};
use crate::edit::TextEdit;

pub(super) fn offer(
    context: &mut Context<'_, '_>,
    names: &[Unresolved],
    found: &mut Vec<CodeAction>,
) {
    for name in names {
        if name.receiver.is_none() && matches!(name.code.as_str(), "CS0246" | "CS0103") {
            types(context, name, found);
        }
        if name.receiver.is_some() && name.code == "CS1061" && name.invocation().is_some() {
            extensions(context, name, found);
        }
    }
}

/// The namespaces, sorted as `using`s are: `System` first.
fn sorted(namespaces: BTreeSet<String>) -> Vec<String> {
    let mut namespaces: Vec<String> = namespaces.into_iter().collect();
    namespaces.sort_by_key(|name| crate::editorconfig::using_sort_key(name));
    namespaces
}

fn types(context: &mut Context<'_, '_>, name: &Unresolved, found: &mut Vec<CodeAction>) {
    let view = &*context.view;
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    let namer = Namer::at(view, &name.name);
    let written = name.text();
    let wanted: Vec<String> = if name.attribute {
        vec![format!("{written}Attribute"), written.to_string()]
    } else {
        vec![written.to_string()]
    };
    let mut namespaces = BTreeSet::new();
    for ty in compilation.all_types() {
        if !wanted.contains(&ty.name)
            || ty.as_named_type().map_or(0, |detail| detail.arity) != name.arity
            || !view.offerable(ty.id)
        {
            continue;
        }
        let Some(container) = ty.container else {
            continue;
        };
        let namespace = symbols.get(container);
        if namespace.kind != SymbolKind::Namespace || namespace.name.is_empty() {
            continue;
        }
        let qualified = symbols.qualified_name(container);
        if !namer.imports(&qualified) {
            namespaces.insert(qualified);
        }
    }
    let namespaces = sorted(namespaces);
    let code = Some(name.code.as_str());
    for namespace in &namespaces {
        if let Some(edit) = add_using(&view.root, &context.text, namespace) {
            found.push(context.local(
                format!("using {namespace};"),
                ActionKind::QuickFix,
                code,
                vec![edit],
            ));
        }
    }
    for namespace in &namespaces {
        let edit = TextEdit::new(name.identifier.span(), format!("{namespace}.{written}"));
        found.push(context.local(
            format!("{namespace}.{written}"),
            ActionKind::QuickFix,
            code,
            vec![edit],
        ));
    }
}

fn extensions(context: &mut Context<'_, '_>, name: &Unresolved, found: &mut Vec<CodeAction>) {
    let Some(receiver) = name.receiver.clone() else {
        return;
    };
    // `Type.Method()` calls a static, never an extension.
    if context.view.named(&receiver).is_some() {
        return;
    }
    let ty = context.view.type_of(&receiver);
    if ty.is_error() {
        return;
    }
    let view = &*context.view;
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    let namer = Namer::at(view, &name.name);
    let receiver_types = view.types_of(&ty);
    let mut namespaces = BTreeSet::new();
    for &method in compilation.extension_methods(name.text()) {
        let Some(class) = symbols.get(method).container else {
            continue;
        };
        let Some(namespace) = symbols.get(class).container else {
            continue;
        };
        if !view.offerable(class) || symbols.get(namespace).kind != SymbolKind::Namespace {
            continue;
        }
        let qualified = symbols.qualified_name(namespace);
        if namer.imports(&qualified) {
            continue;
        }
        let Some(&first) = symbols
            .get(method)
            .as_method()
            .and_then(|detail| detail.parameters.first())
        else {
            continue;
        };
        let takes = match view.model.type_of_symbol(first) {
            Type::TypeParameter(_) => true,
            Type::Named { symbol, .. } if receiver_types.contains(&symbol) => true,
            other => view.model.binder().converts_implicitly(&ty, &other),
        };
        if takes {
            namespaces.insert(qualified);
        }
    }
    for namespace in sorted(namespaces) {
        if let Some(edit) = add_using(&view.root, &context.text, &namespace) {
            found.push(context.local(
                format!("using {namespace};"),
                ActionKind::QuickFix,
                Some(&name.code),
                vec![edit],
            ));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    const TEXT: &str = "namespace System.Text { public class StringBuilder { } }\n\
                        namespace Other.Text { public class StringBuilder<T> { } }\n";

    #[test]
    fn a_type_in_another_namespace_is_imported() {
        let source = "using System;\n\nclass C\n{\n    void M()\n    {\n        var b = new $$StringBuilder();\n    }\n}\n";
        assert_eq!(
            fix(&[source, TEXT], "using System.Text;"),
            "using System;\nusing System.Text;\n\nclass C\n{\n    void M()\n    {\n        var b = new StringBuilder();\n    }\n}\n"
        );
    }

    #[test]
    fn a_type_is_qualified_in_full() {
        let source =
            "class C\n{\n    void M()\n    {\n        var b = new $$StringBuilder();\n    }\n}\n";
        assert_eq!(
            fix(&[source, TEXT], "System.Text.StringBuilder"),
            "class C\n{\n    void M()\n    {\n        var b = new System.Text.StringBuilder();\n    }\n}\n"
        );
        // No `using`s yet: the first goes above the class.
        assert_eq!(
            fix(&[source, TEXT], "using System.Text;"),
            "using System.Text;\n\nclass C\n{\n    void M()\n    {\n        var b = new StringBuilder();\n    }\n}\n"
        );
    }

    #[test]
    fn the_arity_decides_which_type_is_meant() {
        let source = "class C\n{\n    $$StringBuilder<int> field;\n}\n";
        let offered = titles(&[source, TEXT]);
        assert!(
            offered.contains(&"using Other.Text;".to_string()),
            "{offered:?}"
        );
        assert!(
            !offered.contains(&"using System.Text;".to_string()),
            "{offered:?}"
        );
        assert_eq!(
            fix(&[source, TEXT], "using Other.Text;"),
            "using Other.Text;\n\nclass C\n{\n    StringBuilder<int> field;\n}\n"
        );
    }

    #[test]
    fn a_using_goes_in_order() {
        let source = "using System;\nusing Zeta;\n\nclass C : $$Widget { }\n";
        let other =
            "namespace Zeta { class Z { } }\nnamespace Middle { public class Widget { } }\n";
        assert_eq!(
            fix(&[source, other], "using Middle;"),
            "using System;\nusing Middle;\nusing Zeta;\n\nclass C : Widget { }\n"
        );
    }

    #[test]
    fn an_attribute_is_found_without_its_suffix() {
        let source = "class C\n{\n    [$$Marker]\n    void M() { }\n}\n";
        let other = "namespace Tags { public class MarkerAttribute : System.Attribute { } }\n";
        assert_eq!(
            fix(&[source, other], "using Tags;"),
            "using Tags;\n\nclass C\n{\n    [Marker]\n    void M() { }\n}\n"
        );
        assert_eq!(
            fix(&[source, other], "Tags.Marker"),
            "class C\n{\n    [Tags.Marker]\n    void M() { }\n}\n"
        );
    }

    #[test]
    fn a_static_class_used_as_a_value_is_imported() {
        let source = "class C\n{\n    int M() => $$Calculator.Twice(2);\n}\n";
        let other = "namespace Tools { public static class Calculator { public static int Twice(int x) => x * 2; } }\n";
        assert_eq!(
            fix(&[source, other], "using Tools;"),
            "using Tools;\n\nclass C\n{\n    int M() => Calculator.Twice(2);\n}\n"
        );
    }

    #[test]
    fn an_extension_method_brings_its_namespace() {
        let source = "namespace App\n{\n    using System;\n\n    class C\n    {\n        int M(int x) => x.$$Twice();\n    }\n}\n";
        let other = "namespace Tools.Numbers { public static class Ext { public static int Twice(this int x) => x * 2; } }\n\
                     namespace Tools.Words { public static class Ext { public static string Twice(this string x) => x + x; } }\n";
        let offered = titles(&[source, other]);
        assert!(
            !offered.contains(&"using Tools.Words;".to_string()),
            "{offered:?}"
        );
        assert_eq!(
            fix(&[source, other], "using Tools.Numbers;"),
            "namespace App\n{\n    using System;\n    using Tools.Numbers;\n\n    class C\n    {\n        int M(int x) => x.Twice();\n    }\n}\n"
        );
    }

    #[test]
    fn an_imported_namespace_is_not_offered_again() {
        let source = "using System.Text;\nclass C\n{\n    $$Missing field;\n}\n";
        assert!(
            !titles(&[source, TEXT])
                .iter()
                .any(|title| title.starts_with("using "))
        );
    }
}
