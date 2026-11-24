//! Generate class, interface: a type name that names nothing, made into a
//! type.
//!
//! Roslyn's `GenerateType`. The kind follows from where the name is: an
//! interface in a base list where a class cannot go (after the first entry,
//! or in an interface's or struct's list, or first in a class's list when
//! the name reads `IName`), an attribute class deriving `Attribute` for an
//! attribute, an exception for what is thrown or caught, a class otherwise.
//! `new Name(1, "a")` gives it a constructor taking the arguments and
//! fields keeping them, as Roslyn writes it.
//!
//! Three places are offered: a file of its own next to the current one,
//! "in new file", which the edit creates by inserting the whole text at
//! offset 0 of a path that does not exist yet — an editor applying it makes
//! the file; after the type the name is used in; and nested inside that
//! type.

use std::collections::BTreeSet;
use std::path::PathBuf;

use rustlyn_semantics::{SymbolId, SymbolKind, Type};
use rustlyn_syntax::SyntaxKind;

use super::super::{ActionKind, CodeAction, Context};
use super::Unresolved;
use super::support::{
    Argument, MemberPlace, Namer, arguments_of, indent_lines, indent_unit, insert_members,
    is_type_declaration, newline, next_line_start,
};
use crate::edit::{FileEdit, TextEdit, WorkspaceEdit};

pub(super) fn offer(
    context: &mut Context<'_, '_>,
    names: &[Unresolved],
    found: &mut Vec<CodeAction>,
) {
    for name in names {
        let as_type = name.code == "CS0246" && name.receiver.is_none();
        // `Name.Member` where `Name` is nothing: it may be a type.
        let as_receiver = name.code == "CS0103"
            && name.name.parent().is_some_and(|parent| {
                parent.kind() == SyntaxKind::SimpleMemberAccessExpression
                    && parent.children().next().as_ref() == Some(&name.name)
            })
            && name.text().starts_with(char::is_uppercase);
        if as_type || as_receiver {
            generate(context, name, found);
        }
    }
}

/// What sort of type to write.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Class,
    Interface,
}

impl Kind {
    const fn keyword(self) -> &'static str {
        match self {
            Self::Class => "class",
            Self::Interface => "interface",
        }
    }
}

/// The type to write, before it is placed.
struct Shape {
    kind: Kind,
    name: String,
    type_parameters: Vec<String>,
    base: Option<Type>,
    /// The arguments of the `new` that made it, for a constructor.
    arguments: Vec<Argument>,
}

fn generate(context: &mut Context<'_, '_>, name: &Unresolved, found: &mut Vec<CodeAction>) {
    let Some(shape) = shape(context, name) else {
        return;
    };
    let kind = shape.kind.keyword();
    let type_name = &shape.name;
    let code = Some(name.code.as_str());

    // In a file of its own.
    if let Some(edit) = new_file(context, name, &shape) {
        found.push(CodeAction {
            title: format!("Generate {kind} '{type_name}' in new file"),
            kind: ActionKind::Generate,
            fixes: code.map(str::to_owned),
            edit,
        });
    }

    let view = &*context.view;
    let namer = Namer::at(view, &name.name);
    let outermost = name
        .name
        .ancestors()
        .filter(|node| {
            is_type_declaration(node.kind()) || node.kind() == SyntaxKind::EnumDeclaration
        })
        .last();
    let innermost = name
        .name
        .ancestors()
        .find(|node| is_type_declaration(node.kind()));

    // After the type it is used in, or at the end of the file.
    let text = &context.text;
    let nl = newline(text);
    let declaration = write(&shape, &namer, "internal");
    let edit = match &outermost {
        Some(outer) => {
            let indent = super::support::indentation_at(
                text,
                outer
                    .first_token()
                    .map_or(outer.span().start(), |token| token.span().start()),
            );
            let body = indent_lines(&reunit(&declaration, &indent_unit(text)), &indent, nl);
            let at = next_line_start(text, outer.span().end());
            let lead = if at as usize == text.len() && !text.ends_with('\n') {
                nl
            } else {
                ""
            };
            TextEdit::insert(at, format!("{lead}{nl}{body}{nl}"))
        }
        None => {
            let lead = if text.ends_with('\n') { "" } else { nl };
            let body = indent_lines(&reunit(&declaration, &indent_unit(text)), "", nl);
            TextEdit::insert(text.len() as u32, format!("{lead}{nl}{body}{nl}"))
        }
    };
    found.push(context.local(
        format!("Generate {kind} '{type_name}'"),
        ActionKind::Generate,
        code,
        vec![edit],
    ));

    // Nested in the type it is used in.
    if let Some(inner) = innermost {
        let nested = write(&shape, &namer, "private");
        if let Some(edit) = insert_members(&inner, text, &[nested], &MemberPlace::End) {
            found.push(context.local(
                format!("Generate nested {kind} '{type_name}'"),
                ActionKind::Generate,
                code,
                vec![edit],
            ));
        }
    }
}

/// Four-space units, as the declaration is written, turned into the
/// file's.
fn reunit(text: &str, unit: &str) -> String {
    if unit == "    " {
        return text.to_string();
    }
    text.split('\n')
        .map(|line| {
            let spaces = line.len() - line.trim_start_matches(' ').len();
            format!(
                "{}{}",
                unit.repeat(spaces / 4),
                &line[spaces - spaces % 4..]
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// What the name is used as, and so what type it should be.
fn shape(context: &mut Context<'_, '_>, name: &Unresolved) -> Option<Shape> {
    let mut top = name.name.clone();
    while let Some(parent) = top.parent().cloned()
        && parent.kind() == SyntaxKind::QualifiedName
    {
        top = parent;
    }
    let holder = top.parent()?.clone();
    let compilation = context.view.compilation();
    let mut kind = Kind::Class;
    let mut base = None;
    let mut type_name = name.text().to_string();
    let looks_like_interface = {
        let mut chars = type_name.chars();
        chars.next() == Some('I') && chars.next().is_some_and(char::is_uppercase)
    };
    match holder.kind() {
        SyntaxKind::SimpleBaseType => {
            let list = holder.parent()?.clone();
            let declaration = list.parent()?.clone();
            let first = list
                .children()
                .find(|child| child.kind() == SyntaxKind::SimpleBaseType)
                .is_some_and(|first| first == holder);
            kind = match declaration.kind() {
                SyntaxKind::ClassDeclaration | SyntaxKind::RecordDeclaration
                    if first && !looks_like_interface =>
                {
                    Kind::Class
                }
                _ => Kind::Interface,
            };
        }
        SyntaxKind::Attribute => {
            if !type_name.ends_with("Attribute") {
                type_name.push_str("Attribute");
            }
            base = compilation
                .type_by_metadata_name("System.Attribute")
                .map(Type::named);
        }
        SyntaxKind::CatchDeclaration => {
            base = compilation
                .type_by_metadata_name("System.Exception")
                .map(Type::named);
        }
        SyntaxKind::ObjectCreationExpression
            if holder.parent().is_some_and(|parent| {
                parent.kind() == SyntaxKind::ThrowStatement
                    || parent.kind() == SyntaxKind::ThrowExpression
            }) =>
        {
            base = compilation
                .type_by_metadata_name("System.Exception")
                .map(Type::named);
        }
        _ => {}
    }
    let type_parameters = match name.arity {
        0 => Vec::new(),
        1 => vec!["T".to_string()],
        count => (1..=count).map(|index| format!("T{index}")).collect(),
    };
    let arguments = if holder.kind() == SyntaxKind::ObjectCreationExpression {
        holder
            .child_of_kind(SyntaxKind::ArgumentList)
            .map(|list| arguments_of(context.view, &list))
            .unwrap_or_default()
    } else {
        Vec::new()
    };
    Some(Shape {
        kind,
        name: type_name,
        type_parameters,
        base,
        arguments,
    })
}

/// The declaration, unindented, with four-space indentation inside.
fn write(shape: &Shape, namer: &Namer<'_>, access: &str) -> String {
    let mut head = format!("{access} {} {}", shape.kind.keyword(), shape.name);
    if !shape.type_parameters.is_empty() {
        head.push_str(&format!("<{}>", shape.type_parameters.join(", ")));
    }
    if let Some(base) = &shape.base {
        head.push_str(&format!(" : {}", namer.name(base)));
    }
    let mut members: Vec<String> = Vec::new();
    if !shape.arguments.is_empty() {
        let fields: Vec<String> = shape
            .arguments
            .iter()
            .map(|argument| {
                format!(
                    "    private {} {};",
                    namer.name(&argument.ty),
                    argument.name
                )
            })
            .collect();
        members.push(fields.join("\n"));
        let parameters: Vec<String> = shape
            .arguments
            .iter()
            .map(|argument| {
                format!(
                    "{}{} {}",
                    argument.modifier,
                    namer.name(&argument.ty),
                    argument.name
                )
            })
            .collect();
        let assignments: Vec<String> = shape
            .arguments
            .iter()
            .filter(|argument| argument.modifier != "out ")
            .map(|argument| format!("        this.{0} = {0};", argument.name))
            .collect();
        members.push(format!(
            "    public {}({})\n    {{\n{}\n    }}",
            shape.name,
            parameters.join(", "),
            assignments.join("\n")
        ));
    }
    if members.is_empty() {
        format!("{head}\n{{\n}}")
    } else {
        format!("{head}\n{{\n{}\n}}", members.join("\n\n"))
    }
}

/// The edit that makes `Name.cs` next to the current file, declaring the
/// type in the namespace the name was used in.
fn new_file(context: &Context<'_, '_>, name: &Unresolved, shape: &Shape) -> Option<WorkspaceEdit> {
    let view = &*context.view;
    let directory = context.path.parent()?;
    let path: PathBuf = directory.join(format!("{}.cs", shape.name));
    if view.semantic.tree_index(&path).is_some() || path.exists() {
        return None;
    }
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    // The namespace the name was used in, dotted, and how the file wrote it.
    let mut parts: Vec<String> = Vec::new();
    let mut file_scoped = false;
    for ancestor in name.name.ancestors() {
        if ancestor.kind() == SyntaxKind::NamespaceDeclaration
            && let Some(written) = ancestor
                .children()
                .find(|child| child.kind().is_type_node())
        {
            parts.push(written.text().trim().to_string());
        }
    }
    parts.reverse();
    if let Some(scoped) = view
        .root
        .children()
        .find(|child| child.kind() == SyntaxKind::FileScopedNamespaceDeclaration)
        && let Some(written) = scoped.children().find(|child| child.kind().is_type_node())
    {
        parts.insert(0, written.text().trim().to_string());
        file_scoped = true;
    }
    let namespace = parts.join(".");
    let declared: Option<SymbolId> = lookup_namespace(view, &namespace);

    // The namespaces the new file needs to import for the types it names.
    let mut used = BTreeSet::new();
    let mut types: Vec<&Type> = shape
        .arguments
        .iter()
        .map(|argument| &argument.ty)
        .collect();
    types.extend(shape.base.iter());
    for ty in types {
        namespaces_in(symbols, ty, &mut used);
    }
    used.remove(&compilation.global_namespace());
    if let Some(declared) = declared {
        used.remove(&declared);
    }
    let mut imports: Vec<SymbolId> = used.into_iter().collect();
    let mut names: Vec<String> = imports
        .iter()
        .map(|id| symbols.qualified_name(*id))
        .collect();
    names.sort_by_key(|name| crate::editorconfig::using_sort_key(name));
    // `csharp_style_namespace_declarations` decides the new file's
    // namespace; without it, the new file does what this one does.
    if let Some(preferred) = crate::editorconfig::current_code_style().file_scoped_namespaces {
        file_scoped = preferred;
    }
    imports.extend(declared);
    let namer = Namer::with_namespaces(compilation, &imports);
    let nl = newline(&context.text);
    let unit = indent_unit(&context.text);
    let declaration = reunit(&write(shape, &namer, "internal"), &unit);

    let mut out = String::new();
    for name in &names {
        out.push_str(&format!("using {name};{nl}"));
    }
    if !names.is_empty() {
        out.push_str(nl);
    }
    if namespace.is_empty() {
        out.push_str(&indent_lines(&declaration, "", nl));
        out.push_str(nl);
    } else if file_scoped {
        out.push_str(&format!("namespace {namespace};{nl}{nl}"));
        out.push_str(&indent_lines(&declaration, "", nl));
        out.push_str(nl);
    } else {
        out.push_str(&format!("namespace {namespace}{nl}{{{nl}"));
        out.push_str(&indent_lines(&declaration, &unit, nl));
        out.push_str(&format!("{nl}}}{nl}"));
    }
    Some(WorkspaceEdit {
        files: vec![FileEdit {
            path,
            edits: vec![TextEdit::insert(0, out)],
        }],
        renames: Vec::new(),
    })
}

fn lookup_namespace(view: &crate::semantic::View<'_>, name: &str) -> Option<SymbolId> {
    let compilation = view.compilation();
    let symbols = compilation.symbols();
    if name.is_empty() {
        return None;
    }
    let mut current = compilation.global_namespace();
    for part in name.split('.') {
        current = symbols.lookup_namespace(current, part.trim())?;
    }
    Some(current)
}

/// The namespaces the named types in `ty` are declared in.
fn namespaces_in(symbols: &rustlyn_semantics::Symbols, ty: &Type, out: &mut BTreeSet<SymbolId>) {
    match ty {
        Type::Named {
            symbol,
            type_arguments,
        } => {
            let qualified = symbols.qualified_name(*symbol);
            let keyword = rustlyn_semantics::SpecialType::ALL
                .iter()
                .any(|special| special.metadata_name() == qualified);
            if !keyword {
                let mut container = symbols.get(*symbol).container;
                while let Some(at) = container {
                    if symbols.get(at).kind == SymbolKind::Namespace {
                        out.insert(at);
                        break;
                    }
                    container = symbols.get(at).container;
                }
            }
            for argument in type_arguments {
                namespaces_in(symbols, argument, out);
            }
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            namespaces_in(symbols, element, out);
        }
        Type::Tuple(elements) => {
            for element in elements {
                namespaces_in(symbols, &element.ty, out);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{actions, fix, titles};

    #[test]
    fn a_class_is_generated_after_the_type_that_uses_it() {
        let source = "namespace App\n{\n    class C\n    {\n        $$Widget field;\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Generate class 'Widget'"),
            "namespace App\n{\n    class C\n    {\n        Widget field;\n    }\n\n    internal class Widget\n    {\n    }\n}\n"
        );
        assert_eq!(
            fix(&[source], "Generate nested class 'Widget'"),
            "namespace App\n{\n    class C\n    {\n        Widget field;\n\n        private class Widget\n        {\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_new_file_is_made_in_the_same_namespace() {
        let source = "namespace App.Models;\n\nclass C\n{\n    void M()\n    {\n        var w = new $$Widget(3, \"name\");\n    }\n}\n";
        let found = actions(&[source]);
        let action = found
            .iter()
            .find(|action| action.title == "Generate class 'Widget' in new file")
            .expect("offered");
        let file = &action.edit.files[0];
        assert_eq!(file.path, std::path::Path::new("/p/Widget.cs"));
        assert_eq!(
            crate::edit::apply("", &file.edits),
            "namespace App.Models;\n\ninternal class Widget\n{\n    private int v1;\n    private string v2;\n\n    public Widget(int v1, string v2)\n    {\n        this.v1 = v1;\n        this.v2 = v2;\n    }\n}\n"
        );
    }

    #[test]
    fn a_later_base_is_an_interface_and_an_attribute_derives_attribute() {
        let source = "class Base { }\nclass C : Base, $$IRunner\n{\n}\n";
        assert!(titles(&[source]).contains(&"Generate interface 'IRunner'".to_string()));
        let source = "using System;\n\nclass C\n{\n    [$$Marker]\n    void M() { }\n}\n";
        assert_eq!(
            fix(&[source], "Generate class 'MarkerAttribute'"),
            "using System;\n\nclass C\n{\n    [Marker]\n    void M() { }\n}\n\ninternal class MarkerAttribute : Attribute\n{\n}\n"
        );
    }

    #[test]
    fn a_new_file_imports_what_it_names() {
        let source = "namespace App\n{\n    class C\n    {\n        void M()\n        {\n            throw new $$Oops();\n        }\n    }\n}\n";
        let found = actions(&[source]);
        let action = found
            .iter()
            .find(|action| action.title == "Generate class 'Oops' in new file")
            .expect("offered");
        assert_eq!(
            crate::edit::apply("", &action.edit.files[0].edits),
            "using System;\n\nnamespace App\n{\n    internal class Oops : Exception\n    {\n    }\n}\n"
        );
    }

    #[test]
    fn a_generic_use_makes_a_generic_type() {
        let source = "class C\n{\n    $$Box<int> box;\n}\n";
        assert_eq!(
            fix(&[source], "Generate class 'Box'"),
            "class C\n{\n    Box<int> box;\n}\n\ninternal class Box<T>\n{\n}\n"
        );
    }
}
