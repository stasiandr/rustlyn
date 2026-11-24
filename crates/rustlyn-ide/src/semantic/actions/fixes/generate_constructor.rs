//! Generate constructor, and add parameter to constructor: `new T(args)`
//! where no constructor of `T` takes the arguments.
//!
//! The binder does not report this yet (Roslyn's CS1729, or CS1503 when the
//! count is right and a type is not), so the provider checks the
//! constructors itself: none has as many parameters as there are arguments,
//! with every argument converting to its parameter. It is offered with the
//! cursor on the type name after `new`, for a type declared in the project.
//!
//! "Generate constructor" writes one taking the arguments, as Roslyn does:
//! each parameter kept in a field or property of the same name and type
//! where the type has one, and in a new private field where it does not.
//! "Add parameter to" extends a constructor that takes the first arguments
//! already with parameters for the rest.

use rustlyn_semantics::{Accessibility, Modifiers, SymbolId, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::support::{
    Argument, MemberPlace, Namer, arguments_of, declaration_of, insert_members, is_member,
};
use crate::edit::TextEdit;
use crate::semantic::View;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some((creation, written)) = creation_at(context) else {
        return;
    };
    let ty = context.view.model.type_of_syntax(&written);
    let Some(symbol) = ty.symbol() else {
        return;
    };
    let compilation = context.view.compilation();
    let symbols = compilation.symbols();
    if compilation.is_from_corlib(symbol)
        || !matches!(
            symbols.get(symbol).type_kind(),
            Some(TypeKind::Class | TypeKind::Struct | TypeKind::Record | TypeKind::RecordStruct)
        )
    {
        return;
    }
    let Some(list) = creation.child_of_kind(SyntaxKind::ArgumentList) else {
        return;
    };
    let arguments = arguments_of(context.view, &list);
    let view = &*context.view;
    let constructors: Vec<SymbolId> = symbols
        .lookup(symbol, ".ctor")
        .iter()
        .copied()
        .filter(|ctor| !symbols.get(*ctor).modifiers.contains(Modifiers::STATIC))
        .collect();
    if constructors
        .iter()
        .any(|&ctor| takes(view, ctor, &arguments, arguments.len()))
    {
        return;
    }
    // A struct always has the parameterless one.
    if arguments.is_empty() {
        return;
    }
    let code = if constructors
        .iter()
        .any(|&ctor| parameters_of(view, ctor).len() == arguments.len())
    {
        "CS1503"
    } else {
        "CS1729"
    };
    let Some(declaration) = declaration_of(view, symbol, &context.text) else {
        return;
    };
    let namer = Namer::at(view, &declaration.node);
    let type_name = symbols.get(symbol).name.clone();
    let signature: Vec<String> = arguments
        .iter()
        .map(|argument| argument.ty.display(symbols))
        .collect();

    // Generate constructor.
    let mut fields: Vec<String> = Vec::new();
    let mut assignments: Vec<String> = Vec::new();
    for argument in &arguments {
        if argument.modifier == "out " {
            continue;
        }
        match existing_member(view, symbol, argument) {
            Some(member) => assignments.push(format!("    {member} = {};", argument.name)),
            None => {
                fields.push(format!(
                    "private {} {};",
                    namer.name(&argument.ty),
                    argument.name
                ));
                assignments.push(format!("    this.{0} = {0};", argument.name));
            }
        }
    }
    let parameters: Vec<String> = arguments
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
    let constructor = format!(
        "public {type_name}({})\n{{\n{}\n}}",
        parameters.join(", "),
        assignments.join("\n")
    )
    .replace("{\n\n}", "{\n}");
    let has_members = declaration
        .node
        .children()
        .any(|child| is_member(child.kind()));
    let edits: Option<Vec<TextEdit>> = if fields.is_empty() {
        insert_members(
            &declaration.node,
            &declaration.text,
            &[constructor],
            &after_constructors(&declaration.node),
        )
        .map(|edit| vec![edit])
    } else if !has_members {
        insert_members(
            &declaration.node,
            &declaration.text,
            &[fields.join("\n"), constructor],
            &MemberPlace::End,
        )
        .map(|edit| vec![edit])
    } else {
        let field_edit = insert_members(
            &declaration.node,
            &declaration.text,
            &[fields.join("\n")],
            &MemberPlace::Fields,
        );
        let constructor_edit = insert_members(
            &declaration.node,
            &declaration.text,
            &[constructor],
            &after_constructors(&declaration.node),
        );
        field_edit.zip(constructor_edit).map(|(a, b)| vec![a, b])
    };
    if let Some(edits) = edits {
        found.push(declaration.action(
            context,
            format!(
                "Generate constructor '{type_name}({})'",
                signature.join(", ")
            ),
            ActionKind::Generate,
            Some(code),
            edits,
        ));
    }

    // Add parameter to a constructor that takes a prefix of the arguments.
    for &ctor in &constructors {
        let taken = parameters_of(view, ctor);
        if taken.len() >= arguments.len() || !takes(view, ctor, &arguments, taken.len()) {
            continue;
        }
        let Some(node) = view.compilation().declaration_node(ctor) else {
            continue;
        };
        let Some(close) = constructor_list_end(view, &declaration, &node) else {
            continue;
        };
        let added: Vec<String> = arguments[taken.len()..]
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
        let separator = if taken.is_empty() { "" } else { ", " };
        let existing: Vec<String> = taken
            .iter()
            .map(|parameter| view.model.type_of_symbol(*parameter).display(symbols))
            .collect();
        found.push(declaration.action(
            context,
            format!("Add parameter to '{type_name}({})'", existing.join(", ")),
            ActionKind::QuickFix,
            Some(code),
            vec![TextEdit::insert(
                close,
                format!("{separator}{}", added.join(", ")),
            )],
        ));
    }
}

/// The object creation whose type name the cursor is on, and that name.
fn creation_at(context: &Context<'_, '_>) -> Option<(SyntaxNode, SyntaxNode)> {
    let token = context.view.name_token_at(context.span.start())?;
    let creation = token
        .parent()
        .ancestors()
        .find(|node| node.kind() == SyntaxKind::ObjectCreationExpression)?;
    let written = creation
        .children()
        .find(|child| child.kind().is_type_node())?;
    written
        .span()
        .contains_span(token.span())
        .then_some((creation, written))
}

fn parameters_of(view: &View<'_>, method: SymbolId) -> Vec<SymbolId> {
    view.compilation()
        .symbols()
        .get(method)
        .as_method()
        .map(|detail| detail.parameters.clone())
        .unwrap_or_default()
}

/// Whether `ctor` takes the first `count` arguments with its parameters, and
/// has exactly `count` of them.
fn takes(view: &View<'_>, ctor: SymbolId, arguments: &[Argument], count: usize) -> bool {
    let parameters = parameters_of(view, ctor);
    let symbols = view.compilation().symbols();
    let required = parameters
        .iter()
        .filter(|parameter| {
            symbols
                .get(**parameter)
                .as_parameter()
                .is_none_or(|detail| !detail.has_default && !detail.is_params)
        })
        .count();
    let fits_count = if count == arguments.len() {
        (required..=parameters.len()).contains(&count)
            || parameters.last().is_some_and(|last| {
                symbols
                    .get(*last)
                    .as_parameter()
                    .is_some_and(|detail| detail.is_params)
            }) && count >= required
    } else {
        parameters.len() == count
    };
    fits_count
        && arguments
            .iter()
            .take(count)
            .zip(&parameters)
            .all(|(argument, parameter)| {
                let wanted = view.model.type_of_symbol(*parameter);
                let wanted = wanted.value();
                argument.ty.is_error()
                    || matches!(argument.ty, Type::Null) && wanted.is_reference_type(symbols)
                    || view
                        .model
                        .binder()
                        .converts_implicitly(&argument.ty, wanted)
            })
}

/// A field or property of the type with the argument's name, in either
/// case, and its type: what a constructor parameter is kept in.
fn existing_member(view: &View<'_>, ty: SymbolId, argument: &Argument) -> Option<String> {
    let symbols = view.compilation().symbols();
    let pascal = {
        let mut chars = argument.name.chars();
        chars
            .next()
            .map(|first| first.to_uppercase().chain(chars).collect::<String>())
            .unwrap_or_default()
    };
    symbols.get(ty).members.iter().find_map(|&member| {
        let symbol = symbols.get(member);
        let matches_name = symbol.name == argument.name || symbol.name == pascal;
        let kind = matches!(symbol.kind, SymbolKind::Field | SymbolKind::Property);
        (matches_name
            && kind
            && symbol.accessibility != Accessibility::NotApplicable
            && view.model.type_of_symbol(member) == argument.ty)
            .then(|| {
                if symbol.name == argument.name {
                    format!("this.{}", symbol.name)
                } else {
                    symbol.name.clone()
                }
            })
    })
}

/// After the last constructor, or with nothing to follow at the end.
fn after_constructors(declaration: &SyntaxNode) -> MemberPlace {
    declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::ConstructorDeclaration)
        .last()
        .map_or(MemberPlace::End, |last| MemberPlace::After(last.span()))
}

/// Where the parameter list of a constructor closes, in the declaration's
/// file.
fn constructor_list_end(
    view: &View<'_>,
    declaration: &super::support::Declaration,
    compiled: &SyntaxNode,
) -> Option<u32> {
    let node = if declaration.path.is_none() {
        let span = match &view.speculation {
            Some(speculation) => speculation.unmap(compiled.span())?,
            None => compiled.span(),
        };
        view.root.find_node(span)?
    } else {
        compiled.clone()
    };
    let list = node.child_of_kind(SyntaxKind::ParameterList)?;
    Some(
        list.child_token_of_kind(SyntaxKind::CloseParenToken)?
            .span()
            .start(),
    )
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    #[test]
    fn a_constructor_is_generated_with_fields() {
        let source = "class Point\n{\n    public int X;\n\n    void M()\n    {\n        var p = new $$Point(1, 2.5);\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Generate constructor 'Point(int, double)'"),
            "class Point\n{\n    public int X;\n    private int v1;\n    private double v2;\n\n    void M()\n    {\n        var p = new Point(1, 2.5);\n    }\n\n    public Point(int v1, double v2)\n    {\n        this.v1 = v1;\n        this.v2 = v2;\n    }\n}\n"
        );
    }

    #[test]
    fn a_member_of_the_same_name_keeps_the_parameter() {
        let source = "class Person\n{\n    public string Name { get; }\n\n    public Person() { }\n}\nclass C\n{\n    Person M(string name) => new $$Person(name);\n}\n";
        assert_eq!(
            fix(&[source], "Generate constructor 'Person(string)'"),
            "class Person\n{\n    public string Name { get; }\n\n    public Person() { }\n\n    public Person(string name)\n    {\n        Name = name;\n    }\n}\nclass C\n{\n    Person M(string name) => new Person(name);\n}\n"
        );
        assert_eq!(
            fix(&[source], "Add parameter to 'Person()'"),
            "class Person\n{\n    public string Name { get; }\n\n    public Person(string name) { }\n}\nclass C\n{\n    Person M(string name) => new Person(name);\n}\n"
        );
    }

    #[test]
    fn a_constructor_that_fits_offers_nothing() {
        let source = "class Person\n{\n    public Person(object o) { }\n}\nclass C\n{\n    Person M() => new $$Person(\"a\");\n}\n";
        assert!(
            !titles(&[source])
                .iter()
                .any(|title| title.contains("constructor"))
        );
    }

    #[test]
    fn an_empty_class_gets_fields_and_constructor_together() {
        let source = "class Box { }\nclass C\n{\n    Box M() => new $$Box(3);\n}\n";
        assert_eq!(
            fix(&[source], "Generate constructor 'Box(int)'"),
            "class Box\n{\n    private int v;\n\n    public Box(int v)\n    {\n        this.v = v;\n    }\n}\nclass C\n{\n    Box M() => new Box(3);\n}\n"
        );
    }
}
