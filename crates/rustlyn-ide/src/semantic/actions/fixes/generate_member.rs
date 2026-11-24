//! Generate method, property, field, read-only field, local and parameter:
//! a name that is used as if it existed, made to exist.
//!
//! Roslyn's `GenerateMethod` and `GenerateVariable`. The new member goes
//! into the type the name was looked up in — the one the code is in for a
//! simple name, the receiver's for `x.Name`, which must be declared in the
//! project — and is `static` where it was reached through the type or from
//! static code. Its type comes from how it is used: an invoked name becomes
//! a method taking parameters shaped like the arguments and returning what
//! the call's surroundings want (`void` for a call on its own, `object`
//! where nothing says); any other becomes a property or field of the type
//! assigned to it or expected of it.
//!
//! In its own type a new member is `private`, in another `internal`, and in
//! an interface it is a declaration without a body. A method is written
//! after the member that uses it, a field after the other fields, a
//! property at the end.

use rustlyn_semantics::{Modifiers, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::Unresolved;
use super::support::{
    Declaration, MemberPlace, Namer, arguments_of, declaration_of, expected_type, indentation_at,
    insert_members, is_assignment, is_member, line_start, newline,
};
use crate::edit::TextEdit;

pub(super) fn offer(
    context: &mut Context<'_, '_>,
    names: &[Unresolved],
    found: &mut Vec<CodeAction>,
) {
    for name in names {
        if name.in_type
            || !matches!(name.code.as_str(), "CS0103" | "CS0117" | "CS1061")
            || name.arity > 0
        {
            continue;
        }
        let Some(target) = target(context, name) else {
            continue;
        };
        match name.invocation() {
            Some(invocation) => method(context, name, &target, &invocation, found),
            None => variables(context, name, &target, found),
        }
    }
}

/// Where a new member for a name would go.
struct Target {
    declaration: Declaration,
    is_static: bool,
    /// The code using the name is in this type.
    own: bool,
    interface: bool,
}

impl Target {
    /// `private `, `internal ` or nothing, and `static `.
    fn modifiers(&self) -> String {
        if self.interface {
            return String::new();
        }
        let access = if self.own { "private " } else { "internal " };
        let is_static = if self.is_static { "static " } else { "" };
        format!("{access}{is_static}")
    }

    /// After the member the name is used in, when that is in this type.
    fn after_use(&self, name: &SyntaxNode) -> MemberPlace {
        if self.declaration.path.is_none() {
            let user = std::iter::once(name.clone())
                .chain(name.ancestors())
                .find(|node| {
                    is_member(node.kind())
                        && node
                            .parent()
                            .is_some_and(|parent| *parent == self.declaration.node)
                });
            if let Some(user) = user {
                return MemberPlace::After(user.span());
            }
        }
        MemberPlace::End
    }
}

fn target(context: &mut Context<'_, '_>, name: &Unresolved) -> Option<Target> {
    let view = &mut *context.view;
    let binder_context = view.model.binder().context_at(view.tree, &name.name);
    let enclosing = binder_context.enclosing_type();
    let symbols = view.compilation().symbols();
    let (ty, is_static) = match &name.receiver {
        None => {
            let ty = enclosing?;
            let member_static = binder_context
                .enclosing_member()
                .is_some_and(|member| symbols.get(member).modifiers.contains(Modifiers::STATIC));
            (
                ty,
                member_static || symbols.get(ty).modifiers.contains(Modifiers::STATIC),
            )
        }
        Some(receiver) if receiver.kind() == SyntaxKind::ThisExpression => (enclosing?, false),
        Some(receiver) if receiver.kind() == SyntaxKind::BaseExpression => return None,
        Some(receiver) => match view.named(receiver) {
            Some(symbol) if symbols.get(symbol).kind == SymbolKind::NamedType => (symbol, true),
            Some(_) => return None,
            None => (view.type_of(receiver).symbol()?, false),
        },
    };
    let compilation = view.compilation();
    if compilation.is_from_corlib(ty)
        || !matches!(
            symbols.get(ty).type_kind(),
            Some(
                TypeKind::Class
                    | TypeKind::Struct
                    | TypeKind::Interface
                    | TypeKind::Record
                    | TypeKind::RecordStruct
            )
        )
    {
        return None;
    }
    let declaration = declaration_of(view, ty, &context.text)?;
    let own = view.enclosing_types(&name.name).contains(&ty);
    Some(Target {
        declaration,
        is_static,
        own,
        interface: symbols.get(ty).type_kind() == Some(TypeKind::Interface),
    })
}

fn method(
    context: &mut Context<'_, '_>,
    name: &Unresolved,
    target: &Target,
    invocation: &SyntaxNode,
    found: &mut Vec<CodeAction>,
) {
    let arguments = invocation
        .child_of_kind(SyntaxKind::ArgumentList)
        .map(|list| arguments_of(context.view, &list))
        .unwrap_or_default();
    let returns = expected_type(context.view, invocation);
    let view = &*context.view;
    let namer = Namer::at(view, &target.declaration.node);
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
    let head = format!(
        "{}{} {}({})",
        target.modifiers(),
        namer.name(&returns),
        name.text(),
        parameters.join(", ")
    );
    let text = if target.interface {
        format!("{head};")
    } else {
        format!("{head}\n{{\n    {}\n}}", namer.not_implemented())
    };
    let place = target.after_use(&name.name);
    if let Some(edit) = insert_members(
        &target.declaration.node,
        &target.declaration.text,
        &[text],
        &place,
    ) {
        found.push(target.declaration.action(
            context,
            format!("Generate method '{}'", name.text()),
            ActionKind::Generate,
            Some(&name.code),
            vec![edit],
        ));
    }
}

fn variables(
    context: &mut Context<'_, '_>,
    name: &Unresolved,
    target: &Target,
    found: &mut Vec<CodeAction>,
) {
    let expression = name.expression();
    let written = is_written(&expression);
    let ty = expected_type(context.view, &expression);
    let ty = if ty == Type::Void { Type::Error } else { ty };
    let text = name.text().to_string();
    let modifiers = target.modifiers();
    let view = &*context.view;
    let namer = Namer::at(view, &target.declaration.node);
    let type_name = namer.name(&ty);
    let mut actions: Vec<CodeAction> = Vec::new();

    // Property.
    let property = format!("{modifiers}{type_name} {text} {{ get; set; }}");
    if let Some(edit) = insert_members(
        &target.declaration.node,
        &target.declaration.text,
        &[property],
        &MemberPlace::End,
    ) {
        actions.push(target.declaration.action(
            context,
            format!("Generate property '{text}'"),
            ActionKind::Generate,
            Some(&name.code),
            vec![edit],
        ));
    }
    // Field, and a read-only one where nothing writes it.
    if !target.interface {
        let field = format!("{modifiers}{type_name} {text};");
        if let Some(edit) = insert_members(
            &target.declaration.node,
            &target.declaration.text,
            &[field],
            &MemberPlace::Fields,
        ) {
            actions.push(target.declaration.action(
                context,
                format!("Generate field '{text}'"),
                ActionKind::Generate,
                Some(&name.code),
                vec![edit],
            ));
        }
        if !written {
            let field = format!("{modifiers}readonly {type_name} {text};");
            if let Some(edit) = insert_members(
                &target.declaration.node,
                &target.declaration.text,
                &[field],
                &MemberPlace::Fields,
            ) {
                actions.push(target.declaration.action(
                    context,
                    format!("Generate read-only field '{text}'"),
                    ActionKind::Generate,
                    Some(&name.code),
                    vec![edit],
                ));
            }
        }
    }
    // A lower-case name reads as a field first, an upper-case one as a
    // property.
    if text.starts_with(char::is_lowercase) && actions.len() > 1 {
        actions.rotate_left(1);
    }
    found.extend(actions);

    if name.receiver.is_none() {
        local(context, name, &type_name, &expression, found);
        parameter(context, name, &type_name, found);
    }
}

/// Whether an expression is written to: assigned, incremented, or passed
/// by `ref` or `out`.
fn is_written(expression: &SyntaxNode) -> bool {
    let Some(parent) = expression.parent() else {
        return false;
    };
    match parent.kind() {
        kind if is_assignment(kind) => parent.children().next().as_ref() == Some(expression),
        SyntaxKind::PreIncrementExpression
        | SyntaxKind::PreDecrementExpression
        | SyntaxKind::PostIncrementExpression
        | SyntaxKind::PostDecrementExpression => true,
        SyntaxKind::Argument => {
            parent.child_token_of_kind(SyntaxKind::RefKeyword).is_some()
                || parent.child_token_of_kind(SyntaxKind::OutKeyword).is_some()
        }
        _ => false,
    }
}

/// Generate local: `name = value;` becomes a declaration of it; any other
/// use gets one on the line above the statement it is in.
fn local(
    context: &Context<'_, '_>,
    name: &Unresolved,
    type_name: &str,
    expression: &SyntaxNode,
    found: &mut Vec<CodeAction>,
) {
    let Some(statement) = expression.ancestors().find(|node| {
        node.kind().is_statement_node()
            && node.parent().is_some_and(|parent| {
                matches!(parent.kind(), SyntaxKind::Block | SyntaxKind::SwitchSection)
            })
    }) else {
        return;
    };
    let text = name.text();
    let assigned = statement.kind() == SyntaxKind::ExpressionStatement
        && statement.children().next().is_some_and(|assignment| {
            assignment.kind() == SyntaxKind::SimpleAssignmentExpression
                && assignment.children().next().as_ref() == Some(expression)
        });
    let edit = if assigned {
        TextEdit::insert(expression.span().start(), format!("{type_name} "))
    } else {
        let indent = indentation_at(&context.text, statement.span().start());
        let nl = newline(&context.text);
        TextEdit::insert(
            line_start(&context.text, statement.span().start()),
            format!("{indent}{type_name} {text} = default;{nl}"),
        )
    };
    found.push(context.local(
        format!("Generate local '{text}'"),
        ActionKind::Generate,
        Some(&name.code),
        vec![edit],
    ));
}

/// Generate parameter: added at the end of the enclosing method's or
/// constructor's parameters.
fn parameter(
    context: &Context<'_, '_>,
    name: &Unresolved,
    type_name: &str,
    found: &mut Vec<CodeAction>,
) {
    let Some(member) = name.name.ancestors().find(|node| {
        matches!(
            node.kind(),
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::LocalFunctionStatement
        )
    }) else {
        return;
    };
    let Some(list) = member.child_of_kind(SyntaxKind::ParameterList) else {
        return;
    };
    let Some(close) = list.child_token_of_kind(SyntaxKind::CloseParenToken) else {
        return;
    };
    let separator = if list
        .children()
        .any(|child| child.kind() == SyntaxKind::Parameter)
    {
        ", "
    } else {
        ""
    };
    let text = name.text();
    found.push(context.local(
        format!("Generate parameter '{text}'"),
        ActionKind::Generate,
        Some(&name.code),
        vec![TextEdit::insert(
            close.span().start(),
            format!("{separator}{type_name} {text}"),
        )],
    ));
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, fix_file, titles};

    #[test]
    fn a_call_generates_a_method_after_the_caller() {
        let source = "using System;\n\nclass C\n{\n    void M()\n    {\n        int x = $$Compute(1, \"a\");\n    }\n\n    void Other() { }\n}\n";
        assert_eq!(
            fix(&[source], "Generate method 'Compute'"),
            "using System;\n\nclass C\n{\n    void M()\n    {\n        int x = Compute(1, \"a\");\n    }\n\n    private int Compute(int v1, string v2)\n    {\n        throw new NotImplementedException();\n    }\n\n    void Other() { }\n}\n"
        );
    }

    #[test]
    fn a_statement_call_returns_void_and_static_code_makes_it_static() {
        let source = "class C\n{\n    static void Main(string[] args)\n    {\n        var builder = new System.Text.StringBuilder();\n        $$Report(args, builder, args.Length);\n    }\n}\n";
        let text = "namespace System.Text { public class StringBuilder { } }\n";
        assert_eq!(
            fix(&[source, text], "Generate method 'Report'"),
            "class C\n{\n    static void Main(string[] args)\n    {\n        var builder = new System.Text.StringBuilder();\n        Report(args, builder, args.Length);\n    }\n\n    private static void Report(string[] args, System.Text.StringBuilder builder, int length)\n    {\n        throw new System.NotImplementedException();\n    }\n}\n"
        );
    }

    #[test]
    fn a_method_of_another_type_goes_into_its_file() {
        let source = "class C\n{\n    void M(Q q)\n    {\n        bool ok = q.$$Check(out var count);\n    }\n}\n";
        let other = "class Q\n{\n    int field;\n}\n";
        assert_eq!(
            fix_file(&[source, other], "Generate method 'Check'", "B.cs"),
            "class Q\n{\n    int field;\n\n    internal bool Check(out object count)\n    {\n        throw new System.NotImplementedException();\n    }\n}\n"
        );
    }

    #[test]
    fn a_static_call_through_the_type_is_static() {
        let source =
            "class C\n{\n    void M()\n    {\n        Q.$$Make();\n    }\n}\nclass Q\n{\n}\n";
        assert_eq!(
            fix(&[source], "Generate method 'Make'"),
            "class C\n{\n    void M()\n    {\n        Q.Make();\n    }\n}\nclass Q\n{\n    internal static void Make()\n    {\n        throw new System.NotImplementedException();\n    }\n}\n"
        );
    }

    #[test]
    fn a_method_in_an_interface_has_no_body() {
        let source =
            "interface IRepo\n{\n}\nclass C\n{\n    string M(IRepo repo) => repo.$$Find(3);\n}\n";
        assert_eq!(
            fix(&[source], "Generate method 'Find'"),
            "interface IRepo\n{\n    string Find(int v);\n}\nclass C\n{\n    string M(IRepo repo) => repo.Find(3);\n}\n"
        );
    }

    #[test]
    fn an_assigned_member_generates_a_property_or_a_field() {
        let source = "class C\n{\n    int count;\n\n    void M()\n    {\n        this.$$Total = 3;\n    }\n}\n";
        let offered = titles(&[source]);
        assert_eq!(
            &offered[..2],
            ["Generate property 'Total'", "Generate field 'Total'"],
            "{offered:?}"
        );
        assert!(!offered.contains(&"Generate read-only field 'Total'".to_string()));
        assert_eq!(
            fix(&[source], "Generate property 'Total'"),
            "class C\n{\n    int count;\n\n    void M()\n    {\n        this.Total = 3;\n    }\n\n    private int Total { get; set; }\n}\n"
        );
        assert_eq!(
            fix(&[source], "Generate field 'Total'"),
            "class C\n{\n    int count;\n    private int Total;\n\n    void M()\n    {\n        this.Total = 3;\n    }\n}\n"
        );
    }

    #[test]
    fn a_read_name_generates_a_read_only_field_local_or_parameter() {
        let source =
            "class C\n{\n    void M(int a)\n    {\n        string s = $$label;\n    }\n}\n";
        let offered = titles(&[source]);
        assert_eq!(offered[0], "Generate field 'label'", "{offered:?}");
        assert_eq!(
            fix(&[source], "Generate read-only field 'label'"),
            "class C\n{\n    private readonly string label;\n\n    void M(int a)\n    {\n        string s = label;\n    }\n}\n"
        );
        assert_eq!(
            fix(&[source], "Generate local 'label'"),
            "class C\n{\n    void M(int a)\n    {\n        string label = default;\n        string s = label;\n    }\n}\n"
        );
        assert_eq!(
            fix(&[source], "Generate parameter 'label'"),
            "class C\n{\n    void M(int a, string label)\n    {\n        string s = label;\n    }\n}\n"
        );
    }

    #[test]
    fn an_assignment_to_a_new_local_becomes_its_declaration() {
        let source = "class C\n{\n    void M()\n    {\n        $$total = 2.5;\n    }\n}\n";
        assert_eq!(
            fix(&[source], "Generate local 'total'"),
            "class C\n{\n    void M()\n    {\n        double total = 2.5;\n    }\n}\n"
        );
    }

    #[test]
    fn nothing_is_generated_into_the_core_library() {
        let source =
            "class C\n{\n    void M(string s)\n    {\n        s.$$Frobnicate();\n    }\n}\n";
        assert!(
            !titles(&[source])
                .iter()
                .any(|title| title.starts_with("Generate"))
        );
    }
}
