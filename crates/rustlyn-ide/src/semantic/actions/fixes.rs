//! Code fixes: an answer to a diagnostic at the cursor.
//!
//! Each provider lives in a file of its own under `fixes/` and is asked in
//! turn. Most answer a diagnostic the binder reported: a name it could not
//! find (CS0246, CS0103, CS0117 on a type and CS1061 on a value), a
//! conversion it would not make
//! (CS0029, CS1503), a missing `;` (CS1002). A few answer a mistake the
//! binder does not report yet and the provider sees for itself, under the
//! code Roslyn gives it: an interface member left unimplemented (CS0535), an
//! abstract one not overridden (CS0534), `await` outside an `async` method
//! (CS4032, CS4033), a constructor call nothing takes (CS1729), a member that
//! hides an inherited one without saying so (CS0108, CS0114), a local never
//! used (CS0168, CS0219). Populating a `switch` answers no diagnostic at all,
//! as in Roslyn, where it is offered on any `switch` over an enum that does
//! not name every member.

use rustlyn_semantics::Type;
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};

use super::{CodeAction, Context};

mod add_cast;
mod add_using;
mod generate_constructor;
mod generate_member;
mod generate_type;
mod hide_base;
mod implement;
mod make_async;
mod populate_switch;
mod small;
mod spelling;
pub(crate) mod support;

/// Asks every fix provider about the place.
pub(super) fn collect(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let names = unresolved_names(context);
    add_using::offer(context, &names, found);
    spelling::offer(context, &names, found);
    generate_member::offer(context, &names, found);
    generate_type::offer(context, &names, found);
    generate_constructor::offer(context, found);
    implement::offer(context, found);
    make_async::offer(context, found);
    add_cast::offer(context, found);
    hide_base::offer(context, found);
    populate_switch::offer(context, found);
    small::offer(context, found);
}

/// A name the binder could not find, where it is written and how.
#[derive(Clone, Debug)]
pub(crate) struct Unresolved {
    /// The diagnostic that says so: `CS0246`, `CS0103`, `CS0117` or `CS1061`.
    pub code: String,
    /// The `IdentifierName` or `GenericName`.
    pub name: SyntaxNode,
    pub identifier: SyntaxToken,
    /// How many type arguments it was written with.
    pub arity: usize,
    /// Written where a type goes rather than where a value does.
    pub in_type: bool,
    /// The name of an attribute, which may leave off `Attribute`.
    pub attribute: bool,
    /// What is left of the dot, for `x.Name` or `N.Name`.
    pub receiver: Option<SyntaxNode>,
}

impl Unresolved {
    /// The name as written, without type arguments.
    pub(crate) fn text(&self) -> &str {
        self.identifier.value_text()
    }

    /// The invocation this name is the method of: `Name(...)` or
    /// `x.Name(...)`.
    pub(crate) fn invocation(&self) -> Option<SyntaxNode> {
        let callee = self.expression();
        let parent = callee.parent()?.clone();
        (parent.kind() == SyntaxKind::InvocationExpression
            && parent.children().next().as_ref() == Some(&callee))
        .then_some(parent)
    }

    /// The whole expression the name is: `x.Name` rather than `Name` when
    /// it has a receiver.
    pub(crate) fn expression(&self) -> SyntaxNode {
        match self.name.parent() {
            Some(parent)
                if self.receiver.is_some()
                    && matches!(
                        parent.kind(),
                        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName
                    ) =>
            {
                parent.clone()
            }
            _ => self.name.clone(),
        }
    }
}

/// The unresolved names at the place asked about: those the diagnostics
/// there report, and a type name at the cursor that does not resolve where
/// the binder has no body to report it from — a field's type, a
/// parameter's, a base type, an attribute.
fn unresolved_names(context: &mut Context<'_, '_>) -> Vec<Unresolved> {
    let mut found: Vec<Unresolved> = Vec::new();
    let reported: Vec<(String, rustlyn_text::TextSpan)> = context
        .diagnostics_with(&["CS0246", "CS0103", "CS0117", "CS1061"])
        .map(|diagnostic| (diagnostic.code().to_string(), diagnostic.span()))
        .collect();
    for (code, span) in reported {
        let Some(node) = context.view.root.find_node(span) else {
            continue;
        };
        let name = match node.kind() {
            SyntaxKind::QualifiedName | SyntaxKind::SimpleMemberAccessExpression => {
                match node.children().last() {
                    Some(last) => last,
                    None => continue,
                }
            }
            _ => node,
        };
        if let Some(unresolved) = describe(&name, &code) {
            found.push(unresolved);
        }
    }
    if found.is_empty()
        && let Some(unresolved) = unresolved_type_at(context)
    {
        found.push(unresolved);
    }
    found
}

/// What an unresolved name node is, given the diagnostic about it.
fn describe(name: &SyntaxNode, code: &str) -> Option<Unresolved> {
    if !matches!(
        name.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) {
        return None;
    }
    let identifier = name
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
    let arity = name
        .child_of_kind(SyntaxKind::TypeArgumentList)
        .map_or(0, |list| {
            list.children()
                .filter(|child| child.kind().is_type_node())
                .count()
        });
    let parent = name.parent().cloned();
    let receiver = parent.as_ref().and_then(|parent| {
        (matches!(
            parent.kind(),
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName
        ) && parent.children().last().as_ref() == Some(name))
        .then(|| parent.children().next())
        .flatten()
    });
    // Climb a qualified name to what holds it, to see whether that is an
    // attribute.
    let mut top = name.clone();
    while let Some(parent) = top.parent().cloned()
        && parent.kind() == SyntaxKind::QualifiedName
    {
        top = parent;
    }
    let attribute = top.parent().is_some_and(|parent| {
        parent.kind() == SyntaxKind::Attribute && parent.children().next().as_ref() == Some(&top)
    });
    Some(Unresolved {
        code: code.to_string(),
        name: name.clone(),
        identifier,
        arity,
        in_type: code == "CS0246" || attribute,
        attribute,
        receiver,
    })
}

/// A type name at the cursor, outside any body, that names nothing.
fn unresolved_type_at(context: &mut Context<'_, '_>) -> Option<Unresolved> {
    let token = context.view.name_token_at(context.span.start())?;
    if token.kind() != SyntaxKind::IdentifierToken
        || matches!(token.value_text(), "var" | "dynamic" | "nameof" | "_")
    {
        return None;
    }
    let name = token.parent().clone();
    if !matches!(
        name.kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    ) {
        return None;
    }
    let mut top = name.clone();
    while let Some(parent) = top.parent().cloned()
        && parent.kind() == SyntaxKind::QualifiedName
    {
        top = parent;
    }
    let holder = top.parent()?.clone();
    if holder.kind().is_expression_node()
        || matches!(
            holder.kind(),
            SyntaxKind::Argument
                | SyntaxKind::UsingDirective
                | SyntaxKind::NamespaceDeclaration
                | SyntaxKind::FileScopedNamespaceDeclaration
                | SyntaxKind::NameEquals
                | SyntaxKind::ExplicitInterfaceSpecifier
        )
        || top.ancestors().any(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::Block
                    | SyntaxKind::ArrowExpressionClause
                    | SyntaxKind::EqualsValueClause
            )
        })
    {
        return None;
    }
    if holder.kind() == SyntaxKind::Attribute {
        if context.view.attribute_type(&holder).is_some() {
            return None;
        }
    } else if !matches!(context.view.model.type_of_syntax(&top), Type::Error) {
        return None;
    }
    describe(&name, "CS0246")
}

#[cfg(test)]
pub(crate) mod tests {
    use std::path::Path;

    use rustlyn_text::TextSpan;

    use crate::semantic::{CodeAction, Semantic};

    /// The files compiled, with the cursor where `$$` is in the first one
    /// (which is `A.cs`; the others are `B.cs`, `C.cs` and on).
    fn compile(files: &[&str]) -> (Semantic, String, u32) {
        let first = files[0];
        let cursor = first.find("$$").expect("the first file should have a $$") as u32;
        let text = first.replace("$$", "");
        let names = ["A.cs", "B.cs", "C.cs", "D.cs"];
        let mut sources: Vec<(&str, &str)> = vec![(names[0], text.as_str())];
        for (index, file) in files.iter().enumerate().skip(1) {
            sources.push((names[index], file));
        }
        let semantic = crate::semantic::tests::compile(&sources, false).expect("compiles");
        (semantic, text, cursor)
    }

    /// Every action offered at the `$$`.
    pub(crate) fn actions(files: &[&str]) -> Vec<CodeAction> {
        let (semantic, _, cursor) = compile(files);
        semantic
            .code_actions(Path::new("/p/A.cs"), TextSpan::at(cursor), None)
            .expect("the file is compiled")
    }

    /// The titles offered at the `$$`.
    pub(crate) fn titles(files: &[&str]) -> Vec<String> {
        actions(files)
            .into_iter()
            .map(|action| action.title)
            .collect()
    }

    /// The first file after choosing the action called `title`.
    pub(crate) fn fix(files: &[&str], title: &str) -> String {
        fix_file(files, title, "A.cs")
    }

    /// `file` after choosing the action called `title` at the `$$` of the
    /// first file. A file the action creates starts out empty.
    pub(crate) fn fix_file(files: &[&str], title: &str, file: &str) -> String {
        let (semantic, text, cursor) = compile(files);
        let actions = semantic
            .code_actions(Path::new("/p/A.cs"), TextSpan::at(cursor), None)
            .expect("the file is compiled");
        let Some(action) = actions.iter().find(|action| action.title == title) else {
            let offered: Vec<&str> = actions.iter().map(|action| action.title.as_str()).collect();
            panic!("no action {title:?}; offered: {offered:?}");
        };
        let path = format!("/p/{file}");
        let before = if file == "A.cs" {
            text
        } else {
            semantic
                .text(Path::new(&path))
                .map(str::to_owned)
                .unwrap_or_default()
        };
        crate::edit::apply(&before, action.edit.edits_of(Path::new(&path)))
    }

    #[test]
    fn fixes_answer_the_text_the_editor_has() {
        let saved = "namespace App\n{\n    class C\n    {\n        void M()\n        {\n        }\n\n        int Count => 1;\n    }\n}\n";
        let other = "namespace System.Text { public class StringBuilder { } }\n";
        let semantic = crate::semantic::tests::compile(&[("A.cs", saved), ("B.cs", other)], false)
            .expect("compiles");
        let typed = "namespace App\n{\n    class C\n    {\n        void M()\n        {\n            var b = new StringBuilder();\n            int n = Countt;\n        }\n\n        int Count => 1;\n    }\n}\n";
        let at = typed.find("StringBuilder").expect("typed") as u32;
        let actions = semantic
            .code_actions(Path::new("/p/A.cs"), TextSpan::at(at), Some(typed))
            .expect("compiled");
        let using = actions
            .iter()
            .find(|action| action.title == "using System.Text;")
            .expect("offered on unsaved text");
        assert_eq!(
            crate::edit::apply(typed, using.edit.edits_of(Path::new("/p/A.cs"))),
            format!("using System.Text;\n\n{typed}")
        );
        let at = typed.find("Countt").expect("typed") as u32;
        let actions = semantic
            .code_actions(Path::new("/p/A.cs"), TextSpan::at(at), Some(typed))
            .expect("compiled");
        assert!(
            actions
                .iter()
                .any(|action| action.title == "Change 'Countt' to 'Count'."),
            "{actions:?}"
        );
    }
}
