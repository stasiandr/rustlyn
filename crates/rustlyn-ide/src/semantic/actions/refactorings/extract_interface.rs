//! Extract interface: a new interface declaring members of a type, which
//! the type then implements.
//!
//! Roslyn's `ExtractInterface` service, which Visual Studio drives through a
//! dialog choosing the interface's name, its members and whether it goes in
//! a file of its own. [`Semantic::extract_interface`] takes those choices;
//! the light bulb's "Extract interface..." makes the dialog's defaults: `I`
//! and the type's name, every public instance member, a new file.
//!
//! The interface declares each chosen member's signature — a method's
//! return type, name, type parameters, parameters and constraints; a
//! property's or indexer's public accessors; an event — and takes the
//! type's type parameters that those signatures use, with their
//! constraints. It is as accessible as the type. In a new file it is under
//! the `using`s of the type's file that the signatures need, in the type's
//! namespace; in the same file it goes just above the type. The type gets
//! the interface at the end of its base list.

use std::path::Path;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::is_identifier;
use super::super::{ActionKind, CodeAction, Context};
use super::members::{
    Member, add_base, chosen, insert_type_before, is_public_instance, members_of, name_is_taken,
    needed_usings, new_file, new_file_beside, signature, type_accessibility, type_around,
    type_named_at_cursor,
};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::Semantic;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(declaration) = type_named_at_cursor(context) else {
        return;
    };
    if declaration.kind() == SyntaxKind::InterfaceDeclaration {
        return;
    }
    let members = members_of(context, &declaration);
    let names: Vec<String> = members
        .iter()
        .filter(|member| is_public_instance(context, member) && signature(&member.node).is_some())
        .map(|member| member.name.clone())
        .collect();
    if names.is_empty() {
        return;
    }
    let Some(type_name) = declaration.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let mut name = format!("I{}", type_name.value_text());
    let mut counter = 1;
    while name_is_taken(context, &declaration, &name) {
        name = format!("I{}{counter}", type_name.value_text());
        counter += 1;
    }
    let in_new_file = new_file_beside(context, &context.path.clone(), &name).is_some();
    if let Ok(edit) = extract(context, &declaration, &name, &names, in_new_file) {
        found.push(CodeAction {
            title: "Extract interface...".to_string(),
            kind: ActionKind::Extract,
            fixes: None,
            edit,
        });
    }
}

impl Semantic {
    /// Extracts an interface called `name` from the type at `offset` of
    /// `path`, declaring the members called `members` (every overload of
    /// each), into a new file beside it or above the type in its own file.
    ///
    /// # Errors
    ///
    /// Why it cannot: no type there, a name that is not an identifier or is
    /// taken, a member that is not public or not there.
    pub fn extract_interface(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        name: &str,
        members: &[String],
        in_new_file: bool,
    ) -> Result<WorkspaceEdit, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a type.".to_string())?;
            extract(context, &declaration, name, members, in_new_file)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

fn extract(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    name: &str,
    names: &[String],
    in_new_file: bool,
) -> Result<WorkspaceEdit, String> {
    if !is_identifier(name) {
        return Err(format!("'{name}' is not a valid name."));
    }
    if name_is_taken(context, declaration, name) {
        return Err(format!("There is already a type called '{name}'."));
    }
    let all = members_of(context, declaration);
    let chosen: Vec<Member> = chosen(&all, names)?.into_iter().cloned().collect();
    let mut signatures = Vec::new();
    for member in &chosen {
        if !is_public_instance(context, member) {
            return Err(format!(
                "'{}' is not a public instance member.",
                member.name
            ));
        }
        let Some(signature) = signature(&member.node) else {
            return Err(format!(
                "'{}' cannot be declared in an interface.",
                member.name
            ));
        };
        signatures.push(
            if member.node.kind() == SyntaxKind::PropertyDeclaration
                || member.node.kind() == SyntaxKind::IndexerDeclaration
            {
                signature
            } else {
                format!("{signature};")
            },
        );
    }

    // The type's type parameters the signatures use.
    let used: std::collections::HashSet<String> = chosen
        .iter()
        .flat_map(|member| signature_nodes(&member.node))
        .flat_map(|node| node.descendant_tokens().collect::<Vec<_>>())
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
        .collect();
    let type_parameters: Vec<String> = declaration
        .child_of_kind(SyntaxKind::TypeParameterList)
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::TypeParameter)
                .filter_map(|parameter| {
                    parameter
                        .child_token_of_kind(SyntaxKind::IdentifierToken)
                        .map(|token| token.value_text().to_string())
                })
                .filter(|parameter| used.contains(parameter))
                .collect()
        })
        .unwrap_or_default();
    let constraints: Vec<String> = declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
        .filter(|clause| {
            clause
                .descendant_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                .is_some_and(|parameter| {
                    type_parameters
                        .iter()
                        .any(|name| name == parameter.value_text())
                })
        })
        .map(|clause| clause.text())
        .collect();
    let generic = if type_parameters.is_empty() {
        String::new()
    } else {
        format!("<{}>", type_parameters.join(", "))
    };
    let where_clauses = if constraints.is_empty() {
        String::new()
    } else {
        format!(" {}", constraints.join(" "))
    };
    let body: Vec<String> = signatures
        .iter()
        .map(|line| format!("    {line}"))
        .collect();
    let interface = format!(
        "{}interface {name}{generic}{where_clauses}\n{{\n{}\n}}",
        type_accessibility(declaration),
        body.join("\n")
    );

    let mut edit = WorkspaceEdit::default();
    let base = add_base(declaration, &format!("{name}{generic}"), false)
        .ok_or_else(|| "The type's base list cannot be written.".to_string())?;
    edit.add(context.path.clone(), base);
    if in_new_file {
        let target = new_file_beside(context, &context.path.clone(), name)
            .ok_or_else(|| format!("There is already a file called {name}.cs."))?;
        let nodes: Vec<SyntaxNode> = chosen
            .iter()
            .flat_map(|member| signature_nodes(&member.node))
            .collect();
        let root = context.view.syntax_root().clone();
        let usings = needed_usings(context, &root, &nodes);
        let file = new_file(&context.text, declaration, &usings, &interface);
        edit.add(target, TextEdit::insert(0, file));
    } else {
        edit.add(
            context.path.clone(),
            insert_type_before(&context.text, declaration, &interface),
        );
    }
    Ok(edit)
}

/// The parts of a member's declaration its signature is written from.
pub(super) fn signature_nodes(member: &SyntaxNode) -> Vec<SyntaxNode> {
    let mut nodes: Vec<SyntaxNode> = member
        .children()
        .filter(|child| {
            child.kind().is_type_node()
                || matches!(
                    child.kind(),
                    SyntaxKind::ParameterList
                        | SyntaxKind::BracketedParameterList
                        | SyntaxKind::TypeParameterConstraintClause
                )
        })
        .collect();
    if let Some(declaration) = member.child_of_kind(SyntaxKind::VariableDeclaration)
        && let Some(ty) = declaration
            .children()
            .find(|child| child.kind().is_type_node())
    {
        nodes.push(ty);
    }
    nodes
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::support::{apply_in, refuses};
    use crate::semantic::tests::compile;

    fn file<'a>(files: &'a [(PathBuf, String)], name: &str) -> &'a str {
        &files
            .iter()
            .find(|(path, _)| path == Path::new(name))
            .expect("the file")
            .1
    }

    #[test]
    fn the_light_bulb_extracts_every_public_member_into_a_new_file() {
        let source = "using System;\nusing System.Collections.Generic;\nusing System.Text;\n\nnamespace Shop\n{\n    public class $$Cart\n    {\n        private readonly List<string> items = new List<string>();\n\n        public int Count => items.Count;\n\n        public string this[int index] { get => items[index]; }\n\n        public event Action Changed;\n\n        public void Add(string item)\n        {\n            items.Add(item);\n        }\n\n        public List<string> Items() => items;\n\n        public static Cart Empty() => new Cart();\n\n        private void Log() { }\n    }\n}\n";
        let changed = apply_in(&[("Cart.cs", source)], "Extract interface...");
        assert_eq!(
            file(&changed, "/p/ICart.cs"),
            "using System;\nusing System.Collections.Generic;\n\nnamespace Shop\n{\n    public interface ICart\n    {\n        int Count { get; }\n        string this[int index] { get; }\n        event Action Changed;\n        void Add(string item);\n        List<string> Items();\n    }\n}\n"
        );
        assert!(file(&changed, "/p/Cart.cs").contains("public class Cart : ICart\n"));
    }

    #[test]
    fn chosen_members_go_above_the_type_with_the_type_parameters_they_use() {
        let text = "class Repository<T, TKey> : System.Object where T : class\n{\n    public T Find(TKey key) => null;\n    public int Size { get; private set; }\n    public void Clear() { }\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let edit = semantic
            .extract_interface(
                Path::new("/p/A.cs"),
                text.find("Repository").unwrap() as u32,
                None,
                "IReader",
                &["Find".to_string(), "Size".to_string()],
                false,
            )
            .expect("extracted");
        assert_eq!(
            crate::edit::apply(text, edit.edits_of(Path::new("/p/A.cs"))),
            "interface IReader<T, TKey> where T : class\n{\n    T Find(TKey key);\n    int Size { get; }\n}\n\nclass Repository<T, TKey> : System.Object, IReader<T, TKey> where T : class\n{\n    public T Find(TKey key) => null;\n    public int Size { get; private set; }\n    public void Clear() { }\n}\n"
        );
        let refused = semantic
            .extract_interface(
                Path::new("/p/A.cs"),
                text.find("Repository").unwrap() as u32,
                None,
                "IReader",
                &["Missing".to_string()],
                false,
            )
            .expect_err("no such member");
        assert!(refused.contains("Missing"));
    }

    #[test]
    fn nothing_public_nothing_offered() {
        refuses(
            "class $$Hidden\n{\n    void M() { }\n    static public void S() { }\n}\n",
            "Extract interface...",
        );
    }
}
