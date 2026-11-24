//! Move static members to another type, and every use of them with them.
//!
//! Roslyn's `MoveStaticMembers` refactoring, which Visual Studio drives
//! through a dialog choosing the members and the type they go to — one
//! that exists, or a new one. [`Semantic::move_static_members`] takes those
//! choices; the light bulb's "Move static members to another type..." with
//! the cursor on a static member moves it, and the private static members
//! it uses, to a new static class named after the type with `Helpers`, in a
//! new file.
//!
//! * The members are cut from the type and pasted into the destination; a
//!   new destination is a `static class` as accessible as the type, in the
//!   type's namespace.
//! * Every use of a moved member across the project names the destination:
//!   `Type.M()` becomes `Helpers.M()`, and an unqualified `M()` in the code
//!   that stays becomes `Helpers.M()`.
//! * Code that moves and uses a static member that stays names the type it
//!   stays in; a private member that is used from the other side of the
//!   move becomes `internal`.
//!
//! A moved member that uses a private member staying behind cannot see it
//! from its new type, and is refused.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use rustlyn_semantics::{Accessibility, Modifiers, SymbolId, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::fixes::support::declaration_of;
use super::super::text::is_identifier;
use super::super::{ActionKind, CodeAction, Context};
use super::members::{
    Member, accessibility_text, insert_type_before, member_text_with, members_of, name_is_taken,
    needed_usings, new_file, new_file_beside, remove_members, rewrite_modifiers,
    type_accessibility, type_around, usings_for_move,
};
use super::sources::token_at;
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::{ReferenceKind, Resolved, Semantic};

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    if token.kind() != SyntaxKind::IdentifierToken {
        return;
    }
    let mut node = token.parent().clone();
    if node.kind() == SyntaxKind::VariableDeclarator {
        match node.ancestors().find(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
            )
        }) {
            Some(field) => node = field,
            None => return,
        }
    }
    let Some(declaration) = node.parent().cloned() else {
        return;
    };
    if !matches!(
        declaration.kind(),
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::RecordDeclaration
    ) {
        return;
    }
    let all = members_of(context, &declaration);
    let Some(member) = all.iter().find(|member| member.node == node).cloned() else {
        return;
    };
    if !is_static(context, &member) {
        return;
    }
    let Some(type_name) = declaration.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let mut name = format!("{}Helpers", type_name.value_text());
    let mut counter = 1;
    while name_is_taken(context, &declaration, &name) {
        name = format!("{}Helpers{counter}", type_name.value_text());
        counter += 1;
    }
    // The member and the private static members it uses, transitively.
    let class = context.view.declared(&declaration);
    let mut names: Vec<String> = vec![member.name.clone()];
    let mut index = 0;
    while index < names.len() {
        let current: Vec<Member> = all
            .iter()
            .filter(|one| one.name == names[index])
            .cloned()
            .collect();
        for one in current {
            for used in super::extract_base_class::used_members(
                context,
                class.unwrap_or(one.symbol),
                &one.node,
            ) {
                let symbols = context.view.compiled().symbols();
                let symbol = symbols.get(used);
                if symbol.accessibility == Accessibility::Private {
                    let Some(owner) = all.iter().find(|candidate| {
                        candidate.symbol == used
                            || symbols.get(used).container == Some(candidate.symbol)
                    }) else {
                        return;
                    };
                    if !is_static(context, owner) {
                        return;
                    }
                    if !names.contains(&owner.name) {
                        names.push(owner.name.clone());
                    }
                }
            }
        }
        index += 1;
    }
    let in_new_file = new_file_beside(context, &context.path.clone(), &name).is_some();
    if let Ok(edit) = move_members(context, &declaration, &name, &names, in_new_file) {
        found.push(CodeAction {
            title: "Move static members to another type...".to_string(),
            kind: ActionKind::Refactor,
            fixes: None,
            edit,
        });
    }
}

pub(super) fn is_static(context: &Context<'_, '_>, member: &Member) -> bool {
    let symbols = context.view.compiled().symbols();
    let modifiers = symbols.get(member.symbol).modifiers;
    modifiers.contains(Modifiers::STATIC) || modifiers.contains(Modifiers::CONST)
}

impl Semantic {
    /// Moves the static members called `members` of the type at `offset`
    /// of `path` to the type called `destination`: one the project
    /// declares, or a new static class — in a new file beside this one, or
    /// above the type in this file.
    ///
    /// # Errors
    ///
    /// Why it cannot: a member that is not static, a destination that is
    /// not a type of the project, a moved member that uses a private one
    /// staying behind.
    pub fn move_static_members(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        destination: &str,
        members: &[String],
        in_new_file: bool,
    ) -> Result<WorkspaceEdit, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a type.".to_string())?;
            move_members(context, &declaration, destination, members, in_new_file)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

/// Where the members go.
enum Destination {
    /// A type the project declares.
    Existing(SymbolId),
    /// A new static class, in a file of its own or not.
    New { in_new_file: bool },
}

fn move_members(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    destination_name: &str,
    names: &[String],
    in_new_file: bool,
) -> Result<WorkspaceEdit, String> {
    let class = context
        .view
        .declared(declaration)
        .ok_or_else(|| "The type is not in the compilation.".to_string())?;
    let source_name = context.view.compiled().symbols().get(class).name.clone();
    let destination = match find_type(context, declaration, destination_name) {
        Some(symbol) if symbol == class => {
            return Err("The members are in that type already.".to_string());
        }
        Some(symbol) => Destination::Existing(symbol),
        None => {
            if !is_identifier(destination_name) {
                return Err(format!("'{destination_name}' is not a valid name."));
            }
            Destination::New { in_new_file }
        }
    };
    let simple_destination = destination_name
        .rsplit('.')
        .next()
        .unwrap_or(destination_name)
        .to_string();
    let all = members_of(context, declaration);
    let chosen = super::members::chosen(&all, names)?;
    let chosen: Vec<Member> = chosen.into_iter().cloned().collect();
    for member in &chosen {
        if !is_static(context, member) {
            return Err(format!("'{}' is not static.", member.name));
        }
    }
    let moving_nodes: Vec<SyntaxNode> = chosen.iter().map(|member| member.node.clone()).collect();
    let inside_moved = |span: TextSpan| {
        moving_nodes
            .iter()
            .any(|node| node.span().contains(span.start()))
    };
    // Every symbol that moves: fields declare one per variable.
    let mut moving: HashSet<SymbolId> = HashSet::new();
    let mut name_tokens: Vec<SyntaxToken> = Vec::new();
    for member in &chosen {
        moving.insert(member.symbol);
        match member.node.kind() {
            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => {
                for declarator in member
                    .node
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                {
                    if let Some(symbol) = context.view.declared(&declarator) {
                        moving.insert(symbol);
                    }
                    name_tokens.extend(declarator.child_token_of_kind(SyntaxKind::IdentifierToken));
                }
            }
            _ => name_tokens.extend(member.node.child_token_of_kind(SyntaxKind::IdentifierToken)),
        }
    }

    // Uses of what moves, everywhere.
    let semantic = context.view.project();
    let mut edit = WorkspaceEdit::default();
    let mut local_edits: Vec<TextEdit> = Vec::new();
    let mut used_from_outside: HashSet<String> = HashSet::new();
    for token in &name_tokens {
        let Some((_, references)) =
            semantic.references_detailed(&context.path, token.span().start(), Some(&context.text))
        else {
            continue;
        };
        for reference in references {
            if reference.kind == ReferenceKind::Definition {
                continue;
            }
            let Some(use_token) = token_at(context, &reference.path, reference.span) else {
                continue;
            };
            let here = reference.path == context.path;
            if here && inside_moved(reference.span) {
                continue;
            }
            used_from_outside.insert(token.value_text().to_string());
            // `x.M()` of an extension method is found wherever the static
            // class it is in is in scope, as the new one is.
            if let Some(callee) = use_token.parent().parent().cloned()
                && callee.kind() == SyntaxKind::SimpleMemberAccessExpression
                && super::change_signature::is_reduced_call(context, &reference.path, &callee)
            {
                continue;
            }
            let replacement = qualify_use(&use_token, &source_name, &simple_destination);
            if here {
                local_edits.push(replacement);
            } else {
                edit.add(reference.path.clone(), replacement);
            }
        }
    }

    // What the moved code uses of the type that stays.
    let mut inner_edits: Vec<TextEdit> = Vec::new();
    for member in &chosen {
        let tokens: Vec<SyntaxToken> = member
            .node
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .collect();
        for token in tokens {
            let Some(Resolved::Symbol(symbol)) = context.view.resolve(&token) else {
                continue;
            };
            let symbols = context.view.compiled().symbols();
            let found = symbols.get(symbol);
            if found.container != Some(class)
                || moving.contains(&symbol)
                || !matches!(
                    found.kind,
                    SymbolKind::Method
                        | SymbolKind::Field
                        | SymbolKind::Property
                        | SymbolKind::Event
                        | SymbolKind::NamedType
                )
                || is_qualified(&token)
                || is_declaration_name(&token)
            {
                continue;
            }
            if found.accessibility == Accessibility::Private {
                return Err(format!(
                    "'{}' uses '{}', which is private and stays behind.",
                    member.name, found.name
                ));
            }
            inner_edits.push(TextEdit::insert(
                token.span().start(),
                format!("{source_name}."),
            ));
        }
    }

    // The members as the destination declares them.
    let texts: Vec<String> = chosen
        .iter()
        .map(|member| {
            let text = member_text_with(&context.text, &member.node, &inner_edits);
            let access = accessibility_text(&member.node);
            if (access.is_empty() || access == "private")
                && used_from_outside.contains(&member.name)
            {
                rewrite_modifiers(&text, &[], &[], Some("internal"))
            } else {
                text
            }
        })
        .collect();
    local_edits.extend(remove_members(&context.text, &moving_nodes));

    match destination {
        Destination::Existing(symbol) => {
            let target = declaration_of(context.view, symbol, &context.text).ok_or_else(|| {
                "The destination's declaration is not in the project.".to_string()
            })?;
            let target_path: PathBuf = target.path.clone().unwrap_or_else(|| context.path.clone());
            let insert = super::members::append_members(&target.node, &target.text, &texts)
                .ok_or_else(|| "The destination's body cannot be written.".to_string())?;
            if target_path == context.path {
                local_edits.push(insert);
            } else {
                edit.add(target_path.clone(), insert);
                let root = super::sources::root_of(context, &target_path)
                    .ok_or_else(|| "The destination's file is not in the project.".to_string())?;
                let usings =
                    usings_for_move(context, &moving_nodes, &root, &target.text, &target.node);
                edit.add_all(target_path, usings);
            }
        }
        Destination::New { in_new_file } => {
            if name_is_taken(context, declaration, destination_name) {
                return Err(format!(
                    "There is already a type called '{destination_name}'."
                ));
            }
            let body: Vec<String> = texts
                .iter()
                .map(|member| {
                    member
                        .split('\n')
                        .map(|line| {
                            if line.is_empty() {
                                String::new()
                            } else {
                                format!("    {line}")
                            }
                        })
                        .collect::<Vec<_>>()
                        .join("\n")
                })
                .collect();
            let class_text = format!(
                "{}static class {destination_name}\n{{\n{}\n}}",
                type_accessibility(declaration),
                body.join("\n\n")
            );
            if in_new_file {
                let target = new_file_beside(context, &context.path.clone(), destination_name)
                    .ok_or_else(|| {
                        format!("There is already a file called {destination_name}.cs.")
                    })?;
                let root = context.view.syntax_root().clone();
                let usings = needed_usings(context, &root, &moving_nodes);
                edit.add(
                    target,
                    TextEdit::insert(
                        0,
                        new_file(&context.text, declaration, &usings, &class_text),
                    ),
                );
            } else {
                local_edits.push(insert_type_before(&context.text, declaration, &class_text));
            }
        }
    }
    edit.add_all(context.path.clone(), local_edits);
    Ok(edit)
}

/// The type the project declares with the name `name` (simple or
/// qualified), looked up from the namespaces around `declaration`.
fn find_type(context: &Context<'_, '_>, declaration: &SyntaxNode, name: &str) -> Option<SymbolId> {
    let semantic = context.view.project();
    let symbols = semantic.compilation.symbols();
    let own = context.view.declared(declaration)?;
    let namespace = {
        let mut current = symbols.get(own).container;
        while let Some(id) = current {
            if symbols.get(id).kind == SymbolKind::Namespace {
                break;
            }
            current = symbols.get(id).container;
        }
        current
    };
    let candidates: Vec<SymbolId> = symbols
        .iter()
        .filter(|symbol| {
            symbol.kind == SymbolKind::NamedType
                && !symbol.locations.is_empty()
                && !semantic.compilation.is_from_metadata(symbol.id)
                && (symbols.qualified_name(symbol.id) == name || symbol.name == name)
        })
        .map(|symbol| symbol.id)
        .collect();
    candidates
        .iter()
        .copied()
        .find(|&candidate| symbols.get(candidate).container == namespace)
        .or_else(|| candidates.first().copied())
}

/// Whether `token` is the name on the right of `x.Name`.
fn is_qualified(token: &SyntaxToken) -> bool {
    let name = token.parent();
    name.parent().is_some_and(|parent| {
        matches!(
            parent.kind(),
            SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::QualifiedName
                | SyntaxKind::MemberBindingExpression
        ) && parent.children().last().as_ref() == Some(name)
    })
}

/// Whether `token` is the name a declaration declares.
fn is_declaration_name(token: &SyntaxToken) -> bool {
    !matches!(
        token.parent().kind(),
        SyntaxKind::IdentifierName | SyntaxKind::GenericName
    )
}

/// The edit that makes a use of a moved member name the destination:
/// the type in front of it replaced, or the destination put in front.
fn qualify_use(token: &SyntaxToken, source: &str, destination: &str) -> TextEdit {
    let name = token.parent();
    if let Some(parent) = name.parent()
        && matches!(
            parent.kind(),
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName
        )
        && parent.children().last().as_ref() == Some(name)
        && let Some(left) = parent.children().next()
    {
        // `Ns.Type.M`: the last part names the type.
        let target = match left.kind() {
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName => {
                left.children().last().unwrap_or(left.clone())
            }
            _ => left,
        };
        if target.text().trim() == source {
            return TextEdit::new(target.span(), destination);
        }
        return TextEdit::new(target.span(), destination);
    }
    TextEdit::insert(token.span().start(), format!("{destination}."))
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
    fn a_static_member_and_its_helpers_move_to_a_new_type() {
        let source = "namespace Geometry\n{\n    public class Circle\n    {\n        public double Radius;\n\n        public double Area() => Square(Radius) * Pi;\n\n        public static double $$Square(double x) => Scale(x) * x;\n\n        private static double Scale(double x) => x;\n\n        public const double Pi = 3.14;\n    }\n}\n";
        let other = "namespace Geometry\n{\n    class Use\n    {\n        double M() => Circle.Square(2);\n    }\n}\n";
        let changed = apply_in(
            &[("Circle.cs", source), ("Use.cs", other)],
            "Move static members to another type...",
        );
        assert_eq!(
            file(&changed, "/p/CircleHelpers.cs"),
            "namespace Geometry\n{\n    public static class CircleHelpers\n    {\n        public static double Square(double x) => Scale(x) * x;\n\n        private static double Scale(double x) => x;\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/Circle.cs"),
            "namespace Geometry\n{\n    public class Circle\n    {\n        public double Radius;\n\n        public double Area() => CircleHelpers.Square(Radius) * Pi;\n\n        public const double Pi = 3.14;\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/Use.cs"),
            "namespace Geometry\n{\n    class Use\n    {\n        double M() => CircleHelpers.Square(2);\n    }\n}\n"
        );
    }

    #[test]
    fn members_move_to_an_existing_type_and_name_what_stays() {
        let text = "class Config\n{\n    public static int Limit = 10;\n    public static int Twice() => Limit * 2;\n    static int Hidden() => 1;\n}\n\nstatic class Settings\n{\n}\n\nclass User\n{\n    int M() => Config.Twice() + Config.Limit;\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let at = text.find("Config").unwrap() as u32;
        let edit = semantic
            .move_static_members(
                Path::new("/p/A.cs"),
                at,
                None,
                "Settings",
                &["Twice".to_string()],
                false,
            )
            .expect("moved");
        assert_eq!(
            crate::edit::apply(text, edit.edits_of(Path::new("/p/A.cs"))),
            "class Config\n{\n    public static int Limit = 10;\n    static int Hidden() => 1;\n}\n\nstatic class Settings\n{\n    public static int Twice() => Config.Limit * 2;\n}\n\nclass User\n{\n    int M() => Settings.Twice() + Config.Limit;\n}\n"
        );
        let refused = semantic
            .move_static_members(
                Path::new("/p/A.cs"),
                at,
                None,
                "Settings",
                &[
                    "Limit".to_string(),
                    "Hidden".to_string(),
                    "Twice".to_string(),
                ],
                false,
            )
            .map(|_| ())
            .err();
        assert!(refused.is_none());
        refuses(
            "class C\n{\n    public int $$M() => 1;\n}\n",
            "Move static members to another type...",
        );
    }
}
