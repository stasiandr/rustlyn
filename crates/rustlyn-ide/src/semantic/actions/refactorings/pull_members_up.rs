//! Pull members up: a member moved to a base class, or declared by an
//! interface the type implements.
//!
//! Roslyn's `PullMemberUp` refactoring. With the cursor on a member's name
//! the light bulb offers "Pull 'M' up to 'Base'" for each base class and
//! interface of the type that the project declares; Visual Studio's dialog
//! picks several members and one destination, and may leave members behind
//! as overrides of new abstract ones — [`Semantic::pull_members_up`].
//!
//! * To a class, a member is cut from the type and pasted into the base,
//!   with any `using` it needs added to the base's file. A private member
//!   the type still uses becomes `protected`. A member made abstract stays
//!   as an `override`, and the base becomes abstract.
//! * To an interface, the interface declares the member's signature; the
//!   member stays, and must be public.
//!
//! Not offered for a member that uses another member of the type (the base
//! would not see it), one the base already has, an override, or one whose
//! signature uses the type's own type parameters.

use std::path::{Path, PathBuf};

use rustlyn_semantics::{Modifiers, SymbolId, SymbolKind, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::fixes::support::declaration_of;
use super::super::{ActionKind, CodeAction, Context};
use super::extract_base_class::{ExtractedMember, move_to_class};
use super::extract_interface::signature_nodes;
use super::members::{Member, has_modifier, members_of, signature, type_around, usings_for_move};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::Semantic;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    if token.kind() != SyntaxKind::IdentifierToken {
        return;
    }
    let mut node = token.parent().clone();
    if node.kind() == SyntaxKind::VariableDeclarator {
        let Some(field) = node.ancestors().find(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
            )
        }) else {
            return;
        };
        node = field;
    }
    let Some(declaration) = node.parent().cloned() else {
        return;
    };
    if !super::super::text::is_type_declaration(declaration.kind())
        || declaration.kind() == SyntaxKind::InterfaceDeclaration
    {
        return;
    }
    let all = members_of(context, &declaration);
    let Some(member) = all.iter().find(|member| member.node == node).cloned() else {
        return;
    };
    if has_modifier(&member.node, SyntaxKind::OverrideKeyword) {
        return;
    }
    for destination in destinations(context, &declaration) {
        let symbols = context.view.compiled().symbols();
        let name = symbols.get(destination).name.clone();
        if symbols
            .get(destination)
            .members
            .iter()
            .any(|&other| symbols.get(other).name == member.name)
        {
            continue;
        }
        let choice = [ExtractedMember {
            name: member.name.clone(),
            make_abstract: false,
        }];
        // One member at a time: its overloads stay where they are.
        if all.iter().filter(|other| other.name == member.name).count() > 1 {
            continue;
        }
        if let Ok(edit) = pull(context, &declaration, destination, &choice) {
            found.push(CodeAction {
                title: format!("Pull '{}' up to '{name}'", member.name),
                kind: ActionKind::Refactor,
                fixes: None,
                edit,
            });
        }
    }
}

/// The base classes and interfaces of the type, the nearest first, that
/// the project declares.
pub(super) fn destinations(context: &Context<'_, '_>, declaration: &SyntaxNode) -> Vec<SymbolId> {
    let Some(class) = context.view.declared(declaration) else {
        return Vec::new();
    };
    let semantic = context.view.project();
    let mut found: Vec<SymbolId> = Vec::new();
    let mut queue = vec![class];
    while let Some(current) = queue.pop() {
        for base in context.view.base_types(current) {
            let Some(symbol) = base.symbol() else {
                continue;
            };
            if found.contains(&symbol) || symbol == class {
                continue;
            }
            found.push(symbol);
            queue.insert(0, symbol);
        }
    }
    found.retain(|&symbol| {
        !semantic.compilation.is_from_metadata(symbol)
            && !semantic
                .compilation
                .symbols()
                .get(symbol)
                .locations
                .is_empty()
    });
    found
}

impl Semantic {
    /// Pulls the members called `members` of the type at `offset` of
    /// `path` up to its base type called `destination` (as written, or
    /// qualified): moved into a base class, or declared by an interface.
    ///
    /// # Errors
    ///
    /// Why it cannot: no such base type in the project, a member that uses
    /// one staying behind, a member an interface cannot declare.
    pub fn pull_members_up(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        destination: &str,
        members: &[ExtractedMember],
    ) -> Result<WorkspaceEdit, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a type.".to_string())?;
            let symbols = context.view.compiled().symbols();
            let target = destinations(context, &declaration)
                .into_iter()
                .find(|&symbol| {
                    symbols.get(symbol).name == destination
                        || symbols.qualified_name(symbol) == destination
                })
                .ok_or_else(|| {
                    format!("'{destination}' is not a base type declared in the project.")
                })?;
            pull(context, &declaration, target, members)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

fn pull(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    destination: SymbolId,
    chosen: &[ExtractedMember],
) -> Result<WorkspaceEdit, String> {
    let all = members_of(context, declaration);
    let picked: Vec<Member> = all
        .iter()
        .filter(|member| chosen.iter().any(|one| one.name == member.name))
        .cloned()
        .collect();
    for one in chosen {
        if !picked.iter().any(|member| member.name == one.name) {
            return Err(format!("There is no member '{}' to pull up.", one.name));
        }
    }
    for member in &picked {
        if uses_own_type_parameters(&member.node) {
            return Err(format!(
                "'{}' uses the type's own type parameters, which '{}' does not have.",
                member.name,
                context.view.compiled().symbols().get(destination).name
            ));
        }
    }
    let target = declaration_of(context.view, destination, &context.text)
        .ok_or_else(|| "The destination's declaration is not in the project.".to_string())?;
    let target_path: PathBuf = target.path.clone().unwrap_or_else(|| context.path.clone());
    let target_root = super::sources::root_of(context, &target_path)
        .ok_or_else(|| "The destination's file is not in the project.".to_string())?;
    let is_interface = context
        .view
        .compiled()
        .symbols()
        .get(destination)
        .type_kind()
        == Some(TypeKind::Interface);

    let mut edit = WorkspaceEdit::default();
    let (texts, used_nodes) = if is_interface {
        // Every other type that implements the interface would have to
        // implement the member too.
        let class = context.view.declared(declaration);
        let implementors = context.view.project().derived(destination, false);
        if implementors.len() != 1 || implementors.first().copied() != class {
            return Err(format!(
                "Other types implement '{}', and would not implement the member.",
                context.view.compiled().symbols().get(destination).name
            ));
        }
        let mut texts = Vec::new();
        let mut nodes = Vec::new();
        for member in &picked {
            let symbols = context.view.compiled().symbols();
            let symbol = symbols.get(member.symbol);
            if symbol.accessibility != rustlyn_semantics::Accessibility::Public
                || symbol.modifiers.contains(Modifiers::STATIC)
                || !matches!(
                    symbol.kind,
                    SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
                )
            {
                return Err(format!(
                    "'{}' is not a public instance member, so an interface cannot declare it.",
                    member.name
                ));
            }
            let signature = signature(&member.node)
                .ok_or_else(|| format!("An interface cannot declare '{}'.", member.name))?;
            texts.push(
                if matches!(
                    member.node.kind(),
                    SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration
                ) {
                    signature
                } else {
                    format!("{signature};")
                },
            );
            nodes.extend(signature_nodes(&member.node));
        }
        (texts, nodes)
    } else {
        let moved = move_to_class(context, declaration, chosen)?;
        edit.add_all(context.path.clone(), moved.edits);
        if moved.any_abstract && !has_modifier(&target.node, SyntaxKind::AbstractKeyword) {
            let at = target
                .node
                .child_token_of_kind(SyntaxKind::ClassKeyword)
                .ok_or_else(|| "The destination is not a class.".to_string())?;
            let before = target
                .node
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::PartialKeyword | SyntaxKind::ClassKeyword
                    )
                })
                .unwrap_or(at);
            edit.add(
                target_path.clone(),
                TextEdit::insert(before.span().start(), "abstract "),
            );
        }
        (moved.texts, moved.used_nodes)
    };
    let insert = super::members::append_members(&target.node, &target.text, &texts)
        .ok_or_else(|| "The destination's body cannot be written.".to_string())?;
    edit.add(target_path.clone(), insert);
    if target_path != context.path {
        let usings = usings_for_move(
            context,
            &used_nodes,
            &target_root,
            &target.text,
            &target.node,
        );
        edit.add_all(target_path, usings);
    }
    Ok(edit)
}

/// Whether the member's signature or body names a type parameter of the
/// type it is in.
fn uses_own_type_parameters(node: &SyntaxNode) -> bool {
    let Some(ty) = node
        .ancestors()
        .find(|ancestor| super::super::text::is_type_declaration(ancestor.kind()))
    else {
        return false;
    };
    let Some(list) = ty.child_of_kind(SyntaxKind::TypeParameterList) else {
        return false;
    };
    let names: Vec<String> = list
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
        .collect();
    node.descendant_tokens().any(|token| {
        token.kind() == SyntaxKind::IdentifierToken
            && names.iter().any(|name| name == token.value_text())
    })
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::extract_base_class::ExtractedMember;
    use super::super::support::{apply_in, refuses, titles};
    use crate::semantic::tests::compile;

    fn file<'a>(files: &'a [(PathBuf, String)], name: &str) -> &'a str {
        &files
            .iter()
            .find(|(path, _)| path == Path::new(name))
            .expect("the file")
            .1
    }

    #[test]
    fn a_method_moves_to_the_base_class_in_its_own_file() {
        let dog = "using System.Collections.Generic;\n\nnamespace Zoo\n{\n    public class Dog : Animal\n    {\n        public int Legs = 4;\n\n        public List<string> $$Sounds()\n        {\n            return new List<string>();\n        }\n    }\n}\n";
        let animal = "namespace Zoo\n{\n    public class Animal\n    {\n        public string Name { get; set; }\n    }\n}\n";
        let changed = apply_in(
            &[("Dog.cs", dog), ("Animal.cs", animal)],
            "Pull 'Sounds' up to 'Animal'",
        );
        assert_eq!(
            file(&changed, "/p/Dog.cs"),
            "using System.Collections.Generic;\n\nnamespace Zoo\n{\n    public class Dog : Animal\n    {\n        public int Legs = 4;\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/Animal.cs"),
            "using System.Collections.Generic;\n\nnamespace Zoo\n{\n    public class Animal\n    {\n        public string Name { get; set; }\n\n        public List<string> Sounds()\n        {\n            return new List<string>();\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_member_is_declared_by_an_interface() {
        let source = "interface IShape\n{\n    double Area();\n}\n\nclass Square : IShape\n{\n    public double Area() => 4;\n    public double $$Perimeter() => 8;\n}\n";
        let changed = apply_in(&[("A.cs", source)], "Pull 'Perimeter' up to 'IShape'");
        assert_eq!(
            file(&changed, "/p/A.cs"),
            "interface IShape\n{\n    double Area();\n\n    double Perimeter();\n}\n\nclass Square : IShape\n{\n    public double Area() => 4;\n    public double Perimeter() => 8;\n}\n"
        );
    }

    #[test]
    fn every_base_is_offered_and_what_cannot_move_is_not() {
        let source = "interface IA { }\ninterface IB { }\nclass Base : IA { }\nclass Derived : Base, IB\n{\n    int count;\n    public void $$Tick() { count++; }\n    public void Reset() { }\n}\n";
        let offered = titles(source);
        assert!(
            !offered.contains(&"Pull 'Tick' up to 'Base'".to_string()),
            "{offered:?}"
        );
        assert!(
            offered.contains(&"Pull 'Tick' up to 'IB'".to_string()),
            "{offered:?}"
        );
        let offered = titles(
            &source
                .replace("$$Tick", "Tick")
                .replace("void Reset", "void $$Reset"),
        );
        assert!(
            offered.contains(&"Pull 'Reset' up to 'Base'".to_string()),
            "{offered:?}"
        );
        assert!(
            offered.contains(&"Pull 'Reset' up to 'IB'".to_string()),
            "{offered:?}"
        );
        // `Base` implements `IA`, and would have to implement it too.
        assert!(
            !offered.contains(&"Pull 'Reset' up to 'IA'".to_string()),
            "{offered:?}"
        );
        refuses(
            "class Base { public virtual void M() { } }\nclass D : Base { public override void $$M() { } }\n",
            "Pull 'M' up to 'Base'",
        );
    }

    #[test]
    fn the_dialog_can_leave_members_behind_as_overrides() {
        let text = "class Base\n{\n}\n\nclass Derived : Base\n{\n    int count;\n    public void Tick() { count++; }\n    public int Count => count;\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let edit = semantic
            .pull_members_up(
                Path::new("/p/A.cs"),
                text.find("Derived").unwrap() as u32,
                None,
                "Base",
                &[
                    ExtractedMember {
                        name: "Tick".into(),
                        make_abstract: true,
                    },
                    ExtractedMember {
                        name: "count".into(),
                        make_abstract: false,
                    },
                ],
            )
            .expect("pulled");
        assert_eq!(
            crate::edit::apply(text, edit.edits_of(Path::new("/p/A.cs"))),
            "abstract class Base\n{\n    protected int count;\n\n    public abstract void Tick();\n}\n\nclass Derived : Base\n{\n    public override void Tick() { count++; }\n    public int Count => count;\n}\n"
        );
    }
}
