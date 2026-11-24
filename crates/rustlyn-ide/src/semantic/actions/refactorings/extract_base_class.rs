//! Extract base class: a new class between a class and its base, holding
//! members moved out of it.
//!
//! Roslyn's `ExtractClass` service in its base-class form, which Visual
//! Studio drives through a dialog choosing the new class's name, its
//! members, which of them stay behind as overrides of new abstract members,
//! and whether it goes in a file of its own. [`Semantic::extract_base_class`]
//! takes those choices. The light bulb's "Extract base class..." makes a
//! choice that always compiles: `Base` after the class's name, holding its
//! public instance members and the private ones they use, in a new file.
//!
//! * A member moved is cut from the class and pasted into the new one. A
//!   private member that the class still uses becomes `protected`.
//! * A member made abstract stays, with `override`; the new class declares
//!   it `abstract`, and is then abstract itself.
//! * The new class derives from what the class derived from, and the class
//!   from it.
//!
//! A member that uses one staying behind cannot move: the new class would
//! not see it. Neither can one the class's constructors pass arguments to
//! the old base for, since the new class has no constructor to pass them on.

use std::collections::HashSet;
use std::path::Path;

use rustlyn_semantics::{Modifiers, SymbolId, SymbolKind, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::is_identifier;
use super::super::{ActionKind, CodeAction, Context};
use super::extract_interface::signature_nodes;
use super::members::{
    Member, accessibility_text, add_base, has_modifier, insert_type_before, member_text,
    members_of, name_is_taken, needed_usings, new_file, new_file_beside, protected_if_private,
    remove_members, signature, type_accessibility, type_around, type_named_at_cursor,
};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::Semantic;

/// A member the dialog chose, and whether it stays behind as an override
/// of a new abstract member instead of moving.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExtractedMember {
    pub name: String,
    pub make_abstract: bool,
}

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(declaration) = type_named_at_cursor(context) else {
        return;
    };
    if declaration.kind() != SyntaxKind::ClassDeclaration
        || has_modifier(&declaration, SyntaxKind::StaticKeyword)
    {
        return;
    }
    let Some(type_name) = declaration.child_token_of_kind(SyntaxKind::IdentifierToken) else {
        return;
    };
    let all = members_of(context, &declaration);
    let symbols = context.view.compiled().symbols();
    let public: Vec<&Member> = all
        .iter()
        .filter(|member| {
            let symbol = symbols.get(member.symbol);
            symbol.accessibility == rustlyn_semantics::Accessibility::Public
                && !symbol.modifiers.contains(Modifiers::STATIC)
                && !symbol.modifiers.contains(Modifiers::ABSTRACT)
                && member.node.kind() != SyntaxKind::FieldDeclaration
        })
        .collect();
    let Some(names) = with_dependencies(context, &declaration, &all, &public) else {
        return;
    };
    if names.is_empty() {
        return;
    }
    let mut name = format!("{}Base", type_name.value_text());
    let mut counter = 1;
    while name_is_taken(context, &declaration, &name) {
        name = format!("{}Base{counter}", type_name.value_text());
        counter += 1;
    }
    let chosen: Vec<ExtractedMember> = names
        .into_iter()
        .map(|name| ExtractedMember {
            name,
            make_abstract: false,
        })
        .collect();
    let in_new_file = new_file_beside(context, &context.path.clone(), &name).is_some();
    if let Ok(edit) = extract(context, &declaration, &name, &chosen, in_new_file) {
        found.push(CodeAction {
            title: "Extract base class...".to_string(),
            kind: ActionKind::Extract,
            fixes: None,
            edit,
        });
    }
}

/// The names of `start` and of the members of the class they use,
/// transitively; `None` when one of them uses something that cannot move.
fn with_dependencies(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    all: &[Member],
    start: &[&Member],
) -> Option<Vec<String>> {
    let class = context.view.declared(declaration)?;
    let mut chosen: Vec<SymbolId> = start.iter().map(|member| member.symbol).collect();
    let mut index = 0;
    while index < chosen.len() {
        let member = all
            .iter()
            .find(|member| member.symbol == chosen[index])?
            .clone();
        for used in used_members(context, class, &member.node) {
            let owner = owner_of(all, context, used)?;
            if !chosen.contains(&owner.symbol) {
                chosen.push(owner.symbol);
            }
        }
        index += 1;
    }
    let mut names: Vec<String> = Vec::new();
    for member in all {
        if chosen.contains(&member.symbol) && !names.contains(&member.name) {
            names.push(member.name.clone());
        }
    }
    Some(names)
}

/// The member of `all` that declares `symbol`, or whose accessor it is.
fn owner_of<'m>(
    all: &'m [Member],
    context: &Context<'_, '_>,
    symbol: SymbolId,
) -> Option<&'m Member> {
    let symbols = context.view.compiled().symbols();
    all.iter().find(|member| {
        member.symbol == symbol
            || member
                .node
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                .any(|declarator| context.view.declared(&declarator) == Some(symbol))
            || symbols.get(symbol).container == Some(member.symbol)
    })
}

/// The members of `class` (other than `node` itself) that `node` names.
pub(super) fn used_members(
    context: &mut Context<'_, '_>,
    class: SymbolId,
    node: &SyntaxNode,
) -> Vec<SymbolId> {
    let own = context.view.declared(node);
    let mut found = Vec::new();
    let tokens: Vec<_> = node
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .collect();
    for token in tokens {
        let Some(crate::semantic::Resolved::Symbol(symbol)) = context.view.resolve(&token) else {
            continue;
        };
        let symbols = context.view.compiled().symbols();
        let found_symbol = symbols.get(symbol);
        // An accessor is its property's.
        let symbol = match found_symbol.kind {
            SymbolKind::Method | SymbolKind::Field | SymbolKind::Property | SymbolKind::Event => {
                symbol
            }
            _ => continue,
        };
        if symbols.get(symbol).container == Some(class)
            && Some(symbol) != own
            && !found.contains(&symbol)
        {
            found.push(symbol);
        }
    }
    found
}

impl Semantic {
    /// Extracts a base class called `name` from the class at `offset` of
    /// `path`, moving the members in `members` into it — or, for those
    /// marked, declaring them abstract there and overriding them where
    /// they are — into a new file beside it or above the class.
    ///
    /// # Errors
    ///
    /// Why it cannot: not a class, a name that is taken, a member that
    /// uses one staying behind.
    pub fn extract_base_class(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        name: &str,
        members: &[ExtractedMember],
        in_new_file: bool,
    ) -> Result<WorkspaceEdit, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a class.".to_string())?;
            extract(context, &declaration, name, members, in_new_file)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

fn extract(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    name: &str,
    chosen: &[ExtractedMember],
    in_new_file: bool,
) -> Result<WorkspaceEdit, String> {
    if declaration.kind() != SyntaxKind::ClassDeclaration
        || has_modifier(declaration, SyntaxKind::StaticKeyword)
    {
        return Err("Only a class that is not static can have a base class extracted.".to_string());
    }
    if !is_identifier(name) {
        return Err(format!("'{name}' is not a valid name."));
    }
    if name_is_taken(context, declaration, name) {
        return Err(format!("There is already a type called '{name}'."));
    }
    let old_base = base_class_syntax(context, declaration);
    if old_base.is_some() && passes_to_base(declaration) {
        return Err(
            "The class's constructors pass arguments to its base, which the new class could not pass on."
                .to_string(),
        );
    }
    let moved = move_to_class(context, declaration, chosen)?;

    // The type parameters of the class the moved code uses.
    let used: HashSet<String> = moved
        .used_nodes
        .iter()
        .flat_map(|node| node.descendant_tokens().collect::<Vec<_>>())
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
        .collect();
    let type_parameters: Vec<String> = declaration
        .child_of_kind(SyntaxKind::TypeParameterList)
        .map(|list| {
            list.descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
                .filter(|parameter| used.contains(parameter))
                .collect()
        })
        .unwrap_or_default();
    let generic = if type_parameters.is_empty() {
        String::new()
    } else {
        format!("<{}>", type_parameters.join(", "))
    };
    // The constraints of those type parameters come along.
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
        .map(|clause| format!(" {}", clause.text()))
        .collect();
    let base_clause = old_base
        .as_ref()
        .map(|base| format!(" : {}", base.text()))
        .unwrap_or_default();
    let base_clause = format!("{base_clause}{}", constraints.concat());
    let abstract_word = if moved.any_abstract { "abstract " } else { "" };
    let body: Vec<String> = moved
        .texts
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
    let class = format!(
        "{}{abstract_word}class {name}{generic}{base_clause}\n{{\n{}\n}}",
        type_accessibility(declaration),
        body.join("\n\n")
    );

    let mut edit = WorkspaceEdit::default();
    let reference = format!("{name}{generic}");
    let base_edit = match &old_base {
        Some(base) => TextEdit::new(base.span(), reference),
        None => add_base(declaration, &reference, true)
            .ok_or_else(|| "The class's base list cannot be written.".to_string())?,
    };
    edit.add(context.path.clone(), base_edit);
    edit.add_all(context.path.clone(), moved.edits);
    if in_new_file {
        let target = new_file_beside(context, &context.path.clone(), name)
            .ok_or_else(|| format!("There is already a file called {name}.cs."))?;
        let mut nodes = moved.used_nodes.clone();
        nodes.extend(old_base.iter().cloned());
        let root = context.view.syntax_root().clone();
        let usings = needed_usings(context, &root, &nodes);
        edit.add(
            target,
            TextEdit::insert(0, new_file(&context.text, declaration, &usings, &class)),
        );
    } else {
        edit.add(
            context.path.clone(),
            insert_type_before(&context.text, declaration, &class),
        );
    }
    Ok(edit)
}

/// The class's base class as its base list writes it.
pub(super) fn base_class_syntax(
    context: &Context<'_, '_>,
    declaration: &SyntaxNode,
) -> Option<SyntaxNode> {
    let first = declaration
        .child_of_kind(SyntaxKind::BaseList)?
        .children()
        .find(|child| child.kind() == SyntaxKind::SimpleBaseType)?;
    let ty = first.children().find(|child| child.kind().is_type_node())?;
    let resolved = context.view.model.type_of_syntax(&ty);
    let symbol = resolved.symbol()?;
    let kind = context.view.compiled().symbols().get(symbol).type_kind();
    matches!(kind, Some(TypeKind::Class | TypeKind::Record)).then_some(ty)
}

/// Whether a constructor of the class passes arguments to its base.
fn passes_to_base(declaration: &SyntaxNode) -> bool {
    declaration.children().any(|member| {
        member
            .child_of_kind(SyntaxKind::BaseConstructorInitializer)
            .and_then(|initializer| initializer.child_of_kind(SyntaxKind::ArgumentList))
            .is_some_and(|list| {
                list.children()
                    .any(|child| child.kind() == SyntaxKind::Argument)
            })
    })
}

/// Members lifted out of a class for a class above it.
pub(super) struct Moved {
    /// Each member as the class above declares it, unindented.
    pub texts: Vec<String>,
    /// The edits to the class they leave: removals, and `override` on
    /// those that stay behind.
    pub edits: Vec<TextEdit>,
    /// The code that moved, or the signatures that did: what the new
    /// declarations need `using`s and type parameters for.
    pub used_nodes: Vec<SyntaxNode>,
    pub any_abstract: bool,
}

/// Works out moving `chosen` members of the class `declaration` to a class
/// above it.
pub(super) fn move_to_class(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    chosen: &[ExtractedMember],
) -> Result<Moved, String> {
    let class = context
        .view
        .declared(declaration)
        .ok_or_else(|| "The class is not in the compilation.".to_string())?;
    let all = members_of(context, declaration);
    for member in chosen {
        if !all.iter().any(|candidate| candidate.name == member.name) {
            return Err(format!("There is no member '{}' to move.", member.name));
        }
    }
    if chosen.is_empty() {
        return Err("Choose at least one member.".to_string());
    }
    let moving: HashSet<SymbolId> = all
        .iter()
        .filter(|member| {
            chosen
                .iter()
                .any(|one| one.name == member.name && !one.make_abstract)
        })
        .map(|member| member.symbol)
        .collect();
    let mut removed: Vec<SyntaxNode> = Vec::new();
    let mut moved = Moved {
        texts: Vec::new(),
        edits: Vec::new(),
        used_nodes: Vec::new(),
        any_abstract: false,
    };
    // What stays in the class, to see which moved private members it
    // still needs.
    let staying_words: HashSet<String> = all
        .iter()
        .filter(|member| !moving.contains(&member.symbol))
        .map(|member| member.node.clone())
        .chain(declaration.children().filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::ConstructorDeclaration | SyntaxKind::DestructorDeclaration
            )
        }))
        .flat_map(|node| node.descendant_tokens().collect::<Vec<_>>())
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
        .collect();
    for member in &all {
        let Some(choice) = chosen.iter().find(|one| one.name == member.name) else {
            continue;
        };
        if choice.make_abstract {
            let symbols = context.view.compiled().symbols();
            let symbol = symbols.get(member.symbol);
            if symbol.modifiers.contains(Modifiers::STATIC)
                || !matches!(
                    member.node.kind(),
                    SyntaxKind::MethodDeclaration
                        | SyntaxKind::PropertyDeclaration
                        | SyntaxKind::IndexerDeclaration
                        | SyntaxKind::EventDeclaration
                        | SyntaxKind::EventFieldDeclaration
                )
            {
                return Err(format!("'{}' cannot be made abstract.", member.name));
            }
            let access = accessibility_text(&member.node);
            if access.is_empty() || access == "private" {
                return Err(format!(
                    "'{}' is private, and cannot be made abstract.",
                    member.name
                ));
            }
            let signature = signature(&member.node)
                .ok_or_else(|| format!("'{}' cannot be made abstract.", member.name))?;
            let end = if matches!(
                member.node.kind(),
                SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration
            ) {
                ""
            } else {
                ";"
            };
            moved
                .texts
                .push(format!("{access} abstract {signature}{end}"));
            moved.used_nodes.extend(signature_nodes(&member.node));
            moved.edits.extend(add_override(&member.node));
            moved.any_abstract = true;
            continue;
        }
        for used in used_members(context, class, &member.node) {
            let symbols = context.view.compiled().symbols();
            let owner = all.iter().find(|candidate| {
                candidate.symbol == used || symbols.get(used).container == Some(candidate.symbol)
            });
            let moves = owner.is_some_and(|owner| moving.contains(&owner.symbol))
                || all.iter().any(|candidate| {
                    moving.contains(&candidate.symbol)
                        && candidate
                            .node
                            .descendants()
                            .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                            .any(|declarator| context.view.declared(&declarator) == Some(used))
                });
            if !moves {
                return Err(format!(
                    "'{}' uses '{}', which stays behind.",
                    member.name,
                    symbols.get(used).name
                ));
            }
        }
        let mut text = member_text(&context.text, &member.node);
        if staying_words.contains(&member.name) {
            text = protected_if_private(&text, &member.node);
        }
        moved.texts.push(text);
        moved.used_nodes.push(member.node.clone());
        removed.push(member.node.clone());
    }
    moved.edits.extend(remove_members(&context.text, &removed));
    Ok(moved)
}

/// The edits that make a member an override: `virtual` goes, `override`
/// comes after its accessibility.
pub(super) fn add_override(node: &SyntaxNode) -> Vec<TextEdit> {
    let mut edits = Vec::new();
    if let Some(virtual_keyword) = node
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::VirtualKeyword)
    {
        return vec![TextEdit::new(virtual_keyword.span(), "override")];
    }
    let after = node
        .child_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::PublicKeyword
                    | SyntaxKind::ProtectedKeyword
                    | SyntaxKind::InternalKeyword
                    | SyntaxKind::PrivateKeyword
            )
        })
        .last();
    match after {
        Some(token) => edits.push(TextEdit::insert(token.span().end(), " override")),
        None => {
            // Before the first modifier or the type, past any attributes.
            if let Some(first) = node
                .children_with_tokens()
                .find(|element| element.kind() != SyntaxKind::AttributeList)
            {
                edits.push(TextEdit::insert(first.span().start(), "override "));
            }
        }
    }
    edits
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::support::{apply_in, refuses};
    use super::ExtractedMember;
    use crate::semantic::tests::compile;

    fn file<'a>(files: &'a [(PathBuf, String)], name: &str) -> &'a str {
        &files
            .iter()
            .find(|(path, _)| path == Path::new(name))
            .expect("the file")
            .1
    }

    #[test]
    fn the_light_bulb_moves_public_members_and_what_they_use() {
        let source = "using System.Collections.Generic;\n\nnamespace Game\n{\n    public class $$Player : Entity\n    {\n        private int score;\n        private readonly List<int> history = new List<int>();\n\n        public Player()\n        {\n            score = 1;\n        }\n\n        /// <summary>Adds points.</summary>\n        public void Add(int points)\n        {\n            score += points;\n            history.Add(points);\n        }\n\n        public int Score => score;\n    }\n\n    public class Entity { }\n}\n";
        let changed = apply_in(&[("Player.cs", source)], "Extract base class...");
        assert_eq!(
            file(&changed, "/p/PlayerBase.cs"),
            "using System.Collections.Generic;\n\nnamespace Game\n{\n    public class PlayerBase : Entity\n    {\n        protected int score;\n\n        private readonly List<int> history = new List<int>();\n\n        /// <summary>Adds points.</summary>\n        public void Add(int points)\n        {\n            score += points;\n            history.Add(points);\n        }\n\n        public int Score => score;\n    }\n}\n"
        );
        assert_eq!(
            file(&changed, "/p/Player.cs"),
            "using System.Collections.Generic;\n\nnamespace Game\n{\n    public class Player : PlayerBase\n    {\n        public Player()\n        {\n            score = 1;\n        }\n    }\n\n    public class Entity { }\n}\n"
        );
    }

    #[test]
    fn a_member_made_abstract_stays_as_an_override() {
        let text = "class Report\n{\n    public virtual string Title() => \"r\";\n    public int Pages { get; set; }\n    void Print() { }\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let edit = semantic
            .extract_base_class(
                Path::new("/p/A.cs"),
                text.find("Report").unwrap() as u32,
                None,
                "Document",
                &[
                    ExtractedMember {
                        name: "Title".into(),
                        make_abstract: true,
                    },
                    ExtractedMember {
                        name: "Pages".into(),
                        make_abstract: false,
                    },
                ],
                false,
            )
            .expect("extracted");
        assert_eq!(
            crate::edit::apply(text, edit.edits_of(Path::new("/p/A.cs"))),
            "abstract class Document\n{\n    public abstract string Title();\n\n    public int Pages { get; set; }\n}\n\nclass Report : Document\n{\n    public override string Title() => \"r\";\n    void Print() { }\n}\n"
        );
        let refused = semantic
            .extract_base_class(
                Path::new("/p/A.cs"),
                text.find("Report").unwrap() as u32,
                None,
                "Document",
                &[ExtractedMember {
                    name: "Print".into(),
                    make_abstract: true,
                }],
                false,
            )
            .expect_err("private");
        assert!(refused.contains("private"));
    }

    #[test]
    fn a_member_using_one_left_behind_does_not_move() {
        let text = "class Counter\n{\n    int count;\n    public void Tick() { count++; }\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let refused = semantic
            .extract_base_class(
                Path::new("/p/A.cs"),
                text.find("Counter").unwrap() as u32,
                None,
                "CounterBase",
                &[ExtractedMember {
                    name: "Tick".into(),
                    make_abstract: false,
                }],
                false,
            )
            .expect_err("uses count");
        assert!(refused.contains("'count'"));
        refuses(
            "struct $$S { public void M() { } }\n",
            "Extract base class...",
        );
    }
}
