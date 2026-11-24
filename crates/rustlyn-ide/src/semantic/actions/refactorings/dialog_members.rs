//! What the refactoring dialogs list before anything is chosen: the
//! members of the type, which of them start ticked, the name the dialog
//! suggests for what it makes, and — for pull members up — where the
//! members can go.
//!
//! Each list is the one Visual Studio's dialog shows, and its defaults are
//! the choices the light bulb's entry for the same refactoring makes.

use std::path::Path;

use rustlyn_semantics::Modifiers;
use rustlyn_syntax::SyntaxKind;
use rustlyn_text::TextSpan;

use super::members::{is_public_instance, members_of, name_is_taken, signature, type_around};
use crate::semantic::Semantic;

/// Which dialog is asking.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum DialogKind {
    ExtractInterface = 0,
    ExtractBaseClass,
    PullMembersUp,
    GenerateOverrides,
    MoveStaticMembers,
}

impl DialogKind {
    /// The kind with the discriminant `value`.
    #[must_use]
    pub fn from_u32(value: u32) -> Option<Self> {
        Some(match value {
            0 => Self::ExtractInterface,
            1 => Self::ExtractBaseClass,
            2 => Self::PullMembersUp,
            3 => Self::GenerateOverrides,
            4 => Self::MoveStaticMembers,
            _ => return None,
        })
    }
}

/// One line of a dialog's member list.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DialogMember {
    /// What the refactoring is told to choose it: its name, or for
    /// overrides the member as listed.
    pub name: String,
    /// The member as the list shows it: its signature.
    pub display: String,
    /// Whether it starts ticked.
    pub selected: bool,
}

/// A dialog's lists.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DialogMembers {
    /// The type the dialog is about.
    pub type_name: String,
    /// The name suggested for the new type, when the dialog makes one.
    pub suggested_name: String,
    pub members: Vec<DialogMember>,
    /// Where the members can go: the base types, for pull members up.
    pub destinations: Vec<String>,
}

impl Semantic {
    /// The lists the dialog of `kind` shows for the type at `offset` of
    /// `path`, and its defaults. The member at the cursor, if there is one,
    /// starts ticked for pull members up and move static members.
    ///
    /// # Errors
    ///
    /// When there is no type there.
    pub fn dialog_members(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        kind: DialogKind,
    ) -> Result<DialogMembers, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a type.".to_string())?;
            let type_name = declaration
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
                .unwrap_or_default();
            let suggest = |context: &super::super::Context<'_, '_>, prefix: &str, suffix: &str| {
                let mut name = format!("{prefix}{type_name}{suffix}");
                let mut counter = 1;
                while name_is_taken(context, &declaration, &name) {
                    name = format!("{prefix}{type_name}{suffix}{counter}");
                    counter += 1;
                }
                name
            };
            let all = members_of(context, &declaration);
            // The member whose declaration the cursor is in.
            let at_cursor = all
                .iter()
                .find(|member| member.node.span().contains(offset))
                .map(|member| member.name.clone());
            let display = |member: &super::members::Member| {
                signature(&member.node).unwrap_or_else(|| member.name.clone())
            };
            let mut out = DialogMembers {
                type_name: type_name.clone(),
                ..DialogMembers::default()
            };
            match kind {
                DialogKind::ExtractInterface => {
                    out.suggested_name = suggest(context, "I", "");
                    for member in &all {
                        if is_public_instance(context, member) && signature(&member.node).is_some()
                        {
                            out.members.push(DialogMember {
                                name: member.name.clone(),
                                display: display(member),
                                selected: true,
                            });
                        }
                    }
                }
                DialogKind::ExtractBaseClass | DialogKind::PullMembersUp => {
                    if kind == DialogKind::ExtractBaseClass {
                        out.suggested_name = suggest(context, "", "Base");
                    } else {
                        let symbols = context.view.compiled().symbols();
                        out.destinations =
                            super::pull_members_up::destinations(context, &declaration)
                                .into_iter()
                                .map(|symbol| symbols.get(symbol).name.clone())
                                .collect();
                    }
                    for member in &all {
                        if kind == DialogKind::PullMembersUp
                            && member
                                .node
                                .child_token_of_kind(SyntaxKind::OverrideKeyword)
                                .is_some()
                        {
                            continue;
                        }
                        let selected = if kind == DialogKind::PullMembersUp {
                            at_cursor.as_deref() == Some(member.name.as_str())
                        } else {
                            is_public_instance(context, member)
                        };
                        out.members.push(DialogMember {
                            name: member.name.clone(),
                            display: display(member),
                            selected,
                        });
                    }
                }
                DialogKind::GenerateOverrides => {
                    let found = super::generate_overrides::overridable(context.view, &declaration);
                    for (member, map) in &found {
                        let shown = super::generate_overrides::display(
                            context.view,
                            &declaration,
                            *member,
                            map,
                        );
                        out.members.push(DialogMember {
                            name: shown.clone(),
                            display: shown,
                            selected: true,
                        });
                    }
                }
                DialogKind::MoveStaticMembers => {
                    out.suggested_name = suggest(context, "", "Helpers");
                    for member in &all {
                        let symbols = context.view.compiled().symbols();
                        let modifiers = symbols.get(member.symbol).modifiers;
                        if !(modifiers.contains(Modifiers::STATIC)
                            || modifiers.contains(Modifiers::CONST))
                        {
                            continue;
                        }
                        out.members.push(DialogMember {
                            name: member.name.clone(),
                            display: display(member),
                            selected: at_cursor.as_deref() == Some(member.name.as_str()),
                        });
                    }
                }
            }
            Ok(out)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::DialogKind;
    use crate::semantic::tests::compile;

    #[test]
    fn each_dialog_lists_its_members_and_defaults() {
        let text = "class Base { public virtual int Size() => 0; }\ninterface IThing { }\nclass Crate : Base, IThing\n{\n    public int Weight { get; set; }\n    public void Open() { }\n    static int Made;\n    public static int Count() => Made;\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let path = Path::new("/p/A.cs");
        let ask = |kind, at: &str| {
            semantic
                .dialog_members(path, text.find(at).unwrap() as u32, None, kind)
                .expect("listed")
        };
        let interface = ask(DialogKind::ExtractInterface, "Crate");
        assert_eq!(interface.suggested_name, "ICrate");
        let names: Vec<&str> = interface
            .members
            .iter()
            .map(|member| member.display.as_str())
            .collect();
        assert_eq!(names, ["int Weight { get; set; }", "void Open()"]);
        let up = ask(DialogKind::PullMembersUp, "Open");
        assert_eq!(up.destinations, ["Base", "IThing"]);
        assert!(
            up.members
                .iter()
                .any(|member| member.name == "Open" && member.selected)
        );
        let overrides = ask(DialogKind::GenerateOverrides, "Crate");
        assert_eq!(overrides.members[0].name, "Size()");
        let statics = ask(DialogKind::MoveStaticMembers, "Count");
        assert_eq!(statics.suggested_name, "CrateHelpers");
        let listed: Vec<(&str, bool)> = statics
            .members
            .iter()
            .map(|member| (member.name.as_str(), member.selected))
            .collect();
        assert_eq!(listed, [("Made", false), ("Count", true)]);
    }
}
