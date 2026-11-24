//! What the thing under the cursor is.
//!
//! This is `⌘B` proper, and it sits above layer 4 because it needs both
//! halves: the parse tree of the file the cursor is in, to see what shape the
//! name is part of, and the project index, to say where that name was
//! declared.
//!
//! The shape matters more than it looks. `Position` on its own is a local, a
//! parameter, a field of the type around it or a type; `owner.Position` is a
//! member of whatever `owner` is; `Vector3.Position` is a static member of a
//! type. Those are four different lookups, and a navigator that does not read
//! the tree cannot tell which one it is being asked for — which is why one
//! that matches names alone goes to the wrong `Position`.
//!
//! A chain is walked left to right, carrying a type as it goes: `_stash` is a
//! field declared `Stash<Health>`, so `.Get` is looked up on `Stash`, and its
//! return type is what `.Get()` leaves for whatever comes next. Where a step
//! cannot be typed the walk stops and says so, rather than falling back to
//! matching the last word against the project — which is the failure that
//! looks like success.

use std::sync::Arc;

use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxTree};
use rustlyn_text::TextSpan;

use crate::index::{Confidence, Found, ProjectIndex, plain_name};
use crate::outline::DeclarationKind;

/// What was under the cursor and where it leads.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Target {
    /// The word the cursor was on.
    pub word: String,
    /// Its span in the file, in bytes.
    pub span: TextSpan,
    /// Where it goes, as entries in the index.
    pub found: Found,
}

/// Why nothing was found, which is worth telling apart in a status line.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Miss {
    /// The cursor is not on a name at all: whitespace, punctuation, a
    /// keyword, or inside a string or comment.
    NotAName,
    /// A name, but its receiver could not be typed, so looking the name up on
    /// its own would be a guess.
    ///
    /// `thing.Position` where nothing says what `thing` is. Saying this is
    /// the point: the alternative is to find some other `Position` and go
    /// there.
    ReceiverUnknown(String),
    /// A name that is nowhere in the project. Nearly always a type from an
    /// assembly, which is layer 5's business rather than this one's.
    NotInProject(String),
}

/// A local variable or parameter seen in the method around the cursor.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Local {
    name: String,
    /// The type as written, or `None` for a `var` whose initialiser could not
    /// be typed.
    type_text: Option<String>,
    /// Where it comes into scope, so a name is not resolved against a local
    /// declared below it.
    from: u32,
}

/// Resolves what is at `offset` in `tree`, for the file indexed as `file`.
///
/// # Errors
///
/// Returns why nothing was found rather than an empty answer, because "not a
/// name", "cannot type the receiver" and "not in this project" ask for
/// different things to happen next.
pub fn definition_at(
    tree: &SyntaxTree,
    offset: u32,
    index: &ProjectIndex,
    file: u32,
) -> Result<Target, Miss> {
    let root = tree.root();
    let token = root.find_token(offset).ok_or(Miss::NotAName)?;
    if token.kind() != SyntaxKind::IdentifierToken || token.is_missing() {
        return Err(Miss::NotAName);
    }
    let word = token.text().to_owned();
    let span = token.span();

    // The name node the token belongs to, and the access it is part of.
    let name_node = root.find_node(span).ok_or(Miss::NotAName)?;
    let walker = Walker { index, file, tree };

    let found = walker.resolve(&name_node, &word, offset)?;
    Ok(Target { word, span, found })
}

struct Walker<'a> {
    index: &'a ProjectIndex,
    file: u32,
    tree: &'a SyntaxTree,
}

impl Walker<'_> {
    fn resolve(&self, name_node: &SyntaxNode, word: &str, offset: u32) -> Result<Found, Miss> {
        // `a.B` — is this name the right-hand side of a member access?
        if let Some(access) = self.member_access_around(name_node)
            && let Some(receiver) = access.children().next()
            && receiver.span().end() <= name_node.span().start()
        {
            let receiver_type = self
                .type_of(&receiver, offset)
                .ok_or_else(|| Miss::ReceiverUnknown(receiver.text()))?;
            return self
                .member_or_extension(receiver_type, word)
                .ok_or_else(|| Miss::NotInProject(word.to_owned()));
        }

        // A plain name. Nearest first: a local, then the type around it, then
        // the project. That is the order C# looks, and getting it wrong sends
        // a cursor on a local called `Position` to a field somewhere else.
        if let Some(local) = self.local_named(word, offset) {
            // A local's declaration is in this file and not in the index, so
            // there is nothing to jump *to* except the type it was declared
            // as, which is the useful answer.
            if let Some(type_text) = &local.type_text
                && let Some(found) = self.index.resolve_type(plain_name(type_text), self.file)
            {
                return Ok(found);
            }
            return Err(Miss::NotInProject(word.to_owned()));
        }

        if let Some(enclosing) = self.enclosing_type(offset)
            && let Some(found) = self.member_or_extension(enclosing, word)
        {
            return Ok(found);
        }

        self.index
            .resolve_type(word, self.file)
            .or_else(|| Found::of_slice(self.index.by_name(word)))
            .ok_or_else(|| Miss::NotInProject(word.to_owned()))
    }

    /// A member of a type, or an extension method on it when it has no member
    /// of that name — which is the order C# looks in.
    fn member_or_extension(&self, type_entry: u32, name: &str) -> Option<Found> {
        self.index
            .member(type_entry, name)
            .or_else(|| self.index.extension(type_entry, name))
    }

    /// The member access an identifier is the right-hand side of.
    fn member_access_around(&self, name_node: &SyntaxNode) -> Option<SyntaxNode> {
        name_node
            .parent()
            .filter(|parent| parent.kind() == SyntaxKind::SimpleMemberAccessExpression)
            .cloned()
    }

    /// The type an expression has, as an entry in the index.
    ///
    /// Only the shapes whose type can be read off the tree and the index: a
    /// name that is a local, a field or a type, a `new T()`, a call whose
    /// method is known, and a chain of those. Anything else answers `None`,
    /// which is what makes the miss above honest.
    fn type_of(&self, expression: &SyntaxNode, offset: u32) -> Option<u32> {
        match expression.kind() {
            SyntaxKind::IdentifierName => {
                let word = expression.text();
                // A local or parameter declared above here.
                if let Some(local) = self.local_named(&word, offset) {
                    let type_text = local.type_text.as_ref()?;
                    return self
                        .index
                        .resolve_type(plain_name(type_text), self.file)?
                        .entries
                        .first()
                        .copied();
                }
                // A field or property of the type around the cursor.
                if let Some(enclosing) = self.enclosing_type(offset)
                    && let Some(found) = self.index.member(enclosing, &word)
                    && let Some(&member) = found.entries.first()
                {
                    return self.type_of_member(member);
                }
                // Otherwise the name is a type, and what follows it is static.
                self.index
                    .resolve_type(&word, self.file)?
                    .entries
                    .first()
                    .copied()
            }

            SyntaxKind::SimpleMemberAccessExpression => {
                let receiver = expression.children().next()?;
                let name = expression.children().nth(1)?;
                let receiver_type = self.type_of(&receiver, offset)?;
                let member = self
                    .member_or_extension(receiver_type, &name.text())?
                    .entries
                    .first()
                    .copied()?;
                self.type_of_member(member)
            }

            SyntaxKind::InvocationExpression => {
                // The type of a call is the return type of what it calls.
                let callee = expression.children().next()?;
                match callee.kind() {
                    SyntaxKind::SimpleMemberAccessExpression => {
                        let receiver = callee.children().next()?;
                        let name = callee.children().nth(1)?;
                        let receiver_type = self.type_of(&receiver, offset)?;
                        let method = self
                            .member_or_extension(receiver_type, &name.text())?
                            .entries
                            .first()
                            .copied()?;
                        self.type_of_member(method)
                    }
                    SyntaxKind::IdentifierName => {
                        let enclosing = self.enclosing_type(offset)?;
                        let method = self
                            .index
                            .member(enclosing, &callee.text())?
                            .entries
                            .first()
                            .copied()?;
                        self.type_of_member(method)
                    }
                    _ => None,
                }
            }

            SyntaxKind::ObjectCreationExpression => {
                // `new Foo()` is a `Foo`, which is the one case where the
                // type is written next to the value.
                let named = expression
                    .children()
                    .find(|child| child.kind().is_type_node())?;
                self.index
                    .resolve_type(plain_name(&named.text()), self.file)?
                    .entries
                    .first()
                    .copied()
            }

            SyntaxKind::ParenthesizedExpression => {
                self.type_of(&expression.children().next()?, offset)
            }

            _ => None,
        }
    }

    /// The type a member is declared as: a field's or property's own type, a
    /// method's return type.
    fn type_of_member(&self, member: u32) -> Option<u32> {
        let entry = self.index.entry(member)?;
        // A type is its own type: `Foo.Bar` where `Bar` is a nested type.
        if entry.declaration.kind.is_type() {
            return Some(member);
        }
        let type_text = entry.declaration.type_text.as_ref()?;
        self.index
            .resolve_type(plain_name(type_text), entry.file)?
            .entries
            .first()
            .copied()
    }

    /// The type declaration the cursor is inside, as an entry in the index.
    fn enclosing_type(&self, offset: u32) -> Option<u32> {
        // The outline in the index is of a saved file; the tree may be newer.
        // Taking the name from the tree and resolving it keeps the two
        // agreeing about which type is meant even when the file has moved on.
        let root = self.tree.root();
        let mut node = Some(root.find_token(offset)?.parent().clone());
        while let Some(current) = node {
            if is_type_declaration(current.kind())
                && let Some(name) = current.child_token_of_kind(SyntaxKind::IdentifierToken)
            {
                return self
                    .index
                    .resolve_type(name.text(), self.file)?
                    .entries
                    .first()
                    .copied();
            }
            node = current.parent().cloned();
        }
        None
    }

    /// The local or parameter of that name in scope at `offset`.
    ///
    /// Scope here is "declared earlier in the method around the cursor",
    /// which is what C# means for a local and is near enough for a
    /// parameter. The innermost match wins, so a local shadowing a parameter
    /// shadows it.
    fn local_named(&self, name: &str, offset: u32) -> Option<Local> {
        let root = self.tree.root();
        let from = root.find_token(offset)?.parent().clone();
        let method = std::iter::successors(Some(from), |node| node.parent().cloned())
            .find(|node| is_member_declaration(node.kind()))?;

        let mut best: Option<Local> = None;

        for parameter in method
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Parameter)
        {
            let Some(token) = parameter.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                continue;
            };
            if token.text() != name {
                continue;
            }
            best = Some(Local {
                name: name.to_owned(),
                type_text: parameter
                    .children()
                    .find(|child| child.kind().is_type_node())
                    .map(|node| node.text()),
                from: parameter.span().start(),
            });
        }

        for declaration in method
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::VariableDeclaration)
        {
            let written = declaration
                .children()
                .find(|child| child.kind().is_type_node())
                .map(|node| node.text());
            for declarator in declaration
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
            {
                let Some(token) = declarator.child_token_of_kind(SyntaxKind::IdentifierToken)
                else {
                    continue;
                };
                if token.text() != name {
                    continue;
                }
                let from = declarator.span().start();
                // A local declared below the cursor is not in scope at it.
                if from > offset {
                    continue;
                }
                let type_text = match written.as_deref() {
                    // `var` says nothing; the initialiser does.
                    Some("var") | None => declarator
                        .child_of_kind(SyntaxKind::EqualsValueClause)
                        .and_then(|clause| clause.children().next())
                        .and_then(|value| self.written_type_of(&value)),
                    Some(written) => Some(written.to_owned()),
                };
                if best.as_ref().is_none_or(|previous| previous.from <= from) {
                    best = Some(Local {
                        name: name.to_owned(),
                        type_text,
                        from,
                    });
                }
            }
        }
        best
    }

    /// The type of an initialiser, where it is written next to the value.
    ///
    /// `var x = new Foo()` is a `Foo` because the source said so. `var x =
    /// Make()` is not answered here — that needs the index, and it is
    /// [`Self::type_of`] that has it.
    fn written_type_of(&self, value: &SyntaxNode) -> Option<String> {
        match value.kind() {
            SyntaxKind::ObjectCreationExpression => value
                .children()
                .find(|child| child.kind().is_type_node())
                .map(|node| node.text()),
            SyntaxKind::CastExpression => value
                .children()
                .find(|child| child.kind().is_type_node())
                .map(|node| node.text()),
            SyntaxKind::InvocationExpression | SyntaxKind::SimpleMemberAccessExpression => {
                let entry = self.type_of(value, value.span().start())?;
                Some(self.index.entry(entry)?.declaration.qualified_name())
            }
            _ => None,
        }
    }
}

const fn is_type_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
    )
}

const fn is_member_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::GetAccessorDeclaration
            | SyntaxKind::SetAccessorDeclaration
    )
}

impl Found {
    /// A [`Found`] over ids already in hand, for a fallback that has no scope
    /// to narrow with.
    #[must_use]
    pub fn of_slice(entries: &[u32]) -> Option<Self> {
        match entries.len() {
            0 => None,
            1 => Some(Self {
                entries: vec![entries[0]],
                confidence: Confidence::Certain,
            }),
            _ => Some(Self {
                entries: entries.to_vec(),
                confidence: Confidence::Ambiguous,
            }),
        }
    }
}

/// The declaration kind an entry is, for an editor choosing an icon.
#[must_use]
pub fn kind_of(index: &ProjectIndex, entry: u32) -> Option<DeclarationKind> {
    index.entry(entry).map(|entry| entry.declaration.kind)
}

/// Parses a file the way the layers above do, for callers that only have text.
#[must_use]
pub fn parse(text: &str, name: &str) -> Arc<SyntaxTree> {
    Arc::new(rustlyn_syntax::parse(rustlyn_text::SourceText::new(
        name, text,
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::index::outline_of_text;
    use std::path::PathBuf;

    /// A project, and the file the cursor is in.
    ///
    /// The cursor is written into the source as `|`, which is taken out
    /// before anything parses it.
    struct Fixture {
        index: ProjectIndex,
        tree: Arc<SyntaxTree>,
        file: u32,
        offset: u32,
    }

    fn fixture(files: &[(&str, &str)], cursor_in: &str) -> Fixture {
        let cleaned: Vec<(String, String)> = files
            .iter()
            .map(|(name, text)| ((*name).to_owned(), text.replace('|', "")))
            .collect();
        let index = ProjectIndex::from_outlines(
            "/project",
            cleaned
                .iter()
                .map(|(name, text)| (PathBuf::from(name), outline_of_text(text))),
        );
        let file = cleaned
            .iter()
            .position(|(name, _)| name == cursor_in)
            .expect("the cursor's file should be in the project") as u32;
        let raw = files
            .iter()
            .find(|(name, _)| *name == cursor_in)
            .expect("the cursor's file")
            .1;
        let offset = raw.find('|').expect("the source should mark a cursor") as u32;
        let text = raw.replace('|', "");
        Fixture {
            index,
            tree: parse(&text, cursor_in),
            file,
            offset,
        }
    }

    impl Fixture {
        fn go(&self) -> Result<Target, Miss> {
            definition_at(&self.tree, self.offset, &self.index, self.file)
        }

        fn lands_on(&self) -> String {
            let target = self.go().expect("it should resolve");
            let entry = self.index.entry(target.found.entries[0]).expect("an entry");
            entry.declaration.qualified_name()
        }
    }

    #[test]
    fn a_type_name_goes_to_the_type() {
        let f = fixture(
            &[
                ("Pawn.cs", "namespace Game; class Pawn { }"),
                ("Use.cs", "namespace Game; class Use { P|awn p; }"),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Pawn");
    }

    #[test]
    fn a_member_on_a_parameter_goes_to_that_types_member() {
        let f = fixture(
            &[
                (
                    "Pawn.cs",
                    "namespace Game; class Pawn { public int Health; }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M(Pawn p) { var n = p.Hea|lth; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Pawn.Health");
    }

    #[test]
    fn a_member_on_a_local_from_new_goes_to_that_types_member() {
        let f = fixture(
            &[
                (
                    "Pawn.cs",
                    "namespace Game; class Pawn { public int Health; }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M() { var p = new Pawn(); var n = p.Hea|lth; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Pawn.Health");
    }

    #[test]
    fn a_member_on_a_field_goes_to_that_types_member() {
        let f = fixture(
            &[
                (
                    "Pawn.cs",
                    "namespace Game; class Pawn { public int Health; }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { private Pawn _pawn; void M() { var n = _pawn.Hea|lth; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Pawn.Health");
    }

    #[test]
    fn a_chain_is_walked_left_to_right() {
        let f = fixture(
            &[
                ("V.cs", "namespace Game; class Vec { public int X; }"),
                (
                    "T.cs",
                    "namespace Game; class Transform { public Vec Position; }",
                ),
                (
                    "P.cs",
                    "namespace Game; class Pawn { public Transform Root; }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M(Pawn p) { var n = p.Root.Position.|X; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Vec.X");
    }

    #[test]
    fn a_call_is_typed_by_what_it_returns() {
        let f = fixture(
            &[
                ("H.cs", "namespace Game; class Health { public int Value; }"),
                (
                    "S.cs",
                    "namespace Game; class Stash { public Health Get() { return null; } }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { private Stash _s; void M() { var v = _s.Get().Val|ue; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Health.Value");
    }

    #[test]
    fn a_var_typed_by_a_call_carries_that_type_on() {
        let f = fixture(
            &[
                ("H.cs", "namespace Game; class Health { public int Value; }"),
                (
                    "S.cs",
                    "namespace Game; class Stash { public Health Get() { return null; } }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { private Stash _s; void M() { var h = _s.Get(); var v = h.Val|ue; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Health.Value");
    }

    #[test]
    fn a_static_member_is_reached_through_the_type_name() {
        let f = fixture(
            &[
                (
                    "H.cs",
                    "namespace Game; static class Helper { public static void Run() { } }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M() { Helper.R|un(); } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Helper.Run");
    }

    #[test]
    fn an_extension_method_is_reached_on_the_type_it_extends() {
        let f = fixture(
            &[
                ("P.cs", "namespace Game; class Pawn { }"),
                (
                    "E.cs",
                    "namespace Game; static class Extras { public static void Say(this Pawn p) { } }",
                ),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M(Pawn p) { p.S|ay(); } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Extras.Say");
    }

    #[test]
    fn a_members_own_member_is_found_without_a_receiver() {
        let f = fixture(
            &[(
                "Use.cs",
                "namespace Game; class Use { public int Health; void M() { var n = Hea|lth; } }",
            )],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Use.Health");
    }

    #[test]
    fn a_member_inherited_from_a_base_is_found_through_a_receiver() {
        let f = fixture(
            &[
                ("A.cs", "namespace Game; class Actor { public int Health; }"),
                ("P.cs", "namespace Game; class Pawn : Actor { }"),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M(Pawn p) { var n = p.Hea|lth; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.lands_on(), "Game.Actor.Health");
    }

    // MARK: - the things it should refuse to answer

    #[test]
    fn a_keyword_is_not_a_name() {
        let f = fixture(&[("Use.cs", "namespace Game; cl|ass Use { }")], "Use.cs");
        assert_eq!(f.go(), Err(Miss::NotAName));
    }

    #[test]
    fn a_word_inside_a_string_is_not_a_name() {
        let f = fixture(
            &[
                ("P.cs", "namespace Game; class Pawn { }"),
                (
                    "Use.cs",
                    "namespace Game; class Use { string s = \"Pa|wn\"; }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(f.go(), Err(Miss::NotAName));
    }

    #[test]
    fn a_word_inside_a_comment_is_not_a_name() {
        let f = fixture(
            &[
                ("P.cs", "namespace Game; class Pawn { }"),
                ("Use.cs", "namespace Game; class Use { // see Pa|wn\n }"),
            ],
            "Use.cs",
        );
        assert_eq!(f.go(), Err(Miss::NotAName));
    }

    #[test]
    fn a_member_of_an_untypeable_receiver_says_so_rather_than_guessing() {
        // `thing` is declared as a type the project does not have, so nothing
        // says what `.Health` is. There *is* a `Health` in the project, and
        // going there would be the wrong answer delivered confidently.
        let f = fixture(
            &[
                ("P.cs", "namespace Game; class Pawn { public int Health; }"),
                (
                    "Use.cs",
                    "namespace Game; class Use { void M(SomeUnknownType thing) { var n = thing.Hea|lth; } }",
                ),
            ],
            "Use.cs",
        );
        assert!(
            matches!(f.go(), Err(Miss::ReceiverUnknown(_))),
            "{:?}",
            f.go(),
        );
    }

    #[test]
    fn a_name_from_outside_the_project_says_so() {
        let f = fixture(
            &[(
                "Use.cs",
                "namespace Game; class Use { void M() { var v = new Vec|tor3(); } }",
            )],
            "Use.cs",
        );
        assert!(
            matches!(f.go(), Err(Miss::NotInProject(_))),
            "a type from an assembly is layer 5's business: {:?}",
            f.go(),
        );
    }

    #[test]
    fn a_local_shadows_a_field_of_the_same_name() {
        let f = fixture(
            &[
                ("P.cs", "namespace Game; class Pawn { public int N; }"),
                ("O.cs", "namespace Game; class Other { public int N; }"),
                (
                    "Use.cs",
                    "namespace Game; class Use { private Other Position; void M() { var Position = new Pawn(); var n = Position.|N; } }",
                ),
            ],
            "Use.cs",
        );
        assert_eq!(
            f.lands_on(),
            "Game.Pawn.N",
            "the local, declared later, is what `Position` means here",
        );
    }

    #[test]
    fn a_cursor_past_the_end_of_the_file_is_not_a_name() {
        let f = fixture(&[("Use.cs", "class Use { }|")], "Use.cs");
        assert_eq!(f.go(), Err(Miss::NotAName));
    }

    #[test]
    fn the_word_and_span_come_back_with_the_answer() {
        let f = fixture(
            &[
                ("P.cs", "namespace Game; class Pawn { }"),
                ("Use.cs", "namespace Game; class Use { Pa|wn p; }"),
            ],
            "Use.cs",
        );
        let target = f.go().expect("resolves");
        assert_eq!(target.word, "Pawn");
        let text = "namespace Game; class Use { Pawn p; }";
        assert_eq!(
            &text[target.span.start() as usize..target.span.end() as usize],
            "Pawn",
        );
    }

    #[test]
    fn an_ambiguous_name_comes_back_as_all_of_them() {
        let f = fixture(
            &[
                ("A.cs", "namespace Alpha; class Thing { }"),
                ("B.cs", "namespace Beta; class Thing { }"),
                ("Use.cs", "namespace Gamma; class Use { Thi|ng t; }"),
            ],
            "Use.cs",
        );
        let target = f.go().expect("resolves to something");
        assert_eq!(target.found.confidence, Confidence::Ambiguous);
        assert_eq!(target.found.entries.len(), 2);
    }
}
