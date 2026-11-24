//! Code lens: "N references" above every type and member of a file.
//!
//! Asked naively, this is one find-all-references per declaration, and a
//! file with forty members would search the project forty times. It is
//! turned around instead: the file's declarations are gathered first, and
//! the project is searched once for all of them. Each file is looked at in
//! parallel; a file that spells none of the names is dismissed by its text
//! without being parsed, which is what keeps this cheap; and a file that
//! does is walked once, each name spelled like a declaration bound once and
//! counted against whichever declaration it turns out to be.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use rustlyn_semantics::{BoundExpressionKind, MethodKind, SymbolId};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::references::{ReferenceKind, mentions};
use super::{Resolved, Semantic, View, parallel};

/// How many references one declaration has.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lens {
    /// The declaration's name, in bytes of the text asked about.
    pub span: TextSpan,
    /// References in the project, not counting its own declarations.
    pub count: usize,
}

impl Semantic {
    /// A reference count for every type and member declared in `path`:
    /// types, methods, constructors, properties, events, fields, indexers
    /// and operators. A type's count includes the calls of its
    /// constructors; an indexer's is every `x[i]` that reaches it, and an
    /// operator's every expression that applies it. Enum members and local
    /// functions have none, as in Roslyn.
    ///
    /// A member counts the uses of its family in the project, as find all
    /// references lists them ([`Semantic::cascade`]): a call through the
    /// interface member it implements, or of the virtual method it
    /// overrides — which is what every call of an override binds to — is a
    /// call of it as well. Members of assemblies stay out of the family: an
    /// override of `ToString` is not used by every `ToString()` there is.
    #[must_use]
    pub fn reference_counts(&self, path: &Path, text: Option<&str>) -> Option<Vec<Lens>> {
        self.reference_counts_until(path, text, &|| false)
    }

    /// `reference_counts`, giving up once `stop` says so: files not yet
    /// searched are skipped, and the counts are then short — the caller
    /// that asked to stop throws them away.
    #[must_use]
    pub fn reference_counts_until(
        &self,
        path: &Path,
        text: Option<&str>,
        stop: &(dyn Fn() -> bool + Sync),
    ) -> Option<Vec<Lens>> {
        let tree = self.tree_index(path)?;
        let mut view = self.view_of(path, text)?;

        let declarations = declarations(&view);
        let mut slots: HashMap<SymbolId, usize> = HashMap::new();
        let mut names: HashSet<String> = HashSet::new();
        let mut creations = false;
        // Indexers and operators are used without their names: they are
        // counted from the bound code, in the files that name their type.
        let mut unnamed: HashSet<SymbolId> = HashSet::new();
        let mut owners: HashSet<String> = HashSet::new();
        for (span, symbol) in &declarations {
            let next = slots.len();
            slots.entry(*symbol).or_insert(next);
            if is_unnamed(&view, *span) {
                unnamed.insert(*symbol);
                if let Some(container) = self.compilation.symbols().get(*symbol).container {
                    owners.insert(self.compilation.symbols().get(container).name.clone());
                }
                continue;
            }
            names.insert(self.search_name(*symbol));
            creations |= self.is_made_by_new(&Resolved::Symbol(*symbol));
        }
        if declarations.is_empty() {
            return Some(Vec::new());
        }
        // Each member of a family, and the declarations of this file it is
        // in the family of: a file that declares both an interface and its
        // implementation counts a use of either for both.
        let mut family: HashMap<SymbolId, Vec<usize>> = HashMap::new();
        let mut derived = None;
        let in_source = |symbol: SymbolId| !self.compilation.is_from_metadata(symbol);
        let declared_unnamed = unnamed.clone();
        for (&symbol, &slot) in &slots {
            for related in self.cascade_where(symbol, &mut derived, &in_source) {
                let slots = family.entry(related).or_default();
                if !slots.contains(&slot) {
                    slots.push(slot);
                }
                // An indexer reached through its interface is used by code
                // that names the interface, not the type declaring it.
                if declared_unnamed.contains(&symbol) && unnamed.insert(related) {
                    let symbols = self.compilation.symbols();
                    if let Some(container) = symbols.get(related).container {
                        owners.insert(symbols.get(container).name.clone());
                    }
                }
            }
        }

        let edited = view.speculation.is_some();
        let candidates: Vec<usize> = self
            .paths
            .keys()
            .copied()
            .filter(|&other| other != tree || !edited)
            .collect();
        let per_file = parallel(candidates.len(), |index| {
            if stop() {
                return Vec::new();
            }
            let tree = candidates[index];
            let Some(text) = self.compilation.trees().source(tree).map(|s| s.text()) else {
                return Vec::new();
            };
            let named = names.iter().any(|name| mentions(text, name, creations));
            let bound =
                !unnamed.is_empty() && owners.iter().any(|owner| text.contains(owner.as_str()));
            if !named && !bound {
                return Vec::new();
            }
            let Some(mut view) = self.view(tree) else {
                return Vec::new();
            };
            let mut found = if named {
                self.hits(&mut view, &names, creations, &slots, &family)
            } else {
                Vec::new()
            };
            if bound {
                found.extend(unnamed_hits(&mut view, &unnamed, &family));
            }
            found
        });
        let mut counts = vec![0usize; slots.len()];
        let here = if edited {
            let mut found = self.hits(&mut view, &names, creations, &slots, &family);
            if !unnamed.is_empty() {
                found.extend(unnamed_hits(&mut view, &unnamed, &family));
            }
            found
        } else {
            Vec::new()
        };
        for slot in per_file.into_iter().flatten().chain(here) {
            counts[slot] += 1;
        }
        Some(
            declarations
                .into_iter()
                .map(|(span, symbol)| Lens {
                    span,
                    count: counts[slots[&symbol]],
                })
                .collect(),
        )
    }

    /// Where `reference_counts` puts its lenses, in the same order, without
    /// counting anything: the names of the file's declarations. No other
    /// file is looked at, so an editor can ask this while it opens the file
    /// and make room for the lenses before the counts, which search the
    /// project, come in.
    #[must_use]
    pub fn lens_places(&self, path: &Path, text: Option<&str>) -> Option<Vec<TextSpan>> {
        self.tree_index(path)?;
        let view = self.view_of(path, text)?;
        Some(
            declarations(&view)
                .into_iter()
                .map(|(span, _)| span)
                .collect(),
        )
    }

    /// Which declarations each use in a file is a reference to, by slot:
    /// `slots` has the declarations of the file, `family` every symbol a
    /// use of which counts for one of them.
    fn hits(
        &self,
        view: &mut View<'_>,
        names: &HashSet<String>,
        creations: bool,
        slots: &HashMap<SymbolId, usize>,
        family: &HashMap<SymbolId, Vec<usize>>,
    ) -> Vec<usize> {
        let symbols = self.compilation.symbols();
        let mut hits = Vec::new();
        for found in view.uses_of(names, creations) {
            if found.kind == ReferenceKind::Definition {
                continue;
            }
            let Resolved::Symbol(symbol) = found.resolved else {
                continue;
            };
            if let Some(arguments) = found.creation {
                // `new()` makes the type, and calls whichever of its
                // constructors take that many arguments.
                hits.extend(slots.get(&symbol));
                for (&candidate, &slot) in slots {
                    let candidate_symbol = symbols.get(candidate);
                    if candidate_symbol.container == Some(symbol)
                        && candidate_symbol.as_method().is_some_and(|method| {
                            method.method_kind == MethodKind::Constructor
                                && method.parameters.len() == arguments
                        })
                    {
                        hits.push(slot);
                    }
                }
                continue;
            }
            hits.extend(family.get(&symbol).into_iter().flatten());
            // A constructor's call is a reference to its type as well.
            let found_symbol = symbols.get(symbol);
            if found_symbol
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor)
                && let Some(container) = found_symbol.container
            {
                hits.extend(slots.get(&container));
            }
        }
        hits
    }
}

/// Whether the declaration named at `span` is an indexer or an operator,
/// which code uses without writing its name.
fn is_unnamed(view: &View<'_>, span: TextSpan) -> bool {
    view.root.find_token(span.start()).is_some_and(|token| {
        matches!(
            token.parent().kind(),
            SyntaxKind::IndexerDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
        )
    })
}

/// Which of the `unnamed` declarations -- indexers and operators -- each
/// expression of the file's bound code reaches, by slot. Each expression
/// counts once, however many bodies around it bound it.
fn unnamed_hits(
    view: &mut View<'_>,
    unnamed: &HashSet<SymbolId>,
    family: &HashMap<SymbolId, Vec<usize>>,
) -> Vec<usize> {
    let mut owners: Vec<SyntaxNode> = view
        .root
        .descendants()
        .filter(|node| {
            rustlyn_semantics::is_body_owner(node.kind())
                && node.kind() != SyntaxKind::CompilationUnit
        })
        .collect();
    if view
        .root
        .children()
        .any(|child| child.kind() == SyntaxKind::GlobalStatement)
    {
        owners.push(view.root.clone());
    }
    let mut seen: HashSet<(TextSpan, SymbolId)> = HashSet::new();
    for owner in owners {
        let Some(body) = view.body_for(&owner) else {
            continue;
        };
        super::walk::walk_body(&body, &mut |visited| {
            if let super::walk::Visited::Expression(expression) = visited {
                let reached = match &expression.kind {
                    BoundExpressionKind::IndexerAccess { indexer, .. } => Some(*indexer),
                    BoundExpressionKind::Call { method, .. } => Some(*method),
                    _ => None,
                };
                if let Some(symbol) = reached.filter(|symbol| unnamed.contains(symbol)) {
                    seen.insert((expression.span, symbol));
                }
            }
        });
    }
    seen.into_iter()
        .flat_map(|(_, symbol)| family.get(&symbol).into_iter().flatten().copied())
        .collect()
}

/// The declarations of a file that get a lens: each name, and the symbol
/// it declares.
fn declarations(view: &View<'_>) -> Vec<(TextSpan, SymbolId)> {
    let mut found = Vec::new();
    for node in view.root.descendants() {
        let named: Vec<SyntaxNode> = match node.kind() {
            SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::DelegateDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration => vec![node.clone()],
            // `event Action A, B;` declares two, and `int a, b;` too.
            SyntaxKind::EventFieldDeclaration | SyntaxKind::FieldDeclaration => node
                .descendants()
                .filter(|inner| inner.kind() == SyntaxKind::VariableDeclarator)
                .collect(),
            _ => continue,
        };
        for declaration in named {
            // An indexer is named by `this`, an operator by its token.
            let Some(name) = declaration
                .child_tokens()
                .find(|token| match declaration.kind() {
                    SyntaxKind::IndexerDeclaration => token.kind() == SyntaxKind::ThisKeyword,
                    SyntaxKind::OperatorDeclaration => {
                        (token.kind() != SyntaxKind::OperatorKeyword
                            && token.kind().is_punctuation())
                            || matches!(
                                token.kind(),
                                SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword
                            )
                    }
                    SyntaxKind::ConversionOperatorDeclaration => {
                        token.kind() == SyntaxKind::OperatorKeyword
                    }
                    _ => token.kind() == SyntaxKind::IdentifierToken,
                })
            else {
                continue;
            };
            if let Some(symbol) = view.model.declared_symbol(&declaration) {
                found.push((name.span(), symbol));
            }
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::super::tests::compile;
    use super::*;

    /// The count above each declaration of `file`, as `(name, count)`.
    fn counts(semantic: &Semantic, file: &str, text: &str, edited: bool) -> Vec<(String, usize)> {
        semantic
            .reference_counts(Path::new(&format!("/p/{file}")), edited.then_some(text))
            .expect("counted")
            .into_iter()
            .map(|lens| {
                (
                    text[lens.span.start() as usize..lens.span.end() as usize].to_string(),
                    lens.count,
                )
            })
            .collect()
    }

    #[test]
    fn every_type_and_member_gets_its_count() {
        let pawn = "using System;\n\
                    namespace Game {\n\
                      public interface IHittable { void Hit(int damage); }\n\
                      public class Pawn : IHittable {\n\
                        public int Health { get; set; }\n\
                        public event Action Died;\n\
                        public Pawn() { }\n\
                        public Pawn(int health) { Health = health; }\n\
                        public void Hit(int damage) { Health -= damage; if (Health <= 0) Died?.Invoke(); }\n\
                        void Unused() { }\n\
                      }\n\
                    }\n";
        let arena = "namespace Game {\n\
                     class Arena {\n\
                       Pawn a = new Pawn(10);\n\
                       Pawn b = new();\n\
                       void Fight(IHittable h) { a.Hit(1); b.Hit(2); h.Hit(3); a.Health = 5; }\n\
                     }\n\
                     }\n";
        let semantic = compile(&[("Pawn.cs", pawn), ("Arena.cs", arena)], false).expect("compiled");
        let found = counts(&semantic, "Pawn.cs", pawn, false);
        assert_eq!(
            found,
            vec![
                ("IHittable".to_string(), 2),
                // `h.Hit(3)`, and the two calls of the method implementing it.
                ("Hit".to_string(), 3),
                // Two fields typed `Pawn`, `new Pawn(10)` and `new()`.
                ("Pawn".to_string(), 4),
                ("Health".to_string(), 4),
                ("Died".to_string(), 1),
                ("Pawn".to_string(), 1),
                ("Pawn".to_string(), 1),
                // `a.Hit(1)`, `b.Hit(2)`, and `h.Hit(3)` through the interface.
                ("Hit".to_string(), 3),
                ("Unused".to_string(), 0),
            ]
        );
    }

    /// What every call of an override binds to is the method it overrides,
    /// and a member called only through its interface is called all the
    /// same: neither has "no references".
    #[test]
    fn a_member_counts_the_uses_of_what_it_overrides_and_implements() {
        let widget = "using System;\n\
                      public interface IOptions { event Action<int> Selected; void Pick(int i); int Size { get; } }\n\
                      public abstract class View { public abstract void Shown(); public virtual void Hidden() { } }\n\
                      public class Options : View, IOptions {\n\
                        public event Action<int> Selected;\n\
                        public void Pick(int i) { Selected?.Invoke(i); }\n\
                        int IOptions.Size => 1;\n\
                        public override void Shown() { }\n\
                        public override void Hidden() { base.Hidden(); }\n\
                        public override string ToString() => \"options\";\n\
                      }\n";
        let screen = "public class Screen {\n\
                        IOptions options; View view;\n\
                        void Open() { options.Selected += i => { }; options.Pick(1); var n = options.Size; view.Shown(); view.Hidden(); var s = view.ToString(); }\n\
                      }\n";
        let semantic =
            compile(&[("Options.cs", widget), ("Screen.cs", screen)], false).expect("compiled");
        let found = counts(&semantic, "Options.cs", widget, false);
        assert_eq!(
            found,
            vec![
                // The base list, the field and `IOptions.Size`.
                ("IOptions".to_string(), 3),
                ("Selected".to_string(), 2),
                ("Pick".to_string(), 1),
                ("Size".to_string(), 1),
                ("View".to_string(), 2),
                ("Shown".to_string(), 1),
                // `view.Hidden()` and the override's `base.Hidden()`.
                ("Hidden".to_string(), 2),
                ("Options".to_string(), 0),
                // `options.Selected +=` through the interface, and the
                // `Invoke` of its own.
                ("Selected".to_string(), 2),
                ("Pick".to_string(), 1),
                // An explicit implementation: named `IOptions.Size`, used as
                // `Size`.
                ("Size".to_string(), 1),
                ("Shown".to_string(), 1),
                ("Hidden".to_string(), 2),
                // `object.ToString` is not in the family: what every
                // `ToString()` of the project calls is no use of this one.
                ("ToString".to_string(), 0),
            ]
        );
    }

    #[test]
    fn fields_indexers_and_operators_are_counted() {
        let money = "public struct Money {\n\
                       public int cents;\n\
                       public int this[int i] => cents;\n\
                       public static Money operator +(Money a, Money b) => a;\n\
                       public static implicit operator int(Money m) => m.cents;\n\
                     }\n";
        let bank = "class Bank {\n\
                      int Total(Money a, Money b) { Money sum = a + b + a; int first = a[0]; return sum.cents + first; }\n\
                    }\n";
        let semantic = compile(&[("Money.cs", money), ("Bank.cs", bank)], false).expect("compiled");
        let found = counts(&semantic, "Money.cs", money, false);
        let count = |name: &str| {
            found
                .iter()
                .find(|(spelled, _)| spelled == name)
                .unwrap_or_else(|| panic!("{name} in {found:?}"))
                .1
        };
        assert_eq!(count("cents"), 3, "{found:?}");
        assert_eq!(count("this"), 1, "{found:?}");
        assert_eq!(count("+"), 2, "{found:?}");
        assert!(found.iter().any(|(spelled, _)| spelled == "operator"));
    }

    #[test]
    fn unsaved_text_is_counted_as_typed() {
        let text = "class C { void Go() { } void T() { Go(); } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let typed = "class C { void Go() { } void T() { Go(); Go(); } }\n";
        let found = counts(&semantic, "C.cs", typed, true);
        assert_eq!(
            found,
            vec![
                ("C".to_string(), 0),
                ("Go".to_string(), 2),
                ("T".to_string(), 0)
            ]
        );
    }

    #[test]
    fn a_count_told_to_stop_searches_no_file() {
        let semantic = compile(
            &[
                ("A.cs", "class A { public void M() {} }"),
                ("B.cs", "class B { void F(A a) { a.M(); } }"),
            ],
            false,
        )
        .expect("compiled");
        let path = Path::new("/p/A.cs");
        let counted = semantic.reference_counts(path, None).expect("counted");
        assert!(counted.iter().any(|lens| lens.count > 0), "{counted:?}");
        let stopped = semantic
            .reference_counts_until(path, None, &|| true)
            .expect("counted");
        assert_eq!(stopped.len(), counted.len(), "the same declarations");
        assert!(stopped.iter().all(|lens| lens.count == 0), "{stopped:?}");
    }
}
