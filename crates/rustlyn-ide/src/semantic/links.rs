//! Every name in a file with the symbol it settled on: what a project-wide
//! graph is made of.
//!
//! The call hierarchy answers about one member at a time, which is what an
//! editor asks. An analysis of the whole project — which code leads to a
//! given set of APIs, what depends on what — wants the same answer for every
//! member at once, and asking a member at a time binds each file over and
//! over. Here a file is read once: every body in it is bound, and every name
//! comes back with its symbol and the statement it stands in. Names outside
//! bodies come too — base types, attribute arguments, the types of members —
//! since a type that implements an interface, or names a type in an
//! attribute, depends on it without a body saying so.
//!
//! Symbols are described separately ([`Semantic::link_target`]): a project
//! has millions of names and a few hundred thousand symbols, so a caller
//! describes each symbol once.

use std::collections::HashSet;
use std::path::Path;

use rustlyn_semantics::{SemanticModel, SymbolId, SymbolKind, Symbols, Type, is_body_owner};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::{SourceText, TextSpan};

/// A symbol of the compilation, as a [`Link`] names it. It means something
/// only to the [`Semantic`] it came from.
pub type LinkSymbol = SymbolId;

use super::{Place, Resolved, Semantic, View, declaration_kind};
use crate::outline::{DeclarationKind, FileOutline};

/// Where a name stands.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LinkRole {
    /// In a body: a call, a read, a write, a type named in an expression.
    Body,
    /// In a type's base list.
    Base,
    /// In an attribute: its name or an argument.
    Attribute,
    /// In a declaration outside its body: a member's type, a parameter's.
    Signature,
}

/// One name and what it refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Link {
    /// The name, in bytes.
    pub span: TextSpan,
    /// The line of the name, from zero.
    pub line: u32,
    /// The lines of the statement the name is in, first and last, from zero.
    /// For a name in the header of a compound statement — an `if`'s
    /// condition, a `foreach`'s collection — the lines of that header. For a
    /// name outside any statement, the name's own line.
    pub statement: (u32, u32),
    pub target: SymbolId,
    pub role: LinkRole,
}

/// The names of one compiled file.
#[derive(Clone, Debug)]
pub struct FileLinks {
    /// The file's structure, as the compilation parsed it: with the
    /// preprocessor symbols of the assembly it goes into.
    pub outline: FileOutline,
    /// In the order of the text.
    pub links: Vec<Link>,
}

/// A symbol a name refers to, as a graph needs it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkTarget {
    pub name: String,
    /// The qualified name of the type or namespace it is in; empty at the
    /// top.
    pub container: String,
    pub kind: DeclarationKind,
    /// Where it is declared: a file of the project or an assembly.
    pub place: Option<Place>,
    /// The type of a field, property or event, as C# writes it, with every
    /// named type qualified: `Scellecs.Morpeh.Stash<Game.Health>`.
    pub type_text: Option<String>,
}

impl Semantic {
    /// Every name in `path` that refers to a symbol, with the file's
    /// structure. `None` for a file that is not part of the compilation.
    #[must_use]
    pub fn links(&self, path: &Path) -> Option<FileLinks> {
        let tree = self.tree_index(path)?;
        let syntax = self.compilation.trees().get(tree)?;
        let outline = FileOutline::of_tree(syntax);
        let lines = self.compilation.trees().source(tree)?.lines();
        let mut view = self.view(tree)?;

        let mut found: Vec<(TextSpan, SymbolId, LinkRole)> = Vec::new();
        let mut seen: HashSet<TextSpan> = HashSet::new();
        for owner in body_owners(&view.root) {
            // Bound here rather than through the view: the shared cache of
            // bodies is for an editor that asks about one method again and
            // again, and a pass over the project would only churn it.
            let body = view.model.bind_body_for_editor(&owner);
            let within = owner.span();
            for (&at, &symbol) in &body.symbols {
                if within.contains_span(at) && seen.insert(at) {
                    found.push((at, symbol, LinkRole::Body));
                }
            }
        }
        for token in view.root.descendant_tokens() {
            if token.kind() != SyntaxKind::IdentifierToken || seen.contains(&token.span()) {
                continue;
            }
            let Some(role) = declared_role(&token) else {
                continue;
            };
            if let Some(Resolved::Symbol(symbol)) = view.resolve(&token)
                && seen.insert(token.span())
            {
                found.push((token.span(), symbol, role));
            }
        }
        found.sort_by_key(|(at, _, _)| at.start());

        let links = found
            .into_iter()
            .map(|(span, target, role)| {
                let line = lines.line_of(span.start());
                let statement = if role == LinkRole::Body {
                    statement_of(&view, span).map_or((line, line), |statement| {
                        (
                            lines.line_of(statement.start()),
                            lines.line_of(statement.end().saturating_sub(1).max(statement.start())),
                        )
                    })
                } else {
                    (line, line)
                };
                Link {
                    span,
                    line,
                    statement,
                    target,
                    role,
                }
            })
            .collect();
        Some(FileLinks { outline, links })
    }

    /// The structure of another text of `path` — an earlier revision of
    /// it — read with the preprocessor symbols and the version of C# the
    /// compiled file is read with.
    #[must_use]
    pub fn outline_as(&self, path: &Path, text: &str) -> FileOutline {
        FileOutline::of(
            &SourceText::new(path.to_string_lossy(), text),
            &self.parse_options_of(path),
        )
    }

    /// What a graph needs to know about a symbol a [`Link`] names.
    #[must_use]
    pub fn link_target(&self, symbol: SymbolId) -> LinkTarget {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let container = found
            .container
            .map(|container| symbols.qualified_name(container))
            .unwrap_or_default();
        let type_text = matches!(
            found.kind,
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Event
        )
        .then(|| {
            qualified(
                &SemanticModel::new(&self.compilation, 0).type_of_symbol(symbol),
                symbols,
            )
        });
        LinkTarget {
            name: found.name.clone(),
            container,
            kind: declaration_kind(&self.compilation, symbol),
            place: self
                .declarations_of(symbol)
                .into_iter()
                .next()
                .map(|found| found.place),
            type_text,
        }
    }

    /// What a member overrides and implements, and what a type derives
    /// from, as [`Link`] targets: a call to any of them may run the member.
    #[must_use]
    pub fn link_bases(&self, symbol: SymbolId) -> Vec<SymbolId> {
        self.base_symbols(symbol)
    }

    /// The symbol declared at `offset` of `path`: the name of a member or a
    /// type. Joins a file's outline to the targets of links.
    #[must_use]
    pub fn link_declared(&self, path: &Path, offset: u32) -> Option<SymbolId> {
        let tree = self.tree_index(path)?;
        let view = self.view(tree)?;
        let token = view.root.find_token(offset)?;
        std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find_map(|node| {
                let symbol = view.model.declared_symbol(&node)?;
                let named_here = self
                    .compilation
                    .symbols()
                    .get(symbol)
                    .locations
                    .iter()
                    .any(|location| location.tree == tree && location.span.contains(offset));
                named_here.then_some(symbol)
            })
    }
}

/// A type as C# writes it, with every named type qualified:
/// `Scellecs.Morpeh.Stash<Game.Health>`.
fn qualified(ty: &Type, symbols: &Symbols) -> String {
    ty.display_by(symbols, &|symbol, arguments| {
        // Without the arity metadata writes after a generic type's name.
        let mut name = String::new();
        let mut arity = false;
        for c in symbols.qualified_name(symbol).chars() {
            match c {
                '`' => arity = true,
                c if arity && c.is_ascii_digit() => {}
                c => {
                    arity = false;
                    name.push(c);
                }
            }
        }
        Some(if arguments.is_empty() {
            name
        } else {
            let arguments: Vec<String> = arguments
                .iter()
                .map(|argument| qualified(argument, symbols))
                .collect();
            format!("{name}<{}>", arguments.join(", "))
        })
    })
}

/// The nodes of a file whose bodies are bound one by one: members, accessors
/// and the declarators of fields with an initializer.
fn body_owners(root: &SyntaxNode) -> Vec<SyntaxNode> {
    let mut owners = Vec::new();
    if root
        .children()
        .any(|child| child.kind() == SyntaxKind::GlobalStatement)
    {
        owners.push(root.clone());
    }
    for node in root.descendants() {
        match node.kind() {
            SyntaxKind::CompilationUnit => {}
            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => {
                owners.extend(
                    node.descendants()
                        .filter(|inner| inner.kind() == SyntaxKind::VariableDeclarator),
                );
            }
            kind if is_body_owner(kind) => owners.push(node),
            _ => {}
        }
    }
    owners
}

/// Where a name outside any body stands, when it is somewhere a declaration
/// depends on a symbol: a base list, an attribute, a member's signature.
/// `None` inside bodies (bound already), in `using` directives and in the
/// names of namespaces.
fn declared_role(token: &SyntaxToken) -> Option<LinkRole> {
    let mut role = LinkRole::Signature;
    for node in std::iter::once(token.parent().clone()).chain(token.parent().ancestors()) {
        match node.kind() {
            SyntaxKind::Block
            | SyntaxKind::ArrowExpressionClause
            | SyntaxKind::EqualsValueClause
            | SyntaxKind::UsingDirective
            | SyntaxKind::GlobalStatement => return None,
            SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration => {
                return None;
            }
            SyntaxKind::BaseList => role = LinkRole::Base,
            SyntaxKind::AttributeList => return Some(LinkRole::Attribute),
            kind if is_body_owner(kind) || kind.is_declaration_node() => return Some(role),
            _ => {}
        }
    }
    Some(role)
}

/// The statement a name is in. For a name in the header of a compound
/// statement, that header: the condition of an `if` is not the whole `if`.
fn statement_of(view: &View<'_>, span: TextSpan) -> Option<TextSpan> {
    let token = view.root.find_token(span.start())?;
    let mut last = token.parent().clone();
    if is_boundary(last.kind()) {
        return Some(last.span());
    }
    for node in token.parent().ancestors() {
        if is_boundary(node.kind()) {
            let compound = node.children().any(|child| is_boundary(child.kind()));
            return Some(if compound { last.span() } else { node.span() });
        }
        if is_body_owner(node.kind()) {
            return None;
        }
        last = node;
    }
    None
}

/// Where a statement starts for [`statement_of`]: a statement, or a clause
/// that holds statements of its own.
fn is_boundary(kind: SyntaxKind) -> bool {
    kind.is_statement_node()
        || matches!(
            kind,
            SyntaxKind::SwitchSection
                | SyntaxKind::CatchClause
                | SyntaxKind::ElseClause
                | SyntaxKind::FinallyClause
        )
}

// MARK: - the slice of a statement

/// A statement of a body, or the header of a compound one, as a slice sees
/// it.
struct Unit {
    span: TextSpan,
    /// The compound statements it is in, by index, and the statement a
    /// lambda it is in belongs to.
    guards: Vec<usize>,
    /// The names it mentions.
    uses: HashSet<String>,
    /// The locals it declares or assigns.
    defines: Vec<String>,
    /// Leaves the body or a loop: `return`, `break`, `continue`, `throw`.
    jump: bool,
    /// Declares its names rather than assigning them.
    declares: bool,
}

impl Semantic {
    /// The lines of a member's body that decide what the statement at
    /// `offset` does and whether it runs, first and last of each run, from
    /// zero, in order:
    ///
    /// * the statement itself;
    /// * the headers of the statements it is nested in — the condition of
    ///   an `if`, the collection of a `foreach`;
    /// * the conditions under which an earlier `return`, `break`,
    ///   `continue` or `throw` leaves before it;
    /// * the statements that declare or assign the locals any of those
    ///   mention, and so on from them.
    ///
    /// This is a slice by the text of one body, not by its flow: an
    /// assignment after the statement counts as much as one before it. It
    /// errs toward more lines. For a name outside any body, its own line.
    #[must_use]
    pub fn slice(&self, path: &Path, offset: u32) -> Vec<(u32, u32)> {
        let Some(tree) = self.tree_index(path) else {
            return Vec::new();
        };
        let (Some(view), Some(source)) = (self.view(tree), self.compilation.trees().source(tree))
        else {
            return Vec::new();
        };
        let lines = source.lines();
        let own = lines.line_of(offset);
        let Some(token) = view.root.find_token(offset) else {
            return vec![(own, own)];
        };
        // The member, not the accessor or the lambda: a slice is of the
        // whole body the name is in.
        let Some(owner) = token
            .parent()
            .ancestors()
            .find(|node| is_body_owner(node.kind()) && node.kind() != SyntaxKind::CompilationUnit)
        else {
            return vec![(own, own)];
        };
        let mut units: Vec<Unit> = Vec::new();
        collect_units(&owner, &mut Vec::new(), &mut units);
        let Some(seed) = units
            .iter()
            .enumerate()
            .filter(|(_, unit)| unit.span.contains(offset))
            .min_by_key(|(_, unit)| unit.span.length())
            .map(|(index, _)| index)
        else {
            return vec![(own, own)];
        };
        // Names that are locals of this body: declared in it, or its
        // parameters. A field of the same name as a local cannot be told
        // apart here, and C# does not let a body have both unqualified.
        let mut locals: HashSet<String> = units
            .iter()
            .filter(|unit| unit.declares)
            .flat_map(|unit| unit.defines.iter().cloned())
            .collect();
        for node in owner.descendants() {
            if node.kind() == SyntaxKind::Parameter
                && let Some(name) = node
                    .child_tokens()
                    .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .last()
            {
                locals.insert(name.value_text().to_owned());
            }
        }

        let mut inside = vec![false; units.len()];
        let mut pending = vec![seed];
        // What can leave before the statement runs.
        let start = units[seed].span.start();
        for unit in &units {
            if unit.jump && unit.span.start() < start {
                pending.extend(unit.guards.iter().copied());
            }
        }
        while let Some(index) = pending.pop() {
            if std::mem::replace(&mut inside[index], true) {
                continue;
            }
            pending.extend(units[index].guards.iter().copied());
            for (other, unit) in units.iter().enumerate() {
                if !inside[other]
                    && unit
                        .defines
                        .iter()
                        .any(|name| locals.contains(name) && units[index].uses.contains(name))
                {
                    pending.push(other);
                }
            }
        }
        let mut ranges: Vec<(u32, u32)> = units
            .iter()
            .zip(&inside)
            .filter(|(_, inside)| **inside)
            .map(|(unit, _)| {
                (
                    lines.line_of(unit.span.start()),
                    lines.line_of(unit.span.end().saturating_sub(1).max(unit.span.start())),
                )
            })
            .collect();
        ranges.sort_unstable();
        let mut merged: Vec<(u32, u32)> = Vec::new();
        for (first, last) in ranges {
            match merged.last_mut() {
                Some(run) if first <= run.1 + 1 => run.1 = run.1.max(last),
                _ => merged.push((first, last)),
            }
        }
        merged
    }
}

/// The statements under `node` as units, each with the compound statements
/// around it.
fn collect_units(node: &SyntaxNode, guards: &mut Vec<usize>, units: &mut Vec<Unit>) {
    for child in node.children() {
        let kind = child.kind();
        if kind == SyntaxKind::ArrowExpressionClause && guards.is_empty() {
            // An expression-bodied member: its expression is its statement.
            units.push(unit_of(&child, child.span(), guards));
            guards.push(units.len() - 1);
            collect_units(&child, guards, units);
            guards.pop();
            continue;
        }
        if !kind.is_statement_node() || kind == SyntaxKind::Block {
            collect_units(&child, guards, units);
            continue;
        }
        // A compound statement is its header: up to the first statement or
        // clause it holds.
        let body = child
            .children()
            .find(|inner| is_boundary(inner.kind()))
            .map(|inner| inner.span().start());
        let span = match body {
            Some(body) if body > child.span().start() => {
                TextSpan::new(child.span().start(), body - child.span().start())
            }
            _ => child.span(),
        };
        units.push(unit_of(&child, span, guards));
        // What is nested in it — statements of a compound one, the body of
        // a lambda in a simple one — runs under it.
        guards.push(units.len() - 1);
        collect_units(&child, guards, units);
        guards.pop();
    }
}

fn unit_of(node: &SyntaxNode, span: TextSpan, guards: &[usize]) -> Unit {
    let mut uses: HashSet<String> = HashSet::new();
    let mut defines: Vec<String> = Vec::new();
    let mut declares = false;
    for token in node.descendant_tokens() {
        if token.kind() != SyntaxKind::IdentifierToken || !span.contains(token.span().start()) {
            continue;
        }
        let name = token.value_text().to_owned();
        match token.parent().kind() {
            // `var x = …`, `out var x`, `is T x`, `foreach (var x in …)`.
            SyntaxKind::VariableDeclarator
            | SyntaxKind::SingleVariableDesignation
            | SyntaxKind::ForEachStatement => {
                declares = true;
                defines.push(name.clone());
            }
            _ => {}
        }
        uses.insert(name);
    }
    // `x = …`, `x.field += …`, `x++`: the local at the root of what is
    // written.
    for inner in std::iter::once(node.clone()).chain(node.descendants()) {
        if !span.contains(inner.span().start()) {
            continue;
        }
        let written = match inner.kind() {
            SyntaxKind::SimpleAssignmentExpression
            | SyntaxKind::AddAssignmentExpression
            | SyntaxKind::SubtractAssignmentExpression
            | SyntaxKind::MultiplyAssignmentExpression
            | SyntaxKind::DivideAssignmentExpression
            | SyntaxKind::ModuloAssignmentExpression
            | SyntaxKind::AndAssignmentExpression
            | SyntaxKind::ExclusiveOrAssignmentExpression
            | SyntaxKind::OrAssignmentExpression
            | SyntaxKind::LeftShiftAssignmentExpression
            | SyntaxKind::RightShiftAssignmentExpression
            | SyntaxKind::UnsignedRightShiftAssignmentExpression
            | SyntaxKind::CoalesceAssignmentExpression
            | SyntaxKind::PreIncrementExpression
            | SyntaxKind::PostIncrementExpression => inner.first_token(),
            _ => None,
        };
        if let Some(token) = written
            && token.kind() == SyntaxKind::IdentifierToken
        {
            defines.push(token.value_text().to_owned());
        }
    }
    Unit {
        span,
        guards: guards.to_vec(),
        uses,
        defines,
        jump: matches!(
            node.kind(),
            SyntaxKind::ReturnStatement
                | SyntaxKind::BreakStatement
                | SyntaxKind::ContinueStatement
                | SyntaxKind::ThrowStatement
                | SyntaxKind::YieldBreakStatement
                | SyntaxKind::GotoStatement
        ),
        declares,
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::tests::{at, compile};
    use super::*;

    const GAME: &str = "namespace Game {
    public struct Box {}
    public class Stash<T> {}
    public interface IService { void Run(Box times); }
    public class Service : IService {
        public Box Count;
        Stash<Box> _boxes;
        public void Run(Box times) {
            var total = Helper.Add(times, Count);
            if (Helper.Big(total)) return;
            while (Helper.Small(total)) {
                Count = total;
                Helper.Log(
                    total);
            }
            Helper.Done(_boxes);
        }
    }
    public static class Helper {
        public static Box Add(Box a, Box b) => a;
        public static bool Big(Box value) => false;
        public static bool Small(Box value) => false;
        public static void Log(Box value) {}
        public static void Done(Stash<Box> boxes) {}
    }
}
";

    fn line_of(text: &str, marker: &str) -> u32 {
        text[..text.find(marker).expect("the marker should be there")]
            .matches('\n')
            .count() as u32
    }

    #[test]
    fn every_name_of_a_file_with_its_symbol() {
        let semantic = compile(&[("Game.cs", GAME)], false).expect("compiled");
        let path = Path::new("/p/Game.cs");
        let file = semantic.links(path).expect("links");
        let link_at = |marker: &str, into: usize| {
            let offset = at(GAME, marker, into);
            file.links
                .iter()
                .find(|link| link.span.contains(offset))
                .unwrap_or_else(|| panic!("a link at {marker}"))
        };
        // A call in a body: the method, where it is declared, and the lines
        // of its statement — two of them here.
        let log = link_at("Log(\n", 0);
        let target = semantic.link_target(log.target);
        assert_eq!(log.role, LinkRole::Body);
        assert_eq!(
            (target.name.as_str(), target.container.as_str()),
            ("Log", "Game.Helper")
        );
        assert_eq!(target.kind, DeclarationKind::Method);
        assert!(matches!(target.place, Some(Place::Source { .. })));
        let first = line_of(GAME, "Helper.Log(");
        assert_eq!(log.statement, (first, first + 1));
        // A name in the header of a compound statement: the header only.
        let small = link_at("Small(total)", 0);
        assert_eq!(small.statement, (small.line, small.line));
        // A field, with its type as C# writes it, qualified.
        let boxes = semantic.link_target(link_at("_boxes);", 0).target);
        assert_eq!(boxes.kind, DeclarationKind::Field);
        assert_eq!(boxes.type_text.as_deref(), Some("Game.Stash<Game.Box>"));
        // Names outside bodies: a base, a member's type.
        let base = link_at("IService {\n        public Box Count", 0);
        assert_eq!(base.role, LinkRole::Base);
        assert_eq!(
            semantic.link_target(base.target).kind,
            DeclarationKind::Interface
        );
        let signature = link_at("Box Count;", 0);
        assert_eq!(signature.role, LinkRole::Signature);
        // The structure comes along.
        assert!(
            file.outline
                .declarations
                .iter()
                .any(|d| d.name == "Service")
        );
        assert!(semantic.links(Path::new("/p/Other.cs")).is_none());
    }

    #[test]
    fn a_member_and_what_it_implements() {
        let semantic = compile(&[("Game.cs", GAME)], false).expect("compiled");
        let path = Path::new("/p/Game.cs");
        let run = semantic
            .link_declared(path, at(GAME, "Run(Box times) {", 0))
            .expect("declared");
        let bases: Vec<String> = semantic
            .link_bases(run)
            .into_iter()
            .map(|base| semantic.link_target(base).container)
            .collect();
        assert_eq!(bases, ["Game.IService"]);
        // Not a declaration's name.
        assert!(
            semantic
                .link_declared(path, at(GAME, "Helper.Done", 0))
                .is_none()
        );
    }

    #[test]
    fn the_slice_of_a_statement() {
        let semantic = compile(&[("Game.cs", GAME)], false).expect("compiled");
        let path = Path::new("/p/Game.cs");
        let lines = |marker: &str| -> Vec<u32> {
            semantic
                .slice(path, at(GAME, marker, 0))
                .into_iter()
                .flat_map(|(first, last)| first..=last)
                .collect()
        };
        let total = line_of(GAME, "var total");
        let leave = line_of(GAME, "if (Helper.Big");
        let header = line_of(GAME, "while (Helper.Small");
        let assign = line_of(GAME, "Count = total;");
        let log = line_of(GAME, "Helper.Log(");
        let done = line_of(GAME, "Helper.Done(");
        // The last call runs unless the `if` leaves first, and the `if`
        // reads a local: both are in. The loop is not.
        assert_eq!(lines("Done(_boxes)"), [total, leave, done]);
        // A call in the loop runs under its header as well; the statement
        // beside it has no say.
        assert_eq!(lines("Log(\n"), [total, leave, header, log, log + 1]);
        assert_eq!(lines("Count = total;"), [total, leave, header, assign]);
        // Outside any body: the name's own line.
        let field = line_of(GAME, "public Box Count;");
        assert_eq!(lines("Box Count;"), [field]);
    }

    #[test]
    fn another_text_of_a_file_is_outlined_as_the_file_is() {
        let semantic = compile(&[("Game.cs", GAME)], false).expect("compiled");
        let before = GAME.replace("public static void Done", "public static void Finished");
        let outline = semantic.outline_as(Path::new("/p/Game.cs"), &before);
        assert!(outline.declarations.iter().any(|d| d.name == "Finished"));
        assert!(!outline.declarations.iter().any(|d| d.name == "Done"));
    }
}
