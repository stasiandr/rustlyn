//! What the refactorings that move members between types share: finding
//! the type and its members, writing a member's signature for an interface
//! or an abstract class, lifting a member's text out of one type to put it
//! in another, adding to a base list, and writing a new file for a new type
//! with the `using`s and namespace it needs.
//!
//! Extract interface, extract base class, pull members up and move static
//! members all start from a type declaration and a set of its members, and
//! end with those members, or their signatures, somewhere else.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use rustlyn_semantics::{Accessibility, Modifiers, SymbolId, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::Context;
use super::super::text::{
    indent_unit, indentation_at, is_type_declaration, line_start, newline, reindent,
};
use crate::edit::TextEdit;

/// A member of a type declaration, as the dialogs list it.
#[derive(Clone, Debug)]
pub(super) struct Member {
    /// The member's declaration: a method, property, field and so on.
    pub node: SyntaxNode,
    pub name: String,
    pub symbol: SymbolId,
}

/// The type declaration the cursor is on the name of: where the light bulb
/// offers the refactorings that start from a type.
pub(super) fn type_named_at_cursor(context: &Context<'_, '_>) -> Option<SyntaxNode> {
    let token = context.token_at_cursor()?;
    let declaration = token.parent().clone();
    (token.kind() == SyntaxKind::IdentifierToken
        && is_type_declaration(declaration.kind())
        && declaration
            .child_token_of_kind(SyntaxKind::IdentifierToken)
            .as_ref()
            == Some(&token))
    .then_some(declaration)
}

/// The innermost type declaration around `offset`: where a dialog's
/// refactoring was asked for.
pub(super) fn type_around(context: &Context<'_, '_>, offset: u32) -> Option<SyntaxNode> {
    let root = context.view.syntax_root();
    let token = root.find_token(offset)?;
    std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| is_type_declaration(node.kind()))
}

/// The members a type declares in this declaration, in order, each with the
/// symbol it declares. A field with several variables is one member, named
/// after its first.
pub(super) fn members_of(context: &Context<'_, '_>, declaration: &SyntaxNode) -> Vec<Member> {
    let mut found = Vec::new();
    for child in declaration.children() {
        let (name, symbol) = match child.kind() {
            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => {
                let Some(declarator) = child
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::VariableDeclarator)
                else {
                    continue;
                };
                let Some(name) = declarator.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                    continue;
                };
                (
                    name.value_text().to_string(),
                    context.view.declared(&declarator),
                )
            }
            SyntaxKind::MethodDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::EventDeclaration => {
                let Some(name) = child.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                    continue;
                };
                (name.value_text().to_string(), context.view.declared(&child))
            }
            SyntaxKind::IndexerDeclaration => ("this[]".to_string(), context.view.declared(&child)),
            _ => continue,
        };
        if let Some(symbol) = symbol {
            found.push(Member {
                node: child,
                name,
                symbol,
            });
        }
    }
    found
}

/// Whether a member is `public` and not `static`: what an interface can
/// promise.
pub(super) fn is_public_instance(context: &Context<'_, '_>, member: &Member) -> bool {
    let symbols = context.view.compiled().symbols();
    let symbol = symbols.get(member.symbol);
    symbol.accessibility == Accessibility::Public
        && !symbol.modifiers.contains(Modifiers::STATIC)
        && matches!(
            symbol.kind,
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
        )
}

/// Whether the member's declaration carries `modifier`.
pub(super) fn has_modifier(node: &SyntaxNode, modifier: SyntaxKind) -> bool {
    node.child_tokens().any(|token| token.kind() == modifier)
}

/// The members of `all` whose names are in `names`, every overload of each;
/// the first name that matches nothing, when one does not.
pub(super) fn chosen<'m>(all: &'m [Member], names: &[String]) -> Result<Vec<&'m Member>, String> {
    for name in names {
        if !all.iter().any(|member| member.name == *name) {
            return Err(format!("There is no member '{name}' to move."));
        }
    }
    let chosen: Vec<&Member> = all
        .iter()
        .filter(|member| names.contains(&member.name))
        .collect();
    if chosen.is_empty() {
        return Err("Choose at least one member.".to_string());
    }
    Ok(chosen)
}

// MARK: - signatures

/// The type written before a member's name.
fn written_type(node: &SyntaxNode) -> Option<String> {
    node.children()
        .find(|child| child.kind().is_type_node())
        .map(|ty| ty.text())
}

/// What a method, property, indexer or event is, without its body or
/// modifiers: `int Area()`, `string Name { get; set; }`. Only the accessors
/// every caller can use are kept. `None` for a member an interface cannot
/// declare.
pub(super) fn signature(node: &SyntaxNode) -> Option<String> {
    match node.kind() {
        SyntaxKind::MethodDeclaration => {
            let ty = written_type(node)?;
            let name = node.child_token_of_kind(SyntaxKind::IdentifierToken)?;
            let type_parameters = node
                .child_of_kind(SyntaxKind::TypeParameterList)
                .map(|list| list.text())
                .unwrap_or_default();
            let parameters = node.child_of_kind(SyntaxKind::ParameterList)?.text();
            let constraints: Vec<String> = node
                .children()
                .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
                .map(|clause| clause.text())
                .collect();
            let constraints = if constraints.is_empty() {
                String::new()
            } else {
                format!(" {}", constraints.join(" "))
            };
            Some(format!(
                "{ty} {}{type_parameters}{parameters}{constraints}",
                name.text()
            ))
        }
        SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration => {
            let ty = written_type(node)?;
            let head = if node.kind() == SyntaxKind::IndexerDeclaration {
                format!(
                    "this{}",
                    node.child_of_kind(SyntaxKind::BracketedParameterList)?
                        .text()
                )
            } else {
                node.child_token_of_kind(SyntaxKind::IdentifierToken)?
                    .text()
                    .to_string()
            };
            let accessors = accessors_of(node);
            if accessors.is_empty() {
                return None;
            }
            Some(format!("{ty} {head} {{ {} }}", accessors.join(" ")))
        }
        SyntaxKind::EventDeclaration => {
            let ty = written_type(node)?;
            let name = node.child_token_of_kind(SyntaxKind::IdentifierToken)?;
            Some(format!("event {ty} {}", name.text()))
        }
        SyntaxKind::EventFieldDeclaration => {
            let declaration = node.child_of_kind(SyntaxKind::VariableDeclaration)?;
            let ty = written_type(&declaration)?;
            let names: Vec<String> = declaration
                .children()
                .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                .filter_map(|declarator| {
                    declarator
                        .child_token_of_kind(SyntaxKind::IdentifierToken)
                        .map(|token| token.text().to_string())
                })
                .collect();
            Some(format!("event {ty} {}", names.join(", ")))
        }
        _ => None,
    }
}

/// `get;`, `set;`, `init;` for the accessors of a property without an
/// accessibility of their own; `get;` for an expression-bodied one.
fn accessors_of(node: &SyntaxNode) -> Vec<String> {
    let Some(list) = node.child_of_kind(SyntaxKind::AccessorList) else {
        return if node
            .child_of_kind(SyntaxKind::ArrowExpressionClause)
            .is_some()
        {
            vec!["get;".to_string()]
        } else {
            Vec::new()
        };
    };
    list.children()
        .filter(|accessor| {
            !accessor.child_tokens().any(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::PrivateKeyword
                        | SyntaxKind::ProtectedKeyword
                        | SyntaxKind::InternalKeyword
                )
            })
        })
        .filter_map(|accessor| {
            let keyword = accessor.first_token()?;
            let keyword = accessor
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::GetKeyword | SyntaxKind::SetKeyword | SyntaxKind::InitKeyword
                    )
                })
                .unwrap_or(keyword);
            Some(format!("{};", keyword.text()))
        })
        .collect()
}

/// The declaration's `public`, `protected` and so on, as written.
pub(super) fn accessibility_text(node: &SyntaxNode) -> String {
    let words: Vec<&str> = node
        .child_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::PublicKeyword
                    | SyntaxKind::PrivateKeyword
                    | SyntaxKind::ProtectedKeyword
                    | SyntaxKind::InternalKeyword
            )
        })
        .map(|token| match token.kind() {
            SyntaxKind::PublicKeyword => "public",
            SyntaxKind::PrivateKeyword => "private",
            SyntaxKind::ProtectedKeyword => "protected",
            _ => "internal",
        })
        .collect();
    words.join(" ")
}

// MARK: - moving text

/// Where a member's text starts: its first line, with the comments and
/// documentation above it.
pub(super) fn member_start(node: &SyntaxNode) -> u32 {
    let Some(first) = node.first_token() else {
        return node.span().start();
    };
    let mut start = first.span().start();
    for trivia in first.leading_trivia().iter().rev() {
        match trivia.kind() {
            SyntaxKind::WhitespaceTrivia | SyntaxKind::EndOfLineTrivia => {}
            SyntaxKind::SingleLineCommentTrivia
            | SyntaxKind::MultiLineCommentTrivia
            | SyntaxKind::SingleLineDocumentationCommentTrivia
            | SyntaxKind::MultiLineDocumentationCommentTrivia => start = trivia.span().start(),
            _ => break,
        }
    }
    start
}

/// A member's text, with its comments, unindented and with the four-space
/// steps [`insert_members`] expects.
///
/// [`insert_members`]: super::super::fixes::support::insert_members
pub(super) fn member_text(text: &str, node: &SyntaxNode) -> String {
    member_text_with(text, node, &[])
}

/// [`member_text`] with the `edits` of the file that fall inside the member
/// made first: a member that is rewritten as it moves.
pub(super) fn member_text_with(text: &str, node: &SyntaxNode, edits: &[TextEdit]) -> String {
    let start = member_start(node);
    let end = node.span().end();
    let indent = indentation_at(text, start);
    let inside: Vec<TextEdit> = edits
        .iter()
        .filter(|edit| edit.span.start() >= start && edit.span.end() <= end)
        .map(|edit| {
            TextEdit::new(
                TextSpan::new(
                    edit.span.start() - start,
                    edit.span.end() - edit.span.start(),
                ),
                edit.text.clone(),
            )
        })
        .collect();
    let snippet = crate::edit::apply(&text[start as usize..end as usize], &inside);
    let snippet = reindent(&snippet, &indent, "").replace('\r', "");
    normalize_indent(&snippet, &indent_unit(text))
}

/// Leading indentation of `unit` steps turned into four-space steps.
pub(super) fn normalize_indent(snippet: &str, unit: &str) -> String {
    if unit == "    " || unit.is_empty() {
        return snippet.to_string();
    }
    snippet
        .split('\n')
        .map(|line| {
            let mut rest = line;
            let mut steps = 0;
            while let Some(after) = rest.strip_prefix(unit) {
                rest = after;
                steps += 1;
            }
            format!("{}{rest}", "    ".repeat(steps))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The edits removing several members of one type: members next to each
/// other, or with only blank lines between them, go as one block, and the
/// block takes one blank line beside it with it — the one after it when
/// there is nothing but a blank line or the opening brace before it, the
/// one before it when the closing brace follows — so that what is left is
/// spaced as it was.
pub(super) fn remove_members(text: &str, nodes: &[SyntaxNode]) -> Vec<TextEdit> {
    use super::super::text::whole_lines;
    let mut spans: Vec<TextSpan> = nodes
        .iter()
        .map(|node| {
            whole_lines(
                text,
                TextSpan::from_bounds(member_start(node), node.span().end()),
            )
        })
        .collect();
    spans.sort_by_key(|span| span.start());
    let mut merged: Vec<TextSpan> = Vec::new();
    for span in spans {
        if let Some(last) = merged.last_mut()
            && text[last.end() as usize..span.start().max(last.end()) as usize]
                .trim()
                .is_empty()
        {
            *last = TextSpan::from_bounds(last.start(), span.end().max(last.end()));
            continue;
        }
        merged.push(span);
    }
    let line_before = |at: u32| -> Option<TextSpan> {
        if at == 0 {
            return None;
        }
        let start = line_start(text, at - 1);
        Some(TextSpan::from_bounds(start, at))
    };
    let line_after = |at: u32| -> Option<TextSpan> {
        if at as usize >= text.len() {
            return None;
        }
        let end = text[at as usize..]
            .find('\n')
            .map_or(text.len(), |end| at as usize + end + 1);
        Some(TextSpan::from_bounds(at, end as u32))
    };
    merged
        .into_iter()
        .map(|span| {
            // Only whole-line removals can take a blank line with them.
            if !super::super::text::starts_line(text, span.start())
                || !text[..span.end() as usize].ends_with('\n')
            {
                return TextEdit::delete(span);
            }
            let before = line_before(span.start());
            let after = line_after(span.end());
            let slice = |span: Option<TextSpan>| {
                span.map(|span| {
                    text[span.start() as usize..span.end() as usize]
                        .trim()
                        .to_string()
                })
            };
            let before_text = slice(before);
            let after_text = slice(after);
            let gap_before = before_text
                .as_deref()
                .is_none_or(|line| line.is_empty() || line.ends_with('{'));
            if gap_before && after_text.as_deref() == Some("") {
                return TextEdit::delete(TextSpan::from_bounds(
                    span.start(),
                    after.map_or(span.end(), |after| after.end()),
                ));
            }
            if before_text.as_deref() == Some("")
                && after_text
                    .as_deref()
                    .is_some_and(|line| line.starts_with('}'))
            {
                return TextEdit::delete(TextSpan::from_bounds(
                    before.map_or(span.start(), |before| before.start()),
                    span.end(),
                ));
            }
            TextEdit::delete(span)
        })
        .collect()
}

/// The edit adding `members` at the end of the type `declaration`, as
/// [`insert_members`] writes it — and for a type written on one line with
/// members already, `class A { int x; }`, the body opened up onto lines of
/// its own, the members there first.
///
/// [`insert_members`]: super::super::fixes::support::insert_members
pub(super) fn append_members(
    declaration: &SyntaxNode,
    text: &str,
    members: &[String],
) -> Option<TextEdit> {
    use super::super::fixes::support::{MemberPlace, insert_members};
    if let Some(edit) = insert_members(declaration, text, members, &MemberPlace::End) {
        return Some(edit);
    }
    let open = declaration.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
    let close = declaration.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
    let nl = newline(text);
    let unit = indent_unit(text);
    let outer = indentation_at(text, declaration.span().start());
    let inner = format!("{outer}{unit}");
    let existing: Vec<String> = declaration
        .children()
        .filter(|child| super::super::text::is_member(child.kind()))
        .map(|member| format!("{inner}{}", member.text()))
        .collect();
    let added: Vec<String> = members
        .iter()
        .map(|member| {
            member
                .split('\n')
                .map(|line| {
                    if line.is_empty() {
                        String::new()
                    } else {
                        let spaces = line.len() - line.trim_start_matches(' ').len();
                        format!(
                            "{inner}{}{}",
                            unit.repeat(spaces / 4),
                            &line[spaces - spaces % 4..]
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(nl)
        })
        .collect();
    let before = declaration
        .descendant_tokens()
        .take_while(|token| token.span().start() < open.span().start())
        .last()
        .map_or(open.span().start(), |token| token.span().end());
    Some(TextEdit::new(
        TextSpan::from_bounds(before, close.span().end()),
        format!(
            "{nl}{outer}{{{nl}{}{nl}{nl}{}{nl}{outer}}}",
            existing.join(nl),
            added.join(&format!("{nl}{nl}"))
        ),
    ))
}

/// The line of a member's text its declaration starts on, past its
/// comments and attributes.
fn first_code_line(lines: &[String]) -> Option<usize> {
    lines.iter().position(|line| {
        let line = line.trim_start();
        !(line.is_empty()
            || line.starts_with("//")
            || line.starts_with("/*")
            || line.starts_with('*')
            || line.starts_with('['))
    })
}

const ACCESS: [&str; 4] = ["public", "private", "protected", "internal"];
const MODIFIERS: [&str; 14] = [
    "new", "static", "virtual", "abstract", "override", "sealed", "readonly", "async", "extern",
    "unsafe", "partial", "required", "volatile", "const",
];

/// A member's text, unindented as [`member_text`] gives it, with the
/// modifiers in `remove` taken off, those in `add` put on after its
/// accessibility, and its accessibility replaced by `access` when that is
/// given (an empty one removes it).
pub(super) fn rewrite_modifiers(
    member: &str,
    remove: &[&str],
    add: &[&str],
    access: Option<&str>,
) -> String {
    let mut lines: Vec<String> = member.split('\n').map(str::to_string).collect();
    let Some(index) = first_code_line(&lines) else {
        return member.to_string();
    };
    let line = lines[index].clone();
    let indent = line.len() - line.trim_start().len();
    let mut words: Vec<&str> = Vec::new();
    let mut rest = &line[indent..];
    loop {
        let word = rest.split(' ').next().unwrap_or_default();
        if word.is_empty() || !(ACCESS.contains(&word) || MODIFIERS.contains(&word)) {
            break;
        }
        words.push(word);
        rest = rest[word.len()..].trim_start_matches(' ');
    }
    let mut all: Vec<String> = match access {
        Some(access) => access
            .split(' ')
            .filter(|word| !word.is_empty())
            .map(str::to_string)
            .collect(),
        None => words
            .iter()
            .filter(|word| ACCESS.contains(word))
            .map(|word| (*word).to_string())
            .collect(),
    };
    let mut others: Vec<String> = words
        .iter()
        .filter(|word| !ACCESS.contains(word) && !remove.contains(word))
        .map(|word| (*word).to_string())
        .collect();
    for (at, word) in add.iter().enumerate() {
        if !others.iter().any(|other| other == word) {
            others.insert(at.min(others.len()), (*word).to_string());
        }
    }
    all.extend(others);
    let head = if all.is_empty() {
        String::new()
    } else {
        format!("{} ", all.join(" "))
    };
    lines[index] = format!("{}{head}{rest}", &line[..indent]);
    lines.join("\n")
}

/// `member` as a base class holds it for the type it came from: a private
/// member (or one with no accessibility written) becomes `protected`.
pub(super) fn protected_if_private(member: &str, node: &SyntaxNode) -> String {
    let access = accessibility_text(node);
    if access.is_empty() || access == "private" {
        rewrite_modifiers(member, &[], &[], Some("protected"))
    } else {
        member.to_string()
    }
}

// MARK: - base lists

/// The edit that adds `name` to a type's base list: first for a base class,
/// last for an interface. A type with no base list gets one after its name
/// and type parameters.
pub(super) fn add_base(declaration: &SyntaxNode, name: &str, first: bool) -> Option<TextEdit> {
    if let Some(list) = declaration.child_of_kind(SyntaxKind::BaseList) {
        let types: Vec<SyntaxNode> = list
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::SimpleBaseType | SyntaxKind::PrimaryConstructorBaseType
                )
            })
            .collect();
        return if first {
            Some(TextEdit::insert(
                types.first()?.span().start(),
                format!("{name}, "),
            ))
        } else {
            Some(TextEdit::insert(
                types.last()?.span().end(),
                format!(", {name}"),
            ))
        };
    }
    let after = declaration
        .child_of_kind(SyntaxKind::ParameterList)
        .or_else(|| declaration.child_of_kind(SyntaxKind::TypeParameterList))
        .map(|node| node.span().end())
        .or_else(|| {
            declaration
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.span().end())
        })?;
    Some(TextEdit::insert(after, format!(" : {name}")))
}

// MARK: - new files

/// Where a new type called `name` goes, beside `path`; `None` when a file
/// of that name is already in the project.
pub(super) fn new_file_beside(
    context: &Context<'_, '_>,
    path: &Path,
    name: &str,
) -> Option<PathBuf> {
    let directory = path.parent().map(PathBuf::from).unwrap_or_default();
    let target = directory.join(format!("{name}.cs"));
    let exists = context.view.project().tree_index(&target).is_some() || target.exists();
    (!exists).then_some(target)
}

/// A file holding `declaration`, a type written without indentation with
/// `\n` line breaks: under the `usings`, in the namespaces `beside` is in,
/// laid out as the file `text` lays out its own.
pub(super) fn new_file(
    text: &str,
    beside: &SyntaxNode,
    usings: &[String],
    declaration: &str,
) -> String {
    let nl = newline(text);
    let unit = indent_unit(text);
    let mut out = String::new();
    for using in usings {
        out.push_str(using);
        out.push_str(nl);
    }
    if !usings.is_empty() {
        out.push_str(nl);
    }
    let namespaces: Vec<SyntaxNode> = beside
        .ancestors()
        .filter(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
            )
        })
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();
    let mut depth = 0usize;
    let mut closing = String::new();
    for namespace in &namespaces {
        let Some(name) = namespace
            .children()
            .find(|child| child.kind().is_type_node())
        else {
            continue;
        };
        let indent = unit.repeat(depth);
        if namespace.kind() == SyntaxKind::FileScopedNamespaceDeclaration {
            out.push_str(&format!("namespace {};{nl}{nl}", name.text()));
        } else {
            out.push_str(&format!(
                "{indent}namespace {}{nl}{indent}{{{nl}",
                name.text()
            ));
            closing = format!("{nl}{indent}}}{closing}");
            depth += 1;
        }
    }
    let indent = unit.repeat(depth);
    let body: Vec<String> = declaration
        .split('\n')
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                let spaces = line.len() - line.trim_start_matches(' ').len();
                format!(
                    "{indent}{}{}",
                    unit.repeat(spaces / 4),
                    &line[spaces - spaces % 4..]
                )
            }
        })
        .collect();
    out.push_str(&body.join(nl));
    out.push_str(&closing);
    out.push_str(nl);
    out
}

/// A type written without indentation, `\n` line breaks, inserted before
/// `before` in the same file, at its indentation, with a blank line after.
pub(super) fn insert_type_before(text: &str, before: &SyntaxNode, declaration: &str) -> TextEdit {
    let nl = newline(text);
    let unit = indent_unit(text);
    let start = member_start(before);
    let at = line_start(text, start);
    let indent = indentation_at(text, start);
    let body: Vec<String> = declaration
        .split('\n')
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                let spaces = line.len() - line.trim_start_matches(' ').len();
                format!(
                    "{indent}{}{}",
                    unit.repeat(spaces / 4),
                    &line[spaces - spaces % 4..]
                )
            }
        })
        .collect();
    TextEdit::insert(at, format!("{}{nl}{nl}", body.join(nl)))
}

/// The `using` directives of the file `root` is the tree of that the code
/// in `nodes` needs: those that bring in a namespace a name in it is from,
/// and aliases it uses. In the order the file has them.
pub(super) fn needed_usings(
    context: &mut Context<'_, '_>,
    root: &SyntaxNode,
    nodes: &[SyntaxNode],
) -> Vec<String> {
    let mut namespaces: HashSet<String> = HashSet::new();
    let mut words: HashSet<String> = HashSet::new();
    let tokens: Vec<SyntaxToken> = nodes
        .iter()
        .flat_map(|node| node.descendant_tokens().collect::<Vec<_>>())
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
        .collect();
    for token in tokens {
        words.insert(token.value_text().to_string());
        let Some(crate::semantic::Resolved::Symbol(symbol)) = context.view.resolve(&token) else {
            continue;
        };
        let symbols = context.view.compiled().symbols();
        // The namespace of the outermost type the name is in, or of the
        // name itself when it is a member.
        let mut current = Some(symbol);
        while let Some(id) = current {
            let found = symbols.get(id);
            if found.kind == SymbolKind::Namespace {
                namespaces.insert(symbols.qualified_name(id));
                break;
            }
            current = found.container;
        }
    }
    root.descendants()
        .filter(|node| node.kind() == SyntaxKind::UsingDirective)
        .filter(|using| {
            if let Some(alias) = using.child_of_kind(SyntaxKind::NameEquals) {
                return alias
                    .descendant_tokens()
                    .any(|token| words.contains(token.value_text()));
            }
            if using
                .child_token_of_kind(SyntaxKind::StaticKeyword)
                .is_some()
            {
                return false;
            }
            using
                .children()
                .find(|child| child.kind().is_type_node())
                .is_some_and(|name| namespaces.contains(&name.text().replace(' ', "")))
        })
        .map(|using| using.text())
        .collect()
}

/// The edits adding to the file `destination` is in (its tree `root`, its
/// text `text`) the `using`s the file asked about has for the code in
/// `nodes`, which is moving there. A namespace the destination is already
/// inside needs none.
pub(super) fn usings_for_move(
    context: &mut Context<'_, '_>,
    nodes: &[SyntaxNode],
    root: &SyntaxNode,
    text: &str,
    destination: &SyntaxNode,
) -> Vec<TextEdit> {
    let source_root = context.view.syntax_root().clone();
    let inside: Vec<String> = destination
        .ancestors()
        .filter(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
            )
        })
        .filter_map(|namespace| {
            namespace
                .children()
                .find(|child| child.kind().is_type_node())
                .map(|name| name.text().replace(' ', ""))
        })
        .collect();
    let mut edits: Vec<TextEdit> = Vec::new();
    for using in needed_usings(context, &source_root, nodes) {
        let name = using
            .trim()
            .trim_start_matches("using")
            .trim()
            .trim_end_matches(';')
            .trim()
            .to_string();
        if name.contains('=')
            || inside
                .iter()
                .any(|namespace| namespace == &name || namespace.starts_with(&format!("{name}.")))
        {
            continue;
        }
        if let Some(edit) = super::super::fixes::support::add_using(root, text, &name) {
            // Two usings added at one place go in the order they come.
            match edits.iter_mut().find(|other| other.span == edit.span) {
                Some(other) => other.text.push_str(&edit.text),
                None => edits.push(edit),
            }
        }
    }
    edits
}

/// `public ` when the type is public, `internal ` when it says so, nothing
/// otherwise: the accessibility a type extracted from `declaration` gets.
pub(super) fn type_accessibility(declaration: &SyntaxNode) -> &'static str {
    if has_modifier(declaration, SyntaxKind::PublicKeyword) {
        "public "
    } else if has_modifier(declaration, SyntaxKind::InternalKeyword) {
        "internal "
    } else {
        ""
    }
}

/// Whether a type called `name` is already declared in the namespace the
/// type `declaration` is in, or nested beside it.
pub(super) fn name_is_taken(
    context: &Context<'_, '_>,
    declaration: &SyntaxNode,
    name: &str,
) -> bool {
    let Some(symbol) = context.view.declared(declaration) else {
        return false;
    };
    let symbols = context.view.compiled().symbols();
    let Some(container) = symbols.get(symbol).container else {
        return false;
    };
    symbols
        .get(container)
        .members
        .iter()
        .any(|&member| symbols.get(member).name == name)
}
