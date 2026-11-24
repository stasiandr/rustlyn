//! Completion inside `///` comments: Roslyn's
//! `XmlDocCommentCompletionProvider`. The tags a documentation comment can
//! hold, each written with its end tag and the cursor between; `param` and
//! `typeparam` once for each parameter the comment has not described yet;
//! the parameter names inside `name="…"`; what is in scope inside
//! `cref="…"`.
//!
//! Which tags depend on where in the comment: at the top level the
//! sections (`summary`, `param`, `returns`), inside one of them the inline
//! tags (`c`, `paramref`, `see`, `para`).

use std::collections::HashSet;

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode};

use super::context::Site;
use super::{Completion, CompletionKind, View};

/// Tags that hold a section of the documentation.
const TOP_LEVEL: &[&str] = &[
    "summary",
    "remarks",
    "example",
    "exception",
    "include",
    "inheritdoc",
    "permission",
    "seealso",
    "completionlist",
];

/// Tags that go inside a section's text.
const INLINE: &[&str] = &[
    "c",
    "code",
    "para",
    "list",
    "see",
    "seealso",
    "paramref",
    "typeparamref",
    "b",
    "i",
    "br",
    "inheritdoc",
];

/// Tags that take no content.
const EMPTY: &[&str] = &[
    "br",
    "inheritdoc",
    "include",
    "see",
    "seealso",
    "paramref",
    "typeparamref",
];

/// Sections that appear once.
const ONCE: &[&str] = &["summary", "remarks", "returns", "value", "example"];

pub(super) fn complete(view: &mut View<'_>, text: &str, site: &Site, items: &mut Vec<Completion>) {
    let Some((comment_start, owner)) = comment_of(&view.root, site.start) else {
        return;
    };
    let before = &text[comment_start as usize..site.start as usize];
    // To the end of the last `///` line of this comment.
    let mut comment_end = site.start as usize;
    for line in text[comment_end..].split_inclusive('\n').enumerate() {
        let (index, line) = line;
        if index > 0 && !line.trim_start().starts_with("///") {
            break;
        }
        comment_end += line.len();
    }
    let whole = &text[comment_start as usize..comment_end];
    let declaration = owner;
    let parameters = names_of(declaration.as_ref(), K::ParameterList, K::Parameter);
    let type_parameters = names_of(declaration.as_ref(), K::TypeParameterList, K::TypeParameter);

    // Inside an attribute's quotes.
    if let Some((tag, attribute)) = open_attribute(before) {
        match attribute.as_str() {
            "name" => {
                let names = match tag.as_str() {
                    "param" | "paramref" => &parameters,
                    "typeparam" | "typeparamref" => &type_parameters,
                    _ => return,
                };
                let documented = documented(whole, &tag);
                for name in names {
                    if tag.ends_with("ref") || !documented.contains(name) {
                        items.push(Completion {
                            label: name.clone(),
                            kind: if tag.starts_with("type") {
                                CompletionKind::TypeParameter
                            } else {
                                CompletionKind::Parameter
                            },
                            rank: 0,
                            ..Completion::default()
                        });
                    }
                }
            }
            "cref" => {
                let anchor = declaration
                    .as_ref()
                    .map_or(site.start, |node| node.span().start());
                view.scope_completions(anchor, items);
                items.retain(|item| item.kind != CompletionKind::Local);
            }
            "langword" => {
                for word in [
                    "null", "true", "false", "static", "virtual", "abstract", "async", "await",
                ] {
                    items.push(Completion::keyword(word));
                }
            }
            _ => {}
        }
        return;
    }

    let after_open = before.ends_with('<');
    let after_close = before.ends_with("</");
    let open = open_tags(before);
    if after_close {
        // `</` closes the innermost open tag.
        if let Some(innermost) = open.last() {
            items.push(Completion {
                label: innermost.clone(),
                kind: CompletionKind::Keyword,
                insert_text: Some(format!("{innermost}>")),
                ..Completion::default()
            });
        }
        return;
    }
    // Inside a tag's name or attributes, but not straight after `<`: nothing.
    if !after_open && in_tag(before) {
        return;
    }
    let prefix = if after_open { "" } else { "<" };

    if open.is_empty() {
        let written = documented_tags(whole);
        let is_method = declaration.as_ref().is_some_and(|node| {
            matches!(
                node.kind(),
                K::MethodDeclaration
                    | K::DelegateDeclaration
                    | K::OperatorDeclaration
                    | K::ConversionOperatorDeclaration
                    | K::LocalFunctionStatement
            )
        });
        let returns_value = is_method
            && declaration.as_ref().is_some_and(|node| {
                node.children()
                    .find(|child| child.kind().is_type_node())
                    .is_some_and(|ty| ty.text().trim() != "void")
            });
        let is_property = declaration.as_ref().is_some_and(|node| {
            matches!(node.kind(), K::PropertyDeclaration | K::IndexerDeclaration)
        });
        let mut tags: Vec<&str> = TOP_LEVEL.to_vec();
        if returns_value {
            tags.push("returns");
        }
        if is_property {
            tags.push("value");
        }
        for tag in tags {
            if ONCE.contains(&tag) && written.contains(tag) {
                continue;
            }
            items.push(tag_item(tag, prefix));
        }
        let documented_parameters = documented(whole, "param");
        for name in &parameters {
            if !documented_parameters.contains(name) {
                items.push(named_item("param", name, prefix));
            }
        }
        let documented_types = documented(whole, "typeparam");
        for name in &type_parameters {
            if !documented_types.contains(name) {
                items.push(named_item("typeparam", name, prefix));
            }
        }
    } else {
        let inside_list = open
            .last()
            .is_some_and(|tag| tag == "list" || tag == "listheader");
        let inside_item = open.last().is_some_and(|tag| tag == "item");
        if inside_list {
            for tag in ["listheader", "item"] {
                items.push(tag_item(tag, prefix));
            }
        } else if inside_item {
            for tag in ["term", "description"] {
                items.push(tag_item(tag, prefix));
            }
        }
        for tag in INLINE {
            items.push(tag_item(tag, prefix));
        }
        for name in &parameters {
            items.push(Completion {
                label: format!("paramref name=\"{name}\""),
                kind: CompletionKind::Keyword,
                insert_text: Some(format!("{prefix}paramref name=\"{name}\"/>")),
                filter_text: Some("paramref".to_string()),
                ..Completion::default()
            });
        }
    }
}

/// The item for a tag: `summary>|</summary>` after `<`, the whole element
/// otherwise.
fn tag_item(tag: &str, prefix: &str) -> Completion {
    let (text, caret) = match tag {
        "see" | "seealso" => {
            let head = format!("{prefix}{tag} cref=\"");
            let caret = head.len();
            (format!("{head}\"/>"), caret)
        }
        "exception" => {
            let head = format!("{prefix}{tag} cref=\"");
            let caret = head.len();
            (format!("{head}\"></{tag}>"), caret)
        }
        "list" => {
            let head = format!("{prefix}{tag} type=\"");
            let caret = head.len();
            (format!("{head}bullet\"></{tag}>"), caret)
        }
        "include" => {
            let head = format!("{prefix}{tag} file=\"");
            let caret = head.len();
            (format!("{head}\" path=\"\"/>"), caret)
        }
        tag if EMPTY.contains(&tag) => {
            let text = format!("{prefix}{tag}/>");
            let caret = text.len();
            (text, caret)
        }
        _ => {
            let head = format!("{prefix}{tag}>");
            let caret = head.len();
            (format!("{head}</{tag}>"), caret)
        }
    };
    Completion {
        label: tag.to_string(),
        kind: CompletionKind::Keyword,
        insert_text: Some(text),
        caret: Some(caret as u32),
        filter_text: Some(tag.to_string()),
        ..Completion::default()
    }
}

/// `param name="x"`, written whole.
fn named_item(tag: &str, name: &str, prefix: &str) -> Completion {
    let head = format!("{prefix}{tag} name=\"{name}\">");
    let caret = head.len();
    Completion {
        label: format!("{tag} name=\"{name}\""),
        kind: CompletionKind::Keyword,
        insert_text: Some(format!("{head}</{tag}>")),
        caret: Some(caret as u32),
        filter_text: Some(tag.to_string()),
        ..Completion::default()
    }
}

/// Where the documentation comment around `offset` starts — its first
/// `///` line — and the declaration it documents.
fn comment_of(root: &SyntaxNode, offset: u32) -> Option<(u32, Option<SyntaxNode>)> {
    let token = root.find_token(offset)?;
    let mut candidates: Vec<(rustlyn_syntax::SyntaxTrivia, Option<SyntaxNode>)> = token
        .leading_trivia()
        .into_iter()
        .map(|trivia| (trivia, declaration_of(&token)))
        .collect();
    if let Some(before) = offset.checked_sub(1).and_then(|at| root.find_token(at)) {
        candidates.extend(
            before
                .leading_trivia()
                .into_iter()
                .map(|trivia| (trivia, declaration_of(&before))),
        );
        // A comment at the end of the file hangs off the token before it.
        candidates.extend(
            before
                .trailing_trivia()
                .into_iter()
                .map(|trivia| (trivia, None)),
        );
    }
    let mut start = None;
    let mut owner = None;
    for (trivia, declaration) in &candidates {
        let span = trivia.span();
        if matches!(
            trivia.kind(),
            K::SingleLineDocumentationCommentTrivia | K::MultiLineDocumentationCommentTrivia
        ) && span.start() < offset
            && offset <= span.end()
        {
            start = Some(span.start());
            owner.clone_from(declaration);
        }
    }
    let start = start?;
    // Earlier `///` lines of the same comment are trivia of their own.
    let mut first = start;
    for (trivia, _) in &candidates {
        if trivia.kind() == K::SingleLineDocumentationCommentTrivia && trivia.span().start() < first
        {
            first = trivia.span().start();
        }
    }
    Some((first, owner))
}

/// The declaration a token starts, if it starts one.
fn declaration_of(token: &rustlyn_syntax::SyntaxToken) -> Option<SyntaxNode> {
    std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| {
            node.kind().is_declaration_node() && node.kind() != K::CompilationUnit
                || node.kind() == K::LocalFunctionStatement
        })
        .filter(|node| {
            node.first_token()
                .is_some_and(|first| first.span() == token.span())
        })
}

/// The identifiers of a declaration's parameters or type parameters.
fn names_of(declaration: Option<&SyntaxNode>, list: K, item: K) -> Vec<String> {
    let Some(declaration) = declaration else {
        return Vec::new();
    };
    let lists = declaration.children().filter(|child| child.kind() == list);
    lists
        .flat_map(|list| list.children().collect::<Vec<_>>())
        .filter(|child| child.kind() == item)
        .filter_map(|child| {
            child
                .child_token_of_kind(K::IdentifierToken)
                .map(|token| token.value_text().to_string())
        })
        .collect()
}

/// The names `<tag name="…"` already describes in `comment`.
fn documented(comment: &str, tag: &str) -> HashSet<String> {
    let mut found = HashSet::new();
    let open = format!("<{tag} ");
    let mut rest = comment;
    while let Some(at) = rest.find(&open) {
        rest = &rest[at + open.len()..];
        let Some(quote) = rest.find("name=\"") else {
            break;
        };
        let value = &rest[quote + 6..];
        if let Some(end) = value.find('"') {
            found.insert(value[..end].to_string());
        }
    }
    found
}

/// The tags opened anywhere in `comment`.
fn documented_tags(comment: &str) -> HashSet<String> {
    let mut found = HashSet::new();
    for piece in comment.split('<').skip(1) {
        let name: String = piece
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        if !name.is_empty() {
            found.insert(name);
        }
    }
    found
}

/// The tags open at the end of `before`, outermost first.
fn open_tags(before: &str) -> Vec<String> {
    let mut stack: Vec<String> = Vec::new();
    let mut rest = before;
    while let Some(at) = rest.find('<') {
        rest = &rest[at + 1..];
        let Some(end) = rest.find('>') else {
            break;
        };
        let tag = &rest[..end];
        rest = &rest[end + 1..];
        if let Some(closing) = tag.strip_prefix('/') {
            let name = closing.trim();
            if let Some(position) = stack.iter().rposition(|open| open == name) {
                stack.truncate(position);
            }
        } else if !tag.ends_with('/') {
            let name: String = tag
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect();
            if !name.is_empty() {
                stack.push(name);
            }
        }
    }
    stack
}

/// Whether the end of `before` is inside a tag's `< … >`.
fn in_tag(before: &str) -> bool {
    match (before.rfind('<'), before.rfind('>')) {
        (Some(open), Some(close)) => open > close,
        (Some(_), None) => true,
        _ => false,
    }
}

/// The tag and attribute whose quoted value the end of `before` is in:
/// `<param name="|`.
fn open_attribute(before: &str) -> Option<(String, String)> {
    let open = before.rfind('<')?;
    if before[open..].contains('>') {
        return None;
    }
    let inside = &before[open + 1..];
    if inside.matches('"').count().is_multiple_of(2) {
        return None;
    }
    let tag: String = inside
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric())
        .collect();
    let quote = inside.rfind('"')?;
    let attribute = inside[..quote].trim_end().strip_suffix('=')?.trim_end();
    let name: String = attribute
        .chars()
        .rev()
        .take_while(|c| c.is_ascii_alphanumeric())
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect();
    Some((tag, name))
}
