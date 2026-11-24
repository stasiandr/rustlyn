//! The documentation comment snippet: typing `///` above a declaration
//! writes the skeleton of its documentation. Roslyn's
//! `DocumentationCommentSnippetService`, from the parse alone.
//!
//! The skeleton is a `<summary>` with the caret inside it, then a
//! `<typeparam>` for each type parameter, a `<param>` for each parameter, a
//! `<returns>` when there is something to return, and an `<exception>` for
//! each exception the body throws by `throw new`. It fires only where Roslyn
//! fires it: on a line that holds nothing but the `///`, directly above a
//! declaration that has no documentation yet.
//!
//! Enter inside documentation carries the `/// ` on to the new line, and on
//! a line that is only `///` above a declaration it writes the whole
//! skeleton, as typing the third slash would have. The "insert comment"
//! command writes it above the declaration around the caret.

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};
use rustlyn_text::{LineIndex, TextSpan};

use crate::edit::TextEdit;

/// An edit that writes documentation, and where the caret goes after it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocCommentSnippet {
    /// Byte offsets of the text asked about.
    pub edit: TextEdit,
    /// Byte offset in the text once the edit is applied.
    pub caret: u32,
}

/// What typing the third `/` of `///` at `position` (the caret after it)
/// expands into, if anything.
#[must_use]
pub fn on_typed_slash(
    root: &SyntaxNode,
    text: &str,
    position: u32,
    newline: &str,
) -> Option<DocCommentSnippet> {
    let lines = LineIndex::new(text);
    let line_start = lines.line_start(lines.line_of(position))?;
    let before = &text[line_start as usize..position as usize];
    let indent = before.strip_suffix("///")?;
    if !indent.chars().all(|ch| ch == ' ' || ch == '\t') {
        return None;
    }
    let slashes = line_start + indent.len() as u32;
    let rest_end = end_of_line(text, position);
    if !text[position as usize..rest_end as usize].trim().is_empty() {
        return None;
    }
    let declaration = declaration_below(root, slashes, 1)?;
    let body = skeleton(&declaration, indent, newline);
    Some(DocCommentSnippet {
        caret: slashes + caret_in(indent, newline),
        edit: TextEdit::new(TextSpan::from_bounds(slashes, rest_end), body),
    })
}

/// What pressing Enter should add, with `position` the caret at the start
/// of the new line (the line break is already in `text`): `/// ` to carry
/// documentation on, or the whole skeleton after a lone `///`.
#[must_use]
pub fn on_enter(
    root: &SyntaxNode,
    text: &str,
    position: u32,
    newline: &str,
) -> Option<DocCommentSnippet> {
    let lines = LineIndex::new(text);
    let line = lines.line_of(position);
    if line == 0 {
        return None;
    }
    let line_start = lines.line_start(line)?;
    let previous_start = lines.line_start(line - 1)?;
    let previous =
        text[previous_start as usize..line_start as usize].trim_end_matches(['\n', '\r']);
    let indent_length = previous.len() - previous.trim_start().len();
    let indent = &previous[..indent_length];
    let slashes = previous_start + indent_length as u32;
    if !previous.trim_start().starts_with("///") || !is_documentation_at(root, slashes) {
        return None;
    }
    // Only when Enter was pressed after the `///`, not in front of it.
    let current_end = end_of_line(text, line_start);
    let current = &text[line_start as usize..current_end as usize];
    if current.trim_start().starts_with("///") {
        return None;
    }
    let current_indent = (current.len() - current.trim_start().len()) as u32;

    if previous.trim() == "///" && current.trim().is_empty() {
        // The new line Enter made sits between the `///` and the
        // declaration.
        if let Some(declaration) = declaration_below(root, slashes, 2) {
            let body = skeleton(&declaration, indent, newline);
            return Some(DocCommentSnippet {
                caret: slashes + caret_in(indent, newline),
                edit: TextEdit::new(TextSpan::from_bounds(slashes, current_end), body),
            });
        }
    }
    let inserted = format!("{indent}/// ");
    Some(DocCommentSnippet {
        caret: line_start + inserted.len() as u32,
        edit: TextEdit::new(TextSpan::new(line_start, current_indent), inserted),
    })
}

/// The "insert comment" command: the skeleton above the declaration around
/// `position`, when it has no documentation yet.
#[must_use]
pub fn insert_comment(
    root: &SyntaxNode,
    text: &str,
    position: u32,
    newline: &str,
) -> Option<DocCommentSnippet> {
    let token = root.find_token(position)?;
    let declaration = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| is_documentable(node.kind()))?;
    if has_documentation(&declaration) {
        return None;
    }
    let lines = LineIndex::new(text);
    let start = declaration.span().start();
    let line_start = lines.line_start(lines.line_of(start))?;
    let indent = &text[line_start as usize..start as usize];
    if !indent.chars().all(|ch| ch == ' ' || ch == '\t') {
        return None;
    }
    let body = format!(
        "{indent}{}{newline}",
        skeleton(&declaration, indent, newline)
    );
    Some(DocCommentSnippet {
        caret: line_start + indent.len() as u32 + caret_in(indent, newline),
        edit: TextEdit::insert(line_start, body),
    })
}

fn end_of_line(text: &str, offset: u32) -> u32 {
    let rest = &text[offset as usize..];
    offset + rest.find(['\n', '\r']).unwrap_or(rest.len()) as u32
}

/// Where the caret goes in a skeleton that starts at its `///`: inside the
/// summary, on its second line.
fn caret_in(indent: &str, newline: &str) -> u32 {
    ("/// <summary>".len() + newline.len() + indent.len() + "/// ".len()) as u32
}

/// Whether the trivia at `offset` is documentation, rather than `///` in a
/// string.
fn is_documentation_at(root: &SyntaxNode, offset: u32) -> bool {
    root.find_token(offset).is_some_and(|token| {
        token
            .leading_trivia()
            .into_iter()
            .chain(token.trailing_trivia())
            .any(|trivia| {
                trivia.kind() == K::SingleLineDocumentationCommentTrivia
                    && trivia.span().start() == offset
            })
    })
}

/// The declaration whose first token comes straight after the lone `///`
/// at `slashes` — at most `breaks_allowed` line breaks below it — when that
/// `///` is all the documentation it has.
fn declaration_below(root: &SyntaxNode, slashes: u32, breaks_allowed: u32) -> Option<SyntaxNode> {
    let token: SyntaxToken = root.find_token(slashes)?;
    let leading = token.leading_trivia();
    let at = leading.iter().position(|trivia| {
        trivia.kind() == K::SingleLineDocumentationCommentTrivia && trivia.span().start() == slashes
    })?;
    if leading[at].text().trim() != "///" {
        return None;
    }
    // Nothing between the `///` and the declaration but its own line break
    // and the next line's indentation; and no other documentation above.
    let mut breaks = 0;
    for trivia in &leading[at + 1..] {
        match trivia.kind() {
            K::WhitespaceTrivia => {}
            K::EndOfLineTrivia => breaks += 1,
            _ => return None,
        }
    }
    if breaks == 0
        || breaks > breaks_allowed
        || leading[..at].iter().any(|trivia| is_doc(trivia.kind()))
    {
        return None;
    }
    let start = token.span().start();
    let declaration = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .take_while(|node| node.span().start() == start)
        .find(|node| is_documentable(node.kind()))?;
    Some(declaration)
}

fn is_doc(kind: K) -> bool {
    matches!(
        kind,
        K::SingleLineDocumentationCommentTrivia | K::MultiLineDocumentationCommentTrivia
    )
}

fn has_documentation(declaration: &SyntaxNode) -> bool {
    declaration.first_token().is_some_and(|token| {
        token
            .leading_trivia()
            .iter()
            .any(|trivia| is_doc(trivia.kind()))
    })
}

fn is_documentable(kind: K) -> bool {
    matches!(
        kind,
        K::ClassDeclaration
            | K::StructDeclaration
            | K::InterfaceDeclaration
            | K::EnumDeclaration
            | K::RecordDeclaration
            | K::RecordStructDeclaration
            | K::DelegateDeclaration
            | K::EnumMemberDeclaration
            | K::FieldDeclaration
            | K::EventFieldDeclaration
            | K::MethodDeclaration
            | K::OperatorDeclaration
            | K::ConversionOperatorDeclaration
            | K::ConstructorDeclaration
            | K::DestructorDeclaration
            | K::PropertyDeclaration
            | K::EventDeclaration
            | K::IndexerDeclaration
            | K::LocalFunctionStatement
    )
}

/// The skeleton, starting at its `///` and with every later line indented
/// by `indent`.
fn skeleton(declaration: &SyntaxNode, indent: &str, newline: &str) -> String {
    let mut lines = vec![
        "/// <summary>".to_owned(),
        "/// ".to_owned(),
        "/// </summary>".to_owned(),
    ];
    for name in type_parameters(declaration) {
        lines.push(format!("/// <typeparam name=\"{name}\"></typeparam>"));
    }
    for name in parameters(declaration) {
        lines.push(format!("/// <param name=\"{name}\"></param>"));
    }
    // A property says what its value is, as Roslyn's snippet asks it to.
    if declaration.kind() == K::PropertyDeclaration {
        lines.push("/// <value></value>".to_owned());
    }
    if returns_something(declaration) {
        lines.push("/// <returns></returns>".to_owned());
    }
    for exception in thrown(declaration) {
        lines.push(format!("/// <exception cref=\"{exception}\"></exception>"));
    }
    lines.join(&format!("{newline}{indent}"))
}

fn type_parameters(declaration: &SyntaxNode) -> Vec<String> {
    declaration
        .child_of_kind(K::TypeParameterList)
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == K::TypeParameter)
                .filter_map(|parameter| {
                    parameter
                        .child_tokens()
                        .filter(|token| token.kind() == K::IdentifierToken)
                        .last()
                        .map(|name| name.text().to_owned())
                })
                .collect()
        })
        .unwrap_or_default()
}

fn parameters(declaration: &SyntaxNode) -> Vec<String> {
    declaration
        .children()
        .find(|child| matches!(child.kind(), K::ParameterList | K::BracketedParameterList))
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == K::Parameter)
                .filter_map(|parameter| {
                    parameter
                        .child_tokens()
                        .filter(|token| token.kind() == K::IdentifierToken && !token.is_missing())
                        .last()
                        .map(|name| name.text().to_owned())
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Whether a `<returns>` belongs: a method, delegate or local function that
/// does not return `void`, and every operator.
fn returns_something(declaration: &SyntaxNode) -> bool {
    match declaration.kind() {
        K::OperatorDeclaration | K::ConversionOperatorDeclaration => true,
        K::MethodDeclaration | K::DelegateDeclaration | K::LocalFunctionStatement => {
            let returned = declaration.children().find(|child| {
                child.kind() != K::AttributeList
                    && (child.kind().is_type_node() || child.kind() == K::IdentifierName)
            });
            returned.is_some_and(|returned| {
                !(returned.kind() == K::PredefinedType
                    && returned
                        .first_token()
                        .is_some_and(|token| token.kind() == K::VoidKeyword))
            })
        }
        _ => false,
    }
}

/// The types a body throws with `throw new`, each once, in order.
fn thrown(declaration: &SyntaxNode) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    for node in declaration.descendants() {
        if !matches!(node.kind(), K::ThrowStatement | K::ThrowExpression) {
            continue;
        }
        let Some(created) = node
            .children()
            .find(|child| child.kind() == K::ObjectCreationExpression)
        else {
            continue;
        };
        let Some(type_node) = created
            .children()
            .find(|child| child.kind().is_type_node() || child.kind() == K::IdentifierName)
        else {
            continue;
        };
        let name = type_node.text().trim().to_owned();
        if !name.is_empty() && !found.contains(&name) {
            found.push(name);
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_text::SourceText;

    fn parse(text: &str) -> SyntaxNode {
        rustlyn_syntax::parse(SourceText::new("A.cs", text)).root()
    }

    /// Types the third slash where `|` is (the text holds all three), and
    /// returns the text after the edit with the caret shown as `|`.
    fn typed(marked: &str) -> Option<String> {
        let position = marked.find('|').expect("a caret") as u32;
        let text = marked.replacen('|', "", 1);
        let snippet = on_typed_slash(&parse(&text), &text, position, "\n")?;
        Some(show(&text, &snippet))
    }

    fn show(text: &str, snippet: &DocCommentSnippet) -> String {
        let mut after = crate::edit::apply(text, std::slice::from_ref(&snippet.edit));
        after.insert(snippet.caret as usize, '|');
        after
    }

    #[test]
    fn a_method_gets_its_parameters_and_returns() {
        assert_eq!(
            typed("class C\n{\n    ///|\n    public int Add<T>(int a, T b) => a;\n}").as_deref(),
            Some(
                "class C\n{\n    /// <summary>\n    /// |\n    /// </summary>\n    /// <typeparam name=\"T\"></typeparam>\n    /// <param name=\"a\"></param>\n    /// <param name=\"b\"></param>\n    /// <returns></returns>\n    public int Add<T>(int a, T b) => a;\n}"
            )
        );
    }

    #[test]
    fn void_methods_and_constructors_return_nothing() {
        let method = typed("class C\n{\n    ///|\n    void M(string s) { }\n}").expect("a snippet");
        assert!(method.contains("<param name=\"s\">"));
        assert!(!method.contains("<returns>"));
        let constructor =
            typed("class C\n{\n    ///|\n    public C(int x) { }\n}").expect("a snippet");
        assert!(constructor.contains("<param name=\"x\">"));
        assert!(!constructor.contains("<returns>"));
    }

    #[test]
    fn types_delegates_properties_and_throws() {
        let class = typed("///|\npublic class Box<T, U> { }").expect("a snippet");
        assert_eq!(
            class,
            "/// <summary>\n/// |\n/// </summary>\n/// <typeparam name=\"T\"></typeparam>\n/// <typeparam name=\"U\"></typeparam>\npublic class Box<T, U> { }"
        );
        let delegate = typed("///|\ndelegate bool Check(int value);").expect("a snippet");
        assert!(delegate.contains("<param name=\"value\">") && delegate.contains("<returns>"));
        let property =
            typed("class C\n{\n    ///|\n    int P { get; set; }\n}").expect("a snippet");
        assert!(
            property
                .ends_with("/// </summary>\n    /// <value></value>\n    int P { get; set; }\n}")
        );
        let indexer =
            typed("class C\n{\n    ///|\n    int this[int i] => i;\n}").expect("a snippet");
        assert!(indexer.contains("<param name=\"i\">"));
        let throws = typed(
            "class C\n{\n    ///|\n    void M(object o)\n    {\n        if (o == null) throw new ArgumentNullException(nameof(o));\n        throw new ArgumentNullException();\n    }\n}",
        )
        .expect("a snippet");
        assert_eq!(
            throws
                .matches("<exception cref=\"ArgumentNullException\">")
                .count(),
            1
        );
    }

    #[test]
    fn it_does_not_fire_where_roslyn_does_not() {
        // Already documented.
        assert_eq!(
            typed("class C\n{\n    /// <summary>x</summary>\n    ///|\n    void M() { }\n}"),
            None
        );
        // Not directly above a declaration.
        assert_eq!(typed("class C\n{\n    ///|\n\n    void M() { }\n}"), None);
        assert_eq!(
            typed("class C\n{\n    void M()\n    {\n        ///|\n        var x = 1;\n    }\n}"),
            None
        );
        // Something else on the line.
        assert_eq!(
            typed("class C\n{\n    int x; ///|\n    void M() { }\n}"),
            None
        );
        assert_eq!(
            typed("class C\n{\n    ///| text\n    void M() { }\n}"),
            None
        );
    }

    #[test]
    fn enter_carries_documentation_on() {
        let text = "class C\n{\n    /// <summary>\n    /// Text\n\n    void M() { }\n}";
        let position = text.find("Text\n").expect("the line") as u32 + 5;
        let snippet = on_enter(&parse(text), text, position, "\n").expect("a continuation");
        assert_eq!(
            show(text, &snippet),
            "class C\n{\n    /// <summary>\n    /// Text\n    /// |\n    void M() { }\n}"
        );
        // The rest of a split line comes along after the slashes.
        let text = "class C\n{\n    /// <summary>\n    /// Te\n    xt\n    void M() { }\n}";
        let position = text.find("xt\n").expect("the line") as u32 - 4;
        let snippet = on_enter(&parse(text), text, position, "\n").expect("a continuation");
        assert!(show(text, &snippet).contains("    /// Te\n    /// |xt\n"));
        // Not after ordinary comments, and not when Enter went in before the
        // slashes.
        let text = "class C\n{\n    // note\n\n}";
        let position = text.find("note\n").expect("the line") as u32 + 5;
        assert_eq!(on_enter(&parse(text), text, position, "\n"), None);
        let text = "class C\n{\n\n    /// <summary>\n    void M() { }\n}";
        assert_eq!(on_enter(&parse(text), text, 10, "\n"), None);
    }

    #[test]
    fn enter_after_a_lone_triple_slash_expands_it() {
        let text = "class C\n{\n    ///\n\n    void M(int a) { }\n}";
        let position = text.find("///\n").expect("the line") as u32 + 4;
        let snippet = on_enter(&parse(text), text, position, "\n").expect("a snippet");
        assert_eq!(
            show(text, &snippet),
            "class C\n{\n    /// <summary>\n    /// |\n    /// </summary>\n    /// <param name=\"a\"></param>\n    void M(int a) { }\n}"
        );
    }

    #[test]
    fn the_insert_comment_command() {
        let text = "class C\n{\n    [Obsolete]\n    public void Run(int times)\n    {\n        Go();\n    }\n}";
        let position = text.find("Go()").expect("the body") as u32;
        let snippet = insert_comment(&parse(text), text, position, "\r\n").expect("a snippet");
        let shown = show(text, &snippet);
        assert!(
            shown.starts_with("class C\n{\n    /// <summary>\r\n    /// |\r\n    /// </summary>\r\n    /// <param name=\"times\"></param>\r\n    [Obsolete]\n"),
            "{shown}"
        );
        // Documented already: nothing.
        let text = "/// <summary>x</summary>\nclass C { }";
        assert_eq!(insert_comment(&parse(text), text, 30, "\n"), None);
    }
}
