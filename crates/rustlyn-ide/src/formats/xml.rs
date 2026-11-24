//! XML, two ways.
//!
//! * [`Reader`] reads the XML MSBuild writes — project files, `.props`,
//!   `.slnx` — as a flat list of start tags, each with the text it holds and
//!   the `Condition`s it is under. Nothing is validated; a project file that
//!   MSBuild would reject is still read as far as it makes sense.
//! * [`Document`] is a tree for files that are edited and written back, like
//!   `NuGet.Config`: strict like `XMLDocument` (an unclosed tag, a stray
//!   closing tag, an unquoted attribute or an unknown entity is a refusal),
//!   whitespace between elements dropped and re-indented on writing,
//!   comments kept where they were. No namespaces, no DTD entities, UTF-8
//!   only.

use std::fmt::Write as _;

// MARK: - reading MSBuild

/// An element: its name, attributes, and its text when it holds nothing but.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tag<'a> {
    pub name: &'a str,
    pub attributes: Vec<(&'a str, String)>,
    pub text: Option<String>,
    /// The `Condition`s on it and on the elements around it: what it says
    /// holds only when all of them do.
    pub conditions: Vec<String>,
}

impl Tag<'_> {
    #[must_use]
    pub fn attribute(&self, name: &str) -> Option<&str> {
        self.attributes
            .iter()
            .find(|(key, _)| *key == name)
            .map(|(_, value)| value.as_str())
    }
}

/// A reader for the XML MSBuild writes, which is regular enough that every
/// element can be read as a start tag and, when what follows is text, that
/// text. Of where an element is, only the conditions around it are kept.
#[derive(Debug, Clone, Copy)]
pub struct Reader<'a> {
    text: &'a str,
}

impl<'a> Reader<'a> {
    #[must_use]
    pub const fn new(text: &'a str) -> Self {
        Self { text }
    }

    /// Every start tag, in order.
    #[must_use]
    pub fn elements(&self) -> Vec<Tag<'a>> {
        let text = self.text;
        let mut elements = Vec::new();
        // The elements open around the one being read, each with the
        // conditions it holds under, its own and those around it.
        let mut open_elements: Vec<(&str, Vec<String>)> = Vec::new();
        let mut at = 0;
        while let Some(open) = text[at..].find('<').map(|offset| at + offset) {
            let rest = &text[open + 1..];
            if rest.starts_with("!--") {
                at = text[open..]
                    .find("-->")
                    .map_or(text.len(), |end| open + end + 3);
                continue;
            }
            if let Some(closing) = rest.strip_prefix('/') {
                let name_end = closing
                    .find(|c: char| c == '>' || c.is_whitespace())
                    .unwrap_or(closing.len());
                if let Some(index) = open_elements
                    .iter()
                    .rposition(|(name, _)| *name == &closing[..name_end])
                {
                    open_elements.truncate(index);
                }
                at = open + 1;
                continue;
            }
            if rest.starts_with('?') || rest.starts_with('!') {
                at = open + 1;
                continue;
            }
            let Some(close) = tag_end(rest) else {
                break;
            };
            let tag = &rest[..close];
            let self_closing = tag.ends_with('/');
            let tag = tag.trim_end_matches('/');
            let name_end = tag.find(|c: char| c.is_whitespace()).unwrap_or(tag.len());
            let name = &tag[..name_end];
            let attributes = attributes(&tag[name_end..]);
            let after = open + 1 + close + 1;
            let mut element_text = None;
            if !self_closing {
                let closing = format!("</{name}>");
                if let Some(end) = text[after..].find(&closing) {
                    let inner = &text[after..after + end];
                    if !inner.contains('<') {
                        element_text = Some(unescape(inner));
                    }
                }
            }
            let mut conditions = open_elements
                .last()
                .map(|(_, conditions)| conditions.clone())
                .unwrap_or_default();
            conditions.extend(
                attributes
                    .iter()
                    .filter(|(key, _)| *key == "Condition")
                    .map(|(_, value)| value.clone()),
            );
            if !self_closing {
                open_elements.push((name, conditions.clone()));
            }
            elements.push(Tag {
                name,
                attributes,
                text: element_text,
                conditions,
            });
            at = after;
        }
        elements
    }
}

/// Where a start tag ends, skipping `>` inside quoted attribute values —
/// MSBuild conditions are full of them.
pub fn tag_end(rest: &str) -> Option<usize> {
    let mut quote = None;
    for (index, c) in rest.char_indices() {
        match (quote, c) {
            (None, '"' | '\'') => quote = Some(c),
            (Some(open), _) if c == open => quote = None,
            (None, '>') => return Some(index),
            _ => {}
        }
    }
    None
}

/// The `name="value"` pairs of a start tag, values unescaped.
#[must_use]
pub fn attributes(text: &str) -> Vec<(&str, String)> {
    let mut found = Vec::new();
    let mut rest = text;
    while let Some(equals) = rest.find('=') {
        let name = rest[..equals].trim();
        let after = rest[equals + 1..].trim_start();
        let Some(quote) = after.chars().next().filter(|c| *c == '"' || *c == '\'') else {
            break;
        };
        let Some(end) = after[1..].find(quote) else {
            break;
        };
        found.push((name, unescape(&after[1..=end])));
        rest = &after[end + 2..];
    }
    found
}

/// The five predefined entities replaced.
#[must_use]
pub fn unescape(text: &str) -> String {
    text.replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&amp;", "&")
}

// MARK: - a tree to edit and write back

/// A node of a [`Document`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Element(Element),
    Text(String),
    Comment(String),
}

/// An element of a [`Document`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Element {
    pub name: String,
    pub attributes: Vec<(String, String)>,
    pub children: Vec<Node>,
}

impl Element {
    pub fn new(name: &str) -> Self {
        Element {
            name: name.to_string(),
            ..Default::default()
        }
    }

    pub fn attribute(&self, name: &str) -> Option<&str> {
        self.attributes
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v.as_str())
    }

    /// Changes the value of an attribute that is there; adds none.
    pub fn set_existing_attribute(&mut self, name: &str, value: &str) {
        if let Some(slot) = self.attributes.iter_mut().find(|(n, _)| n == name) {
            slot.1 = value.to_string();
        }
    }

    pub fn with_attribute(mut self, name: &str, value: &str) -> Self {
        self.attributes.push((name.to_string(), value.to_string()));
        self
    }

    /// The child elements, without text and comments.
    pub fn elements(&self) -> impl Iterator<Item = &Element> {
        self.children.iter().filter_map(|n| {
            if let Node::Element(e) = n {
                Some(e)
            } else {
                None
            }
        })
    }

    pub fn elements_named<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a Element> {
        self.elements().filter(move |e| e.name == name)
    }

    /// The index, among all children, of the first child element that passes `test`.
    pub fn position(&self, test: impl Fn(&Element) -> bool) -> Option<usize> {
        self.children
            .iter()
            .position(|n| matches!(n, Node::Element(e) if test(e)))
    }

    pub fn element_at(&mut self, index: usize) -> &mut Element {
        match &mut self.children[index] {
            Node::Element(e) => e,
            _ => panic!("element_at({index}): not an element; take indices from `position`"),
        }
    }

    /// Removes the child elements that pass `test`.
    pub fn remove_elements(&mut self, test: impl Fn(&Element) -> bool) {
        self.children
            .retain(|n| !matches!(n, Node::Element(e) if test(e)));
    }

    pub fn push(&mut self, element: Element) {
        self.children.push(Node::Element(element));
    }
}

/// A whole document: what comes before the root, and the root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Document {
    /// The comments before the root.
    pub prolog: Vec<Node>,
    pub root: Element,
}

impl Document {
    pub fn new(root: &str) -> Self {
        Document {
            prolog: Vec::new(),
            root: Element::new(root),
        }
    }

    pub fn parse(data: &[u8]) -> Option<Document> {
        let data = data.strip_prefix(b"\xEF\xBB\xBF").unwrap_or(data);
        let text = std::str::from_utf8(data).ok()?;
        let mut parser = Parser { text, i: 0 };
        let mut prolog = Vec::new();
        parser.misc(&mut prolog)?;
        if !parser.rest().starts_with('<') {
            return None;
        }
        let root = parser.element(0)?;
        let mut trailing = Vec::new();
        parser.misc(&mut trailing)?;
        (parser.i == text.len()).then_some(Document { prolog, root })
    }

    /// With an XML declaration, two-space indentation, and `<x />` for an
    /// empty element.
    pub fn to_text(&self) -> String {
        let mut out = String::from("<?xml version=\"1.0\" encoding=\"utf-8\"?>\n");
        for node in &self.prolog {
            write_node(node, 0, &mut out);
        }
        write_element(&self.root, 0, &mut out);
        out
    }
}

fn write_node(node: &Node, depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    match node {
        Node::Element(e) => write_element(e, depth, out),
        Node::Text(t) => {
            let _ = writeln!(out, "{indent}{}", escape(t.trim(), false));
        }
        Node::Comment(c) => {
            let _ = writeln!(out, "{indent}<!--{c}-->");
        }
    }
}

fn write_element(e: &Element, depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    out.push_str(&indent);
    out.push('<');
    out.push_str(&e.name);
    for (name, value) in &e.attributes {
        let _ = write!(out, " {name}=\"{}\"", escape(value, true));
    }
    match e.children.as_slice() {
        [] => out.push_str(" />\n"),
        [Node::Text(t)] => {
            let _ = writeln!(out, ">{}</{}>", escape(t, false), e.name);
        }
        children => {
            out.push_str(">\n");
            for child in children {
                write_node(child, depth + 1, out);
            }
            let _ = writeln!(out, "{indent}</{}>", e.name);
        }
    }
}

fn escape(text: &str, attribute: bool) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' if attribute => out.push_str("&quot;"),
            '\n' if attribute => out.push_str("&#10;"),
            c => out.push(c),
        }
    }
    out
}

struct Parser<'a> {
    text: &'a str,
    i: usize,
}

impl Parser<'_> {
    fn rest(&self) -> &str {
        &self.text[self.i..]
    }

    fn skip_space(&mut self) {
        let rest = self.rest();
        self.i += rest.len() - rest.trim_start_matches([' ', '\t', '\r', '\n']).len();
    }

    /// Declarations, processing instructions, comments and a DOCTYPE outside
    /// the root.
    fn misc(&mut self, out: &mut Vec<Node>) -> Option<()> {
        loop {
            self.skip_space();
            let rest = self.rest();
            if rest.starts_with("<?") {
                self.i += rest.find("?>")? + 2;
            } else if rest.starts_with("<!--") {
                out.push(Node::Comment(self.comment()?));
            } else if rest.starts_with("<!DOCTYPE") {
                // No internal subset: the files this is for never have one.
                if rest[..rest.find('>')?].contains('[') {
                    return None;
                }
                self.i += rest.find('>')? + 1;
            } else {
                return Some(());
            }
        }
    }

    fn comment(&mut self) -> Option<String> {
        let body_start = self.i + 4;
        let end = self.text[body_start..].find("-->")? + body_start;
        self.i = end + 3;
        Some(self.text[body_start..end].to_string())
    }

    fn name(&mut self) -> Option<String> {
        let rest = self.rest();
        let length = rest
            .find(|c: char| c.is_whitespace() || matches!(c, '/' | '>' | '=' | '<'))
            .unwrap_or(rest.len());
        if length == 0 {
            return None;
        }
        let name = rest[..length].to_string();
        let first = name.chars().next()?;
        if !(first.is_alphabetic() || first == '_' || first == ':') {
            return None;
        }
        self.i += length;
        Some(name)
    }

    fn element(&mut self, depth: usize) -> Option<Element> {
        if depth > 256 {
            return None;
        }
        self.i += 1; // <
        let mut element = Element::new(&self.name()?);
        loop {
            self.skip_space();
            let rest = self.rest();
            if rest.starts_with("/>") {
                self.i += 2;
                return Some(element);
            }
            if rest.starts_with('>') {
                self.i += 1;
                break;
            }
            let name = self.name()?;
            self.skip_space();
            if !self.rest().starts_with('=') {
                return None;
            }
            self.i += 1;
            self.skip_space();
            let quote = self
                .rest()
                .chars()
                .next()
                .filter(|&c| c == '"' || c == '\'')?;
            let start = self.i + 1;
            let end = self.text[start..].find(quote)? + start;
            let value = decode_entities(&self.text[start..end])?;
            self.i = end + 1;
            if element.attribute(&name).is_some() {
                return None;
            }
            element.attributes.push((name, value));
        }
        // The content, up to the closing tag.
        let mut text = String::new();
        loop {
            let rest = self.rest();
            if rest.is_empty() {
                return None;
            }
            if rest.starts_with("</") {
                flush_text(&mut text, &mut element);
                self.i += 2;
                if self.name()? != element.name {
                    return None;
                }
                self.skip_space();
                if !self.rest().starts_with('>') {
                    return None;
                }
                self.i += 1;
                return Some(element);
            }
            if rest.starts_with("<!--") {
                flush_text(&mut text, &mut element);
                let comment = self.comment()?;
                element.children.push(Node::Comment(comment));
            } else if rest.starts_with("<![CDATA[") {
                let start = self.i + 9;
                let end = self.text[start..].find("]]>")? + start;
                text.push_str(&self.text[start..end]);
                self.i = end + 3;
            } else if rest.starts_with("<?") {
                self.i += rest.find("?>")? + 2;
            } else if rest.starts_with('<') {
                flush_text(&mut text, &mut element);
                let child = self.element(depth + 1)?;
                element.push(child);
            } else {
                let length = rest.find('<').unwrap_or(rest.len());
                text.push_str(&decode_entities(&rest[..length])?);
                self.i += length;
            }
        }
    }
}

/// The text gathered so far as a node; whitespace between elements is dropped.
fn flush_text(text: &mut String, element: &mut Element) {
    if !text.trim().is_empty() {
        element.children.push(Node::Text(std::mem::take(text)));
    }
    text.clear();
}

fn decode_entities(text: &str) -> Option<String> {
    if !text.contains('&') {
        return Some(text.to_string());
    }
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find('&') {
        out.push_str(&rest[..at]);
        let end = rest[at..].find(';')? + at;
        let entity = &rest[at + 1..end];
        let c = match entity {
            "amp" => '&',
            "lt" => '<',
            "gt" => '>',
            "quot" => '"',
            "apos" => '\'',
            _ if entity.starts_with("#x") => {
                char::from_u32(u32::from_str_radix(&entity[2..], 16).ok()?)?
            }
            _ if entity.starts_with('#') => char::from_u32(entity[1..].parse().ok()?)?,
            _ => return None,
        };
        out.push(c);
        rest = &rest[end + 1..];
    }
    out.push_str(rest);
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attributes_may_hold_angle_brackets() {
        let elements =
            Reader::new(r#"<A Condition="'$(X)' &gt; '1' and 2 > 1"><B>text &amp; more</B></A>"#)
                .elements();
        assert_eq!(elements.len(), 2);
        assert_eq!(
            elements[0].attribute("Condition"),
            Some("'$(X)' > '1' and 2 > 1")
        );
        assert_eq!(elements[1].text.as_deref(), Some("text & more"));
        assert_eq!(elements[1].conditions, ["'$(X)' > '1' and 2 > 1"]);
    }

    #[test]
    fn parse_and_write() {
        let text = "<?xml version=\"1.0\"?>\n<!-- top -->\n<configuration>\n  <a key=\"x &amp; y\" value='1'/>\n  <!-- c -->\n  <b>text</b>\n</configuration>\n";
        let doc = Document::parse(text.as_bytes()).unwrap();
        assert_eq!(doc.root.elements().count(), 2);
        assert_eq!(
            doc.root
                .elements_named("a")
                .next()
                .unwrap()
                .attribute("key"),
            Some("x & y")
        );
        let written = doc.to_text();
        assert_eq!(
            written,
            "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<!-- top -->\n<configuration>\n  <a key=\"x &amp; y\" value=\"1\" />\n  <!-- c -->\n  <b>text</b>\n</configuration>\n"
        );
        assert_eq!(
            Document::parse(written.as_bytes()),
            Some(doc),
            "what is written reads back as the same tree"
        );
        for broken in [
            "not xml",
            "<a>",
            "<a></b>",
            "<a x=1/>",
            "<a>&nbsp;</a>",
            "<a/><b/>",
            "",
        ] {
            assert!(Document::parse(broken.as_bytes()).is_none(), "{broken}");
        }
    }
}
