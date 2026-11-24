//! JSON: one reader and one writer, with no dependencies.
//!
//! Reading follows `JSONSerialization` on Apple platforms, which is what most
//! of the files a .NET or Unity project holds were checked against: a byte
//! order mark in front is skipped (Unity writes one on an `.asmdef` made in
//! its editor), a repeated key keeps its last value ([`Json::get`] searches
//! from the end), an unknown escape or anything after the value is a refusal.
//! A number with no point and no exponent is an [`Json::Int`], any other a
//! [`Json::Float`]. Objects keep their keys in order.
//!
//! Writing takes a [`Format`]: compact or indented, keys as they are or
//! sorted, `/` escaped or not. Indented output is byte for byte what
//! `JSONSerialization` writes with `.prettyPrinted`: two spaces,
//! `"key" : value`, an empty container over three lines.

use std::fmt::Write as _;

/// A JSON value.
#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Array(Vec<Json>),
    /// Keys in the order they came. A repeated key keeps its last value:
    /// [`Json::get`] searches from the end.
    Object(Vec<(String, Json)>),
}

/// How to write a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Format {
    /// Two-space indentation and ` : ` between a key and its value.
    pub pretty: bool,
    /// Keys sorted by their bytes rather than in the object's order.
    pub sorted_keys: bool,
    /// `/` written as `\/`.
    pub escape_slashes: bool,
}

impl Format {
    /// Compact, keys in the object's order, `/` as it is: request bodies.
    pub const COMPACT: Self = Self {
        pretty: false,
        sorted_keys: false,
        escape_slashes: false,
    };
    /// Compact with sorted keys.
    pub const SORTED: Self = Self {
        pretty: false,
        sorted_keys: true,
        escape_slashes: false,
    };
    /// Indented with sorted keys: files people read and diff.
    pub const PRETTY_SORTED: Self = Self {
        pretty: true,
        sorted_keys: true,
        escape_slashes: false,
    };
    /// Indented with sorted keys and `/` escaped.
    pub const PRETTY_SORTED_ESCAPED: Self = Self {
        pretty: true,
        sorted_keys: true,
        escape_slashes: true,
    };
}

impl Json {
    /// A whole document; `None` when it is not one.
    #[must_use]
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        let bytes = bytes.strip_prefix(b"\xEF\xBB\xBF").unwrap_or(bytes);
        let text = std::str::from_utf8(bytes).ok()?;
        let mut parser = Parser {
            bytes: text.as_bytes(),
            text,
            at: 0,
        };
        parser.skip_space();
        let value = parser.value(0)?;
        parser.skip_space();
        (parser.at == parser.bytes.len()).then_some(value)
    }

    /// A member of an object: the last one with the key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&Self> {
        match self {
            Self::Object(items) => items.iter().rev().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    /// The members of an object as they are, repeats included.
    #[must_use]
    pub fn as_object(&self) -> Option<&[(String, Self)]> {
        match self {
            Self::Object(members) => Some(members),
            _ => None,
        }
    }

    /// The members of an object without repeated keys: a repeat's value takes
    /// the place of the first.
    #[must_use]
    pub fn entries(&self) -> Vec<(&str, &Self)> {
        let Self::Object(items) = self else {
            return Vec::new();
        };
        let mut out: Vec<(&str, &Self)> = Vec::new();
        for (key, value) in items {
            if let Some(slot) = out.iter_mut().find(|(k, _)| *k == key) {
                slot.1 = value;
            } else {
                out.push((key, value));
            }
        }
        out
    }

    /// A whole number: `3` and `3.0` both.
    #[must_use]
    pub fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(n) => Some(*n),
            Self::Float(f) if f.fract() == 0.0 && f.abs() < 9.2e18 => Some(*f as i64),
            _ => None,
        }
    }

    /// Any number, a fraction truncated toward zero.
    #[must_use]
    pub fn as_number_int(&self) -> Option<i64> {
        match self {
            Self::Int(n) => Some(*n),
            Self::Float(f) if f.is_finite() => {
                Some(f.trunc().clamp(i64::MIN as f64, i64::MAX as f64) as i64)
            }
            _ => None,
        }
    }

    /// Any number as a float.
    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Self::Int(n) => Some(*n as f64),
            Self::Float(f) => Some(*f),
            _ => None,
        }
    }

    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_array(&self) -> Option<&[Self]> {
        match self {
            Self::Array(items) => Some(items),
            _ => None,
        }
    }

    #[must_use]
    pub const fn is_object(&self) -> bool {
        matches!(self, Self::Object(_))
    }

    #[must_use]
    pub const fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }

    /// A string member of an object.
    #[must_use]
    pub fn str(&self, key: &str) -> Option<&str> {
        self.get(key).and_then(Self::as_str)
    }

    /// A whole-number member of an object.
    #[must_use]
    pub fn int(&self, key: &str) -> Option<i64> {
        self.get(key).and_then(Self::as_int)
    }

    /// A boolean member of an object.
    #[must_use]
    pub fn bool(&self, key: &str) -> Option<bool> {
        self.get(key).and_then(Self::as_bool)
    }

    /// An object member of an object; `None` when missing or not an object.
    #[must_use]
    pub fn object(&self, key: &str) -> Option<&Self> {
        self.get(key).filter(|v| v.is_object())
    }

    /// An object member, or an empty object when missing or not one.
    #[must_use]
    pub fn object_or_empty(&self, key: &str) -> Self {
        self.object(key)
            .cloned()
            .unwrap_or_else(|| Self::Object(Vec::new()))
    }

    /// A member that is an array of strings, all or nothing: one item that is
    /// not a string makes it `None`.
    #[must_use]
    pub fn strings(&self, key: &str) -> Option<Vec<String>> {
        self.get(key).and_then(Self::as_strings)
    }

    /// An array of strings, all or nothing.
    #[must_use]
    pub fn as_strings(&self) -> Option<Vec<String>> {
        self.as_array()?
            .iter()
            .map(|v| v.as_str().map(str::to_owned))
            .collect()
    }

    /// A member that is an array of objects, all or nothing.
    #[must_use]
    pub fn objects(&self, key: &str) -> Option<Vec<&Self>> {
        self.get(key)?
            .as_array()?
            .iter()
            .map(|v| v.is_object().then_some(v))
            .collect()
    }

    /// The objects of an array member, skipping anything else; empty when
    /// there is no such member.
    #[must_use]
    pub fn objects_in(&self, key: &str) -> Vec<&Self> {
        self.get(key)
            .and_then(Self::as_array)
            .map(|items| items.iter().filter(|v| v.is_object()).collect())
            .unwrap_or_default()
    }

    /// Compact, keys in the object's order ([`Format::COMPACT`]).
    #[must_use]
    pub fn to_text(&self) -> String {
        self.to_text_with(Format::COMPACT)
    }

    #[must_use]
    pub fn to_text_with(&self, format: Format) -> String {
        let mut out = String::new();
        write(self, format, 0, &mut out);
        out
    }
}

/// An object from pairs: shorter than `Json::Object(vec![...])` with `into()`.
#[must_use]
pub fn object(items: Vec<(&str, Json)>) -> Json {
    Json::Object(items.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
}

impl From<&str> for Json {
    fn from(s: &str) -> Self {
        Self::String(s.to_string())
    }
}

impl From<String> for Json {
    fn from(s: String) -> Self {
        Self::String(s)
    }
}

impl From<i64> for Json {
    fn from(n: i64) -> Self {
        Self::Int(n)
    }
}

impl From<bool> for Json {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

/// A number as `JSONSerialization` writes it: a whole one with no point.
#[must_use]
pub fn number(value: f64) -> String {
    if value.is_finite() && value.fract() == 0.0 && value.abs() < 1e15 {
        format!("{}", value as i64)
    } else {
        format!("{value}")
    }
}

// MARK: - writing

fn indent(out: &mut String, level: usize) {
    out.extend(std::iter::repeat_n(' ', 2 * level));
}

fn write(value: &Json, format: Format, level: usize, out: &mut String) {
    match value {
        Json::Null => out.push_str("null"),
        Json::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Json::Int(n) => {
            let _ = write!(out, "{n}");
        }
        Json::Float(f) => {
            if f.is_finite() {
                out.push_str(&number(*f));
            } else {
                out.push_str("null");
            }
        }
        Json::String(s) => write_string(s, format.escape_slashes, out),
        Json::Array(items) => {
            let items: Vec<(Option<&str>, &Json)> = items.iter().map(|item| (None, item)).collect();
            container(('[', ']'), &items, format, level, out);
        }
        Json::Object(entries) => {
            let mut items: Vec<(Option<&str>, &Json)> =
                entries.iter().map(|(k, v)| (Some(k.as_str()), v)).collect();
            if format.sorted_keys {
                items.sort_by(|a, b| a.0.cmp(&b.0));
            }
            container(('{', '}'), &items, format, level, out);
        }
    }
}

fn container(
    brackets: (char, char),
    items: &[(Option<&str>, &Json)],
    format: Format,
    level: usize,
    out: &mut String,
) {
    out.push(brackets.0);
    if !format.pretty {
        for (i, (key, value)) in items.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            if let Some(key) = key {
                write_string(key, format.escape_slashes, out);
                out.push(':');
            }
            write(value, format, level + 1, out);
        }
        out.push(brackets.1);
        return;
    }
    // An empty container takes three lines: `[`, an empty one, `]`.
    out.push('\n');
    if items.is_empty() {
        out.push('\n');
    }
    for (i, (key, value)) in items.iter().enumerate() {
        indent(out, level + 1);
        if let Some(key) = key {
            write_string(key, format.escape_slashes, out);
            out.push_str(" : ");
        }
        write(value, format, level + 1, out);
        if i + 1 < items.len() {
            out.push(',');
        }
        out.push('\n');
    }
    indent(out, level);
    out.push(brackets.1);
}

/// A string in quotes, escaped.
pub fn write_string(s: &str, escape_slashes: bool, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '/' if escape_slashes => out.push_str("\\/"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

// MARK: - reading

struct Parser<'a> {
    bytes: &'a [u8],
    text: &'a str,
    at: usize,
}

impl Parser<'_> {
    fn skip_space(&mut self) {
        while self.at < self.bytes.len()
            && matches!(self.bytes[self.at], b' ' | b'\t' | b'\n' | b'\r')
        {
            self.at += 1;
        }
    }

    fn eat(&mut self, word: &str) -> bool {
        if self.text[self.at..].starts_with(word) {
            self.at += word.len();
            true
        } else {
            false
        }
    }

    fn value(&mut self, depth: usize) -> Option<Json> {
        // Deeper than any real file, and the stack is not endless.
        if depth > 256 {
            return None;
        }
        match *self.bytes.get(self.at)? {
            b'n' => self.eat("null").then_some(Json::Null),
            b't' => self.eat("true").then_some(Json::Bool(true)),
            b'f' => self.eat("false").then_some(Json::Bool(false)),
            b'"' => self.string().map(Json::String),
            b'[' => {
                self.at += 1;
                let mut items = Vec::new();
                self.skip_space();
                if self.bytes.get(self.at) == Some(&b']') {
                    self.at += 1;
                    return Some(Json::Array(items));
                }
                loop {
                    self.skip_space();
                    items.push(self.value(depth + 1)?);
                    self.skip_space();
                    match self.bytes.get(self.at)? {
                        b',' => self.at += 1,
                        b']' => {
                            self.at += 1;
                            return Some(Json::Array(items));
                        }
                        _ => return None,
                    }
                }
            }
            b'{' => {
                self.at += 1;
                let mut items = Vec::new();
                self.skip_space();
                if self.bytes.get(self.at) == Some(&b'}') {
                    self.at += 1;
                    return Some(Json::Object(items));
                }
                loop {
                    self.skip_space();
                    if self.bytes.get(self.at) != Some(&b'"') {
                        return None;
                    }
                    let key = self.string()?;
                    self.skip_space();
                    if self.bytes.get(self.at) != Some(&b':') {
                        return None;
                    }
                    self.at += 1;
                    self.skip_space();
                    let value = self.value(depth + 1)?;
                    items.push((key, value));
                    self.skip_space();
                    match self.bytes.get(self.at)? {
                        b',' => self.at += 1,
                        b'}' => {
                            self.at += 1;
                            return Some(Json::Object(items));
                        }
                        _ => return None,
                    }
                }
            }
            b'-' | b'0'..=b'9' => self.number(),
            _ => None,
        }
    }

    fn number(&mut self) -> Option<Json> {
        let start = self.at;
        let mut real = false;
        while let Some(&c) = self.bytes.get(self.at) {
            match c {
                b'0'..=b'9' | b'-' | b'+' => {}
                b'.' | b'e' | b'E' => real = true,
                _ => break,
            }
            self.at += 1;
        }
        let word = &self.text[start..self.at];
        if !real && let Ok(n) = word.parse::<i64>() {
            return Some(Json::Int(n));
        }
        word.parse::<f64>().ok().map(Json::Float)
    }

    fn hex4(&mut self) -> Option<u32> {
        let hex = self.text.get(self.at..self.at + 4)?;
        let code = u32::from_str_radix(hex, 16).ok()?;
        self.at += 4;
        Some(code)
    }

    fn string(&mut self) -> Option<String> {
        self.at += 1; // the opening quote
        let mut out = String::new();
        loop {
            let start = self.at;
            while let Some(&c) = self.bytes.get(self.at) {
                if c == b'"' || c == b'\\' {
                    break;
                }
                self.at += 1;
            }
            out.push_str(&self.text[start..self.at]);
            if *self.bytes.get(self.at)? == b'"' {
                self.at += 1;
                return Some(out);
            }
            self.at += 1;
            let escape = *self.bytes.get(self.at)?;
            self.at += 1;
            match escape {
                b'"' => out.push('"'),
                b'\\' => out.push('\\'),
                b'/' => out.push('/'),
                b'b' => out.push('\u{08}'),
                b'f' => out.push('\u{0c}'),
                b'n' => out.push('\n'),
                b'r' => out.push('\r'),
                b't' => out.push('\t'),
                b'u' => {
                    let first = self.hex4()?;
                    // A surrogate pair is one character; a lone half is
                    // U+FFFD, and the `\u` after it is read on its own.
                    let low = (0xd800..0xdc00).contains(&first)
                        && self.text[self.at..].starts_with("\\u");
                    let second = if low {
                        self.text
                            .get(self.at + 2..self.at + 6)
                            .and_then(|h| u32::from_str_radix(h, 16).ok())
                    } else {
                        None
                    };
                    let code = match second {
                        Some(second) if (0xdc00..0xe000).contains(&second) => {
                            self.at += 6;
                            0x10000 + ((first - 0xd800) << 10) + (second - 0xdc00)
                        }
                        _ => first,
                    };
                    out.push(char::from_u32(code).unwrap_or('\u{fffd}'));
                }
                _ => return None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        let text = r#"{"seq":3,"type":"event","body":{"output":"a\n\"b\" ё😀","n":1.5,"ok":true,"none":null,"list":[1,-2,3.25e1]}}"#;
        let value = Json::parse(text.as_bytes()).unwrap();
        assert_eq!(value.int("seq"), Some(3));
        let body = value.object_or_empty("body");
        assert_eq!(body.str("output"), Some("a\n\"b\" ё😀"));
        assert_eq!(body.get("n"), Some(&Json::Float(1.5)));
        assert_eq!(body.get("ok").and_then(Json::as_bool), Some(true));
        assert_eq!(
            body.get("list").and_then(Json::as_array).map(<[Json]>::len),
            Some(3)
        );
        assert_eq!(Json::Float(300.0).as_int(), Some(300));
        let again = Json::parse(value.to_text().as_bytes()).unwrap();
        assert_eq!(again, value);
        assert!(Json::parse(b"{\"a\":}").is_none());
        assert!(Json::parse(b"[1,2").is_none());
        assert!(Json::parse(b"1 2").is_none());
        assert!(
            Json::parse(br#"["\q"]"#).is_none(),
            "an unknown escape is a refusal"
        );
        assert_eq!(value.object_or_empty("nope"), Json::Object(Vec::new()));
    }

    #[test]
    fn reads_what_a_restore_writes() {
        let json = Json::parse(r#"{"a": [1, true, null, "xé\n"], "b": {"c": -1.5e2}}"#.as_bytes())
            .expect("valid");
        assert_eq!(
            json.get("b").and_then(|b| b.get("c")),
            Some(&Json::Float(-150.0))
        );
        assert_eq!(
            json.get("a"),
            Some(&Json::Array(vec![
                Json::Int(1),
                Json::Bool(true),
                Json::Null,
                Json::String("xé\n".to_string())
            ]))
        );
        assert!(Json::parse(b"{").is_none());
    }

    #[test]
    fn lists_and_repeats() {
        let value = Json::parse(br#"{"a":[1,"x"],"b":["x","y"],"n":2.5,"a":{"k":1}}"#).unwrap();
        assert!(
            value.get("a").unwrap().is_object(),
            "a repeated key keeps its last value"
        );
        assert_eq!(value.strings("b"), Some(vec!["x".into(), "y".into()]));
        assert_eq!(
            Json::parse(br#"{"b":["x",1]}"#).unwrap().strings("b"),
            None,
            "all or nothing"
        );
        assert_eq!(value.get("n").and_then(Json::as_number_int), Some(2));
        assert_eq!(value.entries().len(), 3);
        assert_eq!(
            Json::parse(value.to_text().as_bytes()).unwrap().get("n"),
            Some(&Json::Float(2.5))
        );
        assert!(Json::parse(b"\xEF\xBB\xBF{}").is_some());
        assert!(Json::parse(b"{\"version\": 3, \"libr").is_none());
        let mixed = Json::parse(br#"{"l":[{"a":1},2,{"b":2}]}"#).unwrap();
        assert_eq!(mixed.objects("l"), None, "all or nothing");
        assert_eq!(
            mixed.objects_in("l").len(),
            2,
            "what is not an object is skipped"
        );
    }

    #[test]
    fn surrogates() {
        let value = Json::parse(br#"["\ud83d\ude00","\u0041","\ud83d","\ud83d\u0041"]"#).unwrap();
        let strings = value.as_strings().unwrap();
        assert_eq!(strings, ["😀", "A", "\u{fffd}", "\u{fffd}A"]);
    }

    // The expected texts were written by `JSONSerialization` on macOS.
    #[test]
    fn writes_like_json_serialization() {
        let value =
            Json::parse(br#"{"y":2,"x":1.0,"s":"a/b","list":[1.5,true,null],"e":{}}"#).unwrap();
        assert_eq!(
            value.to_text_with(Format::SORTED),
            r#"{"e":{},"list":[1.5,true,null],"s":"a/b","x":1,"y":2}"#
        );
        assert_eq!(
            value.to_text(),
            r#"{"y":2,"x":1,"s":"a/b","list":[1.5,true,null],"e":{}}"#,
            "keys in the object's order"
        );
        let pretty = Json::parse(br#"{"a":[1]}"#)
            .unwrap()
            .to_text_with(Format::PRETTY_SORTED);
        assert_eq!(pretty, "{\n  \"a\" : [\n    1\n  ]\n}");
        let empty = Json::parse(br#"{"c":"x/y","b":{},"a":[]}"#).unwrap();
        assert_eq!(
            empty.to_text_with(Format::PRETTY_SORTED_ESCAPED),
            "{\n  \"a\" : [\n\n  ],\n  \"b\" : {\n\n  },\n  \"c\" : \"x\\/y\"\n}"
        );
        assert_eq!(
            empty.to_text_with(Format::PRETTY_SORTED),
            "{\n  \"a\" : [\n\n  ],\n  \"b\" : {\n\n  },\n  \"c\" : \"x/y\"\n}"
        );
        let graph = Json::Object(vec![
            ("root".into(), "a/b".into()),
            ("edges".into(), Json::Array(vec![])),
            (
                "nodes".into(),
                Json::Array(vec![object(vec![
                    ("x", Json::Int(1)),
                    ("t", "q\"\u{1}".into()),
                ])]),
            ),
        ]);
        assert_eq!(
            graph.to_text_with(Format::PRETTY_SORTED_ESCAPED),
            "{\n  \"edges\" : [\n\n  ],\n  \"nodes\" : [\n    {\n      \"t\" : \"q\\\"\\u0001\",\n      \"x\" : 1\n    }\n  ],\n  \"root\" : \"a\\/b\"\n}"
        );
        assert_eq!(number(1.0), "1");
        assert_eq!(number(0.5), "0.5");
    }
}
