//! What happens to a name at one place in the text: is it written or read,
//! and what is the right-hand side of the write. Text only — which names
//! the right-hand side holds is for the compiler to say, at positions from
//! here.
//!
//! It recognizes how projects actually change values: `c.Health = x`,
//! `c.Health += x`, `c.Health++`, `++c.Health`, `out c.Health`,
//! `new Health { Value = x }` in an initializer, and a write to a nested
//! field (`c.Pos.x = 1`) as a write to the struct.
//!
//! TODO: the text here is UTF-16 code units and ranges are [`Utf16Range`],
//! as in the editor this was written for, and as the compiler's locations
//! count. The value graph converts at its boundary ([`super::Site`] offsets
//! are bytes); converting this module and the graph's internals to bytes
//! together is left for later.

/// A range of UTF-16 code units in a text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Utf16Range {
    pub location: usize,
    pub length: usize,
}

impl Utf16Range {
    #[must_use]
    pub const fn new(location: usize, length: usize) -> Self {
        Self { location, length }
    }

    /// One past the last unit.
    #[must_use]
    pub const fn end(&self) -> usize {
        self.location + self.length
    }

    #[must_use]
    pub const fn contains(&self, location: usize) -> bool {
        location >= self.location && location - self.location < self.length
    }

    /// The overlap of two ranges; an empty one has length 0.
    #[must_use]
    pub fn intersection(&self, other: Self) -> Self {
        let start = self.location.max(other.location);
        let end = self.end().min(other.end());
        if end <= start {
            Self::new(0, 0)
        } else {
            Self::new(start, end - start)
        }
    }
}

/// The text of a range; a broken surrogate becomes U+FFFD.
#[must_use]
pub fn string(units: &[u16], range: Utf16Range) -> String {
    String::from_utf16_lossy(&units[range.location..range.end()])
}

/// What is done to a name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Access {
    Read,
    /// `rhs` is the right-hand side when there is one (`=`, `+=`); `++` has
    /// none. `compound`: the old value is part of the new one.
    Write {
        rhs: Option<Utf16Range>,
        compound: bool,
    },
}

/// The characters the reading looks at, as UTF-16 code units.
pub mod chars {
    pub const EQ: u16 = 0x3D;
    pub const GT: u16 = 0x3E;
    pub const LT: u16 = 0x3C;
    pub const PLUS: u16 = 0x2B;
    pub const MINUS: u16 = 0x2D;
    pub const STAR: u16 = 0x2A;
    pub const SLASH: u16 = 0x2F;
    pub const PERCENT: u16 = 0x25;
    pub const AMP: u16 = 0x26;
    pub const BAR: u16 = 0x7C;
    pub const CARET: u16 = 0x5E;
    pub const QUESTION: u16 = 0x3F;
    pub const DOT: u16 = 0x2E;
    pub const COMMA: u16 = 0x2C;
    pub const SEMICOLON: u16 = 0x3B;
    pub const QUOTE: u16 = 0x22;
    pub const APOSTROPHE: u16 = 0x27;
    pub const BACKSLASH: u16 = 0x5C;
    pub const DOLLAR: u16 = 0x24;
    pub const NEWLINE: u16 = 0x0A;
    pub const COLON: u16 = 0x3A;
    pub const OPEN_PAREN: u16 = 0x28;
    pub const CLOSE_PAREN: u16 = 0x29;
    pub const OPEN_BRACKET: u16 = 0x5B;
    pub const CLOSE_BRACKET: u16 = 0x5D;
    pub const OPEN_BRACE: u16 = 0x7B;
    pub const CLOSE_BRACE: u16 = 0x7D;
    /// What can come before `=` in a compound assignment.
    pub const COMPOUND_CHARS: [u16; 11] = [
        0x2B, 0x2D, 0x2A, 0x2F, 0x25, 0x26, 0x7C, 0x5E, 0x3F, 0x3C, 0x3E,
    ];
}

use chars::*;

/// The short name of a range in this module.
use Utf16Range as R;

/// What is done to the name at `name` in `text`. A write into a nested
/// field (`c.Pos.x = 1` for `Pos`) is a write too: the struct changes, and
/// the old value of its other fields stays.
#[must_use]
pub fn access(text: &[u16], name: Utf16Range) -> Access {
    let direct = direct_access(text, name);
    if direct != Access::Read {
        return direct;
    }
    // `Pos.x.y = …`: along the chain to its last link.
    let mut i = skip_space(text, name.end());
    let mut last: Option<Utf16Range> = None;
    while i < text.len() && text[i] == DOT {
        let s = skip_space(text, i + 1);
        let mut e = s;
        while e < text.len() && is_ident_part(text[e]) {
            e += 1;
        }
        if !(e > s && is_ident_start(text[s])) {
            break;
        }
        last = Some(Utf16Range::new(s, e - s));
        i = skip_space(text, e);
    }
    let Some(last) = last else {
        return Access::Read;
    };
    if !(i >= text.len() || text[i] != OPEN_PAREN) {
        return Access::Read;
    }
    if let Access::Write { rhs, .. } = direct_access(text, last) {
        return Access::Write {
            rhs,
            compound: true,
        };
    }
    Access::Read
}

/// What is done to the name at `name` itself, not following a chain after
/// it: `x[i] = v` for the `]` at `name` is a write of `v`.
#[must_use]
pub fn direct_access(text: &[u16], name: Utf16Range) -> Access {
    let end = name.end();
    let mut i = skip_space(text, end);
    if i < text.len() {
        let c = text[i];
        let next = if i + 1 < text.len() { text[i + 1] } else { 0 };
        // `=`, but neither `==` nor `=>`.
        if c == EQ && next != EQ && next != GT {
            return Access::Write {
                rhs: Some(rhs(text, i + 1)),
                compound: false,
            };
        }
        // `++` and `--` after the name.
        if (c == PLUS && next == PLUS) || (c == MINUS && next == MINUS) {
            return Access::Write {
                rhs: None,
                compound: true,
            };
        }
        // Compound: `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `??=`, `<<=`, `>>=`.
        let mut j = i;
        while j < text.len() && COMPOUND_CHARS.contains(&text[j]) {
            j += 1;
        }
        if j > i && j < text.len() && text[j] == EQ && (j + 1 >= text.len() || text[j + 1] != EQ) {
            let op = &text[i..j];
            let known: [&[u16]; 11] = [
                &[PLUS],
                &[MINUS],
                &[STAR],
                &[SLASH],
                &[PERCENT],
                &[AMP],
                &[BAR],
                &[CARET],
                &[QUESTION, QUESTION],
                &[LT, LT],
                &[GT, GT],
            ];
            if known.contains(&op) {
                return Access::Write {
                    rhs: Some(rhs(text, j + 1)),
                    compound: true,
                };
            }
        }
    }
    // `++` and `--` before the name, past an `x.` before it: `++c.Count`.
    let mut k = name.location;
    while k > 0 {
        let c = text[k - 1];
        if is_ident_part(c) || c == DOT {
            k -= 1;
        } else {
            break;
        }
    }
    i = skip_space_backward(text, k);
    if i >= 2
        && ((text[i - 1] == PLUS && text[i - 2] == PLUS)
            || (text[i - 1] == MINUS && text[i - 2] == MINUS))
    {
        return Access::Write {
            rhs: None,
            compound: true,
        };
    }
    // `out x.Field`: the method fills it.
    if i >= 3 && word(text, i) == "out" {
        return Access::Write {
            rhs: None,
            compound: false,
        };
    }
    Access::Read
}

/// The right-hand side of an assignment from `start` to the end of the
/// expression: `;`, or a comma or the brace of an initializer
/// `{ A = 1, B = 2 }` at its own level.
#[must_use]
pub fn rhs(text: &[u16], start: usize) -> Utf16Range {
    let mut depth = 0;
    let mut i = start;
    while i < text.len() {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == SLASH && i + 1 < text.len() && text[i + 1] == SLASH {
            while i < text.len() && text[i] != NEWLINE {
                i += 1;
            }
            continue;
        }
        // Commas among generic arguments (`Dictionary<(A a, B b), int>`)
        // do not end it.
        if c == LT
            && i > 0
            && is_ident_part(text[i - 1])
            && let Some(after) = type_arguments(text, i, text.len())
        {
            i = after;
            continue;
        }
        if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
            depth += 1;
        }
        if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            if depth == 0 {
                break;
            }
            depth -= 1;
        }
        if depth == 0 && (c == SEMICOLON || c == COMMA) {
            break;
        }
        i += 1;
    }
    let mut from = skip_space(text, start);
    let mut to = i;
    while to > from && is_space(text[to - 1]) {
        to -= 1;
    }
    from = from.min(to);
    Utf16Range::new(from, to - from)
}

/// When the `<` at `from` opens type arguments, the position just past the
/// `>`. Inside is only what types are written with: names, dots, commas,
/// tuples, arrays and `?`: `Dictionary<(int a, T b), U[]?>`.
#[must_use]
pub fn type_arguments(text: &[u16], from: usize, limit: usize) -> Option<usize> {
    let mut depth = 0;
    let mut i = from;
    while i < limit {
        let c = text[i];
        if c == LT {
            depth += 1;
        } else if c == GT {
            depth -= 1;
            if depth == 0 {
                return Some(i + 1);
            }
        } else if !(is_ident_part(c)
            || c == DOT
            || c == COMMA
            || is_space(c)
            || c == QUESTION
            || c == OPEN_PAREN
            || c == CLOSE_PAREN
            || c == OPEN_BRACKET
            || c == CLOSE_BRACKET)
        {
            return None;
        }
        i += 1;
    }
    None
}

/// The identifier that ends at `end`.
#[must_use]
pub fn word(text: &[u16], end: usize) -> String {
    let end = end.min(text.len());
    let mut s = end;
    while s > 0 && is_ident_part(text[s - 1]) {
        s -= 1;
    }
    string(text, Utf16Range::new(s, end - s))
}

/// Past the string or character literal that opens at `start`.
#[must_use]
pub fn skip_literal(text: &[u16], start: usize) -> usize {
    let q = text[start];
    let mut i = start + 1;
    while i < text.len() && text[i] != q {
        if text[i] == BACKSLASH {
            i += 1;
        }
        // A backslash at the very end of the text: nothing more to read.
        if i >= text.len() || text[i] == NEWLINE {
            break;
        }
        i += 1;
    }
    (i + 1).min(text.len())
}

#[must_use]
pub fn skip_space(text: &[u16], start: usize) -> usize {
    let mut i = start;
    while i < text.len() && is_space(text[i]) {
        i += 1;
    }
    i
}

#[must_use]
pub fn skip_space_backward(text: &[u16], start: usize) -> usize {
    let mut i = start.min(text.len());
    while i > 0 && is_space(text[i - 1]) {
        i -= 1;
    }
    i
}

/// A space, tab or line break.
#[must_use]
pub const fn is_space(c: u16) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D
}

#[must_use]
pub fn is_ident_start(c: u16) -> bool {
    (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c) || c == 0x5F || c == 0x40 || c > 0x7F
}

#[must_use]
pub fn is_ident_part(c: u16) -> bool {
    is_ident_start(c) || (0x30..=0x39).contains(&c)
}

/// A write into an element of the collection named `name`: `map[key] = value`,
/// `list.Add(value)`, `map.Add(key, value)`, `queue.Enqueue(value)`.
/// `value` is the element's new value: the right-hand side or the last
/// argument; `method` is how it is written (`[]`, `Add`…).
pub fn element_write(text: &[u16], name: R) -> Option<(R, String)> {
    let mut i = skip_space(text, name.end());
    if i < text.len() && text[i] == QUESTION {
        i = skip_space(text, i + 1);
    }
    if i >= text.len() {
        return None;
    }
    if text[i] == OPEN_BRACKET {
        let close = matching(text, i);
        if close <= i as isize {
            return None;
        }
        let Access::Write {
            rhs: Some(value), ..
        } = direct_access(text, R::new(close as usize, 1))
        else {
            return None;
        };
        if value.length == 0 {
            return None;
        }
        return Some((value, "[]".into()));
    }
    if text[i] != DOT {
        return None;
    }
    let start = skip_space(text, i + 1);
    let mut end = start;
    while end < text.len() && is_ident_part(text[end]) {
        end += 1;
    }
    let method = string(text, R::new(start, end - start));
    if ![
        "Add", "TryAdd", "Enqueue", "Push", "Insert", "AddRange", "AddLast", "AddFirst", "Append",
    ]
    .contains(&method.as_str())
    {
        return None;
    }
    let name = R::new(start, end - start);
    let mut last: Option<R> = None;
    let mut index = 0;
    while let Some(found) = argument(text, name, index) {
        last = Some(found);
        index += 1;
    }
    Some((last?, method))
}

/// A name on the right-hand side that the value depends on. Of the chain
/// `stats.Damage` it is the last link (`Damage`): the compiler is asked
/// about that one. `call`: it is a method call.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Source {
    pub range: R,
    pub chain: String,
    pub call: bool,
    /// The chain is taken from an expression, not a name: `f().x`, `a[i].x`.
    pub member: bool,
    /// The call whose result it is taken from: `_stash.Get(e).x` → `_stash.Get`.
    pub receiver: Option<String>,
    /// That call's links: `_stash`, `Get` of `_stash.Get(e).x`.
    pub receiver_links: Vec<R>,
    /// The chain's first link: `a` of `a.b.c`.
    pub head: Option<R>,
    /// All links of the chain in order: `a`, `b`, `c` of `a.b.c`. Without
    /// `this.` and `base.`. The one before last is the receiver of the last.
    pub links: Vec<R>,
    /// `new T(…)`: the object is built right here, from the arguments.
    pub constructs: bool,
    /// The name is the key of an element access: `index` of `data[index]`.
    pub is_index_key: bool,
    /// The calls whose parentheses hold the name — those methods' names,
    /// outermost first: `Clamp` and `Get` for `x` in `Clamp(Get(x), 0, 1)`.
    /// A constructor `new T(…)` is not among them: its arguments are the
    /// object itself.
    pub calls: Vec<R>,
}

impl Source {
    pub fn new(range: R, chain: impl Into<String>, call: bool) -> Self {
        Source {
            range,
            chain: chain.into(),
            call,
            ..Source::default()
        }
    }

    /// The same chain without its last link — what that link is taken from:
    /// `stats.Damage` of `stats.Damage.ToString()`. `None`: one link only.
    pub fn receiver_chain(&self) -> Option<Source> {
        if self.links.len() < 2 {
            return None;
        }
        let parts: Vec<&str> = self.chain.split('.').filter(|p| !p.is_empty()).collect();
        let mut receiver = Source::new(
            self.links[self.links.len() - 2],
            parts[..parts.len().saturating_sub(1)].join("."),
            false,
        );
        receiver.member = self.member;
        receiver.receiver = self.receiver.clone();
        receiver.receiver_links = self.receiver_links.clone();
        receiver.head = self.head;
        receiver.links = self.links[..self.links.len() - 1].to_vec();
        Some(receiver)
    }
}

/// The expressions of the holes `{x}`, `{hp:F1}`, `{name,10}` in the body of
/// an interpolated string `$"…"`; `{{` is just a brace.
fn interpolation_holes(text: &[u16], body: R) -> Vec<R> {
    let mut holes = Vec::new();
    let end = body.end();
    let mut i = body.location;
    while i < end {
        if text[i] != OPEN_BRACE {
            i += 1;
            continue;
        }
        if i + 1 < end && text[i + 1] == OPEN_BRACE {
            i += 2;
            continue;
        }
        let start = i + 1;
        let mut depth = 0;
        let mut stop = None;
        let mut k = start;
        while k < end {
            let c = text[k];
            if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
                depth += 1;
            } else if (c == CLOSE_PAREN || c == CLOSE_BRACKET) && depth > 0 {
                depth -= 1;
            } else if c == CLOSE_BRACE {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            } else if depth == 0 && (c == COLON || c == COMMA) && stop.is_none() {
                stop = Some(k);
            }
            k += 1;
        }
        let hole = trimmed(text, R::new(start, stop.unwrap_or(k) - start));
        if hole.length > 0 {
            holes.push(hole);
        }
        i = k + 1;
    }
    holes
}

pub fn sources(text: &[u16], range: R) -> Vec<Source> {
    let mut result: Vec<Source> = Vec::new();
    let mut i = range.location;
    let end = range.end();
    while i < end {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        // An interpolated string `$"…{x}…"`: the sources are the expressions in
        // braces, without the format after `:` and the alignment after `,`.
        if c == DOLLAR && i + 1 < end && text[i + 1] == QUOTE {
            let close = skip_literal(text, i + 1).min(end);
            for hole in interpolation_holes(text, R::new(i + 2, close.saturating_sub(i + 3))) {
                result.extend(sources(text, hole));
            }
            i = close;
            continue;
        }
        // `=>`: a lambda — its parameters and body are not what the value is made
        // of; a `switch` expression arm is, but the pattern before it is not.
        if c == EQ && i + 1 < end && text[i + 1] == GT {
            let arrow = i;
            i = skip_space(text, i + 2);
            if let Some(arm) = switch_arm_start(text, arrow, range.location) {
                result.retain(|s| !(s.range.location >= arm && s.range.location < arrow));
                continue;
            }
            let back = skip_space_backward(text, arrow);
            let mut parameters = back;
            if back > 0
                && text[back - 1] == CLOSE_PAREN
                && let Some(open) = matching_backward(text, back - 1)
            {
                parameters = open;
            } else {
                while parameters > 0 && is_ident_part(text[parameters - 1]) {
                    parameters -= 1;
                }
            }
            result.retain(|s| !(s.range.location >= parameters && s.range.location < arrow));
            i = lambda_body_end(text, i, end);
            continue;
        }
        if !(is_ident_start(c) && (i == 0 || !is_ident_part(text[i - 1]))) {
            i += 1;
            continue;
        }
        // The chain `a.b.c` (with `?.` and spaces around the dots).
        let mut parts: Vec<R> = Vec::new();
        let mut j = i;
        while j < end && is_ident_start(text[j]) {
            let s = j;
            while j < end && is_ident_part(text[j]) {
                j += 1;
            }
            parts.push(R::new(s, j - s));
            let mut k = skip_space(text, j);
            if k < end && text[k] == QUESTION {
                k += 1;
            }
            if !(k < end && text[k] == DOT) {
                break;
            }
            k = skip_space(text, k + 1);
            if !(k < end && is_ident_start(text[k])) {
                break;
            }
            j = k;
        }
        let mut words: Vec<String> = parts.iter().map(|&p| string(text, p)).collect();
        let after = skip_space(text, j);
        // The target of an assignment (`{ A = x }` in an initializer) and the name
        // of an argument or tuple element (`M(radius: r)`) are not sources.
        if after + 1 < end && text[after] == EQ && text[after + 1] != EQ && text[after + 1] != GT {
            i = j;
            continue;
        }
        if parts.len() == 1
            && after < end
            && text[after] == COLON
            && (after + 1 >= end || text[after + 1] != COLON)
        {
            let before = skip_space_backward(text, i);
            if before > 0 && (text[before - 1] == OPEN_PAREN || text[before - 1] == COMMA) {
                i = j;
                continue;
            }
        }
        let call = after < end
            && (text[after] == OPEN_PAREN
                || (text[after] == LT && looks_generic(text, after, end)));
        // `this.x` is `x`.
        if words.len() > 1 && (words[0] == "this" || words[0] == "base") {
            words.remove(0);
        }
        // `_` is a discarded value: `out _`, `_ = …`.
        if words.len() == 1 && words[0] == "_" {
            i = j;
            continue;
        }
        if let Some(first) = words.first()
            && !KEYWORDS.contains(&first.as_str())
        {
            let mut source = Source::new(
                *parts.last().expect("a link is there"),
                words.join("."),
                call,
            );
            source.head = Some(parts[parts.len() - words.len()]);
            source.links = parts[parts.len() - words.len()..].to_vec();
            // `new T(…)` and `new List<int> { … }` without parentheses: an object from its arguments and elements.
            source.constructs = word(text, skip_space_backward(text, i)) == "new";
            // `…).x`, `…].x`: a member of what the expression on the left returned.
            let back = skip_space_backward(text, i);
            if back > 0 && text[back - 1] == DOT {
                source.member = true;
                let close = skip_space_backward(text, back - 1);
                if close > 0
                    && text[close - 1] == CLOSE_PAREN
                    && let Some(open) = matching_backward(text, close - 1)
                    && let Some(callee) = enclosing_call(text, open + 1)
                {
                    source.receiver = Some(callee.chain.clone());
                    source.receiver_links = callee.links.clone();
                    // The call itself is not a source: only this member is taken from its result.
                    if let Some(index) = result
                        .iter()
                        .rposition(|s| s.call && s.range == callee.range)
                    {
                        result.remove(index);
                    }
                }
            }
            result.push(source);
        }
        // Generic arguments (`new Dictionary<(Rarity rarity, int n), T>()`) are types, not values.
        let constructs = result
            .last()
            .is_some_and(|s| s.constructs && s.range.end() == j);
        i = if (call || constructs) && after < end && text[after] == LT {
            generic_end(text, after, end)
        } else {
            j
        };
    }
    for source in result.iter_mut() {
        let at = source
            .links
            .first()
            .map_or(source.range.location, |l| l.location);
        source.calls = enclosing_call_names(text, at, range.location);
        source.is_index_key = is_index_key(text, at, range.location);
    }
    result
}

/// The names of calls whose unclosed parentheses hold `offset` (not left of
/// `from`), outermost first. `new T(…)`, `if (…)`, `typeof(…)` and the
/// parentheses of an expression are not calls.
pub fn enclosing_call_names(text: &[u16], offset: usize, from: usize) -> Vec<R> {
    let mut names = Vec::new();
    let mut depth = 0;
    let mut i = offset as isize - 1;
    while i >= from as isize {
        let c = text[i as usize];
        if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            depth += 1;
        } else if c == OPEN_BRACKET || c == OPEN_BRACE {
            if depth > 0 {
                depth -= 1;
            }
        } else if c == OPEN_PAREN {
            if depth > 0 {
                depth -= 1;
            } else if let Some(name) = callee(text, i as usize, from) {
                names.insert(0, name);
            }
        }
        i -= 1;
    }
    names
}

/// The expression whose method `name` is called: `player` of
/// `player.TryGet(…)`, `GetPlayer()` of `GetPlayer()?.TryGet(…)`. `None`:
/// a call without a receiver.
pub fn receiver_expression(text: &[u16], name: R) -> Option<R> {
    let dot_at = skip_space_backward(text, name.location);
    if !(dot_at > 0 && text[dot_at - 1] == DOT) {
        return None;
    }
    let mut e = dot_at - 1;
    if e > 0 && text[e - 1] == QUESTION {
        e -= 1;
    }
    let end = skip_space_backward(text, e);
    let mut i = end;
    // Back along the chain: names, dots, parentheses of calls and indexers.
    while i > 0 {
        let c = text[i - 1];
        if is_ident_part(c) || c == DOT || c == QUESTION {
            i -= 1;
        } else if c == CLOSE_PAREN || c == CLOSE_BRACKET {
            let mut depth = 0;
            let mut k = i as isize - 1;
            while k >= 0 {
                let ch = text[k as usize];
                if ch == CLOSE_PAREN || ch == CLOSE_BRACKET {
                    depth += 1;
                } else if ch == OPEN_PAREN || ch == OPEN_BRACKET {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                k -= 1;
            }
            if k < 0 {
                break;
            }
            i = k as usize;
        } else if is_space(c) {
            // Spaces only around a dot of the chain.
            let j = skip_space_backward(text, i);
            if !((j > 0 && text[j - 1] == DOT) || (i < end && text[i] == DOT)) {
                break;
            }
            i = j;
        } else {
            break;
        }
    }
    (i < end).then(|| R::new(i, end - i))
}

/// The chain the name `name` ends: `_stash.Get` for `Get`, `this.` dropped.
pub fn chain(text: &[u16], name: R) -> String {
    chain_links(text, name)
        .iter()
        .map(|&l| string(text, l))
        .collect::<Vec<_>>()
        .join(".")
}

/// The links of the same chain in order, as ranges of names.
pub fn chain_links(text: &[u16], name: R) -> Vec<R> {
    let mut links = vec![name];
    let mut start = name.location;
    loop {
        let dot_at = skip_space_backward(text, start);
        if !(dot_at > 0 && text[dot_at - 1] == DOT) {
            break;
        }
        let end = skip_space_backward(text, dot_at - 1);
        let mut begin = end;
        while begin > 0 && is_ident_part(text[begin - 1]) {
            begin -= 1;
        }
        if !(begin < end && is_ident_start(text[begin])) {
            break;
        }
        links.insert(0, R::new(begin, end - begin));
        start = begin;
    }
    if links.len() > 1 && ["this", "base"].contains(&string(text, links[0]).as_str()) {
        links.remove(0);
    }
    links
}

/// The name of the call before the parenthesis `open`: `Get` of `_stash.Get(`, `Max` of `Max<int>(`.
fn callee(text: &[u16], open: usize, from: usize) -> Option<R> {
    let mut end = skip_space_backward(text, open);
    if end > from && text[end - 1] == GT {
        let mut angle = 0;
        let mut k = end as isize - 1;
        while k >= from as isize {
            let c = text[k as usize];
            if c == GT {
                angle += 1;
            } else if c == LT {
                angle -= 1;
                if angle == 0 {
                    break;
                }
            }
            k -= 1;
        }
        if k < from as isize {
            return None;
        }
        end = skip_space_backward(text, k as usize);
    }
    let mut start = end;
    while start > from && is_ident_part(text[start - 1]) {
        start -= 1;
    }
    if !(start < end && is_ident_start(text[start])) {
        return None;
    }
    let name = string(text, R::new(start, end - start));
    if KEYWORDS.contains(&name.as_str())
        || [
            "if", "while", "for", "foreach", "switch", "using", "lock", "catch",
        ]
        .contains(&name.as_str())
    {
        return None;
    }
    // `new T(…)` is a constructor: its arguments are the object.
    let mut head = start;
    loop {
        let dot_at = skip_space_backward(text, head);
        if !(dot_at > from && text[dot_at - 1] == DOT) {
            break;
        }
        let mut s = skip_space_backward(text, dot_at - 1);
        while s > from && is_ident_part(text[s - 1]) {
            s -= 1;
        }
        head = s;
    }
    if word(text, skip_space_backward(text, head)) == "new" {
        None
    } else {
        Some(R::new(start, end - start))
    }
}

// MARK: - Literals

/// The literals the expression's value may turn out to be: the expression
/// itself (`0`, `"idle"`, `-1f`, `null`, `new()`), the branches of `?:`, the
/// right side of `??`, `switch` arms, a cast `(int)5` and parentheses. A
/// literal inside arithmetic or as a call argument does not count: in
/// `hp - 1`, `Clamp(x, 0, 1)` the value comes from the names.
pub fn literal_alternatives(text: &[u16], range: R) -> Vec<R> {
    let mut result = Vec::new();
    collect_literals(text, trimmed(text, range), 0, &mut result);
    result
}

fn collect_literals(text: &[u16], range: R, depth: usize, result: &mut Vec<R>) {
    if range.length == 0 || depth >= 8 {
        return;
    }
    let start = range.location;
    let end = range.end();
    // Parentheses around the whole expression and a cast `(int)x`.
    if text[start] == OPEN_PAREN {
        let close = matching(text, start);
        if close == end as isize - 1 {
            let close = close as usize;
            collect_literals(
                text,
                trimmed(text, R::new(start + 1, close - start - 1)),
                depth + 1,
                result,
            );
            return;
        }
        if close > start as isize && close < end as isize - 1 {
            let close = close as usize;
            if is_cast_type(text, R::new(start + 1, close - start - 1)) {
                let rest = trimmed(text, R::new(close + 1, end - close - 1));
                // After a cast comes an operand, not more expression: `(a) - b` is not a cast.
                if rest.length > 0
                    && (!binary_operator_start(text[rest.location]) || text[rest.location] == MINUS)
                {
                    collect_literals(text, rest, depth + 1, result);
                    return;
                }
            }
        }
    }
    // `a ?? b`, `c ? a : b` and `x switch { … }` at the top level.
    let mut level: i64 = 0;
    let mut i = start;
    while i < end {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        let next = if i + 1 < end { text[i + 1] } else { 0 };
        if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
            level += 1;
        } else if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            level -= 1;
        } else if level == 0 && c == EQ && next == GT {
            // A lambda: its body is not the expression's value.
            return;
        } else if level == 0 && c == QUESTION {
            if next == QUESTION {
                // `??=` does not get here: that is a write, not an expression.
                collect_literals(
                    text,
                    trimmed(text, R::new(start, i - start)),
                    depth + 1,
                    result,
                );
                collect_literals(
                    text,
                    trimmed(text, R::new(i + 2, end - i - 2)),
                    depth + 1,
                    result,
                );
                return;
            }
            if next != DOT
                && next != OPEN_BRACKET
                && let Some(colon_at) = ternary_colon(text, i + 1, end)
            {
                collect_literals(
                    text,
                    trimmed(text, R::new(i + 1, colon_at - i - 1)),
                    depth + 1,
                    result,
                );
                collect_literals(
                    text,
                    trimmed(text, R::new(colon_at + 1, end - colon_at - 1)),
                    depth + 1,
                    result,
                );
                return;
            }
        } else if level == 0
            && c == 0x73
            && i + 6 <= end
            && string(text, R::new(i, 6)) == "switch"
            && (i == 0 || !is_ident_part(text[i - 1]))
            && (i + 6 == end || !is_ident_part(text[i + 6]))
        {
            let open = skip_space(text, i + 6);
            if open < end && text[open] == OPEN_BRACE {
                let close = matching(text, open);
                if close > open as isize {
                    let close = close as usize;
                    for arm in switch_arms(text, R::new(open + 1, close - open - 1)) {
                        collect_literals(text, arm, depth + 1, result);
                    }
                    return;
                }
            }
        }
        i += 1;
    }
    if is_literal(text, range) || is_constant_arithmetic(text, range) {
        result.push(range);
    } else if let Some(elements) = collection_elements(text, range) {
        // `new List<int> { 1, 2 }`, `new[] { 1, 2 }`, `[1, 2]`: the value is made of the elements.
        for element in elements {
            collect_literals(text, element, depth + 1, result);
        }
    }
}

/// The elements of the collection the expression creates: `new List<int> { 1, 2 }`,
/// `new[] { a, b }`, `new int[] { … }`, `{ 1, 2 }` of an array, `[1, 2]`.
/// An object initializer (`new Pawn { Health = 5 }`) is not a collection.
fn collection_elements(text: &[u16], range: R) -> Option<Vec<R>> {
    let end = range.end();
    if range.length < 2 {
        return None;
    }
    let open = match text[range.location] {
        OPEN_BRACKET | OPEN_BRACE => range.location,
        _ if string(text, R::new(range.location, 3.min(range.length))) == "new"
            && range.length > 3
            && !is_ident_part(text[range.location + 3]) =>
        {
            // The initializer's brace is the first `{` at the top level after `new T…`.
            let mut depth = 0;
            let mut k = range.location + 3;
            loop {
                if k >= end {
                    return None;
                }
                let c = text[k];
                if c == OPEN_PAREN || c == LT || c == OPEN_BRACKET {
                    depth += 1;
                } else if (c == CLOSE_PAREN || c == GT || c == CLOSE_BRACKET) && depth > 0 {
                    depth -= 1;
                } else if c == OPEN_BRACE && depth == 0 {
                    break k;
                }
                k += 1;
            }
        }
        _ => return None,
    };
    if matching(text, open) != end as isize - 1 {
        return None;
    }
    let elements: Vec<R> = tuple_elements(text, R::new(open + 1, end - open - 2))
        .into_iter()
        .filter(|e| e.length > 0)
        .collect();
    // `Health = 5` is an object member; `{ "k", 1 }` of a dictionary is a pair, not taken apart either.
    let assigns = elements.iter().any(|e| {
        let t = string(text, *e);
        t.contains('=') && !t.contains("==") && !t.contains("=>")
    });
    (!elements.is_empty() && !assigns && !elements.iter().any(|e| text[e.location] == OPEN_BRACE))
        .then_some(elements)
}

/// An expression of literals and operators only: `2 + 3`, `60 * 60`,
/// `(1 << 4) | 1`, `"a" + "b"`. Its whole value is known, so it is a
/// source, as a literal is. `b + 1` is not: the value there comes from `b`.
fn is_constant_arithmetic(text: &[u16], range: R) -> bool {
    let end = range.end();
    let digit = |c: u16| (0x30..=0x39).contains(&c);
    let (mut operands, mut operators) = (0, 0);
    let mut i = range.location;
    while i < end {
        let c = text[i];
        if is_space(c) || c == OPEN_PAREN || c == CLOSE_PAREN {
            i += 1;
        } else if digit(c) || (c == DOT && i + 1 < end && digit(text[i + 1])) {
            operands += 1;
            i += 1;
            while i < end
                && (is_ident_part(text[i])
                    || text[i] == DOT
                    || ((text[i] == PLUS || text[i] == MINUS)
                        && (text[i - 1] == 0x65 || text[i - 1] == 0x45)
                        && digit(text[i - 2])))
            {
                i += 1;
            }
        } else if c == QUOTE || c == APOSTROPHE {
            operands += 1;
            i = skip_literal(text, i);
        } else if [
            PLUS, MINUS, STAR, SLASH, PERCENT, AMP, BAR, CARET, LT, GT, 0x7E,
        ]
        .contains(&c)
        {
            operators += 1;
            i += 1;
        } else {
            return false;
        }
    }
    operands >= 2 && operators >= 1
}

/// The whole expression is a literal: a number, a string without holes, a
/// character, `true`/`false`/`null`/`default`, `new()` or `new T()` without arguments.
pub fn is_literal(text: &[u16], range: R) -> bool {
    if range.length == 0 {
        return false;
    }
    let start = range.location;
    let end = range.end();
    let s = string(text, range);
    if ["true", "false", "null", "default"].contains(&s.as_str()) {
        return true;
    }
    if s.starts_with("default(")
        && text[end - 1] == CLOSE_PAREN
        && matching(text, start + 7) == end as isize - 1
    {
        return true;
    }
    // A string or a character: one, from start to end. `$"…"` only without holes.
    let mut i = start;
    if text[i] == 0x40 || text[i] == DOLLAR {
        i += 1;
    }
    if i < end && (text[i] == QUOTE || text[i] == APOSTROPHE) {
        if text[start] == DOLLAR && s.contains('{') {
            return false;
        }
        if text[start] == 0x40 {
            // `@"…"`: a quote is doubled, a backslash is just a character.
            let mut k = i + 1;
            while k < end {
                if text[k] == QUOTE {
                    if k + 1 < end && text[k + 1] == QUOTE {
                        k += 2;
                        continue;
                    }
                    return k == end - 1;
                }
                k += 1;
            }
            return false;
        }
        return skip_literal(text, i) == end;
    }
    // A number: sign, digits, point, exponent, suffix; 0x…, 0b…, `_` between digits.
    i = start;
    if text[i] == MINUS || text[i] == PLUS {
        i = skip_space(text, i + 1);
    }
    let digit = |c: u16| (0x30..=0x39).contains(&c);
    if !(i < end && (digit(text[i]) || (text[i] == DOT && i + 1 < end && digit(text[i + 1])))) {
        return is_empty_construction(text, range);
    }
    while i < end
        && (is_ident_part(text[i])
            || text[i] == DOT
            || ((text[i] == PLUS || text[i] == MINUS)
                && i > start
                && (text[i - 1] == 0x65 || text[i - 1] == 0x45)))
    {
        i += 1;
    }
    i == end
}

/// A default literal: `null`, `default`, `new()`, `new List<int>()`.
pub fn is_default_literal(literal: &str) -> bool {
    literal == "null"
        || literal == "default"
        || literal.starts_with("default(")
        || literal.starts_with("new")
}

/// `new()` and `new T()`: without arguments or an initializer.
fn is_empty_construction(text: &[u16], range: R) -> bool {
    let end = range.end();
    if !(string(text, R::new(range.location, range.length.min(3))) == "new"
        && range.length > 3
        && !is_ident_part(text[range.location + 3]))
    {
        return false;
    }
    let mut i = skip_space(text, range.location + 3);
    while i < end && (is_ident_part(text[i]) || text[i] == DOT) {
        i += 1;
    }
    if i < end
        && text[i] == LT
        && let Some(after) = type_arguments(text, i, end)
    {
        i = after;
    }
    i = skip_space(text, i);
    if !(i + 1 < end && text[i] == OPEN_PAREN) {
        return false;
    }
    let close = skip_space(text, i + 1);
    close == end - 1 && text[close] == CLOSE_PAREN
}

/// `(int)`, `(float?)`, `(Game.Kind)`: a type in parentheses, not an expression.
/// A name starting lowercase is not a type: `(a) - 1` is a subtraction.
fn is_cast_type(text: &[u16], range: R) -> bool {
    let inner = trimmed(text, range);
    if !(inner.length > 0 && is_ident_start(text[inner.location])) {
        return false;
    }
    for &c in &text[inner.location..inner.end()] {
        if !(is_ident_part(c)
            || c == DOT
            || c == QUESTION
            || c == LT
            || c == GT
            || c == COMMA
            || c == OPEN_BRACKET
            || c == CLOSE_BRACKET
            || is_space(c))
        {
            return false;
        }
    }
    let name = string(text, inner);
    let base = name
        .split(['?', '[', '<'])
        .find(|p| !p.is_empty())
        .unwrap_or(&name);
    if PRIMITIVE_TYPES.contains(&base) {
        return true;
    }
    let last = base.split('.').rfind(|p| !p.is_empty()).unwrap_or(base);
    last.chars().next().is_some_and(char::is_uppercase)
}

const PRIMITIVE_TYPES: [&str; 17] = [
    "int", "float", "double", "bool", "string", "long", "short", "byte", "uint", "ulong", "ushort",
    "sbyte", "char", "decimal", "object", "nint", "nuint",
];

fn binary_operator_start(c: u16) -> bool {
    [
        PLUS, MINUS, STAR, SLASH, PERCENT, AMP, BAR, CARET, LT, GT, EQ, QUESTION, DOT, 0x21,
    ]
    .contains(&c)
}

/// The `:` of the ternary whose `?` stands before `from`: nested `?:` are
/// counted, `::` and `x: 1` in parentheses skipped.
fn ternary_colon(text: &[u16], from: usize, end: usize) -> Option<usize> {
    let mut level: i64 = 0;
    let mut pending = 0;
    let mut i = from;
    while i < end {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
            level += 1;
        } else if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            level -= 1;
        } else if level == 0
            && c == QUESTION
            && i + 1 < end
            && text[i + 1] != DOT
            && text[i + 1] != QUESTION
            && text[i + 1] != OPEN_BRACKET
            && (i == 0 || text[i - 1] != QUESTION)
        {
            pending += 1;
        } else if level == 0
            && c == COLON
            && (i + 1 >= end || text[i + 1] != COLON)
            && (i == 0 || text[i - 1] != COLON)
        {
            if pending == 0 {
                return Some(i);
            }
            pending -= 1;
        }
        i += 1;
    }
    None
}

/// The results of the arms of a `switch` expression: `A => 1, _ => 2` → `1`, `2`.
fn switch_arms(text: &[u16], body: R) -> Vec<R> {
    let mut arms = Vec::new();
    let mut level: i64 = 0;
    let mut arm_start = body.location;
    let mut i = body.location;
    let end = body.end();
    let close = |arms: &mut Vec<R>, arm_start: usize, up_to: usize| {
        let arm = R::new(arm_start, up_to - arm_start);
        let mut k = arm.location;
        let mut inner: i64 = 0;
        while k + 1 < arm.end() {
            let c = text[k];
            if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
                inner += 1;
            } else if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
                inner -= 1;
            } else if inner == 0 && c == EQ && text[k + 1] == GT {
                let value = trimmed(text, R::new(k + 2, arm.end() - k - 2));
                if value.length > 0 {
                    arms.push(value);
                }
                return;
            }
            k += 1;
        }
    };
    while i < end {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
            level += 1;
        } else if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            level -= 1;
        } else if level == 0 && c == COMMA {
            close(&mut arms, arm_start, i);
            arm_start = i + 1;
        }
        i += 1;
    }
    close(&mut arms, arm_start, end.max(arm_start));
    arms
}

fn trimmed(text: &[u16], range: R) -> R {
    let mut from = range.location;
    let mut to = range.end();
    while from < to && is_space(text[from]) {
        from += 1;
    }
    while to > from && is_space(text[to - 1]) {
        to -= 1;
    }
    R::new(from, to - from)
}

/// The position just past the `>` that closes the `<` at `start`.
fn generic_end(text: &[u16], start: usize, limit: usize) -> usize {
    type_arguments(text, start, limit).unwrap_or(limit)
}

/// `var x = …` / `T x = …` inside the method before `before`: the right-hand
/// side of the local's declaration, if it was declared so.
pub fn local_initializer(text: &[u16], name: &str, method: R, before: usize) -> Option<R> {
    let target: Vec<u16> = name.encode_utf16().collect();
    if target.is_empty() {
        return None;
    }
    let mut best = None;
    let mut i = method.location;
    let limit = before.min(method.end());
    while i + target.len() <= limit {
        if text[i] == target[0]
            && text[i..i + target.len()] == target[..]
            && (i == 0 || !is_ident_part(text[i - 1]))
            && (i + target.len() >= text.len() || !is_ident_part(text[i + target.len()]))
        {
            // Before the name is a type or `var`, not a dot: `x.name = …` is not a declaration.
            let back = skip_space_backward(text, i);
            if back > 0
                && (is_ident_part(text[back - 1])
                    || text[back - 1] == GT
                    || text[back - 1] == CLOSE_BRACKET)
                && let Access::Write {
                    rhs: Some(rhs),
                    compound: false,
                } = access(text, R::new(i, target.len()))
            {
                best = Some(rhs);
            }
        }
        i += 1;
    }
    best
}

// MARK: - Locals and parameters

/// The parameter parentheses after a method name (`M<T>(int a, ref B b)`): the
/// range between them. A property has none.
pub fn parameter_list(text: &[u16], name: R) -> Option<R> {
    let mut i = skip_space(text, name.end());
    if i < text.len() && text[i] == LT {
        let mut depth = 0;
        while i < text.len() {
            if text[i] == LT {
                depth += 1;
            } else if text[i] == GT {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    break;
                }
            }
            i += 1;
        }
        i = skip_space(text, i);
    }
    if !(i < text.len() && text[i] == OPEN_PAREN) {
        return None;
    }
    let close = matching(text, i);
    if close <= i as isize {
        return None;
    }
    Some(R::new(i + 1, close as usize - i - 1))
}

/// The `foreach (var x in items)` loop variable at `name`: the range of `items`.
/// And an element of a deconstruction `foreach (var (key, x) in items)`.
pub fn foreach_collection(text: &[u16], name: R) -> Option<R> {
    if let Some(direct) = foreach_source(text, name) {
        return Some(direct);
    }
    // In deconstruction parentheses: `(key, x)` counts as one loop variable.
    let mut depth = 0;
    let mut i = name.location as isize - 1;
    while i >= 0 {
        let c = text[i as usize];
        if c == CLOSE_PAREN {
            depth += 1;
        } else if c == OPEN_PAREN {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if c == SEMICOLON || c == OPEN_BRACE || c == CLOSE_BRACE {
            return None;
        }
        i -= 1;
    }
    if i <= 0 {
        return None;
    }
    let i = i as usize;
    let close = matching(text, i);
    if close <= name.location as isize {
        return None;
    }
    foreach_source(text, R::new(i, close as usize - i + 1))
}

fn foreach_source(text: &[u16], name: R) -> Option<R> {
    let after = skip_space(text, name.end());
    if !(after + 2 < text.len()
        && text[after] == 0x69
        && text[after + 1] == 0x6E
        && is_space(text[after + 2]))
    {
        return None;
    }
    let open = type_start(text, name.location).and_then(|s| open_paren_before(text, s))?;
    if word(text, skip_space_backward(text, open)) != "foreach" {
        return None;
    }
    let close = matching(text, open);
    if close <= after as isize {
        return None;
    }
    let close = close as usize;
    let start = skip_space(text, after + 2);
    let mut end = close;
    while end > start && is_space(text[end - 1]) {
        end -= 1;
    }
    (end > start).then(|| R::new(start, end - start))
}

/// A pattern variable: `x is T name`, `x is not T name` — the range of `x`.
pub fn pattern_subject(text: &[u16], name: R) -> Option<R> {
    let type_at = type_start(text, name.location)?;
    let mut i = skip_space_backward(text, type_at);
    if word(text, i) == "not" {
        i = skip_space_backward(text, i.saturating_sub(3));
    }
    if word(text, i) != "is" {
        return None;
    }
    let end = skip_space_backward(text, i.saturating_sub(2));
    // The start of the expression left of `is`: up to a parenthesis, comma, `=`, `&&`, `||`, `!` of its level.
    let mut start = end;
    let mut depth = 0;
    while start > 0 {
        let c = text[start - 1];
        if c == CLOSE_PAREN || c == CLOSE_BRACKET {
            depth += 1;
        } else if c == OPEN_PAREN || c == OPEN_BRACKET {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if depth == 0
            && (c == COMMA
                || c == EQ
                || c == AMP
                || c == BAR
                || c == SEMICOLON
                || c == OPEN_BRACE
                || c == QUESTION
                || c == COLON
                || (c == 0x21 && (start >= text.len() || text[start] != EQ)))
        {
            break;
        }
        start -= 1;
    }
    start = skip_space(text, start);
    (end > start).then(|| R::new(start, end - start))
}

/// A parameter of a local function `void Process(T a, U b) { … }` at `name`:
/// the function's name and the parameter's number.
pub fn local_function_parameter(text: &[u16], name: R) -> Option<(R, usize)> {
    let mut depth = 0;
    let mut commas = 0;
    let mut i = name.location as isize - 1;
    while i >= 0 {
        let c = text[i as usize];
        if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == GT {
            depth += 1;
        } else if c == OPEN_PAREN || c == OPEN_BRACKET || c == LT {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if depth == 0 && c == COMMA {
            commas += 1;
        } else if c == SEMICOLON || c == OPEN_BRACE || c == CLOSE_BRACE || c == EQ {
            return None;
        }
        i -= 1;
    }
    if !(i > 0 && text[i as usize] == OPEN_PAREN) {
        return None;
    }
    let i = i as usize;
    let close = matching(text, i);
    if close <= name.location as isize {
        return None;
    }
    // After the parentheses comes a body: `{`, `=>` or generic constraints.
    let after = skip_space(text, close as usize + 1);
    if !(after + 1 < text.len()
        && (text[after] == OPEN_BRACE
            || (text[after] == EQ && text[after + 1] == GT)
            || word(text, text.len().min(after + 5)) == "where"))
    {
        return None;
    }
    // Before the parenthesis is a name, and before it a type: a declaration, not a call.
    let name_end = skip_space_backward(text, i);
    let mut name_start = name_end;
    while name_start > 0 && is_ident_part(text[name_start - 1]) {
        name_start -= 1;
    }
    if name_start >= name_end {
        return None;
    }
    let type_end = skip_space_backward(text, name_start);
    if type_end == 0 {
        return None;
    }
    let before = text[type_end - 1];
    let type_word = word(text, type_end);
    if !(before == GT
        || before == CLOSE_BRACKET
        || before == QUESTION
        || (is_ident_part(before)
            && ![
                "return", "await", "new", "else", "in", "is", "as", "case", "throw", "yield",
            ]
            .contains(&type_word.as_str())))
    {
        return None;
    }
    Some((R::new(name_start, name_end - name_start), commas))
}

/// The calls of the function `function` in `range`, except its declaration: ranges of the name.
pub fn calls(function: &str, text: &[u16], range: R, declaration: usize) -> Vec<R> {
    let target: Vec<u16> = function.encode_utf16().collect();
    let mut result = Vec::new();
    if target.is_empty() {
        return result;
    }
    let mut i = range.location;
    let end = range.end().min(text.len());
    while i + target.len() < end {
        if text[i] == QUOTE || text[i] == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if !(text[i] == target[0]
            && text[i..i + target.len()] == target[..]
            && (i == 0 || (!is_ident_part(text[i - 1]) && text[i - 1] != DOT))
            && !is_ident_part(text[i + target.len()])
            && i != declaration)
        {
            i += 1;
            continue;
        }
        let open = skip_space(text, i + target.len());
        if open < end && text[open] == OPEN_PAREN {
            result.push(R::new(i, target.len()));
        }
        i += target.len();
    }
    result
}

/// `out var x`, `out int x`, `out x`: the call puts the value at `name`.
pub fn is_out_argument(text: &[u16], name: R) -> bool {
    let mut i = skip_space_backward(text, name.location);
    if word(text, i) == "out" {
        return true;
    }
    // A declaration right in the argument: a type before the name.
    let Some(start) = type_start(text, name.location) else {
        return false;
    };
    if start >= name.location {
        return false;
    }
    i = skip_space_backward(text, start);
    word(text, i) == "out"
}

/// Where the chain `name` ends begins: `this.T`, `o.T` and `a.b.T` start at
/// `this`, `o` and `a`; a name with no receiver starts where it is.
#[must_use]
pub fn chain_start(text: &[u16], name: usize) -> usize {
    let mut start = name;
    loop {
        let mut i = skip_space_backward(text, start);
        if i > 0 && text[i - 1] == DOT {
            i -= 1;
            // `a?.b`
            if i > 0 && text[i - 1] == QUESTION {
                i -= 1;
            }
        } else {
            break;
        }
        let end = skip_space_backward(text, i);
        let mut begin = end;
        while begin > 0 && is_ident_part(text[begin - 1]) {
            begin -= 1;
        }
        if !(begin < end && is_ident_start(text[begin])) {
            break;
        }
        start = begin;
    }
    start
}

/// `ref x`, `ref this.x`, `ref o.x` in a call or a declaration: the place
/// is passed on, and what it is passed to may overwrite the value.
pub fn is_ref_argument(text: &[u16], name: R) -> bool {
    let start = chain_start(text, name.location);
    word(text, skip_space_backward(text, start)) == "ref"
}

/// `ref int r = ref this.T;`, `r = ref T;`: the local `r` is another name
/// for the place `name` is the end of a chain of, and what is written to
/// `r` is written there.
#[must_use]
pub fn ref_alias(text: &[u16], name: R) -> Option<R> {
    let start = chain_start(text, name.location);
    let keyword = skip_space_backward(text, start);
    if word(text, keyword) != "ref" {
        return None;
    }
    let equals = skip_space_backward(text, keyword - 3);
    if equals == 0 || text[equals - 1] != EQ {
        return None;
    }
    // Not `==`, `!=`, `<=`, `>=`, `+=`…: a plain assignment or initializer.
    if equals >= 2 && matches!(text[equals - 2], c if c == EQ || c == 0x21 || c == LT || c == GT) {
        return None;
    }
    let end = skip_space_backward(text, equals - 1);
    let alias = word(text, end);
    if alias.is_empty() || !is_ident_start(text[end - alias.encode_utf16().count()]) {
        return None;
    }
    let length = alias.encode_utf16().count();
    Some(R::new(end - length, length))
}

/// `return ref x;` and `=> ref x`: the method hands out the place.
#[must_use]
pub fn is_ref_return(text: &[u16], name: R) -> bool {
    let start = chain_start(text, name.location);
    let keyword = skip_space_backward(text, start);
    if word(text, keyword) != "ref" {
        return false;
    }
    let before = skip_space_backward(text, keyword - 3);
    word(text, before) == "return"
        || (before >= 2 && text[before - 2] == EQ && text[before - 1] == GT)
}

/// A lambda parameter: `x => …`, `(a, b) => …`, `(int a) => …`.
pub fn is_lambda_parameter(text: &[u16], name: R) -> bool {
    let mut i = skip_space(text, name.end());
    if i + 1 < text.len() && text[i] == EQ && text[i + 1] == GT {
        return true;
    }
    if !(i < text.len() && (text[i] == COMMA || text[i] == CLOSE_PAREN)) {
        return false;
    }
    // Up to the list's closing parenthesis, followed by `=>`.
    let mut depth = 0;
    while i < text.len() {
        let c = text[i];
        if c == OPEN_PAREN {
            depth += 1;
        } else if c == CLOSE_PAREN {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if c == SEMICOLON || c == OPEN_BRACE {
            return false;
        }
        i += 1;
    }
    let arrow = skip_space(text, i + 1);
    arrow + 1 < text.len() && text[arrow] == EQ && text[arrow + 1] == GT
}

/// The call that was given a lambda with the parameter `name`: `list.ForEach`
/// of `list.ForEach(x => …)`, `QueryAsync` of `QueryAsync(sql, (m, v) => …)`.
pub fn lambda_call(text: &[u16], name: R) -> Option<Source> {
    let mut start = name.location;
    // `(a, b) => …`: from the parenthesis of the parameter list.
    let after = skip_space(text, name.end());
    if after < text.len() && (text[after] == COMMA || text[after] == CLOSE_PAREN) {
        let mut depth = 0;
        let mut i = name.location as isize - 1;
        while i >= 0 {
            let c = text[i as usize];
            if c == CLOSE_PAREN {
                depth += 1;
            } else if c == OPEN_PAREN {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            } else if c == SEMICOLON || c == OPEN_BRACE || c == CLOSE_BRACE {
                return None;
            }
            i -= 1;
        }
        if i < 0 {
            return None;
        }
        start = i as usize;
    }
    enclosing_call(text, start)
}

/// The name stands in the square brackets of an element access (`data[index]`):
/// it is a key, not what the value is made of.
pub fn is_index_key(text: &[u16], offset: usize, from: usize) -> bool {
    let mut depth = 0;
    let mut i = offset as isize - 1;
    while i >= from as isize {
        let c = text[i as usize];
        if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            depth += 1;
        } else if c == OPEN_PAREN || c == OPEN_BRACE {
            if depth > 0 {
                depth -= 1;
            }
        } else if c == OPEN_BRACKET {
            if depth > 0 {
                depth -= 1;
            } else {
                // `[` after a name or a parenthesis is an element access, not an array `new[] { }`.
                let before = skip_space_backward(text, i as usize);
                if before > from
                    && (is_ident_part(text[before - 1])
                        || text[before - 1] == CLOSE_PAREN
                        || text[before - 1] == CLOSE_BRACKET)
                    && word(text, before) != "new"
                {
                    return true;
                }
            }
        }
        i -= 1;
    }
    false
}

/// The call whose parentheses hold `offset`: for `_stash.Get(e, out x)` the
/// source `_stash.Get` with the range of the name `Get`.
pub fn enclosing_call(text: &[u16], offset: usize) -> Option<Source> {
    let name = called_name(text, offset)?;
    let mut words = vec![string(text, name)];
    let mut links = vec![name];
    let mut start = name.location;
    loop {
        let dot_at = skip_space_backward(text, start);
        if !(dot_at > 0 && text[dot_at - 1] == DOT) {
            break;
        }
        let end = skip_space_backward(text, dot_at - 1);
        let mut begin = end;
        while begin > 0 && is_ident_part(text[begin - 1]) {
            begin -= 1;
        }
        if !(begin < end && is_ident_start(text[begin])) {
            break;
        }
        words.insert(0, string(text, R::new(begin, end - begin)));
        links.insert(0, R::new(begin, end - begin));
        start = begin;
    }
    if words.len() > 1 && (words[0] == "this" || words[0] == "base") {
        words.remove(0);
        links.remove(0);
    }
    let mut source = Source::new(name, words.join("."), true);
    source.head = links.first().copied();
    source.links = links;
    Some(source)
}

fn called_name(text: &[u16], offset: usize) -> Option<R> {
    let mut depth = 0;
    let mut i = offset as isize - 1;
    while i >= 0 {
        let c = text[i as usize];
        if c == CLOSE_PAREN || c == CLOSE_BRACKET {
            depth += 1;
        } else if c == OPEN_PAREN || c == OPEN_BRACKET {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if depth == 0 && (c == SEMICOLON || c == OPEN_BRACE || c == CLOSE_BRACE) {
            return None;
        }
        i -= 1;
    }
    if !(i > 0 && text[i as usize] == OPEN_PAREN) {
        return None;
    }
    let mut end = skip_space_backward(text, i as usize);
    // `M<T>(…)`: the name before the generic.
    if end > 0 && text[end - 1] == GT {
        let mut angle = 0;
        let mut k = end as isize - 1;
        while k >= 0 {
            let c = text[k as usize];
            if c == GT {
                angle += 1;
            } else if c == LT {
                angle -= 1;
                if angle == 0 {
                    break;
                }
            }
            k -= 1;
        }
        end = skip_space_backward(text, k.max(0) as usize);
    }
    let mut start = end;
    while start > 0 && is_ident_part(text[start - 1]) {
        start -= 1;
    }
    if !(start < end && is_ident_start(text[start])) {
        return None;
    }
    let name = string(text, R::new(start, end - start));
    if KEYWORDS.contains(&name.as_str())
        || [
            "if", "while", "for", "foreach", "switch", "using", "lock", "catch",
        ]
        .contains(&name.as_str())
    {
        None
    } else {
        Some(R::new(start, end - start))
    }
}

/// What the getter of the property `property` (its whole declaration) returns:
/// `T P => x;`, `get => x;`, `get { return x; }`.
pub fn getter_expressions(text: &[u16], property: R, name: R) -> Vec<R> {
    let end = property.end();
    let mut i = skip_space(text, name.end());
    // An indexer: `this[int i]`.
    if i < end && text[i] == OPEN_BRACKET {
        let close = matching(text, i);
        if close <= i as isize {
            return Vec::new();
        }
        i = skip_space(text, close as usize + 1);
    }
    if i + 1 >= end {
        return Vec::new();
    }
    if text[i] == EQ && text[i + 1] == GT {
        let body = rhs(text, i + 2);
        return if body.length > 0 {
            vec![body]
        } else {
            Vec::new()
        };
    }
    if text[i] != OPEN_BRACE {
        return Vec::new();
    }
    let close = matching(text, i);
    if close <= i as isize {
        return Vec::new();
    }
    let accessors = R::new(i + 1, close as usize - i - 1);
    let Some(get) = keyword("get", text, accessors) else {
        return Vec::new();
    };
    let after = skip_space(text, get.end());
    if after + 1 < end && text[after] == EQ && text[after + 1] == GT {
        let body = rhs(text, after + 2);
        return if body.length > 0 {
            vec![body]
        } else {
            Vec::new()
        };
    }
    if !(after < end && text[after] == OPEN_BRACE) {
        return Vec::new();
    }
    let body_end = matching(text, after);
    if body_end <= after as isize {
        return Vec::new();
    }
    returned_expressions(text, R::new(after, body_end as usize - after + 1))
}

/// The property's setter (`set` or `init`) whole: inside it `value` is
/// what is assigned to the property.
pub fn setter(text: &[u16], property: R, name: R) -> Option<R> {
    let end = property.end();
    let mut i = skip_space(text, name.end());
    if i < end && text[i] == OPEN_BRACKET {
        let close = matching(text, i);
        if close <= i as isize {
            return None;
        }
        i = skip_space(text, close as usize + 1);
    }
    if !(i < end && text[i] == OPEN_BRACE) {
        return None;
    }
    let close = matching(text, i);
    if close <= i as isize {
        return None;
    }
    let close = close as usize;
    let accessors = R::new(i + 1, close - i - 1);
    let set = keyword("set", text, accessors).or_else(|| keyword("init", text, accessors))?;
    let after = skip_space(text, set.end());
    if after < close && text[after] == OPEN_BRACE {
        let body_end = matching(text, after);
        return (body_end > after as isize)
            .then(|| R::new(set.location, body_end as usize - set.location + 1));
    }
    if !(after + 1 < close && text[after] == EQ && text[after + 1] == GT) {
        return None;
    }
    let body = rhs(text, after + 2);
    Some(R::new(set.location, body.end() - set.location))
}

/// `{ get; set; } = x;`: the initial value of an auto-property.
pub fn property_initializer(text: &[u16], property: R, name: R) -> Option<R> {
    let i = skip_space(text, name.end());
    if !(i < property.end() && text[i] == OPEN_BRACE) {
        return None;
    }
    let close = matching(text, i);
    if close <= i as isize {
        return None;
    }
    let eq_at = skip_space(text, close as usize + 1);
    if !(eq_at + 1 < text.len()
        && text[eq_at] == EQ
        && text[eq_at + 1] != EQ
        && text[eq_at + 1] != GT)
    {
        return None;
    }
    let value = rhs(text, eq_at + 1);
    (value.length > 0).then_some(value)
}

/// Comma-separated elements of the top level, without surrounding spaces.
fn tuple_elements(text: &[u16], inner: R) -> Vec<R> {
    let mut result = Vec::new();
    let mut depth = 0;
    let mut start = inner.location;
    let mut i = inner.location;
    while i < inner.end() {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE || c == LT {
            depth += 1;
        } else if (c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE || c == GT)
            && depth > 0
        {
            depth -= 1;
        } else if c == COMMA && depth == 0 {
            result.push(trimmed(text, R::new(start, i - start)));
            start = i + 1;
        }
        i += 1;
    }
    result.push(trimmed(text, R::new(start, inner.end() - start)));
    result
}

/// The first word `word` in `range` at the top level of parentheses.
fn keyword(keyword: &str, text: &[u16], range: R) -> Option<R> {
    let target: Vec<u16> = keyword.encode_utf16().collect();
    let mut i = range.location;
    let mut depth = 0;
    while i + target.len() <= range.end() {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == OPEN_BRACE || c == OPEN_PAREN {
            depth += 1;
        } else if c == CLOSE_BRACE || c == CLOSE_PAREN {
            depth -= 1;
        }
        if depth == 0
            && c == target[0]
            && text[i..i + target.len()] == target[..]
            && (i == 0 || !is_ident_part(text[i - 1]))
            && (i + target.len() >= text.len() || !is_ident_part(text[i + target.len()]))
        {
            return Some(R::new(i, target.len()));
        }
        i += 1;
    }
    None
}

/// The start of the type before a declared name: `var x`, `ref Foo<int> x`,
/// `List<int>[] x`. `None` when there is no type before the name.
fn type_start(text: &[u16], position: usize) -> Option<usize> {
    let mut i = skip_space_backward(text, position);
    if i == 0 {
        return None;
    }
    let end = i;
    let mut angle = 0;
    while i > 0 {
        let c = text[i - 1];
        if c == GT {
            angle += 1;
        } else if c == LT {
            if angle <= 0 {
                break;
            }
            angle -= 1;
        } else if !(is_ident_part(c)
            || c == DOT
            || c == QUESTION
            || c == OPEN_BRACKET
            || c == CLOSE_BRACKET
            || (angle > 0 && (c == COMMA || is_space(c))))
        {
            break;
        }
        i -= 1;
    }
    (i < end && is_ident_start(text[i])).then_some(i)
}

/// An opening parenthesis right before `position` (past spaces and `ref`/`var`).
fn open_paren_before(text: &[u16], position: usize) -> Option<usize> {
    let mut i = skip_space_backward(text, position);
    let before = word(text, i);
    if before == "ref" || before == "await" {
        i = skip_space_backward(text, i - before.encode_utf16().count());
    }
    (i > 0 && text[i - 1] == OPEN_PAREN).then(|| i - 1)
}

// MARK: - Conditions and calls

/// `foreach (… in X)` whose body holds `offset`: the range of X.
/// The innermost loop around the place wins.
pub fn enclosing_foreach(text: &[u16], range: R, offset: usize) -> Option<R> {
    let keyword: Vec<u16> = "foreach".encode_utf16().collect();
    let mut best = None;
    let mut i = range.location;
    let end = range.end().min(offset);
    while i + keyword.len() < end {
        if !(text[i] == keyword[0]
            && text[i..i + keyword.len()] == keyword[..]
            && (i == 0 || !is_ident_part(text[i - 1]))
            && !is_ident_part(text[i + keyword.len()]))
        {
            i += 1;
            continue;
        }
        let mut j = skip_space(text, i + keyword.len());
        if !(j < text.len() && text[j] == OPEN_PAREN) {
            i += 1;
            continue;
        }
        let close = matching(text, j);
        if close <= j as isize {
            i += 1;
            continue;
        }
        let close = close as usize;
        // `in` at the top level of the parentheses.
        let mut k = j + 1;
        let mut source = None;
        while k < close {
            if text[k] == 0x69
                && k + 1 < close
                && text[k + 1] == 0x6E
                && is_space(text[k - 1])
                && k + 2 < close
                && is_space(text[k + 2])
            {
                let s = skip_space(text, k + 2);
                let mut e = close;
                while e > s && is_space(text[e - 1]) {
                    e -= 1;
                }
                source = Some(R::new(s, e - s));
                break;
            }
            k += 1;
        }
        // The body: a block in braces or a single statement.
        j = skip_space(text, close + 1);
        let body_end: isize = if j < text.len() && text[j] == OPEN_BRACE {
            matching(text, j)
        } else {
            let mut e = j;
            while e < text.len() && text[e] != SEMICOLON {
                e += 1;
            }
            e as isize
        };
        if let Some(source) = source
            && offset > close
            && offset as isize <= body_end
        {
            best = Some(source);
        }
        i = close;
    }
    best
}

/// The components of an ECS filter: `Filter.With<A>().With<B>().Without<C>()`.
pub fn filter_components(text: &[u16], range: R) -> (Vec<String>, Vec<String>) {
    let mut with = Vec::new();
    let mut without = Vec::new();
    let expression: Vec<char> = string(text, range).chars().collect();
    // `\.(With|Without)\s*<\s*([A-Za-z_][\w.]*)\s*>`
    let mut i = 0;
    while i < expression.len() {
        if expression[i] != '.' {
            i += 1;
            continue;
        }
        let rest: String = expression[i + 1..].iter().take(7).collect();
        let (kind, length) = if rest.starts_with("Without") {
            ("Without", 7)
        } else if rest.starts_with("With") {
            ("With", 4)
        } else {
            i += 1;
            continue;
        };
        let mut j = i + 1 + length;
        while j < expression.len() && is_regex_space(expression[j]) {
            j += 1;
        }
        if !(j < expression.len() && expression[j] == '<') {
            i += 1;
            continue;
        }
        j += 1;
        while j < expression.len() && is_regex_space(expression[j]) {
            j += 1;
        }
        if !(j < expression.len() && (expression[j].is_ascii_alphabetic() || expression[j] == '_'))
        {
            i += 1;
            continue;
        }
        let name_start = j;
        j += 1;
        while j < expression.len() && (is_regex_word(expression[j]) || expression[j] == '.') {
            j += 1;
        }
        // `[\w.]*` is greedy and `\s*>` follows: no backtracking over dots is needed —
        // a dot or a letter is neither a space nor `>`, so there is one match.
        let name_end = j;
        while j < expression.len() && is_regex_space(expression[j]) {
            j += 1;
        }
        if !(j < expression.len() && expression[j] == '>') {
            i += 1;
            continue;
        }
        let full: String = expression[name_start..name_end].iter().collect();
        let name = full
            .split('.')
            .rfind(|p| !p.is_empty())
            .unwrap_or("")
            .to_owned();
        if kind == "With" {
            with.push(name);
        } else {
            without.push(name);
        }
        i = j + 1;
    }
    (with, without)
}

/// `\s` of a regular expression.
fn is_regex_space(c: char) -> bool {
    c.is_whitespace()
}

/// `\w` of a regular expression: letters, digits, combining marks and joiners.
fn is_regex_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || matches!(c, '\u{300}'..='\u{36f}' | '\u{203f}' | '\u{2040}')
}

/// The call argument number `index` after the method name at `name`: `M(a, ref b, c: d)`.
pub fn argument(text: &[u16], name: R, index: usize) -> Option<R> {
    let mut i = skip_space(text, name.end());
    // Explicit generics: `M<T>(…)`.
    if i < text.len() && text[i] == LT {
        let mut depth = 0;
        while i < text.len() {
            if text[i] == LT {
                depth += 1;
            } else if text[i] == GT {
                depth -= 1;
                if depth == 0 {
                    i += 1;
                    break;
                }
            }
            i += 1;
        }
        i = skip_space(text, i);
    }
    if !(i < text.len() && text[i] == OPEN_PAREN) {
        return None;
    }
    let close = matching(text, i);
    if close <= i as isize {
        return None;
    }
    let close = close as usize;
    let mut arguments: Vec<R> = Vec::new();
    let mut start = i + 1;
    let mut depth: i64 = 0;
    let mut k = i + 1;
    while k <= close {
        let c = text[k];
        if c == QUOTE || c == APOSTROPHE {
            k = skip_literal(text, k);
            continue;
        }
        if k == close || (depth == 0 && c == COMMA) {
            arguments.push(R::new(start, k - start));
            start = k + 1;
        } else if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE || c == LT {
            depth += 1;
        } else if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE || c == GT {
            depth = (depth - 1).max(0);
        }
        k += 1;
    }
    let argument = *arguments.get(index)?;
    // Without `ref`/`out`/`in` and a name `name:`.
    let mut s = skip_space(text, argument.location);
    for modifier in ["ref", "out", "in"] {
        let m: Vec<u16> = modifier.encode_utf16().collect();
        if s + m.len() < argument.end()
            && text[s..s + m.len()] == m[..]
            && is_space(text[s + m.len()])
        {
            s = skip_space(text, s + m.len());
        }
    }
    let mut n = s;
    while n < argument.end() && is_ident_part(text[n]) {
        n += 1;
    }
    let colon = skip_space(text, n);
    if n > s
        && colon < argument.end()
        && text[colon] == 0x3A
        && colon + 1 < text.len()
        && text[colon + 1] != 0x3A
    {
        s = skip_space(text, colon + 1);
    }
    let mut e = argument.end();
    while e > s && is_space(text[e - 1]) {
        e -= 1;
    }
    let length = e.saturating_sub(s);
    (length > 0).then(|| R::new(s, length))
}

/// The default value of a parameter `int n = 5` (the range of the whole parameter).
pub fn default_value(text: &[u16], parameter: R) -> Option<R> {
    let mut depth = 0;
    let mut i = parameter.location;
    while i < parameter.end() {
        let c = text[i];
        if c == LT || c == OPEN_PAREN || c == OPEN_BRACKET {
            depth += 1;
        } else if c == GT || c == CLOSE_PAREN || c == CLOSE_BRACKET {
            depth -= 1;
        } else if depth == 0
            && c == EQ
            && i + 1 < text.len()
            && text[i + 1] != EQ
            && text[i + 1] != GT
        {
            let start = skip_space(text, i + 1);
            let mut end = parameter.end();
            while end > start && is_space(text[end - 1]) {
                end -= 1;
            }
            return (end > start).then(|| R::new(start, end - start));
        }
        i += 1;
    }
    None
}

/// The expressions of `return …;` in a method body, and an expression body `=> …;`.
pub fn returned_expressions(text: &[u16], method: R) -> Vec<R> {
    let mut result = Vec::new();
    let keyword: Vec<u16> = "return".encode_utf16().collect();
    let mut i = method.location;
    let end = method.end();
    let mut saw_brace = false;
    while i < end {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == OPEN_BRACE {
            saw_brace = true;
        }
        // `=> expression;` before the first brace is an expression body.
        if !saw_brace && c == EQ && i + 1 < end && text[i + 1] == GT {
            let found = rhs(text, i + 2);
            if found.length > 0 {
                result.push(found);
            }
            return result;
        }
        if c == keyword[0]
            && i + keyword.len() < end
            && text[i..i + keyword.len()] == keyword[..]
            && (i == 0 || !is_ident_part(text[i - 1]))
            && !is_ident_part(text[i + keyword.len()])
        {
            let found = rhs(text, i + keyword.len());
            if found.length > 0 {
                result.push(found);
            }
            i = found.end();
            continue;
        }
        i += 1;
    }
    result
}

/// The start of a `switch` expression arm if the `=>` at `arrow` is its arrow:
/// after the nearest unclosed `{` (with `switch` before it) or a comma inside it.
fn switch_arm_start(text: &[u16], arrow: usize, start: usize) -> Option<usize> {
    let mut depth = 0;
    let mut i = arrow as isize - 1;
    let mut arm: Option<usize> = None;
    while i >= start as isize {
        let c = text[i as usize];
        if c == CLOSE_BRACE || c == CLOSE_PAREN || c == CLOSE_BRACKET {
            depth += 1;
        } else if c == OPEN_PAREN || c == OPEN_BRACKET {
            if depth == 0 {
                return None;
            }
            depth -= 1;
        } else if c == OPEN_BRACE {
            if depth == 0 {
                if word(text, skip_space_backward(text, i as usize)) != "switch" {
                    return None;
                }
                return Some(arm.unwrap_or(i as usize + 1));
            }
            depth -= 1;
        } else if c == COMMA && depth == 0 && arm.is_none() {
            arm = Some(i as usize + 1);
        } else if c == SEMICOLON && depth == 0 {
            return None;
        }
        i -= 1;
    }
    None
}

/// The end of the lambda body started at `start`: a block in braces or an
/// expression up to a comma, parenthesis or `;` of its level.
fn lambda_body_end(text: &[u16], start: usize, limit: usize) -> usize {
    if start < limit && text[start] == OPEN_BRACE {
        let close = matching(text, start);
        return if close > start as isize {
            close as usize + 1
        } else {
            limit
        };
    }
    let mut depth = 0;
    let mut i = start;
    while i < limit {
        let c = text[i];
        if c == QUOTE || c == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if c == OPEN_PAREN || c == OPEN_BRACKET || c == OPEN_BRACE {
            depth += 1;
        } else if c == CLOSE_PAREN || c == CLOSE_BRACKET || c == CLOSE_BRACE {
            if depth == 0 {
                return i;
            }
            depth -= 1;
        } else if depth == 0 && (c == COMMA || c == SEMICOLON) {
            return i;
        }
        i += 1;
    }
    limit
}

/// A type parameter: `T` in `class Box<T>` or `void M<in T, U>()`.
pub fn is_type_parameter(text: &[u16], name: R) -> bool {
    let mut before = skip_space_backward(text, name.location);
    let variance = word(text, before);
    if variance == "in" || variance == "out" {
        before = skip_space_backward(
            text,
            before.saturating_sub(2 + usize::from(variance == "out")),
        );
    }
    let after = skip_space(text, name.end());
    if !(before > 0
        && after < text.len()
        && (text[before - 1] == LT || text[before - 1] == COMMA)
        && (text[after] == GT || text[after] == COMMA))
    {
        return false;
    }
    // The list opens after the name of a type or method.
    let mut i = before - 1;
    while i > 0 && text[i] != LT {
        if !(is_ident_part(text[i]) || is_space(text[i]) || text[i] == COMMA) {
            return false;
        }
        i -= 1;
    }
    if i == 0 {
        return false;
    }
    let back = skip_space_backward(text, i);
    back > 0 && is_ident_part(text[back - 1])
}

/// `var (a, b) = F()`, `(var a, var b) = F()`: for a name in the parentheses,
/// the right-hand side of the deconstruction.
pub fn deconstruction(text: &[u16], name: R) -> Option<R> {
    let mut depth = 0;
    let mut i = name.location as isize - 1;
    while i >= 0 {
        let c = text[i as usize];
        if c == CLOSE_PAREN {
            depth += 1;
        } else if c == OPEN_PAREN {
            if depth == 0 {
                break;
            }
            depth -= 1;
        } else if c == SEMICOLON || c == OPEN_BRACE || c == CLOSE_BRACE || c == EQ {
            return None;
        }
        i -= 1;
    }
    if i < 0 {
        return None;
    }
    let i = i as usize;
    // Before the parenthesis is `var` or the start of a statement, not a method name.
    let before = skip_space_backward(text, i);
    let head = word(text, before);
    if !(head == "var" || head.is_empty()) {
        return None;
    }
    let close = matching(text, i);
    if close <= i as isize {
        return None;
    }
    let eq_at = skip_space(text, close as usize + 1);
    if !(eq_at + 1 < text.len()
        && text[eq_at] == EQ
        && text[eq_at + 1] != EQ
        && text[eq_at + 1] != GT)
    {
        return None;
    }
    let value = trimmed(text, rhs(text, eq_at + 1));
    if value.length == 0 {
        return None;
    }
    // `(x, y) = (1, 2)`: each name has its own tuple element on the right.
    let names = tuple_elements(text, R::new(i + 1, close as usize - i - 1));
    let values = if text[value.location] == OPEN_PAREN
        && matching(text, value.location) == value.end() as isize - 1
    {
        tuple_elements(text, R::new(value.location + 1, value.length - 2))
    } else {
        Vec::new()
    };
    if names.len() > 1
        && names.len() == values.len()
        && let Some(index) = names.iter().position(|n| n.contains(name.location))
    {
        return Some(values[index]);
    }
    Some(value)
}

/// The opening round parenthesis of the closing one at `close`.
pub fn matching_backward(text: &[u16], close: usize) -> Option<usize> {
    let mut depth = 0;
    let mut i = close as isize;
    while i >= 0 {
        let c = text[i as usize];
        if c == CLOSE_PAREN {
            depth += 1;
        } else if c == OPEN_PAREN {
            depth -= 1;
            if depth == 0 {
                return Some(i as usize);
            }
        }
        i -= 1;
    }
    None
}

/// The closing bracket of the opening one at `open` (round or curly); -1: none.
pub fn matching(text: &[u16], open: usize) -> isize {
    let o = text[open];
    let c = if o == OPEN_PAREN {
        CLOSE_PAREN
    } else if o == OPEN_BRACE {
        CLOSE_BRACE
    } else {
        CLOSE_BRACKET
    };
    let mut depth = 0;
    let mut i = open;
    while i < text.len() {
        let ch = text[i];
        if ch == QUOTE || ch == APOSTROPHE {
            i = skip_literal(text, i);
            continue;
        }
        if ch == SLASH && i + 1 < text.len() && text[i + 1] == SLASH {
            while i < text.len() && text[i] != NEWLINE {
                i += 1;
            }
            continue;
        }
        if ch == o {
            depth += 1;
        } else if ch == c {
            depth -= 1;
            if depth == 0 {
                return i as isize;
            }
        }
        i += 1;
    }
    -1
}

// MARK: - Small things

pub(crate) const KEYWORDS: &[&str] = &[
    "new",
    "true",
    "false",
    "null",
    "this",
    "base",
    "var",
    "ref",
    "out",
    "in",
    "typeof",
    "nameof",
    "default",
    "is",
    "as",
    "await",
    "sizeof",
    "stackalloc",
    "checked",
    "unchecked",
    "when",
    "and",
    "or",
    "not",
    "switch",
    "with",
    "int",
    "float",
    "double",
    "bool",
    "string",
    "long",
    "short",
    "byte",
    "uint",
    "ulong",
    "ushort",
    "sbyte",
    "char",
    "decimal",
    "object",
    "void",
    "nint",
    "nuint",
    "dynamic",
    // Statements and modifiers get into a right-hand side from the bodies of
    // lambdas and local functions.
    "if",
    "else",
    "for",
    "foreach",
    "while",
    "do",
    "return",
    "break",
    "continue",
    "goto",
    "throw",
    "try",
    "catch",
    "finally",
    "lock",
    "using",
    "fixed",
    "yield",
    "case",
    "static",
    "async",
    "const",
    "readonly",
    "unsafe",
    "delegate",
    "params",
    "scoped",
];

fn looks_generic(text: &[u16], from: usize, end: usize) -> bool {
    let Some(after) = type_arguments(text, from, end) else {
        return false;
    };
    let next = skip_space(text, after);
    next < end && text[next] == OPEN_PAREN
}

#[cfg(test)]
mod cases;

#[cfg(test)]
mod tests {
    use super::*;

    fn utf16(text: &str) -> Vec<u16> {
        text.encode_utf16().collect()
    }

    /// The first `what` in `s`.
    fn first(s: &str, what: &str) -> Utf16Range {
        let units = utf16(s);
        let needle = utf16(what);
        let at = (0..=units.len().saturating_sub(needle.len()))
            .find(|&i| units[i..i + needle.len()] == needle[..])
            .expect("present");
        Utf16Range::new(at, needle.len())
    }

    #[test]
    fn writes_and_reads() {
        let access_of = |line: &str, name: &str| access(&utf16(line), first(line, name));
        let rhs_text = |line: &str, name: &str| -> Option<String> {
            match access_of(line, name) {
                Access::Write { rhs: Some(rhs), .. } => Some(string(&utf16(line), rhs)),
                _ => None,
            }
        };
        assert_eq!(
            rhs_text("health.Value = d.Amount;", "Value").as_deref(),
            Some("d.Amount")
        );
        assert_eq!(
            access_of("if (health.Value == 0) return;", "Value"),
            Access::Read
        );
        assert_eq!(access_of("var x = c.Value;", "Value"), Access::Read);
        assert_eq!(
            access_of("Func<int> f = () => Value;", "Value"),
            Access::Read
        );
        assert_eq!(
            access_of("c.Count++;", "Count"),
            Access::Write {
                rhs: None,
                compound: true
            }
        );
        assert_eq!(
            access_of("++c.Count;", "Count"),
            Access::Write {
                rhs: None,
                compound: true
            }
        );
        assert_eq!(
            rhs_text("hp.Value -= damage * 2;", "Value").as_deref(),
            Some("damage * 2")
        );
        assert_eq!(
            rhs_text(
                "store.Set(e, new Health { Value = max, Regen = 1 });",
                "Value"
            )
            .as_deref(),
            Some("max"),
            "an initializer: up to the comma of its level"
        );
        assert_eq!(
            rhs_text("new Health { Value = Math.Max(a, b) }", "Value").as_deref(),
            Some("Math.Max(a, b)")
        );
        assert_eq!(
            access_of("Parse(s, out stats.Level);", "Level"),
            Access::Write {
                rhs: None,
                compound: false
            }
        );
        assert_eq!(
            rhs_text("d.Name = \"a;b\";", "Name").as_deref(),
            Some("\"a;b\"")
        );
        assert_eq!(
            rhs_text(
                "var map = new Dictionary<(Rarity r, Kind k), int>();",
                "map"
            )
            .as_deref(),
            Some("new Dictionary<(Rarity r, Kind k), int>()")
        );
        assert_eq!(
            rhs_text("int a = b < c, d = e;", "a").as_deref(),
            Some("b < c")
        );
    }

    #[test]
    fn nested_field() {
        let line = "c.Pos.x = 1;";
        assert_eq!(
            access(&utf16(line), first(line, "Pos")),
            Access::Write {
                rhs: Some(Utf16Range::new(10, 1)),
                compound: true
            }
        );
        let call = "c.Pos.Normalize();";
        assert_eq!(access(&utf16(call), first(call, "Pos")), Access::Read);
    }
}
