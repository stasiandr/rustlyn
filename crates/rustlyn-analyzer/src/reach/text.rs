//! What the text around a name says that its symbol does not: whether the
//! name is read or written there, which method is called on it, which
//! generic method it is a type argument of. In bytes of UTF-8: every
//! character looked at is ASCII, and a byte of a longer character counts as
//! part of a name.

/// What is done to a name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Access {
    Read,
    Write,
    /// `x += 1`, `x++`, `ref x`: the old value is part of the new one.
    Both,
}

const fn is_ident(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte >= 0x80
}

fn skip_space(text: &[u8], mut at: usize) -> usize {
    while at < text.len() && text[at].is_ascii_whitespace() {
        at += 1;
    }
    at
}

/// The position right after the last character before `at` that is not
/// whitespace.
fn skip_space_back(text: &[u8], mut at: usize) -> usize {
    while at > 0 && text[at - 1].is_ascii_whitespace() {
        at -= 1;
    }
    at
}

/// The identifier that starts at `at`: where it ends.
fn ident_end(text: &[u8], mut at: usize) -> usize {
    while at < text.len() && is_ident(text[at]) {
        at += 1;
    }
    at
}

/// The identifier that ends at `at`: where it starts.
fn ident_start(text: &[u8], mut at: usize) -> usize {
    while at > 0 && is_ident(text[at - 1]) {
        at -= 1;
    }
    at
}

fn str_of(text: &[u8], from: usize, to: usize) -> &str {
    std::str::from_utf8(&text[from..to]).unwrap_or_default()
}

/// The byte a line starts at; the end of the text for a line past it.
pub(crate) fn line_start(text: &[u8], line: usize) -> usize {
    if line == 0 {
        return 0;
    }
    let mut seen = 0;
    for (at, &byte) in text.iter().enumerate() {
        if byte == b'\n' {
            seen += 1;
            if seen == line {
                return at + 1;
            }
        }
    }
    text.len()
}

/// Whether an assignment operator starts at `at`, and whether it keeps the
/// old value (`+=`, `++`).
fn assignment_at(text: &[u8], at: usize) -> Option<Access> {
    let rest = &text[at.min(text.len())..];
    let starts = |prefix: &[u8]| rest.starts_with(prefix);
    if starts(b"=") {
        return (!starts(b"==") && !starts(b"=>")).then_some(Access::Write);
    }
    if starts(b"++") || starts(b"--") {
        return Some(Access::Both);
    }
    for operator in [
        &b"+="[..],
        b"-=",
        b"*=",
        b"/=",
        b"%=",
        b"&=",
        b"|=",
        b"^=",
        b"<<=",
        b">>=",
        b"??=",
    ] {
        if starts(operator) {
            return Some(Access::Both);
        }
    }
    None
}

/// What is done to the name at `start..end`.
pub(crate) fn access(text: &[u8], start: usize, end: usize) -> Access {
    if let Some(found) = assignment_at(text, skip_space(text, end)) {
        return found;
    }
    // `++x`, `out x`, `ref x`. The name may be qualified: `ref this.x`.
    let mut head = start;
    loop {
        let before = skip_space_back(text, head);
        if before > 0 && text[before - 1] == b'.' {
            let dot = skip_space_back(text, before - 1);
            let from = ident_start(text, dot);
            if from < dot {
                head = from;
                continue;
            }
        }
        head = before;
        break;
    }
    if head >= 2 && (&text[head - 2..head] == b"++" || &text[head - 2..head] == b"--") {
        return Access::Both;
    }
    // Only a whole argument is passed by reference: in `ref a.b.Get(e)` it
    // is what `Get` returns, not `b`.
    if !matches!(text.get(skip_space(text, end)), Some(&b',' | &b')')) {
        return Access::Read;
    }
    let from = ident_start(text, head);
    match str_of(text, from, head) {
        "out" => Access::Write,
        "ref" => Access::Both,
        _ => Access::Read,
    }
}

/// `name.Method(` right after the name that ends at `end`: `Method`.
pub(crate) fn method_after(text: &[u8], end: usize) -> Option<&str> {
    let dot = skip_space(text, end);
    if text.get(dot) != Some(&b'.') {
        return None;
    }
    let from = skip_space(text, dot + 1);
    let to = ident_end(text, from);
    let open = skip_space(text, to);
    (to > from && matches!(text.get(open), Some(&b'(' | &b'<'))).then(|| str_of(text, from, to))
}

/// The generic method or type the name at `start` is a type argument of:
/// `With<Game.Health>` for `Health` → `With`. The first argument only.
pub(crate) fn generic_owner(text: &[u8], start: usize) -> Option<&str> {
    let mut at = start;
    loop {
        at = skip_space_back(text, at);
        if at == 0 {
            return None;
        }
        match text[at - 1] {
            b'<' => break,
            // The qualifier of the name: `Game.` or `global::`.
            b'.' | b':' => {
                at -= 1;
                while at > 0 && text[at - 1] == b':' {
                    at -= 1;
                }
                let dot = skip_space_back(text, at);
                let from = ident_start(text, dot);
                if from == dot {
                    return None;
                }
                at = from;
            }
            _ => return None,
        }
    }
    let to = skip_space_back(text, at - 1);
    let from = ident_start(text, to);
    (from < to).then(|| str_of(text, from, to))
}

/// The closing parenthesis for the one that opens at `open`.
fn matching(text: &[u8], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut at = open;
    while at < text.len() {
        match text[at] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(at);
                }
            }
            b'"' | b'\'' => {
                let quote = text[at];
                at += 1;
                while at < text.len() && text[at] != quote && text[at] != b'\n' {
                    if text[at] == b'\\' {
                        at += 1;
                    }
                    at += 1;
                }
            }
            _ => {}
        }
        at += 1;
    }
    None
}

/// Whether `name.field = …` (or `name = …`) stands at a use of a name that
/// ends at `end`.
fn written_at(text: &[u8], end: usize) -> bool {
    let mut at = skip_space(text, end);
    if assignment_at(text, at).is_some() {
        return true;
    }
    while text.get(at) == Some(&b'.') {
        let from = skip_space(text, at + 1);
        let to = ident_end(text, from);
        if to == from {
            return false;
        }
        at = skip_space(text, to);
        if assignment_at(text, at).is_some() {
            return true;
        }
    }
    false
}

/// Whether what a stash hands out by reference is written through: straight
/// away (`stash.Get(e).value = x`) or through a ref local taken from it
/// (`ref var c = ref stash.Get(e); … c.value = x`) before `limit`, the end
/// of the member. `start..end` is the stash's name.
pub(crate) fn writes_through(text: &[u8], start: usize, end: usize, limit: usize) -> bool {
    let Some(call) = method_after(text, end) else {
        return false;
    };
    let dot = skip_space(text, end);
    let name_from = skip_space(text, dot + 1);
    let open = skip_space(text, name_from + call.len());
    let Some(close) = (text.get(open) == Some(&b'('))
        .then(|| matching(text, open))
        .flatten()
    else {
        return false;
    };
    if written_at(text, close + 1) {
        return true;
    }
    // `ref var c = ref stash.Get(e)`: the local `c`.
    let before = skip_space_back(text, start);
    let keyword = ident_start(text, before);
    if str_of(text, keyword, before) != "ref" {
        return false;
    }
    let equals = skip_space_back(text, keyword);
    if equals == 0
        || text[equals - 1] != b'='
        || assignment_at(text, equals - 1) != Some(Access::Write)
    {
        return false;
    }
    let local_end = skip_space_back(text, equals - 1);
    let local_start = ident_start(text, local_end);
    if local_start == local_end {
        return false;
    }
    let local = &text[local_start..local_end];
    let limit = limit.min(text.len());
    let mut at = close + 1;
    while at + local.len() <= limit {
        if &text[at..at + local.len()] == local
            && !is_ident(text[at - 1])
            && text[at - 1] != b'.'
            && !text.get(at + local.len()).copied().is_some_and(is_ident)
        {
            if written_at(text, at + local.len()) {
                return true;
            }
            at += local.len();
        } else {
            at += 1;
        }
    }
    false
}

/// The identifiers of a line of code, for looking names up in removed text.
pub(crate) fn words(line: &str) -> impl Iterator<Item = &str> {
    line.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .filter(|word| !word.is_empty() && !word.starts_with(|c: char| c.is_ascii_digit()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span(text: &str, name: &str) -> (usize, usize) {
        let at = text.find(name).unwrap();
        (at, at + name.len())
    }

    #[test]
    fn reads_and_writes() {
        let check = |text: &str, name: &str| {
            let (start, end) = span(text, name);
            access(text.as_bytes(), start, end)
        };
        assert_eq!(check("total = 1;", "total"), Access::Write);
        assert_eq!(check("total == 1", "total"), Access::Read);
        assert_eq!(check("x => total", "total"), Access::Read);
        assert_eq!(check("total += 1;", "total"), Access::Both);
        assert_eq!(check("total ++;", "total"), Access::Both);
        assert_eq!(check("--total;", "total"), Access::Both);
        assert_eq!(check("Parse(s, out total)", "total"), Access::Write);
        assert_eq!(check("Swap(ref this.total)", "total"), Access::Both);
        assert_eq!(check("Use(total)", "total"), Access::Read);
        assert_eq!(
            check("ref var c = ref total.Get(e);", "total"),
            Access::Read
        );
        assert_eq!(
            check("ref var c = ref box.total.Entity.Get(e);", "total"),
            Access::Read
        );
        assert_eq!(check("total.count = 1;", "total"), Access::Read);
        assert_eq!(check("flags <<= 1;", "flags"), Access::Both);
        assert_eq!(check("cache ??= Make();", "cache"), Access::Both);
    }

    #[test]
    fn the_method_called_on_a_name() {
        let check = |text: &'static str, name: &str| {
            let (_, end) = span(text, name);
            method_after(text.as_bytes(), end)
        };
        assert_eq!(check("_health.Set(e, h);", "_health"), Some("Set"));
        assert_eq!(check("_health . Remove (e);", "_health"), Some("Remove"));
        assert_eq!(check("foreach (var h in _health)", "_health"), None);
        assert_eq!(check("_health.Length", "_health"), None);
    }

    #[test]
    fn the_generic_a_type_is_an_argument_of() {
        let check = |text: &'static str, name: &str| {
            let (start, _) = span(text, name);
            generic_owner(text.as_bytes(), start)
        };
        assert_eq!(check("Filter.With<Health>()", "Health"), Some("With"));
        assert_eq!(
            check("Filter.With< Game.Health >()", "Health"),
            Some("With")
        );
        assert_eq!(
            check("e.AddComponent<global::Game.Health>()", "Health"),
            Some("AddComponent")
        );
        assert_eq!(check("new Health()", "Health"), None);
        assert_eq!(check("Map<int, Health>", "Health"), None);
    }

    #[test]
    fn a_component_written_through_its_stash() {
        let check = |text: &str| {
            let (start, end) = span(text, "_health");
            writes_through(text.as_bytes(), start, end, text.len())
        };
        assert!(check("_health.Get(e).value = 3;"));
        assert!(check(
            "ref var h = ref _health.Get(e); if (x) { h.value -= 1; }"
        ));
        assert!(check(
            "ref var h = ref _health.Get(Find(e, 1)); h = default;"
        ));
        assert!(!check("ref var h = ref _health.Get(e); Use(h.value);"));
        assert!(!check("var h = _health.Get(e); h.value = 3;"));
        assert!(!check(
            "ref readonly var h = ref _health.Get(e); other.value = h.value;"
        ));
        assert!(!check(
            "ref var h = ref _health.Get(e); oh.value = 1; this.h.value = 2;"
        ));
    }

    #[test]
    fn lines() {
        let text = b"a\nbb\nccc";
        assert_eq!(line_start(text, 0), 0);
        assert_eq!(line_start(text, 1), 2);
        assert_eq!(line_start(text, 2), 5);
        assert_eq!(line_start(text, 9), 8);
    }
}
