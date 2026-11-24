//! ECS components through stashes, as Morpeh-style code reads and writes
//! them: `ref var c = ref _health.Get(e); c.Value = x`, `_health.Set(e)`,
//! `_health.Remove(e)`. A component's fields are written through what a
//! stash returns, which the compiler sees as a plain call — so the value
//! graph finds those writes here, in the text, and asks [`Symbols`] for
//! the stashes of a component.
//!
//! [`Symbols`]: super::symbols::Symbols

use super::flow::chars::{APOSTROPHE, DOT, EQ, OPEN_PAREN, QUOTE};
use super::flow::{
    Access, KEYWORDS, Utf16Range as R, access, is_ident_part, is_ident_start, matching,
    skip_literal, skip_space, skip_space_backward, string, word,
};

/// The component of a stash type: `Stash<Game.Health>` → `Health`.
#[must_use]
pub fn stash_component(type_text: &str) -> Option<String> {
    let compact: String = type_text.chars().filter(|&c| c != ' ').collect();
    let inner = compact.strip_prefix("Stash<")?.strip_suffix('>')?;
    inner
        .rsplit('.')
        .find(|part| !part.is_empty())
        .map(str::to_owned)
}

/// A write into a component's field through a stash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StashWrite {
    /// The field's name at the place of the write.
    pub name: R,
    pub rhs: Option<R>,
    pub compound: bool,
}

/// Writes into the field `field` of a component through the stash `stash`:
/// straight into what `Get`/`Add` returned (`stash.Get(e).field = x`), and
/// through a ref local (`ref var c = ref stash.Get(e); … c.field = x`) to
/// the end of its method: `scope` gives the method by position.
pub fn stash_field_writes(
    text: &[u16],
    stash: &str,
    field: &str,
    scope: &mut dyn FnMut(usize) -> Option<R>,
) -> Vec<StashWrite> {
    let mut result = Vec::new();
    let check = |name: R, result: &mut Vec<StashWrite>| {
        if string(text, name) != field {
            return;
        }
        if let Access::Write { rhs, compound } = access(text, name) {
            result.push(StashWrite {
                name,
                rhs,
                compound,
            });
        }
    };
    for (start, close) in stash_references(text, stash, 0, None) {
        // Straight into the result: `stash.Get(e).field = x`.
        if let Some(member) = member_after(text, close) {
            check(member, &mut result);
        }
        // Through a ref local: `ref var c = ref stash.Get(e)`.
        let Some(local) = ref_local(text, start) else {
            continue;
        };
        let Some(method) = scope(start) else { continue };
        for member in members(
            &local,
            text,
            R::new(close, method.end().saturating_sub(close)),
        ) {
            check(member, &mut result);
        }
    }
    result
}

/// The stash the ref local `local` was taken from, if it was declared in
/// `method` before `before`: `ref var c = ref _health.Get(e)` → `_health`.
pub fn stash_of_local(text: &[u16], local: &str, method: R, before: usize) -> Option<String> {
    let target: Vec<u16> = local.encode_utf16().collect();
    if target.is_empty() {
        return None;
    }
    let mut found = None;
    let mut i = method.location;
    let limit = before.min(method.end());
    while i + target.len() <= limit {
        if !(text[i] == target[0]
            && text[i..i + target.len()] == target[..]
            && (i == 0 || !is_ident_part(text[i - 1]))
            && i + target.len() < text.len()
            && !is_ident_part(text[i + target.len()]))
        {
            i += 1;
            continue;
        }
        // `c = ref _stash.Get(`
        let mut j = skip_space(text, i + target.len());
        if !(j + 1 < text.len() && text[j] == EQ && text[j + 1] != EQ) {
            i += 1;
            continue;
        }
        j = skip_space(text, j + 1);
        if !(j + 3 < text.len()
            && string(text, R::new(j, 3)) == "ref"
            && !is_ident_part(text[j + 3]))
        {
            i += 1;
            continue;
        }
        j = skip_space(text, j + 3);
        let mut e = j;
        while e < text.len() && is_ident_part(text[e]) {
            e += 1;
        }
        let stash = string(text, R::new(j, e - j));
        if !stash.is_empty()
            && stash_references(text, &stash, j, Some(e + 1))
                .first()
                .is_some_and(|c| c.0 == j)
        {
            found = Some(stash);
        }
        i += target.len();
    }
    found
}

/// Ref returns of the stash: `stash.Get(`, `stash.Add(` — where the stash's
/// name starts and where the call's parenthesis closes.
fn stash_references(
    text: &[u16],
    stash: &str,
    from: usize,
    limit: Option<usize>,
) -> Vec<(usize, usize)> {
    let target: Vec<u16> = stash.encode_utf16().collect();
    if target.is_empty() {
        return Vec::new();
    }
    let mut result = Vec::new();
    let mut i = from;
    let end = limit.unwrap_or(text.len()).min(text.len());
    while i + target.len() < end {
        if !(text[i] == target[0]
            && text[i..i + target.len()] == target[..]
            && (i == 0 || (!is_ident_part(text[i - 1]) && text[i - 1] != DOT))
            && !is_ident_part(text[i + target.len()]))
        {
            i += 1;
            continue;
        }
        let mut j = skip_space(text, i + target.len());
        if !(j < text.len() && text[j] == DOT) {
            i += 1;
            continue;
        }
        j = skip_space(text, j + 1);
        let mut e = j;
        while e < text.len() && is_ident_part(text[e]) {
            e += 1;
        }
        let method = string(text, R::new(j, e - j));
        let open = skip_space(text, e);
        if !((method == "Get" || method == "Add") && open < text.len() && text[open] == OPEN_PAREN)
        {
            i = e;
            continue;
        }
        let close = matching(text, open);
        if close <= open as isize {
            i = e;
            continue;
        }
        result.push((i, close as usize));
        i = e;
    }
    result
}

/// `ref var c = ref ` (or `c = ref `) right before `position`: the name `c`.
fn ref_local(text: &[u16], position: usize) -> Option<String> {
    let mut i = skip_space_backward(text, position);
    if word(text, i) != "ref" {
        return None;
    }
    i = skip_space_backward(text, i - 3);
    let operators: Vec<u16> = "=!<>+-*/%&|^?".encode_utf16().collect();
    if !(i > 1 && text[i - 1] == EQ && !operators.contains(&text[i - 2])) {
        return None;
    }
    i = skip_space_backward(text, i - 1);
    let name = word(text, i);
    let first = name.encode_utf16().next()?;
    (is_ident_start(first) && !KEYWORDS.contains(&name.as_str())).then_some(name)
}

/// `.member` right past `close` (the call's closing parenthesis).
fn member_after(text: &[u16], close: usize) -> Option<R> {
    let dot_at = skip_space(text, close + 1);
    if !(dot_at < text.len() && text[dot_at] == DOT) {
        return None;
    }
    let start = skip_space(text, dot_at + 1);
    let mut end = start;
    while end < text.len() && is_ident_part(text[end]) {
        end += 1;
    }
    (end > start && is_ident_start(text[start])).then(|| R::new(start, end - start))
}

/// Members taken from `local` in `range`: `local.member` → the range of `member`.
fn members(local: &str, text: &[u16], range: R) -> Vec<R> {
    let target: Vec<u16> = local.encode_utf16().collect();
    let mut result = Vec::new();
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
            && !is_ident_part(text[i + target.len()]))
        {
            i += 1;
            continue;
        }
        if let Some(name) = member_after(text, i + target.len() - 1) {
            result.push(name);
        }
        i += target.len();
    }
    result
}

/// What is done to a component through a stash: `name.Set(`, `.Add(`, `.Remove(`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StashCall {
    Set,
    Add,
    Remove,
    SetOrUpdate,
}

pub fn stash_calls(text: &[u16], stash: &str) -> Vec<(R, StashCall)> {
    let mut result = Vec::new();
    let target: Vec<u16> = stash.encode_utf16().collect();
    if target.is_empty() {
        return result;
    }
    let mut i = 0;
    while i + target.len() < text.len() {
        if !(text[i] == target[0]
            && text[i..i + target.len()] == target[..]
            && (i == 0 || !is_ident_part(text[i - 1]))
            && !is_ident_part(text[i + target.len()]))
        {
            i += 1;
            continue;
        }
        let mut j = skip_space(text, i + target.len());
        if !(j < text.len() && text[j] == DOT) {
            i += 1;
            continue;
        }
        j = skip_space(text, j + 1);
        let mut e = j;
        while e < text.len() && is_ident_part(text[e]) {
            e += 1;
        }
        let call = match string(text, R::new(j, e - j)).as_str() {
            "Set" => Some(StashCall::Set),
            "Add" => Some(StashCall::Add),
            "Remove" => Some(StashCall::Remove),
            "SetOrUpdate" => Some(StashCall::SetOrUpdate),
            _ => None,
        };
        let open = skip_space(text, e);
        if let Some(call) = call
            && open < text.len()
            && text[open] == OPEN_PAREN
        {
            result.push((R::new(j, e - j), call));
        }
        i = e;
    }
    result
}
