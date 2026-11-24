//! `switch` on a string, back from the ways a compiler takes it apart.
//!
//! C# compiles `switch (s) { case "a": ... }` into a search for the one
//! literal that can match followed by a single `==`: a binary search over
//! `ComputeStringHash(s)`, a `switch` on `s.Length` and then on one of the
//! characters, or for a few cases a plain chain of `if (s == "a")`. All of
//! them test only the string, so which case a literal lands in is found by
//! running the search for that literal: every hash, length and character
//! test is then decided, and the statement the search stops at is the
//! case's body. What the search reaches for no literal is the `default`.

use std::collections::{HashMap, HashSet};

use crate::ir::{BinOp, Case, Cmp, Expr, Stmt, UnOp};

/// How many literals make a chain of `if`s a `switch`: two read as well
/// as `if`/`else`.
const MIN_CASES: usize = 3;

/// What running the search did.
enum Outcome {
    /// Reached the end of a list of statements without a verdict.
    FallOut,
    /// Left the innermost `switch` of the search.
    Break,
    /// Reached a body that ends the flow itself.
    Done,
}

/// A body the search stops at: where it is in the search, and what it is.
#[derive(Clone)]
struct Leaf {
    path: Vec<usize>,
    body: Vec<Stmt>,
    /// Whether running off the end of the body leaves the search.
    exits: bool,
}

/// The search for one value of the string: `None` is `null`.
struct Run<'r> {
    subject: &'r Expr,
    value: Option<&'r str>,
    locals: HashMap<u16, i64>,
    found: Option<Leaf>,
    routing: &'r HashSet<u16>,
}

/// FNV-1a over UTF-16 code units, which is what Roslyn's
/// `ComputeStringHash` computes.
fn string_hash(text: Option<&str>) -> i64 {
    let mut hash: u32 = 2_166_136_261;
    if let Some(text) = text {
        for unit in text.encode_utf16() {
            hash = (u32::from(unit) ^ hash).wrapping_mul(16_777_619);
        }
    }
    i64::from(hash)
}

fn is_hash_call(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Call {
            method,
            receiver: None,
            args,
        } if method.name == "ComputeStringHash" && args.len() == 1 => Some(&args[0]),
        _ => None,
    }
}

/// The string a routing value is computed from, and whether it is one:
/// `s.Length`, `s[k]`, `ComputeStringHash(s)`.
fn routing_source(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Property {
            receiver: Some(receiver),
            name,
            ..
        } if name == "Length" => Some(receiver),
        Expr::Indexer { receiver, args } if matches!(args.as_slice(), [Expr::Int(_)]) => {
            Some(receiver)
        }
        other => is_hash_call(other),
    }
}

/// The literal a comparison of the string tests: `Some(None)` for `null`.
fn literal_test<'e>(expr: &'e Expr, subject: &Expr) -> Option<Option<&'e str>> {
    let Expr::Compare {
        op: Cmp::Eq | Cmp::Ne,
        left,
        right,
        ..
    } = expr
    else {
        return None;
    };
    let other = if **left == *subject {
        right
    } else if **right == *subject {
        left
    } else {
        return None;
    };
    match other.as_ref() {
        Expr::Str(text) => Some(Some(text.as_str())),
        Expr::Null => Some(None),
        _ => None,
    }
}

impl Run<'_> {
    fn text(&self) -> Option<&str> {
        self.value
    }

    fn int(&self, expr: &Expr) -> Option<i64> {
        match expr {
            Expr::Int(n) | Expr::Long(n) => Some(*n),
            Expr::Char(c) => Some(i64::from(*c)),
            Expr::Local(at) => self.locals.get(at).copied(),
            Expr::Cast(_, inner) => self.int(inner),
            Expr::Property {
                receiver: Some(receiver),
                name,
                ..
            } if name == "Length" && **receiver == *self.subject => {
                Some(self.text()?.encode_utf16().count() as i64)
            }
            Expr::Indexer { receiver, args } if **receiver == *self.subject => {
                let [Expr::Int(at)] = args.as_slice() else {
                    return None;
                };
                let unit = self
                    .text()?
                    .encode_utf16()
                    .nth(usize::try_from(*at).ok()?)?;
                Some(i64::from(unit))
            }
            other => {
                let source = is_hash_call(other)?;
                (*source == *self.subject).then(|| string_hash(self.value))
            }
        }
    }

    fn condition(&self, expr: &Expr) -> Option<bool> {
        if let Some(literal) = literal_test(expr, self.subject) {
            let Expr::Compare { op, .. } = expr else {
                return None;
            };
            let equal = literal == self.value;
            return Some(if *op == Cmp::Eq { equal } else { !equal });
        }
        match expr {
            Expr::Unary(UnOp::Not, inner) => self.condition(inner).map(|value| !value),
            Expr::Binary(BinOp::LogicalAnd, left, right) => {
                Some(self.condition(left)? && self.condition(right)?)
            }
            Expr::Binary(BinOp::LogicalOr, left, right) => {
                Some(self.condition(left)? || self.condition(right)?)
            }
            Expr::Bool(value) => Some(*value),
            Expr::Compare {
                op,
                left,
                right,
                unordered,
                ..
            } => {
                let hashed = |e: &Expr| {
                    is_hash_call(e).is_some()
                        || matches!(e, Expr::Local(at) if self.routing.contains(at))
                };
                let (mut a, mut b) = (self.int(left)?, self.int(right)?);
                // The hash is unsigned, however its constants print.
                if *unordered || hashed(left) || hashed(right) {
                    a = i64::from(a as u32);
                    b = i64::from(b as u32);
                }
                Some(match op {
                    Cmp::Eq => a == b,
                    Cmp::Ne => a != b,
                    Cmp::Lt => a < b,
                    Cmp::Le => a <= b,
                    Cmp::Gt => a > b,
                    Cmp::Ge => a >= b,
                })
            }
            _ => None,
        }
    }

    /// Runs the search through a list of statements.
    fn block(&mut self, stmts: &[Stmt], path: &[usize], nested: bool) -> Option<Outcome> {
        for (index, stmt) in stmts.iter().enumerate() {
            let mut here = path.to_vec();
            here.push(index);
            if !is_routing(stmt, self.subject, self.routing, nested) {
                return self.leaf(&stmts[index..], here);
            }
            match stmt {
                Stmt::Expr(Expr::Assign(target, value)) => {
                    let Expr::Local(at) = target.as_ref() else {
                        return None;
                    };
                    let value = self.int(value)?;
                    self.locals.insert(*at, value);
                }
                Stmt::If {
                    condition,
                    then,
                    otherwise,
                } => {
                    let taken = self.condition(condition)?;
                    here.push(usize::from(!taken));
                    let branch = if taken { then } else { otherwise };
                    match self.block(branch, &here, nested)? {
                        Outcome::FallOut => {}
                        other => return Some(other),
                    }
                }
                Stmt::Switch { value, cases } => {
                    let value = self.int(value)?;
                    let chosen = cases
                        .iter()
                        .position(|case| {
                            case.labels.iter().any(|label| {
                                label
                                    .as_ref()
                                    .is_some_and(|label| self.int(label) == Some(value))
                            })
                        })
                        .or_else(|| cases.iter().position(|case| case.labels.contains(&None)));
                    if let Some(chosen) = chosen {
                        here.push(chosen);
                        match self.block(&cases[chosen].body, &here, true)? {
                            Outcome::FallOut | Outcome::Break => {}
                            Outcome::Done => return Some(Outcome::Done),
                        }
                    }
                }
                Stmt::Break => return Some(Outcome::Break),
                _ => return None,
            }
        }
        Some(Outcome::FallOut)
    }

    /// The body the search stopped at: the rest of its list.
    fn leaf(&mut self, rest: &[Stmt], path: Vec<usize>) -> Option<Outcome> {
        if self.found.is_some() {
            // A second body after the first: not a search any more.
            return None;
        }
        let mut body = rest.to_vec();
        let outcome = if matches!(body.last(), Some(Stmt::Break)) {
            body.pop();
            Outcome::Break
        } else if body.last().is_some_and(Stmt::ends_flow) {
            Outcome::Done
        } else {
            Outcome::FallOut
        };
        self.found = Some(Leaf {
            path,
            body,
            exits: false,
        });
        Some(outcome)
    }
}

/// Whether a statement is part of the search rather than of a case.
fn is_routing(stmt: &Stmt, subject: &Expr, routing: &HashSet<u16>, nested: bool) -> bool {
    match stmt {
        Stmt::Expr(Expr::Assign(target, value)) => {
            matches!(target.as_ref(), Expr::Local(at) if routing.contains(at))
                && routing_source(value).is_some_and(|source| *source == *subject)
        }
        Stmt::If { condition, .. } => is_routing_condition(condition, subject, routing),
        Stmt::Switch { value, .. } => is_routing_value(value, subject, routing),
        Stmt::Break => nested,
        _ => false,
    }
}

fn is_routing_value(expr: &Expr, subject: &Expr, routing: &HashSet<u16>) -> bool {
    match expr {
        Expr::Local(at) => routing.contains(at),
        Expr::Cast(_, inner) => is_routing_value(inner, subject, routing),
        other => routing_source(other).is_some_and(|source| *source == *subject),
    }
}

fn is_routing_condition(expr: &Expr, subject: &Expr, routing: &HashSet<u16>) -> bool {
    if literal_test(expr, subject).is_some() {
        return true;
    }
    match expr {
        Expr::Unary(UnOp::Not, inner) => is_routing_condition(inner, subject, routing),
        Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr, left, right) => {
            is_routing_condition(left, subject, routing)
                && is_routing_condition(right, subject, routing)
        }
        Expr::Compare { left, right, .. } => {
            let constant = |e: &Expr| matches!(e, Expr::Int(_) | Expr::Long(_) | Expr::Char(_));
            (is_routing_value(left, subject, routing) && constant(right))
                || (is_routing_value(right, subject, routing) && constant(left))
        }
        _ => false,
    }
}

/// A condition for a string none of the literals is: `s == "a"` is false,
/// `s != "a"` true, anything about its hash or length unknown.
fn unmatched(condition: &Expr, subject: &Expr) -> Option<bool> {
    if let Some(literal) = literal_test(condition, subject) {
        let Expr::Compare { op, .. } = condition else {
            return None;
        };
        // An unmatched string may be `null` itself.
        literal?;
        return Some(*op == Cmp::Ne);
    }
    match condition {
        Expr::Unary(UnOp::Not, inner) => unmatched(inner, subject).map(|value| !value),
        Expr::Binary(BinOp::LogicalAnd, left, right) => {
            match (unmatched(left, subject), unmatched(right, subject)) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            }
        }
        Expr::Binary(BinOp::LogicalOr, left, right) => {
            match (unmatched(left, subject), unmatched(right, subject)) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Every body a string none of the literals is can reach.
fn all_leaves(
    stmts: &[Stmt],
    path: &[usize],
    subject: &Expr,
    routing: &HashSet<u16>,
    nested: bool,
    tail: bool,
    out: &mut Vec<Leaf>,
) {
    for (index, stmt) in stmts.iter().enumerate() {
        let mut here = path.to_vec();
        here.push(index);
        if !is_routing(stmt, subject, routing, nested) {
            let mut body = stmts[index..].to_vec();
            // A `break` out of a `switch` of the search goes where running
            // off the end of that `switch` would.
            if nested && matches!(body.last(), Some(Stmt::Break)) {
                body.pop();
            }
            out.push(Leaf {
                path: here,
                body,
                exits: tail,
            });
            return;
        }
        let stmt_tail = tail && index + 1 == stmts.len();
        match stmt {
            Stmt::If {
                condition,
                then,
                otherwise,
            } => {
                let known = unmatched(condition, subject);
                for (branch, block) in [then, otherwise].into_iter().enumerate() {
                    if known.is_some_and(|taken| taken == (branch == 1)) {
                        continue;
                    }
                    let mut inner = here.clone();
                    inner.push(branch);
                    all_leaves(block, &inner, subject, routing, nested, stmt_tail, out);
                }
                // Whether both branches end is not asked: the search goes on
                // after an `if` that falls out.
            }
            Stmt::Switch { cases, .. } => {
                for (at, case) in cases.iter().enumerate() {
                    let mut inner = here.clone();
                    inner.push(at);
                    all_leaves(&case.body, &inner, subject, routing, true, stmt_tail, out);
                }
            }
            Stmt::Break => return,
            _ => {}
        }
    }
}

/// The string a search looks at, and the locals it computes from it.
fn search_of(stmts: &[Stmt]) -> Option<(Expr, HashSet<u16>)> {
    let mut subject: Option<Expr> = None;
    let mut routing = HashSet::new();
    let mut literals = 0;
    for stmt in stmts {
        stmt.walk_exprs(&mut |e| {
            if let Expr::Assign(target, value) = e
                && let Expr::Local(at) = target.as_ref()
                && let Some(source) = routing_source(value)
            {
                routing.insert(*at);
                if subject.is_none() {
                    subject = Some(source.clone());
                }
            }
            if let Expr::Compare {
                op: Cmp::Eq | Cmp::Ne,
                left,
                right,
                ..
            } = e
                && matches!(right.as_ref(), Expr::Str(_))
            {
                literals += 1;
                if subject.is_none() {
                    subject = Some((**left).clone());
                }
            }
        });
    }
    let subject = subject?;
    ((literals > 0 || !routing.is_empty())
        && matches!(subject, Expr::Local(_) | Expr::Arg(_) | Expr::Field { .. }))
    .then_some((subject, routing))
}

/// The literals the search compares the string with, `null` included.
fn literals_of(stmts: &[Stmt], subject: &Expr) -> Vec<Option<String>> {
    let mut out: Vec<Option<String>> = Vec::new();
    for stmt in stmts {
        stmt.walk_exprs(&mut |e| {
            if let Some(literal) = literal_test(e, subject) {
                let literal = literal.map(str::to_string);
                if !out.contains(&literal) {
                    out.push(literal);
                }
            }
        });
    }
    out
}

fn reads_local(stmts: &[Stmt], locals: &HashSet<u16>) -> bool {
    stmts.iter().any(|stmt| {
        let mut found = false;
        stmt.walk_exprs(&mut |e| {
            if let Expr::Local(at) = e
                && locals.contains(at)
            {
                found = true;
            }
        });
        found
    })
}

/// Whether a body has a `break` that leaves something around it, which
/// inside a `switch` would leave the `switch` instead.
fn breaks_out(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break => true,
        Stmt::While { .. }
        | Stmt::DoWhile { .. }
        | Stmt::For { .. }
        | Stmt::ForEach { .. }
        | Stmt::Switch { .. } => false,
        other => other.blocks().iter().any(|block| breaks_out(block)),
    })
}

fn jumps_in(stmts: &[Stmt], out: &mut Vec<u32>) {
    for stmt in stmts {
        if let Stmt::Goto(label) = stmt {
            out.push(*label);
        }
        for block in stmt.blocks() {
            jumps_in(block, out);
        }
    }
}

fn has_label(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::Label(_))
        || stmt
            .blocks()
            .iter()
            .any(|block| block.iter().any(has_label))
}

fn gotos_to(stmts: &[Stmt], label: u32) -> usize {
    stmts
        .iter()
        .map(|stmt| {
            usize::from(*stmt == Stmt::Goto(label))
                + stmt
                    .blocks()
                    .iter()
                    .map(|block| gotos_to(block, label))
                    .sum::<usize>()
        })
        .sum()
}

/// Folds the searches in a list of statements back into `switch`es.
pub fn fold_string_switches(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = drop_null_guards(stmts);
    changed |= merge_leading_cases(stmts);
    let mut index = 0;
    while index < stmts.len() {
        if let Some((end, switch)) = string_switch(stmts, index) {
            let tail: Vec<Stmt> = stmts.drain(index..).skip(end - index).collect();
            let (switch, after) = switch.finish(tail);
            stmts.push(switch);
            stmts.extend(after);
            changed = true;
        }
        index += 1;
    }
    changed
}

/// `if (x == k) { A } else { switch (x) { ... } }` is one `switch` with
/// `case k: A` first, when no case of it already takes `k`.
pub fn merge_leading_cases(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = stmt
        else {
            continue;
        };
        let Expr::Compare {
            op: op @ (Cmp::Eq | Cmp::Ne),
            left,
            right,
            float: false,
            ..
        } = condition
        else {
            continue;
        };
        let (matched, rest) = if *op == Cmp::Eq {
            (then, otherwise)
        } else {
            (otherwise, then)
        };
        let [Stmt::Switch { value, cases }] = rest.as_slice() else {
            continue;
        };
        let literal = if **left == *value {
            right.as_ref()
        } else if **right == *value {
            left.as_ref()
        } else {
            continue;
        };
        let Some(first) = cases
            .iter()
            .flat_map(|case| case.labels.iter().flatten())
            .next()
        else {
            continue;
        };
        let same_kind = std::mem::discriminant(first) == std::mem::discriminant(literal)
            || matches!(literal, Expr::Null) && matches!(first, Expr::Str(_));
        if !same_kind
            || !value.is_pure()
            || cases
                .iter()
                .any(|case| case.labels.iter().flatten().any(|label| label == literal))
            || matched.is_empty()
            || breaks_out(matched)
            || matched.iter().any(has_label)
        {
            continue;
        }
        let mut body = std::mem::take(matched);
        if !body.last().is_some_and(Stmt::ends_flow) {
            body.push(Stmt::Break);
        }
        let literal = literal.clone();
        let Some(Stmt::Switch { value, mut cases }) = rest.pop() else {
            unreachable!()
        };
        cases.insert(
            0,
            Case {
                labels: vec![Some(literal)],
                body,
            },
        );
        *stmt = Stmt::Switch { value, cases };
        changed = true;
    }
    changed
}

/// `if (s != null) { switch (s) { ... } }` with no `case null` is the
/// `switch`: `null` matches none of its cases anyway.
fn drop_null_guards(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        let Stmt::If {
            condition:
                Expr::Compare {
                    op: Cmp::Ne,
                    left,
                    right,
                    ..
                },
            then,
            otherwise,
        } = stmt
        else {
            continue;
        };
        if **right != Expr::Null || !otherwise.is_empty() {
            continue;
        }
        let [Stmt::Switch { value, cases }] = then.as_slice() else {
            continue;
        };
        let strings = cases
            .iter()
            .flat_map(|case| case.labels.iter())
            .all(|label| matches!(label, Some(Expr::Str(_))));
        if *value != **left || !strings {
            continue;
        }
        let switch = then[0].clone();
        *stmt = switch;
        changed = true;
    }
    changed
}

/// A `switch` found, waiting for what follows it.
struct Found {
    subject: Expr,
    cases: Vec<Case>,
    default: Option<Vec<Stmt>>,
    /// Whether the search can end without reaching a body, so that what
    /// follows it is what an unmatched string runs.
    falls_out: bool,
}

impl Found {
    /// The `switch` and what comes after it.
    fn finish(self, mut tail: Vec<Stmt>) -> (Stmt, Vec<Stmt>) {
        let Self {
            subject,
            mut cases,
            default,
            falls_out,
        } = self;
        let mut default = match default {
            Some(body) if falls_out && body == tail => {
                // The default is the code after the search, run by both.
                tail.clear();
                Some(body)
            }
            other => other,
        };
        // `goto END` at the end of a case, where END is the code after the
        // switch, is `break`; so is the code before END a default.
        let end_label = cases.iter().find_map(|case| match case.body.last() {
            Some(Stmt::Goto(label)) => Some(*label),
            _ => None,
        });
        if let Some(label) = end_label
            && default.is_none()
            && let Some(at) = tail.iter().position(|stmt| *stmt == Stmt::Label(label))
            && !breaks_out(&tail[..at])
        {
            let before: Vec<Stmt> = tail.drain(..at).collect();
            if !before.is_empty() {
                default = Some(before);
            }
        }
        // A literal the search lets out is the code after it, when nothing
        // else gets there.
        let ends_alone = |body: &[Stmt]| {
            body.last()
                .is_some_and(|last| last.ends_flow() && !matches!(last, Stmt::Goto(_)))
        };
        if let Some(open) = cases.iter().position(|case| case.body.is_empty())
            && !falls_out
            && ends_alone(&tail)
            && !tail.iter().any(has_label)
            && cases
                .iter()
                .enumerate()
                .all(|(at, case)| at == open || ends_alone(&case.body))
            && default.as_deref().is_none_or(ends_alone)
        {
            cases[open].body = std::mem::take(&mut tail);
        }
        let jump_to_end = |body: &mut Vec<Stmt>, tail: &[Stmt]| {
            if let (Some(Stmt::Goto(label)), Some(Stmt::Label(first))) = (body.last(), tail.first())
                && label == first
            {
                body.pop();
                body.push(Stmt::Break);
            }
            if !body.last().is_some_and(Stmt::ends_flow) {
                body.push(Stmt::Break);
            }
        };
        for case in &mut cases {
            jump_to_end(&mut case.body, &tail);
        }
        if let Some(mut body) = default {
            jump_to_end(&mut body, &tail);
            cases.push(Case {
                labels: vec![None],
                body,
            });
        }
        // The label the cases jumped to, if nothing else does.
        if let Some(Stmt::Label(label)) = tail.first() {
            let label = *label;
            let jumps: usize = cases.iter().map(|case| gotos_to(&case.body, label)).sum();
            if jumps == 0 && gotos_to(&tail, label) == 0 {
                tail.remove(0);
            }
        }
        (
            Stmt::Switch {
                value: subject,
                cases,
            },
            tail,
        )
    }
}

/// A case being gathered: where its body is in the search, the literals
/// that reach it, and the body.
type Gathered = (Vec<usize>, Vec<Option<String>>, Vec<Stmt>);

/// The `switch` a search starting at `index` was, and where it ends.
fn string_switch(stmts: &[Stmt], index: usize) -> Option<(usize, Found)> {
    // The search: the statements from here that only look at the string.
    let (subject, routing) = search_of(&stmts[index..=index])?;
    let mut end = index;
    while end < stmts.len() && is_routing(&stmts[end], &subject, &routing, false) {
        end += 1;
    }
    if end == index {
        return None;
    }
    let region = &stmts[index..end];
    // A label inside is somewhere else's jump into the search: the shape is
    // not settled yet.
    if region.iter().any(has_label) {
        return None;
    }
    // A jump out of the search goes to the code after it, or the shape is
    // not settled yet either.
    let mut jumps = Vec::new();
    jumps_in(region, &mut jumps);
    if jumps
        .iter()
        .any(|label| !stmts[end..].contains(&Stmt::Label(*label)))
    {
        return None;
    }
    let (_, routing) = search_of(region)?;
    let literals = literals_of(region, &subject);
    if literals.iter().filter(|literal| literal.is_some()).count() < MIN_CASES {
        return None;
    }
    // The computed locals are the search's alone.
    if reads_local(&stmts[end..], &routing) {
        return None;
    }
    let mut leaves: Vec<Leaf> = Vec::new();
    let mut cases: Vec<Gathered> = Vec::new();
    for literal in &literals {
        let mut run = Run {
            subject: &subject,
            value: literal.as_deref(),
            locals: HashMap::new(),
            found: None,
            routing: &routing,
        };
        run.block(region, &[], false)?;
        let Some(leaf) = run.found else {
            // Nothing for this value: `null` guarded against, or a literal
            // whose case is the code after the search.
            if literal.is_some() {
                match cases
                    .iter_mut()
                    .find(|(path, ..)| path.as_slice() == [usize::MAX])
                {
                    Some((_, labels, _)) => labels.push(literal.clone()),
                    None => cases.push((vec![usize::MAX], vec![literal.clone()], Vec::new())),
                }
            }
            continue;
        };
        if reads_local(&leaf.body, &routing) || breaks_out(&leaf.body) {
            return None;
        }
        match cases.iter_mut().find(|(path, ..)| *path == leaf.path) {
            Some((_, labels, _)) => labels.push(literal.clone()),
            None => cases.push((leaf.path.clone(), vec![literal.clone()], leaf.body.clone())),
        }
        leaves.push(leaf);
    }
    // What no literal reaches is the default: the same everywhere.
    let mut every: Vec<Leaf> = Vec::new();
    all_leaves(region, &[], &subject, &routing, false, true, &mut every);
    let reached: HashSet<Vec<usize>> = leaves.iter().map(|leaf| leaf.path.clone()).collect();
    let mut default: Option<Vec<Stmt>> = None;
    for leaf in every.iter().filter(|leaf| !reached.contains(&leaf.path)) {
        if !(leaf.exits || leaf.body.last().is_some_and(Stmt::ends_flow))
            || reads_local(&leaf.body, &routing)
            || breaks_out(&leaf.body)
        {
            return None;
        }
        match &default {
            Some(body) if *body != leaf.body => return None,
            Some(_) => {}
            None => default = Some(leaf.body.clone()),
        }
    }
    // Nothing left for the default to do.
    if default.as_ref().is_some_and(Vec::is_empty) {
        default = None;
    }
    let falls_out = can_fall_out(region, &subject, &routing, false);
    if default.is_some() && falls_out && default.as_deref() != Some(&stmts[end..]) {
        return None;
    }
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    let cases = cases
        .into_iter()
        .map(|(_, labels, body)| Case {
            labels: labels
                .into_iter()
                .map(|label| Some(label.map_or(Expr::Null, Expr::Str)))
                .collect(),
            body,
        })
        .collect();
    Some((
        end,
        Found {
            subject,
            cases,
            default,
            falls_out,
        },
    ))
}

/// Whether some way through the search reaches its end without a body.
fn can_fall_out(stmts: &[Stmt], subject: &Expr, routing: &HashSet<u16>, nested: bool) -> bool {
    for stmt in stmts {
        if !is_routing(stmt, subject, routing, nested) {
            return false;
        }
        match stmt {
            Stmt::If {
                condition,
                then,
                otherwise,
            } => {
                let known = unmatched(condition, subject);
                let through_then =
                    known != Some(false) && can_fall_out(then, subject, routing, nested);
                let through_else =
                    known != Some(true) && can_fall_out(otherwise, subject, routing, nested);
                if !through_then && !through_else {
                    return false;
                }
            }
            Stmt::Switch { cases, .. } => {
                let has_default = cases.iter().any(|case| case.labels.contains(&None));
                let any = cases
                    .iter()
                    .any(|case| can_fall_out(&case.body, subject, routing, true));
                if has_default && !any {
                    return false;
                }
            }
            Stmt::Break => return true,
            _ => {}
        }
    }
    true
}
