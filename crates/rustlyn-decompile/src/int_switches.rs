//! `switch` on a number or an enum, back from the tests it was compiled to.
//!
//! Roslyn lays out a `switch` whose cases are not dense enough for a jump
//! table as a binary search: `x <= 10` splits the cases, `x == 1` picks
//! one, `(uint)(x - 1) <= 2` takes a run of them at once, and a `switch`
//! instruction may cover a dense stretch inside. Every one of those tests
//! only looks at the value, so the values that reach each statement the
//! search stops at can be worked out exactly, as sets of intervals: the
//! statement a large set reaches is the `default`, the others are cases
//! with the values they get.

use std::collections::{HashMap, HashSet};

use rustlyn_metadata::signature::TypeSig;

use crate::ir::{BinOp, Case, Cmp, Expr, Stmt, UnOp};
use crate::names::Resolver;
use crate::stack::coerce_expr;

/// How many values a case may list before the statement is left as `if`s.
const MAX_LABELS: i64 = 16;

/// A set of integers, as sorted, disjoint, inclusive intervals.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Set(Vec<(i64, i64)>);

impl Set {
    fn empty() -> Self {
        Self(Vec::new())
    }

    fn range(low: i64, high: i64) -> Self {
        if low > high {
            Self::empty()
        } else {
            Self(vec![(low, high)])
        }
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// How many values, capped: only whether it is small matters.
    fn size(&self) -> i64 {
        self.0
            .iter()
            .map(|(low, high)| high.saturating_sub(*low).saturating_add(1))
            .fold(0i64, i64::saturating_add)
    }

    fn values(&self) -> Vec<i64> {
        self.0.iter().flat_map(|(low, high)| *low..=*high).collect()
    }

    fn union(&self, other: &Self) -> Self {
        let mut all: Vec<(i64, i64)> = self.0.iter().chain(&other.0).copied().collect();
        all.sort_unstable();
        let mut out: Vec<(i64, i64)> = Vec::new();
        for (low, high) in all {
            match out.last_mut() {
                Some(last) if low <= last.1.saturating_add(1) => last.1 = last.1.max(high),
                _ => out.push((low, high)),
            }
        }
        Self(out)
    }

    fn intersect(&self, other: &Self) -> Self {
        let mut out = Vec::new();
        for (a_low, a_high) in &self.0 {
            for (b_low, b_high) in &other.0 {
                let low = (*a_low).max(*b_low);
                let high = (*a_high).min(*b_high);
                if low <= high {
                    out.push((low, high));
                }
            }
        }
        Self(out).union(&Self::empty())
    }

    /// What of `within` is not in the set.
    fn complement(&self, within: &Self) -> Self {
        let mut rest = within.clone();
        for (low, high) in &self.0 {
            let mut next = Vec::new();
            for (r_low, r_high) in rest.0 {
                if *high < r_low || *low > r_high {
                    next.push((r_low, r_high));
                    continue;
                }
                if r_low < *low {
                    next.push((r_low, low - 1));
                }
                if r_high > *high {
                    next.push((high + 1, r_high));
                }
            }
            rest = Self(next);
        }
        rest
    }
}

/// The values a type holds.
fn domain(ty: &TypeSig) -> Option<Set> {
    Some(match ty {
        TypeSig::SByte => Set::range(i64::from(i8::MIN), i64::from(i8::MAX)),
        TypeSig::Byte => Set::range(0, i64::from(u8::MAX)),
        TypeSig::Int16 => Set::range(i64::from(i16::MIN), i64::from(i16::MAX)),
        TypeSig::UInt16 | TypeSig::Char => Set::range(0, i64::from(u16::MAX)),
        TypeSig::Int32 => Set::range(i64::from(i32::MIN), i64::from(i32::MAX)),
        TypeSig::UInt32 => Set::range(0, i64::from(u32::MAX)),
        _ => return None,
    })
}

/// An enum's members and their values.
type Members = Vec<(String, i64)>;

/// What the search knows about the value it tests.
struct Search<'s> {
    resolver: Resolver<'s>,
    subject: &'s Expr,
    domain: Set,
    /// The label of the code after the search, when it has one: a jump
    /// there is running off the end.
    end_label: Option<u32>,
    /// The values that jumped there.
    jumped: std::cell::RefCell<Set>,
    /// The labels written in the search: a jump to one is to a case the
    /// compiler shared.
    labels: HashSet<u32>,
    /// The members of the enums the tests name, looked up once each.
    enums: std::cell::RefCell<Vec<(TypeSig, Option<Members>)>>,
}

impl Search<'_> {
    fn constant(&self, expr: &Expr) -> Option<i64> {
        match expr {
            Expr::Int(n) | Expr::Long(n) => Some(*n),
            Expr::Char(c) => Some(i64::from(*c)),
            Expr::Cast(_, inner) => self.constant(inner),
            Expr::EnumMember(ty, name) => {
                let mut enums = self.enums.borrow_mut();
                let at = match enums.iter().position(|(known, _)| known == ty) {
                    Some(at) => at,
                    None => {
                        enums.push((ty.clone(), self.resolver.enum_of(ty)));
                        enums.len() - 1
                    }
                };
                enums[at]
                    .1
                    .as_ref()?
                    .iter()
                    .find(|(member, _)| member == name)
                    .map(|(_, value)| *value)
            }
            _ => None,
        }
    }

    /// `x + d`, read as unsigned or not: the forms a test puts the value
    /// in.
    fn shifted(&self, expr: &Expr) -> Option<(i64, bool)> {
        match expr {
            e if e == self.subject => Some((0, false)),
            Expr::Cast(TypeSig::UInt32, inner) => {
                self.shifted(inner).map(|(offset, _)| (offset, true))
            }
            Expr::Cast(TypeSig::Int32, inner) => self.shifted(inner),
            Expr::Binary(BinOp::Sub, left, right) => {
                let (offset, unsigned) = self.shifted(left)?;
                Some((offset - self.constant(right)?, unsigned))
            }
            Expr::Binary(BinOp::Add, left, right) => {
                let (offset, unsigned) = self.shifted(left)?;
                Some((offset + self.constant(right)?, unsigned))
            }
            _ => None,
        }
    }

    /// The values of the subject for which `x + offset op k` holds.
    fn compare(&self, op: Cmp, offset: i64, unsigned: bool, k: i64) -> Set {
        let bounds = if unsigned {
            Set::range(0, i64::from(u32::MAX))
        } else {
            Set::range(i64::from(i32::MIN), i64::from(i32::MAX))
        };
        let (low, high) = bounds.0[0];
        let shifted = match op {
            Cmp::Eq => Set::range(k, k),
            Cmp::Ne => Set::range(k, k).complement(&bounds),
            Cmp::Lt => Set::range(low, k - 1),
            Cmp::Le => Set::range(low, k),
            Cmp::Gt => Set::range(k + 1, high),
            Cmp::Ge => Set::range(k, high),
        }
        .intersect(&bounds);
        // Unsigned values past `int.MaxValue` are negative ones read so.
        let signed = if unsigned {
            let mut out = Set::empty();
            for (low, high) in shifted.0 {
                let top = i64::from(i32::MAX);
                if low <= top {
                    out = out.union(&Set::range(low, high.min(top)));
                }
                if high > top {
                    let wrap = 1i64 << 32;
                    out = out.union(&Set::range(low.max(top + 1) - wrap, high - wrap));
                }
            }
            out
        } else {
            shifted
        };
        // `x - 1` wraps: back from the shifted value, `x` wraps too.
        let wrap = 1i64 << 32;
        let (min, max) = (i64::from(i32::MIN), i64::from(i32::MAX));
        let mut values = Set::empty();
        for (low, high) in signed.0 {
            let (low, high) = (low - offset, high - offset);
            for shift in [-wrap, 0, wrap] {
                values = values.union(&Set::range((low + shift).max(min), (high + shift).min(max)));
            }
        }
        values.intersect(&self.domain)
    }

    /// The values of the subject for which a condition holds, when the
    /// condition only looks at the subject.
    fn test(&self, condition: &Expr) -> Option<Set> {
        match condition {
            Expr::Unary(UnOp::Not, inner) => Some(self.test(inner)?.complement(&self.domain)),
            Expr::Binary(BinOp::LogicalAnd, left, right) => {
                Some(self.test(left)?.intersect(&self.test(right)?))
            }
            Expr::Binary(BinOp::LogicalOr, left, right) => {
                Some(self.test(left)?.union(&self.test(right)?))
            }
            Expr::Compare {
                op,
                left,
                right,
                unordered,
                float: false,
            } => {
                let (op, side, k) = match (self.shifted(left), self.constant(right)) {
                    (Some(side), Some(k)) => (*op, side, k),
                    _ => {
                        let flipped = match op {
                            Cmp::Lt => Cmp::Gt,
                            Cmp::Le => Cmp::Ge,
                            Cmp::Gt => Cmp::Lt,
                            Cmp::Ge => Cmp::Le,
                            other => *other,
                        };
                        (flipped, self.shifted(right)?, self.constant(left)?)
                    }
                };
                let unsigned = side.1 || (*unordered && !matches!(op, Cmp::Eq | Cmp::Ne));
                Some(self.compare(op, side.0, unsigned, k))
            }
            _ => None,
        }
    }

    fn is_routing(&self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::If { condition, .. } => self.test(condition).is_some(),
            Stmt::Switch { value, cases } => {
                self.shifted(value).is_some()
                    && cases.iter().all(|case| {
                        case.labels
                            .iter()
                            .flatten()
                            .all(|label| self.constant(label).is_some())
                    })
            }
            _ => false,
        }
    }
}

/// A statement the search stops at, and the values that get there.
#[derive(Debug)]
struct Leaf<'s> {
    target: Target<'s>,
    values: Set,
}

/// Where the search goes: statements, or a label among them.
#[derive(Debug, Clone, Copy)]
enum Target<'s> {
    Body(&'s [Stmt]),
    Label(u32),
}

/// Runs the values of `set` through a list of statements: the leaves they
/// reach go into `leaves`, and what runs off the end is returned. `None`
/// when something is not a search.
fn walk<'s>(
    search: &Search<'_>,
    stmts: &'s [Stmt],
    mut set: Set,
    tail: bool,
    nested: bool,
    leaves: &mut Vec<Leaf<'s>>,
) -> Option<Set> {
    for (index, stmt) in stmts.iter().enumerate() {
        if set.is_empty() {
            return Some(set);
        }
        if nested && *stmt == Stmt::Break {
            // Out of the search's own `switch`: on after it.
            return Some(set);
        }
        if let Stmt::Goto(label) = stmt
            && Some(*label) == search.end_label
        {
            let jumped = search.jumped.borrow().union(&set);
            *search.jumped.borrow_mut() = jumped;
            return Some(Set::empty());
        }
        if let Stmt::Goto(label) = stmt
            && search.labels.contains(label)
        {
            leaves.push(Leaf {
                target: Target::Label(*label),
                values: set,
            });
            return Some(Set::empty());
        }
        if !search.is_routing(stmt) {
            let mut body = &stmts[index..];
            // A case of the search's own `switch` ends in a `break` out of
            // it: running on, as far as the case is concerned.
            if nested && body.last() == Some(&Stmt::Break) {
                body = &body[..body.len() - 1];
            }
            // A body that runs on has to leave the search when it does.
            if !body.last().is_some_and(Stmt::ends_flow) && !tail {
                return None;
            }
            if contains_break(body) {
                return None;
            }
            leaves.push(Leaf {
                target: Target::Body(body),
                values: set,
            });
            return Some(Set::empty());
        }
        let stmt_tail = tail && index + 1 == stmts.len();
        match stmt {
            Stmt::If {
                condition,
                then,
                otherwise,
            } => {
                let yes = search.test(condition)?.intersect(&set);
                let no = yes.complement(&set);
                let out_yes = walk(search, then, yes, stmt_tail, nested, leaves)?;
                let out_no = walk(search, otherwise, no, stmt_tail, nested, leaves)?;
                set = out_yes.union(&out_no);
            }
            Stmt::Switch { value, cases } => {
                let (offset, _) = search.shifted(value)?;
                let mut taken = Set::empty();
                let mut out = Set::empty();
                let mut default = None;
                for case in cases {
                    let mut labels = Set::empty();
                    for label in case.labels.iter().flatten() {
                        let k = search.constant(label)? - offset;
                        labels = labels.union(&Set::range(k, k));
                    }
                    if case.labels.contains(&None) {
                        default = Some(case);
                        continue;
                    }
                    let here = labels.intersect(&set);
                    taken = taken.union(&here);
                    out = out.union(&walk(search, &case.body, here, stmt_tail, true, leaves)?);
                }
                let rest = taken.complement(&set);
                match default {
                    Some(case) => {
                        out = out.union(&walk(search, &case.body, rest, stmt_tail, true, leaves)?);
                    }
                    None => out = out.union(&rest),
                }
                set = out;
            }
            _ => return None,
        }
    }
    Some(set)
}

fn contains_break(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break => true,
        Stmt::While { .. }
        | Stmt::DoWhile { .. }
        | Stmt::For { .. }
        | Stmt::ForEach { .. }
        | Stmt::Switch { .. } => false,
        other => other.blocks().iter().any(|block| contains_break(block)),
    })
}

/// A case: its statements and the values that reach them.
struct Group {
    body: Vec<Stmt>,
    values: Set,
}

/// The cases the leaves make. The same statements reached along several
/// ways are one case; statements with labels in them are split there,
/// each label starting a case of the values jumping to it, and a case that
/// runs into the next says `goto case`.
fn group_leaves(leaves: Vec<Leaf<'_>>) -> Option<Vec<Group>> {
    struct Segment<'s> {
        label: Option<u32>,
        stmts: &'s [Stmt],
        values: Set,
        /// Whether the next segment follows it in the same statements.
        runs_on: bool,
    }
    let mut segments: Vec<Segment> = Vec::new();
    let mut bodies: Vec<(&[Stmt], usize)> = Vec::new();
    let mut jumps = Vec::new();
    for leaf in leaves {
        match leaf.target {
            Target::Label(label) => jumps.push((label, leaf.values)),
            Target::Body(body) => {
                // Equal statements are one case, even when the compiler
                // wrote them twice.
                let known = bodies.iter().find(|(known, _)| *known == body);
                if let Some((_, first)) = known {
                    let first = &mut segments[*first];
                    first.values = first.values.union(&leaf.values);
                    continue;
                }
                bodies.push((body, segments.len()));
                let mut start = 0;
                let mut label = None;
                let mut values = leaf.values;
                for (at, stmt) in body.iter().enumerate() {
                    if let Stmt::Label(next) = stmt {
                        if label.is_some() || at > start {
                            segments.push(Segment {
                                label,
                                stmts: &body[start..at],
                                values: std::mem::replace(&mut values, Set::empty()),
                                runs_on: true,
                            });
                        }
                        label = Some(*next);
                        start = at + 1;
                    }
                }
                segments.push(Segment {
                    label,
                    stmts: &body[start..],
                    values,
                    runs_on: false,
                });
            }
        }
    }
    for (label, values) in jumps {
        let segment = segments
            .iter_mut()
            .find(|segment| segment.label == Some(label))?;
        segment.values = segment.values.union(&values);
    }
    // A segment nothing jumps to is part of the one before it.
    let mut groups: Vec<(Group, Option<u32>, bool)> = Vec::new();
    let mut previous_runs_on = false;
    for segment in segments {
        let mut body = Vec::new();
        if let Some(label) = segment.label {
            body.push(Stmt::Label(label));
        }
        body.extend_from_slice(segment.stmts);
        if segment.values.is_empty() && previous_runs_on {
            let (last, _, runs_on) = groups.last_mut()?;
            last.body.extend(body);
            *runs_on = segment.runs_on;
        } else {
            groups.push((
                Group {
                    body,
                    values: segment.values,
                },
                segment.label,
                segment.runs_on,
            ));
        }
        previous_runs_on = segment.runs_on;
    }
    let starts: Vec<Option<u32>> = groups.iter().map(|(_, label, _)| *label).collect();
    let mut out = Vec::new();
    for (at, (mut group, _, runs_on)) in groups.into_iter().enumerate() {
        if group.values.is_empty() {
            return None;
        }
        if runs_on && !group.body.last().is_some_and(Stmt::ends_flow) {
            group
                .body
                .push(Stmt::Goto(starts.get(at + 1).copied().flatten()?));
        }
        out.push(group);
    }
    Some(out)
}

fn labels_and_jumps(stmt: &Stmt, labels: &mut HashSet<u32>, jumps: &mut Vec<u32>) {
    match stmt {
        Stmt::Label(label) => {
            labels.insert(*label);
        }
        Stmt::Goto(label) => jumps.push(*label),
        other => {
            for block in other.blocks() {
                for inner in block {
                    labels_and_jumps(inner, labels, jumps);
                }
            }
        }
    }
}

/// Whether a statement has a label in it, or a jump anywhere but to the
/// given one.
fn has_label(stmt: &Stmt, allowed: Option<u32>) -> bool {
    match stmt {
        Stmt::Label(_) => true,
        Stmt::Goto(label) => Some(*label) != allowed,
        other => other
            .blocks()
            .iter()
            .any(|block| block.iter().any(|inner| has_label(inner, allowed))),
    }
}

/// How many comparisons of the subject a statement's tests make, roughly:
/// a `switch` on it counts as many.
fn count_tests(stmt: &Stmt, subject: &Expr) -> usize {
    match stmt {
        Stmt::If {
            condition,
            then,
            otherwise,
        } => {
            let mut count = 0;
            condition.walk(&mut |e| {
                if let Expr::Compare { left, right, .. } = e
                    && [left, right].iter().any(|side| mentions(side, subject))
                {
                    count += 1;
                }
            });
            count
                + then
                    .iter()
                    .chain(otherwise)
                    .map(|inner| count_tests(inner, subject))
                    .sum::<usize>()
        }
        Stmt::Switch { value, .. } if mentions(value, subject) => 2,
        _ => 0,
    }
}

/// Whether an expression is the subject, shifted or cast.
fn mentions(expr: &Expr, subject: &Expr) -> bool {
    let mut inner = expr;
    while let Expr::Cast(_, deeper) | Expr::Binary(BinOp::Sub | BinOp::Add, deeper, _) = inner {
        inner = deeper;
    }
    inner == subject
}

/// The value a test looks at: the first plain variable a comparison with a
/// constant names.
fn subject_of(stmt: &Stmt) -> Option<Expr> {
    let mut found = None;
    let mut look = |expr: &Expr| {
        expr.walk(&mut |e| {
            if found.is_none()
                && let Expr::Compare { left, right, .. } = e
            {
                for side in [left, right] {
                    let mut inner = side.as_ref();
                    while let Expr::Cast(_, deeper)
                    | Expr::Binary(BinOp::Sub | BinOp::Add, deeper, _) = inner
                    {
                        inner = deeper;
                    }
                    if matches!(inner, Expr::Local(_) | Expr::Arg(_) | Expr::Field { .. })
                        && inner.is_pure()
                    {
                        found = Some(inner.clone());
                        return;
                    }
                }
            }
        });
    };
    match stmt {
        Stmt::If { condition, .. } => look(condition),
        Stmt::Switch { value, .. } => look(&Expr::compare(Cmp::Eq, value.clone(), Expr::Int(0))),
        _ => {}
    }
    found
}

/// Folds the searches in a list of statements back into `switch`es.
pub fn fold_int_switches(
    resolver: Resolver<'_>,
    type_of: &dyn Fn(&Expr) -> Option<TypeSig>,
    gotos: &HashMap<u32, usize>,
    stmts: &mut Vec<Stmt>,
) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        if let Some((end, switch)) = int_switch(resolver, type_of, gotos, stmts, index) {
            stmts.splice(index..end, [switch]);
            changed = true;
        }
        index += 1;
    }
    changed
}

fn int_switch(
    resolver: Resolver<'_>,
    type_of: &dyn Fn(&Expr) -> Option<TypeSig>,
    gotos: &HashMap<u32, usize>,
    stmts: &[Stmt],
    index: usize,
) -> Option<(usize, Stmt)> {
    let subject = subject_of(&stmts[index])?;
    // Three cases take two tests at least: count them before looking up
    // any types.
    let mut tests = 0;
    for stmt in &stmts[index..] {
        if !matches!(stmt, Stmt::If { .. } | Stmt::Switch { .. }) || tests >= 2 {
            break;
        }
        tests += count_tests(stmt, &subject);
    }
    if tests < 2 {
        return None;
    }
    let ty = type_of(&subject)?;
    let underlying = match resolver.enum_underlying(&ty) {
        Some(underlying) => underlying,
        None => ty.clone(),
    };
    let mut search = Search {
        resolver,
        subject: &subject,
        domain: domain(&underlying)?,
        end_label: None,
        jumped: std::cell::RefCell::new(Set::empty()),
        labels: HashSet::new(),
        enums: std::cell::RefCell::new(Vec::new()),
    };
    let mut end = index;
    while end < stmts.len() && search.is_routing(&stmts[end]) {
        end += 1;
    }
    if let Some(Stmt::Label(label)) = stmts.get(end) {
        search.end_label = Some(*label);
    }
    let region = &stmts[index..end];
    // A `switch` alone, with no tests inside its cases, is one already.
    if let [Stmt::Switch { cases, .. }] = region
        && !(end < stmts.len() && stmts.last().is_some_and(Stmt::ends_flow))
        && cases.iter().all(|case| {
            case.body
                .first()
                .is_none_or(|first| count_tests(first, &subject) == 0)
        })
    {
        return None;
    }
    if region.is_empty() {
        return None;
    }
    // Labels in the search are where the compiler shared a case's
    // statements; jumps go there or past the search.
    let mut labels = HashSet::new();
    let mut jumps = Vec::new();
    for stmt in region {
        labels_and_jumps(stmt, &mut labels, &mut jumps);
    }
    if jumps
        .iter()
        .any(|jump| Some(*jump) != search.end_label && !labels.contains(jump))
    {
        return None;
    }
    // Nothing outside may jump in: the labels end up in the cases.
    for label in &labels {
        let inside = jumps.iter().filter(|jump| *jump == label).count();
        if gotos.get(label).copied().unwrap_or(0) != inside {
            return None;
        }
    }
    search.labels = labels;
    let mut leaves = Vec::new();
    let out = walk(
        &search,
        region,
        search.domain.clone(),
        true,
        false,
        &mut leaves,
    );
    let out = out?.union(&search.jumped.borrow());
    if leaves.len() < 3 {
        return None;
    }
    let groups = group_leaves(leaves)?;
    // The default is what almost every value reaches: the statements after
    // the search, or one of its bodies.
    let small = |set: &Set| set.size() <= MAX_LABELS;
    let large: Vec<usize> = groups
        .iter()
        .enumerate()
        .filter(|(_, group)| !small(&group.values))
        .map(|(at, _)| at)
        .collect();
    let default_body = match (large.as_slice(), small(&out)) {
        ([], false) => None,
        ([at], true) => Some(*at),
        _ => return None,
    };
    // The values let through to what follows, when that is not the default
    // and nothing else goes there: their case is what follows.
    let tail = &stmts[end..];
    let takes_tail = default_body.is_some()
        && !out.is_empty()
        && tail.last().is_some_and(Stmt::ends_flow)
        && !tail.iter().any(|stmt| has_label(stmt, None))
        && groups
            .iter()
            .all(|group| group.body.last().is_some_and(Stmt::ends_flow));
    let mut cases_count = groups.len() - usize::from(default_body.is_some());
    if takes_tail {
        cases_count += 1;
    }
    let mut values_seen: HashSet<i64> = HashSet::new();
    let mut cases = Vec::new();
    for (at, group) in groups.iter().enumerate() {
        if Some(at) == default_body {
            continue;
        }
        let mut body = group.body.clone();
        if !body.last().is_some_and(Stmt::ends_flow) {
            body.push(Stmt::Break);
        }
        let labels: Vec<Option<Expr>> = group
            .values
            .values()
            .into_iter()
            .inspect(|value| {
                values_seen.insert(*value);
            })
            .map(|value| Some(coerce_expr(resolver, Expr::Int(value), &ty)))
            .collect();
        cases.push((
            group.values.0.first().map_or(0, |(low, _)| *low),
            labels,
            body,
        ));
    }
    // Values the search lets through to what follows, when that is not the
    // default: cases of their own that do nothing.
    if default_body.is_some() && !out.is_empty() {
        let labels = out
            .values()
            .into_iter()
            .map(|value| Some(coerce_expr(resolver, Expr::Int(value), &ty)))
            .collect();
        cases.push((
            out.0.first().map_or(0, |(low, _)| *low),
            labels,
            if takes_tail {
                tail.to_vec()
            } else {
                vec![Stmt::Break]
            },
        ));
    }
    if cases_count < 3 {
        return None;
    }
    cases.sort_by_key(|(first, ..)| *first);
    let mut cases: Vec<Case> = cases
        .into_iter()
        .map(|(_, labels, body)| Case { labels, body })
        .collect();
    if let Some(at) = default_body {
        let mut body = groups[at].body.clone();
        if !body.last().is_some_and(Stmt::ends_flow) {
            body.push(Stmt::Break);
        }
        cases.push(Case {
            labels: vec![None],
            body,
        });
    }
    let end = if takes_tail { stmts.len() } else { end };
    let switch = Stmt::Switch {
        value: subject,
        cases,
    };
    if stmts[index..end] == [switch.clone()][..] {
        return None;
    }
    Some((end, switch))
}

/// `switch (x) { case 1: return a; ... } return z;` with every case leaving
/// is `switch (x) { case 1: return a; ... default: return z; }`: the code
/// after it is only the default's.
pub fn fold_default_tails(stmts: &mut Vec<Stmt>) -> bool {
    let Some(at) = stmts
        .iter()
        .rposition(|stmt| matches!(stmt, Stmt::Switch { .. }))
    else {
        return false;
    };
    let tail = &stmts[at + 1..];
    if tail.is_empty()
        || !matches!(tail.last(), Some(Stmt::Return(_) | Stmt::Throw(_)))
        || tail
            .iter()
            .any(|stmt| has_label(stmt, None) || contains_break(std::slice::from_ref(stmt)))
    {
        return false;
    }
    let Stmt::Switch { cases, .. } = &stmts[at] else {
        return false;
    };
    let leaves_every_way = cases.iter().all(|case| {
        matches!(
            case.body.last(),
            Some(Stmt::Return(_) | Stmt::Throw(_) | Stmt::Continue | Stmt::Break)
        ) || case.body.last().is_some_and(Stmt::ends_flow)
    });
    if cases.iter().any(|case| case.labels.contains(&None)) || !leaves_every_way {
        return false;
    }
    // A `break` out of a section went to the tail: `goto default` now.
    let breaking = cases.iter().any(|case| contains_break(&case.body));
    let mut tail: Vec<Stmt> = stmts.drain(at + 1..).collect();
    let label = if breaking {
        let mut highest = 0;
        for stmt in stmts.iter().chain(tail.iter()) {
            max_label(stmt, &mut highest);
        }
        let label = highest + 1;
        tail.insert(0, Stmt::Label(label));
        Some(label)
    } else {
        None
    };
    if let Some(Stmt::Switch { cases, .. }) = stmts.last_mut() {
        if let Some(label) = label {
            for case in cases.iter_mut() {
                breaks_to(&mut case.body, label);
            }
        }
        cases.push(Case {
            labels: vec![None],
            body: tail,
        });
    }
    true
}

fn max_label(stmt: &Stmt, highest: &mut u32) {
    if let Stmt::Label(label) | Stmt::Goto(label) = stmt {
        *highest = (*highest).max(*label);
    }
    for block in stmt.blocks() {
        for inner in block {
            max_label(inner, highest);
        }
    }
}

/// The `break`s leaving a switch section, made jumps to a label.
fn breaks_to(stmts: &mut [Stmt], label: u32) {
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::Break => *stmt = Stmt::Goto(label),
            Stmt::While { .. }
            | Stmt::DoWhile { .. }
            | Stmt::For { .. }
            | Stmt::ForEach { .. }
            | Stmt::Switch { .. }
            | Stmt::LocalFunction { .. } => {}
            other => {
                for block in other.blocks_mut() {
                    breaks_to(block, label);
                }
            }
        }
    }
}
