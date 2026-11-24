//! Shared tails, written out where they are jumped to.
//!
//! Where two branches of an `if` end the same way, the compiler writes the
//! ending once, in one branch, and has the other jump into it: `if (a) {
//! A; goto L; } else { B; L: S }`. C# cannot jump into a block from outside
//! it. When both the jump and the labelled statements end their branches,
//! running `S` in place of the jump ends the `if` exactly as the jump did,
//! so a short `S` is written out there instead.

use std::collections::{HashMap, HashSet};

use crate::ir::{Expr, Stmt, UnOp};

/// How many statements, nested ones counted, a tail may have to be copied.
const MAX_TAIL: usize = 16;

/// How many a tail may have that one jump alone goes to: copied there, it
/// is most often moved, the place it was left unreachable.
const MAX_MOVED_TAIL: usize = 64;

/// Copies the shared tails of the `if`s in a body into the branches that
/// jump to them.
pub fn duplicate_shared_tails(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            changed |= duplicate_shared_tails(block);
        }
        if !matches!(stmt, Stmt::If { .. }) {
            continue;
        }
        let mut inside = HashSet::new();
        labels_in(std::slice::from_ref(stmt), &mut inside);
        if inside.is_empty() {
            continue;
        }
        let mut tails = HashMap::new();
        collect_tails(stmt, &inside, &mut tails);
        if !tails.is_empty() {
            changed |= replace_tail_gotos(stmt, &tails);
        }
    }
    changed
}

/// The labelled runs of statements that end an `if`: in its branches, and
/// in theirs where a branch ends with an `if`.
fn collect_tails(stmt: &Stmt, inside: &HashSet<u32>, tails: &mut HashMap<u32, Vec<Stmt>>) {
    let Stmt::If {
        then, otherwise, ..
    } = stmt
    else {
        return;
    };
    for block in [then, otherwise] {
        for (at, item) in block.iter().enumerate() {
            let Stmt::Label(label) = item else {
                continue;
            };
            let segment = &block[at + 1..];
            // Jumps out of the copy must still see where they go: only to
            // labels outside the `if`.
            let mut jumps = Vec::new();
            jumps_of(segment, &mut jumps);
            let mut labels = HashSet::new();
            labels_in(segment, &mut labels);
            if !segment.is_empty()
                && labels.is_empty()
                && jumps.iter().all(|jump| !inside.contains(jump))
                && size(segment) <= MAX_TAIL
            {
                tails.insert(*label, segment.to_vec());
            }
        }
        if let Some(last) = block.last() {
            collect_tails(last, inside, tails);
        }
    }
}

/// Replaces a jump to a tail that ends a branch with the tail itself.
fn replace_tail_gotos(stmt: &mut Stmt, tails: &HashMap<u32, Vec<Stmt>>) -> bool {
    let Stmt::If {
        then, otherwise, ..
    } = stmt
    else {
        return false;
    };
    let mut changed = false;
    for block in [then, otherwise] {
        // `if (c) goto L; R` ending the branch is `if (c) { S } else { R }`.
        let jump_at = block.iter().position(|item| {
            matches!(item, Stmt::If { then, otherwise, .. }
                if otherwise.is_empty()
                    && matches!(then.as_slice(), [Stmt::Goto(label)] if tails.contains_key(label)))
        });
        if let Some(at) = jump_at
            && at + 1 < block.len()
            && !block.iter().any(|item| matches!(item, Stmt::Label(_)))
        {
            let rest: Vec<Stmt> = block.drain(at + 1..).collect();
            if let Some(Stmt::If {
                then: jump,
                otherwise: other,
                ..
            }) = block.last_mut()
                && let [Stmt::Goto(label)] = jump.as_slice()
                && let Some(tail) = tails.get(label)
            {
                *jump = tail.clone();
                *other = rest;
                changed = true;
            }
        }
        if let Some(Stmt::Goto(label)) = block.last()
            && let Some(tail) = tails.get(label)
            && !block.contains(&Stmt::Label(*label))
        {
            block.pop();
            block.extend(tail.iter().cloned());
            changed = true;
        }
        if let Some(last) = block.last_mut() {
            changed |= replace_tail_gotos(last, tails);
        }
    }
    changed
}

fn labels_in(stmts: &[Stmt], out: &mut HashSet<u32>) {
    for stmt in stmts {
        if let Stmt::Label(label) = stmt {
            out.insert(*label);
        }
        for block in stmt.blocks() {
            labels_in(block, out);
        }
    }
}

fn jumps_of(stmts: &[Stmt], out: &mut Vec<u32>) {
    for stmt in stmts {
        if let Stmt::Goto(label) = stmt {
            out.push(*label);
        }
        for block in stmt.blocks() {
            jumps_of(block, out);
        }
    }
}

fn size(stmts: &[Stmt]) -> usize {
    stmts
        .iter()
        .map(|stmt| 1 + stmt.blocks().iter().map(|block| size(block)).sum::<usize>())
        .sum()
}

/// A tail that returns or jumps away, wherever it is, can be written in
/// place of any jump to it that cannot see its label: nothing after it runs
/// either way. The jump has to be inside the same `try`s, so that the
/// `finally`s and the handlers that apply are the same; the tail has to
/// reach nothing outside itself by `break` or `continue`, and the labels it
/// jumps to have to be in sight of the copy.
/// The most statements of a tail copied to a jump that can see it.
const TINY_TAIL: usize = 2;

pub fn copy_returning_tails(stmts: &mut Vec<Stmt>) -> bool {
    let mut survey = Survey::default();
    survey.walk(stmts, &mut Vec::new(), &mut Vec::new(), &mut Vec::new());
    // The jumps to replace, by where they are: the latest and deepest
    // first, so that replacing one leaves the places of the rest as they
    // were.
    let mut jump_counts: HashMap<u32, usize> = HashMap::new();
    for (_, label, _) in &survey.jumps {
        *jump_counts.entry(*label).or_default() += 1;
    }
    let mut sites: Vec<(Vec<usize>, u32)> = survey
        .jumps
        .into_iter()
        .filter_map(|(site, label, tries)| {
            let (tail, label_list, label_tries) = survey.tails.get(&label)?;
            if size(tail) > MAX_TAIL && jump_counts.get(&label) != Some(&1) {
                return None;
            }
            let list = &site[..site.len() - 1];
            // The jumps the tail makes have to reach their labels from
            // where it is copied to.
            let mut jumps = Vec::new();
            jumps_of(tail, &mut jumps);
            let reached = jumps.iter().all(|jump| {
                survey
                    .labels
                    .get(jump)
                    .is_some_and(|at| list.starts_with(at))
            });
            // In sight of the label, a jump to a return that is short
            // enough reads better as the return itself.
            let tiny = size(tail) <= TINY_TAIL
                && matches!(tail.last(), Some(Stmt::Return(_) | Stmt::Throw(_)));
            ((!list.starts_with(label_list) || tiny) && *label_tries == tries && reached)
                .then_some((site, label))
        })
        .collect();
    sites.sort_by(|a, b| b.0.cmp(&a.0));
    let changed = !sites.is_empty();
    for (site, label) in sites {
        let Some((tail, ..)) = survey.tails.get(&label) else {
            continue;
        };
        let (index, list_path) = site.split_last().expect("a site has an index");
        if let Some(list) = list_at(stmts, list_path)
            && list.get(*index) == Some(&Stmt::Goto(label))
        {
            list.splice(*index..=*index, tail.iter().cloned());
        }
    }
    changed
}

/// A tail: the statements, the path of the list the label is in, and the
/// `try` statements around it.
type Tail = (Vec<Stmt>, Vec<usize>, Vec<Vec<usize>>);

/// What runs when a list runs off its end.
enum After<'s> {
    Unknown,
    /// These statements, then what runs after them.
    Rest(&'s [Stmt]),
    /// The loop the list is the body of: its condition, its body, and the
    /// statements after it.
    Loop(&'s Expr, &'s [Stmt], &'s [Stmt]),
}

#[derive(Default)]
struct Survey {
    tails: HashMap<u32, Tail>,
    /// Each `goto`: its path, its label and the `try`s around it.
    jumps: Vec<(Vec<usize>, u32, Vec<Vec<usize>>)>,
    /// The path of the list each label is in.
    labels: HashMap<u32, Vec<usize>>,
}

impl Survey {
    /// A list's path is the index of each statement on the way down and of
    /// the block of it taken.
    ///
    /// `after` holds, for each enclosing list, what runs when it runs off
    /// its end: the rest of the list around it when it is a branch of an
    /// `if`, the loop again when it is a loop's body.
    fn walk<'s>(
        &mut self,
        stmts: &'s [Stmt],
        path: &mut Vec<usize>,
        tries: &mut Vec<Vec<usize>>,
        after: &mut Vec<After<'s>>,
    ) {
        for (at, stmt) in stmts.iter().enumerate() {
            match stmt {
                Stmt::Label(label) => {
                    self.labels.insert(*label, path.clone());
                    // The run from the label, and on out of the `if`s around
                    // it, to where it returns.
                    let mut segment = Vec::new();
                    let mut ended = run_on(&mut segment, &stmts[at + 1..]);
                    let mut outward = after.iter().rev();
                    while !ended && size(&segment) <= MAX_MOVED_TAIL {
                        match outward.next() {
                            Some(After::Rest(rest)) => ended = run_on(&mut segment, rest),
                            // Off the end of a loop's body is its condition:
                            // the loop again, then what follows it.
                            Some(After::Loop(condition, body, rest)) => {
                                let body = match body {
                                    [before @ .., Stmt::Label(_)] => before,
                                    whole => whole,
                                };
                                segment.push(Stmt::While {
                                    condition: (*condition).clone(),
                                    body: body.to_vec(),
                                });
                                ended = run_on(&mut segment, rest);
                            }
                            _ => break,
                        }
                    }
                    let segment = segment.as_slice();
                    let mut labels = HashSet::new();
                    labels_in(segment, &mut labels);
                    if segment.last().is_some_and(Stmt::ends_flow)
                        && labels.is_empty()
                        && !breaks_or_continues(segment)
                        && size(segment) <= MAX_MOVED_TAIL
                    {
                        self.tails
                            .insert(*label, (segment.to_vec(), path.clone(), tries.clone()));
                    }
                }
                Stmt::Goto(label) => {
                    let mut site = path.clone();
                    site.push(at);
                    self.jumps.push((site, *label, tries.clone()));
                }
                Stmt::LocalFunction { .. } => continue,
                _ => {}
            }
            path.push(at);
            let is_try = matches!(stmt, Stmt::Try { .. });
            if is_try {
                tries.push(path.clone());
            }
            after.push(match stmt {
                Stmt::If { .. } => After::Rest(&stmts[at + 1..]),
                // Off the end of a `while (true)` is its start again.
                Stmt::While {
                    condition: Expr::Bool(true),
                    body,
                } => After::Rest(body.as_slice()),
                Stmt::While { condition, body } | Stmt::DoWhile { body, condition } => {
                    After::Loop(condition, body.as_slice(), &stmts[at + 1..])
                }
                _ => After::Unknown,
            });
            for (block_at, block) in stmt.blocks().into_iter().enumerate() {
                path.push(block_at);
                self.walk(block, path, tries, after);
                path.pop();
            }
            after.pop();
            if is_try {
                tries.pop();
            }
            path.pop();
        }
    }
}

/// Adds to a tail the statements that run in turn, up to one that ends
/// the flow: into a `while (true)`, whose body runs from its start. Whether
/// the flow ended.
fn run_on(segment: &mut Vec<Stmt>, stmts: &[Stmt]) -> bool {
    for stmt in stmts {
        if let Stmt::While {
            condition: Expr::Bool(true),
            body,
        } = stmt
        {
            // Only a loop left by nothing but `return` or `throw` is its
            // body run once: the check on the tail rejects the rest.
            return run_on(segment, body);
        }
        segment.push(stmt.clone());
        if stmt.ends_flow() {
            return true;
        }
    }
    false
}

fn list_at<'s>(stmts: &'s mut Vec<Stmt>, path: &[usize]) -> Option<&'s mut Vec<Stmt>> {
    let mut list = stmts;
    for pair in path.chunks(2) {
        let [at, block] = pair else {
            return None;
        };
        let stmt = list.get_mut(*at)?;
        list = stmt.blocks_mut().into_iter().nth(*block)?;
    }
    Some(list)
}

fn breaks_or_continues(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break | Stmt::Continue => true,
        Stmt::While { .. }
        | Stmt::DoWhile { .. }
        | Stmt::For { .. }
        | Stmt::ForEach { .. }
        | Stmt::LocalFunction { .. } => false,
        // `continue` in a switch still continues the loop around it.
        Stmt::Switch { cases, .. } => cases.iter().any(|case| {
            case.body.iter().any(|inner| {
                breaks_or_continues(std::slice::from_ref(inner)) && !matches!(inner, Stmt::Break)
            })
        }),
        other => other
            .blocks()
            .iter()
            .any(|block| breaks_or_continues(block)),
    })
}

/// A label in a branch of an `if` that jumps from elsewhere cannot see is
/// moved out after the `if`, with the branch it is in: `if (c) { T } else
/// { S; L: E }` is `if (c) { T; goto M; } S; L: E M:`, only the `else`
/// going on past the `if`; a `then` so placed is swapped into the `else`
/// first. What was left is a jump out of a block, which C# allows; a label
/// nested deeper moves out one `if` at a time.
pub fn hoist_branch_labels(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    for _ in 0..256 {
        let mut survey = Survey::default();
        survey.walk(stmts, &mut Vec::new(), &mut Vec::new(), &mut Vec::new());
        let unseen = survey.jumps.iter().filter_map(|(site, label, _)| {
            let at = survey.labels.get(label)?;
            (!site[..site.len() - 1].starts_with(at)).then_some((site, *label, at))
        });
        // A label in a branch of an `if`.
        let mut found = None;
        for (_, _, at) in unseen {
            let Some((&block, rest)) = at.split_last() else {
                continue;
            };
            let Some((&index, parent)) = rest.split_last() else {
                continue;
            };
            let is_if = list_at(stmts, parent)
                .and_then(|list| list.get(index))
                .is_some_and(|stmt| matches!(stmt, Stmt::If { .. }));
            if is_if {
                found = Some((parent.to_vec(), index, block));
                break;
            }
        }
        let Some((parent, index, block)) = found else {
            break;
        };
        let mut next = 0;
        let mut all = HashSet::new();
        labels_in(stmts, &mut all);
        for label in &all {
            next = next.max(*label + 1);
        }
        let Some(list) = list_at(stmts, &parent) else {
            break;
        };
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = list.remove(index)
        else {
            break;
        };
        // The branch the label heads goes last.
        let (condition, mut first, mut last) = if block == 0 {
            (crate::stack::negate(condition), otherwise, then)
        } else {
            (condition, then, otherwise)
        };
        let end = next;
        let needs_end = !first.last().is_some_and(Stmt::ends_flow);
        if needs_end {
            first.push(Stmt::Goto(end));
        }
        let mut replaced = vec![Stmt::If {
            condition,
            then: first,
            otherwise: Vec::new(),
        }];
        replaced.append(&mut last);
        if needs_end {
            replaced.push(Stmt::Label(end));
        }
        list.splice(index..index, replaced);
        changed = true;
    }
    changed
}

/// `while (true) { A; if (c) break; L: B } C`, where `C` leaves and jumps
/// back to `L`, is `while (true) { A; if (c) { C } L: B }`: what follows
/// the loop's one way out goes in its place, where the label is in sight.
pub fn sink_exits_into_loops(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            changed |= sink_exits_into_loops(block);
        }
    }
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Stmt::While {
            condition: Expr::Bool(true),
            body,
        } = &stmts[index]
        else {
            index += 1;
            continue;
        };
        let rest = &stmts[index + 1..];
        let mut body_labels = HashSet::new();
        for stmt in body {
            if let Stmt::Label(label) = stmt {
                body_labels.insert(*label);
            }
        }
        let mut jumps = Vec::new();
        jumps_of(rest, &mut jumps);
        let mut rest_labels = HashSet::new();
        labels_in(rest, &mut rest_labels);
        let mut outside_jumps = Vec::new();
        jumps_of(&stmts[..=index], &mut outside_jumps);
        if !jumps.iter().any(|jump| body_labels.contains(jump))
            || !rest.last().is_some_and(Stmt::ends_flow)
            || breaks_or_continues(rest)
            || outside_jumps.iter().any(|jump| rest_labels.contains(jump))
            || count_breaks(body) != 1
        {
            index += 1;
            continue;
        }
        let rest: Vec<Stmt> = stmts.drain(index + 1..).collect();
        if let Stmt::While { body, .. } = &mut stmts[index] {
            replace_break(body, &rest);
        }
        changed = true;
        index += 1;
    }
    changed
}

/// The `break`s leaving the loop whose body this is.
fn count_breaks(stmts: &[Stmt]) -> usize {
    stmts
        .iter()
        .map(|stmt| match stmt {
            Stmt::Break => 1,
            Stmt::While { .. }
            | Stmt::DoWhile { .. }
            | Stmt::For { .. }
            | Stmt::ForEach { .. }
            | Stmt::Switch { .. }
            | Stmt::LocalFunction { .. } => 0,
            other => other.blocks().iter().map(|block| count_breaks(block)).sum(),
        })
        .sum()
}

fn replace_break(stmts: &mut Vec<Stmt>, with: &[Stmt]) -> bool {
    for at in 0..stmts.len() {
        match &mut stmts[at] {
            Stmt::Break => {
                stmts.splice(at..=at, with.iter().cloned());
                return true;
            }
            Stmt::While { .. }
            | Stmt::DoWhile { .. }
            | Stmt::For { .. }
            | Stmt::ForEach { .. }
            | Stmt::Switch { .. }
            | Stmt::LocalFunction { .. } => {}
            other => {
                for block in other.blocks_mut() {
                    if replace_break(block, with) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// A jump from before a loop into its body, loops within loops, enters it
/// by a flag instead: `f = true; goto E;` to just before the loop, whose
/// bodies skip what comes before the label while `f` is set, and the label
/// clears it. `new_flag` makes the `bool` variable.
pub fn enter_loops_by_flag(stmts: &mut Vec<Stmt>, new_flag: &mut dyn FnMut() -> u16) -> bool {
    let mut changed = false;
    for _ in 0..64 {
        let mut survey = Survey::default();
        survey.walk(stmts, &mut Vec::new(), &mut Vec::new(), &mut Vec::new());
        let mut found = None;
        'search: for (site, label, _) in &survey.jumps {
            let Some(label_list) = survey.labels.get(label) else {
                continue;
            };
            let site_list = &site[..site.len() - 1];
            if site_list.starts_with(label_list) {
                continue;
            }
            // The list both are under, and the loop in it the label is in.
            let common = site_list
                .iter()
                .zip(label_list.iter())
                .take_while(|(a, b)| a == b)
                .count();
            let common = common - common % 2;
            let (prefix, chain) = label_list.split_at(common);
            if chain.is_empty() || chain.len() % 2 != 0 {
                continue;
            }
            let entry = chain[0];
            // From before the loop, or from after it: then what follows the
            // loop has to leave, so that a loop around it goes round only by
            // the jumps.
            let before = site.get(common).is_some_and(|at| *at < entry);
            let after = site.get(common).is_some_and(|at| *at > entry);
            if !before && !after {
                continue;
            }
            if after {
                let Some(list) = list_at(stmts, prefix) else {
                    continue;
                };
                let rest = &list[entry + 1..];
                if !rest.last().is_some_and(Stmt::ends_flow) || breaks_or_continues(rest) {
                    continue;
                }
            }
            // Every step down is into a loop's body.
            let mut list = match list_at(stmts, prefix) {
                Some(list) => list.clone(),
                None => continue,
            };
            for (depth, pair) in chain.chunks(2).enumerate() {
                let (at, block) = (pair[0], pair[1]);
                let Some(stmt) = list.get(at) else {
                    continue 'search;
                };
                let body = match stmt {
                    Stmt::DoWhile { body, .. }
                    | Stmt::While {
                        condition: Expr::Bool(true),
                        body,
                    } if block == 0 => body.clone(),
                    // A branch is entered past its test.
                    Stmt::If { then, .. } if block == 0 => then.clone(),
                    Stmt::If { otherwise, .. } if block == 1 => otherwise.clone(),
                    _ => continue 'search,
                };
                // What is skipped may hold no label.
                let mut labels = HashSet::new();
                labels_in(
                    &body[..at_or_label(&body, chain, depth, *label)],
                    &mut labels,
                );
                if !labels.is_empty() {
                    continue 'search;
                }
                list = body;
            }
            // Every other jump to it that cannot see it comes from before
            // the loop too.
            let same_side = survey.jumps.iter().all(|(other, target, _)| {
                *target != *label
                    || other[..other.len() - 1].starts_with(label_list)
                    || (other.starts_with(prefix)
                        && other
                            .get(common)
                            .is_some_and(|at| if before { *at < entry } else { *at > entry }))
            });
            if same_side {
                found = Some((prefix.to_vec(), chain.to_vec(), *label, after));
                break;
            }
        }
        let Some((prefix, chain, label, after)) = found else {
            break;
        };
        let flag = new_flag();
        let mut all = HashSet::new();
        labels_in(stmts, &mut all);
        let entry_label = all.iter().max().map_or(0, |max| max + 1);
        // The jumps: set the flag and go to the loop.
        let Some(list) = list_at(stmts, &prefix) else {
            break;
        };
        let mut entry = chain[0];
        let (mut at, mut end) = if after {
            (entry + 1, list.len())
        } else {
            (0, entry)
        };
        while at < end {
            if list[at] == Stmt::Goto(label) {
                list[at] = Stmt::Goto(entry_label);
                list.insert(
                    at,
                    Stmt::Expr(Expr::assign(Expr::Local(flag), Expr::Bool(true))),
                );
                if !after {
                    entry += 1;
                }
                end += 1;
                at += 2;
                continue;
            }
            redirect(&mut list[at], label, flag, entry_label);
            at += 1;
        }
        // Each body skips what comes before, while the flag is set; a branch
        // is taken whatever its test says.
        let mut body_list: &mut Vec<Stmt> = enter(&mut list[entry], chain[1], flag);
        for depth in 0..chain.len() / 2 {
            let last = depth * 2 + 2 == chain.len();
            let stop = if last {
                body_list
                    .iter()
                    .position(|stmt| *stmt == Stmt::Label(label))
                    .unwrap_or(0)
            } else {
                chain[depth * 2 + 2]
            };
            if stop > 0 {
                let skipped: Vec<Stmt> = body_list.drain(..stop).collect();
                body_list.insert(
                    0,
                    Stmt::If {
                        condition: Expr::unary(UnOp::Not, Expr::Local(flag)),
                        then: skipped,
                        otherwise: Vec::new(),
                    },
                );
            }
            if last {
                let at = body_list
                    .iter()
                    .position(|stmt| *stmt == Stmt::Label(label))
                    .map_or(1, |at| at + 1);
                body_list.insert(
                    at,
                    Stmt::Expr(Expr::assign(Expr::Local(flag), Expr::Bool(false))),
                );
                break;
            }
            // The next step sits just after the `if` now.
            let next_at = if stop > 0 { 1 } else { 0 };
            body_list = enter(&mut body_list[next_at], chain[depth * 2 + 3], flag);
        }
        let Some(list) = list_at(stmts, &prefix) else {
            break;
        };
        if after {
            // `while (true) { E: loop; rest }`, rest always leaving.
            let mut body: Vec<Stmt> = list.drain(entry..).collect();
            body.insert(0, Stmt::Label(entry_label));
            list.push(Stmt::Expr(Expr::assign(
                Expr::Local(flag),
                Expr::Bool(false),
            )));
            list.push(Stmt::While {
                condition: Expr::Bool(true),
                body,
            });
        } else {
            list.insert(entry, Stmt::Label(entry_label));
            list.insert(
                entry,
                Stmt::Expr(Expr::assign(Expr::Local(flag), Expr::Bool(false))),
            );
        }
        changed = true;
    }
    changed
}

/// The list a step down goes into: a loop's body, or a branch of an `if`
/// whose test the flag overrides.
fn enter(stmt: &mut Stmt, block: usize, flag: u16) -> &mut Vec<Stmt> {
    if let Stmt::If { condition, .. } = stmt {
        let test = std::mem::replace(condition, Expr::Bool(true));
        *condition = if block == 0 {
            Expr::binary(crate::ir::BinOp::LogicalOr, Expr::Local(flag), test)
        } else {
            Expr::binary(
                crate::ir::BinOp::LogicalAnd,
                Expr::unary(UnOp::Not, Expr::Local(flag)),
                test,
            )
        };
    }
    stmt.blocks_mut()
        .into_iter()
        .nth(block)
        .expect("the step's block is there")
}

/// Where in a loop body the way to the label goes on: the next loop, or
/// the label itself.
fn at_or_label(body: &[Stmt], chain: &[usize], depth: usize, label: u32) -> usize {
    match chain.get(depth * 2 + 2) {
        Some(next) => *next,
        None => body
            .iter()
            .position(|stmt| *stmt == Stmt::Label(label))
            .unwrap_or(0),
    }
}

/// `goto L` in a statement is `f = true; goto E;`.
fn redirect(stmt: &mut Stmt, label: u32, flag: u16, entry: u32) {
    if matches!(stmt, Stmt::LocalFunction { .. }) {
        return;
    }
    for block in stmt.blocks_mut() {
        let mut at = 0;
        while at < block.len() {
            if block[at] == Stmt::Goto(label) {
                block[at] = Stmt::Goto(entry);
                block.insert(
                    at,
                    Stmt::Expr(Expr::assign(Expr::Local(flag), Expr::Bool(true))),
                );
                at += 2;
                continue;
            }
            redirect(&mut block[at], label, flag, entry);
            at += 1;
        }
    }
}
