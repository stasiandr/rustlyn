//! From blocks and branches to `if`, `while`, `switch` and `try`.
//!
//! A compiler lays structured code out in order: a loop is a contiguous run
//! of blocks ended by a branch back to its start, an `if` is a forward branch
//! over the blocks it guards, a `try` is exactly the range its exception
//! clause names. Walking the blocks in offset order and asking, at each one,
//! which of those shapes starts here recovers the structure without a
//! dominator tree; a branch that fits no shape is left as a `goto` rather
//! than guessed at.

use std::collections::{BTreeSet, HashSet};

use rustlyn_metadata::body::{Handler, Region};
use rustlyn_metadata::signature::TypeSig;

use crate::ir::{Case, Catch, Expr, Stmt};
use crate::names::Resolver;
use crate::stack::{Block, Blocks, Terminator, negate};

/// What a jump means where it is written: which target is `break`, which
/// is `continue`, and which is simply the end of the range being built.
#[derive(Clone, Debug, Default)]
struct Ctx {
    break_to: Option<u32>,
    continue_to: Option<u32>,
    /// The offset reached by falling out of the end of this range.
    follow: Option<u32>,
    /// The follows of the enclosing ranges this one ends together with.
    outer_follows: Vec<u32>,
}

impl Ctx {
    /// Whether a jump to the offset is a jump to where this range ends.
    fn is_follow(&self, target: u32) -> bool {
        self.follow == Some(target) || self.outer_follows.contains(&target)
    }

    /// The context of a range nested in this one, which falls out to
    /// `follow`: to this one's follows too only when it ends this one.
    fn inner(&self, follow: u32, at_end: bool) -> Self {
        if at_end {
            return self.nested(follow);
        }
        Self {
            break_to: self.break_to,
            continue_to: self.continue_to,
            follow: Some(follow),
            outer_follows: Vec::new(),
        }
    }

    /// The context of a range nested at the end of this one.
    fn nested(&self, follow: u32) -> Self {
        let mut outer = self.outer_follows.clone();
        if let Some(own) = self.follow
            && own != follow
        {
            outer.push(own);
        }
        Self {
            break_to: self.break_to,
            continue_to: self.continue_to,
            follow: Some(follow),
            outer_follows: outer,
        }
    }
}

/// One `try` with the handlers that share its range.
#[derive(Clone, Debug)]
struct TryGroup {
    try_start: u32,
    try_end: u32,
    handlers: Vec<Region>,
    /// The offset after the last handler.
    end: u32,
}

/// Turns a body's blocks into statements.
#[must_use]
pub fn structure(
    resolver: Resolver<'_>,
    blocks: &Blocks,
    regions: &[Region],
    code_size: u32,
) -> Vec<Stmt> {
    let mut blocks = blocks.blocks.clone();
    let protected: HashSet<u32> = regions
        .iter()
        .flat_map(|region| {
            let mut edges = vec![region.try_offset, region.handler_offset];
            if let Handler::Filter(at) = region.kind {
                edges.push(at);
            }
            edges
        })
        .collect();
    merge_conditions(&mut blocks, &protected);

    let mut groups: Vec<TryGroup> = Vec::new();
    for region in regions {
        let try_end = region.try_offset + region.try_length;
        let handler_end = region.handler_offset + region.handler_length;
        if let Some(group) = groups
            .iter_mut()
            .find(|group| group.try_start == region.try_offset && group.try_end == try_end)
        {
            group.handlers.push(*region);
            group.end = group.end.max(handler_end);
        } else {
            groups.push(TryGroup {
                try_start: region.try_offset,
                try_end,
                handlers: vec![*region],
                end: handler_end,
            });
        }
    }

    let mut structurer = Structurer {
        resolver,
        blocks: &blocks,
        groups,
        consumed: HashSet::new(),
        loops: HashSet::new(),
        labels: HashSet::new(),
        code_size,
    };
    let count = blocks.len();
    let mut stmts = structurer.range(0, count, &Ctx::default());
    let labels = structurer.labels;
    strip_labels(&mut stmts, &labels);
    stmts
}

/// Folds the blocks that only test a condition into the branch before them:
/// `a && b`, `a || b`, and a branch over a branch.
fn merge_conditions(blocks: &mut Vec<Block>, protected: &HashSet<u32>) {
    loop {
        let mut targeted: HashSet<u32> = HashSet::new();
        for block in blocks.iter() {
            match &block.terminator {
                Terminator::Jump(target) | Terminator::Leave(target) => {
                    targeted.insert(*target);
                }
                Terminator::Cond { target, .. } => {
                    targeted.insert(*target);
                }
                Terminator::Switch { targets, .. } => targeted.extend(targets.iter().copied()),
                _ => {}
            }
        }
        let mut merged = None;
        for index in 0..blocks.len().saturating_sub(1) {
            let Terminator::Cond {
                condition: first,
                target: first_target,
            } = &blocks[index].terminator
            else {
                continue;
            };
            let next = &blocks[index + 1];
            if !next.stmts.is_empty()
                || targeted.contains(&next.start)
                || protected.contains(&next.start)
            {
                continue;
            }
            let after = blocks.get(index + 2).map(|block| block.start);
            // Where falling out of `next` goes: past a block that only
            // jumps on, where it jumps.
            let lands = |target: u32| {
                Some(target) == after
                    || blocks.get(index + 2).is_some_and(|block| {
                        block.stmts.is_empty()
                            && matches!(block.terminator, Terminator::Jump(on) if on == target)
                    })
            };
            let replacement = match &next.terminator {
                Terminator::Cond {
                    condition: second,
                    target: second_target,
                } if second_target == first_target => Terminator::Cond {
                    condition: Expr::binary(
                        crate::ir::BinOp::LogicalOr,
                        first.clone(),
                        second.clone(),
                    ),
                    target: *first_target,
                },
                Terminator::Cond {
                    condition: second,
                    target: second_target,
                } if lands(*first_target) => Terminator::Cond {
                    condition: Expr::binary(
                        crate::ir::BinOp::LogicalAnd,
                        negate(first.clone()),
                        second.clone(),
                    ),
                    target: *second_target,
                },
                // A forward test over a backward jump stays as it is: folding
                // it would make a `do`/`while` out of a `break`.
                Terminator::Jump(target)
                    if Some(*first_target) == after && *target > blocks[index].start =>
                {
                    Terminator::Cond {
                        condition: negate(first.clone()),
                        target: *target,
                    }
                }
                _ => continue,
            };
            merged = Some((index, replacement));
            break;
        }
        let Some((index, replacement)) = merged else {
            break;
        };
        let removed = blocks.remove(index + 1);
        blocks[index].terminator = replacement;
        blocks[index].end = removed.end;
    }
}

struct Structurer<'b, 'a> {
    resolver: Resolver<'a>,
    blocks: &'b [Block],
    groups: Vec<TryGroup>,
    consumed: HashSet<usize>,
    /// The loops already built, as `(header, back-edge block)`.
    loops: HashSet<(usize, usize)>,
    labels: HashSet<u32>,
    code_size: u32,
}

impl Structurer<'_, '_> {
    fn idx(&self, offset: u32) -> Option<usize> {
        self.blocks
            .binary_search_by_key(&offset, |block| block.start)
            .ok()
    }

    /// The index a range ending at an offset stops before: the first block
    /// starting there or after, or the end of the method.
    fn idx_or_end(&self, offset: u32) -> usize {
        // A block removed there (a state machine's dispatch or handler) ends
        // the range at the next one, not at the end of the method.
        self.blocks.partition_point(|block| block.start < offset)
    }

    fn start(&self, index: usize) -> u32 {
        self.blocks
            .get(index)
            .map_or(self.code_size, |block| block.start)
    }

    /// The latest block in `[from, hi)` that branches back to the block at
    /// `from`.
    fn back_edge(&self, from: usize, hi: usize) -> Option<usize> {
        // A jump back to a block that only returns is that return, not a
        // loop: `goto case 1;` where case 1 returns.
        if self.is_return_block(from) {
            return None;
        }
        let header = self.start(from);
        (from..hi).rev().find(|&index| {
            !self.loops.contains(&(from, index))
                && matches!(
                    &self.blocks[index].terminator,
                    Terminator::Jump(target) | Terminator::Cond { target, .. } if *target == header
                )
        })
    }

    /// The group of protected regions whose `try` starts at a block, the
    /// widest one first.
    fn try_starting_at(&self, index: usize, hi: usize) -> Option<usize> {
        let start = self.start(index);
        let limit = self.start(hi);
        self.groups
            .iter()
            .enumerate()
            .filter(|(at, group)| {
                !self.consumed.contains(at) && group.try_start == start && group.end <= limit
            })
            .max_by_key(|(_, group)| group.end)
            .map(|(at, _)| at)
    }

    /// The block in `[lo, cond)` where a loop body begins whose condition
    /// is the block at `cond`: the condition branches back to it, nothing
    /// in front of it falls into it, and nothing else jumps to it.
    fn detached_loop_body(&self, lo: usize, cond: usize, hi: usize) -> Option<usize> {
        if cond >= hi {
            return None;
        }
        let Terminator::Cond { target, .. } = &self.blocks[cond].terminator else {
            return None;
        };
        let body_start = self.idx(*target)?;
        if body_start <= lo || body_start >= cond {
            return None;
        }
        // The block before the body leaves by a jump, so the body is not
        // fallen into.
        if !matches!(
            self.blocks[body_start - 1].terminator,
            Terminator::Jump(_)
                | Terminator::Leave(_)
                | Terminator::Return(_)
                | Terminator::Throw(_)
        ) {
            return None;
        }
        // Only the condition block jumps to the body.
        let targeted_elsewhere = self.blocks.iter().enumerate().any(|(at, block)| {
            at != cond
                && match &block.terminator {
                    Terminator::Jump(t)
                    | Terminator::Leave(t)
                    | Terminator::Cond { target: t, .. } => *t == *target,
                    Terminator::Switch { targets, .. } => targets.contains(target),
                    _ => false,
                }
        });
        if targeted_elsewhere {
            return None;
        }
        // Nothing before the body inside the range jumps past it into the
        // body's blocks, which would make the range a plain `if`.
        Some(body_start)
    }

    /// The block that ends a loop condition starting at `cond_start` by
    /// branching back to `body`: the blocks before it branch only among
    /// themselves, and nothing else enters them but at the start.
    fn condition_end(&self, cond_start: usize, body: usize, hi: usize) -> Option<usize> {
        let back = self.start(body);
        let cond_at = (cond_start..hi.min(cond_start + 16)).find(|&at| {
            matches!(&self.blocks[at].terminator,
                Terminator::Cond { target, .. } | Terminator::Jump(target) if *target == back)
        })?;
        let inside = |target: u32| {
            self.idx(target)
                .is_some_and(|at| at > cond_start && at <= cond_at)
        };
        for at in cond_start..cond_at {
            let ok = match &self.blocks[at].terminator {
                Terminator::Fall => true,
                Terminator::Jump(target) | Terminator::Cond { target, .. } => inside(*target),
                _ => false,
            };
            if !ok {
                return None;
            }
        }
        // Nothing outside jumps into the middle of it.
        let entered = self.blocks.iter().enumerate().any(|(at, block)| {
            (at < cond_start || at > cond_at)
                && match &block.terminator {
                    Terminator::Jump(target)
                    | Terminator::Leave(target)
                    | Terminator::Cond { target, .. } => inside(*target),
                    Terminator::Switch { targets, .. } => targets.iter().any(|t| inside(*t)),
                    _ => false,
                }
        });
        (!entered).then_some(cond_at)
    }

    /// Follows a chain of blocks that only jump on.
    fn resolve_chain(&self, mut target: u32) -> u32 {
        for _ in 0..8 {
            let Some(index) = self.idx(target) else {
                break;
            };
            let block = &self.blocks[index];
            match &block.terminator {
                Terminator::Jump(next) if block.stmts.is_empty() && *next != target => {
                    target = *next;
                }
                _ => break,
            }
        }
        target
    }

    /// Where a forward branch inside the range lands, as a block index, when
    /// it stays inside: the follow counts as the end of the range.
    fn forward_target(&self, target: u32, index: usize, hi: usize, ctx: &Ctx) -> Option<usize> {
        if ctx.is_follow(target) {
            return Some(hi);
        }
        let found = self.idx(target)?;
        (found > index && found < hi).then_some(found)
    }

    #[allow(clippy::too_many_lines)]
    fn range(&mut self, lo: usize, hi: usize, ctx: &Ctx) -> Vec<Stmt> {
        let mut out = Vec::new();
        let mut index = lo;
        while index < hi {
            if let Some(group) = self.try_starting_at(index, hi) {
                self.consumed.insert(group);
                let group = self.groups[group].clone();
                out.push(Stmt::Label(group.try_start));
                out.push(self.build_try(&group, ctx));
                index = self.idx_or_end(group.end);
                continue;
            }

            if let Some(back) = self.back_edge(index, hi) {
                self.loops.insert((index, back));
                out.push(Stmt::Label(self.start(index)));
                let after = self.start(back + 1);
                let header = self.start(index);
                match self.blocks[back].terminator.clone() {
                    Terminator::Cond { condition, .. } => {
                        // `do { ... } while (c)`: the condition sits in the
                        // last block, after whatever else that block does.
                        let loop_ctx = Ctx {
                            break_to: Some(after),
                            continue_to: if self.blocks[back].stmts.is_empty() {
                                Some(self.start(back))
                            } else {
                                None
                            },
                            follow: Some(self.start(back)),
                            outer_follows: Vec::new(),
                        };
                        let mut body = if back > index {
                            self.range(index, back, &loop_ctx)
                        } else {
                            Vec::new()
                        };
                        body.push(Stmt::Label(self.start(back)));
                        body.extend(self.blocks[back].stmts.clone());
                        out.push(Stmt::DoWhile { body, condition });
                    }
                    _ => {
                        let loop_ctx = Ctx {
                            break_to: Some(after),
                            continue_to: Some(header),
                            follow: None,
                            outer_follows: Vec::new(),
                        };
                        let body = self.range(index, back + 1, &loop_ctx);
                        out.push(Stmt::While {
                            condition: Expr::Bool(true),
                            body,
                        });
                    }
                }
                index = back + 1;
                continue;
            }

            let block = &self.blocks[index];
            out.push(Stmt::Label(block.start));
            out.extend(block.stmts.iter().cloned());
            match block.terminator.clone() {
                Terminator::Fall | Terminator::EndFinally | Terminator::EndFilter(_) => {
                    index += 1;
                }
                Terminator::Return(value) => {
                    out.push(Stmt::Return(value));
                    index += 1;
                }
                Terminator::Throw(value) => {
                    out.push(Stmt::Throw(Some(value)));
                    index += 1;
                }
                Terminator::Rethrow => {
                    out.push(Stmt::Throw(None));
                    index += 1;
                }
                Terminator::Jump(target) | Terminator::Leave(target) => {
                    // `br cond` over a body whose last block branches back to
                    // the body's start is a `while`.
                    // A condition that is always true (`while (true)` in a
                    // debug build) jumps back unconditionally; one that
                    // computes something first (`await e.MoveNextAsync()`)
                    // may take several blocks that fall into each other.
                    if let Some(cond_start) = self.idx(target)
                        && cond_start > index
                        && cond_start < hi
                        && let Some(cond_at) = self.condition_end(cond_start, index + 1, hi)
                    {
                        let condition = match self.blocks[cond_at].terminator.clone() {
                            Terminator::Cond { condition, .. } => condition,
                            _ => Expr::Bool(true),
                        };
                        let loop_ctx = Ctx {
                            break_to: Some(self.start(cond_at + 1)),
                            continue_to: Some(target),
                            follow: None,
                            outer_follows: Vec::new(),
                        };
                        let mut body = Vec::new();
                        body.push(Stmt::Label(target));
                        // What the condition computes first, `&&` and all
                        // when a debug build stores it.
                        let computed_ctx = Ctx {
                            break_to: None,
                            continue_to: None,
                            follow: Some(self.start(cond_at)),
                            outer_follows: Vec::new(),
                        };
                        body.extend(self.range(cond_start, cond_at, &computed_ctx));
                        body.extend(self.blocks[cond_at].stmts.iter().cloned());
                        if condition != Expr::Bool(true) {
                            body.push(Stmt::If {
                                condition: negate(condition),
                                then: vec![Stmt::Break],
                                otherwise: Vec::new(),
                            });
                        }
                        body.extend(self.range(index + 1, cond_start, &loop_ctx));
                        let while_loop = Stmt::While {
                            condition: Expr::Bool(true),
                            body,
                        };
                        // A loop further on jumping back to this condition
                        // is a loop around this one: `do { while (a) { } B }
                        // while (c)`, the inner loop's test being where the
                        // outer one starts.
                        let jumps_back = |at: usize| {
                            matches!(&self.blocks[at].terminator,
                                Terminator::Cond { target: to, .. } | Terminator::Jump(to) if *to == target)
                        };
                        let outer_back = (cond_at + 1..hi).rev().find(|&at| jumps_back(at));
                        if let Some(back) = outer_back
                            && !(cond_at + 1..back).any(jumps_back)
                        {
                            let outer_ctx = Ctx {
                                break_to: Some(self.start(back + 1)),
                                continue_to: if self.blocks[back].stmts.is_empty() {
                                    Some(self.start(back))
                                } else {
                                    None
                                },
                                follow: Some(self.start(back)),
                                outer_follows: Vec::new(),
                            };
                            let mut outer = vec![while_loop];
                            outer.extend(self.range(cond_at + 1, back, &outer_ctx));
                            outer.push(Stmt::Label(self.start(back)));
                            outer.extend(self.blocks[back].stmts.iter().cloned());
                            let condition = match self.blocks[back].terminator.clone() {
                                Terminator::Cond { condition, .. } => condition,
                                _ => Expr::Bool(true),
                            };
                            out.push(Stmt::DoWhile {
                                body: outer,
                                condition,
                            });
                            index = back + 1;
                            continue;
                        }
                        out.push(while_loop);
                        index = cond_at + 1;
                        continue;
                    }
                    self.jump(target, index, hi, ctx, &mut out);
                    index += 1;
                }
                Terminator::Cond { condition, target } => {
                    let Some(then_end) = self.forward_target(target, index, hi, ctx) else {
                        let mut then = Vec::new();
                        self.jump(target, index, hi, ctx, &mut then);
                        if then.is_empty() {
                            then.push(Stmt::Goto(target));
                            self.labels.insert(target);
                        }
                        out.push(Stmt::If {
                            condition,
                            then,
                            otherwise: Vec::new(),
                        });
                        index += 1;
                        continue;
                    };
                    if then_end == index + 1 {
                        // Nothing is guarded: the branch skips over nothing.
                        index += 1;
                        continue;
                    }
                    // A loop whose body was laid out inside the guarded range
                    // but is entered only from the condition after it:
                    // `if (c) { A } while (x) { B }` with `B` before `x`.
                    if let Some(body_start) = self.detached_loop_body(index + 1, then_end, hi) {
                        let then_ctx = ctx.inner(target, false);
                        let then = self.range(index + 1, body_start, &then_ctx);
                        out.push(Stmt::If {
                            condition: negate(condition),
                            then,
                            otherwise: Vec::new(),
                        });
                        let Terminator::Cond {
                            condition: looping, ..
                        } = self.blocks[then_end].terminator.clone()
                        else {
                            unreachable!()
                        };
                        let loop_ctx = Ctx {
                            break_to: Some(self.start(then_end + 1)),
                            continue_to: Some(target),
                            follow: None,
                            outer_follows: Vec::new(),
                        };
                        let mut body = Vec::new();
                        body.push(Stmt::Label(target));
                        body.extend(self.blocks[then_end].stmts.iter().cloned());
                        body.push(Stmt::If {
                            condition: negate(looping),
                            then: vec![Stmt::Break],
                            otherwise: Vec::new(),
                        });
                        body.extend(self.range(body_start, then_end, &loop_ctx));
                        out.push(Stmt::While {
                            condition: Expr::Bool(true),
                            body,
                        });
                        index = then_end + 1;
                        continue;
                    }
                    // The guarded range ends with a jump over an `else`?
                    let last = then_end - 1;
                    let mut else_end = None;
                    if last > index
                        && let Terminator::Jump(over) | Terminator::Leave(over) =
                            self.blocks[last].terminator
                    {
                        let over = self.resolve_chain(over);
                        let returns = self.idx(over).is_some_and(|at| self.is_return_block(at));
                        if returns {
                            // A jump to a shared `return` is a return, not an
                            // `else`.
                        } else if ctx.is_follow(over)
                            && Some(over) != ctx.continue_to
                            && then_end < hi
                        {
                            else_end = Some((hi, over));
                        } else if let Some(at) = self.idx(over)
                            && at > then_end
                            && at < hi
                        {
                            else_end = Some((at, over));
                        }
                    }
                    // The `if` ends the range, or what follows it runs next.
                    let if_ends_range = else_end.map_or(then_end, |(at, _)| at) >= hi;
                    let (then_ctx_follow, otherwise) = match else_end {
                        Some((at, over)) => {
                            let else_ctx = ctx.inner(over, if_ends_range);
                            (over, self.range(then_end, at, &else_ctx))
                        }
                        None => (target, Vec::new()),
                    };
                    let then_ctx = ctx.inner(then_ctx_follow, if_ends_range);
                    let then = self.range(index + 1, then_end, &then_ctx);
                    // A conditional expression branches to its `true` side,
                    // the way Roslyn lays it out: the branch condition stays
                    // as written, with that side first, rather than being
                    // negated for the layout.
                    let slot_store = |stmts: &[Stmt]| -> Option<u32> {
                        let mut real = stmts.iter().filter(|stmt| !matches!(stmt, Stmt::Label(_)));
                        let (first, second) = (real.next(), real.next());
                        match (first, second) {
                            (Some(Stmt::Expr(Expr::Assign(target, _))), None) => {
                                match target.as_ref() {
                                    Expr::Slot(slot) => Some(*slot),
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    };
                    let ternary =
                        slot_store(&then).is_some() && slot_store(&then) == slot_store(&otherwise);
                    if ternary {
                        out.push(Stmt::If {
                            condition,
                            then: otherwise,
                            otherwise: then,
                        });
                    } else {
                        out.push(Stmt::If {
                            condition: negate(condition),
                            then,
                            otherwise,
                        });
                    }
                    index = else_end.map_or(then_end, |(at, _)| at);
                }
                Terminator::Switch { value, targets } => {
                    index = self.build_switch(value, &targets, index, hi, ctx, &mut out);
                }
            }
        }
        out
    }

    /// What a jump to a target means where it stands: nothing at the end of
    /// a range that reaches the target anyway, `break`, `continue`, a
    /// `return` through a shared exit block, or a `goto`.
    fn jump(&mut self, target: u32, index: usize, hi: usize, ctx: &Ctx, out: &mut Vec<Stmt>) {
        let target = self.resolve_chain(target);
        // `x = e; br RET` with `RET: ldloc x; ret` is `return e`, wherever
        // `RET` is.
        if let Some(at) = self.idx(target)
            && self.blocks[at].stmts.is_empty()
            && let Terminator::Return(Some(Expr::Local(local))) = &self.blocks[at].terminator
        {
            let local = *local;
            // The store may sit a few statements back, behind statements
            // that do not touch the local; a constant is safe to move past
            // them.
            let is_store = |stmt: &Stmt| matches!(stmt, Stmt::Expr(Expr::Assign(place, _)) if **place == Expr::Local(local));
            let mentions = |stmt: &Stmt| {
                let mut found = false;
                stmt.walk_exprs(&mut |e| {
                    if *e == Expr::Local(local) {
                        found = true;
                    }
                });
                found
            };
            let mut position = None;
            for back in 1..=3 {
                if out.len() < back {
                    break;
                }
                let at = out.len() - back;
                if is_store(&out[at]) {
                    let value = match &out[at] {
                        Stmt::Expr(Expr::Assign(_, value)) => value.as_ref().clone(),
                        _ => unreachable!(),
                    };
                    if back == 1 || value.is_constant() {
                        position = Some(at);
                    }
                    break;
                }
                if mentions(&out[at]) || matches!(out[at], Stmt::Label(_)) {
                    break;
                }
            }
            if let Some(at) = position {
                let Stmt::Expr(Expr::Assign(_, value)) = out.remove(at) else {
                    unreachable!()
                };
                out.push(Stmt::Return(Some(*value)));
                return;
            }
        }
        if ctx.is_follow(target) {
            if index + 1 == hi {
                return;
            }
            if Some(target) == ctx.continue_to {
                out.push(Stmt::Continue);
                return;
            }
        } else if Some(target) == ctx.continue_to {
            out.push(Stmt::Continue);
            return;
        } else if Some(target) == ctx.break_to {
            out.push(Stmt::Break);
            return;
        }
        if let Some(at) = self.idx(target)
            && let Some(returned) = self.return_through(at, out)
        {
            out.push(returned);
            return;
        }
        self.labels.insert(target);
        out.push(Stmt::Goto(target));
    }

    /// Whether a block does nothing but return, possibly through an
    /// assignment of a constant and a jump to the block that does.
    fn is_return_block(&self, at: usize) -> bool {
        let block = &self.blocks[at];
        let real: Vec<&Stmt> = block
            .stmts
            .iter()
            .filter(|s| !matches!(s, Stmt::Label(_)))
            .collect();
        match (&real[..], &block.terminator) {
            ([], Terminator::Return(None)) => true,
            ([], Terminator::Return(Some(value))) => {
                value.is_constant() || matches!(value, Expr::Local(_))
            }
            ([Stmt::Expr(Expr::Assign(place, value))], terminator) => {
                let Expr::Local(local) = **place else {
                    return false;
                };
                if !value.is_pure() {
                    return false;
                }
                let returns_local = |terminator: &Terminator| matches!(terminator, Terminator::Return(Some(Expr::Local(at))) if *at == local);
                match terminator {
                    Terminator::Return(Some(Expr::Local(found))) => *found == local,
                    Terminator::Jump(next) | Terminator::Leave(next) => {
                        self.idx(self.resolve_chain(*next)).is_some_and(|next_at| {
                            self.blocks[next_at].stmts.is_empty()
                                && returns_local(&self.blocks[next_at].terminator)
                        })
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// The `return` a jump to a block amounts to, when the block only returns:
    /// `ret`, `ldloc x; ret` after `x` was just assigned, or an assignment
    /// of a constant followed by a jump to such a block.
    fn return_through(&self, at: usize, out: &mut Vec<Stmt>) -> Option<Stmt> {
        let block = &self.blocks[at];
        if block.stmts.is_empty() {
            match &block.terminator {
                Terminator::Return(None) => return Some(Stmt::Return(None)),
                Terminator::Return(Some(Expr::Local(local))) => {
                    if let Some(Stmt::Expr(Expr::Assign(place, _))) = out.last()
                        && **place == Expr::Local(*local)
                    {
                        let Some(Stmt::Expr(Expr::Assign(_, value))) = out.pop() else {
                            unreachable!()
                        };
                        return Some(Stmt::Return(Some(*value)));
                    }
                    return Some(Stmt::Return(Some(Expr::Local(*local))));
                }
                Terminator::Return(Some(value)) if value.is_constant() => {
                    return Some(Stmt::Return(Some(value.clone())));
                }
                _ => return None,
            }
        }
        // `x = <pure>; br RET` where `RET` is `ldloc x; ret`.
        let real: Vec<&Stmt> = block
            .stmts
            .iter()
            .filter(|s| !matches!(s, Stmt::Label(_)))
            .collect();
        if let [Stmt::Expr(Expr::Assign(place, value))] = real.as_slice()
            && let Expr::Local(local) = **place
            && value.is_pure()
        {
            let returns_local = |terminator: &Terminator| matches!(terminator, Terminator::Return(Some(Expr::Local(at))) if *at == local);
            if returns_local(&block.terminator) {
                return Some(Stmt::Return(Some((**value).clone())));
            }
            if let Terminator::Jump(next) | Terminator::Leave(next) = block.terminator
                && let Some(next_at) = self.idx(self.resolve_chain(next))
                && self.blocks[next_at].stmts.is_empty()
                && returns_local(&self.blocks[next_at].terminator)
            {
                return Some(Stmt::Return(Some((**value).clone())));
            }
        }
        None
    }

    fn build_try(&mut self, group: &TryGroup, ctx: &Ctx) -> Stmt {
        let inner = ctx.nested(group.end);
        let body = self.range(
            self.idx_or_end(group.try_start),
            self.idx_or_end(group.try_end),
            &inner,
        );
        let mut catches = Vec::new();
        let mut finally = None;
        for handler in &group.handlers {
            let handler_end = handler.handler_offset + handler.handler_length;
            let handler_ctx = ctx.nested(group.end);
            let mut stmts = self.range(
                self.idx_or_end(handler.handler_offset),
                self.idx_or_end(handler_end),
                &handler_ctx,
            );
            match handler.kind {
                Handler::Finally => finally = Some(stmts),
                Handler::Fault => {
                    stmts.insert(0, Stmt::Comment("fault handler".into()));
                    finally = Some(stmts);
                }
                Handler::Catch(token) => {
                    let ty = self.resolver.token_sig(token);
                    let ty = match self.resolver.raw_name(token).as_deref() {
                        Some("System.Object") => None,
                        _ => Some(ty),
                    };
                    let variable = take_catch_variable(&mut stmts);
                    catches.push(Catch {
                        ty,
                        variable,
                        filter: None,
                        body: stmts,
                    });
                }
                Handler::Filter(at) => {
                    let filter_stmts = self.range(
                        self.idx_or_end(at),
                        self.idx_or_end(handler.handler_offset),
                        &Ctx::default(),
                    );
                    let last = self.idx_or_end(handler.handler_offset).saturating_sub(1);
                    let result = match &self.blocks[last].terminator {
                        Terminator::EndFilter(value) => value.clone(),
                        _ => Expr::Bool(true),
                    };
                    let variable = take_catch_variable(&mut stmts);
                    catches.push(Catch {
                        ty: Some(TypeSig::Object),
                        variable,
                        filter: Some(Expr::Raw(String::new())),
                        body: stmts,
                    });
                    // The filter is handed on whole; `simplify` reads the
                    // type it tests and the condition out of it.
                    if let Some(catch) = catches.last_mut() {
                        catch.filter = Some(Expr::Lambda {
                            id: u32::MAX,
                            params: Vec::new(),
                            outs: Vec::new(),
                            body: Box::new(crate::ir::Body::Block({
                                let mut all = filter_stmts;
                                all.push(Stmt::Return(Some(result)));
                                all
                            })),
                        });
                    }
                }
            }
        }
        Stmt::Try {
            body,
            catches,
            finally,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn build_switch(
        &mut self,
        value: Expr,
        targets: &[u32],
        index: usize,
        hi: usize,
        ctx: &Ctx,
        out: &mut Vec<Stmt>,
    ) -> usize {
        let mut default = self.start(index + 1);
        if let Some(next) = self.blocks.get(index + 1)
            && next.stmts.is_empty()
            && let Terminator::Jump(target) = next.terminator
        {
            default = target;
        }
        let mut starts: BTreeSet<u32> = targets.iter().copied().collect();
        starts.insert(default);
        let first = starts.iter().next().copied().unwrap_or(default);
        // A case outside the range belongs to what is around the switch:
        // written here as well, it would be written twice.
        if first <= self.start(index) || self.idx_or_end(first) > hi {
            // A case before the switch, or outside the range: only `goto`
            // says where each value goes.
            let mut cases = Vec::new();
            for (at, target) in targets.iter().enumerate() {
                self.labels.insert(*target);
                cases.push(Case {
                    labels: vec![Some(Expr::Int(at as i64))],
                    body: vec![Stmt::Goto(*target)],
                });
            }
            out.push(Stmt::Switch { value, cases });
            return index + 1;
        }
        let limit = self.start(hi);
        let mut end = starts.iter().next_back().copied().unwrap_or(default);
        loop {
            let mut changed = false;
            let from = self.idx_or_end(first);
            let to = self.idx_or_end(end).min(hi);
            for block in &self.blocks[from..to] {
                let mut candidates = Vec::new();
                match &block.terminator {
                    Terminator::Jump(target) | Terminator::Leave(target) => {
                        candidates.push(*target);
                    }
                    Terminator::Cond { target, .. } => candidates.push(*target),
                    Terminator::Switch { targets, .. } => {
                        candidates.extend(targets.iter().copied())
                    }
                    _ => {}
                }
                for target in candidates {
                    if target > end && target <= limit {
                        end = target;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // Nothing past the range: what is there is written by what is
        // around the switch.
        let end = end.min(limit);
        let (value, offset) = match value {
            Expr::Binary(crate::ir::BinOp::Sub, inner, base) => match *base {
                Expr::Int(base) => (*inner, base),
                other => (Expr::binary(crate::ir::BinOp::Sub, *inner, other), 0),
            },
            other => (other, 0),
        };
        let starts: Vec<u32> = starts.into_iter().filter(|start| *start < end).collect();
        let mut cases = Vec::new();
        for (position, start) in starts.iter().enumerate() {
            let next = starts.get(position + 1).copied().unwrap_or(end);
            let mut labels: Vec<Option<Expr>> = targets
                .iter()
                .enumerate()
                .filter(|(_, target)| **target == *start)
                .map(|(at, _)| Some(Expr::Int(at as i64 + offset)))
                .collect();
            if *start == default {
                labels.push(None);
            }
            let case_ctx = Ctx {
                break_to: Some(end),
                continue_to: ctx.continue_to,
                follow: None,
                outer_follows: Vec::new(),
            };
            let from = self.idx_or_end(*start);
            let to = self.idx_or_end(next);
            let mut body = self.range(from, to, &case_ctx);
            // A case that runs into the next one is `goto case`, which C#
            // needs said.
            if next < end
                && to > from
                && matches!(
                    self.blocks[to - 1].terminator,
                    Terminator::Fall | Terminator::Cond { .. }
                )
                && !body.last().is_some_and(Stmt::ends_flow)
            {
                self.labels.insert(next);
                body.push(Stmt::Goto(next));
            }
            cases.push(Case { labels, body });
        }
        // Values whose case is past the switch leave it: to the code right
        // after it with `break`, further with a jump.
        for (at, target) in targets.iter().enumerate() {
            if starts.contains(target) {
                continue;
            }
            let body = if *target == end {
                vec![Stmt::Break]
            } else {
                self.labels.insert(*target);
                vec![Stmt::Goto(*target)]
            };
            cases.push(Case {
                labels: vec![Some(Expr::Int(at as i64 + offset))],
                body,
            });
        }
        // Blocks laid out between the switch and its first case are
        // reached only by jumps from elsewhere: they go after the last
        // case, jumping out by label, so that they can move to where the
        // jumps are.
        let gap_from = if default == self.start(index + 1) {
            index + 1
        } else {
            index + 2
        };
        let gap_to = self.idx_or_end(first).min(hi);
        if gap_from < gap_to
            && let Some(last) = cases.last_mut()
        {
            let gap_ctx = Ctx {
                break_to: None,
                continue_to: ctx.continue_to,
                follow: None,
                outer_follows: Vec::new(),
            };
            if !last.body.last().is_some_and(Stmt::ends_flow) {
                last.body.push(Stmt::Break);
            }
            let mut gap = self.range(gap_from, gap_to, &gap_ctx);
            if !gap.last().is_some_and(Stmt::ends_flow) {
                let next = self.start(gap_to);
                self.labels.insert(next);
                gap.push(Stmt::Goto(next));
            }
            last.body.extend(gap);
        }
        out.push(Stmt::Switch { value, cases });
        self.idx_or_end(end).min(hi)
    }
}

/// The local a handler stores its exception into, taken off the front of
/// the handler.
fn take_catch_variable(stmts: &mut Vec<Stmt>) -> Option<u16> {
    let position = stmts
        .iter()
        .position(|stmt| !matches!(stmt, Stmt::Label(_)))?;
    if let Stmt::Expr(Expr::Assign(place, value)) = &stmts[position]
        && **value == Expr::CaughtException
        && let Expr::Local(local) = **place
    {
        stmts.remove(position);
        return Some(local);
    }
    None
}

/// Removes the labels nothing jumps to.
fn strip_labels(stmts: &mut Vec<Stmt>, keep: &HashSet<u32>) {
    stmts.retain(|stmt| match stmt {
        Stmt::Label(at) => keep.contains(at),
        _ => true,
    });
    for stmt in stmts.iter_mut() {
        for block in stmt.blocks_mut() {
            strip_labels(block, keep);
        }
        if let Stmt::Try { catches, .. } = stmt {
            for catch in catches {
                if let Some(Expr::Lambda { body, .. }) = &mut catch.filter
                    && let crate::ir::Body::Block(inner) = body.as_mut()
                {
                    strip_labels(inner, keep);
                }
            }
        }
    }
}
