//! Making structured statements read like the C# they came from.
//!
//! The structurer is faithful and literal: every value that crossed a block
//! boundary is a slot, every property is a `get_` call, every loop is
//! `while (true)` with a `break` at the top. This pass folds all of that
//! back — slots into the expressions that use them, accessor calls into
//! members, `if`/`break` into loop conditions, enumerator loops into
//! `foreach` — one local rewrite at a time, each of which is a pattern a
//! compiler is known to produce.

use std::collections::{BTreeMap, HashMap, HashSet};

use rustlyn_metadata::signature::TypeSig;

use crate::ir::{BinOp, Body, Case, Catch, Cmp, Expr, Interpolation, Stmt, UnOp};
use crate::names::Resolver;
use crate::stack::{MethodContext, coerce_expr, negate, substitute};

/// Answers what type an expression has, as far as the metadata says.
#[derive(Debug)]
pub struct Typer<'c, 'a> {
    pub ctx: &'c MethodContext<'a>,
    pub slot_types: &'c HashMap<u32, TypeSig>,
    /// Locals the simplifier made up, numbered after the method's own.
    pub extra_locals: std::cell::RefCell<Vec<TypeSig>>,
    /// Names suggested for locals: a captured variable keeps its field's.
    pub hints: std::cell::RefCell<HashMap<u16, String>>,
}

impl Typer<'_, '_> {
    /// A new local of the given type.
    pub fn new_local(&self, ty: TypeSig) -> u16 {
        let mut extras = self.extra_locals.borrow_mut();
        extras.push(ty);
        (self.ctx.locals.len() + extras.len() - 1) as u16
    }

    #[must_use]
    pub fn type_of(&self, expr: &Expr) -> Option<TypeSig> {
        Some(match expr {
            Expr::This => self.ctx.this_type.clone(),
            Expr::Arg(at) => self.ctx.params.get(*at as usize)?.clone(),
            Expr::Local(at) => {
                let at = *at as usize;
                match self.ctx.locals.get(at) {
                    Some(ty) => ty.clone(),
                    None => self
                        .extra_locals
                        .borrow()
                        .get(at - self.ctx.locals.len())?
                        .clone(),
                }
            }
            Expr::Slot(id) => self.slot_types.get(id)?.clone(),
            Expr::Int(_) => TypeSig::Int32,
            Expr::Long(_) => TypeSig::Int64,
            Expr::Float(_, true) => TypeSig::Single,
            Expr::Float(_, false) => TypeSig::Double,
            Expr::Bool(_) | Expr::Compare { .. } | Expr::Is(..) | Expr::IsPattern(..) => {
                TypeSig::Boolean
            }
            Expr::Char(_) => TypeSig::Char,
            Expr::Str(_) => TypeSig::String,
            Expr::EnumMember(ty, _)
            | Expr::Default(ty)
            | Expr::Cast(ty, _)
            | Expr::CheckedCast(ty, _)
            | Expr::OperatorCast(ty, _) => ty.clone(),
            Expr::As(ty, _) if self.ctx.resolver.is_value_type(ty) => TypeSig::Object,
            Expr::As(ty, _) => ty.clone(),
            Expr::TypeOf(_) | Expr::Box(..) | Expr::CaughtException | Expr::Null => TypeSig::Object,
            Expr::SizeOf(_) | Expr::Length(_) => TypeSig::Int32,
            Expr::Unary(UnOp::Not, _) => TypeSig::Boolean,
            Expr::Unary(UnOp::AddressOf, inner) => TypeSig::ByRef(Box::new(self.type_of(inner)?)),
            Expr::Unary(UnOp::Deref, inner) => match self.type_of(inner)? {
                TypeSig::ByRef(inner) | TypeSig::Pointer(inner) => *inner,
                other => other,
            },
            // `-b` and `~b` of a small type are `int`s, and `-u` a `long`.
            Expr::Unary(op, inner) => match read_through(self.type_of(inner)?) {
                ty if numeric_rank(&ty) == Some(1) => TypeSig::Int32,
                TypeSig::UInt32 if *op == UnOp::Neg => TypeSig::Int64,
                ty => ty,
            },
            Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr, ..) => TypeSig::Boolean,
            // A shift is of its left side, promoted.
            Expr::Binary(BinOp::Shl | BinOp::Shr | BinOp::UShr, left, _) => {
                match read_through(self.type_of(left)?) {
                    ty if numeric_rank(&ty) == Some(1) => TypeSig::Int32,
                    ty => ty,
                }
            }
            Expr::Binary(op, left, right) => {
                // A `ref` variable in arithmetic is its value.
                let left_ty = self.type_of(left).map(read_through);
                // `n + " "` is a string, whatever number `n` is: taking the
                // number's type for it casts the next operand to that type.
                if *op == BinOp::Add
                    && (left_ty
                        .as_ref()
                        .is_some_and(|ty| is_string_type(self.ctx.resolver, ty))
                        || self
                            .type_of(right)
                            .is_some_and(|ty| is_string_type(self.ctx.resolver, &ty)))
                {
                    return Some(TypeSig::String);
                }
                // The difference of two values of an enum is a number.
                if *op == BinOp::Sub
                    && let Some(ty) = &left_ty
                    && let Some(underlying) = self.ctx.resolver.enum_underlying(ty)
                    && self.type_of(right).as_ref() == Some(ty)
                {
                    return Some(if numeric_rank(&underlying).unwrap_or(0) < 3 {
                        TypeSig::Int32
                    } else {
                        underlying
                    });
                }
                // Arithmetic promotes both sides to the wider.
                if !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr | BinOp::Coalesce)
                    && let Some(left_ty) = &left_ty
                    && let Some(right_ty) = self.type_of(right).map(read_through)
                    && let (Some(a), Some(b)) = (numeric_rank(left_ty), numeric_rank(&right_ty))
                {
                    // `c - 32` on a `char` is an `int`, like any small type's.
                    let promoted = |ty: TypeSig| {
                        if numeric_rank(&ty).unwrap_or(0) < 3 {
                            TypeSig::Int32
                        } else {
                            ty
                        }
                    };
                    if left.is_constant() {
                        return Some(promoted(right_ty));
                    }
                    if right.is_constant() {
                        return Some(promoted(left_ty.clone()));
                    }
                    let wider = if b > a { right_ty } else { left_ty.clone() };
                    return Some(if numeric_rank(&wider).unwrap_or(0) < 3 {
                        TypeSig::Int32
                    } else {
                        wider
                    });
                }
                match left_ty {
                    Some(ty) if !left.is_constant() => ty,
                    _ => self.type_of(right)?,
                }
            }
            Expr::Assign(target, _) | Expr::Compound(_, target, _) => self.type_of(target)?,
            // An element of an array, a span, a list or a string.
            Expr::Indexer { receiver, .. } => match self.type_of(receiver)? {
                TypeSig::Vector(element) => *element,
                TypeSig::String => TypeSig::Char,
                TypeSig::Generic {
                    definition,
                    arguments,
                } if arguments.len() == 1
                    && matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                        if matches!(self.ctx.resolver.raw_name(*token).as_deref(),
                            Some("System.Span`1" | "System.ReadOnlySpan`1"
                                | "System.Collections.Generic.List`1"
                                | "System.Collections.Generic.IList`1"
                                | "System.Collections.Generic.IReadOnlyList`1"))) =>
                {
                    arguments.into_iter().next()?
                }
                _ => return None,
            },
            Expr::Increment { target, .. } => self.type_of(target)?,
            Expr::Call { method, .. } => {
                substitute(&method.sig.returns, &method.declaring, &method.type_args)
            }
            Expr::New { ctor, .. } => ctor.declaring.clone(),
            Expr::With { source, .. } => self.type_of(source)?,
            Expr::NewOf(ty) => ty.clone(),
            Expr::NewArray { element, size, .. } => match size.as_ref() {
                Expr::Tuple(sizes) => TypeSig::Array {
                    element: Box::new(element.clone()),
                    rank: sizes.len() as u32,
                },
                _ => TypeSig::Vector(Box::new(element.clone())),
            },
            Expr::Field { field, .. } => substitute(&field.ty, &field.declaring, &[]),
            Expr::Index { array, .. } => match self.type_of(array)? {
                TypeSig::Vector(element)
                | TypeSig::Array { element, .. }
                | TypeSig::Pointer(element) => *element,
                other => self.ctx.resolver.fixed_buffer_element(&other)?,
            },
            Expr::Conditional(_, a, b) => match self.type_of(a) {
                Some(ty) if !a.is_constant() => ty,
                _ => self.type_of(b)?,
            },
            Expr::Delegate { ty, .. } => ty.clone(),
            Expr::Property { ty: Some(ty), .. } => ty.clone(),
            Expr::Property { name, .. } => match name.as_str() {
                "Length" | "Count" => TypeSig::Int32,
                "HasValue" => TypeSig::Boolean,
                _ => return None,
            },
            Expr::Interpolated(_) => TypeSig::String,
            _ => return None,
        })
    }

    fn is_bool(&self, expr: &Expr) -> bool {
        matches!(self.type_of(expr), Some(TypeSig::Boolean))
    }
}

/// Everything the simplifier does to a body, in order.
pub fn simplify(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) {
    // Casts are written while calls still say what they take: `Add` is
    // folded into a collection initializer that does not.
    crate::fit::fit_arguments(typer, stmts);
    for _ in 0..4 {
        rewrite_exprs(typer, stmts);
        let reads = Uses {
            slots: slot_reads(stmts),
            locals: typed_local_uses(typer, stmts),
            args_written: args_written(stmts),
            gotos: all_goto_counts(stmts),
        };
        // Copies are propagated over the whole body: a slot's assignments
        // may sit in different branches.
        propagate_slot_copies(stmts, &reads);
        propagate_immutable_locals(typer, stmts, &reads);
        drop_dead_local_stores(stmts, &reads);
        simplify_block(typer, stmts, &reads);
        // After the statements are folded: a foreach's element or a
        // using's resource is not a temporary.
        forward_local_copies(typer, stmts);
        drop_dead_slots(stmts);
    }
    if fold_null_conditional_tail(stmts) {
        rewrite_exprs(typer, stmts);
    }
    let mut moved = inline_goto_targets(stmts) | fold_goto_loops(stmts);
    // What still jumps into a branch from another is a shared ending.
    if crate::tails::duplicate_shared_tails(stmts) | crate::tails::copy_returning_tails(stmts) {
        tidy_gotos(stmts, true);
        moved = true;
    }
    // What is still out of sight is brought into it.
    if crate::tails::sink_exits_into_loops(stmts)
        | crate::tails::hoist_branch_labels(stmts)
        | crate::tails::enter_loops_by_flag(stmts, &mut || typer.new_local(TypeSig::Boolean))
    {
        moved = true;
    }
    if moved {
        let reads = Uses {
            slots: slot_reads(stmts),
            locals: typed_local_uses(typer, stmts),
            args_written: args_written(stmts),
            gotos: all_goto_counts(stmts),
        };
        simplify_block(typer, stmts, &reads);
        if forward_local_copies(typer, stmts) {
            rewrite_exprs(typer, stmts);
        }
    }
    rewrite_exprs(typer, stmts);
    free_iteration_variables(typer, stmts);
    drop_ref_unpins(typer, stmts);
    crate::fit::fit_types(typer, stmts);
    unshare_pattern_variables(typer, stmts);
}

/// `r = 0` on a pinned `ref` variable only lets go of what it pinned: C#
/// has no way to say it, and nothing to say.
fn drop_ref_unpins(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) {
    stmts.retain(|stmt| {
        !matches!(assignment(stmt), Some((Expr::Local(local), value))
            if is_unpin(value)
                && matches!(typer.type_of(&Expr::Local(*local)), Some(TypeSig::ByRef(_))))
    });
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            drop_ref_unpins(typer, block);
        }
    }
}

/// `foreach (var x in xs) { x = f(x); }` is not C#: the variable of a
/// `foreach`, or of a `using`, is read-only. One the body writes is given
/// its value from a fresh variable the statement declares instead.
fn free_iteration_variables(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    fn written(stmts: &[Stmt], local: u16) -> bool {
        let mut found = false;
        for stmt in stmts {
            stmt.walk_exprs(&mut |expr| match expr {
                Expr::Assign(target, _)
                | Expr::Compound(_, target, _)
                | Expr::Increment { target, .. }
                | Expr::Unary(UnOp::AddressOf, target) => {
                    found |= **target == Expr::Local(local);
                }
                _ => {}
            });
        }
        found
    }
    for stmt in stmts.iter_mut() {
        for block in stmt.blocks_mut() {
            free_iteration_variables(typer, block);
        }
        let (local, body) = match stmt {
            Stmt::ForEach { local, body, .. } => (local, body),
            Stmt::Using {
                local: Some(local),
                body,
                ..
            } => (local, body),
            _ => continue,
        };
        if !written(body, *local) {
            continue;
        }
        let Some(ty) = typer.type_of(&Expr::Local(*local)) else {
            continue;
        };
        let fresh = typer.new_local(ty);
        body.insert(
            0,
            Stmt::Expr(Expr::assign(Expr::Local(*local), Expr::Local(fresh))),
        );
        *local = fresh;
    }
}

/// `s is T x` declares `x`, so a local the compiler reused for several
/// patterns, or assigned besides, would be declared twice: its patterns on
/// reference types are written `(x = s as T) != null` instead, which is
/// what they do.
fn unshare_pattern_variables(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    let mut bindings: HashMap<u16, usize> = HashMap::new();
    let mut writes: HashMap<u16, usize> = HashMap::new();
    for stmt in stmts.iter() {
        stmt.walk_exprs(&mut |expr| match expr {
            Expr::IsPattern(_, _, target) => {
                if let Expr::Local(local) = target.as_ref() {
                    *bindings.entry(*local).or_default() += 1;
                }
            }
            Expr::Assign(target, _) => {
                if let Expr::Local(local) = target.as_ref() {
                    *writes.entry(*local).or_default() += 1;
                }
            }
            _ => {}
        });
    }
    let shared: HashSet<u16> = bindings
        .iter()
        .filter(|(local, count)| **count > 1 || writes.get(local).copied().unwrap_or(0) > 0)
        .map(|(local, _)| *local)
        .collect();
    if shared.is_empty() {
        return;
    }
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| {
            if let Expr::IsPattern(ty, source, target) = expr
                && let Expr::Local(local) = target.as_ref()
                && shared.contains(local)
                && !typer.ctx.resolver.is_value_type(ty)
                && !matches!(ty, TypeSig::Var(_) | TypeSig::MVar(_))
            {
                let assigned =
                    Expr::assign((**target).clone(), Expr::As(ty.clone(), source.clone()));
                *expr = Expr::compare(Cmp::Ne, assigned, Expr::Null);
            }
        });
    }
}

fn all_goto_counts(stmts: &[Stmt]) -> HashMap<u32, usize> {
    let mut counts = HashMap::new();
    goto_counts(stmts, &mut counts);
    counts
}

/// How many `goto`s jump to each label, over the whole body.
fn goto_counts(stmts: &[Stmt], counts: &mut HashMap<u32, usize>) {
    for stmt in stmts {
        if let Stmt::Goto(target) = stmt {
            *counts.entry(*target).or_default() += 1;
        }
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks() {
            goto_counts(block, counts);
        }
    }
}

/// Where a statement sits: the innermost statement `break` and `continue`
/// leave, and the protected regions around it.
#[derive(Clone, Debug, Default)]
struct Place {
    breakable: Option<usize>,
    looping: Option<usize>,
    /// Regions by id, and whether each is a `finally`.
    protected: Vec<(usize, bool)>,
    /// The statement lists around it, outermost first: the labels a `goto`
    /// here can see.
    lists: Vec<usize>,
}

/// A label only a `goto` reaches, and the statements under it up to the
/// next label: movable if they end the flow themselves.
#[derive(Debug)]
struct GotoTarget {
    label: u32,
    place: Place,
    segment: Vec<Stmt>,
    /// How many statements after the label the segment takes: one fewer
    /// than its length when it falls into the next label, which it then
    /// jumps to instead.
    taken: usize,
}

/// What a walk over a body finds about its jumps.
#[derive(Default)]
struct GotoSurvey {
    next_id: usize,
    /// How many `goto`s jump to each label.
    counts: HashMap<u32, usize>,
    targets: Vec<GotoTarget>,
    /// Where each `goto` is.
    gotos: HashMap<u32, Place>,
    /// The list each label is in.
    labels: HashMap<u32, usize>,
}

fn find_goto_sites(stmts: &[Stmt], place: &Place, survey: &mut GotoSurvey, successor: Option<u32>) {
    survey.next_id += 1;
    let mut place = place.clone();
    place.lists.push(survey.next_id);
    let place = &place;
    for (position, stmt) in stmts.iter().enumerate() {
        survey.next_id += 1;
        let id = survey.next_id;
        match stmt {
            Stmt::Goto(label) => {
                survey.gotos.insert(*label, place.clone());
            }
            Stmt::Label(label) => {
                survey
                    .labels
                    .insert(*label, place.lists.last().copied().unwrap_or(0));
            }
            _ => {}
        }
        match stmt {
            Stmt::Label(label)
                if position > 0
                    && stmts[position - 1].ends_flow()
                    && survey.counts.get(label) == Some(&1) =>
            {
                let end = stmts[position + 1..]
                    .iter()
                    .position(|stmt| matches!(stmt, Stmt::Label(_)))
                    .map_or(stmts.len(), |at| position + 1 + at);
                let segment = &stmts[position + 1..end];
                let ends = segment.last().is_some_and(Stmt::ends_flow);
                // A segment that falls into the next label jumps to it
                // from wherever it goes.
                let falls_into = match stmts.get(end) {
                    Some(Stmt::Label(next)) if !ends => Some(*next),
                    None if !ends => successor,
                    _ => None,
                };
                if !segment.is_empty()
                    && (ends || falls_into.is_some())
                    && !segment_jumps_to(segment, *label)
                    && is_movable(segment)
                {
                    let mut moved = segment.to_vec();
                    if let Some(next) = falls_into {
                        moved.push(Stmt::Goto(next));
                    }
                    survey.targets.push(GotoTarget {
                        label: *label,
                        place: place.clone(),
                        segment: moved,
                        taken: segment.len(),
                    });
                }
            }
            _ => {}
        }
        // Where the flow goes after this statement, when it is a label.
        let after = match stmts.get(position + 1) {
            Some(Stmt::Label(next)) => Some(*next),
            Some(_) => None,
            None => successor,
        };
        let mut inner = place.clone();
        match stmt {
            Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. } | Stmt::ForEach { .. } => {
                inner.breakable = Some(id);
                inner.looping = Some(id);
            }
            Stmt::Switch { .. } => inner.breakable = Some(id),
            _ => {}
        }
        match stmt {
            Stmt::Try {
                body,
                catches,
                finally,
            } => {
                let mut guarded = inner.clone();
                guarded.protected.push((id, false));
                find_goto_sites(body, &guarded, survey, None);
                for catch in catches {
                    find_goto_sites(&catch.body, &inner, survey, None);
                }
                if let Some(finally) = finally {
                    let mut last = inner.clone();
                    last.protected.push((id, true));
                    find_goto_sites(finally, &last, survey, None);
                }
            }
            Stmt::Using { body, .. }
            | Stmt::Lock { body, .. }
            | Stmt::ForEach { body, .. }
            | Stmt::Fixed { body, .. } => {
                let mut guarded = inner.clone();
                guarded.protected.push((id, false));
                find_goto_sites(body, &guarded, survey, None);
            }
            // A local function's body is another method.
            Stmt::LocalFunction { .. } => {}
            other => {
                // The branches of an `if` end where the `if` does.
                let ends_at = if matches!(other, Stmt::If { .. } | Stmt::Checked(_)) {
                    after
                } else {
                    None
                };
                for block in other.blocks() {
                    find_goto_sites(block, &inner, survey, ends_at);
                }
            }
        }
    }
}

/// The labels the statements jump to.
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

fn segment_jumps_to(stmts: &[Stmt], label: u32) -> bool {
    let mut jumps = Vec::new();
    jumps_in(stmts, &mut jumps);
    jumps.contains(&label)
}

/// Whether statements can be moved elsewhere in the body and mean the
/// same there: no labels to jump into, nothing declared for code around
/// them.
fn is_movable(stmts: &[Stmt]) -> bool {
    stmts.iter().all(|stmt| match stmt {
        Stmt::Label(_) | Stmt::LocalFunction { .. } | Stmt::EnterTry(_) => false,
        other => other.blocks().iter().all(|block| is_movable(block)),
    })
}

/// Whether the statements `break` (or `continue`) out of the statement
/// around them, rather than out of one of their own.
fn leaves_enclosing(stmts: &[Stmt], continues: bool) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Break => !continues,
        Stmt::Continue => continues,
        Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. } | Stmt::ForEach { .. } => {
            false
        }
        Stmt::Switch { cases, .. } => {
            continues && cases.iter().any(|case| leaves_enclosing(&case.body, true))
        }
        other => other
            .blocks()
            .iter()
            .any(|block| leaves_enclosing(block, continues)),
    })
}

/// `goto L; ... return x; L: A; return y;` where nothing falls into `L`
/// and only that one `goto` jumps there is `A; return y;` in place of the
/// `goto`: the compiler put the shared tail of a branch where it had room,
/// not where the source wrote it.
fn inline_goto_targets(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    for _ in 0..64 {
        let mut counts = HashMap::new();
        goto_counts(stmts, &mut counts);
        let mut survey = GotoSurvey {
            counts,
            ..GotoSurvey::default()
        };
        find_goto_sites(stmts, &Place::default(), &mut survey, None);
        let GotoSurvey {
            targets,
            gotos,
            labels,
            ..
        } = survey;
        let mut placed = HashMap::new();
        label_counts(stmts, &mut placed);
        let chosen = targets.into_iter().find(|target| {
            let Some(site) = gotos.get(&target.label) else {
                return false;
            };
            // A label written twice is not one place to move from.
            if placed.get(&target.label) != Some(&1) {
                return false;
            }
            if leaves_enclosing(&target.segment, false) && site.breakable != target.place.breakable
            {
                return false;
            }
            if leaves_enclosing(&target.segment, true) && site.looping != target.place.looping {
                return false;
            }
            // A `goto` moved along has to see its label from there.
            let mut jumps = Vec::new();
            jumps_in(&target.segment, &mut jumps);
            if jumps.iter().any(|jump| {
                labels
                    .get(jump)
                    .is_none_or(|list| !site.lists.contains(list))
            }) {
                return false;
            }
            // Regions entered or left by the move: a `throw` would be caught
            // where it was not, or not where it was; a `finally` cannot
            // return. A plain `return` is the same anywhere else.
            let crossed: Vec<&(usize, bool)> = site
                .protected
                .iter()
                .filter(|region| !target.place.protected.contains(region))
                .chain(
                    target
                        .place
                        .protected
                        .iter()
                        .filter(|region| !site.protected.contains(region)),
                )
                .collect();
            if crossed.is_empty() {
                return true;
            }
            let simple = matches!(target.segment.as_slice(), [Stmt::Return(None)])
                || matches!(target.segment.as_slice(), [Stmt::Return(Some(value))] if value.is_pure());
            simple && !crossed.iter().any(|(_, finally)| *finally)
        });
        let Some(target) = chosen else {
            // Nothing more moves: the jumps that still have somewhere to go
            // are turned into the `if`s and `else`s they were, and what
            // that frees up may move again.
            if tidy_gotos(stmts, true) {
                changed = true;
                continue;
            }
            break;
        };
        remove_labelled(stmts, target.label, target.taken);
        replace_goto(stmts, target.label, &target.segment);
        changed = true;
        tidy_gotos(stmts, false);
    }
    changed
}

/// Jumps to where the flow goes anyway disappear, `if (c) { A; goto L; } B;
/// L:` is `if (c) { A } else { B }`, and labels nothing jumps to go.
fn tidy_gotos(stmts: &mut Vec<Stmt>, restructure: bool) -> bool {
    let mut changed = false;
    loop {
        let mut round = tidy_gotos_in(stmts, restructure, None);
        round |= gotos_to_breaks(stmts);
        let mut counts = HashMap::new();
        goto_counts(stmts, &mut counts);
        round |= strip_unused_labels(stmts, &counts);
        if !round {
            break;
        }
        changed = true;
    }
    changed
}

fn strip_unused_labels(stmts: &mut Vec<Stmt>, counts: &HashMap<u32, usize>) -> bool {
    let before = stmts.len();
    stmts.retain(|stmt| !matches!(stmt, Stmt::Label(label) if !counts.contains_key(label)));
    let mut changed = stmts.len() != before;
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            changed |= strip_unused_labels(block, counts);
        }
    }
    changed
}

/// Removes a `goto` to the label from the end of a block that reaches it
/// by falling out: the block itself, or an `if` branch at its end.
fn drop_trailing_goto(block: &mut Vec<Stmt>, label: u32, restructure: bool) -> bool {
    // `if (c) goto L; A; return;` where running off the block reaches `L`
    // is `if (!c) { A; return; }`.
    let changed = false;
    if restructure
        && let Some(at) = block.iter().position(|stmt| {
            matches!(stmt, Stmt::If { then, otherwise, .. }
            if otherwise.is_empty() && then.as_slice() == [Stmt::Goto(label)])
        })
        && at + 1 < block.len()
        && block.last().is_some_and(Stmt::ends_flow)
        && !block[at + 1..]
            .iter()
            .any(|stmt| matches!(stmt, Stmt::Label(_)))
    {
        let rest: Vec<Stmt> = block.drain(at + 1..).collect();
        if let Some(Stmt::If {
            condition, then, ..
        }) = block.last_mut()
        {
            *condition = negate(condition.clone());
            *then = rest;
        }
        drop_trailing_goto(block, label, restructure);
        return true;
    }
    match block.last_mut() {
        Some(Stmt::Goto(target)) if *target == label => {
            block.pop();
            true
        }
        Some(Stmt::If {
            then, otherwise, ..
        }) => {
            let a = drop_trailing_goto(then, label, restructure);
            let b = drop_trailing_goto(otherwise, label, restructure);
            changed || a || b
        }
        _ => changed,
    }
}

/// `follow` is the label running off the end of the statements reaches,
/// when there is one.
fn tidy_gotos_in(stmts: &mut Vec<Stmt>, restructure: bool, follow: Option<u32>) -> bool {
    let mut changed = false;
    for position in 0..stmts.len() {
        // Running off an `if`'s branch goes on after the `if`.
        let after = match stmts.get(position + 1) {
            Some(Stmt::Label(label)) => Some(*label),
            None => follow,
            Some(_) => None,
        };
        let stmt = &mut stmts[position];
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        let inner = if matches!(stmt, Stmt::If { .. }) {
            after
        } else {
            None
        };
        for block in stmt.blocks_mut() {
            changed |= tidy_gotos_in(block, restructure, inner);
        }
    }
    if let Some(label) = follow {
        if stmts.last() == Some(&Stmt::Goto(label)) {
            stmts.pop();
            changed = true;
        } else if let Some(Stmt::If {
            then, otherwise, ..
        }) = stmts.last_mut()
        {
            changed |= drop_trailing_goto(then, label, restructure);
            changed |= drop_trailing_goto(otherwise, label, restructure);
        }
    }
    // `if (c) { A } else { L: }`: an else holding nothing but a label is
    // the end of the `if`, where the label can be reached from anywhere.
    let mut at = 0;
    while at < stmts.len() {
        if let Stmt::If { otherwise, .. } = &mut stmts[at]
            && let [Stmt::Label(label)] = otherwise.as_slice()
        {
            let label = *label;
            otherwise.clear();
            stmts.insert(at + 1, Stmt::Label(label));
            changed = true;
        }
        at += 1;
    }
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Stmt::Label(label) = stmts[index + 1] else {
            // `if (c) { A; goto L; } B; L:` with nothing jumping into `B`.
            // `if (c) { A; if (d) goto L; B; return; } C; L:` the same way:
            // the branch goes to `L` or out, so `C` is its `else`.
            let jumps_from_inside = |then: &[Stmt]| -> Option<u32> {
                if !then.last().is_some_and(Stmt::ends_flow) {
                    return None;
                }
                let mut jumps = Vec::new();
                jumps_in(then, &mut jumps);
                jumps.first().copied()
            };
            if let Stmt::If {
                then, otherwise, ..
            } = &stmts[index]
                && otherwise.is_empty()
                && let Some(label) = match then.last() {
                    Some(Stmt::Goto(label))
                        if !then[..then.len() - 1].iter().any(Stmt::ends_flow) =>
                    {
                        Some(*label)
                    }
                    _ if restructure => jumps_from_inside(then),
                    _ => None,
                }
                && let Some(end) = match stmts[index + 1..]
                    .iter()
                    .position(|stmt| matches!(stmt, Stmt::Label(_)))
                {
                    Some(offset) if stmts[index + 1 + offset] == Stmt::Label(label) => {
                        Some(index + 1 + offset)
                    }
                    // Or running off the end reaches it.
                    None if follow == Some(label) => Some(stmts.len()),
                    _ => None,
                }
                && end > index + 1
            {
                let rest: Vec<Stmt> = stmts.drain(index + 1..end).collect();
                if let Stmt::If {
                    then, otherwise, ..
                } = &mut stmts[index]
                {
                    drop_trailing_goto(then, label, restructure);
                    *otherwise = rest;
                }
                changed = true;
                continue;
            }
            index += 1;
            continue;
        };
        // The statement before the label reaches it anyway.
        if stmts[index] == Stmt::Goto(label) {
            stmts.remove(index);
            changed = true;
            continue;
        }
        if let Stmt::If {
            then, otherwise, ..
        } = &mut stmts[index]
        {
            let a = drop_trailing_goto(then, label, restructure);
            let b = drop_trailing_goto(otherwise, label, restructure);
            if a || b {
                changed = true;
                continue;
            }
        }
        index += 1;
    }
    changed
}

/// Whether a label is written somewhere inside a statement: a jump can
/// land there even when the statement itself is never reached.
fn has_label_inside(stmt: &Stmt) -> bool {
    !matches!(stmt, Stmt::LocalFunction { .. })
        && stmt.blocks().iter().any(|block| {
            block
                .iter()
                .any(|inner| matches!(inner, Stmt::Label(_)) || has_label_inside(inner))
        })
}

/// How many times each label is written.
fn label_counts(stmts: &[Stmt], counts: &mut HashMap<u32, usize>) {
    for stmt in stmts {
        if let Stmt::Label(label) = stmt {
            *counts.entry(*label).or_default() += 1;
        }
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks() {
            label_counts(block, counts);
        }
    }
}

/// Removes a label and the statements under it.
fn remove_labelled(stmts: &mut Vec<Stmt>, label: u32, count: usize) -> bool {
    if let Some(position) = stmts.iter().position(|stmt| *stmt == Stmt::Label(label)) {
        let end = (position + count + 1).min(stmts.len());
        stmts.drain(position..end);
        return true;
    }
    stmts.iter_mut().any(|stmt| {
        !matches!(stmt, Stmt::LocalFunction { .. })
            && stmt
                .blocks_mut()
                .into_iter()
                .any(|block| remove_labelled(block, label, count))
    })
}

/// Puts the statements where the `goto` to the label is.
fn replace_goto(stmts: &mut Vec<Stmt>, label: u32, segment: &[Stmt]) -> bool {
    if let Some(position) = stmts.iter().position(|stmt| *stmt == Stmt::Goto(label)) {
        stmts.splice(position..=position, segment.iter().cloned());
        return true;
    }
    stmts.iter_mut().any(|stmt| {
        !matches!(stmt, Stmt::LocalFunction { .. })
            && stmt
                .blocks_mut()
                .into_iter()
                .any(|block| replace_goto(block, label, segment))
    })
}

/// The parameters a body assigns or takes the address of.
fn args_written(stmts: &[Stmt]) -> HashSet<u16> {
    let mut written = HashSet::new();
    for stmt in stmts {
        stmt.walk_exprs(&mut |e| match e {
            Expr::Assign(target, _)
            | Expr::Compound(_, target, _)
            | Expr::Increment { target, .. } => {
                if let Expr::Arg(at) = target.as_ref() {
                    written.insert(*at);
                }
                if let Expr::Tuple(items) = target.as_ref() {
                    for item in items {
                        if let Expr::Arg(at) = item {
                            written.insert(*at);
                        }
                    }
                }
            }
            Expr::Unary(UnOp::AddressOf, inner) => {
                if let Expr::Arg(at) = inner.as_ref() {
                    written.insert(*at);
                }
            }
            _ => {}
        });
    }
    written
}

/// How the variables of a body are used, counted over the whole body.
#[derive(Debug, Default)]
pub struct Uses {
    /// Reads of each slot.
    slots: HashMap<u32, usize>,
    /// `(writes, reads, address taken)` of each local.
    locals: HashMap<u16, (usize, usize, bool)>,
    /// The parameters that are assigned or passed by reference.
    args_written: HashSet<u16>,
    /// How many `goto`s jump to each label.
    gotos: HashMap<u32, usize>,
}

impl Uses {
    /// Whether a local is written once and read once, and never by address,
    /// so that its one value can be put where it is read.
    fn local_is_single(&self, local: u16) -> bool {
        matches!(self.locals.get(&local), Some((1, 1, false)))
    }
}

/// The uses of every local, a `ref` local counted as one whose address is
/// taken: a store to it is a store through it, never a dead one, and it
/// is not a copy to fold away.
fn typed_local_uses(typer: &Typer<'_, '_>, stmts: &[Stmt]) -> HashMap<u16, (usize, usize, bool)> {
    let mut uses = local_uses(stmts);
    for (local, entry) in &mut uses {
        if matches!(typer.type_of(&Expr::Local(*local)), Some(TypeSig::ByRef(_))) {
            entry.2 = true;
        }
    }
    // A struct whose fields are written is changed in place, as good as its
    // address taken: `s = default; s.X = 1; use(s)` is no constant.
    let mut roots = HashSet::new();
    for stmt in stmts {
        stmt.walk_exprs(&mut |e| {
            if let Expr::Assign(target, _)
            | Expr::Compound(_, target, _)
            | Expr::Increment { target, .. } = e
                && let Some(root) = struct_root(target)
            {
                roots.insert(root);
            }
            // So does a method called on it.
            if let Expr::Call {
                receiver: Some(receiver),
                method,
                ..
            } = e
                && method.sig.instance
                && let Some(root) = struct_root_of(receiver)
            {
                roots.insert(root);
            }
        });
    }
    for root in roots {
        if typer
            .type_of(&Expr::Local(root))
            .is_some_and(|ty| typer.ctx.resolver.is_value_type(&ty))
        {
            uses.entry(root).or_default().2 = true;
        }
    }
    uses
}

/// The local a field of which, however deep, is the place written: a
/// struct changed in place, as good as its address taken.
fn struct_root(place: &Expr) -> Option<u16> {
    match place {
        Expr::Field {
            receiver: Some(receiver),
            ..
        }
        // A property's setter changes the struct it is called on.
        | Expr::Property {
            receiver: Some(receiver),
            ..
        } => match receiver.as_ref() {
            Expr::Local(at) => Some(*at),
            Expr::Unary(UnOp::AddressOf, inner) => struct_root_of(inner),
            other => struct_root(other),
        },
        _ => None,
    }
}
fn struct_root_of(place: &Expr) -> Option<u16> {
    match place {
        Expr::Local(at) => Some(*at),
        other => struct_root(other),
    }
}

/// Counts the writes and reads of every local.
fn local_uses(stmts: &[Stmt]) -> HashMap<u16, (usize, usize, bool)> {
    let mut uses: HashMap<u16, (usize, usize, bool)> = HashMap::new();
    fn count_expr(expr: &Expr, uses: &mut HashMap<u16, (usize, usize, bool)>) {
        match expr {
            Expr::Assign(target, value) => {
                match target.as_ref() {
                    Expr::Local(at) => uses.entry(*at).or_default().0 += 1,
                    // `(a, b) = (b, a)` writes each.
                    Expr::Tuple(items) => {
                        for item in items {
                            match item {
                                Expr::Local(at) => uses.entry(*at).or_default().0 += 1,
                                other => count_expr(other, uses),
                            }
                        }
                    }
                    other => count_expr(other, uses),
                }
                count_expr(value, uses);
            }
            Expr::Compound(_, target, _) | Expr::Increment { target, .. }
                if matches!(target.as_ref(), Expr::Local(_)) =>
            {
                if let Expr::Local(at) = target.as_ref() {
                    let entry = uses.entry(*at).or_default();
                    entry.0 += 1;
                    entry.1 += 1;
                }
                if let Expr::Compound(_, _, value) = expr {
                    count_expr(value, uses);
                }
            }
            Expr::Unary(UnOp::AddressOf, inner) if matches!(inner.as_ref(), Expr::Local(_)) => {
                if let Expr::Local(at) = inner.as_ref() {
                    let entry = uses.entry(*at).or_default();
                    entry.1 += 1;
                    entry.2 = true;
                }
            }
            Expr::IsPattern(_, inner, target) => {
                if let Expr::Local(at) = target.as_ref() {
                    uses.entry(*at).or_default().0 += 1;
                }
                count_expr(inner, uses);
            }
            Expr::Local(at) => uses.entry(*at).or_default().1 += 1,
            Expr::Lambda { params, body, .. } => {
                // Whatever a lambda touches is captured: shared with code
                // that runs later, so never a single use.
                let mut inner: HashMap<u16, (usize, usize, bool)> = HashMap::new();
                for param in params {
                    inner.entry(*param).or_default().0 += 1;
                }
                match body.as_ref() {
                    Body::Expr(expr) => count_expr(expr, &mut inner),
                    Body::Block(stmts) => {
                        for stmt in stmts {
                            count_stmt(stmt, &mut inner);
                        }
                    }
                }
                for (local, (writes, reads, address)) in inner {
                    let entry = uses.entry(local).or_default();
                    entry.0 += writes + 1;
                    entry.1 += reads + 1;
                    entry.2 |= address;
                }
            }
            other => {
                let mut children: Vec<&Expr> = Vec::new();
                collect_children(other, &mut children);
                for child in children {
                    count_expr(child, uses);
                }
            }
        }
    }
    fn count_stmt(stmt: &Stmt, uses: &mut HashMap<u16, (usize, usize, bool)>) {
        match stmt {
            Stmt::ForEach { local, .. }
            | Stmt::Fixed { local, .. }
            | Stmt::Using {
                local: Some(local), ..
            } => {
                uses.entry(*local).or_default().0 += 1;
            }
            Stmt::Try { catches, .. } => {
                for catch in catches {
                    if let Some(variable) = catch.variable {
                        uses.entry(variable).or_default().0 += 1;
                    }
                }
            }
            _ => {}
        }
        for expr in head_exprs(stmt) {
            count_expr(expr, uses);
        }
        if let Stmt::For {
            initializer,
            condition,
            step,
            ..
        } = stmt
        {
            if let Some(initializer) = initializer {
                count_stmt(initializer, uses);
            }
            count_expr(condition, uses);
            if let Some(step) = step {
                count_expr(step, uses);
            }
        }
        if let Stmt::While { condition, .. } | Stmt::DoWhile { condition, .. } = stmt {
            count_expr(condition, uses);
        }
        if let Stmt::Switch { cases, .. } = stmt {
            for case in cases {
                for label in case.labels.iter().flatten() {
                    count_expr(label, uses);
                }
            }
        }
        if let Stmt::Try { catches, .. } = stmt {
            for catch in catches {
                if let Some(filter) = &catch.filter {
                    count_expr(filter, uses);
                }
            }
        }
        for block in stmt.blocks() {
            for inner in block {
                count_stmt(inner, uses);
            }
        }
    }
    for stmt in stmts {
        count_stmt(stmt, &mut uses);
    }
    uses
}

/// The direct sub-expressions of an expression.
fn collect_children<'e>(expr: &'e Expr, out: &mut Vec<&'e Expr>) {
    match expr {
        Expr::Unary(_, inner)
        | Expr::Cast(_, inner)
        | Expr::CheckedCast(_, inner)
        | Expr::OperatorCast(_, inner)
        | Expr::As(_, inner)
        | Expr::Is(_, inner)
        | Expr::Box(_, inner)
        | Expr::Length(inner)
        | Expr::Checked(inner)
        | Expr::MaybeNull(inner)
        | Expr::StackAlloc(_, inner)
        | Expr::Await(inner) => out.push(inner),
        Expr::IsPattern(_, inner, target) => {
            out.push(inner);
            out.push(target);
        }
        Expr::Binary(_, left, right)
        | Expr::Assign(left, right)
        | Expr::Compound(_, left, right)
        | Expr::Compare { left, right, .. } => {
            out.push(left);
            out.push(right);
        }
        Expr::Increment { target, .. } => out.push(target),
        Expr::Call { receiver, args, .. } => {
            out.extend(receiver.iter().map(|r| r.as_ref()));
            out.extend(args.iter());
        }
        Expr::New {
            args, initializer, ..
        } => {
            out.extend(args.iter());
            out.extend(initializer.iter().map(|(_, value)| value));
        }
        Expr::With {
            source,
            initializer,
        } => {
            out.push(source);
            out.extend(initializer.iter().map(|(_, value)| value));
        }
        Expr::NewArray { size, items, .. } => {
            out.push(size);
            if let Some(items) = items {
                out.extend(items.iter());
            }
        }
        Expr::Field { receiver, .. } | Expr::Property { receiver, .. } => {
            out.extend(receiver.iter().map(|r| r.as_ref()));
        }
        Expr::Index { array, indices } => {
            out.push(array);
            out.extend(indices.iter());
        }
        Expr::Indexer { receiver, args } => {
            out.push(receiver);
            out.extend(args.iter());
        }
        Expr::Conditional(a, b, c) => {
            out.push(a);
            out.push(b);
            out.push(c);
        }
        Expr::Delegate { target, .. } => out.extend(target.iter().map(|t| t.as_ref())),
        Expr::Tuple(items) => out.extend(items.iter()),
        Expr::Interpolated(parts) => {
            for part in parts {
                if let Interpolation::Hole(hole, _) = part {
                    out.push(hole);
                }
            }
        }
        _ => {}
    }
}

/// Visits the expressions a statement evaluates itself: not the ones in
/// the statements nested inside it.
fn own_exprs<'s>(stmt: &'s Stmt, visit: &mut dyn FnMut(&'s Expr)) {
    for expr in head_exprs(stmt) {
        visit(expr);
    }
    match stmt {
        Stmt::For {
            initializer,
            condition,
            step,
            ..
        } => {
            if let Some(initializer) = initializer {
                own_exprs(initializer, visit);
            }
            visit(condition);
            if let Some(step) = step {
                visit(step);
            }
        }
        Stmt::While { condition, .. } | Stmt::DoWhile { condition, .. } => visit(condition),
        Stmt::Switch { cases, .. } => {
            for case in cases {
                for label in case.labels.iter().flatten() {
                    visit(label);
                }
            }
        }
        Stmt::Try { catches, .. } => {
            for catch in catches {
                if let Some(filter) = &catch.filter {
                    visit(filter);
                }
            }
        }
        _ => {}
    }
}

/// How often each slot is read anywhere in the statements.
fn slot_reads(stmts: &[Stmt]) -> HashMap<u32, usize> {
    let mut reads: HashMap<u32, usize> = HashMap::new();
    fn count(expr: &Expr, reads: &mut HashMap<u32, usize>) {
        expr.walk(&mut |e| {
            if let Some(id) = slot_of(e) {
                *reads.entry(id).or_default() += 1;
            }
        });
    }
    fn scan(stmts: &[Stmt], reads: &mut HashMap<u32, usize>) {
        for stmt in stmts {
            if let Some((target, value)) = assignment(stmt)
                && slot_of(target).is_some()
            {
                count(value, reads);
                continue;
            }
            own_exprs(stmt, &mut |e| {
                // A filter still holding its block is scanned as statements.
                if let Expr::Lambda { body, .. } = e
                    && let Body::Block(inner) = body.as_ref()
                {
                    scan(inner, reads);
                } else {
                    count(e, reads);
                }
            });
            for block in stmt.blocks() {
                scan(block, reads);
            }
        }
    }
    scan(stmts, &mut reads);
    reads
}

/// Statement-level rewrites, innermost lists first.
fn simplify_block(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>, reads: &Uses) {
    for stmt in stmts.iter_mut() {
        for block in stmt.blocks_mut() {
            simplify_block(typer, block, reads);
        }
        if let Stmt::Try { catches, .. } = stmt {
            for catch in catches {
                fold_filter(typer, catch);
            }
        }
    }
    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 20 {
        rounds += 1;
        changed = false;
        changed |= remove_dead_code(stmts);
        changed |= unwrap_single_pass_loops(stmts);
        changed |= hoist_loop_head_labels(stmts);
        changed |= fold_array_initializers(stmts);
        changed |= fold_object_initializers(typer, stmts);
        changed |= fold_constrained_copies(stmts);
        changed |= fold_ternaries(typer, stmts);
        changed |= fold_parallel_ternaries(stmts);
        changed |= inline_place_refs(typer, stmts);
        changed |= inline_span_temps(typer, stmts);
        changed |= fold_increments(stmts, reads);
        changed |= fold_assignment_expressions(stmts, reads);
        changed |= hoist_invoked_lambdas(typer, stmts);
        changed |= inline_slots(typer, stmts, reads);
        changed |= push_returns_into_branches(stmts);
        changed |= bind_is_patterns(typer, stmts);
        changed |= fold_is_patterns(typer, stmts);
        changed |= fold_string_handlers(typer.ctx.resolver, stmts);
        changed |= shape_loops(typer, stmts);
        changed |= fold_awaited_finally(stmts);
        changed |= fold_pending_returns(stmts);
        changed |= fold_foreach(typer, stmts);
        changed |= fold_using_and_lock(stmts);
        changed |= fold_fixed(typer, stmts);
        changed |= fold_fixed_buffer_elements(stmts);
        changed |= fold_do_while_flags(stmts, reads);
        changed |= fold_bool_returns(typer, stmts);
        changed |= fold_ref_compounds(typer, stmts, reads);
        changed |= fold_tuple_assignments(stmts, reads);
        changed |= crate::switches::fold_string_switches(stmts);
        changed |= crate::int_switches::fold_int_switches(
            typer.ctx.resolver,
            &|e| typer.type_of(e),
            &reads.gotos,
            stmts,
        );
        changed |= crate::int_switches::fold_default_tails(stmts);
        changed |= merge_nested_ifs(stmts);
        changed |= fold_null_conditional_statements(stmts);
        changed |= fold_coalesce_assignment_temps(stmts, reads);
        changed |= fold_null_conditional_returns(stmts);
        changed |= drop_else_after_exit(stmts);
        changed |= fold_compound(stmts);
        changed |= fold_return_locals(stmts);
        changed |= merge_try_finally(stmts);
    }
}

/// Whether an expression pins nothing more: `(nuint)0`, `0`, `null`.
fn is_unpin(value: &Expr) -> bool {
    match value {
        Expr::Int(0) | Expr::Long(0) | Expr::Null => true,
        Expr::Cast(_, inner) => is_unpin(inner),
        _ => false,
    }
}

/// `(nuint)q`: the pinned variable's address as a pointer.
fn is_pinned_address(expr: &Expr, pinned: u16) -> bool {
    matches!(expr, Expr::Cast(TypeSig::UIntPtr | TypeSig::IntPtr | TypeSig::Pointer(_), inner)
        if **inner == Expr::Local(pinned))
}

/// The null-or-empty check `fixed` does on an array: the pinned copy of
/// the array if there is one, the pointer, the array, and how many
/// statements that took.
fn array_pin(
    typer: &Typer<'_, '_>,
    stmts: &[Stmt],
    index: usize,
) -> Option<(Option<u16>, u16, Expr, usize)> {
    let (copy, check_at) = match assignment(&stmts[index]) {
        Some((Expr::Local(q), source))
            if matches!(typer.type_of(&Expr::Local(*q)), Some(TypeSig::Vector(_))) =>
        {
            (Some((*q, source.clone())), index + 1)
        }
        _ => (None, index),
    };
    let Stmt::If {
        condition,
        then,
        otherwise,
    } = stmts.get(check_at)?
    else {
        return None;
    };
    // The copy may have been folded into the check:
    // `(a2 = a) == null || a2.Length == 0`.
    let mut folded_copy = None;
    condition.walk(&mut |expr| {
        if let Expr::Assign(target, value) = expr
            && let Expr::Local(q) = target.as_ref()
            && folded_copy.is_none()
        {
            let mut value = value.as_ref();
            while let Expr::Assign(_, inner) = value {
                value = inner.as_ref();
            }
            folded_copy = Some((*q, value.clone()));
        }
    });
    let copy = copy.or(folded_copy.filter(|_| check_at == index));
    let [Stmt::Expr(Expr::Assign(p_then, zero))] = then.as_slice() else {
        return None;
    };
    let [Stmt::Expr(Expr::Assign(p_else, address))] = otherwise.as_slice() else {
        return None;
    };
    if p_then != p_else || !is_unpin(zero) {
        return None;
    }
    let Expr::Local(p) = p_then.as_ref() else {
        return None;
    };
    let Expr::Cast(_, inner) = address.as_ref() else {
        return None;
    };
    let Expr::Unary(UnOp::AddressOf, element) = inner.as_ref() else {
        return None;
    };
    let Expr::Index { array, indices } = element.as_ref() else {
        return None;
    };
    if indices.as_slice() != [Expr::Int(0)] {
        return None;
    }
    match copy {
        Some((q, source)) if **array == Expr::Local(q) => {
            Some((Some(q), *p, source, check_at - index + 1))
        }
        None if array.is_pure() && matches!(typer.type_of(array), Some(TypeSig::Vector(_))) => {
            Some((None, *p, (**array).clone(), 1))
        }
        _ => None,
    }
}

/// `ref buffer.FixedElementField + i * 4`, the address of an element of a
/// `fixed` buffer, is `buffer[i]`.
fn fold_fixed_buffer_elements(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| {
            let Expr::Binary(BinOp::Add, base, offset) = expr else {
                return;
            };
            let Expr::Unary(UnOp::AddressOf, first) = base.as_ref() else {
                return;
            };
            let Expr::Field {
                receiver: Some(buffer),
                field,
            } = first.as_ref()
            else {
                return;
            };
            if field.name != "FixedElementField" {
                return;
            }
            let Some(index) = crate::stack::unscale(offset, &field.ty) else {
                return;
            };
            let buffer = match buffer.as_ref() {
                Expr::Unary(UnOp::AddressOf, inner) => (**inner).clone(),
                other => other.clone(),
            };
            // An address is the place it is of, the way IL uses it.
            *expr = Expr::Index {
                array: Box::new(buffer),
                indices: vec![index],
            };
            changed = true;
        });
    }
    changed
}

/// A `fixed` statement: a pinned variable set, its address taken as a
/// pointer, and the variable cleared again where the block ends.
fn fold_fixed(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        // `if (s == null) { t = 0; } else { q = s.GetPinnableReference(); t = (nuint)q; }`
        // is how `fixed (char* p = s)` checks for null: the pin is the else.
        if let Stmt::If {
            condition: Expr::Compare {
                op: Cmp::Eq, right, ..
            },
            then,
            otherwise,
        } = &stmts[index]
            && **right == Expr::Null
            && matches!(then.as_slice(), [Stmt::Expr(Expr::Assign(_, zero))] if is_unpin(zero))
            && let [
                Stmt::Expr(Expr::Assign(pinned, pin)),
                Stmt::Expr(Expr::Assign(target, address)),
            ] = otherwise.as_slice()
            && let Expr::Local(q) = pinned.as_ref()
            && matches!(pin.as_ref(), Expr::Call { method, .. } if method.name == "GetPinnableReference")
            && is_pinned_address(address, *q)
            && let [Stmt::Expr(Expr::Assign(zero_target, _))] = then.as_slice()
            && zero_target == target
        {
            let replacement = otherwise.clone();
            stmts.splice(index..=index, replacement);
            changed = true;
            // The copy of the address folds away before the pin is read.
            index += 2;
            continue;
        }
        // `p = (a == null || a.Length == 0) ? null : &a[0]`, with `a` first
        // copied into a pinned array variable or not: `fixed (T* p = a)`.
        if let Some((q, p, source, start)) = array_pin(typer, stmts, index) {
            let from = index + start;
            let end = q.and_then(|q| {
                stmts[from..]
                    .iter()
                    .position(|stmt| matches!(assignment(stmt), Some((Expr::Local(at), value)) if *at == q && is_unpin(value)))
                    .map(|at| from + at)
            });
            let body: Vec<Stmt> = match end {
                Some(end) => {
                    let body = stmts[from..end].to_vec();
                    stmts.drain(index + 1..=end);
                    body
                }
                None => stmts.drain(index + 1..).skip(start - 1).collect(),
            };
            stmts[index] = Stmt::Fixed {
                local: p,
                init: source,
                body,
            };
            changed = true;
            index += 1;
            continue;
        }
        // `ref T q = ref x;` whose address is then used as a pointer.
        let Some((Expr::Local(q), value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let q = *q;
        let Some(TypeSig::ByRef(element)) = typer.type_of(&Expr::Local(q)) else {
            index += 1;
            continue;
        };
        let init = match value {
            Expr::Unary(UnOp::AddressOf, inner) => match inner.as_ref() {
                // A fixed buffer is pinned through its first element.
                Expr::Field {
                    receiver: Some(buffer),
                    field,
                } if field.name == "FixedElementField" => (**buffer).clone(),
                _ => value.clone(),
            },
            Expr::Call {
                method,
                receiver: Some(receiver),
                args,
            } if method.name == "GetPinnableReference" && args.is_empty() => (**receiver).clone(),
            // `fixed (T* p = &MemoryMarshal.GetReference(span))`: the
            // reference a call returns.
            Expr::Call { method, .. } if matches!(method.sig.returns, TypeSig::ByRef(_)) => {
                Expr::Unary(UnOp::AddressOf, Box::new(value.clone()))
            }
            // `fixed (T* p = &x)` of a `ref` or `out` parameter.
            Expr::Arg(_) | Expr::Local(_)
                if matches!(typer.type_of(value), Some(TypeSig::ByRef(_))) =>
            {
                Expr::Unary(UnOp::AddressOf, Box::new(value.clone()))
            }
            _ => {
                index += 1;
                continue;
            }
        };
        let end = stmts[index + 1..]
            .iter()
            .position(|stmt| {
                matches!(assignment(stmt), Some((Expr::Local(at), value)) if *at == q && is_unpin(value))
            })
            .map(|at| index + 1 + at);
        let body_range = index + 1..end.unwrap_or(stmts.len());
        let is_address = |e: &Expr| is_pinned_address(e, q);
        let addresses: usize = stmts[body_range.clone()]
            .iter()
            .map(|stmt| count_in_stmt_deep(stmt, &is_address))
            .sum();
        let other_reads: usize = stmts[body_range.clone()]
            .iter()
            .map(|stmt| count_in_stmt_deep(stmt, &|e| *e == Expr::Local(q)))
            .sum();
        if addresses == 0 || other_reads != addresses {
            index += 1;
            continue;
        }
        // `q = s.GetPinnableReference(); t = (nuint)q;` ending a branch:
        // the null check of a `fixed` around it, folded from outside.
        if end.is_none()
            && body_range.len() == 1
            && matches!(assignment(&stmts[index + 1]), Some((target, address))
                if is_address(address)
                    && !matches!(typer.type_of(target), Some(TypeSig::Pointer(_))))
        {
            index += 1;
            continue;
        }
        let mut body: Vec<Stmt> = stmts[body_range.clone()].to_vec();
        // The pointer the source declared, when the compiler kept it.
        let pointer = match body.first().and_then(assignment) {
            Some((Expr::Local(p), address))
                if is_address(address)
                    && matches!(typer.type_of(&Expr::Local(*p)), Some(TypeSig::Pointer(_))) =>
            {
                let p = *p;
                body.remove(0);
                p
            }
            _ => typer.new_local(TypeSig::Pointer(element.clone())),
        };
        let pointee = match typer.type_of(&Expr::Local(pointer)) {
            Some(TypeSig::Pointer(inner)) => *inner,
            _ => (*element).clone(),
        };
        for stmt in &mut body {
            // Arithmetic on the address was in bytes; on the pointer it is
            // in elements.
            stmt.map_exprs(&mut |e| {
                if let Expr::Binary(op @ (BinOp::Add | BinOp::Sub), left, right) = e
                    && is_address(left)
                {
                    let offset =
                        crate::stack::unscale(right, &pointee).unwrap_or_else(|| (**right).clone());
                    *e = Expr::binary(*op, Expr::Local(pointer), offset);
                }
            });
            stmt.map_exprs(&mut |e| {
                if is_address(e) {
                    *e = Expr::Local(pointer);
                }
            });
        }
        let stop = end.map_or(stmts.len(), |end| end + 1);
        stmts.drain(index + 1..stop);
        stmts[index] = Stmt::Fixed {
            local: pointer,
            init,
            body,
        };
        changed = true;
        index += 1;
    }
    changed
}

/// `t1 = b; t2 = a + b; b = t2; a = t1;` is `(a, b) = (b, a + b);`: the
/// temporaries a tuple assignment keeps its values in until all are
/// computed.
fn fold_tuple_assignments(stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let is_temp = |e: &Expr| match e {
            Expr::Local(local) => uses.local_is_single(*local),
            Expr::Slot(slot) => uses.slots.get(slot) == Some(&1),
            _ => false,
        };
        // The temporaries, in the order their values are computed.
        let mut temps: Vec<(Expr, Expr)> = Vec::new();
        let mut at = index;
        while let Some((target, value)) = stmts.get(at).and_then(assignment)
            && is_temp(target)
            && !temps.iter().any(|(t, _)| value.count(&|e| e == t) > 0)
        {
            temps.push((target.clone(), value.clone()));
            at += 1;
        }
        if temps.len() < 2 {
            index += 1;
            continue;
        }
        // Then one store of each into its place.
        let mut places: Vec<Option<Expr>> = vec![None; temps.len()];
        let mut stored = 0;
        while stored < temps.len()
            && let Some((place, Some(which))) = stmts
                .get(at + stored)
                .and_then(assignment)
                .map(|(place, value)| (place, temps.iter().position(|(t, _)| t == value)))
            && places[which].is_none()
            && place.is_place()
            && place.is_pure()
        {
            places[which] = Some(place.clone());
            stored += 1;
        }
        if stored != temps.len() {
            index += 1;
            continue;
        }
        let places: Vec<Expr> = places.into_iter().flatten().collect();
        // Only a swap needs the tuple: some value reads a place stored
        // before it would be.
        let reads_a_place = temps
            .iter()
            .any(|(_, value)| places.iter().any(|place| value.count(&|e| e == place) > 0));
        if !reads_a_place {
            index += 1;
            continue;
        }
        let values: Vec<Expr> = temps.into_iter().map(|(_, value)| value).collect();
        stmts.drain(index..at + stored);
        stmts.insert(
            index,
            Stmt::Expr(Expr::assign(Expr::Tuple(places), Expr::Tuple(values))),
        );
        changed = true;
        index += 1;
    }
    changed
}

/// `ref int r = ref a[i]; r = r & x;` is `a[i] &= x;`: the reference the
/// compiler took to evaluate the place once.
fn fold_ref_compounds(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Some((variable @ (Expr::Local(_) | Expr::Slot(_)), bound)) = assignment(&stmts[index])
        else {
            index += 1;
            continue;
        };
        let variable = variable.clone();
        let used_once = match &variable {
            Expr::Local(r) => matches!(uses.locals.get(r), Some((2, 1, _))),
            Expr::Slot(slot) => uses.slots.get(slot) == Some(&1),
            _ => false,
        };
        if !matches!(typer.type_of(&variable), Some(TypeSig::ByRef(_))) || !used_once {
            index += 1;
            continue;
        }
        let place = match bound {
            Expr::Unary(UnOp::AddressOf, inner) => (**inner).clone(),
            other if other.is_place() => other.clone(),
            // `At(i) += x`: a method returning a reference is a place.
            call @ Expr::Call { .. } if matches!(typer.type_of(call), Some(TypeSig::ByRef(_))) => {
                call.clone()
            }
            _ => {
                index += 1;
                continue;
            }
        };
        let Some((target, Expr::Binary(op, left, right))) = assignment(&stmts[index + 1]) else {
            index += 1;
            continue;
        };
        if *target != variable
            || **left != variable
            || right.count(&|e| *e == variable) > 0
            || matches!(op, BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::Coalesce)
        {
            index += 1;
            continue;
        }
        stmts[index] = Stmt::Expr(Expr::Compound(*op, Box::new(place), right.clone()));
        stmts.remove(index + 1);
        changed = true;
        index += 1;
    }
    changed
}

/// A `goto` to the label right after a loop, from the loop's own body, is
/// `break`.
fn gotos_to_breaks(stmts: &mut [Stmt]) -> bool {
    fn replace(stmts: &mut [Stmt], label: u32) -> bool {
        let mut changed = false;
        for stmt in stmts.iter_mut() {
            match stmt {
                Stmt::Goto(target) if *target == label => {
                    *stmt = Stmt::Break;
                    changed = true;
                }
                // `break` in these leaves them, not the loop.
                Stmt::While { .. }
                | Stmt::DoWhile { .. }
                | Stmt::For { .. }
                | Stmt::ForEach { .. }
                | Stmt::Switch { .. }
                | Stmt::LocalFunction { .. } => {}
                // A `finally` cannot be left by a jump at all.
                Stmt::Try { body, catches, .. } => {
                    changed |= replace(body, label);
                    for catch in catches {
                        changed |= replace(&mut catch.body, label);
                    }
                }
                other => {
                    for block in other.blocks_mut() {
                        changed |= replace(block, label);
                    }
                }
            }
        }
        changed
    }
    /// A jump to the end of a loop's body is `continue`, from inside a
    /// `switch` too.
    fn continues(stmts: &mut [Stmt], label: u32) -> bool {
        let mut changed = false;
        for stmt in stmts.iter_mut() {
            match stmt {
                Stmt::Goto(target) if *target == label => {
                    *stmt = Stmt::Continue;
                    changed = true;
                }
                Stmt::While { .. }
                | Stmt::DoWhile { .. }
                | Stmt::For { .. }
                | Stmt::ForEach { .. }
                | Stmt::LocalFunction { .. } => {}
                Stmt::Try { body, catches, .. } => {
                    changed |= continues(body, label);
                    for catch in catches {
                        changed |= continues(&mut catch.body, label);
                    }
                }
                other => {
                    for block in other.blocks_mut() {
                        changed |= continues(block, label);
                    }
                }
            }
        }
        changed
    }
    let mut changed = false;
    for index in 0..stmts.len() {
        if let Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForEach { body, .. } = &mut stmts[index]
            && let Some(Stmt::Label(label)) = body.last()
        {
            let label = *label;
            let at = body.len() - 1;
            changed |= continues(&mut body[..at], label);
        }
        if let Some(Stmt::Label(label)) = stmts.get(index + 1) {
            let label = *label;
            if let Stmt::While { body, .. }
            | Stmt::DoWhile { body, .. }
            | Stmt::For { body, .. }
            | Stmt::ForEach { body, .. } = &mut stmts[index]
            {
                changed |= replace(body, label);
            }
            if let Stmt::Switch { cases, .. } = &mut stmts[index] {
                for case in cases {
                    changed |= replace(&mut case.body, label);
                }
            }
        }
        for block in stmts[index].blocks_mut() {
            changed |= gotos_to_breaks(block);
        }
    }
    changed
}

/// `L: if (c) { A; goto L; }` is `while (c) { A }`, when `A` has no `break`
/// or `continue` that the loop would take for its own.
fn fold_goto_loops(stmts: &mut Vec<Stmt>) -> bool {
    let mut counts = HashMap::new();
    goto_counts(stmts, &mut counts);
    fold_goto_loops_in(stmts, &counts)
}

fn fold_goto_loops_in(stmts: &mut Vec<Stmt>, counts: &HashMap<u32, usize>) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            changed |= fold_goto_loops_in(block, counts);
        }
    }
    changed |= rotate_entered_loops(stmts, counts);
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Stmt::Label(label) = stmts[index] else {
            index += 1;
            continue;
        };
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = &stmts[index + 1]
        else {
            index += 1;
            continue;
        };
        if !otherwise.is_empty()
            || then.last() != Some(&Stmt::Goto(label))
            || counts.get(&label) != Some(&1)
        {
            index += 1;
            continue;
        }
        let body = &then[..then.len() - 1];
        if leaves_enclosing(body, false) || leaves_enclosing(body, true) {
            index += 1;
            continue;
        }
        let looped = Stmt::While {
            condition: condition.clone(),
            body: body.to_vec(),
        };
        stmts[index + 1] = looped;
        stmts.remove(index);
        changed = true;
    }
    changed
}

/// `goto L; do { A; L: B; } while (c);` enters the loop halfway: it is
/// `while (true) { B; if (!c) break; A; }`, the test of a `while` whose
/// condition needed statements of its own.
fn rotate_entered_loops(stmts: &mut Vec<Stmt>, counts: &HashMap<u32, usize>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let (Stmt::Goto(label), Stmt::DoWhile { body, condition }) =
            (&stmts[index], &stmts[index + 1])
        else {
            index += 1;
            continue;
        };
        let label = *label;
        let Some(at) = body.iter().position(|stmt| *stmt == Stmt::Label(label)) else {
            index += 1;
            continue;
        };
        if counts.get(&label) != Some(&1) || leaves_enclosing(body, true) {
            index += 1;
            continue;
        }
        let mut rotated: Vec<Stmt> = body[at + 1..].to_vec();
        if *condition != Expr::Bool(true) {
            rotated.push(Stmt::If {
                condition: crate::stack::negate(condition.clone()),
                then: vec![Stmt::Break],
                otherwise: Vec::new(),
            });
        }
        rotated.extend_from_slice(&body[..at]);
        stmts[index + 1] = Stmt::While {
            condition: Expr::Bool(true),
            body: rotated,
        };
        stmts.remove(index);
        changed = true;
    }
    changed
}

/// `if (c) return x; return false;` is `return c && x;`, and the other
/// three ways round: returns of `bool`s one of which is a constant.
fn fold_bool_returns(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let (
            Stmt::If {
                condition,
                then,
                otherwise,
            },
            Stmt::Return(Some(b)),
        ) = (&stmts[index], &stmts[index + 1])
        else {
            index += 1;
            continue;
        };
        let [Stmt::Return(Some(a))] = then.as_slice() else {
            index += 1;
            continue;
        };
        let constant = |e: &Expr| matches!(e, Expr::Bool(_));
        if !otherwise.is_empty()
            || !(constant(a) || constant(b))
            || !typer.is_bool(a)
            || !typer.is_bool(b)
            || !b.is_pure() && !constant(b)
        {
            index += 1;
            continue;
        }
        let folded = make_conditional(typer, condition.clone(), a.clone(), b.clone());
        if matches!(folded, Expr::Conditional(..)) {
            index += 1;
            continue;
        }
        stmts[index] = Stmt::Return(Some(folded));
        stmts.remove(index + 1);
        changed = true;
    }
    changed
}

/// `do { ...; flag = c; } while (flag);` is `do { ... } while (c);` when
/// the flag is only that.
fn fold_do_while_flags(stmts: &mut [Stmt], uses: &Uses) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        let Stmt::DoWhile { body, condition } = stmt else {
            continue;
        };
        let Expr::Local(flag) = condition else {
            continue;
        };
        let flag = *flag;
        if !uses.local_is_single(flag) {
            continue;
        }
        if let Some((Expr::Local(at), value)) = body.last().and_then(assignment)
            && *at == flag
        {
            let value = value.clone();
            body.pop();
            *condition = value;
            changed = true;
        }
    }
    changed
}

/// Whether statements are the rethrow of an exception kept for later:
/// `if (e != null) { if (!(e is Exception x)) throw e;
/// ExceptionDispatchInfo.Capture(x).Throw(); }`.
fn is_deferred_rethrow(stmt: &Stmt, stash: &Expr) -> bool {
    let Stmt::If {
        condition, then, ..
    } = stmt
    else {
        return false;
    };
    let tested = matches!(condition, Expr::Compare { op: Cmp::Ne, left, right, .. }
        if **left == *stash && **right == Expr::Null);
    let mut captures = false;
    for inner in then {
        inner.walk_exprs(&mut |e| {
            if let Expr::Call { method, .. } = e
                && method.name == "Capture"
            {
                captures = true;
            }
        });
    }
    tested && captures
}

/// `try { A } catch (object e) { s = e; } B; if (s != null) rethrow(s);` is
/// how a `finally` that awaits is compiled: `try { A } finally { B }`.
fn fold_awaited_finally(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let Stmt::Try {
            catches,
            finally: None,
            ..
        } = &stmts[index]
        else {
            index += 1;
            continue;
        };
        let [catch] = catches.as_slice() else {
            index += 1;
            continue;
        };
        let object = catch.ty.as_ref().is_none_or(|ty| *ty == TypeSig::Object);
        let Some(variable) = catch.variable else {
            index += 1;
            continue;
        };
        let stash = match catch.body.as_slice() {
            [Stmt::Expr(Expr::Assign(target, value))]
                if **value == Expr::Local(variable)
                    && matches!(target.as_ref(), Expr::Local(_)) =>
            {
                (**target).clone()
            }
            _ => {
                index += 1;
                continue;
            }
        };
        if !object || catch.filter.is_some() {
            index += 1;
            continue;
        }
        // The finally's statements, then the stash copied back (maybe)
        // and rethrown.
        let Some(rethrow_at) = stmts[index + 1..].iter().position(|stmt| {
            is_deferred_rethrow(stmt, &stash) || is_deferred_rethrow(stmt, &Expr::Local(variable))
        }) else {
            index += 1;
            continue;
        };
        let rethrow_at = index + 1 + rethrow_at;
        let mut end = rethrow_at;
        if let Some((Expr::Local(copy), value)) = assignment(&stmts[rethrow_at - 1])
            && *value == stash
            && *copy == variable
            && rethrow_at - 1 > index
        {
            end = rethrow_at - 1;
        }
        let finally: Vec<Stmt> = stmts[index + 1..end].to_vec();
        let mentions_stash = |stmt: &Stmt| count_in_stmt_deep(stmt, &|e| *e == stash) > 0;
        if finally.iter().any(mentions_stash)
            || finally.iter().any(|stmt| matches!(stmt, Stmt::Label(_)))
        {
            index += 1;
            continue;
        }
        stmts.drain(index + 1..=rethrow_at);
        if let Stmt::Try {
            catches,
            finally: slot,
            ..
        } = &mut stmts[index]
        {
            catches.clear();
            *slot = Some(finally);
        }
        changed = true;
        index += 1;
    }
    changed
}

/// `try { try { A } catch { B } } finally { C }` is one statement in C#.
fn merge_try_finally(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        let Stmt::Try {
            body,
            catches,
            finally: Some(_),
        } = stmt
        else {
            continue;
        };
        if !catches.is_empty() {
            continue;
        }
        let Some(Stmt::Try {
            body: inner_body,
            catches: inner_catches,
            finally: None,
        }) = single(body)
        else {
            continue;
        };
        let (inner_body, inner_catches) = (inner_body.clone(), inner_catches.clone());
        *body = inner_body;
        *catches = inner_catches;
        changed = true;
    }
    changed
}

/// `t = default(T); r = &x; if (t == null) { t = x; r = &t; } r.M()` is
/// how `x.M()` on a type parameter compiles, a reference type's value being
/// copied first: it is `x.M()`.
fn fold_constrained_copies(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 3 < stmts.len() {
        let matched = (|| {
            let (Expr::Local(copy), Expr::Default(_)) = assignment(&stmts[index])? else {
                return None;
            };
            let (reference, Expr::Unary(UnOp::AddressOf, place)) = assignment(&stmts[index + 1])?
            else {
                return None;
            };
            let Stmt::If {
                condition:
                    Expr::Compare {
                        op: Cmp::Eq,
                        left,
                        right,
                        ..
                    },
                then,
                otherwise,
            } = &stmts[index + 2]
            else {
                return None;
            };
            let copied = Expr::Local(*copy);
            let [first, second] = then.as_slice() else {
                return None;
            };
            let (Some((a, a_value)), Some((b, b_value))) = (assignment(first), assignment(second))
            else {
                return None;
            };
            (**left == copied
                && **right == Expr::Null
                && otherwise.is_empty()
                && *a == copied
                && a_value == place.as_ref()
                && b == reference
                && *b_value == Expr::Unary(UnOp::AddressOf, Box::new(copied.clone())))
            .then(|| (*copy, reference.clone(), (**place).clone()))
        })();
        let Some((copy, reference, place)) = matched else {
            index += 1;
            continue;
        };
        // The copy and the reference are the pattern's own.
        let rest = &stmts[index + 3..];
        let copy_used = rest
            .iter()
            .any(|stmt| count_in_stmt_deep(stmt, &|e| *e == Expr::Local(copy)) > 0);
        if copy_used {
            index += 1;
            continue;
        }
        stmts.drain(index..index + 3);
        for stmt in &mut stmts[index..] {
            stmt.map_exprs(&mut |e| {
                if *e == reference {
                    *e = place.clone();
                }
            });
        }
        changed = true;
    }
    changed
}

/// `x = e; return x;` is `return e;`, and `x = e; throw x;` is `throw e;`.
fn fold_return_locals(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 1;
    while index < stmts.len() {
        let Some((variable @ (Expr::Local(_) | Expr::Slot(_)), value)) =
            assignment(&stmts[index - 1])
        else {
            index += 1;
            continue;
        };
        // A lambda that reads the variable sees the value stored: without
        // the store it would see the one before.
        if value
            .count(&|e| matches!(e, Expr::Lambda { .. }) && e.count(&|inner| inner == variable) > 0)
            > 0
        {
            index += 1;
            continue;
        }
        let (variable, value) = (variable.clone(), value.clone());
        let replacement = match &stmts[index] {
            Stmt::Return(Some(read)) if *read == variable => Stmt::Return(Some(value)),
            Stmt::Throw(Some(read)) if *read == variable => Stmt::Throw(Some(value)),
            _ => {
                index += 1;
                continue;
            }
        };
        stmts[index] = replacement;
        stmts.remove(index - 1);
        changed = true;
    }
    changed
}

/// Statements after one that never falls through are unreachable, up to the
/// next label anything still jumps to.
/// `while (true) { L: A }` is `L: while (true) { A }`: the start of the
/// body is where the loop is entered, and a label outside it is in sight of
/// more jumps. So for `do`.
fn hoist_loop_head_labels(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let head = match &mut stmts[index] {
            Stmt::While {
                condition: Expr::Bool(true),
                body,
            }
            | Stmt::DoWhile { body, .. } => match body.first() {
                Some(Stmt::Label(label)) => {
                    let label = *label;
                    body.remove(0);
                    Some(label)
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(label) = head {
            changed = true;
            // The same label may be there already.
            if index == 0 || stmts[index - 1] != Stmt::Label(label) {
                stmts.insert(index, Stmt::Label(label));
                index += 1;
            }
        }
        index += 1;
    }
    changed
}

/// `f = 0; try { A; v = x; f = 1; } finally { F } if (f == 1) return v;`
/// is how a `return` inside a `try` whose `finally` awaits is put off until
/// the `finally` has run: it is `try { A; return x; } finally { F }`.
fn fold_pending_returns(stmts: &mut Vec<Stmt>) -> bool {
    let mut index = 0;
    while index + 2 < stmts.len() {
        let Some((Expr::Local(flag), Expr::Int(0))) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let flag = *flag;
        let Some(try_at) = (index + 1..stmts.len()).take(3).find(|at| {
            matches!(
                stmts[*at],
                Stmt::Try {
                    finally: Some(_),
                    ..
                }
            )
        }) else {
            index += 1;
            continue;
        };
        let Some(Stmt::If {
            condition:
                Expr::Compare {
                    op: Cmp::Eq,
                    left,
                    right,
                    ..
                },
            then,
            otherwise,
        }) = stmts.get(try_at + 1)
        else {
            index += 1;
            continue;
        };
        let (Expr::Local(checked), Expr::Int(pending)) = (left.as_ref(), right.as_ref()) else {
            index += 1;
            continue;
        };
        let [Stmt::Return(Some(Expr::Local(value)))] = then.as_slice() else {
            index += 1;
            continue;
        };
        if *checked != flag || !otherwise.is_empty() {
            index += 1;
            continue;
        }
        let (pending, value) = (*pending, *value);
        // The flag and the value are the lowering's alone.
        let uses = |local: u16| -> usize {
            stmts
                .iter()
                .map(|stmt| count_in_stmt_deep(stmt, &|e| *e == Expr::Local(local)))
                .sum()
        };
        let Stmt::Try { body, .. } = &stmts[try_at] else {
            unreachable!()
        };
        let mut pairs = 0;
        count_pending_pairs(body, flag, value, pending, &mut pairs);
        if pairs == 0 || uses(flag) != pairs + 2 || uses(value) != pairs + 1 {
            index += 1;
            continue;
        }
        if let Stmt::Try { body, .. } = &mut stmts[try_at] {
            replace_pending_pairs(body, flag, value, pending);
        }
        stmts.remove(try_at + 1);
        stmts.remove(index);
        return true;
    }
    false
}

/// The `v = x; f = k;` pairs ending the lists that end a `try` body.
fn count_pending_pairs(stmts: &[Stmt], flag: u16, value: u16, pending: i64, pairs: &mut usize) {
    if let [
        ..,
        Stmt::Expr(Expr::Assign(v, _)),
        Stmt::Expr(Expr::Assign(f, k)),
    ] = stmts
        && **v == Expr::Local(value)
        && **f == Expr::Local(flag)
        && **k == Expr::Int(pending)
    {
        *pairs += 1;
    }
    if let Some(Stmt::If {
        then, otherwise, ..
    }) = stmts.last()
    {
        count_pending_pairs(then, flag, value, pending, pairs);
        count_pending_pairs(otherwise, flag, value, pending, pairs);
    }
}

fn replace_pending_pairs(stmts: &mut Vec<Stmt>, flag: u16, value: u16, pending: i64) {
    if let [
        ..,
        Stmt::Expr(Expr::Assign(v, _)),
        Stmt::Expr(Expr::Assign(f, k)),
    ] = stmts.as_slice()
        && **v == Expr::Local(value)
        && **f == Expr::Local(flag)
        && **k == Expr::Int(pending)
    {
        stmts.pop();
        if let Some(Stmt::Expr(Expr::Assign(_, returned))) = stmts.pop() {
            stmts.push(Stmt::Return(Some(*returned)));
        }
        return;
    }
    if let Some(Stmt::If {
        then, otherwise, ..
    }) = stmts.last_mut()
    {
        replace_pending_pairs(then, flag, value, pending);
        replace_pending_pairs(otherwise, flag, value, pending);
    }
}

/// `ref T r = ref this.f; ...; r.M(x)`: IL takes the field's address
/// before working out the arguments. The field of `this`, or a static one,
/// is at the same place whenever it is taken, so a reference used once is
/// the field itself: `this.f.M(x)`, which an async method can hold.
fn inline_place_refs(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    fn fixed_place(expr: &Expr) -> bool {
        match expr {
            Expr::Field { receiver: None, .. } => true,
            Expr::Field {
                receiver: Some(receiver),
                ..
            } => match receiver.as_ref() {
                Expr::This => true,
                Expr::Unary(UnOp::AddressOf, inner) => fixed_place(inner),
                other => fixed_place(other),
            },
            _ => false,
        }
    }
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Some((variable, Expr::Unary(UnOp::AddressOf, place))) = assignment(&stmts[index])
        else {
            index += 1;
            continue;
        };
        if !matches!(variable, Expr::Local(_) | Expr::Slot(_))
            || !fixed_place(place)
            || !matches!(typer.type_of(variable), Some(TypeSig::ByRef(_)))
        {
            index += 1;
            continue;
        }
        let (variable, place) = (variable.clone(), (**place).clone());
        let is_variable = |e: &Expr| *e == variable;
        let uses: Vec<usize> = stmts
            .iter()
            .map(|stmt| count_in_stmt_deep(stmt, &is_variable))
            .collect();
        let total: usize = uses.iter().sum();
        // Its assignment and one read, in a later statement of this list.
        let Some(read_at) = (index + 1..stmts.len()).find(|at| uses[*at] > 0) else {
            index += 1;
            continue;
        };
        if total != 2 || uses[read_at] != 1 {
            index += 1;
            continue;
        }
        // Only as what a member is reached on: a reference made a pointer,
        // or passed on, is not the field's value.
        let mut as_receiver = false;
        stmts[read_at].walk_exprs(&mut |e| {
            let receiver = match e {
                Expr::Call {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Property {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Field {
                    receiver: Some(receiver),
                    ..
                } => receiver.as_ref(),
                _ => return,
            };
            as_receiver |= *receiver == variable
                || matches!(receiver, Expr::Unary(UnOp::AddressOf, inner) if **inner == variable);
        });
        if !as_receiver {
            index += 1;
            continue;
        }
        stmts[read_at].map_exprs(&mut |e| {
            if *e == variable {
                *e = place.clone();
            }
        });
        stmts.remove(index);
        changed = true;
    }
    changed
}

/// `s = Preface; Write(s.Length)`: a span the compiler parked in a local to
/// call on it, read once as the first thing the next statement does, is
/// the value itself; an async method may not hold a span at all.
fn inline_span_temps(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let span_like = |ty: &TypeSig| {
        matches!(ty, TypeSig::Generic { definition, .. }
            if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                if matches!(typer.ctx.resolver.raw_name(*token).as_deref(),
                    Some("System.Span`1" | "System.ReadOnlySpan`1"))))
    };
    let main_expr = |stmt: &Stmt| -> Option<Expr> {
        match stmt {
            Stmt::Expr(e) | Stmt::Return(Some(e)) => Some(e.clone()),
            Stmt::If { condition, .. } => Some(condition.clone()),
            _ => None,
        }
    };
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Some((Expr::Local(local), value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let local = *local;
        if !typer
            .type_of(&Expr::Local(local))
            .is_some_and(|ty| span_like(&ty))
            || !value.is_pure()
                && !matches!(
                    value,
                    Expr::Property { .. } | Expr::Call { .. } | Expr::StackAlloc(..)
                )
        {
            index += 1;
            continue;
        }
        let value = value.clone();
        let is_local = |e: &Expr| *e == Expr::Local(local);
        // Read once, in the next statement, before anything else there.
        let next = &stmts[index + 1];
        if count_in_stmt_deep(next, &is_local) != 1 {
            index += 1;
            continue;
        }
        let Some(main) = main_expr(next) else {
            index += 1;
            continue;
        };
        if count_in_stmt(next, &is_local) != 1 {
            index += 1;
            continue;
        }
        let mut order = Vec::new();
        evaluation_order(&main, &mut order);
        let first_is_local = order.first().is_some_and(|first| {
            is_local(first)
                || matches!(first, Expr::Unary(UnOp::AddressOf, inner) if is_local(inner))
        });
        // As what a member is reached on, not as a `ref` argument.
        let mut as_receiver = false;
        main.walk(&mut |e| {
            let receiver = match e {
                Expr::Call {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Property {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Indexer { receiver, .. } => receiver.as_ref(),
                _ => return,
            };
            as_receiver |= is_local(receiver)
                || matches!(receiver, Expr::Unary(UnOp::AddressOf, inner) if is_local(inner));
        });
        // Or copied as it is: `s2 = s`, where a `stackalloc` straight into
        // `s2` may live as long as the method, a local's only its block.
        let copied = matches!(assignment(next), Some((_, Expr::Local(from))) if *from == local)
            && matches!(value, Expr::StackAlloc(..));
        if !copied && (!first_is_local || !as_receiver) {
            index += 1;
            continue;
        }
        // Not read again before it is set anew.
        let mut read_later = false;
        for stmt in &stmts[index + 2..] {
            if let Some((Expr::Local(at), value)) = assignment(stmt)
                && *at == local
            {
                read_later = value.count(&is_local) > 0;
                break;
            }
            if count_in_stmt_deep(stmt, &is_local) > 0 {
                read_later = true;
                break;
            }
        }
        if read_later {
            index += 1;
            continue;
        }
        stmts[index + 1].map_exprs(&mut |e| {
            if let Expr::Unary(UnOp::AddressOf, inner) = e
                && **inner == value
            {
                *e = value.clone();
            } else if is_local(e) {
                *e = value.clone();
            }
        });
        stmts.remove(index);
        changed = true;
    }
    changed
}

/// `if (c) { s1 = a; s2 = b; } else { s1 = a; s2 = d; }`, the stack carrying
/// two values out of a conditional, is `s1 = a; s2 = c ? b : d;`, when
/// nothing in it has an effect to repeat.
fn fold_parallel_ternaries(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        index += 1;
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = &stmts[index - 1]
        else {
            continue;
        };
        if then.len() < 2 || then.len() != otherwise.len() || !condition.is_pure() {
            continue;
        }
        let pairs: Option<Vec<(Expr, Expr, Expr)>> = then
            .iter()
            .zip(otherwise.iter())
            .map(|(a, b)| match (assignment(a), assignment(b)) {
                (Some((ta, va)), Some((tb, vb)))
                    if ta == tb
                        && matches!(ta, Expr::Slot(_))
                        && va.is_pure()
                        && vb.is_pure()
                        // A reference has no conditional to be.
                        && (va == vb
                            || !matches!(va, Expr::Unary(UnOp::AddressOf, _))
                                && !matches!(vb, Expr::Unary(UnOp::AddressOf, _))) =>
                {
                    Some((ta.clone(), va.clone(), vb.clone()))
                }
                _ => None,
            })
            .collect();
        let Some(pairs) = pairs else {
            continue;
        };
        // A value may not read a slot set before it here.
        let targets: Vec<&Expr> = pairs.iter().map(|(t, _, _)| t).collect();
        if pairs.iter().any(|(_, a, b)| {
            targets
                .iter()
                .any(|t| a.count(&|e| e == *t) > 0 || b.count(&|e| e == *t) > 0)
        }) {
            continue;
        }
        let condition = condition.clone();
        let assignments: Vec<Stmt> = pairs
            .into_iter()
            .map(|(target, a, b)| {
                let value = if a == b {
                    a
                } else {
                    Expr::Conditional(Box::new(condition.clone()), Box::new(a), Box::new(b))
                };
                Stmt::Expr(Expr::assign(target, value))
            })
            .collect();
        let count = assignments.len();
        stmts.splice(index - 1..index, assignments);
        index += count - 1;
        changed = true;
    }
    changed
}

/// `while (true) { A; return; }`, a loop whose body always leaves it by
/// a jump, never goes round: it is its body.
fn unwrap_single_pass_loops(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        if let Stmt::While {
            condition: Expr::Bool(true),
            body,
        } = &stmts[index]
            && body.last().is_some_and(Stmt::ends_flow)
            && !crate::ir::breaks_out_of(body)
            && !crate::ir::continues_in(body)
        {
            let Stmt::While { body, .. } = stmts.remove(index) else {
                unreachable!()
            };
            let count = body.len();
            stmts.splice(index..index, body);
            index += count;
            changed = true;
            continue;
        }
        index += 1;
    }
    changed
}

fn remove_dead_code(stmts: &mut Vec<Stmt>) -> bool {
    // A value computed and dropped that has nothing to it: a constant, a
    // variable.
    let before = stmts.len();
    stmts.retain(|stmt| {
        !matches!(stmt, Stmt::Expr(value)
        if value.is_constant()
            || matches!(
                value,
                Expr::Local(_)
                    | Expr::Arg(_)
                    | Expr::Slot(_)
                    | Expr::This
                    | Expr::Default(_)
                    | Expr::TypeOf(_)
                    | Expr::SizeOf(_)
            ))
    });
    let mut changed = stmts.len() != before;
    let mut index = 0;
    while index < stmts.len() {
        if stmts[index].ends_flow() {
            let mut end = index + 1;
            while end < stmts.len()
                && !matches!(stmts[end], Stmt::Label(_) | Stmt::LocalFunction { .. })
                && !has_label_inside(&stmts[end])
            {
                end += 1;
            }
            if end > index + 1 {
                stmts.drain(index + 1..end);
                changed = true;
            }
        }
        index += 1;
    }
    changed
}

fn slot_of(expr: &Expr) -> Option<u32> {
    match expr {
        Expr::Slot(id) => Some(*id),
        _ => None,
    }
}

fn assignment(stmt: &Stmt) -> Option<(&Expr, &Expr)> {
    match stmt {
        Stmt::Expr(Expr::Assign(target, value)) => Some((target, value)),
        _ => None,
    }
}

/// `t = new T[n]; t[0] = a; t[1] = b;` becomes `t = new T[] { a, b }`.
fn fold_array_initializers(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let Some((target, value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let (
            Some(slot),
            Expr::NewArray {
                size,
                items,
                element,
            },
        ) = (slot_of(target), value)
        else {
            index += 1;
            continue;
        };
        let Expr::Int(count) = **size else {
            index += 1;
            continue;
        };
        // Stores after an initializer go on filling it, from past the last
        // item it gave that is not a default.
        let existing = items.clone();
        if existing
            .as_ref()
            .is_some_and(|items| items.len() as i64 != count)
        {
            index += 1;
            continue;
        }
        let given = existing.as_ref().map_or(0, |items| {
            let default = default_of(element);
            items
                .iter()
                .rposition(|item| *item != default)
                .map_or(0, |at| at as i64 + 1)
        });
        let mut stores: Vec<(i64, Expr)> = Vec::new();
        let mut at = index + 1;
        while at < stmts.len() {
            let Some((place, item)) = assignment(&stmts[at]) else {
                break;
            };
            let Expr::Index { array, indices } = place else {
                break;
            };
            if slot_of(array) != Some(slot) || indices.len() != 1 {
                break;
            }
            let Expr::Int(position) = indices[0] else {
                break;
            };
            if stores.last().is_some_and(|(last, _)| *last >= position)
                || position < given
                || item.count(&|e| slot_of(e) == Some(slot)) > 0
            {
                break;
            }
            stores.push((position, item.clone()));
            at += 1;
        }
        if stores.is_empty() || !(0..=1024).contains(&count) {
            index += 1;
            continue;
        }
        let mut filled: Vec<Expr> = Vec::with_capacity(count as usize);
        let Some((_, value)) = assignment(&stmts[index]) else {
            unreachable!()
        };
        let Expr::NewArray { element, .. } = value else {
            unreachable!()
        };
        let element = element.clone();
        for position in 0..count {
            match stores.iter().find(|(p, _)| *p == position) {
                Some((_, item)) => filled.push(item.clone()),
                None => filled.push(existing.as_ref().map_or_else(
                    || default_of(&element),
                    |items| items[position as usize].clone(),
                )),
            }
        }
        stmts.drain(index + 1..at);
        if let Some((_, value)) = assignment_mut(&mut stmts[index])
            && let Expr::NewArray { items, .. } = value
        {
            *items = Some(filled);
        }
        changed = true;
        index += 1;
    }
    changed
}

fn assignment_mut(stmt: &mut Stmt) -> Option<(&mut Expr, &mut Expr)> {
    match stmt {
        Stmt::Expr(Expr::Assign(target, value)) => Some((target, value)),
        _ => None,
    }
}

fn default_of(ty: &TypeSig) -> Expr {
    match ty {
        TypeSig::String | TypeSig::Object | TypeSig::Class(_) | TypeSig::Vector(_) => Expr::Null,
        TypeSig::Boolean => Expr::Bool(false),
        TypeSig::Int32
        | TypeSig::Int16
        | TypeSig::Byte
        | TypeSig::SByte
        | TypeSig::UInt16
        | TypeSig::UInt32 => Expr::Int(0),
        TypeSig::Int64 | TypeSig::UInt64 => Expr::Long(0),
        TypeSig::Double => Expr::Float(0.0, false),
        TypeSig::Single => Expr::Float(0.0, true),
        TypeSig::Char => Expr::Char(0),
        _ => Expr::Default(ty.clone()),
    }
}

/// `t = new C(); t.A = 1; t.B = 2;` becomes `t = new C { A = 1, B = 2 }`.
fn fold_object_initializers(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let Some((target, value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        // The stores into a closure's display class are the variables it
        // captures, for the closure pass to take apart.
        if let Expr::New { ctor, .. } = value
            && crate::closures::display_row(typer.ctx.resolver, &ctor.declaring).is_some()
        {
            index += 1;
            continue;
        }
        let is_clone = matches!(value, Expr::Call { method, receiver: Some(_), args }
            if method.name == "<Clone>$" && args.is_empty());
        let (Some(slot), Expr::New { .. } | Expr::Call { .. }) = (slot_of(target), value) else {
            index += 1;
            continue;
        };
        if matches!(value, Expr::Call { .. }) && !is_clone {
            index += 1;
            continue;
        }
        let mut members: Vec<(String, Expr)> = Vec::new();
        let mut at = index + 1;
        while at < stmts.len() {
            // `t.Add(x)` right after the construction is a collection
            // initializer element.
            if let Stmt::Expr(Expr::Call {
                method,
                receiver: Some(receiver),
                args,
            }) = &stmts[at]
                && method.name == "Add"
                && slot_of(receiver) == Some(slot)
                && !args.is_empty()
                && args
                    .iter()
                    .all(|arg| arg.count(&|e| slot_of(e) == Some(slot)) == 0)
            {
                let element = if args.len() == 1 {
                    args[0].clone()
                } else {
                    Expr::Tuple(args.clone())
                };
                members.push((String::new(), element));
                at += 1;
                continue;
            }
            let Some((place, item)) = assignment(&stmts[at]) else {
                break;
            };
            // `t[k] = v` is `[k] = v`.
            if !is_clone
                && let Expr::Indexer {
                    receiver,
                    args: keys,
                } = place
                && slot_of(receiver) == Some(slot)
                && !keys.is_empty()
            {
                if item.count(&|e| slot_of(e) == Some(slot)) > 0
                    || keys
                        .iter()
                        .any(|key| key.count(&|e| slot_of(e) == Some(slot)) > 0)
                {
                    break;
                }
                let mut parts = keys.clone();
                parts.push(item.clone());
                members.push(("[]".to_string(), Expr::Tuple(parts)));
                at += 1;
                continue;
            }
            let name = match place {
                Expr::Field {
                    receiver: Some(receiver),
                    field,
                } if slot_of(receiver) == Some(slot) => field.name.clone(),
                Expr::Property {
                    receiver: Some(receiver),
                    name,
                    ..
                } if slot_of(receiver) == Some(slot) => name.clone(),
                _ => break,
            };
            if item.count(&|e| slot_of(e) == Some(slot)) > 0 {
                break;
            }
            members.push((name, item.clone()));
            at += 1;
        }
        if members.is_empty() {
            index += 1;
            continue;
        }
        stmts.drain(index + 1..at);
        if let Some((_, value)) = assignment_mut(&mut stmts[index]) {
            match value {
                Expr::New { initializer, .. } => initializer.extend(members),
                Expr::Call {
                    receiver: Some(receiver),
                    ..
                } => {
                    *value = Expr::With {
                        source: receiver.clone(),
                        initializer: members,
                    };
                }
                _ => {}
            }
        }
        changed = true;
        index += 1;
    }
    changed
}

/// `if (c) { s = a; } else { s = b; }` becomes `s = c ? a : b`, and so does
/// `s = b; if (c) { s = a; }`.
fn fold_ternaries(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 1;
    while index < stmts.len() {
        let Some((target, before)) = assignment(&stmts[index - 1]) else {
            index += 1;
            continue;
        };
        let (Some(_), before) = (slot_of(target), before.clone()) else {
            index += 1;
            continue;
        };
        let target = target.clone();
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = &stmts[index]
        else {
            index += 1;
            continue;
        };
        if !otherwise.is_empty() {
            index += 1;
            continue;
        }
        let Some(Stmt::Expr(Expr::Assign(a_target, a_value))) = single(then) else {
            index += 1;
            continue;
        };
        if **a_target != target
            || condition.count(&|e| *e == target) > 0
            || !condition.is_pure()
            || matches!(a_value.as_ref(), Expr::Unary(UnOp::AddressOf, _))
            || matches!(before, Expr::Unary(UnOp::AddressOf, _))
        {
            index += 1;
            continue;
        }
        let ternary = make_conditional(typer, condition.clone(), (**a_value).clone(), before);
        stmts[index - 1] = Stmt::Expr(Expr::assign(target, ternary));
        stmts.remove(index);
        changed = true;
    }
    for stmt in stmts.iter_mut() {
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = stmt
        else {
            continue;
        };
        let (
            Some(Stmt::Expr(Expr::Assign(a_target, a_value))),
            Some(Stmt::Expr(Expr::Assign(b_target, b_value))),
        ) = (single(then), single(otherwise))
        else {
            continue;
        };
        // A local too where a branch is a `stackalloc`: only as one
        // expression may the span it makes outlive the branch.
        let stackalloc = matches!(a_value.as_ref(), Expr::StackAlloc(..))
            || matches!(b_value.as_ref(), Expr::StackAlloc(..));
        // A reference has no conditional to be.
        if matches!(a_value.as_ref(), Expr::Unary(UnOp::AddressOf, _))
            || matches!(b_value.as_ref(), Expr::Unary(UnOp::AddressOf, _))
        {
            continue;
        }
        if a_target != b_target || (slot_of(a_target).is_none() && !stackalloc) {
            continue;
        }
        let ternary = make_conditional(
            typer,
            condition.clone(),
            (**a_value).clone(),
            (**b_value).clone(),
        );
        *stmt = Stmt::Expr(Expr::assign((**a_target).clone(), ternary));
        changed = true;
    }
    changed
}

/// The one statement of a block. A label makes a block more than its
/// statement: something jumps there, and would lose its place.
fn single(stmts: &[Stmt]) -> Option<&Stmt> {
    match stmts {
        [only] if !matches!(only, Stmt::Label(_)) => Some(only),
        _ => None,
    }
}

/// `c ? a : b` with the shortcuts C# has for it: `c ? true : b` is
/// `c || b`, `c ? x : null` on a reference is not `??` but `c ? 1 : 0` in a
/// condition is just `c`.
fn make_conditional(typer: &Typer<'_, '_>, condition: Expr, a: Expr, b: Expr) -> Expr {
    // A constant branch takes the type of the other: `c ? x : '?'` where
    // `x` is a `char`, not `c ? x : 63`.
    // A `null` beside a struct is a `T?` taken apart, not that struct's
    // default: it stays, and is printed `(T?)null`.
    let struct_null = |constant: &Expr, other: &TypeSig| {
        *constant == Expr::Null
            && typer.ctx.resolver.is_value_type(other)
            && !typer.ctx.resolver.is_nullable(other)
    };
    let (a, b) = match (a.is_constant(), b.is_constant()) {
        (true, false) => match typer.type_of(&b) {
            Some(ty) if struct_null(&a, &ty) => (a, b),
            Some(ty) if !matches!(ty, TypeSig::Int32) => {
                (coerce_expr(typer.ctx.resolver, a, &ty), b)
            }
            _ => (a, b),
        },
        (false, true) => match typer.type_of(&a) {
            Some(ty) if struct_null(&b, &ty) => (a, b),
            Some(ty) if !matches!(ty, TypeSig::Int32) => {
                let b = coerce_expr(typer.ctx.resolver, b, &ty);
                (a, b)
            }
            _ => (a, b),
        },
        _ => (a, b),
    };
    // `c ? 1 : 0` is a number, `c ? true : false` is `c`: what is a
    // `bool` has had its constants made `true` and `false` already.
    let truthy = |e: &Expr| matches!(e, Expr::Bool(true));
    let falsy = |e: &Expr| matches!(e, Expr::Bool(false));
    let boolish = |e: &Expr| {
        matches!(
            e,
            Expr::Bool(_) | Expr::Compare { .. } | Expr::Is(..) | Expr::Unary(UnOp::Not, _)
        ) || matches!(e, Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr, ..))
            || typer.is_bool(e)
    };
    if truthy(&a) && falsy(&b) {
        return condition;
    }
    if falsy(&a) && truthy(&b) {
        return negate(condition);
    }
    if truthy(&a) && boolish(&b) {
        return Expr::binary(BinOp::LogicalOr, condition, b);
    }
    if falsy(&b) && boolish(&a) {
        return Expr::binary(BinOp::LogicalAnd, condition, a);
    }
    if falsy(&a) && boolish(&b) {
        return Expr::binary(BinOp::LogicalAnd, negate(condition), b);
    }
    if truthy(&b) && boolish(&a) {
        return Expr::binary(BinOp::LogicalOr, negate(condition), a);
    }
    // `x == null ? y : x` is `x ?? y`.
    if let Expr::Compare {
        op: Cmp::Eq,
        left,
        right,
        ..
    } = &condition
        && **right == Expr::Null
        && **left == b
    {
        return Expr::binary(BinOp::Coalesce, b, a);
    }
    // `x == null ? null : x.M()` is `x?.M()`.
    if let Expr::Compare {
        op, left, right, ..
    } = &condition
        && **right == Expr::Null
        && left.is_pure()
    {
        let (absent, present) = match op {
            Cmp::Eq => (&a, &b),
            Cmp::Ne => (&b, &a),
            _ => (&a, &a),
        };
        if matches!(absent, Expr::Null | Expr::Default(_))
            && let Some(chained) = with_maybe_null(present, left)
        {
            return chained;
        }
    }
    if let Expr::Compare {
        op: Cmp::Ne,
        left,
        right,
        ..
    } = &condition
        && **right == Expr::Null
        && **left == a
    {
        return Expr::binary(BinOp::Coalesce, a, b);
    }
    // `!c ? a : b` reads better as `c ? b : a`.
    if let Expr::Unary(UnOp::Not, inner) = condition {
        return Expr::Conditional(inner, Box::new(b), Box::new(a));
    }
    Expr::Conditional(Box::new(condition), Box::new(a), Box::new(b))
}

/// The expression with `?.` put on the innermost receiver that is the given
/// value, when the expression is a member access chain on it.
fn with_maybe_null(expr: &Expr, receiver: &Expr) -> Option<Expr> {
    fn rewrite(expr: &Expr, receiver: &Expr) -> Option<Expr> {
        let wrap = |inner: &Expr| -> Option<Box<Expr>> {
            if inner == receiver {
                Some(Box::new(Expr::MaybeNull(Box::new(receiver.clone()))))
            } else {
                rewrite(inner, receiver).map(Box::new)
            }
        };
        Some(match expr {
            Expr::Call {
                method,
                receiver: Some(inner),
                args,
            } => Expr::Call {
                method: method.clone(),
                receiver: Some(wrap(inner)?),
                args: args.clone(),
            },
            Expr::Property {
                receiver: Some(inner),
                declaring,
                name,
                ty,
            } => Expr::Property {
                receiver: Some(wrap(inner)?),
                declaring: declaring.clone(),
                name: name.clone(),
                ty: ty.clone(),
            },
            Expr::Field {
                receiver: Some(inner),
                field,
            } => Expr::Field {
                receiver: Some(wrap(inner)?),
                field: field.clone(),
            },
            Expr::Indexer {
                receiver: inner,
                args,
            } => Expr::Indexer {
                receiver: wrap(inner)?,
                args: args.clone(),
            },
            // A value type result is lifted to nullable; the box says so.
            Expr::Box(_, inner) => return rewrite(inner, receiver),
            Expr::Cast(_, inner)
                if matches!(inner.as_ref(), Expr::Call { .. } | Expr::Property { .. }) =>
            {
                return rewrite(inner, receiver);
            }
            _ => return None,
        })
    }
    rewrite(expr, receiver)
}

/// The `x` of a null check `x == null` / `x != null` on a variable, and
/// whether the check is for null. A field is not folded into `?.`: the
/// source read it twice, and `?.` would read it once.
fn null_check(condition: &Expr) -> Option<(&Expr, bool)> {
    let Expr::Compare {
        op, left, right, ..
    } = condition
    else {
        return None;
    };
    if **right != Expr::Null
        || !matches!(left.as_ref(), Expr::Local(_) | Expr::Arg(_) | Expr::Slot(_))
    {
        return None;
    }
    match op {
        Cmp::Eq => Some((left, true)),
        Cmp::Ne => Some((left, false)),
        _ => None,
    }
}

/// `t = x; if (t == null) { x = v; }`, with `t` read nowhere else, is
/// `x ??= v;`: the temporary held the place's value for the test.
fn fold_coalesce_assignment_temps(stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let folded = (|| {
            let (Expr::Local(temp), place) = assignment(&stmts[index])? else {
                return None;
            };
            if !uses.local_is_single(*temp) || !place.is_place() || !place.is_pure() {
                return None;
            }
            let Stmt::If {
                condition,
                then,
                otherwise,
            } = &stmts[index + 1]
            else {
                return None;
            };
            if !otherwise.is_empty() {
                return None;
            }
            let (checked, true) = null_check(condition)? else {
                return None;
            };
            if *checked != Expr::Local(*temp) {
                return None;
            }
            let Some(Stmt::Expr(Expr::Assign(target, value))) = single(then) else {
                return None;
            };
            if **target != *place {
                return None;
            }
            Some(Expr::Compound(
                BinOp::Coalesce,
                Box::new(place.clone()),
                value.clone(),
            ))
        })();
        if let Some(expr) = folded {
            stmts[index] = Stmt::Expr(expr);
            stmts.remove(index + 1);
            changed = true;
        } else {
            index += 1;
        }
    }
    changed
}

/// `if (x == null) { return c; } return x.P;` is `return x?.P ?? c;`, and
/// `return x?.P;` when `c` is null.
fn fold_null_conditional_returns(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let folded = (|| {
            let Stmt::If {
                condition,
                then,
                otherwise,
            } = &stmts[index]
            else {
                return None;
            };
            if !otherwise.is_empty() {
                return None;
            }
            let (checked, is_null) = null_check(condition)?;
            let Some(Stmt::Return(Some(inner))) = single(then) else {
                return None;
            };
            let Stmt::Return(Some(next)) = &stmts[index + 1] else {
                return None;
            };
            let (absent, present) = if is_null {
                (inner, next)
            } else {
                (next, inner)
            };
            if present.count(&|e| e == checked) != 1 {
                return None;
            }
            let chained = with_maybe_null(present, checked)?;
            Some(if matches!(absent, Expr::Null | Expr::Default(_)) {
                chained
            } else {
                Expr::binary(BinOp::Coalesce, chained, absent.clone())
            })
        })();
        if let Some(value) = folded {
            stmts[index] = Stmt::Return(Some(value));
            stmts.remove(index + 1);
            changed = true;
        } else {
            index += 1;
        }
    }
    changed
}

/// `if (x == null) { return; } x.M();` closing a body is `x?.M();`.
fn fold_null_conditional_tail(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = fold_null_conditional_tail_here(stmts);
    // The branches of a final `if` end where the method does.
    let last = stmts
        .iter()
        .rposition(|stmt| !matches!(stmt, Stmt::Label(_) | Stmt::Return(None)));
    if let Some(last) = last
        && stmts[last + 1..]
            .iter()
            .all(|stmt| matches!(stmt, Stmt::Label(_) | Stmt::Return(None)))
        && let Stmt::If {
            then, otherwise, ..
        } = &mut stmts[last]
    {
        changed |= fold_null_conditional_tail(then);
        changed |= fold_null_conditional_tail(otherwise);
    }
    changed
}

fn fold_null_conditional_tail_here(stmts: &mut Vec<Stmt>) -> bool {
    let mut real: Vec<usize> = (0..stmts.len())
        .filter(|at| !matches!(stmts[*at], Stmt::Label(_)))
        .collect();
    if matches!(real.last().map(|at| &stmts[*at]), Some(Stmt::Return(None))) {
        real.pop();
    }
    let (Some(&last), Some(&before)) = (real.last(), real.len().checked_sub(2).map(|at| &real[at]))
    else {
        return false;
    };
    let Stmt::If {
        condition,
        then,
        otherwise,
    } = &stmts[before]
    else {
        return false;
    };
    if !otherwise.is_empty() || !matches!(single(then), Some(Stmt::Return(None))) {
        return false;
    }
    let Some((checked, true)) = null_check(condition) else {
        return false;
    };
    let Stmt::Expr(call @ Expr::Call { .. }) = &stmts[last] else {
        return false;
    };
    if call.count(&|e| e == checked) != 1 {
        return false;
    }
    let Some(chained) = with_maybe_null(call, checked) else {
        return false;
    };
    stmts[last] = Stmt::Expr(chained);
    stmts.remove(before);
    true
}

/// `if (x != null) { x.M(); }` is `x?.M();`.
fn fold_null_conditional_statements(stmts: &mut [Stmt]) -> bool {
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
        if !otherwise.is_empty() {
            continue;
        }
        let Expr::Compare {
            op, left, right, ..
        } = condition
        else {
            continue;
        };
        if **right != Expr::Null || !left.is_pure() {
            continue;
        }
        match op {
            Cmp::Ne => {
                let Some(Stmt::Expr(
                    inner @ Expr::Call {
                        receiver: Some(_), ..
                    },
                )) = single(then)
                else {
                    continue;
                };
                let Some(chained) = with_maybe_null(inner, left) else {
                    continue;
                };
                *stmt = Stmt::Expr(chained);
                changed = true;
            }
            // `if (x == null) { x = v; }` is `x ??= v;`.
            Cmp::Eq => {
                let Some(Stmt::Expr(Expr::Assign(target, value))) = single(then) else {
                    continue;
                };
                if target != left {
                    continue;
                }
                let value = (**value).clone();
                *stmt = Stmt::Expr(Expr::Compound(
                    BinOp::Coalesce,
                    left.clone(),
                    Box::new(value),
                ));
                changed = true;
            }
            _ => {}
        }
    }
    changed
}

/// A slot assigned in one statement and read once in the next is the
/// expression itself, put back where it was evaluated; a local written once
/// and read once right after is the same.
fn inline_slots(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut changed = false;
    let mut index = stmts.len();
    while index > 1 {
        index -= 1;
        let at = index - 1;
        let Some((target, value)) = assignment(&stmts[at]) else {
            continue;
        };
        let single = match target {
            Expr::Slot(slot) => uses.slots.get(slot).copied().unwrap_or(0) == 1,
            Expr::Local(local) => uses.local_is_single(*local),
            _ => false,
        };
        // A delegate kept in a local reads better called by its name.
        if !single
            || (matches!(target, Expr::Local(_))
                && matches!(value, Expr::Delegate { .. } | Expr::Lambda { .. }))
        {
            continue;
        }
        let is_local = matches!(target, Expr::Local(_));
        let target = target.clone();
        let value = value.clone();
        let is_target = |e: &Expr| *e == target;
        // A local the source named stays a statement of its own, unless
        // it is only returned, yielded, tested with `?.`, or holds a copy,
        // a default or an awaited value: what a reader would have inlined.
        let local_inlinable = |consumer: &Stmt| -> bool {
            if !is_local {
                return true;
            }
            // A string held as a `ReadOnlySpan<char>` for .NET 8's span
            // concatenation is the compiler's.
            if typer.type_of(&target).is_some_and(|ty| {
                matches!(&ty, TypeSig::Generic { definition, .. }
                    if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                        if typer.ctx.resolver.raw_name(*token).as_deref() == Some("System.ReadOnlySpan`1")))
            }) && typer.type_of(&value) == Some(TypeSig::String)
            {
                return true;
            }
            // A condition a debug build computed into a `bool` before
            // testing it.
            if let Stmt::If { condition, .. } = consumer
                && (*condition == target
                    || matches!(condition, Expr::Unary(UnOp::Not, inner) if **inner == target))
                && typer.is_bool(&target)
            {
                return true;
            }
            if matches!(
                value,
                Expr::Default(_)
                    | Expr::Await(_)
                    | Expr::Assign(..)
                    | Expr::Local(_)
                    | Expr::Arg(_)
                    | Expr::This
            ) || value.is_constant()
            {
                return true;
            }
            // A copy of a stack value that is only the receiver of a member
            // access is the compiler's, not the source's.
            let copied_receiver = matches!(value, Expr::Slot(_)) && {
                let mut as_receiver = 0;
                consumer.walk_exprs(&mut |e| match e {
                    Expr::Field {
                        receiver: Some(inner),
                        ..
                    }
                    | Expr::Property {
                        receiver: Some(inner),
                        ..
                    }
                    | Expr::Call {
                        receiver: Some(inner),
                        ..
                    } if **inner == target => as_receiver += 1,
                    _ => {}
                });
                as_receiver == 1
            };
            if copied_receiver {
                return true;
            }
            match consumer {
                Stmt::Return(Some(read)) | Stmt::YieldReturn(read) if *read == target => true,
                other => {
                    // Through `?.`, under `await`, or as the receiver a
                    // struct value is called on: the compiler's temporaries.
                    // A type parameter is called on through a copy too.
                    let is_struct = typer.type_of(&target).is_some_and(|ty| {
                        typer.ctx.resolver.is_value_type(&ty)
                            || matches!(ty, TypeSig::Var(_) | TypeSig::MVar(_))
                    });
                    // A value read from a property or a call is a copy
                    // already; one read from a variable, a field or an
                    // element is not, and a call on it could change it.
                    let a_copy = !matches!(
                        value,
                        Expr::Local(_)
                            | Expr::Arg(_)
                            | Expr::Field { .. }
                            | Expr::Index { .. }
                            | Expr::Unary(UnOp::Deref, _)
                    );
                    let mut allowed = 0;
                    other.walk_exprs(&mut |e| match e {
                        Expr::MaybeNull(inner) | Expr::Await(inner) if **inner == target => {
                            allowed += 1;
                        }
                        Expr::Call {
                            receiver: Some(inner),
                            ..
                        }
                        | Expr::Property {
                            receiver: Some(inner),
                            ..
                        } if is_struct && a_copy && **inner == target => {
                            allowed += 1;
                        }
                        _ => {}
                    });
                    allowed == 1
                }
            }
        };
        // Statements between the definition and its use may be skipped when
        // they only copy variables around and touch nothing the value reads,
        // or when the value is one nothing can change: `this`, a constant.
        let immutable = matches!(value, Expr::This) || value.is_constant();
        let mut consumer = index;
        while consumer < stmts.len() && count_in_stmt_deep(&stmts[consumer], &is_target) == 0 {
            if immutable {
                if matches!(stmts[consumer], Stmt::Label(_)) || stmts[consumer].ends_flow() {
                    break;
                }
                consumer += 1;
                continue;
            }
            let Some((skipped_target, skipped_value)) = assignment(&stmts[consumer]) else {
                break;
            };
            let simple = matches!(
                skipped_value,
                Expr::Local(_) | Expr::Slot(_) | Expr::Arg(_) | Expr::This
            ) || skipped_value.is_constant();
            let writes_read = value.count(&|e| e == skipped_target) > 0;
            if !simple || writes_read || !matches!(skipped_target, Expr::Local(_) | Expr::Slot(_)) {
                break;
            }
            consumer += 1;
        }
        if consumer >= stmts.len() || !local_inlinable(&stmts[consumer]) {
            continue;
        }
        let uses_in_next = count_in_stmt(&stmts[consumer], &is_target);
        if uses_in_next == usize::MAX && immutable {
            // `this` or a constant can go wherever it is read.
            let mut replaced = stmts[consumer].clone();
            replaced.map_exprs(&mut |e| {
                if is_target(e) {
                    *e = value.clone();
                }
            });
            stmts[consumer] = replaced;
            stmts.remove(at);
            changed = true;
            continue;
        }
        if uses_in_next == usize::MAX
            && value.is_pure()
            && let Stmt::If {
                condition,
                then,
                otherwise,
            } = &mut stmts[consumer]
            && condition.is_pure()
            && condition.count(&is_target) == 0
        {
            // A pure value read once at the start of one branch.
            let mut total = 0;
            for block in [&*then, &*otherwise] {
                for stmt in block {
                    total += count_in_stmt_deep(stmt, &is_target);
                }
            }
            if total == 1 {
                let mut done = false;
                for block in [then, otherwise] {
                    if let Some(first) = block.iter_mut().find(|s| !matches!(s, Stmt::Label(_)))
                        && count_in_stmt(first, &is_target) == 1
                        && first_evaluated(first, &is_target)
                    {
                        replace_in_stmt_head(first, &is_target, &value);
                        done = true;
                        break;
                    }
                }
                if done {
                    stmts.remove(at);
                    changed = true;
                    continue;
                }
            }
            continue;
        }
        if uses_in_next != 1 {
            continue;
        }
        if matches!(
            stmts[consumer],
            Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. }
        ) {
            continue;
        }
        // The value has to be read where the consumer starts evaluating, not
        // after something the consumer does first; a variable the consumer
        // never writes reads the same anywhere in it.
        let unwritten = match &value {
            Expr::Local(_) | Expr::Arg(_) => {
                let mut written = false;
                stmts[consumer].walk_exprs(&mut |e| match e {
                    Expr::Assign(target, _)
                    | Expr::Compound(_, target, _)
                    | Expr::Increment { target, .. }
                        if **target == value =>
                    {
                        written = true;
                    }
                    Expr::Unary(UnOp::AddressOf, inner) | Expr::IsPattern(_, _, inner)
                        if **inner == value =>
                    {
                        written = true;
                    }
                    Expr::Lambda { .. } => written = true,
                    _ => {}
                });
                !written
            }
            _ => false,
        };
        if !unwritten && !first_evaluated(&stmts[consumer], &is_target) {
            continue;
        }
        let mut replaced = stmts[consumer].clone();
        replace_in_stmt_head(&mut replaced, &is_target, &value);
        stmts[consumer] = replaced;
        stmts.remove(at);
        changed = true;
    }
    changed
}

/// A lambda or method group invoked on the spot gets a local: C# cannot
/// call `(x => x)(1)` without a cast, and the local is what the source had.
fn hoist_invoked_lambdas(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut index = 0;
    let mut changed = false;
    while index < stmts.len() {
        let mut hoisted: Option<(Expr, TypeSig)> = None;
        for expr in head_exprs(&stmts[index]) {
            expr.walk(&mut |e| {
                if hoisted.is_none()
                    && let Expr::Call {
                        method,
                        receiver: Some(receiver),
                        ..
                    } = e
                    && method.name == "Invoke"
                    && matches!(
                        receiver.as_ref(),
                        Expr::Lambda { .. } | Expr::Delegate { .. }
                    )
                {
                    hoisted = Some(((**receiver).clone(), method.declaring.clone()));
                }
            });
        }
        let Some((receiver, ty)) = hoisted else {
            index += 1;
            continue;
        };
        let local = typer.new_local(ty);
        let mut consumer = stmts[index].clone();
        replace_in_stmt_head(&mut consumer, &|e| *e == receiver, &Expr::Local(local));
        stmts[index] = consumer;
        stmts.insert(
            index,
            Stmt::Expr(Expr::assign(Expr::Local(local), receiver)),
        );
        changed = true;
        index += 2;
    }
    changed
}

/// A slot that only ever holds one variable that nothing rewrites is that
/// variable: the copies made where a branch carried it are dropped.
fn propagate_slot_copies(stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut values: BTreeMap<u32, Vec<Expr>> = BTreeMap::new();
    fn scan(stmts: &[Stmt], values: &mut BTreeMap<u32, Vec<Expr>>) {
        for stmt in stmts {
            if let Some((target, value)) = assignment(stmt)
                && let Some(slot) = slot_of(target)
            {
                values.entry(slot).or_default().push(value.clone());
            }
            for block in stmt.blocks() {
                scan(block, values);
            }
        }
    }
    scan(stmts, &mut values);
    // Resolve slot-to-slot copies first, so `s2 = s1; s1 = x` reads as `x`.
    let mut resolved: BTreeMap<u32, Expr> = BTreeMap::new();
    let stable = |expr: &Expr, uses: &Uses| -> bool {
        match expr {
            Expr::This => true,
            Expr::Arg(at) => !uses.args_written.contains(at),
            Expr::Local(at) => matches!(uses.locals.get(at), Some((1, _, false))),
            // A slot written once holds its value for good.
            Expr::Slot(other) => values.get(other).is_some_and(|writes| writes.len() == 1),
            other => other.is_constant(),
        }
    };
    for _ in 0..4 {
        for (slot, assigned) in &values {
            if resolved.contains_key(slot) {
                continue;
            }
            let mut candidates: Vec<Expr> = Vec::new();
            for value in assigned {
                let value = match value {
                    Expr::Slot(other) => match resolved.get(other) {
                        Some(found) => found.clone(),
                        // A single-write slot stands for itself.
                        None if stable(value, uses) && other != slot => value.clone(),
                        None => continue,
                    },
                    other => other.clone(),
                };
                candidates.push(value);
            }
            if candidates.len() != assigned.len() || candidates.is_empty() {
                continue;
            }
            let first = candidates[0].clone();
            if candidates.iter().all(|c| *c == first) && stable(&first, uses) {
                resolved.insert(*slot, first);
            }
        }
    }
    if resolved.is_empty() {
        return false;
    }
    // A slot resolved to another slot that is itself resolved reads as
    // that slot's value: the reads are rewritten once, not chased.
    let slots: Vec<u32> = resolved.keys().copied().collect();
    for slot in slots {
        let mut value = resolved[&slot].clone();
        let mut hops = 0;
        while let Expr::Slot(other) = &value
            && let Some(next) = resolved.get(other)
            && hops < 16
        {
            value = next.clone();
            hops += 1;
        }
        resolved.insert(slot, value);
    }
    fn apply(stmts: &mut Vec<Stmt>, resolved: &BTreeMap<u32, Expr>) {
        stmts.retain(|stmt| {
            !matches!(assignment(stmt), Some((target, _)) if slot_of(target).is_some_and(|slot| resolved.contains_key(&slot)))
        });
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                apply(block, resolved);
            }
            stmt.map_exprs(&mut |e| {
                if let Some(slot) = slot_of(e)
                    && let Some(value) = resolved.get(&slot)
                {
                    *e = value.clone();
                }
            });
        }
    }
    apply(stmts, &resolved);
    true
}

/// `s = e; x = s; use(s)` is `use(x = e)`: the assignment was inside the
/// expression, as in `while ((line = reader.ReadLine()) != null)`.
fn fold_assignment_expressions(stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 2 < stmts.len() {
        let Some((temp, value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let twice = match temp {
            Expr::Slot(slot) => uses.slots.get(slot).copied().unwrap_or(0) == 2,
            Expr::Local(local) => matches!(uses.locals.get(local), Some((1, 2, false))),
            _ => false,
        };
        if !twice {
            index += 1;
            continue;
        }
        let temp = temp.clone();
        let value = value.clone();
        let Some((copy_target, copied)) = assignment(&stmts[index + 1]) else {
            index += 1;
            continue;
        };
        if *copied != temp {
            index += 1;
            continue;
        }
        let is_slot = |e: &Expr| *e == temp;
        // `s = e; field = s; use(s)`: a place other than a local takes the
        // assignment the same way.
        if !matches!(copy_target, Expr::Local(_)) {
            if copy_target.is_place()
                && copy_target.is_pure()
                && copy_target.count(&is_slot) == 0
                && count_in_stmt(&stmts[index + 2], &is_slot) == 1
                && first_evaluated(&stmts[index + 2], &is_slot)
            {
                let replacement = Expr::assign(copy_target.clone(), value);
                let mut consumer = stmts[index + 2].clone();
                replace_in_stmt_head(&mut consumer, &is_slot, &replacement);
                stmts[index + 2] = consumer;
                stmts.drain(index..index + 2);
                changed = true;
            } else {
                index += 1;
            }
            continue;
        }
        let Expr::Local(local) = copy_target else {
            unreachable!()
        };
        let local = *local;
        // `s = e; t = s; x = s; use(t)`, the value duplicated into a
        // temporary and a place: `use(x = e)` when `t` is only that use.
        if uses.local_is_single(local)
            && index + 3 < stmts.len()
            && let Some((place, copied)) = assignment(&stmts[index + 2])
            && *copied == temp
            && place.is_place()
            && place.is_pure()
            && place.count(&|e| *e == Expr::Local(local)) == 0
        {
            let is_local = |e: &Expr| *e == Expr::Local(local);
            if count_in_stmt(&stmts[index + 3], &is_local) == 1
                && first_evaluated(&stmts[index + 3], &is_local)
            {
                let replacement = Expr::assign(place.clone(), value);
                let mut consumer = stmts[index + 3].clone();
                replace_in_stmt_head(&mut consumer, &is_local, &replacement);
                stmts[index + 3] = consumer;
                stmts.drain(index..index + 3);
                changed = true;
                continue;
            }
        }
        if count_in_stmt(&stmts[index + 2], &is_slot) != 1
            || !first_evaluated(&stmts[index + 2], &is_slot)
        {
            index += 1;
            continue;
        }
        let replacement = Expr::assign(Expr::Local(local), value);
        let mut consumer = stmts[index + 2].clone();
        replace_in_stmt_head(&mut consumer, &is_slot, &replacement);
        stmts[index + 2] = consumer;
        stmts.drain(index..index + 2);
        changed = true;
    }
    changed
}

/// A local assigned once with `this` or a constant, and never taken by
/// reference, is that value wherever it is read.
fn propagate_immutable_locals(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut values: HashMap<u16, Expr> = HashMap::new();
    fn scan(stmts: &[Stmt], uses: &Uses, values: &mut HashMap<u16, Expr>) {
        for stmt in stmts {
            // A parameter copied into a local whose address is then taken
            // (a struct the method calls into) stays a copy, as written.
            if let Some((Expr::Local(local), value)) = assignment(stmt)
                && matches!(uses.locals.get(local), Some((1, _, false)))
                && (matches!(value, Expr::This)
                    || value.is_constant()
                    || matches!(value, Expr::Arg(at) if !uses.args_written.contains(at)))
            {
                values.insert(*local, value.clone());
            }
            for block in stmt.blocks() {
                scan(block, uses, values);
            }
        }
    }
    scan(stmts, uses, &mut values);
    // A local only ever set to one and the same constant, however often
    // (`num = null` in each branch that needs a `null` of its type), is that
    // constant.
    let mut constants: HashMap<u16, Vec<Expr>> = HashMap::new();
    fn gather(stmts: &[Stmt], constants: &mut HashMap<u16, Vec<Expr>>) {
        for stmt in stmts {
            if let Some((Expr::Local(local), value)) = assignment(stmt) {
                constants.entry(*local).or_default().push(value.clone());
            }
            for block in stmt.blocks() {
                gather(block, constants);
            }
        }
    }
    gather(stmts, &mut constants);
    for (local, written) in constants {
        let Some(first) = written.first() else {
            continue;
        };
        if written.len() > 1
            && matches!(uses.locals.get(&local), Some((writes, _, false)) if *writes == written.len())
            && (first.is_constant() || matches!(first, Expr::Default(_)))
            && written.iter().all(|value| value == first)
        {
            values.insert(local, first.clone());
        }
    }
    // `null` is no receiver, nor the left of a `??`: a local that is one
    // keeps its name.
    let mut receivers: HashSet<u16> = HashSet::new();
    for stmt in stmts.iter() {
        stmt.walk_exprs(&mut |e| {
            let place = match e {
                Expr::Call {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Property {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Field {
                    receiver: Some(receiver),
                    ..
                } => receiver.as_ref(),
                Expr::MaybeNull(inner) | Expr::Length(inner) => inner.as_ref(),
                Expr::Binary(BinOp::Coalesce, left, _) => left.as_ref(),
                _ => return,
            };
            let place = match place {
                Expr::MaybeNull(inner) | Expr::Unary(UnOp::AddressOf, inner) => inner.as_ref(),
                other => other,
            };
            if let Expr::Local(local) = place {
                receivers.insert(*local);
            }
        });
    }
    values.retain(|local, value| {
        !(matches!(value, Expr::Null | Expr::Default(_)) && receivers.contains(local))
    });
    if values.is_empty() {
        return false;
    }
    // On the stack `uint u = 0xFFFFFFFF` is `-1`: the constant goes where
    // the local went as a value of the local's type, not as the `int` it
    // was loaded as.
    for (local, value) in values.iter_mut() {
        if value.is_constant()
            && let Some(ty) = typer.type_of(&Expr::Local(*local))
        {
            crate::fit::fit_value(typer, value, &ty);
        }
    }
    fn apply(stmts: &mut Vec<Stmt>, values: &HashMap<u16, Expr>) {
        stmts.retain(|stmt| {
            !matches!(assignment(stmt), Some((Expr::Local(local), _)) if values.contains_key(local))
        });
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                apply(block, values);
            }
            stmt.map_exprs(&mut |e| {
                if let Expr::Local(local) = e
                    && let Some(value) = values.get(local)
                {
                    *e = value.clone();
                }
            });
        }
    }
    apply(stmts, &values);
    true
}

/// `t = x; f(t);` with `t` read nowhere else before it is written again:
/// the compiler's copy of a variable or constant, used where it was taken.
fn forward_local_copies(typer: &Typer<'_, '_>, root: &mut Vec<Stmt>) -> bool {
    type Live<'a> = &'a dyn Fn(&Expr) -> bool;
    fn mentions_in(stmts: &[Stmt], counts: &mut HashMap<u16, usize>, addressed: &mut HashSet<u16>) {
        for stmt in stmts {
            stmt.walk_exprs(&mut |e| match e {
                Expr::Local(local) => *counts.entry(*local).or_default() += 1,
                Expr::Unary(UnOp::AddressOf, inner) => {
                    if let Expr::Local(local) = inner.as_ref() {
                        addressed.insert(*local);
                    }
                }
                _ => {}
            });
        }
    }
    fn count(stmt: &Stmt, target: &Expr) -> usize {
        let mut found = 0;
        stmt.walk_exprs(&mut |e| found += usize::from(e == target));
        found
    }
    // Written, taken by address, or a receiver somewhere in the statement.
    fn used_as_place(stmt: &Stmt, target: &Expr) -> bool {
        let mut found = false;
        stmt.walk_exprs(&mut |e| {
            let place = match e {
                Expr::Assign(place, _) | Expr::Compound(_, place, _) => Some(place.as_ref()),
                Expr::Increment { target, .. } => Some(target.as_ref()),
                Expr::Unary(UnOp::AddressOf, inner) => Some(inner.as_ref()),
                Expr::Call {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Property {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Field {
                    receiver: Some(receiver),
                    ..
                } => Some(receiver.as_ref()),
                Expr::Lambda { .. } => {
                    found = true;
                    None
                }
                _ => None,
            };
            if place == Some(target) {
                found = true;
            }
        });
        found
    }
    // Whether evaluating the expression reaches the variable before
    // anything that has an effect, reads what an effect could change, or
    // could throw: what it holds may then be computed there instead.
    // `None` when the variable is not in it.
    fn reached_first(
        typer: &Typer<'_, '_>,
        expr: &Expr,
        variable: &Expr,
        written: &[Expr],
        effect: &mut bool,
    ) -> Option<bool> {
        if expr == variable {
            return Some(!*effect);
        }
        // A variable the moved value writes, by `out` or otherwise, is
        // read before it would be written.
        if written.contains(expr) {
            *effect = true;
            return None;
        }
        let mentions = |e: &Expr| e.count(&|inner| inner == variable) > 0;
        match expr {
            Expr::Local(_)
            | Expr::Slot(_)
            | Expr::Int(_)
            | Expr::Long(_)
            | Expr::Float(..)
            | Expr::Bool(_)
            | Expr::Char(_)
            | Expr::Str(_)
            | Expr::Null
            | Expr::This
            | Expr::EnumMember(..)
            | Expr::Default(_)
            | Expr::TypeOf(_)
            | Expr::SizeOf(_) => return None,
            // A `ref` parameter is memory an effect could change.
            Expr::Arg(_) => {
                if matches!(typer.type_of(expr), Some(TypeSig::ByRef(_)) | None) {
                    *effect = true;
                }
                return None;
            }
            // Only some ways evaluate what is conditional.
            Expr::Conditional(condition, a, b) => {
                if let Some(found) = reached_first(typer, condition, variable, written, effect) {
                    return Some(found);
                }
                if mentions(a) || mentions(b) {
                    return Some(false);
                }
                *effect = true;
                return None;
            }
            Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::Coalesce, left, right) => {
                if let Some(found) = reached_first(typer, left, variable, written, effect) {
                    return Some(found);
                }
                if mentions(right) {
                    return Some(false);
                }
                *effect = true;
                return None;
            }
            // A local stored to is no read.
            Expr::Assign(target, value) if matches!(target.as_ref(), Expr::Local(_)) => {
                let found = reached_first(typer, value, variable, written, effect);
                *effect = true;
                return found;
            }
            // Nor is an element or field stored to: what locates it is
            // evaluated, then the value, then the store is made.
            Expr::Assign(target, value)
                if matches!(target.as_ref(), Expr::Index { .. } | Expr::Field { .. }) =>
            {
                let mut parts = Vec::new();
                target.children(&mut parts);
                for part in parts {
                    if let Some(found) = reached_first(typer, part, variable, written, effect) {
                        return Some(found);
                    }
                }
                let found = reached_first(typer, value, variable, written, effect);
                *effect = true;
                return found;
            }
            _ => {}
        }
        let mut children = Vec::new();
        expr.children(&mut children);
        for child in children {
            if let Some(found) = reached_first(typer, child, variable, written, effect) {
                return Some(found);
            }
        }
        // What neither acts, reads memory nor throws.
        let quiet = match expr {
            Expr::Binary(op, ..) => !matches!(op, BinOp::Div | BinOp::Rem),
            Expr::Compare { .. } | Expr::Tuple(_) | Expr::Box(..) | Expr::As(..) | Expr::Is(..) => {
                true
            }
            Expr::Unary(op, _) => !matches!(op, UnOp::Deref),
            Expr::Cast(ty, _) => matches!(
                ty,
                TypeSig::SByte
                    | TypeSig::Byte
                    | TypeSig::Int16
                    | TypeSig::UInt16
                    | TypeSig::Int32
                    | TypeSig::UInt32
                    | TypeSig::Int64
                    | TypeSig::UInt64
                    | TypeSig::Single
                    | TypeSig::Double
                    | TypeSig::Char
                    | TypeSig::Boolean
                    | TypeSig::Object
            ),
            _ => false,
        };
        if !quiet {
            *effect = true;
        }
        None
    }
    // Whether the statement writes the variable, or anything inside it,
    // passes it by reference, or captures it: anything but reading it,
    // directly or as a receiver.
    fn more_than_read(stmt: &Stmt, target: &Expr) -> bool {
        let mut found = false;
        let mut receivers = 0usize;
        let mut addresses = 0usize;
        stmt.walk_exprs(&mut |e| match e {
            Expr::Assign(place, _) | Expr::Compound(_, place, _) | Expr::Increment { target: place, .. } => {
                if place.count(&|inner| inner == target) > 0 {
                    found = true;
                }
            }
            Expr::Unary(UnOp::AddressOf, inner) if **inner == *target => addresses += 1,
            Expr::Call {
                receiver: Some(receiver),
                ..
            }
            | Expr::Property {
                receiver: Some(receiver),
                ..
            }
            | Expr::Field {
                receiver: Some(receiver),
                ..
            } => {
                if matches!(receiver.as_ref(), Expr::Unary(UnOp::AddressOf, inner) if **inner == *target) {
                    receivers += 1;
                }
            }
            Expr::Lambda { .. }
                if e.count(&|inner| inner == target) > 0 => {
                    found = true;
                }
            _ => {}
        });
        found || addresses > receivers
    }
    // Whether every way through writes the variable before reading it:
    // `None` when it falls through without mentioning it. Strictly, a way
    // out of the list counts as what is known of where it leads: `brk`
    // for a `break`, `cont` for a `continue`, nothing for a `goto`.
    fn written_first(
        stmts: &[Stmt],
        variable: &Expr,
        strict: bool,
        brk: Live<'_>,
        cont: Live<'_>,
    ) -> Option<bool> {
        for stmt in stmts {
            if let Stmt::If {
                condition,
                then,
                otherwise,
            } = stmt
            {
                if condition.count(&|e| e == variable) > 0 {
                    return Some(false);
                }
                match (
                    written_first(then, variable, strict, brk, cont),
                    written_first(otherwise, variable, strict, brk, cont),
                ) {
                    (Some(false), _) | (_, Some(false)) => return Some(false),
                    (Some(true), Some(true)) => return Some(true),
                    // One way goes on as it was: what follows decides.
                    _ => continue,
                }
            }
            // A block with a header runs the header, then the block.
            let headed: Option<(&Expr, &[Stmt])> = match stmt {
                Stmt::Using { resource, body, .. } => Some((resource, body)),
                Stmt::Lock { target, body } => Some((target, body)),
                Stmt::Fixed { init, body, .. } => Some((init, body)),
                _ => None,
            };
            if let Some((header, body)) = headed
                && count(stmt, variable) > 0
            {
                if header.count(&|e| e == variable) > 0 {
                    return Some(false);
                }
                match written_first(body, variable, strict, brk, cont) {
                    Some(known) => return Some(known),
                    None => continue,
                }
            }
            // A `try` whose handlers leave it alone: its body reading it
            // first is a read; writing it first is so only on the way that
            // throws nothing, so what follows still decides.
            if let Stmt::Try {
                body,
                catches,
                finally,
            } = stmt
                && count(stmt, variable) > 0
            {
                let handlers_mention = catches.iter().any(|catch| {
                    catch.body.iter().any(|stmt| count(stmt, variable) > 0)
                        || catch
                            .filter
                            .as_ref()
                            .is_some_and(|filter| filter.count(&|e| e == variable) > 0)
                }) || finally
                    .as_ref()
                    .is_some_and(|finally| finally.iter().any(|stmt| count(stmt, variable) > 0));
                if handlers_mention
                    || written_first(body, variable, strict, brk, cont) == Some(false)
                {
                    return Some(false);
                }
                continue;
            }
            if let Stmt::Checked(body) = stmt
                && count(stmt, variable) > 0
            {
                match written_first(body, variable, strict, brk, cont) {
                    Some(known) => return Some(known),
                    None => continue,
                }
            }
            if count(stmt, variable) == 0 {
                if strict {
                    match stmt {
                        Stmt::Return(_) | Stmt::Throw(_) | Stmt::YieldBreak => return Some(true),
                        Stmt::Break => return Some(brk(variable)),
                        Stmt::Continue => return Some(cont(variable)),
                        Stmt::Goto(_) | Stmt::Label(_) => return Some(false),
                        _ if has_jumps(stmt) => return Some(false),
                        _ => {}
                    }
                }
                continue;
            }
            if let Some((target, value)) = assignment(stmt)
                && target == variable
            {
                return Some(value.count(&|e| e == variable) == 0);
            }
            return Some(false);
        }
        None
    }
    // A jump somewhere inside: a `goto` anywhere, or a `break` or
    // `continue` of an enclosing loop (or of one inside, conservatively).
    fn has_jumps(stmt: &Stmt) -> bool {
        stmt.blocks().into_iter().any(|block| {
            block.iter().any(|inner| {
                matches!(
                    inner,
                    Stmt::Goto(_) | Stmt::Label(_) | Stmt::Break | Stmt::Continue
                ) || has_jumps(inner)
            })
        })
    }
    fn locals_in(stmts: &[Stmt]) -> HashSet<u16> {
        let mut found = HashSet::new();
        for stmt in stmts {
            stmt.walk_exprs(&mut |e| {
                if let Expr::Local(local) = e {
                    found.insert(*local);
                }
            });
        }
        found
    }
    // Whether the statement changes the variable before it is done
    // reading: `x = t + 1` reads all of `t + 1` first.
    fn changes(stmt: &Stmt, variable: &Expr) -> bool {
        match stmt {
            Stmt::Expr(Expr::Assign(target, value)) if **target == *variable => {
                used_as_place(&Stmt::Expr((**value).clone()), variable)
            }
            _ => used_as_place(stmt, variable),
        }
    }
    fn go(
        typer: &Typer<'_, '_>,
        stmts: &mut Vec<Stmt>,
        totals: &mut HashMap<u16, usize>,
        addressed: &HashSet<u16>,
        exits: (Live<'_>, Live<'_>, Live<'_>, Live<'_>),
    ) -> bool {
        // Dead where the list ends, where a `break` and a `continue` go,
        // and wherever a throw from inside it lands.
        let (dead_after, brk, cont, thrown) = exits;
        let never = |_: &Expr| false;
        let mut changed = false;
        for at in 0..stmts.len() {
            let (head, tail) = stmts.split_at_mut(at + 1);
            let stmt = &mut head[at];
            let tail: &[Stmt] = tail;
            let after_stmt = |variable: &Expr| match written_first(tail, variable, true, brk, cont)
            {
                Some(known) => known,
                None => dead_after(variable),
            };
            // A loop's body ends at its head: dead there when the head
            // reads nothing of it, what follows the loop reads nothing of
            // it, and the body writes it before reading it.
            let (is_loop, head_reads, body_reads_first) = {
                let stmt: &Stmt = stmt;
                let (head_exprs, body): (Vec<&Expr>, Option<&Vec<Stmt>>) = match stmt {
                    Stmt::While { condition, body } | Stmt::DoWhile { body, condition } => {
                        (vec![condition], Some(body))
                    }
                    Stmt::For {
                        condition,
                        step,
                        body,
                        ..
                    } => (
                        std::iter::once(condition).chain(step.as_ref()).collect(),
                        Some(body),
                    ),
                    Stmt::ForEach { source, body, .. } => (vec![source], Some(body)),
                    _ => (Vec::new(), None),
                };
                let mut head_reads = HashSet::new();
                for expr in head_exprs {
                    expr.walk(&mut |e| {
                        if let Expr::Local(local) = e {
                            head_reads.insert(*local);
                        }
                    });
                }
                if let Stmt::ForEach { local, .. } = stmt {
                    head_reads.insert(*local);
                }
                let mut reads_first = HashSet::new();
                if let Some(body) = body {
                    for local in locals_in(body) {
                        let variable = Expr::Local(local);
                        if written_first(body, &variable, true, &after_stmt, &never) == Some(false)
                        {
                            reads_first.insert(local);
                        }
                    }
                }
                (body.is_some(), head_reads, reads_first)
            };
            let at_head = |variable: &Expr| {
                let Expr::Local(local) = variable else {
                    return false;
                };
                !head_reads.contains(local)
                    && !body_reads_first.contains(local)
                    && after_stmt(variable)
            };
            let unknown = |_: &Expr| false;
            // A throw inside a `try` goes through its handlers, then on
            // after it: they must leave the variable alone, and it must be
            // dead after the `try` as well as wherever else a throw goes.
            let handled: HashSet<u16> = match &*stmt {
                Stmt::Try {
                    catches, finally, ..
                } => {
                    let mut found = HashSet::new();
                    for catch in catches {
                        found.extend(locals_in(&catch.body));
                        if let Some(filter) = &catch.filter {
                            filter.walk(&mut |e| {
                                if let Expr::Local(local) = e {
                                    found.insert(*local);
                                }
                            });
                        }
                    }
                    if let Some(finally) = finally {
                        found.extend(locals_in(finally));
                    }
                    found
                }
                _ => HashSet::new(),
            };
            let caught = |variable: &Expr| {
                matches!(variable, Expr::Local(local) if !handled.contains(local))
                    && after_stmt(variable)
                    && thrown(variable)
            };
            let untouched = |variable: &Expr| matches!(variable, Expr::Local(local) if !handled.contains(local));
            let try_brk = |variable: &Expr| untouched(variable) && brk(variable);
            let try_cont = |variable: &Expr| untouched(variable) && cont(variable);
            let children: (Live<'_>, Live<'_>, Live<'_>, Live<'_>) = match stmt {
                Stmt::If { .. } | Stmt::Checked(_) => (&after_stmt, brk, cont, thrown),
                _ if is_loop => (&at_head, &after_stmt, &at_head, thrown),
                Stmt::Switch { .. } => (&unknown, &after_stmt, cont, thrown),
                // The `finally` of these disposes or unlocks, nothing more.
                Stmt::Using { .. } | Stmt::Lock { .. } | Stmt::Fixed { .. } => {
                    (&after_stmt, brk, cont, thrown)
                }
                // Leaving by the end, a `break` or a `continue` goes through
                // the `finally` too.
                Stmt::Try { .. } => (&caught, &try_brk, &try_cont, &caught),
                _ => (&unknown, &unknown, &unknown, &unknown),
            };
            for block in stmt.blocks_mut() {
                changed |= go(typer, block, totals, addressed, children);
            }
        }
        let mut index = 0;
        while index + 1 < stmts.len() {
            let Some((Expr::Local(local), value)) = assignment(&stmts[index]) else {
                index += 1;
                continue;
            };
            let local = *local;
            let simple = matches!(
                value,
                Expr::Local(_)
                    | Expr::Arg(_)
                    | Expr::Int(_)
                    | Expr::Long(_)
                    | Expr::Float(..)
                    | Expr::Bool(_)
                    | Expr::Char(_)
                    | Expr::Str(_)
                    | Expr::Null
            );
            let copyable = match value {
                Expr::Local(from) => *from != local && !addressed.contains(from),
                Expr::Arg(_) => true,
                Expr::Int(_)
                | Expr::Long(_)
                | Expr::Float(..)
                | Expr::Bool(_)
                | Expr::Char(_)
                | Expr::Str(_)
                | Expr::Null => true,
                // A delegate is named for what it does, a local function's
                // stays where the function is in scope.
                Expr::Delegate { .. } | Expr::Lambda { .. } => false,
                // A value with effects keeps its place among them.
                other => other.count(&|e| matches!(e, Expr::Local(l) if *l == local)) == 0,
            };
            let variable = Expr::Local(local);
            let value = value.clone();
            let mut here: HashMap<u16, usize> = HashMap::new();
            let mut unused = HashSet::new();
            mentions_in(stmts, &mut here, &mut unused);
            // The use may come after statements that neither mention it nor
            // change what it copied.
            let mut use_at = index + 1;
            while use_at + 1 < stmts.len()
                && count(&stmts[use_at], &variable) == 0
                && matches!(stmts[use_at], Stmt::Expr(_))
                && !(matches!(value, Expr::Local(_) | Expr::Arg(_))
                    && used_as_place(&stmts[use_at], &value))
            {
                use_at += 1;
            }
            let next = &stmts[use_at];
            let rest = &stmts[use_at + 1..];
            // What runs after the use: the branches of an `if` it is the
            // condition of, then what follows.
            let after_use = |strict: bool| {
                if let Stmt::If {
                    then, otherwise, ..
                } = next
                {
                    match (
                        written_first(then, &variable, strict, brk, cont),
                        written_first(otherwise, &variable, strict, brk, cont),
                    ) {
                        (Some(false), _) | (_, Some(false)) => return Some(false),
                        (Some(true), Some(true)) => return Some(true),
                        _ => {}
                    }
                }
                written_first(rest, &variable, strict, brk, cont)
            };
            // Every mention of it is in this list, none before the copy.
            let contained = here.get(&local) == totals.get(&local)
                && stmts[..index]
                    .iter()
                    .all(|stmt| count(stmt, &variable) == 0)
                && after_use(false) != Some(false);
            // Or it is dead on every way on from the use, and nothing
            // could throw to a handler reading it in between.
            let dead = thrown(&variable)
                && use_at == index + 1
                && match after_use(true) {
                    Some(known) => known,
                    None => dead_after(&variable),
                };
            // A reference, pinned by `fixed` or not, is not a copy.
            let ty = typer.type_of(&variable);
            let reference = matches!(ty, Some(TypeSig::ByRef(_)) | None);
            // Nor is a copy that converts: `object o = s` compares by
            // reference, `byte b = 5` picks other overloads.
            let same_type = match &value {
                Expr::Local(_) | Expr::Arg(_) => typer.type_of(&value) == ty,
                Expr::Int(_) => ty == Some(TypeSig::Int32),
                Expr::Long(_) => ty == Some(TypeSig::Int64),
                Expr::Float(_, false) => ty == Some(TypeSig::Double),
                Expr::Float(_, true) => ty == Some(TypeSig::Single),
                Expr::Bool(_) => ty == Some(TypeSig::Boolean),
                Expr::Char(_) => ty == Some(TypeSig::Char),
                Expr::Str(_) => ty == Some(TypeSig::String),
                Expr::Null => ty
                    .as_ref()
                    .is_some_and(|ty| typer.ctx.resolver.is_nullable(ty)),
                // Anything else moves only to where it is the first thing
                // evaluated: `await t`, `x = t`, `return t`.
                _ => typer.type_of(&value) == ty,
            };
            let mut written: Vec<Expr> = Vec::new();
            value.walk(&mut |e| {
                let place = match e {
                    Expr::Assign(place, _)
                    | Expr::Compound(_, place, _)
                    | Expr::Increment { target: place, .. }
                    | Expr::Unary(UnOp::AddressOf, place) => place.as_ref(),
                    _ => return,
                };
                if matches!(place, Expr::Local(_) | Expr::Arg(_) | Expr::Slot(_)) {
                    written.push(place.clone());
                }
            });
            let evaluated_first = |stmt: &Stmt| {
                let mut effect = false;
                let found = match stmt {
                    Stmt::Expr(e) | Stmt::Return(Some(e)) | Stmt::Throw(Some(e)) => {
                        reached_first(typer, e, &variable, &written, &mut effect)
                    }
                    Stmt::If { condition, .. } => {
                        reached_first(typer, condition, &variable, &written, &mut effect)
                    }
                    Stmt::Declare {
                        value: Some(value), ..
                    } => reached_first(typer, value, &variable, &written, &mut effect),
                    _ => None,
                };
                found == Some(true)
            };
            let ok = copyable
                && same_type
                && (simple || (use_at == index + 1 && evaluated_first(next)))
                && !reference
                && !addressed.contains(&local)
                && count(next, &variable) == 1
                // Read, and as a receiver only where that reads the same
                // thing: not a struct variable, which would be called on
                // in place.
                && !more_than_read(next, &variable)
                && !(used_as_place(next, &variable)
                    && matches!(value, Expr::Local(_) | Expr::Arg(_))
                    && ty.as_ref().is_some_and(|ty| {
                        // A number's methods change nothing of it.
                        !matches!(
                            ty,
                            TypeSig::Boolean
                                | TypeSig::Char
                                | TypeSig::SByte
                                | TypeSig::Byte
                                | TypeSig::Int16
                                | TypeSig::UInt16
                                | TypeSig::Int32
                                | TypeSig::UInt32
                                | TypeSig::Int64
                                | TypeSig::UInt64
                                | TypeSig::Single
                                | TypeSig::Double
                                | TypeSig::IntPtr
                                | TypeSig::UIntPtr
                        ) && typer.ctx.resolver.is_value_type(ty)
                    }))
                && !(matches!(value, Expr::Local(_) | Expr::Arg(_)) && changes(next, &value))
                && (contained || dead);
            if !ok {
                index += 1;
                continue;
            }
            stmts[use_at].map_exprs(&mut |e| {
                if *e == variable {
                    *e = value.clone();
                }
            });
            stmts.remove(index);
            if let Some(total) = totals.get_mut(&local) {
                *total -= 2;
            }
            changed = true;
        }
        changed
    }
    let mut totals = HashMap::new();
    let mut addressed = HashSet::new();
    mentions_in(root, &mut totals, &mut addressed);
    // What the body's end leaves is never read.
    let never = |_: &Expr| false;
    go(
        typer,
        root,
        &mut totals,
        &addressed,
        (&|_| true, &never, &never, &|_| true),
    )
}

/// A store of a pure value into a local nothing ever reads is dropped:
/// the compiler's temporary for a value the source discarded.
fn drop_dead_local_stores(stmts: &mut Vec<Stmt>, uses: &Uses) {
    fn prune(stmts: &mut Vec<Stmt>, uses: &Uses) {
        stmts.retain(|stmt| {
            !matches!(assignment(stmt), Some((Expr::Local(local), value))
                if matches!(uses.locals.get(local), Some((_, 0, false))) && value.is_pure())
        });
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                prune(block, uses);
            }
        }
    }
    prune(stmts, uses);
}

/// `s = x; x++; use(s)` is `use(x++)`, and `x++; s = x; use(s)` is
/// `use(++x)`.
fn fold_increments(stmts: &mut Vec<Stmt>, uses: &Uses) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 2 < stmts.len() {
        let step = |stmt: &Stmt| -> Option<(Expr, i64)> {
            match stmt {
                Stmt::Expr(Expr::Increment { target, delta, .. }) => {
                    Some(((**target).clone(), *delta))
                }
                Stmt::Expr(Expr::Compound(BinOp::Add, target, value))
                    if **value == Expr::Int(1) =>
                {
                    Some(((**target).clone(), 1))
                }
                Stmt::Expr(Expr::Compound(BinOp::Sub, target, value))
                    if **value == Expr::Int(1) =>
                {
                    Some(((**target).clone(), -1))
                }
                Stmt::Expr(Expr::Assign(target, value)) => match value.as_ref() {
                    Expr::Binary(BinOp::Add, left, right)
                        if left == target && **right == Expr::Int(1) =>
                    {
                        Some(((**target).clone(), 1))
                    }
                    Expr::Binary(BinOp::Sub, left, right)
                        if left == target && **right == Expr::Int(1) =>
                    {
                        Some(((**target).clone(), -1))
                    }
                    _ => None,
                },
                _ => None,
            }
        };
        // Postfix: the copy comes first.
        if let Some((Expr::Slot(slot), copied)) = assignment(&stmts[index])
            && copied.is_place()
            && uses.slots.get(slot).copied().unwrap_or(0) == 1
            && let Some((target, delta)) = step(&stmts[index + 1])
            && target == *copied
        {
            let slot = *slot;
            let is_slot = |e: &Expr| slot_of(e) == Some(slot);
            if count_in_stmt(&stmts[index + 2], &is_slot) == 1 {
                let replacement = Expr::Increment {
                    target: Box::new(target),
                    delta,
                    postfix: true,
                };
                let mut consumer = stmts[index + 2].clone();
                replace_in_stmt_head(&mut consumer, &is_slot, &replacement);
                stmts[index + 2] = consumer;
                stmts.drain(index..index + 2);
                changed = true;
                continue;
            }
        }
        // Prefix: the step comes first.
        if let Some((target, delta)) = step(&stmts[index])
            && let Some((Expr::Slot(slot), copied)) = assignment(&stmts[index + 1])
            && *copied == target
            && uses.slots.get(slot).copied().unwrap_or(0) == 1
        {
            let slot = *slot;
            let is_slot = |e: &Expr| slot_of(e) == Some(slot);
            if count_in_stmt(&stmts[index + 2], &is_slot) == 1 {
                let replacement = Expr::Increment {
                    target: Box::new(target),
                    delta,
                    postfix: false,
                };
                let mut consumer = stmts[index + 2].clone();
                replace_in_stmt_head(&mut consumer, &is_slot, &replacement);
                stmts[index + 2] = consumer;
                stmts.drain(index..index + 2);
                changed = true;
                continue;
            }
        }
        index += 1;
    }
    changed
}

/// `if (x is T) { ... (x as T) ... }` binds a pattern variable:
/// `if (x is T t) { ... t ... }`.
fn bind_is_patterns(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        let Stmt::If {
            condition, then, ..
        } = stmt
        else {
            continue;
        };
        let Expr::Is(ty, source) = condition else {
            continue;
        };
        if !source.is_pure() {
            continue;
        }
        let (ty, source) = (ty.clone(), (**source).clone());
        let is_cast =
            |e: &Expr| matches!(e, Expr::As(as_ty, inner) if *as_ty == ty && **inner == source);
        let mut reads = 0;
        for inner in then.iter() {
            reads += count_in_stmt_deep(inner, &is_cast);
        }
        if reads == 0 {
            continue;
        }
        let local = typer.new_local(ty.clone());
        for inner in then.iter_mut() {
            inner.map_exprs(&mut |e| {
                if is_cast(e) {
                    *e = Expr::Local(local);
                }
            });
        }
        *condition = Expr::IsPattern(ty, Box::new(source), Box::new(Expr::Local(local)));
        changed = true;
    }
    changed
}

/// `if (c) { x = a; } else { x = b; } return x;` becomes returns in the
/// branches.
fn push_returns_into_branches(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 1;
    while index < stmts.len() {
        let Stmt::Return(Some(Expr::Local(local))) = &stmts[index] else {
            index += 1;
            continue;
        };
        let local = *local;
        let eligible = match &stmts[index - 1] {
            Stmt::If { otherwise, .. } => !otherwise.is_empty(),
            Stmt::Using { .. } | Stmt::Lock { .. } => true,
            Stmt::Try { catches, .. } => catches.is_empty(),
            _ => false,
        };
        if !eligible {
            index += 1;
            continue;
        }
        let mut candidate = stmts[index - 1].clone();
        if returns_into(&mut candidate, local) {
            stmts[index - 1] = candidate;
            stmts.remove(index);
            changed = true;
        } else {
            index += 1;
        }
    }
    changed
}

/// Turns the final assignments of a local in every branch into returns of
/// the value; fails, leaving nothing changed, when a branch ends otherwise.
fn returns_into(stmt: &mut Stmt, local: u16) -> bool {
    // The blocks that must each end by returning.
    let mut blocks: Vec<Vec<Stmt>> = match stmt {
        Stmt::If {
            then, otherwise, ..
        } => {
            if otherwise.is_empty() {
                return false;
            }
            vec![then.clone(), otherwise.clone()]
        }
        Stmt::Using { body, .. } | Stmt::Lock { body, .. } => vec![body.clone()],
        Stmt::Try { body, catches, .. } if catches.is_empty() => vec![body.clone()],
        _ => return false,
    };
    for block in &mut blocks {
        let Some(last) = block.last_mut() else {
            return false;
        };
        if last.ends_flow() {
            continue;
        }
        match last {
            Stmt::Expr(Expr::Assign(target, value)) if **target == Expr::Local(local) => {
                let value = (**value).clone();
                *last = Stmt::Return(Some(value));
            }
            Stmt::If { .. } | Stmt::Using { .. } | Stmt::Lock { .. } | Stmt::Try { .. } => {
                if !returns_into(last, local) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    let mut blocks = blocks.into_iter();
    match stmt {
        Stmt::If {
            then, otherwise, ..
        } => {
            *then = blocks.next().unwrap_or_default();
            *otherwise = blocks.next().unwrap_or_default();
        }
        Stmt::Using { body, .. } | Stmt::Lock { body, .. } | Stmt::Try { body, .. } => {
            *body = blocks.next().unwrap_or_default();
        }
        _ => {}
    }
    true
}

/// How often a sub-expression matching the predicate occurs in the
/// statement's own expressions (not the nested statements').
fn count_in_stmt(stmt: &Stmt, matches: &dyn Fn(&Expr) -> bool) -> usize {
    let mut count = 0;
    for expr in head_exprs(stmt) {
        count += expr.count(matches);
    }
    let mut nested = 0;
    for block in stmt.blocks() {
        for inner in block {
            inner.walk_exprs(&mut |e| {
                if matches(e) {
                    nested += 1;
                }
            });
        }
    }
    if nested > 0 {
        return usize::MAX;
    }
    count
}

/// The expressions a statement evaluates itself, in order.
fn head_exprs(stmt: &Stmt) -> Vec<&Expr> {
    match stmt {
        Stmt::Expr(expr) | Stmt::YieldReturn(expr) => vec![expr],
        Stmt::Declare {
            value: Some(value), ..
        }
        | Stmt::Return(Some(value))
        | Stmt::Throw(Some(value)) => vec![value],
        Stmt::If { condition, .. } => vec![condition],
        Stmt::Switch { value, .. } => vec![value],
        Stmt::ForEach { source, .. } => vec![source],
        Stmt::Using { resource, .. } => vec![resource],
        Stmt::Lock { target, .. } | Stmt::Fixed { init: target, .. } => vec![target],
        _ => Vec::new(),
    }
}

fn head_exprs_mut(stmt: &mut Stmt) -> Vec<&mut Expr> {
    match stmt {
        Stmt::Expr(expr) | Stmt::YieldReturn(expr) => vec![expr],
        Stmt::Declare {
            value: Some(value), ..
        }
        | Stmt::Return(Some(value))
        | Stmt::Throw(Some(value)) => vec![value],
        Stmt::If { condition, .. } => vec![condition],
        Stmt::Switch { value, .. } => vec![value],
        Stmt::ForEach { source, .. } => vec![source],
        Stmt::Using { resource, .. } => vec![resource],
        Stmt::Lock { target, .. } | Stmt::Fixed { init: target, .. } => vec![target],
        _ => Vec::new(),
    }
}

/// Whether the first thing the statement evaluates that could have a side
/// effect, in C# evaluation order, is the matching sub-expression.
fn first_evaluated(stmt: &Stmt, matches: &dyn Fn(&Expr) -> bool) -> bool {
    let Some(head) = head_exprs(stmt).into_iter().next() else {
        return false;
    };
    let mut order = Vec::new();
    evaluation_order(head, &mut order);
    for expr in order {
        if matches(expr) {
            return true;
        }
        // A conditional evaluated first is a branch the value would have
        // to cross; it stays where it was computed.
        if !expr.is_pure() || matches!(expr, Expr::Conditional(..)) {
            return false;
        }
    }
    false
}

/// The leaves and calls of an expression in the order C# evaluates them.
fn evaluation_order<'e>(expr: &'e Expr, out: &mut Vec<&'e Expr>) {
    match expr {
        Expr::Assign(target, value) | Expr::Compound(_, target, value) => {
            // The target's receiver and indices come first, then the value.
            match target.as_ref() {
                Expr::Field {
                    receiver: Some(receiver),
                    ..
                }
                | Expr::Property {
                    receiver: Some(receiver),
                    ..
                } => evaluation_order(receiver, out),
                Expr::Index { array, indices } => {
                    evaluation_order(array, out);
                    for index in indices {
                        evaluation_order(index, out);
                    }
                }
                Expr::Indexer { receiver, args } => {
                    evaluation_order(receiver, out);
                    for arg in args {
                        evaluation_order(arg, out);
                    }
                }
                Expr::Unary(UnOp::Deref, inner) => evaluation_order(inner, out),
                _ => {}
            }
            evaluation_order(value, out);
            out.push(expr);
        }
        Expr::Call { receiver, args, .. } => {
            if let Some(receiver) = receiver {
                evaluation_order(receiver, out);
            }
            for arg in args {
                evaluation_order(arg, out);
            }
            out.push(expr);
        }
        Expr::New { args, .. } => {
            for arg in args {
                evaluation_order(arg, out);
            }
            out.push(expr);
        }
        Expr::With { source, .. } => {
            evaluation_order(source, out);
            out.push(expr);
        }
        Expr::Binary(_, left, right) | Expr::Compare { left, right, .. } => {
            evaluation_order(left, out);
            evaluation_order(right, out);
            out.push(expr);
        }
        Expr::Conditional(condition, a, b) => {
            evaluation_order(condition, out);
            evaluation_order(a, out);
            evaluation_order(b, out);
            out.push(expr);
        }
        Expr::Index { array, indices } => {
            evaluation_order(array, out);
            for index in indices {
                evaluation_order(index, out);
            }
            out.push(expr);
        }
        Expr::Indexer { receiver, args } => {
            evaluation_order(receiver, out);
            for arg in args {
                evaluation_order(arg, out);
            }
            out.push(expr);
        }
        Expr::Field {
            receiver: Some(receiver),
            ..
        }
        | Expr::Property {
            receiver: Some(receiver),
            ..
        } => {
            evaluation_order(receiver, out);
            out.push(expr);
        }
        Expr::Unary(_, inner)
        | Expr::Cast(_, inner)
        | Expr::CheckedCast(_, inner)
        | Expr::OperatorCast(_, inner)
        | Expr::As(_, inner)
        | Expr::Is(_, inner)
        | Expr::IsPattern(_, inner, _)
        | Expr::Box(_, inner)
        | Expr::Length(inner)
        | Expr::Checked(inner)
        | Expr::MaybeNull(inner)
        | Expr::Await(inner) => {
            evaluation_order(inner, out);
            out.push(expr);
        }
        Expr::NewArray { size, items, .. } => {
            evaluation_order(size, out);
            if let Some(items) = items {
                for item in items {
                    evaluation_order(item, out);
                }
            }
            out.push(expr);
        }
        Expr::Delegate {
            target: Some(target),
            ..
        } => {
            evaluation_order(target, out);
            out.push(expr);
        }
        Expr::Tuple(items) => {
            for item in items {
                evaluation_order(item, out);
            }
            out.push(expr);
        }
        Expr::Interpolated(parts) => {
            for part in parts {
                if let Interpolation::Hole(hole, _) = part {
                    evaluation_order(hole, out);
                }
            }
            out.push(expr);
        }
        _ => out.push(expr),
    }
}

/// Replaces the matching sub-expression in the statement's own expressions.
fn replace_in_stmt_head(stmt: &mut Stmt, matches: &dyn Fn(&Expr) -> bool, with: &Expr) {
    for expr in head_exprs_mut(stmt) {
        expr.map(&mut |e| {
            if matches(e) {
                *e = with.clone();
            }
        });
    }
}

/// `x = o as T; if (x != null) { ... }` becomes `if (o is T x) { ... }`, and
/// `if (o is T) { x = (T)o; ... }` the same.
fn fold_is_patterns(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index + 1 < stmts.len() {
        let Some((target, value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let Expr::As(ty, _) = value else {
            index += 1;
            continue;
        };
        // A slot holding the test gets a local to be the pattern variable.
        let local = match target {
            Expr::Local(local) => *local,
            Expr::Slot(slot) => {
                let slot = *slot;
                let local = typer.new_local(ty.clone());
                for stmt in stmts.iter_mut().skip(index) {
                    stmt.map_exprs(&mut |e| {
                        if *e == Expr::Slot(slot) {
                            *e = Expr::Local(local);
                        }
                    });
                }
                local
            }
            _ => {
                index += 1;
                continue;
            }
        };
        let Some((_, value)) = assignment(&stmts[index]) else {
            unreachable!()
        };
        let Expr::As(ty, source) = value else {
            unreachable!()
        };
        let (ty, source) = (ty.clone(), (**source).clone());
        let Stmt::If { condition, .. } = &mut stmts[index + 1] else {
            index += 1;
            continue;
        };
        let is_local = |e: &Expr| *e == Expr::Local(local);
        // The test has to be the first thing the condition looks at.
        let mut order = Vec::new();
        evaluation_order(condition, &mut order);
        let Some(first) = order.first() else {
            index += 1;
            continue;
        };
        let compare = |e: &Expr| -> Option<bool> {
            if let Expr::Compare {
                op, left, right, ..
            } = e
                && is_local(left)
                && **right == Expr::Null
            {
                return match op {
                    Cmp::Ne => Some(true),
                    Cmp::Eq => Some(false),
                    _ => None,
                };
            }
            None
        };
        // Find the enclosing comparison of the first leaf.
        let mut found = None;
        condition.walk(&mut |e| {
            if found.is_none()
                && let Some(positive) = compare(e)
                && let Expr::Compare { left, .. } = e
                && std::ptr::eq(left.as_ref(), *first)
            {
                found = Some((e.clone(), positive));
            }
        });
        let Some((old, positive)) = found else {
            index += 1;
            continue;
        };
        // Read after the `if`, the variable has to be definitely assigned
        // there: the way the test fails has to leave.
        let read_after = stmts[index + 2..]
            .iter()
            .any(|stmt| count_in_stmt_deep(stmt, &is_local) > 0);
        if read_after {
            let Stmt::If {
                condition,
                then,
                otherwise,
            } = &stmts[index + 1]
            else {
                unreachable!()
            };
            let failing = if positive { otherwise } else { then };
            if *condition != old || !failing.last().is_some_and(Stmt::ends_flow) {
                index += 1;
                continue;
            }
        }
        let Stmt::If { condition, .. } = &mut stmts[index + 1] else {
            unreachable!()
        };
        let pattern = Expr::IsPattern(ty, Box::new(source), Box::new(Expr::Local(local)));
        let replacement = if positive {
            pattern
        } else {
            Expr::unary(UnOp::Not, pattern)
        };
        condition.map(&mut |e| {
            if *e == old {
                *e = replacement.clone();
            }
        });
        stmts.remove(index);
        changed = true;
    }
    // `if (o is T) { x = (T)o; ... }`
    for stmt in stmts.iter_mut() {
        let Stmt::If {
            condition, then, ..
        } = stmt
        else {
            continue;
        };
        let Expr::Is(ty, source) = condition else {
            continue;
        };
        let first = then.iter().position(|stmt| !matches!(stmt, Stmt::Label(_)));
        let Some(first) = first else {
            continue;
        };
        let Some((Expr::Local(local), Expr::Cast(cast_ty, cast_source))) = assignment(&then[first])
        else {
            continue;
        };
        if cast_ty != ty || cast_source != source {
            continue;
        }
        let local = *local;
        let pattern = Expr::IsPattern(ty.clone(), source.clone(), Box::new(Expr::Local(local)));
        *condition = pattern;
        then.remove(first);
        changed = true;
    }
    changed
}

/// `DefaultInterpolatedStringHandler` calls back into `$"..."`.
fn fold_string_handlers(resolver: Resolver<'_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let Some((target, value)) = assignment(&stmts[index]) else {
            index += 1;
            continue;
        };
        let Expr::New { ctor, .. } = value else {
            index += 1;
            continue;
        };
        if !ctor.name.eq(".ctor")
            || !is_named(
                resolver,
                &ctor.declaring,
                "DefaultInterpolatedStringHandler",
            )
        {
            index += 1;
            continue;
        }
        let handler = target.clone();
        let mut parts = Vec::new();
        let mut at = index + 1;
        while at < stmts.len() {
            let Stmt::Expr(Expr::Call {
                method,
                receiver: Some(receiver),
                args,
            }) = &stmts[at]
            else {
                break;
            };
            if **receiver != handler {
                break;
            }
            match method.name.as_str() {
                "AppendLiteral" if args.len() == 1 => {
                    if let Expr::Str(text) = &args[0] {
                        parts.push(Interpolation::Text(text.clone()));
                    } else {
                        break;
                    }
                }
                "AppendFormatted" if !args.is_empty() => {
                    let format = args.iter().skip(1).find_map(|arg| match arg {
                        Expr::Str(text) => Some(text.clone()),
                        _ => None,
                    });
                    let alignment = args.iter().skip(1).find_map(|arg| match arg {
                        Expr::Int(n) => Some(*n),
                        _ => None,
                    });
                    let spec = match (alignment, format) {
                        (Some(a), Some(f)) => Some(format!("{a}:{f}")),
                        (Some(a), None) => Some(a.to_string()),
                        (None, Some(f)) => Some(format!(":{f}")),
                        (None, None) => None,
                    };
                    parts.push(Interpolation::Hole(Box::new(args[0].clone()), spec));
                }
                _ => break,
            }
            at += 1;
        }
        if at >= stmts.len() {
            index += 1;
            continue;
        }
        // The consumer reads `handler.ToStringAndClear()`.
        let is_final = |e: &Expr| {
            matches!(e, Expr::Call { method, receiver: Some(receiver), .. }
                if method.name == "ToStringAndClear" && **receiver == handler)
        };
        // Or `string.Create(provider, buffer, ref handler)`, which takes the
        // interpolated string itself.
        let is_create = |e: &Expr| {
            matches!(e, Expr::Call { method, receiver: None, args, .. }
                if method.name == "Create"
                    && args.len() == 3
                    && matches!(&args[2], Expr::Unary(UnOp::AddressOf, inner) if **inner == handler))
        };
        let interpolated = Expr::Interpolated(parts);
        if count_in_stmt(&stmts[at], &is_final) == 1 {
            let mut consumer = stmts[at].clone();
            replace_in_stmt_head(&mut consumer, &is_final, &interpolated);
            stmts[at] = consumer;
        } else if count_in_stmt(&stmts[at], &is_create) == 1 {
            let mut buffer = None;
            stmts[at].map_exprs(&mut |e| {
                if is_create(e)
                    && let Expr::Call { args, .. } = e
                {
                    args[2] = interpolated.clone();
                    buffer = Some(args[1].clone());
                }
            });
            stmts.drain(index..at);
            // The buffer, `stackalloc` through copies, goes into the call.
            let mut at = index;
            while let Some(Expr::Local(local)) = buffer.clone()
                && at > 0
                && let Some((Expr::Local(assigned), value)) = assignment(&stmts[at - 1])
                && *assigned == local
                && stmts
                    .iter()
                    .map(|stmt| count_in_stmt_deep(stmt, &|e| *e == Expr::Local(local)))
                    .sum::<usize>()
                    == 2
            {
                let value = value.clone();
                stmts[at].map_exprs(&mut |e| {
                    if *e == Expr::Local(local) {
                        *e = value.clone();
                    }
                });
                stmts.remove(at - 1);
                at -= 1;
                buffer = Some(value);
            }
            changed = true;
            index += 1;
            continue;
        } else {
            index += 1;
            continue;
        }
        stmts.drain(index..at);
        changed = true;
    }
    changed
}

fn is_named(resolver: Resolver<'_>, ty: &TypeSig, name: &str) -> bool {
    match ty {
        TypeSig::ValueType(token) | TypeSig::Class(token) => resolver
            .raw_name(*token)
            .is_some_and(|raw| raw.rsplit(['.', '/']).next() == Some(name)),
        _ => false,
    }
}

/// `while (true) { if (!c) break; ... }` is `while (c) { ... }`, a trailing
/// `continue` says nothing, and `x = 0; while (c) { ...; x++; }` is a `for`.
fn shape_loops(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::While { condition, body } => {
                changed |= strip_trailing_continue(body);
                if *condition == Expr::Bool(true) {
                    let first = body.iter().position(|s| !matches!(s, Stmt::Label(_)));
                    if let Some(first) = first
                        && let Stmt::If {
                            condition: inner,
                            then,
                            otherwise,
                        } = &body[first]
                        && otherwise.is_empty()
                        && matches!(single(then), Some(Stmt::Break))
                        && first == 0
                    {
                        *condition = negate(inner.clone());
                        body.remove(first);
                        changed = true;
                    }
                }
            }
            Stmt::DoWhile { body, .. } => {
                changed |= strip_trailing_continue(body);
            }
            Stmt::For { body, .. } | Stmt::ForEach { body, .. } => {
                changed |= strip_trailing_continue(body);
            }
            _ => {}
        }
        if let Stmt::While { body, .. }
        | Stmt::DoWhile { body, .. }
        | Stmt::For { body, .. }
        | Stmt::ForEach { body, .. } = stmt
        {
            changed |= invert_continue(body);
        }
    }
    // `for`: an initializer just before, a step at the end of the body.
    let mut index = 1;
    while index < stmts.len() {
        let Stmt::While { condition, body } = &stmts[index] else {
            index += 1;
            continue;
        };
        if *condition == Expr::Bool(true) {
            index += 1;
            continue;
        }
        let Some((Expr::Local(local), _)) = assignment(&stmts[index - 1]) else {
            index += 1;
            continue;
        };
        let local = *local;
        let mentions = |e: &Expr| *e == Expr::Local(local);
        if condition.count(&mentions) == 0 {
            index += 1;
            continue;
        }
        let step_is_of_local = |stmt: &Stmt| match stmt {
            Stmt::Expr(Expr::Increment { target, .. }) => **target == Expr::Local(local),
            Stmt::Expr(Expr::Compound(_, target, _)) => **target == Expr::Local(local),
            Stmt::Expr(Expr::Assign(target, _)) => **target == Expr::Local(local),
            _ => false,
        };
        let has_continue = body.iter().any(contains_continue);
        // A `for` variable is gone after the loop: a compiler's local
        // reused for something else starts over with a write.
        let next_mention = stmts[index + 1..]
            .iter()
            .find(|stmt| count_in_stmt_deep(stmt, &mentions) > 0);
        let used_after = next_mention.is_some_and(|stmt| {
            !matches!(assignment(stmt), Some((Expr::Local(target), value))
                if *target == local && value.count(&mentions) == 0)
        });
        // Reused after the loop: the loop's variable is a variable of its
        // own, as the source's was.
        let reused = next_mention.is_some();
        if !body.last().is_some_and(step_is_of_local) || has_continue || used_after {
            index += 1;
            continue;
        }
        let Stmt::While {
            condition,
            mut body,
        } = stmts.remove(index)
        else {
            unreachable!()
        };
        let Some(Stmt::Expr(step)) = body.pop() else {
            unreachable!()
        };
        let mut initializer = stmts.remove(index - 1);
        let (mut condition, mut step) = (condition, step);
        if reused && let Some(ty) = typer.type_of(&Expr::Local(local)) {
            let fresh = Expr::Local(typer.new_local(ty));
            let mut rename = |e: &mut Expr| {
                if *e == Expr::Local(local) {
                    *e = fresh.clone();
                }
            };
            initializer.map_exprs(&mut rename);
            condition.map(&mut rename);
            step.map(&mut rename);
            for stmt in &mut body {
                stmt.map_exprs(&mut rename);
            }
        }
        stmts.insert(
            index - 1,
            Stmt::For {
                initializer: Some(Box::new(initializer)),
                condition,
                step: Some(step),
                body,
            },
        );
        changed = true;
    }
    changed
}

/// A `continue` that ends a loop body says nothing, inside a `try` or
/// `using` that ends the body included.
fn strip_trailing_continue(body: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    while matches!(body.last(), Some(Stmt::Continue)) {
        body.pop();
        changed = true;
    }
    match body.last_mut() {
        Some(Stmt::Try { body: inner, .. }) | Some(Stmt::Using { body: inner, .. }) => {
            changed |= strip_trailing_continue(inner);
        }
        _ => {}
    }
    changed
}

/// `if (c) { continue; } rest...` at the end of a loop body is
/// `if (!c) { rest... }`.
fn invert_continue(body: &mut Vec<Stmt>) -> bool {
    let Some(position) = body.iter().position(|stmt| {
        matches!(stmt, Stmt::If { then, otherwise, .. }
            if otherwise.is_empty() && matches!(single(then), Some(Stmt::Continue)))
    }) else {
        return false;
    };
    if position + 1 >= body.len() {
        return false;
    }
    let rest: Vec<Stmt> = body.drain(position + 1..).collect();
    if rest.iter().any(|stmt| matches!(stmt, Stmt::Label(_))) {
        body.extend(rest);
        return false;
    }
    let Some(Stmt::If { condition, .. }) = body.pop() else {
        unreachable!()
    };
    body.push(Stmt::If {
        condition: negate(condition),
        then: rest,
        otherwise: Vec::new(),
    });
    true
}

fn contains_continue(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Continue => true,
        Stmt::While { .. } | Stmt::DoWhile { .. } | Stmt::For { .. } | Stmt::ForEach { .. } => {
            false
        }
        other => other
            .blocks()
            .iter()
            .any(|block| block.iter().any(contains_continue)),
    }
}

/// Enumerator loops back into `foreach`.
fn fold_foreach(typer: &Typer<'_, '_>, stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 1;
    while index < stmts.len() {
        // `e = source.GetEnumerator(); try { while (e.MoveNext()) { x = e.Current; ... } } finally { e.Dispose(); }`
        let Some((
            Expr::Local(enumerator),
            Expr::Call {
                method,
                receiver: Some(source),
                args,
            },
        )) = assignment(&stmts[index - 1])
        else {
            index += 1;
            continue;
        };
        // `await foreach`: the async enumerator, `await MoveNextAsync()`,
        // `await DisposeAsync()`.
        let asynchronous = method.name == "GetAsyncEnumerator"
            && args.iter().all(|arg| matches!(arg, Expr::Default(_)));
        if !(asynchronous || method.name == "GetEnumerator" && args.is_empty()) {
            index += 1;
            continue;
        }
        let (enumerator, source) = (*enumerator, (**source).clone());
        let disposes = |finally: &[Stmt]| {
            if asynchronous {
                is_async_dispose_of(finally, enumerator)
            } else {
                is_dispose_of(finally, enumerator)
            }
        };
        let loop_stmt = match &stmts[index] {
            Stmt::Try {
                body,
                catches,
                finally: Some(finally),
            } if catches.is_empty() && disposes(finally) => match single(body) {
                Some(inner @ Stmt::While { .. }) => inner.clone(),
                _ => {
                    index += 1;
                    continue;
                }
            },
            inner @ Stmt::While { .. } => inner.clone(),
            _ => {
                index += 1;
                continue;
            }
        };
        let Stmt::While {
            condition,
            mut body,
        } = loop_stmt
        else {
            unreachable!()
        };
        let is_move_next = if asynchronous {
            matches!(&condition, Expr::Await(inner)
                if matches!(inner.as_ref(), Expr::Call { method, receiver: Some(receiver), .. }
                    if method.name == "MoveNextAsync" && **receiver == Expr::Local(enumerator)))
        } else {
            matches!(&condition, Expr::Call { method, receiver: Some(receiver), .. }
                if method.name == "MoveNext" && **receiver == Expr::Local(enumerator))
        };
        if !is_move_next {
            index += 1;
            continue;
        }
        let first = body.iter().position(|s| !matches!(s, Stmt::Label(_)));
        let Some(first) = first else {
            index += 1;
            continue;
        };
        let is_current_read = |value: &Expr| -> bool {
            let inner = match value {
                Expr::Cast(_, inner) => inner.as_ref(),
                other => other,
            };
            matches!(inner, Expr::Property { receiver: Some(receiver), name, .. }
                if name == "Current" && **receiver == Expr::Local(enumerator))
        };
        let current = match &body[first] {
            Stmt::Expr(Expr::Assign(target, value)) => match (target.as_ref(), value.as_ref()) {
                (Expr::Local(item), value) if is_current_read(value) => Some(*item),
                _ => None,
            },
            _ => None,
        };
        let item = match current {
            Some(item) => {
                body.remove(first);
                item
            }
            None => {
                // The element is read straight off the enumerator, in the
                // first statement of the body: give it a local of its own.
                // Read deeper in, the loop stays an enumerator loop.
                let is_current = |e: &Expr| is_current_read(e);
                let mut reads = 0;
                let mut item_type = None;
                for stmt in &body {
                    stmt.walk_exprs(&mut |e| {
                        if is_current(e) {
                            reads += 1;
                            if item_type.is_none() {
                                item_type = typer.type_of(e);
                            }
                        }
                    });
                }
                let Some(item_type) = item_type else {
                    index += 1;
                    continue;
                };
                if reads == 0 || count_in_stmt(&body[first], &is_current) != reads {
                    index += 1;
                    continue;
                }
                let item = typer.new_local(item_type);
                for stmt in &mut body {
                    stmt.map_exprs(&mut |e| {
                        if is_current(e) {
                            *e = Expr::Local(item);
                        }
                    });
                }
                item
            }
        };
        let uses_enumerator = body
            .iter()
            .any(|s| count_in_stmt_deep(s, &|e| *e == Expr::Local(enumerator)) > 0);
        if uses_enumerator {
            index += 1;
            continue;
        }
        stmts.remove(index);
        stmts[index - 1] = Stmt::ForEach {
            local: item,
            // `await` around the source says `await foreach`.
            source: if asynchronous {
                Expr::Await(Box::new(source))
            } else {
                source
            },
            body,
        };
        changed = true;
    }
    // Arrays: `arr2 = arr; for (i = 0; i < arr2.Length; i++) { x = arr2[i]; ... }`
    let mut index = 0;
    while index < stmts.len() {
        let Stmt::For {
            initializer: Some(initializer),
            condition,
            step: Some(step),
            body,
        } = &stmts[index]
        else {
            index += 1;
            continue;
        };
        let Some((Expr::Local(counter), Expr::Int(0))) = assignment(initializer) else {
            index += 1;
            continue;
        };
        let counter = *counter;
        let Expr::Compare {
            op: Cmp::Lt,
            left,
            right,
            ..
        } = condition
        else {
            index += 1;
            continue;
        };
        let (Expr::Local(left_local), Expr::Length(array)) = (left.as_ref(), right.as_ref()) else {
            index += 1;
            continue;
        };
        if *left_local != counter || !array.is_pure() {
            index += 1;
            continue;
        }
        let array = (**array).clone();
        let is_step = matches!(step, Expr::Increment { target, delta: 1, .. } if **target == Expr::Local(counter))
            || matches!(step, Expr::Compound(BinOp::Add, target, value) if **target == Expr::Local(counter) && **value == Expr::Int(1));
        if !is_step {
            index += 1;
            continue;
        }
        let first = body.iter().position(|s| !matches!(s, Stmt::Label(_)));
        let Some(first) = first else {
            index += 1;
            continue;
        };
        let Some((
            Expr::Local(item),
            Expr::Index {
                array: indexed,
                indices,
            },
        )) = assignment(&body[first])
        else {
            index += 1;
            continue;
        };
        if **indexed != array || indices.len() != 1 || indices[0] != Expr::Local(counter) {
            index += 1;
            continue;
        }
        let item = *item;
        let mut body = body.clone();
        body.remove(first);
        let counter_used = body
            .iter()
            .any(|s| count_in_stmt_deep(s, &|e| *e == Expr::Local(counter)) > 0);
        if counter_used {
            index += 1;
            continue;
        }
        // The array was copied into a temporary just before.
        let mut source = array.clone();
        let mut remove_copy = false;
        if let Expr::Local(copy) = &array
            && index > 0
            && let Some((Expr::Local(target), value)) = assignment(&stmts[index - 1])
            && target == copy
        {
            let later_uses = stmts[index + 1..]
                .iter()
                .chain(body.iter())
                .any(|s| count_in_stmt_deep(s, &|e| *e == Expr::Local(*copy)) > 0);
            if !later_uses {
                source = value.clone();
                remove_copy = true;
            }
        }
        stmts[index] = Stmt::ForEach {
            local: item,
            source,
            body,
        };
        if remove_copy {
            stmts.remove(index - 1);
        } else {
            index += 1;
        }
        changed = true;
    }
    changed
}

pub(crate) fn count_in_stmt_deep(stmt: &Stmt, matches: &dyn Fn(&Expr) -> bool) -> usize {
    let mut count = 0;
    stmt.walk_exprs(&mut |e| {
        if matches(e) {
            count += 1;
        }
    });
    count
}

/// Whether a `finally` only disposes the local: directly, after a null
/// check, or after asking whether it is disposable at all.
fn is_dispose_of(finally: &[Stmt], local: u16) -> bool {
    is_dispose_of_kind(finally, local, true)
}

/// The same, choosing whether a `finally` that first asks `is IDisposable`
/// counts: `foreach` absorbs that shape, `using` cannot.
/// Whether a `finally` only awaits the local's `DisposeAsync`, after a null
/// check or not.
fn is_async_dispose_of(finally: &[Stmt], local: u16) -> bool {
    let real: Vec<&Stmt> = finally
        .iter()
        .filter(|s| !matches!(s, Stmt::Label(_)))
        .collect();
    let disposes = |stmt: &Stmt| {
        matches!(stmt, Stmt::Expr(Expr::Await(inner))
            if matches!(inner.as_ref(), Expr::Call { method, receiver: Some(receiver), .. }
                if method.name == "DisposeAsync" && **receiver == Expr::Local(local)))
    };
    match real.as_slice() {
        [stmt] if disposes(stmt) => true,
        [
            Stmt::If {
                condition,
                then,
                otherwise,
            },
        ] => {
            otherwise.is_empty()
                && matches!(condition, Expr::Compare { op: Cmp::Ne, left, right, .. }
                    if **left == Expr::Local(local) && **right == Expr::Null)
                && single(then).is_some_and(disposes)
        }
        _ => false,
    }
}

fn is_dispose_of_kind(finally: &[Stmt], local: u16, typecheck: bool) -> bool {
    let real: Vec<&Stmt> = finally
        .iter()
        .filter(|s| !matches!(s, Stmt::Label(_)))
        .collect();
    let is_local = |e: &Expr| match e {
        Expr::Local(at) => *at == local,
        Expr::Cast(_, inner) | Expr::As(_, inner) | Expr::MaybeNull(inner) => {
            matches!(inner.as_ref(), Expr::Local(at) if *at == local)
        }
        _ => false,
    };
    let is_dispose = |s: &Stmt, receiver_ok: &dyn Fn(&Expr) -> bool| {
        matches!(s, Stmt::Expr(Expr::Call { method, receiver: Some(receiver), .. })
            if method.name == "Dispose" && receiver_ok(receiver))
    };
    match real.as_slice() {
        [] => true,
        [stmt] => {
            if is_dispose(stmt, &is_local) {
                return true;
            }
            if let Stmt::If {
                condition,
                then,
                otherwise,
            } = stmt
                && otherwise.is_empty()
            {
                // `if (e != null) e.Dispose();`
                if matches!(condition, Expr::Compare { op: Cmp::Ne, left, right, .. } if is_local(left) && **right == Expr::Null)
                    && single(then).is_some_and(|s| is_dispose(s, &is_local))
                {
                    return true;
                }
                if !typecheck {
                    return false;
                }
                // `if (e is IDisposable d) d.Dispose();`
                if let Expr::IsPattern(_, source, bound) = condition
                    && is_local(source)
                    && single(then).is_some_and(|s| is_dispose(s, &|r| r == bound.as_ref()))
                {
                    return true;
                }
                // `if (e is IDisposable) (e as IDisposable).Dispose();`
                if let Expr::Is(_, source) = condition
                    && is_local(source)
                    && single(then).is_some_and(|s| is_dispose(s, &is_local))
                {
                    return true;
                }
            }
            false
        }
        // `IDisposable d = e as IDisposable; if (d != null) d.Dispose();`
        [first, second] => {
            if !typecheck {
                return false;
            }
            let Some((disposable, value)) = assignment(first) else {
                return false;
            };
            if !matches!(disposable, Expr::Local(_) | Expr::Slot(_)) || !is_local(value) {
                return false;
            }
            let is_disposable = |e: &Expr| e == disposable;
            matches!(second, Stmt::If { condition, then, otherwise }
                if otherwise.is_empty()
                    && matches!(condition, Expr::Compare { op: Cmp::Ne, left, right, .. } if is_disposable(left) && **right == Expr::Null)
                    && single(then).is_some_and(|s| is_dispose(s, &is_disposable)))
        }
        _ => false,
    }
}

/// `x = e; try { ... } finally { x.Dispose(); }` is `using`, and the
/// `Monitor.Enter`/`Exit` pair is `lock`.
fn fold_using_and_lock(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 1;
    while index < stmts.len() {
        let Stmt::Try {
            body,
            catches,
            finally: Some(finally),
        } = &stmts[index]
        else {
            index += 1;
            continue;
        };
        if !catches.is_empty() {
            index += 1;
            continue;
        }
        if let Some((Expr::Local(local), value)) = assignment(&stmts[index - 1])
            && (is_dispose_of_kind(finally, *local, false) || is_async_dispose_of(finally, *local))
        {
            let local = *local;
            // `await` around the resource says `await using`.
            let resource = if is_async_dispose_of(finally, local) {
                Expr::Await(Box::new(value.clone()))
            } else {
                value.clone()
            };
            let body = body.clone();
            stmts[index] = Stmt::Using {
                local: Some(local),
                resource,
                body,
            };
            stmts.remove(index - 1);
            changed = true;
            continue;
        }
        // lock: `flag = false; try { Monitor.Enter(x, ref flag); ... } finally { if (flag) Monitor.Exit(x); }`
        if let Some((Expr::Local(flag), Expr::Bool(false))) = assignment(&stmts[index - 1]) {
            let flag = *flag;
            let first = body.iter().position(|s| !matches!(s, Stmt::Label(_)));
            if let Some(first) = first
                && let Stmt::Expr(Expr::Call { method, args, .. }) = &body[first]
                && method.name == "Enter"
                && args.len() == 2
                && matches!(&args[1], Expr::Unary(UnOp::AddressOf, inner) if **inner == Expr::Local(flag))
            {
                let target = args[0].clone();
                let mut body = body.clone();
                body.remove(first);
                stmts[index] = Stmt::Lock { target, body };
                stmts.remove(index - 1);
                changed = true;
                continue;
            }
        }
        index += 1;
    }
    changed
}

/// `if (a) { if (b) { X } }` is `if (a && b) { X }`.
fn merge_nested_ifs(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    // `if (c) { } else { A }` is `if (!c) { A }`.
    for stmt in stmts.iter_mut() {
        if let Stmt::If {
            condition,
            then,
            otherwise,
        } = stmt
            && then.is_empty()
            && !otherwise.is_empty()
        {
            *condition = negate(condition.clone());
            std::mem::swap(then, otherwise);
            changed = true;
        }
    }
    for stmt in stmts.iter_mut() {
        let Stmt::If {
            condition,
            then,
            otherwise,
        } = stmt
        else {
            continue;
        };
        // A label on the inner `if` is somewhere jumps land: it stays.
        if !otherwise.is_empty() || then.iter().any(|stmt| matches!(stmt, Stmt::Label(_))) {
            continue;
        }
        let Some(Stmt::If {
            condition: inner,
            then: inner_then,
            otherwise: inner_otherwise,
        }) = single(then)
        else {
            continue;
        };
        if !inner_otherwise.is_empty() {
            continue;
        }
        let merged = Expr::binary(BinOp::LogicalAnd, condition.clone(), inner.clone());
        let inner_then = inner_then.clone();
        *condition = merged;
        *then = inner_then;
        changed = true;
    }
    changed
}

/// `if (c) { return; } else { X }` reads better as `if (c) { return; } X`.
fn drop_else_after_exit(stmts: &mut Vec<Stmt>) -> bool {
    let mut changed = false;
    let mut index = 0;
    while index < stmts.len() {
        let Stmt::If {
            then, otherwise, ..
        } = &mut stmts[index]
        else {
            index += 1;
            continue;
        };
        if otherwise.is_empty() {
            index += 1;
            continue;
        }
        if !then.last().is_some_and(Stmt::ends_flow) {
            // `if (c) { A } else { return x; } B` with `B` ending the way
            // `A` would go on: `B` belongs after `A`, inside the `if`, and
            // the exit follows. When `B` merely returns, the `if` is
            // turned around instead: `if (!c) { return x; } A; B`.
            if !otherwise.last().is_some_and(Stmt::ends_flow)
                || matches!(single(otherwise), Some(Stmt::If { .. }))
            {
                index += 1;
                continue;
            }
            let (head, rest) = stmts.split_at_mut(index + 1);
            let joins = !rest.is_empty()
                && rest.last().is_some_and(Stmt::ends_flow)
                && !matches!(rest.last(), Some(Stmt::Return(None)))
                && !rest.iter().any(|stmt| matches!(stmt, Stmt::Label(_)));
            let Some(Stmt::If {
                condition,
                then,
                otherwise,
            }) = head.last_mut()
            else {
                unreachable!("the `if` stays put");
            };
            if joins {
                then.extend(rest.iter().cloned());
                stmts.truncate(index + 1);
            } else {
                *condition = negate(condition.clone());
                std::mem::swap(then, otherwise);
            }
            let Stmt::If { otherwise, .. } = &mut stmts[index] else {
                unreachable!("the `if` stays put");
            };
            let rest = std::mem::take(otherwise);
            let at = index + 1;
            for (offset, stmt) in rest.into_iter().enumerate() {
                stmts.insert(at + offset, stmt);
            }
            changed = true;
            index += 1;
            continue;
        }
        // Keep `else if` chains where both sides exit: they read as a chain.
        if matches!(single(otherwise), Some(Stmt::If { .. }))
            && otherwise.last().is_some_and(Stmt::ends_flow)
        {
            index += 1;
            continue;
        }
        let rest = std::mem::take(otherwise);
        let at = index + 1;
        for (offset, stmt) in rest.into_iter().enumerate() {
            stmts.insert(at + offset, stmt);
        }
        changed = true;
        index += 1;
    }
    changed
}

/// `x = x + 1` is `x++`, `x = x + e` is `x += e`.
fn fold_compound(stmts: &mut [Stmt]) -> bool {
    let mut changed = false;
    for stmt in stmts.iter_mut() {
        let Stmt::Expr(expr) = stmt else {
            continue;
        };
        let Expr::Assign(target, value) = expr else {
            continue;
        };
        // `x = T.op_Increment(x)` is `++x`.
        if let Expr::Call {
            method,
            receiver: None,
            args,
        } = value.as_ref()
            && args.len() == 1
            && args[0] == **target
            && target.is_pure()
            && target.is_place()
            && let Some(delta) = match method.name.as_str() {
                "op_Increment" => Some(1),
                "op_Decrement" => Some(-1),
                _ => None,
            }
        {
            *expr = Expr::Increment {
                target: target.clone(),
                delta,
                postfix: false,
            };
            changed = true;
            continue;
        }
        let Expr::Binary(op, left, right) = value.as_ref() else {
            continue;
        };
        if left != target || !target.is_pure() || !target.is_place() {
            continue;
        }
        let op = *op;
        if matches!(op, BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::Coalesce) {
            continue;
        }
        let replacement = match (op, right.as_ref()) {
            (BinOp::Add, Expr::Int(1) | Expr::Long(1)) => Expr::Increment {
                target: target.clone(),
                delta: 1,
                postfix: true,
            },
            (BinOp::Sub, Expr::Int(1) | Expr::Long(1)) => Expr::Increment {
                target: target.clone(),
                delta: -1,
                postfix: true,
            },
            (BinOp::Add, Expr::Float(f, _)) if *f == 1.0 => Expr::Increment {
                target: target.clone(),
                delta: 1,
                postfix: true,
            },
            _ => Expr::Compound(op, target.clone(), right.clone()),
        };
        *expr = replacement;
        changed = true;
    }
    changed
}

/// Slots nothing reads are dropped, and the ones read more than once stay
/// as temporaries.
fn drop_dead_slots(stmts: &mut Vec<Stmt>) {
    let reads = slot_reads(stmts);
    fn prune(stmts: &mut Vec<Stmt>, reads: &HashMap<u32, usize>) {
        let mut index = 0;
        while index < stmts.len() {
            if let Some((target, value)) = assignment(&stmts[index])
                && let Some(slot) = slot_of(target)
                && reads.get(&slot).copied().unwrap_or(0) == 0
            {
                if value.is_pure() {
                    stmts.remove(index);
                    continue;
                }
                let value = value.clone();
                stmts[index] = Stmt::Expr(value);
            }
            for block in stmts[index].blocks_mut() {
                prune(block, reads);
            }
            index += 1;
        }
    }
    prune(stmts, &reads);
}

trait PipeAssignment {
    fn pipe_assignment(self) -> Option<(Expr, Expr)>;
}

impl PipeAssignment for Stmt {
    fn pipe_assignment(self) -> Option<(Expr, Expr)> {
        match self {
            Stmt::Expr(Expr::Assign(target, value)) => Some((*target, *value)),
            _ => None,
        }
    }
}

/// The slot a filter's final `return` reads, plain or compared with zero.
fn returned_slot(stmt: &Stmt) -> Option<u32> {
    match stmt {
        Stmt::Return(Some(Expr::Slot(slot))) => Some(*slot),
        Stmt::Return(Some(Expr::Compare {
            op: Cmp::Ne,
            left,
            right,
            ..
        })) if **right == Expr::Int(0) || **right == Expr::Bool(false) => slot_of(left),
        _ => None,
    }
}

/// Reads the type, variable and condition out of a filter handler.
fn fold_filter(typer: &Typer<'_, '_>, catch: &mut Catch) {
    let Some(Expr::Lambda { body, .. }) = &mut catch.filter else {
        return;
    };
    let Body::Block(stmts) = body.as_mut() else {
        return;
    };
    for _ in 0..2 {
        rewrite_exprs(typer, stmts);
        let reads = Uses {
            slots: slot_reads(stmts),
            locals: HashMap::new(),
            args_written: HashSet::new(),
            gotos: all_goto_counts(stmts),
        };
        simplify_block(typer, stmts, &reads);
        drop_dead_slots(stmts);
    }
    rewrite_exprs(typer, stmts);
    let real: Vec<Stmt> = stmts
        .iter()
        .filter(|s| !matches!(s, Stmt::Label(_)))
        .cloned()
        .collect();
    // `[if (!(ex is T)) { r = false; } else { v = ex as T; r = cond; }; return r;]`,
    // with the test spelled either as `is` or as `as ... == null`, and the
    // `as` possibly held in a slot first.
    let mut real = real;
    if let Some((Expr::Slot(slot), Expr::As(..))) = real.first().and_then(assignment) {
        let slot = *slot;
        let Some((_, value)) = real[0].clone().pipe_assignment() else {
            unreachable!()
        };
        real.remove(0);
        for stmt in &mut real {
            stmt.map_exprs(&mut |e| {
                if *e == Expr::Slot(slot) {
                    *e = value.clone();
                }
            });
        }
    }
    if real.len() == 2
        && let Stmt::If {
            condition,
            then,
            otherwise,
        } = &real[0]
        && matches!(single(then), Some(Stmt::Expr(Expr::Assign(_, value))) if **value == Expr::Bool(false) || **value == Expr::Int(0))
        && let Some(result) = returned_slot(&real[1])
    {
        let mut bound: Option<u16> = None;
        let tested = match condition {
            Expr::Unary(UnOp::Not, inner) => match inner.as_ref() {
                Expr::Is(ty, source) if **source == Expr::CaughtException => Some(ty.clone()),
                Expr::IsPattern(ty, source, target) if **source == Expr::CaughtException => {
                    if let Expr::Local(local) = target.as_ref() {
                        bound = Some(*local);
                    }
                    Some(ty.clone())
                }
                _ => None,
            },
            Expr::Compare {
                op: Cmp::Eq,
                left,
                right,
                ..
            } if **right == Expr::Null => match left.as_ref() {
                Expr::As(ty, source) if **source == Expr::CaughtException => Some(ty.clone()),
                _ => None,
            },
            _ => None,
        };
        if let Some(ty) = tested {
            let mut variable = bound;
            let mut rest: Vec<Stmt> = otherwise.clone();
            if let Some(first) = rest.first()
                && let Some((Expr::Local(local), Expr::As(as_ty, source))) = assignment(first)
                && *as_ty == ty
                && **source == Expr::CaughtException
            {
                variable = Some(*local);
                rest.remove(0);
            } else if let Some(first) = rest.first()
                && let Some((Expr::Local(local), Expr::Local(from))) = assignment(first)
                && Some(*from) == bound
            {
                // The pattern variable copied into the source's own.
                let local = *local;
                let from = *from;
                rest.remove(0);
                for stmt in &mut rest {
                    stmt.map_exprs(&mut |e| {
                        if *e == Expr::Local(local) {
                            *e = Expr::Local(from);
                        }
                    });
                }
                variable = Some(from);
                // The handler body refers to the source's local; it is the
                // same variable, so the body is renamed too.
                for stmt in &mut catch.body {
                    stmt.map_exprs(&mut |e| {
                        if *e == Expr::Local(local) {
                            *e = Expr::Local(from);
                        }
                    });
                }
            }
            // Further copies of the exception, cast to the type it was
            // tested for or not: a debug state machine's hoisted locals.
            while let Some(from) = variable
                && let Some(first) = rest.first()
                && let Some((Expr::Local(local), copied)) = assignment(first)
                && match copied {
                    Expr::Local(source) => *source == from,
                    Expr::Cast(cast_to, inner) => *cast_to == ty && **inner == Expr::Local(from),
                    _ => false,
                }
            {
                let local = *local;
                rest.remove(0);
                let mut rename = |e: &mut Expr| {
                    if *e == Expr::Local(local) {
                        *e = Expr::Local(from);
                    }
                };
                for stmt in rest.iter_mut().chain(catch.body.iter_mut()) {
                    stmt.map_exprs(&mut rename);
                }
            }
            // `if (c) { t = true; } else { t = false; }` is `t = c`.
            if let Some(Stmt::If {
                condition,
                then,
                otherwise,
            }) = rest.first()
                && let [Stmt::Expr(Expr::Assign(a, yes))] = then.as_slice()
                && let [Stmt::Expr(Expr::Assign(b, no))] = otherwise.as_slice()
                && a == b
                && matches!(yes.as_ref(), Expr::Bool(true) | Expr::Int(1))
                && matches!(no.as_ref(), Expr::Bool(false) | Expr::Int(0))
            {
                rest[0] = Stmt::Expr(Expr::assign((**a).clone(), condition.clone()));
            }
            // `t = cond; r = t;`: a debug build's temporary for the result.
            if rest.len() == 2
                && let Some((Expr::Local(temp), value)) = assignment(&rest[0])
                && let Some((Expr::Slot(target), Expr::Local(copied))) = assignment(&rest[1])
                && temp == copied
                && *target == result
                && !catch
                    .body
                    .iter()
                    .any(|stmt| count_in_stmt_deep(stmt, &|e| *e == Expr::Local(*temp)) > 0)
            {
                rest = vec![Stmt::Expr(Expr::assign(Expr::Slot(result), value.clone()))];
            }
            if rest.len() == 1
                && let Some((Expr::Slot(target), value)) = assignment(&rest[0])
                && *target == result
            {
                let mut value = value.clone();
                value.map(&mut |e| {
                    if let Expr::As(as_ty, source) = e
                        && *as_ty == ty
                        && **source == Expr::CaughtException
                    {
                        *e = variable.map_or(Expr::CaughtException, Expr::Local);
                    }
                });
                catch.ty = Some(ty);
                catch.variable = variable;
                catch.filter = Some(value);
                return;
            }
        }
    }
    // `[v = ex as T; return v != null && cond]`
    if real.len() == 2
        && let Some((Expr::Local(local), Expr::As(ty, source))) = assignment(&real[0])
        && **source == Expr::CaughtException
        && let Stmt::Return(Some(Expr::Binary(BinOp::LogicalAnd, left, right))) = &real[1]
        && let Expr::Compare {
            op: Cmp::Ne,
            left: tested,
            right: null,
            ..
        } = left.as_ref()
        && **tested == Expr::Local(*local)
        && **null == Expr::Null
    {
        catch.ty = Some(ty.clone());
        catch.variable = Some(*local);
        catch.filter = Some((**right).clone());
        return;
    }
    // `[v = ex as T; return cond]` with `cond` not reading `v`: the type
    // test was folded away (`when (false)`), and what is left asks nothing
    // of the exception, as `catch when (cond)` does not.
    if real.len() == 2
        && let Some((Expr::Local(local), Expr::As(_, source))) = assignment(&real[0])
        && **source == Expr::CaughtException
        && let Stmt::Return(Some(value)) = &real[1]
        && value.count(&|e| *e == Expr::Local(*local)) == 0
    {
        catch.filter = Some(value.clone());
        return;
    }
    // `[return cond]`
    if real.len() == 1
        && let Stmt::Return(Some(value)) = &real[0]
    {
        let mut value = value.clone();
        if let Expr::Binary(BinOp::LogicalAnd, left, right) = &value
            && let Expr::Is(ty, source) = left.as_ref()
            && **source == Expr::CaughtException
        {
            catch.ty = Some(ty.clone());
            value = (**right).clone();
        }
        catch.filter = Some(value);
        return;
    }
    // Anything else is shown as it is, followed by a name nothing declares:
    // it reads, and does not compile. `true` compiled, and caught what the
    // filter turned away.
    let text: Vec<String> = real
        .iter()
        .map(|stmt| crate::print::stmt_text(typer.ctx, stmt))
        .collect();
    catch.filter = Some(Expr::Raw(format!(
        "/* {} */ FilterNotDecompiled",
        text.join(" ").replace('\n', " ")
    )));
}

/// `new ReadOnlySpan<byte>(&<data>, n)` is how a span over constant bytes
/// compiles: the bytes are read back into the array it was written as.
fn span_over_data(resolver: Resolver<'_>, expr: &Expr) -> Option<Expr> {
    // `RuntimeHelpers.CreateSpan<T>(<data>)`, for elements wider than a
    // byte: the data's type says how many bytes there are.
    if let Expr::Call {
        method,
        receiver: None,
        args,
    } = expr
        && method.name == "CreateSpan"
        && let [data] = args.as_slice()
        && let [element] = method.type_args.as_slice()
        && let Expr::Field {
            receiver: None,
            field,
        } = data
        && let TypeSig::ValueType(holder) = &field.ty
        && let Some(holder_name) = resolver.raw_name(*holder)
        && let Some(size) = holder_name
            .split("Size=")
            .nth(1)
            .and_then(|rest| rest.split('_').next())
            .and_then(|digits| digits.parse::<usize>().ok())
        && let Some(width) = crate::data::element_width(resolver, element)
    {
        let count = (size / width) as i64;
        let items = crate::data::array_items(resolver, field, element, count)?;
        let mut ctor = method.clone();
        ctor.name = ".ctor".to_string();
        ctor.declaring = substitute(&method.sig.returns, &method.declaring, &method.type_args);
        ctor.type_args = Vec::new();
        ctor.sig.instance = true;
        ctor.sig.arity = 0;
        ctor.sig.returns = TypeSig::Void;
        ctor.sig.returns_required = Vec::new();
        ctor.sig.parameters = vec![TypeSig::Vector(Box::new(element.clone()))];
        ctor.sig.parameters_required = vec![Vec::new()];
        ctor.out_params = Vec::new();
        ctor.param_names = Vec::new();
        ctor.param_defaults = Vec::new();
        ctor.is_extension = false;
        return Some(Expr::New {
            ctor,
            args: vec![Expr::NewArray {
                element: element.clone(),
                size: Box::new(Expr::Int(count)),
                items: Some(items),
            }],
            initializer: Vec::new(),
        });
    }
    let Expr::New { ctor, args, .. } = expr else {
        return None;
    };
    let [data, Expr::Int(count)] = args.as_slice() else {
        return None;
    };
    let TypeSig::Generic {
        definition,
        arguments,
    } = &ctor.declaring
    else {
        return None;
    };
    let (TypeSig::ValueType(token) | TypeSig::Class(token)) = definition.as_ref() else {
        return None;
    };
    let name = resolver.raw_name(*token)?;
    if !matches!(name.as_str(), "System.ReadOnlySpan`1" | "System.Span`1") {
        return None;
    }
    let field = match data {
        Expr::Unary(UnOp::AddressOf, inner) => inner.as_ref(),
        other => other,
    };
    let Expr::Field {
        receiver: None,
        field,
    } = field
    else {
        return None;
    };
    let element = arguments.first()?;
    let items = crate::data::array_items(resolver, field, element, *count)?;
    let mut ctor = ctor.clone();
    ctor.sig.parameters = vec![TypeSig::Vector(Box::new(element.clone()))];
    Some(Expr::New {
        ctor,
        args: vec![Expr::NewArray {
            element: element.clone(),
            size: Box::new(Expr::Int(*count)),
            items: Some(items),
        }],
        initializer: Vec::new(),
    })
}

/// Expression-level rewrites, applied everywhere.
fn rewrite_exprs(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    let resolver = typer.ctx.resolver;
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| rewrite_expr(typer, resolver, expr));
        // Filters carry their own block until folded.
        if let Stmt::Try { catches, .. } = stmt {
            for catch in catches {
                if let Some(Expr::Lambda { body, .. }) = &mut catch.filter
                    && let Body::Block(inner) = body.as_mut()
                {
                    rewrite_exprs(typer, inner);
                }
            }
        }
    }
    settle_statements(typer, stmts);
}

/// The statement-level rewrites of `rewrite_exprs`, in nested blocks too;
/// a local function returns its own type, and is left alone.
fn settle_statements(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    let resolver = typer.ctx.resolver;
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::LocalFunction { .. }) {
            continue;
        }
        for block in stmt.blocks_mut() {
            settle_statements(typer, block);
        }
        if let Stmt::Switch { value, cases } = stmt {
            coerce_labels(typer, value, cases);
        }
        if let Stmt::Return(Some(value)) = stmt
            && matches!(value, Expr::Int(_) | Expr::Conditional(..))
        {
            *value = coerce_expr(resolver, value.clone(), &typer.ctx.returns);
        }
        // `conv.u2` into a `char` is a cast to `char`.
        if let Stmt::Return(Some(Expr::Cast(to @ TypeSig::UInt16, _))) = stmt
            && typer.ctx.returns == TypeSig::Char
        {
            *to = TypeSig::Char;
        }
        // `return (double)f;` from a `double` method converts by itself.
        if let Stmt::Return(Some(Expr::Cast(to, inner))) = stmt
            && *to == typer.ctx.returns
            && typer
                .type_of(inner)
                .is_some_and(|from| implicit_numeric(&from, to))
        {
            let inner = (**inner).clone();
            *stmt = Stmt::Return(Some(inner));
        }
        if let Stmt::If { condition, .. }
        | Stmt::While { condition, .. }
        | Stmt::DoWhile { condition, .. }
        | Stmt::For { condition, .. } = stmt
        {
            let cleaned = as_bool(typer, condition.clone());
            *condition = cleaned;
        }
    }
}

/// Case labels take the type of what is switched on.
fn coerce_labels(typer: &Typer<'_, '_>, value: &Expr, cases: &mut [Case]) {
    let Some(ty) = typer.type_of(value) else {
        return;
    };
    for case in cases {
        for label in case.labels.iter_mut().flatten() {
            *label = coerce_expr(typer.ctx.resolver, label.clone(), &ty);
        }
    }
}

/// An expression in a `bool` position, with the integer shapes of a
/// materialised condition folded away.
fn as_bool(typer: &Typer<'_, '_>, expr: Expr) -> Expr {
    match expr {
        Expr::Int(0) => Expr::Bool(false),
        Expr::Int(_) => Expr::Bool(true),
        Expr::Conditional(condition, a, b) => make_conditional(
            typer,
            as_bool(typer, *condition),
            as_bool(typer, *a),
            as_bool(typer, *b),
        ),
        Expr::Compare {
            op: op @ (Cmp::Ne | Cmp::Eq),
            left,
            right,
            float,
            unordered,
        } if *right == Expr::Int(0) || *right == Expr::Bool(false) => {
            let boolish = *right == Expr::Bool(false)
                || typer.is_bool(&left)
                || matches!(
                    *left,
                    Expr::Conditional(..)
                        | Expr::Compare { .. }
                        | Expr::Is(..)
                        | Expr::IsPattern(..)
                        | Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr, ..)
                        | Expr::Unary(UnOp::Not, _)
                );
            if !boolish {
                return Expr::Compare {
                    op,
                    left,
                    right,
                    float,
                    unordered,
                };
            }
            let inner = as_bool(typer, *left);
            if op == Cmp::Ne { inner } else { negate(inner) }
        }
        Expr::Unary(UnOp::Not, inner) => negate(as_bool(typer, *inner)),
        Expr::Binary(op @ (BinOp::LogicalAnd | BinOp::LogicalOr), left, right) => {
            Expr::binary(op, as_bool(typer, *left), as_bool(typer, *right))
        }
        other => other,
    }
}

#[allow(clippy::too_many_lines)]
fn rewrite_expr(typer: &Typer<'_, '_>, resolver: Resolver<'_>, expr: &mut Expr) {
    // `x << (n & 31)`: the mask is the one C# puts on the count itself, 63
    // for a 64-bit `x`.
    if let Expr::Binary(BinOp::Shl | BinOp::Shr | BinOp::UShr, left, count) = expr
        && let Expr::Binary(BinOp::And, n, mask) = count.as_ref()
        && let Expr::Int(mask) = mask.as_ref()
        && let Some(width) = typer
            .type_of(left)
            .map(read_through)
            .and_then(|ty| match ty {
                TypeSig::Int32 | TypeSig::UInt32 => Some(31),
                TypeSig::Int64 | TypeSig::UInt64 => Some(63),
                _ => None,
            })
        && *mask & width == width
    {
        let n = (**n).clone();
        **count = n;
    }
    // `c ? a : a` is `a`, when testing `c` does nothing.
    if let Expr::Conditional(condition, a, b) = expr
        && a == b
        && condition.is_pure()
    {
        let a = std::mem::replace(a.as_mut(), Expr::Null);
        *expr = a;
        return;
    }
    // `null == null` is known, and so is a conditional on it.
    if let Expr::Compare {
        op: op @ (Cmp::Eq | Cmp::Ne),
        left,
        right,
        ..
    } = expr
        && **left == Expr::Null
        && **right == Expr::Null
    {
        *expr = Expr::Bool(*op == Cmp::Eq);
        return;
    }
    if let Expr::Conditional(condition, a, b) = expr
        && let Expr::Bool(known) = condition.as_ref()
    {
        let taken = if *known { a } else { b };
        let taken = std::mem::replace(taken.as_mut(), Expr::Null);
        *expr = taken;
        return;
    }
    // `null ?? b` is `b`.
    if let Expr::Binary(BinOp::Coalesce, left, right) = expr
        && matches!(left.as_ref(), Expr::Null | Expr::Default(_))
    {
        let right = std::mem::replace(right.as_mut(), Expr::Null);
        *expr = right;
        return;
    }
    if let Some(span) = span_over_data(resolver, expr) {
        *expr = span;
        return;
    }
    // The address of an address is the address.
    if let Expr::Unary(UnOp::AddressOf, inner) = expr
        && let Expr::Unary(UnOp::AddressOf, place) = inner.as_ref()
    {
        let place = (**place).clone();
        *expr = Expr::Unary(UnOp::AddressOf, Box::new(place));
        return;
    }
    // `(c ? 1 : 0) & b` with a `bool` b is `c & b`: the condition was only
    // made a number on its way through branches.
    if let Expr::Binary(BinOp::And | BinOp::Or | BinOp::Xor, left, right) = expr {
        let as_flag = |side: &Expr| match side {
            Expr::Conditional(c, a, b) => match (a.as_ref(), b.as_ref()) {
                (Expr::Int(1), Expr::Int(0)) => Some((**c).clone()),
                (Expr::Int(0), Expr::Int(1)) => Some(negate((**c).clone())),
                _ => None,
            },
            _ => None,
        };
        if typer.is_bool(right)
            && let Some(flag) = as_flag(left)
        {
            **left = flag;
        } else if typer.is_bool(left)
            && let Some(flag) = as_flag(right)
        {
            **right = flag;
        }
    }
    let replacement = match expr {
        // Accessors back into members.
        // `Activator.CreateInstance<T>()` is how `new T()` compiles.
        Expr::Call {
            method,
            receiver: None,
            args,
        } if method.name == "CreateInstance"
            && args.is_empty()
            && method.type_args.len() == 1
            && matches!(method.type_args[0], TypeSig::Var(_) | TypeSig::MVar(_))
            && is_named(resolver, &method.declaring, "Activator") =>
        {
            Some(Expr::NewOf(method.type_args[0].clone()))
        }
        // `a.GetValueOrDefault(5)` is how `a ?? 5` compiles for an `int?`.
        Expr::Call {
            method,
            receiver: Some(receiver),
            args,
        } if method.name == "GetValueOrDefault"
            && args.len() == 1
            && resolver.is_nullable(&method.declaring) =>
        {
            let receiver = match receiver.as_ref() {
                Expr::Unary(UnOp::AddressOf, inner) => (**inner).clone(),
                other => other.clone(),
            };
            Some(Expr::binary(BinOp::Coalesce, receiver, args[0].clone()))
        }
        // A multi-dimensional array's element accessors.
        Expr::Call {
            method,
            receiver: Some(receiver),
            args,
        } if matches!(method.declaring, TypeSig::Array { .. })
            && matches!(method.name.as_str(), "Get" | "Address")
            && !args.is_empty() =>
        {
            let index = Expr::Index {
                array: receiver.clone(),
                indices: std::mem::take(args),
            };
            Some(if method.name == "Address" {
                Expr::unary(UnOp::AddressOf, index)
            } else {
                index
            })
        }
        Expr::Call {
            method,
            receiver: Some(receiver),
            args,
        } if matches!(method.declaring, TypeSig::Array { .. })
            && method.name == "Set"
            && args.len() >= 2 =>
        {
            let value = args.pop().unwrap_or(Expr::Null);
            Some(Expr::assign(
                Expr::Index {
                    array: receiver.clone(),
                    indices: std::mem::take(args),
                },
                value,
            ))
        }
        Expr::Call {
            method,
            receiver,
            args,
        } => {
            let name = method.name.clone();
            if let Some(property) = name.strip_prefix("get_") {
                if args.is_empty() && !property.is_empty() {
                    let ty = substitute(&method.sig.returns, &method.declaring, &method.type_args);
                    Some(Expr::Property {
                        receiver: receiver.take(),
                        declaring: method.declaring.clone(),
                        name: property.to_string(),
                        ty: Some(ty),
                    })
                } else if property == "Item"
                    || (!args.is_empty()
                        && receiver.is_some()
                        && (is_indexer(method) || resolver.is_accessor(method)))
                {
                    receiver.take().map(|receiver| Expr::Indexer {
                        receiver,
                        args: std::mem::take(args),
                    })
                } else {
                    None
                }
            } else if let Some(operator) = name.strip_prefix("op_")
                && receiver.is_none()
            {
                operator_expr(typer, operator, method, args)
            } else if name == "Concat"
                && receiver.is_none()
                && is_string_type(resolver, &method.declaring)
            {
                concat_expr(typer, method, args)
            } else if name == "Format"
                && receiver.is_none()
                && is_string_type(resolver, &method.declaring)
            {
                format_expr(args)
            } else {
                None
            }
        }

        // `new int[,](w, h)` is the constructor of a multi-dimensional
        // array type: `new int[w, h]`.
        Expr::New {
            ctor,
            args,
            initializer,
        } if initializer.is_empty()
            && matches!(&ctor.declaring, TypeSig::Array { rank, .. } if *rank as usize == args.len()) =>
        {
            let TypeSig::Array { element, .. } = &ctor.declaring else {
                unreachable!()
            };
            Some(Expr::NewArray {
                element: (**element).clone(),
                size: Box::new(Expr::Tuple(std::mem::take(args))),
                items: None,
            })
        }
        // `new Span<int>(stackalloc byte[16], 4)` is `stackalloc int[4]`.
        Expr::New { ctor, args, .. }
            if matches!(args.as_slice(), [Expr::StackAlloc(..), _])
                && matches!(&ctor.declaring, TypeSig::Generic { definition, arguments }
                    if arguments.len() == 1
                        && matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                            if matches!(resolver.raw_name(*token).as_deref(),
                                Some("System.Span`1" | "System.ReadOnlySpan`1")))) =>
        {
            let TypeSig::Generic { arguments, .. } = &ctor.declaring else {
                unreachable!()
            };
            Some(Expr::StackAlloc(
                arguments[0].clone(),
                Box::new(args[1].clone()),
            ))
        }
        // `*(p + i)` is `p[i]`.
        Expr::Unary(UnOp::Deref, inner)
            if matches!(inner.as_ref(), Expr::Binary(BinOp::Add, left, _)
                if matches!(typer.type_of(left), Some(TypeSig::Pointer(element)) if *element != TypeSig::Void)) =>
        {
            let Expr::Binary(_, left, right) = inner.as_ref() else {
                unreachable!()
            };
            Some(Expr::Index {
                array: left.clone(),
                indices: vec![(**right).clone()],
            })
        }
        // A box says nothing in C#, and neither does wrapping a value in
        // its nullable type. What it does say is the type: a `bool` or a
        // `char` is a number on the stack, and `c ? 1 : 0` boxed as a
        // `Boolean` is `c`, not the `int` it would print as.
        Expr::Box(ty, inner) => {
            let mut inner = (**inner).clone();
            if matches!(ty, TypeSig::Boolean | TypeSig::Char) {
                crate::fit::fit_value(typer, &mut inner, ty);
            }
            Some(inner)
        }
        Expr::New { ctor, args, .. }
            if args.len() == 1
                && matches!(&ctor.declaring, TypeSig::Generic { definition, .. }
                    if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                        if resolver.raw_name(*token).as_deref() == Some("System.Nullable`1"))) =>
        {
            Some(args[0].clone())
        }
        Expr::Default(TypeSig::Generic { definition, .. })
            if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                if resolver.raw_name(*token).as_deref() == Some("System.Nullable`1")) =>
        {
            Some(Expr::Null)
        }
        // Casting a constant to the type it already prints as.
        Expr::Cast(ty, inner) => match (ty, inner.as_ref()) {
            (TypeSig::Int64, Expr::Int(n)) => Some(Expr::Long(*n)),
            (TypeSig::Double, Expr::Int(n)) => Some(Expr::Float(*n as f64, false)),
            (TypeSig::Single, Expr::Int(n)) => Some(Expr::Float(*n as f64, true)),
            (TypeSig::Double, Expr::Float(f, true)) => Some(Expr::Float(*f, false)),
            (TypeSig::Char, Expr::Int(n)) => Some(Expr::Char(*n as u16)),
            (TypeSig::Int32, Expr::Char(c)) => Some(Expr::Int(i64::from(*c))),
            (TypeSig::Boolean, Expr::Int(n)) => Some(Expr::Bool(*n != 0)),
            (ty, inner) => {
                // `(int)(x + 1)` where `x` is `int` is a widening the IL did.
                match typer.type_of(inner) {
                    Some(found) if &found == ty => Some(inner.clone()),
                    _ => match resolver.enum_of(ty) {
                        Some(members) => match inner {
                            Expr::Int(n) => Some(enum_member(ty, &members, *n)),
                            _ => None,
                        },
                        None => None,
                    },
                }
            }
        },
        // A compound on a property arrives as `x.set_P(x.get_P() + v)`.
        Expr::Compare {
            op, left, right, ..
        } => {
            // `(x ? 1 : 0) != 0` and friends.
            if matches!(right.as_ref(), Expr::Int(0) | Expr::Bool(false))
                && (matches!(
                    **left,
                    Expr::Conditional(..)
                        | Expr::Binary(BinOp::LogicalAnd | BinOp::LogicalOr, ..)
                        | Expr::Is(..)
                        | Expr::Compare { .. }
                ) || (matches!(
                    **left,
                    Expr::Binary(BinOp::And | BinOp::Or | BinOp::Xor, ..)
                ) && typer.is_bool(left)))
                && matches!(op, Cmp::Eq | Cmp::Ne)
            {
                let inner = as_bool(typer, (**left).clone());
                Some(if *op == Cmp::Ne { inner } else { negate(inner) })
            } else if let Expr::Int(n) = right.as_ref()
                && let Some(ty) = typer.type_of(left)
                && (matches!(ty, TypeSig::Boolean | TypeSig::Char)
                    || resolver.enum_of(&ty).is_some())
            {
                let coerced = coerce_expr(resolver, Expr::Int(*n), &ty);
                if coerced == Expr::Bool(false) && *op == Cmp::Eq {
                    Some(negate((**left).clone()))
                } else if coerced == Expr::Bool(false) && *op == Cmp::Ne {
                    Some((**left).clone())
                } else {
                    Some(Expr::Compare {
                        op: *op,
                        left: left.clone(),
                        right: Box::new(coerced),
                        float: false,
                        unordered: false,
                    })
                }
            } else {
                None
            }
        }
        // Lifted comparisons of nullable values.
        Expr::Binary(BinOp::And | BinOp::Or, ..) if lifted_comparison(resolver, expr).is_some() => {
            lifted_comparison(resolver, expr)
        }
        // `a & b` on `bool`s with nothing to evaluate on the right is how
        // Roslyn compiles `a && b` without a branch.
        Expr::Binary(op @ (BinOp::And | BinOp::Or), left, right)
            if typer.is_bool(left)
                && typer.is_bool(right)
                && right.is_pure()
                && !matches!(right.as_ref(), Expr::Compare { .. } if false) =>
        {
            let op = if *op == BinOp::And {
                BinOp::LogicalAnd
            } else {
                BinOp::LogicalOr
            };
            Some(Expr::binary(op, (**left).clone(), (**right).clone()))
        }
        // `(long)i + l`: the widening the operator does by itself.
        Expr::Binary(
            op @ (BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::And
            | BinOp::Or
            | BinOp::Xor),
            left,
            right,
        ) if implied_cast(typer, left, right, false).is_some()
            || implied_cast(typer, right, left, true).is_some() =>
        {
            // With a cast on both sides, the left one stays to say the type.
            let left_new =
                implied_cast(typer, left, right, false).unwrap_or_else(|| (**left).clone());
            let right_new =
                implied_cast(typer, right, &left_new, true).unwrap_or_else(|| (**right).clone());
            Some(Expr::binary(*op, left_new, right_new))
        }
        Expr::Binary(BinOp::Add, left, right)
            if span_over(resolver, left).is_some() || span_over(resolver, right).is_some() =>
        {
            let left = span_over(resolver, left).unwrap_or_else(|| (**left).clone());
            let right = span_over(resolver, right).unwrap_or_else(|| (**right).clone());
            Some(Expr::binary(BinOp::Add, left, right))
        }
        Expr::Binary(op, left, right)
            if !matches!(op, BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::Coalesce) =>
        {
            // `flags & Color.A` with an integer on one side. Only the
            // bitwise operators take two of an enum.
            if matches!(op, BinOp::And | BinOp::Or | BinOp::Xor)
                && let Expr::Int(n) = right.as_ref()
                && let Some(ty) = typer.type_of(left)
                && resolver.enum_of(&ty).is_some()
            {
                Some(Expr::binary(
                    *op,
                    (**left).clone(),
                    coerce_expr(resolver, Expr::Int(*n), &ty),
                ))
            } else {
                None
            }
        }
        // `x.HasValue ? x.GetValueOrDefault() : y` is `x ?? y`.
        Expr::Conditional(condition, a, b)
            if has_value_of(condition).is_some_and(Expr::is_pure)
                && value_of_nullable(a) == has_value_of(condition) =>
        {
            has_value_of(condition)
                .cloned()
                .map(|nullable| Expr::binary(BinOp::Coalesce, nullable, (**b).clone()))
        }
        // `x.HasValue ? x.GetValueOrDefault().M() : y` is `x?.M() ?? y`.
        Expr::Conditional(condition, a, b)
            if has_value_of(condition).is_some_and(|nullable| {
                nullable.is_pure() && nullable_chain(a, nullable).is_some()
            }) =>
        {
            has_value_of(condition)
                .and_then(|nullable| nullable_chain(a, nullable))
                .map(|chained| match b.as_ref() {
                    Expr::Null => chained,
                    Expr::Default(ty) if resolver.is_nullable(ty) => chained,
                    other => Expr::binary(BinOp::Coalesce, chained, other.clone()),
                })
        }
        Expr::Conditional(condition, a, b)
            if lifted_arithmetic(typer, condition, a, b).is_some() =>
        {
            lifted_arithmetic(typer, condition, a, b)
        }
        Expr::Conditional(condition, a, b) => {
            let made = make_conditional(typer, (**condition).clone(), (**a).clone(), (**b).clone());
            (made != *expr).then_some(made)
        }
        Expr::Assign(target, value)
            if matches!(value.as_ref(), Expr::Cast(TypeSig::UInt16, _))
                && typer.type_of(target) == Some(TypeSig::Char) =>
        {
            let Expr::Cast(_, inner) = value.as_ref() else {
                unreachable!()
            };
            Some(Expr::assign(
                (**target).clone(),
                Expr::Cast(TypeSig::Char, inner.clone()),
            ))
        }
        // A constant stored into a `bool`, `char` or enum variable is one.
        Expr::Assign(target, value)
            if matches!(value.as_ref(), Expr::Int(_) | Expr::Conditional(..))
                && matches!(
                    target.as_ref(),
                    Expr::Local(_) | Expr::Arg(_) | Expr::Field { .. }
                ) =>
        {
            typer.type_of(target).and_then(|ty| {
                let coerced = coerce_expr(resolver, (**value).clone(), &ty);
                (coerced != **value).then(|| Expr::Assign(target.clone(), Box::new(coerced)))
            })
        }
        _ => None,
    };
    if let Some(replacement) = replacement {
        *expr = replacement;
    }
    // Trailing arguments that repeat the parameter's default were not
    // written in the source.
    if let Expr::Call { method, args, .. } = expr
        && !method.param_defaults.is_empty()
        // Fewer arguments could name another overload: `this()`, itself.
        && !resolver.has_overloads(method)
    {
        while let (Some(last), Some(Some(default))) = (
            args.last(),
            args.len()
                .checked_sub(1)
                .and_then(|at| method.param_defaults.get(at)),
        ) {
            let same = match (last, default) {
                (Expr::Int(a), crate::names::Constant::Int(b)) => a == b,
                (Expr::Long(a), crate::names::Constant::Int(b)) => a == b,
                (Expr::Bool(a), crate::names::Constant::Bool(b)) => a == b,
                (Expr::Char(a), crate::names::Constant::Char(b)) => a == b,
                (Expr::Str(a), crate::names::Constant::Str(b)) => a == b,
                (Expr::Null | Expr::Default(_), crate::names::Constant::Null) => true,
                (Expr::EnumMember(ty, name), crate::names::Constant::Int(b)) => resolver
                    .enum_of(ty)
                    .is_some_and(|members| members.iter().any(|(n, v)| n == name && v == b)),
                (Expr::Float(a, _), crate::names::Constant::Float(b, _)) => {
                    (a - b).abs() < f64::EPSILON
                }
                _ => false,
            };
            if !same {
                break;
            }
            args.pop();
        }
    }
    // `x.set_P(v)` as a statement is an assignment.
    if let Expr::Call {
        method,
        receiver,
        args,
    } = expr
        && let Some(property) = method.name.strip_prefix("set_")
        && !args.is_empty()
    {
        let value = args.pop().unwrap_or(Expr::Null);
        let ty = method.sig.parameters.last().cloned();
        // An indexer's setter takes the index too: `set_Item(v)` alone
        // sets a property named `Item`.
        let target = if !args.is_empty() {
            match receiver.take() {
                Some(receiver) => Expr::Indexer {
                    receiver,
                    args: std::mem::take(args),
                },
                None => Expr::Property {
                    receiver: None,
                    declaring: method.declaring.clone(),
                    name: property.to_string(),
                    ty,
                },
            }
        } else {
            Expr::Property {
                receiver: receiver.take(),
                declaring: method.declaring.clone(),
                name: property.to_string(),
                ty,
            }
        };
        *expr = Expr::assign(target, value);
    }
    if let Expr::Call {
        method,
        receiver,
        args,
    } = expr
        && let Some(event) = method
            .name
            .strip_prefix("add_")
            .map(|e| (e, BinOp::Add))
            .or_else(|| method.name.strip_prefix("remove_").map(|e| (e, BinOp::Sub)))
        && args.len() == 1
    {
        let value = args.pop().unwrap_or(Expr::Null);
        let target = Expr::Property {
            receiver: receiver.take(),
            declaring: method.declaring.clone(),
            name: event.0.to_string(),
            ty: method.sig.parameters.first().cloned(),
        };
        *expr = Expr::Compound(event.1, Box::new(target), Box::new(value));
    }
}

fn is_indexer(method: &crate::names::MethodRef) -> bool {
    method.name == "get_Item" || method.name == "get_Chars"
}

fn is_string_type(resolver: Resolver<'_>, ty: &TypeSig) -> bool {
    matches!(ty, TypeSig::String)
        || matches!(ty, TypeSig::Class(token) if resolver.raw_name(*token).as_deref() == Some("System.String"))
}

fn enum_member(ty: &TypeSig, members: &[(String, i64)], value: i64) -> Expr {
    coerce_expr_members(ty, members, value)
}

fn coerce_expr_members(ty: &TypeSig, members: &[(String, i64)], value: i64) -> Expr {
    members.iter().find(|(_, v)| *v == value).map_or_else(
        || Expr::Cast(ty.clone(), Box::new(Expr::Int(value))),
        |(name, _)| Expr::EnumMember(ty.clone(), name.clone()),
    )
}

/// `x.GetValueOrDefault()`: the nullable it is called on.
fn value_of_nullable(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Call {
            method,
            receiver: Some(receiver),
            args,
        } if method.name == "GetValueOrDefault" && args.is_empty() => {
            Some(match receiver.as_ref() {
                Expr::Unary(UnOp::AddressOf, inner) => inner,
                other => other,
            })
        }
        _ => None,
    }
}

/// `x.HasValue`: the nullable it asks about.
fn has_value_of(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Property {
            receiver: Some(receiver),
            name,
            ..
        } if name == "HasValue" => Some(match receiver.as_ref() {
            Expr::Unary(UnOp::AddressOf, inner) => inner,
            other => other,
        }),
        Expr::Call {
            method,
            receiver: Some(receiver),
            args,
        } if method.name == "get_HasValue" && args.is_empty() => Some(match receiver.as_ref() {
            Expr::Unary(UnOp::AddressOf, inner) => inner,
            other => other,
        }),
        _ => None,
    }
}

/// `x.GetValueOrDefault().M().N` as `x?.M().N`: a member chain whose
/// innermost receiver is the nullable's value, read nowhere else.
fn nullable_chain(expr: &Expr, nullable: &Expr) -> Option<Expr> {
    if expr.count(&|e| value_of_nullable(e) == Some(nullable)) != 1 {
        return None;
    }
    fn rebuild(expr: &Expr, nullable: &Expr) -> Option<Expr> {
        let (receiver, rebuild_with): (&Expr, Box<dyn Fn(Expr) -> Expr>) = match expr {
            Expr::Call {
                method,
                receiver: Some(receiver),
                args,
            } if args
                .iter()
                .all(|arg| arg.count(&|e| value_of_nullable(e) == Some(nullable)) == 0) =>
            {
                let (method, args) = (method.clone(), args.clone());
                (
                    receiver,
                    Box::new(move |inner| Expr::Call {
                        method: method.clone(),
                        receiver: Some(Box::new(inner)),
                        args: args.clone(),
                    }),
                )
            }
            Expr::Property {
                receiver: Some(receiver),
                declaring,
                name,
                ty,
            } => {
                let (declaring, name, ty) = (declaring.clone(), name.clone(), ty.clone());
                (
                    receiver,
                    Box::new(move |inner| Expr::Property {
                        receiver: Some(Box::new(inner)),
                        declaring: declaring.clone(),
                        name: name.clone(),
                        ty: ty.clone(),
                    }),
                )
            }
            Expr::Field {
                receiver: Some(receiver),
                field,
            } => {
                let field = field.clone();
                (
                    receiver,
                    Box::new(move |inner| Expr::Field {
                        receiver: Some(Box::new(inner)),
                        field: field.clone(),
                    }),
                )
            }
            _ => return None,
        };
        let receiver = match receiver {
            Expr::Unary(UnOp::AddressOf, inner) => inner.as_ref(),
            other => other,
        };
        if value_of_nullable(receiver) == Some(nullable) {
            return Some(rebuild_with(Expr::MaybeNull(Box::new(nullable.clone()))));
        }
        rebuild(receiver, nullable).map(rebuild_with)
    }
    rebuild(expr, nullable)
}

/// `a.HasValue & b.HasValue ? a.GetValueOrDefault() + b.GetValueOrDefault()
/// : null` is `a + b` on two `int?`: the lifted operator, and the same for
/// one operand, a unary operator or a conversion.
fn lifted_arithmetic(
    typer: &Typer<'_, '_>,
    condition: &Expr,
    value: &Expr,
    absent: &Expr,
) -> Option<Expr> {
    if !matches!(absent, Expr::Null)
        && !matches!(absent, Expr::Default(ty) if typer.ctx.resolver.is_nullable(ty))
    {
        return None;
    }
    // The nullables whose presence is asked.
    fn present<'e>(condition: &'e Expr, out: &mut Vec<&'e Expr>) -> bool {
        match condition {
            Expr::Binary(BinOp::And | BinOp::LogicalAnd, left, right) => {
                present(left, out) && present(right, out)
            }
            other => match has_value_of(other) {
                Some(inner) if inner.is_pure() => {
                    out.push(inner);
                    true
                }
                _ => false,
            },
        }
    }
    let mut nullables = Vec::new();
    if !present(condition, &mut nullables) {
        return None;
    }
    // Each is read only for its value, and nothing else is.
    let mut lifted = value.clone();
    let mut unlifted = 0;
    lifted.map(&mut |e| {
        if let Some(inner) = value_of_nullable(e) {
            if nullables.contains(&inner) {
                *e = inner.clone();
            } else {
                unlifted += 1;
            }
        }
    });
    if unlifted > 0
        || nullables
            .iter()
            .any(|nullable| value.count(&|e| value_of_nullable(e) == Some(nullable)) == 0)
    {
        return None;
    }
    // Only operators lift: a call on the value does not.
    let operators_only = match &lifted {
        Expr::Binary(op, ..) => {
            !matches!(op, BinOp::LogicalAnd | BinOp::LogicalOr | BinOp::Coalesce)
        }
        Expr::Unary(UnOp::Neg | UnOp::BitNot, _) | Expr::Cast(..) => true,
        _ => false,
    };
    if !operators_only {
        return None;
    }
    // `(double)a.GetValueOrDefault()` is `a` converted as a nullable, which
    // widening does by itself.
    if let Expr::Cast(to, inner) = &lifted {
        let from = typer.type_of(value).and(match value {
            Expr::Cast(_, original) => typer.type_of(original),
            _ => None,
        });
        if from.is_some_and(|from| implicit_numeric(&from, to)) {
            return Some((**inner).clone());
        }
        let nullable = match absent {
            Expr::Default(ty) => ty.clone(),
            _ => return None,
        };
        return Some(Expr::Cast(nullable, inner.clone()));
    }
    Some(lifted)
}

/// `(a.GetValueOrDefault() < b.GetValueOrDefault()) & (a.HasValue &
/// b.HasValue)` is `a < b` on two `int?`, and the same with a constant on
/// one side is `a < 5`; `==` compares the `HasValue`s with `==`, `!=`
/// joins them with `|`.
fn lifted_comparison(resolver: Resolver<'_>, expr: &Expr) -> Option<Expr> {
    let _ = resolver;
    let Expr::Binary(joint, compared, presence) = expr else {
        return None;
    };
    let Expr::Compare {
        op, left, right, ..
    } = compared.as_ref()
    else {
        return None;
    };
    let side = |e: &Expr| -> Option<(Expr, bool)> {
        match value_of_nullable(e) {
            Some(inner) => Some((inner.clone(), true)),
            None if e.is_pure() && e.count(&|inner| value_of_nullable(inner).is_some()) == 0 => {
                Some((e.clone(), false))
            }
            None => None,
        }
    };
    let (a, a_nullable) = side(left)?;
    let (b, b_nullable) = side(right)?;
    if !a_nullable && !b_nullable {
        return None;
    }
    let presence_ok = match (a_nullable, b_nullable) {
        (true, true) => match (joint, op, presence.as_ref()) {
            (
                BinOp::And,
                Cmp::Eq,
                Expr::Compare {
                    op: Cmp::Eq,
                    left,
                    right,
                    ..
                },
            )
            | (
                BinOp::Or,
                Cmp::Ne,
                Expr::Compare {
                    op: Cmp::Ne,
                    left,
                    right,
                    ..
                },
            ) => has_value_of(left) == Some(&a) && has_value_of(right) == Some(&b),
            (
                BinOp::And,
                Cmp::Lt | Cmp::Le | Cmp::Gt | Cmp::Ge,
                Expr::Binary(BinOp::And, left, right),
            ) => has_value_of(left) == Some(&a) && has_value_of(right) == Some(&b),
            _ => false,
        },
        (true, false) | (false, true) => {
            let nullable = if a_nullable { &a } else { &b };
            match (joint, op) {
                (BinOp::And, Cmp::Eq | Cmp::Lt | Cmp::Le | Cmp::Gt | Cmp::Ge) => {
                    has_value_of(presence) == Some(nullable)
                }
                (BinOp::Or, Cmp::Ne) => {
                    matches!(presence.as_ref(), Expr::Unary(UnOp::Not, inner) if has_value_of(inner) == Some(nullable))
                }
                _ => false,
            }
        }
        (false, false) => false,
    };
    presence_ok.then(|| Expr::compare(*op, a, b))
}

/// A local the compiler typed `ReadOnlySpan<char>` to hand a string to
/// .NET 8's span concatenation holds that string: only strings go into it,
/// and it is only read as a part of `+`, which in C# is on strings.
/// A slot the stack gave `object` because a `null` reached it first is of
/// the class every value stored into it has: `string`, where `null` and a
/// string meet.
pub fn retype_object_slots(
    typer: &Typer<'_, '_>,
    stmts: &[Stmt],
    slots: &mut HashMap<u32, TypeSig>,
) {
    let mut stored: HashMap<u32, Vec<Expr>> = HashMap::new();
    // A slot given to a call as an `object` stays one: typed otherwise it
    // could pick another overload.
    let mut passed: HashMap<u32, Vec<TypeSig>> = HashMap::new();
    for stmt in stmts {
        stmt.walk_exprs(&mut |e| {
            let (method, args) = match e {
                Expr::Assign(target, value) => {
                    if let Expr::Slot(id) = target.as_ref() {
                        stored.entry(*id).or_default().push((**value).clone());
                    }
                    return;
                }
                Expr::Call { method, args, .. } => (method, args),
                Expr::New { ctor, args, .. } => (ctor, args),
                _ => return,
            };
            for (at, arg) in args.iter().enumerate() {
                if let Expr::Slot(id) = arg {
                    let param = method.sig.parameters.get(at).map_or(TypeSig::Object, |p| {
                        substitute(p, &method.declaring, &method.type_args)
                    });
                    passed.entry(*id).or_default().push(param);
                }
            }
        });
    }
    for _ in 0..8 {
        let mut changed = false;
        for (id, values) in &stored {
            if slots.get(id) != Some(&TypeSig::Object) {
                continue;
            }
            let mut found: Option<TypeSig> = None;
            let mut agree = true;
            for value in values {
                let ty = match value {
                    Expr::Null => continue,
                    Expr::Slot(other) => slots.get(other).cloned(),
                    other => typer.type_of(other),
                };
                match (ty, &found) {
                    (Some(ty), None) => found = Some(ty),
                    (Some(ty), Some(have)) if ty == *have => {}
                    _ => agree = false,
                }
            }
            if agree
                && let Some(ty) = found
                && passed
                    .get(id)
                    .is_none_or(|params| params.iter().all(|param| *param == ty))
                && ty != TypeSig::Object
                && !typer.ctx.resolver.is_value_type(&ty)
                && !matches!(
                    ty,
                    TypeSig::Var(_) | TypeSig::MVar(_) | TypeSig::ByRef(_) | TypeSig::Pointer(_)
                )
            {
                slots.insert(*id, ty);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

pub fn retype_span_strings(
    typer: &Typer<'_, '_>,
    stmts: &[Stmt],
    locals: &mut [TypeSig],
    slots: &mut HashMap<u32, TypeSig>,
) {
    let is_char_span = |ty: &TypeSig| {
        matches!(ty, TypeSig::Generic { definition, arguments }
            if arguments.as_slice() == [TypeSig::Char]
                && matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                    if typer.ctx.resolver.raw_name(*token).as_deref() == Some("System.ReadOnlySpan`1")))
    };
    let mut variables: Vec<Expr> = (0..locals.len())
        .filter(|at| is_char_span(&locals[*at]))
        .map(|at| Expr::Local(at as u16))
        .collect();
    variables.extend(
        slots
            .iter()
            .filter(|(_, ty)| is_char_span(ty))
            .map(|(id, _)| Expr::Slot(*id)),
    );
    for local in variables {
        let mut stores = 0;
        let mut strings = 0;
        let mut reads = 0;
        let mut concatenated = 0;
        for stmt in stmts {
            stmt.walk_exprs(&mut |e| match e {
                Expr::Assign(target, value) if **target == local => {
                    stores += 1;
                    if typer.type_of(value) == Some(TypeSig::String) {
                        strings += 1;
                    }
                }
                Expr::Binary(BinOp::Add, left, right) => {
                    concatenated += usize::from(**left == local) + usize::from(**right == local);
                }
                e if *e == local => reads += 1,
                _ => {}
            });
        }
        // Each store's target is counted as a read by the walk.
        if stores > 0 && strings == stores && reads - stores == concatenated {
            match local {
                Expr::Local(at) => locals[at as usize] = TypeSig::String,
                Expr::Slot(id) => {
                    slots.insert(id, TypeSig::String);
                }
                _ => {}
            }
        }
    }
}

/// Where a numeric type stands in C#'s promotions, wider higher; the small
/// ones all become `int`.
/// What a `ref` of a type reads as.
fn read_through(ty: TypeSig) -> TypeSig {
    match ty {
        TypeSig::ByRef(inner) => *inner,
        other => other,
    }
}

fn numeric_rank(ty: &TypeSig) -> Option<u8> {
    Some(match ty {
        TypeSig::SByte | TypeSig::Byte | TypeSig::Int16 | TypeSig::UInt16 | TypeSig::Char => 1,
        TypeSig::Int32 => 3,
        TypeSig::UInt32 => 4,
        TypeSig::Int64 => 5,
        TypeSig::UInt64 => 6,
        TypeSig::Single => 7,
        TypeSig::Double => 8,
        _ => return None,
    })
}

/// Whether C# converts a value of one numeric type to another without
/// being asked.
pub(crate) fn implicit_numeric(from: &TypeSig, to: &TypeSig) -> bool {
    use TypeSig as T;
    match to {
        T::Int16 => matches!(from, T::SByte | T::Byte),
        T::UInt16 => matches!(from, T::Byte | T::Char),
        T::Int32 => matches!(from, T::SByte | T::Byte | T::Int16 | T::UInt16 | T::Char),
        T::UInt32 => matches!(from, T::Byte | T::UInt16 | T::Char),
        T::Int64 => matches!(
            from,
            T::SByte | T::Byte | T::Int16 | T::UInt16 | T::Char | T::Int32 | T::UInt32 | T::IntPtr
        ),
        T::UInt64 => matches!(from, T::Byte | T::UInt16 | T::Char | T::UInt32 | T::UIntPtr),
        T::IntPtr => matches!(
            from,
            T::SByte | T::Byte | T::Int16 | T::UInt16 | T::Char | T::Int32
        ),
        T::UIntPtr => matches!(from, T::Byte | T::UInt16 | T::Char | T::UInt32),
        T::Single | T::Double => {
            matches!(
                from,
                T::SByte
                    | T::Byte
                    | T::Int16
                    | T::UInt16
                    | T::Char
                    | T::Int32
                    | T::UInt32
                    | T::Int64
                    | T::UInt64
            ) || (matches!(to, T::Double) && matches!(from, T::Single))
        }
        _ => false,
    }
}

/// `side` without a widening cast to the type `other` already has, which
/// the operator between them would do anyway.
fn implied_cast(
    typer: &Typer<'_, '_>,
    side: &Expr,
    other: &Expr,
    cast_partner: bool,
) -> Option<Expr> {
    let Expr::Cast(to, inner) = side else {
        return None;
    };
    // `(float)(double)u` is how an unsigned value reaches a `float`.
    let inner = match inner.as_ref() {
        Expr::Cast(TypeSig::Double, innermost)
            if matches!(to, TypeSig::Single)
                && matches!(
                    typer.type_of(innermost),
                    Some(TypeSig::UInt32 | TypeSig::UInt64)
                ) =>
        {
            innermost.as_ref()
        }
        other => other,
    };
    if other.is_constant() || (!cast_partner && matches!(other, Expr::Cast(..))) {
        return None;
    }
    let from = typer.type_of(inner)?;
    let partner = typer.type_of(other)?;
    // `(ulong)b + l` on a byte is `b + l` as much as `(long)b + l` is:
    // the zero extension is the same.
    let same_width = partner == *to
        || matches!(
            (&partner, to),
            (TypeSig::Int64, TypeSig::UInt64) | (TypeSig::UInt64, TypeSig::Int64)
        );
    (same_width && implicit_numeric(&from, to) && implicit_numeric(&from, &partner))
        .then(|| inner.clone())
}

/// `new ReadOnlySpan<char>(ref c)`, how .NET 8 concatenates a `char`: `c`.
fn span_over(resolver: Resolver<'_>, expr: &Expr) -> Option<Expr> {
    if let Expr::New { ctor, args, .. } = expr
        && let [Expr::Unary(UnOp::AddressOf, value)] = args.as_slice()
        && matches!(&ctor.declaring, TypeSig::Generic { definition, .. }
            if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                if resolver.raw_name(*token).as_deref() == Some("System.ReadOnlySpan`1")))
    {
        return Some((**value).clone());
    }
    None
}

/// `string.Concat(a, b, c)` as `a + b + c`, or as `$"..."` when literal text
/// is mixed in.
fn concat_expr(
    typer: &Typer<'_, '_>,
    method: &crate::names::MethodRef,
    args: &mut [Expr],
) -> Option<Expr> {
    let resolver = typer.ctx.resolver;
    // .NET 8 concatenates spans: a `char` goes in as a span over it, a
    // string as itself. A span that is neither is no string to add.
    let converted: Vec<Option<Expr>> = args.iter().map(|arg| span_over(resolver, arg)).collect();
    let spans_taken = method
        .sig
        .parameters
        .iter()
        .any(|param| matches!(param, TypeSig::Generic { .. }));
    if spans_taken
        && args.iter().zip(&converted).any(|(arg, value)| {
            value.is_none()
                && !is_string_type(resolver, &typer.type_of(arg).unwrap_or(TypeSig::Object))
        })
    {
        return None;
    }
    let mut chars = 0;
    for (arg, value) in args.iter_mut().zip(converted) {
        if let Some(value) = value {
            *arg = value;
            chars += 1;
        }
    }
    let parts: Vec<Expr> = match args {
        [
            Expr::NewArray {
                items: Some(items), ..
            },
        ] => items.clone(),
        [single] if !matches!(single, Expr::NewArray { .. }) => return None,
        _ => args.to_vec(),
    };
    if parts.len() < 2 {
        return None;
    }
    let mut parts = parts;
    // Two characters added first are a number, not text.
    if chars > 0 && !matches!(parts[0], Expr::Str(_)) && !matches!(parts[1], Expr::Str(_)) {
        let first_is_char = matches!(parts[0], Expr::Char(_) | Expr::Local(_) | Expr::Arg(_));
        if first_is_char {
            parts.insert(0, Expr::Str(String::new()));
        }
    }
    let literals = parts.iter().filter(|p| matches!(p, Expr::Str(_))).count();
    if literals > 0 && literals < parts.len() && parts.len() > 2 {
        let mut pieces = Vec::new();
        for part in parts {
            match part {
                Expr::Str(text) => pieces.push(Interpolation::Text(text)),
                other => pieces.push(Interpolation::Hole(Box::new(other), None)),
            }
        }
        return Some(Expr::Interpolated(pieces));
    }
    parts
        .into_iter()
        .reduce(|a, b| Expr::binary(BinOp::Add, a, b))
}

/// Whether a conversion operator's operand is a type parameter's value:
/// the operator is the constraint's, reached by a plain cast.
fn generic_operand(typer: &Typer<'_, '_>, arg: &Expr) -> bool {
    matches!(typer.type_of(arg), Some(TypeSig::Var(_) | TypeSig::MVar(_)))
}

/// `string.Format("a{0}b", x)` as `$"a{x}b"` when the format is a literal.
fn format_expr(args: &mut [Expr]) -> Option<Expr> {
    let Some((Expr::Str(format), rest)) = args.split_first() else {
        return None;
    };
    let holes: Vec<Expr> = match rest {
        [
            Expr::NewArray {
                items: Some(items), ..
            },
        ] => items.clone(),
        other => other.to_vec(),
    };
    if holes.is_empty() {
        return None;
    }
    let mut pieces = Vec::new();
    let mut text = String::new();
    let mut chars = format.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '{' if chars.peek() == Some(&'{') => {
                chars.next();
                text.push('{');
            }
            '}' if chars.peek() == Some(&'}') => {
                chars.next();
                text.push('}');
            }
            '{' => {
                let mut inner = String::new();
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                    inner.push(c);
                }
                let (number, spec) = inner
                    .split_once([',', ':'])
                    .map_or((inner.as_str(), None), |(n, _)| {
                        (n, Some(inner[n.len()..].to_string()))
                    });
                let index: usize = number.trim().parse().ok()?;
                let hole = holes.get(index)?.clone();
                if !text.is_empty() {
                    pieces.push(Interpolation::Text(std::mem::take(&mut text)));
                }
                pieces.push(Interpolation::Hole(
                    Box::new(hole),
                    spec.map(|s| s.trim_start_matches(',').to_string()),
                ));
            }
            other => text.push(other),
        }
    }
    if !text.is_empty() {
        pieces.push(Interpolation::Text(text));
    }
    Some(Expr::Interpolated(pieces))
}

/// A user-defined operator call as the operator.
fn operator_expr(
    typer: &Typer<'_, '_>,
    operator: &str,
    method: &crate::names::MethodRef,
    args: &mut Vec<Expr>,
) -> Option<Expr> {
    let binary = |op: BinOp, args: &mut Vec<Expr>| {
        if args.len() != 2 {
            return None;
        }
        let right = args.pop()?;
        let left = args.pop()?;
        Some(Expr::binary(op, left, right))
    };
    // A user-defined `==` against `null` is not a reference test: the null
    // is marked as the operand of the operator, so that nothing folds it
    // into `?.` or `??`, which test references.
    let marked = |side: Expr| match side {
        Expr::Null => Expr::Cast(method.declaring.clone(), Box::new(Expr::Null)),
        other => other,
    };
    let compare = |op: Cmp, args: &mut Vec<Expr>| {
        if args.len() != 2 {
            return None;
        }
        let right = args.pop()?;
        let left = args.pop()?;
        if matches!(op, Cmp::Eq | Cmp::Ne) {
            return Some(Expr::compare(op, marked(left), marked(right)));
        }
        Some(Expr::compare(op, left, right))
    };
    match operator {
        "Addition" => binary(BinOp::Add, args),
        "Subtraction" => binary(BinOp::Sub, args),
        "Multiply" => binary(BinOp::Mul, args),
        "Division" => binary(BinOp::Div, args),
        "Modulus" => binary(BinOp::Rem, args),
        "BitwiseAnd" => binary(BinOp::And, args),
        "BitwiseOr" => binary(BinOp::Or, args),
        "ExclusiveOr" => binary(BinOp::Xor, args),
        "LeftShift" => binary(BinOp::Shl, args),
        "RightShift" => binary(BinOp::Shr, args),
        "UnsignedRightShift" => binary(BinOp::UShr, args),
        "Equality" => compare(Cmp::Eq, args),
        "Inequality" => compare(Cmp::Ne, args),
        "LessThan" => compare(Cmp::Lt, args),
        "LessThanOrEqual" => compare(Cmp::Le, args),
        "GreaterThan" => compare(Cmp::Gt, args),
        "GreaterThanOrEqual" => compare(Cmp::Ge, args),
        "UnaryNegation" if args.len() == 1 => args.pop().map(|a| Expr::unary(UnOp::Neg, a)),
        "LogicalNot" if args.len() == 1 => args.pop().map(|a| Expr::unary(UnOp::Not, a)),
        "OnesComplement" if args.len() == 1 => args.pop().map(|a| Expr::unary(UnOp::BitNot, a)),
        "UnaryPlus" if args.len() == 1 => args.pop(),
        // The `checked` operators of C# 11 are the operators in a
        // `checked` context.
        "CheckedAddition" => binary(BinOp::Add, args).map(|e| Expr::Checked(Box::new(e))),
        "CheckedSubtraction" => binary(BinOp::Sub, args).map(|e| Expr::Checked(Box::new(e))),
        "CheckedMultiply" => binary(BinOp::Mul, args).map(|e| Expr::Checked(Box::new(e))),
        "CheckedDivision" => binary(BinOp::Div, args).map(|e| Expr::Checked(Box::new(e))),
        "CheckedUnaryNegation" if args.len() == 1 => args
            .pop()
            .map(|a| Expr::Checked(Box::new(Expr::unary(UnOp::Neg, a)))),
        "CheckedExplicit" if args.len() == 1 => {
            let arg = args.pop()?;
            let returns = substitute(&method.sig.returns, &method.declaring, &method.type_args);
            Some(Expr::CheckedCast(returns, Box::new(arg)))
        }
        "Implicit" if args.len() == 1 => {
            // An implicit conversion is what the source left unsaid, but
            // only where the type it converts to is wanted: given to an
            // `object` (a string's `+`, an interpolation) the value would go
            // unconverted, and `(int)mask + " "` print `Mask`. Said as a
            // cast it means the same everywhere.
            let arg = args.pop()?;
            let returns = substitute(&method.sig.returns, &method.declaring, &method.type_args);
            if generic_operand(typer, &arg) {
                return Some(Expr::OperatorCast(returns, Box::new(arg)));
            }
            Some(Expr::Cast(returns, Box::new(arg)))
        }
        "Explicit" if args.len() == 1 => {
            let arg = args.pop()?;
            let returns = substitute(&method.sig.returns, &method.declaring, &method.type_args);
            if generic_operand(typer, &arg) {
                return Some(Expr::OperatorCast(returns, Box::new(arg)));
            }
            Some(Expr::Cast(returns, Box::new(arg)))
        }
        _ => None,
    }
}
