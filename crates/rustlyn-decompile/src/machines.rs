//! Iterators and `async` methods back out of their state machines.
//!
//! A method with `yield` or `await` in it is compiled into a class or
//! struct whose `MoveNext` runs the body one piece at a time: a state field
//! says where to resume, a switch at the top jumps there, every `yield
//! return` stores the value and the next state and returns, every `await`
//! that is not already complete stores the awaiter and returns. The locals
//! that live across those returns become fields.
//!
//! Read the other way, `MoveNext` is the body with the machinery around it:
//! run it as if from the first state, so the dispatch has one answer and
//! the resume points are simply the next statements; take the stores and
//! returns that end a piece as `yield return` and `await`; give the hoisted
//! fields their names back as locals. What is left is the method as it was
//! written, with `yield` and `await` where they were.

use std::collections::{HashMap, HashSet};

use rustlyn_metadata::body::{Handler, Region};
use rustlyn_metadata::signature::{Blob, TypeSig};
use rustlyn_metadata::table;

use crate::ir::{BinOp, Cmp, Expr, Stmt, UnOp};
use crate::names::Resolver;
use crate::stack::{Block, Blocks, MethodContext, Terminator};
use crate::{Decompiled, Options};

/// Which kind of machine a method was compiled into.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Iterator,
    Async,
}

/// A state machine behind a method.
#[derive(Clone, Copy, Debug)]
pub struct Machine {
    pub kind: Kind,
    /// Whether the async machine is an async iterator: it yields through a
    /// promise rather than returning once.
    pub async_iterator: bool,
    /// The `TypeDef` row of the machine.
    pub type_row: u32,
    /// The `MethodDef` row of its `MoveNext`.
    pub move_next: u32,
}

/// The machine a method starts, judged by the body it was given: one that
/// constructs a nested compiler-made type with a `<>1__state` field, or
/// holds one that is a struct in a local.
#[must_use]
pub fn machine_of(resolver: Resolver<'_>, body: &Decompiled<'_>) -> Option<Machine> {
    let mut candidate: Option<u32> = None;
    let mut note = |ty: &TypeSig| {
        if candidate.is_some() {
            return;
        }
        let token = match ty {
            TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
                _ => return,
            },
            _ => return,
        };
        if token.table() == table::TYPE_DEF && is_machine_type(resolver, token.row()) {
            candidate = Some(token.row());
        }
    };
    for stmt in &body.stmts {
        stmt.walk_exprs(&mut |e| {
            if let Expr::New { ctor, .. } = e {
                note(&ctor.declaring);
            }
        });
    }
    // A struct machine (Roslyn's release build) is a local the method never
    // constructs. A class machine is started only by the method that makes
    // it: a lambda holding a reference to the machine around it, as one in a
    // generic async method does, does not start it, and folding the machine
    // into it would nest the method inside itself without end.
    for ty in &body.ctx.locals {
        let struct_machine = match ty {
            TypeSig::ValueType(_) => true,
            TypeSig::Generic { definition, .. } => {
                matches!(definition.as_ref(), TypeSig::ValueType(_))
            }
            _ => false,
        };
        if struct_machine {
            note(ty);
        }
    }
    let type_row = candidate?;
    let heaps = resolver.assembly.heaps();
    let kind = if resolver
        .fields_of(type_row)
        .iter()
        .any(|(_, field)| heaps.string(field.number(1)) == "<>t__builder")
    {
        Kind::Async
    } else {
        Kind::Iterator
    };
    let move_next = resolver
        .methods_of(type_row)
        .into_iter()
        .find(|(_, method)| {
            let name = heaps.string(method.number(3));
            name == "MoveNext" || name.ends_with(".MoveNext")
        })
        .map(|(row, _)| row)?;
    let async_iterator = resolver
        .fields_of(type_row)
        .iter()
        .any(|(_, field)| heaps.string(field.number(1)) == "<>v__promiseOfValueOrEnd");
    Some(Machine {
        kind,
        async_iterator,
        type_row,
        move_next,
    })
}

/// Whether a type is a compiler-made state machine.
fn is_machine_type(resolver: Resolver<'_>, type_row: u32) -> bool {
    let name = resolver.type_def_simple_name(type_row);
    let heaps = resolver.assembly.heaps();
    (name.starts_with('<') || name.contains("d__"))
        && resolver.enclosing_type(type_row).is_some()
        && resolver
            .fields_of(type_row)
            .iter()
            .any(|(_, field)| heaps.string(field.number(1)) == "<>1__state")
}

/// What a field of the machine stands for in the method.
#[derive(Clone, Debug)]
enum Role {
    State,
    Current,
    Builder,
    Awaiter,
    Disposing,
    This,
    Parameter(u16),
    /// Machinery with nothing of the source in it: the statements that use
    /// it go.
    Machinery,
    /// A hoisted local, with the name it had.
    Local(String),
    Other,
}

/// The body of the method the machine was made from.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn machine_body<'a>(
    resolver: Resolver<'a>,
    machine: Machine,
    outer_row: u32,
    options: &Options,
) -> Option<Decompiled<'a>> {
    let heaps = resolver.assembly.heaps();
    let outer = resolver.assembly.table(table::METHOD_DEF).row(outer_row)?;
    let outer_sig = resolver.method_sig_at(outer.number(4))?;
    let outer_params = crate::param_names(resolver, outer_row, outer_sig.parameters.len());
    let outer_owner = resolver.method_owner(outer_row)?;

    // `MoveNext` as the machine sees it.
    let move_next = resolver
        .assembly
        .table(table::METHOD_DEF)
        .row(machine.move_next)?;
    let body = crate::body_of(resolver, machine.move_next)?;
    let mn_sig = resolver.method_sig_at(move_next.number(4))?;
    let mn_locals: Vec<TypeSig> = match body.locals {
        Some(token) => resolver
            .assembly
            .row(token)
            .and_then(|row| heaps.blob(row.number(0)).ok())
            .and_then(|bytes| Blob::new(bytes).locals_sig().ok())
            .unwrap_or_default(),
        None => Vec::new(),
    };
    let mut machine_this = resolver.declared_type_sig(machine.type_row);
    if resolver.is_value_type(&machine_this) {
        machine_this = TypeSig::ByRef(Box::new(machine_this));
    }
    let mn_ctx = MethodContext {
        resolver,
        generics: resolver.generics_of(machine.move_next),
        is_static: false,
        this_type: machine_this,
        params: mn_sig.parameters.clone(),
        locals: mn_locals.clone(),
        returns: mn_sig.returns.clone(),
    };
    let mut blocks = crate::stack::read(&mn_ctx, &body);
    if std::env::var_os("RUSTLYN_DECOMPILE_DEBUG").is_some() {
        for block in &blocks.blocks {
            eprintln!(
                "-- machine block IL_{:04x}..IL_{:04x}",
                block.start, block.end
            );
            for stmt in &block.stmts {
                eprint!("{}", crate::print::stmt_text(&mn_ctx, stmt));
            }
            eprintln!("   -> {:?}", block.terminator);
        }
    }

    // The fields, by role.
    let mut roles: HashMap<String, Role> = HashMap::new();
    let mut extra_locals: Vec<TypeSig> = Vec::new();
    let mut hints: HashMap<u16, String> = HashMap::new();
    let mut field_locals: HashMap<String, u16> = HashMap::new();
    for (_, field) in resolver.fields_of(machine.type_row) {
        let name = heaps.string(field.number(1)).to_string();
        let role = match name.as_str() {
            "<>1__state" => Role::State,
            "<>2__current" => Role::Current,
            "<>t__builder" => Role::Builder,
            "<>4__this" => Role::This,
            "<>w__disposing" | "<>w__disposeMode" => Role::Disposing,
            // An async iterator's promise and the token it links.
            "<>v__promiseOfValueOrEnd" | "<>x__combinedTokens" => Role::Machinery,
            _ if name.starts_with("<>u__") => Role::Awaiter,
            _ if name.starts_with("<>3__") || name == "<>l__initialThreadId" => Role::Other,
            _ => match outer_params.iter().position(|p| *p == name) {
                Some(at) => Role::Parameter(at as u16),
                None => Role::Local(hoisted_name(&name)),
            },
        };
        roles.insert(name, role);
    }

    // The local that holds a copy of the state, and the state a fresh
    // machine starts in.
    let fresh = match machine.kind {
        Kind::Iterator => 0,
        Kind::Async => -1,
    };
    let mut state_local: Option<u16> = None;
    if let Some(first) = blocks.blocks.first()
        && let Some(Stmt::Expr(Expr::Assign(target, value))) =
            first.stmts.iter().find(|s| !matches!(s, Stmt::Label(_)))
        && let Expr::Local(local) = target.as_ref()
        && is_field(value, &roles, |role| matches!(role, Role::State))
    {
        state_local = Some(*local);
    }

    // Regions the machinery made: the fault handler that disposes an
    // iterator, the catch that reports an async method's exception.
    let mut dropped_regions: Vec<Region> = Vec::new();
    let mut kept_regions: Vec<Region> = Vec::new();
    for region in &body.regions {
        let handler_blocks: Vec<&Block> = blocks
            .blocks
            .iter()
            .filter(|b| {
                b.start >= region.handler_offset
                    && b.start < region.handler_offset + region.handler_length
            })
            .collect();
        let machinery = match region.kind {
            Handler::Fault => machine.kind == Kind::Iterator,
            Handler::Catch(_) => handler_blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    let mut found = false;
                    s.walk_exprs(&mut |e| {
                        if let Expr::Call { method, .. } = e
                            && method.name == "SetException"
                        {
                            found = true;
                        }
                    });
                    found
                })
            }),
            _ => false,
        };
        if machinery {
            dropped_regions.push(*region);
        } else {
            kept_regions.push(*region);
        }
    }

    // Which blocks end by returning `true`, directly or through a jump to a
    // shared `return` block after storing `true` into its local.
    let returns_true: HashSet<u32> = {
        let mut found = HashSet::new();
        for block in &blocks.blocks {
            match &block.terminator {
                Terminator::Return(Some(Expr::Bool(true))) => {
                    found.insert(block.start);
                }
                Terminator::Jump(target) | Terminator::Leave(target) => {
                    let Some(at) = blocks.index_of(*target) else {
                        continue;
                    };
                    let landing = &blocks.blocks[at];
                    // `ldc.i4.1; ret` shared by every yield, or `ldloc r; ret`
                    // after `r = true` here.
                    let shared_true = landing.stmts.is_empty()
                        && matches!(
                            landing.terminator,
                            Terminator::Return(Some(Expr::Bool(true)))
                        );
                    let through_local = if let Some(Stmt::Expr(Expr::Assign(place, value))) =
                        block.stmts.last()
                        && **value == Expr::Bool(true)
                        && let Expr::Local(local) = **place
                    {
                        landing.stmts.is_empty()
                            && matches!(&landing.terminator, Terminator::Return(Some(Expr::Local(found))) if *found == local)
                    } else {
                        false
                    };
                    if shared_true || through_local {
                        found.insert(block.start);
                    }
                }
                _ => {}
            }
        }
        found
    };
    // A `leave` out of a region the machinery made is a plain jump.
    for block in &mut blocks.blocks {
        if let Terminator::Leave(target) = block.terminator
            && !kept_regions.iter().any(|region| {
                block.start >= region.try_offset
                    && block.start < region.try_offset + region.try_length
                    || block.start >= region.handler_offset
                        && block.start < region.handler_offset + region.handler_length
            })
        {
            block.terminator = Terminator::Jump(target);
        }
    }

    // An async iterator yields by storing the value, completing its promise
    // with `true` in a shared block, and returning.
    let mut returns_true = returns_true;
    if machine.async_iterator {
        let promises_true: HashSet<u32> = blocks
            .blocks
            .iter()
            .filter(|block| {
                block.stmts.iter().any(|stmt| {
                    matches!(stmt, Stmt::Expr(Expr::Call { method, receiver: Some(receiver), args })
                        if method.name == "SetResult"
                            && is_field(receiver, &roles, |role| matches!(role, Role::Machinery))
                            && matches!(args.as_slice(), [Expr::Bool(true) | Expr::Int(1)]))
                })
            })
            .map(|block| block.start)
            .collect();
        for block in &blocks.blocks {
            if let Terminator::Jump(target) | Terminator::Leave(target) = block.terminator
                && promises_true.contains(&target)
            {
                returns_true.insert(block.start);
            }
        }
    }

    // Pass 1: the state's answers, the machinery's statements, the awaits.
    let mut removed: HashSet<u32> = HashSet::new();
    for region in &dropped_regions {
        for block in &blocks.blocks {
            if block.start >= region.handler_offset
                && block.start < region.handler_offset + region.handler_length
            {
                removed.insert(block.start);
            }
        }
    }
    let mut awaiter_sources: HashMap<u16, Expr> = HashMap::new();
    let block_count = blocks.blocks.len();
    for index in 0..block_count {
        let next_start = blocks.blocks.get(index + 1).map(|b| b.start);
        let block = &mut blocks.blocks[index];
        let mut kept: Vec<Stmt> = Vec::new();
        let mut suspends = false;
        let mut yielded = false;
        for stmt in std::mem::take(&mut block.stmts) {
            if machine.async_iterator {
                // The promise, the linked token, the builder's completion.
                let mut machinery = false;
                stmt.walk_exprs(&mut |e| {
                    machinery |= is_field(e, &roles, |role| matches!(role, Role::Machinery));
                });
                if machinery
                    || matches!(&stmt, Stmt::Expr(Expr::Call { method, receiver: Some(receiver), .. })
                        if method.name == "Complete"
                            && is_field(receiver, &roles, |role| matches!(role, Role::Builder)))
                {
                    continue;
                }
                // `disposeMode = true` and away to the end: `yield break`.
                if let Stmt::Expr(Expr::Assign(target, value)) = &stmt
                    && is_field(target, &roles, |role| matches!(role, Role::Disposing))
                {
                    if matches!(value.as_ref(), Expr::Bool(true) | Expr::Int(1)) {
                        kept.push(Stmt::YieldBreak);
                    }
                    continue;
                }
                // The current value cleared at the end.
                if let Stmt::Expr(Expr::Assign(target, _)) = &stmt
                    && is_field(target, &roles, |role| matches!(role, Role::Current))
                    && !returns_true.contains(&block.start)
                {
                    continue;
                }
            }
            match &stmt {
                Stmt::Expr(Expr::Assign(target, value)) => {
                    // `state = N` at a resume or a yield says nothing; a
                    // negative state inside an iterator marks a `try`.
                    if is_field(target, &roles, |role| matches!(role, Role::State)) {
                        if let Expr::Int(state) = value.as_ref()
                            && *state <= -3
                            && machine.kind == Kind::Iterator
                        {
                            kept.push(Stmt::EnterTry(*state));
                        }
                        continue;
                    }
                    if let Expr::Local(local) = target.as_ref()
                        && Some(*local) == state_local
                    {
                        continue;
                    }
                    if is_field(target, &roles, |role| matches!(role, Role::Awaiter)) {
                        continue;
                    }
                    // `<>7__wrap = null` clears a hoisted local after use.
                    if is_field(target, &roles, |role| matches!(role, Role::Local(_)))
                        && matches!(value.as_ref(), Expr::Null | Expr::Default(_))
                        && field_name(target).is_some_and(|n| n.starts_with("<>7__wrap"))
                    {
                        continue;
                    }
                    // `awaiter = task.GetAwaiter()` is remembered for the
                    // `GetResult` that follows.
                    if let Expr::Local(local) = target.as_ref()
                        && let Expr::Call {
                            method,
                            receiver: Some(receiver),
                            ..
                        } = value.as_ref()
                        && method.name == "GetAwaiter"
                        && machine.kind == Kind::Async
                    {
                        awaiter_sources.insert(*local, strip_address((**receiver).clone()));
                        continue;
                    }
                    // `current = v; state = N; return true` is `yield return v`.
                    if is_field(target, &roles, |role| matches!(role, Role::Current))
                        && returns_true.contains(&block.start)
                    {
                        kept.push(Stmt::YieldReturn((**value).clone()));
                        block.terminator = Terminator::Fall;
                        yielded = true;
                        continue;
                    }
                    // The `true` stored for the shared return block.
                    if yielded
                        && **value == Expr::Bool(true)
                        && matches!(target.as_ref(), Expr::Local(_))
                    {
                        continue;
                    }
                }
                Stmt::Expr(Expr::Call {
                    method,
                    receiver,
                    args,
                }) => {
                    let name = method.name.as_str();
                    if name == "AwaitUnsafeOnCompleted" || name == "AwaitOnCompleted" {
                        suspends = true;
                        continue;
                    }
                    if name == "SetStateMachine" {
                        continue;
                    }
                    if name == "SetResult"
                        && receiver.as_deref().is_some_and(|r| {
                            is_field(r, &roles, |role| matches!(role, Role::Builder))
                        })
                    {
                        block.terminator = Terminator::Return(args.first().cloned());
                        continue;
                    }
                }
                _ => {}
            }
            // An awaiter variable is reused by every `await` of its type:
            // `GetResult` is the await of the task last asked, in order.
            let mut stmt = stmt;
            if machine.kind == Kind::Async {
                stmt.map_exprs(&mut |e| await_in_place(e, &awaiter_sources));
            }
            kept.push(stmt);
        }
        block.stmts = kept;
        if machine.kind == Kind::Async {
            match &mut block.terminator {
                Terminator::Cond { condition, .. } => {
                    condition.map(&mut |e| await_in_place(e, &awaiter_sources));
                }
                Terminator::Switch { value, .. } | Terminator::Return(Some(value)) => {
                    value.map(&mut |e| await_in_place(e, &awaiter_sources));
                }
                _ => {}
            }
        }
        if suspends {
            removed.insert(block.start);
        }

        // The dispatch, answered for a fresh machine; a check of the
        // awaiter, answered as completed; a disposing check, answered no.
        // Inside a `finally` the state is the one a completing machine
        // has, since that is when a finally of the source runs.
        let block_start = block.start;
        let in_finally = kept_regions.iter().any(|region| {
            matches!(region.kind, Handler::Finally | Handler::Fault)
                && block_start >= region.handler_offset
                && block_start < region.handler_offset + region.handler_length
        });
        let seen_state = if in_finally { -1 } else { fresh };
        let answer = |condition: &Expr| -> Option<bool> {
            if mentions_state(condition, state_local, &roles) {
                return eval_state(condition, state_local, &roles, seen_state);
            }
            if mentions_field(condition, &roles, |role| matches!(role, Role::Disposing)) {
                return eval_disposing(condition, &roles);
            }
            if machine.kind == Kind::Async && mentions_is_completed(condition) {
                return eval_is_completed(condition);
            }
            // `if (combinedTokens != null)`: the machinery is never there.
            if let Expr::Compare {
                op: op @ (Cmp::Eq | Cmp::Ne),
                left,
                right,
                ..
            } = condition
                && is_field(left, &roles, |role| matches!(role, Role::Machinery))
                && **right == Expr::Null
            {
                return Some(*op == Cmp::Eq);
            }
            None
        };
        match &block.terminator {
            Terminator::Cond { condition, target } => {
                if let Some(taken) = answer(condition) {
                    block.terminator = if taken {
                        Terminator::Jump(*target)
                    } else {
                        Terminator::Fall
                    };
                }
            }
            Terminator::Switch { value, targets } if mentions_state(value, state_local, &roles) => {
                let target = usize::try_from(fresh)
                    .ok()
                    .and_then(|at| targets.get(at).copied());
                block.terminator = match target {
                    Some(target) => Terminator::Jump(target),
                    None => Terminator::Fall,
                };
            }
            _ => {}
        }
        let _ = next_start;
    }

    // Pass 2: reachability from the entry over the kept regions; whatever
    // only the dispatch reached, resume points and suspensions, goes.
    let reachable = reachable_blocks(&blocks, &kept_regions, &removed);
    blocks
        .blocks
        .retain(|block| reachable.contains(&block.start));
    // A jump to the block that now follows is a fall-through.
    let starts: Vec<u32> = blocks.blocks.iter().map(|b| b.start).collect();
    for (index, block) in blocks.blocks.iter_mut().enumerate() {
        if let Terminator::Jump(target) = block.terminator
            && starts.get(index + 1) == Some(&target)
        {
            block.terminator = Terminator::Fall;
        }
    }

    // Pass 3: `awaiter.GetResult()` is `await task`, and the fields are
    // the method's own variables again.
    let outer_this = {
        let ty = resolver.declared_type_sig(outer_owner);
        if resolver.is_value_type(&ty) {
            TypeSig::ByRef(Box::new(ty))
        } else {
            ty
        }
    };
    let allocate = |name: &str,
                    ty: &TypeSig,
                    field_locals: &mut HashMap<String, u16>,
                    extra_locals: &mut Vec<TypeSig>,
                    hints: &mut HashMap<u16, String>|
     -> u16 {
        if let Some(found) = field_locals.get(name) {
            return *found;
        }
        let local = (mn_locals.len() + extra_locals.len()) as u16;
        extra_locals.push(ty.clone());
        if let Some(Role::Local(hint)) = roles.get(name) {
            hints.insert(local, hint.clone());
        }
        field_locals.insert(name.to_string(), local);
        local
    };
    let mut finally_bodies: HashMap<String, Vec<Stmt>> = if machine.kind == Kind::Iterator {
        finally_methods(resolver, machine.type_row, options, &roles)
    } else {
        HashMap::new()
    };
    let mut rewrite = |expr: &mut Expr| {
        if let Expr::Call {
            method,
            receiver: Some(receiver),
            ..
        } = expr
            && method.name == "GetResult"
            && let Expr::Local(local) = strip_address((**receiver).clone())
            && let Some(source) = awaiter_sources.get(&local)
        {
            *expr = Expr::Await(Box::new(source.clone()));
            return;
        }
        if let Expr::Field {
            receiver: Some(receiver),
            field,
        } = expr
            && **receiver == Expr::This
        {
            match roles.get(&field.name) {
                Some(Role::This) => *expr = Expr::This,
                Some(Role::Parameter(at)) => *expr = Expr::Arg(*at),
                Some(Role::Local(_)) | Some(Role::Other) | Some(Role::Current) => {
                    let ty = crate::stack::substitute(&field.ty, &field.declaring, &[]);
                    let local = allocate(
                        &field.name,
                        &ty,
                        &mut field_locals,
                        &mut extra_locals,
                        &mut hints,
                    );
                    *expr = Expr::Local(local);
                }
                _ => {}
            }
        }
    };
    // Twice: an `await` put in place carries a source that still reads
    // the fields.
    for _ in 0..2 {
        for body in finally_bodies.values_mut() {
            for stmt in body.iter_mut() {
                stmt.map_exprs(&mut rewrite);
            }
        }
        for block in &mut blocks.blocks {
            for stmt in &mut block.stmts {
                stmt.map_exprs(&mut rewrite);
            }
            match &mut block.terminator {
                Terminator::Cond { condition, .. } => condition.map(&mut rewrite),
                Terminator::Switch { value, .. } => value.map(&mut rewrite),
                Terminator::Return(Some(value))
                | Terminator::Throw(value)
                | Terminator::EndFilter(value) => {
                    value.map(&mut rewrite);
                }
                _ => {}
            }
        }
    }

    // The method as it reads now: the outer method's parameters and type,
    // `MoveNext`'s locals and the hoisted ones.
    let mut locals = mn_locals;
    locals.extend(extra_locals);
    // The machine's type parameters are the method's, its type's first:
    // `!0` in a hoisted field's type is what the method calls `T`.
    let mut generics = resolver.generics_of(outer_row);
    let machine_params = resolver.type_generics(machine.type_row);
    if !machine_params.is_empty() {
        generics.type_params = machine_params;
    }
    let ctx = MethodContext {
        resolver,
        generics,
        is_static: outer.number(2) & 0x0010 != 0,
        this_type: outer_this,
        params: outer_sig.parameters.clone(),
        locals,
        returns: outer_sig.returns.clone(),
    };
    let blocks = Blocks {
        blocks: blocks.blocks,
        slot_types: blocks.slot_types,
    };
    if std::env::var_os("RUSTLYN_DECOMPILE_DEBUG").is_some() {
        for block in &blocks.blocks {
            eprintln!(
                "-- machine block after IL_{:04x}..IL_{:04x}",
                block.start, block.end
            );
            for stmt in &block.stmts {
                eprint!("{}", crate::print::stmt_text(&ctx, stmt));
            }
            eprintln!("   -> {:?}", block.terminator);
        }
    }
    let mut stmts = crate::structure::structure(resolver, &blocks, &kept_regions, body.code_size);
    if std::env::var_os("RUSTLYN_DECOMPILE_DEBUG").is_some() {
        eprintln!("-- machine structured");
        for stmt in &stmts {
            eprint!("{}", crate::print::stmt_text(&ctx, stmt));
        }
    }
    if machine.kind == Kind::Iterator {
        yield_breaks(&mut stmts);
        fold_iterator_tries(&mut stmts, &finally_bodies);
        strip_try_markers(&mut stmts);
    }
    drop_final_clears(&mut stmts, &field_locals);
    let typer = crate::simplify::Typer {
        ctx: &ctx,
        slot_types: &blocks.slot_types,
        extra_locals: std::cell::RefCell::new(Vec::new()),
        hints: std::cell::RefCell::new(hints),
    };
    crate::closures::inline(&typer, options, &mut stmts);
    // A lambda in the method reads the variables hoisted into the machine
    // through the machine (`CS$<>8__locals.<count>5__1`): folded in, those
    // reads are the method's variables too, as the method's own were made.
    let machine_type = machine.type_row;
    let is_machine_field = |field: &crate::names::FieldRef| {
        let token = match &field.declaring {
            TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
                _ => return false,
            },
            _ => return false,
        };
        token.table() == table::TYPE_DEF && token.row() == machine_type
    };
    for stmt in &mut stmts {
        stmt.map_exprs(&mut |e| {
            if let Expr::Field {
                receiver: Some(_),
                field,
            } = e
                && is_machine_field(field)
            {
                match roles.get(&field.name) {
                    Some(Role::This) => *e = Expr::This,
                    Some(Role::Parameter(at)) => *e = Expr::Arg(*at),
                    _ => {
                        if let Some(local) = field_locals.get(&field.name) {
                            *e = Expr::Local(*local);
                        }
                    }
                }
            }
        });
    }
    drop_unread_machine_copies(&mut stmts);
    crate::simplify::simplify(&typer, &mut stmts);
    drop_final_clears(&mut stmts, &field_locals);
    drop_dead_clears(&mut stmts, &field_locals);
    crate::simplify::simplify(&typer, &mut stmts);
    if machine.kind == Kind::Iterator {
        yield_breaks(&mut stmts);
    }
    if machine.kind == Kind::Iterator || machine.async_iterator {
        // A `yield break` at the very end says nothing, at the end of a
        // `using` that is the last statement included.
        drop_trailing_yield_breaks(&mut stmts);
    }
    if matches!(stmts.last(), Some(Stmt::Return(None))) {
        stmts.pop();
    }
    let extras = typer.extra_locals.into_inner();
    let local_hints = typer.hints.into_inner();
    let mut ctx = ctx;
    ctx.locals.extend(extras);
    let mut consumed = options.consumed.borrow_mut();
    consumed.types.insert(machine.type_row);
    consumed.machines.insert(machine.type_row);
    drop(consumed);
    Some(Decompiled {
        stmts,
        param_names: outer_params,
        local_hints,
        ctx,
        slot_types: blocks.slot_types,
        is_async: machine.kind == Kind::Async,
        base_call_is_trivial: false,
    })
}

/// `awaiter.GetResult()` as `await task`, for the task the awaiter was
/// last taken from.
fn await_in_place(expr: &mut Expr, sources: &HashMap<u16, Expr>) {
    if let Expr::Call {
        method,
        receiver: Some(receiver),
        ..
    } = expr
        && method.name == "GetResult"
        && let Expr::Local(local) = strip_address((**receiver).clone())
        && let Some(source) = sources.get(&local)
    {
        *expr = Expr::Await(Box::new(source.clone()));
    }
}

/// `seen` out of `<seen>5__2`, `wrap` out of `<>7__wrap2`.
fn hoisted_name(field: &str) -> String {
    if let Some(rest) = field.strip_prefix('<')
        && let Some((name, _)) = rest.split_once('>')
        && !name.is_empty()
    {
        // `<<walked>2>5__3`: a name the compiler itself made up, nested.
        return hoisted_name(name);
    }
    if field.starts_with("<>7__wrap") {
        return "wrap".into();
    }
    if field.starts_with("<>s__") {
        return "spill".into();
    }
    field.to_string()
}

fn field_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Field {
            receiver: Some(receiver),
            field,
        } if **receiver == Expr::This => Some(field.name.as_str()),
        _ => None,
    }
}

/// Whether the expression reads a machine field of the given role.
fn is_field(expr: &Expr, roles: &HashMap<String, Role>, wanted: impl Fn(&Role) -> bool) -> bool {
    field_name(expr).is_some_and(|name| roles.get(name).is_some_and(&wanted))
}

fn mentions_field(
    expr: &Expr,
    roles: &HashMap<String, Role>,
    wanted: impl Fn(&Role) -> bool + Copy,
) -> bool {
    expr.count(&|e| is_field(e, roles, wanted)) > 0
}

fn mentions_state(expr: &Expr, state_local: Option<u16>, roles: &HashMap<String, Role>) -> bool {
    expr.count(&|e| {
        matches!(e, Expr::Local(local) if Some(*local) == state_local)
            || is_field(e, roles, |role| matches!(role, Role::State))
    }) > 0
}

fn is_completed_check(expr: &Expr) -> bool {
    matches!(expr, Expr::Property { name, .. } if name == "IsCompleted")
        || matches!(expr, Expr::Call { method, args, .. }
            if method.name == "get_IsCompleted" && args.is_empty())
}

fn mentions_is_completed(expr: &Expr) -> bool {
    expr.count(&is_completed_check) > 0
}

/// A condition on the state, evaluated for a fresh machine.
fn eval_state(
    expr: &Expr,
    state_local: Option<u16>,
    roles: &HashMap<String, Role>,
    fresh: i64,
) -> Option<bool> {
    let value = |e: &Expr| -> Option<i64> {
        match e {
            Expr::Local(local) if Some(*local) == state_local => Some(fresh),
            Expr::Int(n) => Some(*n),
            _ if is_field(e, roles, |role| matches!(role, Role::State)) => Some(fresh),
            _ => None,
        }
    };
    match expr {
        Expr::Compare {
            op,
            left,
            right,
            unordered,
            ..
        } => {
            let (a, b) = (value(left)?, value(right)?);
            // An unsigned comparison, `(uint)state <= 1`: -1 is past 1.
            let (a, b) = if *unordered {
                (i64::from(a as u32), i64::from(b as u32))
            } else {
                (a, b)
            };
            Some(match op {
                Cmp::Eq => a == b,
                Cmp::Ne => a != b,
                Cmp::Lt => a < b,
                Cmp::Le => a <= b,
                Cmp::Gt => a > b,
                Cmp::Ge => a >= b,
            })
        }
        Expr::Unary(UnOp::Not, inner) => eval_state(inner, state_local, roles, fresh).map(|b| !b),
        Expr::Binary(BinOp::LogicalAnd, a, b) => Some(
            eval_state(a, state_local, roles, fresh)? && eval_state(b, state_local, roles, fresh)?,
        ),
        Expr::Binary(BinOp::LogicalOr, a, b) => Some(
            eval_state(a, state_local, roles, fresh)? || eval_state(b, state_local, roles, fresh)?,
        ),
        _ => None,
    }
}

/// A condition on the disposing flag, evaluated as not disposing.
fn eval_disposing(expr: &Expr, roles: &HashMap<String, Role>) -> Option<bool> {
    match expr {
        _ if is_field(expr, roles, |role| matches!(role, Role::Disposing)) => Some(false),
        Expr::Unary(UnOp::Not, inner) => eval_disposing(inner, roles).map(|b| !b),
        Expr::Compare {
            op: Cmp::Eq,
            left,
            right,
            ..
        } if **right == Expr::Bool(false) => eval_disposing(left, roles).map(|b| !b),
        _ => None,
    }
}

/// A condition on an awaiter's completion, evaluated as completed.
fn eval_is_completed(expr: &Expr) -> Option<bool> {
    match expr {
        e if is_completed_check(e) => Some(true),
        Expr::Unary(UnOp::Not, inner) => eval_is_completed(inner).map(|b| !b),
        _ => None,
    }
}

fn strip_address(expr: Expr) -> Expr {
    match expr {
        Expr::Unary(UnOp::AddressOf, inner) => *inner,
        other => other,
    }
}

/// The blocks control can reach from the entry and the kept handlers,
/// never entering a removed one.
fn reachable_blocks(blocks: &Blocks, regions: &[Region], removed: &HashSet<u32>) -> HashSet<u32> {
    let mut reachable: HashSet<u32> = HashSet::new();
    let mut queue: Vec<u32> = vec![0];
    for region in regions {
        queue.push(region.handler_offset);
        if let Handler::Filter(at) = region.kind {
            queue.push(at);
        }
    }
    while let Some(start) = queue.pop() {
        if removed.contains(&start) || !reachable.insert(start) {
            continue;
        }
        let Some(index) = blocks.index_of(start) else {
            continue;
        };
        let block = &blocks.blocks[index];
        let next = blocks.blocks.get(index + 1).map(|b| b.start);
        match &block.terminator {
            Terminator::Fall => queue.extend(next),
            Terminator::Jump(target) | Terminator::Leave(target) => queue.push(*target),
            Terminator::Cond { target, .. } => {
                queue.push(*target);
                queue.extend(next);
            }
            Terminator::Switch { targets, .. } => {
                queue.extend(targets.iter().copied());
                queue.extend(next);
            }
            Terminator::EndFilter(_) => queue.extend(next),
            _ => {}
        }
    }
    reachable
}

/// Removes the `yield break` that ends a body, looking into a `using` or
/// `try` that is the last statement.
fn drop_trailing_yield_breaks(stmts: &mut Vec<Stmt>) {
    while matches!(stmts.last(), Some(Stmt::YieldBreak)) {
        stmts.pop();
    }
    match stmts.last_mut() {
        Some(Stmt::Using { body, .. }) => drop_trailing_yield_breaks(body),
        Some(Stmt::Try { body, catches, .. }) if catches.is_empty() => {
            drop_trailing_yield_breaks(body);
        }
        _ => {}
    }
}

/// `return false` in an iterator is `yield break`.
fn yield_breaks(stmts: &mut [Stmt]) {
    for stmt in stmts.iter_mut() {
        if matches!(stmt, Stmt::Return(Some(Expr::Bool(false)))) {
            *stmt = Stmt::YieldBreak;
        }
        for block in stmt.blocks_mut() {
            yield_breaks(block);
        }
    }
}

/// The bodies of the `<>m__FinallyN` methods, by their number, decompiled
/// with the machine's fields read as the method's variables.
fn finally_methods(
    resolver: Resolver<'_>,
    type_row: u32,
    options: &Options,
    roles: &HashMap<String, Role>,
) -> HashMap<String, Vec<Stmt>> {
    let heaps = resolver.assembly.heaps();
    let mut bodies = HashMap::new();
    for (row, method) in resolver.methods_of(type_row) {
        let name = heaps.string(method.number(3)).to_string();
        if !name.starts_with("<>m__Finally") {
            continue;
        }
        let mut inner_options = options.clone();
        inner_options.depth += 1;
        let Some(inner) = crate::decompile_body(resolver, row, &inner_options) else {
            continue;
        };
        let mut stmts = inner.stmts;
        // Only the state assignment and the field reads need mapping; the
        // locals of a finally method are few and renumbered past the body's.
        stmts.retain(|stmt| {
            !matches!(stmt, Stmt::Expr(Expr::Assign(target, _)) if is_field(target, roles, |role| matches!(role, Role::State)))
        });
        bodies.insert(name, stmts);
        options.consumed.borrow_mut().methods.insert(row);
    }
    bodies
}

/// `v = this;` in a lambda, where `v` held the machine the lambda read
/// hoisted variables through: with those reads made the method's own
/// variables, nothing reads `v`.
fn drop_unread_machine_copies(stmts: &mut Vec<Stmt>) {
    let mut reads: HashMap<u16, usize> = HashMap::new();
    let mut copies: HashMap<u16, usize> = HashMap::new();
    for stmt in stmts.iter() {
        stmt.walk_exprs(&mut |e| match e {
            Expr::Local(local) => *reads.entry(*local).or_default() += 1,
            Expr::Assign(target, value) if **value == Expr::This => {
                if let Expr::Local(local) = target.as_ref() {
                    *copies.entry(*local).or_default() += 1;
                }
            }
            _ => {}
        });
    }
    let unread: HashSet<u16> = copies
        .into_iter()
        .filter(|(local, count)| reads.get(local) == Some(count))
        .map(|(local, _)| local)
        .collect();
    if unread.is_empty() {
        return;
    }
    fn drop_in(stmts: &mut Vec<Stmt>, unread: &HashSet<u16>) {
        stmts.retain(|stmt| {
            !matches!(stmt, Stmt::Expr(Expr::Assign(target, value))
                if **value == Expr::This
                    && matches!(target.as_ref(), Expr::Local(local) if unread.contains(local)))
        });
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                drop_in(block, unread);
            }
            stmt.map_exprs(&mut |e| {
                if let Expr::Lambda { body, .. } = e
                    && let crate::ir::Body::Block(inner) = body.as_mut()
                {
                    drop_in(inner, unread);
                }
            });
        }
    }
    drop_in(stmts, &unread);
}

/// `state = -N; ...; <>m__FinallyN();` is `try { ... } finally { ... }`.
fn fold_iterator_tries(stmts: &mut Vec<Stmt>, finally_bodies: &HashMap<String, Vec<Stmt>>) {
    fold_branching_tries(stmts, finally_bodies);
    for stmt in stmts.iter_mut() {
        for block in stmt.blocks_mut() {
            fold_iterator_tries(block, finally_bodies);
        }
    }
    while let Some(start) = stmts
        .iter()
        .position(|stmt| matches!(stmt, Stmt::EnterTry(_)))
    {
        let Stmt::EnterTry(state) = stmts[start] else {
            unreachable!()
        };
        let number = (-state - 2).to_string();
        let finally_name = format!("<>m__Finally{number}");
        let is_finally_call = |stmt: &Stmt| matches!(stmt, Stmt::Expr(Expr::Call { method, .. }) if method.name == finally_name);
        let end = stmts.iter().rposition(is_finally_call);
        match end {
            Some(end) if end > start => {
                let mut body: Vec<Stmt> = stmts.drain(start + 1..=end).collect();
                body.pop();
                remove_calls(&mut body, &finally_name);
                let finally = finally_bodies
                    .get(&finally_name)
                    .cloned()
                    .unwrap_or_default();
                // A `try` nested in this one has its own markers.
                fold_iterator_tries(&mut body, finally_bodies);
                stmts[start] = Stmt::Try {
                    body,
                    catches: Vec::new(),
                    finally: Some(finally),
                };
            }
            _ => {
                stmts.remove(start);
            }
        }
    }
}

/// A hoisted local set to `null` right before a `yield break` or at the end
/// of a block is the compiler letting go of it, not the source.
fn drop_final_clears(stmts: &mut Vec<Stmt>, field_locals: &HashMap<String, u16>) {
    let hoisted: HashSet<u16> = field_locals.values().copied().collect();
    let mut index = 0;
    while index < stmts.len() {
        let clears = matches!(&stmts[index], Stmt::Expr(Expr::Assign(target, value))
            if matches!(value.as_ref(), Expr::Null | Expr::Default(_)) && matches!(target.as_ref(), Expr::Local(local) if hoisted.contains(local)));
        // Only clears, and then the end of the block or a way out of it.
        let is_clear = |stmt: &Stmt| {
            matches!(stmt, Stmt::Expr(Expr::Assign(target, value))
                if matches!(value.as_ref(), Expr::Null | Expr::Default(_))
                    && matches!(target.as_ref(), Expr::Local(local) if hoisted.contains(local)))
        };
        let rest = &stmts[index + 1..];
        let after_clears = rest.iter().position(|stmt| !is_clear(stmt));
        let at_end = match after_clears {
            None => true,
            Some(at) => matches!(
                rest[at],
                Stmt::YieldBreak | Stmt::Return(_) | Stmt::Break | Stmt::Continue
            ),
        };
        if clears && at_end {
            stmts.remove(index);
            continue;
        }
        for block in stmts[index].blocks_mut() {
            drop_final_clears(block, field_locals);
        }
        index += 1;
    }
}

/// A hoisted local set to `null` that nothing mentions afterwards is the
/// compiler letting go of it at the end of its scope: a `using` block's,
/// a loop body's.
fn drop_dead_clears(stmts: &mut Vec<Stmt>, field_locals: &HashMap<String, u16>) {
    fn has_labels(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|stmt| {
            matches!(stmt, Stmt::Label(_) | Stmt::Goto(_))
                || stmt.blocks().into_iter().any(|block| has_labels(block))
        })
    }
    fn mentions(stmt: &Stmt, into: &mut HashSet<u16>) {
        stmt.walk_exprs(&mut |e| {
            if let Expr::Local(local) = e {
                into.insert(*local);
            }
        });
    }
    fn drop(stmts: &mut Vec<Stmt>, hoisted: &HashSet<u16>, after: &HashSet<u16>) {
        let mut later = after.clone();
        let mut index = stmts.len();
        while index > 0 {
            index -= 1;
            if let Stmt::Expr(Expr::Assign(target, value)) = &stmts[index]
                && let Expr::Local(local) = target.as_ref()
                && hoisted.contains(local)
                && matches!(value.as_ref(), Expr::Null)
                && !later.contains(local)
            {
                stmts.remove(index);
                continue;
            }
            // A branch runs once, and the other not at all; anything else
            // (a loop, a `try`) may run its start after its end.
            let inner = if matches!(stmts[index], Stmt::If { .. }) {
                later.clone()
            } else {
                let mut inner = later.clone();
                mentions(&stmts[index], &mut inner);
                inner
            };
            for block in stmts[index].blocks_mut() {
                drop(block, hoisted, &inner);
            }
            mentions(&stmts[index], &mut later);
        }
    }
    if has_labels(stmts) {
        return;
    }
    let hoisted: HashSet<u16> = field_locals.values().copied().collect();
    drop(stmts, &hoisted, &HashSet::new());
}

/// `state = -N; if (c) { ...; <>m__FinallyN(); } else { <>m__FinallyN(); continue; }`:
/// a `try` left on every path at once, by the finally call closing each
/// branch rather than one after them.
fn fold_branching_tries(stmts: &mut Vec<Stmt>, finally_bodies: &HashMap<String, Vec<Stmt>>) {
    fn is_call(stmt: &Stmt, name: &str) -> bool {
        matches!(stmt, Stmt::Expr(Expr::Call { method, .. }) if method.name == name)
    }
    // Every way through ends with the call, or with it and then a jump.
    fn ends_with_call(stmts: &[Stmt], name: &str) -> bool {
        match stmts {
            [.., last] if is_call(last, name) => true,
            [.., call, Stmt::Continue | Stmt::Break | Stmt::Goto(_)] => is_call(call, name),
            [
                ..,
                Stmt::If {
                    then, otherwise, ..
                },
            ] => ends_with_call(then, name) && ends_with_call(otherwise, name),
            _ => false,
        }
    }
    fn drop_markers(stmts: &mut Vec<Stmt>, state: i64) {
        stmts.retain(|stmt| !matches!(stmt, Stmt::EnterTry(found) if *found == state));
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                drop_markers(block, state);
            }
        }
    }
    let mut index = 0;
    while index < stmts.len() {
        let Stmt::EnterTry(state) = stmts[index] else {
            index += 1;
            continue;
        };
        let name = format!("<>m__Finally{}", -state - 2);
        let rest = &stmts[index + 1..];
        let top_call = rest.iter().position(|stmt| is_call(stmt, &name));
        let end = (0..top_call.unwrap_or(rest.len()))
            .find(|&at| matches!(rest[at], Stmt::If { .. }) && ends_with_call(&rest[..=at], &name));
        let Some(end) = end else {
            index += 1;
            continue;
        };
        let mut body: Vec<Stmt> = stmts.drain(index + 1..=index + 1 + end).collect();
        remove_calls(&mut body, &name);
        drop_markers(&mut body, state);
        stmts[index] = Stmt::Try {
            body,
            catches: Vec::new(),
            finally: Some(finally_bodies.get(&name).cloned().unwrap_or_default()),
        };
        index += 1;
    }
}

/// Removes the calls of a finally method inside a `try` that now has it.
fn remove_calls(stmts: &mut Vec<Stmt>, name: &str) {
    stmts.retain(
        |stmt| !matches!(stmt, Stmt::Expr(Expr::Call { method, .. }) if method.name == name),
    );
    for stmt in stmts.iter_mut() {
        for block in stmt.blocks_mut() {
            remove_calls(block, name);
        }
    }
}

/// Markers left without a matching finally call are dropped.
fn strip_try_markers(stmts: &mut Vec<Stmt>) {
    stmts.retain(|stmt| !matches!(stmt, Stmt::EnterTry(_)));
    for stmt in stmts.iter_mut() {
        for block in stmt.blocks_mut() {
            strip_try_markers(block);
        }
    }
}

/// Whether a machine type is one that was folded into its method.
#[must_use]
pub fn is_folded_machine(options: &Options, type_row: u32) -> bool {
    options.consumed.borrow().machines.contains(&type_row)
}
