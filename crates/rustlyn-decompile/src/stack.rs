//! From IL to expressions: the evaluation stack replayed symbolically.
//!
//! Every instruction that pushes leaves an expression on a stack of
//! expressions rather than a value, and every instruction that pops takes
//! expressions off it; what comes off at a `stloc`, a `call` or a `ret` is the
//! tree C# wrote. Control flow is not followed here — the body is cut into
//! basic blocks first, and a value still on the stack when a block ends is
//! parked in a [`Expr::Slot`] for the block it flows into.

use std::collections::{BTreeSet, HashMap, HashSet};

use rustlyn_metadata::body::{Body, Handler, Instruction, Value};
use rustlyn_metadata::signature::TypeSig;
use rustlyn_metadata::{Token, table};

use crate::ir::{BinOp, Cmp, Expr, Stmt, UnOp};
use crate::names::{Generics, MethodRef, Resolver};

/// Everything about the method a body belongs to that reading it needs.
#[derive(Clone, Debug)]
pub struct MethodContext<'a> {
    pub resolver: Resolver<'a>,
    pub generics: Generics,
    pub is_static: bool,
    pub this_type: TypeSig,
    /// Parameter types, `this` not counted.
    pub params: Vec<TypeSig>,
    pub locals: Vec<TypeSig>,
    pub returns: TypeSig,
}

/// How a block ends.
#[derive(Clone, PartialEq, Debug)]
pub enum Terminator {
    /// Falls into the next block.
    Fall,
    Jump(u32),
    /// Jumps when the condition holds, falls through otherwise.
    Cond {
        condition: Expr,
        target: u32,
    },
    /// `switch`: one target per value, falling through for any other.
    Switch {
        value: Expr,
        targets: Vec<u32>,
    },
    Return(Option<Expr>),
    Throw(Expr),
    Rethrow,
    Leave(u32),
    EndFinally,
    EndFilter(Expr),
}

/// A basic block with its statements built.
#[derive(Clone, Debug)]
pub struct Block {
    pub start: u32,
    /// The offset just past the last instruction.
    pub end: u32,
    pub stmts: Vec<Stmt>,
    pub terminator: Terminator,
}

/// A value on the symbolic stack.
#[derive(Clone, Debug)]
struct Entry {
    expr: Expr,
    ty: TypeSig,
}

/// The result of reading a body: its blocks in offset order, and the types
/// of the slots they hand each other.
#[derive(Clone, Debug)]
pub struct Blocks {
    pub blocks: Vec<Block>,
    pub slot_types: HashMap<u32, TypeSig>,
}

impl Blocks {
    /// The index of the block starting at an offset.
    #[must_use]
    pub fn index_of(&self, offset: u32) -> Option<usize> {
        self.blocks
            .binary_search_by_key(&offset, |block| block.start)
            .ok()
    }
}

/// Where the blocks begin: branch targets, what follows a branch, and the
/// edges of every protected region.
fn leaders(body: &Body) -> BTreeSet<u32> {
    let mut leaders = BTreeSet::new();
    leaders.insert(0);
    for (index, instruction) in body.instructions.iter().enumerate() {
        let next = body
            .instructions
            .get(index + 1)
            .map_or(body.code_size, |next| next.offset);
        match &instruction.value {
            Value::Target(target) => {
                leaders.insert(*target);
                leaders.insert(next);
            }
            Value::Targets(targets) => {
                leaders.extend(targets.iter().copied());
                leaders.insert(next);
            }
            _ => {}
        }
        if matches!(
            instruction.name,
            "ret" | "throw" | "rethrow" | "endfinally" | "endfilter" | "jmp"
        ) {
            leaders.insert(next);
        }
    }
    for region in &body.regions {
        leaders.insert(region.try_offset);
        leaders.insert(region.try_offset + region.try_length);
        leaders.insert(region.handler_offset);
        leaders.insert(region.handler_offset + region.handler_length);
        if let Handler::Filter(at) = region.kind {
            leaders.insert(at);
        }
    }
    leaders.retain(|offset| *offset < body.code_size);
    leaders
}

/// The compiler's cache of a lambda that captures nothing:
///
/// ```text
/// ldsfld <>9__N; dup; brtrue L; pop; ldsfld <>9; ldftn M; newobj D; dup; stsfld <>9__N; L:
/// ```
///
/// The whole sequence is the delegate. Its instructions are skipped, and the
/// delegate is pushed where the first load was.
fn cached_lambdas(ctx: &MethodContext<'_>, body: &Body) -> (HashMap<u32, Expr>, HashSet<u32>) {
    let mut synthesized = HashMap::new();
    let mut skipped = HashSet::new();
    let instructions = &body.instructions;
    for (index, first) in instructions.iter().enumerate() {
        if first.name != "ldsfld" {
            continue;
        }
        let Value::Token(cache_token) = first.value else {
            continue;
        };
        let Some(cache) = ctx.resolver.field_ref(cache_token) else {
            continue;
        };
        if !cache.name.starts_with("<>9__") {
            continue;
        }
        let names: Vec<&str> = instructions[index..]
            .iter()
            .take(9)
            .map(|instruction| instruction.name)
            .collect();
        let shape = [
            "ldsfld", "dup", "brtrue", "pop", "ldsfld", "ldftn", "newobj", "dup", "stsfld",
        ];
        if names.len() != 9
            || !names
                .iter()
                .zip(shape)
                .all(|(found, wanted)| found.trim_end_matches(".s") == wanted)
        {
            continue;
        }
        let Value::Target(target) = instructions[index + 2].value else {
            continue;
        };
        let after = instructions
            .get(index + 9)
            .map_or(body.code_size, |next| next.offset);
        if target != after {
            continue;
        }
        let (Value::Token(singleton), Value::Token(method), Value::Token(ctor)) = (
            instructions[index + 4].value.clone(),
            instructions[index + 5].value.clone(),
            instructions[index + 6].value.clone(),
        ) else {
            continue;
        };
        let (Some(singleton), Some(method), Some(ctor)) = (
            ctx.resolver.field_ref(singleton),
            ctx.resolver.method_ref(method),
            ctx.resolver.method_ref(ctor),
        ) else {
            continue;
        };
        synthesized.insert(
            first.offset,
            Expr::Delegate {
                ty: ctor.declaring.clone(),
                target: Some(Box::new(Expr::Field {
                    receiver: None,
                    field: singleton,
                })),
                method,
            },
        );
        for instruction in &instructions[index + 1..index + 9] {
            skipped.insert(instruction.offset);
        }
    }
    (synthesized, skipped)
}

/// Reads a body into blocks of statements.
#[must_use]
pub fn read(ctx: &MethodContext<'_>, body: &Body) -> Blocks {
    // A value handed on as itself where branches meet has to be the same
    // on every way in; where it is not, the method is read again with a
    // slot there.
    let mut shared_only: HashSet<u32> = HashSet::new();
    for _ in 0..4 {
        let (blocks, conflicts) = read_with(ctx, body, &shared_only);
        if conflicts.is_empty() || conflicts.is_subset(&shared_only) {
            return blocks;
        }
        shared_only.extend(conflicts);
    }
    read_with(ctx, body, &shared_only).0
}

fn read_with(
    ctx: &MethodContext<'_>,
    body: &Body,
    shared_only: &HashSet<u32>,
) -> (Blocks, HashSet<u32>) {
    let mut conflicts: HashSet<u32> = HashSet::new();
    let (synthesized, skipped) = cached_lambdas(ctx, body);
    let leaders = leaders(body);
    let starts: Vec<u32> = leaders.iter().copied().collect();
    let mut blocks: Vec<Block> = Vec::with_capacity(starts.len());
    let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(starts.len());
    let mut at = 0usize;
    for (index, start) in starts.iter().enumerate() {
        let end = starts.get(index + 1).copied().unwrap_or(body.code_size);
        let first = at;
        while at < body.instructions.len() && body.instructions[at].offset < end {
            at += 1;
        }
        ranges.push((first, at));
        blocks.push(Block {
            start: *start,
            end,
            stmts: Vec::new(),
            terminator: Terminator::Fall,
        });
    }

    let mut reader = Reader {
        ctx,
        stack: Vec::new(),
        stmts: Vec::new(),
        next_slot: 0,
        slot_types: HashMap::new(),
        null_slots: HashSet::new(),
        entry_slots: HashMap::new(),
        constrained: None,
    };

    // Handlers start with the exception on the stack; a filter's code does
    // too. Everything else starts empty unless a predecessor says otherwise.
    for region in &body.regions {
        match region.kind {
            Handler::Catch(_) | Handler::Filter(_) => {
                reader.entry_slots.insert(
                    region.handler_offset,
                    vec![Entry {
                        expr: Expr::CaughtException,
                        ty: TypeSig::Object,
                    }],
                );
                if let Handler::Filter(at) = region.kind {
                    reader.entry_slots.insert(
                        at,
                        vec![Entry {
                            expr: Expr::CaughtException,
                            ty: TypeSig::Object,
                        }],
                    );
                }
            }
            Handler::Finally | Handler::Fault => {}
        }
    }

    for (index, (first, last)) in ranges.iter().enumerate() {
        let start = blocks[index].start;
        reader.stack = reader.entry_slots.get(&start).cloned().unwrap_or_default();
        reader.stmts.clear();
        let mut terminator = Terminator::Fall;
        for instruction in &body.instructions[*first..*last] {
            if skipped.contains(&instruction.offset) {
                continue;
            }
            if let Some(delegate) = synthesized.get(&instruction.offset) {
                let ty = match delegate {
                    Expr::Delegate { ty, .. } => ty.clone(),
                    _ => TypeSig::Object,
                };
                reader.push(delegate.clone(), ty);
                continue;
            }
            if let Some(found) = reader.step(instruction) {
                terminator = found;
            }
        }
        let leftover = std::mem::take(&mut reader.stack);
        let mut stmts = std::mem::take(&mut reader.stmts);
        // Whatever is still on the stack goes to every successor through the
        // slots that successor reads.
        if !leftover.is_empty() {
            let successors = successors(&terminator, blocks.get(index + 1).map(|next| next.start));
            let mut spilled: Vec<Entry> = Vec::with_capacity(leftover.len());
            for entry in leftover {
                if entry.expr.is_pure() || successors.len() <= 1 {
                    spilled.push(entry);
                } else {
                    let slot = reader.fresh_slot(entry.ty.clone());
                    stmts.push(Stmt::Expr(Expr::assign(slot.clone(), entry.expr)));
                    spilled.push(Entry {
                        expr: slot,
                        ty: entry.ty,
                    });
                }
            }
            for successor in successors {
                let slots = reader.slots_for(successor, &spilled, shared_only.contains(&successor));
                for (slot, entry) in slots.iter().zip(&spilled) {
                    if slot.expr != entry.expr {
                        if !matches!(slot.expr, Expr::Slot(_)) {
                            conflicts.insert(successor);
                        }
                        stmts.push(Stmt::Expr(Expr::assign(
                            slot.expr.clone(),
                            entry.expr.clone(),
                        )));
                    }
                }
            }
        }
        blocks[index].stmts = stmts;
        blocks[index].terminator = terminator;
    }

    (
        Blocks {
            blocks,
            slot_types: reader.slot_types,
        },
        conflicts,
    )
}

/// Where control can go from a terminator, the fall-through included.
fn successors(terminator: &Terminator, next: Option<u32>) -> Vec<u32> {
    match terminator {
        Terminator::Fall => next.into_iter().collect(),
        Terminator::Jump(target) | Terminator::Leave(target) => vec![*target],
        Terminator::Cond { target, .. } => {
            let mut out = vec![*target];
            if let Some(next) = next
                && next != *target
            {
                out.push(next);
            }
            out
        }
        Terminator::Switch { targets, .. } => {
            let mut out: Vec<u32> = targets.clone();
            out.extend(next);
            out.sort_unstable();
            out.dedup();
            out
        }
        _ => Vec::new(),
    }
}

struct Reader<'c, 'a> {
    ctx: &'c MethodContext<'a>,
    stack: Vec<Entry>,
    stmts: Vec<Stmt>,
    next_slot: u32,
    slot_types: HashMap<u32, TypeSig>,
    /// The slots made for a `null`, whose type is the next value's.
    null_slots: HashSet<u32>,
    /// The slots each block expects on entry, made when a predecessor first
    /// hands it values.
    entry_slots: HashMap<u32, Vec<Entry>>,
    constrained: Option<Token>,
}

impl Reader<'_, '_> {
    fn fresh_slot(&mut self, ty: TypeSig) -> Expr {
        let id = self.next_slot;
        self.next_slot += 1;
        self.slot_types.insert(id, ty);
        Expr::Slot(id)
    }

    fn slots_for(&mut self, block: u32, values: &[Entry], slots_only: bool) -> Vec<Entry> {
        if let Some(existing) = self.entry_slots.get(&block)
            && existing.len() == values.len()
        {
            let existing = existing.clone();
            // A slot given classes of two kinds holds their common base.
            for (slot, value) in existing.iter().zip(values) {
                let Expr::Slot(id) = slot.expr else {
                    continue;
                };
                // A slot first given `null` holds what it is given next.
                if self.null_slots.contains(&id)
                    && value.expr != Expr::Null
                    && value.ty != TypeSig::Object
                    && !self.resolver().is_value_type(&value.ty)
                {
                    self.null_slots.remove(&id);
                    self.slot_types.insert(id, value.ty.clone());
                    continue;
                }
                if let Some(have) = self.slot_types.get(&id)
                    && *have != value.ty
                    && value.expr != Expr::Null
                    && let Some(common) = self.resolver().common_base(have, &value.ty)
                {
                    self.slot_types.insert(id, common);
                }
            }
            return existing;
        }
        // `this` is the same on every way in: it needs no slot, and a
        // call on it stays a call on it (`: base(x?.Y)`). A `ref` parameter
        // or variable is its address: a copy of it would be written as a
        // variable of its own, and a store through it lost.
        let slots: Vec<Entry> = values
            .iter()
            .map(|entry| Entry {
                expr: if !slots_only
                    && (entry.expr == Expr::This
                        || (matches!(entry.ty, TypeSig::ByRef(_))
                            && matches!(entry.expr, Expr::Arg(_) | Expr::Local(_)))
                        || matches!(&entry.expr, Expr::Unary(UnOp::AddressOf, place)
                        if matches!(place.as_ref(),
                            Expr::Local(_) | Expr::Arg(_) | Expr::Field { receiver: None, .. })))
                {
                    entry.expr.clone()
                } else {
                    let slot = self.fresh_slot(entry.ty.clone());
                    if entry.expr == Expr::Null
                        && let Expr::Slot(id) = slot
                    {
                        self.null_slots.insert(id);
                    }
                    slot
                },
                ty: entry.ty.clone(),
            })
            .collect();
        self.entry_slots.insert(block, slots.clone());
        slots
    }

    fn push(&mut self, expr: Expr, ty: TypeSig) {
        self.stack.push(Entry { expr, ty });
    }

    fn pop(&mut self) -> Entry {
        self.stack.pop().unwrap_or(Entry {
            expr: Expr::Raw("<empty stack>".into()),
            ty: TypeSig::Object,
        })
    }

    fn pop_n(&mut self, count: usize) -> Vec<Entry> {
        let at = self.stack.len().saturating_sub(count);
        let mut taken: Vec<Entry> = self.stack.drain(at..).collect();
        while taken.len() < count {
            taken.insert(
                0,
                Entry {
                    expr: Expr::Raw("<empty stack>".into()),
                    ty: TypeSig::Object,
                },
            );
        }
        taken
    }

    /// Emits a statement, first parking in slots whatever is on the stack
    /// that the statement could change or has to come after: a value read
    /// off a variable the statement writes, or a call that has to run first.
    fn emit(&mut self, stmt: Stmt) {
        if !self.stack.is_empty() {
            let writes = writes_of(&stmt);
            let mut spills: Vec<(usize, Expr, TypeSig)> = Vec::new();
            for (at, entry) in self.stack.iter().enumerate() {
                // A `ref` variable on the stack is its address: writing
                // through it leaves the address as it was, and a copy of
                // it would read as a copy of the value.
                if matches!(entry.ty, TypeSig::ByRef(_))
                    && matches!(entry.expr, Expr::Arg(_) | Expr::Local(_))
                {
                    continue;
                }
                if must_spill(&entry.expr, &writes) {
                    spills.push((at, entry.expr.clone(), entry.ty.clone()));
                }
            }
            for (at, expr, ty) in spills {
                let slot = self.fresh_slot(ty);
                self.stmts
                    .push(Stmt::Expr(Expr::assign(slot.clone(), expr)));
                self.stack[at].expr = slot;
            }
        }
        self.stmts.push(stmt);
    }

    /// Whether a type is the one the method belongs to.
    fn is_own_type(&self, ty: &TypeSig) -> bool {
        let own = match &self.ctx.this_type {
            TypeSig::ByRef(inner) => inner.as_ref(),
            other => other,
        };
        let strip = |ty: &TypeSig| match ty {
            TypeSig::Generic { definition, .. } => (**definition).clone(),
            other => other.clone(),
        };
        strip(ty) == strip(own)
    }

    fn resolver(&self) -> Resolver<'_> {
        self.ctx.resolver
    }

    /// An expression as text, for the remarks about what is not modelled.
    fn text(&self, expr: &Expr) -> String {
        crate::print::expr_text(self.ctx, expr)
    }

    fn local_type(&self, index: u16) -> TypeSig {
        self.ctx
            .locals
            .get(index as usize)
            .cloned()
            .unwrap_or(TypeSig::Object)
    }

    /// The expression and type of `ldarg n`.
    fn argument(&self, index: u16) -> (Expr, TypeSig) {
        if !self.ctx.is_static {
            if index == 0 {
                return (Expr::This, self.ctx.this_type.clone());
            }
            let at = index - 1;
            return (
                Expr::Arg(at),
                self.ctx
                    .params
                    .get(at as usize)
                    .cloned()
                    .unwrap_or(TypeSig::Object),
            );
        }
        (
            Expr::Arg(index),
            self.ctx
                .params
                .get(index as usize)
                .cloned()
                .unwrap_or(TypeSig::Object),
        )
    }

    /// One instruction, with the terminator it makes of the block when it is
    /// the kind that ends one.
    #[allow(clippy::too_many_lines)]
    fn step(&mut self, instruction: &Instruction) -> Option<Terminator> {
        let name = instruction.name;
        let variable = match instruction.value {
            Value::Variable(index) => index,
            _ => 0,
        };
        let token = match instruction.value {
            Value::Token(token) => token,
            _ => Token(0),
        };
        match name {
            "nop" | "break" | "tail." | "volatile." | "unaligned." | "readonly." | "no." => {}
            "constrained." => self.constrained = Some(token),

            "ldarg.0" | "ldarg.1" | "ldarg.2" | "ldarg.3" => {
                let index = u16::from(name.as_bytes()[6] - b'0');
                let (expr, ty) = self.argument(index);
                self.push(expr, ty);
            }
            "ldarg.s" | "ldarg" => {
                let (expr, ty) = self.argument(variable);
                self.push(expr, ty);
            }
            "ldarga.s" | "ldarga" => {
                let (expr, ty) = self.argument(variable);
                self.push(
                    Expr::unary(UnOp::AddressOf, expr),
                    TypeSig::ByRef(Box::new(ty)),
                );
            }
            "starg.s" | "starg" => {
                let (target, ty) = self.argument(variable);
                let value = self.pop();
                let value = self.coerce(value, &ty);
                self.emit(Stmt::Expr(Expr::assign(target, value)));
            }
            "ldloc.0" | "ldloc.1" | "ldloc.2" | "ldloc.3" => {
                let index = u16::from(name.as_bytes()[6] - b'0');
                self.push(Expr::Local(index), self.local_type(index));
            }
            "ldloc.s" | "ldloc" => self.push(Expr::Local(variable), self.local_type(variable)),
            "ldloca.s" | "ldloca" => self.push(
                Expr::unary(UnOp::AddressOf, Expr::Local(variable)),
                TypeSig::ByRef(Box::new(self.local_type(variable))),
            ),
            "stloc.0" | "stloc.1" | "stloc.2" | "stloc.3" => {
                let index = u16::from(name.as_bytes()[6] - b'0');
                self.store_local(index);
            }
            "stloc.s" | "stloc" => self.store_local(variable),

            "ldnull" => self.push(Expr::Null, TypeSig::Object),
            "ldc.i4.m1" => self.push(Expr::Int(-1), TypeSig::Int32),
            "ldc.i4.0" | "ldc.i4.1" | "ldc.i4.2" | "ldc.i4.3" | "ldc.i4.4" | "ldc.i4.5"
            | "ldc.i4.6" | "ldc.i4.7" | "ldc.i4.8" => {
                let value = i64::from(name.as_bytes()[7] - b'0');
                self.push(Expr::Int(value), TypeSig::Int32);
            }
            "ldc.i4.s" | "ldc.i4" => {
                let Value::Int(value) = instruction.value else {
                    return None;
                };
                self.push(Expr::Int(value), TypeSig::Int32);
            }
            "ldc.i8" => {
                let Value::Int(value) = instruction.value else {
                    return None;
                };
                self.push(Expr::Long(value), TypeSig::Int64);
            }
            "ldc.r4" => {
                let Value::Float(value) = instruction.value else {
                    return None;
                };
                self.push(Expr::Float(value, true), TypeSig::Single);
            }
            "ldc.r8" => {
                let Value::Float(value) = instruction.value else {
                    return None;
                };
                self.push(Expr::Float(value, false), TypeSig::Double);
            }
            "ldstr" => {
                let text = self.resolver().user_string(token).unwrap_or_default();
                self.push(Expr::Str(text), TypeSig::String);
            }

            "dup" => {
                let top = self.pop();
                // Only a variable or a constant is copied outright; anything
                // else, a field read included, is evaluated once into a slot,
                // the way the IL evaluated it once.
                let trivial = matches!(
                    top.expr,
                    Expr::This | Expr::Arg(_) | Expr::Local(_) | Expr::Slot(_)
                ) || top.expr.is_constant();
                if trivial {
                    self.stack.push(top.clone());
                    self.stack.push(top);
                } else {
                    let slot = self.fresh_slot(top.ty.clone());
                    self.emit(Stmt::Expr(Expr::assign(slot.clone(), top.expr)));
                    self.push(slot.clone(), top.ty.clone());
                    self.push(slot, top.ty);
                }
            }
            "pop" => {
                let top = self.pop();
                if !top.expr.is_pure() {
                    self.emit(Stmt::Expr(top.expr));
                }
            }

            "call" | "callvirt" | "newobj" => {
                let constrained = self.constrained.take();
                self.call(token, name == "newobj", name == "callvirt", constrained);
            }
            "calli" => {
                let target = self.pop();
                self.emit(Stmt::Comment(format!(
                    "calli through {}",
                    self.text(&target.expr)
                )));
            }
            "jmp" => {
                self.emit(Stmt::Comment("jmp".into()));
                return Some(Terminator::Return(None));
            }
            "ret" => {
                if matches!(self.ctx.returns, TypeSig::Void) {
                    return Some(Terminator::Return(None));
                }
                let value = self.pop();
                let returns = self.ctx.returns.clone();
                let value = self.coerce(value, &returns);
                return Some(Terminator::Return(Some(value)));
            }

            "br" | "br.s" => {
                let Value::Target(target) = instruction.value else {
                    return None;
                };
                return Some(Terminator::Jump(target));
            }
            "leave" | "leave.s" => {
                let Value::Target(target) = instruction.value else {
                    return None;
                };
                self.stack.clear();
                return Some(Terminator::Leave(target));
            }
            "brfalse" | "brfalse.s" | "brtrue" | "brtrue.s" => {
                let Value::Target(target) = instruction.value else {
                    return None;
                };
                let value = self.pop();
                let condition = self.truthy(value);
                let condition = if name.starts_with("brfalse") {
                    negate(condition)
                } else {
                    condition
                };
                return Some(Terminator::Cond { condition, target });
            }
            "beq" | "beq.s" | "bge" | "bge.s" | "bgt" | "bgt.s" | "ble" | "ble.s" | "blt"
            | "blt.s" | "bne.un" | "bne.un.s" | "bge.un" | "bge.un.s" | "bgt.un" | "bgt.un.s"
            | "ble.un" | "ble.un.s" | "blt.un" | "blt.un.s" => {
                let Value::Target(target) = instruction.value else {
                    return None;
                };
                let base = name.trim_end_matches(".s");
                let (op, unordered) = match base {
                    "beq" => (Cmp::Eq, false),
                    "bge" => (Cmp::Ge, false),
                    "bgt" => (Cmp::Gt, false),
                    "ble" => (Cmp::Le, false),
                    "blt" => (Cmp::Lt, false),
                    "bne.un" => (Cmp::Ne, true),
                    "bge.un" => (Cmp::Ge, true),
                    "bgt.un" => (Cmp::Gt, true),
                    "ble.un" => (Cmp::Le, true),
                    _ => (Cmp::Lt, true),
                };
                let condition = self.comparison(op, unordered);
                return Some(Terminator::Cond { condition, target });
            }
            "switch" => {
                let Value::Targets(targets) = &instruction.value else {
                    return None;
                };
                let value = self.pop();
                return Some(Terminator::Switch {
                    value: value.expr,
                    targets: targets.clone(),
                });
            }
            "throw" => {
                let value = self.pop();
                self.stack.clear();
                return Some(Terminator::Throw(value.expr));
            }
            "rethrow" => {
                self.stack.clear();
                return Some(Terminator::Rethrow);
            }
            "endfinally" => {
                self.stack.clear();
                return Some(Terminator::EndFinally);
            }
            "endfilter" => {
                let value = self.pop();
                let condition = self.truthy(value);
                self.stack.clear();
                return Some(Terminator::EndFilter(condition));
            }

            "ceq" => {
                let condition = self.comparison(Cmp::Eq, false);
                self.push(condition, TypeSig::Boolean);
            }
            "cgt" => {
                let condition = self.comparison(Cmp::Gt, false);
                self.push(condition, TypeSig::Boolean);
            }
            "cgt.un" => {
                let condition = self.comparison(Cmp::Gt, true);
                self.push(condition, TypeSig::Boolean);
            }
            "clt" => {
                let condition = self.comparison(Cmp::Lt, false);
                self.push(condition, TypeSig::Boolean);
            }
            "clt.un" => {
                let condition = self.comparison(Cmp::Lt, true);
                self.push(condition, TypeSig::Boolean);
            }

            "add" | "sub" | "mul" | "div" | "div.un" | "rem" | "rem.un" | "and" | "or" | "xor"
            | "shl" | "shr" | "shr.un" | "add.ovf" | "add.ovf.un" | "sub.ovf" | "sub.ovf.un"
            | "mul.ovf" | "mul.ovf.un" => {
                let op = match name.split('.').next().unwrap_or(name) {
                    "add" => BinOp::Add,
                    "sub" => BinOp::Sub,
                    "mul" => BinOp::Mul,
                    "div" => BinOp::Div,
                    "rem" => BinOp::Rem,
                    "and" => BinOp::And,
                    "or" => BinOp::Or,
                    "xor" => BinOp::Xor,
                    "shl" => BinOp::Shl,
                    _ => BinOp::Shr,
                };
                let mut right = self.pop();
                let mut left = self.pop();
                // A comparison's result in arithmetic is a number: C# says
                // so with `c ? 1 : 0`. `&`, `|` and `^` take two as they are.
                let bools = left.ty == TypeSig::Boolean && right.ty == TypeSig::Boolean;
                if !(bools && matches!(op, BinOp::And | BinOp::Or | BinOp::Xor)) {
                    for side in [&mut left, &mut right] {
                        if side.ty == TypeSig::Boolean && !side.expr.is_constant() {
                            let expr = std::mem::replace(&mut side.expr, Expr::Int(0));
                            side.expr = Expr::Conditional(
                                Box::new(expr),
                                Box::new(Expr::Int(1)),
                                Box::new(Expr::Int(0)),
                            );
                            side.ty = TypeSig::Int32;
                        }
                    }
                }
                // `div.un` and `rem.un` divide as unsigned, `div` and `rem`
                // as signed, whatever C# would take the operands' types to
                // say: the operands are cast to the kind the instruction is.
                if matches!(op, BinOp::Div | BinOp::Rem) {
                    let unsigned = name.ends_with(".un");
                    for side in [&mut left, &mut right] {
                        let wanted = match (&side.ty, unsigned) {
                            (TypeSig::SByte | TypeSig::Int16 | TypeSig::Int32, true) => {
                                Some(TypeSig::UInt32)
                            }
                            (TypeSig::Int64, true) => Some(TypeSig::UInt64),
                            (TypeSig::IntPtr, true) => Some(TypeSig::UIntPtr),
                            (TypeSig::UInt32, false) => Some(TypeSig::Int32),
                            (TypeSig::UInt64, false) => Some(TypeSig::Int64),
                            (TypeSig::UIntPtr, false) => Some(TypeSig::IntPtr),
                            _ => None,
                        };
                        if let Some(wanted) = wanted {
                            let expr = std::mem::replace(&mut side.expr, Expr::Int(0));
                            side.expr = match expr {
                                Expr::Int(n) if n >= 0 => Expr::Int(n),
                                Expr::Long(n) if n >= 0 => Expr::Long(n),
                                other => Expr::Cast(wanted.clone(), Box::new(other)),
                            };
                            side.ty = wanted;
                        }
                    }
                }
                // `shr.un` on a signed value is C# 11's `>>>`.
                let op = if name == "shr.un"
                    && matches!(
                        left.ty,
                        TypeSig::Int32
                            | TypeSig::Int64
                            | TypeSig::IntPtr
                            | TypeSig::Int16
                            | TypeSig::SByte
                    ) {
                    BinOp::UShr
                } else {
                    op
                };
                let mut ty = if bools && matches!(op, BinOp::And | BinOp::Or | BinOp::Xor) {
                    TypeSig::Boolean
                } else {
                    arithmetic_type(&left.ty, &right.ty)
                };
                // One value of an enum less another is a number: the
                // constant is written as one of the members.
                if op == BinOp::Sub
                    && (right.ty == left.ty || right.expr.is_constant())
                    && let Some(underlying) = self.resolver().enum_underlying(&left.ty)
                {
                    ty = match underlying {
                        TypeSig::Int64 | TypeSig::UInt64 | TypeSig::UInt32 => underlying,
                        _ => TypeSig::Int32,
                    };
                }
                // Arithmetic on a `void*` is on bytes.
                let left = match &left.ty {
                    TypeSig::Pointer(element)
                        if **element == TypeSig::Void && matches!(op, BinOp::Add | BinOp::Sub) =>
                    {
                        let ty = TypeSig::Pointer(Box::new(TypeSig::Byte));
                        Entry {
                            expr: Expr::Cast(ty.clone(), Box::new(left.expr)),
                            ty,
                        }
                    }
                    _ => left,
                };
                // `p + i * sizeof(T)` is how C# `p + i` reaches IL.
                if matches!(op, BinOp::Add | BinOp::Sub)
                    && !name.contains(".ovf")
                    && let TypeSig::Pointer(element) = &left.ty
                    && let Some(index) = unscale(&right.expr, element)
                {
                    self.push(Expr::binary(op, left.expr, index), left.ty.clone());
                    return None;
                }
                // C# shifts, multiplies and divides numbers, not enums: an
                // enum operand is its number, and a shift's count is an
                // `int` whatever it is shifted by.
                let (left, right) = if matches!(
                    op,
                    BinOp::Shl | BinOp::Shr | BinOp::UShr | BinOp::Mul | BinOp::Div | BinOp::Rem
                ) {
                    let as_number = |entry: Entry| match self.resolver().enum_underlying(&entry.ty)
                    {
                        Some(underlying) if !entry.expr.is_constant() => Entry {
                            expr: Expr::Cast(underlying.clone(), Box::new(entry.expr)),
                            ty: underlying,
                        },
                        _ => entry,
                    };
                    let (left, right) = (as_number(left), as_number(right));
                    if !matches!(left.ty, TypeSig::Pointer(_)) {
                        ty = arithmetic_type(&left.ty, &right.ty);
                    }
                    (left, right)
                } else {
                    (left, right)
                };
                let (left_expr, right_expr) = if matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr)
                {
                    (left.expr, right.expr)
                } else {
                    self.unify(left, right)
                };
                let mut expr = Expr::binary(op, left_expr, right_expr);
                if name.contains(".ovf") {
                    expr = Expr::Checked(Box::new(expr));
                }
                self.push(expr, ty);
            }
            "neg" => {
                let value = self.pop();
                self.push(Expr::unary(UnOp::Neg, value.expr), value.ty);
            }
            "not" => {
                let value = self.pop();
                self.push(Expr::unary(UnOp::BitNot, value.expr), value.ty);
            }

            _ if name.starts_with("conv.") => self.convert(name),

            "ldfld" | "ldflda" | "ldsfld" | "ldsflda" => {
                let Some(field) = self.resolver().field_ref(token) else {
                    self.push(Expr::Raw(format!("{token:?}")), TypeSig::Object);
                    return None;
                };
                let receiver = if name.starts_with("lds") {
                    None
                } else {
                    Some(Box::new(self.receiver_of_field()))
                };
                // `ValueTuple<A, B>.Item1` is an `A`, not a `T1`.
                let ty = substitute(&field.ty, &field.declaring, &[]);
                let expr = Expr::Field { receiver, field };
                if name.ends_with('a') {
                    self.push(
                        Expr::unary(UnOp::AddressOf, expr),
                        TypeSig::ByRef(Box::new(ty)),
                    );
                } else {
                    self.push(expr, ty);
                }
            }
            "stfld" | "stsfld" => {
                let field = self.resolver().field_ref(token)?;
                let value = self.pop();
                let value = self.coerce(value, &substitute(&field.ty, &field.declaring, &[]));
                let receiver = if name == "stsfld" {
                    None
                } else {
                    Some(Box::new(self.receiver_of_field()))
                };
                let target = Expr::Field { receiver, field };
                self.emit(Stmt::Expr(Expr::assign(target, value)));
            }

            "newarr" => {
                let size = self.pop();
                let element = self.resolver().token_sig(token);
                let expr = Expr::NewArray {
                    element: element.clone(),
                    size: Box::new(size.expr),
                    items: None,
                };
                self.push(expr, TypeSig::Vector(Box::new(element)));
            }
            "ldlen" => {
                let array = self.pop();
                self.push(Expr::Length(Box::new(array.expr)), TypeSig::Int32);
            }
            "ldelema" => {
                let index = self.pop();
                let array = self.pop();
                let element = self.resolver().token_sig(token);
                self.push(
                    Expr::unary(
                        UnOp::AddressOf,
                        Expr::Index {
                            array: Box::new(array.expr),
                            indices: vec![index.expr],
                        },
                    ),
                    TypeSig::ByRef(Box::new(element)),
                );
            }
            _ if name.starts_with("ldelem") => {
                let index = self.pop();
                let array = self.pop();
                let element = match (&array.ty, name) {
                    (_, "ldelem") => self.resolver().token_sig(token),
                    (TypeSig::Vector(element), _) => (**element).clone(),
                    (TypeSig::Array { element, .. }, _) => (**element).clone(),
                    _ => element_of_suffix(name),
                };
                self.push(
                    Expr::Index {
                        array: Box::new(array.expr),
                        indices: vec![index.expr],
                    },
                    element,
                );
            }
            _ if name.starts_with("stelem") => {
                let value = self.pop();
                let index = self.pop();
                let array = self.pop();
                let element = match (&array.ty, name) {
                    (_, "stelem") => self.resolver().token_sig(token),
                    (TypeSig::Vector(element), _) => (**element).clone(),
                    (TypeSig::Array { element, .. }, _) => (**element).clone(),
                    _ => element_of_suffix(name),
                };
                let value = self.coerce(value, &element);
                let target = Expr::Index {
                    array: Box::new(array.expr),
                    indices: vec![index.expr],
                };
                self.emit(Stmt::Expr(Expr::assign(target, value)));
            }

            _ if name.starts_with("ldind") || name == "ldobj" => {
                let address = self.pop();
                let address = retype_pointer(address, name);
                let (expr, ty) = self.dereference(address, name == "ldobj", token);
                self.push(expr, ty);
            }
            _ if name.starts_with("stind") || name == "stobj" => {
                let value = self.pop();
                let address = self.pop();
                let address = retype_pointer(address, name);
                let (target, ty) = self.dereference(address, name == "stobj", token);
                let value = self.coerce(value, &ty);
                self.emit(Stmt::Expr(Expr::assign(target, value)));
            }
            "cpobj" => {
                let source = self.pop();
                let target = self.pop();
                let (source, _) = self.dereference(source, true, token);
                let (target, _) = self.dereference(target, true, token);
                self.emit(Stmt::Expr(Expr::assign(target, source)));
            }
            "initobj" => {
                let address = self.pop();
                let ty = self.resolver().token_sig(token);
                let (target, _) = self.dereference(address, true, token);
                self.emit(Stmt::Expr(Expr::assign(target, Expr::Default(ty))));
            }
            "localloc" => {
                let size = match self.pop().expr {
                    Expr::Cast(TypeSig::UIntPtr, inner) if matches!(*inner, Expr::Int(_)) => *inner,
                    other => other,
                };
                self.push(
                    Expr::StackAlloc(TypeSig::Byte, Box::new(size)),
                    TypeSig::Pointer(Box::new(TypeSig::Byte)),
                );
            }
            "cpblk" | "initblk" => {
                let args = self.pop_n(3);
                let texts: Vec<String> = args.iter().map(|entry| self.text(&entry.expr)).collect();
                self.emit(Stmt::Comment(format!("{name}({})", texts.join(", "))));
            }

            "box" => {
                let value = self.pop();
                let ty = self.resolver().token_sig(token);
                // An enum boxed as its number, or a number as an enum, is
                // converted first: the box keeps the type it was given.
                let converted = value.ty != ty
                    && (self.resolver().enum_underlying(&value.ty).is_some()
                        || self.resolver().enum_underlying(&ty).is_some());
                let value = self.coerce(value, &ty);
                let value = if converted {
                    Expr::Cast(ty.clone(), Box::new(value))
                } else {
                    value
                };
                self.push(Expr::Box(ty, Box::new(value)), TypeSig::Object);
            }
            "unbox" => {
                let value = self.pop();
                let ty = self.resolver().token_sig(token);
                self.push(
                    Expr::unary(
                        UnOp::AddressOf,
                        Expr::Cast(ty.clone(), Box::new(value.expr)),
                    ),
                    TypeSig::ByRef(Box::new(ty)),
                );
            }
            "unbox.any" | "castclass" => {
                let value = self.pop();
                let ty = self.resolver().token_sig(token);
                let expr = match value.expr {
                    // Unboxing what was just boxed is a no-op.
                    Expr::Box(inner_ty, inner) if inner_ty == ty => *inner,
                    other => Expr::Cast(ty.clone(), Box::new(other)),
                };
                self.push(expr, ty);
            }
            "isinst" => {
                let value = self.pop();
                let ty = self.resolver().token_sig(token);
                // A value type tested for is still boxed: the result is an
                // object reference, compared with null, never the value.
                let pushed = if self.resolver().is_value_type(&ty) {
                    TypeSig::Object
                } else {
                    ty.clone()
                };
                self.push(Expr::As(ty, Box::new(value.expr)), pushed);
            }
            "ldtoken" => {
                let expr = match token.table() {
                    table::TYPE_DEF | table::TYPE_REF | table::TYPE_SPEC => {
                        Expr::TypeOf(self.resolver().token_sig(token))
                    }
                    table::FIELD | table::MEMBER_REF => {
                        self.resolver().field_ref(token).map_or_else(
                            || Expr::Raw(format!("{token:?}")),
                            |field| Expr::Field {
                                receiver: None,
                                field,
                            },
                        )
                    }
                    _ => self.resolver().method_ref(token).map_or_else(
                        || Expr::Raw(format!("{token:?}")),
                        |method| Expr::Raw(format!("methodof({})", method.name)),
                    ),
                };
                self.push(expr, TypeSig::Object);
            }
            "ldftn" | "ldvirtftn" => {
                if name == "ldvirtftn" {
                    // The receiver the virtual lookup used comes back as the
                    // delegate's target through the `dup` before it.
                    self.pop();
                }
                match self.resolver().method_ref(token) {
                    Some(method) => self.push(Expr::FunctionPointer(method), TypeSig::IntPtr),
                    None => self.push(Expr::Raw(format!("{token:?}")), TypeSig::IntPtr),
                }
            }
            "sizeof" => {
                let ty = self.resolver().token_sig(token);
                self.push(Expr::SizeOf(ty), TypeSig::Int32);
            }
            "ckfinite" => {}
            "arglist" => self.push(Expr::Raw("__arglist".into()), TypeSig::Object),
            "mkrefany" => {
                let value = self.pop();
                self.push(
                    Expr::Raw(format!("__makeref({})", self.text(&value.expr))),
                    TypeSig::TypedReference,
                );
            }
            "refanyval" => {
                let value = self.pop();
                let ty = self.resolver().token_sig(token);
                self.push(
                    Expr::Raw(format!(
                        "__refvalue({}, {})",
                        self.text(&value.expr),
                        self.resolver().type_name(&ty, &self.ctx.generics)
                    )),
                    ty,
                );
            }
            "refanytype" => {
                let value = self.pop();
                self.push(
                    Expr::Raw(format!("__reftype({})", self.text(&value.expr))),
                    TypeSig::Object,
                );
            }
            other => self.emit(Stmt::Comment(format!("unhandled `{other}`"))),
        }
        None
    }

    fn store_local(&mut self, index: u16) {
        let ty = self.local_type(index);
        let value = self.pop();
        let value = self.coerce(value, &ty);
        self.emit(Stmt::Expr(Expr::assign(Expr::Local(index), value)));
    }

    /// The receiver of a field access, with the address a value type's field
    /// is reached through stripped off.
    fn receiver_of_field(&mut self) -> Expr {
        let receiver = self.pop();
        strip_address(receiver.expr)
    }

    /// What loading through an address gives: the variable itself when the
    /// address was taken just for this, `*p` for a real pointer.
    fn dereference(&self, address: Entry, typed: bool, token: Token) -> (Expr, TypeSig) {
        let ty = if typed && !token.is_nil() {
            self.resolver().token_sig(token)
        } else {
            match &address.ty {
                TypeSig::ByRef(inner) | TypeSig::Pointer(inner) => (**inner).clone(),
                _ => TypeSig::Object,
            }
        };
        match address.expr {
            Expr::Unary(UnOp::AddressOf, inner) => (*inner, ty),
            other => match &address.ty {
                // A `ref` parameter or local is spelled as the variable.
                TypeSig::ByRef(_) => (other, ty),
                // A native integer read through by type is a pointer to it.
                TypeSig::IntPtr | TypeSig::UIntPtr if typed => (
                    Expr::unary(
                        UnOp::Deref,
                        Expr::Cast(TypeSig::Pointer(Box::new(ty.clone())), Box::new(other)),
                    ),
                    ty,
                ),
                _ => (Expr::unary(UnOp::Deref, other), ty),
            },
        }
    }

    fn convert(&mut self, name: &str) {
        let value = self.pop();
        let checked = name.contains(".ovf");
        let suffix = name
            .trim_start_matches("conv.")
            .trim_start_matches("ovf.")
            .trim_end_matches(".un");
        let ty = match suffix {
            "i1" => TypeSig::SByte,
            "i2" => TypeSig::Int16,
            "i4" => TypeSig::Int32,
            "i8" => TypeSig::Int64,
            "u1" => TypeSig::Byte,
            "u2" => TypeSig::UInt16,
            "u4" => TypeSig::UInt32,
            "u8" => TypeSig::UInt64,
            "r4" => TypeSig::Single,
            "r8" | "r" => TypeSig::Double,
            "i" => TypeSig::IntPtr,
            _ => TypeSig::UIntPtr,
        };
        // `ldlen; conv.i4` is how `array.Length` is read; the conversion is
        // the type it already has.
        if value.ty == ty || (matches!(value.expr, Expr::Length(_)) && ty == TypeSig::Int32) {
            self.push(value.expr, ty);
            return;
        }
        // `conv.u8` widens a 32-bit value as unsigned, `conv.i8` as signed,
        // whatever C# would take its type to say: the value goes through
        // the 32-bit type that widens that way.
        // A `bool` made a number is `b ? 1 : 0` first.
        let value = if value.ty == TypeSig::Boolean && !value.expr.is_constant() {
            Entry {
                expr: Expr::Conditional(
                    Box::new(value.expr),
                    Box::new(Expr::Int(1)),
                    Box::new(Expr::Int(0)),
                ),
                ty: TypeSig::Int32,
            }
        } else {
            value
        };
        let value = if checked {
            value
        } else {
            match (&value.ty, &ty) {
                (
                    TypeSig::SByte | TypeSig::Int16 | TypeSig::Int32,
                    TypeSig::UInt64 | TypeSig::UIntPtr,
                ) if !matches!(value.expr, Expr::Int(n) if n >= 0) => Entry {
                    expr: match value.expr {
                        Expr::Int(n) => Expr::Long(i64::from(n as u32)),
                        other => Expr::Cast(TypeSig::UInt32, Box::new(other)),
                    },
                    ty: TypeSig::UInt32,
                },
                (TypeSig::UInt32, TypeSig::Int64 | TypeSig::IntPtr)
                    if !value.expr.is_constant() =>
                {
                    Entry {
                        expr: Expr::Cast(TypeSig::Int32, Box::new(value.expr)),
                        ty: TypeSig::Int32,
                    }
                }
                _ => value,
            }
        };
        let expr = match (&value.expr, &ty) {
            (Expr::Long(n), TypeSig::UInt64) => Expr::Long(*n),
            (Expr::Int(n), TypeSig::Int64) => Expr::Long(*n),
            (Expr::Int(n), TypeSig::Double) => Expr::Float(*n as f64, false),
            (Expr::Int(n), TypeSig::Single) => Expr::Float(*n as f64, true),
            (Expr::Float(f, _), TypeSig::Double) => Expr::Float(*f, false),
            (Expr::Float(f, _), TypeSig::Single) => Expr::Float(*f, true),
            _ if checked => Expr::CheckedCast(ty.clone(), Box::new(value.expr)),
            _ => Expr::Cast(ty.clone(), Box::new(value.expr)),
        };
        self.push(expr, ty);
    }

    /// Two operands made to agree: a constant takes the type of the other side.
    fn unify(&self, left: Entry, right: Entry) -> (Expr, Expr) {
        if left.expr.is_constant() && !right.expr.is_constant() {
            let left = self.coerce(left, &right.ty);
            (left, right.expr)
        } else if right.expr.is_constant() && !left.expr.is_constant() {
            let right = self.coerce(right, &left.ty);
            (left.expr, right)
        } else {
            (left.expr, right.expr)
        }
    }

    fn comparison(&mut self, op: Cmp, unordered: bool) -> Expr {
        let right = self.pop();
        let left = self.pop();
        let float = matches!(left.ty, TypeSig::Single | TypeSig::Double)
            || matches!(right.ty, TypeSig::Single | TypeSig::Double);
        // `x > null` with `cgt.un` is how `x != null` is asked, and
        // `(x as T) != null` is `x is T`.
        let not_null = |expr: Expr| match expr {
            Expr::As(ty, inner) => Expr::Is(ty, inner),
            other => Expr::compare(Cmp::Ne, other, Expr::Null),
        };
        if right.expr == Expr::Null && op == Cmp::Gt {
            return not_null(left.expr);
        }
        if left.expr == Expr::Null && op == Cmp::Lt {
            return not_null(right.expr);
        }
        let left_is_bool = left.ty == TypeSig::Boolean;
        // `ceq` on strings or delegates compares references, which C# says
        // with a cast to `object`; `==` on them would compare values.
        let by_reference = matches!(op, Cmp::Eq | Cmp::Ne)
            && left.expr != Expr::Null
            && right.expr != Expr::Null
            && (left.ty == TypeSig::String
                || self.resolver().is_delegate(&left.ty)
                || self.resolver().has_equality_operator(&left.ty)
                || self.resolver().has_equality_operator(&right.ty));
        let (mut left_expr, right_expr) = self.unify(left, right);
        if by_reference {
            left_expr = Expr::Cast(TypeSig::Object, Box::new(left_expr));
        }
        // `flag == false` is `!flag`, and `(a < b) == false` is `a >= b`.
        if op == Cmp::Eq && right_expr == Expr::Bool(false) {
            return negate(left_expr);
        }
        if op == Cmp::Eq && right_expr == Expr::Bool(true) {
            return left_expr;
        }
        // `flag > false` is how a `bool` is normalised: it is `flag`.
        if op == Cmp::Gt && left_is_bool && right_expr == Expr::Bool(false) {
            return left_expr;
        }
        // `cgt.un x, 0` is how `x != 0` is asked.
        if op == Cmp::Gt
            && unordered
            && !float
            && matches!(right_expr, Expr::Int(0) | Expr::Long(0))
        {
            return Expr::compare(Cmp::Ne, left_expr, right_expr);
        }
        Expr::Compare {
            op,
            left: Box::new(left_expr),
            right: Box::new(right_expr),
            float,
            unordered,
        }
    }

    /// The value as a condition: a `bool` stays, anything else is compared
    /// with zero or null the way `brtrue` compares it.
    fn truthy(&self, value: Entry) -> Expr {
        match value.ty {
            TypeSig::Boolean => value.expr,
            _ if is_reference(&value.ty) => match value.expr {
                Expr::As(ty, inner) => Expr::Is(ty, inner),
                other => Expr::compare(Cmp::Ne, other, Expr::Null),
            },
            _ => match value.expr {
                Expr::Compare { .. } | Expr::Bool(_) => value.expr,
                Expr::Int(n) => Expr::Bool(n != 0),
                Expr::Conditional(..) => value.expr,
                other => Expr::compare(Cmp::Ne, other, Expr::Int(0)),
            },
        }
    }

    /// A value made to fit the type that consumes it: `1` becomes `true` for
    /// a `bool`, `97` becomes `'a'` for a `char`, `5` becomes `Color.Green`.
    fn coerce(&self, value: Entry, target: &TypeSig) -> Expr {
        coerce_expr(self.resolver(), value.expr, target)
    }

    #[allow(clippy::too_many_lines)]
    fn call(&mut self, token: Token, creating: bool, is_virtual: bool, constrained: Option<Token>) {
        let Some(mut method) = self.resolver().method_ref(token) else {
            self.emit(Stmt::Comment(format!("call to {token:?}")));
            return;
        };
        // A static abstract member called through a type parameter is
        // `T.M()`, the constraint naming the type.
        if let Some(constrained) = constrained
            && !method.sig.instance
        {
            method.declaring = self.resolver().token_sig(constrained);
        }
        let count = method.sig.parameters.len();
        let mut args: Vec<Expr> = Vec::with_capacity(count);
        let entries = self.pop_n(count);
        for (entry, param) in entries.into_iter().zip(method.sig.parameters.clone()) {
            let mut expr = self.coerce(entry, &param);
            if matches!(param, TypeSig::ByRef(_))
                && !matches!(expr, Expr::Unary(UnOp::AddressOf, _))
            {
                expr = Expr::unary(UnOp::AddressOf, expr);
            }
            args.push(expr);
        }
        let returns = substitute(&method.sig.returns, &method.declaring, &method.type_args);

        if creating {
            // A delegate is made from a target and a method address.
            if args.len() == 2
                && let Expr::FunctionPointer(pointed) = &args[1]
            {
                let target = match &args[0] {
                    Expr::Null => None,
                    other => Some(Box::new(other.clone())),
                };
                let ty = method.declaring.clone();
                self.push(
                    Expr::Delegate {
                        ty: ty.clone(),
                        target,
                        method: pointed.clone(),
                    },
                    ty,
                );
                return;
            }
            let ty = method.declaring.clone();
            if let Some(literal) = decimal_literal(self.resolver(), &method, &args) {
                self.push(literal, ty);
                return;
            }
            // `new ValueTuple<A, B>(a, b)` is the tuple `(a, b)`.
            if args.len() >= 2
                && let TypeSig::Generic { definition, .. } = &ty
                && let TypeSig::ValueType(token) | TypeSig::Class(token) = definition.as_ref()
                && self
                    .resolver()
                    .raw_name(*token)
                    .is_some_and(|raw| raw.starts_with("System.ValueTuple`"))
            {
                self.push(Expr::Tuple(args), ty);
                return;
            }
            self.push(
                Expr::New {
                    ctor: method,
                    args,
                    initializer: Vec::new(),
                },
                ty,
            );
            return;
        }

        let receiver = if method.sig.instance {
            let entry = self.pop();
            Some(entry.expr)
        } else {
            None
        };
        let _ = constrained;

        // `x = new T(...)` on a value type is a constructor call through the
        // variable's address.
        if method.is_constructor() {
            if let Some(receiver) = receiver {
                let target = strip_address(receiver);
                if target == Expr::This {
                    // `this(...)` or `base(...)`: kept as a call.
                    self.emit(Stmt::Expr(Expr::Call {
                        method,
                        receiver: Some(Box::new(Expr::This)),
                        args,
                    }));
                } else {
                    let ty = method.declaring.clone();
                    self.emit(Stmt::Expr(Expr::assign(
                        target,
                        Expr::New {
                            ctor: method,
                            args,
                            initializer: Vec::new(),
                        },
                    )));
                    let _ = ty;
                }
            }
            return;
        }

        // `typeof(T)` is `ldtoken` followed by `GetTypeFromHandle`.
        if method.name == "GetTypeFromHandle"
            && args.len() == 1
            && let Expr::TypeOf(_) = &args[0]
        {
            let ty = args.pop().unwrap_or(Expr::Null);
            self.push(ty, returns);
            return;
        }
        // `RuntimeHelpers.InitializeArray(array, token)` fills a fresh array
        // from a data blob: the values are read back into an initializer.
        if method.name == "InitializeArray" && args.len() == 2 {
            let resolver = self.ctx.resolver;
            if let (Expr::Slot(slot), Expr::Field { field, .. }) = (&args[0], &args[1])
                && let Some(Stmt::Expr(Expr::Assign(target, value))) = self.stmts.last_mut()
                && **target == Expr::Slot(*slot)
            {
                // A multi-dimensional array is made by its type's
                // constructor, and its values are row by row.
                if let Expr::New { ctor, args, .. } = value.as_ref()
                    && let TypeSig::Array { element, rank } = &ctor.declaring
                    && *rank as usize == args.len()
                    && let Some(count) = args.iter().try_fold(1i64, |total, size| match size {
                        Expr::Int(n) => total.checked_mul(*n),
                        _ => None,
                    })
                    && let Some(values) = crate::data::array_items(resolver, field, element, count)
                {
                    **value = Expr::NewArray {
                        element: (**element).clone(),
                        size: Box::new(Expr::Tuple(args.clone())),
                        items: Some(values),
                    };
                    return;
                }
                if let Expr::NewArray {
                    element,
                    size,
                    items,
                } = value.as_mut()
                    && let Expr::Int(count) = **size
                    && let Some(values) = crate::data::array_items(resolver, field, element, count)
                {
                    *items = Some(values);
                    return;
                }
            }
            self.emit(Stmt::Expr(Expr::Call {
                method,
                receiver: None,
                args,
            }));
            return;
        }

        let mut receiver = receiver.map(|receiver| Box::new(strip_address(receiver)));
        // A non-virtual call on `this` to a virtual member of another type
        // is `base.M()`: the one way C# reaches an overridden member. A
        // member that is not virtual, nor hidden here, is reached as `M()`.
        if !is_virtual
            && receiver.as_deref() == Some(&Expr::This)
            && !self.is_own_type(&method.declaring)
            && !self.resolver().is_value_type(&method.declaring)
            && (method.is_virtual
                || self
                    .resolver()
                    .declares_method(&self.ctx.this_type, &method.name))
        {
            receiver = Some(Box::new(Expr::Base));
        }
        // A call on `this` through an interface's member reaches the
        // explicit implementation, which only the cast names.
        if is_virtual
            && receiver.as_deref() == Some(&Expr::This)
            && !self.is_own_type(&method.declaring)
            && self.resolver().is_interface(&method.declaring)
        {
            receiver = Some(Box::new(Expr::Cast(
                method.declaring.clone(),
                Box::new(Expr::This),
            )));
        }
        let expr = Expr::Call {
            method,
            receiver,
            args,
        };
        if matches!(returns, TypeSig::Void) {
            self.emit(Stmt::Expr(expr));
        } else {
            self.push(expr, returns);
        }
    }
}

/// What a statement may change.
#[derive(Debug, Default)]
struct Writes {
    locals: Vec<u16>,
    args: Vec<u16>,
    /// Whether it may write memory anyone else can see: a field, an
    /// element, a pointer, or anything a call does.
    memory: bool,
}

fn writes_of(stmt: &Stmt) -> Writes {
    let mut writes = Writes::default();
    let Stmt::Expr(expr) = stmt else {
        return writes;
    };
    match expr {
        Expr::Assign(target, value) => {
            match target.as_ref() {
                Expr::Local(at) => writes.locals.push(*at),
                Expr::Arg(at) => writes.args.push(*at),
                _ => writes.memory = true,
            }
            if !value.is_pure() {
                writes.memory = true;
            }
        }
        _ => writes.memory = true,
    }
    writes
}

/// Whether a stack entry has to be evaluated before a statement that writes
/// what it says: a call, or a read of something the statement changes.
fn must_spill(expr: &Expr, writes: &Writes) -> bool {
    if !expr.is_pure() {
        return true;
    }
    let mut spill = false;
    expr.walk(&mut |e| match e {
        Expr::Local(at) if writes.locals.contains(at) => spill = true,
        Expr::Arg(at) if writes.args.contains(at) => spill = true,
        Expr::Field { .. } | Expr::Index { .. } | Expr::Unary(UnOp::Deref, _) | Expr::Length(_)
            if writes.memory =>
        {
            spill = true;
        }
        _ => {}
    });
    spill
}

/// `x` out of `&x`.
fn strip_address(expr: Expr) -> Expr {
    match expr {
        Expr::Unary(UnOp::AddressOf, inner) => *inner,
        other => other,
    }
}

/// A constant made to fit the type that consumes it.
pub(crate) fn coerce_expr(resolver: Resolver<'_>, expr: Expr, target: &TypeSig) -> Expr {
    match (&expr, target) {
        (Expr::Int(0), TypeSig::Boolean) => Expr::Bool(false),
        (Expr::Int(1), TypeSig::Boolean) => Expr::Bool(true),
        (Expr::Int(n), TypeSig::Char) => Expr::Char(*n as u16),
        (Expr::Int(n), TypeSig::Int64) => Expr::Long(*n),
        // Unsigned, `1UL`: a shift or a division of it is.
        (Expr::Int(n), TypeSig::UInt64) => Expr::Cast(TypeSig::UInt64, Box::new(Expr::Long(*n))),
        (Expr::Int(n), TypeSig::Double) => Expr::Float(*n as f64, false),
        (Expr::Int(n), TypeSig::Single) => Expr::Float(*n as f64, true),
        (Expr::Float(f, false), TypeSig::Single) => Expr::Float(*f, true),
        (
            Expr::Int(n) | Expr::Long(n),
            TypeSig::ValueType(_) | TypeSig::Class(_) | TypeSig::Generic { .. },
        ) => match resolver.enum_of(target) {
            Some(members) => enum_constant(target, &members, *n),
            None => expr,
        },
        // `stackalloc` allocates bytes; the pointer it is stored in says
        // what of.
        (Expr::StackAlloc(TypeSig::Byte, size), TypeSig::Pointer(element))
            if **element != TypeSig::Byte && **element != TypeSig::Void =>
        {
            let mut bytes = size.as_ref();
            loop {
                match bytes {
                    Expr::Checked(inner) => bytes = inner,
                    Expr::Cast(TypeSig::UIntPtr | TypeSig::IntPtr, inner)
                        if matches!(inner.as_ref(), Expr::Int(_) | Expr::Checked(_)) =>
                    {
                        bytes = inner;
                    }
                    _ => break,
                }
            }
            match unscale(bytes, element) {
                Some(count) => Expr::StackAlloc((**element).clone(), Box::new(count)),
                None => expr,
            }
        }
        (Expr::Null, TypeSig::ValueType(_)) => Expr::Default(target.clone()),
        (Expr::Null, TypeSig::Generic { definition, .. })
            if matches!(**definition, TypeSig::ValueType(_)) =>
        {
            Expr::Default(target.clone())
        }
        // A `null` branch beside a value of a struct is what is left of a
        // `T?` whose other branch was unwrapped: it stays `null`, which the
        // printer says as `(T?)null`, not the `default(T)` it is not.
        (Expr::Conditional(condition, a, b), _) => {
            let branch = |value: &Expr| match value {
                Expr::Null if resolver.is_value_type(target) && !resolver.is_nullable(target) => {
                    Expr::Null
                }
                other => coerce_expr(resolver, other.clone(), target),
            };
            Expr::Conditional(condition.clone(), Box::new(branch(a)), Box::new(branch(b)))
        }
        _ => expr,
    }
}

/// `Color.Red`, `Color.Read | Color.Write` or `(Color)7` for a value of an
/// enum defined here.
fn enum_constant(ty: &TypeSig, members: &[(String, i64)], value: i64) -> Expr {
    if let Some((name, _)) = members.iter().find(|(_, v)| *v == value) {
        return Expr::EnumMember(ty.clone(), name.clone());
    }
    // Flags: a combination of members that covers the value exactly.
    let mut rest = value;
    let mut parts = Vec::new();
    for (name, v) in members.iter().rev() {
        if *v != 0 && rest & v == *v {
            parts.push(name.clone());
            rest &= !v;
        }
    }
    if rest == 0 && !parts.is_empty() && value != 0 {
        parts.reverse();
        return parts
            .into_iter()
            .map(|name| Expr::EnumMember(ty.clone(), name))
            .reduce(|a, b| Expr::binary(BinOp::Or, a, b))
            .unwrap_or(Expr::Int(value));
    }
    Expr::Cast(ty.clone(), Box::new(Expr::Int(value)))
}

/// `!condition`, pushed as far into the expression as it will go.
#[must_use]
pub fn negate(expr: Expr) -> Expr {
    match expr {
        Expr::Bool(value) => Expr::Bool(!value),
        Expr::Unary(UnOp::Not, inner) => *inner,
        Expr::Compare {
            op,
            left,
            right,
            float,
            unordered,
        } => Expr::Compare {
            op: op.negated(),
            left,
            right,
            float,
            // For floats the flag says what NaN does and flips with the
            // comparison; for integers it says "unsigned", which does not.
            unordered: if float { !unordered } else { unordered },
        },
        Expr::Binary(BinOp::LogicalAnd, left, right) => {
            Expr::binary(BinOp::LogicalOr, negate(*left), negate(*right))
        }
        Expr::Binary(BinOp::LogicalOr, left, right) => {
            Expr::binary(BinOp::LogicalAnd, negate(*left), negate(*right))
        }
        Expr::Conditional(condition, a, b) => {
            Expr::Conditional(condition, Box::new(negate(*a)), Box::new(negate(*b)))
        }
        other => Expr::unary(UnOp::Not, other),
    }
}

/// Whether values of the type are references, which a branch tests against
/// null.
fn is_reference(ty: &TypeSig) -> bool {
    matches!(
        ty,
        TypeSig::String
            | TypeSig::Object
            | TypeSig::Class(_)
            | TypeSig::Vector(_)
            | TypeSig::Array { .. }
            | TypeSig::Var(_)
            | TypeSig::MVar(_)
    ) || matches!(ty, TypeSig::Generic { definition, .. } if matches!(**definition, TypeSig::Class(_)))
}

/// The type an arithmetic result has, by the rules IL merges operands with.
/// A pointer read or written as a different size than it points to:
/// `*(int*)p` where `p` is a `byte*` or a `void*`.
fn retype_pointer(address: Entry, instruction: &str) -> Entry {
    let suffix = instruction.rsplit('.').next().unwrap_or("");
    if matches!(suffix, "ref" | "ldobj" | "stobj" | "ldind" | "stind") {
        return address;
    }
    let accessed = match suffix {
        "u1" => TypeSig::Byte,
        "u2" => TypeSig::UInt16,
        "u4" => TypeSig::UInt32,
        "u8" => TypeSig::UInt64,
        other => element_of_suffix(&format!(".{other}")),
    };
    if accessed == TypeSig::Object {
        return address;
    }
    // A native integer used as an address is a pointer to what is read.
    if matches!(address.ty, TypeSig::IntPtr | TypeSig::UIntPtr) {
        let ty = TypeSig::Pointer(Box::new(accessed));
        return Entry {
            expr: Expr::Cast(ty.clone(), Box::new(address.expr)),
            ty,
        };
    }
    let TypeSig::Pointer(element) = &address.ty else {
        return address;
    };
    let differs = match (element_size(element), element_size(&accessed)) {
        (Some(have), Some(want)) => have != want,
        _ => matches!(element.as_ref(), TypeSig::Void),
    };
    if !differs {
        return address;
    }
    let ty = TypeSig::Pointer(Box::new(accessed));
    Entry {
        expr: Expr::Cast(ty.clone(), Box::new(address.expr)),
        ty,
    }
}

/// The size of a pointer's element when it is a constant of the language.
fn element_size(element: &TypeSig) -> Option<i64> {
    Some(match element {
        TypeSig::Boolean | TypeSig::SByte | TypeSig::Byte => 1,
        TypeSig::Char | TypeSig::Int16 | TypeSig::UInt16 => 2,
        TypeSig::Int32 | TypeSig::UInt32 | TypeSig::Single => 4,
        TypeSig::Int64 | TypeSig::UInt64 | TypeSig::Double => 8,
        _ => return None,
    })
}

/// An offset in bytes as a count of pointer elements: `(nint)i * 4` on an
/// `int*` is `i`, `8` is `2`, `sizeof(S)` on an `S*` is `1`.
pub(crate) fn unscale(offset: &Expr, element: &TypeSig) -> Option<Expr> {
    let size = element_size(element);
    let is_size = |e: &Expr| match e {
        Expr::Int(n) | Expr::Long(n) => size == Some(*n),
        Expr::SizeOf(ty) => ty == element,
        _ => false,
    };
    // The index, without the widening to a native integer the IL adds.
    let strip = |e: &Expr| -> Expr {
        match e {
            Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr | TypeSig::Int64, inner) => {
                (**inner).clone()
            }
            other => other.clone(),
        }
    };
    match offset {
        Expr::Int(n) | Expr::Long(n) => {
            let size = size?;
            (n % size == 0).then(|| Expr::Int(n / size))
        }
        Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr, inner) if size.is_none() => {
            unscale(inner, element)
        }
        Expr::Cast(TypeSig::IntPtr | TypeSig::UIntPtr, inner)
            if matches!(inner.as_ref(), Expr::Binary(BinOp::Mul, ..)) =>
        {
            unscale(inner, element)
        }
        Expr::SizeOf(ty) if ty == element => Some(Expr::Int(1)),
        Expr::Binary(BinOp::Mul, left, right) if is_size(right) => Some(strip(left)),
        Expr::Binary(BinOp::Mul, left, right) if is_size(left) => Some(strip(right)),
        other if size == Some(1) => Some(strip(other)),
        _ => None,
    }
}

fn arithmetic_type(left: &TypeSig, right: &TypeSig) -> TypeSig {
    match (left, right) {
        (TypeSig::Double, _) | (_, TypeSig::Double) => TypeSig::Double,
        (TypeSig::Single, _) | (_, TypeSig::Single) => TypeSig::Single,
        (TypeSig::Int64 | TypeSig::UInt64, _) => left.clone(),
        (_, TypeSig::Int64 | TypeSig::UInt64) => right.clone(),
        (TypeSig::IntPtr | TypeSig::UIntPtr | TypeSig::Pointer(_) | TypeSig::ByRef(_), _) => {
            left.clone()
        }
        (_, TypeSig::IntPtr | TypeSig::UIntPtr | TypeSig::Pointer(_) | TypeSig::ByRef(_)) => {
            right.clone()
        }
        (TypeSig::Boolean | TypeSig::Char, _) => TypeSig::Int32,
        _ => left.clone(),
    }
}

/// The element type an `ldelem.*` suffix names.
fn element_of_suffix(name: &str) -> TypeSig {
    match name.rsplit('.').next().unwrap_or("") {
        "i1" => TypeSig::SByte,
        "u1" => TypeSig::Byte,
        "i2" => TypeSig::Int16,
        "u2" => TypeSig::UInt16,
        "i4" => TypeSig::Int32,
        "u4" => TypeSig::UInt32,
        "i8" => TypeSig::Int64,
        "i" => TypeSig::IntPtr,
        "r4" => TypeSig::Single,
        "r8" => TypeSig::Double,
        _ => TypeSig::Object,
    }
}

/// A signature type with the generic parameters of a call filled in from
/// the declaring type's arguments and the method's own.
#[must_use]
pub fn substitute(ty: &TypeSig, declaring: &TypeSig, method_args: &[TypeSig]) -> TypeSig {
    let type_args: &[TypeSig] = match declaring {
        TypeSig::Generic { arguments, .. } => arguments,
        _ => &[],
    };
    substitute_with(ty, type_args, method_args)
}

/// A signature type with `!n` and `!!n` replaced.
#[must_use]
pub fn substitute_with(ty: &TypeSig, type_args: &[TypeSig], method_args: &[TypeSig]) -> TypeSig {
    match ty {
        TypeSig::Var(at) => type_args
            .get(*at as usize)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        TypeSig::MVar(at) => method_args
            .get(*at as usize)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        TypeSig::Vector(inner) => {
            TypeSig::Vector(Box::new(substitute_with(inner, type_args, method_args)))
        }
        TypeSig::Array { element, rank } => TypeSig::Array {
            element: Box::new(substitute_with(element, type_args, method_args)),
            rank: *rank,
        },
        TypeSig::Pointer(inner) => {
            TypeSig::Pointer(Box::new(substitute_with(inner, type_args, method_args)))
        }
        TypeSig::ByRef(inner) => {
            TypeSig::ByRef(Box::new(substitute_with(inner, type_args, method_args)))
        }
        TypeSig::Generic {
            definition,
            arguments,
        } => TypeSig::Generic {
            definition: definition.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_with(argument, type_args, method_args))
                .collect(),
        },
        other => other.clone(),
    }
}

/// `1.5m` out of `new decimal(lo, mid, hi, isNegative, scale)`.
fn decimal_literal(resolver: Resolver<'_>, ctor: &MethodRef, args: &[Expr]) -> Option<Expr> {
    let (TypeSig::ValueType(token) | TypeSig::Class(token)) = &ctor.declaring else {
        return None;
    };
    if resolver.raw_name(*token).as_deref() != Some("System.Decimal") {
        return None;
    }
    // `new decimal(2)`: an integer written as a decimal.
    if let [Expr::Int(n) | Expr::Long(n)] = args {
        return Some(Expr::Raw(format!("{n}m")));
    }
    if args.len() != 5 {
        return None;
    }
    let number = |expr: &Expr| match expr {
        Expr::Int(n) => Some(*n),
        Expr::Bool(b) => Some(i64::from(*b)),
        _ => None,
    };
    let lo = number(&args[0])? as u32;
    let mid = number(&args[1])? as u32;
    let hi = number(&args[2])? as u32;
    let negative = number(&args[3])? != 0;
    let scale = number(&args[4])? as u32;
    Some(Expr::Raw(decimal_text(lo, mid, hi, negative, scale)))
}

/// A decimal's parts as a literal: `1.5m`.
pub(crate) fn decimal_text(lo: u32, mid: u32, hi: u32, negative: bool, scale: u32) -> String {
    let magnitude = (u128::from(hi) << 64) | (u128::from(mid) << 32) | u128::from(lo);
    let digits = magnitude.to_string();
    let mut text = if scale == 0 {
        digits
    } else {
        let scale = scale as usize;
        let padded = format!("{digits:0>width$}", width = scale + 1);
        let (whole, fraction) = padded.split_at(padded.len() - scale);
        format!("{whole}.{fraction}")
    };
    if negative {
        text.insert(0, '-');
    }
    text.push('m');
    text
}
