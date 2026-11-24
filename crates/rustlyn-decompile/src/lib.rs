//! Turning a .NET assembly back into C#.
//!
//! [`rustlyn_metadata`] reads the tables and the IL; this reads the IL as
//! expressions, the branches as statements, and the rows as declarations,
//! and writes what a programmer would have typed to get that assembly. It
//! is `rustlyn-emit` run backwards one more step than the metadata reader:
//! not just the bytes, but the source.
//!
//! The pipeline for one method body:
//!
//! 1. [`stack`] cuts the IL into basic blocks and replays the evaluation
//!    stack symbolically, so every instruction that consumes values gets
//!    the expression trees that produced them.
//! 2. [`structure`] walks the blocks in order and recognises the shapes a
//!    compiler emits: a branch over a range is an `if`, a branch back is a
//!    loop, an exception clause is a `try`.
//! 3. [`simplify`] folds what is left of the translation back into idioms:
//!    temporaries into expressions, accessor calls into properties,
//!    enumerator loops into `foreach`.
//! 4. [`print`] names the locals, decides where each is declared, and
//!    writes the text; [`members`] does the same for the declarations.

pub mod closures;
pub mod data;
pub mod fit;
pub mod int_switches;
pub mod ir;
pub mod machines;
pub mod members;
pub mod names;
pub mod print;
pub mod simplify;
pub mod stack;
pub mod structure;
pub mod switches;
pub mod tails;

use std::collections::HashMap;

use rustlyn_metadata::body::Instruction;
use rustlyn_metadata::signature::{Blob, TypeSig};
use rustlyn_metadata::{Assembly, Body, Token, table};

use ir::Stmt;
use names::Resolver;
use stack::MethodContext;

/// What the decompiler is asked to do.
#[derive(Clone, Debug)]
pub struct Options {
    /// Whether the types and methods the compiler made up are written out,
    /// beyond the ones folded back into lambdas.
    pub compiler_generated: bool,
    /// Whether lambdas are folded back out of their lifted methods.
    pub lambdas: bool,
    /// How many lambdas deep the folding is; zero at a method's own level.
    pub depth: usize,
    /// The methods and types folded into others so far, shared across the
    /// whole assembly's decompilation.
    pub consumed: std::rc::Rc<std::cell::RefCell<closures::Consumed>>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            compiler_generated: true,
            lambdas: true,
            depth: 0,
            consumed: std::rc::Rc::default(),
        }
    }
}

/// A decompiled method body with what printing it needs.
#[derive(Debug)]
pub struct Decompiled<'a> {
    pub stmts: Vec<Stmt>,
    pub ctx: MethodContext<'a>,
    pub slot_types: HashMap<u32, TypeSig>,
    pub param_names: Vec<String>,
    /// Names the simplifier suggests for locals it made or renamed.
    pub local_hints: HashMap<u16, String>,
    /// Whether the method carries an `AsyncStateMachine` attribute.
    pub is_async: bool,
    /// Whether the constructor's base call has no arguments.
    pub base_call_is_trivial: bool,
}

impl<'a> Decompiled<'a> {
    /// A printer set up for this body.
    #[must_use]
    pub fn printer(&self) -> print::Printer<'_, 'a> {
        let mut printer =
            print::Printer::new(&self.ctx, self.param_names.clone(), &self.slot_types);
        printer.hints = self.local_hints.clone();
        printer
    }

    /// The type a field token of this assembly belongs to.
    #[must_use]
    pub fn resolver_field_owner(&self, token: Token) -> Option<u32> {
        self.ctx.resolver.field_owner(token.row())
    }
}

/// Decompiles the whole assembly, or just the types and methods a filter
/// such as `Type` or `Type::Method` names.
///
/// # Errors
///
/// Returns an error when the bytes are not a readable assembly.
pub fn decompile(
    bytes: &[u8],
    filter: Option<&str>,
    options: &Options,
) -> Result<String, rustlyn_metadata::Error> {
    decompile_with_references(bytes, &[], filter, options)
}

/// The same, following references into the given assemblies for what
/// they define: extension methods, `out` parameters, enum members, which
/// referenced types are structs, interfaces or delegates.
///
/// # Errors
///
/// Returns an error when the bytes are not a readable assembly; an image
/// among the references that is not one is skipped.
pub fn decompile_with_references(
    bytes: &[u8],
    references: &[&[u8]],
    filter: Option<&str>,
    options: &Options,
) -> Result<String, rustlyn_metadata::Error> {
    let assembly = Assembly::read(bytes)?;
    let mut index = names::Index::build(&assembly);
    let references = names::References::load(references);
    index.widen_ambiguous(&assembly, &references);
    let mut writer = members::Writer::new(&assembly, &index, options.clone());
    if !references.is_empty() {
        writer.resolver = writer.resolver.with_references(&references);
    }
    Ok(writer.assembly(filter))
}

/// The whole assembly as C#, and where each type and member is in it: an
/// editor goes to a declaration by this rather than by reading the text back,
/// which a construct the printer gets wrong would throw off for the rest of
/// the file.
///
/// # Errors
///
/// Returns an error when the bytes are not a readable assembly.
pub fn decompile_declared(
    bytes: &[u8],
    references: &[&[u8]],
    options: &Options,
) -> Result<(String, Vec<members::Declared>), rustlyn_metadata::Error> {
    let assembly = Assembly::read(bytes)?;
    let index = names::Index::build(&assembly);
    let references = names::References::load(references);
    let mut writer = members::Writer::new(&assembly, &index, options.clone());
    if !references.is_empty() {
        writer.resolver = writer.resolver.with_references(&references);
    }
    Ok(writer.assembly_declared(None))
}

/// `if (c) { A; return; } B;` at the end of a `void` body is
/// `if (c) { A } else { B }`, which is how it was written, and
/// `if (c) { return; } B;` is `if (!c) { B }`.
fn join_final_branches(stmts: &mut Vec<Stmt>) {
    if let Some(position) = stmts.iter().rposition(|stmt| {
        matches!(stmt, Stmt::If { then, otherwise, .. }
            if otherwise.is_empty() && matches!(then.as_slice(), [Stmt::Return(None)]))
    }) && position + 1 < stmts.len()
    {
        let mut rest: Vec<Stmt> = stmts[position + 1..].to_vec();
        if matches!(rest.last(), Some(Stmt::Return(None))) {
            rest.pop();
        }
        if !rest.is_empty()
            && !rest
                .iter()
                .any(|stmt| matches!(stmt, Stmt::Label(_) | Stmt::Return(Some(_))))
        {
            stmts.truncate(position + 1);
            if let Some(Stmt::If {
                condition, then, ..
            }) = stmts.last_mut()
            {
                *condition = stack::negate(condition.clone());
                *then = rest;
            }
            return;
        }
    }
    let Some(position) = stmts.iter().rposition(|stmt| {
        matches!(stmt, Stmt::If { then, otherwise, .. }
            if otherwise.is_empty() && matches!(then.last(), Some(Stmt::Return(None))) && then.len() > 1)
    }) else {
        return;
    };
    if position + 1 >= stmts.len() {
        return;
    }
    let rest: Vec<Stmt> = stmts[position + 1..].to_vec();
    if rest
        .iter()
        .any(|stmt| matches!(stmt, Stmt::Label(_) | Stmt::Return(Some(_))))
    {
        return;
    }
    let mut rest = rest;
    if matches!(rest.last(), Some(Stmt::Return(None))) {
        rest.pop();
    }
    if rest.is_empty() {
        return;
    }
    stmts.truncate(position + 1);
    if let Some(Stmt::If {
        then, otherwise, ..
    }) = stmts.last_mut()
    {
        then.pop();
        *otherwise = rest;
    }
}

/// The decoded body of a method, when it has one.
#[must_use]
pub fn body_of(resolver: Resolver<'_>, method_row: u32) -> Option<Body> {
    let method = resolver.assembly.table(table::METHOD_DEF).row(method_row)?;
    let rva = method.number(0);
    if rva == 0 {
        return None;
    }
    let offset = resolver.assembly.image().offset_of(rva).ok()? as usize;
    let rest = resolver.assembly.image().bytes().get(offset..)?;
    Body::read(rest).ok()
}

/// The instructions of a method body, for the pattern checks that read IL
/// directly.
#[must_use]
pub fn instructions_of(resolver: Resolver<'_>, method_row: u32) -> Option<Vec<Instruction>> {
    body_of(resolver, method_row).map(|body| body.instructions)
}

/// The parameter names of a method, `this` not counted, made up where the
/// metadata has none.
#[must_use]
pub fn param_names(resolver: Resolver<'_>, method_row: u32, count: usize) -> Vec<String> {
    let mut names = vec![String::new(); count];
    for (sequence, _, name) in resolver.params_of(method_row) {
        if sequence == 0 {
            continue;
        }
        if let Some(slot) = names.get_mut(sequence as usize - 1) {
            *slot = name;
        }
    }
    for (index, name) in names.iter_mut().enumerate() {
        if name.is_empty() {
            *name = format!("P_{index}");
        }
    }
    names
}

/// Decompiles one method body.
#[must_use]
pub fn decompile_body<'a>(
    resolver: Resolver<'a>,
    method_row: u32,
    options: &Options,
) -> Option<Decompiled<'a>> {
    let method = resolver.assembly.table(table::METHOD_DEF).row(method_row)?;
    if std::env::var_os("RUSTLYN_DECOMPILE_TRACE").is_some() {
        eprintln!(
            "method {method_row} {} (depth {})",
            resolver.assembly.heaps().string(method.number(3)),
            options.depth
        );
    }
    // A method's own level starts its budget of folds afresh.
    if options.depth == 0 {
        options.consumed.borrow_mut().folded = 0;
    }
    let body = body_of(resolver, method_row)?;
    let sig = resolver.method_sig_at(method.number(4))?;
    let owner = resolver.method_owner(method_row)?;
    let generics = resolver.generics_of(method_row);
    let locals = match body.locals {
        Some(token) => resolver
            .assembly
            .row(token)
            .and_then(|row| resolver.assembly.heaps().blob(row.number(0)).ok())
            .and_then(|bytes| Blob::new(bytes).locals_sig().ok())
            .unwrap_or_default(),
        None => Vec::new(),
    };
    let is_static = method.number(2) & 0x0010 != 0;
    let mut this_type = resolver.declared_type_sig(owner);
    if resolver.is_value_type(&this_type) {
        this_type = TypeSig::ByRef(Box::new(this_type));
    }
    let ctx = MethodContext {
        resolver,
        generics,
        is_static,
        this_type,
        params: sig.parameters.clone(),
        locals,
        returns: sig.returns.clone(),
    };
    let blocks = stack::read(&ctx, &body);
    let debug = std::env::var_os("RUSTLYN_DECOMPILE_DEBUG").is_some();
    if debug {
        for block in &blocks.blocks {
            eprintln!("-- block IL_{:04x}..IL_{:04x}", block.start, block.end);
            for stmt in &block.stmts {
                eprint!("{}", print::stmt_text(&ctx, stmt));
            }
            eprintln!("   -> {:?}", block.terminator);
        }
    }
    let mut stmts = structure::structure(resolver, &blocks, &body.regions, body.code_size);
    if debug {
        eprintln!("-- structured");
        for stmt in &stmts {
            eprint!("{}", print::stmt_text(&ctx, stmt));
        }
    }
    let typer = simplify::Typer {
        ctx: &ctx,
        slot_types: &blocks.slot_types,
        extra_locals: std::cell::RefCell::new(Vec::new()),
        hints: std::cell::RefCell::new(HashMap::new()),
    };
    simplify::simplify(&typer, &mut stmts);
    if debug {
        eprintln!("-- simplified");
        for stmt in &stmts {
            eprint!("{}", print::stmt_text(&ctx, stmt));
        }
    }
    closures::inline(&typer, options, &mut stmts);
    if debug {
        eprintln!("-- closures");
        for stmt in &stmts {
            eprint!("{}", print::stmt_text(&ctx, stmt));
        }
    }
    simplify::simplify(&typer, &mut stmts);
    if debug {
        eprintln!("-- final");
        for stmt in &stmts {
            eprint!("{}", print::stmt_text(&ctx, stmt));
        }
    }
    let mut retyped = ctx.locals.clone();
    retyped.extend(typer.extra_locals.borrow().iter().cloned());
    let mut slot_types = blocks.slot_types.clone();
    simplify::retype_span_strings(&typer, &stmts, &mut retyped, &mut slot_types);
    simplify::retype_object_slots(&typer, &stmts, &mut slot_types);
    let local_hints = typer.hints.into_inner();
    let mut ctx = ctx;
    ctx.locals = retyped;
    if matches!(stmts.last(), Some(Stmt::Return(None))) {
        stmts.pop();
    }
    join_final_branches(&mut stmts);
    hoist_local_functions(&mut stmts);
    let is_async = resolver.has_attribute(
        Token::new(table::METHOD_DEF, method_row),
        "System.Runtime.CompilerServices.AsyncStateMachineAttribute",
    );
    let base_call_is_trivial = stmts.iter().any(|stmt| {
        matches!(stmt, Stmt::Expr(ir::Expr::Call { method, receiver: Some(receiver), args, .. })
            if method.is_constructor() && **receiver == ir::Expr::This && args.is_empty())
    });
    Some(Decompiled {
        stmts,
        param_names: param_names(resolver, method_row, sig.parameters.len()),
        local_hints,
        ctx,
        slot_types,
        is_async,
        base_call_is_trivial,
    })
}

/// A local function a pass moved into a block, with the statements it
/// ended the body with, is in sight only there: it goes back to the end of
/// the body, where every call can see it.
fn hoist_local_functions(stmts: &mut Vec<Stmt>) {
    fn take(stmts: &mut [Stmt], out: &mut Vec<Stmt>) {
        for stmt in stmts.iter_mut() {
            if matches!(stmt, Stmt::LocalFunction { .. }) {
                continue;
            }
            for block in stmt.blocks_mut() {
                let (functions, rest): (Vec<Stmt>, Vec<Stmt>) = std::mem::take(block)
                    .into_iter()
                    .partition(|inner| matches!(inner, Stmt::LocalFunction { .. }));
                *block = rest;
                out.extend(functions);
                take(block, out);
            }
        }
    }
    let mut functions = Vec::new();
    take(stmts, &mut functions);
    stmts.extend(functions);
}
