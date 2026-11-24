//! Lambdas back out of the classes the compiler lifted them into.
//!
//! A lambda that captures nothing becomes a static method; one that captures
//! `this` becomes an instance method; one that captures locals becomes a
//! method of a display class whose fields are the captured variables, and
//! the enclosing method reads and writes those variables through the fields.
//! This pass undoes that: the display class's fields become locals of the
//! enclosing method again, its instance disappears, and every delegate made
//! from one of the lifted methods becomes a lambda whose body is that
//! method's, decompiled and transplanted with its variables renumbered into
//! the enclosing method's.

use std::collections::{HashMap, HashSet};

use rustlyn_metadata::signature::TypeSig;
use rustlyn_metadata::{Token, table};

use crate::ir::{BinOp, Body, Expr, Stmt};
use crate::names::Resolver;
use crate::simplify::Typer;
use crate::{Options, decompile_body};

/// The methods and types that were folded into something else and should
/// not be written on their own.
#[derive(Debug, Default)]
pub struct Consumed {
    pub methods: HashSet<u32>,
    pub types: HashSet<u32>,
    /// The lifted methods being folded right now, so that one calling
    /// itself is folded once rather than without end.
    pub in_progress: HashSet<u32>,
    /// State machine types whose methods were folded back into theirs.
    pub machines: HashSet<u32>,
    /// Lifted methods folded into the method being decompiled now, counted
    /// from its own level. See [`FOLD_BUDGET`].
    pub folded: usize,
}

/// How many lifted methods one method's body may fold in.
///
/// Each call site folds its lambda or local function afresh, with whatever
/// that one calls folded into it in turn. Local functions that call each
/// other through lambdas — Roslyn's `NullableWalker` is full of them — make
/// that a product of the call sites at every level: hundreds of thousands of
/// bodies for one method, and a body grown so large that structuring it ran
/// the stack out and took the editor down. Past the budget a call stays the
/// call it is in the IL, as it does wherever a closure cannot be folded.
pub const FOLD_BUDGET: usize = 512;

impl Consumed {
    /// Counts one more fold; `false` once the budget is spent.
    fn spend(&mut self) -> bool {
        self.folded += 1;
        self.folded <= FOLD_BUDGET
    }
}

/// Folds the closures of a body back into lambdas.
pub fn inline(typer: &Typer<'_, '_>, options: &Options, stmts: &mut Vec<Stmt>) {
    if options.depth > 4 || !options.lambdas {
        return;
    }
    let resolver = typer.ctx.resolver;
    promote_display_slots(typer, stmts);
    let mut pass = Pass {
        resolver,
        typer,
        options,
        fields: HashMap::new(),
        displays: HashMap::new(),
        aliases: HashMap::new(),
        local_functions: Vec::new(),
        next_lambda: 0,
        changed: false,
    };
    pass.find_displays(stmts);
    pass.absorb_field_stores(stmts);
    pass.absorb_aliases(stmts);
    pass.rewrite(stmts);
    let functions = std::mem::take(&mut pass.local_functions);
    if !functions.is_empty() {
        // Declared at the end of the body, before its final `return`.
        let at = if matches!(stmts.last(), Some(Stmt::Return(None))) {
            stmts.len() - 1
        } else {
            stmts.len()
        };
        for (offset, (_, function)) in functions.into_iter().enumerate() {
            stmts.insert(at + offset, function);
        }
    }
    if pass.changed {
        // A display class whose every field is a local again has no reason
        // to be constructed, nor copied about.
        let mut displays = pass.displays.clone();
        for (at, ty) in pass.typer.ctx.locals.iter().enumerate() {
            if let Some(row) = display_row(resolver, ty) {
                displays.insert(at as u16, row);
            }
        }
        for (at, ty) in pass.typer.extra_locals.borrow().iter().enumerate() {
            if let Some(row) = display_row(resolver, ty) {
                displays.insert((pass.typer.ctx.locals.len() + at) as u16, row);
            }
        }
        remove_display_constructions(stmts, &displays);
    }
}

struct Pass<'p, 'c, 'a> {
    resolver: Resolver<'a>,
    typer: &'p Typer<'c, 'a>,
    options: &'p Options,
    /// `(display type row, field name)` → what the field is in the method.
    fields: HashMap<(u32, String), Expr>,
    /// Display-class locals → the type row of the class.
    displays: HashMap<u16, u32>,
    /// Locals that are copies of a display reached through a field, such
    /// as `V = this.CS$<>8__locals`: what they alias, for the field
    /// mapping of an enclosing method to see through.
    aliases: HashMap<u16, Expr>,
    /// Local functions folded back, by method row, in order of first call.
    local_functions: Vec<(u32, Stmt)>,
    next_lambda: u32,
    changed: bool,
}

impl Pass<'_, '_, '_> {
    /// The `MethodDef` row of a method of this assembly a reference names:
    /// directly, or through a `MemberRef` on a generic instantiation of one
    /// of its own types, as a lambda in a generic closure class is reached.
    fn own_method_row(&self, method: &crate::names::MethodRef) -> Option<u32> {
        if method.token.table() == table::METHOD_DEF {
            return Some(method.token.row());
        }
        let (there, row) = self.resolver.definition_of_method(method)?;
        std::ptr::eq(there.assembly, self.resolver.assembly).then_some(row)
    }

    /// The `TypeDef` row of `<>O`, the class C# 11 caches method-group
    /// delegates in.
    fn cache_class_row(&self, ty: &TypeSig) -> Option<u32> {
        let token = match ty {
            TypeSig::Class(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) => *token,
                _ => return None,
            },
            _ => return None,
        };
        (token.table() == table::TYPE_DEF
            && self
                .resolver
                .type_def_simple_name(token.row())
                .starts_with("<>O"))
        .then_some(token.row())
    }

    /// The `TypeDef` row of a display class a type names, if it is one.
    fn display_row(&self, ty: &TypeSig) -> Option<u32> {
        display_row(self.resolver, ty)
    }

    /// The display class a local holds, by what was stored into it or by
    /// its type, the locals made while folding included.
    fn display_of_local(&self, local: u16) -> Option<u32> {
        if let Some(row) = self.displays.get(&local) {
            return Some(*row);
        }
        let ty = self.typer.type_of(&Expr::Local(local))?;
        self.display_row(&ty)
    }

    /// Notes every local holding a display class instance: constructed, or
    /// a struct display that is simply there.
    fn find_displays(&mut self, stmts: &[Stmt]) {
        for (at, ty) in self.typer.ctx.locals.iter().enumerate() {
            if let Some(row) = self.display_row(ty) {
                self.displays.insert(at as u16, row);
            }
        }
        for stmt in stmts {
            stmt.walk_exprs(&mut |expr| {
                if let Expr::Assign(target, value) = expr
                    && let Expr::Local(local) = target.as_ref()
                    && let Expr::New { ctor, .. } = value.as_ref()
                    && let Some(row) = self.display_row(&ctor.declaring)
                {
                    self.displays.insert(*local, row);
                }
            });
        }
    }

    /// Takes the stores that copy captured parameters and `this` into the
    /// display class as the mapping of those fields, and removes them.
    fn absorb_field_stores(&mut self, stmts: &mut Vec<Stmt>) {
        let mut index = 0;
        while index < stmts.len() {
            let mut absorbed = false;
            if let Stmt::Expr(Expr::Assign(target, value)) = &stmts[index]
                && let Expr::Field {
                    receiver: Some(receiver),
                    field,
                } = target.as_ref()
                && let Expr::Local(local) = receiver.as_ref()
                && let Some(row) = self.display_of_local(*local)
            {
                let key = (row, field.name.clone());
                let captured = match value.as_ref() {
                    Expr::This => Some(Expr::This),
                    Expr::Arg(at) => Some(Expr::Arg(*at)),
                    Expr::Local(other) if self.display_of_local(*other).is_some() => {
                        Some(Expr::Local(*other))
                    }
                    _ => None,
                };
                if let Some(captured) = captured
                    && !self.fields.contains_key(&key)
                {
                    self.fields.insert(key, captured);
                    absorbed = true;
                }
            }
            if absorbed {
                stmts.remove(index);
                self.changed = true;
            } else {
                for block in stmts[index].blocks_mut() {
                    self.absorb_field_stores(block);
                }
                index += 1;
            }
        }
    }

    /// Takes `V = <display>.field` and `V = this.field`, where `V` holds a
    /// display class, as aliases: reads of `V` become the field itself,
    /// which is what an enclosing method's mapping knows.
    fn absorb_aliases(&mut self, stmts: &mut Vec<Stmt>) {
        let mut index = 0;
        while index < stmts.len() {
            let mut absorbed = false;
            if let Stmt::Expr(Expr::Assign(target, value)) = &stmts[index]
                && let Expr::Local(local) = target.as_ref()
                && self.display_of_local(*local).is_some()
                && let Expr::Field {
                    receiver: Some(receiver),
                    ..
                } = value.as_ref()
                && (**receiver == Expr::This
                    || matches!(receiver.as_ref(), Expr::Local(other) if self.display_of_local(*other).is_some()))
                && !self.aliases.contains_key(local)
                && !self.is_written_elsewhere(*local, stmts, index)
            {
                self.aliases.insert(*local, (**value).clone());
                absorbed = true;
            }
            if absorbed {
                stmts.remove(index);
                self.changed = true;
            } else {
                for block in stmts[index].blocks_mut() {
                    self.absorb_aliases(block);
                }
                index += 1;
            }
        }
        if !self.aliases.is_empty() {
            let aliases = self.aliases.clone();
            for stmt in stmts.iter_mut() {
                stmt.map_exprs(&mut |expr| {
                    if let Expr::Local(local) = expr
                        && let Some(alias) = aliases.get(local)
                    {
                        *expr = alias.clone();
                    }
                });
            }
        }
    }

    /// Whether a local is assigned anywhere but the statement at `skip`.
    fn is_written_elsewhere(&self, local: u16, stmts: &[Stmt], skip: usize) -> bool {
        let mut written = false;
        for (at, stmt) in stmts.iter().enumerate() {
            if at == skip {
                continue;
            }
            stmt.walk_exprs(&mut |expr| {
                if let Expr::Assign(target, _) = expr
                    && **target == Expr::Local(local)
                {
                    written = true;
                }
            });
        }
        written
    }

    /// What a field of a display class is in the method: a captured
    /// parameter, `this`, another display, or a local made for it.
    fn field_expr(&mut self, row: u32, field: &crate::names::FieldRef) -> Expr {
        let key = (row, field.name.clone());
        if let Some(found) = self.fields.get(&key) {
            return found.clone();
        }
        let ty = crate::stack::substitute(&field.ty, &field.declaring, &[]);
        let local = self.typer.new_local(ty);
        let hint = field
            .name
            .trim_start_matches('<')
            .split('>')
            .next()
            .unwrap_or("")
            .to_string();
        if !hint.is_empty() && !hint.contains("__") {
            self.typer.hints.borrow_mut().insert(local, hint);
        }
        let expr = Expr::Local(local);
        self.fields.insert(key, expr.clone());
        expr
    }

    /// Rewrites field accesses and delegate constructions, everywhere.
    fn rewrite(&mut self, stmts: &mut [Stmt]) {
        for stmt in stmts.iter_mut() {
            stmt.map_exprs(&mut |expr| self.rewrite_expr(expr));
        }
    }

    fn rewrite_expr(&mut self, expr: &mut Expr) {
        // A field of a display instance is the variable it stands for.
        if let Expr::Field {
            receiver: Some(receiver),
            field,
        } = expr
        {
            let row = match receiver.as_ref() {
                Expr::Local(local) => self.display_of_local(*local),
                Expr::New { ctor, .. } => self.display_row(&ctor.declaring),
                _ => None,
            };
            if let Some(row) = row {
                let replacement = self.field_expr(row, field);
                *expr = replacement;
                self.changed = true;
                return;
            }
        }
        // `<>9__0 ?? (<>9__0 = lambda)` is the lambda: the cache is the
        // compiler's business.
        if let Expr::Binary(BinOp::Coalesce, left, right) = expr
            && let Expr::Field { field, .. } = left.as_ref()
            && let Expr::Assign(_, value) = right.as_ref()
        {
            // `<>O.<0>__M ?? (<>O.<0>__M = M)`: a method group cached in a
            // class of its own, which goes with it.
            let method_group_cache = field.name.starts_with('<')
                && field.name.contains(">__")
                && matches!(value.as_ref(), Expr::Delegate { .. })
                && self.cache_class_row(&field.declaring).is_some();
            if field.name.starts_with("<>9__") || method_group_cache {
                if method_group_cache && let Some(row) = self.cache_class_row(&field.declaring) {
                    self.options.consumed.borrow_mut().types.insert(row);
                }
                let value = (**value).clone();
                *expr = value;
                self.changed = true;
            }
        }
        // A local function made a delegate is named, the way the source
        // named it: `xs.ForEach(Print)`.
        if let Expr::Delegate { ty, target, method } = expr
            && let Some(name) = local_function_name(&method.name)
            && let Some(row) = self.own_method_row(method)
        {
            let receiver_local = match target.as_deref() {
                Some(Expr::Local(local)) if self.display_of_local(*local).is_some() => Some(*local),
                _ => None,
            };
            // A function of a display class reached otherwise than through
            // a local holding it is the enclosing method's to fold.
            let foreign = receiver_local.is_none() && self.display_row(&method.declaring).is_some();
            if !foreign && self.local_function(row, &name, receiver_local, &[], &[]) {
                let mut renamed = method.clone();
                renamed.name = name;
                renamed.declaring = match &self.typer.ctx.this_type {
                    TypeSig::ByRef(inner) => (**inner).clone(),
                    other => other.clone(),
                };
                renamed.param_names = Vec::new();
                let inherited = self.typer.ctx.generics.method_params.len();
                if renamed.type_args.len() >= inherited {
                    renamed.type_args.drain(..inherited);
                }
                *expr = Expr::Delegate {
                    ty: ty.clone(),
                    target: None,
                    method: renamed,
                };
                self.changed = true;
                return;
            }
        }
        if let Expr::Delegate { target, method, .. } = expr
            && is_lambda_method(&method.name)
            && let Some(row) = self.own_method_row(method)
        {
            let target = target.as_deref().cloned();
            let declaring = method.declaring.clone();
            if let Some(lambda) = self.lambda(row, target.as_ref(), &declaring) {
                *expr = lambda;
                self.changed = true;
            }
        }
        // A call to a lifted local function becomes a call by its own name,
        // and the function itself is declared at the end of the body.
        if let Expr::Call {
            method,
            receiver,
            args,
        } = expr
            && let Some(name) = local_function_name(&method.name)
            && let Some(row) = self.own_method_row(method)
        {
            // A display that comes in as a parameter, or as `this`, is the
            // enclosing method's: the call is folded there, once this body
            // is part of it, so that the function is declared beside this
            // one rather than inside it.
            let display_param = |at: usize| {
                method.sig.parameters.get(at).is_some_and(|ty| {
                    let ty = match ty {
                        TypeSig::ByRef(inner) => inner.as_ref(),
                        other => other,
                    };
                    self.display_row(ty).is_some()
                })
            };
            let foreign = args.iter().enumerate().any(|(at, arg)| {
                let inner = match arg {
                    Expr::Unary(crate::ir::UnOp::AddressOf, inner) => inner.as_ref(),
                    other => other,
                };
                display_param(at)
                    && !matches!(inner, Expr::Local(local) if self.display_of_local(*local).is_some())
            }) || (matches!(receiver.as_deref(), Some(Expr::This | Expr::Arg(_)))
                && self.display_row(&method.declaring).is_some());
            if foreign {
                return;
            }
            let receiver_local = match receiver.as_deref() {
                Some(Expr::Local(local)) if self.display_of_local(*local).is_some() => Some(*local),
                _ => None,
            };
            // Struct displays travel as `ref` arguments.
            let display_args: Vec<usize> = args
                .iter()
                .enumerate()
                .filter(|(_, arg)| {
                    let inner = match arg {
                        Expr::Unary(crate::ir::UnOp::AddressOf, inner) => inner.as_ref(),
                        other => other,
                    };
                    matches!(inner, Expr::Local(local) if self.display_of_local(*local).is_some())
                })
                .map(|(at, _)| at)
                .collect();
            if self.local_function(row, &name, receiver_local, args, &display_args) {
                let mut kept: Vec<Expr> = Vec::new();
                for (at, arg) in args.iter().enumerate() {
                    if !display_args.contains(&at) {
                        kept.push(arg.clone());
                    }
                }
                let mut renamed = method.clone();
                renamed.name = name;
                // The function's parameters may be renamed where it is
                // declared: arguments are not passed by name.
                renamed.param_names = Vec::new();
                // The enclosing method's type parameters are the function's
                // own, not arguments it is given.
                let inherited = self.typer.ctx.generics.method_params.len();
                if renamed.type_args.len() >= inherited {
                    renamed.type_args.drain(..inherited);
                }
                // A struct's `this` is a reference to it.
                renamed.declaring = match &self.typer.ctx.this_type {
                    TypeSig::ByRef(inner) => (**inner).clone(),
                    other => other.clone(),
                };
                if !renamed.out_params.is_empty() {
                    let mut outs = Vec::new();
                    let mut names = Vec::new();
                    for (at, flag) in renamed.out_params.iter().enumerate() {
                        if !display_args.contains(&at) {
                            outs.push(*flag);
                            names.push(renamed.param_names.get(at).cloned().unwrap_or_default());
                        }
                    }
                    renamed.out_params = outs;
                    renamed.param_names = names;
                }
                let mut params = Vec::new();
                for (at, param) in renamed.sig.parameters.iter().enumerate() {
                    if !display_args.contains(&at) {
                        params.push(param.clone());
                    }
                }
                renamed.sig.parameters = params;
                *expr = Expr::Call {
                    method: renamed,
                    receiver: None,
                    args: kept,
                };
                self.changed = true;
            }
        }
    }

    /// Declares a lifted local function once, transplanting its body the
    /// way a lambda's is; says whether the call can be rewritten.
    fn local_function(
        &mut self,
        method_row: u32,
        name: &str,
        receiver_local: Option<u16>,
        args: &[Expr],
        display_args: &[usize],
    ) -> bool {
        if self
            .local_functions
            .iter()
            .any(|(row, _)| *row == method_row)
        {
            return true;
        }
        // A local function calling itself: the call is by name, and the
        // declaration is being made by whoever is folding it.
        if self
            .options
            .consumed
            .borrow()
            .in_progress
            .contains(&method_row)
        {
            return true;
        }
        if !self.options.consumed.borrow_mut().spend() {
            return false;
        }
        let mut inner_options = self.options.clone();
        inner_options.depth += 1;
        self.options
            .consumed
            .borrow_mut()
            .in_progress
            .insert(method_row);
        let mut inner = decompile_body(self.resolver, method_row, &inner_options);
        // An iterator or async local function is shown as it was written.
        if let Some(found) = &inner
            && let Some(machine) = crate::machines::machine_of(self.resolver, found)
            && let Some(unfolded) =
                crate::machines::machine_body(self.resolver, machine, method_row, &inner_options)
        {
            inner = Some(unfolded);
        }
        self.options
            .consumed
            .borrow_mut()
            .in_progress
            .remove(&method_row);
        let Some(inner) = inner else {
            return false;
        };
        // Its place among the declarations is taken now, before the ones
        // its body calls.
        let slot = self.local_functions.len();
        self.local_functions.push((method_row, Stmt::Break));
        let owner = self.resolver.method_owner(method_row).unwrap_or(0);
        let this_display = self.display_row(&self.resolver.declared_type_sig(owner));
        let mut stmts = inner.stmts;
        let mut locals: HashMap<u16, u16> = HashMap::new();
        for (at, ty) in inner.ctx.locals.iter().enumerate() {
            let local = self.typer.new_local(ty.clone());
            if let Some(hint) = inner.local_hints.get(&(at as u16)) {
                self.typer.hints.borrow_mut().insert(local, hint.clone());
            }
            locals.insert(at as u16, local);
        }
        // Parameters, the display ones mapped to the display local instead.
        let mut params: Vec<u16> = Vec::new();
        let mut outs: Vec<bool> = Vec::new();
        let declared_outs = self
            .resolver
            .method_ref(Token::new(table::METHOD_DEF, method_row))
            .map(|method| method.out_params)
            .unwrap_or_default();
        let mut arg_map: HashMap<u16, Expr> = HashMap::new();
        for (at, ty) in inner.ctx.params.iter().enumerate() {
            if display_args.contains(&at) {
                let display_ty = match ty {
                    TypeSig::ByRef(inner) => inner.as_ref(),
                    other => other,
                };
                if let Some(row) = self.display_row(display_ty) {
                    self.options.consumed.borrow_mut().types.insert(row);
                }
                let inner_arg = match &args[at] {
                    Expr::Unary(crate::ir::UnOp::AddressOf, inner) => (**inner).clone(),
                    other => other.clone(),
                };
                arg_map.insert(at as u16, inner_arg);
                continue;
            }
            let local = self.typer.new_local(ty.clone());
            if let Some(param_name) = inner.param_names.get(at)
                && !param_name.starts_with("P_")
            {
                self.typer
                    .hints
                    .borrow_mut()
                    .insert(local, param_name.clone());
            }
            arg_map.insert(at as u16, Expr::Local(local));
            params.push(local);
            outs.push(declared_outs.get(at).copied().unwrap_or(false));
        }
        let mut slots: HashMap<u32, u16> = HashMap::new();
        for (id, ty) in &inner.slot_types {
            slots.insert(*id, self.typer.new_local(ty.clone()));
        }
        for stmt in &mut stmts {
            stmt.map_exprs(&mut |expr| match expr {
                Expr::Local(at) => {
                    if let Some(mapped) = locals.get(at) {
                        *expr = Expr::Local(*mapped);
                    }
                }
                Expr::Arg(at) => {
                    if let Some(mapped) = arg_map.get(at) {
                        *expr = mapped.clone();
                    }
                }
                Expr::Slot(id) => {
                    if let Some(mapped) = slots.get(id) {
                        *expr = Expr::Local(*mapped);
                    }
                }
                Expr::Field {
                    receiver: Some(receiver),
                    field,
                } if **receiver == Expr::This && this_display.is_some() => {
                    *expr = self.field_expr(this_display.unwrap_or(0), field);
                }
                Expr::This if this_display.is_some() => {
                    if let Some(local) = receiver_local {
                        *expr = Expr::Local(local);
                    }
                }
                _ => {}
            });
        }
        crate::ir::renumber_binders(&mut stmts, &mut |local| {
            locals.get(&local).copied().unwrap_or(local)
        });
        self.rewrite(&mut stmts);
        let returns = inner.ctx.returns.clone();
        self.options
            .consumed
            .borrow_mut()
            .methods
            .insert(method_row);
        if let Some(row) = this_display {
            self.options.consumed.borrow_mut().types.insert(row);
        }
        self.local_functions[slot] = (
            method_row,
            Stmt::LocalFunction {
                name: name.to_string(),
                type_params: inner
                    .ctx
                    .generics
                    .method_params
                    .get(self.typer.ctx.generics.method_params.len()..)
                    .unwrap_or(&[])
                    .to_vec(),
                params,
                outs,
                returns,
                constraints: crate::members::constraint_clauses(
                    self.resolver,
                    true,
                    method_row,
                    &inner.ctx.generics,
                    self.typer.ctx.generics.method_params.len(),
                ),
                body: stmts,
            },
        );
        true
    }

    /// A delegate over a lifted method as the lambda it was.
    fn lambda(
        &mut self,
        method_row: u32,
        target: Option<&Expr>,
        declaring: &TypeSig,
    ) -> Option<Expr> {
        // The class the lambda was lifted into is generic in the enclosing
        // method's type parameters: its own stand for them.
        let class_args: Vec<TypeSig> = match declaring {
            TypeSig::Generic { arguments, .. } => arguments.clone(),
            _ => Vec::new(),
        };
        let in_method = |ty: &TypeSig| crate::stack::substitute_with(ty, &class_args, &[]);
        // The display instance the lambda's `this` is, when it has one.
        let mut display: Option<(u32, HashMap<String, Expr>)> = None;
        match target {
            Some(Expr::Local(local)) => {
                let row = self.display_of_local(*local)?;
                display = Some((row, HashMap::new()));
            }
            Some(Expr::New {
                ctor, initializer, ..
            }) => {
                let row = self.display_row(&ctor.declaring)?;
                let mut direct = HashMap::new();
                for (name, value) in initializer {
                    direct.insert(name.clone(), value.clone());
                }
                display = Some((row, direct));
            }
            Some(Expr::This) | None => {}
            Some(Expr::Field { field, .. }) if field.name == "<>9" => {}
            Some(_) => return None,
        }
        let owner = self.resolver.method_owner(method_row)?;
        // `<>c`, or `<>c__N` for the lambdas of a generic method.
        let owner_name = self.resolver.type_def_simple_name(owner);
        let owner_is_singleton = owner_name == "<>c"
            || (owner_name.starts_with("<>c__") && !owner_name.contains("DisplayClass"));
        if display.is_none()
            && !owner_is_singleton
            && self
                .display_row(&self.resolver.declared_type_sig(owner))
                .is_some()
        {
            // A method of a display class reached some other way: leave it.
            return None;
        }
        if self
            .options
            .consumed
            .borrow()
            .in_progress
            .contains(&method_row)
        {
            return None;
        }
        if !self.options.consumed.borrow_mut().spend() {
            return None;
        }
        let mut inner_options = self.options.clone();
        inner_options.depth += 1;
        self.options
            .consumed
            .borrow_mut()
            .in_progress
            .insert(method_row);
        let mut inner = decompile_body(self.resolver, method_row, &inner_options);
        // An async or iterator lambda is shown as it was written.
        if let Some(found) = &inner
            && let Some(machine) = crate::machines::machine_of(self.resolver, found)
            && let Some(unfolded) =
                crate::machines::machine_body(self.resolver, machine, method_row, &inner_options)
        {
            inner = Some(unfolded);
        }
        self.options
            .consumed
            .borrow_mut()
            .in_progress
            .remove(&method_row);
        let inner = inner?;
        let mut stmts = inner.stmts;

        // The lifted method's variables become the enclosing method's.
        let mut locals: HashMap<u16, u16> = HashMap::new();
        for (at, ty) in inner.ctx.locals.iter().enumerate() {
            let local = self.typer.new_local(in_method(ty));
            if let Some(hint) = inner.local_hints.get(&(at as u16)) {
                self.typer.hints.borrow_mut().insert(local, hint.clone());
            }
            locals.insert(at as u16, local);
        }
        let mut params: Vec<u16> = Vec::with_capacity(inner.ctx.params.len());
        for (at, ty) in inner.ctx.params.iter().enumerate() {
            let local = self.typer.new_local(in_method(ty));
            if let Some(name) = inner.param_names.get(at)
                && !name.starts_with("P_")
            {
                self.typer.hints.borrow_mut().insert(local, name.clone());
            }
            params.push(local);
        }
        let mut slots: HashMap<u32, u16> = HashMap::new();
        for (id, ty) in &inner.slot_types {
            slots.insert(*id, self.typer.new_local(in_method(ty)));
        }
        let this_display = display.as_ref().map(|(row, _)| *row);
        let direct: HashMap<String, Expr> = display
            .as_ref()
            .map(|(_, direct)| direct.clone())
            .unwrap_or_default();
        let display_local = match target {
            Some(Expr::Local(local)) => Some(*local),
            _ => None,
        };
        for stmt in &mut stmts {
            stmt.map_exprs(&mut |expr| match expr {
                Expr::Local(at) => {
                    if let Some(mapped) = locals.get(at) {
                        *expr = Expr::Local(*mapped);
                    }
                }
                Expr::Arg(at) => {
                    if let Some(mapped) = params.get(*at as usize) {
                        *expr = Expr::Local(*mapped);
                    }
                }
                Expr::Slot(id) => {
                    if let Some(mapped) = slots.get(id) {
                        *expr = Expr::Local(*mapped);
                    }
                }
                Expr::Field {
                    receiver: Some(receiver),
                    field,
                } if **receiver == Expr::This && this_display.is_some() => {
                    let row = this_display.unwrap_or(0);
                    if let Some(value) = direct.get(&field.name) {
                        *expr = value.clone();
                    } else {
                        *expr = self.field_expr(row, field);
                    }
                }
                Expr::This if this_display.is_some() => {
                    // The display instance itself, handed to a nested
                    // closure: the local that held it, for the field
                    // mapping to see through.
                    if let Some(local) = display_local {
                        *expr = Expr::Local(local);
                    }
                }
                _ => {}
            });
        }
        crate::ir::renumber_binders(&mut stmts, &mut |local| {
            locals.get(&local).copied().unwrap_or(local)
        });
        if !class_args.is_empty() {
            crate::ir::map_types(&mut stmts, &in_method);
        }
        // The transplanted body is itself subject to this pass.
        self.rewrite(&mut stmts);

        let mut consumed = self.options.consumed.borrow_mut();
        consumed.methods.insert(method_row);
        if let Some(row) = this_display {
            consumed.types.insert(row);
        }
        if self
            .display_row(&self.resolver.declared_type_sig(owner))
            .is_some()
        {
            consumed.types.insert(owner);
        }
        drop(consumed);

        let body = match stmts.as_slice() {
            [Stmt::Return(Some(value))] => Body::Expr(Box::new(value.clone())),
            [Stmt::Return(None)] => Body::Block(Vec::new()),
            _ => Body::Block(stmts),
        };
        let id = self.next_lambda;
        self.next_lambda += 1;
        let outs = self
            .resolver
            .method_ref(Token::new(table::METHOD_DEF, method_row))
            .map(|method| method.out_params)
            .unwrap_or_default();
        Some(Expr::Lambda {
            id,
            params,
            outs,
            body: Box::new(body),
        })
    }
}

/// Removes `d = new DisplayClass()` where nothing reads `d` any more.
fn remove_display_constructions(stmts: &mut Vec<Stmt>, displays: &HashMap<u16, u32>) {
    // `d = null` is a debug state machine letting go of it: no source
    // names a display class.
    fn drop_clears(stmts: &mut Vec<Stmt>, displays: &HashMap<u16, u32>) {
        stmts.retain(|stmt| {
            !matches!(stmt, Stmt::Expr(Expr::Assign(target, value))
                if matches!(target.as_ref(), Expr::Local(local) if displays.contains_key(local))
                    && matches!(value.as_ref(), Expr::Null))
        });
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                drop_clears(block, displays);
            }
        }
    }
    drop_clears(stmts, displays);
    let mut reads: HashMap<u16, usize> = HashMap::new();
    fn count(stmts: &[Stmt], reads: &mut HashMap<u16, usize>) {
        for stmt in stmts {
            stmt.walk_exprs(&mut |expr| {
                if let Expr::Local(local) = expr {
                    *reads.entry(*local).or_default() += 1;
                }
            });
        }
    }
    count(stmts, &mut reads);
    fn prune(stmts: &mut Vec<Stmt>, displays: &HashMap<u16, u32>, reads: &HashMap<u16, usize>) {
        stmts.retain(|stmt| {
            if let Stmt::Expr(Expr::Assign(target, value)) = stmt
                && let Expr::Local(local) = target.as_ref()
                && displays.contains_key(local)
                && (matches!(value.as_ref(), Expr::New { .. } | Expr::Default(_)) || value.is_pure())
                // The construction itself is the one read left.
                && reads.get(local).copied().unwrap_or(0) <= 1
            {
                return false;
            }
            true
        });
        for stmt in stmts.iter_mut() {
            for block in stmt.blocks_mut() {
                prune(block, displays, reads);
            }
        }
    }
    prune(stmts, displays, &reads);
}

/// The `TypeDef` row of a display class or lambda-cache class a type names.
/// A display instance the compiler kept on the stack is a local all the
/// same: the pass follows locals.
fn promote_display_slots(typer: &Typer<'_, '_>, stmts: &mut [Stmt]) {
    let mut found: Vec<(u32, TypeSig)> = Vec::new();
    for stmt in stmts.iter() {
        stmt.walk_exprs(&mut |expr| {
            if let Expr::Assign(target, value) = expr
                && let Expr::Slot(id) = target.as_ref()
                && let Expr::New { ctor, .. } = value.as_ref()
                && display_row(typer.ctx.resolver, &ctor.declaring).is_some()
                && !found.iter().any(|(known, _)| known == id)
            {
                found.push((*id, ctor.declaring.clone()));
            }
        });
    }
    if found.is_empty() {
        return;
    }
    let locals: HashMap<u32, u16> = found
        .into_iter()
        .map(|(id, ty)| (id, typer.new_local(ty)))
        .collect();
    for stmt in stmts.iter_mut() {
        stmt.map_exprs(&mut |expr| {
            if let Expr::Slot(id) = expr
                && let Some(local) = locals.get(id)
            {
                *expr = Expr::Local(*local);
            }
        });
    }
}

#[must_use]
pub fn display_row(resolver: Resolver<'_>, ty: &TypeSig) -> Option<u32> {
    let token = match ty {
        TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
        TypeSig::Generic { definition, .. } => match definition.as_ref() {
            TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
            _ => return None,
        },
        _ => return None,
    };
    if token.table() != table::TYPE_DEF {
        return None;
    }
    let name = resolver.type_def_simple_name(token.row());
    let generated = name.starts_with("<>")
        || resolver.has_attribute(
            Token::new(table::TYPE_DEF, token.row()),
            "System.Runtime.CompilerServices.CompilerGeneratedAttribute",
        );
    (generated && (name.contains("DisplayClass") || name == "<>c" || name.starts_with("<>c__")))
        .then_some(token.row())
}

/// The name a lifted local function had: `Helper` out of
/// `<Outer>g__Helper|0_0`.
#[must_use]
pub fn local_function_name(mangled: &str) -> Option<String> {
    let rest = mangled.strip_prefix('<')?;
    let (_, after) = rest.split_once(">g__")?;
    let name = after.split('|').next()?;
    (!name.is_empty()).then(|| name.to_string())
}

/// Whether a method name is one the compiler gives a lambda's body.
#[must_use]
pub fn is_lambda_method(name: &str) -> bool {
    name.starts_with('<') && name.contains(">b__")
}
