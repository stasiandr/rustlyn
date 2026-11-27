//! Scopes and locals: declaring and finding names in a body, and noting what
//! the closures being bound capture.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_text::TextSpan;

use super::{BodyBinder, DetachedScopes};
use crate::bound::{BoundStatement, BoundStatementKind, BoundSymbol, LocalId, LocalSymbol};
use crate::symbol::SymbolId;
use crate::types::Type;

impl BodyBinder<'_> {
    pub(super) fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.siblings.push(false);
    }

    /// A scope beside the ones already open rather than inside them.
    ///
    /// The sections of a `switch` are one declaration space for the locals
    /// their statements declare — a `case` writes `string unquoted;` and a
    /// later one assigns to it — and separate ones for the variables their
    /// labels declare, so two sections may both write `case Foo f:`. Leaving
    /// the earlier sections in scope answers the first; not counting them when
    /// deciding what is a redeclaration answers the second.
    pub(super) fn push_sibling_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.siblings.push(true);
    }

    pub(super) fn pop_scope(&mut self) {
        self.scopes.pop();
        self.siblings.pop();
    }

    /// Takes every open scope away, leaving one holding only the constants,
    /// and hands back what was there for `restore_scopes`.
    ///
    /// A `static` lambda or local function cannot reach the locals around it,
    /// so they are not in scope inside it at all — except the `const` ones,
    /// which are values and not slots, and so are not captured by being
    /// named. The two stacks move together: a depth is only meaningful
    /// against both of them, and a `switch` inside such a function asks
    /// whether the scope a name was found in is a sibling one.
    pub(super) fn detach_scopes(&mut self) -> DetachedScopes {
        let mut constants = HashMap::new();
        for scope in &self.scopes {
            for (name, local) in scope {
                if self.constant_locals.contains_key(local) {
                    constants.insert(name.clone(), *local);
                }
            }
        }
        (
            std::mem::replace(&mut self.scopes, vec![constants]),
            std::mem::replace(&mut self.siblings, vec![false]),
            std::mem::replace(&mut self.capture_floor, self.lambdas.len()),
        )
    }

    /// Remembers the values of the locals a `const` declaration made.
    pub(super) fn note_constant_locals(&mut self, declared: &[BoundStatement]) {
        for statement in declared {
            match &statement.kind {
                BoundStatementKind::LocalDeclaration {
                    local,
                    initializer: Some(value),
                } => {
                    if let Some(constant) = self.binder.folded(value) {
                        self.constant_locals.insert(*local, constant);
                    }
                    // `const int n = text.Length;` is no constant: said where
                    // nothing else is wrong with the value.
                    if !value.ty.is_error()
                        && !crate::checks::has_error_part(value)
                        && !self.body.diagnostics.iter().any(|(tree, diagnostic)| {
                            *tree == self.tree
                                && diagnostic.is_error()
                                && value.span.start() <= diagnostic.span().start()
                                && diagnostic.span().end() <= value.span.end()
                        })
                        && crate::constant::certainly_not_constant(self.binder, value)
                    {
                        let name = self.body.locals[local.0 as usize].name.clone();
                        self.report(ErrorCode::ErrNotConstantExpression, value.span, &[&name]);
                    }
                }
                BoundStatementKind::Block(inner) => self.note_constant_locals(inner),
                _ => {}
            }
        }
    }

    pub(super) fn restore_scopes(&mut self, saved: DetachedScopes) {
        self.scopes = saved.0;
        self.siblings = saved.1;
        self.capture_floor = saved.2;
    }

    pub(super) fn declare_local(&mut self, name: &str, ty: Type, span: TextSpan) -> LocalId {
        // `_` is a discard: it can be written as often as you like, because
        // none of them can be read back. A lambda or a local function is a
        // method of its own (C# 8): a name it declares may be one the method
        // around it also uses, and then the inner one simply hides the outer
        // for as long as the body lasts. Roslyn writes `var result = ...` in
        // a local function of a method that has a `result` too.
        let floor = self.lambdas.last().map_or(0, |frame| frame.floor);
        if name != "_"
            && let Some((depth, existing)) = self.lookup_local_at(name)
            && depth >= floor
            && !self.siblings.get(depth).copied().unwrap_or(false)
        {
            // The same declaration bound again — a conditional with no
            // natural type is bound once on its own and once for what it
            // is given to, condition and all — is the local it made the
            // first time, not a second one with its name.
            if self.body.locals[existing.0 as usize].span == span {
                return existing;
            }
            // In the same scope it is declared twice; in one around it, the
            // inner one would hide it, which C# does not allow either.
            if depth + 1 == self.scopes.len() {
                self.report(ErrorCode::ErrLocalDuplicate, span, &[name]);
            } else {
                self.report(ErrorCode::ErrLocalIllegallyOverrides, span, &[name]);
            }
        } else if name != "_"
            && self.lambdas.is_empty()
            && self
                .member
                .and_then(|member| self.lookup_parameter(member, name))
                .is_some_and(|parameter| {
                    // A primary constructor's parameter is the type's, and a
                    // local of a method may hide it.
                    self.binder.compilation().symbols().get(parameter).container == self.member
                })
        {
            self.report(ErrorCode::ErrLocalIllegallyOverrides, span, &[name]);
        }
        let id = LocalId(self.body.locals.len() as u32);
        self.body.locals.push(LocalSymbol {
            name: name.to_string(),
            ty,
            span,
            by_ref: false,
            readonly_ref: false,
            readonly: false,
        });
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), id);
        }
        self.refer_to_local(span, id);
        id
    }

    /// Records that the name at `span` is `local`, as a speculation can
    /// take back (see `unwind_speculation`).
    pub(super) fn refer_to_local(&mut self, span: TextSpan, local: LocalId) {
        let before = self.body.references.insert(span, BoundSymbol::Local(local));
        self.local_references.push((span, before));
    }

    /// Declares a local the language needs and the source never wrote.
    ///
    /// It gets a name no C# identifier can collide with and a number, because
    /// two `foreach` loops in one block each need one and neither wrote it:
    /// a shared name would make the second a redeclaration of the first.
    pub(super) fn declare_synthetic_local(&mut self, stem: &str, ty: Type) -> LocalId {
        let id = LocalId(self.body.locals.len() as u32);
        self.body.locals.push(LocalSymbol {
            name: format!("<{stem}>{}", id.0),
            ty,
            span: self.synthetic_span,
            by_ref: false,
            readonly_ref: false,
            readonly: false,
        });
        id
    }

    pub(super) fn lookup_local(&self, name: &str) -> Option<LocalId> {
        self.lookup_local_at(name).map(|(_, local)| local)
    }

    /// The local a name refers to, and how deep the scope holding it is.
    pub(super) fn lookup_local_at(&self, name: &str) -> Option<(usize, LocalId)> {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(depth, scope)| scope.get(name).map(|local| (depth, *local)))
    }

    /// The same, noting a capture when the local belongs to something outside
    /// the lambda being bound.
    pub(super) fn resolve_local(&mut self, name: &str) -> Option<LocalId> {
        let (depth, local) = self.lookup_local_at(name)?;
        let floor = self.capture_floor.min(self.lambdas.len());
        for frame in &mut self.lambdas[floor..] {
            if depth < frame.floor && !frame.captured.contains(&local) {
                frame.captured.push(local);
            }
        }
        Some(local)
    }

    /// Notes that the lambdas being bound read a parameter of the member they
    /// sit in, which is captured like any local.
    pub(super) fn note_parameter_capture(&mut self, parameter: SymbolId) {
        let owner = self.binder.compilation().symbols().get(parameter).container;
        let floor = self.capture_floor.min(self.lambdas.len());
        // From the innermost frame outwards: the closures inside the one
        // that declares the parameter capture it; that one and everything
        // around it merely hold it.
        for frame in self.lambdas[floor..].iter_mut().rev() {
            if frame.declares.is_some() && frame.declares == owner {
                break;
            }
            if !frame.captured_parameters.contains(&parameter) {
                frame.captured_parameters.push(parameter);
            }
        }
    }

    /// Notes that the lambdas being bound read `this`.
    ///
    /// A static member has no `this` for one to read: saying otherwise makes
    /// the lambda's method an instance method of a type nothing hands it an
    /// instance of, and the delegate is built over the first argument
    /// instead.
    pub(super) fn note_this_capture(&mut self) {
        if self.member.is_some_and(|member| self.is_static(member)) {
            return;
        }
        let floor = self.capture_floor.min(self.lambdas.len());
        for frame in &mut self.lambdas[floor..] {
            frame.captures_this = true;
        }
    }

    /// Notes that the closures being bound call a local function: what it
    /// captures, they capture, once its body has said what that is.
    pub(super) fn note_local_function_call(&mut self, function: SymbolId) {
        let floor = self.capture_floor.min(self.lambdas.len());
        for frame in &mut self.lambdas[floor..] {
            if !frame.calls.contains(&function) {
                frame.calls.push(function);
            }
        }
    }

    /// Gives every closure the captures of the local functions it calls
    /// (§12.19.2 in effect): `scope => MakeFrame(scope)` reads whatever
    /// `MakeFrame` reads of the method around them, and has to live with
    /// it. A local function declared inside the closure is left out — what
    /// it captures of the closure's own variables is the closure's business
    /// already — and the rest is repeated until nothing changes, since a
    /// local function may call another.
    pub(super) fn propagate_local_function_captures(&mut self) {
        let functions: Vec<(SymbolId, TextSpan)> = self
            .body
            .local_functions
            .iter()
            .map(|function| (function.symbol, function.body.span))
            .collect();
        loop {
            let mut changed = false;
            let snapshot: Vec<(Vec<LocalId>, Vec<SymbolId>, bool)> = self
                .body
                .local_functions
                .iter()
                .map(|function| {
                    (
                        function.captured.clone(),
                        function.captured_parameters.clone(),
                        function.captures_this,
                    )
                })
                .collect();
            let merge = |captured: &mut Vec<LocalId>,
                         parameters: &mut Vec<SymbolId>,
                         this: &mut bool,
                         from: &(Vec<LocalId>, Vec<SymbolId>, bool)|
             -> bool {
                let mut changed = false;
                for local in &from.0 {
                    if !captured.contains(local) {
                        captured.push(*local);
                        changed = true;
                    }
                }
                for parameter in &from.1 {
                    if !parameters.contains(parameter) {
                        parameters.push(*parameter);
                        changed = true;
                    }
                }
                if from.2 && !*this {
                    *this = true;
                    changed = true;
                }
                changed
            };
            let nested = |outer: TextSpan, inner: TextSpan| {
                inner.start() >= outer.start() && inner.end() <= outer.end()
            };
            for lambda in &mut self.body.lambdas {
                for call in lambda.calls.clone() {
                    let Some(at) = functions.iter().position(|(symbol, _)| *symbol == call) else {
                        continue;
                    };
                    if nested(lambda.span, functions[at].1) {
                        continue;
                    }
                    changed |= merge(
                        &mut lambda.captured,
                        &mut lambda.captured_parameters,
                        &mut lambda.captures_this,
                        &snapshot[at],
                    );
                }
            }
            for index in 0..self.body.local_functions.len() {
                let own = self.body.local_functions[index].body.span;
                for call in self.body.local_functions[index].calls.clone() {
                    let Some(at) = functions.iter().position(|(symbol, _)| *symbol == call) else {
                        continue;
                    };
                    if at == index || nested(own, functions[at].1) {
                        continue;
                    }
                    let from = snapshot[at].clone();
                    let function = &mut self.body.local_functions[index];
                    changed |= merge(
                        &mut function.captured,
                        &mut function.captured_parameters,
                        &mut function.captures_this,
                        &from,
                    );
                }
            }
            if !changed {
                break;
            }
        }
    }

    pub(super) fn local_type(&self, local: LocalId) -> Type {
        self.body.locals[local.0 as usize].ty.clone()
    }
}
