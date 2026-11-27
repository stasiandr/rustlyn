//! Definite assignment (§9.4.4): a local read before anything is sure to
//! have been written to it is CS0165.
//!
//! This is a forward walk over the bound tree carrying the set of locals
//! definitely assigned at each point, the way Roslyn's `DefiniteAssignment`
//! pass does, with the same shapes for branching: a condition splits the
//! state into what holds when it is true and what holds when it is false, a
//! jump makes the state "unreachable" (in which everything counts as
//! assigned), and where paths meet the states are intersected. Loops need no
//! second pass: along any path a local only becomes more assigned, so the
//! state that comes back around a loop is never less assigned than the one
//! that entered it.
//!
//! A `goto` is the one jump that does not fit that: it may go back to a
//! label already walked, carrying a state the walk had not seen when it was
//! there. So a label keeps the state every `goto` to it arrives with, and a
//! body with a `goto` is walked again until those states stop changing —
//! they only ever lose locals, so they do — and only the last walk's
//! findings count.
//!
//! A `break`, a `continue`, a `return` or a `goto` that leaves a `try` with
//! a `finally` runs the `finally` on its way, so it arrives at its target
//! with what it had when it jumped plus whatever the `finally` is sure to
//! assign: the same combination as at the normal end of the `try`, made
//! once for each `finally` it passes through, nested ones included. A jump
//! that stays inside the `try` passes through nothing. For an `out`
//! parameter this means a `return` counts what the `finally` assigned.
//!
//! Like the rest of the flow analysis it would rather say nothing than
//! something wrong. A body with a construct the binder does not model or an
//! expression that did not bind gets no CS0165 at all, and a
//! local is only watched where its type leaves no doubt about what assigning
//! it means: a struct is assigned field by field as well as whole, so one
//! whose fields the body touches is left alone, as is one from another
//! assembly, whose private fields Roslyn counts by rules of its own.

use std::collections::HashMap;

use rustlyn_diagnostics::{Diagnostic, ErrorCode};

use crate::binder::{Binder, Diagnostics};
use crate::bound::{
    BoundBody, BoundExpression, BoundExpressionKind, BoundPattern, BoundPatternKind,
    BoundStatement, BoundStatementKind, BoundSwitchLabel, ConstantValue, ConversionKind, LocalId,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, RefKind, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

/// Checks a bound body and adds a CS0165 for every read of a local that may
/// not have been assigned.
pub(crate) fn check(
    binder: &Binder<'_>,
    tree: usize,
    member: Option<SymbolId>,
    body: &BoundBody,
) -> Diagnostics {
    let mut tracked: Vec<bool> = body
        .locals
        .iter()
        .map(|local| !local.by_ref && trackable(binder, &local.ty))
        .collect();
    let mut shape = Shape {
        by_ref: body.locals.iter().map(|local| local.by_ref).collect(),
        ..Shape::default()
    };
    for statement in &body.statements {
        shape.statement(statement);
    }
    for function in &body.local_functions {
        shape.in_local_function = true;
        shape.statement(&function.body);
    }
    shape.in_local_function = false;
    for lambda in &body.lambdas {
        shape.statement(&lambda.body);
    }
    // A `goto` is followed by the name of its label, so the name has to
    // say which label: one declared once in everything walked here — a
    // lambda may repeat a name of the method around it — and declared at
    // all, which a `goto` to nowhere (an error of its own) is not.
    let mut labels = shape.labels.clone();
    labels.sort_unstable();
    let repeated = labels.windows(2).any(|pair| pair[0] == pair[1]);
    if !shape.gotos.is_empty()
        && (repeated
            || shape
                .gotos
                .iter()
                .any(|label| labels.binary_search(label).is_err()))
    {
        shape.unsure = true;
    }
    if shape.unsure {
        return Diagnostics::new();
    }
    for id in shape.untracked {
        if let Some(slot) = tracked.get_mut(id.0 as usize) {
            *slot = false;
        }
    }

    // The `out` parameters of the member and of its local functions get a
    // slot each after the locals: each has to be assigned before its method
    // returns, and read only once it has been.
    let symbols = binder.compilation().symbols();
    // A struct assigned field by field, or one of a type whose assignment
    // is not one write, is left alone, as a local of it is.
    let outs_of = |method: SymbolId| -> Vec<SymbolId> {
        symbols
            .get(method)
            .as_method()
            .map(|detail| {
                detail
                    .parameters
                    .iter()
                    .copied()
                    .filter(|parameter| {
                        symbols
                            .get(*parameter)
                            .as_parameter()
                            .is_some_and(|detail| detail.ref_kind == RefKind::Out)
                            && !shape.untracked_parameters.contains(parameter)
                            && trackable(
                                binder,
                                &binder.type_of(*parameter, &mut Diagnostics::new()),
                            )
                    })
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut outs: Vec<SymbolId> = member.map(outs_of).unwrap_or_default();
    for function in &body.local_functions {
        outs.extend(outs_of(function.symbol));
    }
    let slots = body.locals.len() + outs.len();
    let mut walk = Walk {
        binder,
        body,
        tracked,
        outs,
        checking: Vec::new(),
        lambdas: 0,
        state: State::assigned(slots),
        targets: Vec::new(),
        found: Vec::new(),
        unsure: false,
        needs: HashMap::new(),
        arriving: HashMap::new(),
        arriving_changed: false,
        follows_gotos: !shape.gotos.is_empty(),
        guards: Vec::new(),
        label_tries: shape.label_tries.clone(),
    };
    // A `goto` may jump over a declaration: `goto L; int x = 1; L: Use(x);`
    // reads an `x` nothing assigned. A local counts as assigned until its
    // declaration is walked — which is where it stops being — so in a body
    // with a `goto` the locals it declares start out unassigned instead,
    // and the jump carries that to the label. Without a `goto` every read
    // comes after the declaration, and nothing is different.
    let has_gotos = !shape.gotos.is_empty();
    let declared_in = |statements: &[BoundStatement]| -> Vec<LocalId> {
        let mut declared = Vec::new();
        if has_gotos {
            for statement in statements {
                each_nested_statement(statement, &mut |inner| {
                    if let BoundStatementKind::LocalDeclaration { local, .. } = &inner.kind {
                        declared.push(*local);
                    }
                });
            }
        }
        declared
    };
    // What each local function reads of the method around it before it
    // assigns it, walked with those locals unassigned. A local function
    // calling another reads what that one reads, so this goes round until
    // nothing more is learned.
    for _ in 0..=body.local_functions.len() {
        let mut changed = false;
        for function in &body.local_functions {
            let saved = std::mem::take(&mut walk.found);
            let declared = declared_in(std::slice::from_ref(&function.body));
            walk.settled(|walk| {
                walk.state = State::assigned(slots);
                walk.targets.clear();
                walk.guards.clear();
                walk.checking = Vec::new();
                for local in function.captured.iter().chain(&declared) {
                    walk.state.unassign(*local);
                }
                walk.statement(&function.body);
            });
            let found = std::mem::replace(&mut walk.found, saved);
            let mut reads: Vec<LocalId> = found
                .into_iter()
                .filter_map(|finding| match finding {
                    Finding::Local(local, _) if function.captured.contains(&local) => Some(local),
                    _ => None,
                })
                .collect();
            reads.sort_by_key(|local| local.0);
            reads.dedup();
            if walk.needs.get(&function.symbol) != Some(&reads) {
                walk.needs.insert(function.symbol, reads);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let walk_body =
        |walk: &mut Walk<'_, '_>, owner: Option<SymbolId>, statements: &[BoundStatement]| {
            let declared = declared_in(statements);
            walk.settled(|walk| {
                walk.state = State::assigned(slots);
                for local in &declared {
                    walk.state.unassign(*local);
                }
                walk.targets.clear();
                walk.guards.clear();
                walk.checking = owner.map(outs_of).unwrap_or_default();
                for parameter in walk.checking.clone() {
                    if let Some(slot) = walk.out_slot(parameter) {
                        walk.state.unassign(slot);
                    }
                }
                for statement in statements {
                    walk.statement(statement);
                }
                // Running off the end leaves as much as a `return` does.
                if !walk.state.unreachable
                    && let Some(at) = owner.and_then(|owner| symbols.get(owner).locations.first())
                {
                    walk.leaving(at.span);
                }
            });
        };
    walk_body(&mut walk, member, &body.statements);
    // A local function is a method of its own: whatever it reads of the
    // method around it is checked where it is called, which this does not
    // do, so it starts with everything outside assigned.
    for function in &body.local_functions {
        // An `extern` one has no body to assign its `out` parameters in:
        // the code that does is not C#.
        if symbols
            .get(function.symbol)
            .modifiers
            .contains(crate::symbol::Modifiers::EXTERN)
        {
            continue;
        }
        walk_body(
            &mut walk,
            Some(function.symbol),
            std::slice::from_ref(&function.body),
        );
    }
    if walk.unsure {
        return Diagnostics::new();
    }
    walk.found
        .into_iter()
        .map(|finding| {
            let diagnostic = match finding {
                Finding::Local(local, span) => {
                    let name = &body.locals[local.0 as usize].name;
                    Diagnostic::new(ErrorCode::ErrUseDefViolation, span, &[name])
                }
                Finding::OutRead(parameter, span) => Diagnostic::new(
                    ErrorCode::ErrUseDefViolationOut,
                    span,
                    &[&symbols.get(parameter).name],
                ),
                Finding::OutLeft(parameter, span) => Diagnostic::new(
                    ErrorCode::ErrParamUnassigned,
                    span,
                    &[&symbols.get(parameter).name],
                ),
            };
            (tree, diagnostic)
        })
        .collect()
}

/// What the walk found wrong.
enum Finding {
    /// A local read before it was surely assigned (CS0165).
    Local(LocalId, rustlyn_text::TextSpan),
    /// An `out` parameter read before it was (CS0269).
    OutRead(SymbolId, rustlyn_text::TextSpan),
    /// Its method left before it was (CS0177).
    OutLeft(SymbolId, rustlyn_text::TextSpan),
}

/// Whether assigning a local of this type is one write, so that the local
/// is either assigned or not.
fn trackable(binder: &Binder<'_>, ty: &Type) -> bool {
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    match ty {
        Type::Error | Type::Void | Type::Null | Type::ByRef(_) => false,
        Type::Array { .. }
        | Type::Pointer(_)
        | Type::FunctionPointer(_)
        | Type::TypeParameter(_)
        | Type::Dynamic => true,
        Type::Tuple(_) => true,
        Type::Named { symbol, .. } => {
            let symbol = *symbol;
            if TRACKED_SPECIAL
                .iter()
                .any(|special| compilation.special_type(*special) == Some(symbol))
                || ["System.Nullable`1", "System.IntPtr", "System.UIntPtr"]
                    .iter()
                    .any(|name| compilation.type_by_metadata_name(name) == Some(symbol))
            {
                return true;
            }
            let declared = symbols.get(symbol);
            match declared.type_kind() {
                Some(TypeKind::Enum) => true,
                Some(kind) if kind.is_reference_type() => true,
                Some(TypeKind::Struct) if !compilation.is_from_metadata(symbol) => {
                    // A struct with no fields is assigned by being declared.
                    !deeply_empty(binder, symbol, 0)
                }
                _ => false,
            }
        }
    }
}

/// Whether a struct written in source has no instance field that holds
/// anything: none, or only fields of structs that are as empty. Such a
/// local is assigned by being declared.
fn deeply_empty(binder: &Binder<'_>, symbol: SymbolId, depth: usize) -> bool {
    let compilation = binder.compilation();
    let symbols = compilation.symbols();
    if depth > 8 {
        return false;
    }
    symbols.get(symbol).members.iter().all(|id| {
        let member = symbols.get(*id);
        if member.kind != SymbolKind::Field
            || member.modifiers.contains(Modifiers::STATIC)
            || member.modifiers.contains(Modifiers::CONST)
        {
            return true;
        }
        match binder.type_of(*id, &mut Diagnostics::new()) {
            Type::Named { symbol, .. } => {
                symbols.get(symbol).type_kind() == Some(TypeKind::Struct)
                    && !compilation.is_from_metadata(symbol)
                    && binder.special_of(&Type::named(symbol)).is_none()
                    && !compilation.declaration_nodes(symbol).is_empty()
                    && deeply_empty(binder, symbol, depth + 1)
            }
            _ => false,
        }
    })
}

/// The types from the core library whose locals are watched: the language's
/// own, whose fields nobody assigns one by one.
const TRACKED_SPECIAL: [SpecialType; 15] = [
    SpecialType::Boolean,
    SpecialType::Char,
    SpecialType::SByte,
    SpecialType::Byte,
    SpecialType::Int16,
    SpecialType::UInt16,
    SpecialType::Int32,
    SpecialType::UInt32,
    SpecialType::Int64,
    SpecialType::UInt64,
    SpecialType::Single,
    SpecialType::Double,
    SpecialType::Decimal,
    SpecialType::String,
    SpecialType::Object,
];

/// What the body is made of, found before the walk: whether it has
/// anything the walk cannot follow, and which locals it must leave alone.
#[derive(Default)]
struct Shape {
    unsure: bool,
    /// Locals whose fields are touched one by one, locals a `ref` local
    /// points at, and locals a local function writes to.
    untracked: Vec<LocalId>,
    /// Parameters whose fields are touched one by one.
    untracked_parameters: Vec<SymbolId>,
    in_local_function: bool,
    /// Which locals are `ref` locals, by index.
    by_ref: Vec<bool>,
    /// The labels the body declares, lambdas and local functions included,
    /// and the labels its `goto`s name.
    labels: Vec<String>,
    gotos: Vec<String>,
    /// The `try` statements with a `finally` whose body or catches the
    /// shape is inside, outermost first, each named by its address.
    tries: Vec<usize>,
    /// For each label, the `try`s with a `finally` it is inside: a `goto`
    /// to it leaves the ones it is in beyond these.
    label_tries: HashMap<String, Vec<usize>>,
}

impl Shape {
    fn statement(&mut self, statement: &BoundStatement) {
        match &statement.kind {
            BoundStatementKind::Unsupported(_) => self.unsure = true,
            BoundStatementKind::Goto(label) => self.gotos.push(label.clone()),
            BoundStatementKind::Label(label) => {
                self.labels.push(label.clone());
                self.label_tries.insert(label.clone(), self.tries.clone());
            }
            BoundStatementKind::Block(statements) => {
                for inner in statements {
                    self.statement(inner);
                }
            }
            BoundStatementKind::LocalDeclaration { local, initializer } => {
                if let Some(value) = initializer {
                    // `ref int r = ref x;` makes `r` another name for `x`,
                    // and writing through it assigns `x`; `int r = x;` is
                    // only a read.
                    let by_ref = self.by_ref.get(local.0 as usize).copied().unwrap_or(false);
                    match &value.kind {
                        _ if !by_ref => {}
                        BoundExpressionKind::Local(target) => self.untracked.push(*target),
                        BoundExpressionKind::Parameter(target) => {
                            self.untracked_parameters.push(*target);
                        }
                        _ => {}
                    }
                    self.expression(value);
                }
            }
            BoundStatementKind::Expression(value)
            | BoundStatementKind::YieldReturn(value)
            | BoundStatementKind::Return(Some(value))
            | BoundStatementKind::Throw(Some(value)) => self.expression(value),
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                self.expression(condition);
                self.statement(consequence);
                if let Some(alternative) = alternative {
                    self.statement(alternative);
                }
            }
            BoundStatementKind::While { condition, body }
            | BoundStatementKind::DoWhile { body, condition } => {
                self.expression(condition);
                self.statement(body);
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                for inner in initializers {
                    self.statement(inner);
                }
                if let Some(condition) = condition {
                    self.expression(condition);
                }
                for incrementor in incrementors {
                    self.expression(incrementor);
                }
                self.statement(body);
            }
            BoundStatementKind::ForEach {
                collection, body, ..
            } => {
                self.expression(collection);
                self.statement(body);
            }
            BoundStatementKind::ConstructorInitializer { arguments, .. } => {
                for argument in arguments {
                    self.expression(argument);
                }
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => {
                self.expression(governing);
                for section in sections {
                    for label in &section.labels {
                        if let BoundSwitchLabel::Case(case) = label {
                            self.pattern(&case.pattern);
                            if let Some(when) = &case.when {
                                self.expression(when);
                            }
                        }
                    }
                    for inner in &section.statements {
                        self.statement(inner);
                    }
                }
            }
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => {
                if finally.is_some() {
                    self.tries.push(std::ptr::from_ref(statement) as usize);
                }
                self.statement(body);
                for catch in catches {
                    if let Some(filter) = &catch.filter {
                        self.expression(filter);
                    }
                    self.statement(&catch.body);
                }
                if let Some(finally) = finally {
                    self.tries.pop();
                    self.statement(finally);
                }
            }
            BoundStatementKind::Using { resources, body } => {
                for resource in resources {
                    self.expression(&resource.value);
                }
                self.statement(body);
            }
            BoundStatementKind::Lock { value, body, .. } => {
                self.expression(value);
                self.statement(body);
            }
            BoundStatementKind::Fixed { declarations, body } => {
                for inner in declarations {
                    self.statement(inner);
                }
                self.statement(body);
            }
            BoundStatementKind::Return(None)
            | BoundStatementKind::Throw(None)
            | BoundStatementKind::YieldBreak
            | BoundStatementKind::Break(_)
            | BoundStatementKind::Continue(_)
            | BoundStatementKind::GotoCase(_)
            | BoundStatementKind::Empty => {}
        }
    }

    fn expression(&mut self, expression: &BoundExpression) {
        match &expression.kind {
            BoundExpressionKind::Error
            | BoundExpressionKind::Unsupported(_)
            | BoundExpressionKind::UnboundCollection(_)
            | BoundExpressionKind::UnboundCreation(_)
            | BoundExpressionKind::UnboundConditional(_)
            | BoundExpressionKind::UnboundSwitch(_) => self.unsure = true,
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                ..
            } => {
                if let Some(local) = struct_local(receiver) {
                    self.untracked.push(local);
                }
                if let Some(parameter) = struct_parameter(receiver) {
                    self.untracked_parameters.push(parameter);
                }
                self.expression(receiver);
            }
            BoundExpressionKind::Assignment { target, value } => {
                if self.in_local_function {
                    self.written(target);
                }
                self.expression(target);
                self.expression(value);
            }
            BoundExpressionKind::RefArgument { operand, .. }
            | BoundExpressionKind::AddressOf { operand } => {
                if self.in_local_function {
                    self.written(operand);
                }
                self.expression(operand);
            }
            BoundExpressionKind::SpillSequence { statements, value } => {
                for statement in statements {
                    self.statement(statement);
                }
                self.expression(value);
            }
            BoundExpressionKind::IsPattern { operand, pattern } => {
                self.expression(operand);
                self.pattern(pattern);
            }
            BoundExpressionKind::Switch { governing, arms } => {
                self.expression(governing);
                for arm in arms {
                    self.pattern(&arm.pattern);
                    if let Some(when) = &arm.when {
                        self.expression(when);
                    }
                    self.expression(&arm.value);
                }
            }
            _ => each_child(expression, |child| self.expression(child)),
        }
    }

    fn pattern(&mut self, pattern: &BoundPattern) {
        match &pattern.kind {
            BoundPatternKind::Unsupported(_) => self.unsure = true,
            BoundPatternKind::Constant(value) | BoundPatternKind::Relational { value, .. } => {
                self.expression(value);
            }
            BoundPatternKind::VarDeconstruct { deconstruction, .. } => {
                self.expression(deconstruction);
            }
            BoundPatternKind::Recursive(recursive) => {
                for (_, inner) in &recursive.properties {
                    self.pattern(inner);
                }
                for inner in &recursive.positional {
                    self.pattern(inner);
                }
            }
            BoundPatternKind::List(list) => {
                for inner in list.patterns() {
                    self.pattern(inner);
                }
            }
            BoundPatternKind::And(left, right) | BoundPatternKind::Or(left, right) => {
                self.pattern(left);
                self.pattern(right);
            }
            BoundPatternKind::Not(inner) | BoundPatternKind::UnionCase { inner, .. } => {
                self.pattern(inner);
            }
            // The test reads only its own local and a constant.
            BoundPatternKind::Discard
            | BoundPatternKind::Var { .. }
            | BoundPatternKind::Type(_)
            | BoundPatternKind::Declaration { .. }
            | BoundPatternKind::SpanString { .. } => {}
        }
    }

    /// A local a local function writes to: calling the function assigns it,
    /// which only a walk that follows calls would see.
    fn written(&mut self, target: &BoundExpression) {
        match &target.kind {
            BoundExpressionKind::Local(local) => self.untracked.push(*local),
            BoundExpressionKind::TupleCreation(elements)
            | BoundExpressionKind::Sequence(elements) => {
                for element in elements {
                    self.written(element);
                }
            }
            BoundExpressionKind::Conversion { operand, .. } => self.written(operand),
            _ => {}
        }
    }
}

/// The local a field is read from, where that local holds a value type.
fn struct_local(receiver: &BoundExpression) -> Option<LocalId> {
    match &receiver.kind {
        BoundExpressionKind::Local(local) => Some(*local),
        BoundExpressionKind::Field {
            receiver: Some(inner),
            ..
        } => struct_local(inner),
        _ => None,
    }
}

/// The parameter a field is read from, through fields of fields.
fn struct_parameter(receiver: &BoundExpression) -> Option<SymbolId> {
    match &receiver.kind {
        BoundExpressionKind::Parameter(parameter) => Some(*parameter),
        BoundExpressionKind::Field {
            receiver: Some(inner),
            ..
        } => struct_parameter(inner),
        _ => None,
    }
}

fn each_nested_statement(statement: &BoundStatement, visit: &mut impl FnMut(&BoundStatement)) {
    visit(statement);
    match &statement.kind {
        BoundStatementKind::Block(statements) => {
            for inner in statements {
                each_nested_statement(inner, visit);
            }
        }
        BoundStatementKind::If {
            consequence,
            alternative,
            ..
        } => {
            each_nested_statement(consequence, visit);
            if let Some(alternative) = alternative {
                each_nested_statement(alternative, visit);
            }
        }
        BoundStatementKind::While { body, .. }
        | BoundStatementKind::DoWhile { body, .. }
        | BoundStatementKind::For { body, .. }
        | BoundStatementKind::ForEach { body, .. }
        | BoundStatementKind::Using { body, .. }
        | BoundStatementKind::Lock { body, .. }
        | BoundStatementKind::Fixed { body, .. } => each_nested_statement(body, visit),
        BoundStatementKind::Switch { sections, .. } => {
            for section in sections {
                for inner in &section.statements {
                    each_nested_statement(inner, visit);
                }
            }
        }
        BoundStatementKind::Try {
            body,
            catches,
            finally,
        } => {
            each_nested_statement(body, visit);
            for catch in catches {
                each_nested_statement(&catch.body, visit);
            }
            if let Some(finally) = finally {
                each_nested_statement(finally, visit);
            }
        }
        _ => {}
    }
}

/// Calls `visit` on each expression a statement holds directly, and on
/// those of the statements inside it; lambdas and local functions are
/// bodies of their own.
pub(crate) fn each_expression_of(
    statement: &BoundStatement,
    visit: &mut impl FnMut(&BoundExpression),
) {
    each_nested_statement(statement, &mut |inner| match &inner.kind {
        BoundStatementKind::LocalDeclaration {
            initializer: Some(value),
            ..
        }
        | BoundStatementKind::Expression(value)
        | BoundStatementKind::YieldReturn(value)
        | BoundStatementKind::Return(Some(value))
        | BoundStatementKind::Throw(Some(value))
        | BoundStatementKind::If {
            condition: value, ..
        }
        | BoundStatementKind::While {
            condition: value, ..
        }
        | BoundStatementKind::DoWhile {
            condition: value, ..
        }
        | BoundStatementKind::ForEach {
            collection: value, ..
        }
        | BoundStatementKind::Lock { value, .. } => visit(value),
        BoundStatementKind::For {
            initializers,
            condition,
            incrementors,
            ..
        } => {
            for initializer in initializers {
                each_expression_of(initializer, visit);
            }
            if let Some(condition) = condition {
                visit(condition);
            }
            for incrementor in incrementors {
                visit(incrementor);
            }
        }
        BoundStatementKind::Switch { governing, .. } => visit(governing),
        BoundStatementKind::Using { resources, .. } => {
            for resource in resources {
                visit(&resource.value);
            }
        }
        BoundStatementKind::ConstructorInitializer { arguments, .. } => {
            for argument in arguments {
                visit(argument);
            }
        }
        _ => {}
    });
}

/// Calls `visit` on each expression directly inside `expression`.
pub(crate) fn each_child_of(
    expression: &BoundExpression,
    visit: &mut impl FnMut(&BoundExpression),
) {
    each_child(expression, visit);
}

/// Calls `visit` on each expression directly inside `expression`.
fn each_child(expression: &BoundExpression, mut visit: impl FnMut(&BoundExpression)) {
    use BoundExpressionKind as K;
    match &expression.kind {
        K::Field { receiver, .. }
        | K::Property { receiver, .. }
        | K::MethodGroup { receiver, .. }
        | K::DelegateCreation { receiver, .. } => {
            if let Some(receiver) = receiver {
                visit(receiver);
            }
        }
        K::RefArgument { operand, .. }
        | K::Dereference { operand }
        | K::AddressOf { operand }
        | K::MakeRef(operand)
        | K::RefValue(operand)
        | K::RefType(operand)
        | K::Unary { operand, .. }
        | K::Conversion { operand, .. }
        | K::TypeTest { operand, .. }
        | K::TryCast { operand, .. }
        | K::IsPattern { operand, .. }
        | K::Await { operand, .. } => visit(operand),
        K::FunctionPointerCall { pointer, arguments } => {
            visit(pointer);
            for argument in arguments {
                visit(argument);
            }
        }
        K::Call {
            receiver,
            arguments,
            ..
        } => {
            if let Some(receiver) = receiver {
                visit(receiver);
            }
            for argument in arguments {
                visit(argument);
            }
        }
        K::ObjectCreation {
            arguments,
            initializers,
            ..
        } => {
            for argument in arguments.iter().chain(initializers) {
                visit(argument);
            }
        }
        K::With {
            receiver,
            initializers,
        } => {
            visit(receiver);
            for initializer in initializers {
                visit(initializer);
            }
        }
        K::TupleCreation(elements)
        | K::Sequence(elements)
        | K::InterpolatedString(elements)
        | K::ArgList(elements) => {
            for element in elements {
                visit(element);
            }
        }
        K::StackAlloc {
            count, elements, ..
        } => {
            visit(count);
            for element in elements {
                visit(element);
            }
        }
        K::Throw(operand) => {
            if let Some(operand) = operand {
                visit(operand);
            }
        }
        K::ConditionalAccess { receiver, access } => {
            visit(receiver);
            visit(access);
        }
        K::ArrayCreation {
            lengths, elements, ..
        } => {
            for inner in lengths.iter().chain(elements) {
                visit(inner);
            }
        }
        K::ArrayAccess { array, indices } => {
            visit(array);
            for index in indices {
                visit(index);
            }
        }
        K::ArrayLength { array } => visit(array),
        K::IndexerAccess {
            receiver,
            arguments,
            ..
        } => {
            visit(receiver);
            for argument in arguments {
                visit(argument);
            }
        }
        K::Binary { left, right, .. } => {
            visit(left);
            visit(right);
        }
        K::Conditional {
            condition,
            consequence,
            alternative,
        } => {
            visit(condition);
            visit(consequence);
            visit(alternative);
        }
        K::Assignment { target, value } | K::CompoundAssignment { target, value, .. } => {
            visit(target);
            visit(value);
        }
        K::EventAssignment {
            receiver, handler, ..
        } => {
            if let Some(receiver) = receiver {
                visit(receiver);
            }
            visit(handler);
        }
        K::Increment { target, .. } => visit(target),
        // The statements are for the walks that know statements.
        K::SpillSequence { value, .. } => visit(value),
        K::StringInsert { value, .. } => visit(value),
        K::Switch { governing, arms } => {
            visit(governing);
            for arm in arms {
                if let Some(when) = &arm.when {
                    visit(when);
                }
                visit(&arm.value);
            }
        }
        K::Dynamic(dynamic) => {
            if let Some(receiver) = &dynamic.receiver {
                visit(receiver);
            }
            for argument in &dynamic.arguments {
                visit(argument);
            }
        }
        K::Error
        | K::ArgListHandle
        | K::Unsupported(_)
        | K::Literal(_)
        | K::MethodAddress { .. }
        | K::Local(_)
        | K::Parameter(_)
        | K::This
        | K::Base
        | K::StackValue
        | K::TypeExpression(_)
        | K::NamespaceExpression(_)
        | K::UnboundLambda(_)
        | K::UnboundCollection(_)
        | K::UnboundCreation(_)
        | K::UnboundConditional(_)
        | K::UnboundSwitch(_)
        | K::Lambda(_)
        | K::SizeOf(_)
        | K::AccessedValue
        | K::CreatedObject
        | K::TypeOf(_)
        | K::Default(_) => {}
    }
}

/// Which locals are definitely assigned at one point, or that the point
/// cannot be reached, where everything counts as assigned.
#[derive(Clone, PartialEq, Debug)]
struct State {
    bits: Vec<u64>,
    unreachable: bool,
}

impl State {
    fn assigned(count: usize) -> Self {
        Self {
            bits: vec![u64::MAX; count.div_ceil(64)],
            unreachable: false,
        }
    }

    fn unreachable(count: usize) -> Self {
        Self {
            unreachable: true,
            ..Self::assigned(count)
        }
    }

    fn is_assigned(&self, local: LocalId) -> bool {
        let index = local.0 as usize;
        self.unreachable || self.bits[index / 64] & (1 << (index % 64)) != 0
    }

    fn assign(&mut self, local: LocalId) {
        let index = local.0 as usize;
        self.bits[index / 64] |= 1 << (index % 64);
    }

    fn unassign(&mut self, local: LocalId) {
        let index = local.0 as usize;
        self.bits[index / 64] &= !(1 << (index % 64));
    }

    /// Where two paths meet: assigned only where both assigned it.
    fn join(&mut self, other: &Self) {
        if other.unreachable {
            return;
        }
        if self.unreachable {
            *self = other.clone();
            return;
        }
        for (mine, theirs) in self.bits.iter_mut().zip(&other.bits) {
            *mine &= theirs;
        }
    }

    /// Both in sequence, as a `finally` follows what it guards: assigned
    /// where either assigned it.
    fn then(&mut self, other: &Self) {
        if other.unreachable {
            self.unreachable = true;
        }
        for (mine, theirs) in self.bits.iter_mut().zip(&other.bits) {
            *mine |= theirs;
        }
    }
}

/// A `try` with a `finally` whose body or catches are being walked, and
/// what its `finally` is sure to assign, which every jump out of it picks up.
struct Guard {
    /// Which `try` it is, as `Shape` named it.
    id: usize,
    /// How many loops and `switch`es were being walked around it: a jump to
    /// one of those leaves it, a jump to a later one does not.
    depth: usize,
    /// The state after the `finally`, walked from the state the `try` began
    /// with.
    finally: State,
}

/// A loop or a `switch` being walked, and the states its jumps carry.
struct Target {
    is_switch: bool,
    breaks: State,
    continues: State,
}

struct Walk<'a, 'b> {
    binder: &'a Binder<'b>,
    body: &'a BoundBody,
    tracked: Vec<bool>,
    /// The `out` parameters with a slot, in slot order after the locals.
    outs: Vec<SymbolId>,
    /// The `out` parameters of the method being walked, which a `return`
    /// has to have assigned.
    checking: Vec<SymbolId>,
    /// How many lambdas deep the walk is: a `return` in one leaves the
    /// lambda, not the method.
    lambdas: usize,
    state: State,
    targets: Vec<Target>,
    found: Vec<Finding>,
    /// Something the walk met that it cannot judge: a `switch` that may
    /// cover every value without a `default`.
    unsure: bool,
    /// For each local function, the locals of the method around it that it
    /// reads before it assigns them: a call to it reads them there.
    needs: HashMap<SymbolId, Vec<LocalId>>,
    /// For each label, what is assigned on every `goto` to it met so far:
    /// the state a label is reached with besides the one that falls into
    /// it. Kept from one walk of a body to the next; see [`Walk::settled`].
    arriving: HashMap<String, State>,
    /// Whether the walk under way took a local out of a label's state: the
    /// label may have been walked already with more assigned than that, so
    /// the body is walked again.
    arriving_changed: bool,
    /// Whether the body has a `goto`, and so its declared locals start out
    /// unassigned rather than becoming so where they are declared.
    follows_gotos: bool,
    /// The `try`s with a `finally` the walk is inside, outermost first, in
    /// the lambda or method being walked.
    guards: Vec<Guard>,
    /// For each label, the ids of the `try`s with a `finally` it is inside.
    label_tries: HashMap<String, Vec<usize>>,
}

impl Walk<'_, '_> {
    fn count(&self) -> usize {
        self.body.locals.len() + self.outs.len()
    }

    /// The slot an `out` parameter is tracked in.
    fn out_slot(&self, parameter: SymbolId) -> Option<LocalId> {
        let at = self.outs.iter().position(|out| *out == parameter)?;
        Some(LocalId((self.body.locals.len() + at) as u32))
    }

    /// Control leaves the method being walked at `span`: every `out`
    /// parameter must have been assigned.
    fn leaving(&mut self, span: rustlyn_text::TextSpan) {
        if self.lambdas > 0 || self.state.unreachable {
            return;
        }
        for parameter in self.checking.clone() {
            if let Some(slot) = self.out_slot(parameter)
                && !self.state.is_assigned(slot)
            {
                self.found.push(Finding::OutLeft(parameter, span));
            }
        }
    }

    /// A read of a parameter, which matters only for an `out` one.
    fn read_parameter(&mut self, parameter: SymbolId, span: rustlyn_text::TextSpan) {
        if let Some(slot) = self.out_slot(parameter)
            && !self.state.is_assigned(slot)
        {
            self.found.push(Finding::OutRead(parameter, span));
            self.state.assign(slot);
        }
    }

    fn statement(&mut self, statement: &BoundStatement) {
        match &statement.kind {
            BoundStatementKind::Block(statements) => {
                for inner in statements {
                    self.statement(inner);
                }
            }
            BoundStatementKind::LocalDeclaration { local, initializer } => {
                // A declaration is where a local stops counting as assigned
                // — except in a body with a `goto`, where its locals start
                // out unassigned and a bare `int x;` changes nothing, as
                // the language has it (§9.4.4.7): a jump back to before the
                // declaration, with `x` assigned on the way, reads it
                // after, which the framework's own vectorised loops do.
                if !self.state.unreachable && (initializer.is_some() || !self.follows_gotos) {
                    self.state.unassign(*local);
                }
                if let Some(value) = initializer {
                    self.expression(value);
                    self.state.assign(*local);
                }
            }
            BoundStatementKind::Expression(value) | BoundStatementKind::YieldReturn(value) => {
                self.expression(value);
            }
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                let (when_true, when_false) = self.condition(condition);
                self.state = when_true;
                self.statement(consequence);
                let after_then = std::mem::replace(&mut self.state, when_false);
                if let Some(alternative) = alternative {
                    self.statement(alternative);
                }
                self.state.join(&after_then);
            }
            BoundStatementKind::While { condition, body } => {
                let (when_true, when_false) = self.condition(condition);
                self.state = when_true;
                let target = self.looping(body);
                self.state = when_false;
                self.state.join(&target.breaks);
            }
            BoundStatementKind::DoWhile { body, condition } => {
                let target = self.looping(body);
                self.state.join(&target.continues);
                let (_, when_false) = self.condition(condition);
                self.state = when_false;
                self.state.join(&target.breaks);
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                for inner in initializers {
                    self.statement(inner);
                }
                let (when_true, when_false) = match condition {
                    Some(condition) => self.condition(condition),
                    None => (self.state.clone(), State::unreachable(self.count())),
                };
                self.state = when_true;
                let target = self.looping(body);
                self.state.join(&target.continues);
                for incrementor in incrementors {
                    self.expression(incrementor);
                }
                self.state = when_false;
                self.state.join(&target.breaks);
            }
            BoundStatementKind::ForEach {
                collection, body, ..
            } => {
                self.expression(collection);
                let before = self.state.clone();
                let target = self.looping(body);
                self.state = before;
                self.state.join(&target.breaks);
            }
            BoundStatementKind::ConstructorInitializer { arguments, .. } => {
                self.arguments(arguments);
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => {
                self.expression(governing);
                let entry = self.state.clone();
                self.targets.push(Target {
                    is_switch: true,
                    breaks: State::unreachable(self.count()),
                    continues: State::unreachable(self.count()),
                });
                let mut has_default = false;
                for section in sections {
                    let mut start = State::unreachable(self.count());
                    for label in &section.labels {
                        self.state = entry.clone();
                        match label {
                            BoundSwitchLabel::Default => has_default = true,
                            BoundSwitchLabel::Case(case) => {
                                let (matched, _) = self.pattern(&case.pattern);
                                self.state = matched;
                                if let Some(when) = &case.when {
                                    self.state = self.condition(when).0;
                                }
                            }
                        }
                        start.join(&self.state);
                    }
                    self.state = start;
                    for inner in &section.statements {
                        self.statement(inner);
                    }
                }
                let target = self.pop_target();
                // Without a `default`, the end is reached where no case
                // matched — unless the cases cover every value, as `case
                // true:` and `case false:` do, or a `case var x:`.
                let exhaustive = has_default || self.covers_everything(governing, sections);
                if !exhaustive && self.may_cover_everything(governing, sections) {
                    self.unsure = true;
                }
                self.state = if exhaustive {
                    State::unreachable(self.count())
                } else {
                    entry
                };
                self.state.join(&target.breaks);
                // `continue` inside a `switch` belongs to the loop around it.
                if let Some(outer) = self.targets.iter_mut().rev().find(|t| !t.is_switch) {
                    outer.continues.join(&target.continues);
                }
            }
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => {
                let entry = self.state.clone();
                // The `finally` is walked first, from where the `try`
                // began, so that the jumps in the body know what it
                // assigns; its findings go after the body's, where they
                // belong.
                let mut finally_found = Vec::new();
                if let Some(finally) = finally {
                    let mark = self.found.len();
                    self.statement(finally);
                    finally_found = self.found.split_off(mark);
                    let after = std::mem::replace(&mut self.state, entry.clone());
                    self.guards.push(Guard {
                        id: std::ptr::from_ref(statement) as usize,
                        depth: self.targets.len(),
                        finally: after,
                    });
                }
                self.statement(body);
                let mut end = self.state.clone();
                for catch in catches {
                    self.state = entry.clone();
                    if let Some(filter) = &catch.filter {
                        self.state = self.condition(filter).0;
                    }
                    self.statement(&catch.body);
                    end.join(&self.state);
                }
                if finally.is_some()
                    && let Some(guard) = self.guards.pop()
                {
                    end.then(&guard.finally);
                    self.found.extend(finally_found);
                }
                self.state = end;
            }
            BoundStatementKind::Using { resources, body } => {
                for resource in resources {
                    self.expression(&resource.value);
                    self.state.assign(resource.local);
                }
                self.statement(body);
            }
            BoundStatementKind::Lock { value, body, .. } => {
                self.expression(value);
                self.statement(body);
            }
            BoundStatementKind::Fixed { declarations, body } => {
                for inner in declarations {
                    self.statement(inner);
                }
                self.statement(body);
            }
            BoundStatementKind::Return(value) => {
                if let Some(value) = value {
                    self.expression(value);
                }
                self.pass_finallys(0);
                self.leaving(statement.span);
                self.state = State::unreachable(self.count());
            }
            BoundStatementKind::Throw(value) => {
                if let Some(value) = value {
                    self.expression(value);
                }
                self.state = State::unreachable(self.count());
            }
            BoundStatementKind::YieldBreak | BoundStatementKind::GotoCase(_) => {
                self.state = State::unreachable(self.count());
            }
            BoundStatementKind::Break(outward) => {
                if let Some(index) = self.targets.len().checked_sub(*outward + 1) {
                    self.pass_finallys_to(index);
                    self.targets[index].breaks.join(&self.state);
                }
                self.state = State::unreachable(self.count());
            }
            BoundStatementKind::Continue(outward) => {
                let index = self
                    .targets
                    .iter()
                    .enumerate()
                    .rev()
                    .filter(|(_, t)| !t.is_switch)
                    .nth(*outward)
                    .map(|(index, _)| index);
                if let Some(index) = index {
                    self.pass_finallys_to(index);
                    self.targets[index].continues.join(&self.state);
                }
                self.state = State::unreachable(self.count());
            }
            // A label is reached by falling into it and by every `goto`
            // to it: assigned only where all of them assigned it.
            BoundStatementKind::Label(label) => {
                if let Some(arriving) = self.arriving.get(label) {
                    self.state.join(arriving);
                }
            }
            BoundStatementKind::Goto(label) => {
                // The label is outside every `try` it is not inside, and
                // those are the ones the jump leaves; a label somewhere
                // else than around the `goto` is not one to follow.
                match self.label_tries.get(label) {
                    Some(inside)
                        if inside.len() <= self.guards.len()
                            && inside.iter().zip(&self.guards).all(|(id, g)| *id == g.id) =>
                    {
                        let kept = inside.len();
                        self.pass_finallys(kept);
                    }
                    _ => self.unsure = true,
                }
                let count = self.count();
                let arriving = self
                    .arriving
                    .entry(label.clone())
                    .or_insert_with(|| State::unreachable(count));
                let before = arriving.clone();
                arriving.join(&self.state);
                if *arriving != before {
                    self.arriving_changed = true;
                }
                self.state = State::unreachable(count);
            }
            BoundStatementKind::Empty | BoundStatementKind::Unsupported(_) => {}
        }
    }

    /// A jump leaves every `try` with a `finally` from the `keep`th outward
    /// in, and takes on what each `finally` assigns on the way.
    fn pass_finallys(&mut self, keep: usize) {
        for index in keep..self.guards.len() {
            let after = self.guards[index].finally.clone();
            self.state.then(&after);
        }
    }

    /// A jump to the loop or `switch` at `target` in the stack leaves the
    /// `try`s that began before it was entered.
    fn pass_finallys_to(&mut self, target: usize) {
        let keep = self.guards.iter().take_while(|g| g.depth <= target).count();
        self.pass_finallys(keep);
    }

    /// Walks a body with `once` until the states its `goto`s carry to their
    /// labels stop changing, keeping the findings of the last walk only.
    ///
    /// A `goto` back to a label arrives after the label was walked, so the
    /// first walk reads what follows the label with too much assigned; the
    /// next knows better. Each walk can only take locals out of a label's
    /// state, so there are no more walks than labels times locals, and for
    /// a body without a `goto` there is the one.
    fn settled(&mut self, mut once: impl FnMut(&mut Self)) {
        self.arriving.clear();
        let mark = self.found.len();
        // Far more than any body needs; past it the walk says nothing
        // rather than something unsettled.
        for _ in 0..1024 {
            self.found.truncate(mark);
            self.arriving_changed = false;
            once(self);
            if !self.arriving_changed {
                return;
            }
        }
        self.unsure = true;
    }

    /// Whether the cases of a switch match every value of what it switches
    /// on, so that its end is reached only by `break`.
    fn covers_everything(
        &self,
        governing: &BoundExpression,
        sections: &[crate::bound::BoundSwitchSection],
    ) -> bool {
        let cases = || {
            sections
                .iter()
                .flat_map(|section| &section.labels)
                .filter_map(|label| match label {
                    BoundSwitchLabel::Case(case) if case.when.is_none() => Some(&case.pattern),
                    _ => None,
                })
        };
        if cases()
            .any(|pattern| always_matches(pattern, Some(&governing.ty), false, self) == Some(true))
        {
            return true;
        }
        let covered = |wanted: bool| {
            cases().any(|pattern| match &pattern.kind {
                BoundPatternKind::Constant(value) => {
                    self.binder.folded(value) == Some(ConstantValue::Boolean(wanted))
                }
                _ => false,
            })
        };
        self.is_bool(&governing.ty) && covered(true) && covered(false)
    }

    /// Whether the cases might cover every value in a way this walk does
    /// not see: patterns other than constants, or a `bool` to switch on.
    fn may_cover_everything(
        &self,
        governing: &BoundExpression,
        sections: &[crate::bound::BoundSwitchSection],
    ) -> bool {
        self.is_bool(&governing.ty)
            || self
                .binder
                .nullable_underlying(&governing.ty)
                .is_some_and(|inner| self.is_bool(&inner))
            || sections
                .iter()
                .flat_map(|section| &section.labels)
                .any(|label| {
                    matches!(label, BoundSwitchLabel::Case(case)
                    if !matches!(case.pattern.kind, BoundPatternKind::Constant(_)))
                })
    }

    /// Whether a pattern made only of `true`, `false`, `_`, `not`, `and`
    /// and `or` matches `true`, and whether it matches `false`; `None` for
    /// any other pattern.
    fn bool_pattern(&self, pattern: &BoundPattern) -> Option<(bool, bool)> {
        Some(match &pattern.kind {
            BoundPatternKind::Constant(value) => match self.binder.folded(value)? {
                ConstantValue::Boolean(value) => (value, !value),
                _ => return None,
            },
            BoundPatternKind::Discard => (true, true),
            BoundPatternKind::Not(inner) => {
                let (on_true, on_false) = self.bool_pattern(inner)?;
                (!on_true, !on_false)
            }
            BoundPatternKind::And(left, right) => {
                let (left_true, left_false) = self.bool_pattern(left)?;
                let (right_true, right_false) = self.bool_pattern(right)?;
                (left_true && right_true, left_false && right_false)
            }
            BoundPatternKind::Or(left, right) => {
                let (left_true, left_false) = self.bool_pattern(left)?;
                let (right_true, right_false) = self.bool_pattern(right)?;
                (left_true || right_true, left_false || right_false)
            }
            _ => return None,
        })
    }

    fn is_bool(&self, ty: &Type) -> bool {
        self.binder.special_of(ty) == Some(SpecialType::Boolean)
    }

    /// Walks a loop's body and gives back the states its jumps carried.
    fn looping(&mut self, body: &BoundStatement) -> Target {
        self.targets.push(Target {
            is_switch: false,
            breaks: State::unreachable(self.count()),
            continues: State::unreachable(self.count()),
        });
        self.statement(body);
        self.pop_target()
    }

    fn pop_target(&mut self) -> Target {
        self.targets.pop().unwrap_or_else(|| Target {
            is_switch: false,
            breaks: State::unreachable(self.count()),
            continues: State::unreachable(self.count()),
        })
    }

    /// A read of a local.
    /// A call to a local function, or a delegate made of one, reads what it
    /// reads of the method around it before assigning it.
    fn local_function_used(&mut self, method: SymbolId, span: rustlyn_text::TextSpan) {
        if let Some(needs) = self.needs.get(&method).cloned() {
            for local in needs {
                self.read(local, span);
            }
        }
    }

    fn read(&mut self, local: LocalId, span: rustlyn_text::TextSpan) {
        let index = local.0 as usize;
        if index < self.tracked.len() && self.tracked[index] && !self.state.is_assigned(local) {
            self.found.push(Finding::Local(local, span));
            // Said once: a second read of it is not a second mistake.
            self.state.assign(local);
        }
    }

    /// The states when a condition is true and when it is false.
    fn condition(&mut self, condition: &BoundExpression) -> (State, State) {
        let unreachable = State::unreachable(self.count());
        // A constant reads no variable that could be unassigned: a `const`
        // local is initialized where it is declared.
        if let Some(ConstantValue::Boolean(value)) = self.binder.folded(condition) {
            let state = self.state.clone();
            return if value {
                (state, unreachable)
            } else {
                (unreachable, state)
            };
        }
        match &condition.kind {
            BoundExpressionKind::Unary {
                operator: crate::bound::UnaryOperator::LogicalNot,
                operand,
            } => {
                let (when_true, when_false) = self.condition(operand);
                (when_false, when_true)
            }
            BoundExpressionKind::Binary {
                operator: BinaryOperator::LogicalAnd,
                left,
                right,
            } => {
                let (left_true, left_false) = self.condition(left);
                self.state = left_true;
                let (right_true, mut right_false) = self.condition(right);
                right_false.join(&left_false);
                (right_true, right_false)
            }
            BoundExpressionKind::Binary {
                operator: BinaryOperator::LogicalOr,
                left,
                right,
            } => {
                let (left_true, left_false) = self.condition(left);
                self.state = left_false;
                let (mut right_true, right_false) = self.condition(right);
                right_true.join(&left_true);
                (right_true, right_false)
            }
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                let (when_true, when_false) = self.condition(condition);
                self.state = when_true;
                let (mut true_true, mut true_false) = self.condition(consequence);
                self.state = when_false;
                let (false_true, false_false) = self.condition(alternative);
                true_true.join(&false_true);
                true_false.join(&false_false);
                (true_true, true_false)
            }
            // `c?.M(out x) is T` is true only where there was a `c`, and so
            // where the call ran.
            BoundExpressionKind::TypeTest { operand, .. } if is_conditional_access(operand) => {
                let (when_true, when_false, when_null) = self.lifted_condition(operand);
                let mut value = when_true;
                value.join(&when_false);
                let mut everything = value.clone();
                everything.join(&when_null);
                (value, everything)
            }
            BoundExpressionKind::IsPattern { operand, pattern } => {
                // `(b && M(out x)) is not true` is `!(b && M(out x))`: a
                // pattern of constants on a `bool` picks out which of its
                // two values match.
                if self.is_bool(&operand.ty)
                    && let Some((on_true, on_false)) = self.bool_pattern(pattern)
                {
                    let (when_true, when_false) = self.condition(operand);
                    let unreachable = State::unreachable(self.count());
                    let pick = |taken: bool, state: &State| {
                        if taken {
                            state.clone()
                        } else {
                            unreachable.clone()
                        }
                    };
                    let mut matched = pick(on_true, &when_true);
                    matched.join(&pick(on_false, &when_false));
                    let mut mismatched = pick(!on_true, &when_true);
                    mismatched.join(&pick(!on_false, &when_false));
                    return (matched, mismatched);
                }
                if !is_conditional_access(operand) {
                    self.expression(operand);
                    // `s is string { Length: int j }` on a constant `s` that
                    // is no null cannot fail.
                    let non_null = self
                        .binder
                        .folded(operand)
                        .is_some_and(|value| !matches!(value, ConstantValue::Null));
                    return self.pattern_on_value(pattern, Some(&operand.ty), non_null);
                }
                // `c?.M(out x) is true` ran the call where it matched, and
                // so does any pattern that no null matches.
                let (when_true, when_false, when_null) = self.lifted_condition(operand);
                let mut value = when_true.clone();
                value.join(&when_false);
                let mut everything = value.clone();
                everything.join(&when_null);
                let values = self.bool_values(pattern);
                let (on_match, on_mismatch) = match &pattern.kind {
                    // `c?.M() is true or false`: which of true, false and
                    // null the pattern takes says which states it keeps.
                    _ if values.is_some() => {
                        let [yes, no, nothing] = values.unwrap_or_default();
                        let unreachable = State::unreachable(self.count());
                        let (mut matched, mut mismatched) =
                            (unreachable.clone(), unreachable.clone());
                        for (taken, state) in [
                            (yes, when_true.clone()),
                            (no, when_false.clone()),
                            (nothing, when_null.clone()),
                        ] {
                            if taken {
                                matched.join(&state);
                            } else {
                                mismatched.join(&state);
                            }
                        }
                        (matched, mismatched)
                    }
                    BoundPatternKind::Constant(constant) => match self.binder.folded(constant) {
                        Some(ConstantValue::Boolean(true)) => (when_true, everything),
                        Some(ConstantValue::Boolean(false)) => (when_false, everything),
                        Some(ConstantValue::Null) => (when_null, value),
                        _ => (value, everything),
                    },
                    BoundPatternKind::Not(inner)
                        if matches!(
                            &inner.kind,
                            BoundPatternKind::Constant(constant)
                                if self.binder.folded(constant) == Some(ConstantValue::Null)
                        ) =>
                    {
                        (value, when_null)
                    }
                    BoundPatternKind::Type(_)
                    | BoundPatternKind::Declaration { .. }
                    | BoundPatternKind::Recursive(_)
                    | BoundPatternKind::Relational { .. } => (value, everything),
                    _ => (everything.clone(), everything),
                };
                self.state = on_match;
                let (matched, _) = self.pattern(pattern);
                self.state = on_mismatch;
                let (_, mismatched) = self.pattern(pattern);
                (matched, mismatched)
            }
            BoundExpressionKind::ConditionalAccess { .. }
            | BoundExpressionKind::Binary {
                operator:
                    BinaryOperator::Coalesce | BinaryOperator::Equality | BinaryOperator::Inequality,
                ..
            } => {
                let (when_true, mut when_false, when_null) = self.lifted_condition(condition);
                when_false.join(&when_null);
                (when_true, when_false)
            }
            _ => {
                self.expression(condition);
                (self.state.clone(), self.state.clone())
            }
        }
    }

    /// Which of `true`, `false` and `null` a pattern takes of a `bool?`, where
    /// it is made of those and of `bool` itself.
    fn bool_values(&self, pattern: &BoundPattern) -> Option<[bool; 3]> {
        match &pattern.kind {
            BoundPatternKind::Constant(constant) => match self.binder.folded(constant)? {
                ConstantValue::Boolean(true) => Some([true, false, false]),
                ConstantValue::Boolean(false) => Some([false, true, false]),
                ConstantValue::Null => Some([false, false, true]),
                _ => None,
            },
            BoundPatternKind::Type(ty) if self.is_bool(ty) => Some([true, true, false]),
            BoundPatternKind::Not(inner) => {
                let [yes, no, nothing] = self.bool_values(inner)?;
                Some([!yes, !no, !nothing])
            }
            BoundPatternKind::Or(left, right) => {
                let (left, right) = (self.bool_values(left)?, self.bool_values(right)?);
                Some([
                    left[0] || right[0],
                    left[1] || right[1],
                    left[2] || right[2],
                ])
            }
            BoundPatternKind::And(left, right) => {
                let (left, right) = (self.bool_values(left)?, self.bool_values(right)?);
                Some([
                    left[0] && right[0],
                    left[1] && right[1],
                    left[2] && right[2],
                ])
            }
            _ => None,
        }
    }

    /// The states where a `bool?` is true, false and null (C# 10's
    /// improved definite assignment): in `c?.TryGet(out x) == true` the call
    /// ran wherever the value is true, and `x` is assigned there.
    fn lifted_condition(&mut self, condition: &BoundExpression) -> (State, State, State) {
        let unreachable = State::unreachable(self.count());
        match &condition.kind {
            BoundExpressionKind::ConditionalAccess { receiver, access } => {
                self.expression(receiver);
                let skipped = self.state.clone();
                let (when_true, when_false, mut when_null) = self.lifted_condition(access);
                // A receiver that is a constant, and no null, is never
                // skipped: `"a"?.M(x = 0)` always runs the call.
                if !self
                    .binder
                    .folded(receiver)
                    .is_some_and(|value| value != ConstantValue::Null)
                {
                    when_null.join(&skipped);
                }
                (when_true, when_false, when_null)
            }
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Coalesce,
                left,
                right,
            } => {
                let (left_true, left_false, left_null) = self.lifted_condition(left);
                self.state = left_null;
                let (mut when_true, mut when_false, when_null) = self.lifted_condition(right);
                when_true.join(&left_true);
                when_false.join(&left_false);
                (when_true, when_false, when_null)
            }
            BoundExpressionKind::Binary {
                operator: operator @ (BinaryOperator::Equality | BinaryOperator::Inequality),
                left,
                right,
            } => {
                // `null` where a `T?` is wanted is bound as that type's
                // `default`, which is no less a null.
                let null_default = |side: &BoundExpression| match &unwrapped(side).kind {
                    BoundExpressionKind::Default(ty) => {
                        self.binder.nullable_underlying(ty).is_some()
                    }
                    _ => false,
                };
                let constant = |side: &BoundExpression| match self.binder.folded(unwrapped(side)) {
                    Some(value @ (ConstantValue::Boolean(_) | ConstantValue::Null)) => Some(value),
                    _ if is_null_literal(side) || null_default(side) => Some(ConstantValue::Null),
                    _ => None,
                };
                let (other, constant) = match (constant(left), constant(right)) {
                    (None, Some(value)) => (left, value),
                    (Some(value), None) => (right, value),
                    _ => {
                        let (equal, unequal) = self.compared(left, right);
                        return match operator {
                            BinaryOperator::Equality => (equal, unequal, unreachable),
                            _ => (unequal, equal, unreachable),
                        };
                    }
                };
                let (when_true, when_false, when_null) = self.lifted_condition(other);
                let joined = |mut first: State, second: &State| {
                    first.join(second);
                    first
                };
                let (equal, unequal) = match constant {
                    ConstantValue::Boolean(true) => (when_true, joined(when_false, &when_null)),
                    ConstantValue::Boolean(false) => (when_false, joined(when_true, &when_null)),
                    _ => (when_null, joined(when_true, &when_false)),
                };
                match operator {
                    BinaryOperator::Equality => (equal, unequal, unreachable),
                    _ => (unequal, equal, unreachable),
                }
            }
            BoundExpressionKind::Conversion {
                operand,
                conversion:
                    ConversionKind::NullableWrap
                    | ConversionKind::Identity
                    | ConversionKind::Boxing
                    | ConversionKind::ImplicitReference
                    | ConversionKind::ExplicitReference,
                ..
            } => self.lifted_condition(operand),
            // `(t = c?.M(x = 0)) != null`, which is how a `??` whose left is
            // converted is bound: `t` is whatever was assigned to it, null
            // where that is, and assigned in every case.
            BoundExpressionKind::Assignment { target, value }
                if matches!(target.kind, BoundExpressionKind::Local(_)) =>
            {
                self.target(target);
                let (when_true, when_false, when_null) = self.lifted_condition(value);
                let mut assigned = |state: State| {
                    self.state = state;
                    self.assign_target(target);
                    std::mem::replace(&mut self.state, State::unreachable(0))
                };
                let when_true = assigned(when_true);
                let when_false = assigned(when_false);
                let when_null = assigned(when_null);
                self.state = when_true.clone();
                (when_true, when_false, when_null)
            }
            _ => {
                let (when_true, when_false) = self.condition(condition);
                // A value that may be null is null somewhere between the two;
                // a constant that is not `null` never is (`"A" ?? y` never
                // reads `y`).
                let constant = self
                    .binder
                    .folded(condition)
                    .is_some_and(|value| value != ConstantValue::Null);
                let when_null = if !constant && self.may_be_null(condition) {
                    let mut either = when_true.clone();
                    either.join(&when_false);
                    either
                } else {
                    unreachable
                };
                (when_true, when_false, when_null)
            }
        }
    }

    /// The states where `left == right` holds and where it does not, for
    /// two operands neither of which is a constant: where one side cannot
    /// be null, equality says the other was not null either, so a
    /// `c?.M(out x) == 1` that holds ran the call.
    fn compared(&mut self, left: &BoundExpression, right: &BoundExpression) -> (State, State) {
        let (left_true, left_false, left_null) = self.lifted_condition(left);
        let mut left_value = left_true.clone();
        left_value.join(&left_false);
        let mut everything = left_value.clone();
        everything.join(&left_null);
        self.state = everything;
        let (right_true, right_false, right_null) = self.lifted_condition(right);
        let mut right_value = right_true;
        right_value.join(&right_false);
        let mut after = right_value.clone();
        after.join(&right_null);
        let equal = if !self.may_be_null(right) {
            // What the right side assigned, it assigned on every path.
            let mut both = left_value;
            both.then(&after);
            both
        } else if !self.may_be_null(left) {
            right_value
        } else {
            after.clone()
        };
        (equal, after)
    }

    /// Whether an expression's type lets it be null.
    fn may_be_null(&self, expression: &BoundExpression) -> bool {
        // `T` lifted into a `T?` to be compared is still not null.
        self.type_may_be_null(&unwrapped(expression).ty)
    }

    /// Whether a value of this type can be null.
    fn type_may_be_null(&self, ty: &Type) -> bool {
        if self.binder.nullable_underlying(ty).is_some() {
            return true;
        }
        let symbols = self.binder.compilation().symbols();
        match ty {
            Type::Named { symbol, .. } => !matches!(
                symbols.get(*symbol).type_kind(),
                Some(TypeKind::Struct | TypeKind::Enum | TypeKind::RecordStruct)
            ),
            Type::Tuple(_) | Type::Pointer(_) => false,
            _ => true,
        }
    }

    /// The states where a pattern matches and where it does not, from the
    /// current one. The variables it declares start out unassigned.
    fn pattern(&mut self, pattern: &BoundPattern) -> (State, State) {
        self.pattern_on(pattern, None)
    }

    /// The same, knowing the type of what is matched: `Get() is int i` on an
    /// `int` cannot fail.
    fn pattern_on(&mut self, pattern: &BoundPattern, input: Option<&Type>) -> (State, State) {
        self.pattern_on_value(pattern, input, false)
    }

    /// The same, knowing too whether what is matched is never null.
    fn pattern_on_value(
        &mut self,
        pattern: &BoundPattern,
        input: Option<&Type>,
        non_null: bool,
    ) -> (State, State) {
        let mut declared = Vec::new();
        declared_by(pattern, &mut declared);
        if !self.state.unreachable {
            for local in &declared {
                self.state.unassign(*local);
            }
        }
        self.pattern_values(pattern);
        let (on_match, on_mismatch) = assigned_by(pattern);
        let mut matched = self.state.clone();
        let mut mismatched = self.state.clone();
        for local in on_match {
            matched.assign(local);
        }
        for local in on_mismatch {
            mismatched.assign(local);
        }
        // `e is var x` cannot fail, and `e is not var x` cannot succeed.
        match always_matches(pattern, input, non_null, self) {
            Some(true) => mismatched = State::unreachable(self.count()),
            Some(false) => matched = State::unreachable(self.count()),
            None => {}
        }
        (matched, mismatched)
    }

    /// The expressions inside a pattern: the constants it compares with.
    fn pattern_values(&mut self, pattern: &BoundPattern) {
        match &pattern.kind {
            BoundPatternKind::Constant(value) | BoundPatternKind::Relational { value, .. } => {
                self.expression(value);
            }
            BoundPatternKind::Recursive(recursive) => {
                for (_, inner) in &recursive.properties {
                    self.pattern_values(inner);
                }
                for inner in &recursive.positional {
                    self.pattern_values(inner);
                }
            }
            BoundPatternKind::List(list) => {
                for inner in list.patterns() {
                    self.pattern_values(inner);
                }
            }
            BoundPatternKind::And(left, right) | BoundPatternKind::Or(left, right) => {
                self.pattern_values(left);
                self.pattern_values(right);
            }
            BoundPatternKind::Not(inner) | BoundPatternKind::UnionCase { inner, .. } => {
                self.pattern_values(inner);
            }
            _ => {}
        }
    }

    /// Arguments in order; an `out` one is assigned once the call returns,
    /// not before the arguments after it are evaluated.
    fn arguments(&mut self, arguments: &[BoundExpression]) {
        let mut outs = Vec::new();
        for argument in arguments {
            match &argument.kind {
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Out,
                    operand,
                } => match &operand.kind {
                    BoundExpressionKind::Local(local) => {
                        // `out int x` declares `x` right here, unassigned
                        // until the call returns.
                        let declared_here =
                            self.body
                                .locals
                                .get(local.0 as usize)
                                .is_some_and(|symbol| {
                                    symbol.span.start() >= operand.span.start()
                                        && symbol.span.end() <= operand.span.end()
                                });
                        if declared_here && !self.state.unreachable {
                            self.state.unassign(*local);
                        }
                        outs.push(*local);
                    }
                    BoundExpressionKind::Parameter(parameter) => {
                        outs.extend(self.out_slot(*parameter));
                    }
                    _ => self.target(operand),
                },
                _ => self.expression(argument),
            }
        }
        for local in outs {
            self.state.assign(local);
        }
    }

    /// The parts of an assignment's target that are read before it is
    /// written: the receiver of a field, the array and its indices.
    fn target(&mut self, target: &BoundExpression) {
        match &target.kind {
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_) => {}
            BoundExpressionKind::TupleCreation(elements) => {
                for element in elements {
                    self.target(element);
                }
            }
            BoundExpressionKind::Conversion { operand, .. } => self.target(operand),
            _ => self.expression(target),
        }
    }

    /// Assigns whatever locals a target names, once the value is written.
    fn assign_target(&mut self, target: &BoundExpression) {
        match &target.kind {
            BoundExpressionKind::Local(local) => self.state.assign(*local),
            BoundExpressionKind::Parameter(parameter) => {
                if let Some(slot) = self.out_slot(*parameter) {
                    self.state.assign(slot);
                }
            }
            BoundExpressionKind::TupleCreation(elements) => {
                for element in elements {
                    self.assign_target(element);
                }
            }
            BoundExpressionKind::Conversion { operand, .. } => self.assign_target(operand),
            _ => {}
        }
    }

    fn expression(&mut self, expression: &BoundExpression) {
        use BoundExpressionKind as K;
        match &expression.kind {
            K::Local(local) => self.read(*local, expression.span),
            K::Parameter(parameter) => self.read_parameter(*parameter, expression.span),
            K::Assignment { target, value } => {
                self.target(target);
                self.expression(value);
                self.assign_target(target);
            }
            K::AddressOf { operand } if matches!(operand.kind, K::Local(_) | K::Parameter(_)) => {
                // `&x` makes `x` something a pointer may write through.
                self.assign_target(operand);
            }
            K::Call {
                receiver,
                arguments,
                method,
                ..
            } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
                self.arguments(arguments);
                self.local_function_used(*method, expression.span);
            }
            K::DelegateCreation {
                receiver, method, ..
            } => {
                if let Some(receiver) = receiver {
                    self.expression(receiver);
                }
                self.local_function_used(*method, expression.span);
            }
            K::ObjectCreation {
                arguments,
                initializers,
                ..
            } => {
                self.arguments(arguments);
                for initializer in initializers {
                    self.expression(initializer);
                }
            }
            K::IndexerAccess {
                receiver,
                arguments,
                ..
            } => {
                self.expression(receiver);
                self.arguments(arguments);
            }
            K::Dynamic(dynamic) => {
                if let Some(receiver) = &dynamic.receiver {
                    self.expression(receiver);
                }
                self.arguments(&dynamic.arguments);
            }
            K::Lambda(index) => {
                // The body runs later, if at all: it reads what is assigned
                // here, and what it assigns counts for nothing out here.
                if let Some(lambda) = self.body.lambdas.get(*index) {
                    let saved = self.state.clone();
                    let targets = std::mem::take(&mut self.targets);
                    let guards = std::mem::take(&mut self.guards);
                    // A lambda written where nothing reaches still has a
                    // body that starts somewhere: what is around it counts
                    // as assigned, and what it declares starts out not.
                    self.state.unreachable = false;
                    // Its own locals start out unassigned, as the method's
                    // do where the body has a `goto`.
                    if self.follows_gotos {
                        let mut declared = Vec::new();
                        each_nested_statement(&lambda.body, &mut |inner| {
                            if let BoundStatementKind::LocalDeclaration { local, .. } = &inner.kind
                            {
                                declared.push(*local);
                            }
                        });
                        for local in declared {
                            self.state.unassign(local);
                        }
                    }
                    self.lambdas += 1;
                    self.statement(&lambda.body);
                    self.lambdas -= 1;
                    self.targets = targets;
                    self.guards = guards;
                    self.state = saved;
                }
            }
            K::Binary {
                operator: BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr,
                ..
            }
            | K::IsPattern { .. } => {
                let (mut when_true, when_false) = self.condition(expression);
                when_true.join(&when_false);
                self.state = when_true;
            }
            K::Binary {
                operator: BinaryOperator::Coalesce,
                left,
                right,
            } => {
                // The right side runs only where the left is null; where the
                // left is `c?.M(out x)` and not null, the call ran.
                let (when_true, when_false, when_null) = self.lifted_condition(left);
                self.state = when_null;
                self.expression(right);
                self.state.join(&when_true);
                self.state.join(&when_false);
            }
            K::CompoundAssignment {
                target,
                operator: BinaryOperator::Coalesce,
                value,
            } => {
                self.expression(target);
                let saved = self.state.clone();
                self.expression(value);
                self.state = saved;
            }
            K::ConditionalAccess { receiver, access } => {
                self.expression(receiver);
                let saved = self.state.clone();
                self.expression(access);
                self.state = saved;
            }
            K::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                let (when_true, when_false) = self.condition(condition);
                self.state = when_true;
                self.expression(consequence);
                let after = std::mem::replace(&mut self.state, when_false);
                self.expression(alternative);
                self.state.join(&after);
            }
            K::Switch { governing, arms } => {
                self.expression(governing);
                let entry = self.state.clone();
                let mut end = State::unreachable(self.count());
                for arm in arms {
                    self.state = entry.clone();
                    let (matched, _) = self.pattern(&arm.pattern);
                    self.state = matched;
                    if let Some(when) = &arm.when {
                        self.state = self.condition(when).0;
                    }
                    self.expression(&arm.value);
                    end.join(&self.state);
                }
                self.state = if arms.is_empty() { entry } else { end };
            }
            K::Throw(operand) => {
                if let Some(operand) = operand {
                    self.expression(operand);
                }
                self.state = State::unreachable(self.count());
            }
            K::SpillSequence { statements, value } => {
                for statement in statements {
                    self.statement(statement);
                }
                self.expression(value);
            }
            _ => each_child(expression, |child| self.expression(child)),
        }
    }
}

/// An expression without the conversions that only lift it into a `T?`.
fn unwrapped(expression: &BoundExpression) -> &BoundExpression {
    match &expression.kind {
        BoundExpressionKind::Conversion {
            operand,
            conversion: ConversionKind::NullableWrap | ConversionKind::Identity,
            ..
        } => unwrapped(operand),
        _ => expression,
    }
}

/// Whether an expression is a conditional access, perhaps converted to a
/// type that keeps its null a null (`(object)c?.M()`).
fn is_conditional_access(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::ConditionalAccess { .. } => true,
        BoundExpressionKind::Conversion {
            operand,
            conversion:
                ConversionKind::NullableWrap
                | ConversionKind::Identity
                | ConversionKind::Boxing
                | ConversionKind::ImplicitReference
                | ConversionKind::ExplicitReference,
            ..
        } => is_conditional_access(operand),
        _ => false,
    }
}

/// Whether an expression is `null`, however converted.
fn is_null_literal(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::Literal(ConstantValue::Null) => true,
        BoundExpressionKind::Conversion { operand, .. } => is_null_literal(operand),
        _ => false,
    }
}

/// The locals a pattern declares.
fn declared_by(pattern: &BoundPattern, out: &mut Vec<LocalId>) {
    match &pattern.kind {
        BoundPatternKind::Var { local }
        | BoundPatternKind::Declaration {
            local: Some(local), ..
        } => out.push(*local),
        BoundPatternKind::VarDeconstruct {
            local,
            deconstruction,
            ..
        } => {
            out.push(*local);
            written_locals(deconstruction, out);
        }
        BoundPatternKind::Recursive(recursive) => {
            out.extend(recursive.local);
            for (_, inner) in &recursive.properties {
                declared_by(inner, out);
            }
            for inner in &recursive.positional {
                declared_by(inner, out);
            }
        }
        BoundPatternKind::List(list) => {
            out.extend(list.local);
            for inner in list.patterns() {
                declared_by(inner, out);
            }
        }
        BoundPatternKind::And(left, right) | BoundPatternKind::Or(left, right) => {
            declared_by(left, out);
            declared_by(right, out);
        }
        BoundPatternKind::Not(inner) | BoundPatternKind::UnionCase { inner, .. } => {
            declared_by(inner, out);
        }
        _ => {}
    }
}

/// The locals an expression assigns, for the deconstruction a `var (a, b)`
/// pattern does.
fn written_locals(expression: &BoundExpression, out: &mut Vec<LocalId>) {
    match &expression.kind {
        BoundExpressionKind::Assignment { target, value } => {
            if let BoundExpressionKind::Local(local) = &target.kind {
                out.push(*local);
            }
            written_locals(value, out);
        }
        _ => each_child(expression, |child| written_locals(child, out)),
    }
}

/// Whether a pattern matches whatever it is given (`Some(true)`), nothing
/// at all (`Some(false)`), or depends on the value (`None`).
fn always_matches(
    pattern: &BoundPattern,
    input: Option<&Type>,
    non_null: bool,
    walk: &Walk<'_, '_>,
) -> Option<bool> {
    let may_be_null = |input: &Type| !non_null && walk.type_may_be_null(input);
    match &pattern.kind {
        BoundPatternKind::Var { .. } | BoundPatternKind::Discard => Some(true),
        // A type test of what can only be that type, and never null.
        BoundPatternKind::Type(ty) | BoundPatternKind::Declaration { ty, .. }
            if input.is_some_and(|input| input == ty && !may_be_null(input)) =>
        {
            Some(true)
        }
        BoundPatternKind::Not(inner) => {
            always_matches(inner, input, non_null, walk).map(|matches| !matches)
        }
        BoundPatternKind::And(left, right) => match (
            always_matches(left, input, non_null, walk),
            always_matches(right, input, non_null, walk),
        ) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            // `b is >= 0 and <= 255` on a `byte`.
            _ => takes_everything(pattern, input?, non_null, walk).then_some(true),
        },
        BoundPatternKind::Relational { .. } => {
            takes_everything(pattern, input?, non_null, walk).then_some(true)
        }
        BoundPatternKind::Or(left, right) => match (
            always_matches(left, input, non_null, walk),
            always_matches(right, input, non_null, walk),
        ) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            // `o is string or not string`, `ni is int or null`: neither side
            // takes everything, but together they take every value there is.
            _ => takes_everything(pattern, input?, non_null, walk).then_some(true),
        },
        // `s is Assignment(int left, var right)` on a struct: nothing is
        // tested — there is no null, no type to check, and `Deconstruct`
        // always hands its parts out — when every part always matches, so
        // what it declares is assigned after it (Roslyn warns CS8794).
        BoundPatternKind::Recursive(recursive) => {
            let input = input?;
            if may_be_null(input) || recursive.ty.as_ref().is_some_and(|ty| ty != input) {
                return None;
            }
            // `{ Length: int j }` reads each property, and matches where
            // every subpattern cannot fail on what the property is.
            let symbols = walk.binder.compilation().symbols();
            let properties_match = recursive.properties.iter().all(|(member, inner)| {
                let mut sink = crate::binder::Diagnostics::new();
                let ty = walk.binder.type_of(*member, &mut sink);
                symbols.get(*member).kind != crate::symbol::SymbolKind::Method
                    && always_matches(inner, Some(&ty), false, walk) == Some(true)
            });
            if !properties_match {
                return None;
            }
            if recursive.positional.is_empty() && recursive.deconstruct.is_none() {
                return Some(true);
            }
            let parts: Vec<Type> = match (recursive.deconstruct, input) {
                (None, Type::Tuple(elements)) => {
                    elements.iter().map(|element| element.ty.clone()).collect()
                }
                (Some(method), _) => {
                    let symbols = walk.binder.compilation().symbols();
                    let detail = symbols.get(method).as_method()?;
                    // An extension's receiver is not one of the parts.
                    let skip = usize::from(detail.is_extension);
                    let mut sink = crate::binder::Diagnostics::new();
                    detail
                        .parameters
                        .iter()
                        .skip(skip)
                        .map(
                            |parameter| match walk.binder.type_of(*parameter, &mut sink) {
                                Type::ByRef(inner) => *inner,
                                ty => ty,
                            },
                        )
                        .collect()
                }
                _ => return None,
            };
            if parts.len() != recursive.positional.len() {
                return None;
            }
            recursive
                .positional
                .iter()
                .zip(&parts)
                .all(|(part, ty)| always_matches(part, Some(ty), false, walk) == Some(true))
                .then_some(true)
        }
        _ => None,
    }
}

/// Whether a pattern is known to take every value of its input: null as well,
/// unless the input cannot be null or is known not to be.
fn takes_everything(
    pattern: &BoundPattern,
    input: &Type,
    non_null: bool,
    walk: &Walk<'_, '_>,
) -> bool {
    let may_be_null = !non_null && walk.type_may_be_null(input);
    let held = walk
        .binder
        .nullable_underlying(input)
        .unwrap_or_else(|| input.clone());
    // `nb is true or false or null` on a `bool?`.
    if walk.is_bool(&held)
        && let Some([yes, no, nothing]) = walk.bool_values(pattern)
    {
        return yes && no && (nothing || !may_be_null);
    }
    let reach = coverage(pattern, input, walk);
    (reach.null == Reach::All || !may_be_null) && reach.value == Reach::All
}

/// How much of one kind of value a pattern is known to take.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reach {
    /// Every value of the kind.
    All,
    /// No value of the kind.
    Nothing,
    /// Not known: some, or the analysis cannot tell.
    Unknown,
}

impl Reach {
    const fn negate(self) -> Self {
        match self {
            Self::All => Self::Nothing,
            Self::Nothing => Self::All,
            Self::Unknown => Self::Unknown,
        }
    }

    /// What both of two patterns taking a value says, `and`.
    const fn both(self, other: Self) -> Self {
        match (self, other) {
            (Self::Nothing, _) | (_, Self::Nothing) => Self::Nothing,
            (Self::All, Self::All) => Self::All,
            _ => Self::Unknown,
        }
    }

    /// What either of two patterns taking a value says, `or`.
    const fn either(self, other: Self) -> Self {
        match (self, other) {
            (Self::All, _) | (_, Self::All) => Self::All,
            (Self::Nothing, Self::Nothing) => Self::Nothing,
            _ => Self::Unknown,
        }
    }
}

/// What a pattern takes of the two kinds of value its input can hold: null,
/// and everything else.
#[derive(Clone, Copy)]
struct Coverage {
    null: Reach,
    value: Reach,
}

/// What `pattern` is known to take of an input of type `input`. Only what is
/// certain is said: a type test that takes every non-null value is the input's
/// own type or one it reaches by a reference or a boxing conversion, `null`
/// takes null and nothing else, and everything the analysis cannot place is
/// `Unknown`.
fn coverage(pattern: &BoundPattern, input: &Type, walk: &Walk<'_, '_>) -> Coverage {
    let unknown = Coverage {
        null: Reach::Unknown,
        value: Reach::Unknown,
    };
    match &pattern.kind {
        BoundPatternKind::Var { .. } | BoundPatternKind::Discard => Coverage {
            null: Reach::All,
            value: Reach::All,
        },
        BoundPatternKind::Type(ty) | BoundPatternKind::Declaration { ty, .. } => Coverage {
            null: Reach::Nothing,
            value: if takes_every_value(input, ty, walk) {
                Reach::All
            } else {
                Reach::Unknown
            },
        },
        BoundPatternKind::Constant(value) => match walk.binder.folded(value) {
            Some(ConstantValue::Null) => Coverage {
                null: Reach::All,
                value: Reach::Nothing,
            },
            Some(_) => Coverage {
                null: Reach::Nothing,
                value: Reach::Unknown,
            },
            None => unknown,
        },
        BoundPatternKind::Relational { .. } => Coverage {
            null: Reach::Nothing,
            value: takes_every_number(pattern, input, walk).unwrap_or(Reach::Unknown),
        },
        // `{ }` and a property pattern whose parts cannot fail take what is
        // not null, and `ni is { }` on an `int?` looks at the `int`.
        BoundPatternKind::Recursive(_) => {
            let held = walk
                .binder
                .nullable_underlying(input)
                .unwrap_or_else(|| input.clone());
            Coverage {
                null: Reach::Nothing,
                value: if always_matches(pattern, Some(&held), true, walk) == Some(true) {
                    Reach::All
                } else {
                    Reach::Unknown
                },
            }
        }
        BoundPatternKind::Not(inner) => {
            let inner = coverage(inner, input, walk);
            Coverage {
                null: inner.null.negate(),
                value: takes_every_number(pattern, input, walk).unwrap_or(inner.value.negate()),
            }
        }
        BoundPatternKind::And(left, right) => {
            let (left, right) = (coverage(left, input, walk), coverage(right, input, walk));
            Coverage {
                null: left.null.both(right.null),
                value: takes_every_number(pattern, input, walk)
                    .unwrap_or(left.value.both(right.value)),
            }
        }
        BoundPatternKind::Or(left, right) => {
            // A pattern and its negation take everything between them.
            let complement = |pattern: &BoundPattern, other: &BoundPattern| matches!(&pattern.kind, BoundPatternKind::Not(inner) if same_pattern(inner, other, walk));
            if complement(left, right) || complement(right, left) {
                return Coverage {
                    null: Reach::All,
                    value: Reach::All,
                };
            }
            // `{ Next: null } or { Next: not null }`: one property read, and
            // what is found in it taken whole by the two patterns together.
            if splits_a_property(left, right, input, walk) {
                return Coverage {
                    null: Reach::Nothing,
                    value: Reach::All,
                };
            }
            let (left, right) = (coverage(left, input, walk), coverage(right, input, walk));
            Coverage {
                null: left.null.either(right.null),
                value: takes_every_number(pattern, input, walk)
                    .unwrap_or(left.value.either(right.value)),
            }
        }
        _ => unknown,
    }
}

/// `All` where the numbers a pattern takes of an integral input cover its
/// whole range, as in `n is < 0 or >= 0` or `b is not (> 0 and < 255)`:
/// the patterns are sets of ranges, which are worked out exactly. `None` where
/// that does not settle it, and so says nothing against what is known
/// otherwise.
fn takes_every_number(pattern: &BoundPattern, input: &Type, walk: &Walk<'_, '_>) -> Option<Reach> {
    let held = walk
        .binder
        .nullable_underlying(input)
        .unwrap_or_else(|| input.clone());
    let range = match walk.binder.special_of(&held)? {
        SpecialType::SByte => (i128::from(i8::MIN), i128::from(i8::MAX)),
        SpecialType::Byte => (0, i128::from(u8::MAX)),
        SpecialType::Int16 => (i128::from(i16::MIN), i128::from(i16::MAX)),
        SpecialType::UInt16 | SpecialType::Char => (0, i128::from(u16::MAX)),
        SpecialType::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
        SpecialType::UInt32 => (0, i128::from(u32::MAX)),
        SpecialType::Int64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
        SpecialType::UInt64 => (0, i128::from(u64::MAX)),
        _ => return None,
    };
    let taken = numbers_taken(pattern, &held, range, walk)?;
    (taken == [range]).then_some(Reach::All)
}

/// The ranges of numbers, in order and apart, that a pattern takes of the
/// values of `held` between `range.0` and `range.1`.
fn numbers_taken(
    pattern: &BoundPattern,
    held: &Type,
    range: (i128, i128),
    walk: &Walk<'_, '_>,
) -> Option<Vec<(i128, i128)>> {
    let number = |value: &BoundExpression| crate::constant::as_exact(&walk.binder.folded(value)?);
    let (low, high) = range;
    Some(match &pattern.kind {
        BoundPatternKind::Var { .. } | BoundPatternKind::Discard => vec![range],
        BoundPatternKind::Type(ty) | BoundPatternKind::Declaration { ty, .. } if ty == held => {
            vec![range]
        }
        BoundPatternKind::Constant(value) => match walk.binder.folded(value)? {
            ConstantValue::Null => Vec::new(),
            other => {
                let at = crate::constant::as_exact(&other)?;
                if (low..=high).contains(&at) {
                    vec![(at, at)]
                } else {
                    Vec::new()
                }
            }
        },
        BoundPatternKind::Relational { operator, value } => {
            let at = number(value)?;
            let (from, to) = match operator {
                BinaryOperator::LessThan => (low, at.checked_sub(1)?),
                BinaryOperator::LessThanOrEqual => (low, at),
                BinaryOperator::GreaterThan => (at.checked_add(1)?, high),
                BinaryOperator::GreaterThanOrEqual => (at, high),
                _ => return None,
            };
            let (from, to) = (from.max(low), to.min(high));
            if from <= to {
                vec![(from, to)]
            } else {
                Vec::new()
            }
        }
        BoundPatternKind::Not(inner) => {
            let taken = numbers_taken(inner, held, range, walk)?;
            let mut rest = Vec::new();
            let mut next = low;
            for (from, to) in taken {
                if from > next {
                    rest.push((next, from - 1));
                }
                next = to + 1;
            }
            if next <= high {
                rest.push((next, high));
            }
            rest
        }
        BoundPatternKind::Or(left, right) => {
            let mut all = numbers_taken(left, held, range, walk)?;
            all.extend(numbers_taken(right, held, range, walk)?);
            all.sort_unstable();
            let mut merged: Vec<(i128, i128)> = Vec::new();
            for (from, to) in all {
                match merged.last_mut() {
                    Some(last) if from <= last.1 + 1 => last.1 = last.1.max(to),
                    _ => merged.push((from, to)),
                }
            }
            merged
        }
        BoundPatternKind::And(left, right) => {
            let (left, right) = (
                numbers_taken(left, held, range, walk)?,
                numbers_taken(right, held, range, walk)?,
            );
            let mut both = Vec::new();
            for (a, b) in &left {
                for (c, d) in &right {
                    let (from, to) = ((*a).max(*c), (*b).min(*d));
                    if from <= to {
                        both.push((from, to));
                    }
                }
            }
            both.sort_unstable();
            both
        }
        _ => return None,
    })
}

/// Whether two property patterns read the same one property, and between them
/// take every value it has.
fn splits_a_property(
    first: &BoundPattern,
    second: &BoundPattern,
    input: &Type,
    walk: &Walk<'_, '_>,
) -> bool {
    let (BoundPatternKind::Recursive(first), BoundPatternKind::Recursive(second)) =
        (&first.kind, &second.kind)
    else {
        return false;
    };
    let held = walk
        .binder
        .nullable_underlying(input)
        .unwrap_or_else(|| input.clone());
    let plain = |pattern: &crate::bound::BoundRecursivePattern| {
        pattern.positional.is_empty()
            && pattern.deconstruct.is_none()
            && pattern.properties.len() == 1
            && pattern.ty.as_ref().is_none_or(|ty| *ty == held)
    };
    if !plain(first) || !plain(second) || first.properties[0].0 != second.properties[0].0 {
        return false;
    }
    let member = first.properties[0].0;
    let symbols = walk.binder.compilation().symbols();
    if symbols.get(member).kind == crate::symbol::SymbolKind::Method {
        return false;
    }
    let mut sink = crate::binder::Diagnostics::new();
    let ty = walk.binder.type_of(member, &mut sink);
    let either = BoundPattern::new(
        BoundPatternKind::Or(
            Box::new(first.properties[0].1.clone()),
            Box::new(second.properties[0].1.clone()),
        ),
        first.properties[0].1.span,
    );
    takes_everything(&either, &ty, false, walk)
}

/// Whether a test for `tested` is passed by every value of `input` that is not
/// null: the type itself, the type under a `T?`, or a base class or interface
/// of it, `object` among them. A number widening or an operator is no such
/// conversion, and `int?` as a pattern is not the type under it.
fn takes_every_value(input: &Type, tested: &Type, walk: &Walk<'_, '_>) -> bool {
    if walk.binder.nullable_underlying(tested).is_some() {
        return false;
    }
    let held = walk
        .binder
        .nullable_underlying(input)
        .unwrap_or_else(|| input.clone());
    if held.is_error() || tested.is_error() {
        return false;
    }
    if held == *tested {
        return true;
    }
    // A base class or an interface of the type, as written: a conversion an
    // operator makes is no such thing, and neither is a number widening.
    matches!(tested, Type::Named { .. })
        && !matches!(
            held,
            Type::TypeParameter(_) | Type::Pointer(_) | Type::Dynamic
        )
        && tested.symbol().is_some_and(|symbol| {
            walk.binder.constructed_from(&held, symbol).as_ref() == Some(tested)
        })
}

/// Whether two patterns test for the same thing, as far as they can be told
/// apart without looking inside a property or positional pattern.
fn same_pattern(first: &BoundPattern, second: &BoundPattern, walk: &Walk<'_, '_>) -> bool {
    match (&first.kind, &second.kind) {
        (
            BoundPatternKind::Type(a) | BoundPatternKind::Declaration { ty: a, .. },
            BoundPatternKind::Type(b) | BoundPatternKind::Declaration { ty: b, .. },
        ) => a == b && !a.is_error(),
        (BoundPatternKind::Constant(a), BoundPatternKind::Constant(b)) => {
            match (walk.binder.folded(a), walk.binder.folded(b)) {
                (Some(a), Some(b)) => a == b,
                _ => false,
            }
        }
        (
            BoundPatternKind::Relational {
                operator: a,
                value: x,
            },
            BoundPatternKind::Relational {
                operator: b,
                value: y,
            },
        ) => {
            a == b
                && match (walk.binder.folded(x), walk.binder.folded(y)) {
                    (Some(x), Some(y)) => x == y,
                    _ => false,
                }
        }
        (BoundPatternKind::Not(a), BoundPatternKind::Not(b)) => same_pattern(a, b, walk),
        (BoundPatternKind::And(a, b), BoundPatternKind::And(c, d))
        | (BoundPatternKind::Or(a, b), BoundPatternKind::Or(c, d)) => {
            same_pattern(a, c, walk) && same_pattern(b, d, walk)
        }
        _ => false,
    }
}

/// The locals a pattern assigns where it matches, and where it does not.
fn assigned_by(pattern: &BoundPattern) -> (Vec<LocalId>, Vec<LocalId>) {
    match &pattern.kind {
        BoundPatternKind::Not(inner) => {
            let (on_match, on_mismatch) = assigned_by(inner);
            (on_mismatch, on_match)
        }
        BoundPatternKind::And(left, right) => {
            let (mut on_match, left_mismatch) = assigned_by(left);
            let (right_match, right_mismatch) = assigned_by(right);
            // `a and b` fails where `a` fails, or where `a` matched and `b`
            // failed.
            let mismatch = left_mismatch
                .iter()
                .copied()
                .filter(|local| on_match.contains(local) || right_mismatch.contains(local))
                .collect();
            on_match.extend(right_match);
            (on_match, mismatch)
        }
        BoundPatternKind::Or(left, right) => {
            let (left_match, mut on_mismatch) = assigned_by(left);
            let (right_match, right_mismatch) = assigned_by(right);
            let matched = left_match
                .iter()
                .copied()
                .filter(|local| on_mismatch.contains(local) || right_match.contains(local))
                .collect();
            on_mismatch.extend(right_mismatch);
            (matched, on_mismatch)
        }
        _ => {
            let mut declared = Vec::new();
            declared_by(pattern, &mut declared);
            (declared, Vec::new())
        }
    }
}
