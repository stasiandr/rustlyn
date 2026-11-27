//! Running bound statements, and matching bound patterns.

use rustlyn_semantics::{
    BoundBody, BoundEnumeration, BoundExpression, BoundExpressionKind, BoundPattern,
    BoundPatternKind, BoundStatement, BoundStatementKind, BoundSwitchLabel, BoundUsingResource,
    ConstantValue, Type,
};

use crate::interpreter::{Eval, Flow, Frame, Interpreter, Outcome, Signal};
use crate::value::Value;

impl Interpreter<'_> {
    pub(crate) fn exec(
        &mut self,
        body: &BoundBody,
        statement: &BoundStatement,
        frame: &mut Frame,
    ) -> Outcome {
        match &statement.kind {
            BoundStatementKind::Empty => Ok(Flow::Normal),
            BoundStatementKind::Block(statements) => self.run_statements(body, statements, frame),
            BoundStatementKind::LocalDeclaration { local, initializer } => {
                let value = match initializer {
                    Some(initializer) => self.eval(body, initializer, frame)?,
                    None => Value::Null,
                };
                frame.set_local(*local, value);
                Ok(Flow::Normal)
            }
            BoundStatementKind::Expression(expression) => {
                self.eval(body, expression, frame)?;
                Ok(Flow::Normal)
            }
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                if self.condition(body, condition, frame)? {
                    self.exec(body, consequence, frame)
                } else {
                    match alternative {
                        Some(alternative) => self.exec(body, alternative, frame),
                        None => Ok(Flow::Normal),
                    }
                }
            }
            BoundStatementKind::While {
                condition,
                body: inner,
            } => {
                while self.condition(body, condition, frame)? {
                    match self.exec(body, inner, frame)? {
                        Flow::Break(0) => break,
                        Flow::Break(outward) => return Ok(Flow::Break(outward - 1)),
                        Flow::Continue(outward) if outward > 0 => {
                            return Ok(Flow::Continue(outward - 1));
                        }
                        Flow::Return(value) => return Ok(Flow::Return(value)),
                        _ => {}
                    }
                }
                Ok(Flow::Normal)
            }
            BoundStatementKind::DoWhile {
                body: inner,
                condition,
            } => {
                loop {
                    match self.exec(body, inner, frame)? {
                        Flow::Break(0) => break,
                        Flow::Break(outward) => return Ok(Flow::Break(outward - 1)),
                        Flow::Continue(outward) if outward > 0 => {
                            return Ok(Flow::Continue(outward - 1));
                        }
                        Flow::Return(value) => return Ok(Flow::Return(value)),
                        _ => {}
                    }
                    if !self.condition(body, condition, frame)? {
                        break;
                    }
                }
                Ok(Flow::Normal)
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body: inner,
            } => {
                for initializer in initializers {
                    self.exec(body, initializer, frame)?;
                }
                loop {
                    if let Some(condition) = condition
                        && !self.condition(body, condition, frame)?
                    {
                        break;
                    }
                    match self.exec(body, inner, frame)? {
                        Flow::Break(0) => break,
                        Flow::Break(outward) => return Ok(Flow::Break(outward - 1)),
                        Flow::Continue(outward) if outward > 0 => {
                            return Ok(Flow::Continue(outward - 1));
                        }
                        Flow::Return(value) => return Ok(Flow::Return(value)),
                        _ => {}
                    }
                    for incrementor in incrementors {
                        self.eval(body, incrementor, frame)?;
                    }
                }
                Ok(Flow::Normal)
            }
            BoundStatementKind::ForEach {
                local,
                collection,
                body: inner,
                enumeration,
                walk: _,
                dimensions: _,
                conversion: _,
            } => {
                let collection = self.eval(body, collection, frame)?;
                // A collection the interpreter provides is walked directly;
                // one declared in source is asked for an enumerator, because
                // there is nothing else to ask.
                let items = match enumeration {
                    Some(enumeration) if !is_built_in_collection(&collection) => {
                        // What a `ref struct`'s own `Dispose` is given: the
                        // defaults of its parameters, an `in` one's as the
                        // value it is.
                        let dispose_arguments = enumeration
                            .dispose_arguments
                            .iter()
                            .map(|argument| {
                                let value = match &argument.kind {
                                    BoundExpressionKind::RefArgument { operand, .. } => operand,
                                    _ => argument,
                                };
                                self.eval(body, value, frame)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        self.enumerate(collection, enumeration, dispose_arguments)?
                    }
                    _ => self.items_of(collection)?,
                };
                for item in items {
                    frame.set_local(*local, item);
                    match self.exec(body, inner, frame)? {
                        Flow::Break(0) => break,
                        Flow::Break(outward) => return Ok(Flow::Break(outward - 1)),
                        Flow::Continue(outward) if outward > 0 => {
                            return Ok(Flow::Continue(outward - 1));
                        }
                        Flow::Return(value) => return Ok(Flow::Return(value)),
                        _ => {}
                    }
                }
                Ok(Flow::Normal)
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => {
                let value = self.eval(body, governing, frame)?;
                // Every label is tried in order, and `default` is only used
                // once nothing else matched, wherever it was written.
                let mut chosen = None;
                let mut fallback = None;
                'sections: for (index, section) in sections.iter().enumerate() {
                    for label in &section.labels {
                        match label {
                            BoundSwitchLabel::Default => fallback = fallback.or(Some(index)),
                            BoundSwitchLabel::Case(case) => {
                                if self.matches(body, &case.pattern, &value, frame)?
                                    && match &case.when {
                                        Some(when) => self.condition(body, when, frame)?,
                                        None => true,
                                    }
                                {
                                    chosen = Some(index);
                                    break 'sections;
                                }
                            }
                        }
                    }
                }
                match chosen.or(fallback) {
                    Some(index) => {
                        match self.run_statements(body, &sections[index].statements, frame)? {
                            // `break` leaves the switch and stops there;
                            // `continue` is not about the switch at all and
                            // has to reach the loop around it.
                            Flow::Break(0) | Flow::Normal => Ok(Flow::Normal),
                            Flow::Break(outward) => Ok(Flow::Break(outward - 1)),
                            other => Ok(other),
                        }
                    }
                    None => Ok(Flow::Normal),
                }
            }
            BoundStatementKind::Try {
                body: protected,
                catches,
                finally,
            } => {
                let mut result = self.exec(body, protected, frame);
                if let Err(Signal::Thrown(thrown)) = &result {
                    let thrown = thrown.clone();
                    for catch in catches {
                        if !self.catches(&catch.exception_type, &thrown) {
                            continue;
                        }
                        if let Some(local) = catch.local {
                            frame.set_local(local, thrown.clone());
                        }
                        if let Some(filter) = &catch.filter
                            && !self.condition(body, filter, frame)?
                        {
                            continue;
                        }
                        result = self.exec(body, &catch.body, frame);
                        break;
                    }
                }
                // The `finally` runs however the region was left, and a
                // failure inside it replaces whatever was on its way out.
                if let Some(finally) = finally {
                    match self.exec(body, finally, frame) {
                        Ok(Flow::Normal) => {}
                        other => return other,
                    }
                }
                result
            }
            BoundStatementKind::Using {
                resources,
                body: inner,
            } => self.exec_using(body, resources, inner, frame),
            BoundStatementKind::Return(value) => match value {
                Some(value) => {
                    let value = self.eval(body, value, frame)?;
                    Ok(Flow::Return(value))
                }
                None => Ok(Flow::Return(Value::Null)),
            },
            // One thread, so taking the lock is nothing; the body is the
            // whole of it.
            BoundStatementKind::Lock { body: locked, .. } => self.exec(body, locked, frame),
            BoundStatementKind::Fixed { .. } => Err(Signal::fault(
                "`fixed` pins memory, which this backend has none of",
            )),
            BoundStatementKind::GotoCase(_) => Err(Signal::fault(
                "`goto case` jumps between the sections of a switch, which is not walked here",
            )),
            // A label is nothing to walk past; a `goto` is a jump this
            // interpreter has no way to make, because it walks the tree
            // rather than a list of instructions.
            BoundStatementKind::Label(_) => Ok(Flow::Normal),
            BoundStatementKind::Goto(name) => Err(Signal::fault(format!(
                "`goto {name}` needs instructions to jump between, and this walks the tree"
            ))),
            BoundStatementKind::Break(outward) => Ok(Flow::Break(*outward)),
            BoundStatementKind::Continue(outward) => Ok(Flow::Continue(*outward)),
            BoundStatementKind::Throw(value) => {
                let value = match value {
                    Some(value) => self.eval(body, value, frame)?,
                    None => Value::Null,
                };
                Err(Signal::Thrown(value))
            }
            BoundStatementKind::ConstructorInitializer {
                constructor,
                arguments,
                ..
            } => {
                let Some(constructor) = constructor else {
                    return Ok(Flow::Normal);
                };
                let mut values = Vec::new();
                for argument in arguments {
                    values.push(self.eval(body, argument, frame)?);
                }
                let this = frame.this.clone();
                self.run_constructor_body(*constructor, this, values)?;
                Ok(Flow::Normal)
            }
            // An iterator is a state machine, which is a rewriting of the
            // whole method rather than anything a statement-at-a-time walk
            // can do.
            BoundStatementKind::YieldReturn(_) | BoundStatementKind::YieldBreak => Err(
                Signal::fault("an iterator cannot be run a statement at a time"),
            ),
            BoundStatementKind::Unsupported(kind) => {
                Err(Signal::fault(format!("{kind:?} is not supported")))
            }
        }
    }

    /// A `using`: acquire, run, dispose — and dispose however the body ended,
    /// including when it threw.
    ///
    /// Several resources nest, so the second is disposed before the first.
    fn exec_using(
        &mut self,
        body: &BoundBody,
        resources: &[BoundUsingResource],
        inner: &BoundStatement,
        frame: &mut Frame,
    ) -> Outcome {
        let Some((first, rest)) = resources.split_first() else {
            return self.exec(body, inner, frame);
        };
        let value = self.eval(body, &first.value, frame)?;
        frame.set_local(first.local, value.clone());

        let result = self.exec_using(body, rest, inner, frame);

        if let Some(dispose) = first.dispose
            && !matches!(value, Value::Null)
        {
            // `Dispose` is reached through the run-time type, as any call
            // through an interface is.
            let target = match &value {
                Value::Object(object) => {
                    let runtime = object.borrow().ty;
                    self.most_derived(dispose, runtime)
                }
                _ => dispose,
            };
            self.call_method(target, Some(value), Vec::new())?;
        }
        result
    }

    pub(crate) fn condition(
        &mut self,
        body: &BoundBody,
        expression: &BoundExpression,
        frame: &mut Frame,
    ) -> Result<bool, Signal> {
        match self.eval(body, expression, frame)? {
            Value::Bool(value) => Ok(value),
            other => Err(Signal::fault(format!(
                "a condition needs a bool, not {}",
                other.display()
            ))),
        }
    }

    /// What a `foreach` walks.
    /// Walks a collection through the enumerator the binder found.
    ///
    /// The whole run is collected up front rather than stepped through, which
    /// is the one place the interpreter is not what the IL does: the loop body
    /// here cannot change what the enumerator would yield next. Nothing in the
    /// subset can make that difference visible, and saying so beats pretending
    /// otherwise.
    fn enumerate(
        &mut self,
        collection: Value,
        enumeration: &BoundEnumeration,
        dispose_arguments: Vec<Value>,
    ) -> Result<Vec<Value>, Signal> {
        let enumerator =
            self.call_method(enumeration.get_enumerator, Some(collection), Vec::new())?;
        let mut items = Vec::new();
        // A runaway enumerator is stopped rather than allowed to hang.
        for _ in 0..MAX_ITERATIONS {
            let more =
                self.call_method(enumeration.move_next, Some(enumerator.clone()), Vec::new())?;
            if more.as_bool() != Some(true) {
                break;
            }
            items.push(self.read_property(enumeration.current, Some(enumerator.clone()))?);
        }
        if let Some(dispose) = enumeration.dispose {
            // Through the run-time type; where the static type made no
            // promise, a value without a `Dispose` is left alone.
            let target = match &enumerator {
                Value::Object(object) => {
                    let runtime = object.borrow().ty;
                    self.most_derived(dispose, runtime)
                }
                _ => dispose,
            };
            if !(enumeration.dispose_checked && target == dispose) {
                self.call_method(target, Some(enumerator), dispose_arguments)?;
            }
        }
        Ok(items)
    }

    fn items_of(&self, value: Value) -> Result<Vec<Value>, Signal> {
        Ok(match value {
            Value::Array(items) | Value::List(items) => items.borrow().clone(),
            Value::Str(text) => text.chars().map(Value::Char).collect(),
            other => {
                return Err(Signal::fault(format!(
                    "{} cannot be iterated",
                    other.display()
                )));
            }
        })
    }

    /// Whether a `catch` of this type takes the exception.
    fn catches(&self, declared: &Type, thrown: &Value) -> bool {
        let Some(declared) = declared.symbol() else {
            return true;
        };
        let name = self.compilation().symbols().qualified_name(declared);
        // A `catch (Exception)` takes everything, which includes the strings
        // the interpreter throws for its own faults.
        if name == "System.Exception" || name == "System.Object" {
            return true;
        }
        match thrown {
            Value::Object(object) => {
                let runtime = object.borrow().ty;
                self.type_hierarchy(runtime).contains(&declared)
            }
            _ => false,
        }
    }

    // -- patterns ----------------------------------------------------------

    /// Whether a value matches a pattern, binding what the pattern names.
    pub(crate) fn matches(
        &mut self,
        body: &BoundBody,
        pattern: &BoundPattern,
        value: &Value,
        frame: &mut Frame,
    ) -> Result<bool, Signal> {
        match &pattern.kind {
            BoundPatternKind::Discard => Ok(true),
            BoundPatternKind::Var { local } => {
                frame.set_local(*local, value.clone());
                Ok(true)
            }
            BoundPatternKind::VarDeconstruct {
                local,
                deconstruction,
                ..
            } => {
                if matches!(value, Value::Null) {
                    return Ok(false);
                }
                frame.set_local(*local, value.clone());
                self.eval(body, deconstruction, frame)?;
                Ok(true)
            }
            BoundPatternKind::Type(target) => Ok(self.is_of_type(value, target)),
            BoundPatternKind::Declaration { ty, local } => {
                if !self.is_of_type(value, ty) {
                    return Ok(false);
                }
                if let Some(local) = local {
                    frame.set_local(*local, value.clone());
                }
                Ok(true)
            }
            BoundPatternKind::Constant(constant) => {
                if matches!(constant.constant(), Some(ConstantValue::Null)) {
                    return Ok(matches!(value, Value::Null));
                }
                let expected = self.eval(body, constant, frame)?;
                Ok(value.equals(&expected))
            }
            BoundPatternKind::Relational {
                operator,
                value: bound,
            } => {
                let expected = self.eval(body, bound, frame)?;
                match self.apply(*operator, value, &expected)? {
                    Value::Bool(result) => Ok(result),
                    _ => Ok(false),
                }
            }
            // The type test and the name it binds are here; reading members
            // off the value and taking it apart are not, and saying so beats
            // matching half a pattern and calling it a match.
            BoundPatternKind::Recursive(recursive) => {
                if !recursive.properties.is_empty() || !recursive.positional.is_empty() {
                    return Err(Signal::fault(
                        "a pattern that reads members or takes a value apart is not walked here",
                    ));
                }
                if let Some(ty) = &recursive.ty
                    && !self.is_of_type(value, ty)
                {
                    return Ok(false);
                }
                if let Some(local) = recursive.local {
                    frame.set_local(local, value.clone());
                }
                Ok(true)
            }
            BoundPatternKind::And(left, right) => Ok(self.matches(body, left, value, frame)?
                && self.matches(body, right, value, frame)?),
            BoundPatternKind::Or(left, right) => Ok(self.matches(body, left, value, frame)?
                || self.matches(body, right, value, frame)?),
            BoundPatternKind::Not(inner) => Ok(!self.matches(body, inner, value, frame)?),
            // A list pattern reads a length and an indexer off the value,
            // which this walk has no way to ask for.
            BoundPatternKind::List(_) => Err(Signal::fault(
                "a list pattern is not supported by the interpreter",
            )),
            BoundPatternKind::UnionCase { .. } => Err(Signal::fault(
                "a union's `TryGetValue` is not called by the interpreter",
            )),
            BoundPatternKind::SpanString { .. } => Err(Signal::fault(
                "a span is not compared with a string by the interpreter",
            )),
            BoundPatternKind::Unsupported(kind) => Err(Signal::fault(format!(
                "the pattern {kind:?} is not supported"
            ))),
        }
    }

    /// Whether a value would answer yes to `is T`.
    pub(crate) fn is_of_type(&self, value: &Value, target: &Type) -> bool {
        let symbols = self.compilation().symbols();
        let Some(target) = target.symbol() else {
            // `T[]`, which only an array can be.
            return matches!(value, Value::Array(_));
        };
        let name = symbols.qualified_name(target);
        match value {
            Value::Null => false,
            Value::Object(object) => {
                name == "System.Object" || self.type_hierarchy(object.borrow().ty).contains(&target)
            }
            Value::Bool(_) => matches!(name.as_str(), "System.Boolean" | "System.Object"),
            Value::Char(_) => matches!(name.as_str(), "System.Char" | "System.Object"),
            Value::Str(_) => matches!(name.as_str(), "System.String" | "System.Object"),
            Value::Double(_) => matches!(
                name.as_str(),
                "System.Double" | "System.Single" | "System.Object"
            ),
            // Every integral type is held the same way, so the best this can
            // do is say whether the target is one of them.
            Value::Int(_) => matches!(
                name.as_str(),
                "System.Int32"
                    | "System.Int64"
                    | "System.Int16"
                    | "System.SByte"
                    | "System.Byte"
                    | "System.UInt16"
                    | "System.UInt32"
                    | "System.UInt64"
                    | "System.Object"
            ),
            Value::Array(_) | Value::List(_) => name == "System.Object" || name.contains("List"),
            Value::Map(_) => name == "System.Object" || name.contains("Dictionary"),
            // A boxed enum knows which enum it is, so `is Colour` can answer.
            Value::Enumeration { ty, .. } => {
                *ty == target
                    || matches!(
                        name.as_str(),
                        "System.Object" | "System.Enum" | "System.ValueType"
                    )
            }
            // A delegate's run-time type is the delegate type it was made as,
            // which the interpreter does not keep: it holds a target and a
            // method, the way the runtime does.
            // A reference is not a value, so it is not an instance of
            // anything a `is` could ask about.
            Value::Reference(_) => false,
            Value::Closure(_) | Value::Delegate { .. } => {
                matches!(
                    name.as_str(),
                    "System.Object" | "System.Delegate" | "System.MulticastDelegate"
                )
            }
        }
    }

    /// Evaluates an expression with a frame of its own, for the places that
    /// need a value before any method is running: a field's initializer.
    pub(crate) fn eval_detached(
        &mut self,
        body: &BoundBody,
        expression: &BoundExpression,
        this: Option<Value>,
    ) -> Eval {
        let mut frame = Frame::new(this, body.locals.len());
        self.eval(body, expression, &mut frame)
    }
}

/// Whether the interpreter provides this collection itself, in which case it
/// walks it directly rather than asking it for an enumerator it has no body
/// for.
fn is_built_in_collection(value: &Value) -> bool {
    matches!(
        value,
        Value::Array(_) | Value::List(_) | Value::Map(_) | Value::Str(_)
    )
}

/// How many times an enumerator may answer `true` before the interpreter gives
/// up, for the same reason the call depth is capped: to report a runaway loop
/// rather than hang.
const MAX_ITERATIONS: usize = 1_000_000;
