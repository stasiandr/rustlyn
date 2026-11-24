//! Evaluating bound expressions.
//!
//! Every question a tree-walker would normally ask — which method, which
//! field, which conversion — has already been answered, so this is mostly a
//! matter of carrying out decisions. The one thing it does decide is which
//! *override* a virtual call reaches, because that depends on the run-time
//! type of the receiver and nothing before run time could know it.

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundExpression, BoundExpressionKind, ConstantValue, ConversionKind,
    IncrementOperator, LocalId, Modifiers, SpecialType, SymbolId, Type, UnaryOperator,
};

use crate::interpreter::{Eval, Flow, Frame, Interpreter, Signal};
use crate::value::{Reference, Value};

/// Somewhere a value can be written back to.
pub(crate) enum Place {
    Local(LocalId),
    Argument(SymbolId),
    Field {
        receiver: Option<Value>,
        field: SymbolId,
    },
    Property {
        receiver: Option<Value>,
        property: SymbolId,
    },
    Element {
        collection: Value,
        /// The index or key, as a value: an array wants an integer, a
        /// dictionary wants whatever its key type is.
        index: Value,
    },
    /// An indexer declared in source, which is two methods rather than
    /// storage. The built-in collections are not this: the interpreter
    /// provides them, so they are `Element`.
    Indexer {
        receiver: Option<Value>,
        indexer: SymbolId,
        arguments: Vec<Value>,
    },
}

impl Interpreter<'_> {
    /// Runs an object or collection initializer against the object it made.
    fn run_initializers(
        &mut self,
        body: &BoundBody,
        initializers: &[BoundExpression],
        instance: &Value,
        frame: &mut Frame,
    ) -> Result<(), Signal> {
        if initializers.is_empty() {
            return Ok(());
        }
        self.creating.push(instance.clone());
        let mut result = Ok(());
        for initializer in initializers {
            if let Err(signal) = self.eval(body, initializer, frame) {
                result = Err(signal);
                break;
            }
        }
        self.creating.pop();
        result
    }

    pub(crate) fn eval(
        &mut self,
        body: &BoundBody,
        expression: &BoundExpression,
        frame: &mut Frame,
    ) -> Eval {
        match &expression.kind {
            BoundExpressionKind::Literal(value) => Ok(runtime_value(value)),
            // A `ref` local holds a reference, and reading the name reads
            // through it — the same as a `ref` parameter, for the same reason.
            BoundExpressionKind::Local(local) => {
                let value = frame.local(*local);
                Ok(self.through(value))
            }
            // A `ref` parameter holds a reference, and reading it reads what
            // that reference points at.
            BoundExpressionKind::Parameter(parameter) => {
                Ok(self.through(frame.argument(*parameter)))
            }
            BoundExpressionKind::This | BoundExpressionKind::Base => {
                Ok(frame.this.clone().unwrap_or(Value::Null))
            }
            // `a?.B` evaluates `a` once and stops there when it is null.
            BoundExpressionKind::ConditionalAccess { receiver, access } => {
                let value = self.eval(body, receiver, frame)?;
                if matches!(value, Value::Null) {
                    return Ok(self.zero_of(&expression.ty));
                }
                self.accessed.push(value);
                let result = self.eval(body, access, frame);
                self.accessed.pop();
                result
            }
            BoundExpressionKind::AccessedValue => self
                .accessed
                .last()
                .cloned()
                .ok_or_else(|| Signal::fault("a `?.` access with no receiver")),
            BoundExpressionKind::Field { receiver, field } => {
                let receiver = self.eval_receiver(body, receiver.as_deref(), frame)?;
                self.read_field(*field, receiver)
            }
            BoundExpressionKind::Property { receiver, property } => {
                let receiver = self.eval_receiver(body, receiver.as_deref(), frame)?;
                self.read_property(*property, receiver)
            }
            // The type arguments are the emitter's business: the interpreter
            // holds values, not signatures, so `Echo<int>` and `Echo<string>`
            // run the same body.
            // `ref x` hands over the variable, not what it holds.
            BoundExpressionKind::RefArgument { operand, .. } => {
                let reference = self.reference_to(body, operand, frame)?;
                Ok(Value::Reference(std::rc::Rc::new(reference)))
            }
            BoundExpressionKind::UnboundLambda(_) => Err(Signal::fault(
                "a lambda has no type until it is converted to a delegate",
            )),
            BoundExpressionKind::UnboundCollection(_) => Err(Signal::fault(
                "a collection expression has no type until something says what it is",
            )),
            BoundExpressionKind::UnboundCreation(_) => Err(Signal::fault(
                "`new(...)` has no type until something says what is being made",
            )),
            BoundExpressionKind::UnboundConditional(_) => Err(Signal::fault(
                "`c ? a : b` has no type until something says what its branches are",
            )),
            BoundExpressionKind::UnboundSwitch(_) => Err(Signal::fault(
                "a `switch` expression has no type until something says what its arms are",
            )),
            BoundExpressionKind::Lambda(index) => {
                let Some(lambda) = body.lambdas.get(*index) else {
                    return Err(Signal::fault("a lambda with no body"));
                };
                // The lambda keeps a locals table of its own, because it
                // outlives the method it was written in: the delegate can be
                // called long after that method returned. A lambda inside this
                // one is still found by index, so the whole list comes along.
                let owned = BoundBody {
                    locals: body.locals.clone(),
                    statements: vec![lambda.body.clone()],
                    lambdas: body.lambdas.clone(),
                    ..BoundBody::default()
                };
                frame.ensure_locals(owned.locals.len());
                Ok(Value::Closure(std::rc::Rc::new(crate::value::Closure {
                    parameters: lambda.parameters.clone(),
                    body: std::rc::Rc::new(owned),
                    frame: frame.clone(),
                })))
            }
            BoundExpressionKind::DelegateCreation {
                method,
                receiver,
                virtual_dispatch,
                ..
            } => {
                let receiver = self.eval_receiver(body, receiver.as_deref(), frame)?;
                // `ldvirtftn` settles the override *when the delegate is
                // made*, from the receiver it is made with — not when it is
                // called. A delegate made from `Shape s = new Square()` calls
                // `Square.Name` ever after.
                let method = match (*virtual_dispatch, &receiver) {
                    (true, Some(Value::Object(object))) => {
                        let runtime = object.borrow().ty;
                        self.most_derived(*method, runtime)
                    }
                    _ => *method,
                };
                Ok(Value::Delegate {
                    method,
                    receiver: receiver.map(std::rc::Rc::new),
                })
            }
            BoundExpressionKind::MethodGroup { .. } => Err(Signal::fault(
                "a method group is not a value until it is converted to a delegate",
            )),
            BoundExpressionKind::Call {
                receiver,
                method,
                arguments,
                virtual_call,
                ..
            } => {
                let receiver = self.eval_receiver(body, receiver.as_deref(), frame)?;
                // Calling a delegate's `Invoke` reaches whatever the delegate
                // was made from; the runtime provides that body, so nothing
                // else can.
                if let Some(Value::Closure(closure)) = &receiver {
                    let closure = std::rc::Rc::clone(closure);
                    let mut values = Vec::with_capacity(arguments.len());
                    for argument in arguments {
                        values.push(self.eval(body, argument, frame)?);
                    }
                    return self.call_closure(&closure, values);
                }
                if let Some(Value::Delegate {
                    method: target,
                    receiver: held,
                }) = &receiver
                {
                    let (target, held) = (*target, held.clone());
                    let mut values = Vec::with_capacity(arguments.len());
                    for argument in arguments {
                        values.push(self.eval(body, argument, frame)?);
                    }
                    let held = held.map(|value| (*value).clone());
                    return self.call_method(target, held, values);
                }
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    values.push(self.eval(body, argument, frame)?);
                }
                // A virtual call reaches whatever the run-time type provides,
                // which is the one thing binding could not settle.
                let target = match (*virtual_call, &receiver) {
                    (true, Some(Value::Object(object))) => {
                        let runtime = object.borrow().ty;
                        self.most_derived(*method, runtime)
                    }
                    _ => *method,
                };
                self.call_method(target, receiver, values)
            }
            BoundExpressionKind::With {
                receiver,
                initializers,
            } => {
                // A struct and a record alike are objects here, so the copy
                // is the same shallow one for both.
                let copy = match self.eval(body, receiver, frame)? {
                    Value::Object(object) => {
                        let original = object.borrow();
                        Value::object(original.ty, original.fields.clone())
                    }
                    other => other,
                };
                self.run_initializers(body, initializers, &copy, frame)?;
                Ok(copy)
            }
            BoundExpressionKind::ObjectCreation {
                constructor,
                arguments,
                initializers,
            } => {
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    values.push(self.eval(body, argument, frame)?);
                }
                let Some(ty) = expression.ty.symbol() else {
                    return Err(Signal::fault("cannot create a value of an unknown type"));
                };
                // The collections are provided rather than run, so they are
                // made here.
                match self.compilation().symbols().get(ty).name.as_str() {
                    "List" | "Dictionary" => {
                        let instance = if self.compilation().symbols().get(ty).name == "List" {
                            Value::list(Vec::new())
                        } else {
                            Value::map(Vec::new())
                        };
                        self.run_initializers(body, initializers, &instance, frame)?;
                        return Ok(instance);
                    }
                    _ => {}
                }
                if self.is_builtin_symbol(ty) {
                    // An exception is a real object, so that `catch
                    // (ArgumentException)` can tell it from `catch
                    // (InvalidOperationException)`; its message is the one
                    // thing it carries.
                    if self.derives_from_exception(ty) {
                        let instance = self.construct(ty, Vec::new())?;
                        if let (Value::Object(object), Some(message)) =
                            (&instance, values.into_iter().next())
                        {
                            object
                                .borrow_mut()
                                .fields
                                .insert(crate::value::EXCEPTION_MESSAGE.to_string(), message);
                        }
                        return Ok(instance);
                    }
                    return Ok(values.into_iter().next().unwrap_or(Value::Null));
                }
                let _ = constructor;
                let instance = self.construct(ty, values)?;
                self.run_initializers(body, initializers, &instance, frame)?;
                Ok(instance)
            }
            BoundExpressionKind::CreatedObject => self
                .creating
                .last()
                .cloned()
                .ok_or_else(|| Signal::fault("an initializer with nothing to initialize")),
            BoundExpressionKind::ArrayCreation {
                lengths, elements, ..
            } => {
                if !elements.is_empty() || lengths.is_empty() {
                    let mut items = Vec::with_capacity(elements.len());
                    for element in elements {
                        items.push(self.eval(body, element, frame)?);
                    }
                    return Ok(Value::array(items));
                }
                let length = self.eval(body, &lengths[0], frame)?;
                let length = usize::try_from(length.as_int().unwrap_or(0)).unwrap_or(0);
                let zero = self.zero_of(&expression.ty);
                Ok(Value::array(vec![zero; length]))
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                let collection = self.eval(body, array, frame)?;
                let index = self.index_of(body, indices, frame)?;
                self.read_element(&collection, &index)
            }
            BoundExpressionKind::ArrayLength { array } => match self.eval(body, array, frame)? {
                Value::Array(items) | Value::List(items) => {
                    Ok(Value::Int(items.borrow().len() as i64))
                }
                Value::Str(text) => Ok(Value::Int(text.chars().count() as i64)),
                other => Err(Signal::fault(format!("{} has no length", other.display()))),
            },
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => {
                let place = self.indexer_place(body, receiver, *indexer, arguments, frame)?;
                self.read(&place, frame)
            }
            BoundExpressionKind::Binary {
                operator,
                left,
                right,
            } => {
                // `&&` and `||` are the two that do not evaluate both sides.
                match operator {
                    BinaryOperator::LogicalAnd => {
                        return if self.condition(body, left, frame)? {
                            Ok(Value::Bool(self.condition(body, right, frame)?))
                        } else {
                            Ok(Value::Bool(false))
                        };
                    }
                    BinaryOperator::LogicalOr => {
                        return if self.condition(body, left, frame)? {
                            Ok(Value::Bool(true))
                        } else {
                            Ok(Value::Bool(self.condition(body, right, frame)?))
                        };
                    }
                    BinaryOperator::Coalesce => {
                        let left = self.eval(body, left, frame)?;
                        return if matches!(left, Value::Null) {
                            self.eval(body, right, frame)
                        } else {
                            Ok(left)
                        };
                    }
                    _ => {}
                }
                // `"is " + colour` joins strings, and joining boxes whatever
                // is not one — which is where an enum stops being a number.
                let left_value = self.eval(body, left, frame)?;
                let left_value = self.box_enum(left_value, &left.ty);
                let right_value = self.eval(body, right, frame)?;
                let right_value = self.box_enum(right_value, &right.ty);
                self.apply(*operator, &left_value, &right_value)
            }
            BoundExpressionKind::Unary { operator, operand } => {
                let value = self.eval(body, operand, frame)?;
                match (operator, &value) {
                    (UnaryOperator::Plus, _) => Ok(value),
                    (UnaryOperator::Minus, Value::Int(value)) => Ok(Value::Int(-value)),
                    (UnaryOperator::Minus, Value::Double(value)) => Ok(Value::Double(-value)),
                    (UnaryOperator::BitwiseNot, Value::Int(value)) => Ok(Value::Int(!value)),
                    (UnaryOperator::LogicalNot, Value::Bool(value)) => Ok(Value::Bool(!value)),
                    (operator, value) => Err(Signal::fault(format!(
                        "{operator:?} cannot be applied to {}",
                        value.display()
                    ))),
                }
            }
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                if self.condition(body, condition, frame)? {
                    self.eval(body, consequence, frame)
                } else {
                    self.eval(body, alternative, frame)
                }
            }
            BoundExpressionKind::Assignment { target, value } => {
                let place = self.place_of(body, target, frame)?;
                let value = self.eval(body, value, frame)?;
                self.store(place, value.clone(), frame)?;
                Ok(value)
            }
            BoundExpressionKind::CompoundAssignment {
                target,
                operator,
                value,
            } => {
                let place = self.place_of(body, target, frame)?;
                let current = self.read(&place, frame)?;
                let operand = self.eval(body, value, frame)?;
                let result = self.apply(*operator, &current, &operand)?;
                self.store(place, result.clone(), frame)?;
                Ok(result)
            }
            BoundExpressionKind::Increment {
                target,
                operator,
                prefix,
                ..
            } => {
                let place = self.place_of(body, target, frame)?;
                let before = self.read(&place, frame)?;
                let one = Value::Int(1);
                let operator = match operator {
                    IncrementOperator::Increment => BinaryOperator::Add,
                    IncrementOperator::Decrement => BinaryOperator::Subtract,
                };
                let after = self.apply(operator, &before, &one)?;
                self.store(place, after.clone(), frame)?;
                Ok(if *prefix { after } else { before })
            }
            BoundExpressionKind::Conversion {
                operand,
                conversion,
                ..
            } => {
                let value = self.eval(body, operand, frame)?;
                Ok(self.convert(value, *conversion, &operand.ty, &expression.ty))
            }
            BoundExpressionKind::InterpolatedString(parts) => {
                let mut text = String::new();
                for part in parts {
                    text.push_str(&self.eval(body, part, frame)?.display());
                }
                Ok(Value::Str(text.into()))
            }
            // The alignment and format are the runtime's to apply, and this
            // backend has none: the value is written as it is.
            BoundExpressionKind::StringInsert { value, .. } => {
                Ok(Value::Str(self.eval(body, value, frame)?.display().into()))
            }
            BoundExpressionKind::TypeTest { operand, target } => {
                let value = self.eval(body, operand, frame)?;
                Ok(Value::Bool(self.is_of_type(&value, target)))
            }
            BoundExpressionKind::TryCast { operand, target } => {
                let value = self.eval(body, operand, frame)?;
                Ok(if self.is_of_type(&value, target) {
                    value
                } else {
                    Value::Null
                })
            }
            BoundExpressionKind::IsPattern { operand, pattern } => {
                let value = self.eval(body, operand, frame)?;
                Ok(Value::Bool(self.matches(body, pattern, &value, frame)?))
            }
            BoundExpressionKind::Switch { governing, arms } => {
                let value = self.eval(body, governing, frame)?;
                for arm in arms {
                    if !self.matches(body, &arm.pattern, &value, frame)? {
                        continue;
                    }
                    if let Some(when) = &arm.when
                        && !self.condition(body, when, frame)?
                    {
                        continue;
                    }
                    return self.eval(body, &arm.value, frame);
                }
                Err(Signal::Thrown(Value::Str(
                    "non-exhaustive switch expression failed to match its input".into(),
                )))
            }
            BoundExpressionKind::Default(ty) => Ok(self.zero_of(ty)),
            BoundExpressionKind::TypeOf(_) => Err(Signal::fault("typeof is not supported")),
            BoundExpressionKind::EventAssignment { .. } => {
                Err(Signal::fault("an event accessor is not supported"))
            }
            // `x ?? throw new E()` throws instead of producing a value.
            BoundExpressionKind::Throw(thrown) => {
                let value = match thrown {
                    Some(thrown) => self.eval(body, thrown, frame)?,
                    None => Value::Null,
                };
                Err(Signal::Thrown(value))
            }
            BoundExpressionKind::ArgList(_) | BoundExpressionKind::ArgListHandle => {
                Err(Signal::fault("`__arglist` is not interpreted".to_string()))
            }
            BoundExpressionKind::TupleCreation(_) => Err(Signal::fault(
                "a tuple is a `ValueTuple` of the framework, which there is none of here",
            )),
            // Each in order; the value is the last one's.
            BoundExpressionKind::Sequence(steps) => {
                let mut result = Value::Null;
                for step in steps {
                    result = self.eval(body, step, frame)?;
                }
                Ok(result)
            }
            // The statements are a loop the expression needed; nothing in
            // them leaves it.
            BoundExpressionKind::SpillSequence { statements, value } => {
                self.run_statements(body, statements, frame)?;
                self.eval(body, value, frame)
            }
            BoundExpressionKind::SizeOf(_) => Err(Signal::fault(
                "`sizeof` asks the runtime how wide a type is, which there is none of here",
            )),
            BoundExpressionKind::Dereference { .. }
            | BoundExpressionKind::AddressOf { .. }
            | BoundExpressionKind::MethodAddress { .. }
            | BoundExpressionKind::MakeRef(_)
            | BoundExpressionKind::RefValue(_)
            | BoundExpressionKind::RefType(_)
            | BoundExpressionKind::FunctionPointerCall { .. }
            | BoundExpressionKind::StackAlloc { .. } => Err(Signal::fault(
                "a pointer names memory, which this backend has none of",
            )),
            BoundExpressionKind::Await { .. } => Err(Signal::fault(
                "await needs a state machine, which is not built yet",
            )),
            BoundExpressionKind::TypeExpression(_)
            | BoundExpressionKind::NamespaceExpression(_) => Err(Signal::fault(
                "a type or namespace name was used as a value",
            )),
            BoundExpressionKind::Error => {
                Err(Signal::fault("an expression that did not bind was reached"))
            }
            BoundExpressionKind::Unsupported(kind) => {
                Err(Signal::fault(format!("{kind:?} is not supported")))
            }
            BoundExpressionKind::Dynamic(_) => Err(Signal::fault(
                "an operation on `dynamic` is bound at run time, which is not modelled",
            )),
        }
    }

    fn eval_receiver(
        &mut self,
        body: &BoundBody,
        receiver: Option<&BoundExpression>,
        frame: &mut Frame,
    ) -> Result<Option<Value>, Signal> {
        match receiver {
            // `Holder<int>.Count` carries its construction as a receiver that
            // is a type rather than a value. The compiler needs it — each
            // construction has storage of its own — and the interpreter, which
            // keeps one value per field, has nothing to do with it.
            Some(receiver) if matches!(receiver.kind, BoundExpressionKind::TypeExpression(_)) => {
                Ok(None)
            }
            Some(receiver) => Ok(Some(self.eval(body, receiver, frame)?)),
            None => Ok(None),
        }
    }

    fn index_of(
        &mut self,
        body: &BoundBody,
        arguments: &[BoundExpression],
        frame: &mut Frame,
    ) -> Eval {
        let Some(first) = arguments.first() else {
            return Err(Signal::fault("an index is missing"));
        };
        if arguments.len() > 1 {
            return Err(Signal::fault("only one index is supported"));
        }
        self.eval(body, first, frame)
    }

    /// What a value means when it might be a reference: the variable it
    /// points at, or itself.
    pub(crate) fn through(&mut self, value: Value) -> Value {
        let Value::Reference(reference) = &value else {
            return value;
        };
        if let Reference::Static(field) = &**reference {
            return self.static_value(*field);
        }
        reference.read().unwrap_or(Value::Null)
    }

    fn write_through(&mut self, reference: &Reference, value: Value) -> Result<(), Signal> {
        if let Reference::Static(field) = reference {
            self.set_static(*field, value);
            return Ok(());
        }
        if reference.write(value) {
            return Ok(());
        }
        Err(Signal::fault("cannot write through that reference"))
    }

    /// The variable a `ref` or `out` argument points at.
    fn reference_to(
        &mut self,
        body: &BoundBody,
        target: &BoundExpression,
        frame: &mut Frame,
    ) -> Result<Reference, Signal> {
        match &target.kind {
            BoundExpressionKind::Local(local) => Ok(Reference::Local {
                slots: frame.local_slots(),
                index: local.0 as usize,
            }),
            BoundExpressionKind::Parameter(parameter) => {
                // A `ref` parameter passed on stays pointing where it did.
                if let Value::Reference(reference) = frame.argument(*parameter) {
                    return Ok(match &*reference {
                        Reference::Local { slots, index } => Reference::Local {
                            slots: std::rc::Rc::clone(slots),
                            index: *index,
                        },
                        Reference::Argument { slots, parameter } => Reference::Argument {
                            slots: std::rc::Rc::clone(slots),
                            parameter: *parameter,
                        },
                        Reference::Field { object, name } => Reference::Field {
                            object: std::rc::Rc::clone(object),
                            name: name.clone(),
                        },
                        Reference::Element { items, index } => Reference::Element {
                            items: std::rc::Rc::clone(items),
                            index: *index,
                        },
                        Reference::Static(field) => Reference::Static(*field),
                    });
                }
                Ok(Reference::Argument {
                    slots: frame.argument_slots(),
                    parameter: *parameter,
                })
            }
            BoundExpressionKind::Field { receiver, field } => {
                let symbols = self.compilation().symbols();
                if symbols.get(*field).modifiers.contains(Modifiers::STATIC) {
                    return Ok(Reference::Static(*field));
                }
                let name = symbols.get(*field).name.clone();
                match self.eval_receiver(body, receiver.as_deref(), frame)? {
                    Some(Value::Object(object)) => Ok(Reference::Field { object, name }),
                    _ => Err(Signal::fault(
                        "a field of nothing cannot be passed by reference",
                    )),
                }
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                let collection = self.eval(body, array, frame)?;
                let index = self.index_of(body, indices, frame)?;
                let index = usize::try_from(index.as_int().unwrap_or(-1)).map_err(|_| {
                    Signal::Thrown(Value::Str(
                        "index was outside the bounds of the array".into(),
                    ))
                })?;
                match collection {
                    Value::Array(items) | Value::List(items) => {
                        Ok(Reference::Element { items, index })
                    }
                    other => Err(Signal::fault(format!(
                        "{} cannot be passed by reference",
                        other.display()
                    ))),
                }
            }
            _ => Err(Signal::fault("only a variable can be passed by reference")),
        }
    }

    /// Where an indexer's value lives.
    ///
    /// A collection the interpreter provides is indexed directly; one declared
    /// in source is two methods, and the arguments are evaluated once here so
    /// that `b[f()] += 1` calls `f` once.
    fn indexer_place(
        &mut self,
        body: &BoundBody,
        receiver: &BoundExpression,
        indexer: SymbolId,
        arguments: &[BoundExpression],
        frame: &mut Frame,
    ) -> Result<Place, Signal> {
        let collection = self.eval(body, receiver, frame)?;
        if self.is_builtin_symbol(indexer) {
            return Ok(Place::Element {
                collection,
                index: self.index_of(body, arguments, frame)?,
            });
        }
        let mut values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            values.push(self.eval(body, argument, frame)?);
        }
        Ok(Place::Indexer {
            receiver: Some(collection),
            indexer,
            arguments: values,
        })
    }

    /// The integer an array or a list is indexed by.
    fn as_index(index: &Value) -> Result<i64, Signal> {
        index
            .as_int()
            .ok_or_else(|| Signal::fault(format!("{} is not an index", index.display())))
    }

    /// What a freshly made value of a type holds.
    pub(crate) fn zero_of(&self, ty: &Type) -> Value {
        let element = match ty {
            Type::Array { element, .. } => element.as_ref(),
            other => other,
        };
        let special = element.symbol().and_then(|symbol| self.special_of(symbol));
        match special {
            Some(SpecialType::Boolean) => Value::Bool(false),
            Some(SpecialType::Char) => Value::Char('\0'),
            Some(SpecialType::Single | SpecialType::Double | SpecialType::Decimal) => {
                Value::Double(0.0)
            }
            Some(SpecialType::String | SpecialType::Object) | None => Value::Null,
            Some(_) => Value::Int(0),
        }
    }

    /// The name an enum value goes by, or its number when no member has it.
    ///
    /// `Enum.ToString` does the same: a value no member names prints as the
    /// number rather than as a guess.
    fn enum_name(&self, ty: SymbolId, value: i64) -> String {
        let symbols = self.compilation().symbols();
        for member in symbols.get(ty).members.clone() {
            if symbols.get(member).kind != rustlyn_semantics::SymbolKind::Field {
                continue;
            }
            if self
                .binder
                .constant_value(member)
                .and_then(|constant| constant_as_int(&constant))
                == Some(value)
            {
                return symbols.get(member).name.clone();
            }
        }
        value.to_string()
    }

    pub(crate) fn special_of(&self, symbol: SymbolId) -> Option<SpecialType> {
        SpecialType::ALL
            .iter()
            .copied()
            .find(|special| self.compilation().special_type(*special) == Some(symbol))
    }

    /// Narrows a value the way a conversion says to.
    ///
    /// Boxing and reference conversions do nothing here: the interpreter holds
    /// every value the same way whatever its static type.
    /// Boxes an enum, which is what makes it know its own name.
    ///
    /// An unboxed enum is its number and nothing more; boxing is where a value
    /// picks up its type, and `Colour.Green` starts printing as `Green`.
    /// Anything else is handed back untouched.
    fn box_enum(&self, value: Value, ty: &Type) -> Value {
        let Some(symbol) = ty.symbol() else {
            return value;
        };
        if self.compilation().symbols().get(symbol).type_kind()
            != Some(rustlyn_semantics::TypeKind::Enum)
        {
            return value;
        }
        let Some(number) = value.as_int() else {
            return value;
        };
        Value::Enumeration {
            ty: symbol,
            value: number,
            name: self.enum_name(symbol, number).into(),
        }
    }

    fn convert(
        &self,
        value: Value,
        conversion: ConversionKind,
        source: &Type,
        target: &Type,
    ) -> Value {
        if matches!(conversion, ConversionKind::Boxing) {
            return self.box_enum(value, source);
        }
        if !matches!(conversion, ConversionKind::Numeric) {
            return value;
        }
        let special = target.symbol().and_then(|symbol| self.special_of(symbol));
        match special {
            Some(SpecialType::Single | SpecialType::Double | SpecialType::Decimal) => {
                Value::Double(value.as_double().unwrap_or(0.0))
            }
            Some(SpecialType::Char) => match value.as_int() {
                Some(code) => u32::try_from(code)
                    .ok()
                    .and_then(char::from_u32)
                    .map_or(value, Value::Char),
                None => value,
            },
            Some(SpecialType::Boolean) => value,
            Some(special) => {
                // A narrowing integer conversion wraps, as C# says an
                // unchecked one does.
                let raw = value.as_int().unwrap_or(0);
                Value::Int(match special {
                    SpecialType::SByte => i64::from(raw as i8),
                    SpecialType::Byte => i64::from(raw as u8),
                    SpecialType::Int16 => i64::from(raw as i16),
                    SpecialType::UInt16 => i64::from(raw as u16),
                    SpecialType::Int32 => i64::from(raw as i32),
                    SpecialType::UInt32 => i64::from(raw as u32),
                    _ => raw,
                })
            }
            None => value,
        }
    }

    // -- places ------------------------------------------------------------

    pub(crate) fn place_of(
        &mut self,
        body: &BoundBody,
        target: &BoundExpression,
        frame: &mut Frame,
    ) -> Result<Place, Signal> {
        match &target.kind {
            BoundExpressionKind::Local(local) => Ok(Place::Local(*local)),
            BoundExpressionKind::Parameter(parameter) => Ok(Place::Argument(*parameter)),
            BoundExpressionKind::Field { receiver, field } => Ok(Place::Field {
                receiver: self.eval_receiver(body, receiver.as_deref(), frame)?,
                field: *field,
            }),
            BoundExpressionKind::Property { receiver, property } => Ok(Place::Property {
                receiver: self.eval_receiver(body, receiver.as_deref(), frame)?,
                property: *property,
            }),
            BoundExpressionKind::ArrayAccess { array, indices } => Ok(Place::Element {
                collection: self.eval(body, array, frame)?,
                index: self.index_of(body, indices, frame)?,
            }),
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => self.indexer_place(body, receiver, *indexer, arguments, frame),
            _ => Err(Signal::fault("this expression cannot be assigned to")),
        }
    }

    pub(crate) fn read(&mut self, place: &Place, frame: &Frame) -> Eval {
        match place {
            Place::Local(local) => {
                let value = frame.local(*local);
                Ok(self.through(value))
            }
            Place::Argument(parameter) => Ok(self.through(frame.argument(*parameter))),
            Place::Field { receiver, field } => self.read_field(*field, receiver.clone()),
            Place::Property { receiver, property } => {
                self.read_property(*property, receiver.clone())
            }
            Place::Element { collection, index } => self.read_element(collection, index),
            Place::Indexer {
                receiver,
                indexer,
                arguments,
            } => {
                let getter = self
                    .compilation()
                    .symbols()
                    .get(*indexer)
                    .as_property()
                    .and_then(|detail| detail.getter)
                    .ok_or_else(|| Signal::fault("the indexer has no getter to call"))?;
                self.call_method(getter, receiver.clone(), arguments.clone())
            }
        }
    }

    pub(crate) fn store(
        &mut self,
        place: Place,
        value: Value,
        frame: &mut Frame,
    ) -> Result<(), Signal> {
        match place {
            Place::Local(local) => {
                // Writing to a `ref` local writes where it points.
                if let Value::Reference(reference) = frame.local(local) {
                    return self.write_through(&reference, value);
                }
                frame.set_local(local, value);
                Ok(())
            }
            Place::Argument(parameter) => {
                // Writing to a `ref` parameter writes where it points, which
                // is the whole reason it was passed that way.
                if let Value::Reference(reference) = frame.argument(parameter) {
                    return self.write_through(&reference, value);
                }
                frame.set_argument(parameter, value);
                Ok(())
            }
            Place::Field { receiver, field } => self.write_field(field, receiver, value),
            Place::Property { receiver, property } => {
                self.write_property(property, receiver, value)
            }
            Place::Element { collection, index } => match collection {
                Value::Array(items) | Value::List(items) => {
                    let position = Self::as_index(&index)?;
                    let mut items = items.borrow_mut();
                    match usize::try_from(position).ok().filter(|i| *i < items.len()) {
                        Some(position) => {
                            items[position] = value;
                            Ok(())
                        }
                        None => Err(Signal::Thrown(Value::Str(
                            "index was outside the bounds of the array".into(),
                        ))),
                    }
                }
                // Writing through a dictionary's indexer adds the key when it
                // is not there, which is what makes it different from `Add`.
                Value::Map(entries) => {
                    let mut entries = entries.borrow_mut();
                    match entries.iter_mut().find(|(key, _)| key.equals(&index)) {
                        Some(entry) => entry.1 = value,
                        None => entries.push((index, value)),
                    }
                    Ok(())
                }
                other => Err(Signal::fault(format!(
                    "{} cannot be indexed",
                    other.display()
                ))),
            },
            Place::Indexer {
                receiver,
                indexer,
                mut arguments,
            } => {
                let setter = self
                    .compilation()
                    .symbols()
                    .get(indexer)
                    .as_property()
                    .and_then(|detail| detail.setter)
                    .ok_or_else(|| Signal::fault("the indexer has no setter to call"))?;
                // A setter takes the value last, after the arguments.
                arguments.push(value);
                self.call_method(setter, receiver, arguments)?;
                Ok(())
            }
        }
    }

    pub(crate) fn read_element(&mut self, collection: &Value, index: &Value) -> Eval {
        // A dictionary is the one collection whose index is not a number.
        if let Value::Map(entries) = collection {
            return entries
                .borrow()
                .iter()
                .find(|(key, _)| key.equals(index))
                .map(|(_, value)| value.clone())
                .ok_or_else(|| {
                    Signal::Thrown(Value::Str(
                        "the given key was not present in the dictionary".into(),
                    ))
                });
        }
        let index = Self::as_index(index)?;
        match collection {
            Value::Array(items) | Value::List(items) => {
                let items = items.borrow();
                usize::try_from(index)
                    .ok()
                    .and_then(|index| items.get(index).cloned())
                    .ok_or_else(|| {
                        Signal::Thrown(Value::Str(
                            "index was outside the bounds of the array".into(),
                        ))
                    })
            }
            Value::Str(text) => usize::try_from(index)
                .ok()
                .and_then(|index| text.chars().nth(index))
                .map(Value::Char)
                .ok_or_else(|| {
                    Signal::Thrown(Value::Str(
                        "index was outside the bounds of the string".into(),
                    ))
                }),
            Value::Null => Err(Signal::Thrown(Value::Str(
                "object reference not set to an instance of an object".into(),
            ))),
            other => Err(Signal::fault(format!(
                "{} cannot be indexed",
                other.display()
            ))),
        }
    }

    // -- operators ---------------------------------------------------------

    pub(crate) fn apply(&mut self, operator: BinaryOperator, left: &Value, right: &Value) -> Eval {
        use BinaryOperator as Op;

        // Equality is defined for every pair, so it comes first.
        match operator {
            Op::Equality => return Ok(Value::Bool(left.equals(right))),
            Op::Inequality => return Ok(Value::Bool(!left.equals(right))),
            _ => {}
        }

        // `+` joins strings when either side is one, whatever the other is.
        if matches!(operator, Op::Add)
            && (matches!(left, Value::Str(_)) || matches!(right, Value::Str(_)))
        {
            return Ok(Value::Str(
                format!("{}{}", left.display(), right.display()).into(),
            ));
        }

        if let (Value::Bool(left), Value::Bool(right)) = (left, right) {
            return match operator {
                Op::BitwiseAnd | Op::LogicalAnd => Ok(Value::Bool(*left && *right)),
                Op::BitwiseOr | Op::LogicalOr => Ok(Value::Bool(*left || *right)),
                Op::ExclusiveOr => Ok(Value::Bool(left ^ right)),
                _ => Err(self.operator_fault(operator, &Value::Bool(*left), &Value::Bool(*right))),
            };
        }

        // Anything with a `double` on either side is done in `double`.
        let floating = matches!(left, Value::Double(_)) || matches!(right, Value::Double(_));
        if floating {
            let (a, b) = (
                left.as_double().unwrap_or(0.0),
                right.as_double().unwrap_or(0.0),
            );
            return Ok(match operator {
                Op::Add => Value::Double(a + b),
                Op::Subtract => Value::Double(a - b),
                Op::Multiply => Value::Double(a * b),
                Op::Divide => Value::Double(a / b),
                Op::Modulo => Value::Double(a % b),
                Op::LessThan => Value::Bool(a < b),
                Op::GreaterThan => Value::Bool(a > b),
                Op::LessThanOrEqual => Value::Bool(a <= b),
                Op::GreaterThanOrEqual => Value::Bool(a >= b),
                _ => return Err(self.operator_fault(operator, left, right)),
            });
        }

        let (Some(a), Some(b)) = (left.as_int(), right.as_int()) else {
            return Err(self.operator_fault(operator, left, right));
        };
        Ok(match operator {
            Op::Add => Value::Int(a.wrapping_add(b)),
            Op::Subtract => Value::Int(a.wrapping_sub(b)),
            Op::Multiply => Value::Int(a.wrapping_mul(b)),
            Op::Divide | Op::Modulo => {
                if b == 0 {
                    return Err(Signal::Thrown(Value::Str(
                        "attempted to divide by zero".into(),
                    )));
                }
                if operator == Op::Divide {
                    Value::Int(a.wrapping_div(b))
                } else {
                    Value::Int(a.wrapping_rem(b))
                }
            }
            Op::BitwiseAnd => Value::Int(a & b),
            Op::BitwiseOr => Value::Int(a | b),
            Op::ExclusiveOr => Value::Int(a ^ b),
            Op::LeftShift => Value::Int(a.wrapping_shl(b as u32)),
            Op::RightShift => Value::Int(a.wrapping_shr(b as u32)),
            Op::LessThan => Value::Bool(a < b),
            Op::GreaterThan => Value::Bool(a > b),
            Op::LessThanOrEqual => Value::Bool(a <= b),
            Op::GreaterThanOrEqual => Value::Bool(a >= b),
            _ => return Err(self.operator_fault(operator, left, right)),
        })
    }

    fn operator_fault(&self, operator: BinaryOperator, left: &Value, right: &Value) -> Signal {
        Signal::fault(format!(
            "{operator:?} cannot be applied to {} and {}",
            left.display(),
            right.display()
        ))
    }

    // -- members -----------------------------------------------------------

    pub(crate) fn read_field(&mut self, field: SymbolId, receiver: Option<Value>) -> Eval {
        // A constant has no storage; the binder knows its value.
        if let Some(constant) = self.binder.constant_value(field) {
            return Ok(runtime_value(&constant));
        }
        let symbols = self.compilation().symbols();
        let name = symbols.get(field).name.clone();
        if symbols
            .get(field)
            .modifiers
            .contains(rustlyn_semantics::Modifiers::STATIC)
        {
            return Ok(self.static_value(field));
        }
        match receiver {
            Some(Value::Object(object)) => Ok(object
                .borrow()
                .fields
                .get(&name)
                .cloned()
                .unwrap_or(Value::Null)),
            Some(Value::Null) | None => Err(Signal::Thrown(Value::Str(
                "object reference not set to an instance of an object".into(),
            ))),
            Some(other) => Err(Signal::fault(format!(
                "{} has no field {name}",
                other.display()
            ))),
        }
    }

    fn write_field(
        &mut self,
        field: SymbolId,
        receiver: Option<Value>,
        value: Value,
    ) -> Result<(), Signal> {
        let symbols = self.compilation().symbols();
        let name = symbols.get(field).name.clone();
        if symbols
            .get(field)
            .modifiers
            .contains(rustlyn_semantics::Modifiers::STATIC)
        {
            self.set_static(field, value);
            return Ok(());
        }
        match receiver {
            Some(Value::Object(object)) => {
                object.borrow_mut().fields.insert(name, value);
                Ok(())
            }
            _ => Err(Signal::Thrown(Value::Str(
                "object reference not set to an instance of an object".into(),
            ))),
        }
    }

    /// Runs a constructor's own body against an object that already exists,
    /// which is what a `: base(...)` or `: this(...)` chain needs.
    pub(crate) fn run_constructor_body(
        &mut self,
        constructor: SymbolId,
        instance: Option<Value>,
        arguments: Vec<Value>,
    ) -> Result<(), Signal> {
        if self.is_builtin_symbol(constructor) {
            return Ok(());
        }
        // A record's positional constructor has no body: what it does is fill
        // the properties its parameters named.
        if self.is_record_constructor(constructor) {
            self.run_record_constructor(constructor, instance, arguments);
            return Ok(());
        }
        let Some(body) = self.body_of(constructor) else {
            return Ok(());
        };
        let mut frame = self.frame_for(constructor, instance, &body, arguments);
        let statements = body.statements.clone();
        match self.run_statements(&body, &statements, &mut frame)? {
            Flow::Return(_) | Flow::Normal => Ok(()),
            _ => Ok(()),
        }
    }
}

/// Turns a bound constant into a runtime value.
fn runtime_value(value: &ConstantValue) -> Value {
    match value {
        ConstantValue::Null => Value::Null,
        ConstantValue::Boolean(value) => Value::Bool(*value),
        ConstantValue::Char(value) => Value::Char(*value),
        ConstantValue::Int32(value) => Value::Int(i64::from(*value)),
        ConstantValue::UInt32(value) => Value::Int(i64::from(*value)),
        ConstantValue::Int64(value) => Value::Int(*value),
        ConstantValue::UInt64(value) => Value::Int(*value as i64),
        ConstantValue::Single(value) => Value::Double(f64::from(*value)),
        ConstantValue::Double(value) => Value::Double(*value),
        ConstantValue::String(text) => Value::Str(text.clone().into()),
    }
}

/// The integer inside a constant, where there is one.
fn constant_as_int(value: &ConstantValue) -> Option<i64> {
    match value {
        ConstantValue::Int32(value) => Some(i64::from(*value)),
        ConstantValue::Int64(value) => Some(*value),
        ConstantValue::UInt32(value) => Some(i64::from(*value)),
        ConstantValue::UInt64(value) => i64::try_from(*value).ok(),
        _ => None,
    }
}
