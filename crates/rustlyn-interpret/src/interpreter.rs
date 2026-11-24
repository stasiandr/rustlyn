//! A tree-walking interpreter over the bound tree.
//!
//! It walks what the binder produced rather than the syntax, which matters for
//! a reason that has nothing to do with speed: the binder has already decided
//! which overload a call means, what each name refers to and which conversions
//! apply, and a second walk over the syntax would have to decide all of that
//! again. Two answers to the same question is how a compiler comes to describe
//! a program other than the one that runs.
//!
//! So the interpreter resolves nothing. It reads decisions and carries them
//! out — which makes running a program a check on the binder, and makes the
//! interpreter and the IL backend agree by construction rather than by care.
//!
//! What it cannot do it says so about, rather than guessing.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustlyn_semantics::{
    Binder, BodyBinder, BoundBody, BoundStatement, Compilation, LocalId, Modifiers, SymbolId,
    SymbolKind,
};

use crate::value::Value;

/// How a statement finished.
#[derive(Debug)]
pub(crate) enum Flow {
    Normal,
    Return(Value),
    /// A `break` still to pass over this many loops and `switch` statements.
    Break(usize),
    /// A `continue` still to pass over this many loops.
    Continue(usize),
}

/// Why execution stopped early.
#[derive(Debug)]
pub enum Signal {
    /// A C# exception the program threw.
    Thrown(Value),
    /// Something the interpreter cannot do, or a genuine fault such as
    /// dividing by zero.
    Fault(String),
}

impl Signal {
    pub(crate) fn fault(message: impl Into<String>) -> Self {
        Self::Fault(message.into())
    }

    /// How the failure reads to whoever ran the program.
    #[must_use]
    pub fn describe(&self) -> String {
        match self {
            Self::Thrown(value) => format!("unhandled exception: {}", value.display()),
            Self::Fault(message) => message.clone(),
        }
    }
}

pub(crate) type Outcome = Result<Flow, Signal>;
pub(crate) type Eval = Result<Value, Signal>;

/// One method's local state.
///
/// Locals are a flat vector because the binder already gave each of them a
/// number: two `i`s in two `for` loops are two locals, so nothing here has to
/// know about scopes.
/// One method's local state.
///
/// The slots are shared rather than owned, because a lambda captures a
/// variable and not a copy of it: `int n = 0; Act f = () => n++;` has to see
/// the same `n` the method does, and assigning to `n` after `f` is made has to
/// be visible inside it. Sharing the frame is how C# gets that, and a display
/// class is how the IL backend will.
#[derive(Clone, Debug)]
pub(crate) struct Frame {
    locals: Rc<RefCell<Vec<Value>>>,
    arguments: Rc<RefCell<HashMap<SymbolId, Value>>>,
    pub(crate) this: Option<Value>,
}

impl Frame {
    pub(crate) fn new(this: Option<Value>, locals: usize) -> Self {
        Self {
            locals: Rc::new(RefCell::new(vec![Value::Null; locals])),
            arguments: Rc::new(RefCell::new(HashMap::new())),
            this,
        }
    }

    pub(crate) fn local(&self, local: LocalId) -> Value {
        self.locals
            .borrow()
            .get(local.0 as usize)
            .cloned()
            .unwrap_or(Value::Null)
    }

    pub(crate) fn set_local(&mut self, local: LocalId, value: Value) {
        if let Some(slot) = self.locals.borrow_mut().get_mut(local.0 as usize) {
            *slot = value;
        }
    }

    pub(crate) fn argument(&self, parameter: SymbolId) -> Value {
        self.arguments
            .borrow()
            .get(&parameter)
            .cloned()
            .unwrap_or(Value::Null)
    }

    pub(crate) fn set_argument(&mut self, parameter: SymbolId, value: Value) {
        self.arguments.borrow_mut().insert(parameter, value);
    }

    /// The slots themselves, for a `ref` argument that points at one of them.
    pub(crate) fn local_slots(&self) -> Rc<RefCell<Vec<Value>>> {
        Rc::clone(&self.locals)
    }

    pub(crate) fn argument_slots(&self) -> Rc<RefCell<HashMap<SymbolId, Value>>> {
        Rc::clone(&self.arguments)
    }

    /// Makes room for locals a lambda's body needs that the frame was not made
    /// with, which happens when a lambda is called after its method returned.
    pub(crate) fn ensure_locals(&self, count: usize) {
        let mut locals = self.locals.borrow_mut();
        if locals.len() < count {
            locals.resize(count, Value::Null);
        }
    }
}

/// A frame a closure holds on to. It is the same frame, shared: that is what
/// makes a captured variable the variable and not a copy of it.
pub(crate) type CapturedFrame = Frame;

/// Runs a compilation.
pub struct Interpreter<'a> {
    compilation: &'a Compilation,
    pub(crate) binder: Binder<'a>,
    /// Bound bodies, kept because binding one is not cheap and a method is
    /// usually called more than once.
    bodies: HashMap<SymbolId, Rc<BoundBody>>,
    pub(crate) statics: HashMap<SymbolId, Value>,
    output: String,
    depth: usize,
    /// The objects being initialized, innermost last.
    ///
    /// `new Point { X = 1 }` has nowhere to put the new object between making
    /// it and setting `X`, and no name for it either; this is that place.
    pub(crate) creating: Vec<Value>,
    /// The receivers of the `?.` expressions being evaluated, innermost last.
    pub(crate) accessed: Vec<Value>,
}

impl std::fmt::Debug for Interpreter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Interpreter")
            .field("output", &self.output)
            .finish_non_exhaustive()
    }
}

/// How deep calls may nest before the interpreter gives up.
///
/// A C# call costs a dozen or so Rust frames — a statement calls an
/// expression calls a method calls a statement — so this has to stay well
/// inside the host thread's stack. The point is to report runaway recursion
/// the way .NET reports a stack overflow, rather than to take the process
/// down; a test thread's stack is smaller than the main one's, so the limit
/// is set for the smaller.
const MAX_DEPTH: usize = 48;

impl<'a> Interpreter<'a> {
    #[must_use]
    pub fn new(compilation: &'a Compilation) -> Self {
        Self {
            compilation,
            binder: Binder::new(compilation),
            bodies: HashMap::new(),
            statics: HashMap::new(),
            output: String::new(),
            depth: 0,
            creating: Vec::new(),
            accessed: Vec::new(),
        }
    }

    /// What the program printed.
    #[must_use]
    pub fn output(&self) -> &str {
        &self.output
    }

    pub(crate) fn compilation(&self) -> &'a Compilation {
        self.compilation
    }

    /// Runs the program's entry point.
    ///
    /// # Errors
    ///
    /// Returns a description of what went wrong: an unhandled exception, a
    /// missing entry point, or a construct the interpreter does not support.
    pub fn run(&mut self) -> Result<(), String> {
        let entry = self
            .find_entry_point()
            .ok_or_else(|| "no entry point: expected a static method called Main".to_string())?;
        // `Main` may take a string[] of command-line arguments.
        let parameters = self
            .compilation
            .symbols()
            .get(entry)
            .as_method()
            .map_or(0, |detail| detail.parameters.len());
        let arguments = vec![Value::array(Vec::new()); parameters];

        match self.call_method(entry, None, arguments) {
            Ok(_) => Ok(()),
            Err(signal) => Err(signal.describe()),
        }
    }

    fn find_entry_point(&self) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        symbols
            .iter()
            .find(|symbol| {
                symbol.kind == SymbolKind::Method
                    && symbol.name == "Main"
                    && symbol.modifiers.contains(Modifiers::STATIC)
                    // The core library is not the program.
                    && !self.compilation.is_from_corlib(symbol.id)
            })
            .map(|symbol| symbol.id)
    }

    // -- calling -----------------------------------------------------------

    pub(crate) fn body_of(&mut self, member: SymbolId) -> Option<Rc<BoundBody>> {
        if let Some(body) = self.bodies.get(&member) {
            return Some(Rc::clone(body));
        }
        let (tree, span) = *self.compilation.declaration_nodes(member).first()?;
        let node = self.compilation.trees().get(tree)?.root().find_node(span)?;
        let bound = Rc::new(BodyBinder::bind_member(&self.binder, tree, &node));
        self.bodies.insert(member, Rc::clone(&bound));
        Some(bound)
    }

    pub(crate) fn call_method(
        &mut self,
        method: SymbolId,
        this: Option<Value>,
        arguments: Vec<Value>,
    ) -> Eval {
        if self.depth >= MAX_DEPTH {
            return Err(Signal::fault("call stack too deep"));
        }
        if self.is_builtin_symbol(method) {
            return self.call_builtin(method, this, arguments);
        }
        // A record's members have symbols but no source, so what they do comes
        // from what the record holds.
        if self.is_record_member(method) {
            return self.call_record_member(method, this, arguments);
        }

        let Some(body) = self.body_of(method) else {
            let name = self.compilation.symbols().qualified_name(method);
            return Err(Signal::fault(format!("{name} has no body to run")));
        };
        let mut frame = self.frame_for(method, this, &body, arguments);

        self.depth += 1;
        let result = self.run_statements(&body, &body.statements.clone(), &mut frame);
        self.depth -= 1;

        match result? {
            Flow::Return(value) => Ok(value),
            _ => Ok(Value::Null),
        }
    }

    /// A frame with the method's parameters already bound to its arguments.
    /// Runs a lambda, in the frame it was made in.
    ///
    /// The frame is shared rather than copied, so a captured variable is the
    /// variable: what the lambda writes, the method that made it sees.
    pub(crate) fn call_closure(
        &mut self,
        closure: &crate::value::Closure,
        arguments: Vec<Value>,
    ) -> Eval {
        if self.depth >= MAX_DEPTH {
            return Err(Signal::fault("call stack too deep"));
        }
        let mut frame = closure.frame.clone();
        frame.ensure_locals(closure.body.locals.len());
        for (parameter, value) in closure.parameters.iter().zip(arguments) {
            frame.set_local(*parameter, value);
        }
        let body = Rc::clone(&closure.body);
        self.depth += 1;
        let result = self.run_statements(&body, &body.statements, &mut frame);
        self.depth -= 1;
        match result? {
            Flow::Return(value) => Ok(value),
            _ => Ok(Value::Null),
        }
    }

    pub(crate) fn frame_for(
        &self,
        method: SymbolId,
        this: Option<Value>,
        body: &BoundBody,
        arguments: Vec<Value>,
    ) -> Frame {
        let mut frame = Frame::new(this, body.locals.len());
        let parameters = self
            .compilation
            .symbols()
            .get(method)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        for (parameter, value) in parameters.iter().zip(arguments) {
            frame.set_argument(*parameter, value);
        }
        frame
    }

    pub(crate) fn run_statements(
        &mut self,
        body: &BoundBody,
        statements: &[BoundStatement],
        frame: &mut Frame,
    ) -> Outcome {
        for statement in statements {
            let flow = self.exec(body, statement, frame)?;
            if !matches!(flow, Flow::Normal) {
                return Ok(flow);
            }
        }
        Ok(Flow::Normal)
    }

    /// Whether a symbol comes from the synthesised core library, which the
    /// interpreter implements rather than runs.
    pub(crate) fn is_builtin_symbol(&self, symbol: SymbolId) -> bool {
        self.compilation.is_from_corlib(symbol)
    }

    /// How a value prints, which for an object is whatever its `ToString`
    /// says. `Console.WriteLine(object)` calls it, so this has to as well.
    pub(crate) fn printed(&mut self, value: Option<&Value>) -> Result<String, Signal> {
        let Some(value) = value else {
            return Ok(String::new());
        };
        if let Value::Object(object) = value {
            let ty = object.borrow().ty;
            if let Some(to_string) = self.to_string_of(ty) {
                let text = self.call_method(to_string, Some(value.clone()), Vec::new())?;
                return Ok(text.display());
            }
        }
        Ok(value.display())
    }

    /// The `ToString` a type provides, if it overrides the one every object
    /// inherits.
    fn to_string_of(&self, ty: SymbolId) -> Option<SymbolId> {
        self.overridden(ty, "ToString")
    }

    /// The method of `name` a type provides, where it overrides the one every
    /// object inherits. The core library's own is not one: that is the
    /// inherited behaviour rather than a replacement for it.
    pub(crate) fn overridden(&self, ty: SymbolId, name: &str) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        self.type_hierarchy(ty).into_iter().find_map(|candidate| {
            symbols
                .lookup(candidate, name)
                .iter()
                .copied()
                .find(|found| {
                    symbols.get(*found).kind == SymbolKind::Method
                        && !self.compilation.is_from_corlib(*found)
                })
        })
    }

    fn call_builtin(
        &mut self,
        method: SymbolId,
        this: Option<Value>,
        arguments: Vec<Value>,
    ) -> Eval {
        let name = self.compilation.symbols().qualified_name(method);
        match name.as_str() {
            "System.Console.WriteLine" => {
                let line = self.printed(arguments.first())?;
                self.output.push_str(&line);
                self.output.push('\n');
                Ok(Value::Null)
            }
            "System.Console.Write" => {
                let text = self.printed(arguments.first())?;
                self.output.push_str(&text);
                Ok(Value::Null)
            }
            "System.Math.Abs" => match arguments.first() {
                Some(Value::Double(value)) => Ok(Value::Double(value.abs())),
                Some(value) => Ok(Value::Int(value.as_int().unwrap_or(0).abs())),
                None => Ok(Value::Null),
            },
            "System.Math.Max" | "System.Math.Min" => {
                let (a, b) = (
                    arguments.first().and_then(Value::as_int).unwrap_or(0),
                    arguments.get(1).and_then(Value::as_int).unwrap_or(0),
                );
                Ok(Value::Int(if name.ends_with("Max") {
                    a.max(b)
                } else {
                    a.min(b)
                }))
            }
            "System.String.Concat" => {
                let joined: String = arguments.iter().map(Value::display).collect();
                Ok(Value::Str(joined.into()))
            }
            "System.String.Substring" => {
                let text = this.map_or(String::new(), |value| value.display());
                let start = arguments.first().and_then(Value::as_int).unwrap_or(0);
                let start = usize::try_from(start)
                    .unwrap_or(0)
                    .min(text.chars().count());
                Ok(Value::Str(
                    text.chars().skip(start).collect::<String>().into(),
                ))
            }
            "System.String.Contains" => {
                let text = this.map_or(String::new(), |value| value.display());
                let needle = arguments.first().map_or(String::new(), Value::display);
                Ok(Value::Bool(text.contains(&needle)))
            }
            "System.String.Trim" => {
                let text = this.map_or(String::new(), |value| value.display());
                Ok(Value::Str(text.trim().to_string().into()))
            }
            "System.Int32.TryParse" | "System.Double.TryParse" => {
                let text = arguments.first().map_or(String::new(), Value::display);
                let parsed = if name.starts_with("System.Int32") {
                    text.trim().parse::<i64>().ok().map(Value::Int)
                } else {
                    text.trim().parse::<f64>().ok().map(Value::Double)
                };
                // `TryParse` writes zero when it fails, which is what makes it
                // safe to read the result either way.
                if let Some(Value::Reference(reference)) = arguments.get(1) {
                    let zero = if name.starts_with("System.Int32") {
                        Value::Int(0)
                    } else {
                        Value::Double(0.0)
                    };
                    reference.write(parsed.clone().unwrap_or(zero));
                }
                Ok(Value::Bool(parsed.is_some()))
            }
            "System.Int32.Parse" | "System.Double.Parse" => {
                let text = arguments.first().map_or(String::new(), Value::display);
                if name.starts_with("System.Int32") {
                    text.trim().parse::<i64>().map(Value::Int).map_err(|_| {
                        Signal::Thrown(Value::Str(
                            "input string was not in a correct format".into(),
                        ))
                    })
                } else {
                    text.trim().parse::<f64>().map(Value::Double).map_err(|_| {
                        Signal::Thrown(Value::Str(
                            "input string was not in a correct format".into(),
                        ))
                    })
                }
            }
            "System.Collections.Generic.List`1.Add" => {
                let Some(Value::List(items)) = this else {
                    return Err(Signal::fault("Add called on something that is not a list"));
                };
                items
                    .borrow_mut()
                    .push(arguments.into_iter().next().unwrap_or(Value::Null));
                Ok(Value::Null)
            }
            "System.Collections.Generic.Dictionary`2.Add" => {
                let Some(Value::Map(entries)) = this else {
                    return Err(Signal::fault(
                        "Add called on something that is not a dictionary",
                    ));
                };
                let mut arguments = arguments.into_iter();
                let key = arguments.next().unwrap_or(Value::Null);
                let value = arguments.next().unwrap_or(Value::Null);
                // `Add` refuses a key that is already there; the indexer is
                // the one that overwrites.
                if entries.borrow().iter().any(|(other, _)| other.equals(&key)) {
                    return Err(Signal::Thrown(Value::Str(
                        "an item with the same key has already been added".into(),
                    )));
                }
                entries.borrow_mut().push((key, value));
                Ok(Value::Null)
            }
            other if other.ends_with("..ctor") => Ok(Value::Null),
            other => Err(Signal::fault(format!("{other} is not implemented"))),
        }
    }
}
