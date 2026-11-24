//! Runtime values.
//!
//! The set is deliberately small: enough to run the subset of C# the rest of
//! the compiler understands, and no attempt at the exact width and overflow
//! behaviour of every numeric type. Integers are held as `i64` and narrowed
//! only where a cast says to.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

use rustlyn_semantics::SymbolId;

/// A value the interpreter can hold.
#[derive(Clone)]
pub enum Value {
    Null,
    Bool(bool),
    /// Every integral type, `char` aside.
    Int(i64),
    /// `float` and `double` alike.
    Double(f64),
    Char(char),
    Str(Rc<str>),
    /// An instance of a class or struct declared in source.
    Object(Rc<RefCell<Instance>>),
    /// An array, and also the backing of the built-in `List<T>`.
    Array(Rc<RefCell<Vec<Value>>>),
    /// A `List<T>`, which the interpreter provides rather than running.
    List(Rc<RefCell<Vec<Value>>>),
    /// A `Dictionary<TKey, TValue>`, held as pairs rather than as a hash map
    /// because a key is a `Value` and a `Value` is not hashable — an object
    /// key compares by identity, a string key by its text. A small dictionary
    /// is what the interpreter is for, so a linear scan is the honest choice
    /// rather than a hidden one.
    Map(Rc<RefCell<Vec<(Value, Value)>>>),
    /// A boxed enum value: the number, and the name it goes by.
    ///
    /// An unboxed enum *is* its number — `Colour.Green` and `4` are the same
    /// bits, and every operator on one is an operator on the number. Boxing is
    /// where the difference shows, because a boxed value carries its type:
    /// that is what makes `Console.WriteLine(c)` print `Green` rather than
    /// `4`. The name is worked out when the value is boxed, since nothing down
    /// here can reach the symbol table.
    Enumeration {
        ty: SymbolId,
        value: i64,
        name: Rc<str>,
    },
    /// A reference to a variable, which is what `ref` and `out` pass: the
    /// variable itself rather than what it holds.
    Reference(Rc<Reference>),
    /// A lambda, with the frame it was made in. A delegate over a method and
    /// a closure over a lambda are the same kind of value to whoever holds
    /// one, which is why both are invoked the same way.
    Closure(Rc<Closure>),
    /// A delegate: the method it will call, and what to call it on. In
    /// metadata this is an object with a target and a function pointer, and it
    /// is the same two things here.
    Delegate {
        method: SymbolId,
        receiver: Option<Rc<Value>>,
    },
}

/// The backing field of `Exception.Message`, which the interpreter fills in
/// when a core-library exception is made.
pub(crate) const EXCEPTION_MESSAGE: &str = "<Message>k__BackingField";

/// An object, with the fields its type declares.
pub struct Instance {
    pub ty: SymbolId,
    pub fields: HashMap<String, Value>,
}

impl Value {
    #[must_use]
    pub fn object(ty: SymbolId, fields: HashMap<String, Value>) -> Self {
        Self::Object(Rc::new(RefCell::new(Instance { ty, fields })))
    }

    #[must_use]
    pub fn array(items: Vec<Self>) -> Self {
        Self::Array(Rc::new(RefCell::new(items)))
    }

    #[must_use]
    pub fn list(items: Vec<Self>) -> Self {
        Self::List(Rc::new(RefCell::new(items)))
    }

    #[must_use]
    pub fn map(entries: Vec<(Self, Self)>) -> Self {
        Self::Map(Rc::new(RefCell::new(entries)))
    }

    /// Whether the value counts as true, which only a `bool` does.
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    #[must_use]
    pub const fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(value) => Some(*value),
            Self::Enumeration { value, .. } => Some(*value),
            Self::Char(ch) => Some(*ch as i64),
            _ => None,
        }
    }

    /// The value as a floating-point number, which an integer also is.
    #[must_use]
    pub fn as_double(&self) -> Option<f64> {
        match self {
            Self::Double(value) => Some(*value),
            Self::Enumeration { value, .. } => Some(*value as f64),
            Self::Int(value) => Some(*value as f64),
            Self::Char(ch) => Some(*ch as u32 as f64),
            _ => None,
        }
    }

    /// Whether the value is a floating-point one, which decides whether an
    /// operator computes in floating point.
    #[must_use]
    pub const fn is_double(&self) -> bool {
        matches!(self, Self::Double(_))
    }

    /// What `Console.WriteLine` prints.
    #[must_use]
    pub fn display(&self) -> String {
        match self {
            Self::Null => String::new(),
            Self::Bool(value) => {
                // C# prints these capitalised.
                if *value { "True" } else { "False" }.to_string()
            }
            Self::Int(value) => value.to_string(),
            Self::Double(value) => format_double(*value),
            Self::Char(value) => value.to_string(),
            Self::Str(value) => value.to_string(),
            // An exception prints as its message. The interpreter has no type
            // names to hand here, and the message is what both the
            // unhandled-exception report and `e.Message` are after.
            Self::Object(instance) => match instance.borrow().fields.get(EXCEPTION_MESSAGE) {
                Some(Self::Str(message)) => message.to_string(),
                _ => "<object>".to_string(),
            },
            Self::Array(items) | Self::List(items) => {
                format!("<{} items>", items.borrow().len())
            }
            Self::Map(entries) => format!("<{} entries>", entries.borrow().len()),
            Self::Enumeration { name, .. } => name.to_string(),
            Self::Closure(_) | Self::Delegate { .. } => "<delegate>".to_string(),
            Self::Reference(_) => "<reference>".to_string(),
        }
    }

    /// Whether two values are the same, by value for primitives and by
    /// identity for objects.
    #[must_use]
    pub fn equals(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Null, _) | (_, Self::Null) => false,
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Str(a), Self::Str(b)) => a == b,
            (Self::Char(a), Self::Char(b)) => a == b,
            (Self::Object(a), Self::Object(b)) => Rc::ptr_eq(a, b),
            (Self::Array(a), Self::Array(b)) | (Self::List(a), Self::List(b)) => Rc::ptr_eq(a, b),
            (Self::Map(a), Self::Map(b)) => Rc::ptr_eq(a, b),
            (Self::Closure(a), Self::Closure(b)) => Rc::ptr_eq(a, b),
            (Self::Reference(a), Self::Reference(b)) => Rc::ptr_eq(a, b),
            // Two delegates are equal when they would call the same thing,
            // which is what `Delegate.Equals` promises.
            (
                Self::Delegate {
                    method: a,
                    receiver: left,
                },
                Self::Delegate {
                    method: b,
                    receiver: right,
                },
            ) => {
                a == b
                    && match (left, right) {
                        (None, None) => true,
                        (Some(left), Some(right)) => left.equals(right),
                        _ => false,
                    }
            }
            _ => match (self.as_double(), other.as_double()) {
                (Some(a), Some(b)) => a == b,
                _ => false,
            },
        }
    }
}

/// Prints a double the way C# does: no trailing `.0`, and `E` notation only
/// when the number is far from 1.
fn format_double(value: f64) -> String {
    if value.is_nan() {
        return "NaN".to_string();
    }
    if value.is_infinite() {
        return if value > 0.0 { "∞" } else { "-∞" }.to_string();
    }
    if value == value.trunc() && value.abs() < 1e15 {
        return format!("{}", value as i64);
    }
    let mut text = format!("{value}");
    if text.contains('e') {
        text = text.replace('e', "E");
    }
    text
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Null => f.write_str("null"),
            Self::Object(instance) => write!(f, "object({:?})", instance.borrow().ty),
            other => f.write_str(&other.display()),
        }
    }
}

impl fmt::Debug for Instance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Instance").field("ty", &self.ty).finish()
    }
}

/// A lambda and what it closed over: its parameters, its body with a locals
/// table of its own, and the frame it was made in.
///
/// The body carries its own table rather than pointing at the method it was
/// written in, because the lambda outlives that method — the delegate can be
/// called long after `Main` returned. The frame, by contrast, is shared: a
/// captured variable has to be the variable and not a copy of it.
pub struct Closure {
    pub(crate) parameters: Vec<rustlyn_semantics::LocalId>,
    pub(crate) body: Rc<rustlyn_semantics::BoundBody>,
    pub(crate) frame: crate::interpreter::CapturedFrame,
}

impl fmt::Debug for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Closure")
            .field("parameters", &self.parameters.len())
            .finish_non_exhaustive()
    }
}

/// Where a `ref` or `out` argument points.
///
/// A reference is not a value: it is somewhere a value lives, and writing
/// through it has to be seen by whoever owns that somewhere. Each variant is
/// one of the places C# lets a variable be.
#[derive(Debug)]
pub enum Reference {
    Local {
        slots: Rc<RefCell<Vec<Value>>>,
        index: usize,
    },
    Argument {
        slots: Rc<RefCell<HashMap<SymbolId, Value>>>,
        parameter: SymbolId,
    },
    Field {
        object: Rc<RefCell<Instance>>,
        name: String,
    },
    Element {
        items: Rc<RefCell<Vec<Value>>>,
        index: usize,
    },
    /// A static field, which the interpreter keeps rather than the frame.
    Static(SymbolId),
}

impl Reference {
    /// What the variable holds now.
    #[must_use]
    pub fn read(&self) -> Option<Value> {
        Some(match self {
            Self::Local { slots, index } => slots.borrow().get(*index)?.clone(),
            Self::Argument { slots, parameter } => slots.borrow().get(parameter)?.clone(),
            Self::Field { object, name } => object.borrow().fields.get(name)?.clone(),
            Self::Element { items, index } => items.borrow().get(*index)?.clone(),
            // Read through the interpreter, which owns the statics.
            Self::Static(_) => return None,
        })
    }

    /// Puts a value where the variable is.
    pub fn write(&self, value: Value) -> bool {
        match self {
            Self::Local { slots, index } => match slots.borrow_mut().get_mut(*index) {
                Some(slot) => *slot = value,
                None => return false,
            },
            Self::Argument { slots, parameter } => {
                slots.borrow_mut().insert(*parameter, value);
            }
            Self::Field { object, name } => {
                object.borrow_mut().fields.insert(name.clone(), value);
            }
            Self::Element { items, index } => match items.borrow_mut().get_mut(*index) {
                Some(slot) => *slot = value,
                None => return false,
            },
            Self::Static(_) => return false,
        }
        true
    }
}
