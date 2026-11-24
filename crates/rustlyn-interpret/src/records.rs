//! The members a record gets from the language rather than from its source.
//!
//! A positional record is a shorthand: `record Point(int X, int Y);` means two
//! properties, a constructor that fills them, value equality, and a `ToString`
//! that prints what it holds. The declaration pass gives those members symbols
//! so that lookup and overload resolution find them like any others; what they
//! *do* has to come from somewhere, and for the interpreter it comes from here.

use rustlyn_semantics::{MethodKind, Modifiers, SymbolId, SymbolKind, TypeKind};
use rustlyn_syntax::SyntaxKind;

use crate::interpreter::{Eval, Interpreter, Signal};
use crate::value::Value;

impl Interpreter<'_> {
    /// Whether a symbol is a member the language gave a record.
    pub(crate) fn is_record_member(&self, method: SymbolId) -> bool {
        self.compilation()
            .symbols()
            .get(method)
            .as_method()
            .is_some_and(|detail| detail.method_kind == MethodKind::RecordSynthesized)
    }

    /// Whether a constructor is a record's positional one, which fills the
    /// properties its parameters named and has no body to run.
    pub(crate) fn is_record_constructor(&self, constructor: SymbolId) -> bool {
        let symbols = self.compilation().symbols();
        let Some(container) = symbols.get(constructor).container else {
            return false;
        };
        let is_record = matches!(
            symbols.get(container).type_kind(),
            Some(TypeKind::Record | TypeKind::RecordStruct)
        );
        is_record && self.body_of_is_absent(constructor)
    }

    /// A positional constructor is declared by its parameter list alone; one
    /// the source wrote has a `ConstructorDeclaration`.
    fn body_of_is_absent(&self, member: SymbolId) -> bool {
        self.compilation()
            .declaration_node(member)
            .is_none_or(|node| node.kind() != SyntaxKind::ConstructorDeclaration)
    }

    /// Fills a record's properties from the arguments its constructor took.
    pub(crate) fn run_record_constructor(
        &mut self,
        constructor: SymbolId,
        instance: Option<Value>,
        arguments: Vec<Value>,
    ) {
        let symbols = self.compilation().symbols();
        let parameters = symbols
            .get(constructor)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        let Some(Value::Object(object)) = instance else {
            return;
        };
        for (parameter, value) in parameters.iter().zip(arguments) {
            let name = self.compilation().symbols().get(*parameter).name.clone();
            object
                .borrow_mut()
                .fields
                .insert(Self::backing_field(&name), value);
        }
    }

    /// Runs one of the members the language gave a record.
    pub(crate) fn call_record_member(
        &mut self,
        method: SymbolId,
        this: Option<Value>,
        arguments: Vec<Value>,
    ) -> Eval {
        let symbols = self.compilation().symbols();
        let name = symbols.get(method).name.clone();
        let Some(container) = symbols.get(method).container else {
            return Ok(Value::Null);
        };
        match name.as_str() {
            "ToString" => {
                let text = self.record_to_string(container, this.as_ref())?;
                Ok(Value::Str(text.into()))
            }
            "Equals" => {
                let other = arguments.into_iter().next().unwrap_or(Value::Null);
                Ok(Value::Bool(self.record_equals(
                    container,
                    this.as_ref(),
                    Some(&other),
                )?))
            }
            "GetHashCode" => {
                // The same shape `HashCode.Combine` has, and the same promise:
                // equal records hash alike. Nothing here relies on the exact
                // number, and neither does C#.
                let mut hash: i64 = 17;
                for property in self.record_properties(container) {
                    let value = self.read_property(property, this.clone())?;
                    hash = hash.wrapping_mul(31).wrapping_add(hash_of(&value));
                }
                Ok(Value::Int(i64::from(hash as i32)))
            }
            "op_Equality" | "op_Inequality" => {
                let mut arguments = arguments.into_iter();
                let left = arguments.next().unwrap_or(Value::Null);
                let right = arguments.next().unwrap_or(Value::Null);
                let equal = match (&left, &right) {
                    // `null == null` is true, and a record is never equal to
                    // nothing.
                    (Value::Null, Value::Null) => true,
                    (Value::Null, _) | (_, Value::Null) => false,
                    _ => self.record_equals(container, Some(&left), Some(&right))?,
                };
                Ok(Value::Bool(equal == (name == "op_Equality")))
            }
            "<Clone>$" => match this {
                Some(Value::Object(object)) => {
                    let original = object.borrow();
                    Ok(Value::object(original.ty, original.fields.clone()))
                }
                _ => Err(Signal::fault("`<Clone>$` needs a record to copy")),
            },
            "Deconstruct" => {
                // Each property goes back through the reference it was handed.
                for (property, slot) in self.record_properties(container).into_iter().zip(arguments)
                {
                    let value = self.read_property(property, this.clone())?;
                    let Value::Reference(reference) = slot else {
                        return Err(Signal::fault("`Deconstruct` takes its parts by reference"));
                    };
                    reference.write(value);
                }
                Ok(Value::Null)
            }
            other => Err(Signal::fault(format!("{other} is not implemented"))),
        }
    }

    /// `Point { X = 1, Y = 2 }`, which is what a record prints as.
    pub(crate) fn record_to_string(
        &mut self,
        container: SymbolId,
        instance: Option<&Value>,
    ) -> Result<String, Signal> {
        let name = self.compilation().symbols().get(container).name.clone();
        let mut text = format!("{name} {{");
        for (index, property) in self.record_properties(container).into_iter().enumerate() {
            let label = self.compilation().symbols().get(property).name.clone();
            let value = self.read_property(property, instance.cloned())?;
            // A record inside a record prints as a record, because
            // `String.Concat` calls `ToString` on whatever it is handed.
            let printed = self.printed(Some(&value))?;
            if index > 0 {
                text.push(',');
            }
            text.push_str(&format!(" {label} = {printed}"));
        }
        text.push_str(" }");
        Ok(text)
    }

    /// Two records are equal when they are the same kind and hold the same
    /// things, which is the whole point of declaring one.
    fn record_equals(
        &mut self,
        container: SymbolId,
        left: Option<&Value>,
        right: Option<&Value>,
    ) -> Result<bool, Signal> {
        let runtime = |value: Option<&Value>| match value {
            Some(Value::Object(object)) => Some(object.borrow().ty),
            _ => None,
        };
        if runtime(left) != runtime(right) {
            return Ok(false);
        }
        for property in self.record_properties(container) {
            let a = self.read_property(property, left.cloned())?;
            let b = self.read_property(property, right.cloned())?;
            if !self.object_equals(&a, &b)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Whether two values are equal the way `object.Equals(a, b)` is: through
    /// whatever `Equals` the left one provides, which is how a record nested
    /// inside another is compared by value all the way down.
    fn object_equals(&mut self, left: &Value, right: &Value) -> Result<bool, Signal> {
        if let Value::Object(object) = left {
            let ty = object.borrow().ty;
            if let Some(equals) = self.overridden(ty, "Equals") {
                let answer = self.call_method(equals, Some(left.clone()), vec![right.clone()])?;
                return Ok(answer.as_bool().unwrap_or(false));
            }
        }
        Ok(left.equals(right))
    }

    /// The instance properties a record's equality and printing walk, in the
    /// order they were declared.
    pub(crate) fn record_properties(&self, container: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation().symbols();
        symbols
            .get(container)
            .members
            .iter()
            .copied()
            .filter(|member| {
                let symbol = symbols.get(*member);
                // `EqualityContract` is the language's too, and protected:
                // it is how records compare, not something one holds.
                symbol.kind == SymbolKind::Property
                    && !symbol.modifiers.contains(Modifiers::STATIC)
                    && symbol.as_property().is_none_or(|detail| {
                        detail.synthesized != Some(rustlyn_semantics::SynthesizedType::SystemType)
                    })
            })
            .collect()
    }
}

/// A number that two equal values agree on.
fn hash_of(value: &Value) -> i64 {
    match value {
        Value::Null => 0,
        Value::Bool(value) => i64::from(*value),
        Value::Str(text) => text.bytes().fold(7i64, |hash, byte| {
            hash.wrapping_mul(31).wrapping_add(i64::from(byte))
        }),
        other => other.as_int().unwrap_or(0),
    }
}
