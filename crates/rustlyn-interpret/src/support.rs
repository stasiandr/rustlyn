//! Objects, statics, properties and virtual dispatch.

use std::collections::HashMap;

use rustlyn_semantics::{BoundStatementKind, Modifiers, SymbolId, SymbolKind, TypeKind};

use crate::interpreter::{Eval, Interpreter, Signal};
use crate::value::Value;

impl Interpreter<'_> {
    /// The hidden field an automatic property stores its value in.
    pub(crate) fn backing_field(name: &str) -> String {
        format!("<{name}>k__BackingField")
    }

    // -- statics -----------------------------------------------------------

    pub(crate) fn static_value(&mut self, field: SymbolId) -> Value {
        if let Some(value) = self.statics.get(&field) {
            return value.clone();
        }
        // A static field is initialised the first time it is read, which is
        // close enough to what `beforefieldinit` allows.
        let value = self
            .field_initializer(field, None)
            .unwrap_or_else(|_| self.default_value(field));
        self.statics.insert(field, value.clone());
        value
    }

    pub(crate) fn set_static(&mut self, field: SymbolId, value: Value) {
        self.statics.insert(field, value);
    }

    /// What a field holds before anything is assigned to it.
    pub(crate) fn default_value(&self, member: SymbolId) -> Value {
        let mut sink = rustlyn_semantics::Diagnostics::new();
        let ty = self.binder.type_of(member, &mut sink);
        self.zero_of(&ty)
    }

    /// Runs a field's `= ...`, if it has one.
    fn field_initializer(&mut self, field: SymbolId, this: Option<Value>) -> Eval {
        let Some(body) = self.body_of(field) else {
            return Ok(self.default_value(field));
        };
        let Some(value) = body
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                BoundStatementKind::Return(Some(value)) => Some(value.clone()),
                _ => None,
            })
        else {
            return Ok(self.default_value(field));
        };
        self.eval_detached(&body, &value, this)
    }

    // -- objects -----------------------------------------------------------

    /// Makes an object: its fields zeroed, its initialisers run, then its
    /// constructor.
    pub(crate) fn construct(&mut self, ty: SymbolId, arguments: Vec<Value>) -> Eval {
        let mut fields = HashMap::new();
        for owner in self.type_hierarchy(ty) {
            for member in self.compilation().symbols().get(owner).members.clone() {
                let symbol = self.compilation().symbols().get(member);
                if symbol.modifiers.contains(Modifiers::STATIC) {
                    continue;
                }
                match symbol.kind {
                    SymbolKind::Field => {
                        let name = symbol.name.clone();
                        fields.insert(name, self.default_value(member));
                    }
                    SymbolKind::Property if self.binder.is_automatic_property(member) => {
                        let name = Self::backing_field(&symbol.name);
                        fields.insert(name, self.default_value(member));
                    }
                    _ => {}
                }
            }
        }

        let instance = Value::object(ty, fields);

        // Field initialisers run against the new object, base first.
        for owner in self.type_hierarchy(ty).into_iter().rev() {
            for member in self.compilation().symbols().get(owner).members.clone() {
                let symbol = self.compilation().symbols().get(member);
                if symbol.kind != SymbolKind::Field || symbol.modifiers.contains(Modifiers::STATIC)
                {
                    continue;
                }
                if !symbol.as_field().is_some_and(|field| field.has_initializer) {
                    continue;
                }
                let name = symbol.name.clone();
                let value = self.field_initializer(member, Some(instance.clone()))?;
                if let Value::Object(object) = &instance {
                    object.borrow_mut().fields.insert(name, value);
                }
            }
        }

        // Then the constructor whose parameter count fits. A base constructor
        // is reached by the `: base(...)` the bound body carries, so nothing
        // here has to chain.
        let constructors: Vec<_> = self.compilation().symbols().lookup(ty, ".ctor").to_vec();
        if let Some(constructor) = constructors.into_iter().find(|candidate| {
            self.compilation()
                .symbols()
                .get(*candidate)
                .as_method()
                .is_some_and(|detail| detail.parameters.len() == arguments.len())
        }) {
            self.run_constructor_body(constructor, Some(instance.clone()), arguments)?;
        }
        Ok(instance)
    }

    // -- properties --------------------------------------------------------

    pub(crate) fn read_property(&mut self, property: SymbolId, receiver: Option<Value>) -> Eval {
        let symbols = self.compilation().symbols();
        let name = symbols.get(property).name.clone();

        // A property with a body is a method; one without is storage.
        if !self.binder.is_automatic_property(property) {
            if self.is_builtin_symbol(property) {
                return self.builtin_property(&name, receiver);
            }
            // The getter is a member of its own, unless the property is
            // expression-bodied — then the property declaration is the getter.
            let getter = symbols
                .get(property)
                .as_property()
                .and_then(|detail| detail.getter)
                .unwrap_or(property);
            return self.call_method(getter, receiver, Vec::new());
        }

        let field = Self::backing_field(&name);
        if symbols.get(property).modifiers.contains(Modifiers::STATIC) {
            return Ok(self.statics.get(&property).cloned().unwrap_or(Value::Null));
        }
        match receiver {
            Some(Value::Object(object)) => Ok(object
                .borrow()
                .fields
                .get(&field)
                .cloned()
                .unwrap_or(Value::Null)),
            Some(other) => self.builtin_property_of(&name, &other),
            None => Err(Signal::Thrown(Value::Str(
                "object reference not set to an instance of an object".into(),
            ))),
        }
    }

    pub(crate) fn write_property(
        &mut self,
        property: SymbolId,
        receiver: Option<Value>,
        value: Value,
    ) -> Result<(), Signal> {
        let symbols = self.compilation().symbols();
        let name = symbols.get(property).name.clone();
        if let Some(setter) = symbols
            .get(property)
            .as_property()
            .and_then(|detail| detail.setter)
        {
            self.call_method(setter, receiver, vec![value])?;
            return Ok(());
        }
        if symbols.get(property).modifiers.contains(Modifiers::STATIC) {
            self.statics.insert(property, value);
            return Ok(());
        }
        let field = Self::backing_field(&name);
        match receiver {
            Some(Value::Object(object)) => {
                object.borrow_mut().fields.insert(field, value);
                Ok(())
            }
            _ => Err(Signal::Thrown(Value::Str(
                "object reference not set to an instance of an object".into(),
            ))),
        }
    }

    /// The properties the core library declares and the interpreter provides.
    fn builtin_property(&mut self, name: &str, receiver: Option<Value>) -> Eval {
        match receiver {
            Some(value) => self.builtin_property_of(name, &value),
            None => Ok(Value::Null),
        }
    }

    fn builtin_property_of(&self, name: &str, receiver: &Value) -> Eval {
        match (name, receiver) {
            ("Length", Value::Str(text)) => Ok(Value::Int(text.chars().count() as i64)),
            ("Length", Value::Array(items)) | ("Count", Value::List(items)) => {
                Ok(Value::Int(items.borrow().len() as i64))
            }
            ("Count", Value::Map(entries)) => Ok(Value::Int(entries.borrow().len() as i64)),
            ("Message", value) => Ok(value.clone()),
            (name, value) => Err(Signal::fault(format!(
                "{} has no property {name}",
                value.display()
            ))),
        }
    }

    // -- dispatch ----------------------------------------------------------

    /// Whether a core-library type is an exception, which is the one kind of
    /// built-in the interpreter makes a real object of.
    pub(crate) fn derives_from_exception(&self, ty: SymbolId) -> bool {
        let symbols = self.compilation().symbols();
        self.type_hierarchy(ty)
            .into_iter()
            .any(|base| symbols.qualified_name(base) == "System.Exception")
    }

    /// A type and everything it derives from, most derived first.
    pub(crate) fn type_hierarchy(&self, ty: SymbolId) -> Vec<SymbolId> {
        let mut chain = vec![ty];
        let mut current = ty;
        // Broken code can make this circular; stop rather than hang.
        for _ in 0..16 {
            match self.base_type_of(current) {
                Some(base) => {
                    chain.push(base);
                    current = base;
                }
                None => break,
            }
        }
        chain
    }

    /// The base class of a type, ignoring the interfaces beside it.
    fn base_type_of(&self, ty: SymbolId) -> Option<SymbolId> {
        self.binder.base_types_of(ty).into_iter().find_map(|base| {
            let symbol = base.symbol()?;
            let is_class = self
                .compilation()
                .symbols()
                .get(symbol)
                .type_kind()
                .is_some_and(|kind| !matches!(kind, TypeKind::Interface));
            is_class.then_some(symbol)
        })
    }

    /// The override of `method` that the runtime type provides, which is what
    /// a virtual call reaches.
    ///
    /// This is the one decision binding could not make: it depends on what the
    /// receiver turned out to be, and nothing before run time knows that.
    pub(crate) fn most_derived(&self, method: SymbolId, runtime: SymbolId) -> SymbolId {
        let symbols = self.compilation().symbols();
        let name = symbols.get(method).name.clone();
        let arity = symbols
            .get(method)
            .as_method()
            .map_or(0, |detail| detail.parameters.len());

        for ty in self.type_hierarchy(runtime) {
            if let Some(found) = symbols.lookup(ty, &name).iter().copied().find(|candidate| {
                symbols.get(*candidate).kind == SymbolKind::Method
                    && symbols
                        .get(*candidate)
                        .as_method()
                        .is_some_and(|detail| detail.parameters.len() == arity)
            }) {
                return found;
            }
        }
        method
    }
}
