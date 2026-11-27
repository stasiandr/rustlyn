//! The IL for the members the language gives a record.
//!
//! None of these has a body anywhere in the source, so there is nothing to
//! lower: each one is written out here from what the record holds, in the
//! shape Roslyn's `SynthesizedRecord*` symbols give them. Equality compares
//! every instance field through `EqualityComparer<T>.Default` after the
//! `EqualityContract`s (or the base record) agree, `ToString` is the record's
//! name around what `PrintMembers` appends, and a derived record chains each
//! of them to its base's.
//!
//! An anonymous type gets the same three `object` members, written the
//! simpler way it always had them.

use rustlyn_semantics::{Modifiers, SpecialType, SymbolId, SymbolKind, Type, TypeKind};
use rustlyn_syntax::SyntaxKind;

use crate::codegen::BodyEmitter;
use crate::emitter::{EmitError, Emitter, TypePlan};
use crate::il::{Instruction, Token};
use crate::signature::{ElementType, SigType};

/// The factor Roslyn combines hash codes with (`MethodBodySynthesizer`).
const HASH_FACTOR: i32 = -1_521_134_295;

impl Emitter<'_> {
    /// The record a record class derives from, if it derives from one: what
    /// its `Equals`, `GetHashCode`, `PrintMembers` and copy constructor
    /// chain to. `None` for a record whose base is `object`.
    pub(crate) fn record_base(&self, record: SymbolId) -> Option<Type> {
        let symbols = self.compilation.symbols();
        if symbols.get(record).type_kind() != Some(TypeKind::Record) {
            return None;
        }
        self.binder.base_types_of(record).into_iter().find(|base| {
            base.symbol().is_some_and(|base| {
                let symbol = symbols.get(base);
                match symbol.type_kind() {
                    Some(TypeKind::Record) => true,
                    // A record read from metadata is a class with a
                    // `<Clone>$`, which is how the language tells one.
                    Some(TypeKind::Class) => {
                        self.compilation.is_from_metadata(base)
                            && !symbols.lookup(base, "<Clone>$").is_empty()
                    }
                    _ => false,
                }
            })
        })
    }

    /// Whether a property is one a record's parameter list declared, rather
    /// than one its body wrote: it has no declaration of its own.
    pub(crate) fn is_positional_property(&self, property: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(property);
        symbol.kind == SymbolKind::Property
            && symbol.container.is_some_and(|container| {
                matches!(
                    symbols.get(container).type_kind(),
                    Some(TypeKind::Record | TypeKind::RecordStruct)
                )
            })
            && symbol
                .as_property()
                .is_some_and(|detail| detail.synthesized.is_none())
            && self.compilation.declaration_nodes(property).is_empty()
    }

    /// What `virtual`, `override`, `abstract` a member the language gave a
    /// record has, which Roslyn decides from the record and its base.
    pub(crate) fn record_member_modifiers(&self, member: SymbolId) -> Modifiers {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let Some(record) = symbol.container else {
            return Modifiers::empty();
        };
        let class = symbols.get(record).type_kind() == Some(TypeKind::Record);
        let sealed = symbols.get(record).modifiers.contains(Modifiers::SEALED);
        let abstract_record = symbols.get(record).modifiers.contains(Modifiers::ABSTRACT);
        let derived = self.record_base(record).is_some();
        // `virtual` where nothing is overridden and something may override,
        // `override` where the base record has one.
        let chained = if derived {
            Modifiers::OVERRIDE
        } else if sealed {
            Modifiers::empty()
        } else {
            Modifiers::VIRTUAL
        };
        match symbol.name.as_str() {
            "ToString" | "GetHashCode" => Modifiers::OVERRIDE,
            "Equals" if self.is_object_equals(member) => Modifiers::OVERRIDE,
            "Equals" if class && !sealed => Modifiers::VIRTUAL,
            "PrintMembers" | "EqualityContract" if class => chained,
            "<Clone>$" if abstract_record => {
                let mut modifiers = Modifiers::ABSTRACT;
                if derived {
                    modifiers.insert(Modifiers::OVERRIDE);
                }
                modifiers
            }
            "<Clone>$" => chained,
            _ => Modifiers::empty(),
        }
    }

    /// Whether an `Equals` takes an `object`, rather than the record.
    fn is_object_equals(&self, method: SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        symbols
            .get(method)
            .as_method()
            .and_then(|detail| detail.parameters.first().copied())
            .is_some_and(|parameter| {
                self.special_type_of(&self.type_of(parameter)) == Some(SpecialType::Object)
            })
    }
}

impl BodyEmitter<'_, '_> {
    /// `Point(int X, int Y)`, which fills the properties its parameters named
    /// before the initializers the body wrote run — the parameter list comes
    /// first in the source — and then chains to the base.
    pub(crate) fn emit_record_constructor(
        &mut self,
        plan: &TypePlan,
        constructor: SymbolId,
    ) -> Result<(), EmitError> {
        self.emit_parameter_captures(plan)?;
        let symbols = self.emitter.compilation.symbols();
        // A union's constructor keeps its case in `Value`, boxed where the
        // case is a value.
        if symbols
            .get(plan.symbol)
            .as_named_type()
            .is_some_and(|detail| detail.union_declaration)
        {
            return self.emit_union_constructor(plan, constructor);
        }
        // An anonymous type's constructor fills every property it has.
        let anonymous = symbols
            .get(plan.symbol)
            .as_named_type()
            .is_some_and(|detail| detail.anonymous);
        let parameters = symbols
            .get(constructor)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        for (position, parameter) in parameters.iter().enumerate() {
            let name = self
                .emitter
                .compilation
                .symbols()
                .get(*parameter)
                .name
                .clone();
            let Some(property) = self.record_property_named(plan.symbol, &name) else {
                continue;
            };
            // Only a property the parameter list declared is filled: one
            // the body wrote itself says with its own initializer what it
            // holds, if anything.
            if !anonymous && !self.emitter.is_positional_property(property) {
                continue;
            }
            let field = self.backing_field(plan, property)?;
            self.stream.emit(Instruction::LoadArgument(0));
            self.load_parameter_value(*parameter, position)?;
            self.stream.emit(Instruction::StoreField(field));
        }
        self.emit_instance_initializers(plan)?;
        // `record Derived(int X) : Base(X)` chains with what it was given,
        // which the binder read from the base list; without one, the base's
        // parameterless constructor is what runs.
        let initializer = self.chained_constructor();
        match initializer {
            Some((base, arguments)) => self.emit_constructor_call(plan, Some(base), &arguments)?,
            None => self.emit_implicit_base_constructor(plan)?,
        }
        Ok(())
    }

    /// `Value = value;` for a union's constructor.
    fn emit_union_constructor(
        &mut self,
        plan: &TypePlan,
        constructor: SymbolId,
    ) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let parameter = symbols
            .get(constructor)
            .as_method()
            .and_then(|detail| detail.parameters.first().copied())
            .ok_or_else(|| EmitError::new("a union constructor without its case"))?;
        let property = self
            .record_property_named(plan.symbol, "Value")
            .ok_or_else(|| EmitError::new("a union without a `Value`"))?;
        let field = self.backing_field(plan, property)?;
        let ty = self.emitter.type_of(parameter);
        self.stream.emit(Instruction::LoadArgument(0));
        self.load_parameter_value(parameter, 0)?;
        self.box_if_a_value(&ty)?;
        self.stream.emit(Instruction::StoreField(field));
        Ok(())
    }

    /// One of the members the language gives a record, by its name.
    pub(crate) fn emit_record_member(
        &mut self,
        plan: &TypePlan,
        method: SymbolId,
    ) -> Result<(), EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let name = symbols.get(method).name.clone();
        let anonymous = symbols
            .get(plan.symbol)
            .as_named_type()
            .is_some_and(|detail| detail.anonymous);
        if anonymous {
            return match name.as_str() {
                "ToString" => self.emit_anonymous_to_string(plan),
                "Equals" => self.emit_anonymous_equals(plan),
                "GetHashCode" => self.emit_anonymous_hash_code(plan),
                other => Err(EmitError::new(format!(
                    "cannot emit the anonymous type member `{other}`"
                ))),
            };
        }
        match name.as_str() {
            "Deconstruct" => self.emit_record_deconstruct(plan, method),
            "ToString" => self.emit_record_to_string(plan),
            "PrintMembers" => self.emit_record_print_members(plan),
            "Equals" if self.emitter.is_object_equals_of(method) => {
                self.emit_record_object_equals(plan)
            }
            "Equals" => self.emit_record_equals(plan),
            "GetHashCode" => self.emit_record_hash_code(plan),
            "op_Equality" => self.emit_record_equality(plan, true),
            "op_Inequality" => self.emit_record_equality(plan, false),
            "<Clone>$" => self.emit_record_clone(plan),
            ".ctor" => self.emit_record_copy_constructor(plan),
            "EqualityContract" => self.emit_record_equality_contract(plan),
            other => Err(EmitError::new(format!(
                "cannot emit the record member `{other}` yet"
            ))),
        }
    }

    /// `Deconstruct(out int X, out int Y)`, which writes each positional
    /// member — the property or field of the parameter's name, the record's
    /// own or inherited — through the reference it was handed.
    fn emit_record_deconstruct(
        &mut self,
        plan: &TypePlan,
        method: SymbolId,
    ) -> Result<(), EmitError> {
        let value_type = self.record_is_value_type(plan.symbol);
        let names: Vec<String> = {
            let symbols = self.emitter.compilation.symbols();
            symbols
                .get(method)
                .as_method()
                .map(|detail| {
                    detail
                        .parameters
                        .iter()
                        .map(|parameter| symbols.get(*parameter).name.clone())
                        .collect()
                })
                .unwrap_or_default()
        };
        let own = self.self_type.clone();
        for (position, name) in names.iter().enumerate() {
            let Some((member, receiver)) = self.positional_member(plan.symbol, name) else {
                return Err(EmitError::new(format!(
                    "no member `{name}` for a record's `Deconstruct` to read"
                )));
            };
            let ty = self.emitter.member_type(member, &receiver);
            // `ref int X => ref _x;` hands back where the value is.
            let (ty, by_reference) = match ty {
                Type::ByRef(inner) => (*inner, true),
                ty => (ty, false),
            };
            let kind = self.indirect_kind(&ty)?;
            self.stream
                .emit(Instruction::LoadArgument(position as u16 + 1));
            self.push_record_this();
            if self.emitter.compilation.symbols().get(member).kind == SymbolKind::Field {
                let token = self.field_token_on(member, Some(&receiver))?;
                self.stream.emit(Instruction::LoadField(token));
            } else {
                let getter = self
                    .emitter
                    .property_accessor(member, Some(&receiver), false)
                    .or_else(|_| self.emitter.property_accessor(member, Some(&own), false))?;
                let call = if value_type {
                    Instruction::Call(getter)
                } else {
                    Instruction::CallVirtual(getter)
                };
                self.stream.call_effect(call, 1, 1);
                if by_reference {
                    self.stream.emit(Instruction::LoadIndirect(kind));
                }
            }
            self.stream.emit(Instruction::StoreIndirect(kind));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// The property or field a positional parameter stands for, looked for
    /// in the record and then up its bases, with the type it is a member of.
    fn positional_member(&self, record: SymbolId, name: &str) -> Option<(SymbolId, Type)> {
        let symbols = self.emitter.compilation.symbols();
        let mut current = Some(self.emitter.binder.self_type(record));
        while let Some(ty) = current {
            let symbol = ty.symbol()?;
            let found = symbols.lookup(symbol, name).iter().copied().find(|member| {
                let member = symbols.get(*member);
                matches!(member.kind, SymbolKind::Property | SymbolKind::Field)
                    && !member.modifiers.contains(Modifiers::STATIC)
            });
            if let Some(member) = found {
                return Some((member, ty));
            }
            current = self
                .emitter
                .binder
                .base_types_of(symbol)
                .into_iter()
                .find(|base| {
                    base.symbol().is_some_and(|base| {
                        symbols.get(base).type_kind() != Some(TypeKind::Interface)
                    })
                });
        }
        None
    }

    /// `<Clone>$()`, which is `new R(this)` through the copy constructor.
    fn emit_record_clone(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let copy = self
            .record_copy_constructor(plan.symbol)
            .ok_or_else(|| EmitError::new("a record class without a copy constructor"))?;
        let own = self.emitter.own_construction(plan.symbol);
        let token = self.method_token_on(copy, own.as_ref())?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.call_effect(Instruction::NewObject(token), 1, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `R(R original)`, which hands the original to the base's copy
    /// constructor where the base is a record, and then copies every field
    /// declared here, backing fields included.
    fn emit_record_copy_constructor(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let base = self
            .emitter
            .binder
            .base_types_of(plan.symbol)
            .into_iter()
            .find_map(|base| {
                let symbol = base.symbol()?;
                let copy = self.record_copy_constructor(symbol)?;
                Some((base, copy))
            });
        match base {
            Some((base, copy)) => {
                let token = self.method_token_on(copy, Some(&base))?;
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::LoadArgument(1));
                self.stream.call_effect(Instruction::Call(token), 2, 0);
            }
            None => self.emit_base_constructor(plan)?,
        }
        for (token, _) in self.record_fields(plan)? {
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.emit(Instruction::LoadField(token));
            self.stream.emit(Instruction::StoreField(token));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// The copy constructor of a record class — the language's, or one the
    /// source wrote taking the record — if the type is one.
    pub(crate) fn record_copy_constructor(&self, record: SymbolId) -> Option<SymbolId> {
        let symbols = self.emitter.compilation.symbols();
        let own = self.emitter.binder.self_type(record);
        let constructors = symbols.lookup(record, ".ctor");
        constructors
            .iter()
            .copied()
            .find(|constructor| {
                symbols.get(*constructor).as_method().is_some_and(|detail| {
                    detail.method_kind == rustlyn_semantics::MethodKind::RecordSynthesized
                        && detail.parameters.len() == 1
                })
            })
            .or_else(|| {
                // A record read from metadata is a class with a `<Clone>$`.
                let from_metadata = self.emitter.compilation.is_from_metadata(record)
                    && !symbols.lookup(record, "<Clone>$").is_empty();
                if symbols.get(record).type_kind() != Some(TypeKind::Record) && !from_metadata {
                    return None;
                }
                constructors.iter().copied().find(|constructor| {
                    symbols.get(*constructor).as_method().is_some_and(|detail| {
                        detail.parameters.len() == 1
                            && !self.emitter.is_by_reference(Some(detail.parameters[0]))
                            && self.emitter.type_of(detail.parameters[0]).symbol() == own.symbol()
                    })
                })
            })
    }

    /// `EqualityContract => typeof(R)`.
    fn emit_record_equality_contract(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let own = self.emitter.binder.self_type(plan.symbol);
        let token = self.emitter.type_token(&own)?;
        let handle = self
            .emitter
            .references
            .type_ref_coded(&mut self.emitter.metadata, "System.RuntimeTypeHandle");
        let system_type = self.system_type_sig();
        let get_type = self.emitter.framework_member(
            "System.Type",
            "GetTypeFromHandle",
            false,
            &system_type,
            &[SigType::Named {
                value_type: true,
                coded: handle,
            }],
        );
        self.stream.emit(Instruction::LoadToken(token));
        self.stream.call_effect(Instruction::Call(get_type), 1, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `ToString()`: `R { ` and what `PrintMembers` appends, then `}`.
    fn emit_record_to_string(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let builder_type = self.string_builder_type()?;
        let builder = self.add_local(&builder_type)?;
        let constructor = self.emitter.framework_member(
            "System.Text.StringBuilder",
            ".ctor",
            true,
            &SigType::Primitive(ElementType::Void),
            &[],
        );
        self.stream
            .call_effect(Instruction::NewObject(constructor), 0, 1);
        self.stream.emit(Instruction::StoreLocal(builder));
        let name = self
            .emitter
            .compilation
            .symbols()
            .get(plan.symbol)
            .name
            .clone();
        for text in [name.as_str(), " { "] {
            self.stream.emit(Instruction::LoadLocal(builder));
            self.append_string(text);
        }
        let print = self
            .record_method(plan.symbol, "PrintMembers", |this, parameters| {
                parameters.len() == 1
                    && this.emitter.type_of(parameters[0]).symbol() == builder_type.symbol()
            })
            .ok_or_else(|| EmitError::new("a record without `PrintMembers`"))?;
        let own = self.self_type.clone();
        let token = self.method_token_on(print, Some(&own))?;
        let skip = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadLocal(builder));
        let call = if self.record_is_value_type(plan.symbol) {
            Instruction::Call(token)
        } else {
            Instruction::CallVirtual(token)
        };
        self.stream.call_effect(call, 2, 1);
        self.stream.emit(Instruction::BranchIfFalse(skip));
        self.stream.emit(Instruction::LoadLocal(builder));
        self.append_char(' ');
        self.stream.mark(skip);
        self.stream.emit(Instruction::LoadLocal(builder));
        self.append_char('}');
        self.stream.emit(Instruction::LoadLocal(builder));
        let to_string = self.object_to_string();
        self.stream
            .call_effect(Instruction::CallVirtual(to_string), 1, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `PrintMembers(StringBuilder builder)`: the base record's members,
    /// then `Name = value` for each public instance field and readable
    /// property, and whether it printed anything.
    fn emit_record_print_members(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let value_type = self.record_is_value_type(plan.symbol);
        let printable = self.record_printable_members(plan.symbol);
        let base = self.emitter.record_base(plan.symbol);
        match &base {
            Some(base) => {
                let builder_type = self.string_builder_type()?;
                let base_symbol = base
                    .symbol()
                    .ok_or_else(|| EmitError::new("a record base that is not a type"))?;
                let print = self
                    .inherited_method(base_symbol, "PrintMembers", |this, parameters| {
                        parameters.len() == 1
                            && this.emitter.type_of(parameters[0]).symbol() == builder_type.symbol()
                    })
                    .ok_or_else(|| EmitError::new("a base record without `PrintMembers`"))?;
                let token = self.method_token_on(print, Some(base))?;
                self.stream.emit(Instruction::LoadArgument(0));
                self.stream.emit(Instruction::LoadArgument(1));
                self.stream.call_effect(Instruction::Call(token), 2, 1);
                if printable.is_empty() {
                    self.stream.emit(Instruction::Ret);
                    return Ok(());
                }
                let skip = self.stream.label();
                self.stream.emit(Instruction::BranchIfFalse(skip));
                self.stream.emit(Instruction::LoadArgument(1));
                self.append_string(", ");
                self.stream.mark(skip);
            }
            None => {
                if printable.is_empty() {
                    self.stream.emit(Instruction::LoadInt32(0));
                    self.stream.emit(Instruction::Ret);
                    return Ok(());
                }
                // A record class can be printed inside itself; the runtime
                // says so before the stack runs out rather than after.
                if !value_type {
                    let ensure = self.emitter.framework_member(
                        "System.Runtime.CompilerServices.RuntimeHelpers",
                        "EnsureSufficientExecutionStack",
                        false,
                        &SigType::Primitive(ElementType::Void),
                        &[],
                    );
                    self.stream.call_effect(Instruction::Call(ensure), 0, 0);
                }
            }
        }
        let own = self.self_type.clone();
        let builder_sig = self.string_builder_sig();
        let append_object = self.emitter.framework_member(
            "System.Text.StringBuilder",
            "Append",
            true,
            &builder_sig,
            &[SigType::Primitive(ElementType::Object)],
        );
        for (index, member) in printable.iter().enumerate() {
            let name = self.emitter.compilation.symbols().get(*member).name.clone();
            let header = if index == 0 {
                format!("{name} = ")
            } else {
                format!(", {name} = ")
            };
            self.stream.emit(Instruction::LoadArgument(1));
            self.append_string(&header);

            // `ref int P` prints the `int` it refers to.
            let ty = match self.emitter.member_type(*member, &own) {
                Type::ByRef(inner) => *inner,
                ty => ty,
            };
            let field = self.emitter.compilation.symbols().get(*member).kind == SymbolKind::Field;
            // A `T` not known to be a struct is appended as an `object`, as
            // Roslyn does for anything whose type is not a value type: a
            // `null` in it prints as nothing rather than throwing.
            let struct_only = match &ty {
                Type::TypeParameter(parameter) => self
                    .emitter
                    .compilation
                    .symbols()
                    .get(*parameter)
                    .as_type_parameter()
                    .is_some_and(|detail| detail.value_type),
                _ => self.emitter.is_value_type(&ty),
            };
            self.stream.emit(Instruction::LoadArgument(1));
            if struct_only {
                // `builder.Append(value.ToString())`, called on the value
                // where it lies.
                let type_token = self.emitter.type_token(&ty)?;
                self.stream.emit(Instruction::LoadArgument(0));
                if field {
                    let token = self.field_token_on(*member, Some(&own))?;
                    self.stream.emit(Instruction::LoadFieldAddress(token));
                } else {
                    self.push_record_property(*member, value_type)?;
                    let slot = self.add_local(&ty)?;
                    self.stream.emit(Instruction::StoreLocal(slot));
                    self.stream.emit(Instruction::LoadLocalAddress(slot));
                }
                let to_string = self.object_to_string();
                self.stream.emit(Instruction::Constrained(type_token));
                self.stream
                    .call_effect(Instruction::CallVirtual(to_string), 1, 1);
                let append_string = self.append_string_token();
                self.stream
                    .call_effect(Instruction::CallVirtual(append_string), 2, 1);
            } else {
                self.stream.emit(Instruction::LoadArgument(0));
                if field {
                    let token = self.field_token_on(*member, Some(&own))?;
                    self.stream.emit(Instruction::LoadField(token));
                } else {
                    self.push_record_property(*member, value_type)?;
                }
                self.box_if_needed(&ty)?;
                self.stream
                    .call_effect(Instruction::CallVirtual(append_object), 2, 1);
            }
            self.stream.emit(Instruction::Pop);
        }
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// What `PrintMembers` prints: the public instance fields, and the
    /// public instance properties that can be read and are not indexers or
    /// overrides, in the order Roslyn declares them: the positional ones
    /// where the part with the parameter list begins — after what the
    /// parts before it declared, and before its own members and those of
    /// the parts after it.
    fn record_printable_members(&self, record: SymbolId) -> Vec<SymbolId> {
        let symbols = self.emitter.compilation.symbols();
        let printable = |member: &SymbolId| {
            let symbol = symbols.get(*member);
            if symbol.accessibility != rustlyn_semantics::Accessibility::Public
                || symbol.modifiers.contains(Modifiers::STATIC)
                || symbol.modifiers.contains(Modifiers::CONST)
            {
                return false;
            }
            match symbol.kind {
                SymbolKind::Field => true,
                SymbolKind::Property => symbol.as_property().is_some_and(|detail| {
                    !detail.is_indexer
                        && detail.has_get
                        && !symbol.modifiers.contains(Modifiers::OVERRIDE)
                }),
                _ => false,
            }
        };
        let members: Vec<SymbolId> = symbols
            .get(record)
            .members
            .iter()
            .copied()
            .filter(printable)
            .collect();
        let (positional, rest): (Vec<SymbolId>, Vec<SymbolId>) = members
            .into_iter()
            .partition(|member| self.emitter.is_positional_property(*member));
        let compilation = self.emitter.compilation;
        let primary = compilation
            .declaration_nodes(record)
            .iter()
            .copied()
            .find(|(tree, span)| {
                compilation
                    .trees()
                    .get(*tree)
                    .and_then(|tree| tree.root().find_node(*span))
                    .is_some_and(|node| node.child_of_kind(SyntaxKind::ParameterList).is_some())
            })
            .map(|(tree, span)| (tree, span.start()));
        let (before, after): (Vec<SymbolId>, Vec<SymbolId>) =
            rest.into_iter().partition(|member| {
                primary.is_some_and(|primary| {
                    compilation
                        .declaration_nodes(*member)
                        .first()
                        .is_some_and(|(tree, span)| (*tree, span.start()) < primary)
                })
            });
        before.into_iter().chain(positional).chain(after).collect()
    }

    /// `Equals(object obj)`: `Equals(obj as R)`, or for a record struct
    /// `obj is R r && Equals(r)`.
    fn emit_record_object_equals(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let own = self.self_type.clone();
        let record = self.emitter.type_token(&own)?;
        let equals = self.typed_equals(plan.symbol)?;
        let token = self.method_token_on(equals, Some(&own))?;
        if self.record_is_value_type(plan.symbol) {
            let no = self.stream.label();
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.emit(Instruction::IsInstance(record));
            self.stream.emit(Instruction::BranchIfFalse(no));
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.emit(Instruction::UnboxAny(record));
            self.stream.call_effect(Instruction::Call(token), 2, 1);
            self.stream.emit(Instruction::Ret);
            self.stream.mark(no);
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::Ret);
            return Ok(());
        }
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.emit(Instruction::IsInstance(record));
        self.stream
            .call_effect(Instruction::CallVirtual(token), 2, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// The record's `Equals(R)`, the language's or the source's.
    fn typed_equals(&self, record: SymbolId) -> Result<SymbolId, EmitError> {
        let own = self.emitter.binder.self_type(record);
        self.record_method(record, "Equals", |this, parameters| {
            parameters.len() == 1 && this.emitter.type_of(parameters[0]).symbol() == own.symbol()
        })
        .ok_or_else(|| EmitError::new("a record without an `Equals` of its own type"))
    }

    /// `Equals(Base other)` in a record derived from another: a sealed
    /// override of the base's that hands over to `Equals(object)`.
    pub(crate) fn emit_record_base_equals(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let own = self.self_type.clone();
        let object_equals = self
            .record_method(plan.symbol, "Equals", |this, parameters| {
                parameters.len() == 1
                    && this
                        .emitter
                        .special_type_of(&this.emitter.type_of(parameters[0]))
                        == Some(SpecialType::Object)
            })
            .ok_or_else(|| EmitError::new("a record without `Equals(object)`"))?;
        let token = self.method_token_on(object_equals, Some(&own))?;
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream
            .call_effect(Instruction::CallVirtual(token), 2, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `Equals(R other)`: the same instance, or one whose contract (or base
    /// record) agrees and whose every field is equal by
    /// `EqualityComparer<T>.Default`.
    fn emit_record_equals(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let value_type = self.record_is_value_type(plan.symbol);
        let no = self.stream.label();
        let yes = self.stream.label();
        if !value_type {
            // `(object)this == other`
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::BranchIfTrue(yes));
            match self.emitter.record_base(plan.symbol) {
                None => {
                    // `other != null && EqualityContract == other.EqualityContract`
                    self.stream.emit(Instruction::LoadArgument(1));
                    self.stream.emit(Instruction::BranchIfFalse(no));
                    let contract = self.equality_contract_getter(plan.symbol)?;
                    self.stream.emit(Instruction::LoadArgument(0));
                    self.stream
                        .call_effect(Instruction::CallVirtual(contract), 1, 1);
                    self.stream.emit(Instruction::LoadArgument(1));
                    self.stream
                        .call_effect(Instruction::CallVirtual(contract), 1, 1);
                    let type_sig = self.system_type_sig();
                    let op_equality = self.emitter.framework_member(
                        "System.Type",
                        "op_Equality",
                        false,
                        &SigType::Primitive(ElementType::Boolean),
                        &[type_sig.clone(), type_sig],
                    );
                    self.stream
                        .call_effect(Instruction::Call(op_equality), 2, 1);
                    self.stream.emit(Instruction::BranchIfFalse(no));
                }
                Some(base) => {
                    // `base.Equals((Base)other)`
                    let base_symbol = base
                        .symbol()
                        .ok_or_else(|| EmitError::new("a record base that is not a type"))?;
                    let equals = self
                        .inherited_method(base_symbol, "Equals", |this, parameters| {
                            parameters.len() == 1
                                && this.emitter.type_of(parameters[0]).symbol() == Some(base_symbol)
                        })
                        .ok_or_else(|| EmitError::new("a base record without `Equals`"))?;
                    let token = self.method_token_on(equals, Some(&base))?;
                    self.stream.emit(Instruction::LoadArgument(0));
                    self.stream.emit(Instruction::LoadArgument(1));
                    self.stream.call_effect(Instruction::Call(token), 2, 1);
                    self.stream.emit(Instruction::BranchIfFalse(no));
                }
            }
        }
        for (token, ty) in self.record_fields(plan)? {
            let (get_default, equals, _) = self.equality_comparer(&ty)?;
            self.stream
                .call_effect(Instruction::Call(get_default), 0, 1);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(token));
            if value_type {
                self.stream.emit(Instruction::LoadArgumentAddress(1));
            } else {
                self.stream.emit(Instruction::LoadArgument(1));
            }
            self.stream.emit(Instruction::LoadField(token));
            self.stream
                .call_effect(Instruction::CallVirtual(equals), 3, 1);
            self.stream.emit(Instruction::BranchIfFalse(no));
        }
        self.stream.mark(yes);
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::Ret);
        self.stream.mark(no);
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `GetHashCode()`: the contract's hash (or the base record's), then
    /// each field's folded in by Roslyn's factor.
    fn emit_record_hash_code(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let value_type = self.record_is_value_type(plan.symbol);
        let mut started = false;
        if !value_type {
            match self.emitter.record_base(plan.symbol) {
                None => {
                    let contract = self.equality_contract_getter(plan.symbol)?;
                    let type_type = self.system_type()?;
                    let (get_default, _, hash) = self.equality_comparer(&type_type)?;
                    self.stream
                        .call_effect(Instruction::Call(get_default), 0, 1);
                    self.stream.emit(Instruction::LoadArgument(0));
                    self.stream
                        .call_effect(Instruction::CallVirtual(contract), 1, 1);
                    self.stream
                        .call_effect(Instruction::CallVirtual(hash), 2, 1);
                }
                Some(base) => {
                    let base_symbol = base
                        .symbol()
                        .ok_or_else(|| EmitError::new("a record base that is not a type"))?;
                    let hash = self
                        .inherited_method(base_symbol, "GetHashCode", |_, parameters| {
                            parameters.is_empty()
                        })
                        .ok_or_else(|| EmitError::new("a base record without `GetHashCode`"))?;
                    let token = self.method_token_on(hash, Some(&base))?;
                    self.stream.emit(Instruction::LoadArgument(0));
                    self.stream.call_effect(Instruction::Call(token), 1, 1);
                }
            }
            started = true;
        }
        for (token, ty) in self.record_fields(plan)? {
            let (get_default, _, hash) = self.equality_comparer(&ty)?;
            if started {
                self.stream.emit(Instruction::LoadInt32(HASH_FACTOR));
                self.stream.emit(Instruction::Multiply);
            }
            self.stream
                .call_effect(Instruction::Call(get_default), 0, 1);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(token));
            self.stream
                .call_effect(Instruction::CallVirtual(hash), 2, 1);
            if started {
                self.stream.emit(Instruction::Add);
            }
            started = true;
        }
        if !started {
            self.stream.emit(Instruction::LoadInt32(0));
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// `left == right`: the same instance, or `left` not null and
    /// `left.Equals(right)`; `!=` is its negation. A record struct's is
    /// `left.Equals(right)` alone.
    fn emit_record_equality(&mut self, plan: &TypePlan, equal: bool) -> Result<(), EmitError> {
        let own = self.self_type.clone();
        if !equal {
            let equality = self
                .emitter
                .compilation
                .symbols()
                .lookup(plan.symbol, "op_Equality")
                .first()
                .copied()
                .ok_or_else(|| EmitError::new("a record without `==`"))?;
            let token = self.method_token_on(equality, Some(&own))?;
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.call_effect(Instruction::Call(token), 2, 1);
            self.stream.emit(Instruction::LoadInt32(0));
            self.stream.emit(Instruction::CompareEqual);
            self.stream.emit(Instruction::Ret);
            return Ok(());
        }
        let equals = self.typed_equals(plan.symbol)?;
        let equals = self.method_token_on(equals, Some(&own))?;
        if self.record_is_value_type(plan.symbol) {
            self.stream.emit(Instruction::LoadArgumentAddress(0));
            self.stream.emit(Instruction::LoadArgument(1));
            self.stream.call_effect(Instruction::Call(equals), 2, 1);
            self.stream.emit(Instruction::Ret);
            return Ok(());
        }
        let yes = self.stream.label();
        let no = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.emit(Instruction::CompareEqual);
        self.stream.emit(Instruction::BranchIfTrue(yes));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::BranchIfFalse(no));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream
            .call_effect(Instruction::CallVirtual(equals), 2, 1);
        self.stream.emit(Instruction::Ret);
        self.stream.mark(yes);
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::Ret);
        self.stream.mark(no);
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    // -- helpers ---------------------------------------------------------

    /// Every instance field the record declares — backing fields and the
    /// fields of field-like events included — named through the record's
    /// own construction, with its type: what equality compares, the hash
    /// folds in and the copy constructor copies. The positional properties'
    /// come first, as Roslyn declares them first.
    fn record_fields(&mut self, plan: &TypePlan) -> Result<Vec<(Token, Type)>, EmitError> {
        let receiver = self.emitter.binder.self_type(plan.symbol);
        let symbols = self.emitter.compilation.symbols();
        let mut positional = Vec::new();
        let mut rest = Vec::new();
        for field in &plan.fields {
            let Some(symbol) = field.symbol else { continue };
            let detail = symbols.get(symbol);
            if field.constant.is_some()
                || detail.modifiers.contains(Modifiers::STATIC)
                || detail.modifiers.contains(Modifiers::CONST)
            {
                continue;
            }
            if self.emitter.is_positional_property(symbol) {
                positional.push((symbol, field.ty.clone()));
            } else {
                rest.push((symbol, field.ty.clone()));
            }
        }
        positional.extend(rest);
        let mut fields = Vec::with_capacity(positional.len());
        for (symbol, _) in positional {
            let kind = self.emitter.compilation.symbols().get(symbol).kind;
            let token = match kind {
                SymbolKind::Property => self.backing_field(plan, symbol)?,
                _ => self.field_token_on(symbol, Some(&receiver))?,
            };
            let ty = self.emitter.member_type(symbol, &receiver);
            fields.push((token, ty));
        }
        Ok(fields)
    }

    /// `EqualityComparer<T>.get_Default`, `Equals(T, T)` and
    /// `GetHashCode(T)` for one `T`.
    fn equality_comparer(&mut self, ty: &Type) -> Result<(Token, Token, Token), EmitError> {
        let argument = self.emitter.sig_type(ty)?;
        let coded = self.emitter.references.type_ref_coded(
            &mut self.emitter.metadata,
            "System.Collections.Generic.EqualityComparer`1",
        );
        let constructed = SigType::Constructed {
            value_type: false,
            coded,
            arguments: vec![argument],
        };
        let mut blob = Vec::new();
        constructed.write(&mut blob);
        let spec = self
            .emitter
            .references
            .type_spec(&mut self.emitter.metadata, &blob);
        let own = SigType::Constructed {
            value_type: false,
            coded,
            arguments: vec![SigType::TypeParameter(0)],
        };
        let get_default = crate::signature::method_signature(false, &own, &[]);
        let equals = crate::signature::method_signature(
            true,
            &SigType::Primitive(ElementType::Boolean),
            &[SigType::TypeParameter(0), SigType::TypeParameter(0)],
        );
        let hash = crate::signature::method_signature(
            true,
            &SigType::Primitive(ElementType::I4),
            &[SigType::TypeParameter(0)],
        );
        let references = &mut self.emitter.references;
        let metadata = &mut self.emitter.metadata;
        Ok((
            references.member_of_spec(metadata, spec, "get_Default", &get_default),
            references.member_of_spec(metadata, spec, "Equals", &equals),
            references.member_of_spec(metadata, spec, "GetHashCode", &hash),
        ))
    }

    /// The getter of the record's `EqualityContract`, through its own
    /// construction.
    fn equality_contract_getter(&mut self, record: SymbolId) -> Result<Token, EmitError> {
        let symbols = self.emitter.compilation.symbols();
        let contract = symbols
            .lookup(record, "EqualityContract")
            .iter()
            .copied()
            .find(|member| symbols.get(*member).kind == SymbolKind::Property)
            .ok_or_else(|| EmitError::new("a record class without `EqualityContract`"))?;
        let own = self.self_type.clone();
        self.emitter.property_accessor(contract, Some(&own), false)
    }

    /// A method the record declares — the language's or the source's — of
    /// this name whose parameters pass the test.
    fn record_method(
        &self,
        record: SymbolId,
        name: &str,
        accept: impl Fn(&Self, &[SymbolId]) -> bool,
    ) -> Option<SymbolId> {
        let symbols = self.emitter.compilation.symbols();
        symbols.lookup(record, name).iter().copied().find(|member| {
            let symbol = symbols.get(*member);
            // `Equals(ref R other)` is some other method.
            !symbol.modifiers.contains(Modifiers::STATIC)
                && symbol.as_method().is_some_and(|detail| {
                    detail
                        .parameters
                        .iter()
                        .all(|parameter| !self.emitter.is_by_reference(Some(*parameter)))
                        && accept(self, &detail.parameters)
                })
        })
    }

    /// The same, looked for up the bases from `ty` on.
    fn inherited_method(
        &self,
        ty: SymbolId,
        name: &str,
        accept: impl Fn(&Self, &[SymbolId]) -> bool + Copy,
    ) -> Option<SymbolId> {
        let symbols = self.emitter.compilation.symbols();
        let mut current = Some(ty);
        while let Some(ty) = current {
            if let Some(found) = self.record_method(ty, name, accept) {
                return Some(found);
            }
            current = self
                .emitter
                .binder
                .base_types_of(ty)
                .into_iter()
                .filter_map(|base| base.symbol())
                .find(|base| symbols.get(*base).type_kind() != Some(TypeKind::Interface));
        }
        None
    }

    fn string_builder_type(&self) -> Result<Type, EmitError> {
        self.emitter
            .compilation
            .type_by_metadata_name("System.Text.StringBuilder")
            .map(Type::named)
            .ok_or_else(|| EmitError::new("`System.Text.StringBuilder` is not referenced"))
    }

    pub(crate) fn system_type(&self) -> Result<Type, EmitError> {
        self.emitter
            .compilation
            .type_by_metadata_name("System.Type")
            .map(Type::named)
            .ok_or_else(|| EmitError::new("`System.Type` is not referenced"))
    }

    fn string_builder_sig(&mut self) -> SigType {
        SigType::Named {
            value_type: false,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.Text.StringBuilder"),
        }
    }

    fn system_type_sig(&mut self) -> SigType {
        SigType::Named {
            value_type: false,
            coded: self
                .emitter
                .references
                .type_ref_coded(&mut self.emitter.metadata, "System.Type"),
        }
    }

    fn append_string_token(&mut self) -> Token {
        let builder = self.string_builder_sig();
        self.emitter.framework_member(
            "System.Text.StringBuilder",
            "Append",
            true,
            &builder,
            &[SigType::Primitive(ElementType::String)],
        )
    }

    /// `builder.Append("text");` with the builder already on the stack.
    fn append_string(&mut self, text: &str) {
        let token = self.append_string_token();
        let literal = self.emitter.metadata.user_string(text);
        self.stream.emit(Instruction::LoadString(literal));
        self.stream
            .call_effect(Instruction::CallVirtual(token), 2, 1);
        self.stream.emit(Instruction::Pop);
    }

    /// `builder.Append('c');` with the builder already on the stack.
    fn append_char(&mut self, c: char) {
        let builder = self.string_builder_sig();
        let token = self.emitter.framework_member(
            "System.Text.StringBuilder",
            "Append",
            true,
            &builder,
            &[SigType::Primitive(ElementType::Char)],
        );
        self.stream.emit(Instruction::LoadInt32(c as i32));
        self.stream
            .call_effect(Instruction::CallVirtual(token), 2, 1);
        self.stream.emit(Instruction::Pop);
    }

    fn object_to_string(&mut self) -> Token {
        self.emitter.framework_member(
            "System.Object",
            "ToString",
            true,
            &SigType::Primitive(ElementType::String),
            &[],
        )
    }

    // -- anonymous types -------------------------------------------------

    /// `{ a = 1, b = text }`, built the way an interpolated string is.
    fn emit_anonymous_to_string(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let properties = self.record_properties(plan.symbol);
        let object = SigType::Primitive(ElementType::Object);
        let object_token = self
            .emitter
            .references
            .type_ref(&mut self.emitter.metadata, "System.Object");
        let count = properties.len() * 2 + 2;
        self.stream.emit(Instruction::LoadInt32(count as i32));
        self.stream.emit(Instruction::NewArray(object_token));

        let mut index = 0i32;
        let text = |this: &mut Self, at: i32, literal: &str| {
            let token = this.emitter.metadata.user_string(literal);
            this.stream.emit(Instruction::Dup);
            this.stream.emit(Instruction::LoadInt32(at));
            this.stream.emit(Instruction::LoadString(token));
            this.stream.emit(Instruction::StoreElementRef);
        };
        text(self, index, "{");
        index += 1;
        for (position, property) in properties.iter().enumerate() {
            let label = self
                .emitter
                .compilation
                .symbols()
                .get(*property)
                .name
                .clone();
            let separator = if position == 0 { " " } else { ", " };
            text(self, index, &format!("{separator}{label} = "));
            index += 1;

            self.stream.emit(Instruction::Dup);
            self.stream.emit(Instruction::LoadInt32(index));
            self.push_record_this();
            self.push_record_property(*property, false)?;
            let ty = self.emitter.type_of(*property);
            self.box_if_needed(&ty)?;
            self.stream.emit(Instruction::StoreElementRef);
            index += 1;
        }
        text(self, index, " }");

        let concat = self.emitter.framework_member(
            "System.String",
            "Concat",
            false,
            &SigType::Primitive(ElementType::String),
            &[SigType::Array(Box::new(object))],
        );
        self.stream.call_effect(Instruction::Call(concat), 1, 1);
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// Two anonymous objects are equal when they are the same object, or the
    /// other is of the same shape and every field is equal by
    /// `EqualityComparer<T>.Default` (Roslyn's `AnonymousTypeEqualsMethodSymbol`).
    fn emit_anonymous_equals(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let own = self.self_type.clone();
        let record = self.emitter.type_token(&own)?;
        let other = self.add_local(&own)?;
        let yes = self.stream.label();
        let no = self.stream.label();
        self.stream.emit(Instruction::LoadArgument(1));
        self.stream.emit(Instruction::IsInstance(record));
        self.stream.emit(Instruction::StoreLocal(other));
        self.stream.emit(Instruction::LoadArgument(0));
        self.stream.emit(Instruction::LoadLocal(other));
        self.stream.emit(Instruction::CompareEqual);
        self.stream.emit(Instruction::BranchIfTrue(yes));
        self.stream.emit(Instruction::LoadLocal(other));
        self.stream.emit(Instruction::BranchIfFalse(no));
        for (token, ty) in self.record_fields(plan)? {
            let (get_default, equals, _) = self.equality_comparer(&ty)?;
            self.stream
                .call_effect(Instruction::Call(get_default), 0, 1);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(token));
            self.stream.emit(Instruction::LoadLocal(other));
            self.stream.emit(Instruction::LoadField(token));
            self.stream
                .call_effect(Instruction::CallVirtual(equals), 3, 1);
            self.stream.emit(Instruction::BranchIfFalse(no));
        }
        self.stream.mark(yes);
        self.stream.emit(Instruction::LoadInt32(1));
        self.stream.emit(Instruction::Ret);
        self.stream.mark(no);
        self.stream.emit(Instruction::LoadInt32(0));
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// Roslyn's hash of an anonymous object: a start worked out from the
    /// fields' names, then each field's hash folded in by its factor.
    fn emit_anonymous_hash_code(&mut self, plan: &TypePlan) -> Result<(), EmitError> {
        let properties = self.record_properties(plan.symbol);
        let mut start: i32 = 0;
        for property in &properties {
            let field = self.emitter.backing_field_name(*property);
            start = start
                .wrapping_mul(HASH_FACTOR)
                .wrapping_add(fnv_hash(&field));
        }
        self.stream.emit(Instruction::LoadInt32(start));
        for (token, ty) in self.record_fields(plan)? {
            let (get_default, _, hash) = self.equality_comparer(&ty)?;
            self.stream.emit(Instruction::LoadInt32(HASH_FACTOR));
            self.stream.emit(Instruction::Multiply);
            self.stream
                .call_effect(Instruction::Call(get_default), 0, 1);
            self.stream.emit(Instruction::LoadArgument(0));
            self.stream.emit(Instruction::LoadField(token));
            self.stream
                .call_effect(Instruction::CallVirtual(hash), 2, 1);
            self.stream.emit(Instruction::Add);
        }
        self.stream.emit(Instruction::Ret);
        Ok(())
    }

    /// Reads a property off whatever is on the stack.
    ///
    /// `value_type` says what is on the stack: a record struct is reached
    /// through its address, and a method on a value type is called rather
    /// than dispatched.
    fn push_record_property(
        &mut self,
        property: SymbolId,
        value_type: bool,
    ) -> Result<(), EmitError> {
        // Named through the record's own construction: a generic record's
        // `get_Item` returns `!0`, and the bare definition says nothing
        // about whose `!0` that is.
        let own = self.self_type.clone();
        let getter = self
            .emitter
            .property_accessor(property, Some(&own), false)
            .or_else(|_| self.emitter.property_accessor(property, None, false))?;
        let call = if value_type {
            Instruction::Call(getter)
        } else {
            Instruction::CallVirtual(getter)
        };
        self.stream.call_effect(call, 1, 1);
        // `ref int P` gives back where the value is; the value is what is
        // printed and compared.
        if let Type::ByRef(inner) = self.emitter.member_type(property, &own) {
            let kind = self.indirect_kind(&inner)?;
            self.stream.emit(Instruction::LoadIndirect(kind));
        }
        Ok(())
    }

    /// Whether the record is a `record struct`, which changes how every one of
    /// these bodies reaches `this`.
    fn record_is_value_type(&self, record: SymbolId) -> bool {
        self.emitter.compilation.symbols().get(record).type_kind()
            == Some(rustlyn_semantics::TypeKind::RecordStruct)
    }

    /// Puts `this` where a member call wants it.
    ///
    /// The same instruction either way: inside an instance method of a struct,
    /// argument zero *is* the address, and asking for the address of it would
    /// name the slot holding the pointer rather than the value.
    fn push_record_this(&mut self) {
        self.stream.emit(Instruction::LoadArgument(0));
    }

    /// `object.Equals(object, object)`, which the framework has and the core
    /// library here does not declare.
    fn record_property_named(&self, record: SymbolId, name: &str) -> Option<SymbolId> {
        let symbols = self.emitter.compilation.symbols();
        symbols
            .lookup(record, name)
            .iter()
            .copied()
            .find(|member| symbols.get(*member).kind == SymbolKind::Property)
    }

    /// The instance properties of an anonymous type, in the order they were
    /// declared.
    fn record_properties(&self, record: SymbolId) -> Vec<SymbolId> {
        let symbols = self.emitter.compilation.symbols();
        symbols
            .get(record)
            .members
            .iter()
            .copied()
            .filter(|member| {
                let symbol = symbols.get(*member);
                symbol.kind == SymbolKind::Property && !symbol.modifiers.contains(Modifiers::STATIC)
            })
            .collect()
    }
}

impl Emitter<'_> {
    /// Whether a record's `Equals` is the one taking `object`.
    pub(crate) fn is_object_equals_of(&self, method: SymbolId) -> bool {
        self.is_object_equals(method)
    }
}

/// The FNV-1a hash of a name, over its UTF-16 units, as Roslyn's
/// `Hash.GetFNVHashCode` computes it.
fn fnv_hash(text: &str) -> i32 {
    const OFFSET_BIAS: i32 = 2_166_136_261_u32 as i32;
    const PRIME: i32 = 16_777_619;
    text.encode_utf16().fold(OFFSET_BIAS, |hash, unit| {
        (hash ^ i32::from(unit)).wrapping_mul(PRIME)
    })
}
