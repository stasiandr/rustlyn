//! The class the lambdas that capture nothing share.
//!
//! A lambda that reads no variable and no `this` needs no display class, and
//! could be a static method of the type. Roslyn makes it an instance method
//! of one class per type instead, `<>c`, whose one instance `<>9` is made by
//! its class constructor: a delegate over an instance method is cheaper to
//! call than one over a static method, and its `Target` is an object that can
//! be serialized. Each delegate made is cached in a static field,
//! `<>9__0_1`, and made again only while that is still null.

use rustlyn_semantics::{BoundBody, SymbolId, SymbolKind, Type, TypeKind};

use crate::emitter::{
    Closure, EmitError, Emitter, FieldPlan, MachineKey, MethodPlan, MethodSource, ParameterPlan,
    TypePlan, generic_param_flags, lambda_return, predicted, within,
};
use crate::il::Token;
use crate::metadata::{field_attributes, method_attributes, table, type_attributes};
use crate::signature::{
    ElementType, SigType, generic_method_signature, method_signature, type_def_or_ref,
};

/// Where a lambda that went to `<>c` is reached: the singleton, the field its
/// delegate is cached in, and its method.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SingletonLambda {
    pub(crate) instance: Token,
    pub(crate) cache: Token,
    pub(crate) method: Token,
}

/// A `<>c` class: the type it is nested in, and what its class constructor
/// needs to make the one instance.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Singleton {
    pub(crate) enclosing: SymbolId,
    pub(crate) constructor: Token,
    pub(crate) instance: Token,
}

/// The members of a `<>c` in a generic type, to be named under the
/// construction `<>c<!0, …>` once every type has a token.
pub(crate) struct PendingSingleton {
    token: Token,
    enclosing: SymbolId,
    arity: usize,
    lambdas: Vec<PendingLambda>,
}

/// One lambda of a pending `<>c`: its cache field's name and delegate type,
/// and its method's name, return type and parameters.
struct PendingLambda {
    key: (SymbolId, usize),
    cache: String,
    delegate: Type,
    name: String,
    returns: Type,
    parameters: Vec<Type>,
}

impl Emitter<'_> {
    /// Whether a lambda of a member that has no display class is a method of
    /// the type's `<>c` (Roslyn's `ClosureKind.Singleton`): it captures
    /// nothing, calls no local function (which would want the member's
    /// `this`), is made into a delegate rather than an expression tree, and
    /// is no state machine. Lambdas of a generic method, and those inside a
    /// generic local function, stay methods of the type: the class they
    /// would need is one per method, `<>c__0<T>`, which is not made here.
    pub(crate) fn goes_to_singleton(
        &mut self,
        body: &BoundBody,
        owner: SymbolId,
        index: usize,
    ) -> bool {
        let symbols = self.compilation.symbols();
        let Some(lambda) = body.lambdas.get(index) else {
            return false;
        };
        let is_delegate = body.types.get(&lambda.span).is_some_and(|ty| {
            ty.symbol()
                .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Delegate))
        });
        let generic_method = symbols
            .get(owner)
            .as_method()
            .is_some_and(|detail| !detail.type_parameters.is_empty());
        let in_a_type = self.enclosing_type(owner).is_some_and(|container| {
            symbols.get(container).kind == SymbolKind::NamedType
                && matches!(
                    symbols.get(container).type_kind(),
                    Some(
                        TypeKind::Class
                            | TypeKind::Struct
                            | TypeKind::Record
                            | TypeKind::RecordStruct
                    )
                )
        });
        let alone = |candidate: &rustlyn_semantics::BoundLambda| {
            candidate.captured.is_empty()
                && candidate.captured_parameters.is_empty()
                && !candidate.captures_this
                && candidate.calls.is_empty()
        };
        let span = lambda.span;
        let holds_function = body.local_functions.iter().any(|function| {
            self.compilation
                .declaration_node(function.symbol)
                .is_some_and(|node| within(node.span(), span))
        });
        let inner_alone = body
            .lambdas
            .iter()
            .filter(|inner| inner.span != span && within(inner.span, span))
            .all(alone);
        let key = MachineKey::Lambda { owner, index };
        is_delegate
            && in_a_type
            && !generic_method
            && alone(lambda)
            && inner_alone
            && !holds_function
            && self.function_generics_around(body, span).is_empty()
            && self.iterated_element(key).is_none()
            && !self.is_async_closure(key)
    }

    /// Plans the `<>c` of a type, with the lambdas that went to it.
    pub(crate) fn plan_singleton(
        &mut self,
        enclosing: SymbolId,
        lambdas: Vec<(SymbolId, usize)>,
        next_type: &mut u32,
        next_field: &mut u32,
        next_method: &mut u32,
    ) -> Result<Option<TypePlan>, EmitError> {
        if lambdas.is_empty() {
            return Ok(None);
        }
        let token = Token::new(table::TYPE_DEF, *next_type);
        *next_type += 1;
        let arity = self
            .compilation
            .symbols()
            .get(enclosing)
            .as_named_type()
            .map_or(0, |detail| detail.type_parameters.len());
        let coded = type_def_or_ref(0, token.0 & 0x00FF_FFFF);
        let inner_sig = if arity == 0 {
            SigType::Named {
                value_type: false,
                coded,
            }
        } else {
            SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..arity as u32).map(SigType::TypeParameter).collect(),
            }
        };
        let mut fields = Vec::new();
        let mut methods = Vec::new();
        let instance = Token::new(table::FIELD, *next_field);
        *next_field += 1;
        fields.push(FieldPlan {
            token: instance,
            name: "<>9".to_string(),
            ty: Type::Error,
            flags: field_attributes::PUBLIC
                | field_attributes::STATIC
                | field_attributes::INIT_ONLY,
            symbol: None,
            constant: None,
            sig: Some(inner_sig),
        });
        let static_constructor = Token::new(table::METHOD_DEF, *next_method);
        *next_method += 1;
        let constructor = Token::new(table::METHOD_DEF, *next_method);
        *next_method += 1;
        methods.push(MethodPlan {
            source: MethodSource::SingletonStaticConstructor,
            token: static_constructor,
            name: ".cctor".to_string(),
            flags: method_attributes::PRIVATE
                | method_attributes::STATIC
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
                | method_attributes::RT_SPECIAL_NAME,
            instance: false,
            return_type: Type::Void,
            parameters: Vec::new(),
            type_parameters: Vec::new(),
            impl_flags: 0,
            signature: None,
        });
        methods.push(MethodPlan {
            source: MethodSource::DisplayConstructor,
            token: constructor,
            name: ".ctor".to_string(),
            flags: method_attributes::PUBLIC
                | method_attributes::HIDE_BY_SIG
                | method_attributes::SPECIAL_NAME
                | method_attributes::RT_SPECIAL_NAME,
            instance: true,
            return_type: Type::Void,
            parameters: Vec::new(),
            type_parameters: Vec::new(),
            impl_flags: 0,
            signature: None,
        });
        let mut pending = PendingSingleton {
            token,
            enclosing,
            arity,
            lambdas: Vec::new(),
        };
        for (owner, index) in lambdas {
            let Some(body) = self.body_of(owner) else {
                continue;
            };
            let lambda = &body.lambdas[index];
            let delegate = body.types.get(&lambda.span).cloned().unwrap_or(Type::Error);
            let name = self.lambda_method_name(&body, owner, index, false);
            let cache_name = format!(
                "<>9__{}_{}",
                self.method_ordinal(owner),
                self.closure_ordinal(&body, Closure::Lambda(index))
            );
            let cache = Token::new(table::FIELD, *next_field);
            *next_field += 1;
            fields.push(FieldPlan {
                token: cache,
                name: cache_name.clone(),
                ty: delegate.clone(),
                flags: field_attributes::PUBLIC | field_attributes::STATIC,
                symbol: None,
                constant: None,
                sig: None,
            });
            let method = Token::new(table::METHOD_DEF, *next_method);
            *next_method += 1;
            self.lambdas.insert((owner, index), method);
            self.lambda_names.insert((owner, index), name.clone());
            let parameters: Vec<ParameterPlan> = lambda
                .parameters
                .iter()
                .map(|local| ParameterPlan {
                    by_ref: body.locals[local.0 as usize].by_ref,
                    symbol: None,
                    name: body.locals[local.0 as usize].name.clone(),
                    ty: body.locals[local.0 as usize].ty.clone(),
                })
                .collect();
            let returns = lambda_return(lambda);
            pending.lambdas.push(PendingLambda {
                key: (owner, index),
                cache: cache_name,
                delegate,
                name: name.clone(),
                returns: returns.clone(),
                parameters: parameters
                    .iter()
                    .map(|parameter| {
                        if parameter.by_ref {
                            Type::ByRef(Box::new(parameter.ty.clone()))
                        } else {
                            parameter.ty.clone()
                        }
                    })
                    .collect(),
            });
            let source = self.closure_source(MachineKey::Lambda { owner, index }, true, None);
            methods.push(MethodPlan {
                source,
                token: method,
                name,
                flags: method_attributes::ASSEMBLY | method_attributes::HIDE_BY_SIG,
                instance: true,
                return_type: returns,
                parameters,
                type_parameters: Vec::new(),
                impl_flags: 0,
                signature: None,
            });
            self.singleton_lambdas.insert(
                (owner, index),
                SingletonLambda {
                    instance,
                    cache,
                    method,
                },
            );
        }
        self.singleton_types.insert(
            token,
            Singleton {
                enclosing,
                constructor,
                instance,
            },
        );
        if arity > 0 {
            self.pending_singletons.push(pending);
        }
        Ok(Some(TypePlan {
            symbol: enclosing,
            token,
            fields,
            methods,
            properties: Vec::new(),
            display: None,
            iterator: None,
            machine: None,
            nested: None,
        }))
    }

    /// Names the members of every `<>c` in a generic type through
    /// `<>c<!0, …>`, now that every type has a token. The enclosing type's
    /// parameters and the class's are numbered alike, so the one
    /// construction serves the methods of both.
    pub(crate) fn resolve_singleton_members(&mut self) -> Result<(), EmitError> {
        for pending in std::mem::take(&mut self.pending_singletons) {
            let coded = type_def_or_ref(0, pending.token.0 & 0x00FF_FFFF);
            let sig = SigType::Constructed {
                value_type: false,
                coded,
                arguments: (0..pending.arity as u32)
                    .map(SigType::TypeParameter)
                    .collect(),
            };
            let mut blob = Vec::new();
            sig.write(&mut blob);
            let spec = self.references.type_spec(&mut self.metadata, &blob);
            self.display_generics = self
                .compilation
                .symbols()
                .get(pending.enclosing)
                .as_named_type()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            let instance = self.display_field_sig(spec, "<>9", &sig);
            let signature = method_signature(true, &SigType::Primitive(ElementType::Void), &[]);
            let constructor =
                self.references
                    .member_of_spec(&mut self.metadata, spec, ".ctor", &signature);
            for lambda in &pending.lambdas {
                let cache = self.display_field(spec, &lambda.cache, &lambda.delegate)?;
                let returns = self.sig_type(&lambda.returns)?;
                let mut written = Vec::with_capacity(lambda.parameters.len());
                for parameter in &lambda.parameters {
                    written.push(self.sig_type(parameter)?);
                }
                let signature = generic_method_signature(true, 0, &returns, &written);
                let method = self.references.member_of_spec(
                    &mut self.metadata,
                    spec,
                    &lambda.name,
                    &signature,
                );
                self.singleton_lambdas.insert(
                    lambda.key,
                    SingletonLambda {
                        instance,
                        cache,
                        method,
                    },
                );
            }
            if let Some(singleton) = self.singleton_types.get_mut(&pending.token) {
                singleton.constructor = constructor;
                singleton.instance = instance;
            }
            self.display_generics = Vec::new();
        }
        Ok(())
    }

    /// Writes the `TypeDef` of a `<>c`: nested, sealed, serializable, and
    /// declaring the enclosing type's parameters as its own.
    pub(crate) fn write_singleton_type(
        &mut self,
        plan: &TypePlan,
        enclosing: SymbolId,
        type_offsets: &[u32],
    ) -> Result<(), EmitError> {
        let object = self
            .references
            .type_ref_coded(&mut self.metadata, "System.Object");
        let token = self.metadata.add_type_def(
            type_attributes::NESTED_PRIVATE
                | type_attributes::SEALED
                | type_attributes::SERIALIZABLE
                | type_attributes::BEFORE_FIELD_INIT,
            "",
            "<>c",
            object,
        );
        predicted(token, plan.token, "a lambda singleton")?;
        if let Some(outer) = self.types.get(&enclosing).copied() {
            self.metadata.add_nested_class(token, outer);
        }
        self.mark_compiler_generated(token);
        let inherited = self
            .compilation
            .symbols()
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        let owner = (token.0 & 0x00FF_FFFF) << 1;
        self.display_generics = inherited.clone();
        for (number, parameter) in inherited.iter().enumerate() {
            let name = self.compilation.symbols().get(*parameter).name.clone();
            let flags = generic_param_flags(self.compilation.symbols(), *parameter) & !0x0003u16;
            self.metadata
                .add_generic_param(number as u16, flags, owner, &name);
            self.write_constraints(owner, number as u16, *parameter)?;
        }
        let written = self.write_members(plan, type_offsets);
        self.display_generics = Vec::new();
        written
    }
}
