//! The delegates made from static method groups, kept in static fields.
//!
//! Since C# 11 `Func<int, int> f = Helper.Twice;` does not make a delegate
//! each time it runs: the delegate is kept in a field of a class nested in
//! the type the code is in, `<>O`, and made again only while that is still
//! null. Two conversions of the same method to the same delegate type are
//! then the same object, which a program can see (`ReferenceEquals`).
//!
//! A field is the delegate of one method (with its type arguments) converted
//! to one delegate type, named `<0>__Twice` after its number in the class. The
//! class a conversion goes to depends on what the delegate type mentions:
//!
//! * nothing generic, or only the type's own parameters: the type's `<>O`,
//!   which declares those parameters;
//! * a type parameter of the method the code is in: a class of that method,
//!   `<M>O__3_0`, which declares the type's parameters and then the method's.
//!
//! Not every conversion is cached. Only a method group that names a static
//! method (or a `static` local function) and was *converted*: `new D(M)` makes
//! a delegate anew, as does a method group closed over a receiver, which is an
//! instance method or an extension method called on a value. Nothing is cached
//! where the code runs once anyway, in a static constructor and the static
//! field initializers that run in it.
//!
//! The fields are given tokens while the type is planned, from what its
//! bodies convert, since a type's fields have to be contiguous rows; a
//! conversion met while a body is emitted finds its field by what it
//! converts, and where it finds none the delegate is simply made.

use rustlyn_semantics::{
    BoundBody, BoundExpressionKind, MethodKind, Modifiers, SymbolId, SymbolKind, Symbols, Type,
};
use std::collections::HashMap;

use rustlyn_syntax::SyntaxKind;

use crate::emitter::{EmitError, Emitter, FieldPlan, TypePlan, generic_param_flags};
use crate::il::Token;
use crate::metadata::{field_attributes, table, type_attributes};
use crate::signature::{SigType, field_signature, type_def_or_ref};

/// Which class a cached delegate lives in.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum CacheHome {
    /// The type's own `<>O`.
    Type,
    /// The class of a generic method, for a delegate type that mentions one
    /// of its parameters.
    Method(SymbolId),
}

/// What a cached delegate is of: where, which method, and which delegate.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct CacheKey {
    pub(crate) enclosing: SymbolId,
    pub(crate) home: CacheHome,
    pub(crate) method: SymbolId,
    pub(crate) type_arguments: Vec<Type>,
    pub(crate) delegate: Type,
}

/// A planned `<>O`.
#[derive(Clone, Debug)]
pub(crate) struct CacheClass {
    pub(crate) enclosing: SymbolId,
    pub(crate) name: String,
    /// The parameters it declares, the type's first.
    pub(crate) parameters: Vec<SymbolId>,
    /// How many of them are the type's.
    pub(crate) type_arity: usize,
}

/// A planned field: its row, its name, and the class's token.
#[derive(Clone, Debug)]
pub(crate) struct CacheField {
    pub(crate) token: Token,
    pub(crate) class: Token,
    pub(crate) name: String,
}

/// Whether a member's body runs in the class constructor: its own, or the
/// initializer of a static field, event or automatic property. Whatever runs
/// once keeps nothing in a field.
pub(crate) fn runs_in_static_constructor(symbols: &Symbols, member: SymbolId) -> bool {
    let detail = symbols.get(member);
    if !detail.modifiers.contains(Modifiers::STATIC) {
        return false;
    }
    match detail.kind {
        SymbolKind::Field | SymbolKind::Event => true,
        SymbolKind::Property => detail
            .as_property()
            .is_some_and(|property| property.backing_field.is_some()),
        SymbolKind::Method => {
            detail.name == ".cctor"
                || detail
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::StaticConstructor)
        }
        _ => false,
    }
}

/// A class being collected while a type is planned.
struct Building {
    home: CacheHome,
    name: String,
    parameters: Vec<SymbolId>,
    type_arity: usize,
    fields: Vec<FieldPlan>,
}

impl Emitter<'_> {
    /// Plans the `<>O` classes of a type: one for the type itself, and one
    /// for each generic method whose conversions need its parameters.
    pub(crate) fn plan_delegate_caches(
        &mut self,
        symbol: SymbolId,
        next_type: &mut u32,
        next_field: &mut u32,
    ) -> Result<Vec<TypePlan>, EmitError> {
        let symbols = self.compilation.symbols();
        let type_parameters = symbols
            .get(symbol)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        let mut classes: Vec<Building> = Vec::new();
        let mut found: HashMap<CacheKey, (usize, usize)> = HashMap::new();
        for owner in self.owners_of_bodies(&[symbol]) {
            if runs_in_static_constructor(self.compilation.symbols(), owner) {
                continue;
            }
            let Some(body) = self.body_of(owner) else {
                continue;
            };
            let method_parameters = self
                .compilation
                .symbols()
                .get(owner)
                .as_method()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            for (delegate, method, type_arguments) in self.cacheable_conversions(&body) {
                let Some(home) = self.cache_home(
                    owner,
                    &type_parameters,
                    &method_parameters,
                    &delegate,
                    &type_arguments,
                ) else {
                    continue;
                };
                let key = CacheKey {
                    enclosing: symbol,
                    home,
                    method,
                    type_arguments,
                    delegate: delegate.clone(),
                };
                if found.contains_key(&key) {
                    continue;
                }
                let class = match classes.iter().position(|class| class.home == home) {
                    Some(class) => class,
                    None => {
                        let (name, parameters) = match home {
                            CacheHome::Type => ("<>O".to_string(), type_parameters.clone()),
                            CacheHome::Method(method) => (
                                format!(
                                    "<{}>O__{}_0{}",
                                    self.compilation.symbols().get(method).name,
                                    self.method_ordinal(method),
                                    // A generic class is named for the
                                    // parameters it adds to its type's.
                                    match method_parameters.len() {
                                        0 => String::new(),
                                        added => format!("`{added}"),
                                    }
                                ),
                                type_parameters
                                    .iter()
                                    .chain(&method_parameters)
                                    .copied()
                                    .collect(),
                            ),
                        };
                        classes.push(Building {
                            home,
                            name,
                            parameters,
                            type_arity: type_parameters.len(),
                            fields: Vec::new(),
                        });
                        classes.len() - 1
                    }
                };
                let building = &mut classes[class];
                let name = format!(
                    "<{}>__{}",
                    building.fields.len(),
                    self.compilation.symbols().get(method).name
                );
                building.fields.push(FieldPlan {
                    token: Token::new(table::FIELD, 0),
                    name,
                    ty: delegate,
                    flags: field_attributes::PUBLIC | field_attributes::STATIC,
                    symbol: None,
                    constant: None,
                    sig: None,
                });
                found.insert(key, (class, building.fields.len() - 1));
            }
        }
        // A type's fields are contiguous rows, so the fields are numbered
        // class by class once every body has been looked through.
        let mut plans = Vec::new();
        let mut tokens = Vec::new();
        for building in &mut classes {
            tokens.push(Token::new(table::TYPE_DEF, *next_type));
            *next_type += 1;
            for field in &mut building.fields {
                field.token = Token::new(table::FIELD, *next_field);
                *next_field += 1;
            }
        }
        for (key, (class, number)) in found {
            let field = &classes[class].fields[number];
            self.delegate_cache_fields.insert(
                key,
                CacheField {
                    token: field.token,
                    class: tokens[class],
                    name: field.name.clone(),
                },
            );
        }
        for (building, token) in classes.into_iter().zip(tokens) {
            self.delegate_cache_classes.insert(
                token,
                CacheClass {
                    enclosing: symbol,
                    name: building.name,
                    parameters: building.parameters,
                    type_arity: building.type_arity,
                },
            );
            plans.push(TypePlan {
                symbol,
                token,
                fields: building.fields,
                methods: Vec::new(),
                properties: Vec::new(),
                display: None,
                iterator: None,
                machine: None,
                nested: None,
            });
        }
        Ok(plans)
    }

    /// The conversions of static method groups a body makes: the delegate
    /// type, the method and its type arguments. Those inside an expression
    /// tree are described, not run, and are left out.
    fn cacheable_conversions(&self, body: &BoundBody) -> Vec<(Type, SymbolId, Vec<Type>)> {
        let symbols = self.compilation.symbols();
        let trees: Vec<rustlyn_text::TextSpan> = body
            .lambdas
            .iter()
            .filter(|lambda| {
                body.types.get(&lambda.span).is_some_and(|ty| {
                    matches!(ty, Type::Named { symbol, type_arguments }
                        if type_arguments.len() == 1
                            && symbols.qualified_name(*symbol)
                                == "System.Linq.Expressions.Expression`1")
                })
            })
            .map(|lambda| lambda.span)
            .collect();
        let mut found = Vec::new();
        body.each_expression(&mut |expression| {
            let BoundExpressionKind::DelegateCreation {
                method,
                receiver,
                type_arguments,
                written_new: false,
                ..
            } = &expression.kind
            else {
                return;
            };
            if receiver.as_deref().is_some_and(|receiver| {
                !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_))
            }) || trees
                .iter()
                .any(|tree| crate::emitter::within(expression.span, *tree))
                || !matches!(expression.ty, Type::Named { .. })
            {
                return;
            }
            let detail = symbols.get(*method);
            let is_static = detail.modifiers.contains(Modifiers::STATIC);
            let eligible = match detail.as_method().map(|method| method.method_kind) {
                Some(MethodKind::LocalFunction) => {
                    // A local function written `static` takes nothing from
                    // the method around it; one that is not is left alone
                    // even where it happens to capture nothing, and one that
                    // is generic makes its delegate each time.
                    type_arguments.is_empty()
                        && self
                            .compilation
                            .declaration_node(*method)
                            .is_some_and(|node| {
                                node.child_tokens()
                                    .any(|token| token.kind() == SyntaxKind::StaticKeyword)
                            })
                }
                Some(MethodKind::Ordinary) => is_static,
                _ => false,
            };
            if eligible {
                found.push((expression.ty.clone(), *method, type_arguments.clone()));
            }
        });
        found
    }

    /// The class a conversion belongs in, or `None` where it is one this
    /// emitter makes the delegate for each time.
    fn cache_home(
        &self,
        owner: SymbolId,
        type_parameters: &[SymbolId],
        method_parameters: &[SymbolId],
        delegate: &Type,
        type_arguments: &[Type],
    ) -> Option<CacheHome> {
        let symbols = self.compilation.symbols();
        let mut mentioned = Vec::new();
        collect_type_parameters(delegate, &mut mentioned);
        for argument in type_arguments {
            collect_type_parameters(argument, &mut mentioned);
        }
        let mut method_level = false;
        for parameter in mentioned {
            if method_parameters.contains(&parameter) {
                method_level = true;
            } else if !type_parameters.contains(&parameter) {
                // A parameter of a local function around it: not nameable
                // from a class of the type or of the method.
                return None;
            }
        }
        if symbols.get(owner).kind != SymbolKind::Method && method_level {
            return None;
        }
        Some(if method_level {
            CacheHome::Method(owner)
        } else {
            CacheHome::Type
        })
    }

    /// The field a conversion's delegate is kept in, as the body being
    /// emitted names it, or `None` where there is none to keep it in.
    pub(crate) fn delegate_cache_field(
        &mut self,
        owner: Option<SymbolId>,
        method: SymbolId,
        type_arguments: &[Type],
        delegate: &Type,
    ) -> Result<Option<Token>, EmitError> {
        let Some(enclosing) = self.dynamic_enclosing else {
            return Ok(None);
        };
        let mut homes = Vec::with_capacity(2);
        if let Some(owner) = owner {
            homes.push(CacheHome::Method(owner));
        }
        homes.push(CacheHome::Type);
        let type_parameters = self
            .compilation
            .symbols()
            .get(enclosing)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        for home in homes {
            let key = CacheKey {
                enclosing,
                home,
                method,
                type_arguments: type_arguments.to_vec(),
                delegate: delegate.clone(),
            };
            let Some(field) = self.delegate_cache_fields.get(&key).cloned() else {
                continue;
            };
            let Some(class) = self.delegate_cache_classes.get(&field.class).cloned() else {
                continue;
            };
            // The class is named through the parameters the body being
            // emitted has: the type's own, and a method's — which are `!!0`
            // in a method of the type, and the class's own, copied from the
            // method, where the language made a class over it.
            let method_arity = class.parameters.len() - class.type_arity;
            let in_class = !self.display_generics.is_empty();
            if (in_class && !self.display_generics.starts_with(&type_parameters))
                || (method_arity > 0
                    && if in_class {
                        self.display_generics != class.parameters
                    } else {
                        self.method_generics.len() != method_arity
                    })
            {
                return Ok(None);
            }
            if class.parameters.is_empty() {
                return Ok(Some(field.token));
            }
            if let Some(reference) = self.delegate_cache_references.get(&(field.token, in_class)) {
                return Ok(Some(*reference));
            }
            let arguments: Vec<SigType> = if in_class {
                (0..class.parameters.len() as u32)
                    .map(SigType::TypeParameter)
                    .collect()
            } else {
                (0..class.type_arity as u32)
                    .map(SigType::TypeParameter)
                    .chain((0..method_arity as u32).map(SigType::MethodTypeParameter))
                    .collect()
            };
            let constructed = SigType::Constructed {
                value_type: false,
                coded: type_def_or_ref(0, field.class.0 & 0x00FF_FFFF),
                arguments,
            };
            let mut blob = Vec::new();
            constructed.write(&mut blob);
            let spec = self.references.type_spec(&mut self.metadata, &blob);
            // The field's type in the class's own terms: its parameters, the
            // type's and then the method's.
            let outer = std::mem::replace(&mut self.display_generics, class.parameters.clone());
            let outer_methods = std::mem::take(&mut self.method_generics);
            let written = self.sig_type(delegate);
            self.display_generics = outer;
            self.method_generics = outer_methods;
            let reference = self.references.member_of_spec(
                &mut self.metadata,
                spec,
                &field.name,
                &field_signature(&written?),
            );
            self.delegate_cache_references
                .insert((field.token, in_class), reference);
            return Ok(Some(reference));
        }
        Ok(None)
    }

    /// Writes the `TypeDef` of a `<>O`: nested, static, declaring the
    /// parameters of the type and the method it is for.
    pub(crate) fn write_delegate_cache_type(
        &mut self,
        plan: &TypePlan,
        class: &CacheClass,
        type_offsets: &[u32],
    ) -> Result<(), EmitError> {
        let object = self
            .references
            .type_ref_coded(&mut self.metadata, "System.Object");
        let token = self.metadata.add_type_def(
            type_attributes::NESTED_PRIVATE
                | type_attributes::ABSTRACT
                | type_attributes::SEALED
                | type_attributes::BEFORE_FIELD_INIT,
            "",
            &class.name,
            object,
        );
        crate::emitter::predicted(token, plan.token, "a class of cached delegates")?;
        if let Some(outer) = self.types.get(&class.enclosing).copied() {
            self.metadata.add_nested_class(token, outer);
        }
        self.mark_compiler_generated(token);
        let owner = (token.0 & 0x00FF_FFFF) << 1;
        self.display_generics = class.parameters.clone();
        for (number, parameter) in class.parameters.iter().enumerate() {
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

/// Every type parameter a type names.
fn collect_type_parameters(ty: &Type, into: &mut Vec<SymbolId>) {
    match ty {
        Type::TypeParameter(symbol) => into.push(*symbol),
        Type::Named { type_arguments, .. } => {
            for argument in type_arguments {
                collect_type_parameters(argument, into);
            }
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            collect_type_parameters(element, into);
        }
        Type::Tuple(elements) => {
            for element in elements {
                collect_type_parameters(&element.ty, into);
            }
        }
        Type::FunctionPointer(pointer) => {
            for ty in pointer.types() {
                collect_type_parameters(ty, into);
            }
        }
        Type::Error | Type::Null | Type::Void | Type::Dynamic => {}
    }
}
