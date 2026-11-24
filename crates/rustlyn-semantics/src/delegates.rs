//! The delegate types the language synthesizes (C# 10, §10.7.3).
//!
//! A lambda or a method group has a type of its own where its signature says
//! enough: `var f = (int x) => x;` is a `Func<int, int>`. Where no `Action`
//! or `Func` has that shape — a `ref` parameter, a default value, `params`,
//! a pointer, more parameters than the framework's delegates take — the
//! compiler declares a delegate type for it, the way it declares a class for
//! `new { a = 1 }`. Roslyn keeps these in its `AnonymousTypeManager`; so do
//! we, as templates built the first time a body asks for one:
//!
//! * `<>A{00000001}`2` and `<>F{00000009}`2`, generic in every parameter
//!   type, for a shape that differs from `Action`/`Func` only by the `ref`
//!   kinds its name spells;
//! * `<>f__AnonymousDelegate0`, generic in every parameter type too, where a
//!   default value or `params` has to live on the `Invoke` it declares;
//! * `<>f__AnonymousDelegate1`, not generic, where a parameter's type cannot
//!   be a type argument — a pointer.
//!
//! The indexed names are handed out when the module is written, in the order
//! of the first place each template was asked for.

use std::collections::HashMap;
use std::fmt::Write as _;

use crate::bound::ConstantValue;
use crate::compilation::Compilation;
use crate::symbol::{
    Accessibility, Detail, Location, Method, Modifiers, NamedType, Parameter, RefKind, Symbol,
    SymbolId, SymbolKind, TypeKind, TypeParameter,
};
use crate::types::Type;

/// One parameter of a signature a lambda or a method group has.
#[derive(Clone, Debug, PartialEq)]
pub struct DelegateParameter {
    pub ty: Type,
    pub ref_kind: RefKind,
    /// `ref readonly` rather than `in`.
    pub ref_readonly: bool,
    /// `[UnscopedRef]`, a scope other than the one the parameter has by
    /// default.
    pub unscoped: bool,
    /// `int x = 10`: the value, as a constant of the parameter's type.
    pub default: Option<ConstantValue>,
    /// Where a default value that folds to no constant was written — a
    /// `decimal` one, which the language computes but metadata cannot hold
    /// as a constant — and its text, which tells two of them apart.
    pub default_syntax: Option<(Location, String)>,
    pub is_params: bool,
    /// Written `scoped`, which for anything but an `out` is a scope other
    /// than the one the parameter would have anyway.
    pub scoped: bool,
}

impl DelegateParameter {
    /// Whether the parameter has the scope its kind gives it by default: an
    /// `out` is `scoped` whether or not it says so.
    fn has_default_scope(&self) -> bool {
        (!self.scoped || self.ref_kind == RefKind::Out) && !self.unscoped
    }
}

/// The signature a delegate type is looked for or made for.
#[derive(Clone, Debug, PartialEq)]
pub struct DelegateSignature {
    pub parameters: Vec<DelegateParameter>,
    /// What it gives back: `Void`, a type, or a `ByRef` for `ref T`.
    pub returns: Type,
    /// `ref readonly T`.
    pub returns_readonly: bool,
}

/// How a synthesized delegate is named in metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DelegateName {
    /// `<>A{...}` or `<>F{...}`, which the signature alone decides.
    Structural(String),
    /// `<>f__AnonymousDelegateN`, numbered when the module is written.
    Indexed,
}

/// One delegate type the compilation synthesized.
#[derive(Clone, Debug)]
pub(crate) struct AnonymousDelegate {
    pub symbol: SymbolId,
    pub name: DelegateName,
    /// The first place in the source that asked for it, which orders the
    /// indexed names.
    pub first: Option<Location>,
}

/// Every delegate type synthesized so far, by the shape it was made for.
#[derive(Debug, Default)]
pub(crate) struct AnonymousDelegates {
    by_key: HashMap<String, usize>,
    pub(crate) made: Vec<AnonymousDelegate>,
    /// The default values of the parameters of their `Invoke` methods.
    pub(crate) defaults: HashMap<SymbolId, ConstantValue>,
    /// Where the defaults that are no constant were written.
    pub(crate) default_syntax: HashMap<SymbolId, Location>,
}

/// The type arguments `Action` and `Func` take at most.
const FRAMEWORK_ARITY: usize = 16;

impl Compilation {
    /// Every delegate type the bodies bound so far needed synthesized, with
    /// the name each one has in metadata, ordered as Roslyn orders them:
    /// the structural ones by name, then the indexed ones by where they
    /// were first needed.
    #[must_use]
    pub fn anonymous_delegates(&self) -> Vec<(SymbolId, String)> {
        let registry = crate::compilation::lock(&self.anonymous_delegates);
        let mut structural: Vec<(SymbolId, String)> = Vec::new();
        let mut indexed: Vec<&AnonymousDelegate> = Vec::new();
        // A type made only to bind a lambda against while its return type
        // was being worked out was never the type of anything.
        for made in registry.made.iter().filter(|made| made.first.is_some()) {
            match &made.name {
                DelegateName::Structural(name) => structural.push((made.symbol, name.clone())),
                DelegateName::Indexed => indexed.push(made),
            }
        }
        structural.sort_by(|a, b| {
            self.symbols
                .get(a.0)
                .metadata_name()
                .cmp(&self.symbols.get(b.0).metadata_name())
        });
        indexed.sort_by_key(|made| {
            made.first.map_or((usize::MAX, 0, 0), |at| {
                (at.tree, at.span.start(), at.span.end())
            })
        });
        structural.extend(
            indexed
                .into_iter()
                .enumerate()
                .map(|(index, made)| (made.symbol, format!("<>f__AnonymousDelegate{index}"))),
        );
        structural
    }

    /// Where the default value of an anonymous delegate's `Invoke`
    /// parameter was written, where it is no constant.
    #[must_use]
    pub fn anonymous_delegate_default_syntax(&self, parameter: SymbolId) -> Option<Location> {
        if !parameter.is_late() {
            return None;
        }
        crate::compilation::lock(&self.anonymous_delegates)
            .default_syntax
            .get(&parameter)
            .copied()
    }

    /// The default value an anonymous delegate's `Invoke` parameter has.
    #[must_use]
    pub fn anonymous_delegate_default(&self, parameter: SymbolId) -> Option<ConstantValue> {
        if !parameter.is_late() {
            return None;
        }
        crate::compilation::lock(&self.anonymous_delegates)
            .defaults
            .get(&parameter)
            .cloned()
    }
}

impl crate::binder::Binder<'_> {
    /// The delegate type a lambda or a method group with this signature has
    /// on its own (§10.7.3 of C# 10): an `Action` or a `Func` where one fits,
    /// and otherwise one the compilation declares for it.
    ///
    /// `None` where the signature is not one a delegate can have.
    #[must_use]
    pub fn delegate_type_for(
        &self,
        signature: &DelegateSignature,
        at: Option<Location>,
    ) -> Option<Type> {
        let returns_void = matches!(signature.returns, Type::Void);
        let returns_by_ref = matches!(signature.returns, Type::ByRef(_));
        let returned = signature.returns.value().clone();
        if signature
            .parameters
            .iter()
            .any(|parameter| !is_a_type(&parameter.ty))
            || (!returns_void && !is_a_type(&returned))
        {
            return None;
        }
        let needs_indexed_name = signature
            .parameters
            .iter()
            .any(|parameter| parameter.default.is_some() || parameter.is_params);
        let all_by_value = signature
            .parameters
            .iter()
            .all(|parameter| parameter.ref_kind == RefKind::None);
        let mut arguments: Vec<Type> = signature
            .parameters
            .iter()
            .map(|parameter| parameter.ty.clone())
            .collect();
        if !returns_void {
            arguments.push(returned.clone());
        }
        let symbols = self.compilation().symbols();
        let valid = arguments
            .iter()
            .all(|argument| is_valid_type_argument(argument, symbols))
            && signature.parameters.iter().all(|parameter| {
                (!parameter.is_params || is_array(&parameter.ty)) && parameter.has_default_scope()
            });

        // `System.Action<...>` or `System.Func<...>` where they fit.
        if !needs_indexed_name && !returns_by_ref && all_by_value && valid {
            let family = if returns_void {
                "System.Action"
            } else {
                "System.Func"
            };
            let count = signature.parameters.len();
            if count <= FRAMEWORK_ARITY {
                let name = if arguments.is_empty() {
                    family.to_string()
                } else {
                    format!("{family}`{}", arguments.len())
                };
                if let Some(symbol) = self.compilation().type_by_metadata_name(&name) {
                    return Some(Type::Named {
                        symbol,
                        type_arguments: arguments,
                    });
                }
            }
        }

        let refs = ref_kind_string(signature, returns_void);
        if valid && !needs_indexed_name {
            // `<>A{00000001}`2`: generic in every type, named by its ref kinds.
            let name = format!(
                "{}{}",
                if returns_void { "<>A" } else { "<>F" },
                refs.as_deref().unwrap_or("")
            );
            let key = format!("S:{name}`{}", arguments.len());
            let template = self.delegate_template(&key, at, || Template {
                name: DelegateName::Structural(name.clone()),
                type_name: name.clone(),
                type_parameters: generic_names(signature.parameters.len(), !returns_void),
                parameters: signature
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(index, parameter)| TemplateParameter {
                        ty: Shape::Parameter(index),
                        ref_kind: parameter.ref_kind,
                        ref_readonly: parameter.ref_readonly,
                        default: None,
                        default_syntax: None,
                        is_params: false,
                    })
                    .collect(),
                returns: if returns_void {
                    Shape::Void
                } else {
                    Shape::Parameter(signature.parameters.len())
                },
                returns_by_ref,
                returns_readonly: signature.returns_readonly,
            })?;
            return Some(construct(template, arguments));
        }

        if valid {
            // `<>f__AnonymousDelegate0<T1, T2>`: generic in every type, with
            // the default values and `params` on its `Invoke`. The element
            // type of a `params T[]` is what it is generic in.
            let arguments: Vec<Type> = signature
                .parameters
                .iter()
                .map(|parameter| {
                    if parameter.is_params {
                        array_element(&parameter.ty)
                    } else {
                        parameter.ty.clone()
                    }
                })
                .chain((!returns_void).then(|| returned.clone()))
                .collect();
            let mut key = format!("I:{}:", arguments.len());
            for parameter in &signature.parameters {
                let _ = write!(
                    key,
                    "({:?},{},{:?},{:?},{}),",
                    parameter.ref_kind,
                    parameter.ref_readonly,
                    parameter.default,
                    parameter.default_syntax.as_ref().map(|(_, text)| text),
                    parameter.is_params
                );
            }
            let _ = write!(
                key,
                "->{returns_void},{returns_by_ref},{}",
                signature.returns_readonly
            );
            let template = self.delegate_template(&key, at, || Template {
                name: DelegateName::Indexed,
                type_name: "<>f__AnonymousDelegate".to_string(),
                type_parameters: generic_names(signature.parameters.len(), !returns_void),
                parameters: signature
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(index, parameter)| TemplateParameter {
                        ty: if parameter.is_params {
                            Shape::ArrayOf(index)
                        } else {
                            Shape::Parameter(index)
                        },
                        ref_kind: parameter.ref_kind,
                        ref_readonly: parameter.ref_readonly,
                        default: parameter.default.clone(),
                        default_syntax: parameter.default_syntax.as_ref().map(|(at, _)| *at),
                        is_params: parameter.is_params,
                    })
                    .collect(),
                returns: if returns_void {
                    Shape::Void
                } else {
                    Shape::Parameter(signature.parameters.len())
                },
                returns_by_ref,
                returns_readonly: signature.returns_readonly,
            })?;
            return Some(construct(template, arguments));
        }

        // A pointer cannot be a type argument, so the type is the signature
        // itself, generic only in the type parameters around it that it
        // mentions.
        let mut referenced: Vec<SymbolId> = Vec::new();
        for parameter in &signature.parameters {
            collect_type_parameters(&parameter.ty, &mut referenced);
        }
        collect_type_parameters(&returned, &mut referenced);
        let symbols = self.compilation().symbols();
        referenced.sort_by_key(|parameter| {
            let owner = symbols.get(*parameter).container;
            let depth = owner.map_or(0, |owner| {
                let mut depth = 0;
                let mut current = symbols.get(owner).container;
                while let Some(container) = current {
                    depth += 1;
                    current = symbols.get(container).container;
                }
                depth
            });
            let ordinal = owner
                .and_then(|owner| {
                    let symbol = symbols.get(owner);
                    symbol
                        .as_named_type()
                        .map(|detail| detail.type_parameters.clone())
                        .or_else(|| {
                            symbol
                                .as_method()
                                .map(|detail| detail.type_parameters.clone())
                        })
                })
                .and_then(|list| list.iter().position(|p| p == parameter))
                .unwrap_or(0);
            (depth, ordinal)
        });
        let placeholders: HashMap<SymbolId, Type> = referenced
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                (
                    *parameter,
                    Type::TypeParameter(SymbolId(u32::MAX - index as u32)),
                )
            })
            .collect();
        let mut key = format!("N:{}:", referenced.len());
        for parameter in &signature.parameters {
            let _ = write!(
                key,
                "({:?},{:?},{},{:?},{:?},{},{}),",
                parameter.ty.substitute(&placeholders),
                parameter.ref_kind,
                parameter.ref_readonly,
                parameter.default,
                parameter.default_syntax.as_ref().map(|(_, text)| text),
                parameter.is_params,
                parameter.has_default_scope()
            );
        }
        let _ = write!(
            key,
            "->{:?},{}",
            signature.returns.substitute(&placeholders),
            signature.returns_readonly
        );
        let names: Vec<String> = referenced
            .iter()
            .map(|parameter| symbols.get(*parameter).name.clone())
            .collect();
        let template = self.delegate_template(&key, at, || Template {
            name: DelegateName::Indexed,
            type_name: "<>f__AnonymousDelegate".to_string(),
            type_parameters: names.clone(),
            parameters: signature
                .parameters
                .iter()
                .map(|parameter| TemplateParameter {
                    ty: Shape::Written(parameter.ty.clone(), referenced.clone()),
                    ref_kind: parameter.ref_kind,
                    ref_readonly: parameter.ref_readonly,
                    default: parameter.default.clone(),
                    default_syntax: parameter.default_syntax.as_ref().map(|(at, _)| *at),
                    is_params: parameter.is_params,
                })
                .collect(),
            returns: if returns_void {
                Shape::Void
            } else {
                Shape::Written(returned.clone(), referenced.clone())
            },
            returns_by_ref,
            returns_readonly: signature.returns_readonly,
        })?;
        Some(construct(
            template,
            referenced.into_iter().map(Type::TypeParameter).collect(),
        ))
    }

    /// The template made for `key`, made now if this is the first time.
    fn delegate_template(
        &self,
        key: &str,
        at: Option<Location>,
        make: impl FnOnce() -> Template,
    ) -> Option<SymbolId> {
        let compilation = self.compilation();
        let mut registry = crate::compilation::lock(&compilation.anonymous_delegates);
        if let Some(index) = registry.by_key.get(key).copied() {
            let made = &mut registry.made[index];
            if let Some(at) = at
                && made.first.is_none_or(|first| {
                    (at.tree, at.span.start()) < (first.tree, first.span.start())
                })
            {
                made.first = Some(at);
            }
            return Some(made.symbol);
        }
        let template = make();
        // A runtime that has generics over `ref struct`s gets delegates that
        // take them: every type parameter `allows ref struct`, as Roslyn
        // makes them where `RuntimeFeature.ByRefLikeGenerics` is there.
        let allows_ref_struct = compilation
            .type_by_metadata_name("System.Runtime.CompilerServices.RuntimeFeature")
            .is_some_and(|feature| {
                compilation
                    .symbols()
                    .get(feature)
                    .members
                    .iter()
                    .any(|member| compilation.symbols().get(*member).name == "ByRefLikeGenerics")
            });
        let symbols = compilation.symbols();
        let arity = template.type_parameters.len();
        let count = template.parameters.len();
        let first = symbols.reserve_late(1 + arity + 1 + count)?;
        let id = |offset: usize| SymbolId(first.0 + offset as u32);
        let ty = first;
        let type_parameters: Vec<SymbolId> = (0..arity).map(|index| id(1 + index)).collect();
        let invoke = id(1 + arity);
        let parameters: Vec<SymbolId> = (0..count).map(|index| id(2 + arity + index)).collect();

        let shape = |shape: &Shape| -> Type {
            match shape {
                Shape::Void => Type::Void,
                Shape::Parameter(index) => Type::TypeParameter(type_parameters[*index]),
                Shape::ArrayOf(index) => Type::Array {
                    element: Box::new(Type::TypeParameter(type_parameters[*index])),
                    rank: 1,
                },
                Shape::Written(ty, referenced) => ty.substitute(
                    &referenced
                        .iter()
                        .zip(&type_parameters)
                        .map(|(outer, own)| (*outer, Type::TypeParameter(*own)))
                        .collect(),
                ),
            }
        };

        let mut members = vec![("Invoke".to_string(), invoke)];
        members.extend(
            type_parameters
                .iter()
                .zip(&template.type_parameters)
                .map(|(id, name)| (name.clone(), *id)),
        );
        let mut symbol = Symbol {
            id: ty,
            kind: SymbolKind::NamedType,
            name: template.type_name.clone(),
            container: Some(compilation.global_namespace()),
            members: vec![invoke],
            locations: Vec::new(),
            accessibility: Accessibility::Internal,
            modifiers: Modifiers::SEALED,
            detail: Detail::NamedType(NamedType {
                type_kind: Some(TypeKind::Delegate),
                arity,
                type_parameters: type_parameters.clone(),
                ..NamedType::default()
            }),
        };
        symbol.members.extend(type_parameters.iter().copied());
        symbols.set_late(symbol, &members);
        for (own, name) in type_parameters.iter().zip(&template.type_parameters) {
            symbols.set_late(
                Symbol {
                    id: *own,
                    kind: SymbolKind::TypeParameter,
                    name: name.clone(),
                    container: Some(ty),
                    members: Vec::new(),
                    locations: Vec::new(),
                    accessibility: Accessibility::NotApplicable,
                    modifiers: Modifiers::empty(),
                    detail: Detail::TypeParameter(TypeParameter {
                        allows_ref_struct,
                        ..TypeParameter::default()
                    }),
                },
                &[],
            );
        }
        let returns = shape(&template.returns);
        let returns = if template.returns_by_ref {
            Type::ByRef(Box::new(returns))
        } else {
            returns
        };
        compilation.cache_symbol_type(invoke, returns);
        symbols.set_late(
            Symbol {
                id: invoke,
                kind: SymbolKind::Method,
                name: "Invoke".to_string(),
                container: Some(ty),
                members: Vec::new(),
                locations: Vec::new(),
                accessibility: Accessibility::Public,
                modifiers: Modifiers::empty(),
                detail: Detail::Method(Method {
                    parameters: parameters.clone(),
                    returns_readonly: template.returns_readonly,
                    ..Method::default()
                }),
            },
            &[],
        );
        let single = count == 1;
        for (index, (parameter, spec)) in parameters.iter().zip(&template.parameters).enumerate() {
            compilation.cache_symbol_type(*parameter, shape(&spec.ty));
            if let Some(default) = &spec.default {
                registry.defaults.insert(*parameter, default.clone());
            }
            if let Some(at) = spec.default_syntax {
                registry.default_syntax.insert(*parameter, at);
            }
            symbols.set_late(
                Symbol {
                    id: *parameter,
                    kind: SymbolKind::Parameter,
                    name: if single {
                        "arg".to_string()
                    } else {
                        format!("arg{}", index + 1)
                    },
                    container: Some(invoke),
                    members: Vec::new(),
                    locations: Vec::new(),
                    accessibility: Accessibility::NotApplicable,
                    modifiers: Modifiers::empty(),
                    detail: Detail::Parameter(Parameter {
                        ref_kind: spec.ref_kind,
                        ref_readonly: spec.ref_readonly,
                        is_params: spec.is_params,
                        has_default: spec.default.is_some(),
                        ..Parameter::default()
                    }),
                },
                &[],
            );
        }
        let index = registry.made.len();
        registry.made.push(AnonymousDelegate {
            symbol: ty,
            name: template.name,
            first: at,
        });
        registry.by_key.insert(key.to_string(), index);
        Some(ty)
    }
}

/// What a template is made from.
struct Template {
    name: DelegateName,
    type_name: String,
    type_parameters: Vec<String>,
    parameters: Vec<TemplateParameter>,
    returns: Shape,
    returns_by_ref: bool,
    returns_readonly: bool,
}

struct TemplateParameter {
    ty: Shape,
    ref_kind: RefKind,
    ref_readonly: bool,
    default: Option<ConstantValue>,
    default_syntax: Option<Location>,
    is_params: bool,
}

/// A type in a template, in terms of the template's own type parameters.
enum Shape {
    Void,
    /// The template's type parameter at this position.
    Parameter(usize),
    /// An array of it: a `params T[]`.
    ArrayOf(usize),
    /// A type as written, with the type parameters around it that the
    /// template takes as its own, in order.
    Written(Type, Vec<SymbolId>),
}

/// `T1, T2, TResult`, as Roslyn names a template's type parameters.
fn generic_names(parameters: usize, returns: bool) -> Vec<String> {
    let mut names: Vec<String> = (1..=parameters).map(|index| format!("T{index}")).collect();
    if returns {
        names.push("TResult".to_string());
    }
    names
}

fn construct(template: SymbolId, arguments: Vec<Type>) -> Type {
    Type::Named {
        symbol: template,
        type_arguments: arguments,
    }
}

/// `{00000009}`: three bits a parameter, the return last, in 64-bit words
/// printed in hex — `None` where everything is by value.
fn ref_kind_string(signature: &DelegateSignature, returns_void: bool) -> Option<String> {
    let returns = if !matches!(signature.returns, Type::ByRef(_)) {
        0
    } else if signature.returns_readonly {
        3
    } else {
        1
    };
    let mut kinds: Vec<u64> = signature
        .parameters
        .iter()
        .map(|parameter| match parameter.ref_kind {
            RefKind::None => 0,
            RefKind::Ref => 1,
            RefKind::Out => 2,
            RefKind::In if parameter.ref_readonly => 4,
            RefKind::In => 3,
        })
        .collect();
    if !returns_void {
        kinds.push(returns);
    }
    if kinds.iter().all(|kind| *kind == 0) {
        return None;
    }
    // Roslyn's `BitVector` keeps 64 bits a word and prints every word it
    // has room for.
    let bits = kinds.len() * 3;
    let mut words = vec![0u64; bits.div_ceil(64).max(1)];
    for (index, kind) in kinds.iter().enumerate() {
        for bit in 0..3 {
            if kind & (1 << bit) != 0 {
                let at = index * 3 + bit;
                words[at / 64] |= 1 << (at % 64);
            }
        }
    }
    let words: Vec<String> = words.iter().map(|word| format!("{word:08x}")).collect();
    Some(format!("{{{}}}", words.join(",")))
}

/// Whether a type can be a parameter's or a result's at all.
fn is_a_type(ty: &Type) -> bool {
    !matches!(ty, Type::Error | Type::Null | Type::Void | Type::ByRef(_))
}

/// Whether a type may be a type argument: a pointer may not, and neither may
/// a `ref struct` — the runtimes the language's rules for these types were
/// written against have no generics over one.
fn is_valid_type_argument(ty: &Type, symbols: &crate::symbol::Symbols) -> bool {
    match ty {
        Type::Pointer(_) | Type::FunctionPointer(_) | Type::ByRef(_) | Type::Void => false,
        Type::Named { symbol, .. } => !symbols
            .get(*symbol)
            .as_named_type()
            .is_some_and(|detail| detail.ref_like),
        _ => true,
    }
}

fn is_array(ty: &Type) -> bool {
    matches!(ty, Type::Array { rank: 1, .. })
}

fn array_element(ty: &Type) -> Type {
    match ty {
        Type::Array { element, .. } => (**element).clone(),
        other => other.clone(),
    }
}

fn collect_type_parameters(ty: &Type, into: &mut Vec<SymbolId>) {
    match ty {
        Type::TypeParameter(symbol) => {
            if !into.contains(symbol) {
                into.push(*symbol);
            }
        }
        Type::Named { type_arguments, .. } => {
            for argument in type_arguments {
                collect_type_parameters(argument, into);
            }
        }
        Type::Array { element, .. } => collect_type_parameters(element, into),
        Type::Pointer(inner) | Type::ByRef(inner) => collect_type_parameters(inner, into),
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
