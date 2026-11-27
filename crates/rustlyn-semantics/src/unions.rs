//! Union types (C# 15): a class or struct marked `[Union]`, whose value is
//! one of its *case types* or null, and which conversions and patterns treat
//! as the value it holds.
//!
//! Nothing about a union is a new kind of type to the runtime. What the
//! language adds is found by name and shape on the union — or on the public
//! `IUnionMembers` interface it declares and implements, a *union member
//! provider*: the members that make one (its public one-parameter
//! constructors, or the provider's static `Create` methods), whose parameter
//! types are the case types; the `object Value` the contents are read
//! through; and, optionally, `bool HasValue` and a `bool TryGetValue(out T)`
//! per case type, which pattern matching prefers because they need not box.
//! Shapes are judged on the declarations as written, before any type
//! arguments are put in.

use std::collections::HashMap;

use crate::binder::{Binder, Diagnostics};
use crate::corlib::SpecialType;
use crate::symbol::{Accessibility, Modifiers, RefKind, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

/// What a union type offers the language.
#[derive(Clone, Debug)]
pub struct UnionMembers {
    /// The one-parameter constructors of the union, or the provider's
    /// static `Create` methods, each with the case type it takes.
    pub creations: Vec<(SymbolId, Type)>,
    /// `object Value { get; }`
    pub value: Option<SymbolId>,
    /// `bool HasValue { get; }`
    pub has_value: Option<SymbolId>,
    /// `bool TryGetValue(out T value)`, each with its `T`.
    pub try_get_values: Vec<(SymbolId, Type)>,
}

impl Binder<'_> {
    /// Whether a type is a union type: a class or a struct with `[Union]`
    /// written on it. A type parameter never is, whatever it is constrained
    /// to. Unions are C# 15: before it, what union matching and union
    /// conversions would be is an error (a compiler of those versions knows
    /// `[Union]` as no more than an attribute), so the type is an ordinary
    /// one.
    #[must_use]
    pub fn is_union_type(&self, ty: &Type) -> bool {
        let Type::Named { symbol, .. } = ty else {
            return false;
        };
        if !self
            .compilation()
            .language_version()
            .at_least(rustlyn_syntax::LanguageVersion::CSharp15)
        {
            return false;
        }
        let symbols = self.compilation().symbols();
        if !matches!(
            symbols.get(*symbol).type_kind(),
            Some(TypeKind::Class | TypeKind::Struct)
        ) {
            return false;
        }
        if symbols
            .get(*symbol)
            .as_named_type()
            .is_some_and(|detail| detail.union_attribute)
        {
            return true;
        }
        self.compilation()
            .declaration_nodes(*symbol)
            .iter()
            .filter_map(|(tree, span)| {
                self.compilation()
                    .trees()
                    .get(*tree)?
                    .root()
                    .find_node(*span)
            })
            .any(|node| {
                node.kind() == rustlyn_syntax::SyntaxKind::UnionDeclaration
                    || node
                        .children()
                        .filter(|child| child.kind() == rustlyn_syntax::SyntaxKind::AttributeList)
                        .flat_map(|list| list.children().collect::<Vec<_>>())
                        .filter(|attribute| {
                            attribute.kind() == rustlyn_syntax::SyntaxKind::Attribute
                        })
                        .any(|attribute| {
                            attribute.children().next().is_some_and(|name| {
                                let name = name.text();
                                let name = name.trim().rsplit('.').next().unwrap_or_default();
                                name == "Union" || name == "UnionAttribute"
                            })
                        })
            })
    }

    /// The interfaces a type lists and those they list, depth first in the
    /// order written (Roslyn's `GetInterfacesToEmit`).
    fn interfaces_to_emit(&self, ty: &Type) -> Vec<Type> {
        fn visit(binder: &Binder<'_>, ty: &Type, seen: &mut Vec<Type>, found: &mut Vec<Type>) {
            let Some(symbol) = ty.symbol() else {
                return;
            };
            let substitution = binder.type_substitution(ty);
            for base in binder.base_types_of(symbol) {
                let base = base.substitute(&substitution);
                if base.symbol().is_some() && !seen.contains(&base) {
                    seen.push(base.clone());
                    found.push(base.clone());
                    visit(binder, &base, seen, found);
                }
            }
        }
        let mut found = Vec::new();
        visit(self, ty, &mut Vec::new(), &mut found);
        found
    }

    /// Lists an interface after the ones it extends, the last written first,
    /// as Roslyn's `MakeAllInterfaces` does before it reverses the result.
    fn list_interface(
        &self,
        interface: Type,
        visited: &mut Vec<Type>,
        listed: &mut Vec<(SymbolId, HashMap<SymbolId, Type>)>,
    ) {
        let Some(symbol) = interface.symbol() else {
            return;
        };
        if visited.contains(&interface) {
            return;
        }
        visited.push(interface.clone());
        for inherited in self.interfaces_to_emit(&interface).into_iter().rev() {
            self.list_interface(inherited, visited, listed);
        }
        listed.push((symbol, self.type_substitution(&interface)));
    }

    /// The members that make a union type one, where the type is a union.
    #[must_use]
    pub fn union_members(&self, ty: &Type) -> Option<UnionMembers> {
        if !self.is_union_type(ty) {
            return None;
        }
        let symbol = ty.symbol()?;
        let symbols = self.compilation().symbols();
        let mut sink = Diagnostics::new();
        let declared = |member: SymbolId, sink: &mut Diagnostics| self.type_of(member, sink);
        // A property read from metadata has none of its own: its getter is
        // what can be reached.
        let public = |member: SymbolId| {
            let found = symbols.get(member);
            match found.accessibility {
                Accessibility::NotApplicable => found
                    .as_property()
                    .and_then(|detail| detail.getter)
                    .is_some_and(|getter| {
                        symbols.get(getter).accessibility == Accessibility::Public
                    }),
                declared => declared == Accessibility::Public,
            }
        };
        let special = |ty: &Type, wanted: SpecialType| self.special_of(ty) == Some(wanted);

        // Where members are looked for, each with the substitution that puts
        // the union's type arguments into what it declares: the provider and
        // the interfaces it inherits, or the union and its base classes.
        let provider = symbols.get(symbol).members.iter().copied().find(|member| {
            let candidate = symbols.get(*member);
            candidate.name == "IUnionMembers"
                && candidate.type_kind() == Some(TypeKind::Interface)
                // Of its own, it takes no type arguments: a nested type of a
                // generic union may carry the union's.
                && candidate.as_named_type().is_some_and(|detail| {
                    let outer = symbols
                        .get(symbol)
                        .as_named_type()
                        .map_or(0, |outer| outer.type_parameters.len());
                    detail.type_parameters.is_empty() || detail.type_parameters.len() == outer
                })
        });
        // Shapes are judged on the union as declared, with its own type
        // parameters standing for themselves; what it inherits is seen
        // through the type arguments its declaration gives the base.
        let outer = self.type_substitution(ty);
        let own: Vec<Type> = symbols
            .get(symbol)
            .as_named_type()
            .map(|detail| {
                detail
                    .type_parameters
                    .iter()
                    .copied()
                    .map(Type::TypeParameter)
                    .collect()
            })
            .unwrap_or_default();
        let definition = Type::Named {
            symbol,
            type_arguments: own,
        };
        // The union has to list its own provider, with its own type
        // parameters as the arguments: `S1<T> : S1<long>.IUnionMembers`
        // lists another construction, and so none.
        let provider = provider.filter(|provider| {
            public(*provider) && {
                let arguments = if symbols
                    .get(*provider)
                    .as_named_type()
                    .is_some_and(|detail| detail.type_parameters.is_empty())
                {
                    Vec::new()
                } else {
                    match &definition {
                        Type::Named { type_arguments, .. } => type_arguments.clone(),
                        _ => Vec::new(),
                    }
                };
                let interface = Type::Named {
                    symbol: *provider,
                    type_arguments: arguments,
                };
                self.lists_exactly(symbol, &interface)
            }
        });
        let mut places: Vec<(SymbolId, HashMap<SymbolId, Type>)> = Vec::new();
        match provider {
            Some(provider) => {
                places.push((provider, HashMap::new()));
                // The provider's interfaces in the order Roslyn lists them,
                // which decides the `TryGetValue` that wins among equals.
                let mut visited: Vec<Type> = Vec::new();
                let mut listed: Vec<(SymbolId, HashMap<SymbolId, Type>)> = Vec::new();
                for base in self
                    .interfaces_to_emit(&Type::Named {
                        symbol: provider,
                        type_arguments: Vec::new(),
                    })
                    .into_iter()
                    .rev()
                {
                    self.list_interface(base, &mut visited, &mut listed);
                }
                listed.reverse();
                places.extend(listed);
            }
            None => {
                let mut current = Some(definition.clone());
                while let Some(here) = current.take() {
                    let Some(here_symbol) = here.symbol() else {
                        break;
                    };
                    if places.iter().any(|(seen, _)| *seen == here_symbol) {
                        break;
                    }
                    let substitution = self.type_substitution(&here);
                    places.push((here_symbol, substitution.clone()));
                    current = self
                        .base_class_of(here_symbol)
                        .map(|base| base.substitute(&substitution))
                        .filter(|base| self.special_of(base) != Some(SpecialType::Object));
                }
            }
        }
        let declared_here = |place: SymbolId, name: &str| -> Vec<SymbolId> {
            symbols
                .get(place)
                .members
                .iter()
                .copied()
                .filter(|member| symbols.get(*member).name == name)
                .collect()
        };

        // A property: the first place that declares a suitable one wins.
        // Among a provider's inherited interfaces two unrelated ones that
        // both do make it ambiguous, and there is none.
        let property = |name: &str, wanted: SpecialType, sink: &mut Diagnostics| {
            let suitable = |member: &SymbolId,
                            substitution: &HashMap<SymbolId, Type>,
                            sink: &mut Diagnostics| {
                let found = symbols.get(*member);
                found.kind == SymbolKind::Property
                    && !found.modifiers.contains(Modifiers::STATIC)
                    && public(*member)
                    && found.as_property().is_some_and(|detail| {
                        // The getter itself has to be public: `private
                        // get` leaves the property out.
                        detail.parameters.is_empty()
                            && detail.has_get
                            && detail.getter.is_none_or(&public)
                            && detail
                                .get_accessibility
                                .is_none_or(|narrowed| narrowed == Accessibility::Public)
                    })
                    && special(&declared(*member, sink).substitute(substitution), wanted)
            };
            let mut found: Option<SymbolId> = None;
            for (index, (place, substitution)) in places.iter().enumerate() {
                let Some(member) = declared_here(*place, name)
                    .into_iter()
                    .find(|member| suitable(member, substitution, sink))
                else {
                    continue;
                };
                if provider.is_none() || index == 0 {
                    return Some(member);
                }
                match found {
                    None => found = Some(member),
                    Some(earlier) => {
                        let earlier_place = symbols.get(earlier).container?;
                        let related = self.implements(
                            earlier_place,
                            &Type::Named {
                                symbol: *place,
                                type_arguments: Vec::new(),
                            },
                        ) || self.implements(
                            *place,
                            &Type::Named {
                                symbol: earlier_place,
                                type_arguments: Vec::new(),
                            },
                        );
                        if !related {
                            return None;
                        }
                    }
                }
            }
            found
        };
        let value = property("Value", SpecialType::Object, &mut sink);
        let has_value = property("HasValue", SpecialType::Boolean, &mut sink);

        let single_parameter = |member: SymbolId| -> Option<SymbolId> {
            let detail = symbols.get(member).as_method()?;
            let [parameter] = detail.parameters[..] else {
                return None;
            };
            let kind = symbols.get(parameter).as_parameter()?.ref_kind;
            matches!(kind, RefKind::None | RefKind::In).then_some(parameter)
        };
        let mut creations = Vec::new();
        let mut case_types: Vec<Type> = Vec::new();
        if provider.is_some() {
            let mut seen: Vec<Type> = Vec::new();
            for (place, substitution) in &places {
                for member in declared_here(*place, "Create") {
                    let found = symbols.get(member);
                    let Some(detail) = found.as_method() else {
                        continue;
                    };
                    if !found.modifiers.contains(Modifiers::STATIC)
                        || !public(member)
                        || !detail.type_parameters.is_empty()
                        || declared(member, &mut sink).symbol() != Some(symbol)
                    {
                        continue;
                    }
                    let Some(parameter) = single_parameter(member) else {
                        continue;
                    };
                    let taken = declared(parameter, &mut sink).substitute(substitution);
                    // A `Create` a closer interface declares with the same
                    // parameter shadows the one it inherits.
                    if seen.contains(&taken) {
                        continue;
                    }
                    seen.push(taken.clone());
                    case_types.push(taken.clone());
                    creations.push((member, taken.substitute(&outer)));
                }
            }
        } else {
            for member in symbols.lookup(symbol, ".ctor") {
                if symbols.get(*member).modifiers.contains(Modifiers::STATIC) || !public(*member) {
                    continue;
                }
                if let Some(parameter) = single_parameter(*member) {
                    let taken = declared(parameter, &mut sink);
                    case_types.push(taken.clone());
                    creations.push((*member, taken.substitute(&outer)));
                }
            }
        }
        // `int?` among the case types lets a `TryGetValue(out int)` answer
        // for it.
        let mut answerable = case_types.clone();
        for case in &case_types {
            if let Some(inner) = self.nullable_underlying(case) {
                answerable.push(inner);
            }
        }

        let mut try_get_values = Vec::new();
        for (place, substitution) in &places {
            for member in declared_here(*place, "TryGetValue") {
                let found = symbols.get(member);
                let Some(detail) = found.as_method() else {
                    continue;
                };
                let [parameter] = detail.parameters[..] else {
                    continue;
                };
                if found.modifiers.contains(Modifiers::STATIC)
                    || !public(member)
                    || !detail.type_parameters.is_empty()
                    || symbols.get(parameter).as_parameter().map(|p| p.ref_kind)
                        != Some(RefKind::Out)
                    || !special(
                        &declared(member, &mut sink).substitute(substitution),
                        SpecialType::Boolean,
                    )
                {
                    continue;
                }
                let taken = declared(parameter, &mut sink).substitute(substitution);
                if !answerable.contains(&taken) {
                    continue;
                }
                try_get_values.push((member, taken.substitute(&outer)));
            }
        }
        Some(UnionMembers {
            creations,
            value,
            has_value,
            try_get_values,
        })
    }

    /// Whether a union conversion (C# 15) takes a value of one type to
    /// another: the other is a union, or a `U?` of a struct one, and the
    /// value reaches one of its case types by a conversion of the
    /// language's own — never another union conversion.
    #[must_use]
    pub fn union_converts(&self, from: &Type, to: &Type) -> bool {
        let union = self.nullable_underlying(to).unwrap_or_else(|| to.clone());
        let Some(members) = self.union_members(&union) else {
            return false;
        };
        members.creations.iter().any(|(_, case)| {
            case == from || (!self.is_union_type(case) && self.converts_implicitly(from, case))
        })
    }

    /// Whether a type lists a construction of an interface among what it
    /// implements, directly or through what it inherits.
    fn lists_exactly(&self, ty: SymbolId, wanted: &Type) -> bool {
        let mut pending = self.base_types_of(ty);
        let mut seen: Vec<Type> = Vec::new();
        while let Some(base) = pending.pop() {
            if base == *wanted {
                return true;
            }
            let Some(symbol) = base.symbol() else {
                continue;
            };
            if seen.contains(&base) {
                continue;
            }
            let substitution = self.type_substitution(&base);
            pending.extend(
                self.base_types_of(symbol)
                    .into_iter()
                    .map(|inherited| inherited.substitute(&substitution)),
            );
            seen.push(base);
        }
        false
    }

    /// Whether a type lists an interface among what it implements,
    /// directly or through what it inherits.
    fn implements(&self, ty: SymbolId, interface: &Type) -> bool {
        let Some(wanted) = interface.symbol() else {
            return false;
        };
        let mut pending = self.base_types_of(ty);
        let mut seen = Vec::new();
        while let Some(base) = pending.pop() {
            let Some(base) = base.symbol() else {
                continue;
            };
            if base == wanted {
                return true;
            }
            if seen.contains(&base) {
                continue;
            }
            seen.push(base);
            pending.extend(self.base_types_of(base));
        }
        false
    }
}
