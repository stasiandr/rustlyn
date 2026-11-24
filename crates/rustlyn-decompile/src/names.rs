//! Turning tokens and signatures back into the names C# would write.
//!
//! Metadata never says `int` or `List<string>`: it says `System.Int32` and
//! `List`1<System.String>` with the arity welded onto the name. Everything
//! that prints a type goes through here so that the spelling is decided in
//! one place, and so that a `TypeSpec` is followed into the signature it
//! stands for rather than shown as a row number.

use std::collections::{HashMap, HashSet};

use rustlyn_metadata::signature::{Blob, MethodSig, TypeSig};
use rustlyn_metadata::{Assembly, Row, Token, table, tables};

/// Lookups over the tables that are keyed by something other than their
/// row number, built once so that no resolution walks a whole table.
#[derive(Debug, Default)]
pub struct Index {
    /// `HasConstant` coded parent → `Constant` row.
    constants: HashMap<u32, u32>,
    /// `HasCustomAttribute` coded parent → `CustomAttribute` rows.
    attributes: HashMap<u32, Vec<u32>>,
    /// Nested type → enclosing type.
    nested_parent: HashMap<u32, u32>,
    /// Enclosing type → nested types.
    nested_children: HashMap<u32, Vec<u32>>,
    /// Accessor method → `(HasSemantics parent, semantics)`.
    semantics_by_method: HashMap<u32, (Token, u16)>,
    /// `HasSemantics` coded parent → `(semantics, method row)`.
    semantics_by_parent: HashMap<u32, Vec<(u16, u32)>>,
    /// `TypeOrMethodDef` coded owner → `(number, name, flags, row)`.
    generic_params: HashMap<u32, Vec<(u32, String, u16, u32)>>,
    /// `GenericParam` row → constraint tokens.
    constraints: HashMap<u32, Vec<Token>>,
    /// Method row → owning type row.
    method_owner: Vec<u32>,
    /// Field row → owning type row.
    field_owner: Vec<u32>,
    /// Type row → implemented interfaces.
    interfaces: HashMap<u32, Vec<Token>>,
    /// Type row → `(body, declaration)` of its `MethodImpl` rows.
    method_impls: HashMap<u32, Vec<(Token, Token)>>,
    /// Field row → RVA.
    field_rva: HashMap<u32, u32>,
    /// Type row → the `PropertyMap` row's `(start, end)` of properties.
    properties: HashMap<u32, (u32, u32)>,
    /// Type row → the `EventMap` row's `(start, end)` of events.
    events: HashMap<u32, (u32, u32)>,
    /// Name and signature → method row, for turning a `MemberRef` into the
    /// `MethodDef` it names when that is in this assembly.
    methods_by_name: HashMap<(u32, String), Vec<u32>>,
    /// Top-level type names two namespaces the assembly uses both have:
    /// `Object` of `System` and of `UnityEngine`. They are written with
    /// their namespace.
    ambiguous: HashSet<String>,
    /// The token naming each primitive type here (`System.Int32`), for
    /// finding the methods of `int` where it is defined.
    primitive_tokens: HashMap<String, Token>,
}

impl Index {
    /// Adds to the names written with their namespace those that a type of
    /// a referenced assembly, in a namespace this one uses, also has:
    /// `BooleanConverter` of `System.ComponentModel` beside this assembly's.
    pub fn widen_ambiguous(&mut self, assembly: &Assembly<'_>, refs: &References<'_>) {
        let heaps = assembly.heaps();
        let mut namespaces: HashSet<&str> = HashSet::new();
        let mut names: HashSet<&str> = HashSet::new();
        let mut own: HashSet<String> = HashSet::new();
        for table_id in [table::TYPE_DEF, table::TYPE_REF] {
            for (at, row) in assembly.table(table_id).iter().enumerate() {
                let namespace = heaps.string(row.number(2));
                if namespace.is_empty() {
                    continue;
                }
                if table_id == table::TYPE_DEF && self.nested_parent.contains_key(&(at as u32 + 1))
                {
                    continue;
                }
                namespaces.insert(namespace);
                names.insert(heaps.string(row.number(1)));
                if table_id == table::TYPE_DEF {
                    own.insert(format!("{namespace}.{}", heaps.string(row.number(1))));
                }
            }
        }
        for name in names {
            let homes = namespaces
                .iter()
                .filter(|namespace| {
                    let full = format!("{namespace}.{name}");
                    refs.types.contains_key(&full) || own.contains(&full)
                })
                .count();
            if homes > 1 {
                self.ambiguous.insert(name.to_string());
            }
        }
    }

    /// Builds the lookups for an assembly.
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn build(assembly: &Assembly<'_>) -> Self {
        let heaps = assembly.heaps();
        let mut index = Self::default();
        for (at, row) in assembly.table(table::CONSTANT).iter().enumerate() {
            index
                .constants
                .entry(row.number(2))
                .or_insert(at as u32 + 1);
        }
        for (at, row) in assembly.table(table::CUSTOM_ATTRIBUTE).iter().enumerate() {
            index
                .attributes
                .entry(row.number(0))
                .or_default()
                .push(at as u32 + 1);
        }
        for row in assembly.table(table::NESTED_CLASS).iter() {
            index.nested_parent.insert(row.number(0), row.number(1));
            index
                .nested_children
                .entry(row.number(1))
                .or_default()
                .push(row.number(0));
        }
        for row in assembly.table(table::METHOD_SEMANTICS).iter() {
            let semantics = row.number(0) as u16;
            let method = row.number(1);
            index
                .semantics_by_method
                .entry(method)
                .or_insert((row.token(2), semantics));
            index
                .semantics_by_parent
                .entry(row.number(2))
                .or_default()
                .push((semantics, method));
        }
        for (at, row) in assembly.table(table::GENERIC_PARAM).iter().enumerate() {
            index
                .generic_params
                .entry(row.number(2))
                .or_default()
                .push((
                    row.number(0),
                    heaps.string(row.number(3)).to_string(),
                    row.number(1) as u16,
                    at as u32 + 1,
                ));
        }
        for params in index.generic_params.values_mut() {
            params.sort_by_key(|(number, ..)| *number);
        }
        for row in assembly.table(table::GENERIC_PARAM_CONSTRAINT).iter() {
            index
                .constraints
                .entry(row.number(0))
                .or_default()
                .push(row.token(1));
        }
        let types = assembly.table(table::TYPE_DEF);
        let methods = assembly.rows(table::METHOD_DEF);
        let fields = assembly.rows(table::FIELD);
        index.method_owner = vec![0; methods as usize + 2];
        index.field_owner = vec![0; fields as usize + 2];
        let count = types.len();
        for (at, row) in types.iter().enumerate() {
            let number = at as u32 + 1;
            let next = types.row(number + 1);
            let method_end = next.map_or(methods + 1, |next| next.number(5));
            for method in row.number(5)..method_end.min(methods + 1) {
                index.method_owner[method as usize] = number;
            }
            let field_end = next.map_or(fields + 1, |next| next.number(4));
            for field in row.number(4)..field_end.min(fields + 1) {
                index.field_owner[field as usize] = number;
            }
        }
        let _ = count;
        for row in assembly.table(table::INTERFACE_IMPL).iter() {
            index
                .interfaces
                .entry(row.number(0))
                .or_default()
                .push(row.token(1));
        }
        for row in assembly.table(table::METHOD_IMPL).iter() {
            index
                .method_impls
                .entry(row.number(0))
                .or_default()
                .push((row.token(1), row.token(2)));
        }
        for row in assembly.table(table::FIELD_RVA).iter() {
            index.field_rva.insert(row.number(1), row.number(0));
        }
        let property_maps = assembly.table(table::PROPERTY_MAP);
        let properties = assembly.rows(table::PROPERTY);
        for (at, row) in property_maps.iter().enumerate() {
            let end = property_maps
                .row(at as u32 + 2)
                .map_or(properties + 1, |next| next.number(1));
            index.properties.insert(row.number(0), (row.number(1), end));
        }
        let event_maps = assembly.table(table::EVENT_MAP);
        let events = assembly.rows(table::EVENT);
        for (at, row) in event_maps.iter().enumerate() {
            let end = event_maps
                .row(at as u32 + 2)
                .map_or(events + 1, |next| next.number(1));
            index.events.insert(row.number(0), (row.number(1), end));
        }
        for (at, row) in assembly.table(table::METHOD_DEF).iter().enumerate() {
            let method = at as u32 + 1;
            let owner = index.method_owner[method as usize];
            index
                .methods_by_name
                .entry((owner, heaps.string(row.number(3)).to_string()))
                .or_default()
                .push(method);
        }
        let mut homes: HashMap<String, HashSet<String>> = HashMap::new();
        for row in assembly.table(table::TYPE_REF).iter() {
            let scope = row.token(0);
            if scope.table() == table::TYPE_REF && !scope.is_nil() {
                continue;
            }
            let namespace = heaps.string(row.number(2));
            if !namespace.is_empty() {
                homes
                    .entry(heaps.string(row.number(1)).to_string())
                    .or_default()
                    .insert(namespace.to_string());
            }
        }
        for (at, row) in types.iter().enumerate() {
            if index.nested_parent.contains_key(&(at as u32 + 1)) {
                continue;
            }
            let namespace = heaps.string(row.number(2));
            if !namespace.is_empty() {
                homes
                    .entry(heaps.string(row.number(1)).to_string())
                    .or_default()
                    .insert(namespace.to_string());
            }
        }
        // A type named like a namespace is taken for the namespace where
        // both could be meant: `Utils` in `System.Dynamic` is the namespace
        // `System.Dynamic.Utils`, not the class of that name in it.
        let mut segments: HashSet<String> = HashSet::new();
        for table_id in [table::TYPE_DEF, table::TYPE_REF] {
            for row in assembly.table(table_id).iter() {
                for segment in heaps.string(row.number(2)).split('.') {
                    if !segment.is_empty() {
                        segments.insert(segment.to_string());
                    }
                }
            }
        }
        index.ambiguous = homes
            .into_iter()
            .filter(|(name, namespaces)| {
                namespaces.len() > 1 || segments.contains(strip_arity(name))
            })
            .map(|(name, _)| name)
            .collect();
        for table_id in [table::TYPE_DEF, table::TYPE_REF] {
            for (at, row) in assembly.table(table_id).iter().enumerate() {
                // Both tables keep the name and the namespace in the same
                // columns.
                let (name, namespace) = (row.number(1), row.number(2));
                if heaps.string(namespace) != "System" {
                    continue;
                }
                let raw = format!("System.{}", heaps.string(name));
                if primitive_of(&raw).is_some() {
                    index
                        .primitive_tokens
                        .entry(raw)
                        .or_insert(Token::new(table_id, at as u32 + 1));
                }
            }
        }
        index
    }
}

/// The names in scope for `!0` and `!!0`: the enclosing type's type parameters
/// and the method's own.
#[derive(Clone, Debug, Default)]
pub struct Generics {
    pub type_params: Vec<String>,
    pub method_params: Vec<String>,
}

/// A method a call names, resolved as far as one assembly allows.
#[derive(Clone, PartialEq, Debug)]
pub struct MethodRef {
    pub token: Token,
    pub name: String,
    /// The type the method belongs to.
    pub declaring: TypeSig,
    pub sig: MethodSig,
    /// What a `MethodSpec` instantiated the method with.
    pub type_args: Vec<TypeSig>,
    /// Which parameters are `out`, when the method is defined here and its
    /// `Param` rows say so; empty otherwise.
    pub out_params: Vec<bool>,
    /// The names of the parameters, when defined here.
    pub param_names: Vec<String>,
    /// The default value of each optional parameter, when defined here.
    pub param_defaults: Vec<Option<Constant>>,
    /// Whether the method is an extension method.
    pub is_extension: bool,
    /// Whether the method is virtual, so that a non-virtual call to it on
    /// `this` from a derived type is `base.M()`.
    pub is_virtual: bool,
}

impl MethodRef {
    #[must_use]
    pub fn is_constructor(&self) -> bool {
        self.name == ".ctor"
    }
}

/// A field a load or store names.
#[derive(Clone, PartialEq, Debug)]
pub struct FieldRef {
    pub token: Token,
    pub name: String,
    pub declaring: TypeSig,
    pub ty: TypeSig,
    pub is_static: Option<bool>,
}

/// The assemblies a decompilation may look into for what its own
/// references only name: the framework, usually.
#[derive(Debug, Default)]
pub struct References<'a> {
    pub assemblies: Vec<(Assembly<'a>, Index)>,
    /// Raw full type name (nesting with `/`) → `(assembly, TypeDef row)`.
    types: HashMap<String, (usize, u32)>,
}

impl<'a> References<'a> {
    /// Reads every image that is an assembly; the rest are skipped.
    #[must_use]
    pub fn load(images: &[&'a [u8]]) -> Self {
        let mut references = Self::default();
        for image in images {
            let Ok(assembly) = Assembly::read(image) else {
                continue;
            };
            let index = Index::build(&assembly);
            references.assemblies.push((assembly, index));
        }
        for (at, (assembly, index)) in references.assemblies.iter().enumerate() {
            let resolver = Resolver {
                assembly,
                index,
                refs: None,
                qualify: true,
            };
            let types = assembly.table(table::TYPE_DEF);
            for row in 1..=types.len() {
                let Some(raw) = resolver.raw_name(Token::new(table::TYPE_DEF, row)) else {
                    continue;
                };
                references.types.entry(raw).or_insert((at, row));
            }
        }
        references
    }

    /// Whether anything was loaded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.assemblies.is_empty()
    }
}

/// Resolves tokens against one assembly.
#[derive(Clone, Copy, Debug)]
pub struct Resolver<'a> {
    pub assembly: &'a Assembly<'a>,
    pub index: &'a Index,
    /// The assemblies references may be followed into.
    pub refs: Option<&'a References<'a>>,
    /// Whether names carry their namespace.
    pub qualify: bool,
}

impl<'a> Resolver<'a> {
    #[must_use]
    pub const fn new(assembly: &'a Assembly<'a>, index: &'a Index) -> Self {
        Self {
            assembly,
            index,
            refs: None,
            qualify: false,
        }
    }

    /// The same resolver, following references into the given assemblies.
    #[must_use]
    pub const fn with_references(self, refs: &'a References<'a>) -> Self {
        Self {
            refs: Some(refs),
            ..self
        }
    }

    /// The definition a `TypeRef` names, in whichever reference defines it,
    /// as a resolver over that assembly and the row.
    #[must_use]
    pub fn resolve_type_ref(&self, token: Token) -> Option<(Resolver<'a>, u32)> {
        let refs = self.refs?;
        let raw = self.raw_name(token)?;
        let (at, row) = *refs.types.get(&raw)?;
        let (assembly, index) = &refs.assemblies[at];
        Some((
            Resolver {
                assembly,
                index,
                refs: Some(refs),
                qualify: self.qualify,
            },
            row,
        ))
    }

    /// A type token followed to its definition: the same assembly for a
    /// `TypeDef`, a reference for a `TypeRef`, the definition under a
    /// `TypeSpec`'s instantiation.
    #[must_use]
    pub fn definition_of(&self, token: Token) -> Option<(Resolver<'a>, u32)> {
        match token.table() {
            table::TYPE_DEF => Some((*self, token.row())),
            table::TYPE_REF => self.resolve_type_ref(token),
            table::TYPE_SPEC => match self.type_spec(token.row())? {
                TypeSig::Generic { definition, .. } => match *definition {
                    TypeSig::Class(inner) | TypeSig::ValueType(inner) => self.definition_of(inner),
                    _ => None,
                },
                TypeSig::Class(inner) | TypeSig::ValueType(inner) => self.definition_of(inner),
                _ => None,
            },
            _ => None,
        }
    }

    /// The definition behind a signature type, when it has one.
    #[must_use]
    pub fn definition_of_sig(&self, sig: &TypeSig) -> Option<(Resolver<'a>, u32)> {
        match sig {
            TypeSig::Class(token) | TypeSig::ValueType(token) => self.definition_of(*token),
            TypeSig::Generic { definition, .. } => self.definition_of_sig(definition),
            primitive => {
                let name = primitive_name(primitive)?;
                let token = *self.index.primitive_tokens.get(name)?;
                self.definition_of(token)
            }
        }
    }

    /// A canonical spelling of a type for comparing signatures across
    /// assemblies, where the tokens differ but the names do not.
    #[must_use]
    pub fn type_key(&self, sig: &TypeSig) -> String {
        match sig {
            TypeSig::Class(token) | TypeSig::ValueType(token) => match token.table() {
                table::TYPE_SPEC => self
                    .type_spec(token.row())
                    .map_or_else(|| "?".into(), |inner| self.type_key(&inner)),
                _ => self.raw_name(*token).unwrap_or_else(|| "?".into()),
            },
            TypeSig::Vector(inner) => format!("{}[]", self.type_key(inner)),
            TypeSig::Array { element, rank } => format!("{}[{rank}]", self.type_key(element)),
            TypeSig::Pointer(inner) => format!("{}*", self.type_key(inner)),
            TypeSig::ByRef(inner) => format!("{}&", self.type_key(inner)),
            TypeSig::Var(at) => format!("!{at}"),
            TypeSig::MVar(at) => format!("!!{at}"),
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                let args: Vec<String> = arguments.iter().map(|a| self.type_key(a)).collect();
                format!("{}<{}>", self.type_key(definition), args.join(","))
            }
            other => format!("{other:?}"),
        }
    }

    /// The method a `MemberRef` names, found in the type's definition: the
    /// one with that name whose signature spells the same types.
    #[must_use]
    pub fn resolve_member_method(
        &self,
        declaring: &TypeSig,
        name: &str,
        sig: &MethodSig,
    ) -> Option<(Resolver<'a>, u32)> {
        let (there, type_row) = self.definition_of_sig(declaring)?;
        let candidates = there
            .index
            .methods_by_name
            .get(&(type_row, name.to_string()))?;
        let wanted: Vec<String> = sig.parameters.iter().map(|p| self.type_key(p)).collect();
        for candidate in candidates {
            let Some(found) = there.assembly.table(table::METHOD_DEF).row(*candidate) else {
                continue;
            };
            let Some(their_sig) = there.method_sig_at(found.number(4)) else {
                continue;
            };
            if their_sig.instance != sig.instance
                || their_sig.arity != sig.arity
                || their_sig.parameters.len() != sig.parameters.len()
            {
                continue;
            }
            let theirs: Vec<String> = their_sig
                .parameters
                .iter()
                .map(|p| there.type_key(p))
                .collect();
            if theirs == wanted {
                return Some((there, *candidate));
            }
        }
        None
    }

    /// The nearest class two classes both derive from, when this assembly
    /// can name it.
    #[must_use]
    pub fn common_base(&self, a: &TypeSig, b: &TypeSig) -> Option<TypeSig> {
        let (TypeSig::Class(_), TypeSig::Class(_)) = (a, b) else {
            return None;
        };
        let chain = |ty: &TypeSig| -> Vec<String> {
            let mut names = Vec::new();
            let mut current = self.definition_of_sig(ty);
            while let Some((there, row)) = current {
                let token = Token::new(table::TYPE_DEF, row);
                let Some(name) = there.raw_name(token) else {
                    break;
                };
                names.push(name);
                let Some(found) = there.assembly.row(token) else {
                    break;
                };
                let base = found.token(3);
                if base.is_nil() || names.len() > 32 {
                    break;
                }
                current = there.definition_of(base);
            }
            names
        };
        let (first, second) = (chain(a), chain(b));
        let shared = second.iter().find(|name| first.contains(name))?;
        if first.first() == Some(shared) {
            return Some(a.clone());
        }
        if second.first() == Some(shared) {
            return Some(b.clone());
        }
        if shared == "System.Object" {
            return Some(TypeSig::Object);
        }
        for table_id in [table::TYPE_DEF, table::TYPE_REF] {
            for row in 1..=self.assembly.rows(table_id) {
                let token = Token::new(table_id, row);
                if self.raw_name(token).as_deref() == Some(shared.as_str()) {
                    return Some(TypeSig::Class(token));
                }
            }
        }
        None
    }

    /// The names the types nested in a type and in those enclosing it go
    /// by there: another type of one of these names has to be qualified.
    #[must_use]
    pub fn nested_names_in_scope(&self, row: u32) -> HashSet<String> {
        let mut names = HashSet::new();
        let mut current = Some(row);
        let types = self.assembly.table(table::TYPE_DEF);
        while let Some(at) = current {
            for nested in self.nested_of(at) {
                if let Some(found) = types.row(nested) {
                    let name = self.string(found.number(1));
                    let name = name.split('`').next().unwrap_or(name);
                    if !name.starts_with('<') {
                        names.insert(name.to_string());
                    }
                }
            }
            current = self.index.nested_parent.get(&at).copied();
        }
        names
    }

    /// The nested types of a type.
    #[must_use]
    pub fn nested_of(&self, row: u32) -> Vec<u32> {
        self.index
            .nested_children
            .get(&row)
            .cloned()
            .unwrap_or_default()
    }

    /// The interfaces a type lists.
    #[must_use]
    pub fn interfaces_of(&self, row: u32) -> Vec<Token> {
        self.index.interfaces.get(&row).cloned().unwrap_or_default()
    }

    /// The `MethodImpl` rows of a type, as `(body, declaration)`.
    #[must_use]
    pub fn method_impls_of(&self, row: u32) -> Vec<(Token, Token)> {
        self.index
            .method_impls
            .get(&row)
            .cloned()
            .unwrap_or_default()
    }

    /// The RVA of a field with data.
    #[must_use]
    pub fn field_rva(&self, field_row: u32) -> Option<u32> {
        self.index.field_rva.get(&field_row).copied()
    }

    /// The `Property` rows of a type, as a range.
    #[must_use]
    pub fn property_range(&self, type_row: u32) -> Option<(u32, u32)> {
        self.index.properties.get(&type_row).copied()
    }

    /// The `Event` rows of a type, as a range.
    #[must_use]
    pub fn event_range(&self, type_row: u32) -> Option<(u32, u32)> {
        self.index.events.get(&type_row).copied()
    }

    /// The `GenericParam` rows of a type or method: `(name, flags, row)`.
    #[must_use]
    pub fn generic_param_rows(&self, is_method: bool, row: u32) -> Vec<(String, u16, u32)> {
        let wanted = (row << 1) | u32::from(is_method);
        self.index
            .generic_params
            .get(&wanted)
            .map(|params| {
                params
                    .iter()
                    .map(|(_, name, flags, row)| (name.clone(), *flags, *row))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The constraints on a `GenericParam` row.
    #[must_use]
    pub fn constraints_of(&self, param_row: u32) -> Vec<Token> {
        self.index
            .constraints
            .get(&param_row)
            .cloned()
            .unwrap_or_default()
    }

    /// The same resolver, spelling names with their namespaces.
    #[must_use]
    pub const fn qualified(self) -> Self {
        Self {
            qualify: true,
            ..self
        }
    }

    fn spell(&self, namespace: &str, name: &str) -> String {
        if self.qualify {
            qualified(namespace, name)
        } else {
            name.to_string()
        }
    }

    fn string(&self, offset: u32) -> &'a str {
        self.assembly.heaps().string(offset)
    }

    /// `Namespace.Name` of a `TypeDef` row, with the arity suffix removed and
    /// enclosing types spelled in front of a nested one.
    #[must_use]
    pub fn type_def_name(&self, row: u32) -> String {
        let Some(found) = self.assembly.table(table::TYPE_DEF).row(row) else {
            return format!("TypeDef{row}");
        };
        let name = strip_arity(self.string(found.number(1)));
        if let Some(outer) = self.enclosing_type(row) {
            return format!("{}.{name}", self.type_def_name(outer));
        }
        let namespace = self.string(found.number(2));
        if self.index.ambiguous.contains(self.string(found.number(1))) {
            return qualified(namespace, name);
        }
        self.spell(namespace, name)
    }

    /// The simple name of a `TypeDef` row, arity removed.
    #[must_use]
    pub fn type_def_simple_name(&self, row: u32) -> String {
        self.assembly.table(table::TYPE_DEF).row(row).map_or_else(
            || format!("TypeDef{row}"),
            |found| strip_arity(self.string(found.number(1))).to_string(),
        )
    }

    /// The `TypeDef` row of an anonymous type, `new { a, b }`'s class.
    #[must_use]
    pub fn anonymous_type_row(&self, ty: &TypeSig) -> Option<u32> {
        let token = match ty {
            TypeSig::Class(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) => *token,
                _ => return None,
            },
            _ => return None,
        };
        if token.table() != table::TYPE_DEF {
            return None;
        }
        let name = self.type_def_simple_name(token.row());
        (name.starts_with("<>f__AnonymousType") || name.starts_with("VB$AnonymousType"))
            .then_some(token.row())
    }

    /// Whether a type is, or is built from, an anonymous type: one no
    /// source can name.
    #[must_use]
    pub fn mentions_anonymous(&self, ty: &TypeSig) -> bool {
        match ty {
            TypeSig::Vector(inner) | TypeSig::Pointer(inner) | TypeSig::ByRef(inner) => {
                self.mentions_anonymous(inner)
            }
            TypeSig::Array { element, .. } => self.mentions_anonymous(element),
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                self.anonymous_type_row(ty).is_some()
                    || self.is_anonymous_delegate(definition)
                    || arguments
                        .iter()
                        .any(|argument| self.mentions_anonymous(argument))
            }
            other => self.anonymous_type_row(other).is_some() || self.is_anonymous_delegate(other),
        }
    }

    /// Whether a type is a delegate the compiler made for a lambda's natural
    /// type (`var f = (int x, params int[] rest) => …`): `<>f__AnonymousDelegate0`
    /// from rustlyn, `<>A{…}` and `<>F{…}` from Roslyn. No source names one.
    fn is_anonymous_delegate(&self, ty: &TypeSig) -> bool {
        let TypeSig::Class(token) = ty else {
            return false;
        };
        token.table() == table::TYPE_DEF && {
            let name = self.type_def_simple_name(token.row());
            name.starts_with("<>f__AnonymousDelegate")
                || name.starts_with("<>A{")
                || name.starts_with("<>F{")
                || name.starts_with("<>A`")
                || name.starts_with("<>F`")
        }
    }

    /// The properties of an anonymous type, in order: its type
    /// parameters are named after them, `<x>j__TPar`.
    #[must_use]
    pub fn anonymous_members(&self, row: u32) -> Vec<String> {
        self.type_generics(row)
            .into_iter()
            .map(|name| {
                name.strip_prefix('<')
                    .and_then(|rest| rest.split_once('>'))
                    .map_or(name.clone(), |(member, _)| member.to_string())
            })
            .collect()
    }

    /// The `TypeDef` a nested type sits inside, when it is nested.
    #[must_use]
    pub fn enclosing_type(&self, row: u32) -> Option<u32> {
        self.index.nested_parent.get(&row).copied()
    }

    /// The full name a `TypeRef` row spells, nesting included.
    #[must_use]
    pub fn type_ref_name(&self, row: u32) -> String {
        let Some(found) = self.assembly.table(table::TYPE_REF).row(row) else {
            return format!("TypeRef{row}");
        };
        let name = strip_arity(self.string(found.number(1)));
        let scope = found.token(0);
        if scope.table() == table::TYPE_REF && !scope.is_nil() {
            return format!("{}.{name}", self.type_ref_name(scope.row()));
        }
        if self.index.ambiguous.contains(self.string(found.number(1))) {
            return qualified(self.string(found.number(2)), name);
        }
        self.spell(self.string(found.number(2)), name)
    }

    /// The raw, namespace-qualified name with the arity still attached, which
    /// is what well-known types are recognised by.
    #[must_use]
    pub fn raw_name(&self, token: Token) -> Option<String> {
        let found = self.assembly.row(token)?;
        match token.table() {
            table::TYPE_DEF => {
                if let Some(outer) = self.enclosing_type(token.row()) {
                    return Some(format!(
                        "{}/{}",
                        self.raw_name(Token::new(table::TYPE_DEF, outer))?,
                        self.string(found.number(1))
                    ));
                }
                Some(qualified(
                    self.string(found.number(2)),
                    self.string(found.number(1)),
                ))
            }
            table::TYPE_REF => {
                let scope = found.token(0);
                if scope.table() == table::TYPE_REF && !scope.is_nil() {
                    return Some(format!(
                        "{}/{}",
                        self.raw_name(scope)?,
                        self.string(found.number(1))
                    ));
                }
                Some(qualified(
                    self.string(found.number(2)),
                    self.string(found.number(1)),
                ))
            }
            _ => None,
        }
    }

    /// How many type parameters a type token declares, nesting included.
    #[must_use]
    pub fn arity_of(&self, token: Token) -> usize {
        self.raw_name(token).map_or(0, |raw| {
            raw.split('/')
                .map(|part| {
                    part.rsplit_once('`')
                        .and_then(|(_, n)| n.parse::<usize>().ok())
                        .unwrap_or(0)
                })
                .sum()
        })
    }

    /// The signature a `TypeSpec` row holds.
    #[must_use]
    pub fn type_spec(&self, row: u32) -> Option<TypeSig> {
        let found = self.assembly.table(table::TYPE_SPEC).row(row)?;
        let bytes = self.assembly.heaps().blob(found.number(0)).ok()?;
        Blob::new(bytes).type_sig().ok()
    }

    /// A type token as a signature: a `TypeSpec` becomes what it stands for,
    /// and a reference to `System.Int32` becomes `int`.
    #[must_use]
    pub fn token_sig(&self, token: Token) -> TypeSig {
        if token.table() == table::TYPE_SPEC {
            return self.type_spec(token.row()).unwrap_or(TypeSig::Unknown(0));
        }
        if let Some(primitive) = self.raw_name(token).as_deref().and_then(primitive_of) {
            return primitive;
        }
        if self.is_value_type_token(token) {
            TypeSig::ValueType(token)
        } else {
            TypeSig::Class(token)
        }
    }

    /// The C# spelling of a type token.
    #[must_use]
    pub fn token_name(&self, token: Token, generics: &Generics) -> String {
        match token.table() {
            table::TYPE_DEF => self.type_def_name(token.row()),
            table::TYPE_REF => self.type_ref_name(token.row()),
            table::TYPE_SPEC => self.type_spec(token.row()).map_or_else(
                || format!("TypeSpec{}", token.row()),
                |sig| self.type_name(&sig, generics),
            ),
            _ => format!("{token:?}"),
        }
    }

    /// The C# spelling of a signature type: keywords for the primitives, `T?`
    /// for `Nullable<T>`, tuples in parentheses.
    #[must_use]
    pub fn type_name(&self, sig: &TypeSig, generics: &Generics) -> String {
        self.type_name_with(sig, generics, &mut Annotations::default())
    }

    /// The same, with tuple element names and `?` on the reference types an
    /// attribute annotated.
    #[must_use]
    #[allow(clippy::too_many_lines)]
    pub fn type_name_with(
        &self,
        sig: &TypeSig,
        generics: &Generics,
        annotations: &mut Annotations,
    ) -> String {
        let annotated = |text: String, annotations: &mut Annotations| {
            if annotations.next_nullable() == 2 {
                format!("{text}?")
            } else {
                text
            }
        };
        match sig {
            TypeSig::Void => "void".into(),
            TypeSig::String => annotated("string".into(), annotations),
            TypeSig::Object => annotated("object".into(), annotations),
            TypeSig::Boolean
            | TypeSig::Char
            | TypeSig::SByte
            | TypeSig::Byte
            | TypeSig::Int16
            | TypeSig::UInt16
            | TypeSig::Int32
            | TypeSig::UInt32
            | TypeSig::Int64
            | TypeSig::UInt64
            | TypeSig::Single
            | TypeSig::Double
            | TypeSig::IntPtr
            | TypeSig::UIntPtr
            | TypeSig::TypedReference => {
                // A value type takes a byte and never a `?`.
                annotations.next_nullable();
                self.plain_type_name(sig, generics)
            }
            TypeSig::Class(_) | TypeSig::ValueType(_) => {
                let text = self.plain_type_name(sig, generics);
                if self.is_value_type(sig) {
                    annotations.next_nullable();
                    text
                } else {
                    annotated(text, annotations)
                }
            }
            TypeSig::Vector(element) => {
                let flag = annotations.next_nullable();
                let inner = self.type_name_with(element, generics, annotations);
                if flag == 2 {
                    format!("{inner}[]?")
                } else {
                    format!("{inner}[]")
                }
            }
            TypeSig::Array { element, rank } => {
                let flag = annotations.next_nullable();
                let inner = self.type_name_with(element, generics, annotations);
                let text = format!(
                    "{inner}[{}]",
                    ",".repeat((*rank as usize).saturating_sub(1))
                );
                if flag == 2 { format!("{text}?") } else { text }
            }
            TypeSig::Pointer(element) => {
                annotations.next_nullable();
                format!("{}*", self.type_name_with(element, generics, annotations))
            }
            TypeSig::ByRef(element) => {
                format!(
                    "ref {}",
                    self.type_name_with(element, generics, annotations)
                )
            }
            TypeSig::Var(_) | TypeSig::MVar(_) => {
                let text = self.plain_type_name(sig, generics);
                annotated(text, annotations)
            }
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                let flag = annotations.next_nullable();
                let token = match definition.as_ref() {
                    TypeSig::Class(token) | TypeSig::ValueType(token) => Some(*token),
                    _ => None,
                };
                let raw = token.and_then(|token| self.raw_name(token));
                let is_nullable =
                    raw.as_deref() == Some("System.Nullable`1") && arguments.len() == 1;
                let is_tuple = raw
                    .as_deref()
                    .is_some_and(|name| name.starts_with("System.ValueTuple`"))
                    && arguments.len() >= 2;
                // The tuple's own names come off the queue before its
                // elements' types are spelled.
                let names: Vec<Option<String>> = if is_tuple {
                    (0..arguments.len())
                        .map(|_| annotations.tuple_names.pop_front().flatten())
                        .collect()
                } else {
                    Vec::new()
                };
                let args: Vec<String> = arguments
                    .iter()
                    .enumerate()
                    .map(|(at, argument)| {
                        let text = self.type_name_with(argument, generics, annotations);
                        match names.get(at) {
                            Some(Some(name)) => format!("{text} {name}"),
                            _ => text,
                        }
                    })
                    .collect();
                if is_nullable {
                    return format!("{}?", args[0]);
                }
                if is_tuple {
                    return format!("({})", args.join(", "));
                }
                let text = match token {
                    Some(token) => self.generic_name(token, &args),
                    None => format!(
                        "{}<{}>",
                        self.plain_type_name(definition, generics),
                        args.join(", ")
                    ),
                };
                if flag == 2 && !self.is_value_type(sig) {
                    format!("{text}?")
                } else {
                    text
                }
            }
            // The signature is not read, and a bare `delegate*` is not C#:
            // the pointer is what is known about it.
            TypeSig::FunctionPointer(_) => "void*".into(),
            TypeSig::Unknown(code) => format!("?{code:#x}"),
        }
    }

    /// The spelling of a type with nothing read off the annotations: the
    /// leaf cases of [`Self::type_name_with`].
    fn plain_type_name(&self, sig: &TypeSig, generics: &Generics) -> String {
        match sig {
            TypeSig::Void => "void".into(),
            TypeSig::Boolean => "bool".into(),
            TypeSig::Char => "char".into(),
            TypeSig::SByte => "sbyte".into(),
            TypeSig::Byte => "byte".into(),
            TypeSig::Int16 => "short".into(),
            TypeSig::UInt16 => "ushort".into(),
            TypeSig::Int32 => "int".into(),
            TypeSig::UInt32 => "uint".into(),
            TypeSig::Int64 => "long".into(),
            TypeSig::UInt64 => "ulong".into(),
            TypeSig::Single => "float".into(),
            TypeSig::Double => "double".into(),
            TypeSig::String => "string".into(),
            TypeSig::Object => "object".into(),
            TypeSig::IntPtr => "nint".into(),
            TypeSig::UIntPtr => "nuint".into(),
            TypeSig::TypedReference => "TypedReference".into(),
            TypeSig::Class(token) | TypeSig::ValueType(token) => {
                let raw = self.raw_name(*token);
                match raw.as_deref() {
                    Some("System.Decimal") => "decimal".into(),
                    Some(raw) if primitive_of(raw).is_some() => {
                        self.type_name(&primitive_of(raw).unwrap_or(TypeSig::Object), generics)
                    }
                    _ => self.token_name(*token, generics),
                }
            }
            TypeSig::Vector(element) => format!("{}[]", self.type_name(element, generics)),
            TypeSig::Array { element, rank } => format!(
                "{}[{}]",
                self.type_name(element, generics),
                ",".repeat((*rank as usize).saturating_sub(1))
            ),
            TypeSig::Pointer(element) => format!("{}*", self.type_name(element, generics)),
            TypeSig::ByRef(element) => format!("ref {}", self.type_name(element, generics)),
            TypeSig::Var(at) => generics
                .type_params
                .get(*at as usize)
                .cloned()
                .unwrap_or_else(|| format!("T{at}")),
            TypeSig::MVar(at) => generics
                .method_params
                .get(*at as usize)
                .cloned()
                .unwrap_or_else(|| format!("TM{at}")),
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                let token = match definition.as_ref() {
                    TypeSig::Class(token) | TypeSig::ValueType(token) => Some(*token),
                    _ => None,
                };
                let raw = token.and_then(|token| self.raw_name(token));
                let args: Vec<String> = arguments
                    .iter()
                    .map(|argument| self.type_name(argument, generics))
                    .collect();
                match raw.as_deref() {
                    Some("System.Nullable`1") if args.len() == 1 => return format!("{}?", args[0]),
                    Some(name) if name.starts_with("System.ValueTuple`") && args.len() >= 2 => {
                        return format!("({})", args.join(", "));
                    }
                    _ => {}
                }
                let Some(token) = token else {
                    return format!(
                        "{}<{}>",
                        self.type_name(definition, generics),
                        args.join(", ")
                    );
                };
                self.generic_name(token, &args)
            }
            // The signature is not read, and a bare `delegate*` is not C#:
            // the pointer is what is known about it.
            TypeSig::FunctionPointer(_) => "void*".into(),
            TypeSig::Unknown(code) => format!("?{code:#x}"),
        }
    }

    /// `Outer<A>.Inner<B>`: the arguments handed out along the nesting chain,
    /// each level taking as many as its own suffix says.
    /// An open generic type as `typeof` names it: `Dictionary<,>`,
    /// `Outer<>.Inner<>`. `None` when the type is not generic.
    #[must_use]
    pub fn open_generic_name(&self, token: Token) -> Option<String> {
        let raw = self.raw_name(token)?;
        if !raw.contains('`') {
            return None;
        }
        let parts: Vec<&str> = raw.split('/').collect();
        let mut out = String::new();
        for (index, part) in parts.iter().enumerate() {
            let (name, arity) = part
                .rsplit_once('`')
                .and_then(|(name, n)| n.parse::<usize>().ok().map(|n| (name, n)))
                .unwrap_or((part, 0));
            if index > 0 {
                out.push('.');
            }
            let name = if index == 0 && !self.qualify && !self.index.ambiguous.contains(*part) {
                name.rsplit('.').next().unwrap_or(name)
            } else {
                name
            };
            out.push_str(name);
            if arity > 0 {
                out.push('<');
                out.push_str(&",".repeat(arity - 1));
                out.push('>');
            }
        }
        Some(out)
    }

    fn generic_name(&self, token: Token, args: &[String]) -> String {
        let Some(raw) = self.raw_name(token) else {
            return format!(
                "{}<{}>",
                self.token_name(token, &Generics::default()),
                args.join(", ")
            );
        };
        let namespace_and_parts: Vec<&str> = raw.split('/').collect();
        let mut used = 0usize;
        let mut out = String::new();
        for (index, part) in namespace_and_parts.iter().enumerate() {
            let (name, arity) = part
                .rsplit_once('`')
                .and_then(|(name, n)| n.parse::<usize>().ok().map(|n| (name, n)))
                .unwrap_or((part, 0));
            if index > 0 {
                out.push('.');
            }
            let name = if index == 0 && !self.qualify {
                name.rsplit('.').next().unwrap_or(name)
            } else {
                name
            };
            out.push_str(name);
            if arity > 0 {
                let slice = &args[used.min(args.len())..(used + arity).min(args.len())];
                used += arity;
                out.push('<');
                out.push_str(&slice.join(", "));
                out.push('>');
            }
        }
        out
    }

    /// Whether a type token names a value type, as far as one assembly can
    /// tell: a `TypeDef` says what it extends, and a `TypeRef` is judged by
    /// the names the framework is known to give its structs.
    #[must_use]
    pub fn is_value_type_token(&self, token: Token) -> bool {
        match token.table() {
            table::TYPE_DEF => {
                let Some(found) = self.assembly.row(token) else {
                    return false;
                };
                let base = found.token(3);
                matches!(
                    self.raw_name(base).as_deref(),
                    Some("System.ValueType" | "System.Enum")
                )
            }
            table::TYPE_REF if self.resolve_type_ref(token).is_some() => {
                let Some((there, row)) = self.resolve_type_ref(token) else {
                    return false;
                };
                there.is_value_type_token(Token::new(table::TYPE_DEF, row))
            }
            table::TYPE_REF => self
                .raw_name(token)
                .is_some_and(|name| is_well_known_struct(&name)),
            table::TYPE_SPEC => match self.type_spec(token.row()) {
                Some(TypeSig::Generic { definition, .. }) => match *definition {
                    TypeSig::ValueType(_) => true,
                    TypeSig::Class(token) => self.is_value_type_token(token),
                    _ => false,
                },
                Some(TypeSig::ValueType(_)) => true,
                _ => false,
            },
            _ => false,
        }
    }

    /// Whether a type is a delegate: defined here over `MulticastDelegate`,
    /// or one of the framework's delegate families.
    #[must_use]
    pub fn is_delegate(&self, sig: &TypeSig) -> bool {
        let token = match sig {
            TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
                _ => return false,
            },
            _ => return false,
        };
        match token.table() {
            table::TYPE_DEF => self.assembly.row(token).is_some_and(|found| {
                matches!(
                    self.raw_name(found.token(3)).as_deref(),
                    Some("System.MulticastDelegate" | "System.Delegate")
                )
            }),
            table::TYPE_REF if self.resolve_type_ref(token).is_some() => {
                self.resolve_type_ref(token).is_some_and(|(there, row)| {
                    there.is_delegate(&TypeSig::Class(Token::new(table::TYPE_DEF, row)))
                })
            }
            table::TYPE_REF => self.raw_name(token).is_some_and(|raw| {
                let (namespace, name) = raw.rsplit_once('.').unwrap_or(("", &raw));
                let stem = strip_arity(name);
                (namespace == "System"
                    && matches!(
                        stem,
                        "Func"
                            | "Action"
                            | "Predicate"
                            | "Comparison"
                            | "Converter"
                            | "EventHandler"
                            | "AsyncCallback"
                            | "ThreadStart"
                    ))
                    || name.ends_with("Handler")
                    || name.ends_with("Callback")
                    || name.ends_with("Delegate")
            }),
            _ => false,
        }
    }

    /// Whether a type is an interface: by its flags when defined here, by
    /// the `I` convention when referenced.
    #[must_use]
    pub fn is_interface(&self, sig: &TypeSig) -> bool {
        let token = match sig {
            TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
                _ => return false,
            },
            _ => return false,
        };
        match token.table() {
            table::TYPE_DEF => self
                .assembly
                .row(token)
                .is_some_and(|found| found.number(0) & 0x20 != 0),
            table::TYPE_REF if self.resolve_type_ref(token).is_some() => {
                self.resolve_type_ref(token).is_some_and(|(there, row)| {
                    there.is_interface(&TypeSig::Class(Token::new(table::TYPE_DEF, row)))
                })
            }
            table::TYPE_REF => self.raw_name(token).is_some_and(|raw| {
                let name = raw.rsplit(['.', '/']).next().unwrap_or(&raw);
                let mut chars = name.chars();
                chars.next() == Some('I') && chars.next().is_some_and(char::is_uppercase)
            }),
            _ => false,
        }
    }

    /// Whether a signature type is `Nullable<T>`.
    #[must_use]
    pub fn is_nullable(&self, sig: &TypeSig) -> bool {
        matches!(sig, TypeSig::Generic { definition, .. }
            if matches!(definition.as_ref(), TypeSig::ValueType(token) | TypeSig::Class(token)
                if self.raw_name(*token).as_deref() == Some("System.Nullable`1")))
    }

    /// Whether a signature type is a value type.
    #[must_use]
    pub fn is_value_type(&self, sig: &TypeSig) -> bool {
        match sig {
            TypeSig::Class(token) => self.is_value_type_token(*token),
            TypeSig::ValueType(_) => true,
            TypeSig::Generic { definition, .. } => self.is_value_type(definition),
            TypeSig::Boolean
            | TypeSig::Char
            | TypeSig::SByte
            | TypeSig::Byte
            | TypeSig::Int16
            | TypeSig::UInt16
            | TypeSig::Int32
            | TypeSig::UInt32
            | TypeSig::Int64
            | TypeSig::UInt64
            | TypeSig::Single
            | TypeSig::Double
            | TypeSig::IntPtr
            | TypeSig::UIntPtr => true,
            _ => false,
        }
    }

    /// The `TypeDef` an enum token names, when it is an enum defined here,
    /// with the members and their values.
    #[must_use]
    pub fn enum_members(&self, token: Token) -> Option<Vec<(String, i64)>> {
        let token = match token.table() {
            table::TYPE_SPEC => match self.type_spec(token.row())? {
                TypeSig::ValueType(token) | TypeSig::Class(token) => token,
                _ => return None,
            },
            _ => token,
        };
        if token.table() == table::TYPE_REF {
            let (there, row) = self.resolve_type_ref(token)?;
            return there.enum_members(Token::new(table::TYPE_DEF, row));
        }
        if token.table() != table::TYPE_DEF {
            return None;
        }
        let found = self.assembly.row(token)?;
        if self.raw_name(found.token(3)).as_deref() != Some("System.Enum") {
            return None;
        }
        let mut members = Vec::new();
        for (field_row, field) in self.fields_of(token.row()) {
            if field.number(0) & 0x0040 == 0 {
                continue;
            }
            let name = self.string(field.number(1)).to_string();
            if let Some(Constant::Int(value)) =
                self.constant_of(Token::new(table::FIELD, field_row))
            {
                members.push((name, value));
            }
        }
        Some(members)
    }

    /// The enum a signature type names, when it is one defined here.
    #[must_use]
    pub fn enum_of(&self, sig: &TypeSig) -> Option<Vec<(String, i64)>> {
        match sig {
            TypeSig::ValueType(token) | TypeSig::Class(token) => self.enum_members(*token),
            TypeSig::Generic { definition, .. } => self.enum_of(definition),
            _ => None,
        }
    }

    /// The fields of a `TypeDef`, with their row numbers.
    pub fn fields_of(&self, type_row: u32) -> Vec<(u32, Row<'a>)> {
        let types = self.assembly.table(table::TYPE_DEF);
        let fields = self.assembly.table(table::FIELD);
        let Some(row) = types.row(type_row) else {
            return Vec::new();
        };
        let start = row.number(4);
        let end = types
            .row(type_row + 1)
            .map_or(fields.len() + 1, |next| next.number(4));
        (start..end)
            .filter_map(|number| fields.row(number).map(|field| (number, field)))
            .collect()
    }

    /// The methods of a `TypeDef`, with their row numbers.
    /// Whether a type, or one it derives from, implements a member of the
    /// given name explicitly: a call of the interface's member through the
    /// type has to go through the interface.
    #[must_use]
    pub fn implements_explicitly(&self, sig: &TypeSig, name: &str) -> bool {
        let token = match sig {
            TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
            TypeSig::Generic { definition, .. } => match definition.as_ref() {
                TypeSig::Class(token) | TypeSig::ValueType(token) => *token,
                _ => return false,
            },
            _ => return false,
        };
        self.explicitly_in(token, name, 0)
    }

    fn explicitly_in(&self, token: Token, name: &str, depth: u32) -> bool {
        if depth > 16 {
            return false;
        }
        match token.table() {
            table::TYPE_DEF => {
                let heaps = self.assembly.heaps();
                let suffix = format!(".{name}");
                let mut implicit = false;
                for (_, method) in self.methods_of(token.row()) {
                    let own = heaps.string(method.number(3));
                    if own.len() > suffix.len() && own.ends_with(&suffix) {
                        return true;
                    }
                    implicit |= own == name;
                }
                if implicit {
                    return false;
                }
                let Some(found) = self.assembly.row(token) else {
                    return false;
                };
                let base = found.token(3);
                base.row() != 0 && self.explicitly_in(base, name, depth + 1)
            }
            table::TYPE_REF => self.resolve_type_ref(token).is_some_and(|(there, row)| {
                there.explicitly_in(Token::new(table::TYPE_DEF, row), name, depth + 1)
            }),
            table::TYPE_SPEC => match self.type_spec(token.row()) {
                Some(TypeSig::Generic { definition, .. }) => match *definition {
                    TypeSig::Class(inner) | TypeSig::ValueType(inner) => {
                        self.explicitly_in(inner, name, depth + 1)
                    }
                    _ => false,
                },
                _ => false,
            },
            _ => false,
        }
    }

    pub fn methods_of(&self, type_row: u32) -> Vec<(u32, Row<'a>)> {
        let types = self.assembly.table(table::TYPE_DEF);
        let methods = self.assembly.table(table::METHOD_DEF);
        let Some(row) = types.row(type_row) else {
            return Vec::new();
        };
        let start = row.number(5);
        let end = types
            .row(type_row + 1)
            .map_or(methods.len() + 1, |next| next.number(5));
        (start..end)
            .filter_map(|number| methods.row(number).map(|method| (number, method)))
            .collect()
    }

    /// The `TypeDef` a method row belongs to.
    #[must_use]
    pub fn method_owner(&self, method_row: u32) -> Option<u32> {
        self.index
            .method_owner
            .get(method_row as usize)
            .copied()
            .filter(|owner| *owner != 0)
    }

    /// The `TypeDef` a field row belongs to.
    #[must_use]
    pub fn field_owner(&self, field_row: u32) -> Option<u32> {
        self.index
            .field_owner
            .get(field_row as usize)
            .copied()
            .filter(|owner| *owner != 0)
    }

    /// The `Param` rows of a method: `(sequence, flags, name)`.
    #[must_use]
    pub fn params_of(&self, method_row: u32) -> Vec<(u16, u16, String)> {
        self.param_rows(method_row)
            .into_iter()
            .map(|(_, sequence, flags, name)| (sequence, flags, name))
            .collect()
    }

    /// The `Param` rows of a method: `(row, sequence, flags, name)`.
    #[must_use]
    pub fn param_rows(&self, method_row: u32) -> Vec<(u32, u16, u16, String)> {
        let methods = self.assembly.table(table::METHOD_DEF);
        let params = self.assembly.table(table::PARAM);
        let Some(row) = methods.row(method_row) else {
            return Vec::new();
        };
        let start = row.number(5);
        let end = methods
            .row(method_row + 1)
            .map_or(params.len() + 1, |next| next.number(5));
        (start..end)
            .filter_map(|number| params.row(number).map(|param| (number, param)))
            .map(|(number, param)| {
                (
                    number,
                    param.number(1) as u16,
                    param.number(0) as u16,
                    self.string(param.number(2)).to_string(),
                )
            })
            .collect()
    }

    /// The names of the type parameters a `TypeDef` or `MethodDef` declares.
    #[must_use]
    pub fn generic_param_names(&self, is_method: bool, row: u32) -> Vec<String> {
        self.generic_param_rows(is_method, row)
            .into_iter()
            .map(|(name, _, _)| name)
            .collect()
    }

    /// The generics in scope inside a method: its type's parameters, the
    /// enclosing types' included, and its own.
    #[must_use]
    pub fn generics_of(&self, method_row: u32) -> Generics {
        let mut type_params = Vec::new();
        if let Some(owner) = self.method_owner(method_row) {
            type_params = self.type_generics(owner);
        }
        Generics {
            type_params,
            method_params: self.generic_param_names(true, method_row),
        }
    }

    /// The type parameters of a type, outer types' first.
    #[must_use]
    pub fn type_generics(&self, type_row: u32) -> Vec<String> {
        // A nested type's `GenericParam` rows repeat the outer ones, so the
        // list of the innermost type is already complete.
        self.generic_param_names(false, type_row)
    }

    /// A method signature blob, decoded.
    #[must_use]
    pub fn method_sig_at(&self, blob: u32) -> Option<MethodSig> {
        let bytes = self.assembly.heaps().blob(blob).ok()?;
        Blob::new(bytes).method_sig().ok()
    }

    /// The method behind a `MethodDef`, `MemberRef` or `MethodSpec` token.
    #[must_use]
    pub fn method_ref(&self, token: Token) -> Option<MethodRef> {
        match token.table() {
            table::METHOD_DEF => {
                let found = self.assembly.row(token)?;
                let sig = self.method_sig_at(found.number(4))?;
                let owner = self.method_owner(token.row())?;
                let params = self.param_rows(token.row());
                let mut out_params = vec![false; sig.parameters.len()];
                let mut param_names = vec![String::new(); sig.parameters.len()];
                let mut param_defaults = vec![None; sig.parameters.len()];
                for (row, sequence, flags, name) in params {
                    if sequence == 0 {
                        continue;
                    }
                    if let Some(slot) = out_params.get_mut(sequence as usize - 1) {
                        *slot = flags & 0x0002 != 0 && flags & 0x0001 == 0;
                    }
                    if let Some(slot) = param_names.get_mut(sequence as usize - 1) {
                        *slot = name;
                    }
                    if flags & 0x1000 != 0
                        && let Some(slot) = param_defaults.get_mut(sequence as usize - 1)
                    {
                        *slot = self.constant_of(Token::new(table::PARAM, row));
                    }
                }
                let is_extension =
                    self.has_attribute(token, "System.Runtime.CompilerServices.ExtensionAttribute");
                Some(MethodRef {
                    token,
                    name: self.string(found.number(3)).to_string(),
                    declaring: self.declared_type_sig(owner),
                    sig,
                    type_args: Vec::new(),
                    out_params,
                    param_names,
                    param_defaults,
                    is_extension,
                    is_virtual: found.number(2) & 0x0040 != 0,
                })
            }
            table::MEMBER_REF => {
                let found = self.assembly.row(token)?;
                let sig = self.method_sig_at(found.number(2))?;
                let parent = found.token(0);
                let declaring = match parent.table() {
                    table::TYPE_DEF | table::TYPE_REF | table::TYPE_SPEC => self.token_sig(parent),
                    table::METHOD_DEF => self
                        .method_owner(parent.row())
                        .map_or(TypeSig::Unknown(0), |owner| self.declared_type_sig(owner)),
                    _ => TypeSig::Unknown(0),
                };
                let name = self.string(found.number(1)).to_string();
                // A reference into this assembly's own types (through a
                // generic instantiation, usually) has a definition to read
                // the parameter names and `out`s from.
                let mut out_params = Vec::new();
                let mut param_names = Vec::new();
                let mut param_defaults = Vec::new();
                let mut is_extension = false;
                let mut is_virtual = false;
                if let Some((there, row)) = self.resolve_member_method(&declaring, &name, &sig)
                    && let Some(defined) = there.method_ref(Token::new(table::METHOD_DEF, row))
                {
                    out_params = defined.out_params;
                    param_names = defined.param_names;
                    param_defaults = defined.param_defaults;
                    is_extension = defined.is_extension;
                    is_virtual = defined.is_virtual;
                }
                Some(MethodRef {
                    token,
                    name,
                    declaring,
                    sig,
                    type_args: Vec::new(),
                    out_params,
                    param_names,
                    param_defaults,
                    is_extension,
                    is_virtual,
                })
            }
            table::METHOD_SPEC => {
                let found = self.assembly.row(token)?;
                let mut method = self.method_ref(found.token(0))?;
                let bytes = self.assembly.heaps().blob(found.number(1)).ok()?;
                let mut blob = Blob::new(bytes);
                // A `MethodSpec` blob is `GENERICINST`, a count, then the types.
                blob.byte().ok()?;
                let count = blob.unsigned().ok()?;
                let mut args = Vec::with_capacity(count as usize);
                for _ in 0..count {
                    args.push(blob.type_sig().ok()?);
                }
                method.type_args = args;
                Some(method)
            }
            _ => None,
        }
    }

    /// The definition of a method a reference names, wherever it lives.
    #[must_use]
    pub fn definition_of_method(&self, method: &MethodRef) -> Option<(Resolver<'a>, u32)> {
        match method.token.table() {
            table::METHOD_DEF => Some((*self, method.token.row())),
            table::MEMBER_REF | table::METHOD_SPEC => {
                self.resolve_member_method(&method.declaring, &method.name, &method.sig)
            }
            _ => None,
        }
    }

    /// Whether a type declares a method of a name itself, hiding one of
    /// its base types'.
    #[must_use]
    pub fn declares_method(&self, ty: &TypeSig, name: &str) -> bool {
        let Some((there, row)) = self.definition_of_sig(ty) else {
            return false;
        };
        there
            .index
            .methods_by_name
            .contains_key(&(row, name.to_string()))
    }

    /// The element of a `fixed` buffer, when `ty` is the struct the
    /// compiler made for one.
    #[must_use]
    pub fn fixed_buffer_element(&self, ty: &TypeSig) -> Option<TypeSig> {
        let TypeSig::ValueType(token) = ty else {
            return None;
        };
        if token.table() != table::TYPE_DEF || !self.raw_name(*token)?.ends_with("e__FixedBuffer") {
            return None;
        }
        let heaps = self.assembly.heaps();
        let (_, element) = self.fields_of(token.row()).into_iter().next()?;
        Blob::new(heaps.blob(element.number(2)).ok()?)
            .field_sig()
            .ok()
    }

    /// Whether a type or one of its bases has a method or a property of a
    /// name, which hides an enclosing type's of the same name.
    #[must_use]
    pub fn has_member_named(&self, ty: &TypeSig, name: &str) -> bool {
        self.has_named(ty, name, true)
    }

    /// Whether a type or one of its bases has a method of a name.
    #[must_use]
    pub fn has_method_named(&self, ty: &TypeSig, name: &str) -> bool {
        self.has_named(ty, name, false)
    }

    fn has_named(&self, ty: &TypeSig, name: &str, properties: bool) -> bool {
        let mut current = self.definition_of_sig(ty);
        for _ in 0..16 {
            let Some((there, row)) = current else {
                return false;
            };
            let names = &there.index.methods_by_name;
            if names.contains_key(&(row, name.to_string()))
                || (properties && names.contains_key(&(row, format!("get_{name}"))))
            {
                return true;
            }
            let Some(found) = there.assembly.table(table::TYPE_DEF).row(row) else {
                return false;
            };
            let base = found.token(3);
            if base.is_nil() {
                return false;
            }
            current = there.definition_of(base);
        }
        false
    }

    /// Whether a class or one of its bases defines `==`, so that C#'s `==`
    /// on it calls that rather than comparing references.
    #[must_use]
    pub fn has_equality_operator(&self, ty: &TypeSig) -> bool {
        // A delegate's `==` compares what it calls, which for `null` is the
        // same as the reference.
        if matches!(ty, TypeSig::String | TypeSig::Object)
            || self.is_value_type(ty)
            || self.is_delegate(ty)
        {
            return false;
        }
        let mut current = self.definition_of_sig(ty);
        for _ in 0..16 {
            let Some((there, row)) = current else {
                return false;
            };
            if there
                .index
                .methods_by_name
                .contains_key(&(row, "op_Equality".to_string()))
            {
                return true;
            }
            let Some(found) = there.assembly.table(table::TYPE_DEF).row(row) else {
                return false;
            };
            let base = found.token(3);
            if base.is_nil() || there.raw_name(base).as_deref() == Some("System.Object") {
                return false;
            }
            current = there.definition_of(base);
        }
        false
    }

    /// The type a `null` argument has to be cast to for the call to name
    /// one overload, and whether that parameter is annotated nullable;
    /// nothing when no other overload of the same length could take it.
    #[must_use]
    pub fn null_cast_for(&self, method: &MethodRef, index: usize) -> Option<(TypeSig, bool)> {
        let (there, row) = self.definition_of_method(method)?;
        let param = method.sig.parameters.get(index)?;
        let type_row = there.method_owner(row)?;
        let candidates = there
            .index
            .methods_by_name
            .get(&(type_row, method.name.clone()))?;
        let own_key = there.type_key(param);
        let ambiguous = candidates.iter().any(|candidate| {
            if *candidate == row {
                return false;
            }
            let Some(found) = there.assembly.table(table::METHOD_DEF).row(*candidate) else {
                return false;
            };
            let Some(their_sig) = there.method_sig_at(found.number(4)) else {
                return false;
            };
            if their_sig.instance != method.sig.instance
                || their_sig.parameters.len() != method.sig.parameters.len()
            {
                return false;
            }
            let Some(theirs) = their_sig.parameters.get(index) else {
                return false;
            };
            if there.type_key(theirs) == own_key {
                return false;
            }
            // Its type parameters have to be inferable from the other
            // arguments, `null` telling nothing.
            let inferable = (0..their_sig.arity).all(|at| {
                their_sig
                    .parameters
                    .iter()
                    .enumerate()
                    .any(|(position, param)| position != index && mentions_mvar(param, at))
            });
            if !inferable {
                return false;
            }
            // `null` goes where a reference or a `Nullable<T>` goes.
            let is_nullable_struct = matches!(theirs, TypeSig::Generic { definition, .. }
                if matches!(definition.as_ref(), TypeSig::ValueType(_))
                    && there.type_key(definition).ends_with("System.Nullable`1"));
            !matches!(theirs, TypeSig::ByRef(_) | TypeSig::Pointer(_))
                && (!there.is_value_type(theirs) || is_nullable_struct)
        });
        if !ambiguous {
            return None;
        }
        let nullable = !there.is_value_type(param) && there.param_is_nullable(row, index);
        Some((param.clone(), nullable))
    }

    /// Whether another overload of a method, taking as many arguments,
    /// takes exactly `ty` where it takes something else: an argument of
    /// that type would pick it.
    #[must_use]
    pub fn another_overload_takes(&self, method: &MethodRef, index: usize, ty: &TypeSig) -> bool {
        let Some((there, row)) = self.definition_of_method(method) else {
            return false;
        };
        let Some(type_row) = there.method_owner(row) else {
            return false;
        };
        let Some(candidates) = there
            .index
            .methods_by_name
            .get(&(type_row, method.name.clone()))
        else {
            return false;
        };
        let wanted = self.type_key(ty);
        candidates.iter().any(|candidate| {
            *candidate != row
                && there
                    .assembly
                    .table(table::METHOD_DEF)
                    .row(*candidate)
                    .and_then(|found| there.method_sig_at(found.number(4)))
                    .is_some_and(|sig| {
                        sig.instance == method.sig.instance
                            && sig.parameters.len() == method.sig.parameters.len()
                            && sig
                                .parameters
                                .get(index)
                                .is_some_and(|param| there.type_key(param) == wanted)
                    })
        })
    }

    /// Whether a method is a property's or an event's accessor, by the
    /// special name its definition carries: `get_ItemOf(i)` is an indexer.
    #[must_use]
    pub fn is_accessor(&self, method: &MethodRef) -> bool {
        self.definition_of_method(method)
            .is_some_and(|(there, row)| there.index.semantics_by_method.contains_key(&row))
    }

    /// The primitive a type names, `System.Int32` as `int`, when it does.
    #[must_use]
    pub fn as_primitive(&self, ty: &TypeSig) -> Option<TypeSig> {
        match ty {
            TypeSig::ValueType(token) | TypeSig::Class(token) => {
                primitive_of(&self.raw_name(*token)?)
            }
            other if primitive_name(other).is_some() => Some(other.clone()),
            _ => None,
        }
    }

    /// Whether a property's getter returns a read-only reference.
    #[must_use]
    pub fn property_is_readonly_ref(&self, declaring: &TypeSig, name: &str) -> bool {
        let Some((there, row)) = self.definition_of_sig(declaring) else {
            return false;
        };
        there
            .index
            .methods_by_name
            .get(&(row, format!("get_{name}")))
            .into_iter()
            .flatten()
            .filter_map(|method| there.assembly.table(table::METHOD_DEF).row(*method))
            .filter_map(|found| there.method_sig_at(found.number(4)))
            .any(|sig| {
                sig.returns_required.iter().any(|token| {
                    there.raw_name(*token).as_deref()
                        == Some("System.Runtime.InteropServices.InAttribute")
                })
            })
    }

    /// Whether a method's parameter is `in`: a reference marked read-only.
    #[must_use]
    pub fn param_is_in(&self, method: &MethodRef, index: usize) -> bool {
        let Some((there, row)) = self.definition_of_method(method) else {
            return false;
        };
        there
            .param_rows(row)
            .into_iter()
            .find(|(_, sequence, _, _)| usize::from(*sequence) == index + 1)
            .is_some_and(|(param_row, ..)| {
                let token = Token::new(table::PARAM, param_row);
                // `ref readonly` takes what `in` does.
                there.has_attribute(token, "System.Runtime.CompilerServices.IsReadOnlyAttribute")
                    || there.has_attribute(
                        token,
                        "System.Runtime.CompilerServices.RequiresLocationAttribute",
                    )
            })
    }

    /// Whether a method's type has another of its name, of any arity.
    #[must_use]
    pub fn has_overloads(&self, method: &MethodRef) -> bool {
        let Some((there, row)) = self.definition_of_method(method) else {
            return false;
        };
        let Some(type_row) = there.method_owner(row) else {
            return false;
        };
        there
            .index
            .methods_by_name
            .get(&(type_row, method.name.clone()))
            .is_some_and(|rows| rows.len() > 1)
    }

    /// Whether a method's type has another of its name taking as many
    /// arguments, which a constant argument could pick instead.
    #[must_use]
    pub fn is_overloaded(&self, method: &MethodRef) -> bool {
        let Some((there, row)) = self.definition_of_method(method) else {
            return false;
        };
        let Some(type_row) = there.method_owner(row) else {
            return false;
        };
        let Some(candidates) = there
            .index
            .methods_by_name
            .get(&(type_row, method.name.clone()))
        else {
            return false;
        };
        candidates.iter().any(|candidate| {
            *candidate != row
                && there
                    .assembly
                    .table(table::METHOD_DEF)
                    .row(*candidate)
                    .and_then(|found| there.method_sig_at(found.number(4)))
                    .is_some_and(|sig| {
                        sig.instance == method.sig.instance
                            && sig.parameters.len() == method.sig.parameters.len()
                    })
        })
    }

    /// Whether the nullable annotations mark a parameter `T?`.
    #[must_use]
    pub fn param_is_nullable(&self, method_row: u32, index: usize) -> bool {
        let sequence = index as u16 + 1;
        if let Some((param_row, _, _, _)) = self
            .param_rows(method_row)
            .into_iter()
            .find(|(_, found, _, _)| *found == sequence)
            && let Some(flags) = self.nullable_flags(Token::new(table::PARAM, param_row))
        {
            return flags.first() == Some(&2);
        }
        let method = Token::new(table::METHOD_DEF, method_row);
        if let Some(context) = self.nullable_context(method) {
            return context == 2;
        }
        self.method_owner(method_row)
            .and_then(|owner| self.nullable_context(Token::new(table::TYPE_DEF, owner)))
            == Some(2)
    }

    /// The type a `TypeDef` row is, as a signature: the open generic form
    /// when it has type parameters.
    #[must_use]
    pub fn declared_type_sig(&self, type_row: u32) -> TypeSig {
        let token = Token::new(table::TYPE_DEF, type_row);
        let base = if self.is_value_type_token(token) {
            TypeSig::ValueType(token)
        } else {
            TypeSig::Class(token)
        };
        let params = self.type_generics(type_row);
        if params.is_empty() {
            base
        } else {
            TypeSig::Generic {
                definition: Box::new(base),
                arguments: (0..params.len() as u32).map(TypeSig::Var).collect(),
            }
        }
    }

    /// The field behind a `Field` or `MemberRef` token.
    #[must_use]
    pub fn field_ref(&self, token: Token) -> Option<FieldRef> {
        let found = self.assembly.row(token)?;
        match token.table() {
            table::FIELD => {
                let bytes = self.assembly.heaps().blob(found.number(2)).ok()?;
                let ty = Blob::new(bytes).field_sig().ok()?;
                let owner = self.field_owner(token.row())?;
                Some(FieldRef {
                    token,
                    name: self.string(found.number(1)).to_string(),
                    declaring: self.declared_type_sig(owner),
                    ty,
                    is_static: Some(found.number(0) & 0x0010 != 0),
                })
            }
            table::MEMBER_REF => {
                let bytes = self.assembly.heaps().blob(found.number(2)).ok()?;
                let ty = Blob::new(bytes).field_sig().ok()?;
                let parent = found.token(0);
                let name = self.string(found.number(1)).to_string();
                let declaring = self.token_sig(parent);
                let is_static = self.definition_of_sig(&declaring).and_then(|(there, row)| {
                    there
                        .fields_of(row)
                        .into_iter()
                        .find(|(_, field)| there.string(field.number(1)) == name)
                        .map(|(_, field)| field.number(0) & 0x0010 != 0)
                });
                Some(FieldRef {
                    token,
                    name,
                    declaring,
                    ty,
                    is_static,
                })
            }
            _ => None,
        }
    }

    /// The constant a `Field`, `Param` or `Property` row carries.
    #[must_use]
    pub fn constant_of(&self, parent: Token) -> Option<Constant> {
        let tag = match parent.table() {
            table::FIELD => 0,
            table::PARAM => 1,
            table::PROPERTY => 2,
            _ => return None,
        };
        let wanted = (parent.row() << 2) | tag;
        let row = self
            .assembly
            .table(table::CONSTANT)
            .row(*self.index.constants.get(&wanted)?)?;
        let kind = row.number(0) as u8;
        let bytes = self.assembly.heaps().blob(row.number(3)).ok()?;
        Some(match kind {
            0x02 => Constant::Bool(bytes.first().copied().unwrap_or(0) != 0),
            0x03 => Constant::Char(u16::from_le_bytes([
                bytes.first().copied().unwrap_or(0),
                bytes.get(1).copied().unwrap_or(0),
            ])),
            0x04 => Constant::Int(i64::from(bytes.first().copied().unwrap_or(0) as i8)),
            0x05 => Constant::Int(i64::from(bytes.first().copied().unwrap_or(0))),
            0x06 => Constant::Int(i64::from(i16::from_le_bytes(pair(bytes)))),
            0x07 => Constant::Int(i64::from(u16::from_le_bytes(pair(bytes)))),
            0x08 => Constant::Int(i64::from(i32::from_le_bytes(quad(bytes)))),
            0x09 => Constant::Int(i64::from(u32::from_le_bytes(quad(bytes)))),
            0x0A => Constant::Int(i64::from_le_bytes(octet(bytes))),
            0x0B => Constant::Int(u64::from_le_bytes(octet(bytes)) as i64),
            0x0C => Constant::Float(f64::from(f32::from_le_bytes(quad(bytes))), true),
            0x0D => Constant::Float(f64::from_le_bytes(octet(bytes)), false),
            0x0E => {
                let units: Vec<u16> = bytes
                    .chunks_exact(2)
                    .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
                    .collect();
                Constant::Str(String::from_utf16_lossy(&units))
            }
            0x12 => Constant::Null,
            _ => return None,
        })
    }

    /// The names of the custom attributes on a row, as the attribute's type
    /// spells them.
    #[must_use]
    pub fn attribute_names(&self, parent: Token) -> Vec<String> {
        let Some(tag) = tables::HAS_CUSTOM_ATTRIBUTE
            .tables
            .iter()
            .position(|table| *table == parent.table())
        else {
            return Vec::new();
        };
        let wanted = (parent.row() << 5) | tag as u32;
        let Some(rows) = self.index.attributes.get(&wanted) else {
            return Vec::new();
        };
        let attributes = self.assembly.table(table::CUSTOM_ATTRIBUTE);
        rows.iter()
            .filter_map(|row| attributes.row(*row))
            .filter_map(|row| {
                let ctor = row.token(1);
                let declaring = match ctor.table() {
                    table::METHOD_DEF => {
                        Token::new(table::TYPE_DEF, self.method_owner(ctor.row())?)
                    }
                    table::MEMBER_REF => self.assembly.row(ctor)?.token(0),
                    _ => return None,
                };
                self.raw_name(declaring)
            })
            .collect()
    }

    /// The custom attributes on a row as `(attribute type name, constructor,
    /// blob)`.
    #[must_use]
    pub fn attribute_rows(&self, parent: Token) -> Vec<(String, Token, &'a [u8])> {
        let Some(tag) = tables::HAS_CUSTOM_ATTRIBUTE
            .tables
            .iter()
            .position(|table| *table == parent.table())
        else {
            return Vec::new();
        };
        let wanted = (parent.row() << 5) | tag as u32;
        let Some(rows) = self.index.attributes.get(&wanted) else {
            return Vec::new();
        };
        let attributes = self.assembly.table(table::CUSTOM_ATTRIBUTE);
        rows.iter()
            .filter_map(|row| attributes.row(*row))
            .filter_map(|row| {
                let ctor = row.token(1);
                let declaring = match ctor.table() {
                    table::METHOD_DEF => {
                        Token::new(table::TYPE_DEF, self.method_owner(ctor.row())?)
                    }
                    table::MEMBER_REF => self.assembly.row(ctor)?.token(0),
                    _ => return None,
                };
                let blob = self.assembly.heaps().blob(row.number(2)).ok()?;
                Some((self.raw_name(declaring)?, ctor, blob))
            })
            .collect()
    }

    /// The element names a `TupleElementNamesAttribute` gives the tuples in
    /// a signature, in the order the tuples are met.
    #[must_use]
    pub fn tuple_names(&self, parent: Token) -> Option<Vec<Option<String>>> {
        let (_, _, blob) = self
            .attribute_rows(parent)
            .into_iter()
            .find(|(name, _, _)| {
                name == "System.Runtime.CompilerServices.TupleElementNamesAttribute"
            })?;
        let mut reader = AttributeBlob::new(blob);
        reader.prolog()?;
        reader.string_array()
    }

    /// The `NullableAttribute` flags on a row: one byte per type in the
    /// signature, or one for all of them.
    #[must_use]
    pub fn nullable_flags(&self, parent: Token) -> Option<Vec<u8>> {
        let (_, ctor, blob) = self
            .attribute_rows(parent)
            .into_iter()
            .find(|(name, _, _)| name == "System.Runtime.CompilerServices.NullableAttribute")?;
        let mut reader = AttributeBlob::new(blob);
        reader.prolog()?;
        let takes_array = match ctor.table() {
            table::METHOD_DEF => self.method_ref(ctor).is_some_and(|method| {
                matches!(method.sig.parameters.first(), Some(TypeSig::Vector(_)))
            }),
            table::MEMBER_REF => self.method_ref(ctor).is_some_and(|method| {
                matches!(method.sig.parameters.first(), Some(TypeSig::Vector(_)))
            }),
            _ => false,
        };
        if takes_array {
            reader.byte_array()
        } else {
            reader.byte().map(|flag| vec![flag])
        }
    }

    /// The `NullableContextAttribute` value on a row, if any.
    #[must_use]
    pub fn nullable_context(&self, parent: Token) -> Option<u8> {
        let (_, _, blob) = self
            .attribute_rows(parent)
            .into_iter()
            .find(|(name, _, _)| {
                name == "System.Runtime.CompilerServices.NullableContextAttribute"
            })?;
        let mut reader = AttributeBlob::new(blob);
        reader.prolog()?;
        reader.byte()
    }

    /// Whether a row carries an attribute of the given full name.
    #[must_use]
    pub fn has_attribute(&self, parent: Token, name: &str) -> bool {
        self.attribute_names(parent)
            .iter()
            .any(|found| found == name)
    }

    /// The `MethodSemantics` rows binding accessors to a property or event:
    /// `(semantics flags, method row)`.
    #[must_use]
    pub fn semantics_of(&self, parent: Token) -> Vec<(u16, u32)> {
        let tag = match parent.table() {
            table::EVENT => 0,
            table::PROPERTY => 1,
            _ => return Vec::new(),
        };
        let wanted = (parent.row() << 1) | tag;
        self.index
            .semantics_by_parent
            .get(&wanted)
            .cloned()
            .unwrap_or_default()
    }

    /// Which property or event a method is an accessor of, with the role.
    #[must_use]
    pub fn accessor_role(&self, method_row: u32) -> Option<(Token, u16)> {
        self.index.semantics_by_method.get(&method_row).copied()
    }

    /// The text of a `ldstr` token.
    #[must_use]
    pub fn user_string(&self, token: Token) -> Option<String> {
        self.assembly.heaps().user_string(token.row()).ok()
    }
}

/// The annotations a signature carries beside its types: the names of its
/// tuples' elements and which of its reference types may be null.
#[derive(Clone, Debug, Default)]
pub struct Annotations {
    /// Tuple element names still to be handed out, in order.
    pub tuple_names: std::collections::VecDeque<Option<String>>,
    /// `NullableAttribute` bytes still to be consumed, one per type.
    pub nullable: std::collections::VecDeque<u8>,
    /// The `NullableContext` value that stands in for a missing byte.
    pub context: u8,
}

impl Annotations {
    /// The flag for the next type in pre-order.
    fn next_nullable(&mut self) -> u8 {
        match self.nullable.len() {
            0 => self.context,
            // A single byte covers every type.
            1 => self.nullable[0],
            _ => self.nullable.pop_front().unwrap_or(self.context),
        }
    }
}

/// Reads the fixed arguments of a custom attribute blob.
#[derive(Debug)]
struct AttributeBlob<'b> {
    bytes: &'b [u8],
    at: usize,
}

impl<'b> AttributeBlob<'b> {
    const fn new(bytes: &'b [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn prolog(&mut self) -> Option<()> {
        (self.u16()? == 1).then_some(())
    }

    fn byte(&mut self) -> Option<u8> {
        let byte = *self.bytes.get(self.at)?;
        self.at += 1;
        Some(byte)
    }

    fn u16(&mut self) -> Option<u16> {
        let slice = self.bytes.get(self.at..self.at + 2)?;
        self.at += 2;
        Some(u16::from_le_bytes([slice[0], slice[1]]))
    }

    fn u32(&mut self) -> Option<u32> {
        let slice = self.bytes.get(self.at..self.at + 4)?;
        self.at += 4;
        Some(u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
    }

    /// A `SerString`: a compressed length and UTF-8, or `0xFF` for null.
    fn string(&mut self) -> Option<Option<String>> {
        let first = *self.bytes.get(self.at)?;
        if first == 0xFF {
            self.at += 1;
            return Some(None);
        }
        let mut blob = Blob::new(&self.bytes[self.at..]);
        let length = blob.unsigned().ok()? as usize;
        let start = self.at + blob.position();
        let text = self.bytes.get(start..start + length)?;
        self.at = start + length;
        Some(Some(String::from_utf8_lossy(text).into_owned()))
    }

    fn string_array(&mut self) -> Option<Vec<Option<String>>> {
        let count = self.u32()?;
        if count == u32::MAX {
            return None;
        }
        let mut out = Vec::with_capacity(count as usize);
        for _ in 0..count {
            out.push(self.string()?);
        }
        Some(out)
    }

    fn byte_array(&mut self) -> Option<Vec<u8>> {
        let count = self.u32()?;
        if count == u32::MAX {
            return None;
        }
        let slice = self.bytes.get(self.at..self.at + count as usize)?;
        self.at += count as usize;
        Some(slice.to_vec())
    }
}

/// One argument of a custom attribute, as its blob stores it.
#[derive(Clone, PartialEq, Debug)]
pub enum AttributeValue {
    Bool(bool),
    Char(u16),
    Int(i64),
    UInt(u64),
    Float(f64, bool),
    Str(Option<String>),
    /// A `System.Type`, by its serialized name.
    Type(Option<String>),
    /// An enum value, and the enum's type when the signature says it.
    Enum(Option<TypeSig>, Option<String>, i64),
    Array(Option<Vec<AttributeValue>>),
}

/// A custom attribute's constructor arguments, then its named ones.
pub type AttributeArguments = (Vec<AttributeValue>, Vec<(String, AttributeValue)>);

/// The type a named argument or boxed value says it has.
enum Serialized {
    Primitive(TypeSig),
    Type,
    Boxed,
    Enum(String),
    Array(Box<Serialized>),
}

impl AttributeBlob<'_> {
    fn bytes_le<const N: usize>(&mut self) -> Option<[u8; N]> {
        let slice = self.bytes.get(self.at..self.at + N)?;
        self.at += N;
        let mut out = [0u8; N];
        out.copy_from_slice(slice);
        Some(out)
    }

    fn serialized_type(&mut self) -> Option<Serialized> {
        Some(match self.byte()? {
            0x02 => Serialized::Primitive(TypeSig::Boolean),
            0x03 => Serialized::Primitive(TypeSig::Char),
            0x04 => Serialized::Primitive(TypeSig::SByte),
            0x05 => Serialized::Primitive(TypeSig::Byte),
            0x06 => Serialized::Primitive(TypeSig::Int16),
            0x07 => Serialized::Primitive(TypeSig::UInt16),
            0x08 => Serialized::Primitive(TypeSig::Int32),
            0x09 => Serialized::Primitive(TypeSig::UInt32),
            0x0A => Serialized::Primitive(TypeSig::Int64),
            0x0B => Serialized::Primitive(TypeSig::UInt64),
            0x0C => Serialized::Primitive(TypeSig::Single),
            0x0D => Serialized::Primitive(TypeSig::Double),
            0x0E => Serialized::Primitive(TypeSig::String),
            0x50 => Serialized::Type,
            0x51 => Serialized::Boxed,
            0x55 => Serialized::Enum(self.string()??),
            0x1D => Serialized::Array(Box::new(self.serialized_type()?)),
            _ => return None,
        })
    }

    fn primitive(&mut self, ty: &TypeSig) -> Option<AttributeValue> {
        Some(match ty {
            TypeSig::Boolean => AttributeValue::Bool(self.byte()? != 0),
            TypeSig::Char => AttributeValue::Char(self.u16()?),
            TypeSig::SByte => AttributeValue::Int(i64::from(self.byte()? as i8)),
            TypeSig::Byte => AttributeValue::Int(i64::from(self.byte()?)),
            TypeSig::Int16 => AttributeValue::Int(i64::from(i16::from_le_bytes(self.bytes_le()?))),
            TypeSig::UInt16 => AttributeValue::Int(i64::from(self.u16()?)),
            TypeSig::Int32 => AttributeValue::Int(i64::from(i32::from_le_bytes(self.bytes_le()?))),
            TypeSig::UInt32 => AttributeValue::Int(i64::from(self.u32()?)),
            TypeSig::Int64 => AttributeValue::Int(i64::from_le_bytes(self.bytes_le()?)),
            TypeSig::UInt64 => AttributeValue::UInt(u64::from_le_bytes(self.bytes_le()?)),
            TypeSig::Single => {
                AttributeValue::Float(f64::from(f32::from_le_bytes(self.bytes_le()?)), true)
            }
            TypeSig::Double => AttributeValue::Float(f64::from_le_bytes(self.bytes_le()?), false),
            TypeSig::String => AttributeValue::Str(self.string()?),
            _ => return None,
        })
    }

    /// An integer of the width of an enum's underlying type.
    fn enum_value(&mut self, underlying: &TypeSig) -> Option<i64> {
        match self.primitive(underlying)? {
            AttributeValue::Int(value) => Some(value),
            AttributeValue::UInt(value) => Some(value as i64),
            _ => None,
        }
    }
}

impl<'a> Resolver<'a> {
    /// The integer type an enum is stored as, when the enum can be found.
    #[must_use]
    pub fn enum_underlying(&self, sig: &TypeSig) -> Option<TypeSig> {
        // An enum nested in a generic type has its arguments.
        let sig = match sig {
            TypeSig::Generic { definition, .. } => definition.as_ref(),
            other => other,
        };
        let (TypeSig::ValueType(token) | TypeSig::Class(token)) = sig else {
            return None;
        };
        let token = *token;
        if token.table() == table::TYPE_REF {
            let (there, row) = self.resolve_type_ref(token)?;
            return there.enum_underlying(&TypeSig::ValueType(Token::new(table::TYPE_DEF, row)));
        }
        if token.table() != table::TYPE_DEF {
            return None;
        }
        let found = self.assembly.row(token)?;
        if self.raw_name(found.token(3)).as_deref() != Some("System.Enum") {
            return None;
        }
        let heaps = self.assembly.heaps();
        self.fields_of(token.row())
            .into_iter()
            .find(|(_, field)| field.number(0) & 0x0010 == 0)
            .and_then(|(_, field)| heaps.blob(field.number(2)).ok())
            .and_then(|bytes| Blob::new(bytes).field_sig().ok())
    }

    /// A type of this assembly or a referenced one by its serialized name,
    /// `Ns.Outer+Inner, Assembly, ...`.
    #[must_use]
    pub fn type_by_serialized_name(&self, name: &str) -> Option<TypeSig> {
        let wanted = name.split(',').next()?.trim().replace('+', "/");
        for table_id in [table::TYPE_DEF, table::TYPE_REF] {
            for row in 1..=self.assembly.rows(table_id) {
                let token = Token::new(table_id, row);
                if self.raw_name(token).as_deref() == Some(wanted.as_str()) {
                    return Some(TypeSig::ValueType(token));
                }
            }
        }
        None
    }

    /// The arguments of a custom attribute: the constructor's, then the
    /// named fields and properties.
    #[must_use]
    pub fn attribute_arguments(&self, ctor: Token, blob: &[u8]) -> Option<AttributeArguments> {
        let method = self.method_ref(ctor)?;
        let mut reader = AttributeBlob::new(blob);
        reader.prolog()?;
        let mut fixed = Vec::new();
        for param in &method.sig.parameters {
            fixed.push(self.fixed_argument(&mut reader, param)?);
        }
        let count = reader.u16()?;
        let mut named = Vec::new();
        for _ in 0..count {
            let kind = reader.byte()?;
            if kind != 0x53 && kind != 0x54 {
                return None;
            }
            let ty = reader.serialized_type()?;
            let name = reader.string()??;
            named.push((name, self.serialized_argument(&mut reader, &ty)?));
        }
        Some((fixed, named))
    }

    fn fixed_argument(
        &self,
        reader: &mut AttributeBlob<'_>,
        ty: &TypeSig,
    ) -> Option<AttributeValue> {
        match ty {
            TypeSig::Object => {
                let ty = reader.serialized_type()?;
                self.serialized_argument(reader, &ty)
            }
            TypeSig::Vector(element) => {
                let count = reader.u32()?;
                if count == u32::MAX {
                    return Some(AttributeValue::Array(None));
                }
                let mut items = Vec::new();
                for _ in 0..count {
                    items.push(self.fixed_argument(reader, element)?);
                }
                Some(AttributeValue::Array(Some(items)))
            }
            TypeSig::Class(token) | TypeSig::ValueType(token)
                if self.raw_name(*token).as_deref() == Some("System.Type") =>
            {
                Some(AttributeValue::Type(reader.string()?))
            }
            TypeSig::Class(_) | TypeSig::ValueType(_) => {
                let underlying = self.enum_underlying(ty).unwrap_or(TypeSig::Int32);
                let value = reader.enum_value(&underlying)?;
                Some(AttributeValue::Enum(Some(ty.clone()), None, value))
            }
            other => reader.primitive(other),
        }
    }

    fn serialized_argument(
        &self,
        reader: &mut AttributeBlob<'_>,
        ty: &Serialized,
    ) -> Option<AttributeValue> {
        match ty {
            Serialized::Primitive(ty) => reader.primitive(ty),
            Serialized::Type => Some(AttributeValue::Type(reader.string()?)),
            Serialized::Boxed => {
                let ty = reader.serialized_type()?;
                self.serialized_argument(reader, &ty)
            }
            Serialized::Enum(name) => {
                let found = self.type_by_serialized_name(name);
                let underlying = found
                    .as_ref()
                    .and_then(|found| self.enum_underlying(found))
                    .unwrap_or(TypeSig::Int32);
                let value = reader.enum_value(&underlying)?;
                Some(AttributeValue::Enum(found, Some(name.clone()), value))
            }
            Serialized::Array(element) => {
                let count = reader.u32()?;
                if count == u32::MAX {
                    return Some(AttributeValue::Array(None));
                }
                let mut items = Vec::new();
                for _ in 0..count {
                    items.push(self.serialized_argument(reader, element)?);
                }
                Some(AttributeValue::Array(Some(items)))
            }
        }
    }
}

/// A compile-time constant out of the `Constant` table.
#[derive(Clone, PartialEq, Debug)]
pub enum Constant {
    Bool(bool),
    Char(u16),
    Int(i64),
    Float(f64, bool),
    Str(String),
    Null,
}

fn pair(bytes: &[u8]) -> [u8; 2] {
    [
        bytes.first().copied().unwrap_or(0),
        bytes.get(1).copied().unwrap_or(0),
    ]
}

fn quad(bytes: &[u8]) -> [u8; 4] {
    let mut out = [0u8; 4];
    for (slot, byte) in out.iter_mut().zip(bytes) {
        *slot = *byte;
    }
    out
}

fn octet(bytes: &[u8]) -> [u8; 8] {
    let mut out = [0u8; 8];
    for (slot, byte) in out.iter_mut().zip(bytes) {
        *slot = *byte;
    }
    out
}

/// `Namespace.Name`, or the name alone outside any namespace.
#[must_use]
pub fn qualified(namespace: &str, name: &str) -> String {
    if namespace.is_empty() {
        name.to_string()
    } else {
        format!("{namespace}.{name}")
    }
}

/// `List` out of `` List`1 ``.
#[must_use]
pub fn strip_arity(name: &str) -> &str {
    let name = file_local_name(name).unwrap_or(name);
    name.rsplit_once('`')
        .filter(|(_, n)| n.chars().all(|c| c.is_ascii_digit()))
        .map_or(name, |(name, _)| name)
}

/// The name a `file` type was given: `<Source_g>F1A2B...__Name` is `Name`.
fn file_local_name(name: &str) -> Option<&str> {
    let rest = name.strip_prefix('<')?;
    let (_, after) = rest.split_once('>')?;
    let hashed = after.strip_prefix('F')?;
    let (hash, own) = hashed.split_once("__")?;
    (hash.len() >= 8 && hash.chars().all(|c| c.is_ascii_hexdigit()) && !own.is_empty())
        .then_some(own)
}

/// The framework name of a primitive type.
fn primitive_name(ty: &TypeSig) -> Option<&'static str> {
    Some(match ty {
        TypeSig::Boolean => "System.Boolean",
        TypeSig::Char => "System.Char",
        TypeSig::SByte => "System.SByte",
        TypeSig::Byte => "System.Byte",
        TypeSig::Int16 => "System.Int16",
        TypeSig::UInt16 => "System.UInt16",
        TypeSig::Int32 => "System.Int32",
        TypeSig::UInt32 => "System.UInt32",
        TypeSig::Int64 => "System.Int64",
        TypeSig::UInt64 => "System.UInt64",
        TypeSig::Single => "System.Single",
        TypeSig::Double => "System.Double",
        TypeSig::String => "System.String",
        TypeSig::Object => "System.Object",
        TypeSig::IntPtr => "System.IntPtr",
        TypeSig::UIntPtr => "System.UIntPtr",
        _ => return None,
    })
}

/// The primitive a framework type name stands for, when it is one.
fn primitive_of(raw: &str) -> Option<TypeSig> {
    Some(match raw {
        "System.Void" => TypeSig::Void,
        "System.Boolean" => TypeSig::Boolean,
        "System.Char" => TypeSig::Char,
        "System.SByte" => TypeSig::SByte,
        "System.Byte" => TypeSig::Byte,
        "System.Int16" => TypeSig::Int16,
        "System.UInt16" => TypeSig::UInt16,
        "System.Int32" => TypeSig::Int32,
        "System.UInt32" => TypeSig::UInt32,
        "System.Int64" => TypeSig::Int64,
        "System.UInt64" => TypeSig::UInt64,
        "System.Single" => TypeSig::Single,
        "System.Double" => TypeSig::Double,
        "System.String" => TypeSig::String,
        "System.Object" => TypeSig::Object,
        "System.IntPtr" => TypeSig::IntPtr,
        "System.UIntPtr" => TypeSig::UIntPtr,
        _ => return None,
    })
}

/// Whether a framework type of this raw name is a struct.
fn is_well_known_struct(raw: &str) -> bool {
    if raw.ends_with("/Enumerator") {
        return true;
    }
    let (namespace, name) = raw.rsplit_once('.').unwrap_or(("", raw));
    match namespace {
        "System" => matches!(
            name,
            "Boolean"
                | "Byte"
                | "SByte"
                | "Char"
                | "Int16"
                | "UInt16"
                | "Int32"
                | "UInt32"
                | "Int64"
                | "UInt64"
                | "Single"
                | "Double"
                | "Decimal"
                | "IntPtr"
                | "UIntPtr"
                | "DateTime"
                | "DateTimeOffset"
                | "TimeSpan"
                | "Guid"
                | "Nullable`1"
                | "ValueTuple"
                | "ValueTuple`1"
                | "ValueTuple`2"
                | "ValueTuple`3"
                | "ValueTuple`4"
                | "ValueTuple`5"
                | "ValueTuple`6"
                | "ValueTuple`7"
                | "ValueTuple`8"
                | "ArraySegment`1"
                | "Span`1"
                | "ReadOnlySpan`1"
                | "Memory`1"
                | "ReadOnlyMemory`1"
                | "Index"
                | "Range"
                | "RuntimeTypeHandle"
                | "RuntimeMethodHandle"
                | "RuntimeFieldHandle"
                | "TypedReference"
                | "Void"
                | "Enum"
                | "ValueType"
        ),
        "System.Collections.Generic" => matches!(name, "KeyValuePair`2"),
        "System.Threading" => matches!(name, "CancellationToken" | "SpinLock"),
        "System.Threading.Tasks" => matches!(name, "ValueTask" | "ValueTask`1"),
        "System.Runtime.CompilerServices" => matches!(
            name,
            "TaskAwaiter"
                | "TaskAwaiter`1"
                | "ValueTaskAwaiter"
                | "ValueTaskAwaiter`1"
                | "ConfiguredTaskAwaitable"
                | "ConfiguredTaskAwaitable`1"
                | "ConfiguredTaskAwaitable/ConfiguredTaskAwaiter"
                | "ConfiguredTaskAwaitable`1/ConfiguredTaskAwaiter"
                | "AsyncTaskMethodBuilder"
                | "AsyncTaskMethodBuilder`1"
                | "AsyncVoidMethodBuilder"
                | "AsyncValueTaskMethodBuilder"
                | "AsyncValueTaskMethodBuilder`1"
                | "DefaultInterpolatedStringHandler"
                | "YieldAwaitable"
                | "YieldAwaitable/YieldAwaiter"
        ),
        _ => false,
    }
}

/// Whether a signature type mentions a method type parameter by position.
fn mentions_mvar(ty: &TypeSig, at: u32) -> bool {
    match ty {
        TypeSig::MVar(found) => *found == at,
        TypeSig::Vector(inner) | TypeSig::Pointer(inner) | TypeSig::ByRef(inner) => {
            mentions_mvar(inner, at)
        }
        TypeSig::Array { element, .. } => mentions_mvar(element, at),
        TypeSig::Generic { arguments, .. } => {
            arguments.iter().any(|argument| mentions_mvar(argument, at))
        }
        _ => false,
    }
}

/// A compiler-generated name made into one C# accepts, for members that
/// are left as they are: `<M>g__F|0_1` is `_M_g__F_0_1`. Qualified names
/// (explicit implementations) are written their own way, and left alone.
#[must_use]
pub fn identifier(name: &str) -> std::borrow::Cow<'_, str> {
    if name.contains('.') || name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return std::borrow::Cow::Borrowed(name);
    }
    let mut out: String = name
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    std::borrow::Cow::Owned(out)
}
