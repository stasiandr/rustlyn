//! A compilation written to bytes and read back.
//!
//! Declaring a large project takes seconds, and an editor opening the project
//! it had open yesterday would spend them producing what it had yesterday.
//! This writes out what declaring produced — the symbol table, what each
//! declaration node declared, what came out of the referenced assemblies —
//! and the text of every file, and reads it back into a compilation that
//! answers the same questions. The trees are not written: they come back
//! unparsed, and are parsed from the stored text the first time something
//! asks for one ([`Trees`]).
//!
//! What is not kept is what is cheaper to work out again than to store: the
//! special types, the extension-method index, the declaration nodes by
//! symbol. What is not kept at all is the diagnostics, which an editor does
//! not ask a compilation read from disk for; a build compiles afresh.
//!
//! The format is private to one build: it is read only by the code that
//! wrote it, so it carries a version and nothing is done to keep old
//! versions readable. A snapshot that does not read is simply not used.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, RwLock};

use rustlyn_syntax::ParseOptions;
use rustlyn_text::{SourceText, TextSpan};

use crate::bound::{ConstantValue, SpecialConstant};
use crate::compilation::Compilation;
use crate::corlib::SpecialType;
use crate::fxhash::FxHashMap;
use crate::metadata::{ComDefault, Loaded, Reference};
use crate::symbol::{
    Accessibility, CallerInfo, Detail, Event, Field, Local, Location, Method, MethodKind,
    Modifiers, NamedType, Parameter, Property, RefKind, Symbol, SymbolId, SymbolKind, Symbols,
    SynthesizedType, TypeKind, TypeParameter, TypeSyntaxRef, Variance,
};
use crate::trees::Trees;
use crate::types::{TupleElement, Type};

/// Changes whenever the layout below does.
const FORMAT: u32 = 26;
const MAGIC: &[u8; 8] = b"RLNCOMP\0";

impl Compilation {
    /// The compilation as bytes, for [`Compilation::read_snapshot`].
    #[must_use]
    pub fn write_snapshot(&self) -> Vec<u8> {
        let mut out = Writer::default();
        out.bytes.extend_from_slice(MAGIC);
        out.u32(FORMAT);

        // The files, with the preprocessor symbols each was parsed under.
        let trees = self.trees();
        let mut option_sets: Vec<Vec<String>> = Vec::new();
        let mut option_index: Vec<usize> = Vec::with_capacity(trees.len());
        for index in 0..trees.len() {
            let defined = trees.defined(index).to_vec();
            let at = option_sets
                .iter()
                .position(|set| *set == defined)
                .unwrap_or_else(|| {
                    option_sets.push(defined);
                    option_sets.len() - 1
                });
            option_index.push(at);
        }
        out.usize(option_sets.len());
        for set in &option_sets {
            out.strings(set);
        }
        out.usize(trees.len());
        for (index, options) in option_index.iter().enumerate() {
            let source = trees.source(index).expect("every tree has a source");
            out.str(source.name());
            out.str(source.text());
            out.usize(*options);
        }
        out.usize(self.corlib_trees);
        out.usizes(&self.global_using_trees);

        // The symbols, and the name index exactly as it was built: its order
        // is the order lookups return overloads in.
        let symbols = &self.symbols;
        out.usize(symbols.symbols.len());
        for symbol in &symbols.symbols {
            write_symbol(&mut out, symbol);
        }
        let mut containers: Vec<_> = symbols.index.iter().collect();
        containers.sort_by_key(|(container, _)| container.0);
        out.usize(containers.len());
        for (container, names) in containers {
            out.id(*container);
            let mut names: Vec<_> = names.iter().collect();
            names.sort_by(|a, b| a.0.cmp(b.0));
            out.usize(names.len());
            for (name, ids) in names {
                out.str(name);
                out.ids(ids);
            }
        }
        out.id(self.global);
        out.usize(self.metadata_floor);

        let mut declarations: Vec<_> = self.declarations.iter().collect();
        declarations.sort_by_key(|((tree, span), _)| (*tree, span.start(), span.length()));
        out.usize(declarations.len());
        for ((tree, span), symbol) in declarations {
            out.usize(*tree);
            out.span(*span);
            out.id(*symbol);
        }
        let mut anonymous: Vec<_> = self.anonymous_types.iter().collect();
        anonymous.sort_by_key(|(_, symbol)| symbol.0);
        out.usize(anonymous.len());
        for (names, symbol) in anonymous {
            out.strings(names);
            out.id(*symbol);
        }

        write_loaded(&mut out, &self.loaded);
        out.usize(self.tree_assemblies.len());
        for assembly in &self.tree_assemblies {
            out.u32(u32::from(*assembly));
        }
        for lists in [&self.assembly_references, &self.source_friends] {
            out.usize(lists.len());
            for list in lists {
                out.usize(list.len());
                for index in list {
                    out.u32(u32::from(*index));
                }
            }
        }
        out.usize(self.metadata_references.len());
        for names in &self.metadata_references {
            out.strings(names);
        }
        out.usize(self.assembly_nullable.len());
        for enabled in &self.assembly_nullable {
            out.u8(u8::from(*enabled));
        }
        let mut also: Vec<_> = self.tree_assemblies_also.iter().collect();
        also.sort();
        out.usize(also.len());
        for (tree, assemblies) in also {
            out.usize(*tree);
            out.usize(assemblies.len());
            for assembly in assemblies {
                out.u32(u32::from(*assembly));
            }
        }
        out.bytes
    }

    /// A compilation read back from [`Compilation::write_snapshot`], or
    /// `None` when the bytes are from another version or are damaged.
    #[must_use]
    pub fn read_snapshot(bytes: &[u8]) -> Option<Self> {
        let mut input = Reader { bytes, at: 0 };
        if input.take(MAGIC.len())? != MAGIC || input.u32()? != FORMAT {
            return None;
        }

        let option_sets: Vec<Arc<ParseOptions>> = (0..input.usize()?)
            .map(|_| Some(Arc::new(ParseOptions::with_symbols(input.strings()?))))
            .collect::<Option<_>>()?;
        let tree_count = input.usize()?;
        let mut sources = Vec::with_capacity(tree_count);
        for _ in 0..tree_count {
            let name = input.string()?;
            let text = input.string()?;
            let options = option_sets.get(input.usize()?)?.clone();
            sources.push((SourceText::new(name, text), options));
        }
        let corlib_trees = input.usize()?;
        let global_using_trees = input.usizes()?;

        let symbol_count = input.usize()?;
        let mut list = Vec::with_capacity(symbol_count);
        for id in 0..symbol_count {
            let mut symbol = read_symbol(&mut input)?;
            symbol.id = SymbolId(u32::try_from(id).ok()?);
            list.push(symbol);
        }
        let mut index: FxHashMap<SymbolId, FxHashMap<String, Vec<SymbolId>>> = FxHashMap::default();
        for _ in 0..input.usize()? {
            let container = input.id()?;
            let mut names = FxHashMap::default();
            for _ in 0..input.usize()? {
                let name = input.string()?;
                names.insert(name, input.ids()?);
            }
            index.insert(container, names);
        }
        let symbols = Symbols::from_parts(list, index);
        let global = input.id()?;
        let metadata_floor = input.usize()?;

        let mut declarations = HashMap::new();
        for _ in 0..input.usize()? {
            let tree = input.usize()?;
            let span = input.span()?;
            declarations.insert((tree, span), input.id()?);
        }
        let mut anonymous_types = HashMap::new();
        for _ in 0..input.usize()? {
            let names = input.strings()?;
            anonymous_types.insert(names, input.id()?);
        }
        let loaded = read_loaded(&mut input)?;
        let tree_assemblies = (0..input.usize()?)
            .map(|_| u16::try_from(input.u32()?).ok())
            .collect::<Option<Vec<u16>>>()?;
        let lists = |input: &mut Reader<'_>| {
            (0..input.usize()?)
                .map(|_| {
                    (0..input.usize()?)
                        .map(|_| u16::try_from(input.u32()?).ok())
                        .collect::<Option<Vec<u16>>>()
                })
                .collect::<Option<Vec<Vec<u16>>>>()
        };
        let assembly_references = lists(&mut input)?;
        let source_friends = lists(&mut input)?;
        let metadata_references = (0..input.usize()?)
            .map(|_| input.strings())
            .collect::<Option<Vec<Vec<String>>>>()?;
        let assembly_nullable = (0..input.usize()?)
            .map(|_| Some(input.u8()? != 0))
            .collect::<Option<Vec<bool>>>()?;
        let mut tree_assemblies_also = HashMap::new();
        for _ in 0..input.usize()? {
            let tree = input.usize()?;
            let also = (0..input.usize()?)
                .map(|_| u16::try_from(input.u32()?).ok())
                .collect::<Option<Vec<u16>>>()?;
            tree_assemblies_also.insert(tree, also);
        }
        if input.at != bytes.len() || symbols.symbols.len() <= global.index() {
            return None;
        }

        let mut compilation = Self {
            trees: Trees::unparsed(sources),
            global_using_trees,
            symbols,
            global,
            diagnostics: Vec::new(),
            special_types: Default::default(),
            well_known: Default::default(),
            declarations,
            declaration_nodes: HashMap::new(),
            anonymous_types,
            corlib_trees,
            loaded,
            metadata_floor,
            base_types: crate::compilation::SymbolCache::new(metadata_floor),
            resolving: Mutex::new(HashSet::new()),
            extensions: HashMap::new(),
            extension_members: HashMap::new(),
            conversions: RwLock::new(HashMap::new()),
            constants: RwLock::new(HashMap::new()),
            circular_constants: RwLock::new(std::collections::BTreeSet::new()),
            imports: RwLock::new(HashMap::new()),
            global_imports: RwLock::new(None),
            obsolete: std::sync::OnceLock::new(),
            anonymous_delegates: Mutex::new(crate::delegates::AnonymousDelegates::default()),
            options: crate::compilation::CompilationOptions::default(),
            priorities: std::sync::OnceLock::new(),
            assembly_references,
            namespaces_seen: RwLock::new(HashMap::new()),
            source_friends,
            metadata_references,
            assembly_nullable,
            tree_assemblies_also,
            tree_assemblies,
            metadata_names: RwLock::new(HashMap::new()),
            inheritance: RwLock::new(HashMap::new()),
            implicit_conversions: RwLock::new(HashMap::new()),
            symbol_types: crate::compilation::SymbolCache::new(metadata_floor),
        };
        compilation.derive_indexes();
        Some(compilation)
    }
}

// MARK: - symbols

fn write_symbol(out: &mut Writer, symbol: &Symbol) {
    out.u8(symbol_kind(symbol.kind));
    out.str(&symbol.name);
    out.option_id(symbol.container);
    out.ids(&symbol.members);
    out.usize(symbol.locations.len());
    for location in &symbol.locations {
        out.location(*location);
    }
    out.u8(accessibility(symbol.accessibility));
    out.u32(symbol.modifiers.bits());
    match &symbol.detail {
        Detail::Namespace => out.u8(0),
        Detail::NamedType(detail) => {
            out.u8(1);
            out.u8(detail.type_kind.map_or(0, |kind| type_kind(kind) + 1));
            out.usize(detail.arity);
            out.ids(&detail.type_parameters);
            out.usize(detail.base_types.len());
            for base in &detail.base_types {
                out.location(base.0);
            }
            out.option_type_ref(detail.enum_underlying);
            out.bool(detail.ref_like);
            out.option_id(detail.primary_constructor);
            out.bool(detail.anonymous);
            out.bool(detail.union_declaration);
            out.bool(detail.union_attribute);
            out.bool(detail.interpolated_string_handler);
        }
        Detail::Method(detail) => {
            out.u8(2);
            out.option_type_ref(detail.return_type);
            out.option_synthesized(detail.synthesized_return);
            out.ids(&detail.parameters);
            out.ids(&detail.type_parameters);
            out.usize(detail.arity);
            out.u8(method_kind(detail.method_kind));
            out.bool(detail.is_extension);
            out.bool(detail.returns_readonly);
            out.option_type_ref(detail.extended);
            out.bool(detail.is_vararg);
        }
        Detail::Field(detail) => {
            out.u8(3);
            out.option_type_ref(detail.ty);
            out.bool(detail.has_initializer);
        }
        Detail::Property(detail) => {
            out.u8(4);
            out.option_type_ref(detail.ty);
            out.option_synthesized(detail.synthesized);
            out.ids(&detail.parameters);
            out.bool(detail.has_get);
            out.bool(detail.has_set);
            out.bool(detail.has_init);
            out.option_id(detail.backing_field);
            out.bool(detail.is_indexer);
            out.bool(detail.returns_readonly);
            out.option_id(detail.getter);
            out.option_id(detail.setter);
            out.u8(option_accessibility(detail.get_accessibility));
            out.u8(option_accessibility(detail.set_accessibility));
            out.option_type_ref(detail.extended);
            out.ids(&detail.extension_generics);
        }
        Detail::Event(detail) => {
            out.u8(5);
            out.option_type_ref(detail.ty);
            out.option_id(detail.adder);
            out.option_id(detail.remover);
        }
        Detail::Parameter(detail) => {
            out.u8(6);
            out.option_type_ref(detail.ty);
            out.option_synthesized(detail.synthesized);
            out.u8(ref_kind(detail.ref_kind));
            out.bool(detail.ref_readonly);
            out.bool(detail.unscoped_ref);
            out.bool(detail.is_params);
            out.bool(detail.has_default);
            out.bool(detail.enumerator_cancellation);
            match &detail.caller_info {
                None => out.u8(0),
                Some(CallerInfo::MemberName) => out.u8(1),
                Some(CallerInfo::LineNumber) => out.u8(2),
                Some(CallerInfo::FilePath) => out.u8(3),
                Some(CallerInfo::ArgumentExpression(name)) => {
                    out.u8(4);
                    out.str(name);
                }
                Some(CallerInfo::ArgumentConstant(name)) => {
                    out.u8(5);
                    out.str(name);
                }
            }
            out.option_id(detail.captured);
            out.strings(detail.declared_name.as_slice());
            out.bool(detail.handler_arguments.is_some());
            out.strings(detail.handler_arguments.as_deref().unwrap_or_default());
        }
        Detail::TypeParameter(detail) => {
            out.u8(7);
            out.usize(detail.constraints.len());
            for constraint in &detail.constraints {
                out.location(constraint.0);
            }
            out.bool(detail.value_type);
            out.bool(detail.reference_type);
            out.bool(detail.constructor);
            out.bool(detail.allows_ref_struct);
            out.bool(detail.unmanaged);
            out.u8(match detail.variance {
                Variance::None => 0,
                Variance::Out => 1,
                Variance::In => 2,
            });
            out.strings(detail.declared_name.as_slice());
        }
        Detail::Local(detail) => {
            out.u8(8);
            out.option_type_ref(detail.ty);
        }
    }
}

fn read_symbol(input: &mut Reader<'_>) -> Option<Symbol> {
    let kind = from_symbol_kind(input.u8()?)?;
    let name = input.string()?;
    let container = input.option_id()?;
    let members = input.ids()?;
    let locations = (0..input.usize()?)
        .map(|_| input.location())
        .collect::<Option<Vec<_>>>()?;
    let accessibility = from_accessibility(input.u8()?)?;
    let modifiers = Modifiers::from_bits(input.u32()?);
    let detail = match input.u8()? {
        0 => Detail::Namespace,
        1 => Detail::NamedType(NamedType {
            type_kind: match input.u8()? {
                0 => None,
                kind => Some(from_type_kind(kind - 1)?),
            },
            arity: input.usize()?,
            type_parameters: input.ids()?,
            base_types: (0..input.usize()?)
                .map(|_| input.location().map(TypeSyntaxRef))
                .collect::<Option<_>>()?,
            enum_underlying: input.option_type_ref()?,
            ref_like: input.bool()?,
            primary_constructor: input.option_id()?,
            anonymous: input.bool()?,
            union_declaration: input.bool()?,
            union_attribute: input.bool()?,
            interpolated_string_handler: input.bool()?,
        }),
        2 => Detail::Method(Method {
            return_type: input.option_type_ref()?,
            synthesized_return: input.option_synthesized()?,
            parameters: input.ids()?,
            type_parameters: input.ids()?,
            arity: input.usize()?,
            method_kind: from_method_kind(input.u8()?)?,
            is_extension: input.bool()?,
            returns_readonly: input.bool()?,
            extended: input.option_type_ref()?,
            is_vararg: input.bool()?,
        }),
        3 => Detail::Field(Field {
            ty: input.option_type_ref()?,
            has_initializer: input.bool()?,
        }),
        4 => Detail::Property(Property {
            ty: input.option_type_ref()?,
            synthesized: input.option_synthesized()?,
            parameters: input.ids()?,
            has_get: input.bool()?,
            has_set: input.bool()?,
            has_init: input.bool()?,
            backing_field: input.option_id()?,
            is_indexer: input.bool()?,
            returns_readonly: input.bool()?,
            getter: input.option_id()?,
            setter: input.option_id()?,
            get_accessibility: from_option_accessibility(input.u8()?)?,
            set_accessibility: from_option_accessibility(input.u8()?)?,
            extended: input.option_type_ref()?,
            extension_generics: input.ids()?,
        }),
        5 => Detail::Event(Event {
            ty: input.option_type_ref()?,
            adder: input.option_id()?,
            remover: input.option_id()?,
        }),
        6 => Detail::Parameter(Parameter {
            ty: input.option_type_ref()?,
            synthesized: input.option_synthesized()?,
            ref_kind: from_ref_kind(input.u8()?)?,
            ref_readonly: input.bool()?,
            unscoped_ref: input.bool()?,
            is_params: input.bool()?,
            has_default: input.bool()?,
            enumerator_cancellation: input.bool()?,
            caller_info: match input.u8()? {
                0 => None,
                1 => Some(CallerInfo::MemberName),
                2 => Some(CallerInfo::LineNumber),
                3 => Some(CallerInfo::FilePath),
                4 => Some(CallerInfo::ArgumentExpression(input.string()?)),
                5 => Some(CallerInfo::ArgumentConstant(input.string()?)),
                _ => return None,
            },
            captured: input.option_id()?,
            declared_name: input.strings()?.pop(),
            handler_arguments: match (input.bool()?, input.strings()?) {
                (true, names) => Some(names),
                (false, _) => None,
            },
        }),
        7 => Detail::TypeParameter(TypeParameter {
            constraints: (0..input.usize()?)
                .map(|_| input.location().map(TypeSyntaxRef))
                .collect::<Option<_>>()?,
            value_type: input.bool()?,
            reference_type: input.bool()?,
            constructor: input.bool()?,
            allows_ref_struct: input.bool()?,
            unmanaged: input.bool()?,
            variance: match input.u8()? {
                0 => Variance::None,
                1 => Variance::Out,
                2 => Variance::In,
                _ => return None,
            },
            declared_name: input.strings()?.pop(),
        }),
        8 => Detail::Local(Local {
            ty: input.option_type_ref()?,
        }),
        _ => return None,
    };
    Some(Symbol {
        id: SymbolId(0),
        kind,
        name,
        container,
        members,
        locations,
        accessibility,
        modifiers,
        detail,
    })
}

// MARK: - what came out of metadata

fn write_loaded(out: &mut Writer, loaded: &Loaded) {
    let mut types: Vec<_> = loaded.types.iter().collect();
    types.sort_by_key(|(id, _)| id.0);
    out.usize(types.len());
    for (id, ty) in types {
        out.id(*id);
        out.ty(ty);
    }
    let mut bases: Vec<_> = loaded.bases.iter().collect();
    bases.sort_by_key(|(id, _)| id.0);
    out.usize(bases.len());
    for (id, list) in bases {
        out.id(*id);
        out.usize(list.len());
        for ty in list {
            out.ty(ty);
        }
    }
    let mut assemblies: Vec<_> = loaded.assemblies.iter().collect();
    assemblies.sort_by_key(|(id, _)| id.0);
    out.usize(assemblies.len());
    for (id, reference) in assemblies {
        out.id(*id);
        out.str(&reference.name);
        for part in reference.version {
            out.u32(u32::from(part));
        }
    }
    let mut constants: Vec<_> = loaded.constants.iter().collect();
    constants.sort_by_key(|(id, _)| id.0);
    out.usize(constants.len());
    for (id, value) in constants {
        out.id(*id);
        out.constant(value);
    }
    let mut conditions: Vec<_> = loaded.conditions.iter().collect();
    conditions.sort_by_key(|(id, _)| id.0);
    out.usize(conditions.len());
    for (id, names) in conditions {
        out.id(*id);
        out.strings(names);
    }
    let mut builders: Vec<_> = loaded.builders.iter().collect();
    builders.sort_by_key(|(id, _)| id.0);
    out.usize(builders.len());
    for (id, (ty, method)) in builders {
        out.id(*id);
        out.str(ty);
        out.str(method);
    }
    let mut async_builders: Vec<_> = loaded.async_builders.iter().collect();
    async_builders.sort_by_key(|(id, _)| id.0);
    out.usize(async_builders.len());
    for (id, builder) in async_builders {
        out.id(*id);
        out.str(builder);
    }
    let mut in_modifiers: Vec<_> = loaded.in_modifiers.iter().collect();
    in_modifiers.sort_by_key(|id| id.0);
    out.usize(in_modifiers.len());
    for id in in_modifiers {
        out.id(*id);
    }
    let mut priorities: Vec<_> = loaded.priorities.iter().collect();
    priorities.sort_by_key(|(id, _)| id.0);
    out.usize(priorities.len());
    for (id, priority) in priorities {
        out.id(*id);
        out.u32(priority.cast_unsigned());
    }
    let mut obsolete: Vec<_> = loaded.obsolete.iter().collect();
    obsolete.sort_by_key(|(id, _)| id.0);
    out.usize(obsolete.len());
    for (id, (message, error)) in obsolete {
        out.id(*id);
        out.u8(u8::from(message.is_some()) | (u8::from(*error) << 1));
        out.str(message.as_deref().unwrap_or(""));
    }
    let mut modifier_types: Vec<_> = loaded.modifier_types.iter().collect();
    modifier_types.sort_by_key(|(id, _)| id.0);
    out.usize(modifier_types.len());
    for (id, modifier) in modifier_types {
        out.id(*id);
        out.id(*modifier);
    }
    let mut fixed_buffers: Vec<_> = loaded.fixed_buffers.iter().collect();
    fixed_buffers.sort_by_key(|(id, _)| id.0);
    out.usize(fixed_buffers.len());
    for (id, buffer) in fixed_buffers {
        out.id(*id);
        out.id(*buffer);
    }
    let mut parameter_defaults: Vec<_> = loaded.parameter_defaults.iter().collect();
    parameter_defaults.sort_by_key(|(id, _)| id.0);
    out.usize(parameter_defaults.len());
    for (id, value) in parameter_defaults {
        out.id(*id);
        out.constant(value);
    }
    let mut com_imports: Vec<_> = loaded.com_imports.iter().collect();
    com_imports.sort_by_key(|(id, _)| id.0);
    out.usize(com_imports.len());
    for (id, co_class) in com_imports {
        out.id(*id);
        match co_class {
            Some(name) => {
                out.u8(1);
                out.str(name);
            }
            None => out.u8(0),
        }
    }
    let mut custom_modifiers: Vec<_> = loaded.custom_modifiers.iter().collect();
    custom_modifiers.sort_by_key(|(id, _)| id.0);
    out.usize(custom_modifiers.len());
    for (id, modifiers) in custom_modifiers {
        out.id(*id);
        out.usize(modifiers.len());
        for modifier in modifiers {
            out.u8(u8::from(modifier.required));
            out.str(&modifier.name);
            match &modifier.assembly {
                Some(assembly) => {
                    out.u8(1);
                    out.str(&assembly.name);
                    for part in assembly.version {
                        out.u32(u32::from(part));
                    }
                }
                None => out.u8(0),
            }
        }
    }
    let mut extern_aliases: Vec<_> = loaded.extern_aliases.iter().collect();
    extern_aliases.sort();
    out.usize(extern_aliases.len());
    for (alias, root) in extern_aliases {
        out.str(alias);
        out.id(*root);
    }
    let mut specials: Vec<_> = loaded.special_constants.iter().collect();
    specials.sort_by_key(|(id, _)| id.0);
    out.usize(specials.len());
    for (id, value) in specials {
        out.id(*id);
        match value {
            SpecialConstant::Decimal {
                scale,
                negative,
                hi,
                mid,
                lo,
            } => {
                out.u8(0);
                out.u8(*scale);
                out.bool(*negative);
                out.u32(*hi);
                out.u32(*mid);
                out.u32(*lo);
            }
            SpecialConstant::DateTime(ticks) => {
                out.u8(1);
                out.u64(*ticks as u64);
            }
        }
    }
    let mut com_defaults: Vec<_> = loaded.com_defaults.iter().collect();
    com_defaults.sort_by_key(|(id, _)| id.0);
    out.usize(com_defaults.len());
    for (id, default) in com_defaults {
        out.id(*id);
        out.u8(match default {
            ComDefault::Null => 0,
            ComDefault::UnknownWrapper => 1,
            ComDefault::DispatchWrapper => 2,
        });
    }
    let mut trusting: Vec<_> = loaded.trusting.iter().collect();
    trusting.sort();
    out.usize(trusting.len());
    for (name, trusted) in trusting {
        out.str(name);
        out.usize(trusted.len());
        for index in trusted {
            out.u32(u32::from(*index));
        }
    }
}

fn read_loaded(input: &mut Reader<'_>) -> Option<Loaded> {
    let mut loaded = Loaded::default();
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.types.insert(id, input.ty()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let list = (0..input.usize()?)
            .map(|_| input.ty())
            .collect::<Option<Vec<_>>>()?;
        loaded.bases.insert(id, list);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let name = input.string()?;
        let mut version = [0u16; 4];
        for part in &mut version {
            *part = u16::try_from(input.u32()?).ok()?;
        }
        loaded.assemblies.insert(id, Reference { name, version });
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.constants.insert(id, input.constant()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.conditions.insert(id, input.strings()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let ty = input.string()?;
        loaded.builders.insert(id, (ty, input.string()?));
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.async_builders.insert(id, input.string()?);
    }
    for _ in 0..input.usize()? {
        loaded.in_modifiers.insert(input.id()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.priorities.insert(id, input.u32()?.cast_signed());
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let flags = input.u8()?;
        let message = input.string()?;
        loaded
            .obsolete
            .insert(id, ((flags & 1 != 0).then_some(message), flags & 2 != 0));
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.modifier_types.insert(id, input.id()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.fixed_buffers.insert(id, input.id()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        loaded.parameter_defaults.insert(id, input.constant()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let co_class = match input.u8()? {
            0 => None,
            _ => Some(input.string()?),
        };
        loaded.com_imports.insert(id, co_class);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let modifiers = (0..input.usize()?)
            .map(|_| {
                let required = input.u8()? != 0;
                let name = input.string()?;
                let assembly = match input.u8()? {
                    0 => None,
                    _ => {
                        let assembly = input.string()?;
                        let mut version = [0u16; 4];
                        for part in &mut version {
                            *part = u16::try_from(input.u32()?).ok()?;
                        }
                        Some(Reference {
                            name: assembly,
                            version,
                        })
                    }
                };
                Some(crate::metadata::SignatureModifier {
                    required,
                    assembly,
                    name,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        loaded.custom_modifiers.insert(id, modifiers);
    }
    for _ in 0..input.usize()? {
        let alias = input.string()?;
        loaded.extern_aliases.insert(alias, input.id()?);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let value = match input.u8()? {
            0 => SpecialConstant::Decimal {
                scale: input.u8()?,
                negative: input.bool()?,
                hi: input.u32()?,
                mid: input.u32()?,
                lo: input.u32()?,
            },
            1 => SpecialConstant::DateTime(input.u64()? as i64),
            _ => return None,
        };
        loaded.special_constants.insert(id, value);
    }
    for _ in 0..input.usize()? {
        let id = input.id()?;
        let default = match input.u8()? {
            0 => ComDefault::Null,
            1 => ComDefault::UnknownWrapper,
            2 => ComDefault::DispatchWrapper,
            _ => return None,
        };
        loaded.com_defaults.insert(id, default);
    }
    for _ in 0..input.usize()? {
        let name = input.string()?;
        let trusted = (0..input.usize()?)
            .map(|_| u16::try_from(input.u32()?).ok())
            .collect::<Option<Vec<u16>>>()?;
        loaded.trusting.insert(name, trusted);
    }
    Some(loaded)
}

// MARK: - enumerations

const fn symbol_kind(kind: SymbolKind) -> u8 {
    match kind {
        SymbolKind::Namespace => 0,
        SymbolKind::NamedType => 1,
        SymbolKind::Method => 2,
        SymbolKind::Field => 3,
        SymbolKind::Property => 4,
        SymbolKind::Event => 5,
        SymbolKind::Parameter => 6,
        SymbolKind::TypeParameter => 7,
        SymbolKind::Local => 8,
    }
}

const fn from_symbol_kind(value: u8) -> Option<SymbolKind> {
    Some(match value {
        0 => SymbolKind::Namespace,
        1 => SymbolKind::NamedType,
        2 => SymbolKind::Method,
        3 => SymbolKind::Field,
        4 => SymbolKind::Property,
        5 => SymbolKind::Event,
        6 => SymbolKind::Parameter,
        7 => SymbolKind::TypeParameter,
        8 => SymbolKind::Local,
        _ => return None,
    })
}

const fn type_kind(kind: TypeKind) -> u8 {
    match kind {
        TypeKind::Class => 0,
        TypeKind::Struct => 1,
        TypeKind::Interface => 2,
        TypeKind::Enum => 3,
        TypeKind::Delegate => 4,
        TypeKind::Record => 5,
        TypeKind::RecordStruct => 6,
    }
}

const fn from_type_kind(value: u8) -> Option<TypeKind> {
    Some(match value {
        0 => TypeKind::Class,
        1 => TypeKind::Struct,
        2 => TypeKind::Interface,
        3 => TypeKind::Enum,
        4 => TypeKind::Delegate,
        5 => TypeKind::Record,
        6 => TypeKind::RecordStruct,
        _ => return None,
    })
}

const fn accessibility(value: Accessibility) -> u8 {
    match value {
        Accessibility::NotApplicable => 0,
        Accessibility::Private => 1,
        Accessibility::ProtectedAndInternal => 2,
        Accessibility::Protected => 3,
        Accessibility::Internal => 4,
        Accessibility::ProtectedOrInternal => 5,
        Accessibility::Public => 6,
    }
}

const fn from_accessibility(value: u8) -> Option<Accessibility> {
    Some(match value {
        0 => Accessibility::NotApplicable,
        1 => Accessibility::Private,
        2 => Accessibility::ProtectedAndInternal,
        3 => Accessibility::Protected,
        4 => Accessibility::Internal,
        5 => Accessibility::ProtectedOrInternal,
        6 => Accessibility::Public,
        _ => return None,
    })
}

/// An accessor's own accessibility, or none: `u8::MAX` is none.
const fn option_accessibility(value: Option<Accessibility>) -> u8 {
    match value {
        Some(value) => accessibility(value),
        None => u8::MAX,
    }
}

const fn from_option_accessibility(value: u8) -> Option<Option<Accessibility>> {
    if value == u8::MAX {
        return Some(None);
    }
    match from_accessibility(value) {
        Some(value) => Some(Some(value)),
        None => None,
    }
}

const fn method_kind(kind: MethodKind) -> u8 {
    match kind {
        MethodKind::Ordinary => 0,
        MethodKind::Constructor => 1,
        MethodKind::StaticConstructor => 2,
        MethodKind::Destructor => 3,
        MethodKind::Operator => 4,
        MethodKind::Conversion => 5,
        MethodKind::LocalFunction => 6,
        MethodKind::RecordSynthesized => 7,
        MethodKind::PropertyGet => 8,
        MethodKind::PropertySet => 9,
    }
}

const fn from_method_kind(value: u8) -> Option<MethodKind> {
    Some(match value {
        0 => MethodKind::Ordinary,
        1 => MethodKind::Constructor,
        2 => MethodKind::StaticConstructor,
        3 => MethodKind::Destructor,
        4 => MethodKind::Operator,
        5 => MethodKind::Conversion,
        6 => MethodKind::LocalFunction,
        7 => MethodKind::RecordSynthesized,
        8 => MethodKind::PropertyGet,
        9 => MethodKind::PropertySet,
        _ => return None,
    })
}

const fn ref_kind(kind: RefKind) -> u8 {
    match kind {
        RefKind::None => 0,
        RefKind::Ref => 1,
        RefKind::Out => 2,
        RefKind::In => 3,
    }
}

const fn from_ref_kind(value: u8) -> Option<RefKind> {
    Some(match value {
        0 => RefKind::None,
        1 => RefKind::Ref,
        2 => RefKind::Out,
        3 => RefKind::In,
        _ => return None,
    })
}

fn special_index(special: SpecialType) -> usize {
    SpecialType::ALL
        .iter()
        .position(|candidate| *candidate == special)
        .expect("every special type is in ALL")
}

// MARK: - the bytes

/// Integers as LEB128: most of what is written is a small id or a length.
#[derive(Default)]
struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn bool(&mut self, value: bool) {
        self.u8(u8::from(value));
    }

    fn u64(&mut self, mut value: u64) {
        loop {
            let byte = (value & 0x7f) as u8;
            value >>= 7;
            if value == 0 {
                self.bytes.push(byte);
                return;
            }
            self.bytes.push(byte | 0x80);
        }
    }

    fn u32(&mut self, value: u32) {
        self.u64(u64::from(value));
    }

    fn usize(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn usizes(&mut self, values: &[usize]) {
        self.usize(values.len());
        for value in values {
            self.usize(*value);
        }
    }

    fn str(&mut self, text: &str) {
        self.usize(text.len());
        self.bytes.extend_from_slice(text.as_bytes());
    }

    fn strings(&mut self, texts: &[String]) {
        self.usize(texts.len());
        for text in texts {
            self.str(text);
        }
    }

    fn id(&mut self, id: SymbolId) {
        self.u32(id.0);
    }

    fn ids(&mut self, ids: &[SymbolId]) {
        self.usize(ids.len());
        for id in ids {
            self.id(*id);
        }
    }

    fn option_id(&mut self, id: Option<SymbolId>) {
        // Zero is "none", so an id is written one up.
        self.u64(id.map_or(0, |id| u64::from(id.0) + 1));
    }

    fn span(&mut self, span: TextSpan) {
        self.u32(span.start());
        self.u32(span.length());
    }

    fn location(&mut self, location: Location) {
        self.usize(location.tree);
        self.span(location.span);
    }

    fn option_type_ref(&mut self, reference: Option<TypeSyntaxRef>) {
        match reference {
            None => self.u8(0),
            Some(reference) => {
                self.u8(1);
                self.location(reference.0);
            }
        }
    }

    fn option_synthesized(&mut self, synthesized: Option<SynthesizedType>) {
        match synthesized {
            None => self.u8(0),
            Some(SynthesizedType::Special(special)) => {
                self.u8(1);
                self.usize(special_index(special));
            }
            Some(SynthesizedType::Containing) => self.u8(2),
            Some(SynthesizedType::TypeParameter(index)) => {
                self.u8(3);
                self.usize(index);
            }
            Some(SynthesizedType::StringArray) => self.u8(4),
            Some(SynthesizedType::Task) => self.u8(5),
            Some(SynthesizedType::TaskOfInt32) => self.u8(6),
            Some(SynthesizedType::SystemType) => self.u8(7),
            Some(SynthesizedType::StringBuilder) => self.u8(8),
        }
    }

    fn ty(&mut self, ty: &Type) {
        match ty {
            Type::Error => self.u8(0),
            Type::Named {
                symbol,
                type_arguments,
            } => {
                self.u8(1);
                self.id(*symbol);
                self.usize(type_arguments.len());
                for argument in type_arguments {
                    self.ty(argument);
                }
            }
            Type::Array { element, rank } => {
                self.u8(2);
                self.ty(element);
                self.usize(*rank);
            }
            Type::Pointer(inner) => {
                self.u8(3);
                self.ty(inner);
            }
            Type::TypeParameter(symbol) => {
                self.u8(4);
                self.id(*symbol);
            }
            Type::Tuple(elements) => {
                self.u8(5);
                self.usize(elements.len());
                for element in elements {
                    match &element.name {
                        Some(name) => {
                            self.u8(1);
                            self.str(name);
                        }
                        None => self.u8(0),
                    }
                    self.ty(&element.ty);
                }
            }
            Type::ByRef(inner) => {
                self.u8(6);
                self.ty(inner);
            }
            Type::Null => self.u8(7),
            Type::Void => self.u8(8),
            Type::Dynamic => self.u8(9),
            Type::FunctionPointer(pointer) => {
                self.u8(10);
                self.u8(pointer.convention);
                self.strings(&pointer.modifiers);
                self.u8(ref_kind(pointer.returns_ref));
                self.ty(&pointer.returns);
                self.usize(pointer.parameters.len());
                for (kind, ty) in &pointer.parameters {
                    self.u8(ref_kind(*kind));
                    self.ty(ty);
                }
            }
        }
    }

    fn constant(&mut self, value: &ConstantValue) {
        match value {
            ConstantValue::Null => self.u8(0),
            ConstantValue::Boolean(value) => {
                self.u8(1);
                self.bool(*value);
            }
            ConstantValue::Char(value) => {
                self.u8(2);
                self.u32(u32::from(*value));
            }
            ConstantValue::Int32(value) => {
                self.u8(3);
                self.u32(*value as u32);
            }
            ConstantValue::UInt32(value) => {
                self.u8(4);
                self.u32(*value);
            }
            ConstantValue::Int64(value) => {
                self.u8(5);
                self.u64(*value as u64);
            }
            ConstantValue::UInt64(value) => {
                self.u8(6);
                self.u64(*value);
            }
            ConstantValue::Single(value) => {
                self.u8(7);
                self.u32(value.to_bits());
            }
            ConstantValue::Double(value) => {
                self.u8(8);
                self.u64(value.to_bits());
            }
            ConstantValue::String(value) => {
                self.u8(9);
                self.str(value);
            }
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, count: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(count)?;
        let slice = self.bytes.get(self.at..end)?;
        self.at = end;
        Some(slice)
    }

    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }

    fn bool(&mut self) -> Option<bool> {
        match self.u8()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    fn u64(&mut self) -> Option<u64> {
        let mut value = 0u64;
        for shift in (0..64).step_by(7) {
            let byte = self.u8()?;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Some(value);
            }
        }
        None
    }

    fn u32(&mut self) -> Option<u32> {
        u32::try_from(self.u64()?).ok()
    }

    fn usize(&mut self) -> Option<usize> {
        let value = usize::try_from(self.u64()?).ok()?;
        // No count in a well-formed snapshot is larger than what is left of
        // it; a damaged one must not ask for gigabytes.
        (value <= self.bytes.len()).then_some(value)
    }

    fn usizes(&mut self) -> Option<Vec<usize>> {
        (0..self.usize()?).map(|_| self.usize()).collect()
    }

    fn string(&mut self) -> Option<String> {
        let length = self.usize()?;
        String::from_utf8(self.take(length)?.to_vec()).ok()
    }

    fn strings(&mut self) -> Option<Vec<String>> {
        (0..self.usize()?).map(|_| self.string()).collect()
    }

    fn id(&mut self) -> Option<SymbolId> {
        self.u32().map(SymbolId)
    }

    fn ids(&mut self) -> Option<Vec<SymbolId>> {
        (0..self.usize()?).map(|_| self.id()).collect()
    }

    fn option_id(&mut self) -> Option<Option<SymbolId>> {
        Some(match self.u64()? {
            0 => None,
            value => Some(SymbolId(u32::try_from(value - 1).ok()?)),
        })
    }

    fn span(&mut self) -> Option<TextSpan> {
        let start = self.u32()?;
        Some(TextSpan::new(start, self.u32()?))
    }

    fn location(&mut self) -> Option<Location> {
        let tree = self.usize()?;
        Some(Location::new(tree, self.span()?))
    }

    fn option_type_ref(&mut self) -> Option<Option<TypeSyntaxRef>> {
        Some(match self.u8()? {
            0 => None,
            1 => Some(TypeSyntaxRef(self.location()?)),
            _ => return None,
        })
    }

    fn option_synthesized(&mut self) -> Option<Option<SynthesizedType>> {
        Some(match self.u8()? {
            0 => None,
            1 => Some(SynthesizedType::Special(
                *SpecialType::ALL.get(self.usize()?)?,
            )),
            2 => Some(SynthesizedType::Containing),
            3 => Some(SynthesizedType::TypeParameter(self.usize()?)),
            4 => Some(SynthesizedType::StringArray),
            5 => Some(SynthesizedType::Task),
            6 => Some(SynthesizedType::TaskOfInt32),
            7 => Some(SynthesizedType::SystemType),
            8 => Some(SynthesizedType::StringBuilder),
            _ => return None,
        })
    }

    fn ty(&mut self) -> Option<Type> {
        Some(match self.u8()? {
            0 => Type::Error,
            1 => {
                let symbol = self.id()?;
                let type_arguments = (0..self.usize()?)
                    .map(|_| self.ty())
                    .collect::<Option<_>>()?;
                Type::Named {
                    symbol,
                    type_arguments,
                }
            }
            2 => {
                let element = Box::new(self.ty()?);
                Type::Array {
                    element,
                    rank: self.usize()?,
                }
            }
            3 => Type::Pointer(Box::new(self.ty()?)),
            4 => Type::TypeParameter(self.id()?),
            5 => Type::Tuple(
                (0..self.usize()?)
                    .map(|_| {
                        let name = match self.u8()? {
                            0 => None,
                            1 => Some(self.string()?),
                            _ => return None,
                        };
                        Some(TupleElement {
                            name,
                            ty: self.ty()?,
                        })
                    })
                    .collect::<Option<_>>()?,
            ),
            6 => Type::ByRef(Box::new(self.ty()?)),
            7 => Type::Null,
            8 => Type::Void,
            9 => Type::Dynamic,
            10 => {
                let convention = self.u8()?;
                let modifiers = self.strings()?;
                let returns_ref = from_ref_kind(self.u8()?)?;
                let returns = self.ty()?;
                let parameters = (0..self.usize()?)
                    .map(|_| Some((from_ref_kind(self.u8()?)?, self.ty()?)))
                    .collect::<Option<_>>()?;
                Type::FunctionPointer(Box::new(crate::types::FunctionPointer {
                    convention,
                    modifiers,
                    returns,
                    returns_ref,
                    parameters,
                }))
            }
            _ => return None,
        })
    }

    fn constant(&mut self) -> Option<ConstantValue> {
        Some(match self.u8()? {
            0 => ConstantValue::Null,
            1 => ConstantValue::Boolean(self.bool()?),
            2 => ConstantValue::Char(char::from_u32(self.u32()?)?),
            3 => ConstantValue::Int32(self.u32()? as i32),
            4 => ConstantValue::UInt32(self.u32()?),
            5 => ConstantValue::Int64(self.u64()? as i64),
            6 => ConstantValue::UInt64(self.u64()?),
            7 => ConstantValue::Single(f32::from_bits(self.u32()?)),
            8 => ConstantValue::Double(f64::from_bits(self.u64()?)),
            9 => ConstantValue::String(self.string()?),
            _ => return None,
        })
    }
}

#[cfg(test)]
mod tests {
    use rustlyn_syntax::parse;

    use super::*;

    const PROGRAM: &str = r#"
using System;
namespace Game {
    public enum Mode { Idle, Run = 4 }
    public interface IActor { void Act(); }
    public partial class Pawn<T> : IActor where T : class {
        public const string Tag = "pawn";
        public int Health { get; private set; }
        public event Action Died;
        public void Act() { }
        public static Pawn<T> Make(ref int count, params T[] items) => null;
        public (int x, string name) Pair => (1, "a");
    }
    public static class Extensions { public static int Twice(this int x) => x * 2; }
}
"#;

    #[test]
    fn a_compilation_reads_back_as_the_compilation_it_was() {
        let compilation = Compilation::create(vec![parse(SourceText::new("Game.cs", PROGRAM))]);
        let bytes = compilation.write_snapshot();
        let read = Compilation::read_snapshot(&bytes).expect("it reads back");

        assert_eq!(read.symbols().len(), compilation.symbols().len());
        for (a, b) in compilation.symbols().iter().zip(read.symbols().iter()) {
            assert_eq!(a.name, b.name);
            assert_eq!(a.kind, b.kind);
            assert_eq!(a.container, b.container);
            assert_eq!(a.members, b.members);
            assert_eq!(a.locations, b.locations);
            assert_eq!(format!("{:?}", a.detail), format!("{:?}", b.detail));
        }
        assert_eq!(read.trees().len(), compilation.trees().len());
        assert!(!read.trees().is_parsed(1), "trees come back unparsed");
        assert_eq!(read.global_using_trees(), compilation.global_using_trees());
        for special in SpecialType::ALL {
            assert_eq!(
                read.special_type(*special),
                compilation.special_type(*special)
            );
        }
        assert_eq!(
            read.extension_methods("Twice"),
            compilation.extension_methods("Twice")
        );

        // And it answers questions as the original did.
        let pawn = compilation
            .type_by_metadata_name("Game.Pawn`1")
            .expect("Pawn");
        assert_eq!(read.type_by_metadata_name("Game.Pawn`1"), Some(pawn));
        let model = crate::SemanticModel::new(&read, 1);
        let health = read.symbols().lookup(pawn, "Health")[0];
        assert_eq!(
            model.type_of_symbol(health).display(read.symbols()),
            "int",
            "a property's type is resolved from the lazily parsed tree"
        );
        assert!(read.trees().is_parsed(1));
    }

    #[test]
    fn a_damaged_snapshot_is_not_used() {
        let compilation = Compilation::from_source("class A { }");
        let mut bytes = compilation.write_snapshot();
        assert!(Compilation::read_snapshot(&bytes[..bytes.len() - 1]).is_none());
        bytes[8] = bytes[8].wrapping_add(1);
        assert!(
            Compilation::read_snapshot(&bytes).is_none(),
            "another format"
        );
        assert!(Compilation::read_snapshot(b"nonsense").is_none());
    }
}
