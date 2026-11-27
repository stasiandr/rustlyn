//! Building symbols out of a real assembly's metadata.
//!
//! Everything else in this crate learns what exists by reading syntax. This
//! learns it by reading tables, which is the other half of what a compiler
//! needs: the core library is not compiled from source, it is referenced, and
//! a reference is a file of metadata rather than a file of text.
//!
//! The two kinds of symbol end up in the same arena and answer the same
//! questions, with one difference that runs through this whole module: a
//! metadata symbol has no syntax, so its type cannot be a [`TypeSyntaxRef`]
//! pointing at a tree. Its types are resolved here, once, and handed back in
//! [`Loaded`] for the binder to consult instead.
//!
//! [`TypeSyntaxRef`]: crate::symbol::TypeSyntaxRef

use std::collections::HashSet;
use std::sync::Arc;

use rustlyn_metadata::signature::{Blob, MethodSig, TypeSig};
use rustlyn_metadata::{Assembly, Token, table};

use crate::bound::{ConstantValue, SpecialConstant};
use crate::fxhash::{FxHashMap, FxHashSet};
use crate::symbol::{
    Accessibility, CallerInfo, Detail, Event, Field, Method, MethodKind, Modifiers, NamedType,
    Parameter, Property, RefKind, Symbol, SymbolId, SymbolKind, Symbols, TypeKind, Variance,
};
use crate::types::Type;

/// What loading produced besides the symbols themselves.
///
/// A metadata symbol's type is worked out while its assembly is being read,
/// because that is the only moment the tokens in its signature mean anything.
/// These maps are where the answers wait for the binder.
#[derive(Clone, Debug, Default)]
pub(crate) struct Loaded {
    /// A field's type, a method's return type, a parameter's type.
    pub(crate) types: FxHashMap<SymbolId, Type>,
    /// What a type extends and implements.
    pub(crate) bases: FxHashMap<SymbolId, Vec<Type>>,
    /// The assembly each loaded type came out of, which is what a backend has
    /// to write an `AssemblyRef` for.
    pub(crate) assemblies: FxHashMap<SymbolId, Reference>,
    /// The value of each `const` field read out of an assembly: a literal has
    /// no storage, so every read of one is the value itself.
    pub(crate) constants: FxHashMap<SymbolId, ConstantValue>,
    /// The symbols a `[Conditional("...")]` names, per method. A call to one
    /// of these is kept only where one of them is defined.
    pub(crate) conditions: FxHashMap<SymbolId, Vec<String>>,
    /// What a `[CollectionBuilder]` type is built by: the builder type's full
    /// name and the method on it. `ImmutableArray<T>` is made by
    /// `ImmutableArray.Create`, and nothing but this attribute says so.
    pub(crate) builders: FxHashMap<SymbolId, (String, String)>,
    /// What a task-like type is built by: the full name its
    /// `[AsyncMethodBuilder(typeof(B))]` gives `B`, which is how an `async`
    /// method returning `UniTask` knows to make an `AsyncUniTaskMethodBuilder`.
    pub(crate) async_builders: FxHashMap<SymbolId, String>,
    /// The `in` parameters whose signature puts the reference under a
    /// `modreq(InAttribute)`. C# writes one only on a virtual or abstract
    /// member's (and on whatever overrides or implements it), and a reference
    /// to the member has to spell the signature exactly as it was written.
    pub(crate) in_modifiers: std::collections::HashSet<SymbolId>,
    /// The priority each member's `[OverloadResolutionPriority(n)]` gives
    /// it, where it has one.
    pub(crate) priorities: FxHashMap<SymbolId, i32>,
    /// What an `[Obsolete]` on a type or member says: its message, if it
    /// gave one, and whether a use is an error. One that names a
    /// `DiagnosticId` is reported under that id, which no `ErrorCode` is,
    /// and is left out.
    pub(crate) obsolete: FxHashMap<SymbolId, (Option<String>, bool)>,
    /// The `InAttribute` a parameter's or a member's return `modreq` names,
    /// where it is not the one the framework defines: the modifier is part of
    /// the signature, and a reference that names another type of that name
    /// names a member the runtime cannot find.
    pub(crate) modifier_types: FxHashMap<SymbolId, SymbolId>,
    /// The struct each `fixed` buffer field is of, whose type is otherwise
    /// the element's: the field reads as a pointer, and its signature still
    /// names the struct.
    pub(crate) fixed_buffers: FxHashMap<SymbolId, SymbolId>,
    /// The namespace each `extern alias` names: the root an aliased
    /// assembly's namespaces were declared under.
    pub(crate) extern_aliases: FxHashMap<String, SymbolId>,
    /// The custom modifiers, `modreq` and `modopt`, a parameter's type or a
    /// method's or property's return carries in its signature, in the order
    /// written. A reference to the member repeats them, and an override
    /// copies them: the runtime tells signatures apart by them.
    pub(crate) custom_modifiers: FxHashMap<SymbolId, Vec<SignatureModifier>>,
    /// The `decimal` and `DateTime` constants written as attributes: on a
    /// parameter, its default; on a field, its value.
    pub(crate) special_constants: FxHashMap<SymbolId, SpecialConstant>,
    /// The default value an optional parameter read from metadata was given.
    pub(crate) parameter_defaults: FxHashMap<SymbolId, ConstantValue>,
    /// The `[ComImport]` types (the `import` flag of §II.23.1.15), each with
    /// the class its `[CoClass]` names, as the attribute's blob spells it:
    /// what `new I()` on such an interface makes.
    pub(crate) com_imports: FxHashMap<SymbolId, Option<String>>,
    /// What a parameter read from metadata is when it is an `[Optional]
    /// object` left out, where a COM attribute says.
    pub(crate) com_defaults: FxHashMap<SymbolId, ComDefault>,
    /// Which of the assemblies being compiled each reference names in an
    /// `[InternalsVisibleTo]`, by the reference's name, as indexes into the
    /// names it was compiled as: its internals are for their code alone.
    pub(crate) trusting: FxHashMap<String, Vec<u16>>,
}

/// What a COM attribute makes of an `[Optional] object` parameter a call
/// leaves out, in place of `Missing.Value` (Roslyn's
/// `GetDefaultParameterSpecialNoConversion`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ComDefault {
    /// Marshalled as an interface, `IUnknown` or `IDispatch`: `null`.
    Null,
    /// `[IUnknownConstant]`: `new UnknownWrapper(null)`.
    UnknownWrapper,
    /// `[IDispatchConstant]`: `new DispatchWrapper(null)`.
    DispatchWrapper,
}

/// One `modreq` or `modopt` of a signature read from metadata, by the type
/// it names: its full metadata name and the assembly that defines it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SignatureModifier {
    pub required: bool,
    pub assembly: Option<Reference>,
    pub name: String,
}

/// An assembly as a reference to it names it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Reference {
    pub name: String,
    /// Major, minor, build, revision.
    pub version: [u16; 4],
}

impl std::fmt::Display for Reference {
    /// The name and version, as a diagnostic names an assembly.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let [major, minor, build, revision] = self.version;
        write!(
            f,
            "{}, Version={major}.{minor}.{build}.{revision}",
            self.name
        )
    }
}

/// Reads every assembly in `images` into `symbols`.
///
/// The assemblies are read together rather than one at a time because a
/// signature in one names types in another, and a name can only be resolved
/// once everything that might answer it has been declared.
///
/// Some references may be named by `extern alias` (`/r:A=x.dll`): an
/// assembly given aliases, none of them `global`, is not seen from the
/// global namespace at all. Its namespaces hang off a root of their own,
/// which each of its aliases names, and `A::N.T` is looked up from there.
pub(crate) fn load(
    symbols: &mut Symbols,
    global: SymbolId,
    images: &[&[u8]],
    aliases: &[Vec<String>],
    names: &[&str],
) -> Loaded {
    // Reading an assembly's tables and indexing them is its own business;
    // only declaring what they hold has to be done in order.
    let read: Vec<_> = crate::parallel::map(images, |bytes| Assembly::read(bytes).ok())
        .into_iter()
        .enumerate()
        .filter_map(|(at, assembly)| {
            assembly.map(|assembly| (assembly, aliases.get(at).cloned().unwrap_or_default()))
        })
        .collect();
    let (assemblies, aliases): (Vec<_>, Vec<_>) = read.into_iter().unzip();
    let mut loader = Loader::new(&assemblies);
    // An assembly that names the one being compiled in an
    // `[InternalsVisibleTo]` shows it what is internal as well.
    if !names.is_empty() {
        let trusted: Vec<Vec<u16>> = (0..assemblies.len())
            .map(|index| {
                let mut trusted: Vec<u16> = loader
                    .every_attribute_string(
                        index,
                        table::ASSEMBLY,
                        1,
                        "System.Runtime.CompilerServices.InternalsVisibleToAttribute",
                    )
                    .iter()
                    .filter_map(|friend| {
                        let friend = friend.split(',').next()?.trim();
                        names
                            .iter()
                            .position(|name| name.eq_ignore_ascii_case(friend))
                            .and_then(|at| u16::try_from(at).ok())
                    })
                    .collect();
                trusted.sort_unstable();
                trusted.dedup();
                trusted
            })
            .collect();
        for (index, trusted) in trusted.iter().enumerate() {
            if !trusted.is_empty()
                && let Some(reference) = reference_of(&assemblies[index])
            {
                loader
                    .loaded
                    .trusting
                    .insert(reference.name, trusted.clone());
            }
        }
        loader.friends = Arc::new(trusted.iter().map(|trusted| !trusted.is_empty()).collect());
    }
    for (index, names) in aliases.iter().enumerate() {
        let root = if names.is_empty() || names.iter().any(|name| name == "global") {
            global
        } else {
            let root = symbols.add(SymbolKind::Namespace, "", None, Detail::Namespace);
            for name in names {
                loader.loaded.extern_aliases.insert(name.clone(), root);
            }
            root
        };
        loader.declare_types(symbols, root, index);
    }
    // Every assembly's members are read beside the others' into a staging
    // table of their own, the biggest assemblies first so that none is left
    // running alone at the end; then each is appended in assembly order,
    // which numbers every symbol as reading them one after another would.
    let mut order: Vec<usize> = (0..assemblies.len()).collect();
    order.sort_by_key(|&index| std::cmp::Reverse(assemblies[index].rows(table::METHOD_DEF)));
    let table: &Symbols = symbols;
    let mut staged = crate::parallel::map(&order, |&index| {
        let mut staging = Staging::new(table);
        let mut fork = loader.fork(index);
        fork.fill_members(&mut staging, index);
        (index, staging.made, fork.loaded)
    });
    staged.sort_unstable_by_key(|(index, ..)| *index);
    // Where each assembly's symbols will start, which is known before any
    // is appended: the symbols and the tables beside them are then filled
    // at once, each on a thread of its own.
    let mut next = symbols.len() as u32;
    let mut made_all = Vec::new();
    let mut loaded_all = Vec::new();
    for (_, made, loaded) in staged {
        let count = made.len() as u32;
        made_all.push((next, made));
        loaded_all.push((next, loaded));
        next += count;
    }
    symbols.reserve(next as usize - symbols.len());
    let mut loaded = std::mem::take(&mut loader.loaded);
    std::thread::scope(|scope| {
        scope.spawn(|| {
            let types = loaded_all
                .iter()
                .map(|(_, staged)| staged.types.len())
                .sum();
            loaded.types.reserve(types);
            for (base, staged) in loaded_all {
                loaded.absorb(staged, base);
            }
        });
        for (base, made) in made_all {
            for (mut symbol, indexed) in made {
                // A member of a type declared before is listed there now; one
                // of a symbol made in the same staging already is.
                let link = symbol
                    .container
                    .is_some_and(|container| !is_staged(container));
                relocate_symbol(&mut symbol, base);
                symbols.push_made(symbol, link, indexed);
            }
        }
    });
    loader.loaded = loaded;
    loader.withdraw_bad_members(symbols);
    loader.new_slots_for_mismatched_overrides(symbols);
    loader.loaded
}

/// What reading members does with a symbol table: [`Symbols`] itself, or a
/// [`Staging`] table beside it.
trait Table {
    fn get(&self, id: SymbolId) -> &Symbol;
    fn get_mut(&mut self, id: SymbolId) -> &mut Symbol;
    fn add(
        &mut self,
        kind: SymbolKind,
        name: impl Into<String>,
        container: Option<SymbolId>,
        detail: Detail,
    ) -> SymbolId;
    fn add_unindexed(
        &mut self,
        kind: SymbolKind,
        name: String,
        container: SymbolId,
        detail: Detail,
    ) -> SymbolId;
}

impl Table for Symbols {
    fn get(&self, id: SymbolId) -> &Symbol {
        Symbols::get(self, id)
    }

    fn get_mut(&mut self, id: SymbolId) -> &mut Symbol {
        Symbols::get_mut(self, id)
    }

    fn add(
        &mut self,
        kind: SymbolKind,
        name: impl Into<String>,
        container: Option<SymbolId>,
        detail: Detail,
    ) -> SymbolId {
        Symbols::add(self, kind, name, container, detail)
    }

    fn add_unindexed(
        &mut self,
        kind: SymbolKind,
        name: String,
        container: SymbolId,
        detail: Detail,
    ) -> SymbolId {
        Symbols::add_unindexed(self, kind, name, container, detail)
    }
}

/// Where the symbols made in a staging table are numbered from until they
/// are appended: above every real symbol, below the late ones.
const STAGED: u32 = 1 << 29;

fn is_staged(id: SymbolId) -> bool {
    (STAGED..1 << 30).contains(&id.0)
}

/// The symbols one assembly's members make, read beside the real table and
/// numbered apart from it, in the order they were made, each with whether
/// it goes into the name index.
struct Staging<'s> {
    table: &'s Symbols,
    made: Vec<(Symbol, bool)>,
}

impl<'s> Staging<'s> {
    fn new(table: &'s Symbols) -> Self {
        Self {
            table,
            made: Vec::new(),
        }
    }

    fn make(
        &mut self,
        kind: SymbolKind,
        name: String,
        container: Option<SymbolId>,
        detail: Detail,
        indexed: bool,
    ) -> SymbolId {
        let id = SymbolId(STAGED + self.made.len() as u32);
        if let Some(container) = container
            && is_staged(container)
        {
            self.made[(container.0 - STAGED) as usize]
                .0
                .members
                .push(id);
        }
        self.made.push((
            Symbol {
                id,
                kind,
                name,
                container,
                members: Vec::new(),
                locations: Vec::new(),
                accessibility: Accessibility::NotApplicable,
                modifiers: Modifiers::empty(),
                detail,
            },
            indexed,
        ));
        id
    }
}

impl Table for Staging<'_> {
    fn get(&self, id: SymbolId) -> &Symbol {
        if is_staged(id) {
            &self.made[(id.0 - STAGED) as usize].0
        } else {
            self.table.get(id)
        }
    }

    fn get_mut(&mut self, id: SymbolId) -> &mut Symbol {
        assert!(
            is_staged(id),
            "reading members changes only the symbols it makes"
        );
        &mut self.made[(id.0 - STAGED) as usize].0
    }

    fn add(
        &mut self,
        kind: SymbolKind,
        name: impl Into<String>,
        container: Option<SymbolId>,
        detail: Detail,
    ) -> SymbolId {
        self.make(kind, name.into(), container, detail, container.is_some())
    }

    fn add_unindexed(
        &mut self,
        kind: SymbolKind,
        name: String,
        container: SymbolId,
        detail: Detail,
    ) -> SymbolId {
        self.make(kind, name, Some(container), detail, false)
    }
}

/// A staged symbol's number once its staging is appended at `base`.
fn relocated(id: SymbolId, base: u32) -> SymbolId {
    if is_staged(id) {
        SymbolId(id.0 - STAGED + base)
    } else {
        id
    }
}

fn relocate_all(ids: &mut [SymbolId], base: u32) {
    for id in ids {
        *id = relocated(*id, base);
    }
}

fn relocate_option(id: &mut Option<SymbolId>, base: u32) {
    if let Some(id) = id {
        *id = relocated(*id, base);
    }
}

/// Every symbol number a staged symbol holds, renumbered.
fn relocate_symbol(symbol: &mut Symbol, base: u32) {
    symbol.id = relocated(symbol.id, base);
    relocate_option(&mut symbol.container, base);
    relocate_all(&mut symbol.members, base);
    match &mut symbol.detail {
        Detail::NamedType(detail) => {
            relocate_all(&mut detail.type_parameters, base);
            relocate_option(&mut detail.primary_constructor, base);
        }
        Detail::Method(detail) => {
            relocate_all(&mut detail.parameters, base);
            relocate_all(&mut detail.type_parameters, base);
        }
        Detail::Property(detail) => {
            relocate_all(&mut detail.parameters, base);
            relocate_option(&mut detail.backing_field, base);
            relocate_option(&mut detail.getter, base);
            relocate_option(&mut detail.setter, base);
            relocate_all(&mut detail.extension_generics, base);
        }
        Detail::Event(detail) => {
            relocate_option(&mut detail.adder, base);
            relocate_option(&mut detail.remover, base);
        }
        Detail::Parameter(detail) => relocate_option(&mut detail.captured, base),
        Detail::Namespace | Detail::Field(_) | Detail::TypeParameter(_) | Detail::Local(_) => {}
    }
}

/// A type naming staged symbols, renumbered.
fn relocate_type(ty: &mut Type, base: u32) {
    match ty {
        Type::Named {
            symbol,
            type_arguments,
        } => {
            *symbol = relocated(*symbol, base);
            for argument in type_arguments {
                relocate_type(argument, base);
            }
        }
        Type::TypeParameter(symbol) => *symbol = relocated(*symbol, base),
        Type::Array { element, .. } => relocate_type(element, base),
        Type::Pointer(inner) | Type::ByRef(inner) => relocate_type(inner, base),
        Type::Tuple(elements) => {
            for element in elements {
                relocate_type(&mut element.ty, base);
            }
        }
        Type::FunctionPointer(pointer) => {
            relocate_type(&mut pointer.returns, base);
            for (_, parameter) in &mut pointer.parameters {
                relocate_type(parameter, base);
            }
        }
        Type::Error | Type::Null | Type::Void | Type::Dynamic => {}
    }
}

impl Loaded {
    /// Takes in what one staged assembly's members produced, renumbered.
    fn absorb(&mut self, staged: Self, base: u32) {
        for (id, mut ty) in staged.types {
            relocate_type(&mut ty, base);
            self.types.insert(relocated(id, base), ty);
        }
        for (id, mut bases) in staged.bases {
            for ty in &mut bases {
                relocate_type(ty, base);
            }
            self.bases.insert(relocated(id, base), bases);
        }
        for (id, reference) in staged.assemblies {
            self.assemblies.insert(relocated(id, base), reference);
        }
        for (id, value) in staged.constants {
            self.constants.insert(relocated(id, base), value);
        }
        for (id, conditions) in staged.conditions {
            self.conditions.insert(relocated(id, base), conditions);
        }
        for (id, builder) in staged.builders {
            self.builders.insert(relocated(id, base), builder);
        }
        for (id, builder) in staged.async_builders {
            self.async_builders.insert(relocated(id, base), builder);
        }
        for id in staged.in_modifiers {
            self.in_modifiers.insert(relocated(id, base));
        }
        for (id, priority) in staged.priorities {
            self.priorities.insert(relocated(id, base), priority);
        }
        for (id, obsolete) in staged.obsolete {
            self.obsolete.insert(relocated(id, base), obsolete);
        }
        for (id, attribute) in staged.modifier_types {
            self.modifier_types
                .insert(relocated(id, base), relocated(attribute, base));
        }
        for (id, buffer) in staged.fixed_buffers {
            self.fixed_buffers
                .insert(relocated(id, base), relocated(buffer, base));
        }
        for (name, root) in staged.extern_aliases {
            self.extern_aliases.insert(name, relocated(root, base));
        }
        for (id, modifiers) in staged.custom_modifiers {
            self.custom_modifiers.insert(relocated(id, base), modifiers);
        }
        for (id, value) in staged.special_constants {
            self.special_constants.insert(relocated(id, base), value);
        }
        for (id, value) in staged.parameter_defaults {
            self.parameter_defaults.insert(relocated(id, base), value);
        }
        for (id, co_class) in staged.com_imports {
            self.com_imports.insert(relocated(id, base), co_class);
        }
        for (id, default) in staged.com_defaults {
            self.com_defaults.insert(relocated(id, base), default);
        }
    }
}

/// The tables of one assembly, indexed the way this module walks them.
struct Index {
    /// A nested type's enclosing type, by `TypeDef` row.
    enclosing: FxHashMap<u32, u32>,
    /// A type's or a method's type parameters, in position order, each with
    /// the `GenericParam` row it came from — which is what its constraints
    /// are keyed by.
    /// Each type parameter's name, its `GenericParam` row and the raw flags
    /// of §II.23.1.7 — variance and the `class`, `struct` and `new()`
    /// constraints all live in there.
    type_parameters: FxHashMap<u32, Vec<(String, u32, u32)>>,
    method_parameters: FxHashMap<u32, Vec<(String, u32, u32)>>,
    /// What each `GenericParam` row is constrained to be.
    constraints: FxHashMap<u32, Vec<Token>>,
    /// The interfaces a type lists, by `TypeDef` row, each with its
    /// `InterfaceImpl` row, where the attributes on the listing are.
    interfaces: FxHashMap<u32, Vec<(u32, Token)>>,
    /// Which property a `get_` or `set_` method belongs to, and which half it
    /// is: these methods are real rows in `MethodDef`, and C# reaches them
    /// only through the property.
    accessors: FxHashMap<u32, (u32, bool)>,
    /// The same the other way round: each property's accessors, getter
    /// first. Looking them up by scanning the map above is quadratic in the
    /// size of the assembly, and the core library has thousands.
    property_accessors: FxHashMap<u32, Vec<(u32, bool)>>,
    /// A type's properties, by `TypeDef` row.
    properties: FxHashMap<u32, Vec<u32>>,
    /// A type's events, by `TypeDef` row.
    events: FxHashMap<u32, Vec<u32>>,
    /// Each event's adder and remover, adder first: `add_` and `remove_`
    /// methods are real rows in `MethodDef`, reached only through the event.
    accessors_of_event: FxHashMap<u32, Vec<(u32, bool)>>,
    /// Which methods are an event's `add_` or `remove_`, read under the
    /// event and nowhere else.
    event_accessors: FxHashSet<u32>,
    /// The value of each `const` field, by `Field` row. A literal field has no
    /// storage at all: every read of `char.MaxValue` is the value itself, and
    /// there is nothing to load.
    constants: FxHashMap<u32, ConstantValue>,
    /// The default value of each optional parameter, by `Param` row.
    parameter_constants: FxHashMap<u32, ConstantValue>,
    /// The native type each parameter is marshalled as, by `Param` row: the
    /// first byte of its `FieldMarshal` descriptor.
    parameter_marshals: FxHashMap<u32, u8>,
    /// Which type each method belongs to, which the tables say only the other
    /// way round.
    method_owner: FxHashMap<u32, u32>,
    /// The attributes applied to each row, by the table the row is in.
    ///
    /// An attribute is the CLI's way of saying what the metadata format has no
    /// column for, so a reader that skips them cannot see `params`, cannot see
    /// an extension method, and cannot see which property is the indexer.
    attributes: FxHashMap<(u8, u32), Vec<(Token, u32)>>,
}

struct Loader<'a> {
    assemblies: &'a [Assembly<'a>],
    // The tables below are only read once the types are declared, and every
    // assembly's members are then filled on a loader of its own that shares
    // them: see [`Loader::fork`].
    indexes: Arc<Vec<Index>>,
    /// How each assembly names itself, for whoever has to reference it.
    references: Arc<Vec<Option<Reference>>>,
    /// The symbol a `TypeDef` row produced, per assembly.
    rows: Arc<Vec<FxHashMap<u32, SymbolId>>>,
    /// The symbol each `GenericParam` row produced, per assembly.
    generics: Vec<FxHashMap<u32, SymbolId>>,
    /// Every loaded type by its full metadata name, which is how a `TypeRef`
    /// in one assembly finds a `TypeDef` in another.
    names: Arc<FxHashMap<String, SymbolId>>,
    /// Every loaded type by the assembly that defines it and its full name:
    /// a `TypeRef` says which assembly it means, and two assemblies may each
    /// have a type of that name.
    by_assembly: Arc<FxHashMap<(String, String), SymbolId>>,
    /// The name a row's type has, so a nested type can be found by the name
    /// its enclosing type gives it.
    keys: Arc<Vec<FxHashMap<u32, String>>>,
    loaded: Loaded,
    /// Guards against a `NestedClass` table that points in a circle.
    visiting: HashSet<(usize, u32)>,
    /// Which assemblies show the one being compiled their internals.
    friends: Arc<Vec<bool>>,
}

impl<'a> Loader<'a> {
    fn new(assemblies: &'a [Assembly<'a>]) -> Self {
        let indexes = crate::parallel::map(assemblies, index_of);
        let references = assemblies.iter().map(reference_of).collect();
        Self {
            assemblies,
            indexes: Arc::new(indexes),
            references: Arc::new(references),
            rows: Arc::new(
                (0..assemblies.len())
                    .map(|_| FxHashMap::default())
                    .collect(),
            ),
            generics: (0..assemblies.len())
                .map(|_| FxHashMap::default())
                .collect(),
            friends: Arc::new(vec![false; assemblies.len()]),
            names: Arc::new(FxHashMap::default()),
            keys: Arc::new(
                (0..assemblies.len())
                    .map(|_| FxHashMap::default())
                    .collect(),
            ),
            by_assembly: Arc::new(FxHashMap::default()),
            loaded: Loaded::default(),
            visiting: HashSet::new(),
        }
    }

    /// A loader for filling one assembly's members beside the others: it
    /// shares the declared types, and keeps what it finds to itself.
    /// Whether a member's access bits let the code being compiled see it:
    /// what another assembly could use, and what is internal too where the
    /// assembly names this one its friend.
    fn visible(&self, index: usize, access: u32) -> bool {
        is_visible(access)
            || (self.friends.get(index).copied().unwrap_or(false) && matches!(access, 2 | 3))
    }

    fn fork(&self, index: usize) -> Self {
        Self {
            assemblies: self.assemblies,
            indexes: Arc::clone(&self.indexes),
            references: Arc::clone(&self.references),
            rows: Arc::clone(&self.rows),
            generics: (0..self.assemblies.len())
                .map(|at| {
                    if at == index {
                        self.generics[at].clone()
                    } else {
                        FxHashMap::default()
                    }
                })
                .collect(),
            names: Arc::clone(&self.names),
            keys: Arc::clone(&self.keys),
            by_assembly: Arc::clone(&self.by_assembly),
            loaded: Loaded::default(),
            visiting: HashSet::new(),
            friends: Arc::clone(&self.friends),
        }
    }

    // -- declaring ---------------------------------------------------------

    fn declare_types(&mut self, symbols: &mut Symbols, global: SymbolId, index: usize) {
        for row in 1..=self.assemblies[index].rows(table::TYPE_DEF) {
            self.declare_type(symbols, global, index, row);
        }
    }

    /// Declares one `TypeDef`, and whatever encloses it first.
    fn declare_type(
        &mut self,
        symbols: &mut Symbols,
        global: SymbolId,
        index: usize,
        row: u32,
    ) -> Option<SymbolId> {
        if let Some(id) = self.rows[index].get(&row) {
            return Some(*id);
        }
        if !self.visiting.insert((index, row)) {
            return None;
        }
        let result = self.declare_type_uncached(symbols, global, index, row);
        self.visiting.remove(&(index, row));
        result
    }

    fn declare_type_uncached(
        &mut self,
        symbols: &mut Symbols,
        global: SymbolId,
        index: usize,
        row: u32,
    ) -> Option<SymbolId> {
        let assembly = &self.assemblies[index];
        let heaps = assembly.heaps();
        let definition = assembly.table(table::TYPE_DEF).row(row)?;
        let flags = definition.number(0);
        let name = heaps.string(definition.number(1));
        let namespace = heaps.string(definition.number(2));

        // Row one is the module's own pseudo-type, which holds whatever has no
        // type of its own and is nobody's to name.
        if name == "<Module>" {
            return None;
        }
        // Only what another assembly could have used: an internal type is real
        // but unreachable, and reading them all triples the table for nothing.
        let visibility = flags & 0x07;
        let friend = self.friends.get(index).copied().unwrap_or(false);
        if !matches!(
            visibility,
            PUBLIC | NESTED_PUBLIC | NESTED_FAMILY | NESTED_FAM_OR_ASSEM
        ) && !(friend
            && matches!(
                visibility,
                NOT_PUBLIC | NESTED_ASSEMBLY | NESTED_FAM_AND_ASSEM
            ))
        {
            return None;
        }

        // A nested type repeats its enclosing type's type parameters in its
        // own `GenericParam` rows, before any of its own: `Dictionary<K, V>`'s
        // `Enumerator` has two, and declares neither.
        let mut inherited = 0;
        let mut inherited_parameters: Vec<SymbolId> = Vec::new();
        let (container, key) = if matches!(visibility, NOT_PUBLIC | PUBLIC) {
            (
                namespace_chain(symbols, global, namespace),
                qualified(namespace, name),
            )
        } else {
            let enclosing = *self.indexes[index].enclosing.get(&row)?;
            let container = self.declare_type(symbols, global, index, enclosing)?;
            inherited = self.indexes[index]
                .type_parameters
                .get(&enclosing)
                .map_or(0, Vec::len);
            // The enclosing type's parameters are *the same* parameters, not
            // copies of them: `ImmutableArray<T>.Builder.ToImmutable()` gives
            // back an `ImmutableArray<T>` for that very `T`, and two symbols
            // spelled `T` would make those two different types.
            inherited_parameters = symbols
                .get(container)
                .as_named_type()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            // Metadata spells a nested type `Outer+Inner`, and that is the
            // name a `TypeRef` in another assembly will ask for.
            let outer = self.keys[index].get(&enclosing).cloned()?;
            (container, format!("{outer}+{name}"))
        };

        // Two counts, and they are different things. The arity is how many
        // parameters the type declares *in C#* — `Dictionary<K, V>.Enumerator`
        // declares none — and it is what a name lookup and a metadata name are
        // spelled with. The parameter list is all of them, inherited ones
        // first, because that is what a construction of the nested type
        // carries and what a substitution has to line up against.
        let all = self.indexes[index]
            .type_parameters
            .get(&row)
            .cloned()
            .unwrap_or_default();
        let arity = all.len().saturating_sub(inherited);
        let reference = self.references[index].clone();
        let id = symbols.add(
            SymbolKind::NamedType,
            strip_arity(name),
            Some(container),
            Detail::NamedType(NamedType {
                type_kind: Some(self.kind_of(
                    index,
                    flags,
                    definition.token(3),
                    &qualified(namespace, name),
                )),
                arity,
                // A `ref struct` says so with an attribute; there is no flag
                // for it, and nothing but the attribute tells `Span<T>` from
                // any other struct.
                ref_like: self.has_attribute(
                    index,
                    table::TYPE_DEF,
                    row,
                    "System.Runtime.CompilerServices.IsByRefLikeAttribute",
                ),
                interpolated_string_handler: self.has_attribute(
                    index,
                    table::TYPE_DEF,
                    row,
                    "System.Runtime.CompilerServices.InterpolatedStringHandlerAttribute",
                ),
                union_attribute: self.has_attribute(
                    index,
                    table::TYPE_DEF,
                    row,
                    "System.Runtime.CompilerServices.UnionAttribute",
                ),
                ..NamedType::default()
            }),
        );
        let own = add_type_parameters(symbols, id, &all[inherited.min(all.len())..]);
        let mut type_parameters = inherited_parameters;
        type_parameters.truncate(inherited);
        type_parameters.extend(own);
        for ((_, generic, _), parameter) in all.iter().zip(&type_parameters) {
            self.generics[index].insert(*generic, *parameter);
        }
        if let Detail::NamedType(detail) = &mut symbols.get_mut(id).detail {
            detail.type_parameters = type_parameters;
        }
        let symbol = symbols.get_mut(id);
        // An internal type is here only for an assembly it names its friend.
        symbol.accessibility = match visibility {
            NESTED_FAMILY => Accessibility::Protected,
            NESTED_FAM_OR_ASSEM => Accessibility::ProtectedOrInternal,
            NOT_PUBLIC | NESTED_ASSEMBLY => Accessibility::Internal,
            NESTED_FAM_AND_ASSEM => Accessibility::ProtectedAndInternal,
            _ => Accessibility::Public,
        };
        symbol.modifiers = type_modifiers(flags);
        // `readonly struct` is an attribute: every member of it promises not
        // to write `this`, which is what spares a caller a defensive copy.
        if self.has_attribute(
            index,
            table::TYPE_DEF,
            row,
            "System.Runtime.CompilerServices.IsReadOnlyAttribute",
        ) {
            symbols.get_mut(id).modifiers.insert(Modifiers::READONLY);
        }

        if let Some(reference) = reference {
            self.loaded.assemblies.insert(id, reference);
        }
        if flags & 0x1000 != 0 {
            let co_class = self
                .attribute_strings(
                    index,
                    table::TYPE_DEF,
                    row,
                    "System.Runtime.InteropServices.CoClassAttribute",
                )
                .and_then(|given| given.into_iter().next());
            self.loaded.com_imports.insert(id, co_class);
        }
        // `[CollectionBuilder(typeof(ImmutableArray), "Create")]` is how a
        // type says a collection expression can be made into one of it.
        if let Some(given) = self.attribute_strings(
            index,
            table::TYPE_DEF,
            row,
            "System.Runtime.CompilerServices.CollectionBuilderAttribute",
        ) && let [builder, method, ..] = &given[..]
        {
            // The type argument is written the way a reference names a type,
            // with the assembly after a comma; only the name is wanted.
            let builder = builder.split(',').next().unwrap_or(builder).trim();
            self.loaded
                .builders
                .insert(id, (builder.to_string(), method.clone()));
        }
        // `[AsyncMethodBuilder(typeof(B))]`, whose one argument is a type
        // and so, in the blob, a name.
        if let Some(given) = self.attribute_strings(
            index,
            table::TYPE_DEF,
            row,
            "System.Runtime.CompilerServices.AsyncMethodBuilderAttribute",
        ) && let Some(builder) = given.first()
        {
            let builder = builder.split(',').next().unwrap_or(builder).trim();
            self.loaded.async_builders.insert(id, builder.to_string());
        }
        Arc::make_mut(&mut self.rows)[index].insert(row, id);
        Arc::make_mut(&mut self.keys)[index].insert(row, key.clone());
        // First one wins: two assemblies can both define `System.Object`, and
        // the one loaded first is the one everything else will have resolved
        // against.
        if let Some(reference) = &self.references[index] {
            Arc::make_mut(&mut self.by_assembly).insert((reference.name.clone(), key.clone()), id);
        }
        Arc::make_mut(&mut self.names).entry(key).or_insert(id);
        Some(id)
    }

    /// Which flavour of type a `TypeDef` is, which metadata says only by what
    /// the type extends: an enum is a class deriving from `System.Enum`.
    fn kind_of(&self, index: usize, flags: u32, extends: Token, own: &str) -> TypeKind {
        if flags & 0x20 != 0 {
            return TypeKind::Interface;
        }
        // The types the test below reads are classes themselves. `System.Enum`
        // extends `System.ValueType` without being a struct, and a value of an
        // enum reaches it only boxed — which is why `marks.HasFlag(other)`
        // passes an object where the value was written.
        if matches!(
            own,
            "System.ValueType" | "System.Enum" | "System.Delegate" | "System.MulticastDelegate"
        ) {
            return TypeKind::Class;
        }
        match self.name_of(index, extends).as_deref() {
            Some("System.Enum") => TypeKind::Enum,
            Some("System.ValueType") => TypeKind::Struct,
            Some("System.MulticastDelegate" | "System.Delegate") => TypeKind::Delegate,
            _ => TypeKind::Class,
        }
    }

    /// The full metadata name a `TypeDef` or `TypeRef` token spells, without
    /// resolving it to anything.
    ///
    /// This runs before the symbols exist, which is why it works in names.
    fn name_of(&self, index: usize, token: Token) -> Option<String> {
        // A chain of enclosing types is no longer than there are `TypeRef`
        // rows; one that is has come round to itself, which only a damaged
        // assembly's does — a `TypeRef` nested in itself was followed for
        // ever.
        let hops = self.assemblies[index].rows(table::TYPE_REF);
        self.name_within(index, token, hops)
    }

    fn name_within(&self, index: usize, token: Token, hops: u32) -> Option<String> {
        let assembly = &self.assemblies[index];
        let heaps = assembly.heaps();
        let row = assembly.row(token)?;
        match token.table() {
            table::TYPE_DEF => Some(qualified(
                heaps.string(row.number(2)),
                heaps.string(row.number(1)),
            )),
            table::TYPE_REF => {
                let name = heaps.string(row.number(1));
                let namespace = heaps.string(row.number(2));
                // A `TypeRef` whose scope is another `TypeRef` is a nested
                // type, and its own namespace column is empty.
                let scope = row.token(0);
                if scope.table() == table::TYPE_REF {
                    let outer = self.name_within(index, scope, hops.checked_sub(1)?)?;
                    Some(format!("{outer}+{name}"))
                } else {
                    Some(qualified(namespace, name))
                }
            }
            _ => None,
        }
    }

    // -- members -----------------------------------------------------------

    fn fill_members(&mut self, symbols: &mut impl Table, index: usize) {
        for row in 1..=self.assemblies[index].rows(table::TYPE_DEF) {
            let Some(id) = self.rows[index].get(&row).copied() else {
                continue;
            };
            self.fill_bases(symbols, index, row, id);
            self.fill_constraints(symbols, index, row, id, table::TYPE_DEF, &[]);
            if let Some(obsolete) = self.obsolete_of(index, table::TYPE_DEF, row) {
                self.loaded.obsolete.insert(id, obsolete);
            }
            self.fill_fields(symbols, index, row, id);
            self.fill_properties(symbols, index, row, id);
            self.fill_events(symbols, index, row, id);
            self.fill_methods(symbols, index, row, id);
        }
    }

    fn fill_bases(&mut self, symbols: &impl Table, index: usize, row: u32, id: SymbolId) {
        let Some(definition) = self.assemblies[index].table(table::TYPE_DEF).row(row) else {
            return;
        };
        let scope = Scope::new(symbols, id, &[]);
        let mut bases = Vec::new();
        let extends = definition.token(3);
        // `class C2 : Base<(int x, int y)>` names the elements with a
        // `[TupleElementNames]` on the type itself, and a `dynamic` among the
        // type arguments with a `[Dynamic]`; an interface's are on its
        // `InterfaceImpl` row.
        if !extends.is_nil()
            && let Some(base) = self.type_of_token(symbols, index, extends, &scope)
        {
            let base = self.with_dynamic(index, table::TYPE_DEF, row, base, false);
            bases.push(self.with_tuple_names(index, table::TYPE_DEF, row, base));
        }
        if let Some(interfaces) = self.indexes[index].interfaces.get(&row) {
            for (listed, token) in interfaces.clone() {
                if let Some(ty) = self.type_of_token(symbols, index, token, &scope) {
                    let ty = self.with_dynamic(index, table::INTERFACE_IMPL, listed, ty, false);
                    bases.push(self.with_tuple_names(index, table::INTERFACE_IMPL, listed, ty));
                }
            }
        }
        self.loaded.bases.insert(id, bases);
    }

    /// Resolves what each of an owner's type parameters is constrained to be.
    ///
    /// A constraint is where a `T` gets its members: without one it has only
    /// `object`'s, and `item.Area()` on a `T` has nothing to find.
    fn fill_constraints(
        &mut self,
        symbols: &impl Table,
        index: usize,
        owner_row: u32,
        owner: SymbolId,
        owner_table: u8,
        method_parameters: &[SymbolId],
    ) {
        let parameters = if owner_table == table::TYPE_DEF {
            self.indexes[index].type_parameters.get(&owner_row).cloned()
        } else {
            self.indexes[index]
                .method_parameters
                .get(&owner_row)
                .cloned()
        };
        let Some(parameters) = parameters else {
            return;
        };
        let scope = Scope::new(symbols, owner, method_parameters);
        for (_, generic, _) in parameters {
            let Some(parameter) = self.generics[index].get(&generic).copied() else {
                continue;
            };
            let Some(tokens) = self.indexes[index].constraints.get(&generic).cloned() else {
                continue;
            };
            let bases: Vec<Type> = tokens
                .into_iter()
                .filter_map(|token| self.type_of_token(symbols, index, token, &scope))
                .collect();
            if !bases.is_empty() {
                self.loaded.bases.insert(parameter, bases);
            }
        }
    }

    fn fill_fields(&mut self, symbols: &mut impl Table, index: usize, row: u32, id: SymbolId) {
        let assembly = &self.assemblies[index];
        let scope = Scope::new(symbols, id, &[]);
        for field in list_range(assembly, table::TYPE_DEF, row, 4, table::FIELD) {
            let Some(entry) = assembly.table(table::FIELD).row(field) else {
                continue;
            };
            let flags = entry.number(0);
            if !self.visible(index, flags & 0x07) {
                continue;
            }
            let name = assembly.heaps().string(entry.number(1));
            let ty = assembly
                .heaps()
                .blob(entry.number(2))
                .ok()
                .and_then(|bytes| Blob::new(bytes).field_sig().ok())
                .and_then(|sig| self.type_of_sig(symbols, index, &sig, &scope))
                .unwrap_or(Type::Error);
            let member = symbols.add(
                SymbolKind::Field,
                name,
                Some(id),
                Detail::Field(Field::default()),
            );
            let symbol = symbols.get_mut(member);
            symbol.accessibility = accessibility_of(flags & 0x07);
            // A literal is `const`, which in the CLI means static as well;
            // `InitOnly` is `readonly`.
            if flags & 0x10 != 0 {
                symbol.modifiers.insert(Modifiers::STATIC);
            }
            if flags & 0x20 != 0 {
                symbol.modifiers.insert(Modifiers::READONLY);
            }
            if flags & 0x40 != 0 {
                symbol.modifiers.insert(Modifiers::CONST);
            }
            // `required` is `[RequiredMember]` (C# 11).
            if self.has_attribute(
                index,
                table::FIELD,
                field,
                "System.Runtime.CompilerServices.RequiredMemberAttribute",
            ) {
                symbols
                    .get_mut(member)
                    .modifiers
                    .insert(Modifiers::REQUIRED);
            }
            if let Some(value) = self.indexes[index].constants.get(&field) {
                self.loaded.constants.insert(member, value.clone());
            }
            if let Some(value) = self.special_constant(index, table::FIELD, field) {
                self.loaded.special_constants.insert(member, value);
            }
            // `fixed int x[10]` is a field of a struct made for it, holding
            // one `int` and sized for all ten; C# reads the field as the
            // `int*` to its first element (§24.8.3), the way it reads its own.
            let buffer = ty.symbol().filter(|_| {
                self.has_attribute(
                    index,
                    table::FIELD,
                    field,
                    "System.Runtime.CompilerServices.FixedBufferAttribute",
                )
            });
            if let Some(element) =
                buffer.and_then(|buffer| self.fixed_element(symbols, index, buffer))
            {
                symbols.get_mut(member).modifiers.insert(Modifiers::FIXED);
                self.loaded
                    .fixed_buffers
                    .insert(member, ty.symbol().unwrap_or(id));
                self.loaded.types.insert(member, element);
                continue;
            }
            if let Some(obsolete) = self.obsolete_of(index, table::FIELD, field) {
                self.loaded.obsolete.insert(member, obsolete);
            }
            let ty = self.with_dynamic(index, table::FIELD, field, ty, false);
            let ty = self.with_tuple_names(index, table::FIELD, field, ty);
            self.loaded.types.insert(member, ty);
        }
    }

    /// The element type of a `fixed` buffer's struct: the type of the one
    /// field it has, `FixedElementField`.
    fn fixed_element(&self, symbols: &impl Table, index: usize, buffer: SymbolId) -> Option<Type> {
        let row = self.rows[index]
            .iter()
            .find(|(_, id)| **id == buffer)
            .map(|(row, _)| *row)?;
        let assembly = &self.assemblies[index];
        let field = list_range(assembly, table::TYPE_DEF, row, 4, table::FIELD).next()?;
        let entry = assembly.table(table::FIELD).row(field)?;
        let sig = Blob::new(assembly.heaps().blob(entry.number(2)).ok()?)
            .field_sig()
            .ok()?;
        let scope = Scope::new(symbols, buffer, &[]);
        self.type_of_sig(symbols, index, &sig, &scope)
    }

    fn fill_properties(&mut self, symbols: &mut impl Table, index: usize, row: u32, id: SymbolId) {
        let Some(properties) = self.indexes[index].properties.get(&row).cloned() else {
            return;
        };
        // A `[ComImport]` type's indexer is the property `[DefaultMember]`
        // names, and any other with parameters is an indexed property, `P[i]`
        // under its own name (Roslyn's `IsIndexer` and `IsIndexedProperty`).
        let com_import = self.assemblies[index]
            .table(table::TYPE_DEF)
            .row(row)
            .is_some_and(|definition| definition.number(0) & 0x1000 != 0);
        let default_member = com_import.then(|| {
            self.attribute_strings(
                index,
                table::TYPE_DEF,
                row,
                "System.Reflection.DefaultMemberAttribute",
            )
            .and_then(|given| given.into_iter().next())
            .unwrap_or_default()
        });
        let assembly = &self.assemblies[index];
        let scope = Scope::new(symbols, id, &[]);
        for property in properties {
            let Some(entry) = assembly.table(table::PROPERTY).row(property) else {
                continue;
            };
            let name = assembly.heaps().string(entry.number(1));
            // A property none of whose accessors can be seen from outside —
            // `KeyedCollection<TKey, TItem>.Items`, a private `new` over the
            // base's — is not there for the code being compiled, and a
            // symbol for it would hide the one it shadows.
            let accessors = self.indexes[index]
                .property_accessors
                .get(&property)
                .cloned()
                .unwrap_or_default();
            let seen = accessors.iter().any(|(method, _)| {
                assembly
                    .table(table::METHOD_DEF)
                    .row(*method)
                    .is_some_and(|entry| self.visible(index, entry.number(2) & 0x07))
            });
            if !seen {
                continue;
            }
            let Some(sig) = assembly
                .heaps()
                .blob(entry.number(2))
                .ok()
                .and_then(|bytes| Blob::new(bytes).property_sig().ok())
            else {
                continue;
            };
            let ty = self
                .type_of_sig(symbols, index, &sig.returns, &scope)
                .unwrap_or(Type::Error);
            // A property with parameters is an indexer, which C# spells with
            // `this[...]` rather than with the name metadata gives it — but an
            // explicit interface implementation is not reachable by that name
            // at all, and metadata spells one `IList<T>.Item`, dots and all.
            let indexer = !sig.parameters.is_empty()
                && !name.contains('.')
                && default_member
                    .as_ref()
                    .is_none_or(|default| default == name);
            let member = symbols.add(
                SymbolKind::Property,
                if indexer { "this[]" } else { name },
                Some(id),
                Detail::Property(Property {
                    is_indexer: indexer,
                    returns_readonly: sig.returns_required.iter().any(|modifier| {
                        self.name_of(index, *modifier).as_deref()
                            == Some("System.Runtime.InteropServices.InAttribute")
                    }),
                    ..Property::default()
                }),
            );
            if let Some(Some(modifier)) =
                self.in_attribute_modifier(symbols, index, &sig.returns_required, &scope)
            {
                self.loaded.modifier_types.insert(member, modifier);
            }
            if !sig.returns_modifiers.is_empty() {
                let written = self.signature_modifiers(index, &sig.returns_modifiers);
                self.loaded.custom_modifiers.insert(member, written);
            }
            if let Some(obsolete) = self.obsolete_of(index, table::PROPERTY, property) {
                self.loaded.obsolete.insert(member, obsolete);
            }
            // An indexer carries its `[OverloadResolutionPriority]` on the
            // property, not on an accessor.
            if let Some(priority) = self.attribute_int(
                index,
                table::PROPERTY,
                property,
                "System.Runtime.CompilerServices.OverloadResolutionPriorityAttribute",
            ) && priority != 0
            {
                self.loaded.priorities.insert(member, priority);
            }
            let ty = self.with_dynamic(index, table::PROPERTY, property, ty, false);
            let ty = self.with_tuple_names(index, table::PROPERTY, property, ty);
            self.loaded.types.insert(member, ty);
            // `required` is `[RequiredMember]` (C# 11).
            if self.has_attribute(
                index,
                table::PROPERTY,
                property,
                "System.Runtime.CompilerServices.RequiredMemberAttribute",
            ) {
                symbols
                    .get_mut(member)
                    .modifiers
                    .insert(Modifiers::REQUIRED);
            }
            // A `Property` row has no parameter rows of its own: an indexer's
            // names, and the `[In]` that says a reference is `in`, are on its
            // accessors', which take the same parameters first.
            // Getter first, as the list is sorted.
            let accessor = accessors.first().map(|(method, _)| *method);
            let parameters = self.add_parameters(symbols, index, member, &sig, accessor, &scope);
            // The accessors of a `[ComImport]` type's indexed property may be
            // called by name, `ia.get_P(ref x)`, where the property is not
            // the indexer or takes a `ref` (Roslyn's `CanCallMethodsDirectly`).
            let callable = com_import
                && !parameters.is_empty()
                && (!indexer
                    || parameters.iter().any(|parameter| {
                        symbols
                            .get(*parameter)
                            .as_parameter()
                            .is_some_and(|detail| detail.ref_kind != RefKind::None)
                    }));
            if let Detail::Property(detail) = &mut symbols.get_mut(member).detail {
                detail.parameters = parameters;
            }
            self.link_accessors(symbols, index, property, member, &scope);
            if callable {
                for (method, _) in &accessors {
                    self.add_method(symbols, index, *method, id, &scope);
                }
            }
        }
    }

    /// The events a type declares: each is its delegate type and the
    /// `add_` and `remove_` methods a handler goes through.
    fn fill_events(&mut self, symbols: &mut impl Table, index: usize, row: u32, id: SymbolId) {
        let Some(events) = self.indexes[index].events.get(&row).cloned() else {
            return;
        };
        let assembly = &self.assemblies[index];
        let scope = Scope::new(symbols, id, &[]);
        for event in events {
            let Some(entry) = assembly.table(table::EVENT).row(event) else {
                continue;
            };
            let name = assembly.heaps().string(entry.number(1));
            let ty = self
                .type_of_token(symbols, index, entry.token(2), &scope)
                .unwrap_or(Type::Error);
            let member = symbols.add(
                SymbolKind::Event,
                name,
                Some(id),
                Detail::Event(Event {
                    ty: None,
                    adder: None,
                    remover: None,
                }),
            );
            if let Some(obsolete) = self.obsolete_of(index, table::EVENT, event) {
                self.loaded.obsolete.insert(member, obsolete);
            }
            let ty = self.with_dynamic(index, table::EVENT, event, ty, false);
            let ty = self.with_tuple_names(index, table::EVENT, event, ty);
            self.loaded.types.insert(member, ty);
            let accessors = self.indexes[index]
                .accessors_of_event
                .get(&event)
                .cloned()
                .unwrap_or_default();
            for (method, remover) in accessors {
                let Some(accessor) = self.add_method(symbols, index, method, member, &scope) else {
                    continue;
                };
                if let Detail::Event(detail) = &mut symbols.get_mut(member).detail {
                    if remover {
                        detail.remover = Some(accessor);
                    } else {
                        detail.adder = Some(accessor);
                    }
                }
                if symbols.get(accessor).modifiers.contains(Modifiers::STATIC) {
                    symbols.get_mut(member).modifiers.insert(Modifiers::STATIC);
                }
            }
        }
    }

    /// Gives a property the methods it is read and written through.
    fn link_accessors(
        &mut self,
        symbols: &mut impl Table,
        index: usize,
        property: u32,
        member: SymbolId,
        scope: &Scope,
    ) {
        let accessors = self.indexes[index]
            .property_accessors
            .get(&property)
            .cloned()
            .unwrap_or_default();
        for (method, setter) in accessors {
            let Some(id) = self.add_method(symbols, index, method, member, scope) else {
                continue;
            };
            if let Detail::Method(detail) = &mut symbols.get_mut(id).detail {
                detail.method_kind = if setter {
                    MethodKind::PropertySet
                } else {
                    MethodKind::PropertyGet
                };
            }
            if let Detail::Property(detail) = &mut symbols.get_mut(member).detail {
                if setter {
                    detail.has_set = true;
                    detail.setter = Some(id);
                } else {
                    detail.has_get = true;
                    detail.getter = Some(id);
                }
            }
            // Nothing on a `Property` row says whether it is static; its
            // accessors do, and a reference to it has to get that right or
            // the signature it names is the wrong one.
            if symbols.get(id).modifiers.contains(Modifiers::STATIC) {
                symbols.get_mut(member).modifiers.insert(Modifiers::STATIC);
            }
        }
    }

    fn fill_methods(&mut self, symbols: &mut impl Table, index: usize, row: u32, id: SymbolId) {
        let assembly = &self.assemblies[index];
        let scope = Scope::new(symbols, id, &[]);
        for method in list_range(assembly, table::TYPE_DEF, row, 5, table::METHOD_DEF) {
            // An accessor is already under its property or event, where C#
            // can find it and nothing can call it by name. An event's taken
            // as a method of its own too made an interface's `add_` and
            // `remove_` members every class implementing it lacked (CS0535),
            // whatever event it declared.
            if self.indexes[index].accessors.contains_key(&method)
                || self.indexes[index].event_accessors.contains(&method)
            {
                continue;
            }
            self.add_method(symbols, index, method, id, &scope);
        }
    }

    /// Adds one `MethodDef` under `container`, with its parameters.
    fn add_method(
        &mut self,
        symbols: &mut impl Table,
        index: usize,
        method: u32,
        container: SymbolId,
        outer: &Scope,
    ) -> Option<SymbolId> {
        let assembly = &self.assemblies[index];
        let entry = assembly.table(table::METHOD_DEF).row(method)?;
        let flags = entry.number(2);
        if !self.visible(index, flags & 0x07) {
            return None;
        }
        let name = assembly.heaps().string(entry.number(3));
        let sig = assembly
            .heaps()
            .blob(entry.number(4))
            .ok()
            .and_then(|bytes| Blob::new(bytes).method_sig().ok())?;

        let names = self.indexes[index]
            .method_parameters
            .get(&method)
            .cloned()
            .unwrap_or_default();
        let kind = match name {
            ".ctor" => MethodKind::Constructor,
            ".cctor" => MethodKind::StaticConstructor,
            _ if flags & 0x0800 != 0 && name.starts_with("op_") => MethodKind::Operator,
            _ => MethodKind::Ordinary,
        };
        let id = symbols.add(
            SymbolKind::Method,
            name,
            Some(container),
            Detail::Method(Method {
                arity: sig.arity as usize,
                method_kind: kind,
                // Nothing in a signature says a method is an extension: the
                // compiler that wrote it said so with an attribute, and a
                // compiler that reads it has to look there.
                is_extension: self.has_attribute(
                    index,
                    table::METHOD_DEF,
                    method,
                    "System.Runtime.CompilerServices.ExtensionAttribute",
                ),
                returns_readonly: sig.returns_required.iter().any(|modifier| {
                    self.name_of(index, *modifier).as_deref()
                        == Some("System.Runtime.InteropServices.InAttribute")
                }),
                ..Method::default()
            }),
        );
        if let Some(Some(modifier)) =
            self.in_attribute_modifier(symbols, index, &sig.returns_required, outer)
        {
            self.loaded.modifier_types.insert(id, modifier);
        }
        if !sig.returns_modifiers.is_empty() {
            let written = self.signature_modifiers(index, &sig.returns_modifiers);
            self.loaded.custom_modifiers.insert(id, written);
        }
        // `[Conditional("DEBUG")]` says every call to this method is kept only
        // where `DEBUG` is defined. `Debug.Assert` is the one that matters
        // most: without this, every assertion in a release build still runs.
        // Several of them keep the call where any one's symbol is defined.
        let conditions = self.every_attribute_string(
            index,
            table::METHOD_DEF,
            method,
            "System.Diagnostics.ConditionalAttribute",
        );
        if !conditions.is_empty() {
            self.loaded.conditions.insert(id, conditions);
        }
        if let Some(priority) = self.attribute_int(
            index,
            table::METHOD_DEF,
            method,
            "System.Runtime.CompilerServices.OverloadResolutionPriorityAttribute",
        ) && priority != 0
        {
            self.loaded.priorities.insert(id, priority);
        }
        if let Some(obsolete) = self.obsolete_of(index, table::METHOD_DEF, method) {
            self.loaded.obsolete.insert(id, obsolete);
        }
        let type_parameters = add_type_parameters(symbols, id, &names);
        for ((_, generic, _), parameter) in names.iter().zip(&type_parameters) {
            self.generics[index].insert(*generic, *parameter);
        }
        let scope = Scope::new(symbols, outer.owner, &type_parameters);
        self.fill_constraints(
            symbols,
            index,
            method,
            outer.owner,
            table::METHOD_DEF,
            &type_parameters,
        );
        let returns = self
            .type_of_sig(symbols, index, &sig.returns, &scope)
            .unwrap_or(Type::Error);
        let returns = match self.parameter_row(index, method, 0) {
            Some(row) => {
                let returns = self.with_dynamic(
                    index,
                    table::PARAM,
                    row,
                    returns,
                    matches!(sig.returns, TypeSig::ByRef(_)),
                );
                self.with_tuple_names(index, table::PARAM, row, returns)
            }
            None => returns,
        };
        self.loaded.types.insert(
            id,
            // A constructor's signature returns `void`; the language says it
            // returns nothing at all, which is the same answer spelled the way
            // the rest of the binder expects.
            if matches!(returns, Type::Void) {
                Type::Void
            } else {
                returns
            },
        );
        let parameters = self.add_parameters(symbols, index, id, &sig, Some(method), &scope);
        if let Detail::Method(detail) = &mut symbols.get_mut(id).detail {
            detail.parameters = parameters;
            detail.type_parameters = type_parameters;
        }
        let symbol = symbols.get_mut(id);
        symbol.accessibility = accessibility_of(flags & 0x07);
        symbol.modifiers = method_modifiers(flags);
        // A `readonly` member of a struct says so with an attribute.
        if self.has_attribute(
            index,
            table::METHOD_DEF,
            method,
            "System.Runtime.CompilerServices.IsReadOnlyAttribute",
        ) {
            symbols.get_mut(id).modifiers.insert(Modifiers::READONLY);
        }
        Some(id)
    }

    /// Adds a parameter symbol per signature parameter.
    ///
    /// The `Param` table is where the names live, and it is optional: a
    /// signature always says how many parameters there are and what types they
    /// have, and a row may or may not exist to say what one is called.
    fn add_parameters(
        &mut self,
        symbols: &mut impl Table,
        index: usize,
        owner: SymbolId,
        signature: &MethodSig,
        source: Option<u32>,
        scope: &Scope,
    ) -> Vec<SymbolId> {
        let required = &signature.parameters_required;
        let names = source.map(|method| self.parameter_names(index, method));
        let mut ids = Vec::new();
        for (position, sig) in signature.parameters.iter().enumerate() {
            let (name, flags) = names
                .as_ref()
                .and_then(|names| names.get(&(position as u32 + 1)).cloned())
                .unwrap_or_else(|| (format!("arg{position}"), 0));
            // `ref`, `out` and `in` are all `T&` in a signature. The `Out`
            // flag on the parameter row tells the second apart; the third is
            // an attribute, and without it `Unsafe.AsRef(in x)` is a call to
            // a `ref` parameter that the `in` at the call site does not fit.
            let in_attribute = required
                .get(position)
                .and_then(|modifiers| self.in_attribute_modifier(symbols, index, modifiers, scope));
            let in_modifier = in_attribute.is_some();
            let (ty, ref_kind) = match sig {
                TypeSig::ByRef(inner) => (
                    inner.as_ref(),
                    if flags & 0x02 != 0 {
                        RefKind::Out
                    } else if flags & 0x01 != 0 || in_modifier {
                        RefKind::In
                    } else {
                        RefKind::Ref
                    },
                ),
                other => (other, RefKind::None),
            };
            let resolved = self
                .type_of_sig(symbols, index, ty, scope)
                .unwrap_or(Type::Error);
            // `params` is an attribute rather than a flag, and a parameter
            // row exists to carry it only where one was written.
            let row =
                source.and_then(|method| self.parameter_row(index, method, position as u32 + 1));
            // Only on a one-dimensional array does it make a `params`: C#
            // reads one on anything else as not there.
            let is_params = matches!(resolved, Type::Array { rank: 1, .. })
                && row.is_some_and(|row| {
                    self.has_attribute(index, table::PARAM, row, "System.ParamArrayAttribute")
                });
            // `in` is what C# writes as `[IsReadOnly]` on a `ref`, with or
            // without the `In` flag and modifier.
            let ref_kind = if ref_kind == RefKind::Ref
                && row.is_some_and(|row| {
                    self.has_attribute(
                        index,
                        table::PARAM,
                        row,
                        "System.Runtime.CompilerServices.IsReadOnlyAttribute",
                    )
                }) {
                RefKind::In
            } else {
                ref_kind
            };
            // `ref readonly` is a `ref` marked `[RequiresLocation]`.
            let ref_readonly = ref_kind != RefKind::None
                && ref_kind != RefKind::Out
                && row.is_some_and(|row| {
                    self.has_attribute(
                        index,
                        table::PARAM,
                        row,
                        "System.Runtime.CompilerServices.RequiresLocationAttribute",
                    )
                });
            let ref_kind = if ref_readonly { RefKind::In } else { ref_kind };
            // The caller-info attributes say what an omitted argument is
            // filled with at the call site, and only the attribute says so.
            let caller_info = row.and_then(|row| {
                // Most parameters carry no attribute at all.
                if !self.indexes[index]
                    .attributes
                    .contains_key(&(table::PARAM, row))
                {
                    return None;
                }
                if self.has_attribute(
                    index,
                    table::PARAM,
                    row,
                    "System.Runtime.CompilerServices.CallerMemberNameAttribute",
                ) {
                    Some(CallerInfo::MemberName)
                } else if self.has_attribute(
                    index,
                    table::PARAM,
                    row,
                    "System.Runtime.CompilerServices.CallerLineNumberAttribute",
                ) {
                    Some(CallerInfo::LineNumber)
                } else if self.has_attribute(
                    index,
                    table::PARAM,
                    row,
                    "System.Runtime.CompilerServices.CallerFilePathAttribute",
                ) {
                    Some(CallerInfo::FilePath)
                } else {
                    self.attribute_strings(
                        index,
                        table::PARAM,
                        row,
                        "System.Runtime.CompilerServices.CallerArgumentExpressionAttribute",
                    )
                    .and_then(|strings| strings.into_iter().next())
                    .map(CallerInfo::ArgumentExpression)
                }
            });
            let id = symbols.add_unindexed(
                SymbolKind::Parameter,
                name,
                owner,
                Detail::Parameter(Parameter {
                    ref_kind,
                    ref_readonly,
                    // It counts only where the module says it follows the
                    // ref safety rules of C# 11, which brought it.
                    unscoped_ref: self.has_attribute(
                        index,
                        table::MODULE,
                        1,
                        "System.Runtime.CompilerServices.RefSafetyRulesAttribute",
                    ) && row.is_some_and(|row| {
                        self.has_attribute(
                            index,
                            table::PARAM,
                            row,
                            "System.Diagnostics.CodeAnalysis.UnscopedRefAttribute",
                        )
                    }),
                    is_params,
                    // `[Optional]` alone makes a parameter optional too, with
                    // its type's default or what an attribute says.
                    has_default: flags & 0x1000 != 0 || (flags & 0x0010 != 0 && !is_params),
                    caller_info,
                    handler_arguments: row.and_then(|row| self.handler_arguments(index, row)),
                    ..Parameter::default()
                }),
            );
            if let Some(row) = row
                && let Some(value) = self.special_constant(index, table::PARAM, row)
            {
                self.loaded.special_constants.insert(id, value);
            }
            if let Some(row) = row
                && let Some(default) = self.com_default(index, row, flags)
            {
                self.loaded.com_defaults.insert(id, default);
            }
            let resolved = match row {
                Some(row) => {
                    let resolved = self.with_dynamic(
                        index,
                        table::PARAM,
                        row,
                        resolved,
                        ref_kind != RefKind::None,
                    );
                    self.with_tuple_names(index, table::PARAM, row, resolved)
                }
                None => resolved,
            };
            self.loaded.types.insert(id, resolved);
            if in_modifier && ref_kind == RefKind::In {
                self.loaded.in_modifiers.insert(id);
            }
            if let Some(Some(modifier)) = in_attribute {
                self.loaded.modifier_types.insert(id, modifier);
            }
            if let Some(value) =
                row.and_then(|row| self.indexes[index].parameter_constants.get(&row))
            {
                self.loaded.parameter_defaults.insert(id, value.clone());
            }
            if let Some(modifiers) = signature.parameters_modifiers.get(position)
                && !modifiers.is_empty()
            {
                let written = self.signature_modifiers(index, modifiers);
                self.loaded.custom_modifiers.insert(id, written);
            }
            ids.push(id);
        }
        ids
    }

    /// The `Param` row for one position of one method, where there is one.
    fn parameter_row(&self, index: usize, method: u32, sequence: u32) -> Option<u32> {
        let assembly = &self.assemblies[index];
        list_range(assembly, table::METHOD_DEF, method, 5, table::PARAM).find(|row| {
            assembly
                .table(table::PARAM)
                .row(*row)
                .is_some_and(|entry| entry.number(1) == sequence)
        })
    }

    /// The names and flags of one method's parameters, by position.
    fn parameter_names(&self, index: usize, method: u32) -> FxHashMap<u32, (String, u32)> {
        let assembly = &self.assemblies[index];
        let mut names = FxHashMap::default();
        for row in list_range(assembly, table::METHOD_DEF, method, 5, table::PARAM) {
            let Some(entry) = assembly.table(table::PARAM).row(row) else {
                continue;
            };
            // Sequence zero is the return value, which has no name to give.
            let sequence = entry.number(1);
            if sequence == 0 {
                continue;
            }
            names.insert(
                sequence,
                (
                    assembly.heaps().string(entry.number(2)).to_string(),
                    entry.number(0),
                ),
            );
        }
        names
    }

    // -- types -------------------------------------------------------------

    /// Turns a signature's type into the binder's.
    fn type_of_sig(
        &self,
        symbols: &impl Table,
        index: usize,
        sig: &TypeSig,
        scope: &Scope,
    ) -> Option<Type> {
        Some(match sig {
            TypeSig::Void => Type::Void,
            TypeSig::Boolean => self.special("System.Boolean")?,
            TypeSig::Char => self.special("System.Char")?,
            TypeSig::SByte => self.special("System.SByte")?,
            TypeSig::Byte => self.special("System.Byte")?,
            TypeSig::Int16 => self.special("System.Int16")?,
            TypeSig::UInt16 => self.special("System.UInt16")?,
            TypeSig::Int32 => self.special("System.Int32")?,
            TypeSig::UInt32 => self.special("System.UInt32")?,
            TypeSig::Int64 => self.special("System.Int64")?,
            TypeSig::UInt64 => self.special("System.UInt64")?,
            TypeSig::Single => self.special("System.Single")?,
            TypeSig::Double => self.special("System.Double")?,
            TypeSig::String => self.special("System.String")?,
            TypeSig::Object => self.special("System.Object")?,
            TypeSig::IntPtr => self.special("System.IntPtr")?,
            TypeSig::UIntPtr => self.special("System.UIntPtr")?,
            TypeSig::TypedReference => self.special("System.TypedReference")?,
            TypeSig::Class(token) | TypeSig::ValueType(token) => {
                self.type_of_token(symbols, index, *token, scope)?
            }
            TypeSig::Vector(element) => Type::Array {
                element: Box::new(self.type_of_sig(symbols, index, element, scope)?),
                rank: 1,
            },
            TypeSig::Array { element, rank } => Type::Array {
                element: Box::new(self.type_of_sig(symbols, index, element, scope)?),
                rank: *rank as usize,
            },
            TypeSig::Pointer(inner) => {
                Type::Pointer(Box::new(self.type_of_sig(symbols, index, inner, scope)?))
            }
            TypeSig::ByRef(inner) => {
                Type::ByRef(Box::new(self.type_of_sig(symbols, index, inner, scope)?))
            }
            // A signature never names a type parameter, it numbers one, and
            // the scope says which declaration the numbers belong to.
            TypeSig::Var(position) => {
                Type::TypeParameter(*scope.type_parameters.get(*position as usize)?)
            }
            TypeSig::MVar(position) => {
                Type::TypeParameter(*scope.method_parameters.get(*position as usize)?)
            }
            TypeSig::Generic {
                definition,
                arguments,
            } => {
                let symbol = self
                    .type_of_sig(symbols, index, definition, scope)?
                    .symbol()?;
                Type::Named {
                    symbol,
                    type_arguments: arguments
                        .iter()
                        .map(|argument| {
                            self.type_of_sig(symbols, index, argument, scope)
                                .unwrap_or(Type::Error)
                        })
                        .collect(),
                }
            }
            TypeSig::FunctionPointer(pointer) => {
                self.function_pointer_of(symbols, index, pointer, scope)?
            }
            TypeSig::Unknown(_) => Type::Error,
        })
    }

    /// A `delegate*` read back: a reference under `modreq(InAttribute)` is
    /// `in` (or `ref readonly` on the return), under `modreq(OutAttribute)`
    /// is `out`, and each `modopt(CallConv*)` on the return names a calling
    /// convention.
    fn function_pointer_of(
        &self,
        symbols: &impl Table,
        index: usize,
        pointer: &rustlyn_metadata::signature::FunctionPointerSig,
        scope: &Scope,
    ) -> Option<Type> {
        let named = |modifiers: &[Token], name: &str| {
            modifiers
                .iter()
                .any(|modifier| self.name_of(index, *modifier).as_deref() == Some(name))
        };
        let ref_kind = |sig: &TypeSig, modifiers: &[Token]| match sig {
            TypeSig::ByRef(_) if named(modifiers, "System.Runtime.InteropServices.InAttribute") => {
                RefKind::In
            }
            TypeSig::ByRef(_)
                if named(modifiers, "System.Runtime.InteropServices.OutAttribute") =>
            {
                RefKind::Out
            }
            TypeSig::ByRef(_) => RefKind::Ref,
            _ => RefKind::None,
        };
        let value = |sig: &TypeSig| match sig {
            TypeSig::ByRef(inner) => self.type_of_sig(symbols, index, inner, scope),
            other => self.type_of_sig(symbols, index, other, scope),
        };
        let signature = &pointer.signature;
        let mut parameters = Vec::with_capacity(signature.parameters.len());
        for (at, parameter) in signature.parameters.iter().enumerate() {
            let modifiers = signature
                .parameters_required
                .get(at)
                .map_or(&[][..], Vec::as_slice);
            parameters.push((ref_kind(parameter, modifiers), value(parameter)?));
        }
        const PREFIX: &str = "System.Runtime.CompilerServices.CallConv";
        let modifiers = pointer
            .returns_optional
            .iter()
            .filter_map(|modifier| {
                self.name_of(index, *modifier)?
                    .strip_prefix(PREFIX)
                    .map(str::to_string)
            })
            .collect();
        Some(Type::FunctionPointer(Box::new(
            crate::types::FunctionPointer {
                convention: pointer.convention,
                modifiers,
                returns: value(&signature.returns)?,
                returns_ref: ref_kind(&signature.returns, &signature.returns_required),
                parameters,
            },
        )))
    }

    /// A `TypeDef`, `TypeRef` or `TypeSpec` token as a type.
    fn type_of_token(
        &self,
        symbols: &impl Table,
        index: usize,
        token: Token,
        scope: &Scope,
    ) -> Option<Type> {
        match token.table() {
            table::TYPE_DEF => self.rows[index].get(&token.row()).copied().map(Type::named),
            table::TYPE_REF => {
                let name = self.name_of(index, token)?;
                // The assembly the reference names first; a type forwarded
                // elsewhere (everything `System.Runtime` names) is found by
                // its name alone.
                self.scope_assembly(index, token)
                    .and_then(|assembly| self.by_assembly.get(&(assembly, name.clone())))
                    .or_else(|| self.names.get(&name))
                    .copied()
                    .map(Type::named)
            }
            table::TYPE_SPEC => {
                let blob = self.assemblies[index]
                    .heaps()
                    .blob(self.assemblies[index].row(token)?.number(0))
                    .ok()?;
                let sig = Blob::new(blob).type_sig().ok()?;
                self.type_of_sig(symbols, index, &sig, scope)
            }
            _ => None,
        }
    }

    /// Whether a row carries an attribute of the given type.
    ///
    /// The attribute's arguments are not read: what these are asked about is
    /// whether the attribute is there at all.
    fn has_attribute(&self, index: usize, table: u8, row: u32, attribute: &str) -> bool {
        let Some(applied) = self.indexes[index].attributes.get(&(table, row)) else {
            return false;
        };
        applied
            .iter()
            .any(|(constructor, _)| self.is_attribute(index, *constructor, attribute))
    }

    /// The `decimal` or `DateTime` constant a row's attribute writes.
    /// What a COM attribute makes of the parameter in `row` left out, were
    /// it an `[Optional] object`: the `HasFieldMarshal` flag's descriptor
    /// first, then `[IUnknownConstant]`, then `[IDispatchConstant]`.
    fn com_default(&self, index: usize, row: u32, flags: u32) -> Option<ComDefault> {
        // `UnmanagedType.IUnknown`, `IDispatch` and `Interface`.
        if flags & 0x2000 != 0
            && let Some(0x19 | 0x1A | 0x1C) = self.indexes[index].parameter_marshals.get(&row)
        {
            return Some(ComDefault::Null);
        }
        let attributed = |name: &str| self.has_attribute(index, table::PARAM, row, name);
        if attributed("System.Runtime.CompilerServices.IUnknownConstantAttribute") {
            Some(ComDefault::UnknownWrapper)
        } else if attributed("System.Runtime.CompilerServices.IDispatchConstantAttribute") {
            Some(ComDefault::DispatchWrapper)
        } else {
            None
        }
    }

    fn special_constant(&self, index: usize, table: u8, row: u32) -> Option<SpecialConstant> {
        let applied = self.indexes[index].attributes.get(&(table, row))?;
        for (constructor, blob) in applied {
            let name = self.attribute_name(index, *constructor);
            let Ok(bytes) = self.assemblies[index].heaps().blob(*blob) else {
                continue;
            };
            let Some(bytes) = bytes.strip_prefix(&[0x01, 0x00]) else {
                continue;
            };
            let word = |at: usize| -> Option<u32> {
                Some(u32::from_le_bytes(bytes.get(at..at + 4)?.try_into().ok()?))
            };
            match name.as_deref() {
                Some("System.Runtime.CompilerServices.DecimalConstantAttribute") => {
                    return Some(SpecialConstant::Decimal {
                        scale: *bytes.first()?,
                        negative: *bytes.get(1)? != 0,
                        hi: word(2)?,
                        mid: word(6)?,
                        lo: word(10)?,
                    });
                }
                Some("System.Runtime.CompilerServices.DateTimeConstantAttribute") => {
                    let ticks = i64::from_le_bytes(bytes.get(0..8)?.try_into().ok()?);
                    // Ticks no `DateTime` can hold make no constant at all
                    // (Roslyn reads a bad one): the default goes unused.
                    if !(0..=3_155_378_975_999_999_999).contains(&ticks) {
                        return None;
                    }
                    return Some(SpecialConstant::DateTime(ticks));
                }
                _ => {}
            }
        }
        None
    }

    /// The strings an attribute was given, where all its arguments are ones.
    ///
    /// `[CollectionBuilder(typeof(ImmutableArray), "Create")]` is the reason
    /// this exists: a `System.Type` argument is written into the blob as the
    /// type's name, so both of its arguments are strings and nothing has to
    /// know the constructor's signature to read them (§II.23.3).
    /// The first string argument of every application of one attribute to
    /// a row: `[Conditional("A"), Conditional("B")]` gives both.
    fn every_attribute_string(
        &self,
        index: usize,
        table: u8,
        row: u32,
        attribute: &str,
    ) -> Vec<String> {
        let Some(applied) = self.indexes[index].attributes.get(&(table, row)) else {
            return Vec::new();
        };
        applied
            .iter()
            .filter(|(constructor, _)| self.is_attribute(index, *constructor, attribute))
            .filter_map(|(_, blob)| {
                let bytes = self.assemblies[index].heaps().blob(*blob).ok()?;
                let rest = bytes.strip_prefix(&[0x01, 0x00])?;
                serialized_string(rest).map(|(text, _)| text)
            })
            .collect()
    }

    fn attribute_strings(
        &self,
        index: usize,
        table: u8,
        row: u32,
        attribute: &str,
    ) -> Option<Vec<String>> {
        let applied = self.indexes[index].attributes.get(&(table, row))?;
        let blob = applied.iter().find_map(|(constructor, blob)| {
            (self.is_attribute(index, *constructor, attribute)).then_some(*blob)
        })?;
        let bytes = self.assemblies[index].heaps().blob(blob).ok()?;
        // Every one starts with the prolog 0x0001.
        let mut rest = bytes.strip_prefix(&[0x01, 0x00])?;
        let mut found = Vec::new();
        while !rest.is_empty() {
            // A count of named arguments ends the fixed ones, and two bytes
            // are all that is left when there are none.
            if rest.len() == 2 {
                break;
            }
            let (text, next) = serialized_string(rest)?;
            found.push(text);
            rest = next;
        }
        Some(found)
    }

    /// The names `[InterpolatedStringHandlerArgument]` on a parameter row
    /// gives. The attribute has two constructors, one taking a string and
    /// one a `params string[]`, and the blob is read as whichever of the two
    /// it reads as exactly (§II.23.3): an array's count is four bytes, a
    /// string's length one to four, and only one reading ends where the
    /// blob does.
    fn handler_arguments(&self, index: usize, row: u32) -> Option<Vec<String>> {
        const NAME: &str =
            "System.Runtime.CompilerServices.InterpolatedStringHandlerArgumentAttribute";
        let applied = self.indexes[index].attributes.get(&(table::PARAM, row))?;
        let blob = applied.iter().find_map(|(constructor, blob)| {
            self.is_attribute(index, *constructor, NAME)
                .then_some(*blob)
        })?;
        let bytes = self.assemblies[index].heaps().blob(blob).ok()?;
        let rest = bytes.strip_prefix(&[0x01, 0x00])?;
        // No named arguments follow: two zero bytes end the blob.
        let exact = |rest: &[u8]| rest == [0x00, 0x00];
        if let Some(count) = rest.get(..4).and_then(|count| count.try_into().ok()) {
            let count = u32::from_le_bytes(count);
            let mut names = Vec::new();
            let mut left = &rest[4..];
            let mut read = true;
            for _ in 0..count.min(256) {
                match serialized_string(left) {
                    Some((name, next)) => {
                        names.push(name);
                        left = next;
                    }
                    None => {
                        read = false;
                        break;
                    }
                }
            }
            if read && names.len() == count as usize && exact(left) {
                return Some(names);
            }
        }
        let (name, left) = serialized_string(rest)?;
        exact(left).then(|| vec![name])
    }

    /// What `[Obsolete]` on a row says (see [`Loaded::obsolete`]): `()`,
    /// `(string)` or `(string, bool)`, told apart by what follows the
    /// string — a `bool` byte before the two-byte count of named arguments,
    /// or the count itself.
    fn obsolete_of(&self, index: usize, table: u8, row: u32) -> Option<(Option<String>, bool)> {
        let applied = self.indexes[index].attributes.get(&(table, row))?;
        let blob = applied.iter().find_map(|(constructor, blob)| {
            self.is_attribute(index, *constructor, "System.ObsoleteAttribute")
                .then_some(*blob)
        })?;
        let bytes = self.assemblies[index].heaps().blob(blob).ok()?;
        if bytes.windows(12).any(|window| window == b"DiagnosticId") {
            return None;
        }
        let rest = bytes.strip_prefix(&[0x01, 0x00])?;
        if rest == [0x00, 0x00] {
            return Some((None, false));
        }
        let null = rest.first() == Some(&0xFF);
        let (message, next) = serialized_string(rest)?;
        let message = (!null && !message.is_empty()).then_some(message);
        // What a compiler writes to keep older compilers away from what they
        // would get wrong — a `ref struct`, a constructor of a type with
        // `required` members — is no deprecation to one that knows better,
        // and Roslyn reads past it.
        if message.as_deref().is_some_and(|message| {
            matches!(
                message,
                "Types with embedded references are not supported in this version of your compiler."
                    | "Constructors of types with required members are not supported in this version of your compiler."
            )
        }) {
            return None;
        }
        // A named argument starts with 0x53 (a field) or 0x54 (a property),
        // right after the count: two bytes on, or three after a `bool`.
        let named = |at: usize| next.get(at).is_none_or(|byte| matches!(byte, 0x53 | 0x54));
        let error = next.len() >= 3 && next[0] == 1 && named(3) && !named(2);
        Some((message, error))
    }

    /// The `int` an attribute was given as its one argument.
    fn attribute_int(&self, index: usize, table: u8, row: u32, attribute: &str) -> Option<i32> {
        let applied = self.indexes[index].attributes.get(&(table, row))?;
        let blob = applied.iter().find_map(|(constructor, blob)| {
            (self.attribute_name(index, *constructor).as_deref() == Some(attribute))
                .then_some(*blob)
        })?;
        let bytes = self.assemblies[index].heaps().blob(blob).ok()?;
        let rest = bytes.strip_prefix(&[0x01, 0x00])?;
        Some(i32::from_le_bytes(rest.get(..4)?.try_into().ok()?))
    }

    /// A type as C# wrote it: `dynamic` where the row's `[Dynamic]` says the
    /// `object` in metadata was one. The attribute's flags walk the type in
    /// pre-order, one per type and type argument, after one for a `ref`.
    fn with_dynamic(&self, index: usize, table: u8, row: u32, ty: Type, by_ref: bool) -> Type {
        let Some(flags) = self.dynamic_flags(index, table, row) else {
            return ty;
        };
        // Flags that do not number one per node of the type — the `ref`
        // counted — say nothing Roslyn will read, and the type stays as
        // written.
        if flags.len() != dynamic_positions(&ty) + usize::from(by_ref) {
            return ty;
        }
        let object = self.names.get("System.Object").copied();
        let mut at = usize::from(by_ref);
        apply_dynamic(ty, &flags, &mut at, object)
    }

    /// A type with the element names `[TupleElementNames]` on the row gives
    /// its tuples, which `ValueTuple<...>` in the signature cannot say.
    fn with_tuple_names(&self, index: usize, table: u8, row: u32, ty: Type) -> Type {
        let Some(applied) = self.indexes[index].attributes.get(&(table, row)) else {
            return ty;
        };
        let Some(blob) = applied.iter().find_map(|(constructor, blob)| {
            (self.is_attribute(
                index,
                *constructor,
                "System.Runtime.CompilerServices.TupleElementNamesAttribute",
            ))
            .then_some(*blob)
        }) else {
            return ty;
        };
        let Some(names) = self.assemblies[index]
            .heaps()
            .blob(blob)
            .ok()
            .and_then(decode_string_array)
        else {
            return ty;
        };
        let mut at = 0;
        apply_tuple_names(ty, &names, &mut at, &self.names)
    }

    /// The flags of a `[Dynamic]` on a row: `[Dynamic]` alone is one `true`.
    fn dynamic_flags(&self, index: usize, table: u8, row: u32) -> Option<Vec<bool>> {
        let applied = self.indexes[index].attributes.get(&(table, row))?;
        let blob = applied.iter().find_map(|(constructor, blob)| {
            (self.is_attribute(
                index,
                *constructor,
                "System.Runtime.CompilerServices.DynamicAttribute",
            ))
            .then_some(*blob)
        })?;
        let bytes = self.assemblies[index].heaps().blob(blob).ok()?;
        let rest = bytes.strip_prefix(&[0x01, 0x00])?;
        if rest.len() <= 2 {
            return Some(vec![true]);
        }
        let count = u32::from_le_bytes(rest.get(..4)?.try_into().ok()?) as usize;
        Some(
            rest.get(4..4 + count)?
                .iter()
                .map(|flag| *flag != 0)
                .collect(),
        )
    }

    /// Whether an attribute's constructor belongs to the type `name` names.
    ///
    /// Asked of every attribute on every member loaded, so the name is
    /// compared where it lies in the string heap rather than put together
    /// first.
    fn is_attribute(&self, index: usize, constructor: Token, name: &str) -> bool {
        let assembly = &self.assemblies[index];
        let owner = match constructor.table() {
            table::METHOD_DEF => match self.indexes[index].method_owner.get(&constructor.row()) {
                Some(owner) => Token::new(table::TYPE_DEF, *owner),
                None => return false,
            },
            table::MEMBER_REF => match assembly.row(constructor) {
                Some(row) => row.token(0),
                None => return false,
            },
            _ => return false,
        };
        let heaps = assembly.heaps();
        let Some(row) = assembly.row(owner) else {
            return false;
        };
        let (namespace, own) = match owner.table() {
            table::TYPE_DEF => (heaps.string(row.number(2)), heaps.string(row.number(1))),
            // A nested type's name is its enclosing type's and its own.
            table::TYPE_REF if row.token(0).table() != table::TYPE_REF => {
                (heaps.string(row.number(2)), heaps.string(row.number(1)))
            }
            _ => return self.attribute_name(index, constructor).as_deref() == Some(name),
        };
        if namespace.is_empty() {
            return name == own;
        }
        name.len() == namespace.len() + 1 + own.len()
            && name.starts_with(namespace)
            && name.as_bytes()[namespace.len()] == b'.'
            && name.ends_with(own)
    }

    /// The type an attribute's constructor belongs to, by name.
    fn attribute_name(&self, index: usize, constructor: Token) -> Option<String> {
        let assembly = &self.assemblies[index];
        match constructor.table() {
            table::METHOD_DEF => {
                let owner = *self.indexes[index].method_owner.get(&constructor.row())?;
                self.name_of(index, Token::new(table::TYPE_DEF, owner))
            }
            table::MEMBER_REF => {
                let parent = assembly.row(constructor)?.token(0);
                self.name_of(index, parent)
            }
            _ => None,
        }
    }

    /// The name of the assembly a `TypeRef` points into: the scope at the
    /// end of its chain of enclosing types, where that is an `AssemblyRef`.
    fn scope_assembly(&self, index: usize, token: Token) -> Option<String> {
        let assembly = &self.assemblies[index];
        let mut scope = assembly.row(token)?.token(0);
        for _ in 0..64 {
            match scope.table() {
                table::TYPE_REF => scope = assembly.row(scope)?.token(0),
                table::ASSEMBLY_REF => {
                    return Some(
                        assembly
                            .heaps()
                            .string(assembly.row(scope)?.number(6))
                            .to_string(),
                    );
                }
                _ => return None,
            }
        }
        None
    }

    /// Takes out the members C# cannot use (Roslyn calls them bad): an `in`
    /// parameter is under a `modreq(InAttribute)` exactly where its member
    /// is virtual or abstract, and a member where that does not hold is one
    /// no call can be bound to. A derived method that left the modifier out
    /// overrides nothing the runtime sees, and a call is left to the base's.
    fn withdraw_bad_members(&self, symbols: &mut Symbols) {
        let dispatched = |symbols: &Symbols, member: SymbolId| {
            let virtual_ = |id: SymbolId| {
                let modifiers = symbols.get(id).modifiers;
                modifiers.contains(Modifiers::VIRTUAL)
                    || modifiers.contains(Modifiers::ABSTRACT)
                    || modifiers.contains(Modifiers::OVERRIDE)
            };
            let symbol = symbols.get(member);
            virtual_(member)
                || symbol.as_property().is_some_and(|detail| {
                    detail.getter.is_some_and(virtual_) || detail.setter.is_some_and(virtual_)
                })
        };
        let mut bad = Vec::new();
        for rows in self.rows.iter() {
            for ty in rows.values() {
                for member in &symbols.get(*ty).members {
                    let symbol = symbols.get(*member);
                    let parameters = match (symbol.as_method(), symbol.as_property()) {
                        (Some(detail), _) => &detail.parameters,
                        (_, Some(detail)) => &detail.parameters,
                        _ => continue,
                    };
                    let virtual_ = dispatched(symbols, *member);
                    let mismatched = parameters.iter().any(|parameter| {
                        symbols
                            .get(*parameter)
                            .as_parameter()
                            .is_some_and(|detail| detail.ref_kind == RefKind::In)
                            && self.loaded.in_modifiers.contains(parameter) != virtual_
                    });
                    if mismatched {
                        bad.push(*member);
                    }
                }
            }
        }
        for member in bad {
            symbols.withdraw(member);
        }
    }

    /// A method metadata marks virtual without `NewSlot` overrides only a
    /// base method whose signature it matches exactly, custom modifiers
    /// included: the runtime compares them, and one that differs only there
    /// gets a slot of its own. Such a method is a new virtual one to C# too,
    /// which hides the base's.
    fn new_slots_for_mismatched_overrides(&self, symbols: &mut Symbols) {
        let mut demoted = Vec::new();
        for rows in self.rows.iter() {
            for ty in rows.values() {
                for method in symbols.get(*ty).members.clone() {
                    let symbol = symbols.get(method);
                    if !symbol.modifiers.contains(Modifiers::OVERRIDE)
                        || symbol.as_method().is_none()
                        || !self.loaded.custom_modifiers.contains_key(&method)
                            && !self.parameters_of(symbols, method).iter().any(|parameter| {
                                self.loaded.custom_modifiers.contains_key(parameter)
                            })
                    {
                        continue;
                    }
                    if self.overrides_by_types_only(symbols, *ty, method) {
                        demoted.push(method);
                    }
                }
            }
        }
        for method in demoted {
            let symbol = symbols.get_mut(method);
            symbol.modifiers =
                Modifiers::from_bits(symbol.modifiers.bits() & !Modifiers::OVERRIDE.bits())
                    .union(Modifiers::VIRTUAL);
        }
    }

    fn parameters_of(&self, symbols: &Symbols, method: SymbolId) -> Vec<SymbolId> {
        symbols
            .get(method)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default()
    }

    /// Whether some base method of the same name takes the same types but no
    /// base method of it carries the same modifiers as well.
    fn overrides_by_types_only(&self, symbols: &Symbols, ty: SymbolId, method: SymbolId) -> bool {
        let name = &symbols.get(method).name;
        let parameters = self.parameters_of(symbols, method);
        let modifiers_of = |symbol: SymbolId| self.loaded.custom_modifiers.get(&symbol);
        let mut by_types = false;
        let mut current = ty;
        for _ in 0..32 {
            let Some(base) = self
                .loaded
                .bases
                .get(&current)
                .and_then(|bases| bases.first())
                .and_then(Type::symbol)
            else {
                break;
            };
            for candidate in symbols.lookup(base, name) {
                let theirs = self.parameters_of(symbols, *candidate);
                if theirs.len() != parameters.len()
                    || theirs.iter().zip(&parameters).any(|(theirs, ours)| {
                        self.loaded.types.get(theirs) != self.loaded.types.get(ours)
                    })
                {
                    continue;
                }
                if modifiers_of(*candidate) == modifiers_of(method)
                    && theirs
                        .iter()
                        .zip(&parameters)
                        .all(|(theirs, ours)| modifiers_of(*theirs) == modifiers_of(*ours))
                {
                    return false;
                }
                by_types = true;
            }
            current = base;
        }
        by_types
    }

    /// The custom modifiers of a signature position as a writer names them
    /// again: by name and home assembly rather than by symbol, since the
    /// type a `modopt` names need be nothing any code can see.
    fn signature_modifiers(
        &self,
        index: usize,
        modifiers: &[rustlyn_metadata::CustomModifier],
    ) -> Vec<SignatureModifier> {
        let assembly = &self.assemblies[index];
        modifiers
            .iter()
            .filter_map(|modifier| {
                // `modopt(uint16)` names a primitive, which a `TypeSpec`
                // spells as its element type: the framework's type of that
                // name is the same one.
                if modifier.token.table() == table::TYPE_SPEC {
                    let blob = assembly
                        .heaps()
                        .blob(assembly.row(modifier.token)?.number(0))
                        .ok()?;
                    let name = match blob {
                        [0x02] => "System.Boolean",
                        [0x03] => "System.Char",
                        [0x04] => "System.SByte",
                        [0x05] => "System.Byte",
                        [0x06] => "System.Int16",
                        [0x07] => "System.UInt16",
                        [0x08] => "System.Int32",
                        [0x09] => "System.UInt32",
                        [0x0A] => "System.Int64",
                        [0x0B] => "System.UInt64",
                        [0x0C] => "System.Single",
                        [0x0D] => "System.Double",
                        [0x0E] => "System.String",
                        [0x18] => "System.IntPtr",
                        [0x19] => "System.UIntPtr",
                        [0x1C] => "System.Object",
                        _ => return None,
                    };
                    return Some(SignatureModifier {
                        required: modifier.required,
                        assembly: None,
                        name: name.to_string(),
                    });
                }
                let name = self.name_of(index, modifier.token)?;
                let home = match modifier.token.table() {
                    table::TYPE_DEF => self.references[index].clone(),
                    _ => {
                        let mut scope = assembly.row(modifier.token)?.token(0);
                        // As in `name_of`: a chain longer than the table
                        // has come round to itself.
                        let mut hops = assembly.rows(table::TYPE_REF);
                        while scope.table() == table::TYPE_REF {
                            hops = hops.checked_sub(1)?;
                            scope = assembly.row(scope)?.token(0);
                        }
                        (scope.table() == table::ASSEMBLY_REF)
                            .then(|| assembly.row(scope))
                            .flatten()
                            .map(|row| Reference {
                                name: assembly.heaps().string(row.number(6)).to_string(),
                                version: [
                                    row.number(0) as u16,
                                    row.number(1) as u16,
                                    row.number(2) as u16,
                                    row.number(3) as u16,
                                ],
                            })
                    }
                };
                Some(SignatureModifier {
                    required: modifier.required,
                    assembly: home,
                    name,
                })
            })
            .collect()
    }

    /// Whether the required modifiers in front of a type name `InAttribute`,
    /// and which one where it is not the framework's.
    fn in_attribute_modifier(
        &self,
        symbols: &impl Table,
        index: usize,
        modifiers: &[Token],
        scope: &Scope,
    ) -> Option<Option<SymbolId>> {
        let modifier = modifiers.iter().find(|modifier| {
            self.name_of(index, **modifier).as_deref()
                == Some("System.Runtime.InteropServices.InAttribute")
        })?;
        let resolved = self
            .type_of_token(symbols, index, *modifier, scope)
            .and_then(|ty| ty.symbol());
        let framework = self
            .names
            .get("System.Runtime.InteropServices.InAttribute")
            .copied();
        Some(resolved.filter(|symbol| Some(*symbol) != framework))
    }

    /// One of the types a signature spells with an element type of its own.
    fn special(&self, name: &str) -> Option<Type> {
        self.names.get(name).copied().map(Type::named)
    }
}

/// One length-prefixed UTF-8 string out of an attribute blob, and what is
/// left after it.
///
/// The length is a compressed unsigned integer, and `0xFF` alone means the
/// string is null rather than empty (§II.23.3).
fn serialized_string(bytes: &[u8]) -> Option<(String, &[u8])> {
    let (&first, rest) = bytes.split_first()?;
    if first == 0xFF {
        return Some((String::new(), rest));
    }
    let (length, rest) = if first & 0x80 == 0 {
        (u32::from(first), rest)
    } else if first & 0xC0 == 0x80 {
        let (&second, rest) = rest.split_first()?;
        (u32::from(first & 0x3F) << 8 | u32::from(second), rest)
    } else {
        let [second, third, fourth, rest @ ..] = rest else {
            return None;
        };
        (
            u32::from(first & 0x1F) << 24
                | u32::from(*second) << 16
                | u32::from(*third) << 8
                | u32::from(*fourth),
            rest,
        )
    };
    let length = length as usize;
    if rest.len() < length {
        return None;
    }
    let (text, rest) = rest.split_at(length);
    Some((String::from_utf8_lossy(text).into_owned(), rest))
}

/// Which type parameters are in scope while a signature is being read.
struct Scope {
    owner: SymbolId,
    type_parameters: Vec<SymbolId>,
    method_parameters: Vec<SymbolId>,
}

impl Scope {
    /// A type's parameters as a signature numbers them.
    ///
    /// A nested type repeats its enclosing type's parameters in its own
    /// `GenericParam` rows, so its list is already the whole list: walking up
    /// the chain would count the outer ones twice.
    fn new(symbols: &impl Table, owner: SymbolId, method_parameters: &[SymbolId]) -> Self {
        let type_parameters = symbols
            .get(owner)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        Self {
            owner,
            type_parameters,
            method_parameters: method_parameters.to_vec(),
        }
    }
}

// -- table indexing --------------------------------------------------------

fn index_of(assembly: &Assembly<'_>) -> Index {
    let heaps = assembly.heaps();
    let mut enclosing = FxHashMap::default();
    for row in assembly.table(table::NESTED_CLASS).iter() {
        enclosing.insert(row.number(0), row.number(1));
    }

    let mut type_parameters: FxHashMap<u32, Vec<(u32, String, u32, u32)>> = FxHashMap::default();
    let mut method_parameters: FxHashMap<u32, Vec<(u32, String, u32, u32)>> = FxHashMap::default();
    for (row, entry) in assembly.table(table::GENERIC_PARAM).iter().enumerate() {
        let owner = entry.token(2);
        let parameter = (
            entry.number(0),
            heaps.string(entry.number(3)).to_string(),
            row as u32 + 1,
            entry.number(1),
        );
        match owner.table() {
            table::TYPE_DEF => type_parameters
                .entry(owner.row())
                .or_default()
                .push(parameter),
            table::METHOD_DEF => method_parameters
                .entry(owner.row())
                .or_default()
                .push(parameter),
            _ => {}
        }
    }
    // The table is sorted by owner, not by position, so the numbers decide.
    let ordered = |mut map: FxHashMap<u32, Vec<(u32, String, u32, u32)>>|
     -> FxHashMap<u32, Vec<(String, u32, u32)>> {
        map.iter_mut()
            .for_each(|(_, list)| list.sort_by_key(|(number, ..)| *number));
        map.into_iter()
            .map(|(owner, list)| {
                (
                    owner,
                    list.into_iter()
                        .map(|(_, name, row, flags)| (name, row, flags))
                        .collect(),
                )
            })
            .collect()
    };

    let mut constraints: FxHashMap<u32, Vec<Token>> = FxHashMap::default();
    for row in assembly.table(table::GENERIC_PARAM_CONSTRAINT).iter() {
        constraints
            .entry(row.number(0))
            .or_default()
            .push(row.token(1));
    }

    // §II.22.9: a `HasConstant` parent tagged 0 is a `Field`. The blob is the
    // value in the little-endian form the element type says.
    // Tagged 1, a `Param`: an optional parameter's default value.
    let mut constants: FxHashMap<u32, ConstantValue> = FxHashMap::default();
    let mut parameter_constants: FxHashMap<u32, ConstantValue> = FxHashMap::default();
    for row in assembly.table(table::CONSTANT).iter() {
        let parent = row.number(2);
        let into = match parent & 0x0003 {
            0 => &mut constants,
            1 => &mut parameter_constants,
            _ => continue,
        };
        let Ok(bytes) = heaps.blob(row.number(3)) else {
            continue;
        };
        if let Some(value) = decode_constant(row.number(0) as u8, bytes) {
            into.insert(parent >> 2, value);
        }
    }

    let mut parameter_marshals = FxHashMap::default();
    for row in assembly.table(table::FIELD_MARSHAL).iter() {
        let parent = row.token(0);
        if parent.table() == table::PARAM
            && let Ok(&[native, ..]) = heaps.blob(row.number(1))
        {
            parameter_marshals.insert(parent.row(), native);
        }
    }

    let mut interfaces: FxHashMap<u32, Vec<(u32, Token)>> = FxHashMap::default();
    for (at, row) in assembly.table(table::INTERFACE_IMPL).iter().enumerate() {
        interfaces
            .entry(row.number(0))
            .or_default()
            .push((at as u32 + 1, row.token(1)));
    }

    let mut accessors = FxHashMap::default();
    let mut event_accessors = FxHashMap::default();
    for row in assembly.table(table::METHOD_SEMANTICS).iter() {
        let association = row.token(2);
        if association.table() == table::EVENT {
            let remover = match row.number(0) {
                0x0008 => false,
                0x0010 => true,
                _ => continue,
            };
            event_accessors.insert(row.number(1), (association.row(), remover));
            continue;
        }
        if association.table() != table::PROPERTY {
            continue;
        }
        let setter = match row.number(0) {
            0x0001 => true,
            0x0002 => false,
            _ => continue,
        };
        accessors.insert(row.number(1), (association.row(), setter));
    }

    // Getter before setter and adder before remover, so the order does not
    // depend on a hash.
    let mut property_accessors: FxHashMap<u32, Vec<(u32, bool)>> = FxHashMap::default();
    for (method, (property, setter)) in &accessors {
        property_accessors
            .entry(*property)
            .or_default()
            .push((*method, *setter));
    }
    let mut accessors_of_event: FxHashMap<u32, Vec<(u32, bool)>> = FxHashMap::default();
    for (method, (event, remover)) in &event_accessors {
        accessors_of_event
            .entry(*event)
            .or_default()
            .push((*method, *remover));
    }
    for list in property_accessors
        .values_mut()
        .chain(accessors_of_event.values_mut())
    {
        list.sort_unstable_by_key(|(method, second)| (*second, *method));
    }

    let mut method_owner = FxHashMap::default();
    for row in 1..=assembly.rows(table::TYPE_DEF) {
        for method in list_range(assembly, table::TYPE_DEF, row, 5, table::METHOD_DEF) {
            method_owner.insert(method, row);
        }
    }

    let mut attributes: FxHashMap<(u8, u32), Vec<(Token, u32)>> = FxHashMap::default();
    for row in assembly.table(table::CUSTOM_ATTRIBUTE).iter() {
        let parent = row.token(0);
        attributes
            .entry((parent.table(), parent.row()))
            .or_default()
            // The constructor says which attribute it is; the blob says what
            // it was given.
            .push((row.token(1), row.number(2)));
    }

    let mut properties = FxHashMap::default();
    for row in 1..=assembly.rows(table::PROPERTY_MAP) {
        let Some(entry) = assembly.table(table::PROPERTY_MAP).row(row) else {
            continue;
        };
        properties.insert(
            entry.number(0),
            list_range(assembly, table::PROPERTY_MAP, row, 1, table::PROPERTY).collect(),
        );
    }

    let mut events = FxHashMap::default();
    for row in 1..=assembly.rows(table::EVENT_MAP) {
        let Some(entry) = assembly.table(table::EVENT_MAP).row(row) else {
            continue;
        };
        events.insert(
            entry.number(0),
            list_range(assembly, table::EVENT_MAP, row, 1, table::EVENT).collect(),
        );
    }

    Index {
        enclosing,
        type_parameters: ordered(type_parameters),
        method_parameters: ordered(method_parameters),
        interfaces,
        accessors,
        property_accessors,
        events,
        event_accessors: event_accessors.keys().copied().collect(),
        accessors_of_event,
        properties,
        constants,
        parameter_constants,
        parameter_marshals,
        method_owner,
        attributes,
        constraints,
    }
}

/// How an assembly names itself, out of its own `Assembly` row.
fn reference_of(assembly: &Assembly<'_>) -> Option<Reference> {
    let row = assembly.table(table::ASSEMBLY).row(1)?;
    Some(Reference {
        name: assembly.heaps().string(row.number(7)).to_string(),
        version: [
            row.number(1) as u16,
            row.number(2) as u16,
            row.number(3) as u16,
            row.number(4) as u16,
        ],
    })
}

/// The run of rows a "list" column names.
///
/// A `TypeDef` says where its fields start and nothing says where they end:
/// the next row's start is the end, and the last row runs to the end of the
/// table. Every one-to-many relation in metadata is spelled this way.
fn list_range(
    assembly: &Assembly<'_>,
    owner: u8,
    row: u32,
    column: usize,
    target: u8,
) -> impl Iterator<Item = u32> + use<> {
    let table = assembly.table(owner);
    let start = table.row(row).map_or(0, |entry| entry.number(column));
    let end = match table.row(row + 1) {
        Some(next) => next.number(column),
        None => assembly.rows(target) + 1,
    };
    (start..end).filter(move |value| *value > 0)
}

// -- little helpers --------------------------------------------------------

const NOT_PUBLIC: u32 = 0x00;
const PUBLIC: u32 = 0x01;
const NESTED_PUBLIC: u32 = 0x02;
const NESTED_ASSEMBLY: u32 = 0x05;
const NESTED_FAM_AND_ASSEM: u32 = 0x06;
const NESTED_FAMILY: u32 = 0x04;
const NESTED_FAM_OR_ASSEM: u32 = 0x07;

/// Whether a member's access bits make it visible outside its assembly.
const fn is_visible(access: u32) -> bool {
    // 6 is `public`, 4 is `family`, 5 is `famORassem`.
    matches!(access, 4..=6)
}

const fn accessibility_of(access: u32) -> Accessibility {
    match access {
        1 => Accessibility::Private,
        2 => Accessibility::ProtectedAndInternal,
        3 => Accessibility::Internal,
        4 => Accessibility::Protected,
        5 => Accessibility::ProtectedOrInternal,
        6 => Accessibility::Public,
        _ => Accessibility::NotApplicable,
    }
}

fn type_modifiers(flags: u32) -> Modifiers {
    let mut modifiers = Modifiers::empty();
    if flags & 0x0080 != 0 {
        modifiers.insert(Modifiers::ABSTRACT);
    }
    if flags & 0x0100 != 0 {
        modifiers.insert(Modifiers::SEALED);
    }
    // A static class is how C# spells one that is both, and metadata has no
    // other way to say it.
    if flags & 0x0180 == 0x0180 {
        modifiers.insert(Modifiers::STATIC);
    }
    modifiers
}

fn method_modifiers(flags: u32) -> Modifiers {
    let mut modifiers = Modifiers::empty();
    if flags & 0x0010 != 0 {
        modifiers.insert(Modifiers::STATIC);
    }
    if flags & 0x0400 != 0 {
        modifiers.insert(Modifiers::ABSTRACT);
    }
    if flags & 0x0040 != 0 {
        // `NewSlot` introduces a method; without it a virtual one overrides.
        if flags & 0x0100 == 0 {
            modifiers.insert(Modifiers::OVERRIDE);
        } else {
            modifiers.insert(Modifiers::VIRTUAL);
        }
    }
    if flags & 0x0020 != 0 {
        modifiers.insert(Modifiers::SEALED);
    }
    modifiers
}

/// `List` out of `List\`1`, which is the name C# uses.
fn strip_arity(name: &str) -> &str {
    match name.rsplit_once('`') {
        Some((stem, arity)) if arity.chars().all(|c| c.is_ascii_digit()) => stem,
        _ => name,
    }
}

fn qualified(namespace: &str, name: &str) -> String {
    if namespace.is_empty() {
        name.to_string()
    } else {
        format!("{namespace}.{name}")
    }
}

/// Finds or makes the namespace a dotted name spells.
fn namespace_chain(symbols: &mut Symbols, global: SymbolId, namespace: &str) -> SymbolId {
    let mut container = global;
    if namespace.is_empty() {
        return container;
    }
    for part in namespace.split('.') {
        container = match symbols.lookup_namespace(container, part) {
            Some(found) => found,
            None => symbols.add(
                SymbolKind::Namespace,
                part,
                Some(container),
                Detail::Namespace,
            ),
        };
    }
    container
}

fn add_type_parameters(
    symbols: &mut impl Table,
    owner: SymbolId,
    names: &[(String, u32, u32)],
) -> Vec<SymbolId> {
    names
        .iter()
        .map(|(name, _, flags)| {
            symbols.add(
                SymbolKind::TypeParameter,
                name.clone(),
                Some(owner),
                Detail::TypeParameter(crate::symbol::TypeParameter {
                    // §II.23.1.7: the low two bits are the variance, and the
                    // three above them are `class`, `struct` and `new()`.
                    variance: match flags & 0x0003 {
                        1 => Variance::Out,
                        2 => Variance::In,
                        _ => Variance::None,
                    },
                    reference_type: flags & 0x0004 != 0,
                    value_type: flags & 0x0008 != 0,
                    constructor: flags & 0x0010 != 0,
                    // `AllowByRefLike` (.NET 9): `allows ref struct`.
                    allows_ref_struct: flags & 0x0020 != 0,
                    ..Default::default()
                }),
            )
        })
        .collect()
}

/// A `Constant` blob, read back as the value it stands for.
///
/// §II.23.1.16 numbers the element types and §II.22.9 lays the bytes out
/// little-endian. A string is UTF-16, which is what the heap holds.
fn decode_constant(element: u8, bytes: &[u8]) -> Option<ConstantValue> {
    let number = |width: usize| -> Option<u64> {
        let slice = bytes.get(..width)?;
        let mut value = 0u64;
        for (at, byte) in slice.iter().enumerate() {
            value |= u64::from(*byte) << (at * 8);
        }
        Some(value)
    };
    Some(match element {
        // ELEMENT_TYPE_BOOLEAN
        0x02 => ConstantValue::Boolean(number(1)? != 0),
        0x03 => ConstantValue::Char(char::from_u32(number(2)? as u32)?),
        0x04 => ConstantValue::Int32(number(1)? as u8 as i8 as i32),
        0x05 => ConstantValue::Int32(number(1)? as u8 as i32),
        0x06 => ConstantValue::Int32(number(2)? as u16 as i16 as i32),
        0x07 => ConstantValue::Int32(number(2)? as u16 as i32),
        0x08 => ConstantValue::Int32(number(4)? as u32 as i32),
        0x09 => ConstantValue::UInt32(number(4)? as u32),
        0x0A => ConstantValue::Int64(number(8)? as i64),
        0x0B => ConstantValue::UInt64(number(8)?),
        0x0C => ConstantValue::Single(f32::from_bits(number(4)? as u32)),
        0x0D => ConstantValue::Double(f64::from_bits(number(8)?)),
        0x0E => {
            let units: Vec<u16> = bytes
                .chunks_exact(2)
                .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
                .collect();
            ConstantValue::String(String::from_utf16(&units).ok()?)
        }
        // ELEMENT_TYPE_CLASS, which is only ever a null reference here.
        0x12 => ConstantValue::Null,
        _ => return None,
    })
}

/// Puts `dynamic` back where the flags of a `[Dynamic]` say an `object` was
/// one, walking the type in the order the flags were written.
/// How many flags of a `[Dynamic]` a type takes: one for itself, and one
/// for each node inside it, as [`apply_dynamic`] reads them.
fn dynamic_positions(ty: &Type) -> usize {
    1 + match ty {
        Type::Named { type_arguments, .. } => type_arguments.iter().map(dynamic_positions).sum(),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            dynamic_positions(element)
        }
        Type::Tuple(elements) => elements
            .iter()
            .map(|element| dynamic_positions(&element.ty))
            .sum(),
        _ => 0,
    }
}

fn apply_dynamic(ty: Type, flags: &[bool], at: &mut usize, object: Option<SymbolId>) -> Type {
    let flag = flags.get(*at).copied().unwrap_or(false);
    *at += 1;
    match ty {
        Type::Named {
            symbol,
            type_arguments,
        } if flag && type_arguments.is_empty() && Some(symbol) == object => Type::Dynamic,
        Type::Named {
            symbol,
            type_arguments,
        } => Type::Named {
            symbol,
            type_arguments: type_arguments
                .into_iter()
                .map(|argument| apply_dynamic(argument, flags, at, object))
                .collect(),
        },
        Type::Array { element, rank } => Type::Array {
            element: Box::new(apply_dynamic(*element, flags, at, object)),
            rank,
        },
        Type::Pointer(element) => {
            Type::Pointer(Box::new(apply_dynamic(*element, flags, at, object)))
        }
        Type::ByRef(element) => Type::ByRef(Box::new(apply_dynamic(*element, flags, at, object))),
        Type::Tuple(elements) => Type::Tuple(
            elements
                .into_iter()
                .map(|element| crate::types::TupleElement {
                    name: element.name,
                    ty: apply_dynamic(element.ty, flags, at, object),
                })
                .collect(),
        ),
        other => other,
    }
}

/// The `string[]` an attribute's only argument is: `null` elements where a
/// name was not given.
fn decode_string_array(blob: &[u8]) -> Option<Vec<Option<String>>> {
    let rest = blob.strip_prefix(&[0x01, 0x00])?;
    let count = u32::from_le_bytes(rest.get(..4)?.try_into().ok()?);
    let mut rest = rest.get(4..)?;
    let mut names = Vec::with_capacity(count as usize);
    for _ in 0..count {
        if rest.first() == Some(&0xFF) {
            names.push(None);
            rest = &rest[1..];
            continue;
        }
        let (name, next) = serialized_string(rest)?;
        names.push(Some(name));
        rest = next;
    }
    Some(names)
}

/// Turns each `ValueTuple<...>` in a type into the tuple it is, named as the
/// names of `[TupleElementNames]` say: one per element of every tuple, in
/// pre-order.
fn apply_tuple_names(
    ty: Type,
    names: &[Option<String>],
    at: &mut usize,
    known: &FxHashMap<String, SymbolId>,
) -> Type {
    match ty {
        Type::Named {
            symbol,
            type_arguments,
        } if (1..=7).contains(&type_arguments.len())
            && known.get(&format!("System.ValueTuple`{}", type_arguments.len()))
                == Some(&symbol) =>
        {
            let own: Vec<Option<String>> = (0..type_arguments.len())
                .map(|offset| names.get(*at + offset).cloned().flatten())
                .collect();
            *at += type_arguments.len();
            Type::Tuple(
                type_arguments
                    .into_iter()
                    .zip(own)
                    .map(|(argument, name)| crate::types::TupleElement {
                        name,
                        ty: apply_tuple_names(argument, names, at, known),
                    })
                    .collect(),
            )
        }
        Type::Named {
            symbol,
            type_arguments,
        } => Type::Named {
            symbol,
            type_arguments: type_arguments
                .into_iter()
                .map(|argument| apply_tuple_names(argument, names, at, known))
                .collect(),
        },
        Type::Array { element, rank } => Type::Array {
            element: Box::new(apply_tuple_names(*element, names, at, known)),
            rank,
        },
        Type::Pointer(element) => {
            Type::Pointer(Box::new(apply_tuple_names(*element, names, at, known)))
        }
        Type::ByRef(element) => {
            Type::ByRef(Box::new(apply_tuple_names(*element, names, at, known)))
        }
        other => other,
    }
}
