//! Symbols: what a name in the source actually refers to.
//!
//! Roslyn models these as a class hierarchy. Here they are one struct in an
//! arena with a kind-specific tail, because a compiler spends its life passing
//! symbols around by identity, and an index is the cheapest identity there is.
//! `SymbolId` is also stable, which matters once the binder starts caching.

use std::collections::HashMap;
use std::fmt;
use std::sync::{Mutex, OnceLock};

use rustlyn_text::TextSpan;

use crate::corlib::SpecialType;
use crate::fxhash::FxHashMap;

/// A symbol's identity inside one [`Symbols`] table.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId(pub(crate) u32);

impl SymbolId {
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// Whether the symbol was made while bodies were being bound rather than
    /// declared up front: a delegate type the language synthesizes for a
    /// lambda or a method group (§10.7.3 of C# 10) and its members.
    #[must_use]
    pub const fn is_late(self) -> bool {
        self.0 >= LATE_BASE
    }
}

/// Where the identities of symbols made after declaration start. They live
/// in a table of their own, which can grow behind a shared reference.
const LATE_BASE: u32 = 1 << 30;
const LATE_CHUNK: usize = 256;
const LATE_CHUNKS: usize = 256;

impl fmt::Debug for SymbolId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

/// What sort of thing a symbol is.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SymbolKind {
    Namespace,
    NamedType,
    Method,
    Field,
    Property,
    Event,
    Parameter,
    TypeParameter,
    Local,
}

/// Which flavour of type a named type is.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TypeKind {
    Class,
    Struct,
    Interface,
    Enum,
    Delegate,
    Record,
    RecordStruct,
}

impl TypeKind {
    /// Whether instances are held by reference.
    #[must_use]
    pub const fn is_reference_type(self) -> bool {
        matches!(
            self,
            Self::Class | Self::Interface | Self::Delegate | Self::Record
        )
    }
}

/// How widely a symbol can be seen.
///
/// Ordered from least to most visible, so `<` answers "is this narrower than".
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub enum Accessibility {
    #[default]
    NotApplicable,
    Private,
    /// `private protected`
    ProtectedAndInternal,
    Protected,
    Internal,
    /// `protected internal`
    ProtectedOrInternal,
    Public,
}

impl fmt::Display for Accessibility {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::NotApplicable => "",
            Self::Private => "private",
            Self::ProtectedAndInternal => "private protected",
            Self::Protected => "protected",
            Self::Internal => "internal",
            Self::ProtectedOrInternal => "protected internal",
            Self::Public => "public",
        })
    }
}

/// The modifiers a declaration carried, as a bit set.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Modifiers(u32);

impl Modifiers {
    pub const STATIC: Self = Self(1 << 0);
    pub const ABSTRACT: Self = Self(1 << 1);
    pub const SEALED: Self = Self(1 << 2);
    pub const VIRTUAL: Self = Self(1 << 3);
    pub const OVERRIDE: Self = Self(1 << 4);
    pub const READONLY: Self = Self(1 << 5);
    pub const CONST: Self = Self(1 << 6);
    pub const PARTIAL: Self = Self(1 << 7);
    pub const EXTERN: Self = Self(1 << 8);
    pub const UNSAFE: Self = Self(1 << 9);
    pub const ASYNC: Self = Self(1 << 10);
    pub const NEW: Self = Self(1 << 11);
    pub const VOLATILE: Self = Self(1 << 12);
    pub const REQUIRED: Self = Self(1 << 13);
    pub const FIXED: Self = Self(1 << 14);
    pub const REF: Self = Self(1 << 15);
    /// `file class C`: a type seen only in the file that declares it.
    pub const FILE: Self = Self(1 << 16);

    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The flags as a number, for writing out.
    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn from_bits(bits: u32) -> Self {
        Self(bits)
    }

    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    pub fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }
}

impl fmt::Debug for Modifiers {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names = [
            (Self::STATIC, "static"),
            (Self::ABSTRACT, "abstract"),
            (Self::SEALED, "sealed"),
            (Self::VIRTUAL, "virtual"),
            (Self::OVERRIDE, "override"),
            (Self::READONLY, "readonly"),
            (Self::CONST, "const"),
            (Self::PARTIAL, "partial"),
            (Self::EXTERN, "extern"),
            (Self::UNSAFE, "unsafe"),
            (Self::ASYNC, "async"),
            (Self::NEW, "new"),
            (Self::VOLATILE, "volatile"),
            (Self::REQUIRED, "required"),
            (Self::FIXED, "fixed"),
            (Self::REF, "ref"),
            (Self::FILE, "file"),
        ];
        let present: Vec<_> = names
            .iter()
            .filter(|(flag, _)| self.contains(*flag))
            .map(|(_, name)| *name)
            .collect();
        write!(f, "{}", present.join(" "))
    }
}

/// Where a symbol was declared.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Location {
    /// Which syntax tree of the compilation.
    pub tree: usize,
    /// The declaration's own span — the name, where there is one.
    pub span: TextSpan,
}

impl Location {
    #[must_use]
    pub const fn new(tree: usize, span: TextSpan) -> Self {
        Self { tree, span }
    }
}

/// A reference to type syntax that has not been resolved yet.
///
/// Declaration and resolution are separate passes for the reason Roslyn keeps
/// them separate: a field's type may be a class declared further down the file,
/// or in another file, so nothing can be resolved until everything is declared.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TypeSyntaxRef(pub Location);

impl TypeSyntaxRef {
    /// The reference of a symbol read from metadata, which has no syntax:
    /// the type it stands for was worked out while the assembly was read
    /// and is kept under the symbol (`Compilation::loaded_extended`). The
    /// location names no tree, and its span starts at the symbol's number.
    #[must_use]
    pub const fn loaded(symbol: SymbolId) -> Self {
        Self(Location::new(usize::MAX, TextSpan::new(symbol.0, 0)))
    }

    /// The symbol whose loaded type this refers to, where it is one.
    #[must_use]
    pub fn loaded_symbol(self) -> Option<SymbolId> {
        (self.0.tree == usize::MAX).then(|| SymbolId(self.0.span.start()))
    }
}

/// The part of a symbol that depends on what kind it is.
#[derive(Clone, Debug)]
pub enum Detail {
    Namespace,
    NamedType(NamedType),
    Method(Method),
    Field(Field),
    Property(Property),
    Event(Event),
    Parameter(Parameter),
    TypeParameter(TypeParameter),
    Local(Local),
}

#[derive(Clone, Debug, Default)]
pub struct NamedType {
    pub type_kind: Option<TypeKind>,
    /// How many type parameters, which is part of a type's identity: `List<T>`
    /// and `List<T, U>` are different types with the same name.
    pub arity: usize,
    pub type_parameters: Vec<SymbolId>,
    /// The base types and interfaces as written, before resolution.
    pub base_types: Vec<TypeSyntaxRef>,
    /// The underlying type of an enum, if one was written.
    pub enum_underlying: Option<TypeSyntaxRef>,
    /// `ref struct`: a value that may hold a reference into the stack, and so
    /// may never be a field of anything that is not one itself.
    pub ref_like: bool,
    /// The constructor a parameter list on the type itself declares (C# 12):
    /// `class Scope(DiagnosticAnalyzer analyzer)`. Its parameters are in
    /// scope in every instance member and initializer of the type.
    pub primary_constructor: Option<SymbolId>,
    /// `new { i = key, d }`: a class the language declares for the shape,
    /// generic in each property's type, with a constructor taking them in
    /// order.
    pub anonymous: bool,
    /// `union Pet(Cat, Dog);` (C# 15): a struct whose `Value` and constructors
    /// the language declares from the types in the list.
    pub union_declaration: bool,
    /// `[Union]` on a type read from metadata: a source type says so in its
    /// own declaration.
    pub union_attribute: bool,
    /// `[InterpolatedStringHandler]` (C# 10): an interpolated string converts
    /// to the type by making one and appending its pieces to it, rather
    /// than by being a string first.
    pub interpolated_string_handler: bool,
}

/// A type a synthesised member has that no syntax spells.
///
/// A record's `==` takes two of the record, its `Equals` takes an `object` and
/// its `ToString` gives back a `string`, and none of that is written anywhere
/// for a [`TypeSyntaxRef`] to point at.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SynthesizedType {
    /// One of the language's own: `string`, `bool`, `int`, `object`.
    Special(SpecialType),
    /// The type the member belongs to.
    Containing,
    /// The containing type's type parameter at this position: an anonymous
    /// type's property is of the parameter that stands for it.
    TypeParameter(usize),
    /// `string[]`: the `args` of a program's top-level statements.
    StringArray,
    /// `System.Threading.Tasks.Task`, and `Task<int>`: what top-level
    /// statements with an `await` in them return.
    Task,
    TaskOfInt32,
    /// `System.Type`: a record class's `EqualityContract`.
    SystemType,
    /// `System.Text.StringBuilder`: what a record's `PrintMembers` appends to.
    StringBuilder,
}

#[derive(Clone, Debug, Default)]
pub struct Method {
    pub return_type: Option<TypeSyntaxRef>,
    /// The return type when the language rather than the source decides it.
    pub synthesized_return: Option<SynthesizedType>,
    pub parameters: Vec<SymbolId>,
    pub type_parameters: Vec<SymbolId>,
    pub arity: usize,
    pub method_kind: MethodKind,
    /// Whether the first parameter was written `this`, which makes the method
    /// callable as if it were a member of that parameter's type.
    pub is_extension: bool,
    /// Whether it gives back a reference nothing may write through.
    ///
    /// `ref readonly T` is `T&` under a `modreq` naming `InAttribute`, and a
    /// reference to such a method has to carry the modifier or it names a
    /// method the runtime does not have.
    pub returns_readonly: bool,
    /// The type an extension block (C# 14) that declared the method extends:
    /// what `C.M()` names a static member of, and what an instance member's
    /// receiver is.
    pub extended: Option<TypeSyntaxRef>,
    /// Whether the method of an extension block is an instance member of it:
    /// the block's receiver is its first parameter, as in metadata.
    pub takes_receiver: bool,
    /// Whether it ends in `__arglist`: a varargs method, called with the
    /// types of what it is given past its parameters written at the call.
    pub is_vararg: bool,
}

/// What a method is for, which decides both its name and how it can be called.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum MethodKind {
    #[default]
    Ordinary,
    Constructor,
    StaticConstructor,
    Destructor,
    Operator,
    Conversion,
    LocalFunction,
    /// A member the language gives a record: `ToString`, `Equals`,
    /// `GetHashCode`, `==` and `Deconstruct`. Its body is decided by what the
    /// record holds rather than by anything written.
    RecordSynthesized,
    /// `get_X`, the method a property is read through.
    PropertyGet,
    /// `set_X`, the method it is written through.
    PropertySet,
}

#[derive(Clone, Debug, Default)]
pub struct Field {
    pub ty: Option<TypeSyntaxRef>,
    /// Whether the declaration gave it a value.
    pub has_initializer: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Property {
    pub ty: Option<TypeSyntaxRef>,
    /// The type when the language rather than the source decides it.
    pub synthesized: Option<SynthesizedType>,
    pub parameters: Vec<SymbolId>,
    pub has_get: bool,
    pub has_set: bool,
    pub has_init: bool,
    /// The field behind the property where an accessor body says `field`
    /// (C# 14): declared by the language rather than the source, typed as
    /// the property is, and named so that nothing in C# can collide with it.
    pub backing_field: Option<SymbolId>,
    /// Whether this is `this[...]` rather than a named property.
    pub is_indexer: bool,
    /// Whether it gives back a reference nothing may write through, which its
    /// signature spells with a `modreq` the same way a method's does.
    pub returns_readonly: bool,
    /// The methods the property is read and written through, where the
    /// declaration wrote a body for them.
    ///
    /// Roslyn gives every property a `GetMethod` and a `SetMethod` because
    /// that is what the CLI has; these are the same thing, declared under the
    /// property rather than under its type so that nothing can find them by
    /// name — C# forbids calling `get_X` directly.
    pub getter: Option<SymbolId>,
    pub setter: Option<SymbolId>,
    /// The accessibility an accessor narrowed itself to: `private set;`.
    pub get_accessibility: Option<Accessibility>,
    pub set_accessibility: Option<Accessibility>,
    /// The type an extension block (C# 14) that declared the property
    /// extends. An instance one takes the block's receiver as its first
    /// parameter, and is static in metadata like any extension method.
    pub extended: Option<TypeSyntaxRef>,
    /// The extension block's type parameters, which its accessors declare
    /// as their own in metadata.
    pub extension_generics: Vec<SymbolId>,
}

#[derive(Clone, Debug, Default)]
pub struct Event {
    pub ty: Option<TypeSyntaxRef>,
    /// The `add_E` and `remove_E` of an event read from metadata; a source
    /// event's are synthesized by the emitter and have no symbols.
    pub adder: Option<SymbolId>,
    pub remover: Option<SymbolId>,
}

/// A caller-info attribute on an optional parameter: the value the call
/// site fills in when it leaves the argument out (§22.5.6).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CallerInfo {
    /// `[CallerMemberName]`: the name of the member the call is written in.
    MemberName,
    /// `[CallerLineNumber]`: the line of the call.
    LineNumber,
    /// `[CallerFilePath]`: the path of the file the call is written in.
    FilePath,
    /// `[CallerArgumentExpression("name")]`: the text of the argument given
    /// for the named parameter.
    ArgumentExpression(String),
    /// `[CallerArgumentExpression(p)]` where `p` is a constant of the
    /// declaring type — a `const string p = nameof(p)` — whose value names
    /// the parameter: resolved where the call is bound.
    ArgumentConstant(String),
}

#[derive(Clone, Debug, Default)]
pub struct Parameter {
    pub ty: Option<TypeSyntaxRef>,
    /// The type when the language rather than the source decides it.
    pub synthesized: Option<SynthesizedType>,
    pub ref_kind: RefKind,
    /// Written `ref readonly` (C# 12) rather than `in`: the same `RefKind`,
    /// but marked `[RequiresLocation]` rather than `[IsReadOnly]` and told
    /// apart in the names of synthesized delegates.
    pub ref_readonly: bool,
    /// `[UnscopedRef]`: a reference that may escape further than its kind
    /// lets it by default, which a synthesized delegate has to say.
    pub unscoped_ref: bool,
    pub is_params: bool,
    pub has_default: bool,
    /// What the call site supplies for an omitted argument marked with a
    /// caller-info attribute (§22.5.6).
    pub caller_info: Option<CallerInfo>,
    /// `[InterpolatedStringHandlerArgument("a", "")]` (C# 10): the names of
    /// the parameters — `""` for the receiver — whose arguments the handler
    /// an interpolated string argument becomes is made with, after its two
    /// lengths.
    pub handler_arguments: Option<Vec<String>>,
    /// `[EnumeratorCancellation]`: the `CancellationToken` of an `async`
    /// iterator that the token handed to `GetAsyncEnumerator` is combined
    /// with (C# 8), so that either one cancels the walk.
    pub enumerator_cancellation: bool,
    /// The field a primary constructor's parameter is kept in when a member
    /// other than an initializer reads it (§15.11.1 of C# 12).
    pub captured: Option<SymbolId>,
    /// The name the declaring part of a partial method gave it, where the
    /// implementing part named it otherwise: callers name it so, and so
    /// does metadata, while the body goes by the implementing part's.
    pub declared_name: Option<String>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub enum RefKind {
    #[default]
    None,
    Ref,
    Out,
    In,
}

/// A type parameter, and what a `where` clause said it must be.
///
/// Without constraints a `T` has only the members of `object`; with them it
/// has the members of everything it is constrained to, which is what makes a
/// generic method able to do anything with its argument.
#[derive(Clone, Debug, Default)]
pub struct TypeParameter {
    pub constraints: Vec<TypeSyntaxRef>,
    /// `where T : struct`, which decides whether `T?` is a `Nullable<T>`.
    pub value_type: bool,
    /// `where T : class`.
    pub reference_type: bool,
    /// `where T : new()`.
    pub constructor: bool,
    /// `where T : allows ref struct` (C# 13): a `ref struct` may be the
    /// type argument.
    pub allows_ref_struct: bool,
    /// `where T : unmanaged` (C# 7.3), which is kept as `value_type` and
    /// this rather than as a constraint type: a `T` holds no references.
    pub unmanaged: bool,
    /// `out T` or `in T`, which says which way a construction converts.
    pub variance: Variance,
    /// The name the declaring part of a partial method gave it, where the
    /// implementing part named it otherwise: metadata goes by it.
    pub declared_name: Option<String>,
}

/// Which way a construction of a generic type converts along one of its
/// parameters.
///
/// `IEnumerable<out T>` gives values out and never takes one in, so an
/// `IEnumerable<string>` is safe to read as an `IEnumerable<object>`.
/// `IComparer<in T>` takes them in and never gives one out, so it goes the
/// other way. A parameter in both positions is neither.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Variance {
    #[default]
    None,
    /// `out T`
    Out,
    /// `in T`
    In,
}

#[derive(Clone, Debug, Default)]
pub struct Local {
    pub ty: Option<TypeSyntaxRef>,
}

/// One declared entity.
#[derive(Clone, Debug)]
pub struct Symbol {
    pub id: SymbolId,
    pub kind: SymbolKind,
    /// The name as written, without any arity suffix.
    pub name: String,
    pub container: Option<SymbolId>,
    pub members: Vec<SymbolId>,
    /// Every place this was declared. A partial type or a namespace has more
    /// than one.
    pub locations: Vec<Location>,
    pub accessibility: Accessibility,
    pub modifiers: Modifiers,
    pub detail: Detail,
}

impl Symbol {
    /// Every place in the trees this symbol points at: where it was
    /// declared, and each type written for it — for moving them where a
    /// tree was edited (`Compilation::with_tree_replaced`).
    pub(crate) fn for_each_location(&mut self, visit: &mut dyn FnMut(&mut Location)) {
        for location in &mut self.locations {
            visit(location);
        }
        let written = |reference: &mut Option<TypeSyntaxRef>,
                       visit: &mut dyn FnMut(&mut Location)| {
            if let Some(TypeSyntaxRef(location)) = reference {
                visit(location);
            }
        };
        match &mut self.detail {
            Detail::Namespace => {}
            Detail::NamedType(detail) => {
                for TypeSyntaxRef(location) in &mut detail.base_types {
                    visit(location);
                }
                written(&mut detail.enum_underlying, visit);
            }
            Detail::Method(detail) => {
                written(&mut detail.return_type, visit);
                written(&mut detail.extended, visit);
            }
            Detail::Field(detail) => written(&mut detail.ty, visit),
            Detail::Property(detail) => {
                written(&mut detail.ty, visit);
                written(&mut detail.extended, visit);
            }
            Detail::Event(detail) => written(&mut detail.ty, visit),
            Detail::Parameter(detail) => written(&mut detail.ty, visit),
            Detail::TypeParameter(detail) => {
                for TypeSyntaxRef(location) in &mut detail.constraints {
                    visit(location);
                }
            }
            Detail::Local(detail) => written(&mut detail.ty, visit),
        }
    }

    #[must_use]
    pub fn as_named_type(&self) -> Option<&NamedType> {
        match &self.detail {
            Detail::NamedType(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_method(&self) -> Option<&Method> {
        match &self.detail {
            Detail::Method(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_field(&self) -> Option<&Field> {
        match &self.detail {
            Detail::Field(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_property(&self) -> Option<&Property> {
        match &self.detail {
            Detail::Property(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_event(&self) -> Option<&Event> {
        match &self.detail {
            Detail::Event(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_type_parameter(&self) -> Option<&TypeParameter> {
        match &self.detail {
            Detail::TypeParameter(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_parameter(&self) -> Option<&Parameter> {
        match &self.detail {
            Detail::Parameter(detail) => Some(detail),
            _ => None,
        }
    }

    #[must_use]
    pub fn type_kind(&self) -> Option<TypeKind> {
        self.as_named_type().and_then(|detail| detail.type_kind)
    }

    /// The name as metadata spells it: `List`1` for `List<T>`.
    #[must_use]
    pub fn metadata_name(&self) -> String {
        match &self.detail {
            Detail::NamedType(detail) if detail.arity > 0 => {
                format!("{}`{}", self.name, detail.arity)
            }
            _ => self.name.clone(),
        }
    }
}

/// The arena every symbol of one compilation lives in.
#[derive(Clone, Debug)]
pub struct Symbols {
    pub(crate) symbols: Vec<Symbol>,
    /// Members by container and then by name, so lookup neither scans nor
    /// builds a key: a compiler looks a name up far more often than it
    /// declares one, and `(SymbolId, String)` would allocate on every one.
    pub(crate) index: FxHashMap<SymbolId, FxHashMap<String, Vec<SymbolId>>>,
    /// The symbols made while binding, which a body may need where the
    /// declarations could not know it would: the anonymous delegate type of
    /// `var f = (ref int x) => x;` exists because of what the lambda is.
    late: Late,
}

/// One symbol made after declaration, with its members by name.
#[derive(Clone, Debug)]
struct LateSymbol {
    symbol: Symbol,
    by_name: HashMap<String, Vec<SymbolId>>,
}

/// A run of late symbols, allocated the first time one of them is made.
type LateChunk = Box<[OnceLock<LateSymbol>]>;

/// An append-only table that hands out references which stay valid while it
/// grows, so that a symbol can be added through `&Symbols`.
#[derive(Debug)]
struct Late {
    chunks: Box<[OnceLock<LateChunk>]>,
    next: Mutex<u32>,
}

impl Late {
    fn new() -> Self {
        Self {
            chunks: (0..LATE_CHUNKS).map(|_| OnceLock::new()).collect(),
            next: Mutex::new(0),
        }
    }

    fn slot(&self, index: usize) -> &OnceLock<LateSymbol> {
        let chunk = self.chunks[index / LATE_CHUNK]
            .get_or_init(|| (0..LATE_CHUNK).map(|_| OnceLock::new()).collect());
        &chunk[index % LATE_CHUNK]
    }

    fn get(&self, id: SymbolId) -> Option<&LateSymbol> {
        let index = (id.0 - LATE_BASE) as usize;
        self.chunks.get(index / LATE_CHUNK)?.get()?[index % LATE_CHUNK].get()
    }
}

impl Clone for Late {
    fn clone(&self) -> Self {
        Self {
            chunks: self.chunks.clone(),
            next: Mutex::new(
                *self
                    .next
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
            ),
        }
    }
}

impl Default for Symbols {
    fn default() -> Self {
        Self::new()
    }
}

impl Symbols {
    #[must_use]
    pub fn new() -> Self {
        Self {
            symbols: Vec::new(),
            index: FxHashMap::default(),
            late: Late::new(),
        }
    }

    /// Builds the table from symbols and their index, as a snapshot reads
    /// them back.
    pub(crate) fn from_parts(
        symbols: Vec<Symbol>,
        index: FxHashMap<SymbolId, FxHashMap<String, Vec<SymbolId>>>,
    ) -> Self {
        Self {
            symbols,
            index,
            late: Late::new(),
        }
    }

    /// Reserves `count` identities for symbols made after declaration; the
    /// first is returned, and each has to be filled by [`Self::set_late`].
    pub(crate) fn reserve_late(&self, count: usize) -> Option<SymbolId> {
        let mut next = self
            .late
            .next
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let first = *next;
        let end = first.checked_add(u32::try_from(count).ok()?)?;
        if end as usize > LATE_CHUNK * LATE_CHUNKS {
            return None;
        }
        *next = end;
        Some(SymbolId(LATE_BASE + first))
    }

    /// Fills a reserved identity. Its members are looked up by name among
    /// `members`, which have to be filled already or be filled later with
    /// the names given here.
    pub(crate) fn set_late(&self, symbol: Symbol, members: &[(String, SymbolId)]) {
        let mut by_name: HashMap<String, Vec<SymbolId>> = HashMap::new();
        for (name, id) in members {
            by_name.entry(name.clone()).or_default().push(*id);
        }
        let index = (symbol.id.0 - LATE_BASE) as usize;
        let _ = self.late.slot(index).set(LateSymbol { symbol, by_name });
    }

    /// Adds a symbol and returns its identity.
    pub fn add(
        &mut self,
        kind: SymbolKind,
        name: impl Into<String>,
        container: Option<SymbolId>,
        detail: Detail,
    ) -> SymbolId {
        let id = SymbolId(self.symbols.len() as u32);
        let name = name.into();
        self.symbols.push(Symbol {
            id,
            kind,
            name: name.clone(),
            container,
            members: Vec::new(),
            locations: Vec::new(),
            accessibility: Accessibility::NotApplicable,
            modifiers: Modifiers::empty(),
            detail,
        });
        if let Some(container) = container {
            self.symbols[container.index()].members.push(id);
            self.index
                .entry(container)
                .or_default()
                .entry(name)
                .or_default()
                .push(id);
        }
        id
    }

    /// Adds a symbol that is one of its container's members but that nothing
    /// looks up by name there: a parameter of a method out of a referenced
    /// assembly, which is reached through the method's parameter list and
    /// never from inside a body, since no body of that method is bound.
    /// Loading a framework makes a hundred thousand of these, and a name
    /// index for each method's parameters was a sixth of loading it.
    pub(crate) fn add_unindexed(
        &mut self,
        kind: SymbolKind,
        name: String,
        container: SymbolId,
        detail: Detail,
    ) -> SymbolId {
        let id = SymbolId(self.symbols.len() as u32);
        self.symbols.push(Symbol {
            id,
            kind,
            name,
            container: Some(container),
            members: Vec::new(),
            locations: Vec::new(),
            accessibility: Accessibility::NotApplicable,
            modifiers: Modifiers::empty(),
            detail,
        });
        self.symbols[container.index()].members.push(id);
        id
    }

    /// Takes a member out of its container, where no lookup finds it again.
    /// The symbol itself stays, for whatever already refers to it.
    pub fn withdraw(&mut self, id: SymbolId) {
        let Some(container) = self.symbols[id.index()].container else {
            return;
        };
        let name = self.symbols[id.index()].name.clone();
        self.symbols[container.index()]
            .members
            .retain(|member| *member != id);
        if let Some(found) = self
            .index
            .get_mut(&container)
            .and_then(|members| members.get_mut(&name))
        {
            found.retain(|member| *member != id);
        }
    }

    /// Makes room for this many more symbols.
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.symbols.reserve(additional);
    }

    /// Appends a symbol made elsewhere and numbered as the next one, as
    /// [`Symbols::add`] would have added it: put among its container's
    /// members where `link` says it is not there yet, and into the name index
    /// where `indexed`.
    pub(crate) fn push_made(&mut self, symbol: Symbol, link: bool, indexed: bool) {
        debug_assert_eq!(symbol.id.index(), self.symbols.len());
        let (id, container) = (symbol.id, symbol.container);
        let name = indexed.then(|| symbol.name.clone());
        self.symbols.push(symbol);
        if let Some(container) = container {
            if link {
                self.symbols[container.index()].members.push(id);
            }
            if let Some(name) = name {
                self.index
                    .entry(container)
                    .or_default()
                    .entry(name)
                    .or_default()
                    .push(id);
            }
        }
    }

    /// Renames a symbol, keeping the per-container name index in step.
    pub fn rename(&mut self, id: SymbolId, name: impl Into<String>) {
        let name = name.into();
        let symbol = &mut self.symbols[id.index()];
        if symbol.name == name {
            return;
        }
        let old = std::mem::replace(&mut symbol.name, name.clone());
        if let Some(container) = symbol.container
            && let Some(members) = self.index.get_mut(&container)
        {
            if let Some(ids) = members.get_mut(&old) {
                ids.retain(|member| *member != id);
                if ids.is_empty() {
                    members.remove(&old);
                }
            }
            members.entry(name).or_default().push(id);
        }
    }

    /// Takes a symbol out of its container's members and name index, for a
    /// declaration another one stands for: the defining part of a partial
    /// property, once its implementing part is declared. The symbol stays,
    /// and nothing finds it through the container any more.
    pub fn detach(&mut self, id: SymbolId) {
        let Some(container) = self.symbols[id.index()].container else {
            return;
        };
        let name = self.symbols[id.index()].name.clone();
        self.symbols[container.index()]
            .members
            .retain(|member| *member != id);
        if let Some(members) = self.index.get_mut(&container)
            && let Some(ids) = members.get_mut(&name)
        {
            ids.retain(|member| *member != id);
            if ids.is_empty() {
                members.remove(&name);
            }
        }
    }

    #[must_use]
    pub fn get(&self, id: SymbolId) -> &Symbol {
        if id.is_late() {
            return &self
                .late
                .get(id)
                .expect("a late symbol is filled before its identity is handed out")
                .symbol;
        }
        &self.symbols[id.index()]
    }

    pub fn get_mut(&mut self, id: SymbolId) -> &mut Symbol {
        &mut self.symbols[id.index()]
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.iter()
    }

    /// Takes a member out of its container: it is no longer found by name
    /// or listed among the container's members, though its record stays.
    pub(crate) fn unlink(&mut self, member: SymbolId) {
        let Some(container) = self.symbols[member.index()].container else {
            return;
        };
        let name = self.symbols[member.index()].name.clone();
        self.symbols[container.index()]
            .members
            .retain(|id| *id != member);
        if let Some(named) = self
            .index
            .get_mut(&container)
            .and_then(|members| members.get_mut(&name))
        {
            named.retain(|id| *id != member);
        }
    }

    /// The members of `container` called `name`.
    ///
    /// More than one comes back for overloads, and for a type and a method that
    /// share a name.
    #[must_use]
    pub fn lookup(&self, container: SymbolId, name: &str) -> &[SymbolId] {
        if container.is_late() {
            return self
                .late
                .get(container)
                .and_then(|late| late.by_name.get(name))
                .map_or(&[], Vec::as_slice);
        }
        self.index
            .get(&container)
            .and_then(|members| members.get(name))
            .map_or(&[], Vec::as_slice)
    }

    /// The tree a file-local type (`file class C`) belongs to: it is seen
    /// only there. `None` for any other symbol.
    #[must_use]
    pub fn file_of(&self, id: SymbolId) -> Option<usize> {
        let symbol = self.get(id);
        if !symbol.modifiers.contains(Modifiers::FILE) {
            return None;
        }
        symbol.locations.first().map(|location| location.tree)
    }

    /// Whether a type is seen from `tree`: any type but one that is
    /// local to another file.
    #[must_use]
    pub fn visible_from(&self, id: SymbolId, tree: usize) -> bool {
        self.file_of(id).is_none_or(|file| file == tree)
    }

    /// The type of `container` called `name` with `arity` type parameters
    /// that code in `tree` sees: a file-local type of another file is not
    /// one (Roslyn's `IsInScopeOfAssociatedSyntaxTree`), and one of this
    /// file comes before any other.
    #[must_use]
    pub fn lookup_type_from(
        &self,
        container: SymbolId,
        name: &str,
        arity: usize,
        tree: usize,
    ) -> Option<SymbolId> {
        let mut found = None;
        for &id in self.lookup(container, name) {
            let symbol = self.get(id);
            if symbol.kind != SymbolKind::NamedType
                || symbol.as_named_type().is_none_or(|d| d.arity != arity)
                || !self.visible_from(id, tree)
            {
                continue;
            }
            if self.file_of(id).is_some() {
                return Some(id);
            }
            found = found.or(Some(id));
        }
        found
    }

    /// The one member of `container` called `name` with `arity` type
    /// parameters, if there is exactly one.
    #[must_use]
    pub fn lookup_type(&self, container: SymbolId, name: &str, arity: usize) -> Option<SymbolId> {
        self.lookup(container, name).iter().copied().find(|id| {
            let symbol = self.get(*id);
            symbol.kind == SymbolKind::NamedType
                && symbol.as_named_type().is_some_and(|d| d.arity == arity)
        })
    }

    /// The child namespace of `container` called `name`.
    #[must_use]
    pub fn lookup_namespace(&self, container: SymbolId, name: &str) -> Option<SymbolId> {
        self.lookup(container, name)
            .iter()
            .copied()
            .find(|id| self.get(*id).kind == SymbolKind::Namespace)
    }

    /// The name metadata gives a symbol: like [`Symbols::qualified_name`],
    /// but with `+` where a type is nested in another.
    ///
    /// The distinction matters only to a writer of metadata, and there it
    /// matters entirely: a nested type's `TypeRef` is scoped to its enclosing
    /// type's rather than to an assembly, and a dotted name cannot say which
    /// of its parts are namespaces.
    #[must_use]
    pub fn metadata_qualified_name(&self, id: SymbolId) -> String {
        let symbol = self.get(id);
        let mut name = symbol.metadata_name();
        let mut current = symbol.container;
        let mut nested = symbol.kind == SymbolKind::NamedType;
        while let Some(container) = current {
            let parent = self.get(container);
            if !parent.name.is_empty() {
                let separator = if nested && parent.kind == SymbolKind::NamedType {
                    '+'
                } else {
                    '.'
                };
                name = format!("{}{separator}{name}", parent.metadata_name());
            }
            nested = parent.kind == SymbolKind::NamedType;
            current = parent.container;
        }
        name
    }

    /// The dotted name a symbol has from the global namespace down, as
    /// diagnostics and tests spell it.
    #[must_use]
    pub fn qualified_name(&self, id: SymbolId) -> String {
        let symbol = self.get(id);
        let mut parts = vec![symbol.metadata_name()];
        let mut current = symbol.container;
        while let Some(container) = current {
            let parent = self.get(container);
            // The global namespace has no name and contributes no dot.
            if !parent.name.is_empty() {
                parts.push(parent.metadata_name());
            }
            current = parent.container;
        }
        parts.reverse();
        parts.join(".")
    }
}
