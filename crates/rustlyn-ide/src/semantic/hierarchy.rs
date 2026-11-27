//! The questions an editor asks about how declarations hang together rather
//! than about one name: what type a thing has, what a type derives from and
//! what derives from it, what a member overrides and what overrides it, and
//! who calls what.
//!
//! Every answer here is worked out from the compilation's symbols, not from
//! the words a declaration was written with. `class Circle : Shape` names
//! `Shape` as a word; the compiler knows which `Shape`, and knows that
//! `Circle.Area` overrides `Shape.Area` because their signatures are the
//! same once `Shape<T>`'s `T` is replaced by what `Circle` gave it. That is
//! the difference between these answers and the index's: the index guesses
//! from spelling, and is wrong exactly where two types share a name.
//!
//! Members are matched the way C# matches them (§15.6.5, §19.6.5): the same
//! name, the same kind, the same number of type parameters, and the same
//! parameter types after substituting the type arguments the derived type
//! supplied. Explicit interface implementations are named after the
//! interface they implement — `IShape.Area` — and are matched on that.
//!
//! Call hierarchy reads the bound bodies. Binding records, for every name in
//! a body, the symbol it settled on, keyed by the name's span: the overload
//! a call chose, the constructor a `new` runs, the property an access reads.
//! Looking for callers is then the same search [`Semantic::references`] does
//! — spelling first, binding only the files the word is in — and looking at
//! callees is reading one member's table.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use rustlyn_semantics::{
    BoundBody, BoundStatementKind, MethodKind, Modifiers, SemanticModel, SymbolId, SymbolKind,
    Type, TypeKind, is_body_owner,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::implicit::UseKind;
use super::references::use_kind_of;
use super::{
    Found, Place, Resolved, Semantic, View, attribute_stem, contains_word, declaration_kind,
    describe_symbol, parallel,
};
use crate::outline::DeclarationKind;

/// A declaration as a hierarchy view lists it: a node that can be expanded
/// into its callers, its callees, its base types or its derived types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HierarchyItem {
    pub symbol: SymbolId,
    /// The name as written: `Area`, `Circle`, `IShape.Area` for an explicit
    /// implementation. A constructor goes by its type's name.
    pub name: String,
    pub kind: DeclarationKind,
    /// The signature: `double Area()`, `class Circle`.
    pub detail: String,
    /// The type or namespace it is in, qualified.
    pub container: String,
    /// What finds this symbol again, in this compilation or the next one:
    /// see [`Semantic::symbol_key`].
    pub key: String,
    /// Where its name is, which is what a jump selects. `None` for what has
    /// no place anyone can go to, such as a type the compiler made up.
    pub place: Option<Place>,
    /// The whole declaration, in the same file as `place`, for a source
    /// declaration.
    pub full: Option<TextSpan>,
}

/// A member that calls the one asked about, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IncomingCall {
    pub from: HierarchyItem,
    /// The file the calls are in, which is the caller's.
    pub path: PathBuf,
    /// The name of each call, in bytes; for a use no name stands for, the
    /// start of the construct (`a + b`, `m[3]`, `new()`, `foreach`).
    pub spans: Vec<TextSpan>,
    /// How each of `spans` uses the target, in the same order: a property's
    /// or an indexer's getter and setter are different code, and a call that
    /// only assigns does not run the getter.
    pub uses: Vec<UseKind>,
    /// Whether these calls name a member the target overrides or implements
    /// rather than the target itself: `shape.Area()` is a call to
    /// `IShape.Area` that may run `Circle.Area`. Roslyn lists these apart,
    /// as calls to the base member.
    pub through_base: bool,
}

/// A member the one asked about calls, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutgoingCall {
    pub to: HierarchyItem,
    /// The file the calls are in, which is the caller's.
    pub path: PathBuf,
    pub spans: Vec<TextSpan>,
}

/// A base type or interface, with what its type parameters stand for when
/// seen from the type it was reached from: `Shape<double>` reached from
/// `Circle` maps `Shape`'s `T` to `double`.
#[derive(Clone, Debug)]
pub(super) struct Supertype {
    pub(super) symbol: SymbolId,
    pub(super) arguments: HashMap<SymbolId, Type>,
}

impl Semantic {
    // MARK: - go to type definition

    /// Where the type of whatever is at `offset` is declared: a variable's
    /// type, a method's return type, a type itself.
    ///
    /// An array, a pointer or a `ref` leads to its element type, and a
    /// nullable value type to what it wraps. A constructed generic type
    /// leads to its definition and then to each type argument's, so that
    /// `List<Order> orders` offers `List<T>` and `Order` both, as Roslyn
    /// does.
    #[must_use]
    pub fn type_definition(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(String, Vec<Found>)> {
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        let resolved = view.resolve(&token)?;
        let model = SemanticModel::new(&self.compilation, 0);
        let ty = match &resolved {
            Resolved::Local { ty, .. } => ty.clone(),
            Resolved::Symbol(symbol) => match view.type_of_named(&token, *symbol) {
                Some(ty) => ty,
                None => self.navigable_type(&model, *symbol)?,
            },
        };
        let mut types = Vec::new();
        self.types_in(&ty, &mut types);
        let mut found = self.places_of_all(&types);
        view.move_into_edited(path, &Resolved::Symbol(types.first().copied()?), &mut found);
        Some((token.value_text().to_string(), found))
    }

    /// The type a symbol is, holds or returns.
    fn navigable_type(&self, model: &SemanticModel<'_>, symbol: SymbolId) -> Option<Type> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        match found.kind {
            SymbolKind::NamedType => Some(Type::named(symbol)),
            SymbolKind::TypeParameter => Some(Type::TypeParameter(symbol)),
            SymbolKind::Namespace => None,
            SymbolKind::Method
                if found
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::Constructor) =>
            {
                found.container.map(Type::named)
            }
            _ => Some(model.type_of_symbol(symbol)),
        }
    }

    /// The declarations a type is made of, the outermost first.
    fn types_in(&self, ty: &Type, into: &mut Vec<SymbolId>) {
        let push = |symbol: SymbolId, into: &mut Vec<SymbolId>| {
            if !into.contains(&symbol) {
                into.push(symbol);
            }
        };
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                // `int?` is `Nullable<int>`, and what the reader wrote, and
                // wants, is `int`.
                let nullable = self
                    .compilation
                    .type_by_metadata_name("System.Nullable`1")
                    .is_some_and(|nullable| nullable == *symbol);
                if !nullable {
                    push(*symbol, into);
                }
                for argument in type_arguments {
                    self.types_in(argument, into);
                }
            }
            Type::TypeParameter(symbol) => push(*symbol, into),
            Type::Array { element, .. } => self.types_in(element, into),
            Type::Pointer(element) | Type::ByRef(element) => self.types_in(element, into),
            Type::Tuple(elements) => {
                for element in elements {
                    self.types_in(&element.ty, into);
                }
            }
            Type::FunctionPointer(pointer) => {
                for ty in pointer.types() {
                    self.types_in(ty, into);
                }
            }
            Type::Error | Type::Null | Type::Void | Type::Dynamic => {}
        }
    }

    /// Every declaration of every symbol, in order, without repeats.
    fn places_of_all(&self, symbols: &[SymbolId]) -> Vec<Found> {
        let mut found: Vec<Found> = Vec::new();
        for &symbol in symbols {
            for place in self.declarations_of(symbol) {
                if !found.contains(&place) {
                    found.push(place);
                }
            }
        }
        found
    }

    /// What the cursor is on, as a symbol: a local has none, and is taken
    /// as its type where a type will do.
    pub(super) fn symbol_at(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(View<'_>, String, SymbolId)> {
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        let symbol = match view.resolve(&token)? {
            Resolved::Symbol(symbol) => view.most_derived(&token, symbol),
            Resolved::Local { .. } => return None,
        };
        Some((view, token.value_text().to_string(), symbol))
    }

    /// Runs `answer` on the symbol at the cursor and gives back where what
    /// it found is declared, in the editor's text.
    fn places_for(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        answer: impl FnOnce(SymbolId) -> Vec<SymbolId>,
    ) -> Option<(String, Vec<Found>)> {
        let (view, word, symbol) = self.symbol_at(path, offset, text)?;
        let symbols = answer(symbol);
        let mut found = self.places_of_all(&symbols);
        view.move_into_edited(path, &Resolved::Symbol(symbol), &mut found);
        Some((word, found))
    }

    // MARK: - go to base

    /// What whatever is at `offset` derives from: for a type, its base
    /// classes and every interface, nearest first; for a member, the member
    /// it overrides, what that overrides in turn, and the interface members
    /// any of them implement.
    #[must_use]
    pub fn bases(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(String, Vec<Found>)> {
        self.places_for(path, offset, text, |symbol| self.base_symbols(symbol))
    }

    /// The symbols [`Self::bases`] leads to.
    #[must_use]
    pub fn base_symbols(&self, symbol: SymbolId) -> Vec<SymbolId> {
        let model = SemanticModel::new(&self.compilation, 0);
        let symbols = self.compilation.symbols();
        let symbol = self.callable(symbol).unwrap_or(symbol);
        match symbols.get(symbol).kind {
            SymbolKind::NamedType => {
                let all = self.supertypes(&model, symbol);
                // The class chain first, then the interfaces: nearest first
                // within each, as the walk found them.
                let (classes, interfaces): (Vec<_>, Vec<_>) =
                    all.into_iter().partition(|supertype| {
                        symbols.get(supertype.symbol).type_kind() != Some(TypeKind::Interface)
                    });
                classes
                    .into_iter()
                    .chain(interfaces)
                    .map(|supertype| supertype.symbol)
                    .collect()
            }
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Event => {
                let mut chain = vec![symbol];
                while let Some(&last) = chain.last()
                    && let Some(overridden) = self.overridden(&model, last)
                    && !chain.contains(&overridden)
                {
                    chain.push(overridden);
                }
                let mut found: Vec<SymbolId> = chain[1..].to_vec();
                for &member in &chain {
                    for implemented in self.implemented(&model, member) {
                        if !found.contains(&implemented) {
                            found.push(implemented);
                        }
                    }
                }
                found
            }
            _ => Vec::new(),
        }
    }

    // MARK: - go to implementation

    /// What implements whatever is at `offset`: the classes and structs that
    /// implement an interface or derive from a class, the overrides of a
    /// virtual member and the implementations of an interface member —
    /// across the whole project, however indirectly. Only what has a body
    /// counts; an abstract class or member is not an implementation. A
    /// member that nothing can override is its own implementation.
    #[must_use]
    pub fn implementations(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(String, Vec<Found>)> {
        self.places_for(path, offset, text, |symbol| {
            self.implementation_symbols(symbol)
        })
    }

    /// The symbols [`Self::implementations`] leads to.
    #[must_use]
    pub fn implementation_symbols(&self, symbol: SymbolId) -> Vec<SymbolId> {
        let model = SemanticModel::new(&self.compilation, 0);
        let symbols = self.compilation.symbols();
        let symbol = self.callable(symbol).unwrap_or(symbol);
        let found = symbols.get(symbol);
        let is_abstract = |symbol: SymbolId| {
            let found = symbols.get(symbol);
            found.modifiers.contains(Modifiers::ABSTRACT)
                || found.type_kind() == Some(TypeKind::Interface)
                || found.container.is_some_and(|container| {
                    symbols.get(container).type_kind() == Some(TypeKind::Interface)
                        && !self.has_body(symbol)
                })
        };
        let mut result: Vec<SymbolId> = match found.kind {
            SymbolKind::NamedType => {
                let derived = self.derived(symbol, true);
                std::iter::once(symbol)
                    .chain(derived.into_iter().filter(|&derived| {
                        symbols.get(derived).type_kind() != Some(TypeKind::Interface)
                    }))
                    .collect()
            }
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Event => {
                let mut all = vec![symbol];
                all.extend(self.member_implementations(&model, symbol));
                all
            }
            _ => vec![symbol],
        };
        result.retain(|&symbol| !is_abstract(symbol));
        result
    }

    /// Whether a member was written with a body: a default interface
    /// method has one, an ordinary interface member does not.
    fn has_body(&self, symbol: SymbolId) -> bool {
        self.compilation
            .declaration_node(symbol)
            .is_some_and(|node| {
                node.descendants().any(|child| {
                    matches!(
                        child.kind(),
                        SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                    )
                })
            })
    }

    /// Every member that overrides or implements `member`, directly or
    /// through another that does.
    fn member_implementations(&self, model: &SemanticModel<'_>, member: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let Some(container) = symbols.get(member).container else {
            return Vec::new();
        };
        let mut found: Vec<SymbolId> = Vec::new();
        let in_interface = symbols.get(container).type_kind() == Some(TypeKind::Interface);
        let mut queue = vec![member];
        if in_interface {
            for derived in self.derived(container, true) {
                if symbols.get(derived).type_kind() == Some(TypeKind::Interface) {
                    continue;
                }
                let Some(seen) = self
                    .supertypes(model, derived)
                    .into_iter()
                    .find(|supertype| supertype.symbol == container)
                else {
                    continue;
                };
                if let Some(implementation) = self.implementation_in(model, derived, member, &seen)
                    && !found.contains(&implementation)
                {
                    found.push(implementation);
                    queue.push(implementation);
                }
            }
        }
        // Then what overrides each of them, however far down.
        while let Some(current) = queue.pop() {
            for over in self.overrides_of(model, current) {
                if !found.contains(&over) {
                    found.push(over);
                    queue.push(over);
                }
            }
        }
        found
    }

    /// The members that override `member` directly.
    fn overrides_of(&self, model: &SemanticModel<'_>, member: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(member);
        let Some(container) = found.container else {
            return Vec::new();
        };
        let mut overrides = Vec::new();
        for derived in self.derived(container, true) {
            for &candidate in symbols.lookup(derived, &found.name) {
                if symbols
                    .get(candidate)
                    .modifiers
                    .contains(Modifiers::OVERRIDE)
                    && self.overridden(model, candidate) == Some(member)
                {
                    overrides.push(candidate);
                }
            }
        }
        overrides
    }

    // MARK: - derived types

    /// Every type in the project that derives from `ty` or implements it —
    /// directly, or through another that does when `transitive` — interfaces
    /// that extend it among them.
    #[must_use]
    pub fn derived(&self, ty: SymbolId, transitive: bool) -> Vec<SymbolId> {
        let map = self.derivation_map();
        let mut found: Vec<SymbolId> = Vec::new();
        let mut queue = vec![ty];
        while let Some(current) = queue.pop() {
            for &derived in map.get(&current).map_or(&[][..], Vec::as_slice) {
                if derived != ty && !found.contains(&derived) {
                    found.push(derived);
                    if transitive {
                        queue.push(derived);
                    }
                }
            }
        }
        found
    }

    /// The types derived from whatever is at `offset`, however indirectly:
    /// the classes and structs when `interfaces` is false, the interfaces
    /// that extend it when it is true. Roslyn's "Find Derived Types" and
    /// "Find Derived Interfaces".
    #[must_use]
    pub fn derived_types(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        interfaces: bool,
    ) -> Option<(String, Vec<Found>)> {
        self.places_for(path, offset, text, |symbol| {
            let symbols = self.compilation.symbols();
            let ty = if symbols.get(symbol).kind == SymbolKind::NamedType {
                symbol
            } else {
                return Vec::new();
            };
            self.derived(ty, true)
                .into_iter()
                .filter(|&derived| {
                    (symbols.get(derived).type_kind() == Some(TypeKind::Interface)) == interfaces
                })
                .collect()
        })
    }

    /// The types declared in the project's files, as opposed to those read
    /// from assemblies or made up by the compiler.
    fn project_types(&self) -> Vec<SymbolId> {
        self.compilation
            .all_types()
            .filter(|symbol| {
                symbol
                    .locations
                    .iter()
                    .any(|location| self.paths.contains_key(&location.tree))
                    && !self.compilation.is_from_metadata(symbol.id)
            })
            .map(|symbol| symbol.id)
            .collect()
    }

    /// Each type the project derives from, with the project's types that
    /// name it after their `:`.
    fn derivation_map(&self) -> HashMap<SymbolId, Vec<SymbolId>> {
        let model = SemanticModel::new(&self.compilation, 0);
        let mut map: HashMap<SymbolId, Vec<SymbolId>> = HashMap::new();
        for ty in self.project_types() {
            for base in model.base_types_of(ty) {
                if let Type::Named { symbol, .. } = base {
                    let list = map.entry(symbol).or_default();
                    if !list.contains(&ty) {
                        list.push(ty);
                    }
                }
            }
        }
        map
    }

    // MARK: - matching members

    /// Every type `ty` derives from or implements, nearest first, each with
    /// what its type parameters mean as seen from `ty`.
    pub(super) fn supertypes(&self, model: &SemanticModel<'_>, ty: SymbolId) -> Vec<Supertype> {
        let symbols = self.compilation.symbols();
        let mut found: Vec<Supertype> = Vec::new();
        let mut seen: HashSet<SymbolId> = HashSet::from([ty]);
        let mut queue: std::collections::VecDeque<(SymbolId, HashMap<SymbolId, Type>)> =
            std::collections::VecDeque::from([(ty, HashMap::new())]);
        while let Some((current, arguments)) = queue.pop_front() {
            let mut bases = model.base_types_of(current);
            // A class that names no base class still has one.
            let names_class = bases.iter().any(|base| {
                base.symbol()
                    .is_some_and(|base| symbols.get(base).type_kind() != Some(TypeKind::Interface))
            });
            if !names_class
                && symbols.get(current).type_kind() != Some(TypeKind::Interface)
                && let Some(implicit) = model.binder().base_class_of(current)
            {
                bases.insert(0, implicit);
            }
            for base in bases {
                let Type::Named {
                    symbol,
                    type_arguments,
                } = base.substitute(&arguments)
                else {
                    continue;
                };
                if !seen.insert(symbol) {
                    continue;
                }
                let parameters = symbols
                    .get(symbol)
                    .as_named_type()
                    .map(|detail| detail.type_parameters.clone())
                    .unwrap_or_default();
                let map: HashMap<SymbolId, Type> =
                    parameters.into_iter().zip(type_arguments).collect();
                found.push(Supertype {
                    symbol,
                    arguments: map.clone(),
                });
                queue.push_back((symbol, map));
            }
        }
        found
    }

    /// The parameters that make a member's signature: a method's, an
    /// indexer's, none for anything else.
    fn signature_parameters(&self, member: SymbolId) -> Vec<SymbolId> {
        let found = self.compilation.symbols().get(member);
        if let Some(method) = found.as_method() {
            return method.parameters.clone();
        }
        if let Some(property) = found.as_property() {
            return property.parameters.clone();
        }
        Vec::new()
    }

    /// Whether two members have the same signature, each seen through the
    /// type arguments its own type was reached with. A generic method's
    /// type parameters are matched by position.
    fn same_signature(
        &self,
        model: &SemanticModel<'_>,
        a: (SymbolId, &HashMap<SymbolId, Type>),
        b: (SymbolId, &HashMap<SymbolId, Type>),
    ) -> bool {
        let symbols = self.compilation.symbols();
        let (first, second) = (symbols.get(a.0), symbols.get(b.0));
        if first.kind != second.kind {
            return false;
        }
        let type_parameters = |symbol: &rustlyn_semantics::Symbol| {
            symbol
                .as_method()
                .map(|method| method.type_parameters.clone())
                .unwrap_or_default()
        };
        let (own, theirs) = (type_parameters(first), type_parameters(second));
        if own.len() != theirs.len() {
            return false;
        }
        let mut second_arguments = b.1.clone();
        for (&theirs, &own) in theirs.iter().zip(&own) {
            second_arguments.insert(theirs, Type::TypeParameter(own));
        }
        let (left, right) = (
            self.signature_parameters(a.0),
            self.signature_parameters(b.0),
        );
        left.len() == right.len()
            && left.iter().zip(&right).all(|(&left, &right)| {
                model.type_of_symbol(left).substitute(a.1)
                    == model.type_of_symbol(right).substitute(&second_arguments)
            })
    }

    /// The member `member` overrides: the nearest one up the class chain
    /// with the same signature.
    fn overridden(&self, model: &SemanticModel<'_>, member: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(member);
        if !found.modifiers.contains(Modifiers::OVERRIDE) {
            return None;
        }
        let container = found.container?;
        let own = HashMap::new();
        for supertype in self.supertypes(model, container) {
            if symbols.get(supertype.symbol).type_kind() == Some(TypeKind::Interface) {
                continue;
            }
            for &candidate in symbols.lookup(supertype.symbol, &found.name) {
                if self.same_signature(model, (member, &own), (candidate, &supertype.arguments)) {
                    return Some(candidate);
                }
            }
        }
        None
    }

    /// The interface members `member` implements for its own type.
    fn implemented(&self, model: &SemanticModel<'_>, member: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(member);
        let Some(container) = found.container else {
            return Vec::new();
        };
        if found.modifiers.contains(Modifiers::STATIC)
            || symbols.get(container).type_kind() == Some(TypeKind::Interface)
        {
            return Vec::new();
        }
        let name = split_explicit(&found.name).map_or(found.name.as_str(), |(_, name)| name);
        let mut implemented = Vec::new();
        for supertype in self.supertypes(model, container) {
            if symbols.get(supertype.symbol).type_kind() != Some(TypeKind::Interface) {
                continue;
            }
            for &candidate in symbols.lookup(supertype.symbol, name) {
                if self.implementation_in(model, container, candidate, &supertype) == Some(member) {
                    implemented.push(candidate);
                }
            }
        }
        implemented
    }

    /// The member of `ty` that implements `wanted`, a member of the
    /// interface `interface` — which `ty` sees with `interface.arguments`.
    ///
    /// An explicit implementation in `ty` wins; otherwise the nearest
    /// member up the class chain with the name and the signature, which is
    /// how a base class's public method comes to implement an interface
    /// only a derived class lists (§19.6.5).
    pub(super) fn implementation_in(
        &self,
        model: &SemanticModel<'_>,
        ty: SymbolId,
        wanted: SymbolId,
        interface: &Supertype,
    ) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let wanted_symbol = symbols.get(wanted);
        let interface_name = &symbols.get(interface.symbol).name;
        let own = HashMap::new();
        for &member in &symbols.get(ty).members {
            if let Some((written, name)) = split_explicit(&symbols.get(member).name)
                && name == wanted_symbol.name
                && crate::index::plain_name(written) == interface_name
                && self.same_signature(model, (member, &own), (wanted, &interface.arguments))
            {
                return Some(member);
            }
        }
        let classes = std::iter::once(Supertype {
            symbol: ty,
            arguments: HashMap::new(),
        })
        .chain(self.supertypes(model, ty).into_iter().filter(|supertype| {
            symbols.get(supertype.symbol).type_kind() != Some(TypeKind::Interface)
        }));
        for class in classes {
            for &candidate in symbols.lookup(class.symbol, &wanted_symbol.name) {
                if !symbols.get(candidate).modifiers.contains(Modifiers::STATIC)
                    && self.same_signature(
                        model,
                        (candidate, &class.arguments),
                        (wanted, &interface.arguments),
                    )
                {
                    return Some(candidate);
                }
            }
        }
        None
    }

    // MARK: - hierarchy items

    /// What a call hierarchy is about for a symbol: a method, a
    /// constructor, a property, an event or a field. An accessor is its
    /// property's, and a local function its method's.
    fn callable(&self, symbol: SymbolId) -> Option<SymbolId> {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        match found.kind {
            SymbolKind::Method => match found.as_method().map(|method| method.method_kind) {
                Some(MethodKind::PropertyGet | MethodKind::PropertySet) => found.container,
                Some(MethodKind::LocalFunction) => {
                    let mut current = found.container;
                    while let Some(container) = current {
                        let method = symbols.get(container).as_method();
                        if method
                            .is_none_or(|method| method.method_kind != MethodKind::LocalFunction)
                        {
                            return self.callable(container);
                        }
                        current = symbols.get(container).container;
                    }
                    None
                }
                _ => Some(symbol),
            },
            SymbolKind::Property | SymbolKind::Event | SymbolKind::Field => Some(symbol),
            _ => None,
        }
    }

    /// A symbol as a hierarchy lists it.
    #[must_use]
    pub fn hierarchy_item(&self, symbol: SymbolId) -> HierarchyItem {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let is_constructor = found.as_method().is_some_and(|method| {
            matches!(
                method.method_kind,
                MethodKind::Constructor | MethodKind::StaticConstructor
            )
        });
        let name = match found.container {
            Some(container) if is_constructor => symbols.get(container).name.clone(),
            _ if found.kind == SymbolKind::NamedType => {
                let parameters: Vec<String> = found
                    .as_named_type()
                    .map(|detail| {
                        detail
                            .type_parameters
                            .iter()
                            .map(|&parameter| symbols.get(parameter).name.clone())
                            .collect()
                    })
                    .unwrap_or_default();
                if parameters.is_empty() {
                    found.name.clone()
                } else {
                    format!("{}<{}>", found.name, parameters.join(", "))
                }
            }
            _ => found.name.clone(),
        };
        let container = found
            .container
            .map(|container| symbols.qualified_name(container))
            .unwrap_or_default();
        let place = self
            .declarations_of(symbol)
            .into_iter()
            .next()
            .map(|found| found.place);
        let full = match &place {
            Some(Place::Source { path, span }) => {
                let tree = self.tree_index(path);
                self.compilation
                    .declaration_nodes(symbol)
                    .iter()
                    .find(|(at, full)| Some(*at) == tree && full.contains_span(*span))
                    .map(|(_, full)| *full)
                    .or(Some(*span))
            }
            _ => None,
        };
        HierarchyItem {
            symbol,
            name,
            kind: declaration_kind(&self.compilation, symbol),
            detail: describe_symbol(&self.compilation, symbol),
            container,
            key: self.symbol_key(symbol),
            place,
            full,
        }
    }

    /// A name for a symbol that finds it again, even in a compilation built
    /// after this one: its kind, the metadata name of the type it is in,
    /// its own name, and for a method its type parameter count and
    /// parameter types — what tells overloads apart. Roslyn's `SymbolKey`
    /// does the same job for the same reason: an editor holds on to a
    /// hierarchy item while the code under it is recompiled.
    #[must_use]
    pub fn symbol_key(&self, symbol: SymbolId) -> String {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let model = SemanticModel::new(&self.compilation, 0);
        let letter = match found.kind {
            SymbolKind::NamedType => 'T',
            SymbolKind::Method => 'M',
            SymbolKind::Property => 'P',
            SymbolKind::Field => 'F',
            SymbolKind::Event => 'E',
            SymbolKind::Namespace => 'N',
            _ => 'X',
        };
        if matches!(found.kind, SymbolKind::NamedType | SymbolKind::Namespace) {
            return format!("{letter}:{}", symbols.metadata_qualified_name(symbol));
        }
        let container = found
            .container
            .map(|container| symbols.metadata_qualified_name(container))
            .unwrap_or_default();
        let arity = found
            .as_method()
            .map_or(0, |method| method.type_parameters.len());
        let parameters: Vec<String> = self
            .signature_parameters(symbol)
            .into_iter()
            .map(|parameter| model.type_of_symbol(parameter).display(symbols))
            .collect();
        format!(
            "{letter}:{container}|{}`{arity}({})",
            found.name,
            parameters.join(",")
        )
    }

    /// The symbol a [`Self::symbol_key`] names in this compilation.
    #[must_use]
    pub fn symbol_by_key(&self, key: &str) -> Option<SymbolId> {
        let (letter, rest) = key.split_once(':')?;
        if letter == "T" {
            return self.compilation.type_by_metadata_name(rest);
        }
        let (container, member) = rest.split_once('|')?;
        let (name, _) = member.split_once('`')?;
        let ty = self.compilation.type_by_metadata_name(container)?;
        self.compilation
            .symbols()
            .lookup(ty, name)
            .iter()
            .copied()
            .find(|&candidate| self.symbol_key(candidate) == key)
    }

    // MARK: - call hierarchy

    /// The member at `offset`, as the root of a call hierarchy: a method,
    /// a constructor, a property, an event or a field. The name of a call
    /// is the member called; the name in a declaration, the member
    /// declared.
    #[must_use]
    pub fn call_hierarchy_item(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<HierarchyItem> {
        if let Some((view, symbol)) = self.operator_declared_at(path, offset, text) {
            return Some(self.edited_item(&view, path, self.hierarchy_item(symbol)));
        }
        let (view, _, symbol) = self.symbol_at(path, offset, text)?;
        let symbol = self.callable(symbol)?;
        Some(self.edited_item(&view, path, self.hierarchy_item(symbol)))
    }

    /// The operator, conversion or indexer declared at `offset`, which is
    /// named by the token of the operator, by the `operator` keyword of a
    /// conversion or by an indexer's `this`: none is an identifier that a
    /// name can be resolved from.
    fn operator_declared_at(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<(View<'_>, SymbolId)> {
        let view = self.view_of(path, text)?;
        let token = view
            .root
            .find_token(offset)
            .filter(|token| token.span().contains(offset))?;
        let declaration = token.parent().clone();
        match declaration.kind() {
            SyntaxKind::OperatorDeclaration | SyntaxKind::ConversionOperatorDeclaration => {
                let after_keyword = declaration
                    .child_tokens()
                    .find(|candidate| candidate.kind() == SyntaxKind::OperatorKeyword)
                    .is_some_and(|keyword| token.span().start() >= keyword.span().start());
                if !after_keyword {
                    return None;
                }
            }
            SyntaxKind::IndexerDeclaration if token.kind() == SyntaxKind::ThisKeyword => {}
            _ => return None,
        }
        let symbol = view.model.declared_symbol(&declaration)?;
        Some((view, symbol))
    }

    /// Moves an item's places into the editor's text, when that is what
    /// the question was asked about.
    fn edited_item(&self, view: &View<'_>, path: &Path, mut item: HierarchyItem) -> HierarchyItem {
        let Some(speculation) = &view.speculation else {
            return item;
        };
        if let Some(Place::Source { path: at, span }) = &mut item.place
            && at == path
        {
            match speculation.unmap(*span) {
                Some(moved) => *span = moved,
                None => {
                    item.place = None;
                    item.full = None;
                    return item;
                }
            }
            item.full = item.full.and_then(|full| speculation.unmap(full));
        }
        item
    }

    /// Every member in the project whose body calls `target`, with where.
    ///
    /// Calls to a member `target` overrides or implements are included too,
    /// marked `through_base`: `IShape.Area()` may be `Circle.Area()` when it
    /// runs. Calls from a lambda are its enclosing member's, and from a
    /// field's initializer the field's.
    ///
    /// A call is a name the body binds to the member, and also a construct
    /// that runs the member without one: an operator, an indexer, a
    /// target-typed `new()`, `foreach`, `using`, `await`, an interpolated
    /// string's `ToString`, a collection initializer's `Add`, a
    /// deconstruction, a pattern, a query, an attribute. `nameof(m.Area)`,
    /// `typeof` and a documentation `cref` name the member and do not call
    /// it.
    #[must_use]
    pub fn incoming_calls(&self, target: SymbolId) -> Vec<IncomingCall> {
        let symbols = self.compilation.symbols();
        let Some(target) = self.callable(target) else {
            return Vec::new();
        };
        let bases: HashSet<SymbolId> = self.base_symbols(target).into_iter().collect();
        let mut words: Vec<String> = vec![self.search_name(target)];
        for &base in &bases {
            let name = symbols.get(base).name.clone();
            let name = split_explicit(&name).map_or(name.clone(), |(_, name)| name.to_string());
            if !words.contains(&name) {
                words.push(name);
            }
        }
        let is_constructor = symbols
            .get(target)
            .as_method()
            .is_some_and(|method| method.method_kind == MethodKind::Constructor);

        let trees: Vec<usize> = self.paths.keys().copied().collect();
        let found = parallel(trees.len(), |index| {
            let tree = trees[index];
            let Some(text) = self
                .compilation
                .trees()
                .source(tree)
                .map(|source| source.text())
            else {
                return Vec::new();
            };
            let mentions = words.iter().any(|word| {
                contains_word(text, word)
                    || attribute_stem(word).is_some_and(|stem| contains_word(text, stem))
            }) || (is_constructor
                && (contains_word(text, "base") || contains_word(text, "this")));
            if !mentions {
                return Vec::new();
            }
            let Some(mut view) = self.view(tree) else {
                return Vec::new();
            };
            let mut calls: Vec<(SymbolId, bool, TextSpan, UseKind)> = Vec::new();
            let tokens: Vec<_> = view
                .root
                .descendant_tokens()
                .filter(|token| match token.kind() {
                    SyntaxKind::IdentifierToken => {
                        let text = token.value_text();
                        words.iter().any(|word| {
                            word == text || attribute_stem(word).is_some_and(|stem| stem == text)
                        })
                    }
                    SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword => is_constructor,
                    _ => false,
                })
                .collect();
            for token in tokens {
                let parent = token.parent().clone();
                // The name of a member in `nameof(…)` is its name, not a use.
                if in_nameof(&token) {
                    continue;
                }
                if let Some(attribute) = attribute_of(&token) {
                    if let Some((caller, kind)) =
                        self.attribute_use(&view, &token, &attribute, target, &bases)
                    {
                        calls.push((caller, false, token.span(), kind));
                    }
                    continue;
                }
                let Some(body) = view.body_for(&parent) else {
                    continue;
                };
                let Some(called) = called_at(&body, &token) else {
                    continue;
                };
                let called = view.most_derived(&token, called);
                let called = self.callable(called).unwrap_or(called);
                let through_base = if called == target {
                    false
                } else if bases.contains(&called) && !calls_base(&token) {
                    true
                } else {
                    // `base.Area()` runs the base's own member, never an
                    // override of it.
                    continue;
                };
                // A declaration is not a call, and neither is the name of
                // what is being declared.
                let Some(caller) = view.caller_of(&parent) else {
                    continue;
                };
                calls.push((caller, through_base, token.span(), use_kind_of(&token)));
            }
            let path = self.paths[&tree].clone();
            calls
                .into_iter()
                .map(|(caller, through, span, kind)| (path.clone(), caller, through, span, kind))
                .collect::<Vec<_>>()
        });

        let mut found: Vec<(PathBuf, SymbolId, bool, TextSpan, UseKind)> =
            found.into_iter().flatten().collect();
        let constructs = self.constructs_reaching(target);
        if constructs != 0 {
            let index = symbols
                .get(target)
                .container
                .map(|container| self.implicit_index(constructs, container))
                .unwrap_or_default();
            // What the target's type is, and the classes it derives from: a
            // use of a base member on a value of some other type is no use
            // of the target, and neither is one on an interface, which every
            // implementation answers to.
            let model = SemanticModel::new(&self.compilation, 0);
            let kinds: HashSet<SymbolId> = symbols
                .get(target)
                .container
                .into_iter()
                .flat_map(|container| {
                    std::iter::once(container).chain(
                        self.supertypes(&model, container)
                            .into_iter()
                            .map(|supertype| supertype.symbol)
                            .filter(|&ty| symbols.get(ty).type_kind() != Some(TypeKind::Interface)),
                    )
                })
                .collect();
            for symbol in std::iter::once(target).chain(bases.iter().copied()) {
                let through_base = symbol != target;
                for used in index.by_symbol.get(&symbol).into_iter().flatten() {
                    if through_base && used.receiver.is_some_and(|ty| !kinds.contains(&ty)) {
                        continue;
                    }
                    if let Some(path) = self.paths.get(&used.tree) {
                        found.push((
                            path.clone(),
                            used.caller,
                            through_base,
                            used.span,
                            used.kind,
                        ));
                    }
                }
            }
        }

        let mut grouped: Vec<IncomingCall> = Vec::new();
        let mut at: HashMap<(PathBuf, SymbolId, bool), usize> = HashMap::new();
        for (path, caller, through_base, span, kind) in found {
            let key = (path.clone(), caller, through_base);
            let slot = *at.entry(key).or_insert_with(|| {
                grouped.push(IncomingCall {
                    from: self.hierarchy_item(caller),
                    path,
                    spans: Vec::new(),
                    uses: Vec::new(),
                    through_base,
                });
                grouped.len() - 1
            });
            grouped[slot].spans.push(span);
            grouped[slot].uses.push(kind);
        }
        for call in &mut grouped {
            let mut pairs: Vec<(TextSpan, UseKind)> = call
                .spans
                .iter()
                .copied()
                .zip(call.uses.iter().copied())
                .collect();
            pairs.sort_by_key(|(span, _)| span.start());
            pairs.dedup_by_key(|(span, _)| *span);
            call.spans = pairs.iter().map(|(span, _)| *span).collect();
            call.uses = pairs.iter().map(|(_, kind)| *kind).collect();
        }
        grouped.sort_by(|a, b| {
            a.through_base
                .cmp(&b.through_base)
                .then_with(|| a.path.cmp(&b.path))
                .then_with(|| a.spans[0].start().cmp(&b.spans[0].start()))
        });
        grouped
    }

    /// An attribute that names the type of the constructor `target`, or sets
    /// the property or field `target` by name: the member the attribute is
    /// on is its caller. The constructor is the one the binder chose for the
    /// arguments.
    fn attribute_use(
        &self,
        view: &View<'_>,
        token: &SyntaxToken,
        attribute: &SyntaxNode,
        target: SymbolId,
        bases: &HashSet<SymbolId>,
    ) -> Option<(SymbolId, UseKind)> {
        let declaration = attribute.parent()?.parent()?.clone();
        let bound = view
            .model
            .binder()
            .bind_attribute(view.tree, &declaration, attribute)?;
        let names_type = !token
            .parent()
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::AttributeArgument);
        let hit = if names_type {
            bound
                .constructor
                .is_some_and(|constructor| constructor == target || bases.contains(&constructor))
        } else {
            bound.named.iter().any(|(member, _)| *member == target)
        };
        if !hit {
            return None;
        }
        // The member the attribute is on; a parameter's or a return value's
        // attribute is its method's.
        let owner = std::iter::once(declaration.clone())
            .chain(declaration.ancestors())
            .find_map(|node| self.attributed_symbol(view, &node))?;
        let kind = if names_type {
            UseKind::Call
        } else {
            UseKind::Write
        };
        Some((owner, kind))
    }

    /// The symbol declared by `node`, for a node that is a declaration.
    fn attributed_symbol(&self, view: &View<'_>, node: &SyntaxNode) -> Option<SymbolId> {
        if !node.kind().is_declaration_node() {
            return None;
        }
        // A field's attributes are on the declaration, its symbols on the
        // declarators.
        let named = if matches!(
            node.kind(),
            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
        ) {
            node.descendants()
                .find(|inner| inner.kind() == SyntaxKind::VariableDeclarator)?
        } else {
            node.clone()
        };
        let declared = view.model.declared_symbol(&named)?;
        Some(self.callable(declared).unwrap_or(declared))
    }

    /// Every method, constructor, property and event `source`'s body calls
    /// or reads, with where, in the order first called.
    #[must_use]
    pub fn outgoing_calls(&self, source: SymbolId) -> Vec<OutgoingCall> {
        let symbols = self.compilation.symbols();
        let Some(source) = self.callable(source) else {
            return Vec::new();
        };
        let mut calls: Vec<OutgoingCall> = Vec::new();
        for &(tree, span) in self.compilation.declaration_nodes(source) {
            let (Some(path), Some(mut view)) = (self.path_of(tree), self.view(tree)) else {
                continue;
            };
            let Some(declaration) = view.root.find_node(span) else {
                continue;
            };
            let owners: Vec<SyntaxNode> = std::iter::once(declaration.clone())
                .chain(declaration.descendants())
                .filter(|node| {
                    is_body_owner(node.kind())
                        || (node.kind() == SyntaxKind::VariableDeclarator && node == &declaration)
                })
                .collect();
            let mut seen: HashSet<TextSpan> = HashSet::new();
            let mut found: Vec<(TextSpan, SymbolId)> = Vec::new();
            for owner in owners {
                let Some(body) = view.body_for(&owner) else {
                    continue;
                };
                let mut named: Vec<(TextSpan, SymbolId)> = body
                    .symbols
                    .iter()
                    .filter(|(at, _)| declaration.span().contains_span(**at))
                    .map(|(&at, &called)| (at, called))
                    .collect();
                // `: base(radius)` calls a constructor with no name of its
                // own to record it under: the keyword stands for it.
                for statement in &body.statements {
                    if let BoundStatementKind::ConstructorInitializer {
                        constructor: Some(constructor),
                        ..
                    } = &statement.kind
                        && let Some(initializer) = view.root.find_node(statement.span)
                        && let Some(keyword) = initializer.child_tokens().find(|token| {
                            matches!(
                                token.kind(),
                                SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword
                            )
                        })
                    {
                        named.push((keyword.span(), *constructor));
                    }
                }
                for (at, called) in named {
                    if !seen.insert(at) {
                        continue;
                    }
                    let called = match view.root.find_token(at.start()) {
                        Some(token) if token.span() == at => view.most_derived(&token, called),
                        _ => called,
                    };
                    found.push((at, called));
                }
            }
            found.sort_by_key(|(at, _)| at.start());
            let mut index: HashMap<SymbolId, usize> = HashMap::new();
            let first = calls.len();
            for (at, called) in found {
                let Some(called) = self.callable(called) else {
                    continue;
                };
                if called == source || symbols.get(called).kind == SymbolKind::Field {
                    continue;
                }
                let slot = *index.entry(called).or_insert_with(|| {
                    calls.push(OutgoingCall {
                        to: self.hierarchy_item(called),
                        path: path.to_path_buf(),
                        spans: Vec::new(),
                    });
                    calls.len() - 1
                });
                calls[slot].spans.push(at);
            }
            debug_assert!(calls[first..].iter().all(|call| !call.spans.is_empty()));
        }
        calls
    }

    // MARK: - type hierarchy

    /// The type at `offset`, as the root of a type hierarchy: a type's own
    /// name, or the type of a variable or member.
    #[must_use]
    pub fn type_hierarchy_item(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<HierarchyItem> {
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        let model = SemanticModel::new(&self.compilation, 0);
        let ty = match view.resolve(&token)? {
            Resolved::Local { ty, .. } => ty,
            Resolved::Symbol(symbol) => self.navigable_type(&model, symbol)?,
        };
        let mut types = Vec::new();
        self.types_in(&ty, &mut types);
        let symbols = self.compilation.symbols();
        let ty = types
            .into_iter()
            .find(|&symbol| symbols.get(symbol).kind == SymbolKind::NamedType)?;
        Some(self.edited_item(&view, path, self.hierarchy_item(ty)))
    }

    /// The base class and the interfaces `ty` names, one level up, as
    /// items — those from assemblies among them.
    #[must_use]
    pub fn supertypes_of(&self, ty: SymbolId) -> Vec<HierarchyItem> {
        let model = SemanticModel::new(&self.compilation, 0);
        let symbols = self.compilation.symbols();
        if symbols.get(ty).kind != SymbolKind::NamedType {
            return Vec::new();
        }
        let mut found: Vec<SymbolId> = Vec::new();
        if symbols.get(ty).type_kind() != Some(TypeKind::Interface)
            && let Some(Type::Named { symbol, .. }) = model.binder().base_class_of(ty)
        {
            found.push(symbol);
        }
        for base in model.base_types_of(ty) {
            if let Type::Named { symbol, .. } = base
                && !found.contains(&symbol)
            {
                found.push(symbol);
            }
        }
        found
            .into_iter()
            .map(|symbol| self.hierarchy_item(symbol))
            .collect()
    }

    /// The types in the project that name `ty` after their `:`.
    #[must_use]
    pub fn subtypes_of(&self, ty: SymbolId) -> Vec<HierarchyItem> {
        self.derived(ty, false)
            .into_iter()
            .map(|symbol| self.hierarchy_item(symbol))
            .collect()
    }
}

impl View<'_> {
    /// The member a call through a name actually reaches, as far as the
    /// type of what it is called on says.
    ///
    /// The binder records the member lookup settled on, which for a
    /// virtual member is the declaration that introduced it: `c.Area()`
    /// with `c` a `Circle` is recorded as `Shape.Area`. Roslyn's model says
    /// `Circle.Area`, and so does a reader: the nearest override in the
    /// receiver's class chain is what the call means. A call through an
    /// interface, or on something whose type is not known more precisely,
    /// is left as it was.
    fn most_derived(&mut self, token: &SyntaxToken, called: SymbolId) -> SymbolId {
        let semantic = self.semantic;
        let symbols = semantic.compilation.symbols();
        let found = symbols.get(called);
        let dispatched = matches!(
            found.kind,
            SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
        ) && (found.modifiers.contains(Modifiers::VIRTUAL)
            || found.modifiers.contains(Modifiers::ABSTRACT)
            || found.modifiers.contains(Modifiers::OVERRIDE));
        if !dispatched {
            return called;
        }
        let name = token.parent().clone();
        let receiver = match name.parent() {
            Some(access)
                if access.kind() == SyntaxKind::SimpleMemberAccessExpression
                    && access.children().last().as_ref() == Some(&name) =>
            {
                let Some(receiver) = access.children().next() else {
                    return called;
                };
                let Some(body) = self.body_for(&receiver) else {
                    return called;
                };
                match body.type_at(receiver.span()) {
                    Some(Type::Named { symbol, .. }) => Some(*symbol),
                    _ => None,
                }
            }
            Some(access) if access.kind() == SyntaxKind::MemberBindingExpression => None,
            _ => self
                .model
                .binder()
                .context_at(self.tree, &name)
                .enclosing_type(),
        };
        let Some(receiver) = receiver else {
            return called;
        };
        let model = SemanticModel::new(&semantic.compilation, 0);
        let classes = std::iter::once(receiver).chain(
            semantic
                .supertypes(&model, receiver)
                .into_iter()
                .map(|supertype| supertype.symbol)
                .filter(|&symbol| symbols.get(symbol).type_kind() != Some(TypeKind::Interface)),
        );
        for class in classes {
            for &candidate in symbols.lookup(class, &found.name) {
                if candidate == called {
                    return called;
                }
                if symbols.get(candidate).kind == found.kind
                    && semantic.base_symbols(candidate).contains(&called)
                {
                    return candidate;
                }
            }
        }
        called
    }

    /// The type of the expression a name ends: `shapes.Find(0)` for the
    /// `Find` in it, with the type arguments of `shapes` put in — which is
    /// `IShape` where the declaration says `T`.
    fn type_of_named(&mut self, token: &SyntaxToken, symbol: SymbolId) -> Option<Type> {
        let symbols = self.semantic.compilation.symbols();
        let found = symbols.get(symbol);
        let typed = match found.kind {
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Event => true,
            SymbolKind::Method => found
                .as_method()
                .is_some_and(|method| method.method_kind != MethodKind::Constructor),
            _ => false,
        };
        if !typed {
            return None;
        }
        let mut expression = token.parent().clone();
        if let Some(access) = expression.parent().cloned()
            && matches!(
                access.kind(),
                SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
            )
            && access.children().last().as_ref() == Some(&expression)
        {
            expression = access;
        }
        if let Some(call) = expression.parent().cloned()
            && call.kind() == SyntaxKind::InvocationExpression
            && call.children().next().as_ref() == Some(&expression)
        {
            expression = call;
        }
        let body = self.body_for(&expression)?;
        body.type_at(expression.span())
            .filter(|ty| !matches!(ty, Type::Error))
            .cloned()
    }

    /// The member whose body `node` is in, as a call hierarchy names it:
    /// an accessor's property, a field initializer's field, a top-level
    /// statement's `<Main>$`.
    pub(super) fn caller_of(&self, node: &SyntaxNode) -> Option<SymbolId> {
        let owner = SemanticModel::body_owner(node)?;
        let owner = match owner.kind() {
            SyntaxKind::GetAccessorDeclaration
            | SyntaxKind::SetAccessorDeclaration
            | SyntaxKind::InitAccessorDeclaration
            | SyntaxKind::AddAccessorDeclaration
            | SyntaxKind::RemoveAccessorDeclaration => owner
                .ancestors()
                .find(|ancestor| {
                    matches!(
                        ancestor.kind(),
                        SyntaxKind::PropertyDeclaration
                            | SyntaxKind::IndexerDeclaration
                            | SyntaxKind::EventDeclaration
                    )
                })
                .unwrap_or(owner),
            _ => owner,
        };
        let declared = self.model.declared_symbol(&owner)?;
        self.semantic.callable(declared)
    }
}

/// What the name `token` calls or reads, as its body recorded it: the
/// symbol bound at its span, or — for the `base` of `: base(...)` — the
/// constructor the initializer chains to.
fn called_at(body: &BoundBody, token: &SyntaxToken) -> Option<SymbolId> {
    if let Some(&called) = body.symbols.get(&token.span()) {
        return Some(called);
    }
    let initializer = token.parent();
    if !matches!(
        initializer.kind(),
        SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer
    ) {
        return None;
    }
    body.statements
        .iter()
        .find_map(|statement| match &statement.kind {
            BoundStatementKind::ConstructorInitializer { constructor, .. }
                if statement.span == initializer.span() =>
            {
                *constructor
            }
            _ => None,
        })
}

/// Whether `token` is in the argument of a `nameof(…)`, which names what it
/// is given without running it.
fn in_nameof(token: &SyntaxToken) -> bool {
    token.parent().ancestors().any(|node| is_nameof(&node))
}

/// Whether `node` is `nameof(…)`.
pub(super) fn is_nameof(node: &SyntaxNode) -> bool {
    node.kind() == SyntaxKind::InvocationExpression
        && node.children().next().is_some_and(|callee| {
            callee.kind() == SyntaxKind::IdentifierName && callee.text().trim() == "nameof"
        })
}

/// The attribute `token` is in, when it is in one.
fn attribute_of(token: &SyntaxToken) -> Option<SyntaxNode> {
    token
        .parent()
        .ancestors()
        .find(|node| node.kind() == SyntaxKind::Attribute)
}

/// Whether `token` names a member of `base`, which is called as it is and
/// not dispatched.
fn calls_base(token: &SyntaxToken) -> bool {
    token
        .parent()
        .parent()
        .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
        .and_then(|access| access.children().next())
        .is_some_and(|receiver| receiver.kind() == SyntaxKind::BaseExpression)
}

/// `IShape.Area` as the interface it was written with and the member's own
/// name; `None` for a name with no interface in front of it.
pub(super) fn split_explicit(name: &str) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    let mut last = None;
    for (at, byte) in name.bytes().enumerate() {
        match byte {
            b'<' => depth += 1,
            b'>' => depth -= 1,
            b'.' if depth == 0 => last = Some(at),
            _ => {}
        }
    }
    let at = last?;
    Some((&name[..at], &name[at + 1..]))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::tests::{at, compile};
    use super::*;

    const SHAPES: &str = r#"namespace Geo;

public interface IShape
{
    double Area();
    string Name { get; }
}

public interface ISolid : IShape
{
    double Volume();
}

public abstract class Shape : IShape
{
    public abstract double Area();
    public virtual string Name => "shape";
    public string Describe() { return Name + Area(); }
}

public class Circle : Shape
{
    public double Radius;
    public Circle(double radius) { Radius = radius; }
    public override double Area() => 3.14 * Radius * Radius;
    public override string Name => "circle";
}

public sealed class Unit : Circle
{
    public Unit() : base(1) { }
    public override double Area() => base.Area();
}

public struct Square : IShape
{
    public double Side;
    double IShape.Area() => Side * Side;
    public string Name => "square";
}
"#;

    const GENERIC: &str = r#"namespace Geo;

public interface IRepository<T>
{
    T Find(int id);
    void Add(T item);
}

public class Repository<T> : IRepository<T>
{
    public virtual T Find(int id) { return default(T); }
    public void Add(T item) { }
}

public class Shapes : Repository<IShape>
{
    public override IShape Find(int id) { return new Circle(id); }
}
"#;

    const CANVAS: &str = r#"namespace Geo;

public partial class Canvas
{
    private readonly Shapes shapes = new Shapes();
    private Repository<Circle> circles;

    public IShape Current { get { return shapes.Find(0); } }

    public double Total(IShape[] all)
    {
        double sum = 0;
        foreach (var shape in all) { sum += shape.Area(); }
        return sum;
    }

    public double One() { var c = new Circle(2); return c.Area(); }
}
"#;

    const LATER: &str = r#"namespace Geo;

public delegate double Measure();

public partial class Canvas
{
    public Measure Later() { return () => new Unit().Area(); }
    public int? Count;
    public void Fill() { circles.Add(new Circle(3)); var total = Total(null); }
}
"#;

    fn project() -> Semantic {
        compile(
            &[
                ("Shapes.cs", SHAPES),
                ("Generic.cs", GENERIC),
                ("Canvas.cs", CANVAS),
                ("Later.cs", LATER),
            ],
            false,
        )
        .expect("compiled")
    }

    fn names(found: &[Found]) -> Vec<String> {
        found.iter().map(|found| found.name.clone()).collect()
    }

    fn file(name: &str) -> &'static str {
        match name {
            "Shapes.cs" => SHAPES,
            "Generic.cs" => GENERIC,
            "Canvas.cs" => CANVAS,
            "Later.cs" => LATER,
            _ => panic!("no file {name}"),
        }
    }

    /// What `question` finds at `marker` (plus `into`) in `name`, by
    /// qualified name.
    fn ask(
        semantic: &Semantic,
        name: &str,
        marker: &str,
        into: usize,
        question: impl Fn(&Semantic, &Path, u32) -> Option<(String, Vec<Found>)>,
    ) -> Vec<String> {
        let path = PathBuf::from(format!("/p/{name}"));
        let (_, found) =
            question(semantic, &path, at(file(name), marker, into)).expect("an answer");
        names(&found)
    }

    fn symbol(semantic: &Semantic, name: &str, marker: &str, into: usize) -> SymbolId {
        let path = PathBuf::from(format!("/p/{name}"));
        let (_, _, symbol) = semantic
            .symbol_at(&path, at(file(name), marker, into), None)
            .expect("a symbol");
        symbol
    }

    #[test]
    fn type_definition_goes_to_the_type_of_a_variable_member_or_call() {
        let semantic = project();
        let ask = |marker: &str, into: usize| {
            ask(
                &semantic,
                "Canvas.cs",
                marker,
                into,
                |semantic, path, offset| semantic.type_definition(path, offset, None),
            )
        };
        // A local declared with `var`; a property's type; a call's return
        // type, after substitution.
        assert_eq!(ask("c.Area", 0), vec!["Geo.Circle"]);
        assert_eq!(ask("Current", 0), vec!["Geo.IShape"]);
        assert_eq!(ask("Find(0)", 0), vec!["Geo.IShape"]);
        // An array leads to its element type.
        assert_eq!(ask("all)", 0), vec!["Geo.IShape"]);
        // A constructed generic type leads to the definition and to its
        // argument.
        assert_eq!(ask("circles;", 0), vec!["Geo.Repository`1", "Geo.Circle"]);
        // A type is its own type.
        assert_eq!(ask("Shapes shapes", 0), vec!["Geo.Shapes"]);
    }

    #[test]
    fn type_definition_of_a_nullable_is_what_it_wraps_and_of_a_generic_its_parameter() {
        let semantic = project();
        let found = ask(
            &semantic,
            "Later.cs",
            "Count",
            0,
            |semantic, path, offset| semantic.type_definition(path, offset, None),
        );
        // `int?` wraps `int`, which the synthesised core library has no
        // file for.
        assert!(
            found.iter().all(|name| !name.contains("Nullable")),
            "{found:?}"
        );
        let found = ask(
            &semantic,
            "Generic.cs",
            "Find(int id);",
            0,
            |semantic, path, offset| semantic.type_definition(path, offset, None),
        );
        assert_eq!(found, vec!["Geo.IRepository`1.T"]);
    }

    #[test]
    fn bases_of_a_type_are_its_classes_then_its_interfaces() {
        let semantic = project();
        let found = ask(
            &semantic,
            "Shapes.cs",
            "Unit :",
            0,
            |semantic, path, offset| semantic.bases(path, offset, None),
        );
        assert_eq!(found, vec!["Geo.Circle", "Geo.Shape", "Geo.IShape"]);
        let found = ask(
            &semantic,
            "Shapes.cs",
            "ISolid :",
            0,
            |semantic, path, offset| semantic.bases(path, offset, None),
        );
        assert_eq!(found, vec!["Geo.IShape"]);
    }

    #[test]
    fn bases_of_an_override_are_what_it_overrides_and_implements_nearest_first() {
        let semantic = project();
        let bases = |marker: &str| {
            ask(
                &semantic,
                "Shapes.cs",
                marker,
                0,
                |semantic, path, offset| semantic.bases(path, offset, None),
            )
        };
        assert_eq!(
            bases("Area() => base"),
            vec!["Geo.Circle.Area", "Geo.Shape.Area", "Geo.IShape.Area"]
        );
        assert_eq!(
            bases("Area() => 3.14"),
            vec!["Geo.Shape.Area", "Geo.IShape.Area"]
        );
        assert_eq!(
            bases("Name => \"circle\""),
            vec!["Geo.Shape.Name", "Geo.IShape.Name"]
        );
        // An explicit implementation, and an implicit one in a struct.
        assert_eq!(bases("Area() => Side"), vec!["Geo.IShape.Area"]);
        assert_eq!(bases("Name => \"square\""), vec!["Geo.IShape.Name"]);
        // A member that neither overrides nor implements has no base.
        assert_eq!(bases("Describe"), Vec::<String>::new());
    }

    #[test]
    fn bases_see_through_type_arguments() {
        let semantic = project();
        let bases = |marker: &str| {
            ask(
                &semantic,
                "Generic.cs",
                marker,
                0,
                |semantic, path, offset| semantic.bases(path, offset, None),
            )
        };
        // `Shapes.Find` returns `IShape` where `Repository<T>.Find` returns
        // `T`: the parameters are what match, and they do.
        assert_eq!(
            bases("Find(int id) { return new"),
            vec!["Geo.Repository`1.Find", "Geo.IRepository`1.Find"]
        );
        assert_eq!(bases("Add(T item) {"), vec!["Geo.IRepository`1.Add"]);
    }

    #[test]
    fn implementations_of_an_interface_are_the_concrete_types_however_indirect() {
        let semantic = project();
        let mut found = ask(
            &semantic,
            "Shapes.cs",
            "IShape\n{",
            0,
            |semantic, path, offset| semantic.implementations(path, offset, None),
        );
        found.sort();
        assert_eq!(found, vec!["Geo.Circle", "Geo.Square", "Geo.Unit"]);
    }

    #[test]
    fn implementations_of_a_member_are_its_overrides_and_implementations() {
        let semantic = project();
        let implementations = |marker: &str| {
            let mut found = ask(
                &semantic,
                "Shapes.cs",
                marker,
                0,
                |semantic, path, offset| semantic.implementations(path, offset, None),
            );
            found.sort();
            found
        };
        assert_eq!(
            implementations("Area();\n    string"),
            vec!["Geo.Circle.Area", "Geo.Square.IShape.Area", "Geo.Unit.Area"]
        );
        assert_eq!(
            implementations("Area();\n    public virtual"),
            vec!["Geo.Circle.Area", "Geo.Unit.Area"]
        );
        // A virtual member with a body is an implementation itself.
        assert_eq!(
            implementations("Name => \"shape\""),
            vec!["Geo.Circle.Name", "Geo.Shape.Name"]
        );
        assert_eq!(implementations("Describe"), vec!["Geo.Shape.Describe"]);
    }

    #[test]
    fn implementations_of_a_generic_interface_member_substitute_its_parameter() {
        let semantic = project();
        let mut found = ask(
            &semantic,
            "Generic.cs",
            "Find(int id);",
            0,
            |semantic, path, offset| semantic.implementations(path, offset, None),
        );
        found.sort();
        assert_eq!(found, vec!["Geo.Repository`1.Find", "Geo.Shapes.Find"]);
    }

    #[test]
    fn derived_types_and_derived_interfaces_are_asked_for_apart() {
        let semantic = project();
        let derived = |interfaces: bool| {
            let mut found = ask(
                &semantic,
                "Shapes.cs",
                "IShape\n{",
                0,
                |semantic, path, offset| semantic.derived_types(path, offset, None, interfaces),
            );
            found.sort();
            found
        };
        assert_eq!(
            derived(false),
            vec!["Geo.Circle", "Geo.Shape", "Geo.Square", "Geo.Unit"]
        );
        assert_eq!(derived(true), vec!["Geo.ISolid"]);
    }

    fn callers(calls: &[IncomingCall]) -> Vec<(String, usize, bool)> {
        calls
            .iter()
            .map(|call| {
                (
                    format!("{}.{}", call.from.container, call.from.name),
                    call.spans.len(),
                    call.through_base,
                )
            })
            .collect()
    }

    #[test]
    fn incoming_calls_include_calls_through_what_a_member_overrides() {
        let semantic = project();
        let area = symbol(&semantic, "Shapes.cs", "Area() => 3.14", 0);
        let calls = semantic.incoming_calls(area);
        assert_eq!(
            callers(&calls),
            vec![
                ("Geo.Canvas.One".to_string(), 1, false),
                ("Geo.Unit.Area".to_string(), 1, false),
                ("Geo.Canvas.Total".to_string(), 1, true),
                ("Geo.Shape.Describe".to_string(), 1, true),
            ]
        );
        // Each call is a span of its caller's file, on the name called.
        let one = &calls[0];
        assert_eq!(one.path, PathBuf::from("/p/Canvas.cs"));
        assert_eq!(one.spans[0].start(), at(CANVAS, "Area(); }\n}", 0));
    }

    #[test]
    fn incoming_calls_to_a_constructor_are_news_and_base_calls() {
        let semantic = project();
        let constructor = symbol(&semantic, "Shapes.cs", "Circle(double", 0);
        let calls = semantic.incoming_calls(constructor);
        let mut found = callers(&calls);
        found.sort();
        assert_eq!(
            found,
            vec![
                ("Geo.Canvas.Fill".to_string(), 1, false),
                ("Geo.Canvas.One".to_string(), 1, false),
                ("Geo.Shapes.Find".to_string(), 1, false),
                ("Geo.Unit.Unit".to_string(), 1, false),
            ]
        );
    }

    #[test]
    fn incoming_calls_from_an_accessor_and_a_lambda() {
        let semantic = project();
        let find = symbol(&semantic, "Generic.cs", "Find(int id) { return new", 0);
        let calls = semantic.incoming_calls(find);
        assert_eq!(
            callers(&calls),
            vec![("Geo.Canvas.Current".to_string(), 1, false)]
        );
        assert_eq!(calls[0].from.kind, DeclarationKind::Property);

        let unit_area = symbol(&semantic, "Shapes.cs", "Area() => base", 0);
        let calls = semantic.incoming_calls(unit_area);
        // A lambda's call is its method's. Calls to what `Unit.Area`
        // overrides may reach it too — but not `base.Area()` in itself,
        // which never dispatches.
        assert_eq!(
            callers(&calls),
            vec![
                ("Geo.Canvas.Later".to_string(), 1, false),
                ("Geo.Canvas.Total".to_string(), 1, true),
                ("Geo.Canvas.One".to_string(), 1, true),
                ("Geo.Shape.Describe".to_string(), 1, true),
            ]
        );
    }

    fn callees(calls: &[OutgoingCall]) -> Vec<String> {
        calls
            .iter()
            .map(|call| format!("{}.{}", call.to.container, call.to.name))
            .collect()
    }

    #[test]
    fn outgoing_calls_are_what_the_body_calls_in_order() {
        let semantic = project();
        let one = symbol(&semantic, "Canvas.cs", "One", 0);
        let calls = semantic.outgoing_calls(one);
        assert_eq!(
            callees(&calls),
            vec!["Geo.Circle.Circle", "Geo.Circle.Area"]
        );
        assert_eq!(calls[1].spans[0].start(), at(CANVAS, "Area(); }\n}", 0));

        let fill = symbol(&semantic, "Later.cs", "Fill", 0);
        assert_eq!(
            callees(&semantic.outgoing_calls(fill)),
            vec![
                "Geo.Repository`1.Add",
                "Geo.Circle.Circle",
                "Geo.Canvas.Total"
            ]
        );

        // A lambda's calls are its method's; a property's, its accessors'.
        let later = symbol(&semantic, "Later.cs", "Later", 0);
        assert_eq!(
            callees(&semantic.outgoing_calls(later)),
            vec!["Geo.Unit.Unit", "Geo.Unit.Area"]
        );
        let current = symbol(&semantic, "Canvas.cs", "Current", 0);
        assert_eq!(
            callees(&semantic.outgoing_calls(current)),
            vec!["Geo.Shapes.Find"]
        );
        let describe = symbol(&semantic, "Shapes.cs", "Describe", 0);
        assert_eq!(
            callees(&semantic.outgoing_calls(describe)),
            vec!["Geo.Shape.Name", "Geo.Shape.Area"]
        );
    }

    #[test]
    fn a_call_hierarchy_item_says_what_and_where() {
        let semantic = project();
        let item = semantic
            .call_hierarchy_item(Path::new("/p/Canvas.cs"), at(CANVAS, "c.Area", 2), None)
            .expect("an item");
        assert_eq!(item.name, "Area");
        assert_eq!(item.container, "Geo.Circle");
        assert_eq!(item.kind, DeclarationKind::Method);
        assert_eq!(item.detail, "double Area()");
        let Some(Place::Source { path, span }) = &item.place else {
            panic!("a place in the source: {item:?}");
        };
        assert_eq!(path, Path::new("/p/Shapes.cs"));
        assert_eq!(span.start(), at(SHAPES, "Area() => 3.14", 0));
        let full = item.full.expect("the whole declaration");
        assert_eq!(
            full.start(),
            at(SHAPES, "public override double Area() => 3.14", 0)
        );

        // A type is not something that is called.
        assert!(
            semantic
                .call_hierarchy_item(
                    Path::new("/p/Canvas.cs"),
                    at(CANVAS, "Shapes shapes", 0),
                    None
                )
                .is_none()
        );
    }

    #[test]
    fn a_key_finds_its_symbol_again() {
        let semantic = project();
        for (name, marker) in [
            ("Shapes.cs", "Area() => 3.14"),
            ("Shapes.cs", "Area() => Side"),
            ("Shapes.cs", "Circle(double"),
            ("Shapes.cs", "Name => \"circle\""),
            ("Generic.cs", "Add(T item) {"),
            ("Generic.cs", "Repository<T> :"),
            ("Canvas.cs", "shapes ="),
        ] {
            let symbol = symbol(&semantic, name, marker, 0);
            let key = semantic.symbol_key(symbol);
            assert_eq!(semantic.symbol_by_key(&key), Some(symbol), "{key}");
        }
        // And in a compilation built again from the same files.
        let area = symbol(&semantic, "Shapes.cs", "Area() => 3.14", 0);
        let key = semantic.symbol_key(area);
        let again = project();
        let found = again.symbol_by_key(&key).expect("found again");
        assert_eq!(again.hierarchy_item(found).container, "Geo.Circle");
    }

    #[test]
    fn a_type_hierarchy_goes_up_one_level_and_down_one_level() {
        let semantic = project();
        let item = semantic
            .type_hierarchy_item(Path::new("/p/Canvas.cs"), at(CANVAS, "c.Area", 0), None)
            .expect("the type of `c`");
        assert_eq!(item.name, "Circle");
        let item_names = |items: Vec<HierarchyItem>| -> Vec<String> {
            let mut names: Vec<String> = items.into_iter().map(|item| item.name).collect();
            names.sort();
            names
        };
        assert_eq!(
            item_names(semantic.supertypes_of(item.symbol)),
            vec!["Shape"]
        );
        let shape = semantic.symbol_by_key("T:Geo.Shape").expect("Shape");
        assert_eq!(
            item_names(semantic.supertypes_of(shape)),
            vec!["IShape", "Object"]
        );
        assert_eq!(item_names(semantic.subtypes_of(shape)), vec!["Circle"]);
        let interface = semantic.symbol_by_key("T:Geo.IShape").expect("IShape");
        assert_eq!(
            item_names(semantic.subtypes_of(interface)),
            vec!["ISolid", "Shape", "Square"]
        );
        let generic = semantic
            .symbol_by_key("T:Geo.Repository`1")
            .expect("Repository");
        assert_eq!(semantic.hierarchy_item(generic).name, "Repository<T>");
    }

    #[test]
    fn an_edited_file_is_asked_about_as_it_reads_now() {
        let semantic = project();
        let edited = CANVAS.replace("namespace Geo;\n", "namespace Geo;\n\n// moved\n");
        let offset = at(&edited, "c.Area", 2);
        let (_, found) = semantic
            .bases(Path::new("/p/Canvas.cs"), offset, Some(&edited))
            .expect("resolved in the edited text");
        assert_eq!(names(&found), vec!["Geo.Shape.Area", "Geo.IShape.Area"]);
        let item = semantic
            .call_hierarchy_item(
                Path::new("/p/Canvas.cs"),
                at(&edited, "One", 0),
                Some(&edited),
            )
            .expect("an item");
        let Some(Place::Source { span, .. }) = item.place else {
            panic!("a place");
        };
        assert_eq!(span.start(), at(&edited, "One", 0));
    }

    const DOC_A: &str = r#"public interface IRun { void Run(); }
public interface IGo { void Go(); }
public partial class Doc : IRun
{
    private int count = Compute();
    static int Compute() => 1;
    public void Run() { }
}
"#;

    const DOC_B: &str = r#"public partial class Doc : IGo
{
    void IGo.Go() { Run(); }
}
"#;

    const PROGRAM: &str = "var doc = new Doc();\ndoc.Run();\n";

    fn partial_project() -> Semantic {
        compile(
            &[("A.cs", DOC_A), ("B.cs", DOC_B), ("Program.cs", PROGRAM)],
            false,
        )
        .expect("compiled")
    }

    #[test]
    fn a_partial_type_is_every_part_of_it() {
        let semantic = partial_project();
        let path = Path::new("/p/A.cs");
        let (_, found) = semantic
            .implementations(path, at(DOC_A, "IRun {", 0), None)
            .expect("an answer");
        let places: Vec<(String, String)> = found
            .iter()
            .map(|found| match &found.place {
                Place::Source { path, .. } => (
                    found.name.clone(),
                    path.file_name().unwrap().to_string_lossy().into_owned(),
                ),
                Place::Metadata { .. } => panic!("in the project"),
            })
            .collect();
        assert_eq!(
            places,
            vec![
                ("Doc".to_string(), "A.cs".to_string()),
                ("Doc".to_string(), "B.cs".to_string())
            ]
        );
        // Its bases are what either part names.
        let (_, found) = semantic
            .bases(path, at(DOC_A, "Doc :", 0), None)
            .expect("an answer");
        let mut found = names(&found);
        found.sort();
        assert_eq!(found, vec!["IGo", "IRun"]);
        // And an explicit implementation in one part implements an
        // interface the other part lists.
        let (_, found) = semantic
            .bases(Path::new("/p/B.cs"), at(DOC_B, "Go()", 0), None)
            .expect("an answer");
        assert_eq!(names(&found), vec!["IGo.Go"]);
    }

    #[test]
    fn callers_can_be_a_field_initializer_and_top_level_statements() {
        let semantic = partial_project();
        let compute = semantic
            .symbol_by_key("M:Doc|Compute`0()")
            .expect("Compute");
        let calls = semantic.incoming_calls(compute);
        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].from.name, "count");
        assert_eq!(calls[0].from.kind, DeclarationKind::Field);

        let run = semantic.symbol_by_key("M:Doc|Run`0()").expect("Run");
        let calls = semantic.incoming_calls(run);
        let mut from: Vec<(String, bool)> = calls
            .iter()
            .map(|call| (call.from.name.clone(), call.through_base))
            .collect();
        from.sort();
        assert_eq!(
            from,
            vec![
                ("<Main>$".to_string(), false),
                ("IGo.Go".to_string(), false)
            ]
        );
        // The explicit implementation calls `Run`; nothing it calls is a
        // field.
        let go = semantic.symbol_by_key("M:Doc|IGo.Go`0()").expect("IGo.Go");
        let calls = semantic.outgoing_calls(go);
        assert_eq!(callees(&calls), vec!["Doc.Run"]);
        assert_eq!(calls[0].path, PathBuf::from("/p/B.cs"));
    }

    #[test]
    fn an_explicit_name_splits_at_the_last_dot_outside_brackets() {
        assert_eq!(split_explicit("IShape.Area"), Some(("IShape", "Area")));
        assert_eq!(
            split_explicit("IComparer<A.B>.Compare"),
            Some(("IComparer<A.B>", "Compare"))
        );
        assert_eq!(split_explicit("Area"), None);
    }
}
