//! Uses of a member that no name stands for.
//!
//! `a + b` calls `operator +`, `m[3]` the indexer, `new()` a constructor,
//! `foreach` four members and `using` one, and none of them writes the name
//! of what it runs. A search that starts from the member's name never meets
//! them, and a project's callers are not only the ones that spell it. The
//! compiler knows: each of these is a node of the bound tree with the symbol
//! the binder chose. This reads them there.
//!
//! The cost is binding, which a name search avoids by looking only at the
//! files that spell the name. So a use is looked for only in the bodies that
//! hold the construct that could make it — `foreach` and `using` for a
//! `Dispose`, a `[` for an indexer, `new(` for a constructor — and the search
//! for the few members that anything can reach (an operator, a conversion,
//! `ToString`) reads every body. The uses found are kept for the project, by
//! the members they reach, so that a walk that asks about several of them
//! binds each body once.
//!
//! A use is implicit when the construct holds no name token for its symbol:
//! `a.M()` is found by the name `M`, and is not repeated here.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use rustlyn_semantics::{
    BinaryOperator, BoundBody, BoundExpression, BoundExpressionKind as E, BoundPattern,
    BoundPatternKind as P, BoundStatement, BoundStatementKind as S, BoundSwitchLabel,
    ConversionKind, MethodKind, Modifiers, SemanticModel, SpecialType, SymbolId, SymbolKind, Type,
    TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::links::body_owners;
use super::walk::{Visited, walk_body, walk_statement};
use super::{Semantic, contains_word, parallel};

/// How a use touches what it reaches. Only a property or an indexer has two
/// accessors, and a caller of one is not a caller of the other.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UseKind {
    /// A call, or any use of something that has no accessors.
    Call,
    /// The getter runs.
    Read,
    /// The setter (or the `init`) runs.
    Write,
    /// Both: `x.P += 1`, `x.P++`, `ref x.P`.
    ReadWrite,
}

/// Constructs a use can come from: the bodies a search looks in.
pub(super) mod construct {
    /// Every body: what an operator, a conversion or a string's `ToString`
    /// can be reached from.
    pub(crate) const BROAD: u32 = 1;
    /// `x[i]`, `x[^1]`, `x[a..b]`, a list pattern.
    pub(crate) const INDEX: u32 = 1 << 1;
    /// `new()`, `with`.
    pub(crate) const NEW: u32 = 1 << 2;
    /// `foreach`.
    pub(crate) const FOREACH: u32 = 1 << 3;
    /// `using (…)`, `using var …`, `await using`.
    pub(crate) const USING: u32 = 1 << 4;
    /// `await`.
    pub(crate) const AWAIT: u32 = 1 << 5;
    /// `var (a, b) = x`, `(a, b) = x`, `x is (var a, var b)`.
    pub(crate) const DECONSTRUCT: u32 = 1 << 6;
    /// `new C { 1, 2 }`, `new C { P = 1 }`, `[1, 2]`.
    pub(crate) const INITIALIZER: u32 = 1 << 7;
    /// `from x in y select z`.
    pub(crate) const QUERY: u32 = 1 << 8;
    /// `lock`.
    pub(crate) const LOCK: u32 = 1 << 9;
    /// `x is [1, ..]`: a list pattern.
    pub(crate) const LISTPAT: u32 = 1 << 10;
}
use construct::{
    AWAIT, BROAD, DECONSTRUCT, FOREACH, INDEX, INITIALIZER, LISTPAT, LOCK, NEW, QUERY, USING,
};

/// One implicit use of a symbol.
#[derive(Clone, Debug)]
pub(super) struct ImplicitUse {
    pub tree: usize,
    /// The member the code is in, as a call hierarchy names it.
    pub caller: SymbolId,
    pub span: TextSpan,
    pub kind: UseKind,
    /// The type the member is run on, where the construct says: a use of an
    /// interface's `Dispose` on an `IEnumerator<int>` is not a use of the
    /// `Dispose` of a type that is no enumerator.
    pub receiver: Option<SymbolId>,
}

/// The implicit uses of a project's members, by the member reached.
#[derive(Default)]
pub(super) struct ImplicitIndex {
    pub by_symbol: HashMap<SymbolId, Vec<ImplicitUse>>,
}

/// The names of the query operators a `from … select …` calls.
const QUERY_METHODS: &[&str] = &[
    "Select",
    "SelectMany",
    "Where",
    "OrderBy",
    "OrderByDescending",
    "ThenBy",
    "ThenByDescending",
    "GroupBy",
    "Join",
    "GroupJoin",
    "Cast",
    "OfType",
];

/// Calls of the framework that turn an argument into text with its
/// `ToString`: what `Console.WriteLine(m)` and `string.Format("{0}", m)` do.
const STRINGIFIERS: &[&str] = &[
    "Write",
    "WriteLine",
    "Format",
    "Concat",
    "Append",
    "AppendLine",
    "AppendFormat",
    "Insert",
    "Join",
    "Log",
    "LogWarning",
    "LogError",
    "LogFormat",
    "Print",
    "AppendFormatted",
];

impl Semantic {
    /// The constructs that can reach `target` without naming it; 0 when
    /// nothing can.
    pub(super) fn constructs_reaching(&self, target: SymbolId) -> u32 {
        let symbols = self.compilation.symbols();
        let found = symbols.get(target);
        match found.kind {
            SymbolKind::Method => {
                let Some(method) = found.as_method() else {
                    return 0;
                };
                match method.method_kind {
                    MethodKind::Operator | MethodKind::Conversion => BROAD,
                    MethodKind::Constructor => NEW,
                    MethodKind::Ordinary => {
                        let name = found.name.as_str();
                        let name =
                            super::hierarchy::split_explicit(name).map_or(name, |(_, name)| name);
                        match name {
                            "Dispose" | "DisposeAsync" => USING | FOREACH,
                            "GetEnumerator" | "MoveNext" | "MoveNextAsync"
                            | "GetAsyncEnumerator" => FOREACH,
                            "GetAwaiter" | "GetResult" | "OnCompleted" | "UnsafeOnCompleted" => {
                                AWAIT
                            }
                            "Deconstruct" => DECONSTRUCT | FOREACH,
                            "Add" => INITIALIZER,
                            "ToString" => BROAD,
                            "EnterScope" => LOCK,
                            "Slice" => INDEX,
                            name if QUERY_METHODS.contains(&name) => QUERY,
                            _ => 0,
                        }
                    }
                    _ => 0,
                }
            }
            SymbolKind::Property => {
                let Some(property) = found.as_property() else {
                    return 0;
                };
                let mut mask = 0;
                if property.is_indexer {
                    mask |= INDEX;
                }
                match found.name.as_str() {
                    "Current" => mask |= FOREACH,
                    "IsCompleted" => mask |= AWAIT,
                    "Length" | "Count" => mask |= LISTPAT,
                    _ => {}
                }
                // `new C { P = 1 }` and `o with { P = 1 }` call the setter
                // without a name the call could be searched by.
                if property.has_set || property.has_init {
                    mask |= INITIALIZER | NEW;
                }
                mask
            }
            _ => 0,
        }
    }

    /// The names a body can mention to hold a value of the type `container`,
    /// of one derived from it, or of a base class of it — a use through a
    /// base class is a use that may run the member; one through an interface
    /// is every implementation's, and not followed: the types' own names,
    /// and the names of the project's members that are declared with such a
    /// type or take one. A member that does none of that is not in a body that
    /// has one, unless the value comes out of something this does not see —
    /// a `dynamic`, a generic parameter inferred from a value of the type.
    fn reaching_names(&self, container: SymbolId) -> Arc<Reach> {
        if let Some(known) = self
            .reaching
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&container)
        {
            return known.clone();
        }
        let symbols = self.compilation.symbols();
        let model = SemanticModel::new(&self.compilation, 0);
        let mut roots = vec![container];
        roots.extend(
            self.supertypes(&model, container)
                .into_iter()
                .map(|supertype| supertype.symbol)
                .filter(|&ty| {
                    // Every type is an `object`: a body that has one has no
                    // more to say about this.
                    symbols.get(ty).type_kind() != Some(TypeKind::Interface)
                        && !matches!(
                            symbols.qualified_name(ty).as_str(),
                            "System.Object"
                                | "System.ValueType"
                                | "System.Enum"
                                | "System.Delegate"
                                | "System.MulticastDelegate"
                        )
                }),
        );
        let mut types: HashSet<SymbolId> = HashSet::new();
        for root in roots {
            types.insert(root);
            types.extend(self.derived(root, true));
        }
        let mut names: HashSet<String> = types
            .iter()
            .map(|&ty| symbols.get(ty).name.clone())
            .collect();
        let mut holders: HashSet<SymbolId> = HashSet::new();
        for member in self.member_types() {
            if member.mentions.iter().any(|ty| types.contains(ty)) {
                names.insert(member.name.clone());
                holders.extend(member.holder);
            }
        }
        for holder in holders {
            names.insert(symbols.get(holder).name.clone());
            for derived in self.derived(holder, true) {
                names.insert(symbols.get(derived).name.clone());
            }
        }
        let reach = Arc::new(Reach { names, types });
        self.reaching
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(container, reach.clone());
        reach
    }

    /// What each member of the project says about the types it is written
    /// with, worked out once.
    fn member_types(&self) -> &[MemberTypes] {
        self.member_types.get_or_init(|| {
            let symbols = self.compilation.symbols();
            let model = SemanticModel::new(&self.compilation, 0);
            let mut found = Vec::new();
            for member in symbols.iter() {
                if !matches!(
                    member.kind,
                    SymbolKind::Field
                        | SymbolKind::Property
                        | SymbolKind::Method
                        | SymbolKind::Event
                ) || !member
                    .locations
                    .iter()
                    .any(|location| self.paths.contains_key(&location.tree))
                {
                    continue;
                }
                let parameters: &[SymbolId] = if let Some(method) = member.as_method() {
                    &method.parameters
                } else if let Some(property) = member.as_property() {
                    &property.parameters
                } else {
                    &[]
                };
                let mut mentions = HashSet::new();
                for symbol in std::iter::once(member.id).chain(parameters.iter().copied()) {
                    named_types(&model.type_of_symbol(symbol), &mut mentions);
                }
                if mentions.is_empty() {
                    continue;
                }
                // An indexer has no name to write, and neither has the
                // `GetEnumerator` of a `foreach`: their container's is what
                // stands for them.
                let holder = (member
                    .as_property()
                    .is_some_and(|property| property.is_indexer)
                    || PATTERN_PRODUCERS.contains(&member.name.as_str()))
                .then_some(member.container)
                .flatten();
                found.push(MemberTypes {
                    name: spelling(symbols, member.id).to_owned(),
                    holder,
                    mentions: mentions.into_iter().collect(),
                });
            }
            found
        })
    }

    /// The implicit uses of what a value of the type `container` can run,
    /// in the bodies that hold a construct of `mask` and mention what can
    /// bring such a value. Made once for each, and every use found in them
    /// is kept.
    pub(super) fn implicit_index(&self, mask: u32, container: SymbolId) -> Arc<ImplicitIndex> {
        if let Some(index) = self
            .implicit
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&(mask, container))
        {
            return index.clone();
        }
        let reach = self.reaching_names(container);
        let trees: Vec<usize> = self.paths.keys().copied().collect();
        let found = parallel(trees.len(), |at| {
            self.implicit_in_tree(trees[at], mask, &reach)
        });
        let mut index = ImplicitIndex::default();
        for (symbol, found) in found.into_iter().flatten() {
            index.by_symbol.entry(symbol).or_default().push(found);
        }
        let index = Arc::new(index);
        self.implicit
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert((mask, container), index.clone());
        index
    }

    /// Every implicit use in one file's bodies that hold a construct of
    /// `mask`.
    fn implicit_in_tree(
        &self,
        tree: usize,
        mask: u32,
        reach: &Reach,
    ) -> Vec<(SymbolId, ImplicitUse)> {
        let Some(text) = self
            .compilation
            .trees()
            .source(tree)
            .map(|source| source.text())
        else {
            return Vec::new();
        };
        if !text_may_hold(text, mask) {
            return Vec::new();
        }
        let Some(mut view) = self.view(tree) else {
            return Vec::new();
        };
        let mut found = Vec::new();
        for owner in body_owners(&view.root) {
            if mask != BROAD && owner_constructs(&owner) & mask == 0 {
                continue;
            }
            let Some(caller) = view.caller_of(&owner) else {
                continue;
            };
            // A body reaches a value of the type by a name it mentions, or
            // as `this` in the type.
            if !self.in_types(caller, &reach.types)
                && !owner.descendant_tokens().any(|token| {
                    token.kind() == SyntaxKind::IdentifierToken
                        && reach.names.contains(token.value_text())
                })
            {
                continue;
            }
            let Some(body) = view.body_of(owner.clone()) else {
                continue;
            };
            for (span, symbol, kind, receiver) in
                self.implicit_symbols(&view.model, &body, &owner, text)
            {
                found.push((
                    symbol,
                    ImplicitUse {
                        tree,
                        caller,
                        span,
                        kind,
                        receiver,
                    },
                ));
            }
        }
        found
    }

    /// The symbols a bound body reaches without a name for them, with the
    /// span of the construct that reaches them.
    pub(super) fn implicit_symbols(
        &self,
        model: &SemanticModel<'_>,
        body: &BoundBody,
        owner: &SyntaxNode,
        text: &str,
    ) -> Vec<(TextSpan, SymbolId, UseKind, Option<SymbolId>)> {
        let within = owner.span();
        // The names the binder recorded, by where they start: a construct
        // that has one for its own symbol was found by that name already.
        let mut named: Vec<(u32, u32, SymbolId)> = body
            .symbols
            .iter()
            .filter(|(at, _)| within.contains_span(**at))
            .map(|(at, symbol)| (at.start(), at.end(), *symbol))
            .collect();
        named.sort_unstable();
        let mut collector = Collector {
            semantic: self,
            model,
            access: HashMap::new(),
            found: Vec::new(),
        };
        let mut awaited: Vec<&BoundStatement> = Vec::new();
        walk_body(body, &mut |visited| match visited {
            Visited::Expression(expression) => collector.expression(expression),
            Visited::Statement(statement) => {
                collector.statement(statement);
                if let S::Using { resources, .. } = &statement.kind {
                    awaited.extend(resources.iter().filter_map(|r| r.awaited.as_deref()));
                }
            }
        });
        for statement in awaited {
            walk_statement(body, statement, &mut |visited| {
                if let Visited::Expression(expression) = visited {
                    collector.expression(expression);
                }
            });
        }
        let symbols = self.compilation.symbols();
        let Collector { found, .. } = collector;
        found
            .into_iter()
            .filter(|(span, symbol, _, _)| {
                !named_in(&named, text, *span, spelling(symbols, *symbol))
            })
            .map(|(span, symbol, kind, receiver)| {
                // An indexer is used by the whole `x[i]`, which is what a
                // text that looks at what is done to it reads; any other
                // construct is placed where it begins.
                let indexer = symbols
                    .get(symbol)
                    .as_property()
                    .is_some_and(|property| property.is_indexer);
                let shown = if indexer {
                    span
                } else {
                    first_token(span, text)
                };
                (shown, symbol, kind, receiver)
            })
            .collect()
    }
}

impl Semantic {
    /// Whether `member` is in one of `types`, or in a type nested in one.
    fn in_types(&self, member: SymbolId, types: &HashSet<SymbolId>) -> bool {
        let symbols = self.compilation.symbols();
        let mut at = symbols.get(member).container;
        while let Some(holder) = at {
            if types.contains(&holder) {
                return true;
            }
            at = symbols.get(holder).container;
        }
        false
    }

    /// Whether `symbol` is declared in one of the project's files rather
    /// than in an assembly.
    fn in_project(&self, symbol: SymbolId) -> bool {
        self.compilation
            .symbols()
            .get(symbol)
            .locations
            .iter()
            .any(|location| self.paths.contains_key(&location.tree))
    }

    /// The member of the class or struct `ty` that implements the interface
    /// member `member`, when `member` is an interface's and `ty` lists that
    /// interface: `using (bag)` runs `Bag.Dispose`, not the interface's.
    fn concrete(&self, model: &SemanticModel<'_>, ty: &Type, member: SymbolId) -> SymbolId {
        let symbols = self.compilation.symbols();
        let Type::Named { symbol: ty, .. } = ty else {
            return member;
        };
        let Some(interface) = symbols.get(member).container else {
            return member;
        };
        if symbols.get(interface).type_kind() != Some(TypeKind::Interface)
            || symbols.get(*ty).type_kind() == Some(TypeKind::Interface)
        {
            return member;
        }
        self.supertypes(model, *ty)
            .into_iter()
            .find(|supertype| supertype.symbol == interface)
            .and_then(|supertype| self.implementation_in(model, *ty, member, &supertype))
            .unwrap_or(member)
    }
}

/// What can bring a body a value of a type: the names a body mentions, and
/// the types whose members have the value as `this`.
#[derive(Debug, Default)]
pub(super) struct Reach {
    names: HashSet<String>,
    types: HashSet<SymbolId>,
}

/// A member of the project and the types its signature mentions.
pub(super) struct MemberTypes {
    /// What a use of it is written with.
    name: String,
    /// For an indexer, and for a member that makes the object a construct
    /// runs members of (`GetEnumerator`, `GetAwaiter`) without naming it:
    /// the type it is in, which is what stands for it.
    holder: Option<SymbolId>,
    mentions: Vec<SymbolId>,
}

/// The members that make the object `foreach` and `await` run members of.
const PATTERN_PRODUCERS: &[&str] = &["GetEnumerator", "GetAsyncEnumerator", "GetAwaiter"];

/// The types `ty` is made of: itself, its type arguments, its elements, what
/// it points at.
fn named_types(ty: &Type, found: &mut HashSet<SymbolId>) {
    match ty {
        Type::Named {
            symbol,
            type_arguments,
        } => {
            found.insert(*symbol);
            for argument in type_arguments {
                named_types(argument, found);
            }
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            named_types(element, found);
        }
        Type::Tuple(elements) => {
            for element in elements {
                named_types(&element.ty, found);
            }
        }
        _ => {}
    }
}

/// The span of the first token at the start of `span`, so that a use is
/// placed where the construct begins.
fn first_token(span: TextSpan, text: &str) -> TextSpan {
    let start = span.start() as usize;
    let rest = text.get(start..).unwrap_or("");
    let length = rest
        .char_indices()
        .find(|(_, c)| c.is_whitespace())
        .map_or(rest.len(), |(at, _)| at)
        .min(span.length() as usize)
        .max(1);
    TextSpan::new(span.start(), length as u32)
}

/// The name a construct would write to reach `symbol`: a constructor's is
/// its type's.
fn spelling(symbols: &rustlyn_semantics::Symbols, symbol: SymbolId) -> &str {
    let found = symbols.get(symbol);
    if found
        .as_method()
        .is_some_and(|method| method.method_kind == MethodKind::Constructor)
        && let Some(container) = found.container
    {
        return &symbols.get(container).name;
    }
    super::hierarchy::split_explicit(&found.name).map_or(found.name.as_str(), |(_, name)| name)
}

/// Whether a name the binder recorded inside `span` is `name`: the
/// construct spells what it reaches.
fn named_in(named: &[(u32, u32, SymbolId)], text: &str, span: TextSpan, name: &str) -> bool {
    let from = named.partition_point(|(start, _, _)| *start < span.start());
    named[from..]
        .iter()
        .take_while(|(start, _, _)| *start < span.end())
        .any(|(start, end, _)| {
            *end <= span.end() && text.get(*start as usize..*end as usize) == Some(name)
        })
}

/// What a walk of a bound body collects.
struct Collector<'a, 'm> {
    semantic: &'a Semantic,
    model: &'a SemanticModel<'m>,
    /// How the targets of assignments are used, by span.
    access: HashMap<TextSpan, UseKind>,
    found: Vec<(TextSpan, SymbolId, UseKind, Option<SymbolId>)>,
}

impl Collector<'_, '_> {
    fn push(&mut self, span: TextSpan, symbol: SymbolId, kind: UseKind) {
        self.found.push((span, symbol, kind, None));
    }

    /// A use of `symbol` run on a value of type `receiver`.
    fn push_on(&mut self, span: TextSpan, symbol: SymbolId, kind: UseKind, receiver: &Type) {
        let on = receiver.symbol();
        self.found.push((span, symbol, kind, on));
    }

    fn mark(&mut self, target: &BoundExpression, kind: UseKind) {
        self.access.insert(target.span, kind);
    }

    fn expression(&mut self, expression: &BoundExpression) {
        let span = expression.span;
        match &expression.kind {
            E::Assignment { target, .. } => self.mark(target, UseKind::Write),
            E::CompoundAssignment { target, .. } => self.mark(target, UseKind::ReadWrite),
            E::Increment { target, method, .. } => {
                self.mark(target, UseKind::ReadWrite);
                if let Some(method) = method {
                    self.push(span, *method, UseKind::Call);
                }
            }
            E::RefArgument { kind, operand } => {
                let how = if matches!(kind, rustlyn_semantics::RefKind::Out) {
                    UseKind::Write
                } else {
                    UseKind::ReadWrite
                };
                self.mark(operand, how);
            }
            E::Property { property, .. } => {
                let kind = self.access.get(&span).copied().unwrap_or(UseKind::Read);
                self.push(span, *property, kind);
            }
            E::IndexerAccess { indexer, .. } => {
                let kind = self.access.get(&span).copied().unwrap_or(UseKind::Read);
                self.push(span, *indexer, kind);
            }
            E::Call {
                method,
                arguments,
                receiver,
                ..
            } => {
                match receiver {
                    Some(receiver) => {
                        self.push_on(span, *method, UseKind::Call, &receiver.ty);
                    }
                    None => self.push(span, *method, UseKind::Call),
                }
                self.stringified(*method, arguments);
            }
            E::DelegateCreation { method, .. } => self.push(span, *method, UseKind::Call),
            E::ObjectCreation {
                constructor: Some(constructor),
                ..
            } => self.push(span, *constructor, UseKind::Call),
            E::Await {
                awaiting: Some(awaiting),
                ..
            } => {
                self.push(span, awaiting.get_awaiter, UseKind::Call);
                self.push(span, awaiting.is_completed, UseKind::Read);
                self.push(span, awaiting.get_result, UseKind::Call);
            }
            E::StringInsert { value, .. } => self.push_to_string(value),
            E::Binary {
                operator: BinaryOperator::Add,
                left,
                right,
            } => {
                let string = self.semantic.compilation.special_type(SpecialType::String);
                let is_string = |e: &BoundExpression| matches!(&e.ty, Type::Named { symbol, .. } if Some(*symbol) == string);
                if is_string(left) && !is_string(right) {
                    self.push_to_string(right);
                } else if is_string(right) && !is_string(left) {
                    self.push_to_string(left);
                }
            }
            E::With { receiver, .. } => {
                if let Some(copy) = self.copy_constructor(&receiver.ty) {
                    self.push(span, copy, UseKind::Call);
                }
            }
            E::IsPattern { pattern, .. } => self.pattern(pattern),
            E::Switch { arms, .. } => {
                for arm in arms {
                    self.pattern(&arm.pattern);
                }
            }
            _ => {}
        }
    }

    fn statement(&mut self, statement: &BoundStatement) {
        let span = statement.span;
        match &statement.kind {
            S::ForEach {
                enumeration: Some(enumeration),
                collection,
                ..
            } => {
                let span = collection.span;
                self.push(span, enumeration.get_enumerator, UseKind::Call);
                self.push(span, enumeration.move_next, UseKind::Call);
                self.push(span, enumeration.current, UseKind::Read);
                if let Some(dispose) = enumeration.dispose {
                    let dispose =
                        self.semantic
                            .concrete(self.model, &enumeration.enumerator_type, dispose);
                    self.push_on(span, dispose, UseKind::Call, &enumeration.enumerator_type);
                }
            }
            S::Using { resources, .. } => {
                for resource in resources {
                    if let Some(dispose) = resource.dispose {
                        let dispose =
                            self.semantic
                                .concrete(self.model, &resource.value.ty, dispose);
                        self.push_on(
                            resource.value.span,
                            dispose,
                            UseKind::Call,
                            &resource.value.ty,
                        );
                    }
                }
            }
            S::Lock {
                scope: Some(scope), ..
            } => {
                self.push(span, scope.enter, UseKind::Call);
                self.push(span, scope.dispose, UseKind::Call);
            }
            S::Switch { sections, .. } => {
                for section in sections {
                    for label in &section.labels {
                        if let BoundSwitchLabel::Case(case) = label {
                            self.pattern(&case.pattern);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// What a pattern calls: the `Deconstruct` of a positional one, the
    /// properties of a property pattern, the length and indexer of a list
    /// pattern.
    fn pattern(&mut self, pattern: &BoundPattern) {
        let span = pattern.span;
        match &pattern.kind {
            P::Recursive(recursive) => {
                if let Some(deconstruct) = recursive.deconstruct {
                    self.push(span, deconstruct, UseKind::Call);
                }
                for (property, inner) in &recursive.properties {
                    self.push(span, *property, UseKind::Read);
                    self.pattern(inner);
                }
                for inner in &recursive.positional {
                    self.pattern(inner);
                }
            }
            P::List(list) => {
                if let Some(length) = list.length {
                    self.push(span, length, UseKind::Read);
                }
                if let Some(indexer) = list.indexer {
                    self.push(span, indexer, UseKind::Read);
                }
                for inner in list.patterns() {
                    self.pattern(inner);
                }
            }
            P::And(a, b) | P::Or(a, b) => {
                self.pattern(a);
                self.pattern(b);
            }
            P::Not(inner) => self.pattern(inner),
            P::UnionCase {
                try_get_value,
                inner,
                ..
            } => {
                self.push(span, *try_get_value, UseKind::Call);
                self.pattern(inner);
            }
            _ => {}
        }
    }

    /// The arguments of a call of the framework that writes them as text.
    fn stringified(&mut self, method: SymbolId, arguments: &[BoundExpression]) {
        let symbols = self.semantic.compilation.symbols();
        let found = symbols.get(method);
        if !STRINGIFIERS.contains(&found.name.as_str()) || self.semantic.in_project(method) {
            return;
        }
        for argument in arguments {
            match &argument.kind {
                // `params object[]` spelled as the arguments it holds.
                E::ArrayCreation { elements, .. } => {
                    for element in elements {
                        self.push_to_string(element);
                    }
                }
                _ => self.push_to_string(argument),
            }
        }
    }

    /// `value` is written as text: the `ToString` its static type shows
    /// runs. A value of a type that declares none, and one the static type
    /// does not tell (an `object`, an interface), is not a use of any.
    fn push_to_string(&mut self, value: &BoundExpression) {
        let mut inner = value;
        while let E::Conversion {
            operand,
            conversion: ConversionKind::Boxing | ConversionKind::ImplicitReference,
            ..
        } = &inner.kind
        {
            inner = operand;
        }
        let Type::Named { symbol, .. } = &inner.ty else {
            return;
        };
        if let Some(to_string) = self.to_string_declared(*symbol) {
            self.push_on(inner.span, to_string, UseKind::Call, &inner.ty);
        }
    }

    /// The `ToString` that `ty` is given by the project's own code: its own
    /// or its nearest base class's.
    fn to_string_declared(&self, ty: SymbolId) -> Option<SymbolId> {
        let symbols = self.semantic.compilation.symbols();
        if symbols.get(ty).type_kind() == Some(TypeKind::Interface) {
            return None;
        }
        let classes = std::iter::once(ty).chain(
            self.semantic
                .supertypes(self.model, ty)
                .into_iter()
                .map(|supertype| supertype.symbol)
                .filter(|&base| symbols.get(base).type_kind() != Some(TypeKind::Interface)),
        );
        for class in classes {
            for &candidate in symbols.lookup(class, "ToString") {
                let found = symbols.get(candidate);
                if found.kind == SymbolKind::Method
                    && !found.modifiers.contains(Modifiers::STATIC)
                    && found
                        .as_method()
                        .is_some_and(|method| method.parameters.is_empty())
                    && self.semantic.in_project(candidate)
                {
                    return Some(candidate);
                }
            }
        }
        None
    }

    /// The copy constructor a record's `with` runs, when the record declares
    /// one: a constructor of one parameter of the record's own type.
    fn copy_constructor(&self, ty: &Type) -> Option<SymbolId> {
        let Type::Named { symbol, .. } = ty else {
            return None;
        };
        let symbols = self.semantic.compilation.symbols();
        symbols
            .lookup(*symbol, ".ctor")
            .iter()
            .copied()
            .find(|&candidate| {
                let found = symbols.get(candidate);
                self.semantic.in_project(candidate)
                    && found.as_method().is_some_and(|method| {
                        method.parameters.len() == 1
                            && matches!(
                                self.model.type_of_symbol(method.parameters[0]),
                                Type::Named { symbol: parameter, .. } if parameter == *symbol
                            )
                    })
            })
    }
}

/// Whether a file's text can hold a construct of `mask`: a cheap test that
/// spares binding the bodies of files that cannot.
fn text_may_hold(text: &str, mask: u32) -> bool {
    if mask & (BROAD | DECONSTRUCT) != 0 {
        return true;
    }
    let bits: [(u32, Holds); 8] = [
        (INDEX, |text| text.contains('[')),
        (NEW, |text| {
            word_then(text, "new", b'(') || contains_word(text, "with")
        }),
        (FOREACH, |text| contains_word(text, "foreach")),
        (USING, uses_resource),
        (AWAIT, |text| contains_word(text, "await")),
        (QUERY, |text| contains_word(text, "from")),
        (LOCK, |text| contains_word(text, "lock")),
        (LISTPAT, has_list_pattern),
    ];
    if mask & INITIALIZER != 0 && has_initializer(text) {
        return true;
    }
    bits.iter()
        .any(|(bit, holds)| mask & bit != 0 && holds(text))
}

/// A test of a file's text for a construct.
type Holds = fn(&str) -> bool;

/// Whether the text has a `[` where a list pattern may begin.
fn has_list_pattern(text: &str) -> bool {
    [
        "is [", "is not [", "case [", "or [", "and [", "([", "{ [", ", [",
    ]
    .iter()
    .any(|mark| text.contains(mark))
}

/// Whether the text has an object or a collection initializer, a `with`
/// expression or a collection expression: `new C { … }`, `new C(…) { … }`,
/// `x with { … }`, `= [ … ]`.
fn has_initializer(text: &str) -> bool {
    if contains_word(text, "with")
        || ["= [", "return [", "([", "=> ["]
            .iter()
            .any(|mark| text.contains(mark))
    {
        return true;
    }
    let bytes = text.as_bytes();
    let mut from = 0;
    while let Some(at) = text[from..].find("new") {
        let mut i = from + at + 3;
        from = i;
        // The type after `new`, then perhaps arguments, then `{`.
        while i < bytes.len()
            && (bytes[i].is_ascii_alphanumeric() || b" \t\r\n_.<>,?[]:".contains(&bytes[i]))
        {
            i += 1;
        }
        if bytes.get(i) == Some(&b'(') {
            let mut depth = 0usize;
            while i < bytes.len() {
                match bytes[i] {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            i += 1;
                            break;
                        }
                    }
                    _ => {}
                }
                i += 1;
            }
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1;
            }
        }
        if bytes.get(i) == Some(&b'{') {
            return true;
        }
    }
    false
}

/// Whether the word `word` is followed, past spaces, by `next`.
fn word_then(text: &str, word: &str, next: u8) -> bool {
    let bytes = text.as_bytes();
    let mut from = 0;
    while let Some(at) = text[from..].find(word) {
        let start = from + at;
        let end = start + word.len();
        let before =
            start == 0 || !(bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_');
        if before {
            let after = text[end..].trim_start_matches([' ', '\t', '\r', '\n']);
            if after.as_bytes().first() == Some(&next)
                && !text[end..].starts_with(|c: char| c.is_alphanumeric() || c == '_')
            {
                return true;
            }
        }
        from = end;
    }
    false
}

/// Whether a `using` of the text holds a resource: it is followed by a `(`
/// or an `=` before a `;`, which a directive for a namespace is not.
fn uses_resource(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut from = 0;
    while let Some(at) = text[from..].find("using") {
        let start = from + at;
        let end = start + 5;
        from = end;
        let before =
            start == 0 || !(bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_');
        let after =
            end >= bytes.len() || !(bytes[end].is_ascii_alphanumeric() || bytes[end] == b'_');
        if !before || !after {
            continue;
        }
        if let Some(stop) = text[end..].find(['(', '=', ';'])
            && bytes[end + stop] != b';'
        {
            return true;
        }
    }
    false
}

/// The constructs of `construct` that a body holds.
pub(super) fn owner_constructs(owner: &SyntaxNode) -> u32 {
    let mut mask = 0;
    for node in owner.descendants() {
        mask |= match node.kind() {
            SyntaxKind::ElementAccessExpression
            | SyntaxKind::ElementBindingExpression
            | SyntaxKind::ImplicitElementAccess
            | SyntaxKind::IndexExpression
            | SyntaxKind::RangeExpression => INDEX,
            SyntaxKind::ListPattern => INDEX | LISTPAT,
            SyntaxKind::ImplicitObjectCreationExpression | SyntaxKind::WithExpression => NEW,
            SyntaxKind::ForEachStatement => FOREACH,
            SyntaxKind::ForEachVariableStatement => FOREACH | DECONSTRUCT,
            SyntaxKind::UsingStatement | SyntaxKind::LocalDeclarationStatement => {
                if node.kind() == SyntaxKind::UsingStatement
                    || node
                        .child_tokens()
                        .any(|token| token.kind() == SyntaxKind::UsingKeyword)
                {
                    USING
                } else {
                    0
                }
            }
            SyntaxKind::AwaitExpression => AWAIT,
            SyntaxKind::PositionalPatternClause
            | SyntaxKind::ParenthesizedVariableDesignation
            | SyntaxKind::TupleExpression => DECONSTRUCT,
            SyntaxKind::ObjectInitializerExpression
            | SyntaxKind::CollectionInitializerExpression
            | SyntaxKind::CollectionExpression => INITIALIZER,
            SyntaxKind::QueryExpression => QUERY,
            SyntaxKind::LockStatement => LOCK,
            _ => 0,
        };
    }
    mask
}

#[cfg(test)]
mod tests;
