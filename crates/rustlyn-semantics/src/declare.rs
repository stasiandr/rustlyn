//! Building the declaration table.
//!
//! One pass over the syntax trees turns every declaration into a symbol. It
//! resolves nothing: a field's type may be a class declared further down the
//! file or in another file, so types are recorded as syntax references and
//! looked up later. Roslyn splits the work the same way, and for the same
//! reason.
//!
//! Declarations that name the same thing are merged rather than duplicated:
//! two `namespace Foo` blocks are one namespace, and two halves of a partial
//! class are one type with two locations.

use std::collections::HashMap;

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken, SyntaxTree, TokenValue};
use rustlyn_text::TextSpan;

use crate::corlib::SpecialType;
use crate::symbol::{
    Accessibility, CallerInfo, Detail, Event, Field, Location, Method, MethodKind, Modifiers,
    NamedType, Parameter, Property, RefKind, SymbolId, SymbolKind, Symbols, SynthesizedType,
    TypeKind, TypeParameter as TypeParameterDetail, TypeSyntaxRef, Variance,
};

/// The trees a [`Declarer`] reads: all parsed already, or being parsed on
/// other threads, each slot filled as its file is done — `None` where parsing
/// it failed. Each comes with its [`TreeFacts`].
#[derive(Clone, Copy)]
pub(crate) enum TreeSource<'a> {
    Parsed(&'a [SyntaxTree], &'a [TreeFacts]),
    Parsing(&'a crate::compilation::ParseQueue<'a>),
}

impl<'a> TreeSource<'a> {
    fn len(self) -> usize {
        match self {
            Self::Parsed(trees, _) => trees.len(),
            Self::Parsing(queue) => queue.slots.len(),
        }
    }

    /// One tree and its facts, waiting for it to be parsed if it is not yet.
    fn get(self, index: usize) -> Option<(&'a SyntaxTree, &'a TreeFacts)> {
        match self {
            Self::Parsed(trees, facts) => Some((trees.get(index)?, facts.get(index)?)),
            Self::Parsing(queue) => {
                let (tree, facts) = queue
                    .get(index)?
                    .as_ref()
                    .expect("a file that failed to parse cannot be declared");
                Some((tree, facts))
            }
        }
    }
}

/// The nodes of one tree that declaring looks for inside bodies, found in one
/// walk over the tree — which is done where the tree is parsed, beside the
/// declarations rather than in front of them — instead of one walk per body.
/// Each list is in source order, which is the order a walk would meet them.
#[derive(Debug, Default)]
pub(crate) struct TreeFacts {
    /// Every local function.
    local_functions: Vec<SyntaxNode>,
    /// Every `new { ... }`.
    anonymous_objects: Vec<SyntaxNode>,
    /// Every name `field`, which in an accessor is the backing field (C# 14).
    field_names: Vec<SyntaxNode>,
}

impl TreeFacts {
    pub(crate) fn of(tree: &SyntaxTree) -> Self {
        let mut facts = Self::default();
        for node in tree.root().descendants() {
            match node.kind() {
                SyntaxKind::LocalFunctionStatement => facts.local_functions.push(node),
                SyntaxKind::AnonymousObjectCreationExpression => {
                    facts.anonymous_objects.push(node);
                }
                SyntaxKind::IdentifierName
                    if node.span().length() == 5 && node.text().trim() == "field" =>
                {
                    facts.field_names.push(node);
                }
                _ => {}
            }
        }
        facts
    }
}

/// The nodes of a list in source order that lie inside `owner`, the owner
/// itself included: what `owner.descendants()` would have met of them.
fn within<'n>(nodes: &'n [SyntaxNode], owner: &SyntaxNode) -> impl Iterator<Item = &'n SyntaxNode> {
    let span = owner.full_span();
    let first = nodes.partition_point(|node| node.full_span().start() < span.start());
    nodes[first..]
        .iter()
        .take_while(move |node| node.full_span().start() <= span.end())
        .filter(move |node| span.contains_span(node.full_span()))
}

/// What declaring produced, handed on to the compilation.
pub(crate) struct Declared {
    pub(crate) symbols: Symbols,
    pub(crate) global: SymbolId,
    pub(crate) diagnostics: Vec<(usize, Diagnostic)>,
    pub(crate) declarations: HashMap<(usize, TextSpan), SymbolId>,
    pub(crate) anonymous: HashMap<Vec<String>, SymbolId>,
}

impl From<Declarer<'_>> for Declared {
    fn from(declarer: Declarer<'_>) -> Self {
        Self {
            global: declarer.global,
            symbols: declarer.symbols,
            diagnostics: declarer.diagnostics,
            declarations: declarer.declarations,
            anonymous: declarer.anonymous,
        }
    }
}

pub(crate) struct Declarer<'a> {
    trees: TreeSource<'a>,
    pub(crate) symbols: Symbols,
    /// Reported problems, each tagged with the file it came from, since a
    /// diagnostic's span alone does not say which one that is.
    pub(crate) diagnostics: Vec<(usize, Diagnostic)>,
    /// Which symbol each declaration node produced, so the semantic model can
    /// get from a piece of syntax back to what it declared.
    pub(crate) declarations: HashMap<(usize, TextSpan), SymbolId>,
    global: SymbolId,
    tree: usize,
    /// Types that may still need the constructor nobody wrote, with the file
    /// and the declaration that would carry its location.
    ///
    /// A partial type declares no constructor until its last part has been
    /// read, so the question cannot be answered where it is asked.
    pending_constructors: Vec<(usize, SyntaxNode, SymbolId, TypeKind)>,
    /// Records whose synthesized members wait for every part to be read,
    /// with the declaration that carries their location.
    pending_records: Vec<(usize, SyntaxNode, SymbolId)>,
    /// Every part of every type, for deciding which primary constructor
    /// parameters are kept in fields once all of them have been read.
    pending_captures: Vec<(usize, SyntaxNode, SymbolId)>,
    /// Type parameters constrained `where T : unmanaged`, with the constraint
    /// as written: the keyword unless a type named `unmanaged` is declared,
    /// which only the end of the declarations can say.
    pending_unmanaged: Vec<(SymbolId, TypeSyntaxRef)>,
    /// Each partial property or indexer declared so far, by its container
    /// and its signature as written, for its other part to find.
    partial_properties: HashMap<(SymbolId, String), SymbolId>,
    /// The class declared for each anonymous object shape, by its property
    /// names in order: `new { i = k, d }` anywhere in the compilation is one
    /// `<>f__AnonymousType0<<i>j__TPar, <d>j__TPar>`.
    pub(crate) anonymous: HashMap<Vec<String>, SymbolId>,
}

impl<'a> Declarer<'a> {
    pub(crate) fn new(trees: TreeSource<'a>) -> Self {
        let mut symbols = Symbols::new();
        let global = symbols.add(SymbolKind::Namespace, "", None, Detail::Namespace);
        Self {
            trees,
            symbols,
            diagnostics: Vec::new(),
            declarations: HashMap::new(),
            global,
            tree: 0,
            pending_constructors: Vec::new(),
            pending_records: Vec::new(),
            pending_captures: Vec::new(),
            pending_unmanaged: Vec::new(),
            partial_properties: HashMap::new(),
            anonymous: HashMap::new(),
        }
    }

    pub(crate) fn declare_all(&mut self) {
        for index in 0..self.trees.len() {
            self.tree = index;
            let Some(root) = self.trees.get(index).map(|(tree, _)| tree.root()) else {
                continue;
            };
            self.declare_members(&root, self.global);
            if root
                .children()
                .any(|child| child.kind() == SyntaxKind::GlobalStatement)
            {
                self.declare_top_level_main(&root);
            }
        }
        // `where T : unmanaged` is a struct constraint and more (C# 7.3) —
        // which metadata says with the value type and constructor bits, and
        // which a `where T : struct` it is passed on to checks — unless the
        // program declares a type of that name.
        let unmanaged_type = self
            .symbols
            .iter()
            .any(|symbol| symbol.kind == SymbolKind::NamedType && symbol.name == "unmanaged");
        for (parameter, reference) in std::mem::take(&mut self.pending_unmanaged) {
            if unmanaged_type {
                break;
            }
            if let Detail::TypeParameter(detail) = &mut self.symbols.get_mut(parameter).detail {
                detail
                    .constraints
                    .retain(|constraint| *constraint != reference);
                detail.value_type = true;
                detail.unmanaged = true;
            }
        }
        // A base record's members first: a derived record's positional
        // parameter may name a property the base already has.
        let pending = std::mem::take(&mut self.pending_records);
        let mut done = std::collections::HashSet::new();
        for index in 0..pending.len() {
            self.declare_record_with_bases(&pending, index, &mut done);
        }
        // Each type's parts, in the order the types were first met: one pass,
        // not a pass over every part for each type — a large program has
        // tens of thousands of both.
        let captures = std::mem::take(&mut self.pending_captures);
        let mut owners: Vec<SymbolId> = Vec::new();
        let mut parts: std::collections::HashMap<SymbolId, Vec<(usize, SyntaxNode)>> =
            std::collections::HashMap::new();
        for (tree, node, owner) in captures {
            let list = parts.entry(owner).or_default();
            if list.is_empty() {
                owners.push(owner);
            }
            list.push((tree, node));
        }
        for owner in owners {
            let list = parts.remove(&owner).unwrap_or_default();
            self.capture_primary_parameters(&list, owner);
        }
        // Only now is it known that a type declares no constructor: the part
        // that declares one may be the last file read.
        for (tree, node, owner, type_kind) in std::mem::take(&mut self.pending_constructors) {
            self.tree = tree;
            self.declare_implicit_constructor(&node, owner, type_kind);
        }
        self.declare_anonymous_types();
    }

    /// Top-level statements are the body of `Program.<Main>$(string[] args)`
    /// (§7.1 of the C# 9 proposal): a class `Program` — the one the source
    /// declares as `partial class Program`, or one made here — with a
    /// static method whose declaration is the compilation unit itself, so
    /// that binding it binds the statements. It returns `int` where a
    /// top-level `return` gives a value, `Task` or `Task<int>` where the
    /// statements `await`.
    fn declare_top_level_main(&mut self, root: &SyntaxNode) {
        let program = self
            .symbols
            .lookup(self.global, "Program")
            .iter()
            .copied()
            .find(|candidate| {
                self.symbols.get(*candidate).kind == SymbolKind::NamedType
                    && self
                        .symbols
                        .get(*candidate)
                        .as_named_type()
                        .is_some_and(|detail| {
                            detail.type_kind == Some(TypeKind::Class) && detail.arity == 0
                        })
            });
        let location = self.location(root);
        // The class is placed at the first statement rather than at the
        // file: the file is where the method is, and one span may name one
        // symbol.
        let first_statement = root
            .children()
            .find(|child| child.kind() == SyntaxKind::GlobalStatement)
            .map_or(location, |statement| self.location(&statement));
        let program = program.unwrap_or_else(|| {
            let id = self.symbols.add(
                SymbolKind::NamedType,
                "Program",
                Some(self.global),
                Detail::NamedType(NamedType {
                    type_kind: Some(TypeKind::Class),
                    ..NamedType::default()
                }),
            );
            let symbol = self.symbols.get_mut(id);
            symbol.locations.push(first_statement);
            symbol.accessibility = Accessibility::Internal;
            symbol.modifiers.insert(Modifiers::PARTIAL);
            id
        });
        let global_statements: Vec<SyntaxNode> = root
            .children()
            .filter(|child| child.kind() == SyntaxKind::GlobalStatement)
            .collect();
        let awaits = global_statements.iter().any(statement_awaits);
        let returns_value = global_statements.iter().any(statement_returns_a_value);
        let returns = match (awaits, returns_value) {
            (false, false) => SynthesizedType::Special(SpecialType::Void),
            (false, true) => SynthesizedType::Special(SpecialType::Int32),
            (true, false) => SynthesizedType::Task,
            (true, true) => SynthesizedType::TaskOfInt32,
        };
        let main = self.symbols.add(
            SymbolKind::Method,
            "<Main>$",
            Some(program),
            Detail::Method(Method {
                synthesized_return: Some(returns),
                method_kind: MethodKind::Ordinary,
                ..Method::default()
            }),
        );
        {
            let symbol = self.symbols.get_mut(main);
            symbol.locations.push(location);
            symbol.accessibility = Accessibility::Private;
            symbol.modifiers.insert(Modifiers::STATIC);
            if awaits {
                symbol.modifiers.insert(Modifiers::ASYNC);
            }
        }
        // The compilation unit is the method's declaration: binding the
        // method binds the unit's statements.
        self.record(root, main);
        // A local function among the statements is the method's, callable
        // from any of them, above or below.
        for statement in &global_statements {
            self.declare_local_functions(statement, main);
        }
        if !self
            .declarations
            .contains_key(&(self.tree, first_statement.span))
        {
            self.declarations
                .insert((self.tree, first_statement.span), program);
        }
        self.declare_record_parameter(
            main,
            "args",
            None,
            Some(SynthesizedType::StringArray),
            RefKind::None,
            location,
        );
    }

    /// Declares a class for every shape of `new { ... }` in the compilation.
    ///
    /// C# has no name for the type of `new { i = key, d }`, but the runtime
    /// needs one, so the language declares it (§12.8.17.7): a sealed class
    /// generic in each property's type, with a read-only property per member
    /// and a constructor taking them in order. Two expressions with the same
    /// names in the same order share it, which is why the shapes are found
    /// up front rather than as the bodies are bound.
    fn declare_anonymous_types(&mut self) {
        let mut shapes: Vec<(Vec<String>, Location)> = Vec::new();
        for index in 0..self.trees.len() {
            let Some((_, facts)) = self.trees.get(index) else {
                continue;
            };
            for node in &facts.anonymous_objects {
                let names = anonymous_member_names(node);
                if !shapes.iter().any(|(shape, _)| *shape == names) {
                    let location = self.location(node);
                    shapes.push((names, location));
                }
            }
        }
        for (ordinal, (names, location)) in shapes.into_iter().enumerate() {
            let ty = self.symbols.add(
                SymbolKind::NamedType,
                format!("<>f__AnonymousType{ordinal}"),
                Some(self.global),
                Detail::NamedType(NamedType {
                    type_kind: Some(TypeKind::Class),
                    arity: names.len(),
                    anonymous: true,
                    ..NamedType::default()
                }),
            );
            {
                let symbol = self.symbols.get_mut(ty);
                symbol.accessibility = Accessibility::Internal;
                symbol.modifiers.insert(Modifiers::SEALED);
            }
            let parameters: Vec<SymbolId> = names
                .iter()
                .map(|name| {
                    self.symbols.add(
                        SymbolKind::TypeParameter,
                        format!("<{name}>j__TPar"),
                        Some(ty),
                        Detail::TypeParameter(TypeParameterDetail::default()),
                    )
                })
                .collect();
            if let Detail::NamedType(detail) = &mut self.symbols.get_mut(ty).detail {
                detail.type_parameters = parameters;
            }
            let constructor = self.symbols.add(
                SymbolKind::Method,
                ".ctor",
                Some(ty),
                Detail::Method(Method {
                    method_kind: MethodKind::Constructor,
                    ..Method::default()
                }),
            );
            self.symbols.get_mut(constructor).accessibility = Accessibility::Public;
            let mut constructor_parameters = Vec::new();
            for (index, name) in names.iter().enumerate() {
                let parameter = self.symbols.add(
                    SymbolKind::Parameter,
                    name.clone(),
                    Some(constructor),
                    Detail::Parameter(Parameter {
                        synthesized: Some(SynthesizedType::TypeParameter(index)),
                        ..Parameter::default()
                    }),
                );
                constructor_parameters.push(parameter);
                let property = self.symbols.add(
                    SymbolKind::Property,
                    name.clone(),
                    Some(ty),
                    Detail::Property(Property {
                        synthesized: Some(SynthesizedType::TypeParameter(index)),
                        has_get: true,
                        ..Property::default()
                    }),
                );
                self.symbols.get_mut(property).accessibility = Accessibility::Public;
            }
            if let Detail::Method(detail) = &mut self.symbols.get_mut(constructor).detail {
                detail.parameters = constructor_parameters;
            }
            // `{ a = 1, b = text }`, and equal where every member is: the
            // same members a record gets, written by the emitter the same
            // way (§12.8.17.4).
            self.declare_record_method(
                ty,
                "ToString",
                Some(SynthesizedType::Special(SpecialType::String)),
                location,
                false,
            );
            let equals = self.declare_record_method(
                ty,
                "Equals",
                Some(SynthesizedType::Special(SpecialType::Boolean)),
                location,
                false,
            );
            self.declare_record_parameter(
                equals,
                "value",
                None,
                Some(SynthesizedType::Special(SpecialType::Object)),
                RefKind::None,
                location,
            );
            self.declare_record_method(
                ty,
                "GetHashCode",
                Some(SynthesizedType::Special(SpecialType::Int32)),
                location,
                false,
            );
            self.anonymous.insert(names, ty);
        }
    }

    /// Notes that `node` declared `id`.
    fn record(&mut self, node: &SyntaxNode, id: SymbolId) {
        self.declarations.insert((self.tree, node.span()), id);
    }

    /// The other part of a partial method already declared in `container`:
    /// a method of the same name, arity and staticness that was itself
    /// written `partial`.
    fn partial_counterpart(
        &self,
        node: &SyntaxNode,
        container: SymbolId,
        token: &rustlyn_syntax::SyntaxToken,
    ) -> Option<SymbolId> {
        let name = explicit_name(node, token.value_text());
        let arity = parameter_count(node);
        let is_static = modifiers_of(node).0.contains(Modifiers::STATIC);
        // `partial void M(int i)` and `partial void M(in int i)` are two
        // methods, each with parts of its own: the ref kinds have to agree.
        let ref_kinds: Vec<RefKind> = node
            .child_of_kind(SyntaxKind::ParameterList)
            .into_iter()
            .flat_map(|list| list.children())
            .filter(|parameter| parameter.kind() == SyntaxKind::Parameter)
            .map(|parameter| {
                parameter
                    .child_tokens()
                    .fold(RefKind::None, |kind, token| match token.kind() {
                        SyntaxKind::RefKeyword => RefKind::Ref,
                        SyntaxKind::OutKeyword => RefKind::Out,
                        SyntaxKind::InKeyword => RefKind::In,
                        SyntaxKind::ReadOnlyKeyword if kind == RefKind::Ref => RefKind::In,
                        _ => kind,
                    })
            })
            .collect();
        self.symbols
            .lookup(container, &name)
            .iter()
            .copied()
            .find(|candidate| {
                let symbol = self.symbols.get(*candidate);
                symbol.kind == SymbolKind::Method
                    && symbol.modifiers.contains(Modifiers::PARTIAL)
                    && symbol.modifiers.contains(Modifiers::STATIC) == is_static
                    && symbol.as_method().is_some_and(|detail| {
                        detail.parameters.len() == arity
                            && detail
                                .parameters
                                .iter()
                                .zip(&ref_kinds)
                                .all(|(parameter, kind)| {
                                    self.symbols
                                        .get(*parameter)
                                        .as_parameter()
                                        .is_none_or(|parameter| parameter.ref_kind == *kind)
                                })
                    })
            })
    }

    /// Makes the implementing part of a partial method the one its symbol
    /// stands for: its node becomes the symbol's only declaration, its
    /// parameter names replace the declaring part's, and the local functions
    /// in its body are declared under it.
    fn take_over_partial(&mut self, node: &SyntaxNode, id: SymbolId) {
        self.declarations.retain(|_, declared| *declared != id);
        self.record(node, id);
        let location = name_token(node).map(|token| self.token_location(&token));
        let parameters = self
            .symbols
            .get(id)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        if let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) {
            let written: Vec<SyntaxNode> = list
                .children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
                .collect();
            for (parameter, node) in parameters.iter().zip(written) {
                // The body names the parameters as this part wrote them,
                // and finds them by this part's syntax — their types too,
                // which name this part's type parameters.
                if let Some(token) = name_token(&node) {
                    let declared = self.symbols.get(*parameter).name.clone();
                    if declared != token.value_text()
                        && let Detail::Parameter(detail) =
                            &mut self.symbols.get_mut(*parameter).detail
                    {
                        detail.declared_name.get_or_insert(declared);
                    }
                    self.symbols.rename(*parameter, token.value_text());
                }
                if let Some(ty) = node.children().find(|child| child.kind().is_type_node()) {
                    let ty = self.type_ref(&ty);
                    if let Detail::Parameter(detail) = &mut self.symbols.get_mut(*parameter).detail
                    {
                        detail.ty = Some(ty);
                    }
                }
                self.record(&node, *parameter);
            }
        }
        if let Some(ty) = node.children().find(|child| child.kind().is_type_node()) {
            let ty = self.type_ref(&ty);
            if let Detail::Method(detail) = &mut self.symbols.get_mut(id).detail {
                detail.return_type = Some(ty);
            }
        }
        // So do its type parameters: `M<T1, T2>(T1 y, T2 x)` implementing
        // `M<T, U>(T x, U y)` names `T1` in its body.
        let type_parameters = self
            .symbols
            .get(id)
            .as_method()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        if let Some(list) = node.child_of_kind(SyntaxKind::TypeParameterList) {
            let written: Vec<SyntaxNode> = list
                .children()
                .filter(|child| child.kind() == SyntaxKind::TypeParameter)
                .collect();
            for (parameter, node) in type_parameters.iter().zip(written) {
                if let Some(token) = name_token(&node) {
                    let declared = self.symbols.get(*parameter).name.clone();
                    if declared != token.value_text()
                        && let Detail::TypeParameter(detail) =
                            &mut self.symbols.get_mut(*parameter).detail
                    {
                        detail.declared_name.get_or_insert(declared);
                    }
                    self.symbols.rename(*parameter, token.value_text());
                }
                self.record(&node, *parameter);
            }
        }
        // `async` and `unsafe` say how the body is compiled, and only the
        // part with the body writes them.
        let written = modifiers_of(node).0;
        let symbol = self.symbols.get_mut(id);
        for modifier in [Modifiers::ASYNC, Modifiers::UNSAFE] {
            if written.contains(modifier) {
                symbol.modifiers.insert(modifier);
            }
        }
        if let Some(location) = location {
            symbol.locations.push(location);
        }
        self.declare_local_functions(node, id);
    }

    /// A declaring part of a partial method met after its implementing part:
    /// the names it writes are the ones callers and metadata know.
    fn keep_declared_names(&mut self, node: &SyntaxNode, id: SymbolId) {
        let Some(detail) = self.symbols.get(id).as_method() else {
            return;
        };
        let (parameters, type_parameters) =
            (detail.parameters.clone(), detail.type_parameters.clone());
        let written = |list: Option<SyntaxNode>, kind: SyntaxKind| -> Vec<String> {
            list.map(|list| {
                list.children()
                    .filter(|child| child.kind() == kind)
                    .filter_map(|child| name_token(&child).map(|t| t.value_text().to_string()))
                    .collect()
            })
            .unwrap_or_default()
        };
        let names = written(
            node.child_of_kind(SyntaxKind::ParameterList),
            SyntaxKind::Parameter,
        );
        for (parameter, name) in parameters.iter().zip(names) {
            let symbol = self.symbols.get_mut(*parameter);
            if symbol.name != name
                && let Detail::Parameter(detail) = &mut symbol.detail
            {
                detail.declared_name = Some(name);
            }
        }
        let names = written(
            node.child_of_kind(SyntaxKind::TypeParameterList),
            SyntaxKind::TypeParameter,
        );
        for (parameter, name) in type_parameters.iter().zip(names) {
            let symbol = self.symbols.get_mut(*parameter);
            if symbol.name != name
                && let Detail::TypeParameter(detail) = &mut symbol.detail
            {
                detail.declared_name = Some(name);
            }
        }
    }

    /// The signature a partial property or indexer is matched with its other
    /// part by: its name and its parameter types as written.
    fn partial_property_key(node: &SyntaxNode, name: &str) -> String {
        let mut key = name.to_string();
        if let Some(list) = node.child_of_kind(SyntaxKind::BracketedParameterList) {
            for parameter in list
                .children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
            {
                key.push('|');
                if let Some(ty) = parameter
                    .children()
                    .find(|child| child.kind().is_type_node())
                {
                    key.extend(ty.text().to_string().chars().filter(|c| !c.is_whitespace()));
                }
            }
        }
        key
    }

    /// Makes the implementing part of a partial property the one its symbol
    /// is declared by: its node, its parameter names and its accessors.
    fn take_over_partial_property(
        &mut self,
        node: &SyntaxNode,
        id: SymbolId,
        ty: Option<TypeSyntaxRef>,
    ) {
        self.declarations.retain(|_, declared| *declared != id);
        self.record(node, id);
        let parameters = self
            .symbols
            .get(id)
            .as_property()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        if let Some(list) = node.child_of_kind(SyntaxKind::BracketedParameterList) {
            let written: Vec<SyntaxNode> = list
                .children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
                .collect();
            for (parameter, node) in parameters.iter().zip(written) {
                if let Some(token) = name_token(&node) {
                    self.symbols.rename(*parameter, token.value_text());
                }
                self.record(&node, *parameter);
            }
        }
        let location = self.location(node);
        self.symbols.get_mut(id).locations.push(location);
        self.declare_accessors(node, id, ty);
    }

    fn report(&mut self, code: ErrorCode, location: Location, args: &[&str]) {
        self.diagnostics
            .push((location.tree, Diagnostic::new(code, location.span, args)));
    }

    fn location(&self, node: &SyntaxNode) -> Location {
        Location::new(self.tree, node.span())
    }

    /// Where an accessor's `value` is: its `set`, `init`, `add` or `remove`,
    /// as Roslyn places it — not the modifiers in front.
    fn accessor_keyword_location(&self, accessor: &SyntaxNode) -> Location {
        accessor
            .child_tokens()
            .find(|token| matches!(token.text(), "set" | "init" | "add" | "remove"))
            .map_or_else(
                || self.location(accessor),
                |token| self.token_location(&token),
            )
    }

    fn token_location(&self, token: &SyntaxToken) -> Location {
        Location::new(self.tree, token.span())
    }

    fn type_ref(&self, node: &SyntaxNode) -> TypeSyntaxRef {
        TypeSyntaxRef(self.location(node))
    }

    /// Walks the children of a compilation unit, namespace or type body.
    fn declare_members(&mut self, container_node: &SyntaxNode, container: SymbolId) {
        for child in container_node.children() {
            match child.kind() {
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration => {
                    let namespace = self.declare_namespace(&child, container);
                    self.declare_members(&child, namespace);
                }
                SyntaxKind::ClassDeclaration
                | SyntaxKind::StructDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::RecordDeclaration
                | SyntaxKind::RecordStructDeclaration
                | SyntaxKind::UnionDeclaration => {
                    self.declare_type(&child, container);
                }
                SyntaxKind::EnumDeclaration => self.declare_enum(&child, container),
                SyntaxKind::DelegateDeclaration => self.declare_delegate(&child, container),
                SyntaxKind::FieldDeclaration => self.declare_field(&child, container, false),
                SyntaxKind::EventFieldDeclaration => self.declare_field(&child, container, true),
                SyntaxKind::MethodDeclaration => self.declare_method(&child, container),
                SyntaxKind::ConstructorDeclaration => self.declare_constructor(&child, container),
                SyntaxKind::DestructorDeclaration => self.declare_destructor(&child, container),
                SyntaxKind::OperatorDeclaration | SyntaxKind::ConversionOperatorDeclaration => {
                    self.declare_operator(&child, container);
                }
                SyntaxKind::PropertyDeclaration
                | SyntaxKind::IndexerDeclaration
                | SyntaxKind::EventDeclaration => self.declare_property(&child, container),
                SyntaxKind::EnumMemberDeclaration => self.declare_enum_member(&child, container),
                SyntaxKind::ExtensionBlockDeclaration => {
                    self.declare_extension_block(&child, container);
                }
                _ => {}
            }
        }
    }

    // -- namespaces --------------------------------------------------------

    /// Declares `namespace A.B.C`, which is three nested namespaces.
    fn declare_namespace(&mut self, node: &SyntaxNode, container: SymbolId) -> SymbolId {
        let Some(name) = node.children().find(|child| child.kind().is_type_node()) else {
            return container;
        };

        let mut current = container;
        for (part, token) in name_parts(&name) {
            current = match self.symbols.lookup_namespace(current, &part) {
                Some(existing) => existing,
                None => self.symbols.add(
                    SymbolKind::Namespace,
                    part,
                    Some(current),
                    Detail::Namespace,
                ),
            };
            let location = self.token_location(&token);
            self.symbols.get_mut(current).locations.push(location);
        }
        self.record(node, current);
        current
    }

    // -- types -------------------------------------------------------------

    fn declare_type(&mut self, node: &SyntaxNode, container: SymbolId) {
        let type_kind = match node.kind() {
            SyntaxKind::ClassDeclaration => TypeKind::Class,
            SyntaxKind::StructDeclaration => TypeKind::Struct,
            SyntaxKind::InterfaceDeclaration => TypeKind::Interface,
            SyntaxKind::RecordStructDeclaration => TypeKind::RecordStruct,
            SyntaxKind::UnionDeclaration => TypeKind::Struct,
            _ => TypeKind::Record,
        };
        let Some(name_token) = name_token(node) else {
            return;
        };
        let name = name_token.value_text().to_string();
        let type_parameters = type_parameter_names(node);
        let arity = type_parameters.len();
        let (modifiers, accessibility) = modifiers_of(node);

        let id = self.merge_or_add_type(
            container,
            &name,
            arity,
            type_kind,
            &name_token,
            modifiers,
            accessibility.unwrap_or_else(|| default_type_accessibility(&self.symbols, container)),
        );

        self.record(node, id);
        // `[InterpolatedStringHandler]` on any part makes the type one an
        // interpolated string converts to by being appended to (C# 10).
        if parameter_attribute(node, "InterpolatedStringHandler").is_some()
            && let Detail::NamedType(detail) = &mut self.symbols.get_mut(id).detail
        {
            detail.interpolated_string_handler = true;
        }
        self.declare_type_parameters(node, id);
        self.record_base_types(node, id);
        // The list of a union names its case types: no constructor of the
        // union takes them all.
        if node.kind() == SyntaxKind::UnionDeclaration {
            if let Detail::NamedType(detail) = &mut self.symbols.get_mut(id).detail {
                detail.union_declaration = true;
            }
        } else {
            self.declare_primary_constructor(node, id);
        }
        self.declare_members(node, id);
        if node.kind() == SyntaxKind::UnionDeclaration {
            self.declare_union_members(node, id);
        }
        if matches!(type_kind, TypeKind::Record | TypeKind::RecordStruct)
            && (self
                .pending_records
                .iter()
                .all(|(_, _, owner)| *owner != id)
                || node.child_of_kind(SyntaxKind::ParameterList).is_some())
        {
            // The part with the parameter list is the one whose location the
            // members take; any part will do where none has one.
            self.pending_records.retain(|(_, _, owner)| *owner != id);
            self.pending_records.push((self.tree, node.clone(), id));
        }
        // What the primary constructor's parameters are captured for is
        // decided once every part of the type has been read.
        self.pending_captures.push((self.tree, node.clone(), id));
        self.pending_constructors
            .push((self.tree, node.clone(), id, type_kind));
    }

    /// The members the language gives a union (C# 15): `object? Value { get; }`
    /// and, for each case type, a public constructor taking it that stores it
    /// in `Value`. The constructors come out in the order of the list.
    fn declare_union_members(&mut self, node: &SyntaxNode, owner: SymbolId) {
        let location = self.location(node);
        let property = self.symbols.add(
            SymbolKind::Property,
            "Value",
            Some(owner),
            Detail::Property(Property {
                synthesized: Some(SynthesizedType::Special(SpecialType::Object)),
                has_get: true,
                ..Property::default()
            }),
        );
        let symbol = self.symbols.get_mut(property);
        symbol.accessibility = Accessibility::Public;
        symbol.locations.push(location);
        let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) else {
            return;
        };
        for case in list.children() {
            if case.kind() != SyntaxKind::Parameter {
                continue;
            }
            let Some(ty) = case.children().find(|child| child.kind().is_type_node()) else {
                continue;
            };
            let constructor = self.symbols.add(
                SymbolKind::Method,
                ".ctor",
                Some(owner),
                Detail::Method(Method {
                    method_kind: MethodKind::Constructor,
                    ..Method::default()
                }),
            );
            let case_location = self.location(&ty);
            let symbol = self.symbols.get_mut(constructor);
            symbol.accessibility = Accessibility::Public;
            symbol.locations.push(case_location);
            let parameter = self.symbols.add(
                SymbolKind::Parameter,
                "value",
                Some(constructor),
                Detail::Parameter(Parameter {
                    ty: Some(self.type_ref(&ty)),
                    ..Parameter::default()
                }),
            );
            if let Detail::Method(detail) = &mut self.symbols.get_mut(constructor).detail {
                detail.parameters = vec![parameter];
            }
        }
    }

    /// The members the language gives a record.
    ///
    /// `record Point(int X, int Y);` declares two properties, and then value
    /// equality, a `ToString` that prints what it holds, and a `Deconstruct`
    /// that hands its parts back. Roslyn synthesises the symbols rather than
    /// answering questions about them by special case, and so does this: a
    /// backend then emits them like anything else. A member the source
    /// declared with the same signature wins, as it does in Roslyn's
    /// `AddSynthesizedRecordMembersIfNecessary`; this runs once every part of
    /// the record has been read, so that one part's member counts for all.
    fn declare_record_members(&mut self, node: &SyntaxNode, owner: SymbolId) {
        let record_class = self.symbols.get(owner).type_kind() == Some(TypeKind::Record);
        let sealed = self
            .symbols
            .get(owner)
            .modifiers
            .contains(Modifiers::SEALED);
        let readonly = self
            .symbols
            .get(owner)
            .modifiers
            .contains(Modifiers::READONLY);
        let abstract_record = self
            .symbols
            .get(owner)
            .modifiers
            .contains(Modifiers::ABSTRACT);
        // The record this one derives from, where it derives from one:
        // without one its base is `object`, and what would override a base
        // record's member starts a chain of its own instead.
        let base = self.record_base_by_name(owner);
        let has_base_list = base.is_some();
        // `virtual` where nothing is overridden and something may override,
        // `override` where the base record has one.
        let chained = if base.is_some() {
            Modifiers::OVERRIDE
        } else if sealed || !record_class {
            Modifiers::empty()
        } else {
            Modifiers::VIRTUAL
        };
        let positional: Vec<SymbolId> = self
            .symbols
            .get(owner)
            .as_named_type()
            .and_then(|detail| detail.primary_constructor)
            .and_then(|constructor| {
                self.symbols
                    .get(constructor)
                    .as_method()
                    .map(|detail| detail.parameters.clone())
            })
            .unwrap_or_default();

        let location = self.location(node);
        // One property per positional parameter, unless the body declared a
        // member of that name itself — then the source wins.
        for parameter in &positional {
            let name = self.symbols.get(*parameter).name.clone();
            if !self.symbols.lookup(owner, &name).is_empty() {
                continue;
            }
            // A member the base record already has stands for the
            // parameter, as Roslyn's `FindFirstHiddenMemberIfAny` finds it —
            // unless it is an abstract property, which the record then
            // overrides with one of its own (Roslyn's
            // `SynthesizedRecordPropertySymbol` made with `isOverride`).
            let overrides = match self.inherited_member(base, &name) {
                Some(member) => {
                    let member = self.symbols.get(member);
                    if member.kind == SymbolKind::Property
                        && member.modifiers.contains(Modifiers::ABSTRACT)
                    {
                        true
                    } else {
                        continue;
                    }
                }
                None => false,
            };
            let ty = self
                .symbols
                .get(*parameter)
                .as_parameter()
                .and_then(|detail| detail.ty);
            // A record class's are `init`, made whole and then left alone; a
            // record struct's are `set` unless the struct is `readonly`.
            let init = record_class || readonly;
            let id = self.symbols.add(
                SymbolKind::Property,
                name,
                Some(owner),
                Detail::Property(Property {
                    ty,
                    has_get: true,
                    has_init: init,
                    has_set: !init,
                    ..Property::default()
                }),
            );
            let symbol = self.symbols.get_mut(id);
            symbol.locations.push(location);
            symbol.accessibility = Accessibility::Public;
            if overrides {
                symbol.modifiers.insert(Modifiers::OVERRIDE);
            }
        }

        let record = SynthesizedType::Containing;
        let object = SynthesizedType::Special(SpecialType::Object);
        let boolean = SynthesizedType::Special(SpecialType::Boolean);
        let void = SynthesizedType::Special(SpecialType::Void);

        // `Deconstruct` is what lets a positional pattern take a record apart.
        if !positional.is_empty()
            && !self.declares_method(owner, "Deconstruct", positional.len(), false)
        {
            let deconstruct =
                self.declare_record_method(owner, "Deconstruct", Some(void), location, false);
            for parameter in &positional {
                let name = self.symbols.get(*parameter).name.clone();
                let ty = self
                    .symbols
                    .get(*parameter)
                    .as_parameter()
                    .and_then(|detail| detail.ty);
                self.declare_record_parameter(deconstruct, &name, ty, None, RefKind::Out, location);
            }
        }

        // A record class copies itself for `with`: `<Clone>$` makes a new
        // instance through a copy constructor that takes the original
        // (§15.1.2 of the records proposal). A record struct is copied by
        // being loaded, and gets neither.
        if record_class {
            if !self.declares_method(owner, ".ctor", 1, true) {
                let copy = self.declare_record_method(owner, ".ctor", Some(void), location, false);
                self.symbols.get_mut(copy).accessibility = if sealed {
                    Accessibility::Private
                } else {
                    Accessibility::Protected
                };
                self.declare_record_parameter(
                    copy,
                    "original",
                    None,
                    Some(record),
                    RefKind::None,
                    location,
                );
            }
            let clone =
                self.declare_record_method(owner, "<Clone>$", Some(record), location, false);
            let modifiers = if abstract_record {
                let mut modifiers = Modifiers::ABSTRACT;
                if base.is_some() {
                    modifiers.insert(Modifiers::OVERRIDE);
                }
                modifiers
            } else {
                chained
            };
            self.symbols.get_mut(clone).modifiers.insert(modifiers);

            // `protected virtual Type EqualityContract => typeof(R);`, which
            // is what keeps a `Base` from equalling a `Derived` that holds
            // the same things.
            let declared = self
                .symbols
                .lookup(owner, "EqualityContract")
                .iter()
                .any(|member| self.symbols.get(*member).kind == SymbolKind::Property);
            if !declared {
                let id = self.symbols.add(
                    SymbolKind::Property,
                    "EqualityContract",
                    Some(owner),
                    Detail::Property(Property {
                        synthesized: Some(SynthesizedType::SystemType),
                        has_get: true,
                        ..Property::default()
                    }),
                );
                let symbol = self.symbols.get_mut(id);
                symbol.locations.push(location);
                symbol.accessibility = if sealed && !has_base_list {
                    Accessibility::Private
                } else {
                    Accessibility::Protected
                };
                symbol.modifiers.insert(chained);
            }
        }

        // `Equals(R other)`, the one that compares; `Equals(object)` only
        // hands over to it.
        if !self.declares_method(owner, "Equals", 1, true) {
            let equals =
                self.declare_record_method(owner, "Equals", Some(boolean), location, false);
            self.declare_record_parameter(
                equals,
                "other",
                None,
                Some(record),
                RefKind::None,
                location,
            );
            if record_class && !sealed {
                self.symbols
                    .get_mut(equals)
                    .modifiers
                    .insert(Modifiers::VIRTUAL);
            }
        }
        let equals = self.declare_record_method(owner, "Equals", Some(boolean), location, false);
        self.declare_record_parameter(equals, "obj", None, Some(object), RefKind::None, location);
        self.symbols
            .get_mut(equals)
            .modifiers
            .insert(Modifiers::OVERRIDE);
        if !self.declares_method(owner, "GetHashCode", 0, false) {
            let hash = self.declare_record_method(
                owner,
                "GetHashCode",
                Some(SynthesizedType::Special(SpecialType::Int32)),
                location,
                false,
            );
            self.symbols
                .get_mut(hash)
                .modifiers
                .insert(Modifiers::OVERRIDE);
        }
        for name in ["op_Equality", "op_Inequality"] {
            let operator = self.declare_record_method(owner, name, Some(boolean), location, true);
            for side in ["left", "right"] {
                self.declare_record_parameter(
                    operator,
                    side,
                    None,
                    Some(record),
                    RefKind::None,
                    location,
                );
            }
        }
        // `PrintMembers(StringBuilder)` writes the members, and `ToString`
        // puts the record's name and braces around them.
        if !self.declares_method(owner, "PrintMembers", 1, false) {
            let print =
                self.declare_record_method(owner, "PrintMembers", Some(boolean), location, false);
            self.symbols.get_mut(print).accessibility =
                if !record_class || (sealed && !has_base_list) {
                    Accessibility::Private
                } else {
                    Accessibility::Protected
                };
            self.symbols.get_mut(print).modifiers.insert(chained);
            self.declare_record_parameter(
                print,
                "builder",
                None,
                Some(SynthesizedType::StringBuilder),
                RefKind::None,
                location,
            );
        }
        // Nor where the nearest `ToString` of a base record is `sealed`: the
        // record keeps that one (Roslyn's `addToStringMethod`).
        if !self.declares_method(owner, "ToString", 0, false) && !self.sealed_to_string(base) {
            let to_string = self.declare_record_method(
                owner,
                "ToString",
                Some(SynthesizedType::Special(SpecialType::String)),
                location,
                false,
            );
            self.symbols
                .get_mut(to_string)
                .modifiers
                .insert(Modifiers::OVERRIDE);
        }
    }

    /// Whether the nearest `ToString()` declared up a record's bases is
    /// `sealed`.
    fn sealed_to_string(&self, base: Option<SymbolId>) -> bool {
        let mut current = base;
        let mut seen = 0;
        while let Some(ty) = current {
            if let Some(found) = self.symbols.lookup(ty, "ToString").iter().find(|member| {
                let symbol = self.symbols.get(**member);
                symbol.as_method().is_some_and(|detail| {
                    detail.parameters.is_empty()
                        && detail.method_kind != MethodKind::RecordSynthesized
                }) && !symbol.modifiers.contains(Modifiers::STATIC)
            }) {
                return self
                    .symbols
                    .get(*found)
                    .modifiers
                    .contains(Modifiers::SEALED);
            }
            seen += 1;
            if seen > 64 {
                return false;
            }
            current = self.record_base_by_name(ty);
        }
        false
    }

    /// The record a record class derives from, found by the name its base
    /// list writes first — nothing is resolved yet, and a record's base, if
    /// it has one, is a record declared in source or else a class this
    /// cannot see into anyway.
    fn record_base_by_name(&self, owner: SymbolId) -> Option<SymbolId> {
        if self.symbols.get(owner).type_kind() != Some(TypeKind::Record) {
            return None;
        }
        let first = self
            .symbols
            .get(owner)
            .as_named_type()
            .and_then(|detail| detail.base_types.first().copied())?;
        let written = self.syntax_text(first.0)?;
        let written: String = written.chars().filter(|c| !c.is_whitespace()).collect();
        let bare = written.split('<').next().unwrap_or(&written);
        let simple = bare.rsplit(['.', ':']).next().unwrap_or(bare);
        // The type of that name nearest the record: its own container's
        // members first, then outward, then anywhere.
        let mut container = self.symbols.get(owner).container;
        while let Some(current) = container {
            let found = self
                .symbols
                .lookup(current, simple)
                .iter()
                .copied()
                .find(|id| *id != owner && self.symbols.get(*id).kind == SymbolKind::NamedType);
            if let Some(found) = found {
                return (self.symbols.get(found).type_kind() == Some(TypeKind::Record))
                    .then_some(found);
            }
            container = self.symbols.get(current).container;
        }
        self.symbols
            .iter()
            .find(|symbol| {
                symbol.id != owner
                    && symbol.kind == SymbolKind::NamedType
                    && symbol.name == simple
                    && symbol.type_kind() == Some(TypeKind::Record)
            })
            .map(|symbol| symbol.id)
    }

    /// Whether a record up the chain from `base` has an instance property or
    /// field called `name`.
    fn inherited_member(&self, base: Option<SymbolId>, name: &str) -> Option<SymbolId> {
        let mut current = base;
        let mut seen = 0;
        while let Some(ty) = current {
            if let Some(found) = self
                .symbols
                .lookup(ty, name)
                .iter()
                .copied()
                .find(|member| {
                    let member = self.symbols.get(*member);
                    matches!(member.kind, SymbolKind::Property | SymbolKind::Field)
                        && !member.modifiers.contains(Modifiers::STATIC)
                        && member.accessibility != Accessibility::Private
                })
            {
                return Some(found);
            }
            // A cycle is an error reported elsewhere; it must not hang here.
            seen += 1;
            if seen > 64 {
                return None;
            }
            current = self.record_base_by_name(ty);
        }
        None
    }

    /// Declares one pending record's members, after its base's if the base
    /// is pending too.
    fn declare_record_with_bases(
        &mut self,
        pending: &[(usize, SyntaxNode, SymbolId)],
        index: usize,
        done: &mut std::collections::HashSet<SymbolId>,
    ) {
        let (tree, node, owner) = &pending[index];
        if !done.insert(*owner) {
            return;
        }
        if let Some(base) = self.record_base_by_name(*owner)
            && let Some(position) = pending.iter().position(|(_, _, id)| *id == base)
        {
            self.declare_record_with_bases(pending, position, done);
        }
        self.tree = *tree;
        self.declare_record_members(node, *owner);
    }

    /// Whether the source declared an instance method (or constructor) of
    /// this name taking this many parameters — the first of the record's
    /// own type, where `of_self` asks — which a member the language would
    /// give the record then gives way to. The types are read from the
    /// syntax, since nothing is resolved yet: `R` and `R?` both name the
    /// record.
    fn declares_method(&self, owner: SymbolId, name: &str, count: usize, of_self: bool) -> bool {
        self.symbols.lookup(owner, name).iter().any(|member| {
            let symbol = self.symbols.get(*member);
            let Some(detail) = symbol.as_method() else {
                return false;
            };
            if detail.method_kind == MethodKind::RecordSynthesized
                || symbol.modifiers.contains(Modifiers::STATIC)
                || detail.parameters.len() != count
            {
                return false;
            }
            // `Equals(ref R other)` is another signature altogether, and so
            // is a `Deconstruct` that takes anything but `out` parameters:
            // `Deconstruct(int X)` leaves the record its own.
            let wanted = if name == "Deconstruct" {
                RefKind::Out
            } else {
                RefKind::None
            };
            let same_kinds = detail.parameters.iter().all(|parameter| {
                self.symbols
                    .get(*parameter)
                    .as_parameter()
                    .is_none_or(|parameter| parameter.ref_kind == wanted)
            });
            if !same_kinds {
                return false;
            }
            !of_self
                || detail
                    .parameters
                    .first()
                    .is_some_and(|parameter| self.names_own_type(owner, *parameter))
        })
    }

    /// Whether a constructor the source wrote takes one of its own record
    /// by value, which makes it the record's copy constructor.
    fn is_copy_constructor(&self, owner: SymbolId, constructor: SymbolId) -> bool {
        let Some(detail) = self.symbols.get(constructor).as_method() else {
            return false;
        };
        let [parameter] = detail.parameters.as_slice() else {
            return false;
        };
        self.symbols
            .get(*parameter)
            .as_parameter()
            .is_some_and(|parameter| parameter.ref_kind == RefKind::None)
            && self.names_own_type(owner, *parameter)
    }

    /// Whether a parameter's written type names the record it belongs to.
    fn names_own_type(&self, owner: SymbolId, parameter: SymbolId) -> bool {
        let own_name = self.symbols.get(owner).name.clone();
        let Some(written) = self
            .symbols
            .get(parameter)
            .as_parameter()
            .and_then(|parameter| parameter.ty)
            .and_then(|ty| self.syntax_text(ty.0))
        else {
            return false;
        };
        let written: String = written.chars().filter(|c| !c.is_whitespace()).collect();
        let written = written.trim_end_matches('?');
        let bare = written.split('<').next().unwrap_or(written);
        bare == own_name || bare.rsplit('.').next() == Some(own_name.as_str())
    }

    /// The source text at a location.
    fn syntax_text(&self, location: Location) -> Option<String> {
        let (tree, _) = self.trees.get(location.tree)?;
        let node = tree.root().find_node(location.span)?;
        Some(node.text().to_string())
    }

    fn declare_record_method(
        &mut self,
        owner: SymbolId,
        name: &str,
        returns: Option<SynthesizedType>,
        location: Location,
        is_static: bool,
    ) -> SymbolId {
        let id = self.symbols.add(
            SymbolKind::Method,
            name,
            Some(owner),
            Detail::Method(Method {
                synthesized_return: returns,
                method_kind: MethodKind::RecordSynthesized,
                ..Method::default()
            }),
        );
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.accessibility = Accessibility::Public;
        if is_static {
            symbol.modifiers.insert(Modifiers::STATIC);
        }
        id
    }

    fn declare_record_parameter(
        &mut self,
        owner: SymbolId,
        name: &str,
        ty: Option<TypeSyntaxRef>,
        synthesized: Option<SynthesizedType>,
        ref_kind: RefKind,
        location: Location,
    ) {
        let id = self.symbols.add(
            SymbolKind::Parameter,
            name,
            Some(owner),
            Detail::Parameter(Parameter {
                ty,
                synthesized,
                ref_kind,
                ..Parameter::default()
            }),
        );
        self.symbols.get_mut(id).locations.push(location);
        if let Detail::Method(detail) = &mut self.symbols.get_mut(owner).detail {
            detail.parameters.push(id);
        }
    }

    /// A class or struct that declares no constructor still has one.
    ///
    /// Roslyn synthesises the symbol rather than leaving `new C()` to be
    /// resolved by a special case, and so does this: the constructor is a
    /// member like any other, so overload resolution and emit both find it
    /// without knowing it was never written.
    fn declare_implicit_constructor(
        &mut self,
        node: &SyntaxNode,
        owner: SymbolId,
        type_kind: TypeKind,
    ) {
        if !matches!(
            type_kind,
            TypeKind::Class | TypeKind::Struct | TypeKind::Record | TypeKind::RecordStruct
        ) {
            return;
        }
        // A static class has no instances, so it has no instance constructor.
        if self
            .symbols
            .get(owner)
            .modifiers
            .contains(Modifiers::STATIC)
        {
            return;
        }
        // The copy constructor a record class gets from the language is not
        // one the source wrote, and does not stand in for `new C()`.
        // Nor does one the source wrote in its place: a record's copy
        // constructor is not a constructor `new R()` could have called.
        let record = type_kind == TypeKind::Record;
        let written = self
            .symbols
            .lookup(owner, ".ctor")
            .iter()
            .any(|constructor| {
                self.symbols
                    .get(*constructor)
                    .as_method()
                    .is_none_or(|detail| detail.method_kind != MethodKind::RecordSynthesized)
                    && !(record && self.is_copy_constructor(owner, *constructor))
            });
        if written {
            return;
        }
        let id = self.symbols.add(
            SymbolKind::Method,
            ".ctor",
            Some(owner),
            Detail::Method(Method {
                method_kind: MethodKind::Constructor,
                is_implicit: true,
                ..Method::default()
            }),
        );
        let location = self.location(node);
        // An abstract class can only be constructed by a derived one.
        let accessibility = if self
            .symbols
            .get(owner)
            .modifiers
            .contains(Modifiers::ABSTRACT)
        {
            Accessibility::Protected
        } else {
            Accessibility::Public
        };
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.accessibility = accessibility;
    }

    /// Finds the existing symbol for a partial type, or makes a new one.
    #[allow(clippy::too_many_arguments)]
    fn merge_or_add_type(
        &mut self,
        container: SymbolId,
        name: &str,
        arity: usize,
        type_kind: TypeKind,
        name_token: &SyntaxToken,
        modifiers: Modifiers,
        accessibility: Accessibility,
    ) -> SymbolId {
        let location = self.token_location(name_token);

        // A file-local type is another type than one of the same name in
        // another file, or than one that is not file-local: only the parts
        // of one type in one file merge.
        let file = modifiers.contains(Modifiers::FILE).then_some(self.tree);
        let existing = self
            .symbols
            .lookup(container, name)
            .iter()
            .copied()
            .find(|id| {
                let symbol = self.symbols.get(*id);
                symbol.kind == SymbolKind::NamedType
                    && symbol.as_named_type().is_some_and(|d| d.arity == arity)
                    && self.symbols.file_of(*id) == file
            });
        if let Some(existing) = existing {
            let previous = self.symbols.get(existing);
            let both_partial = previous.modifiers.contains(Modifiers::PARTIAL)
                && modifiers.contains(Modifiers::PARTIAL);
            if !both_partial {
                let container_name = self.symbols.qualified_name(container);
                let code = if self.symbols.get(container).kind == SymbolKind::Namespace {
                    ErrorCode::ErrDuplicateNameInNS
                } else {
                    ErrorCode::ErrDuplicateNameInClass
                };
                self.report(code, location, &[&container_name, name]);
            }
            let symbol = self.symbols.get_mut(existing);
            symbol.locations.push(location);
            symbol.modifiers.insert(modifiers);
            // `static partial class M` in one file and `public static partial
            // class M` in another: the parts agree on whatever any of them
            // says (§15.2.7), so a part that says `public` says it for all.
            if accessibility == Accessibility::Public {
                symbol.accessibility = accessibility;
            }
            return existing;
        }

        let id = self.symbols.add(
            SymbolKind::NamedType,
            name,
            Some(container),
            Detail::NamedType(NamedType {
                type_kind: Some(type_kind),
                arity,
                // `ref struct` is the one modifier the runtime has to be told
                // about: it decides what may hold one, and metadata says it
                // with `IsByRefLikeAttribute` rather than a flag.
                ref_like: modifiers.contains(Modifiers::REF),
                ..NamedType::default()
            }),
        );
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.modifiers = modifiers;
        symbol.accessibility = accessibility;
        id
    }

    fn declare_type_parameters(&mut self, node: &SyntaxNode, owner: SymbolId) {
        // A nested type can spell its enclosing type's parameters without
        // declaring any, and metadata makes that literal: `Enumerator` inside
        // `ArrayBuilder<T>` carries `T` in its own list, as the very same
        // symbol. Numbering them any other way loses `T` the moment a
        // signature crosses from one type to the other — and a method's are
        // its own, which is why only a type inherits here.
        let inherited: Vec<SymbolId> = if self.symbols.get(owner).kind == SymbolKind::NamedType {
            self.symbols
                .get(owner)
                .container
                .and_then(|container| {
                    self.symbols
                        .get(container)
                        .as_named_type()
                        .map(|detail| detail.type_parameters.clone())
                })
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let Some(list) = node.child_of_kind(SyntaxKind::TypeParameterList) else {
            if !inherited.is_empty()
                && let Detail::NamedType(detail) = &mut self.symbols.get_mut(owner).detail
                && detail.type_parameters.is_empty()
            {
                detail.type_parameters = inherited;
            }
            return;
        };
        // Every part of a partial type writes the same type parameters, and
        // they are one set: declaring them again would leave two `T`s under
        // one type, so a later part reuses what the first one made and only
        // adds whatever constraints it wrote.
        //
        // Only the type's *own* parameters, though. The ones it inherited from
        // the type around it are a different `T`, and reusing one of those for
        // a nested type that writes its own would put the nested type's
        // constraints on the enclosing type's parameter.
        let existing: Vec<SymbolId> = self
            .symbols
            .get(owner)
            .as_named_type()
            .map(|detail| {
                detail
                    .type_parameters
                    .get(inherited.len()..)
                    .unwrap_or_default()
                    .to_vec()
            })
            .unwrap_or_default();
        let mut ids = Vec::new();
        for parameter in list.children() {
            if parameter.kind() != SyntaxKind::TypeParameter {
                continue;
            }
            let Some(token) = name_token(&parameter) else {
                continue;
            };
            let id = match existing
                .iter()
                .copied()
                .find(|id| self.symbols.get(*id).name == token.value_text())
            {
                Some(id) => id,
                None => self.symbols.add(
                    SymbolKind::TypeParameter,
                    token.value_text(),
                    Some(owner),
                    Detail::TypeParameter(TypeParameterDetail::default()),
                ),
            };
            // `out T` and `in T` say which way a construction of the type
            // converts, and the keyword is the only place it is written.
            let variance = parameter
                .child_tokens()
                .find_map(|token| match token.kind() {
                    SyntaxKind::OutKeyword => Some(Variance::Out),
                    SyntaxKind::InKeyword => Some(Variance::In),
                    _ => None,
                });
            if let Some(variance) = variance
                && let Detail::TypeParameter(detail) = &mut self.symbols.get_mut(id).detail
            {
                detail.variance = variance;
            }
            let location = self.token_location(&token);
            self.symbols.get_mut(id).locations.push(location);
            self.record(&parameter, id);
            ids.push(id);
        }

        match &mut self.symbols.get_mut(owner).detail {
            Detail::NamedType(detail) => {
                let mut all = inherited;
                all.extend(ids.iter().copied());
                detail.type_parameters = all;
            }
            Detail::Method(detail) => {
                detail.arity = ids.len();
                detail.type_parameters = ids.clone();
            }
            _ => {}
        }
        self.declare_constraints(node, &ids);
    }

    /// Records what a `where` clause said each type parameter must be.
    ///
    /// The constraint is type syntax like any other and is resolved later, for
    /// the same reason a base type is: it may name a type declared further
    /// down the file.
    fn declare_constraints(&mut self, node: &SyntaxNode, parameters: &[SymbolId]) {
        for clause in node.children() {
            if clause.kind() != SyntaxKind::TypeParameterConstraintClause {
                continue;
            }
            let Some(name) = clause
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
            else {
                continue;
            };
            let Some(parameter) = parameters
                .iter()
                .copied()
                .find(|id| self.symbols.get(*id).name == name)
            else {
                continue;
            };
            let mut constraints = Vec::new();
            let mut value_type = false;
            let mut reference_type = false;
            let mut constructor = false;
            let mut allows_ref_struct = false;
            for constraint in clause.children() {
                match constraint.kind() {
                    SyntaxKind::TypeConstraint => {
                        if let Some(ty) = constraint
                            .children()
                            .find(|child| child.kind().is_type_node())
                        {
                            let reference = self.type_ref(&ty);
                            // `where T : unmanaged` is spelled as a type, and is
                            // one only where a type of that name is declared;
                            // which that is is known once every file is read.
                            if ty.kind() == SyntaxKind::IdentifierName
                                && ty.text().trim() == "unmanaged"
                            {
                                self.pending_unmanaged.push((parameter, reference));
                            }
                            constraints.push(reference);
                        }
                    }
                    SyntaxKind::StructConstraint => value_type = true,
                    SyntaxKind::ClassConstraint => reference_type = true,
                    SyntaxKind::ConstructorConstraint => constructor = true,
                    SyntaxKind::AllowsConstraintClause => {
                        allows_ref_struct |= constraint
                            .children()
                            .any(|allowed| allowed.kind() == SyntaxKind::RefStructConstraint);
                    }
                    _ => {}
                }
            }
            if let Detail::TypeParameter(detail) = &mut self.symbols.get_mut(parameter).detail {
                // Another part of the same partial type may have written them
                // already; both sets hold.
                detail.constraints.extend(constraints);
                detail.value_type |= value_type;
                detail.reference_type |= reference_type;
                detail.constructor |= constructor;
                detail.allows_ref_struct |= allows_ref_struct;
            }
        }
    }

    fn record_base_types(&mut self, node: &SyntaxNode, owner: SymbolId) {
        let Some(list) = node.child_of_kind(SyntaxKind::BaseList) else {
            return;
        };
        let mut refs = Vec::new();
        for base in list.children() {
            if !matches!(
                base.kind(),
                SyntaxKind::SimpleBaseType | SyntaxKind::PrimaryConstructorBaseType
            ) {
                continue;
            }
            if let Some(ty) = base.children().find(|child| child.kind().is_type_node()) {
                refs.push(self.type_ref(&ty));
            }
        }
        if let Detail::NamedType(detail) = &mut self.symbols.get_mut(owner).detail {
            detail.base_types.extend(refs);
        }
    }

    /// `record Point(int X, int Y)` and `class C(int x)` declare a constructor
    /// in their header.
    fn declare_primary_constructor(&mut self, node: &SyntaxNode, owner: SymbolId) {
        let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) else {
            return;
        };
        let id = self.symbols.add(
            SymbolKind::Method,
            ".ctor",
            Some(owner),
            Detail::Method(Method {
                method_kind: MethodKind::Constructor,
                ..Method::default()
            }),
        );
        let location = self.location(node);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.accessibility = Accessibility::Public;
        // The parameter list is the constructor's declaration: the type's
        // own node names the type, and a body binder asked about the list
        // finds the `: Base(...)` beside it.
        self.record(&list, id);
        self.declare_parameters(&list, id);
        if let Detail::NamedType(detail) = &mut self.symbols.get_mut(owner).detail {
            detail.primary_constructor = Some(id);
        }
    }

    /// A field for each primary constructor parameter that a member body
    /// reads: `struct Disposer<T>(T instance)` whose `Dispose` frees
    /// `instance` keeps it, since the parameter is gone by then. Which are
    /// read is decided by name, which may keep one a local shadows — an
    /// unused field, and nothing worse.
    fn capture_primary_parameters(&mut self, parts: &[(usize, SyntaxNode)], owner: SymbolId) {
        let Some(primary) = self
            .symbols
            .get(owner)
            .as_named_type()
            .and_then(|detail| detail.primary_constructor)
        else {
            return;
        };
        let parameters = self
            .symbols
            .get(primary)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        if parameters.is_empty() {
            return;
        }
        let names_in = |part: &SyntaxNode, read: &mut Vec<String>| {
            for inner in std::iter::once(part.clone()).chain(part.descendants()) {
                if inner.kind() == SyntaxKind::IdentifierName
                    && let Some(token) = name_token(&inner)
                {
                    read.push(token.value_text().to_string());
                }
            }
        };
        let mut read: Vec<String> = Vec::new();
        // What a lambda in an initializer reads: the lambda runs whenever it
        // is called, long after the constructor that held the parameter.
        let mut read_later: Vec<String> = Vec::new();
        for member in parts.iter().flat_map(|(_, node)| node.children()) {
            let body_member = matches!(
                member.kind(),
                SyntaxKind::MethodDeclaration
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::IndexerDeclaration
                    | SyntaxKind::EventDeclaration
                    | SyntaxKind::OperatorDeclaration
                    | SyntaxKind::ConversionOperatorDeclaration
                    | SyntaxKind::DestructorDeclaration
            );
            if !body_member
                && !matches!(
                    member.kind(),
                    SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration
                )
            {
                continue;
            }
            for part in std::iter::once(member.clone()).chain(member.descendants()) {
                if part.kind() != SyntaxKind::EqualsValueClause {
                    continue;
                }
                for lambda in part.descendants().filter(|inner| {
                    matches!(
                        inner.kind(),
                        SyntaxKind::SimpleLambdaExpression
                            | SyntaxKind::ParenthesizedLambdaExpression
                            | SyntaxKind::AnonymousMethodExpression
                    )
                }) {
                    names_in(&lambda, &mut read_later);
                }
            }
            if !body_member {
                continue;
            }
            for part in member.children() {
                // An initializer runs in the constructor, where the
                // parameter itself is still there.
                if part.kind() == SyntaxKind::EqualsValueClause {
                    continue;
                }
                names_in(&part, &mut read);
            }
        }
        let is_record = matches!(
            self.symbols.get(owner).type_kind(),
            Some(TypeKind::Record | TypeKind::RecordStruct)
        );
        // A lambda in a struct cannot close over `this`, so the field is no
        // way for it to reach the parameter.
        if matches!(
            self.symbols.get(owner).type_kind(),
            Some(TypeKind::Struct | TypeKind::RecordStruct)
        ) {
            read_later.clear();
        }
        let location = self
            .symbols
            .get(primary)
            .locations
            .first()
            .copied()
            .unwrap_or_else(|| Location::new(parts[0].0, parts[0].1.span()));
        for parameter in parameters {
            let name = self.symbols.get(parameter).name.clone();
            // A record's positional parameter is a property in its members;
            // only a lambda in an initializer reads the parameter itself.
            if !read_later.contains(&name) && (is_record || !read.contains(&name)) {
                continue;
            }
            let ty = self
                .symbols
                .get(parameter)
                .as_parameter()
                .and_then(|detail| detail.ty);
            let field = self.symbols.add(
                SymbolKind::Field,
                format!("<{name}>P"),
                Some(owner),
                Detail::Field(Field {
                    ty,
                    has_initializer: false,
                }),
            );
            let symbol = self.symbols.get_mut(field);
            symbol.locations.push(location);
            symbol.accessibility = Accessibility::Private;
            if let Detail::Parameter(detail) = &mut self.symbols.get_mut(parameter).detail {
                detail.captured = Some(field);
            }
        }
    }

    fn declare_enum(&mut self, node: &SyntaxNode, container: SymbolId) {
        let Some(name_token) = name_token(node) else {
            return;
        };
        let name = name_token.value_text().to_string();
        let (modifiers, accessibility) = modifiers_of(node);
        let id = self.merge_or_add_type(
            container,
            &name,
            0,
            TypeKind::Enum,
            &name_token,
            modifiers,
            accessibility.unwrap_or_else(|| default_type_accessibility(&self.symbols, container)),
        );

        // `enum E : byte` names the storage the members use.
        if let Some(list) = node.child_of_kind(SyntaxKind::BaseList)
            && let Some(base) = list
                .children()
                .find(|child| child.kind() == SyntaxKind::SimpleBaseType)
            && let Some(ty) = base.children().find(|child| child.kind().is_type_node())
        {
            let type_ref = self.type_ref(&ty);
            if let Detail::NamedType(detail) = &mut self.symbols.get_mut(id).detail {
                detail.enum_underlying = Some(type_ref);
            }
        }

        self.record(node, id);
        // An enum nested in `Outer<T>` is `Outer<T>.E`, as any nested type
        // is: it carries the enclosing type's parameters, and
        // `typeof(Outer<int>.E)` names that construction.
        self.declare_type_parameters(node, id);
        self.declare_members(node, id);
    }

    fn declare_enum_member(&mut self, node: &SyntaxNode, container: SymbolId) {
        let Some(token) = name_token(node) else {
            return;
        };
        let id = self.symbols.add(
            SymbolKind::Field,
            token.value_text(),
            Some(container),
            Detail::Field(Field {
                ty: None,
                has_initializer: node.child_of_kind(SyntaxKind::EqualsValueClause).is_some(),
            }),
        );
        let location = self.token_location(&token);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.accessibility = Accessibility::Public;
        symbol.modifiers = Modifiers::CONST.union(Modifiers::STATIC);
        self.record(node, id);
    }

    /// A delegate is a type whose signature lives on its `Invoke` method, the
    /// way it does in metadata.
    fn declare_delegate(&mut self, node: &SyntaxNode, container: SymbolId) {
        let Some(name_token) = name_token(node) else {
            return;
        };
        let name = name_token.value_text().to_string();
        let type_parameters = type_parameter_names(node);
        let (modifiers, accessibility) = modifiers_of(node);
        let id = self.merge_or_add_type(
            container,
            &name,
            type_parameters.len(),
            TypeKind::Delegate,
            &name_token,
            modifiers,
            accessibility.unwrap_or_else(|| default_type_accessibility(&self.symbols, container)),
        );
        self.record(node, id);
        self.declare_type_parameters(node, id);

        let return_type = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| self.type_ref(&ty));
        let returns_readonly = returns_readonly_reference(node);
        let invoke = self.symbols.add(
            SymbolKind::Method,
            "Invoke",
            Some(id),
            Detail::Method(Method {
                return_type,
                returns_readonly,
                ..Method::default()
            }),
        );
        let location = self.location(node);
        let symbol = self.symbols.get_mut(invoke);
        symbol.locations.push(location);
        symbol.accessibility = Accessibility::Public;
        if let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) {
            self.declare_parameters(&list, invoke);
        }
    }

    // -- members -----------------------------------------------------------

    fn declare_field(&mut self, node: &SyntaxNode, container: SymbolId, is_event: bool) {
        let Some(declaration) = node.child_of_kind(SyntaxKind::VariableDeclaration) else {
            return;
        };
        // `partial event Action E;` (C# 14) only says that the event its
        // implementing part declares, accessors and all, exists: it is no
        // field-like event.
        if is_event && modifiers_of(node).0.contains(Modifiers::PARTIAL) {
            return;
        }
        let ty = declaration
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| self.type_ref(&ty));
        let (modifiers, accessibility) = modifiers_of(node);
        let accessibility =
            accessibility.unwrap_or_else(|| default_member_accessibility(&self.symbols, container));

        for declarator in declaration.children() {
            if declarator.kind() != SyntaxKind::VariableDeclarator {
                continue;
            }
            let Some(token) = name_token(&declarator) else {
                continue;
            };
            let has_initializer = declarator
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .is_some();
            let detail = if is_event {
                Detail::Event(Event {
                    ty,
                    adder: None,
                    remover: None,
                })
            } else {
                Detail::Field(Field {
                    ty,
                    has_initializer,
                })
            };
            let kind = if is_event {
                SymbolKind::Event
            } else {
                SymbolKind::Field
            };
            let id = self
                .symbols
                .add(kind, token.value_text(), Some(container), detail);
            let location = self.token_location(&token);
            let symbol = self.symbols.get_mut(id);
            symbol.locations.push(location);
            symbol.accessibility = accessibility;
            symbol.modifiers = modifiers;
            self.record(&declarator, id);
            if is_event {
                self.declare_event_accessors(id, ty, &token, modifiers, accessibility);
            }
            // `F = () => { ... static int Local() => 1; }`: a lambda in an
            // initializer may declare local functions of its own.
            if has_initializer {
                self.declare_local_functions(&declarator, id);
            }
        }
    }

    /// Declares the `add_E` and `remove_E` of a field-like event (§15.8.2).
    ///
    /// Their bodies are the emitter's to synthesize; the symbols are what a
    /// `+=` on the event from outside its type calls, and what names the
    /// methods under a construction of a generic type.
    fn declare_event_accessors(
        &mut self,
        event: SymbolId,
        ty: Option<TypeSyntaxRef>,
        token: &rustlyn_syntax::SyntaxToken,
        modifiers: Modifiers,
        accessibility: Accessibility,
    ) {
        let name = self.symbols.get(event).name.clone();
        for add in [true, false] {
            let id = self.symbols.add(
                SymbolKind::Method,
                format!("{}_{name}", if add { "add" } else { "remove" }),
                Some(event),
                Detail::Method(Method {
                    return_type: None,
                    // An accessor returns nothing, and has nowhere to say so.
                    synthesized_return: Some(SynthesizedType::Special(SpecialType::Void)),
                    ..Method::default()
                }),
            );
            let location = self.token_location(token);
            let symbol = self.symbols.get_mut(id);
            symbol.locations.push(location);
            symbol.modifiers = modifiers;
            symbol.accessibility = accessibility;
            // `value`: the handler being added or removed.
            let value = self.symbols.add(
                SymbolKind::Parameter,
                "value",
                Some(id),
                Detail::Parameter(Parameter {
                    ty,
                    ..Parameter::default()
                }),
            );
            let location = self.token_location(token);
            self.symbols.get_mut(value).locations.push(location);
            if let Detail::Method(detail) = &mut self.symbols.get_mut(id).detail {
                detail.parameters = vec![value];
            }
            if let Detail::Event(detail) = &mut self.symbols.get_mut(event).detail {
                if add {
                    detail.adder = Some(id);
                } else {
                    detail.remover = Some(id);
                }
            }
        }
    }

    fn declare_method(&mut self, node: &SyntaxNode, container: SymbolId) {
        let Some(token) = name_token(node) else {
            return;
        };
        let return_type = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| self.type_ref(&ty));
        let (modifiers, accessibility) = modifiers_of(node);

        // The two parts of a partial method are one method (§15.6.9): the
        // declaring part says it exists, the implementing part says what it
        // does. Whichever comes second joins the first, and the body is the
        // implementing part's — a declaring part met after it adds nothing,
        // and one met before it hands its symbol over.
        if modifiers.contains(Modifiers::PARTIAL)
            && let Some(other) = self.partial_counterpart(node, container, &token)
        {
            if has_body(node) {
                self.take_over_partial(node, other);
            } else {
                self.keep_declared_names(node, other);
            }
            return;
        }

        // A partial method of an interface is private unless it says
        // otherwise, as it would be in a class (C# 8 keeps that of the
        // partial methods before it); so is an explicit implementation,
        // which nothing reaches but through its interface.
        let accessibility = accessibility.unwrap_or_else(|| {
            if modifiers.contains(Modifiers::PARTIAL) || is_explicit_implementation(node) {
                Accessibility::Private
            } else {
                default_member_accessibility(&self.symbols, container)
            }
        });
        let id = self.symbols.add(
            SymbolKind::Method,
            explicit_name(node, token.value_text()),
            Some(container),
            Detail::Method(Method {
                return_type,
                returns_readonly: returns_readonly_reference(node),
                ..Method::default()
            }),
        );
        let location = self.token_location(&token);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.modifiers = modifiers;
        symbol.accessibility = accessibility;

        self.record(node, id);
        self.declare_type_parameters(node, id);
        if let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) {
            self.declare_parameters(&list, id);
        }
        self.declare_local_functions(node, id);
    }

    /// `extension(TypeSymbol type) { ... }` (C# 14): members that read as
    /// the receiver's and are the static class's.
    ///
    /// Each instance member of the block is a static method of the class
    /// with the receiver as its first parameter and the `this` an extension
    /// method carries, which is exactly what the CLI has for it and what the
    /// binder already knows how to find. A property is read through a
    /// `get_Name(receiver)`, and `type.IsSubjectForUnionMatching` reaches it
    /// as a call. A `static` member of the block is the class's own.
    fn declare_extension_block(&mut self, node: &SyntaxNode, container: SymbolId) {
        let receiver = node.child_of_kind(SyntaxKind::ParameterList);
        // The type the block extends, as its receiver writes it.
        let extended = receiver
            .as_ref()
            .and_then(|list| list.child_of_kind(SyntaxKind::Parameter))
            .and_then(|parameter| {
                parameter
                    .children()
                    .find(|child| child.kind().is_type_node())
            })
            .map(|ty| self.type_ref(&ty));
        // `extension<T>(T x)` declares its type parameters once, on a holder
        // no type lists as a member: the block's syntax names it, so that
        // `T` resolves anywhere inside, and every member takes them as its
        // own first type parameters.
        let generics: Vec<SymbolId> = if node.child_of_kind(SyntaxKind::TypeParameterList).is_some()
        {
            let holder = self.symbols.add(
                SymbolKind::Method,
                "<extension>",
                None,
                Detail::Method(Method::default()),
            );
            self.record(node, holder);
            self.declare_type_parameters(node, holder);
            self.symbols
                .get(holder)
                .as_method()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        for member in node.children() {
            match member.kind() {
                SyntaxKind::MethodDeclaration => {
                    self.declare_method(&member, container);
                    let Some(id) = self.declarations.get(&(self.tree, member.span())).copied()
                    else {
                        continue;
                    };
                    self.take_receiver(id, receiver.as_ref());
                    if let Detail::Method(detail) = &mut self.symbols.get_mut(id).detail {
                        detail.extended = extended;
                        if !generics.is_empty() {
                            let mut all = generics.clone();
                            all.extend(detail.type_parameters.iter().copied());
                            detail.arity = all.len();
                            detail.type_parameters = all;
                        }
                    }
                }
                // `static C operator +(C a, C b)` (C# 14): an operator the
                // extended type gains, found by the operands' types.
                SyntaxKind::OperatorDeclaration | SyntaxKind::ConversionOperatorDeclaration => {
                    self.declare_operator(&member, container);
                    let Some(id) = self.declarations.get(&(self.tree, member.span())).copied()
                    else {
                        continue;
                    };
                    // An instance operator (`operator +=`) takes the block's
                    // receiver first, as an instance method does, without
                    // being an extension method that a call could reach.
                    self.take_receiver(id, receiver.as_ref());
                    if let Detail::Method(detail) = &mut self.symbols.get_mut(id).detail {
                        detail.is_extension = false;
                        detail.extended = extended;
                        // The block's type parameters are the operator's
                        // own, as they are a method's.
                        if !generics.is_empty() {
                            detail.arity = generics.len();
                            detail.type_parameters = generics.clone();
                        }
                    }
                }
                SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration => {
                    self.declare_property(&member, container);
                    let Some(id) = self.declarations.get(&(self.tree, member.span())).copied()
                    else {
                        continue;
                    };
                    let is_static = self.symbols.get(id).modifiers.contains(Modifiers::STATIC);
                    // An instance one reads its receiver as its first
                    // parameter, as an extension method does.
                    let mut receiver_parameters = Vec::new();
                    if !is_static && let Some(list) = receiver.as_ref() {
                        let before = self.symbols.get(id).members.clone();
                        self.declare_parameters(list, id);
                        receiver_parameters = self
                            .symbols
                            .get(id)
                            .members
                            .iter()
                            .copied()
                            .filter(|member| !before.contains(member))
                            .collect();
                    }
                    let accessors: Vec<SymbolId> = match &mut self.symbols.get_mut(id).detail {
                        Detail::Property(detail) => {
                            detail.extended = extended;
                            detail.extension_generics = generics.clone();
                            let mut all = receiver_parameters.clone();
                            all.extend(detail.parameters.iter().copied());
                            detail.parameters = all;
                            detail.getter.into_iter().chain(detail.setter).collect()
                        }
                        _ => Vec::new(),
                    };
                    if !receiver_parameters.is_empty() {
                        self.symbols.get_mut(id).modifiers.insert(Modifiers::STATIC);
                        for accessor in accessors {
                            self.symbols
                                .get_mut(accessor)
                                .modifiers
                                .insert(Modifiers::STATIC);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Gives a member of an extension block the block's receiver as its
    /// first parameter, and makes it the static extension method it is.
    fn take_receiver(&mut self, method: SymbolId, receiver: Option<&SyntaxNode>) {
        if self
            .symbols
            .get(method)
            .modifiers
            .contains(Modifiers::STATIC)
        {
            return;
        }
        let Some(list) = receiver else {
            return;
        };
        let own: Vec<SymbolId> = self
            .symbols
            .get(method)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        self.declare_parameters(list, method);
        if let Detail::Method(detail) = &mut self.symbols.get_mut(method).detail {
            // An unnamed receiver — `extension(string)` — declares no
            // parameter, and then the block holds only static members.
            let mut receiver: Vec<SymbolId> = detail
                .parameters
                .iter()
                .copied()
                .filter(|parameter| !own.contains(parameter))
                .collect();
            if receiver.is_empty() {
                detail.parameters = own;
                return;
            }
            receiver.extend(own);
            detail.parameters = receiver;
            detail.is_extension = true;
            detail.takes_receiver = true;
        }
        self.symbols
            .get_mut(method)
            .modifiers
            .insert(Modifiers::STATIC);
    }

    /// Declares the local functions written inside a body.
    ///
    /// Roslyn makes a local function a symbol of the method that holds it, and
    /// so does this: it has parameters, type parameters and a return type like
    /// any method, and the only thing unusual about it is that the only place
    /// it can be named from is inside its owner.
    fn declare_local_functions(&mut self, owner_node: &SyntaxNode, owner: SymbolId) {
        let Some((_, facts)) = self.trees.get(self.tree) else {
            return;
        };
        for node in within(&facts.local_functions, owner_node) {
            // The nearest enclosing function owns it: a local function inside
            // a local function belongs to that one.
            let container = self
                .enclosing_function(node)
                .and_then(|enclosing| {
                    self.declarations
                        .get(&(self.tree, enclosing.span()))
                        .copied()
                })
                .unwrap_or(owner);
            self.declare_local_function(node, container);
        }
    }

    /// The function a local function is written inside, where that is another
    /// local function rather than the member itself.
    fn enclosing_function(&self, node: &SyntaxNode) -> Option<SyntaxNode> {
        node.ancestors()
            .find(|ancestor| ancestor.kind() == SyntaxKind::LocalFunctionStatement)
    }

    fn declare_local_function(&mut self, node: &SyntaxNode, container: SymbolId) {
        let Some(token) = name_token(node) else {
            return;
        };
        let return_type = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| self.type_ref(&ty));
        let (mut modifiers, _) = modifiers_of(node);
        // A local function inside a static method is static whether or not it
        // says so: there is no `this` for it to have. Writing it down here is
        // what lets everything downstream ask one question instead of two.
        if self
            .symbols
            .get(container)
            .modifiers
            .contains(Modifiers::STATIC)
        {
            modifiers.insert(Modifiers::STATIC);
        }
        let id = self.symbols.add(
            SymbolKind::Method,
            token.value_text(),
            Some(container),
            Detail::Method(Method {
                return_type,
                returns_readonly: returns_readonly_reference(node),
                method_kind: MethodKind::LocalFunction,
                ..Method::default()
            }),
        );
        let location = self.token_location(&token);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.modifiers = modifiers;
        symbol.accessibility = Accessibility::Private;
        self.record(node, id);
        self.declare_type_parameters(node, id);
        if let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) {
            self.declare_parameters(&list, id);
        }
    }

    fn declare_constructor(&mut self, node: &SyntaxNode, container: SymbolId) {
        let (modifiers, accessibility) = modifiers_of(node);
        let static_constructor = modifiers.contains(Modifiers::STATIC);
        // A partial constructor (C# 14) is one constructor in two parts, as
        // a partial method is: the part with the body is the one kept.
        if modifiers.contains(Modifiers::PARTIAL) {
            let arity = parameter_count(node);
            let other = self
                .symbols
                .lookup(
                    container,
                    if static_constructor {
                        ".cctor"
                    } else {
                        ".ctor"
                    },
                )
                .iter()
                .copied()
                .find(|candidate| {
                    let symbol = self.symbols.get(*candidate);
                    symbol.modifiers.contains(Modifiers::PARTIAL)
                        && symbol
                            .as_method()
                            .is_some_and(|detail| detail.parameters.len() == arity)
                });
            if let Some(other) = other {
                if has_body(node) {
                    self.take_over_partial(node, other);
                }
                return;
            }
        }
        let id = self.symbols.add(
            SymbolKind::Method,
            if static_constructor {
                ".cctor"
            } else {
                ".ctor"
            },
            Some(container),
            Detail::Method(Method {
                method_kind: if static_constructor {
                    MethodKind::StaticConstructor
                } else {
                    MethodKind::Constructor
                },
                ..Method::default()
            }),
        );
        let location = self.location(node);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.modifiers = modifiers;
        symbol.accessibility = accessibility.unwrap_or(Accessibility::Private);
        self.record(node, id);
        if let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) {
            self.declare_parameters(&list, id);
        }
        self.declare_local_functions(node, id);
    }

    fn declare_destructor(&mut self, node: &SyntaxNode, container: SymbolId) {
        let id = self.symbols.add(
            SymbolKind::Method,
            "Finalize",
            Some(container),
            Detail::Method(Method {
                method_kind: MethodKind::Destructor,
                // `~C()` writes no return type; it returns nothing.
                synthesized_return: Some(SynthesizedType::Special(SpecialType::Void)),
                ..Method::default()
            }),
        );
        let location = self.location(node);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.accessibility = Accessibility::Protected;
        symbol.modifiers = Modifiers::OVERRIDE;
        self.record(node, id);
        self.declare_local_functions(node, id);
    }

    fn declare_operator(&mut self, node: &SyntaxNode, container: SymbolId) {
        let conversion = node.kind() == SyntaxKind::ConversionOperatorDeclaration;
        let parameter_count = node
            .child_of_kind(SyntaxKind::ParameterList)
            .map_or(0, |list| {
                list.children()
                    .filter(|child| child.kind() == SyntaxKind::Parameter)
                    .count()
            });

        let name = if conversion {
            if node
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::ImplicitKeyword)
            {
                "op_Implicit"
            } else {
                "op_Explicit"
            }
            .to_string()
        } else {
            let operator = node
                .child_tokens()
                .find(|token| token.kind().is_punctuation() || is_bool_keyword(token.kind()));
            operator.map_or_else(
                || "op_Unknown".to_string(),
                |token| operator_metadata_name(token.text(), parameter_count).to_string(),
            )
        };
        let (modifiers, accessibility) = modifiers_of(node);
        // `void operator ++()` without `static` (C# 14) changes its receiver
        // and is `op_IncrementAssignment`, as `+=` and the other compound
        // operators are named for the assignment they stand for.
        let name = if matches!(name.as_str(), "op_Increment" | "op_Decrement")
            && !modifiers.contains(Modifiers::STATIC)
        {
            format!("{name}Assignment")
        } else {
            name
        };
        // `operator checked -` (C# 11) is a method of its own beside the
        // regular `-`: `op_CheckedSubtraction`, which a checked context
        // prefers and everything else, the runtime binder of `dynamic`
        // included, never sees.
        let name = if node
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::CheckedKeyword)
        {
            checked_operator_name(&name).map_or(name, str::to_string)
        } else {
            name
        };

        // A conversion's return type is the type it converts to, and it comes
        // after the `operator` keyword rather than before it.
        let return_type = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| self.type_ref(&ty));

        let id = self.symbols.add(
            SymbolKind::Method,
            name,
            Some(container),
            Detail::Method(Method {
                return_type,
                method_kind: if conversion {
                    MethodKind::Conversion
                } else {
                    MethodKind::Operator
                },
                ..Method::default()
            }),
        );
        let location = self.location(node);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.modifiers = modifiers;
        symbol.accessibility = accessibility.unwrap_or(Accessibility::Public);
        self.record(node, id);
        if let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) {
            self.declare_parameters(&list, id);
        }
        self.declare_local_functions(node, id);
    }

    fn declare_property(&mut self, node: &SyntaxNode, container: SymbolId) {
        let is_indexer = node.kind() == SyntaxKind::IndexerDeclaration;
        let is_event = node.kind() == SyntaxKind::EventDeclaration;
        let name = if is_indexer {
            "this[]".to_string()
        } else {
            match name_token(node) {
                Some(token) => explicit_name(node, token.value_text()),
                None => return,
            }
        };

        let ty = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| self.type_ref(&ty));
        let (modifiers, accessibility) = modifiers_of(node);

        // The two parts of a partial property or indexer are one (C# 13):
        // the declaring part's accessors are bare, the implementing part's
        // have bodies, and the implementing part is what the symbol is
        // declared by, whichever of the two comes first.
        if !is_event
            && modifiers.contains(Modifiers::PARTIAL)
            && let Some(other) = self
                .partial_properties
                .get(&(container, Self::partial_property_key(node, &name)))
                .copied()
        {
            if implements_accessors(node) {
                self.take_over_partial_property(node, other, ty);
            }
            return;
        }

        let accessors = node.child_of_kind(SyntaxKind::AccessorList);
        let has = |kind: SyntaxKind| {
            accessors
                .as_ref()
                .is_some_and(|list| list.children().any(|child| child.kind() == kind))
        };
        // An expression-bodied property is a getter with no accessor list.
        let expression_bodied = node
            .child_of_kind(SyntaxKind::ArrowExpressionClause)
            .is_some();
        // `private set;` narrows one accessor below the property.
        let accessor_accessibility = |kinds: &[SyntaxKind]| {
            accessors.as_ref().and_then(|list| {
                list.children()
                    .find(|child| kinds.contains(&child.kind()))
                    .and_then(|accessor| modifiers_of(&accessor).1)
            })
        };
        let get_accessibility = accessor_accessibility(&[SyntaxKind::GetAccessorDeclaration]);
        let set_accessibility = accessor_accessibility(&[
            SyntaxKind::SetAccessorDeclaration,
            SyntaxKind::InitAccessorDeclaration,
        ]);

        let detail = if is_event {
            Detail::Event(Event {
                ty,
                adder: None,
                remover: None,
            })
        } else {
            Detail::Property(Property {
                ty,
                parameters: Vec::new(),
                has_get: expression_bodied || has(SyntaxKind::GetAccessorDeclaration),
                has_set: has(SyntaxKind::SetAccessorDeclaration),
                has_init: has(SyntaxKind::InitAccessorDeclaration),
                is_indexer,
                returns_readonly: returns_readonly_reference(node),
                getter: None,
                setter: None,
                backing_field: None,
                synthesized: None,
                get_accessibility,
                set_accessibility,
                extended: None,
                extension_generics: Vec::new(),
            })
        };

        let accessibility = accessibility.unwrap_or_else(|| {
            if is_explicit_implementation(node) {
                Accessibility::Private
            } else {
                default_member_accessibility(&self.symbols, container)
            }
        });
        let id = self.symbols.add(
            if is_event {
                SymbolKind::Event
            } else {
                SymbolKind::Property
            },
            name.clone(),
            Some(container),
            detail,
        );
        let location = self.location(node);
        let symbol = self.symbols.get_mut(id);
        symbol.locations.push(location);
        symbol.modifiers = modifiers;
        symbol.accessibility = accessibility;
        self.record(node, id);
        if modifiers.contains(Modifiers::PARTIAL) && !is_event {
            self.partial_properties
                .insert((container, Self::partial_property_key(node, &name)), id);
        }

        if let Some(list) = node.child_of_kind(SyntaxKind::BracketedParameterList) {
            self.declare_parameters(&list, id);
            let parameters = self.symbols.get(id).members.clone();
            if let Detail::Property(detail) = &mut self.symbols.get_mut(id).detail {
                detail.parameters = parameters;
            }
        }
        if is_event {
            self.declare_event_accessor_bodies(node, id, ty, modifiers, accessibility);
        } else {
            self.declare_accessors(node, id, ty);
            if modifiers.contains(Modifiers::PARTIAL) {
                self.join_partial_property(node, id, container);
            }
        }
    }

    /// The two parts of a partial property are one property (C# 13): the
    /// implementing part, whose accessors have bodies, is the one kept, and
    /// the defining part — which reads like an auto-property — is taken out
    /// of the type, so that no backing field is made for it.
    fn join_partial_property(&mut self, node: &SyntaxNode, id: SymbolId, container: SymbolId) {
        let symbol = self.symbols.get(id);
        let name = symbol.name.clone();
        let is_static = symbol.modifiers.contains(Modifiers::STATIC);
        let arity = symbol
            .as_property()
            .map_or(0, |detail| detail.parameters.len());
        // An indexer's parts are told apart by their parameter types, as
        // written: `this[params int[] a]` and `this[params IEnumerable<string>
        // e]` are two indexers of two parts each.
        let written_types = |node: &SyntaxNode| -> Vec<String> {
            node.child_of_kind(SyntaxKind::BracketedParameterList)
                .map(|list| {
                    list.children()
                        .filter(|child| child.kind() == SyntaxKind::Parameter)
                        .map(|parameter| {
                            parameter
                                .children()
                                .find(|child| child.kind().is_type_node())
                                .map(|ty| ty.text().split_whitespace().collect::<String>())
                                .unwrap_or_default()
                        })
                        .collect()
                })
                .unwrap_or_default()
        };
        let mine = written_types(node);
        let node_of = |this: &Self, symbol: SymbolId| {
            this.declarations
                .iter()
                .find(|(_, declared)| **declared == symbol)
                .and_then(|((tree, span), _)| this.trees.get(*tree)?.0.root().find_node(*span))
        };
        let Some((other, _)) = self
            .symbols
            .lookup(container, &name)
            .iter()
            .copied()
            .filter(|candidate| {
                let other = self.symbols.get(*candidate);
                *candidate != id
                    && other.kind == SymbolKind::Property
                    && other.modifiers.contains(Modifiers::PARTIAL)
                    && other.modifiers.contains(Modifiers::STATIC) == is_static
                    && other
                        .as_property()
                        .is_some_and(|detail| detail.parameters.len() == arity)
            })
            .filter_map(|candidate| node_of(self, candidate).map(|node| (candidate, node)))
            .find(|(_, other_node)| written_types(other_node) == mine)
        else {
            return;
        };
        let implements = |symbols: &Symbols, id: SymbolId| {
            symbols
                .get(id)
                .as_property()
                .is_some_and(|detail| detail.getter.is_some() || detail.setter.is_some())
        };
        let this_implements = implements(&self.symbols, id)
            || node
                .child_of_kind(SyntaxKind::ArrowExpressionClause)
                .is_some();
        let (defining, kept) = if this_implements && !implements(&self.symbols, other) {
            (other, id)
        } else if !this_implements {
            (id, other)
        } else {
            return;
        };
        // An indexer's parameters are the implementing part's, which its
        // bodies name; what callers see of them — defaults, `params`,
        // caller-info attributes — is what the defining part wrote.
        let parameters = |symbols: &Symbols, property: SymbolId| {
            symbols
                .get(property)
                .as_property()
                .map(|detail| detail.parameters.clone())
                .unwrap_or_default()
        };
        let declared = parameters(&self.symbols, defining);
        let kept_parameters = parameters(&self.symbols, kept);
        if declared.len() == kept_parameters.len() {
            for (from, to) in declared.iter().zip(&kept_parameters) {
                let Some(written) = self.symbols.get(*from).as_parameter().cloned() else {
                    continue;
                };
                if let Detail::Parameter(detail) = &mut self.symbols.get_mut(*to).detail {
                    detail.is_params = written.is_params;
                    detail.has_default = written.has_default;
                    detail.caller_info = written.caller_info;
                }
                // The default value is read from the defining part's syntax.
                let nodes: Vec<(usize, TextSpan)> = self
                    .declarations
                    .iter()
                    .filter(|(_, declared)| **declared == *from)
                    .map(|(at, _)| *at)
                    .collect();
                if written.has_default {
                    for at in nodes {
                        self.declarations.insert(at, *to);
                    }
                }
            }
        }
        if let Some(field) = self
            .symbols
            .get(defining)
            .as_property()
            .and_then(|detail| detail.backing_field)
        {
            self.symbols.detach(field);
        }
        self.symbols.detach(defining);
    }

    /// Declares the `add_E` and `remove_E` an event with `add { }` and
    /// `remove { }` blocks wrote (§15.8.2), each with its `value`.
    fn declare_event_accessor_bodies(
        &mut self,
        node: &SyntaxNode,
        event: SymbolId,
        ty: Option<TypeSyntaxRef>,
        modifiers: Modifiers,
        accessibility: Accessibility,
    ) {
        let name = self.symbols.get(event).name.clone();
        // `abstract event Action I1.E;` (C# 8) writes no accessors: it has
        // the two a field-like event has, abstract as it is.
        let Some(list) = node.child_of_kind(SyntaxKind::AccessorList) else {
            if let Some(token) = name_token(node) {
                self.declare_event_accessors(event, ty, &token, modifiers, accessibility);
            }
            return;
        };
        for accessor in list.children() {
            let add = match accessor.kind() {
                SyntaxKind::AddAccessorDeclaration => true,
                SyntaxKind::RemoveAccessorDeclaration => false,
                _ => continue,
            };
            let id = self.symbols.add(
                SymbolKind::Method,
                format!("{}_{name}", if add { "add" } else { "remove" }),
                Some(event),
                Detail::Method(Method {
                    return_type: None,
                    synthesized_return: Some(SynthesizedType::Special(SpecialType::Void)),
                    ..Method::default()
                }),
            );
            let location = self.location(&accessor);
            let symbol = self.symbols.get_mut(id);
            symbol.locations.push(location);
            symbol.modifiers = modifiers;
            symbol.accessibility = accessibility;
            self.record(&accessor, id);
            self.declare_local_functions(&accessor, id);
            let value = self.symbols.add(
                SymbolKind::Parameter,
                "value",
                Some(id),
                Detail::Parameter(Parameter {
                    ty,
                    ..Parameter::default()
                }),
            );
            let at = self.accessor_keyword_location(&accessor);
            self.symbols.get_mut(value).locations.push(at);
            if let Detail::Method(detail) = &mut self.symbols.get_mut(id).detail {
                detail.parameters = vec![value];
            }
            if let Detail::Event(detail) = &mut self.symbols.get_mut(event).detail {
                if add {
                    detail.adder = Some(id);
                } else {
                    detail.remover = Some(id);
                }
            }
        }
    }

    /// Declares the `get_X` and `set_X` an accessor with a body becomes.
    ///
    /// Only an accessor that wrote a body gets one: `int X { get; set; }` is
    /// storage, and the two methods around it are synthesised by whichever
    /// backend needs them rather than declared here.
    fn declare_accessors(
        &mut self,
        node: &SyntaxNode,
        property: SymbolId,
        ty: Option<TypeSyntaxRef>,
    ) {
        let name = self.symbols.get(property).name.clone();
        let is_indexer = self.symbols.get(property).name == "this[]";
        let modifiers = self.symbols.get(property).modifiers;
        let accessibility = self.symbols.get(property).accessibility;
        // An indexer's accessors take its arguments before anything else.
        let arguments = self
            .symbols
            .get(property)
            .as_property()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();

        // An accessor symbol exists where an accessor was written. `int X =>
        // e;` writes none: the property declaration *is* the getter, and
        // binding it binds the getter's body, so nothing is gained by giving
        // that one a symbol of its own.
        let mut accessors: Vec<(SyntaxNode, bool)> = Vec::new();
        if let Some(list) = node.child_of_kind(SyntaxKind::AccessorList) {
            for accessor in list.children() {
                let setter = match accessor.kind() {
                    SyntaxKind::GetAccessorDeclaration => false,
                    SyntaxKind::SetAccessorDeclaration | SyntaxKind::InitAccessorDeclaration => {
                        true
                    }
                    _ => continue,
                };
                let has_body = accessor.children().any(|part| {
                    matches!(
                        part.kind(),
                        SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                    )
                });
                if has_body {
                    accessors.push((accessor, setter));
                }
            }
        }

        // `get => field; set => field = value;` (C# 14) reads and writes a
        // field the language declares for the property: one per property,
        // however many accessors name it. Before C# 14 `field` is an
        // ordinary name, and `@field` always is — and so it is in an
        // indexer's accessors, which have no field of their own.
        let (tree, facts) = self.trees.get(self.tree).expect("the tree being declared");
        let keyword = !is_indexer
            && tree
                .language_version()
                .at_least(rustlyn_syntax::LanguageVersion::CSharp14);
        let field_names = if keyword {
            &facts.field_names[..]
        } else {
            &[][..]
        };
        let names_field = |accessor: &SyntaxNode| within(field_names, accessor).next().is_some();
        // `object P => field = 1;` is a getter too.
        let arrow_names_field = node
            .child_of_kind(SyntaxKind::ArrowExpressionClause)
            .is_some_and(|arrow| names_field(&arrow));
        // An indexer has no backing field: `field` in one is whatever the
        // name means around it.
        if !is_indexer
            && (arrow_names_field || accessors.iter().any(|(accessor, _)| names_field(accessor)))
            && let Some(container) = self.symbols.get(property).container
        {
            let field = self.symbols.add(
                SymbolKind::Field,
                format!("<{name}>k__BackingField"),
                Some(container),
                Detail::Field(Field {
                    ty,
                    has_initializer: false,
                }),
            );
            let symbol = self.symbols.get_mut(field);
            symbol.modifiers = if modifiers.contains(Modifiers::STATIC) {
                Modifiers::STATIC
            } else {
                Modifiers::empty()
            };
            symbol.accessibility = Accessibility::Private;
            if let Detail::Property(detail) = &mut self.symbols.get_mut(property).detail {
                detail.backing_field = Some(field);
            }
        }

        for (accessor, setter) in accessors {
            let accessor_name = if is_indexer {
                format!("{}_Item", if setter { "set" } else { "get" })
            } else {
                format!("{}_{name}", if setter { "set" } else { "get" })
            };
            let id = self.symbols.add(
                SymbolKind::Method,
                accessor_name,
                Some(property),
                Detail::Method(Method {
                    // A setter returns nothing; a getter returns what the
                    // property holds.
                    return_type: if setter { None } else { ty },
                    method_kind: if setter {
                        MethodKind::PropertySet
                    } else {
                        MethodKind::PropertyGet
                    },
                    ..Method::default()
                }),
            );
            let location = self.location(&accessor);
            let symbol = self.symbols.get_mut(id);
            symbol.locations.push(location);
            symbol.modifiers = modifiers;
            // `readonly get` makes the one accessor readonly, whatever the
            // property says.
            if accessor
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::ReadOnlyKeyword)
            {
                symbol.modifiers.insert(Modifiers::READONLY);
            }
            symbol.accessibility = accessibility;
            self.record(&accessor, id);
            // A getter with a block is a body like any other, and may declare
            // local functions of its own.
            self.declare_local_functions(&accessor, id);

            let mut parameters = arguments.clone();
            if setter {
                // `value` is a parameter no one writes, typed as the property
                // is; a setter body has no other way to name what it is given.
                let value = self.symbols.add(
                    SymbolKind::Parameter,
                    "value",
                    Some(id),
                    Detail::Parameter(Parameter {
                        ty,
                        ..Parameter::default()
                    }),
                );
                let at = self.accessor_keyword_location(&accessor);
                self.symbols.get_mut(value).locations.push(at);
                parameters.push(value);
            }
            if let Detail::Method(detail) = &mut self.symbols.get_mut(id).detail {
                detail.parameters = parameters;
            }
            if let Detail::Property(detail) = &mut self.symbols.get_mut(property).detail {
                if setter {
                    detail.setter = Some(id);
                } else {
                    detail.getter = Some(id);
                }
            }
        }
    }

    fn declare_parameters(&mut self, list: &SyntaxNode, owner: SymbolId) {
        // `__arglist` is no parameter: it makes the method a varargs one.
        if list.children().any(|parameter| {
            parameter.kind() == SyntaxKind::Parameter
                && parameter
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::ArgListKeyword)
        }) && let Detail::Method(detail) = &mut self.symbols.get_mut(owner).detail
        {
            detail.is_vararg = true;
        }
        let mut ids = Vec::new();
        let mut is_extension = false;
        for parameter in list.children() {
            if parameter.kind() != SyntaxKind::Parameter {
                continue;
            }
            let Some(token) = name_token(&parameter) else {
                continue;
            };
            let ty = parameter
                .children()
                .find(|child| child.kind().is_type_node())
                .map(|ty| self.type_ref(&ty));

            let mut ref_kind = RefKind::None;
            let mut ref_readonly = false;
            let mut is_params = false;
            for token in parameter.child_tokens() {
                match token.kind() {
                    SyntaxKind::RefKeyword => ref_kind = RefKind::Ref,
                    SyntaxKind::OutKeyword => ref_kind = RefKind::Out,
                    SyntaxKind::InKeyword => ref_kind = RefKind::In,
                    // `ref readonly` (C# 12) is `in` with a different spelling
                    // at the call: the callee gets an address it may not write
                    // through, and metadata marks both the same way.
                    SyntaxKind::ReadOnlyKeyword if ref_kind == RefKind::Ref => {
                        ref_kind = RefKind::In;
                        ref_readonly = true;
                    }
                    SyntaxKind::ParamsKeyword => is_params = true,
                    // `this` on the first parameter is what makes a static
                    // method callable as if it belonged to that type.
                    SyntaxKind::ThisKeyword if ids.is_empty() => is_extension = true,
                    _ => {}
                }
            }

            let id = self.symbols.add(
                SymbolKind::Parameter,
                token.value_text(),
                Some(owner),
                Detail::Parameter(Parameter {
                    ty,
                    ref_kind,
                    ref_readonly,
                    unscoped_ref: parameter_attribute(&parameter, "UnscopedRef").is_some(),
                    is_params,
                    // `[Optional]` makes a parameter optional as much as
                    // `= value` does.
                    has_default: parameter
                        .child_of_kind(SyntaxKind::EqualsValueClause)
                        .is_some()
                        || parameter_attribute(&parameter, "Optional").is_some(),
                    caller_info: caller_info_of(&parameter),
                    handler_arguments: handler_arguments_of(&parameter),
                    enumerator_cancellation: parameter_attribute(
                        &parameter,
                        "EnumeratorCancellation",
                    )
                    .is_some(),
                    ..Parameter::default()
                }),
            );
            // `out T` and `in T` say which way a construction of the type
            // converts, and the keyword is the only place it is written.
            let variance = parameter
                .child_tokens()
                .find_map(|token| match token.kind() {
                    SyntaxKind::OutKeyword => Some(Variance::Out),
                    SyntaxKind::InKeyword => Some(Variance::In),
                    _ => None,
                });
            if let Some(variance) = variance
                && let Detail::TypeParameter(detail) = &mut self.symbols.get_mut(id).detail
            {
                detail.variance = variance;
            }
            let location = self.token_location(&token);
            self.symbols.get_mut(id).locations.push(location);
            self.record(&parameter, id);
            ids.push(id);
        }

        if let Detail::Method(detail) = &mut self.symbols.get_mut(owner).detail {
            detail.parameters = ids;
            detail.is_extension = is_extension;
        }
    }
}

// -- syntax helpers --------------------------------------------------------

/// The identifier a declaration gives itself, ignoring names nested in
/// children such as an explicit interface specifier.
/// The name a member goes by, with the interface it explicitly implements in
/// front of it where there is one.
///
/// `ImmutableArray<IParameterDefinition> IMethodDefinition.Parameters` is not
/// reachable as `Parameters`: C# says an explicit implementation can be called
/// only through the interface, and a type that has both would otherwise find
/// the wrong one.
fn explicit_name(node: &SyntaxNode, name: &str) -> String {
    match node.child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier) {
        Some(specifier) => format!("{}{name}", specifier.text().trim()),
        None => name.to_string(),
    }
}

/// Whether a member declaration names the interface member it implements:
/// such a member is private wherever it is written, an interface included,
/// since nothing reaches it but through that interface.
fn is_explicit_implementation(node: &SyntaxNode) -> bool {
    node.child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier)
        .is_some()
}

fn name_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    node.child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
}

fn type_parameter_names(node: &SyntaxNode) -> Vec<String> {
    node.child_of_kind(SyntaxKind::TypeParameterList)
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::TypeParameter)
                .filter_map(|parameter| {
                    name_token(&parameter).map(|token| token.value_text().to_string())
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Flattens `A.B.C` into its parts, left to right.
fn name_parts(name: &SyntaxNode) -> Vec<(String, SyntaxToken)> {
    let mut parts = Vec::new();
    collect_name_parts(name, &mut parts);
    parts
}

fn collect_name_parts(name: &SyntaxNode, parts: &mut Vec<(String, SyntaxToken)>) {
    match name.kind() {
        SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => {
            for child in name.children() {
                collect_name_parts(&child, parts);
            }
        }
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => {
            if let Some(token) = name_token(name) {
                parts.push((token.value_text().to_string(), token));
            }
        }
        _ => {}
    }
}

fn modifiers_of(node: &SyntaxNode) -> (Modifiers, Option<Accessibility>) {
    let mut modifiers = Modifiers::empty();
    let mut protected = false;
    let mut internal = false;
    let mut accessibility = None;

    for token in node.child_tokens() {
        match token.kind() {
            SyntaxKind::PublicKeyword => accessibility = Some(Accessibility::Public),
            SyntaxKind::PrivateKeyword => accessibility = Some(Accessibility::Private),
            SyntaxKind::ProtectedKeyword => protected = true,
            SyntaxKind::InternalKeyword => internal = true,
            SyntaxKind::StaticKeyword => modifiers.insert(Modifiers::STATIC),
            SyntaxKind::AbstractKeyword => modifiers.insert(Modifiers::ABSTRACT),
            SyntaxKind::SealedKeyword => modifiers.insert(Modifiers::SEALED),
            SyntaxKind::VirtualKeyword => modifiers.insert(Modifiers::VIRTUAL),
            SyntaxKind::OverrideKeyword => modifiers.insert(Modifiers::OVERRIDE),
            SyntaxKind::ReadOnlyKeyword => modifiers.insert(Modifiers::READONLY),
            SyntaxKind::ConstKeyword => {
                modifiers.insert(Modifiers::CONST);
                modifiers.insert(Modifiers::STATIC);
            }
            SyntaxKind::PartialKeyword => modifiers.insert(Modifiers::PARTIAL),
            SyntaxKind::ExternKeyword => modifiers.insert(Modifiers::EXTERN),
            SyntaxKind::UnsafeKeyword => modifiers.insert(Modifiers::UNSAFE),
            SyntaxKind::AsyncKeyword => modifiers.insert(Modifiers::ASYNC),
            SyntaxKind::NewKeyword => modifiers.insert(Modifiers::NEW),
            SyntaxKind::VolatileKeyword => modifiers.insert(Modifiers::VOLATILE),
            SyntaxKind::RequiredKeyword => modifiers.insert(Modifiers::REQUIRED),
            SyntaxKind::FixedKeyword => modifiers.insert(Modifiers::FIXED),
            SyntaxKind::RefKeyword => modifiers.insert(Modifiers::REF),
            SyntaxKind::FileKeyword => modifiers.insert(Modifiers::FILE),
            _ => {}
        }
    }

    // `protected internal` widens; `private protected` narrows.
    if protected || internal {
        accessibility = Some(match (protected, internal, accessibility) {
            (true, true, _) => Accessibility::ProtectedOrInternal,
            (true, false, Some(Accessibility::Private)) => Accessibility::ProtectedAndInternal,
            (true, false, _) => Accessibility::Protected,
            (false, true, _) => Accessibility::Internal,
            (false, false, existing) => return (modifiers, existing),
        });
    }

    (modifiers, accessibility)
}

/// What a type gets when it says nothing: `internal` at namespace level,
/// `public` nested in an interface, `private` nested anywhere else.
fn default_type_accessibility(symbols: &Symbols, container: SymbolId) -> Accessibility {
    match symbols.get(container).kind {
        SymbolKind::Namespace => Accessibility::Internal,
        _ if symbols.get(container).type_kind() == Some(TypeKind::Interface) => {
            Accessibility::Public
        }
        _ => Accessibility::Private,
    }
}

/// What a member gets when it says nothing: `public` in an interface,
/// `private` everywhere else.
fn default_member_accessibility(symbols: &Symbols, container: SymbolId) -> Accessibility {
    match symbols.get(container).type_kind() {
        Some(TypeKind::Interface) => Accessibility::Public,
        _ => Accessibility::Private,
    }
}

const fn is_bool_keyword(kind: SyntaxKind) -> bool {
    matches!(kind, SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword)
}

/// The name an overloaded operator has in metadata.
///
/// `+` is two different operators depending on how many operands it takes,
/// which is why the count matters.
fn operator_metadata_name(text: &str, parameters: usize) -> &'static str {
    match (text, parameters) {
        ("+", 1) => "op_UnaryPlus",
        ("-", 1) => "op_UnaryNegation",
        ("+", _) => "op_Addition",
        ("-", _) => "op_Subtraction",
        ("*", _) => "op_Multiply",
        ("/", _) => "op_Division",
        ("%", _) => "op_Modulus",
        ("&", _) => "op_BitwiseAnd",
        ("|", _) => "op_BitwiseOr",
        ("^", _) => "op_ExclusiveOr",
        ("<<", _) => "op_LeftShift",
        (">>", _) => "op_RightShift",
        (">>>", _) => "op_UnsignedRightShift",
        ("==", _) => "op_Equality",
        ("!=", _) => "op_Inequality",
        ("<", _) => "op_LessThan",
        (">", _) => "op_GreaterThan",
        ("<=", _) => "op_LessThanOrEqual",
        (">=", _) => "op_GreaterThanOrEqual",
        ("!", _) => "op_LogicalNot",
        ("~", _) => "op_OnesComplement",
        ("++", _) => "op_Increment",
        ("--", _) => "op_Decrement",
        ("+=", _) => "op_AdditionAssignment",
        ("-=", _) => "op_SubtractionAssignment",
        ("*=", _) => "op_MultiplicationAssignment",
        ("/=", _) => "op_DivisionAssignment",
        ("%=", _) => "op_ModulusAssignment",
        ("&=", _) => "op_BitwiseAndAssignment",
        ("|=", _) => "op_BitwiseOrAssignment",
        ("^=", _) => "op_ExclusiveOrAssignment",
        ("<<=", _) => "op_LeftShiftAssignment",
        (">>=", _) => "op_RightShiftAssignment",
        (">>>=", _) => "op_UnsignedRightShiftAssignment",
        ("true", _) => "op_True",
        ("false", _) => "op_False",
        _ => "op_Unknown",
    }
}

/// The name of the checked form of an operator (C# 11), for the operators
/// that have one: the arithmetic that can overflow, and explicit
/// conversions.
#[must_use]
pub(crate) fn checked_operator_name(name: &str) -> Option<&'static str> {
    Some(match name {
        "op_Addition" => "op_CheckedAddition",
        "op_Subtraction" => "op_CheckedSubtraction",
        "op_Multiply" => "op_CheckedMultiply",
        "op_Division" => "op_CheckedDivision",
        "op_UnaryNegation" => "op_CheckedUnaryNegation",
        "op_Increment" => "op_CheckedIncrement",
        "op_Decrement" => "op_CheckedDecrement",
        "op_AdditionAssignment" => "op_CheckedAdditionAssignment",
        "op_SubtractionAssignment" => "op_CheckedSubtractionAssignment",
        "op_MultiplicationAssignment" => "op_CheckedMultiplicationAssignment",
        "op_DivisionAssignment" => "op_CheckedDivisionAssignment",
        "op_IncrementAssignment" => "op_CheckedIncrementAssignment",
        "op_DecrementAssignment" => "op_CheckedDecrementAssignment",
        "op_Explicit" => "op_CheckedExplicit",
        _ => return None,
    })
}

/// The property names an anonymous object creation declares, in order: the
/// name before `=` where one was written, else the last identifier of the
/// expression (`x.Name` and `local` name `Name` and `local`).
pub(crate) fn anonymous_member_names(node: &SyntaxNode) -> Vec<String> {
    let Some(initializer) = node.child_of_kind(SyntaxKind::ObjectInitializerExpression) else {
        return Vec::new();
    };
    initializer
        .children()
        .filter(|child| child.kind() == SyntaxKind::AnonymousObjectMemberDeclarator)
        .filter_map(|declarator| {
            if let Some(name) = declarator.child_of_kind(SyntaxKind::NameEquals) {
                return name
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| token.value_text().to_string());
            }
            let expression = declarator
                .children()
                .find(|child| child.kind().is_expression())?;
            projected_name(&expression)
        })
        .collect()
}

/// The name `new { x.Name }` gives its member: the last identifier written.
fn projected_name(expression: &SyntaxNode) -> Option<String> {
    match expression.kind() {
        SyntaxKind::IdentifierName => expression
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| token.value_text().to_string()),
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression => {
            expression
                .children()
                .filter(|child| child.kind() == SyntaxKind::IdentifierName)
                .last()
                .and_then(|name| projected_name(&name))
        }
        _ => None,
    }
}

/// Whether a method declaration carries a body: a block or an `=> e`.
fn has_body(node: &SyntaxNode) -> bool {
    node.child_of_kind(SyntaxKind::Block).is_some()
        || node
            .child_of_kind(SyntaxKind::ArrowExpressionClause)
            .is_some()
}

/// Whether a property declaration gives any accessor a body: what tells the
/// implementing part of a partial property from its declaring part.
fn implements_accessors(node: &SyntaxNode) -> bool {
    node.child_of_kind(SyntaxKind::ArrowExpressionClause)
        .is_some()
        || node
            .child_of_kind(SyntaxKind::AccessorList)
            .is_some_and(|list| list.children().any(|accessor| has_body(&accessor)))
}

/// How many parameters a member declaration writes.
fn parameter_count(node: &SyntaxNode) -> usize {
    node.child_of_kind(SyntaxKind::ParameterList)
        .map_or(0, |list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
                .count()
        })
}

/// The caller-info attribute written on a parameter, if any (§22.5.6).
/// The `[Name]` or `[NameAttribute]` written on a parameter, if it is.
pub(crate) fn parameter_attribute(parameter: &SyntaxNode, name: &str) -> Option<SyntaxNode> {
    let long = format!("{name}Attribute");
    parameter
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
        .flat_map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::Attribute)
        })
        .find(|attribute| {
            attribute.children().next().is_some_and(|written| {
                let text = written.text().to_string();
                let last = text
                    .trim()
                    .rsplit('.')
                    .next()
                    .unwrap_or_default()
                    .to_string();
                last == name || last == long
            })
        })
}

/// The value a `[DefaultParameterValue(value)]` on a parameter gives it: the
/// expression, where the parameter is `[Optional]` too and so optional at
/// all.
pub(crate) fn attributed_default(parameter: &SyntaxNode) -> Option<SyntaxNode> {
    parameter_attribute(parameter, "Optional")?;
    parameter_attribute(parameter, "DefaultParameterValue")?
        .child_of_kind(SyntaxKind::AttributeArgumentList)?
        .child_of_kind(SyntaxKind::AttributeArgument)?
        .children()
        .find(|child| child.kind().is_expression())
}

/// The names `[InterpolatedStringHandlerArgument("a", "")]` on a parameter
/// lists, in order: the parameters, and `""` for the receiver, whose
/// arguments the handler an interpolated string argument becomes is made
/// with. Each is a string constant, which is all the attribute takes: a
/// literal or a `nameof`.
fn handler_arguments_of(parameter: &SyntaxNode) -> Option<Vec<String>> {
    let attribute = parameter_attribute(parameter, "InterpolatedStringHandlerArgument")?;
    attribute
        .child_of_kind(SyntaxKind::AttributeArgumentList)
        .into_iter()
        .flat_map(|list| list.children())
        .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
        .map(|argument| {
            let expression = argument
                .children()
                .find(|child| child.kind().is_expression())?;
            // `nameof(condition)`, as Roslyn's own `RoslynDebug.Assert`
            // writes it, is the name written last in it.
            if expression.kind() == SyntaxKind::InvocationExpression
                && expression
                    .children()
                    .next()
                    .is_some_and(|callee| callee.text().trim() == "nameof")
            {
                let written = expression
                    .child_of_kind(SyntaxKind::ArgumentList)?
                    .child_of_kind(SyntaxKind::Argument)?
                    .text()
                    .trim()
                    .to_string();
                return written
                    .rsplit('.')
                    .next()
                    .map(|name| name.trim().to_string());
            }
            match expression.first_token()?.value() {
                TokenValue::String(text)
                    if expression.kind() == SyntaxKind::StringLiteralExpression =>
                {
                    Some(text.to_string())
                }
                _ => None,
            }
        })
        .collect()
}

fn caller_info_of(parameter: &SyntaxNode) -> Option<CallerInfo> {
    // More than one may be written: the line wins over the file, the file
    // over the member name, and any of them over the argument text; of two
    // argument texts the one written last is the one.
    let mut found: Vec<CallerInfo> = Vec::new();
    for list in parameter
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
    {
        for attribute in list
            .children()
            .filter(|child| child.kind() == SyntaxKind::Attribute)
        {
            if let Some(info) = caller_info_in(&attribute) {
                found.push(info);
            }
        }
    }
    let rank = |info: &CallerInfo| match info {
        CallerInfo::LineNumber => 3,
        CallerInfo::FilePath => 2,
        CallerInfo::MemberName => 1,
        CallerInfo::ArgumentExpression(_) | CallerInfo::ArgumentConstant(_) => 0,
    };
    let best = found.iter().map(rank).max()?;
    found.into_iter().rfind(|info| rank(info) == best)
}

/// The caller-info attribute one `[...]` entry is, if it is one.
fn caller_info_in(attribute: &SyntaxNode) -> Option<CallerInfo> {
    let name = attribute.children().next()?;
    let name = name.text();
    let name = name.trim().rsplit('.').next().unwrap_or_default();
    let name = name.strip_suffix("Attribute").unwrap_or(name);
    match name {
        "CallerMemberName" => Some(CallerInfo::MemberName),
        "CallerLineNumber" => Some(CallerInfo::LineNumber),
        "CallerFilePath" => Some(CallerInfo::FilePath),
        "CallerArgumentExpression" => {
            // Only the constructor that takes the parameter's name alone
            // makes the attribute one the compiler reads.
            let count = attribute
                .child_of_kind(SyntaxKind::AttributeArgumentList)
                .map_or(0, |list| {
                    list.children()
                        .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
                        .count()
                });
            if count != 1 {
                return None;
            }
            let argument = attribute
                .child_of_kind(SyntaxKind::AttributeArgumentList)
                .and_then(|list| list.child_of_kind(SyntaxKind::AttributeArgument))
                .and_then(|argument| {
                    argument
                        .children()
                        .find(|child| child.kind().is_expression())
                })?;
            match argument.kind() {
                SyntaxKind::StringLiteralExpression => {
                    let token = argument.child_tokens().next()?;
                    match token.value() {
                        TokenValue::String(text) => {
                            Some(CallerInfo::ArgumentExpression(text.to_string()))
                        }
                        _ => None,
                    }
                }
                // `nameof(p)` is the name written last in it.
                SyntaxKind::InvocationExpression
                    if argument
                        .children()
                        .next()
                        .is_some_and(|callee| callee.text().trim() == "nameof") =>
                {
                    argument
                        .child_of_kind(SyntaxKind::ArgumentList)
                        .and_then(|list| list.child_of_kind(SyntaxKind::Argument))
                        .map(|part| part.text().trim().to_string())
                        .and_then(|text| {
                            text.rsplit('.').next().map(|name| name.trim().to_string())
                        })
                        .map(CallerInfo::ArgumentExpression)
                }
                SyntaxKind::IdentifierName => Some(CallerInfo::ArgumentConstant(
                    argument.text().trim().to_string(),
                )),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether a top-level statement `await`s anything of its own: an `await`
/// inside a lambda, an anonymous method or a local function is theirs.
fn statement_awaits(statement: &SyntaxNode) -> bool {
    fn walk(node: &SyntaxNode) -> bool {
        match node.kind() {
            SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::RecordDeclaration => false,
            SyntaxKind::AwaitExpression => true,
            SyntaxKind::ForEachStatement
            | SyntaxKind::ForEachVariableStatement
            | SyntaxKind::UsingStatement
            | SyntaxKind::LocalDeclarationStatement
                if node
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::AwaitKeyword) =>
            {
                true
            }
            _ => node.children().any(|child| walk(&child)),
        }
    }
    walk(statement)
}

/// Whether a top-level statement `return`s a value of its own.
fn statement_returns_a_value(statement: &SyntaxNode) -> bool {
    fn walk(node: &SyntaxNode) -> bool {
        match node.kind() {
            SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::RecordDeclaration => false,
            SyntaxKind::ReturnStatement => {
                node.children().any(|child| child.kind().is_expression())
            }
            _ => node.children().any(|child| walk(&child)),
        }
    }
    walk(statement)
}

/// Whether a declaration's type is `ref readonly T`: a reference nothing may
/// write through, which its signature marks with `modreq(InAttribute)`.
fn returns_readonly_reference(node: &SyntaxNode) -> bool {
    node.children()
        .find(|child| child.kind().is_type_node())
        .is_some_and(|ty| {
            ty.kind() == SyntaxKind::RefType
                && ty
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::ReadOnlyKeyword)
        })
}

/// Settles what a record inherits from a referenced record, which the
/// declaration pass could not see: references are read after the source is
/// declared. A positional parameter a referenced base already has an
/// accessible property or field for makes no property of its own — unless
/// that is an abstract property, which the record then overrides (Roslyn's
/// `FindFirstHiddenMemberIfAny`, over the whole chain).
pub(crate) fn settle_records_over_references(
    symbols: &mut Symbols,
    floor: usize,
    declared: &std::collections::HashSet<SymbolId>,
    bases: &crate::fxhash::FxHashMap<SymbolId, Vec<crate::types::Type>>,
    trees: &[SyntaxTree],
) {
    let records: Vec<SymbolId> = symbols
        .iter()
        .take(floor)
        .filter(|symbol| {
            symbol.kind == SymbolKind::NamedType && symbol.type_kind() == Some(TypeKind::Record)
        })
        .map(|symbol| symbol.id)
        .collect();
    for record in records {
        let Some(base) = referenced_record_base(symbols, record, floor, trees) else {
            continue;
        };
        let parameters: Vec<String> = symbols
            .get(record)
            .as_named_type()
            .and_then(|detail| detail.primary_constructor)
            .and_then(|constructor| symbols.get(constructor).as_method())
            .map(|detail| {
                detail
                    .parameters
                    .iter()
                    .map(|parameter| symbols.get(*parameter).name.clone())
                    .collect()
            })
            .unwrap_or_default();
        for name in parameters {
            let Some(property) = symbols
                .lookup(record, &name)
                .iter()
                .copied()
                .find(|member| {
                    symbols.get(*member).kind == SymbolKind::Property && !declared.contains(member)
                })
            else {
                continue;
            };
            let Some(inherited) = inherited_from_reference(symbols, bases, base, &name) else {
                continue;
            };
            // One read from metadata is abstract by its accessors.
            let abstract_property = symbols.get(inherited).kind == SymbolKind::Property
                && (symbols
                    .get(inherited)
                    .modifiers
                    .contains(Modifiers::ABSTRACT)
                    || symbols.get(inherited).as_property().is_some_and(|detail| {
                        [detail.getter, detail.setter]
                            .into_iter()
                            .flatten()
                            .any(|accessor| {
                                symbols
                                    .get(accessor)
                                    .modifiers
                                    .contains(Modifiers::ABSTRACT)
                            })
                    }));
            if abstract_property {
                symbols
                    .get_mut(property)
                    .modifiers
                    .insert(Modifiers::OVERRIDE);
            } else {
                symbols.unlink(property);
            }
        }
    }
}

/// The referenced record a record's base list names first: a type of that
/// name and arity read from metadata with a `<Clone>$` of its own.
fn referenced_record_base(
    symbols: &Symbols,
    record: SymbolId,
    floor: usize,
    trees: &[SyntaxTree],
) -> Option<SymbolId> {
    let first = symbols
        .get(record)
        .as_named_type()?
        .base_types
        .first()
        .copied()?;
    let tree = trees.get(first.0.tree)?;
    let written = tree.root().find_node(first.0.span)?.text().to_string();
    let written: String = written.chars().filter(|c| !c.is_whitespace()).collect();
    let arity = written
        .split_once('<')
        .map_or(0, |(_, arguments)| arguments.matches(',').count() + 1);
    let bare = written.split('<').next().unwrap_or(&written);
    let simple = bare.rsplit(['.', ':']).next().unwrap_or(bare);
    symbols
        .iter()
        .skip(floor)
        .find(|symbol| {
            symbol.kind == SymbolKind::NamedType
                && symbol.name == simple
                && symbol
                    .as_named_type()
                    .is_some_and(|detail| detail.type_parameters.len() == arity)
                && !symbols.lookup(symbol.id, "<Clone>$").is_empty()
        })
        .map(|symbol| symbol.id)
}

/// The property or field called `name` a referenced class or one of its
/// bases has, where another assembly can reach it: public or protected.
fn inherited_from_reference(
    symbols: &Symbols,
    bases: &crate::fxhash::FxHashMap<SymbolId, Vec<crate::types::Type>>,
    start: SymbolId,
    name: &str,
) -> Option<SymbolId> {
    let mut current = Some(start);
    let mut depth = 0;
    while let Some(ty) = current {
        if let Some(found) = symbols.lookup(ty, name).iter().copied().find(|member| {
            let member = symbols.get(*member);
            // A property read from metadata says how far it is seen by its
            // accessors.
            let accessibility = match member.as_property() {
                Some(detail) if member.accessibility == Accessibility::NotApplicable => detail
                    .getter
                    .or(detail.setter)
                    .map_or(Accessibility::NotApplicable, |accessor| {
                        symbols.get(accessor).accessibility
                    }),
                _ => member.accessibility,
            };
            matches!(member.kind, SymbolKind::Property | SymbolKind::Field)
                && !member.modifiers.contains(Modifiers::STATIC)
                && matches!(
                    accessibility,
                    Accessibility::Public
                        | Accessibility::Protected
                        | Accessibility::ProtectedOrInternal
                )
        }) {
            return Some(found);
        }
        depth += 1;
        if depth > 64 {
            return None;
        }
        current = bases
            .get(&ty)
            .and_then(|list| list.first())
            .and_then(crate::types::Type::symbol);
    }
    None
}
