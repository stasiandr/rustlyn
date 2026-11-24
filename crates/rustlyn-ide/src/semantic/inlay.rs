//! Inlay hints: the names and types the code leaves out, shown in place.
//!
//! Roslyn's InlineHints feature, with its two halves. **Parameter hints** put
//! `count:` in front of an argument whose parameter the call does not name;
//! **type hints** put `int` in front of a variable whose type `var`, a
//! lambda or a `new()` left out. Roslyn has them off until the user turns
//! them on, and then shows each kind its options allow; [`InlayHintOptions`]
//! defaults to what Roslyn shows once they are turned on.
//!
//! Most arguments would get a hint, and most of those hints would say what
//! the code already says — `SetColor(color)`, `Max(value1, value2)`,
//! `Log(message)`. Roslyn leaves those out, and so does this: an argument
//! named like its parameter, a method whose name ends in its parameter's,
//! parameters told apart only by a numbered or lettered suffix.
//!
//! An editor asks for the hints of what is on screen, as it scrolls, so only
//! the part of the tree that overlaps the range is visited and only the
//! bodies in it are bound.

use rustlyn_semantics::{BoundExpressionKind, MethodKind, SymbolId, SymbolKind, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::walk::find_expression;
use super::{Place, Resolved, Semantic, View};
use crate::edit::TextEdit;

/// Which hints to show: Roslyn's `InlineParameterHintsOptions` and
/// `InlineTypeHintsOptions`, defaulting to what Roslyn shows once the two
/// kinds are turned on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools)] // one check box each, as Roslyn has them
pub struct InlayHintOptions {
    /// Parameter names at all.
    pub parameters: bool,
    /// Before a literal: `Wait(500)`, `Open("a.txt")`, `-1`.
    pub for_literal_parameters: bool,
    /// Before a `new`: `Add(new Item())`.
    pub for_object_creation_parameters: bool,
    /// Before anything else: a variable, a call, a member. Off in Roslyn,
    /// where it is the noisiest by far.
    pub for_other_parameters: bool,
    /// Inside `[...]` of an indexer.
    pub for_indexer_parameters: bool,
    /// Not where the parameters differ only by a numbered or lettered
    /// suffix: `Max(value1, value2)`, `Lerp(pointA, pointB)`.
    pub suppress_for_parameters_that_differ_only_by_suffix: bool,
    /// Not where the method's name already says it: `SetColor(color)`,
    /// `FromResult(result)`, `EnableLogging(true)`.
    pub suppress_for_parameters_that_match_method_intent: bool,
    /// Not where the argument is named like the parameter: `Load(path)`,
    /// `Load(this.path)`, `Load(configPath)`.
    pub suppress_for_parameters_that_match_argument_name: bool,
    /// Types at all.
    pub types: bool,
    /// After `var`, in a declaration, a `foreach`, an `out var` or a
    /// deconstruction.
    pub for_implicit_variable_types: bool,
    /// Before a lambda's parameter that has no type written.
    pub for_lambda_parameter_types: bool,
    /// After the `new` of a `new()` that does not name its type.
    pub for_implicit_object_creation: bool,
}

impl Default for InlayHintOptions {
    fn default() -> Self {
        Self {
            parameters: true,
            for_literal_parameters: true,
            for_object_creation_parameters: true,
            for_other_parameters: false,
            for_indexer_parameters: true,
            suppress_for_parameters_that_differ_only_by_suffix: true,
            suppress_for_parameters_that_match_method_intent: true,
            suppress_for_parameters_that_match_argument_name: true,
            types: true,
            for_implicit_variable_types: true,
            for_lambda_parameter_types: true,
            for_implicit_object_creation: true,
        }
    }
}

/// What a hint shows.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum InlayHintKind {
    /// A type: `int`, `List<string>`.
    Type = 0,
    /// A parameter's name: `count:`.
    Parameter = 1,
}

/// One hint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InlayHint {
    /// Where it goes, in bytes: the hint is drawn before the character here.
    pub position: u32,
    /// What it says: `count:` or `int`.
    pub label: String,
    pub kind: InlayHintKind,
    /// Whether to leave a space before it, and after it. Roslyn draws a type
    /// placed in front of a name with a space after it, and one placed after
    /// `new` with a space before it.
    pub padding_left: bool,
    pub padding_right: bool,
    /// What clicking it goes to: the parameter, or the type.
    pub target: Option<Place>,
    /// What double-clicking it writes into the code: `count: ` before the
    /// argument, or the type in place of `var`.
    pub replacement: Option<TextEdit>,
}

impl Semantic {
    /// The hints for `range` of `path` as the editor has it.
    #[must_use]
    pub fn inlay_hints(
        &self,
        path: &std::path::Path,
        range: TextSpan,
        text: Option<&str>,
        options: &InlayHintOptions,
    ) -> Option<Vec<InlayHint>> {
        let mut view = self.view_of(path, text)?;
        Some(view.inlay_hints(range, options))
    }
}

/// What an argument is, for deciding whether it gets a hint.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ArgumentKind {
    Literal,
    ObjectCreation,
    Other,
}

impl View<'_> {
    /// The hints for `range` of the file this view is of.
    pub fn inlay_hints(&mut self, range: TextSpan, options: &InlayHintOptions) -> Vec<InlayHint> {
        let mut nodes = Vec::new();
        nodes_in(&self.root, range, &mut nodes);
        let mut hints = Vec::new();
        for node in nodes {
            match node.kind() {
                SyntaxKind::ArgumentList
                | SyntaxKind::BracketedArgumentList
                | SyntaxKind::AttributeArgumentList
                    if options.parameters =>
                {
                    self.parameter_hints(&node, options, &mut hints);
                }
                _ if options.types => self.type_hints(&node, options, &mut hints),
                _ => {}
            }
        }
        hints.retain(|hint| {
            range.contains(hint.position) || range.end() == hint.position || range.is_empty()
        });
        hints.sort_by_key(|hint| hint.position);
        hints
    }

    // MARK: - parameters

    fn parameter_hints(
        &mut self,
        list: &SyntaxNode,
        options: &InlayHintOptions,
        hints: &mut Vec<InlayHint>,
    ) {
        let Some(call) = list.parent().cloned() else {
            return;
        };
        let is_indexer = list.kind() == SyntaxKind::BracketedArgumentList;
        if is_indexer && !options.for_indexer_parameters {
            return;
        }
        let Some((method, shift)) = self.called(&call) else {
            return;
        };
        let symbols = self.compilation().symbols();
        let parameters: Vec<SymbolId> = match symbols.get(method).kind {
            SymbolKind::Method => symbols
                .get(method)
                .as_method()
                .map(|found| found.parameters.clone())
                .unwrap_or_default(),
            SymbolKind::Property => symbols
                .get(method)
                .as_property()
                .map(|found| found.parameters.clone())
                .unwrap_or_default(),
            _ => return,
        };
        let differ_by_suffix = options.suppress_for_parameters_that_differ_only_by_suffix
            && differ_only_by_suffix(
                &parameters
                    .iter()
                    .map(|&parameter| symbols.get(parameter).name.as_str())
                    .collect::<Vec<_>>(),
            );
        let arguments: Vec<SyntaxNode> = list
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Argument | SyntaxKind::AttributeArgument
                )
            })
            .collect();
        for (index, argument) in arguments.iter().enumerate() {
            // Already named, or setting a property of an attribute.
            if argument.child_of_kind(SyntaxKind::NameColon).is_some()
                || argument.child_of_kind(SyntaxKind::NameEquals).is_some()
            {
                continue;
            }
            let Some(&parameter) = parameters.get(index + shift) else {
                continue;
            };
            let name = symbols.get(parameter).name.clone();
            if name.is_empty() || differ_by_suffix {
                continue;
            }
            let Some(expression) = argument.children().last() else {
                continue;
            };
            let allowed = match argument_kind(&expression) {
                ArgumentKind::Literal => options.for_literal_parameters,
                ArgumentKind::ObjectCreation => options.for_object_creation_parameters,
                ArgumentKind::Other => options.for_other_parameters,
            };
            if !allowed {
                continue;
            }
            if options.suppress_for_parameters_that_match_method_intent
                && index + shift == 0
                && matches_method_intent(&symbols.get(method).name, &name)
            {
                continue;
            }
            if options.suppress_for_parameters_that_match_argument_name
                && argument_name(&expression)
                    .is_some_and(|written| matches_argument_name(&written, &name))
            {
                continue;
            }
            let position = argument.span().start();
            let target = self.place_of(parameter);
            hints.push(InlayHint {
                position,
                label: format!("{name}:"),
                kind: InlayHintKind::Parameter,
                padding_left: false,
                padding_right: true,
                target,
                replacement: Some(TextEdit::insert(position, format!("{name}: "))),
            });
        }
    }

    /// What an argument list's call calls: the method, constructor or
    /// indexer, and how many parameters the arguments skip — one for an
    /// extension method called on its first argument.
    fn called(&mut self, call: &SyntaxNode) -> Option<(SymbolId, usize)> {
        let symbols = self.compilation().symbols();
        match call.kind() {
            SyntaxKind::InvocationExpression => {
                let callee = call.children().next()?;
                let name = name_token(&callee)?;
                let body = self.body_for(call)?;
                let found = match body.symbol_at(name.span()) {
                    Some(rustlyn_semantics::BoundSymbol::Declared(symbol)) => Some(symbol),
                    _ => None,
                };
                let method = match found {
                    Some(symbol) if symbols.get(symbol).kind == SymbolKind::Method => symbol,
                    // A delegate called like a method: its `Invoke`.
                    _ => {
                        let ty = body.type_at(callee.span()).cloned()?;
                        self.delegate_invoke(&ty)?
                    }
                };
                let detail = symbols.get(method).as_method()?;
                let reduced = detail.is_extension
                    && callee.kind() == SyntaxKind::SimpleMemberAccessExpression
                    && !callee
                        .children()
                        .next()
                        .and_then(|receiver| name_token(&receiver))
                        .and_then(|token| match body.symbol_at(token.span()) {
                            Some(rustlyn_semantics::BoundSymbol::Declared(symbol)) => Some(symbol),
                            _ => None,
                        })
                        .is_some_and(|symbol| symbols.get(symbol).kind == SymbolKind::NamedType);
                Some((method, usize::from(reduced)))
            }
            SyntaxKind::ObjectCreationExpression => {
                let ty = call.children().find(|child| child.kind().is_type_node())?;
                let name = name_token(&ty)?;
                let body = self.body_for(call)?;
                match body.symbol_at(name.span()) {
                    Some(rustlyn_semantics::BoundSymbol::Declared(symbol))
                        if is_constructor(self, symbol) =>
                    {
                        Some((symbol, 0))
                    }
                    _ => None,
                }
            }
            SyntaxKind::ImplicitObjectCreationExpression => {
                let body = self.body_for(call)?;
                let span = call.span();
                let created = find_expression(&body, &|expression| {
                    expression.span == span
                        && matches!(expression.kind, BoundExpressionKind::ObjectCreation { .. })
                })?;
                match &created.kind {
                    BoundExpressionKind::ObjectCreation {
                        constructor: Some(constructor),
                        ..
                    } => Some((*constructor, 0)),
                    _ => None,
                }
            }
            SyntaxKind::ElementAccessExpression => {
                let body = self.body_for(call)?;
                let span = call.span();
                let access = find_expression(&body, &|expression| {
                    expression.span == span
                        && matches!(expression.kind, BoundExpressionKind::IndexerAccess { .. })
                })?;
                match &access.kind {
                    BoundExpressionKind::IndexerAccess { indexer, .. } => Some((*indexer, 0)),
                    _ => None,
                }
            }
            SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer => {
                let body = self.body_for(call)?;
                body.statements
                    .iter()
                    .find_map(|statement| match &statement.kind {
                        rustlyn_semantics::BoundStatementKind::ConstructorInitializer {
                            constructor: Some(constructor),
                            ..
                        } => Some((*constructor, 0)),
                        _ => None,
                    })
            }
            SyntaxKind::Attribute => {
                let ty = self.attribute_type(call)?;
                let arguments = call
                    .child_of_kind(SyntaxKind::AttributeArgumentList)
                    .map_or(0, |list| {
                        list.children()
                            .filter(|argument| {
                                argument.child_of_kind(SyntaxKind::NameEquals).is_none()
                                    && argument.child_of_kind(SyntaxKind::NameColon).is_none()
                            })
                            .count()
                    });
                // The constructor the positional arguments fit: the one
                // with that many parameters, or failing that the only one.
                let constructors: Vec<SymbolId> = symbols
                    .get(ty)
                    .members
                    .iter()
                    .copied()
                    .filter(|&member| is_constructor(self, member))
                    .collect();
                let fits = |constructor: &&SymbolId| {
                    symbols
                        .get(**constructor)
                        .as_method()
                        .is_some_and(|method| method.parameters.len() == arguments)
                };
                constructors
                    .iter()
                    .find(fits)
                    .or_else(|| (constructors.len() == 1).then(|| &constructors[0]))
                    .map(|&constructor| (constructor, 0))
            }
            _ => None,
        }
    }

    /// A delegate type's `Invoke`.
    fn delegate_invoke(&self, ty: &Type) -> Option<SymbolId> {
        let symbols = self.compilation().symbols();
        let Type::Named { symbol, .. } = ty else {
            return None;
        };
        if symbols.get(*symbol).type_kind() != Some(TypeKind::Delegate) {
            return None;
        }
        symbols
            .lookup(*symbol, "Invoke")
            .iter()
            .copied()
            .find(|&member| symbols.get(member).kind == SymbolKind::Method)
    }

    /// Where a symbol is declared, in the text this view is of.
    pub(super) fn place_of(&self, symbol: SymbolId) -> Option<Place> {
        let resolved = Resolved::Symbol(symbol);
        let mut found = self.semantic.places_of(&resolved);
        if let Some(path) = self.semantic.path_of(self.tree) {
            let path = path.to_path_buf();
            self.move_into_edited(&path, &resolved, &mut found);
        }
        found.into_iter().next().map(|found| found.place)
    }

    // MARK: - types

    fn type_hints(
        &mut self,
        node: &SyntaxNode,
        options: &InlayHintOptions,
        hints: &mut Vec<InlayHint>,
    ) {
        match node.kind() {
            // `var x = 1;`, one declarator only, as Roslyn has it.
            SyntaxKind::VariableDeclaration if options.for_implicit_variable_types => {
                let Some(var) = node.children().next().filter(is_var) else {
                    return;
                };
                let declarators: Vec<SyntaxNode> = node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
                    .collect();
                if let [declarator] = declarators.as_slice()
                    && let Some(name) = declarator.child_token_of_kind(SyntaxKind::IdentifierToken)
                {
                    self.variable_hint(&var, &name, hints);
                }
            }
            SyntaxKind::ForEachStatement if options.for_implicit_variable_types => {
                let Some(var) = node.children().find(is_var) else {
                    return;
                };
                if let Some(name) = node.child_token_of_kind(SyntaxKind::IdentifierToken) {
                    self.variable_hint(&var, &name, hints);
                }
            }
            // `out var x`, `var (a, b) = ...`, `is var x`: each name.
            SyntaxKind::SingleVariableDesignation if options.for_implicit_variable_types => {
                let Some(name) = node.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                    return;
                };
                let var = node
                    .ancestors()
                    .take_while(|ancestor| {
                        matches!(
                            ancestor.kind(),
                            SyntaxKind::ParenthesizedVariableDesignation
                                | SyntaxKind::DeclarationExpression
                                | SyntaxKind::VarPattern
                        )
                    })
                    .last()
                    .and_then(|outer| match outer.kind() {
                        SyntaxKind::DeclarationExpression => outer.children().next(),
                        SyntaxKind::VarPattern => Some(outer),
                        _ => None,
                    });
                let Some(var) = var else { return };
                if var.kind() == SyntaxKind::VarPattern || is_var(&var) {
                    self.variable_hint(&var, &name, hints);
                }
            }
            SyntaxKind::Parameter if options.for_lambda_parameter_types => {
                let in_lambda = node.parent().is_some_and(|parent| {
                    parent.kind() == SyntaxKind::SimpleLambdaExpression
                        || (parent.kind() == SyntaxKind::ParameterList
                            && parent.parent().is_some_and(|lambda| {
                                lambda.kind() == SyntaxKind::ParenthesizedLambdaExpression
                            }))
                });
                let typed = node.children().any(|child| child.kind().is_type_node());
                if !in_lambda || typed {
                    return;
                }
                let Some(name) = node.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                    return;
                };
                if name.value_text() == "_" {
                    return;
                }
                let Some(ty) = self.local_type(node, &name) else {
                    return;
                };
                if let Some(label) = self.shown(&ty) {
                    let position = name.span().start();
                    hints.push(InlayHint {
                        position,
                        replacement: Some(TextEdit::insert(position, format!("{label} "))),
                        label,
                        kind: InlayHintKind::Type,
                        padding_left: false,
                        padding_right: true,
                        target: self.type_place(&ty),
                    });
                }
            }
            SyntaxKind::ImplicitObjectCreationExpression
                if options.for_implicit_object_creation =>
            {
                let Some(new) = node.child_token_of_kind(SyntaxKind::NewKeyword) else {
                    return;
                };
                let Some(body) = self.body_for(node) else {
                    return;
                };
                let span = node.span();
                let ty = find_expression(&body, &|expression| {
                    expression.span == span
                        && matches!(expression.kind, BoundExpressionKind::ObjectCreation { .. })
                })
                .map(|created| created.ty.clone())
                .or_else(|| body.type_at(span).cloned());
                let Some(ty) = ty else { return };
                if let Some(label) = self.shown(&ty) {
                    let position = new.span().end();
                    hints.push(InlayHint {
                        position,
                        replacement: Some(TextEdit::insert(position, format!(" {label}"))),
                        label,
                        kind: InlayHintKind::Type,
                        padding_left: true,
                        padding_right: false,
                        target: self.type_place(&ty),
                    });
                }
            }
            _ => {}
        }
    }

    /// The hint for a variable declared with `var`: its type, in front of
    /// its name; double-clicked, the type replaces the `var`.
    fn variable_hint(&mut self, var: &SyntaxNode, name: &SyntaxToken, hints: &mut Vec<InlayHint>) {
        if name.value_text() == "_" {
            return;
        }
        let Some(ty) = self.local_type(var, name) else {
            return;
        };
        let Some(label) = self.shown(&ty) else {
            return;
        };
        // `is var x` has no `var` of its own to replace with the type.
        let replacement = (var.kind() != SyntaxKind::VarPattern)
            .then(|| TextEdit::new(var.span(), label.clone()));
        hints.push(InlayHint {
            position: name.span().start(),
            label,
            kind: InlayHintKind::Type,
            padding_left: false,
            padding_right: true,
            target: self.type_place(&ty),
            replacement,
        });
    }

    /// The type of the local `name` declares.
    fn local_type(&mut self, at: &SyntaxNode, name: &SyntaxToken) -> Option<Type> {
        let body = self.body_for(at)?;
        let local = match body.symbol_at(name.span()) {
            Some(rustlyn_semantics::BoundSymbol::Local(local)) => body.locals.get(local.0 as usize),
            _ => body.locals.iter().find(|local| local.span == name.span()),
        }?;
        Some(local.ty.clone())
    }

    /// How a type reads in a hint, or `None` when it should not get one:
    /// a type the binder could not work out, or one no code can name.
    fn shown(&self, ty: &Type) -> Option<String> {
        let symbols = self.compilation().symbols();
        if !nameable(symbols, ty) {
            return None;
        }
        Some(ty.display(symbols))
    }

    /// Where the type a hint shows is declared: an array's element type.
    fn type_place(&self, ty: &Type) -> Option<Place> {
        let mut ty = ty;
        while let Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) = ty {
            ty = element;
        }
        match ty {
            Type::Named { symbol, .. } | Type::TypeParameter(symbol) => self.place_of(*symbol),
            _ => None,
        }
    }
}

/// Whether a type can be written in code: not an error, not `null`, not an
/// anonymous type, and nothing inside it either.
fn nameable(symbols: &rustlyn_semantics::Symbols, ty: &Type) -> bool {
    match ty {
        Type::Error | Type::Null | Type::Void => false,
        Type::Named {
            symbol,
            type_arguments,
        } => {
            !symbols
                .get(*symbol)
                .as_named_type()
                .is_some_and(|named| named.anonymous)
                && type_arguments
                    .iter()
                    .all(|argument| nameable(symbols, argument))
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            nameable(symbols, element)
        }
        Type::Tuple(elements) => elements
            .iter()
            .all(|element| nameable(symbols, &element.ty)),
        Type::FunctionPointer(pointer) => pointer.types().all(|ty| nameable(symbols, ty)),
        Type::TypeParameter(_) | Type::Dynamic => true,
    }
}

fn is_var(node: &SyntaxNode) -> bool {
    node.kind() == SyntaxKind::IdentifierName && node.text().trim() == "var"
}

fn is_constructor(view: &View<'_>, symbol: SymbolId) -> bool {
    view.compilation()
        .symbols()
        .get(symbol)
        .as_method()
        .is_some_and(|method| method.method_kind == MethodKind::Constructor)
}

/// Every node under `node` whose span meets `range`, outermost first.
fn nodes_in(node: &SyntaxNode, range: TextSpan, out: &mut Vec<SyntaxNode>) {
    for child in node.children() {
        let span = child.full_span();
        let meets = span.start() <= range.end() && range.start() <= span.end();
        if meets {
            out.push(child.clone());
            nodes_in(&child, range, out);
        }
    }
}

/// The identifier that names what an expression or a type refers to.
fn name_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => {
            node.child_token_of_kind(SyntaxKind::IdentifierToken)
        }
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::MemberBindingExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName => name_token(&node.children().last()?),
        _ => None,
    }
}

/// Roslyn's classification of an argument: a literal (a signed one too), a
/// `new`, or anything else. A cast is what it casts.
fn argument_kind(expression: &SyntaxNode) -> ArgumentKind {
    match expression.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::Utf8StringLiteralExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression
        | SyntaxKind::DefaultLiteralExpression
        | SyntaxKind::InterpolatedStringExpression => ArgumentKind::Literal,
        SyntaxKind::ObjectCreationExpression | SyntaxKind::ImplicitObjectCreationExpression => {
            ArgumentKind::ObjectCreation
        }
        SyntaxKind::CastExpression | SyntaxKind::ParenthesizedExpression => expression
            .children()
            .last()
            .map_or(ArgumentKind::Other, |inner| argument_kind(&inner)),
        SyntaxKind::UnaryMinusExpression | SyntaxKind::UnaryPlusExpression => {
            match expression
                .children()
                .next()
                .map(|inner| argument_kind(&inner))
            {
                Some(ArgumentKind::Literal) => ArgumentKind::Literal,
                _ => ArgumentKind::Other,
            }
        }
        _ => ArgumentKind::Other,
    }
}

/// The name an argument is written as: `path` for `path`, `this.path` and
/// `options.path`.
fn argument_name(expression: &SyntaxNode) -> Option<String> {
    match expression.kind() {
        SyntaxKind::IdentifierName
        | SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::MemberBindingExpression
        | SyntaxKind::ConditionalAccessExpression => {
            let last = expression
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .last()?;
            Some(last.value_text().to_string())
        }
        _ => None,
    }
}

/// Whether the argument's name already says the parameter's: the same
/// word, or one that ends with it (`configPath` for `path`).
fn matches_argument_name(argument: &str, parameter: &str) -> bool {
    let argument = argument.trim_start_matches('_').to_lowercase();
    let parameter = parameter.to_lowercase();
    !parameter.is_empty() && argument.ends_with(&parameter)
}

/// Roslyn's method-intent check: `SetColor(color)`, `FromResult(result)`,
/// `EnableLogging(true)` say with the method's name what the parameter is.
fn matches_method_intent(method: &str, parameter: &str) -> bool {
    if method.starts_with("Enable") || method.starts_with("Disable") {
        return true;
    }
    let suffix = method
        .strip_prefix("Set")
        .or_else(|| method.strip_prefix("From"));
    let Some(suffix) = suffix else {
        return false;
    };
    let mut suffix_chars = suffix.chars();
    let mut parameter_chars = parameter.chars();
    match (suffix_chars.next(), parameter_chars.next()) {
        (Some(a), Some(b)) => {
            a.to_lowercase().eq(b.to_lowercase())
                && suffix_chars.as_str() == parameter_chars.as_str()
        }
        _ => false,
    }
}

/// Roslyn's check that parameters differ only by a suffix: every name the
/// same prefix and then a number (`value1`, `value2`), or the same prefix
/// and then one capital letter (`pointA`, `pointB`).
fn differ_only_by_suffix(names: &[&str]) -> bool {
    if names.len() < 2 {
        return false;
    }
    let numeric = |name: &str| -> Option<String> {
        let digits = name.chars().rev().take_while(char::is_ascii_digit).count();
        (digits > 0 && digits < name.len()).then(|| name[..name.len() - digits].to_string())
    };
    let alpha = |name: &str| -> Option<String> {
        let chars: Vec<char> = name.chars().collect();
        let n = chars.len();
        (n >= 2 && chars[n - 1].is_ascii_uppercase() && !chars[n - 2].is_ascii_uppercase())
            .then(|| chars[..n - 1].iter().collect())
    };
    let same = |suffix: &dyn Fn(&str) -> Option<String>| {
        let prefixes: Option<Vec<String>> = names.iter().map(|name| suffix(name)).collect();
        prefixes.is_some_and(|prefixes| prefixes.windows(2).all(|pair| pair[0] == pair[1]))
    };
    same(&numeric) || same(&alpha)
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::tests::{at, compile};
    use super::*;

    /// Every hint of the file, as `label@text after it`.
    fn hints_of(text: &str, options: &InlayHintOptions) -> Vec<String> {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let range = TextSpan::from_bounds(0, text.len() as u32);
        semantic
            .inlay_hints(Path::new("/p/C.cs"), range, None, options)
            .expect("hints")
            .iter()
            .map(|hint| {
                let after: String = text[hint.position as usize..]
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '"' || *c == '-')
                    .collect();
                format!("{}@{after}", hint.label)
            })
            .collect()
    }

    fn defaults(text: &str) -> Vec<String> {
        hints_of(text, &InlayHintOptions::default())
    }

    #[test]
    fn literals_and_new_get_their_parameter_names() {
        let text = "class Item { public Item(int weight) { } }\n\
                    class Shop {\n\
                      void Stock(Item item, int count, bool fragile, string label) { }\n\
                      void Run(int n) {\n\
                        Stock(new Item(3), 10, true, \"box\");\n\
                        Stock(new Item(-1), n, fragile: false, null);\n\
                      }\n\
                    }\n";
        let found = defaults(text);
        assert_eq!(
            found,
            vec![
                "item:@new",
                "weight:@3",
                "count:@10",
                "fragile:@true",
                "label:@\"box\"",
                "item:@new",
                "weight:@-1",
                "label:@null",
            ],
            "{found:?}"
        );
    }

    #[test]
    fn other_arguments_only_when_asked() {
        let text = "class C {\n  void Move(int dx, int speed) { }\n  int speed = 1;\n  void Run(int step) { Move(step, this.speed); }\n}\n";
        assert!(defaults(text).is_empty(), "{:?}", defaults(text));
        let everything = InlayHintOptions {
            for_other_parameters: true,
            ..InlayHintOptions::default()
        };
        // `this.speed` is named like the parameter.
        assert_eq!(hints_of(text, &everything), vec!["dx:@step"]);
        let unsuppressed = InlayHintOptions {
            for_other_parameters: true,
            suppress_for_parameters_that_match_argument_name: false,
            ..InlayHintOptions::default()
        };
        assert_eq!(
            hints_of(text, &unsuppressed),
            vec!["dx:@step", "speed:@this"]
        );
    }

    #[test]
    fn what_the_code_already_says_gets_no_hint() {
        let text = "class C {\n\
                      static int Max(int value1, int value2) => value1;\n\
                      static int Lerp(int pointA, int pointB) => pointA;\n\
                      void SetColor(int color) { }\n\
                      void EnableLogging(bool on) { }\n\
                      static C FromResult(int result) => null;\n\
                      void Load(string path) { }\n\
                      string path;\n\
                      void Run(string configPath) {\n\
                        Max(1, 2); Lerp(1, 2); SetColor(3); EnableLogging(true); FromResult(4);\n\
                        Load(configPath); Load(this.path); Load(\"a\");\n\
                      }\n\
                    }\n";
        let everything = InlayHintOptions {
            for_other_parameters: true,
            ..InlayHintOptions::default()
        };
        assert_eq!(hints_of(text, &everything), vec!["path:@\"a\""]);
        let nothing_suppressed = InlayHintOptions {
            suppress_for_parameters_that_differ_only_by_suffix: false,
            suppress_for_parameters_that_match_method_intent: false,
            ..InlayHintOptions::default()
        };
        let found = hints_of(text, &nothing_suppressed);
        for expected in [
            "value1:@1",
            "pointB:@2",
            "color:@3",
            "on:@true",
            "result:@4",
        ] {
            assert!(
                found.contains(&expected.to_string()),
                "{expected} in {found:?}"
            );
        }
    }

    #[test]
    fn indexers_constructors_initializers_delegates_and_extensions() {
        let text = "using System;\nusing System.Collections.Generic;\n\
                    static class Ext { public static int Twice(this int value, int times) => value; }\n\
                    class Grid { public int this[int row, int column] { get { return 0; } } }\n\
                    class Base { protected Base(string name) { } }\n\
                    class C : Base {\n\
                      C() : base(\"root\") { }\n\
                      void Run(Grid grid, Func<int, int> twice) {\n\
                        var cell = grid[1, 2];\n\
                        var list = new List<int>();\n\
                        list.Add(5);\n\
                        twice(7);\n\
                        var x = 3.Twice(2);\n\
                        C made = new(); Base other = new(\"leaf\");\n\
                      }\n\
                    }\n";
        let options = InlayHintOptions {
            types: false,
            ..InlayHintOptions::default()
        };
        let found = hints_of(text, &options);
        assert_eq!(
            found,
            vec![
                "name:@\"root\"",
                "row:@1",
                "column:@2",
                "item:@5",
                "arg:@7",
                "times:@2",
                "name:@\"leaf\"",
            ],
            "{found:?}"
        );
        let no_indexers = InlayHintOptions {
            types: false,
            for_indexer_parameters: false,
            ..InlayHintOptions::default()
        };
        assert!(!hints_of(text, &no_indexers).contains(&"row:@1".to_string()));
    }

    #[test]
    fn attribute_arguments_are_hinted_by_position() {
        let text = "class RangeAttribute : System.Attribute { public RangeAttribute(int min, int max) { } public int Step; }\n\
                    class C { [Range(1, 10, Step = 2)] int level; }\n";
        assert_eq!(defaults(text), vec!["min:@1", "max:@10"]);
    }

    #[test]
    fn var_foreach_out_deconstruction_lambdas_and_new() {
        let text = "using System;\nusing System.Collections.Generic;\n\
                    class Point { }\n\
                    class C {\n\
                      void Run(List<string> names) {\n\
                        var count = 3;\n\
                        foreach (var name in names) { }\n\
                        int.TryParse(\"1\", out var parsed);\n\
                        var (a, b) = (1, \"x\");\n\
                        Func<int, bool> even = n => n > 0;\n\
                        Func<int, string, int> pick = (i, s) => i;\n\
                        Point p = new();\n\
                        object o = count; if (o is var any) { }\n\
                        var q = new Point(), r = new Point();\n\
                      }\n\
                    }\n";
        let options = InlayHintOptions {
            parameters: false,
            ..InlayHintOptions::default()
        };
        let found = hints_of(text, &options);
        assert_eq!(
            found,
            vec![
                "int@count",
                "string@name",
                "int@parsed",
                "int@a",
                "string@b",
                "int@n",
                "int@i",
                "string@s",
                "Point@",
                "object@any",
            ],
            "{found:?}"
        );
    }

    #[test]
    fn a_hint_knows_where_it_leads_and_what_it_would_write() {
        let text = "class Point { }\nclass C { void Run() { var p = new Point(); Take(5); }\n  void Take(int amount) { } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let range = TextSpan::from_bounds(0, text.len() as u32);
        let hints = semantic
            .inlay_hints(
                Path::new("/p/C.cs"),
                range,
                None,
                &InlayHintOptions::default(),
            )
            .expect("hints");
        assert_eq!(hints.len(), 2, "{hints:?}");
        let ty = &hints[0];
        assert_eq!(ty.kind, InlayHintKind::Type);
        assert_eq!(ty.position, at(text, "p =", 0));
        assert!(ty.padding_right && !ty.padding_left);
        assert_eq!(
            ty.target,
            Some(Place::Source {
                path: "/p/C.cs".into(),
                span: TextSpan::new(at(text, "Point", 0), 5),
            })
        );
        let replaced = crate::edit::apply(text, &[ty.replacement.clone().unwrap()]);
        assert!(replaced.contains("Point p = new Point()"), "{replaced}");

        let parameter = &hints[1];
        assert_eq!(parameter.kind, InlayHintKind::Parameter);
        assert_eq!(parameter.label, "amount:");
        assert_eq!(
            parameter.target,
            Some(Place::Source {
                path: "/p/C.cs".into(),
                span: TextSpan::new(at(text, "amount", 0), 6),
            })
        );
        let named = crate::edit::apply(text, &[parameter.replacement.clone().unwrap()]);
        assert!(named.contains("Take(amount: 5)"), "{named}");
    }

    #[test]
    fn only_the_range_asked_for_is_hinted() {
        let text = "class C {\n  void A() { var x = 1; }\n  void B() { var y = 2; }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let start = at(text, "void B", 0);
        let range = TextSpan::from_bounds(start, text.len() as u32);
        let hints = semantic
            .inlay_hints(
                Path::new("/p/C.cs"),
                range,
                None,
                &InlayHintOptions::default(),
            )
            .expect("hints");
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].position, at(text, "y =", 0));
    }

    #[test]
    fn unsaved_text_is_hinted_as_typed() {
        let compiled = "class C { void Take(int amount) { } void Run() { } }\n";
        let semantic = compile(&[("C.cs", compiled)], false).expect("compiled");
        let typed =
            "class C { void Take(int amount) { } void Run() { var s = \"a\"; Take(2); } }\n";
        let hints = semantic
            .inlay_hints(
                Path::new("/p/C.cs"),
                TextSpan::from_bounds(0, typed.len() as u32),
                Some(typed),
                &InlayHintOptions::default(),
            )
            .expect("hints");
        let labels: Vec<(&str, u32)> = hints
            .iter()
            .map(|hint| (hint.label.as_str(), hint.position))
            .collect();
        assert_eq!(
            labels,
            vec![
                ("string", at(typed, "s =", 0)),
                ("amount:", at(typed, "2)", 0))
            ]
        );
        assert_eq!(
            hints[1].target,
            Some(Place::Source {
                path: "/p/C.cs".into(),
                span: TextSpan::new(at(typed, "amount", 0), 6),
            })
        );
    }

    #[test]
    fn suffix_and_intent_rules() {
        assert!(differ_only_by_suffix(&["value1", "value2"]));
        assert!(differ_only_by_suffix(&["pointA", "pointB"]));
        assert!(!differ_only_by_suffix(&["x", "y"]));
        assert!(!differ_only_by_suffix(&["value1"]));
        assert!(!differ_only_by_suffix(&["value1", "other2"]));
        assert!(!differ_only_by_suffix(&["ID", "IP"]));
        assert!(matches_method_intent("SetColor", "color"));
        assert!(matches_method_intent("FromResult", "result"));
        assert!(!matches_method_intent("SetColor", "value"));
        assert!(!matches_method_intent("Paint", "color"));
        assert!(matches_argument_name("_path", "path"));
        assert!(matches_argument_name("configPath", "path"));
        assert!(!matches_argument_name("pathway", "path"));
    }
}
