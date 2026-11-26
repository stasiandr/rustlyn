//! Binding member bodies: attributes, constructors and their initializers,
//! expression-bodied members, and the parameters in scope.

use std::collections::HashMap;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, Evidence, identifier_text};
use crate::binder::{Binder, Diagnostics};
use crate::bound::{
    BoundAttribute, BoundBody, BoundExpression, BoundExpressionKind, BoundStatement,
    BoundStatementKind, BoundSymbol,
};
use crate::symbol::{SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl<'a> BodyBinder<'a> {
    /// Binds the body of the member declared by `declaration`.
    #[must_use]
    /// Binds one expression written inside `declaration`, in that member's
    /// scope: the `N` of `fixed byte Buffer[N]`.
    /// Binds an attribute written on a declaration (§22.3): `[Obsolete("x",
    /// Error = true)]` is the `ObsoleteAttribute(string)` constructor, its
    /// argument, and a property set by name.
    ///
    /// The attribute class is looked up with `Attribute` appended first and
    /// as written second, in the scope of the declaration it is on.
    pub fn bind_attribute(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
        attribute: &SyntaxNode,
    ) -> Option<BoundAttribute> {
        Self::bind_attribute_diagnosed(binder, tree, declaration, attribute).0
    }

    /// [`bind_attribute`](Self::bind_attribute), with what binding its
    /// arguments found wrong: a name that does not exist, an argument that
    /// does not convert.
    pub fn bind_attribute_diagnosed(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
        attribute: &SyntaxNode,
    ) -> (Option<BoundAttribute>, Diagnostics) {
        let context = binder.context_at(tree, declaration);
        // An attribute is bound in the member it is on, as Roslyn's
        // attribute binder is: a parameter's in its method, and a field's in
        // its type — so `[CallerMemberName]` there is the method's name, and
        // nothing at all on a field.
        let member = binder.declared_symbol_at(tree, declaration).map(|symbol| {
            let symbols = binder.compilation().symbols();
            match symbols.get(symbol).kind {
                SymbolKind::Parameter | SymbolKind::Field => {
                    symbols.get(symbol).container.unwrap_or(symbol)
                }
                _ => symbol,
            }
        });
        let mut body_binder = Self::new(binder, tree, context, member, false);
        body_binder.in_attribute = true;
        let bound = body_binder.bind_attribute_node(attribute);
        (bound, std::mem::take(&mut body_binder.body.diagnostics))
    }

    /// The arguments of an attribute bound as a body of their own, for an
    /// editor to ask what a name in them is: `MethodImplOptions` in
    /// `[MethodImpl(MethodImplOptions.AggressiveInlining)]`.
    pub fn bind_attribute_for_editor(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
        attribute: &SyntaxNode,
    ) -> BoundBody {
        let context = binder.context_at(tree, declaration);
        let member = binder.declared_symbol_at(tree, declaration);
        let mut body_binder = Self::new(binder, tree, context, member, false);
        body_binder.in_attribute = true;
        body_binder.bind_attribute_node(attribute);
        body_binder.body
    }

    /// A parameter's default value bound as a body of its own, for an
    /// editor to ask what a name in it is: `uint.MaxValue` in `uint state =
    /// uint.MaxValue`. It is bound in the member the parameter is of.
    pub fn bind_default_for_editor(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
        value: &SyntaxNode,
    ) -> BoundBody {
        let context = binder.context_at(tree, declaration);
        let member = binder.declared_symbol_at(tree, declaration);
        let mut body_binder = Self::new(binder, tree, context, member, false);
        body_binder.bind_expression(value);
        body_binder.body
    }

    fn bind_attribute_node(&mut self, attribute: &SyntaxNode) -> Option<BoundAttribute> {
        let span = attribute.span();
        let name = attribute
            .children()
            .find(|child| child.kind().is_type_node())?;
        let ty = self.attribute_type(&name);
        let symbol = ty.symbol();

        let mut positional = Vec::new();
        let mut names: Vec<Option<String>> = Vec::new();
        let mut named = Vec::new();
        for argument in attribute
            .child_of_kind(SyntaxKind::AttributeArgumentList)
            .into_iter()
            .flat_map(|list| list.children())
            .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
        {
            let Some(expression) = argument
                .children()
                .filter(|child| child.kind().is_expression())
                .last()
            else {
                continue;
            };
            // `[My(q: 1, p: 2)]` names the constructor's parameters, the way
            // a call does.
            if let Some(colon) = argument.child_of_kind(SyntaxKind::NameColon) {
                names.push(
                    colon
                        .child_tokens()
                        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                        .map(|token| token.value_text().to_string()),
                );
                positional.push(self.bind_expression(&expression));
                continue;
            }
            // `Error = true` names a field or property of the attribute
            // class and sets it once the object is made.
            if let Some(equals) = argument.child_of_kind(SyntaxKind::NameEquals) {
                // The name is a token of the `NameEquals`, not a name node.
                let member_name = equals.text();
                let member_name = member_name.trim().trim_end_matches('=').trim().to_string();
                let member = Some(member_name)
                    .filter(|name| !name.is_empty())
                    .zip(symbol)
                    .and_then(|(member_name, symbol)| {
                        self.binder
                            .lookup_member(symbol, &member_name)
                            .into_iter()
                            .find(|candidate| {
                                matches!(
                                    self.kind_of(*candidate),
                                    SymbolKind::Field | SymbolKind::Property
                                )
                            })
                    });
                let value = self.bind_expression(&expression);
                if let Some(member) = member {
                    let member_type = self.member_type(member, &ty);
                    let value = self.convert(value, &member_type);
                    named.push((member, value));
                }
                continue;
            }
            names.push(None);
            positional.push(self.bind_expression(&expression));
        }

        let candidates: Vec<SymbolId> = symbol
            .map(|symbol| {
                self.binder
                    .compilation()
                    .symbols()
                    .lookup(symbol, ".ctor")
                    .to_vec()
            })
            .unwrap_or_default();
        let candidates = self.named_candidates(&candidates, &names);
        let mut positional = self.reorder_named(&candidates, &names, positional, &ty);
        let constructor = if candidates.is_empty() {
            None
        } else {
            self.resolve_with_lambdas(&candidates, &mut positional, &ty, &[], false)
                .map(|resolved| resolved.method)
        };
        let arguments = match constructor {
            Some(constructor) => {
                self.convert_arguments(constructor, positional, &ty, &HashMap::new(), span)
            }
            None => positional,
        };
        Some(BoundAttribute {
            ty,
            constructor,
            arguments,
            named,
        })
    }

    /// The class an attribute names: `[Obsolete]` is `ObsoleteAttribute`
    /// where there is one and `Obsolete` otherwise (§22.2).
    fn attribute_type(&mut self, name: &SyntaxNode) -> Type {
        let symbols = self.binder.compilation().symbols();
        let is_type = |candidate: SymbolId| symbols.get(candidate).kind == SymbolKind::NamedType;
        let (container, last) = match name.kind() {
            SyntaxKind::IdentifierName => match identifier_text(name) {
                Some(text) => (None, text),
                None => return Type::Error,
            },
            SyntaxKind::QualifiedName => {
                let mut children = name.children();
                let (Some(left), Some(right)) = (children.next(), children.next()) else {
                    return Type::Error;
                };
                let container = self.binder.resolve_namespace_or_type(&left, &self.context);
                match (container, identifier_text(&right)) {
                    (Some(container), Some(text)) => (Some(container), text),
                    _ => return self.resolve(name),
                }
            }
            _ => return self.resolve(name),
        };
        for candidate in [format!("{last}Attribute"), last] {
            let found = match container {
                Some(container) => symbols
                    .lookup(container, &candidate)
                    .iter()
                    .copied()
                    .find(|found| is_type(*found)),
                None => self
                    .binder
                    .lookup(&candidate, 0, &self.context)
                    .filter(|found| is_type(*found)),
            };
            if let Some(found) = found {
                return Type::named(found);
            }
        }
        Type::Error
    }

    pub fn bind_lone_expression(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
        expression: &SyntaxNode,
    ) -> BoundExpression {
        let context = binder.context_at(tree, declaration);
        let member = binder.declared_symbol_at(tree, declaration);
        let mut body_binder = Self::new(binder, tree, context, member, false);
        body_binder.bind_expression(expression)
    }

    pub fn bind_member(binder: &'a Binder<'a>, tree: usize, declaration: &SyntaxNode) -> BoundBody {
        Self::bind_member_as(binder, tree, declaration, false)
    }

    /// [`Self::bind_member`] for an editor, which asks about code that
    /// does not compile: a lambda no delegate took is bound anyway, its
    /// parameters typed as written or as nothing known.
    pub fn bind_member_for_editor(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
    ) -> BoundBody {
        Self::bind_member_as(binder, tree, declaration, true)
    }

    fn bind_member_as(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
        editor: bool,
    ) -> BoundBody {
        // Top-level statements are declared by the compilation unit itself,
        // and a file holding one statement and nothing else spans exactly
        // what that statement spans: the unit is the declaration wanted.
        let root = binder.tree_root(tree);
        let declaration = match root {
            Some(root)
                if declaration.kind() != SyntaxKind::CompilationUnit
                    && root.span() == declaration.span()
                    && root
                        .children()
                        .any(|child| child.kind() == SyntaxKind::GlobalStatement) =>
            {
                root
            }
            _ => declaration.clone(),
        };
        let declaration = &declaration;
        let context = binder.context_at(tree, declaration);
        let member = binder.declared_symbol_at(tree, declaration);
        // A primary constructor is declared by its parameter list, and what
        // it does is written beside it: `class Scope(DiagnosticAnalyzer
        // analyzer) : Base(analyzer)` chains to the base with `analyzer`.
        let primary_base = (declaration.kind() == SyntaxKind::ParameterList)
            .then(|| declaration.parent())
            .flatten()
            .and_then(|owner| owner.child_of_kind(SyntaxKind::BaseList))
            .and_then(|list| {
                list.children()
                    .find(|base| base.kind() == SyntaxKind::PrimaryConstructorBaseType)
            })
            .filter(|base| base.child_of_kind(SyntaxKind::ArgumentList).is_some());
        let in_initializer = declaration
            .child_of_kind(SyntaxKind::EqualsValueClause)
            .is_some()
            && matches!(
                declaration.kind(),
                SyntaxKind::VariableDeclarator | SyntaxKind::PropertyDeclaration
            );

        let mut body_binder = Self::new(binder, tree, context, member, in_initializer);
        body_binder.recover_lambdas = editor;
        body_binder.declare_parameters();

        let mut statements = Vec::new();
        // A file of top-level statements is one body: its statements are
        // bound as a run, the way a block's are, so that a `using`
        // declaration covers the rest and a local function further down is
        // in scope further up.
        let global: Vec<SyntaxNode> = declaration
            .children()
            .filter(|child| child.kind() == SyntaxKind::GlobalStatement)
            .filter_map(|child| child.children().next())
            .collect();
        if !global.is_empty() {
            statements.extend(body_binder.bind_statement_list(&global));
        }
        for child in declaration.children() {
            match child.kind() {
                SyntaxKind::Block => statements.push(body_binder.bind_block(&child)),
                SyntaxKind::ArrowExpressionClause => {
                    if let Some(expression) = child.children().next() {
                        // `=> e` is `{ return e; }`, and a void member's is
                        // `{ e; }`. Which one it is depends on the member's
                        // return type, which the check below already knows.
                        let value = body_binder.bind_expression(&expression);
                        statements.push(body_binder.arrow_body(&expression, value));
                    }
                }
                SyntaxKind::EqualsValueClause => {
                    if let Some(expression) = child.children().next() {
                        let declared = member.map(|member| {
                            let mut sink = Diagnostics::new();
                            binder.type_of(member, &mut sink).value().clone()
                        });
                        // `byte[] table = { 0x00, 0x01 }` writes no type
                        // beside the braces: the declaration's is the one.
                        let value = match &declared {
                            Some(declared)
                                if expression.kind() == SyntaxKind::ArrayInitializerExpression
                                    && matches!(declared, Type::Array { .. }) =>
                            {
                                body_binder.bind_array_creation_as(&expression, Some(declared))
                            }
                            _ => body_binder.bind_expression(&expression),
                        };
                        // An initializer is an assignment, and the member's
                        // declared type is what it assigns to:
                        // `Func<int, int> f = x => x * 2;` is where that
                        // lambda gets a type, and without it it has none.
                        // And it converts only where an assignment would: `int
                        // count = "many";` is CS0029, as a local's is.
                        let value = match &declared {
                            Some(declared) => {
                                body_binder.check_assignable(&expression, &value, declared);
                                body_binder.convert(value, declared)
                            }
                            None => value,
                        };
                        statements.push(BoundStatement::new(
                            BoundStatementKind::Return(Some(value)),
                            child.span(),
                        ));
                    }
                }
                SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer => {
                    statements.push(body_binder.bind_constructor_initializer(&child));
                }
                _ => {}
            }
        }
        if let Some(base) = primary_base {
            statements.push(body_binder.bind_constructor_initializer(&base));
        }

        // A constructor that wrote no `: base(...)` still runs one, and the
        // base may take arguments it fills itself. That call is made here,
        // where the defaults can be read; where the base takes none there is
        // nothing to say, and a backend writes it without being told.
        if !statements.iter().any(|statement| {
            matches!(
                statement.kind,
                BoundStatementKind::ConstructorInitializer { .. }
            )
        }) && let Some(initializer) = body_binder.synthesize_base_initializer(declaration.span())
        {
            statements.insert(0, initializer);
        }

        body_binder.body.statements = statements;
        body_binder.lower_interpolated_strings();
        body_binder.propagate_local_function_captures();
        crate::flow::check(binder, tree, declaration, member, &mut body_binder.body);
        crate::obsolete::check(binder, tree, declaration, member, &mut body_binder.body);
        body_binder.body
    }

    /// The `: base(...)` the constructor nobody wrote for a type would need:
    /// `class Finder : Walker` with no constructor of its own still chains to
    /// `Walker(int depth = 3)`, and has to pass the 3.
    ///
    /// `None` where the base's constructor takes nothing, and so needs
    /// nothing said.
    #[must_use]
    pub fn implicit_base_initializer(
        binder: &'a Binder<'a>,
        tree: usize,
        declaration: &SyntaxNode,
    ) -> Option<BoundStatement> {
        let context = binder.context_at(tree, declaration);
        let mut body_binder = Self::new(binder, tree, context, None, false);
        body_binder.base_initializer_of(declaration.span())
    }

    /// The `: base(...)` a constructor did not write, where the base takes
    /// arguments that it fills.
    ///
    /// `ErrorTypeSymbol(TupleExtraData? tupleData = null)` is one of those:
    /// nothing may chain to it without passing something, and what to pass is
    /// written on the parameter.
    fn synthesize_base_initializer(&mut self, span: TextSpan) -> Option<BoundStatement> {
        let member = self.member?;
        let symbols = self.binder.compilation().symbols();
        if symbols
            .get(member)
            .as_method()
            .map(|detail| detail.method_kind)
            != Some(crate::symbol::MethodKind::Constructor)
        {
            return None;
        }
        self.base_initializer_of(span)
    }

    fn base_initializer_of(&mut self, span: TextSpan) -> Option<BoundStatement> {
        let symbols = self.binder.compilation().symbols();
        let enclosing = self.context.enclosing_type()?;
        if !self.binder.self_type(enclosing).is_reference_type(symbols) {
            return None;
        }
        let base = self.binder.base_class_of(enclosing)?;
        let candidates = symbols.lookup(base.symbol()?, ".ctor").to_vec();
        let constructor = self.resolve_overload(&candidates, &[], &Evidence::default(), &base)?;
        // One that takes nothing needs nothing said about it.
        let takes = self
            .binder
            .compilation()
            .symbols()
            .get(constructor)
            .as_method()
            .map(|detail| detail.parameters.len())
            .unwrap_or_default();
        if takes == 0 {
            return None;
        }
        let outer = std::mem::replace(&mut self.implicit_call, true);
        let arguments =
            self.convert_arguments(constructor, Vec::new(), &base, &HashMap::new(), span);
        self.implicit_call = outer;
        Some(BoundStatement::new(
            BoundStatementKind::ConstructorInitializer {
                constructor: Some(constructor),
                arguments,
                chains_to_this: false,
            },
            span,
        ))
    }

    /// `: base(x)` and `: this(x)`, which pick a constructor the way any
    /// other call does.
    /// Whether `S()` written with nothing in it is the constructor every
    /// struct has without writing one.
    ///
    /// A `params` constructor is applicable to no arguments too, in its
    /// expanded form — but §12.6.4.5 prefers a candidate applicable as
    /// written, and the implicit one is. `SyntaxNodeOrTokenList(params
    /// SyntaxNodeOrToken[])` chaining to `this()` would otherwise be the
    /// constructor calling itself with an empty array.
    pub(super) fn implicit_struct_constructor(&self, ty: &Type, candidates: &[SymbolId]) -> bool {
        let symbols = self.binder.compilation().symbols();
        !ty.is_reference_type(symbols)
            && !matches!(ty, Type::TypeParameter(_))
            && ty.symbol().is_some()
            && !candidates.iter().any(|candidate| {
                symbols
                    .get(*candidate)
                    .as_method()
                    .is_some_and(|detail| detail.parameters.is_empty())
            })
    }

    fn bind_constructor_initializer(&mut self, node: &SyntaxNode) -> BoundStatement {
        let chains_to_this = node.kind() == SyntaxKind::ThisConstructorInitializer;
        let list = node.child_of_kind(SyntaxKind::ArgumentList);
        let arguments = list
            .as_ref()
            .map(|list| self.bind_argument_list(list))
            .unwrap_or_default();

        let enclosing = self.context.enclosing_type();
        // The base is a construction rather than a bare name: `Embedded :
        // Manager.CommonEmbedded` chains to a constructor whose parameter is
        // an adapter, not the `TSymbol` the declaration spells.
        let target: Option<Type> = if chains_to_this {
            enclosing.map(|symbol| self.binder.self_type(symbol))
        } else {
            enclosing.and_then(|symbol| self.binder.base_class_of(symbol))
        };
        let candidates: Vec<SymbolId> = target
            .as_ref()
            .and_then(Type::symbol)
            .map(|symbol| {
                self.binder
                    .compilation()
                    .symbols()
                    .lookup(symbol, ".ctor")
                    .to_vec()
            })
            .unwrap_or_default();
        // `: base(checksumAlgorithm: text.ChecksumAlgorithm)` names the
        // parameter it fills, exactly as any other call may.
        let names = list.as_ref().map(Self::argument_names).unwrap_or_default();
        let arguments = self.reorder_named(
            &candidates,
            &names,
            arguments,
            target.as_ref().unwrap_or(&Type::Error),
        );
        let argument_types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();
        let mut arguments = arguments;
        let written_arguments =
            (candidates.len() > 1 && names.iter().all(Option::is_none)).then(|| arguments.clone());

        let constructor = target
            .clone()
            .filter(|receiver| {
                !(arguments.is_empty() && self.implicit_struct_constructor(receiver, &candidates))
            })
            .and_then(|receiver| {
                self.resolve_with_lambdas(&candidates, &mut arguments, &receiver, &[], false)
                    .map(|resolved| resolved.method)
            });
        if let (Some(constructor), Some(receiver), Some(written)) =
            (constructor, target.as_ref(), &written_arguments)
        {
            // Blamed on the keyword, as an unusable call is.
            let keyword = node
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword
                    )
                })
                .map_or(node.span(), |token| token.span());
            self.report_if_ambiguous(
                constructor,
                &candidates,
                written,
                receiver,
                &[],
                false,
                keyword,
            );
        }
        let arguments = match (constructor, target.as_ref()) {
            (Some(constructor), Some(receiver)) => self.convert_arguments(
                constructor,
                arguments,
                receiver,
                &HashMap::new(),
                node.span(),
            ),
            _ => arguments,
        };
        // Every struct has a parameterless constructor nobody wrote: `: this()`
        // means the fields start at zero, and there is no row to resolve.
        let implicit = arguments.is_empty()
            && target
                .as_ref()
                .is_some_and(|ty| !ty.is_reference_type(self.binder.compilation().symbols()));
        if constructor.is_none()
            && let Some(receiver) = target.as_ref()
            && !implicit
            && !argument_types.iter().any(Type::is_error)
        {
            // `: base(...)` and `: this(...)` are blamed on the keyword.
            let keyword = node
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword
                    )
                })
                .map_or(node.span(), |token| token.span());
            let spans: Vec<TextSpan> = arguments.iter().map(|argument| argument.span).collect();
            self.report_no_overload(
                &candidates,
                ".ctor",
                &argument_types,
                &spans,
                receiver,
                &[],
                keyword,
                Some(receiver),
            );
        }
        self.recover_lambdas_in(node);
        BoundStatement::new(
            BoundStatementKind::ConstructorInitializer {
                constructor,
                arguments,
                chains_to_this,
            },
            node.span(),
        )
    }

    /// `=> e` as a statement: a return, unless the member returns `void`.
    pub(super) fn arrow_body(
        &mut self,
        node: &SyntaxNode,
        value: BoundExpression,
    ) -> BoundStatement {
        let expected = self.expected_return();
        let span = node.span();
        if matches!(expected, Type::Void) {
            // `() => () => 1` bound as an `Action` to see what it gives back:
            // the inner lambda is a value of the type it has on its own.
            let value = match value.kind {
                BoundExpressionKind::UnboundLambda(_) | BoundExpressionKind::MethodGroup { .. } => {
                    match self.natural_function_type(&value) {
                        Some(natural) => self.convert(value, &natural),
                        None => value,
                    }
                }
                _ => value,
            };
            BoundStatement::new(BoundStatementKind::Expression(value), span)
        } else {
            self.check_return(node, &value);
            let value = self.convert(value, &expected);
            BoundStatement::new(BoundStatementKind::Return(Some(value)), span)
        }
    }

    /// A parameter of the enclosing member, by name.
    ///
    /// An accessor is a member under its property, and an indexer's arguments
    /// belong to the property rather than to either accessor — so `this[int i]
    /// { get { return i; } }` finds `i` one step up. A setter's `value` is its
    /// own.
    pub(super) fn lookup_parameter(&self, member: SymbolId, name: &str) -> Option<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        // The member's own, then — for a local function — those of every
        // function it is written inside, which it captures.
        let mut current = Some(member);
        while let Some(member) = current {
            if let Some(found) = symbols
                .lookup(member, name)
                .iter()
                .copied()
                .find(|candidate| symbols.get(*candidate).kind == SymbolKind::Parameter)
            {
                return Some(found);
            }
            let container = symbols.get(member).container?;
            if symbols.get(container).kind != SymbolKind::Method {
                break;
            }
            current = Some(container);
        }
        // An accessor's parameters are the indexer's, declared on it rather
        // than on the accessor.
        let container = symbols.get(member).container?;
        if symbols.get(container).kind == SymbolKind::Property
            && let Some(found) = symbols
                .lookup(container, name)
                .iter()
                .copied()
                .find(|candidate| symbols.get(*candidate).kind == SymbolKind::Parameter)
        {
            return Some(found);
        }
        // A primary constructor's parameters are in scope throughout the
        // type (C# 12): `class Scope(DiagnosticAnalyzer analyzer)` writes
        // `Analyzer { get; } = analyzer;` and reads `analyzer` in its methods.
        let mut enclosing = Some(member);
        while let Some(current) = enclosing {
            if symbols.get(current).kind == SymbolKind::NamedType {
                break;
            }
            enclosing = symbols.get(current).container;
        }
        let enclosing = enclosing?;
        let primary = symbols
            .get(enclosing)
            .as_named_type()
            .and_then(|detail| detail.primary_constructor)
            .filter(|primary| *primary != member)?;
        // A record's positional parameter is a property everywhere but in the
        // initializers: `record struct Info(int Offset)` reads `Offset` in its
        // methods as the property it declared (§15.1.1 of the records spec).
        if !self.in_initializer
            && matches!(
                symbols.get(enclosing).type_kind(),
                Some(TypeKind::Record | TypeKind::RecordStruct)
            )
            && symbols
                .lookup(enclosing, name)
                .iter()
                .any(|found| symbols.get(*found).kind != SymbolKind::Parameter)
        {
            return None;
        }
        symbols
            .lookup(primary, name)
            .iter()
            .copied()
            .find(|candidate| symbols.get(*candidate).kind == SymbolKind::Parameter)
    }

    /// The field behind the property whose accessor is being bound, where
    /// the accessor says `field`.
    pub(super) fn backing_field_in_scope(&self) -> Option<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let mut current = self.member;
        while let Some(member) = current {
            if let Some(detail) = symbols.get(member).as_property() {
                return detail.backing_field;
            }
            if symbols.get(member).kind == SymbolKind::NamedType {
                return None;
            }
            current = symbols.get(member).container;
        }
        None
    }

    /// Whether a local found under `name` would be one from outside the local
    /// function being bound, which declares a parameter of that name itself.
    pub(super) fn hidden_by_own_parameter(&self, name: &str) -> bool {
        let Some(frame) = self.lambdas.last() else {
            return false;
        };
        let Some(function) = frame.declares else {
            return false;
        };
        let Some((depth, _)) = self.lookup_local_at(name) else {
            return false;
        };
        let symbols = self.binder.compilation().symbols();
        depth < frame.floor
            && symbols
                .lookup(function, name)
                .iter()
                .any(|candidate| symbols.get(*candidate).kind == SymbolKind::Parameter)
    }

    /// The parameters of the enclosing member are in scope throughout its body,
    /// but they are declared symbols rather than locals.
    fn declare_parameters(&mut self) {
        let Some(member) = self.member else { return };
        let symbols = self.binder.compilation().symbols();
        for id in symbols.get(member).members.clone() {
            if symbols.get(id).kind == SymbolKind::Parameter {
                let span = symbols.get(id).locations.first().map(|l| l.span);
                if let Some(span) = span {
                    self.body.references.insert(span, BoundSymbol::Declared(id));
                }
            }
        }
    }
}
