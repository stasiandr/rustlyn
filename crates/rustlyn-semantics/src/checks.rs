//! What is wrong with the declarations of a file, as opposed to its bodies.
//!
//! Declaring every type and member is one pass that resolves nothing; this is
//! the pass after it, which asks the questions only a finished symbol table
//! can answer. Does every type a signature names exist? Does a class
//! implement what its interfaces promise and what its abstract base leaves
//! open? Does an `override` have something to override, and does a member
//! hide one it did not say it meant to?
//!
//! Every check here would rather say nothing than say something wrong. The
//! compiler is run over Roslyn's own sources and has to find them clean, so
//! where a question turns on a type that did not resolve, or on a base this
//! compiler cannot see all of, the answer is to stay quiet: a missing
//! diagnostic costs a user one squiggle, a false one costs them their trust
//! in all of them.

use std::collections::HashMap;

use rustlyn_diagnostics::{Diagnostic, ErrorCode};
use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};

use crate::binder::{Binder, Diagnostics};
use crate::bound::{BoundExpression, BoundExpressionKind, ConstantValue};
use crate::compilation::Compilation;
use crate::symbol::{
    Accessibility, Detail, Location, MethodKind, Modifiers, RefKind, SymbolId, SymbolKind,
    TypeKind, TypeSyntaxRef,
};
use crate::types::Type;

/// What the type parameters of a type mean in the type a question is asked
/// from: `B<T>` seen from `class D : B<int>` has `T` standing for `int`.
type Frame = HashMap<SymbolId, Type>;

impl Compilation {
    /// What the declarations of one file get wrong: the types their
    /// signatures, base lists, constraints and attributes name that do not
    /// exist, and what the members of its types get wrong against each other
    /// and against what they inherit.
    ///
    /// Syntax errors and the duplicate types the declaration pass itself
    /// found are in [`Compilation::diagnostics`], and what the bodies say is
    /// in [`SemanticModel::body_diagnostics`](crate::SemanticModel::body_diagnostics).
    #[must_use]
    pub fn declaration_diagnostics(&self, tree: usize) -> Vec<Diagnostic> {
        self.check_declarations(Some(tree))
            .into_iter()
            .filter(|(at, _)| *at == tree)
            .map(|(_, diagnostic)| diagnostic)
            .collect()
    }

    /// [`Compilation::declaration_diagnostics`] for every file at once,
    /// which walks the symbol table once rather than once a file.
    pub(crate) fn check_declarations(&self, tree: Option<usize>) -> Diagnostics {
        let mut checker = Checker {
            compilation: self,
            binder: Binder::new(self),
            tree,
            found: Vec::new(),
        };
        checker.signatures();
        checker.attributes();
        checker.types();
        checker.constants();
        checker.enumerators();
        let trees = match tree {
            Some(tree) => tree..tree + 1,
            None => self.corlib_trees..self.trees().len(),
        };
        for tree in trees {
            crate::obsolete::check_declarations(&checker.binder, tree, &mut checker.found);
            crate::warnings::check(&checker.binder, tree, &mut checker.found);
        }
        checker.found
    }
}

struct Checker<'a> {
    compilation: &'a Compilation,
    binder: Binder<'a>,
    /// The file being checked, or `None` for all of them.
    tree: Option<usize>,
    found: Diagnostics,
}

impl Checker<'_> {
    fn covers(&self, tree: usize) -> bool {
        self.tree.is_none_or(|wanted| wanted == tree)
    }

    fn report(&mut self, location: Location, code: ErrorCode, args: &[&str]) {
        self.found
            .push((location.tree, Diagnostic::new(code, location.span, args)));
    }

    // MARK: - types named in signatures

    /// Resolves every type a declaration in the file wrote down, which is
    /// what reports the ones that do not exist.
    fn signatures(&mut self) {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        let mut sink = Diagnostics::new();
        for symbol in symbols.iter() {
            if compilation.is_from_metadata(symbol.id) {
                break;
            }
            match &symbol.detail {
                Detail::NamedType(detail) => {
                    for base in detail
                        .base_types
                        .iter()
                        .filter(|base| self.covers(base.0.tree))
                    {
                        let _ = self.binder.resolve_type_ref(*base, &mut sink);
                    }
                    if let Some(underlying) =
                        detail.enum_underlying.filter(|at| self.covers(at.0.tree))
                    {
                        let _ = self.binder.resolve_type_ref(underlying, &mut sink);
                    }
                }
                Detail::TypeParameter(detail) => {
                    for constraint in detail
                        .constraints
                        .iter()
                        .filter(|at| self.covers(at.0.tree))
                    {
                        // `notnull` and `unmanaged` are spelled like type
                        // names and are not: where nothing of that name is
                        // declared, they are the constraints the language
                        // gives those words.
                        let keyword = self
                            .binder
                            .node_at(constraint.0.tree, constraint.0.span)
                            .is_some_and(|node| {
                                node.kind() == SyntaxKind::IdentifierName
                                    && matches!(node.text().trim(), "notnull" | "unmanaged")
                            });
                        let mut own = Diagnostics::new();
                        let resolved = self.binder.resolve_type_ref(*constraint, &mut own);
                        if !keyword {
                            sink.extend(own);
                        }
                        // `where T : object` says nothing, and `ValueType` and
                        // `Array` are what `struct` and an array type say:
                        // none of them is a constraint (CS0702).
                        let special = resolved.symbol().filter(|symbol| {
                            [
                                compilation.special_type(crate::corlib::SpecialType::Object),
                                compilation.type_by_metadata_name("System.ValueType"),
                                compilation.type_by_metadata_name("System.Array"),
                            ]
                            .contains(&Some(*symbol))
                        });
                        if !keyword
                            && let Some(special) = special
                            && matches!(resolved, Type::Named { .. })
                        {
                            let shown = symbols.qualified_name(special);
                            let shown = match shown.as_str() {
                                "System.Object" => "object".to_string(),
                                _ => shown,
                            };
                            sink.push((
                                constraint.0.tree,
                                Diagnostic::new(
                                    ErrorCode::ErrSpecialTypeAsBound,
                                    constraint.0.span,
                                    &[&shown],
                                ),
                            ));
                        }
                    }
                }
                Detail::Namespace => {}
                Detail::Parameter(detail) => {
                    if symbol
                        .locations
                        .first()
                        .is_some_and(|location| self.covers(location.tree))
                    {
                        let _ = self.binder.type_of(symbol.id, &mut sink);
                        if detail.has_default {
                            self.default_value(symbol.id, &mut sink);
                        }
                    }
                }
                _ => {
                    if symbol
                        .locations
                        .first()
                        .is_some_and(|location| self.covers(location.tree))
                    {
                        let _ = self.binder.type_of(symbol.id, &mut sink);
                    }
                }
            }
        }
        self.found.extend(sink);
    }

    /// CS1736: a parameter's `= value` has to be a constant, a `default`, or
    /// a `new S()` of a struct, which is its default written another way.
    fn default_value(&self, parameter: SymbolId, sink: &mut Diagnostics) {
        let Some((tree, node, expression)) = self.binder.parameter_default_syntax(parameter) else {
            return;
        };
        // `[Optional, DefaultParameterValue(x)]` is an attribute's argument,
        // which is judged as one.
        if node.child_of_kind(SyntaxKind::EqualsValueClause).is_none() {
            return;
        }
        // A `decimal` constant (`= 1.10m`, `= -Limit`) is one, though it is
        // made with `new decimal(...)`: metadata holds it in an attribute.
        if self.binder.special_constant(parameter).is_some() {
            return;
        }
        let value =
            crate::body::BodyBinder::bind_lone_expression(&self.binder, tree, &node, &expression);
        if has_error_part(&value) || self.decimal_constant(&value) || !self.bad_default(&value) {
            return;
        }
        let name = self.compilation.symbols().get(parameter).name.clone();
        sink.push((
            tree,
            Diagnostic::new(
                ErrorCode::ErrDefaultValueMustBeConstant,
                value.span,
                &[&name],
            ),
        ));
    }

    /// Whether a value is a `decimal` constant, perhaps converted — the
    /// `1.1m` of a `decimal? d = 1.1m` — which C# makes with `new
    /// decimal(lo, mid, hi, negative, scale)`.
    fn decimal_constant(&self, value: &BoundExpression) -> bool {
        match &value.kind {
            BoundExpressionKind::Conversion { operand, .. } => self.decimal_constant(operand),
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } => {
                initializers.is_empty()
                    && arguments.len() == 5
                    && self.binder.special_of(&value.ty) == Some(crate::SpecialType::Decimal)
                    && arguments
                        .iter()
                        .all(|argument| self.binder.folded(argument).is_some())
            }
            _ => false,
        }
    }

    /// Whether a default value is plainly no constant.
    fn bad_default(&self, value: &BoundExpression) -> bool {
        let symbols = self.compilation.symbols();
        match &value.kind {
            BoundExpressionKind::Conversion { operand, .. } => self.bad_default(operand),
            BoundExpressionKind::Literal(_) | BoundExpressionKind::Default(_) => false,
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } => {
                !arguments.is_empty()
                    || !initializers.is_empty()
                    || value.ty.symbol().is_none_or(|symbol| {
                        !matches!(
                            symbols.get(symbol).type_kind(),
                            Some(TypeKind::Struct | TypeKind::Enum | TypeKind::RecordStruct)
                        )
                    })
            }
            BoundExpressionKind::Parameter(_) => true,
            _ => self.binder.folded(value).is_none() && !self.could_be_attribute_value(value),
        }
    }

    /// `[Nonesuch]` on a declaration: neither `NonesuchAttribute` nor
    /// `Nonesuch` is a type, and Roslyn says so of both spellings.
    fn attributes(&mut self) {
        let trees = match self.tree {
            Some(tree) => tree..tree + 1,
            None => self.compilation.corlib_trees..self.compilation.trees().len(),
        };
        for tree in trees {
            self.attributes_in(tree);
            self.attribute_targets_in(tree);
            self.pointers_in(tree);
            self.duplicate_modifiers_in(tree);
            self.misplaced_modifiers_in(tree);
        }
    }

    /// CS1004: `public public class C`, said at the second one.
    fn duplicate_modifiers_in(&mut self, tree: usize) {
        let Some(root) = self.binder.tree_root(tree) else {
            return;
        };
        for declaration in root.descendants().filter(|node| {
            matches!(
                node.kind(),
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::StructDeclaration
                    | SyntaxKind::InterfaceDeclaration
                    | SyntaxKind::RecordDeclaration
                    | SyntaxKind::RecordStructDeclaration
                    | SyntaxKind::EnumDeclaration
                    | SyntaxKind::DelegateDeclaration
                    | SyntaxKind::MethodDeclaration
                    | SyntaxKind::ConstructorDeclaration
                    | SyntaxKind::DestructorDeclaration
                    | SyntaxKind::OperatorDeclaration
                    | SyntaxKind::ConversionOperatorDeclaration
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::IndexerDeclaration
                    | SyntaxKind::EventDeclaration
                    | SyntaxKind::EventFieldDeclaration
                    | SyntaxKind::FieldDeclaration
                    | SyntaxKind::GetAccessorDeclaration
                    | SyntaxKind::SetAccessorDeclaration
                    | SyntaxKind::InitAccessorDeclaration
                    | SyntaxKind::AddAccessorDeclaration
                    | SyntaxKind::RemoveAccessorDeclaration
                    | SyntaxKind::LocalFunctionStatement
            )
        }) {
            let mut seen: Vec<String> = Vec::new();
            for token in declaration.child_tokens() {
                let text = token.text().to_string();
                if !MODIFIERS.contains(&text.as_str()) {
                    continue;
                }
                if seen.contains(&text) {
                    self.report(
                        Location::new(tree, token.span()),
                        ErrorCode::ErrDuplicateModifier,
                        &[&text],
                    );
                } else {
                    seen.push(text);
                }
            }
        }
    }

    /// CS0106, CS0112 and CS0267: a modifier the kind of declaration it is
    /// written on cannot have, `static` with one only an instance member can
    /// have, and `partial` anywhere but last.
    ///
    /// What each kind may have is Roslyn's: a method in an interface may be
    /// `static` and `abstract` together, an accessor may be `readonly` only
    /// in a struct, a field may be `const` or `volatile` and nothing else
    /// may, and so on.
    fn misplaced_modifiers_in(&mut self, tree: usize) {
        let Some(root) = self.binder.tree_root(tree) else {
            return;
        };
        for declaration in root.descendants() {
            let Some(rule) = modifier_rule(&declaration) else {
                continue;
            };
            let tokens = modifier_tokens(&declaration);
            if tokens.is_empty() {
                continue;
            }
            let mut written = 0;
            for token in &tokens {
                written |= modifier_flag(token.text());
            }
            // `partial` must come last, and only where it means something;
            // Roslyn's placement check says so and nothing else does.
            if let Some(index) = tokens.iter().position(|token| token.text() == "partial") {
                let last = index + 1 == tokens.len()
                    || (index + 2 == tokens.len() && tokens[index + 1].text() == "async");
                if rule.allowed & modifier::PARTIAL == 0 || !last {
                    self.report(
                        Location::new(tree, tokens[index].span()),
                        ErrorCode::ErrPartialMisplaced,
                        &[],
                    );
                }
            }
            let mut allowed = rule.allowed;
            let mut instance_only = 0;
            if !rule.is_type && written & allowed & modifier::STATIC != 0 {
                instance_only = allowed
                    & if rule.in_interface {
                        modifier::OVERRIDE
                    } else {
                        modifier::ABSTRACT | modifier::OVERRIDE | modifier::VIRTUAL
                    };
                allowed &= !instance_only;
            }
            let wrong = written & !allowed & !modifier::PARTIAL;
            for (flag, text) in modifier::ORDER {
                if wrong & flag == 0 {
                    continue;
                }
                let code = if instance_only & flag != 0 {
                    ErrorCode::ErrStaticNotVirtual
                } else {
                    ErrorCode::ErrBadMemberFlag
                };
                for at in &rule.at {
                    self.report(Location::new(tree, *at), code, &[text]);
                }
            }
        }
    }

    /// Pointers outside an unsafe context. Up to C# 15 a pointer type, and
    /// `&x`, `*p` and `p->f`, may only be written in one (CS0214). The
    /// memory safety rules of the preview make naming a pointer safe, and
    /// only reading or writing through one needs an unsafe context (CS9360,
    /// on the operator). Whether a context is unsafe is a matter of where
    /// the code is written — inside something marked `unsafe`, or an
    /// `unsafe` block — so the syntax alone answers it.
    fn pointers_in(&mut self, tree: usize) {
        let Some(root) = self.binder.tree_root(tree) else {
            return;
        };
        let evolved = self
            .compilation
            .trees()
            .get(tree)
            .is_some_and(|syntax| syntax.language_version().at_least(LanguageVersion::Preview));
        for node in root.descendants() {
            let (legacy, operation) = match node.kind() {
                SyntaxKind::PointerType
                | SyntaxKind::FunctionPointerType
                | SyntaxKind::AddressOfExpression => (true, false),
                SyntaxKind::PointerIndirectionExpression
                | SyntaxKind::PointerMemberAccessExpression => (true, true),
                _ => (false, false),
            };
            if !legacy || in_unsafe_context(&node) {
                continue;
            }
            if !evolved {
                self.report(
                    Location::new(tree, node.span()),
                    ErrorCode::ErrUnsafeNeeded,
                    &[],
                );
                continue;
            }
            let operator = node.child_tokens().find(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::AsteriskToken | SyntaxKind::MinusGreaterThanToken
                )
            });
            if operation && let Some(operator) = operator {
                self.report(
                    Location::new(tree, operator.span()),
                    ErrorCode::ErrUnsafeOperation,
                    &[],
                );
            }
        }
    }

    /// `[return: X]` on a declaration that has no return value (CS0657),
    /// and `[delegate: X]`, which names no location at all (CS0658).
    fn attribute_targets_in(&mut self, tree: usize) {
        let Some(root) = self.binder.tree_root(tree) else {
            return;
        };
        for specifier in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::AttributeTargetSpecifier)
        {
            let Some(target) = specifier.first_token() else {
                continue;
            };
            let Some(declaration) = specifier.parent().and_then(|list| list.parent()) else {
                continue;
            };
            let Some(valid) = attribute_locations(declaration) else {
                continue;
            };
            let word = target.value_text().to_string();
            let code = if !ATTRIBUTE_LOCATIONS.contains(&word.as_str()) {
                ErrorCode::WrnInvalidAttributeLocation
            } else if valid.contains(&word.as_str()) {
                continue;
            } else {
                ErrorCode::WrnAttributeLocationOnBadDeclaration
            };
            self.report(
                Location::new(tree, target.span()),
                code,
                &[&word, &valid.join(", ")],
            );
        }
    }

    fn attributes_in(&mut self, tree: usize) {
        let Some(root) = self.binder.tree_root(tree) else {
            return;
        };
        for attribute in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Attribute)
        {
            let Some(name) = attribute
                .children()
                .find(|child| child.kind().is_type_node())
            else {
                continue;
            };
            let Some(declaration) = attribute.parent().and_then(|list| list.parent()) else {
                continue;
            };
            let (bound, found) = crate::body::BodyBinder::bind_attribute_diagnosed(
                &self.binder,
                tree,
                declaration,
                &attribute,
            );
            // An argument of an attribute that did not bind is not judged:
            // Roslyn says what is wrong with the attribute, and stops.
            let clean = !found.iter().any(|(_, diagnostic)| diagnostic.is_error());
            self.found.extend(found);
            if let Some(bound) = bound
                .as_ref()
                .filter(|bound| clean && bound.constructor.is_some())
            {
                for value in bound
                    .arguments
                    .iter()
                    .chain(bound.named.iter().map(|(_, value)| value))
                {
                    self.attribute_argument(tree, value);
                }
            }
            if name.kind() != SyntaxKind::IdentifierName {
                continue;
            }
            if bound.is_some_and(|bound| bound.ty.is_error()) {
                let text = name.text().trim().trim_start_matches('@').to_string();
                let location = Location::new(tree, name.span());
                if !text.ends_with("Attribute") {
                    self.report(
                        location,
                        ErrorCode::ErrSingleTypeNameNotFound,
                        &[&format!("{text}Attribute")],
                    );
                }
                self.report(location, ErrorCode::ErrSingleTypeNameNotFound, &[&text]);
            }
        }
    }

    /// CS0182: an attribute argument has to be something the metadata can
    /// hold — a constant, a `typeof`, or a one-dimensional array of those.
    /// Only what plainly cannot be one is reported, so that a constant the
    /// folder does not understand is never called anything else.
    fn attribute_argument(&mut self, tree: usize, value: &BoundExpression) {
        if has_error_part(value) || is_null(value) {
            return;
        }
        match &value.kind {
            BoundExpressionKind::Conversion { operand, .. } => {
                self.attribute_argument(tree, operand);
            }
            BoundExpressionKind::ArrayCreation {
                element,
                lengths,
                elements,
            } => {
                let sized = lengths.len() > 1
                    || lengths.first().is_some_and(|length| {
                        self.binder.folded(length) != Some(ConstantValue::Int32(0))
                            && elements.is_empty()
                    });
                if sized || matches!(element, Type::Array { .. }) {
                    self.report(
                        Location::new(tree, value.span),
                        ErrorCode::ErrBadAttributeArgument,
                        &[],
                    );
                    return;
                }
                for element in elements {
                    self.attribute_argument(tree, element);
                }
            }
            _ if self.binder.folded(value).is_none() && !self.could_be_attribute_value(value) => {
                self.report(
                    Location::new(tree, value.span),
                    ErrorCode::ErrBadAttributeArgument,
                    &[],
                );
            }
            _ => {}
        }
    }

    /// Whether an expression might be a constant as far as this compiler can
    /// tell: `false` only for what never is one.
    fn could_be_attribute_value(&self, value: &BoundExpression) -> bool {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        match &value.kind {
            // `new AttributeTargets()` is the enum's zero, a constant.
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } => {
                arguments.is_empty()
                    && initializers.is_empty()
                    && value.ty.symbol().is_some_and(|symbol| {
                        symbols.get(symbol).type_kind() == Some(TypeKind::Enum)
                            || ATTRIBUTE_PRIMITIVES
                                .iter()
                                .filter(|special| {
                                    !matches!(
                                        special,
                                        crate::corlib::SpecialType::Object
                                            | crate::corlib::SpecialType::String
                                    )
                                })
                                .any(|special| compilation.special_type(*special) == Some(symbol))
                    })
            }
            // A parameter of the member the attribute is on is not in scope
            // there (CS0103), which is not this check's to say.
            BoundExpressionKind::Parameter(_) => true,
            BoundExpressionKind::Call { .. }
            | BoundExpressionKind::Lambda(_)
            | BoundExpressionKind::UnboundLambda(_)
            | BoundExpressionKind::Property { .. }
            | BoundExpressionKind::IndexerAccess { .. }
            | BoundExpressionKind::ArrayAccess { .. }
            | BoundExpressionKind::This
            | BoundExpressionKind::Base
            | BoundExpressionKind::Assignment { .. }
            | BoundExpressionKind::CompoundAssignment { .. }
            | BoundExpressionKind::Increment { .. }
            | BoundExpressionKind::Await { .. }
            | BoundExpressionKind::IsPattern { .. }
            | BoundExpressionKind::Switch { .. }
            | BoundExpressionKind::DelegateCreation { .. } => false,
            BoundExpressionKind::Field { field, .. } => {
                let field = symbols.get(*field);
                field.modifiers.contains(Modifiers::CONST)
                    || field.container.is_some_and(|container| {
                        symbols.get(container).type_kind() == Some(TypeKind::Enum)
                    })
            }
            // `default(T)` and `sizeof(T)` of a type parameter, or of a
            // struct the metadata has no constants of.
            BoundExpressionKind::Default(ty) | BoundExpressionKind::SizeOf(ty) => match ty {
                Type::TypeParameter(_) => false,
                Type::Named { symbol, .. } => {
                    let declared = symbols.get(*symbol);
                    let primitive = ATTRIBUTE_PRIMITIVES
                        .iter()
                        .any(|special| compilation.special_type(*special) == Some(*symbol));
                    primitive
                        || declared.type_kind() != Some(TypeKind::Struct)
                        || matches!(value.kind, BoundExpressionKind::SizeOf(_))
                            && declared.type_kind() == Some(TypeKind::Enum)
                }
                _ => true,
            },
            BoundExpressionKind::Binary { left, right, .. } => {
                self.could_be_attribute_value(left) && self.could_be_attribute_value(right)
            }
            BoundExpressionKind::Unary { operand, .. }
            | BoundExpressionKind::Conversion { operand, .. } => {
                self.could_be_attribute_value(operand)
            }
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                self.could_be_attribute_value(condition)
                    && self.could_be_attribute_value(consequence)
                    && self.could_be_attribute_value(alternative)
            }
            _ => true,
        }
    }

    // MARK: - constants

    /// CS0110: a constant whose value is written in terms of itself, through
    /// however many others. Each circle is reported once, at the member of
    /// it written first, as Roslyn reports it at the one it reaches first.
    fn constants(&mut self) {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        // A circle is found by working a member of it out, so every
        // constant of the files checked is, which caches what the bodies
        // and the emitter ask for next.
        for symbol in symbols.iter() {
            if compilation.is_from_metadata(symbol.id) {
                break;
            }
            if symbol.kind != SymbolKind::Field
                || compilation.is_from_corlib(symbol.id)
                || !symbol
                    .locations
                    .iter()
                    .any(|location| self.covers(location.tree))
            {
                continue;
            }
            let in_enum = symbol.container.is_some_and(|container| {
                symbols.get(container).type_kind() == Some(TypeKind::Enum)
            });
            if in_enum || symbol.modifiers.contains(Modifiers::CONST) {
                let _ = self.binder.constant_value(symbol.id);
            }
        }
        for circle in compilation.circular_constants() {
            let first = circle
                .iter()
                .filter_map(|member| {
                    let location = symbols.get(*member).locations.first()?;
                    Some(((location.tree, location.span.start()), *member, *location))
                })
                .min_by_key(|(place, _, _)| *place);
            let Some((_, member, location)) = first else {
                continue;
            };
            if !self.covers(location.tree) {
                continue;
            }
            let display = member_display(compilation, member, &Frame::new(), None);
            self.report(location, ErrorCode::ErrCircConstValue, &[&display]);
        }
    }

    /// CS0543: an enumerator without a value of its own is one more than the
    /// member before it, so it overflows when that member holds the last
    /// value of the underlying type. Only the first overflowing member of a
    /// run is reported: the members after it have no value to count from.
    fn enumerators(&mut self) {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        for symbol in symbols.iter() {
            if compilation.is_from_metadata(symbol.id) {
                break;
            }
            if symbol.kind != SymbolKind::NamedType
                || compilation.is_from_corlib(symbol.id)
                || symbol.type_kind() != Some(TypeKind::Enum)
                || !symbol
                    .locations
                    .iter()
                    .any(|location| self.covers(location.tree))
            {
                continue;
            }
            let enum_type = Type::named(symbol.id);
            let Some(underlying) = self.binder.enum_underlying(&enum_type) else {
                continue;
            };
            let Some(max) = self
                .binder
                .special_of(&underlying)
                .and_then(max_of_integral)
            else {
                continue;
            };
            // The value the previous member has: `Some(-1)` before the first
            // one, so that it counts from zero. `None` once there is none to
            // count from, which is after an overflow or an erroneous value.
            let mut previous: Option<i128> = Some(-1);
            for &member in &symbol.members {
                if symbols.get(member).kind != SymbolKind::Field {
                    continue;
                }
                if self.binder.has_initializer(member) {
                    previous = self
                        .binder
                        .constant_value(member)
                        .and_then(|value| crate::constant::as_exact(&value));
                    continue;
                }
                match previous {
                    Some(value) if value == max => {
                        previous = None;
                        let Some(location) = symbols.get(member).locations.first().copied() else {
                            continue;
                        };
                        if self.covers(location.tree) {
                            let display = member_display(compilation, member, &Frame::new(), None);
                            self.report(location, ErrorCode::ErrEnumeratorOverflow, &[&display]);
                        }
                    }
                    Some(value) => previous = Some(value + 1),
                    None => {}
                }
            }
        }
    }

    // MARK: - members against each other and against the bases

    fn types(&mut self) {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        for symbol in symbols.iter() {
            if compilation.is_from_metadata(symbol.id) {
                break;
            }
            if symbol.kind != SymbolKind::NamedType
                || compilation.is_from_corlib(symbol.id)
                || !symbol
                    .locations
                    .iter()
                    .any(|location| self.covers(location.tree))
                || symbol
                    .as_named_type()
                    .is_some_and(|detail| detail.anonymous)
            {
                continue;
            }
            let kind = symbol.type_kind();
            // A record's members are half the language's, and what it
            // synthesises and what the source wrote meet in ways this pass
            // does not model; enums and delegates have no members to check.
            if !matches!(
                kind,
                Some(TypeKind::Class | TypeKind::Struct | TypeKind::Interface)
            ) {
                continue;
            }
            self.duplicates(symbol.id);
            if kind == Some(TypeKind::Class) {
                self.abstract_in_concrete(symbol.id);
            }
            if kind != Some(TypeKind::Interface) {
                self.bodies(symbol.id);
            }
            if kind == Some(TypeKind::Interface) {
                continue;
            }
            let Some(chain) = self.chain(symbol.id) else {
                continue;
            };
            self.inheritance(symbol.id, &chain);
            self.equality(symbol.id);
            if kind == Some(TypeKind::Class) {
                self.abstract_members(symbol.id, &chain);
            }
            self.interfaces(symbol.id, &chain);
        }
    }

    /// The members of a type that is being checked: written in the source,
    /// by a name the source gave them.
    fn own_members(&self, ty: SymbolId) -> Vec<SymbolId> {
        let symbols = self.compilation.symbols();
        symbols
            .get(ty)
            .members
            .iter()
            .copied()
            .filter(|member| {
                let symbol = symbols.get(*member);
                !symbol.locations.is_empty()
                    && !symbol.name.contains('<')
                    && !symbol.modifiers.contains(Modifiers::PARTIAL)
                    && match &symbol.detail {
                        Detail::Method(detail) => {
                            !detail.is_extension && !in_extension_block(self.compilation, *member)
                        }
                        Detail::Field(_) | Detail::Property(_) | Detail::Event(_) => true,
                        _ => false,
                    }
            })
            .collect()
    }

    /// CS0102 and CS0111: two members of one type with one name, where only
    /// methods with different parameters may share one.
    fn duplicates(&mut self, ty: SymbolId) {
        let symbols = self.compilation.symbols();
        let mut members = self.own_members(ty);
        members.sort_by_key(|member| {
            let location = symbols.get(*member).locations[0];
            (location.tree, location.span.start())
        });
        let type_name = symbols.qualified_name(ty);
        for (index, member) in members.iter().enumerate() {
            let symbol = symbols.get(*member);
            let method = symbol.as_method();
            if (symbol.name.contains('.') && symbol.name != ".ctor") || symbol.name == "this[]" {
                continue;
            }
            if method.is_some_and(|detail| {
                !matches!(
                    detail.method_kind,
                    MethodKind::Ordinary | MethodKind::Constructor
                )
            }) {
                continue;
            }
            for earlier in &members[..index] {
                let other = symbols.get(*earlier);
                if other.name != symbol.name {
                    continue;
                }
                let location = symbol.locations[0];
                match (method, other.as_method()) {
                    (Some(_), Some(earlier_method)) => {
                        if !matches!(
                            earlier_method.method_kind,
                            MethodKind::Ordinary | MethodKind::Constructor
                        ) {
                            continue;
                        }
                        let same =
                            self.same_parameters(*member, &Frame::new(), *earlier, &Frame::new());
                        // `M(int a, __arglist)` is called another way than
                        // `M(int a)`, and is another signature.
                        let vararg = method.is_some_and(|detail| detail.is_vararg);
                        if same == Some(true)
                            && self.same_ref_kinds(*member, *earlier)
                            && vararg == earlier_method.is_vararg
                        {
                            let name = if symbol.name == ".ctor" {
                                symbols.get(ty).name.clone()
                            } else {
                                symbol.name.clone()
                            };
                            let owner = type_display(self.compilation, ty);
                            self.report(
                                location,
                                ErrorCode::ErrMemberAlreadyExists,
                                &[&name, &owner],
                            );
                            break;
                        }
                    }
                    (None, None) => {
                        self.report(
                            location,
                            ErrorCode::ErrDuplicateNameInClass,
                            &[&type_name, &symbol.name],
                        );
                        break;
                    }
                    // A method beside a field of its name: the one written
                    // second is the duplicate, whichever it is.
                    _ => {
                        if symbol.name == ".ctor"
                            || accessor_like(&symbol.name)
                            || accessor_like(&other.name)
                        {
                            continue;
                        }
                        self.report(
                            location,
                            ErrorCode::ErrDuplicateNameInClass,
                            &[&type_name, &symbol.name],
                        );
                        break;
                    }
                }
            }
        }
    }

    /// CS0513: an `abstract` member of a class that is not, which nothing
    /// could ever derive a complete class from.
    fn abstract_in_concrete(&mut self, ty: SymbolId) {
        let symbols = self.compilation.symbols();
        let owner = symbols.get(ty);
        if owner.modifiers.contains(Modifiers::ABSTRACT) {
            return;
        }
        let owner_name = type_display(self.compilation, ty);
        for member in self.own_members(ty) {
            let symbol = symbols.get(member);
            if symbol.modifiers.contains(Modifiers::ABSTRACT) {
                let display = member_display(self.compilation, member, &Frame::new(), None);
                self.report(
                    symbol.locations[0],
                    ErrorCode::ErrAbstractInConcreteClass,
                    &[&display, &owner_name],
                );
            }
        }
    }

    /// CS0501 and CS0500: a method of a class or struct without a body
    /// that says nothing about why, or an abstract one with a body.
    fn bodies(&mut self, ty: SymbolId) {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        for member in self.own_members(ty) {
            let symbol = symbols.get(member);
            if symbol
                .as_method()
                .is_none_or(|detail| detail.method_kind != MethodKind::Ordinary)
            {
                continue;
            }
            let Some(node) = compilation.declaration_node(member) else {
                continue;
            };
            if node.kind() != SyntaxKind::MethodDeclaration {
                continue;
            }
            let has_body = node.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                )
            });
            let modifiers = symbol.modifiers;
            let excused = modifiers.contains(Modifiers::ABSTRACT)
                || modifiers.contains(Modifiers::EXTERN)
                || modifiers.contains(Modifiers::PARTIAL)
                // `[DllImport]` and friends make a method extern in all but
                // name; the modifier is still required, but not by this.
                || node
                    .children()
                    .any(|child| child.kind() == SyntaxKind::AttributeList);
            let location = symbol.locations[0];
            if !has_body && !excused {
                let display = member_display(compilation, member, &Frame::new(), None);
                self.report(location, ErrorCode::ErrConcreteMissingBody, &[&display]);
            } else if has_body && modifiers.contains(Modifiers::ABSTRACT) {
                let display = member_display(compilation, member, &Frame::new(), None);
                self.report(location, ErrorCode::ErrAbstractHasBody, &[&display]);
            }
        }
    }

    /// Whether two methods take their parameters the same way: `ref` and
    /// `out` differ from each other only in a way C# rejects with another
    /// error, and from a value parameter in a way it allows.
    fn same_ref_kinds(&self, first: SymbolId, second: SymbolId) -> bool {
        let kinds = |method: SymbolId| -> Vec<RefKind> {
            self.parameters_of(method)
                .iter()
                .map(|parameter| {
                    self.compilation
                        .symbols()
                        .get(*parameter)
                        .as_parameter()
                        .map_or(RefKind::None, |detail| detail.ref_kind)
                })
                .collect()
        };
        kinds(first) == kinds(second)
    }

    fn parameters_of(&self, member: SymbolId) -> Vec<SymbolId> {
        match &self.compilation.symbols().get(member).detail {
            Detail::Method(detail) => detail.parameters.clone(),
            Detail::Property(detail) => detail.parameters.clone(),
            _ => Vec::new(),
        }
    }

    /// The classes a type derives from, nearest first, each with what its
    /// type parameters stand for as the type sees them. `None` where one of
    /// them could not be worked out, which leaves every question about what
    /// the type inherits without an answer.
    fn chain(&self, ty: SymbolId) -> Option<Vec<(SymbolId, Frame)>> {
        let symbols = self.compilation.symbols();
        let mut chain = Vec::new();
        let mut frame = Frame::new();
        let mut current = ty;
        for _ in 0..64 {
            let Some(base) = self.binder.base_class_of(current) else {
                return Some(chain);
            };
            let base = base.substitute(&frame);
            let Type::Named {
                symbol,
                type_arguments,
            } = &base
            else {
                return None;
            };
            if contains_error(&base)
                || chain.iter().any(|(seen, _)| seen == symbol)
                || *symbol == ty
            {
                return None;
            }
            frame = frame_of(symbols, *symbol, type_arguments)?;
            chain.push((*symbol, frame.clone()));
            current = *symbol;
        }
        None
    }

    /// CS0115, CS0506, CS0239, CS0108 and CS0114: what each member does to
    /// the members of the same name it inherits.
    fn inheritance(&mut self, ty: SymbolId, chain: &[(SymbolId, Frame)]) {
        let symbols = self.compilation.symbols();
        for member in self.own_members(ty) {
            let symbol = symbols.get(member);
            if symbol.name.contains('.') || symbol.name == "this[]" {
                continue;
            }
            if symbol
                .as_method()
                .is_some_and(|detail| detail.method_kind != MethodKind::Ordinary)
            {
                continue;
            }
            let location = symbol.locations[0];
            let display = || member_display(self.compilation, member, &Frame::new(), None);
            if symbol.modifiers.contains(Modifiers::OVERRIDE) {
                match self.overridden(member, chain) {
                    Lookup::Unknown => {}
                    Lookup::Missing => {
                        self.report(location, ErrorCode::ErrOverrideNotExpected, &[&display()]);
                    }
                    Lookup::Found(base, frame) => {
                        let modifiers = effective_modifiers(self.compilation, base);
                        let base_display = || member_display(self.compilation, base, &frame, None);
                        if modifiers.contains(Modifiers::OVERRIDE)
                            && modifiers.contains(Modifiers::SEALED)
                        {
                            self.report(
                                location,
                                ErrorCode::ErrCantOverrideSealed,
                                &[&display(), &base_display()],
                            );
                        } else if !is_virtual(modifiers) {
                            self.report(
                                location,
                                ErrorCode::ErrCantOverrideNonVirtual,
                                &[&display(), &base_display()],
                            );
                        }
                        // CS0809: `[Obsolete]` on an override of a member
                        // that is not, whose callers see no warning.
                        if self.compilation.obsolete_of(member).is_some()
                            && self.compilation.obsolete_of(base).is_none()
                        {
                            self.report(
                                location,
                                ErrorCode::WrnObsoleteOverridingNonObsolete,
                                &[&display(), &base_display()],
                            );
                        }
                    }
                }
                continue;
            }
            if symbol.modifiers.contains(Modifiers::NEW) {
                continue;
            }
            if let Lookup::Found(base, frame) = self.hidden(member, chain) {
                let base_display = member_display(self.compilation, base, &frame, None);
                let same_kind = symbols.get(base).kind == symbol.kind;
                let code = if same_kind
                    && matches!(symbol.kind, SymbolKind::Method | SymbolKind::Property)
                    && is_virtual(effective_modifiers(self.compilation, base))
                {
                    ErrorCode::WrnNewOrOverrideExpected
                } else {
                    ErrorCode::WrnNewRequired
                };
                self.report(location, code, &[&display(), &base_display]);
            }
        }
    }

    /// CS0660 and CS0661: `==` or `!=` defined without overriding `Equals`
    /// or `GetHashCode`, and CS0659: `Equals` overridden without
    /// `GetHashCode`. At the type's name; a record makes all three itself.
    fn equality(&mut self, ty: SymbolId) {
        let symbols = self.compilation.symbols();
        let mut operator = false;
        let mut equals = false;
        let mut hash = false;
        for member in self.own_members(ty) {
            let symbol = symbols.get(member);
            let Some(detail) = symbol.as_method() else {
                continue;
            };
            let overrides = symbol.modifiers.contains(Modifiers::OVERRIDE);
            match (symbol.name.as_str(), detail.method_kind) {
                ("op_Equality" | "op_Inequality", MethodKind::Operator) => operator = true,
                ("Equals", MethodKind::Ordinary) if overrides && detail.parameters.len() == 1 => {
                    equals = true;
                }
                ("GetHashCode", MethodKind::Ordinary)
                    if overrides && detail.parameters.is_empty() =>
                {
                    hash = true;
                }
                _ => {}
            }
        }
        let Some(&location) = symbols.get(ty).locations.first() else {
            return;
        };
        let shown = self.binder.self_type(ty).display(symbols);
        if operator && !equals {
            self.report(location, ErrorCode::WrnEqualityOpWithoutEquals, &[&shown]);
        }
        if operator && !hash {
            self.report(
                location,
                ErrorCode::WrnEqualityOpWithoutGetHashCode,
                &[&shown],
            );
        }
        if equals && !hash {
            self.report(location, ErrorCode::WrnEqualsWithoutGetHashCode, &[&shown]);
        }
    }

    /// The member an `override` overrides: the nearest one up the chain with
    /// its name and, for a method, its parameters.
    fn overridden(&self, member: SymbolId, chain: &[(SymbolId, Frame)]) -> Lookup {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let tree = symbol
            .locations
            .first()
            .map_or(usize::MAX, |location| location.tree);
        for (base, frame) in chain {
            for candidate in symbols.lookup(*base, &symbol.name) {
                let found = symbols.get(*candidate);
                if !self.visible(*candidate, tree) {
                    continue;
                }
                match (symbol.kind, found.kind) {
                    (SymbolKind::Method, SymbolKind::Method) => {
                        match self.same_parameters(member, &Frame::new(), *candidate, frame) {
                            Some(true) => return Lookup::Found(*candidate, frame.clone()),
                            Some(false) => {}
                            None => return Lookup::Unknown,
                        }
                    }
                    (SymbolKind::Property, SymbolKind::Property)
                    | (SymbolKind::Event, SymbolKind::Event) => {
                        return Lookup::Found(*candidate, frame.clone());
                    }
                    // A field or a type of that name in between: another
                    // error, and not this one.
                    _ => return Lookup::Unknown,
                }
            }
        }
        Lookup::Missing
    }

    /// The inherited member a member without `new` or `override` hides, if
    /// it hides one: a method hides the one with its parameters, anything
    /// else the one with its name.
    fn hidden(&self, member: SymbolId, chain: &[(SymbolId, Frame)]) -> Lookup {
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(member);
        let tree = symbol
            .locations
            .first()
            .map_or(usize::MAX, |location| location.tree);
        for (base, frame) in chain {
            for candidate in symbols.lookup(*base, &symbol.name) {
                let found = symbols.get(*candidate);
                if !self.visible(*candidate, tree) || found.name.contains('.') {
                    continue;
                }
                match (symbol.kind, found.kind) {
                    (SymbolKind::Method, SymbolKind::Method) => {
                        if found
                            .as_method()
                            .is_some_and(|detail| detail.method_kind != MethodKind::Ordinary)
                        {
                            continue;
                        }
                        match self.same_parameters(member, &Frame::new(), *candidate, frame) {
                            Some(true) => return Lookup::Found(*candidate, frame.clone()),
                            Some(false) => {}
                            None => return Lookup::Unknown,
                        }
                    }
                    (
                        SymbolKind::Field | SymbolKind::Property | SymbolKind::Event,
                        SymbolKind::Field | SymbolKind::Property | SymbolKind::Event,
                    ) => return Lookup::Found(*candidate, frame.clone()),
                    // A field, property or event hides every inherited
                    // member of its name, a method among them, and a method
                    // every one that is not a method (§15.3.9): `public Action
                    // Close` over a base's `Close()` is CS0108.
                    (
                        SymbolKind::Field | SymbolKind::Property | SymbolKind::Event,
                        SymbolKind::Method,
                    ) => {
                        if found
                            .as_method()
                            .is_some_and(|detail| detail.method_kind != MethodKind::Ordinary)
                        {
                            continue;
                        }
                        return Lookup::Found(*candidate, frame.clone());
                    }
                    (
                        SymbolKind::Method,
                        SymbolKind::Field | SymbolKind::Property | SymbolKind::Event,
                    ) => return Lookup::Found(*candidate, frame.clone()),
                    _ => return Lookup::Unknown,
                }
            }
        }
        Lookup::Missing
    }

    /// Whether a derived type can see an inherited member at all: a private
    /// one is not inherited in any way that matters here, and neither is an
    /// internal one of another assembly.
    fn visible(&self, member: SymbolId, tree: usize) -> bool {
        let accessibility = effective_accessibility(self.compilation, member);
        match accessibility {
            Accessibility::Private => false,
            // A reference's internals are loaded only where it names the
            // code compiled in an `[InternalsVisibleTo]`, and then for the
            // assemblies it names: Timeline overrides the `internal virtual
            // OnHeaderIconGUI` of the engine's `Editor`, which trusts it.
            Accessibility::Internal | Accessibility::ProtectedAndInternal => {
                !self.compilation.is_from_metadata(member)
                    || (self.compilation.trusts_any() && self.compilation.sees(member, tree))
            }
            _ => true,
        }
    }

    /// CS0534: an abstract member up the chain that nothing between it and
    /// this class overrides.
    fn abstract_members(&mut self, ty: SymbolId, chain: &[(SymbolId, Frame)]) {
        let symbols = self.compilation.symbols();
        let owner = symbols.get(ty);
        if owner.modifiers.contains(Modifiers::ABSTRACT)
            || owner.modifiers.contains(Modifiers::STATIC)
        {
            return;
        }
        let Some(location) = owner.locations.first().copied() else {
            return;
        };
        // Every class from this one up, with what its parameters mean here.
        let mut levels: Vec<(SymbolId, Frame)> = vec![(ty, Frame::new())];
        levels.extend(chain.iter().cloned());
        let type_name = type_display(self.compilation, ty);
        for (depth, (level, frame)) in levels.iter().enumerate().skip(1) {
            for member in symbols.get(*level).members.clone() {
                let symbol = symbols.get(member);
                // A metadata property says whether it is abstract on its
                // accessors, not on itself.
                if !effective_modifiers(self.compilation, member).contains(Modifiers::ABSTRACT)
                    || symbol.name.contains('.')
                    || !self.visible(member, location.tree)
                {
                    continue;
                }
                if symbol.name == "this[]" {
                    return;
                }
                if !matches!(
                    symbol.kind,
                    SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
                ) || symbol
                    .as_method()
                    .is_some_and(|detail| detail.method_kind != MethodKind::Ordinary)
                {
                    continue;
                }
                match self.overridden_below(member, frame, &levels[..depth]) {
                    Some(true) => {}
                    None => return,
                    Some(false) => {
                        let names: Vec<String> = match &symbol.detail {
                            Detail::Property(detail) => {
                                let base = member_display(self.compilation, member, frame, None);
                                let mut names = Vec::new();
                                if detail.has_get {
                                    names.push(format!("{base}.get"));
                                }
                                if detail.has_set {
                                    names.push(format!("{base}.set"));
                                }
                                names
                            }
                            _ => vec![member_display(self.compilation, member, frame, None)],
                        };
                        for name in names {
                            self.report(
                                location,
                                ErrorCode::ErrUnimplementedAbstractMethod,
                                &[&type_name, &name],
                            );
                        }
                    }
                }
            }
        }
    }

    /// Whether a class below `abstract_member`'s overrides it. `None` where
    /// that cannot be told.
    fn overridden_below(
        &self,
        abstract_member: SymbolId,
        frame: &Frame,
        below: &[(SymbolId, Frame)],
    ) -> Option<bool> {
        let symbols = self.compilation.symbols();
        let wanted = symbols.get(abstract_member);
        for (level, level_frame) in below {
            for candidate in symbols.lookup(*level, &wanted.name) {
                let found = symbols.get(*candidate);
                if found.kind != wanted.kind
                    || !effective_modifiers(self.compilation, *candidate)
                        .contains(Modifiers::OVERRIDE)
                {
                    continue;
                }
                if found.kind == SymbolKind::Method {
                    match self.same_parameters(*candidate, level_frame, abstract_member, frame) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => return None,
                    }
                } else {
                    return Some(true);
                }
            }
        }
        Some(false)
    }

    /// CS0535 and CS0738: a member of an interface the type lists that
    /// nothing in the type or its bases implements.
    fn interfaces(&mut self, ty: SymbolId, chain: &[(SymbolId, Frame)]) {
        let compilation = self.compilation;
        let symbols = compilation.symbols();
        let Some(detail) = symbols.get(ty).as_named_type() else {
            return;
        };
        if compilation.metadata_bases(ty).is_some() {
            return;
        }
        let written = detail.base_types.clone();
        let resolved = self.binder.base_types_of(ty);
        if written.len() != resolved.len() {
            return;
        }
        let type_name = type_display(compilation, ty);
        let mut levels: Vec<(SymbolId, Frame)> = vec![(ty, Frame::new())];
        levels.extend(chain.iter().cloned());
        let listed_interfaces: Vec<(&TypeSyntaxRef, &Type)> = written
            .iter()
            .zip(&resolved)
            .filter(|(_, listed)| {
                listed.symbol().is_some_and(|listed| {
                    symbols.get(listed).type_kind() == Some(TypeKind::Interface)
                }) && !contains_error(listed)
            })
            .collect();
        // An interface member may have its body in any interface the type
        // has, not only below the one that declared it: `class C : I1, I2`
        // needs nothing for `I1.M` where `I2 : I1` implements it (C# 8).
        let everything: Vec<(SymbolId, Frame)> = listed_interfaces
            .iter()
            .filter_map(|(_, listed)| self.interface_closure(listed))
            .flatten()
            .collect();
        // An interface a compiled base class has is implemented there, all
        // of it, even where by explicit implementations — private methods,
        // which a reference shows nothing of: the engine's `Editor` is an
        // `IToolModeOwner`, and so is every inspector deriving from it.
        let compiled: Vec<SymbolId> = chain
            .iter()
            .filter(|(level, _)| compilation.is_from_metadata(*level))
            .flat_map(|(level, frame)| {
                self.binder
                    .base_types_of(*level)
                    .into_iter()
                    .map(|base| base.substitute(frame))
                    .collect::<Vec<_>>()
            })
            .filter_map(|base| self.interface_closure(&base))
            .flatten()
            .map(|(interface, _)| interface)
            .collect();
        for (reference, listed) in listed_interfaces {
            let Some(interfaces) = self.interface_closure(listed) else {
                continue;
            };
            for (interface, frame) in &interfaces {
                if compiled.contains(interface) {
                    continue;
                }
                for member in symbols.get(*interface).members.clone() {
                    if !self.needs_implementation(member) {
                        continue;
                    }
                    match self.implementation(member, *interface, frame, &levels, &everything) {
                        Implementation::Found | Implementation::Unknown => {}
                        Implementation::Missing => {
                            let name = member_display(compilation, member, frame, None);
                            self.report(
                                reference.0,
                                ErrorCode::ErrUnimplementedInterfaceMember,
                                &[&type_name, &name],
                            );
                        }
                        Implementation::WrongReturn(candidate, returns) => {
                            let name = member_display(compilation, member, frame, None);
                            let candidate =
                                member_display(compilation, candidate, &Frame::new(), None);
                            self.report(
                                reference.0,
                                ErrorCode::ErrCloseUnimplementedInterfaceMemberWrongReturnType,
                                &[&type_name, &name, &candidate, &returns],
                            );
                        }
                    }
                }
            }
        }
    }

    /// An interface and every interface it extends, each with what its
    /// parameters stand for. `None` where one of them did not resolve.
    fn interface_closure(&self, listed: &Type) -> Option<Vec<(SymbolId, Frame)>> {
        let symbols = self.compilation.symbols();
        let mut found: Vec<(SymbolId, Frame, Type)> = Vec::new();
        let mut pending = vec![listed.clone()];
        while let Some(next) = pending.pop() {
            let Type::Named {
                symbol,
                type_arguments,
            } = &next
            else {
                return None;
            };
            if contains_error(&next) {
                return None;
            }
            if found.iter().any(|(_, _, seen)| *seen == next) || found.len() > 64 {
                continue;
            }
            let frame = frame_of(symbols, *symbol, type_arguments)?;
            for base in self.binder.base_types_of(*symbol) {
                pending.push(base.substitute(&frame));
            }
            found.push((*symbol, frame, next));
        }
        Some(
            found
                .into_iter()
                .map(|(symbol, frame, _)| (symbol, frame))
                .collect(),
        )
    }

    /// Whether an interface member is one a class has to implement: an
    /// instance member with no body of its own.
    fn needs_implementation(&self, member: SymbolId) -> bool {
        let compilation = self.compilation;
        let symbol = compilation.symbols().get(member);
        if symbol.modifiers.contains(Modifiers::STATIC)
            || symbol.name.contains('.')
            || symbol.name == "this[]"
        {
            return false;
        }
        match &symbol.detail {
            Detail::Method(detail) if detail.method_kind == MethodKind::Ordinary => {}
            Detail::Property(_) | Detail::Event(_) => {}
            _ => return false,
        }
        if compilation.is_from_metadata(member) {
            return effective_modifiers(compilation, member).contains(Modifiers::ABSTRACT)
                && effective_accessibility(compilation, member) == Accessibility::Public;
        }
        if matches!(
            symbol.accessibility,
            Accessibility::Private | Accessibility::Protected | Accessibility::ProtectedAndInternal
        ) {
            return false;
        }
        // A member with a body is one the type may leave to the interface
        // (C# 8); so is a `sealed` one, which nothing may implement at all.
        compilation
            .interface_member_modifiers(member)
            .contains(Modifiers::ABSTRACT)
    }

    /// What in a type or its bases implements an interface member.
    fn implementation(
        &self,
        member: SymbolId,
        interface: SymbolId,
        frame: &Frame,
        levels: &[(SymbolId, Frame)],
        interfaces: &[(SymbolId, Frame)],
    ) -> Implementation {
        let symbols = self.compilation.symbols();
        let wanted = symbols.get(member);
        let interface_name = &symbols.get(interface).name;
        // `void IShape.Draw()`: an explicit implementation, in the type, in
        // a base, or in an interface that gives it a body. The interface is
        // told by its name, or — `Type.Method` where `using Type =
        // Interface;` — by what the name resolves to.
        let explicit = |owner: SymbolId| {
            symbols.get(owner).members.iter().any(|candidate| {
                let found = symbols.get(*candidate);
                found.kind == wanted.kind
                    && found.name.rsplit_once('.').is_some_and(|(prefix, name)| {
                        name == wanted.name
                            && (names_interface(prefix, interface_name)
                                || self
                                    .binder
                                    .explicit_interface(*candidate)
                                    .and_then(|ty| ty.symbol())
                                    == Some(interface))
                    })
            })
        };
        if levels.iter().any(|(level, _)| explicit(*level))
            || interfaces.iter().any(|(other, _)| explicit(*other))
        {
            return Implementation::Found;
        }
        let mut wrong_return = None;
        for (level, level_frame) in levels {
            for candidate in symbols.lookup(*level, &wanted.name) {
                let found = symbols.get(*candidate);
                if found.kind != wanted.kind || found.modifiers.contains(Modifiers::STATIC) {
                    continue;
                }
                if found.kind != SymbolKind::Method {
                    return Implementation::Found;
                }
                match self.same_parameters(*candidate, level_frame, member, frame) {
                    None => return Implementation::Unknown,
                    Some(false) => continue,
                    Some(true) => {}
                }
                let mut sink = Diagnostics::new();
                let returns = self
                    .binder
                    .type_of(*candidate, &mut sink)
                    .substitute(level_frame);
                let expected = self
                    .binder
                    .type_of(member, &mut sink)
                    .substitute(&self.method_frame(member, frame, *candidate));
                if contains_error(&returns) || contains_error(&expected) {
                    return Implementation::Unknown;
                }
                if same_type(symbols, &returns, &expected) || level != &levels[0].0 {
                    return Implementation::Found;
                }
                wrong_return.get_or_insert((*candidate, expected));
            }
        }
        match wrong_return {
            Some((candidate, expected)) => {
                Implementation::WrongReturn(candidate, expected.display(symbols))
            }
            None => Implementation::Missing,
        }
    }

    /// The frame of `base` with its own type parameters standing for those
    /// of `derived`, position by position: `M<U>(U)` overriding `M<T>(T)`
    /// reads `T` as `U`.
    fn method_frame(&self, base: SymbolId, frame: &Frame, derived: SymbolId) -> Frame {
        let symbols = self.compilation.symbols();
        let mut frame = frame.clone();
        if let (Some(base), Some(derived)) = (
            symbols.get(base).as_method(),
            symbols.get(derived).as_method(),
        ) {
            for (from, to) in base.type_parameters.iter().zip(&derived.type_parameters) {
                frame.insert(*from, Type::TypeParameter(*to));
            }
        }
        frame
    }

    /// Whether two members take the same parameter types, each read in its
    /// own frame. `None` where a type involved did not resolve.
    fn same_parameters(
        &self,
        derived: SymbolId,
        derived_frame: &Frame,
        base: SymbolId,
        base_frame: &Frame,
    ) -> Option<bool> {
        let symbols = self.compilation.symbols();
        let arity = |member: SymbolId| {
            symbols
                .get(member)
                .as_method()
                .map_or(0, |detail| detail.type_parameters.len())
        };
        let (mine, theirs) = (self.parameters_of(derived), self.parameters_of(base));
        if arity(derived) != arity(base) || mine.len() != theirs.len() {
            return Some(false);
        }
        let base_frame = self.method_frame(base, base_frame, derived);
        let mut sink = Diagnostics::new();
        for (left, right) in mine.iter().zip(&theirs) {
            let by_ref = |parameter: SymbolId| {
                symbols
                    .get(parameter)
                    .as_parameter()
                    .is_some_and(|detail| detail.ref_kind != RefKind::None)
            };
            let left_type = self.binder.type_of(*left, &mut sink);
            let right_type = self.binder.type_of(*right, &mut sink);
            let left_ref = by_ref(*left) || matches!(left_type, Type::ByRef(_));
            let right_ref = by_ref(*right) || matches!(right_type, Type::ByRef(_));
            let left_type = left_type.value().substitute(derived_frame);
            let right_type = right_type.value().substitute(&base_frame);
            if contains_error(&left_type) || contains_error(&right_type) {
                return None;
            }
            if left_ref != right_ref || !same_type(symbols, &left_type, &right_type) {
                return Some(false);
            }
        }
        Some(true)
    }
}

/// What looking for an inherited member found.
enum Lookup {
    Found(SymbolId, Frame),
    Missing,
    /// Something in the way this pass cannot judge.
    Unknown,
}

enum Implementation {
    Found,
    Missing,
    Unknown,
    /// A method with the right parameters and the wrong return type, and the
    /// type it should have returned.
    WrongReturn(SymbolId, String),
}

/// What each type parameter of `symbol` stands for, given its arguments.
fn frame_of(
    symbols: &crate::symbol::Symbols,
    symbol: SymbolId,
    arguments: &[Type],
) -> Option<Frame> {
    let parameters = &symbols.get(symbol).as_named_type()?.type_parameters;
    if arguments.is_empty() {
        return Some(Frame::new());
    }
    if parameters.len() != arguments.len() {
        return None;
    }
    Some(
        parameters
            .iter()
            .copied()
            .zip(arguments.iter().cloned())
            .collect(),
    )
}

/// Whether two types are one type, a tuple being the `ValueTuple` it is
/// written for: `(int, string)` and `ValueTuple<int, string>` are the same
/// type to the language, whichever an alias or a signature spelled.
fn same_type(symbols: &crate::symbol::Symbols, first: &Type, second: &Type) -> bool {
    match (first, second) {
        // `dynamic` and `object` are one type to everything but the binder.
        (Type::Dynamic, Type::Named { symbol, .. })
        | (Type::Named { symbol, .. }, Type::Dynamic) => {
            symbols.qualified_name(*symbol) == "System.Object"
        }
        (Type::Tuple(elements), other) | (other, Type::Tuple(elements)) => {
            let parts: Vec<&Type> = match other {
                Type::Tuple(others) => others.iter().map(|element| &element.ty).collect(),
                Type::Named {
                    symbol,
                    type_arguments,
                } if symbols.get(*symbol).name == "ValueTuple" && elements.len() < 8 => {
                    type_arguments.iter().collect()
                }
                _ => return false,
            };
            parts.len() == elements.len()
                && elements
                    .iter()
                    .zip(parts)
                    .all(|(element, part)| same_type(symbols, &element.ty, part))
        }
        (
            Type::Named {
                symbol: first,
                type_arguments: first_arguments,
            },
            Type::Named {
                symbol: second,
                type_arguments: second_arguments,
            },
        ) => {
            first == second
                && first_arguments.len() == second_arguments.len()
                && first_arguments
                    .iter()
                    .zip(second_arguments)
                    .all(|(first, second)| same_type(symbols, first, second))
        }
        (
            Type::Array {
                element: first,
                rank: first_rank,
            },
            Type::Array {
                element: second,
                rank: second_rank,
            },
        ) => first_rank == second_rank && same_type(symbols, first, second),
        (Type::Pointer(first), Type::Pointer(second))
        | (Type::ByRef(first), Type::ByRef(second)) => same_type(symbols, first, second),
        _ => first == second,
    }
}

/// The types whose values an attribute argument can hold as constants.
const ATTRIBUTE_PRIMITIVES: [crate::corlib::SpecialType; 14] = [
    crate::corlib::SpecialType::Boolean,
    crate::corlib::SpecialType::Char,
    crate::corlib::SpecialType::SByte,
    crate::corlib::SpecialType::Byte,
    crate::corlib::SpecialType::Int16,
    crate::corlib::SpecialType::UInt16,
    crate::corlib::SpecialType::Int32,
    crate::corlib::SpecialType::UInt32,
    crate::corlib::SpecialType::Int64,
    crate::corlib::SpecialType::UInt64,
    crate::corlib::SpecialType::Single,
    crate::corlib::SpecialType::Double,
    crate::corlib::SpecialType::String,
    crate::corlib::SpecialType::Object,
];

/// Whether an expression is `null`, however converted.
fn is_null(expression: &BoundExpression) -> bool {
    match &expression.kind {
        BoundExpressionKind::Literal(ConstantValue::Null) => true,
        BoundExpressionKind::Conversion { operand, .. } => is_null(operand),
        _ => false,
    }
}

/// Whether a bound expression has a part that did not bind, which has been
/// complained about already.
fn has_error_part(expression: &BoundExpression) -> bool {
    let mut found = false;
    crate::definite::each_child_of(expression, &mut |child| {
        found |= has_error_part(child);
    });
    found
        || matches!(
            expression.kind,
            BoundExpressionKind::Error | BoundExpressionKind::Unsupported(_)
        )
}

fn contains_error(ty: &Type) -> bool {
    match ty {
        Type::Error => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(contains_error),
        Type::Array { element, .. } => contains_error(element),
        Type::Pointer(inner) | Type::ByRef(inner) => contains_error(inner),
        Type::Tuple(elements) => elements.iter().any(|element| contains_error(&element.ty)),
        Type::FunctionPointer(pointer) => pointer.types().any(contains_error),
        Type::TypeParameter(_) | Type::Null | Type::Void | Type::Dynamic => false,
    }
}

/// Whether a member can be overridden: `virtual`, `abstract` or an override
/// that is not sealed. A metadata method that is virtual and final is how C#
/// writes an implicit interface implementation, which is not virtual at all.
/// Whether code at `node` is in an unsafe context (§24.2): inside a
/// declaration marked `unsafe`, an `unsafe` block, or a `using unsafe`
/// alias.
fn in_unsafe_context(node: &SyntaxNode) -> bool {
    node.ancestors().any(|ancestor| {
        ancestor.kind() == SyntaxKind::UnsafeStatement
            // `typeof(int*)` names a type and reads through nothing: Roslyn's
            // `TypeofBinder` binds its operand as an unsafe region.
            || ancestor.kind() == SyntaxKind::TypeOfExpression
            || ancestor
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::UnsafeKeyword)
    })
}

/// The words a declaration may carry in front of it.
const MODIFIERS: [&str; 19] = [
    "public",
    "private",
    "protected",
    "internal",
    "static",
    "abstract",
    "sealed",
    "virtual",
    "override",
    "extern",
    "readonly",
    "volatile",
    "unsafe",
    "new",
    "partial",
    "async",
    "const",
    "required",
    "file",
];

/// Every location an attribute can be aimed at, in the order Roslyn lists
/// them.
const ATTRIBUTE_LOCATIONS: [&str; 10] = [
    "assembly", "module", "type", "method", "field", "property", "event", "param", "return",
    "typevar",
];

/// Where an attribute on this declaration may be aimed, or `None` where
/// that is not certain enough to warn about.
fn attribute_locations(declaration: &SyntaxNode) -> Option<Vec<&'static str>> {
    let has_parameters = || {
        declaration
            .child_of_kind(SyntaxKind::ParameterList)
            .is_some()
    };
    Some(match declaration.kind() {
        SyntaxKind::CompilationUnit => vec!["assembly", "module"],
        SyntaxKind::ClassDeclaration
        | SyntaxKind::StructDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::RecordDeclaration
        | SyntaxKind::RecordStructDeclaration => {
            // A primary constructor is a method the type's attributes may
            // be aimed at.
            if has_parameters() {
                vec!["type", "method"]
            } else {
                vec!["type"]
            }
        }
        SyntaxKind::EnumDeclaration => vec!["type"],
        SyntaxKind::DelegateDeclaration => vec!["type", "return"],
        SyntaxKind::MethodDeclaration
        | SyntaxKind::OperatorDeclaration
        | SyntaxKind::ConversionOperatorDeclaration
        | SyntaxKind::LocalFunctionStatement
        | SyntaxKind::GetAccessorDeclaration => vec!["method", "return"],
        SyntaxKind::SetAccessorDeclaration | SyntaxKind::InitAccessorDeclaration => {
            vec!["method", "param", "return"]
        }
        SyntaxKind::ConstructorDeclaration | SyntaxKind::DestructorDeclaration => {
            vec!["method"]
        }
        SyntaxKind::FieldDeclaration | SyntaxKind::EnumMemberDeclaration => vec!["field"],
        SyntaxKind::EventFieldDeclaration => vec!["method", "field", "event"],
        SyntaxKind::EventDeclaration => vec!["event"],
        SyntaxKind::IndexerDeclaration => vec!["property"],
        SyntaxKind::TypeParameter => vec!["typevar"],
        _ => return None,
    })
}

fn is_virtual(modifiers: Modifiers) -> bool {
    if modifiers.contains(Modifiers::SEALED) {
        return false;
    }
    modifiers.contains(Modifiers::VIRTUAL)
        || modifiers.contains(Modifiers::ABSTRACT)
        || modifiers.contains(Modifiers::OVERRIDE)
}

/// A member's modifiers, where a property read from metadata carries them on
/// its accessors rather than on itself.
fn effective_modifiers(compilation: &Compilation, member: SymbolId) -> Modifiers {
    let symbols = compilation.symbols();
    let symbol = symbols.get(member);
    let mut modifiers = symbol.modifiers;
    if compilation.is_from_metadata(member) {
        let accessors = match &symbol.detail {
            Detail::Property(detail) => vec![detail.getter, detail.setter],
            Detail::Event(detail) => vec![detail.adder, detail.remover],
            _ => Vec::new(),
        };
        for accessor in accessors.into_iter().flatten() {
            modifiers.insert(symbols.get(accessor).modifiers);
        }
    }
    modifiers
}

fn effective_accessibility(compilation: &Compilation, member: SymbolId) -> Accessibility {
    let symbols = compilation.symbols();
    let symbol = symbols.get(member);
    if symbol.accessibility != Accessibility::NotApplicable {
        return symbol.accessibility;
    }
    let accessors = match &symbol.detail {
        Detail::Property(detail) => vec![detail.getter, detail.setter],
        Detail::Event(detail) => vec![detail.adder, detail.remover],
        _ => Vec::new(),
    };
    accessors
        .into_iter()
        .flatten()
        .map(|accessor| symbols.get(accessor).accessibility)
        .max()
        .unwrap_or(Accessibility::Public)
}

/// Whether the text in front of an explicit implementation's name names
/// this interface: `IEnumerable<T>.` and `System.IDisposable.` both end in
/// the interface's own name, arguments aside.
fn names_interface(prefix: &str, interface: &str) -> bool {
    // `Outer<T>.Inner<int>.I<long>` names `I`: every argument list goes,
    // not only the first.
    let mut depth = 0usize;
    let without_arguments: String = prefix
        .chars()
        .filter(|c| {
            match c {
                '<' => depth += 1,
                '>' => {
                    depth = depth.saturating_sub(1);
                    return false;
                }
                _ => {}
            }
            depth == 0
        })
        .collect();
    let last = without_arguments
        .rsplit(['.', ':'])
        .next()
        .unwrap_or(&without_arguments)
        .trim();
    last == interface
}

/// Names a property or event accessor goes by in metadata, which a method
/// beside a field of the same name would be mistaken for.
fn accessor_like(name: &str) -> bool {
    ["get_", "set_", "add_", "remove_"]
        .iter()
        .any(|prefix| name.starts_with(prefix))
}

fn in_extension_block(compilation: &Compilation, member: SymbolId) -> bool {
    compilation.declaration_node(member).is_some_and(|node| {
        node.ancestors()
            .any(|ancestor| ancestor.kind() == SyntaxKind::ExtensionBlockDeclaration)
    })
}

/// A type as a diagnostic names it: `C<T>` for a generic one.
fn type_display(compilation: &Compilation, ty: SymbolId) -> String {
    compilation.symbols().get(ty).as_named_type().map_or_else(
        || compilation.symbols().get(ty).name.clone(),
        |_| {
            let own = crate::binder::Binder::new(compilation).self_type(ty);
            own.display(compilation.symbols())
        },
    )
}

/// A member as a diagnostic names it: `B<int>.M(int, ref string)`, with the
/// type it belongs to read through `frame`.
pub(crate) fn member_display(
    compilation: &Compilation,
    member: SymbolId,
    frame: &Frame,
    owner: Option<&str>,
) -> String {
    let symbols = compilation.symbols();
    let binder = Binder::new(compilation);
    let symbol = symbols.get(member);
    let owner = owner.map(str::to_string).or_else(|| {
        symbol.container.map(|container| {
            if symbols.get(container).kind == SymbolKind::NamedType {
                binder
                    .self_type(container)
                    .substitute(frame)
                    .display(symbols)
            } else {
                symbols.get(container).name.clone()
            }
        })
    });
    let parameters = |list: &[SymbolId]| {
        let mut sink = Diagnostics::new();
        list.iter()
            .map(|parameter| {
                let detail = symbols.get(*parameter).as_parameter();
                let prefix = match detail.map(|detail| detail.ref_kind) {
                    Some(RefKind::Ref) => "ref ",
                    Some(RefKind::Out) => "out ",
                    Some(RefKind::In) => "in ",
                    _ if detail.is_some_and(|detail| detail.is_params) => "params ",
                    _ => "",
                };
                let ty = binder.type_of(*parameter, &mut sink);
                format!("{prefix}{}", ty.value().substitute(frame).display(symbols))
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    let name = match &symbol.detail {
        Detail::Method(detail) => {
            let name = match detail.method_kind {
                MethodKind::Constructor | MethodKind::StaticConstructor => {
                    symbol.container.map_or_else(
                        || symbol.name.clone(),
                        |container| symbols.get(container).name.clone(),
                    )
                }
                _ => symbol.name.clone(),
            };
            let type_parameters = if detail.type_parameters.is_empty() {
                String::new()
            } else {
                let names: Vec<_> = detail
                    .type_parameters
                    .iter()
                    .map(|parameter| symbols.get(*parameter).name.clone())
                    .collect();
                format!("<{}>", names.join(", "))
            };
            format!(
                "{name}{type_parameters}({})",
                parameters(&detail.parameters)
            )
        }
        Detail::Property(detail) if detail.is_indexer || symbol.name == "this[]" => {
            format!("this[{}]", parameters(&detail.parameters))
        }
        _ => symbol.name.clone(),
    };
    match owner {
        Some(owner) if !owner.is_empty() => format!("{owner}.{name}"),
        _ => name,
    }
}

/// The modifiers a declaration can be written with, one bit each, and the
/// order Roslyn goes through them in when it says which are wrong.
mod modifier {
    pub(super) const ABSTRACT: u32 = 1 << 0;
    pub(super) const SEALED: u32 = 1 << 1;
    pub(super) const STATIC: u32 = 1 << 2;
    pub(super) const NEW: u32 = 1 << 3;
    pub(super) const PUBLIC: u32 = 1 << 4;
    pub(super) const PROTECTED: u32 = 1 << 5;
    pub(super) const INTERNAL: u32 = 1 << 6;
    pub(super) const PRIVATE: u32 = 1 << 8;
    pub(super) const EXTERN: u32 = 1 << 9;
    pub(super) const READONLY: u32 = 1 << 10;
    pub(super) const VOLATILE: u32 = 1 << 11;
    pub(super) const UNSAFE: u32 = 1 << 12;
    pub(super) const PARTIAL: u32 = 1 << 13;
    pub(super) const VIRTUAL: u32 = 1 << 14;
    pub(super) const OVERRIDE: u32 = 1 << 15;
    pub(super) const CONST: u32 = 1 << 17;
    pub(super) const FIXED: u32 = 1 << 18;
    pub(super) const ASYNC: u32 = 1 << 20;
    pub(super) const REF: u32 = 1 << 21;
    pub(super) const REQUIRED: u32 = 1 << 23;
    pub(super) const SCOPED: u32 = 1 << 24;
    pub(super) const FILE: u32 = 1 << 25;
    pub(super) const ACCESS: u32 = PUBLIC | PROTECTED | INTERNAL | PRIVATE;

    pub(super) const ORDER: [(u32, &str); 22] = [
        (ABSTRACT, "abstract"),
        (SEALED, "sealed"),
        (STATIC, "static"),
        (NEW, "new"),
        (PUBLIC, "public"),
        (PROTECTED, "protected"),
        (INTERNAL, "internal"),
        (PRIVATE, "private"),
        (EXTERN, "extern"),
        (READONLY, "readonly"),
        (VOLATILE, "volatile"),
        (UNSAFE, "unsafe"),
        (PARTIAL, "partial"),
        (VIRTUAL, "virtual"),
        (OVERRIDE, "override"),
        (CONST, "const"),
        (FIXED, "fixed"),
        (ASYNC, "async"),
        (REF, "ref"),
        (REQUIRED, "required"),
        (SCOPED, "scoped"),
        (FILE, "file"),
    ];
}

/// The bit of a modifier word, `0` for a word that is none.
fn modifier_flag(text: &str) -> u32 {
    modifier::ORDER
        .iter()
        .find(|(_, word)| *word == text)
        .map_or(0, |(flag, _)| *flag)
}

/// The modifier words written in front of a declaration: the tokens after
/// its attributes and before the first thing that is not a modifier.
fn modifier_tokens(declaration: &SyntaxNode) -> Vec<rustlyn_syntax::SyntaxToken> {
    let mut tokens = Vec::new();
    for element in declaration.children_with_tokens() {
        match element {
            rustlyn_syntax::SyntaxElement::Node(node)
                if node.kind() == SyntaxKind::AttributeList => {}
            rustlyn_syntax::SyntaxElement::Token(token)
                if modifier_flag(token.text()) != 0 && !token.span().is_empty() =>
            {
                tokens.push(token);
            }
            _ => break,
        }
    }
    tokens
}

/// What a declaration may be written with, and where Roslyn says it when
/// it was written with something else.
struct ModifierRule {
    allowed: u32,
    is_type: bool,
    in_interface: bool,
    at: Vec<rustlyn_text::TextSpan>,
}

/// The rule for a declaration, from what it is and what it is declared in;
/// `None` for anything this check leaves alone.
fn modifier_rule(declaration: &SyntaxNode) -> Option<ModifierRule> {
    use modifier::*;
    let container = declaration.parent()?;
    let container_kind = container.kind();
    let in_interface = container_kind == SyntaxKind::InterfaceDeclaration;
    // A member of an `extension` block extends another type: it cannot be
    // `new`, `virtual`, `abstract`, `sealed` or `override`, and is `static`
    // or not as the block's receiver says.
    let in_extension = container_kind == SyntaxKind::ExtensionBlockDeclaration;
    let in_struct = matches!(
        container_kind,
        SyntaxKind::StructDeclaration | SyntaxKind::RecordStructDeclaration
    );
    let in_type = in_extension
        || matches!(
            container_kind,
            SyntaxKind::ClassDeclaration
                | SyntaxKind::StructDeclaration
                | SyntaxKind::InterfaceDeclaration
                | SyntaxKind::RecordDeclaration
                | SyntaxKind::RecordStructDeclaration
        );
    let explicit = declaration
        .children()
        .any(|child| child.kind() == SyntaxKind::ExplicitInterfaceSpecifier);
    let identifier = || {
        declaration
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| token.span())
    };
    let struct_readonly = if in_struct { READONLY } else { 0 };
    let kind = declaration.kind();
    let (allowed, at) = match kind {
        SyntaxKind::MethodDeclaration if in_type => {
            let mut allowed = PARTIAL | UNSAFE | ASYNC | EXTERN | struct_readonly;
            if explicit {
                allowed |= STATIC | if in_interface { ABSTRACT } else { 0 };
            } else {
                allowed |= STATIC | ACCESS;
                if !in_extension {
                    allowed |= NEW | SEALED | ABSTRACT | VIRTUAL;
                    if !in_interface {
                        allowed |= OVERRIDE;
                    }
                }
            }
            (allowed, vec![identifier()?])
        }
        SyntaxKind::PropertyDeclaration | SyntaxKind::IndexerDeclaration if in_type => {
            let indexer = kind == SyntaxKind::IndexerDeclaration;
            let mut allowed = PARTIAL | UNSAFE | EXTERN | struct_readonly;
            if explicit {
                if in_interface {
                    allowed |= ABSTRACT;
                }
                if !indexer {
                    allowed |= STATIC;
                }
            } else {
                allowed |= ACCESS;
                if !in_extension {
                    allowed |= NEW | SEALED | ABSTRACT | VIRTUAL;
                }
                if !indexer {
                    allowed |= STATIC;
                }
                if !in_interface && !in_extension {
                    allowed |= OVERRIDE;
                    if !indexer {
                        allowed |= REQUIRED;
                    }
                }
            }
            let at = if indexer {
                declaration
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::ThisKeyword)
                    .map(|token| token.span())?
            } else {
                identifier()?
            };
            (allowed, vec![at])
        }
        SyntaxKind::EventDeclaration | SyntaxKind::EventFieldDeclaration
            if in_type && !in_extension =>
        {
            let mut allowed = PARTIAL | UNSAFE | struct_readonly;
            if explicit {
                allowed |= STATIC | if in_interface { ABSTRACT } else { 0 };
            } else {
                allowed |= NEW | SEALED | ABSTRACT | STATIC | VIRTUAL | ACCESS;
                allowed |= if in_interface { EXTERN } else { OVERRIDE };
            }
            if !in_interface {
                allowed |= EXTERN;
            }
            // A field-like event is a symbol per name, and each says it.
            let at = if kind == SyntaxKind::EventFieldDeclaration {
                declaration
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
                    .filter_map(|declarator| {
                        declarator
                            .child_tokens()
                            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                            .map(|token| token.span())
                    })
                    .collect()
            } else {
                vec![identifier()?]
            };
            (allowed, at)
        }
        SyntaxKind::FieldDeclaration if in_type && !in_extension => {
            let mut allowed = ACCESS
                | CONST
                | NEW
                | READONLY
                | STATIC
                | VOLATILE
                | FIXED
                | UNSAFE
                | ABSTRACT
                | REQUIRED;
            // A fixed-size buffer is an instance's storage, and it is
            // written to in place.
            if declaration
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::FixedKeyword)
            {
                allowed &= !(READONLY | STATIC | VOLATILE | CONST);
            }
            // One symbol per declaration as far as modifiers go: said once,
            // at the first name.
            let first = declaration
                .descendants()
                .find(|node| node.kind() == SyntaxKind::VariableDeclarator)?
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)?
                .span();
            (allowed, vec![first])
        }
        SyntaxKind::GetAccessorDeclaration
        | SyntaxKind::SetAccessorDeclaration
        | SyntaxKind::InitAccessorDeclaration => {
            let property = container.parent()?;
            let owner = property.parent()?.kind();
            if !matches!(
                owner,
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::StructDeclaration
                    | SyntaxKind::InterfaceDeclaration
                    | SyntaxKind::RecordDeclaration
                    | SyntaxKind::RecordStructDeclaration
                    | SyntaxKind::ExtensionBlockDeclaration
            ) {
                return None;
            }
            let explicit = property
                .children()
                .any(|child| child.kind() == SyntaxKind::ExplicitInterfaceSpecifier);
            let mut allowed = UNSAFE;
            if !explicit {
                allowed |= ACCESS;
            }
            if matches!(
                owner,
                SyntaxKind::StructDeclaration | SyntaxKind::RecordStructDeclaration
            ) {
                allowed |= READONLY;
            }
            let keyword = declaration.child_tokens().find(|token| {
                matches!(token.text(), "get" | "set" | "init") && !token.span().is_empty()
            })?;
            (allowed, vec![keyword.span()])
        }
        SyntaxKind::ConstructorDeclaration if in_type && !in_extension => {
            let is_static = declaration
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::StaticKeyword);
            let mut allowed = ACCESS | STATIC | EXTERN | UNSAFE;
            if !is_static {
                allowed |= PARTIAL;
            }
            (allowed, vec![identifier()?])
        }
        SyntaxKind::DestructorDeclaration if in_type && !in_extension => {
            (EXTERN | UNSAFE, vec![identifier()?])
        }
        // An `extension` block takes no modifiers at all.
        SyntaxKind::ExtensionBlockDeclaration => {
            let keyword = declaration
                .child_tokens()
                .find(|token| token.text() == "extension")?;
            (0, vec![keyword.span()])
        }
        SyntaxKind::ClassDeclaration
        | SyntaxKind::StructDeclaration
        | SyntaxKind::InterfaceDeclaration
        | SyntaxKind::RecordDeclaration
        | SyntaxKind::RecordStructDeclaration
        | SyntaxKind::EnumDeclaration
        | SyntaxKind::DelegateDeclaration => {
            if in_extension {
                return None;
            }
            let nested = in_type;
            if !nested
                && !matches!(
                    container_kind,
                    SyntaxKind::CompilationUnit
                        | SyntaxKind::NamespaceDeclaration
                        | SyntaxKind::FileScopedNamespaceDeclaration
                )
            {
                return None;
            }
            let mut allowed = ACCESS | FILE;
            if nested {
                allowed |= NEW;
            }
            allowed |= match kind {
                SyntaxKind::ClassDeclaration => PARTIAL | SEALED | ABSTRACT | UNSAFE | STATIC,
                SyntaxKind::RecordDeclaration => {
                    // `record struct` is a struct, however the parser
                    // spells it.
                    if declaration
                        .child_tokens()
                        .any(|token| token.kind() == SyntaxKind::StructKeyword)
                    {
                        PARTIAL | READONLY | UNSAFE
                    } else {
                        PARTIAL | SEALED | ABSTRACT | UNSAFE
                    }
                }
                SyntaxKind::StructDeclaration => PARTIAL | READONLY | UNSAFE | REF,
                SyntaxKind::RecordStructDeclaration => PARTIAL | READONLY | UNSAFE,
                SyntaxKind::InterfaceDeclaration => PARTIAL | UNSAFE,
                SyntaxKind::DelegateDeclaration => UNSAFE,
                _ => 0,
            };
            (allowed, vec![identifier()?])
        }
        _ => return None,
    };
    let is_type = matches!(
        kind,
        SyntaxKind::ExtensionBlockDeclaration
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::DelegateDeclaration
    );
    Some(ModifierRule {
        allowed,
        is_type,
        in_interface,
        at,
    })
}

/// The last value of an integral type: the one an enumerator without a
/// value of its own cannot be one past.
fn max_of_integral(special: crate::corlib::SpecialType) -> Option<i128> {
    use crate::corlib::SpecialType;
    Some(match special {
        SpecialType::SByte => i128::from(i8::MAX),
        SpecialType::Byte => i128::from(u8::MAX),
        SpecialType::Int16 => i128::from(i16::MAX),
        SpecialType::UInt16 => i128::from(u16::MAX),
        SpecialType::Int32 => i128::from(i32::MAX),
        SpecialType::UInt32 => i128::from(u32::MAX),
        SpecialType::Int64 => i128::from(i64::MAX),
        SpecialType::UInt64 => i128::from(u64::MAX),
        _ => return None,
    })
}
