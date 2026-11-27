//! Patterns (§11) and the `switch` expression.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, identifier_text, typeless};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundCaseLabel, BoundExpression, BoundExpressionKind, BoundListPattern, BoundListSlice,
    BoundPattern, BoundPatternKind, BoundRecursivePattern, BoundSwitchArm, BoundSwitchLabel,
    ConstantValue, LocalId,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;
use crate::unions::UnionMembers;

/// What a property pattern's entry turned out to read.
enum ChainEntry {
    /// A member of the type, and the pattern its value is matched against.
    Member(SymbolId, BoundPattern),
    /// A pattern on the matched value itself: what `Value: P` on a union
    /// asks of what the union holds.
    OnSelf(BoundPattern),
}

impl BodyBinder<'_> {
    /// Binds a pattern against the type of the value it will be matched with.
    ///
    /// The input type matters: `int n` against an `int` is a binding with no
    /// test, and against an `object` it is a test as well. The binder records
    /// the type it narrows to and leaves that decision to whoever lowers it.
    /// Whether a name in a pattern names a type rather than a constant.
    pub(super) fn names_a_type(&self, node: &SyntaxNode) -> bool {
        let mut sink = Diagnostics::new();
        !self
            .binder
            .resolve_type(node, &self.context, &mut sink)
            .is_error()
    }

    /// CS9135: what a constant or relational pattern holds has to be a
    /// constant. Said only of what is certainly none: a call, a property, an
    /// element, a parameter or a `readonly` field.
    pub(super) fn require_constant(&mut self, value: &BoundExpression, input: &Type) {
        if value.ty.is_error() || input.is_error() {
            return;
        }
        let symbols = self.binder.compilation().symbols();
        let mut held = value;
        while let BoundExpressionKind::Conversion { operand, .. } = &held.kind {
            held = operand;
        }
        let certain = match &held.kind {
            BoundExpressionKind::Property { .. }
            | BoundExpressionKind::ArrayAccess { .. }
            | BoundExpressionKind::ArrayLength { .. }
            | BoundExpressionKind::IndexerAccess { .. }
            | BoundExpressionKind::Parameter(_) => true,
            BoundExpressionKind::Call { method, .. } => {
                !symbols.get(*method).name.starts_with("op_")
            }
            BoundExpressionKind::Field { field, .. } => {
                let modifiers = symbols.get(*field).modifiers;
                // A `decimal` constant of the framework is a `readonly`
                // field with an attribute that makes it one.
                modifiers.contains(Modifiers::READONLY)
                    && !modifiers.contains(Modifiers::CONST)
                    && self.binder.special_constant(*field).is_none()
            }
            _ => false,
        };
        if certain && self.binder.folded(held).is_none() {
            let shown = self.display(
                &self
                    .binder
                    .nullable_underlying(input)
                    .unwrap_or_else(|| input.clone()),
            );
            self.report(ErrorCode::ErrConstantValueExpected, value.span, &[&shown]);
        }
    }

    /// What a union offers to patterns, where it is one they can look into:
    /// one with no `Value` is an error where it is declared, and a pattern
    /// against it is as against any type.
    fn matchable_union(&self, union: &Type) -> Option<UnionMembers> {
        self.binder
            .union_members(union)
            .filter(|members| members.value.is_some())
    }

    /// The constant of a pattern on a `decimal` (or a `decimal?`), as a
    /// `decimal`: `m is 1` compares the input with `1m`, the constant having
    /// the input's type (§11.2.3), where the other numeric types are
    /// compared as the machine's numbers. A constant that is not implicitly
    /// a `decimal` is left as written, for the check that it is a constant
    /// of the input's type to say so.
    pub(super) fn constant_as_decimal(
        &mut self,
        value: BoundExpression,
        input: &Type,
    ) -> BoundExpression {
        let target = self
            .binder
            .nullable_underlying(input)
            .unwrap_or_else(|| input.clone());
        if self.binder.special_of(&target) != Some(SpecialType::Decimal)
            || value.ty == target
            || value.ty.is_error()
            || self.binder.folded(&value).is_none()
            || self.binder.special_of(&value.ty).is_none()
            || !self.binder.converts_implicitly(&value.ty, &target)
        {
            return value;
        }
        self.convert(value, &target)
    }

    pub(super) fn bind_pattern(&mut self, node: &SyntaxNode, input: &Type) -> BoundPattern {
        // A union — or a `U?` of one — is matched by what it holds (C# 15).
        let (union, nullable) = match self.binder.nullable_underlying(input) {
            Some(inner) => (inner, true),
            None => (input.clone(), false),
        };
        if let Some(members) = self.matchable_union(&union) {
            return self.bind_union_pattern(node, input, &union, nullable, &members);
        }
        self.bind_pattern_plain(node, input)
    }

    /// A pattern against a union (C# 15). What tests a type, a value or a
    /// null applies to the union's contents; `var`, `_`, a list and a
    /// property pattern with no type written apply to the union itself; the
    /// logical ones pass each side on.
    fn bind_union_pattern(
        &mut self,
        node: &SyntaxNode,
        input: &Type,
        union: &Type,
        nullable: bool,
        members: &UnionMembers,
    ) -> BoundPattern {
        let span = node.span();
        let at = |kind| BoundPattern::new(kind, span);
        let children: Vec<SyntaxNode> = node
            .children()
            .filter(|child| child.kind().is_pattern_node())
            .collect();
        match node.kind() {
            SyntaxKind::ParenthesizedPattern if children.len() == 1 => {
                self.bind_union_pattern(&children[0], input, union, nullable, members)
            }
            SyntaxKind::NotPattern if children.len() == 1 => {
                let inner = self.bind_union_pattern(&children[0], input, union, nullable, members);
                at(BoundPatternKind::Not(Box::new(inner)))
            }
            SyntaxKind::OrPattern if children.len() == 2 => {
                let left = self.bind_union_pattern(&children[0], input, union, nullable, members);
                let right = self.bind_union_pattern(&children[1], input, union, nullable, members);
                at(BoundPatternKind::Or(Box::new(left), Box::new(right)))
            }
            // `var pet and Dog`: the left keeps the union, and the right is
            // matched against it in turn. `Dog and { Name: "Rex" }` unwraps
            // on the left, and the right sees what the left narrowed to.
            SyntaxKind::AndPattern => {
                let mut chain = Vec::new();
                and_chain(node, &mut chain);
                self.bind_and_chain(&chain, input, span)
            }
            SyntaxKind::ConstantPattern | SyntaxKind::TypePattern
                if self.is_null_constant(node) =>
            {
                self.union_null_pattern(span, union, nullable, members)
                    .unwrap_or_else(|| self.bind_pattern_plain(node, input))
            }
            _ if self.unwraps(node) => self.union_contents(node, union, nullable, members),
            _ => self.bind_pattern_plain(node, input),
        }
    }

    /// Whether a constant pattern is `null` or a constant that is: `const S1
    /// none = null;`.
    fn is_null_constant(&mut self, node: &SyntaxNode) -> bool {
        // A bare name is a type pattern to the parser, and a constant where
        // it names none.
        let Some(value) = node.children().find(|child| {
            child.kind().is_expression()
                || (node.kind() == SyntaxKind::TypePattern
                    && child.kind().is_type_node()
                    && !self.names_a_type(child))
        }) else {
            return false;
        };
        if value.kind() == SyntaxKind::NullLiteralExpression {
            return true;
        }
        let floor = self.body.diagnostics.len();
        let bound = self.bind_expression(&value);
        self.body.diagnostics.truncate(floor);
        matches!(self.binder.folded(&bound), Some(ConstantValue::Null))
    }

    /// `a and b and c`, each part matched against what the ones before it
    /// established. Against a union, a part that unwraps it takes the rest
    /// of the chain along: `S2 and 10` on an `S1` is `S2` and then `10` on
    /// what the `S1` holds.
    fn bind_and_chain(
        &mut self,
        chain: &[SyntaxNode],
        input: &Type,
        span: TextSpan,
    ) -> BoundPattern {
        let [first, rest @ ..] = chain else {
            return BoundPattern::new(BoundPatternKind::Unsupported(SyntaxKind::AndPattern), span);
        };
        if rest.is_empty() {
            return self.bind_pattern(first, input);
        }
        let (union, nullable) = match self.binder.nullable_underlying(input) {
            Some(inner) => (inner, true),
            None => (input.clone(), false),
        };
        if let Some(members) = self.matchable_union(&union) {
            if self.unwraps(first) {
                let tested = self.tested_type(first);
                return self.union_wrap(tested, &union, nullable, &members, span, |this, ty| {
                    this.bind_and_chain(chain, ty, span)
                });
            }
            let left = self.bind_pattern_plain(first, input);
            let right = self.bind_and_chain(rest, input, span);
            return BoundPattern::new(BoundPatternKind::And(Box::new(left), Box::new(right)), span);
        }
        let left = self.bind_pattern(first, input);
        let narrowed = self.narrowed_by(&left, input);
        let right = self.bind_and_chain(rest, &narrowed, span);
        BoundPattern::new(BoundPatternKind::And(Box::new(left), Box::new(right)), span)
    }

    /// `u is Kind.Red` on a union, where the name is a constant: the
    /// constant pattern against what it holds.
    pub(super) fn union_constant_test(
        &mut self,
        input: &Type,
        value: BoundExpression,
        span: TextSpan,
    ) -> Result<BoundPattern, Box<BoundExpression>> {
        let (union, nullable) = match self.binder.nullable_underlying(input) {
            Some(inner) => (inner, true),
            None => (input.clone(), false),
        };
        let Some(members) = self.matchable_union(&union) else {
            return Err(Box::new(value));
        };
        if matches!(self.binder.folded(&value), Some(ConstantValue::Null)) {
            return self
                .union_null_pattern(span, &union, nullable, &members)
                .ok_or_else(|| Box::new(value));
        }
        let tested =
            (!value.ty.is_error() && !matches!(value.ty, Type::Null)).then(|| value.ty.clone());
        Ok(
            self.union_wrap(tested, &union, nullable, &members, span, |_, _| {
                BoundPattern::new(BoundPatternKind::Constant(value), span)
            }),
        )
    }

    /// Whether a pattern against a union applies to what it holds.
    fn unwraps(&self, node: &SyntaxNode) -> bool {
        match node.kind() {
            SyntaxKind::ConstantPattern
            | SyntaxKind::RelationalPattern
            | SyntaxKind::TypePattern
            | SyntaxKind::DeclarationPattern => true,
            SyntaxKind::RecursivePattern => node
                .children()
                .find(|child| child.kind().is_type_node())
                .is_some_and(|written| self.names_a_type(&written)),
            SyntaxKind::ParenthesizedPattern | SyntaxKind::AndPattern => node
                .children()
                .find(|child| child.kind().is_pattern_node())
                .is_some_and(|first| self.unwraps(&first)),
            _ => false,
        }
    }

    /// The type a pattern that unwraps a union tests for, where one can be
    /// read off it without binding it: what decides which `TryGetValue`
    /// gives the contents.
    fn tested_type(&mut self, node: &SyntaxNode) -> Option<Type> {
        match node.kind() {
            SyntaxKind::TypePattern
            | SyntaxKind::DeclarationPattern
            | SyntaxKind::RecursivePattern => {
                let written = node.children().find(|child| child.kind().is_type_node())?;
                self.names_a_type(&written).then(|| self.resolve(&written))
            }
            SyntaxKind::ParenthesizedPattern | SyntaxKind::AndPattern => {
                let first = node
                    .children()
                    .find(|child| child.kind().is_pattern_node())?;
                self.tested_type(&first)
            }
            // `10` and `> 10` test for the constant's type. The value is
            // bound again with the pattern, so nothing said here is kept.
            SyntaxKind::ConstantPattern | SyntaxKind::RelationalPattern => {
                let value = node.children().find(|child| child.kind().is_expression())?;
                let floor = self.body.diagnostics.len();
                let bound = self.bind_expression(&value);
                self.body.diagnostics.truncate(floor);
                (!bound.ty.is_error() && !matches!(bound.ty, Type::Null)).then_some(bound.ty)
            }
            _ => None,
        }
    }

    /// A pattern applied to a union's contents: through the `TryGetValue`
    /// whose type the tested one reaches without a conversion of its own —
    /// by identity first, then by reference, then by boxing — and otherwise
    /// through `Value`.
    fn union_contents(
        &mut self,
        node: &SyntaxNode,
        union: &Type,
        nullable: bool,
        members: &UnionMembers,
    ) -> BoundPattern {
        let tested = self.tested_type(node);
        self.union_wrap(
            tested,
            union,
            nullable,
            members,
            node.span(),
            |this, input| this.bind_pattern(node, input),
        )
    }

    /// `u is T` on a union: the type pattern against what it holds.
    pub(super) fn union_type_test(
        &mut self,
        input: &Type,
        target: &Type,
        span: TextSpan,
    ) -> Option<BoundPattern> {
        let (union, nullable) = match self.binder.nullable_underlying(input) {
            Some(inner) => (inner, true),
            None => (input.clone(), false),
        };
        let members = self.matchable_union(&union)?;
        Some(self.union_wrap(
            Some(target.clone()),
            &union,
            nullable,
            &members,
            span,
            |_, _| BoundPattern::new(BoundPatternKind::Type(target.clone()), span),
        ))
    }

    /// A pattern bound by `inner` against a union's contents: through the
    /// `TryGetValue` whose type the tested one reaches without a conversion
    /// of its own — by identity first, then by reference, then by boxing —
    /// and otherwise through `Value`.
    fn union_wrap(
        &mut self,
        tested: Option<Type>,
        union: &Type,
        nullable: bool,
        members: &UnionMembers,
        span: TextSpan,
        inner: impl FnOnce(&mut Self, &Type) -> BoundPattern,
    ) -> BoundPattern {
        if let Some(tested) = tested {
            let symbols = self.binder.compilation().symbols();
            let rank = |target: &Type| -> Option<u8> {
                if *target == tested {
                    Some(0)
                } else if self.binder.nullable_underlying(target).as_ref() == Some(&tested) {
                    // `int` into `int?` keeps the value as it is.
                    Some(1)
                } else if !self.binder.converts_implicitly(&tested, target)
                    || !target.is_reference_type(symbols)
                {
                    None
                } else if self.binder.held_by_reference(&tested) {
                    Some(1)
                } else {
                    Some(2)
                }
            };
            let chosen = members
                .try_get_values
                .iter()
                .filter_map(|(method, ty)| rank(ty).map(|rank| (rank, *method, ty.clone())))
                .min_by_key(|(rank, _, _)| *rank);
            if let Some((_, method, ty)) = chosen {
                let inner = inner(self, &ty);
                return BoundPattern::new(
                    BoundPatternKind::UnionCase {
                        try_get_value: method,
                        ty,
                        inner: Box::new(inner),
                    },
                    span,
                );
            }
        }
        let Some(value) = members.value else {
            return inner(self, union);
        };
        let value_type = self.special(SpecialType::Object);
        let inner = inner(self, &value_type);
        self.union_property_pattern(value, inner, union, nullable, span)
    }

    /// `{ Value: inner }` against a union, or against the `U?` around one.
    fn union_property_pattern(
        &self,
        member: SymbolId,
        inner: BoundPattern,
        union: &Type,
        nullable: bool,
        span: TextSpan,
    ) -> BoundPattern {
        BoundPattern::new(
            BoundPatternKind::Recursive(Box::new(BoundRecursivePattern {
                ty: nullable.then(|| union.clone()),
                properties: vec![(member, inner)],
                deconstruct: None,
                positional: Vec::new(),
                local: None,
            })),
            span,
        )
    }

    /// `null` against a union: its contents are null, which `HasValue`
    /// says where there is one and `Value` otherwise — or the union itself
    /// is, where it is a class or a `U?`.
    fn union_null_pattern(
        &mut self,
        span: TextSpan,
        union: &Type,
        nullable: bool,
        members: &UnionMembers,
    ) -> Option<BoundPattern> {
        let symbols = self.binder.compilation().symbols();
        let itself_null = nullable || union.is_reference_type(symbols);
        let null = BoundPattern::new(
            BoundPatternKind::Constant(BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Null),
                Type::Null,
                span,
            )),
            span,
        );
        let contents = match (members.has_value, members.value) {
            (Some(has_value), _) => {
                let boolean = self.special(SpecialType::Boolean);
                let no = BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Boolean(false)),
                    boolean,
                    span,
                );
                let inner = BoundPattern::new(BoundPatternKind::Constant(no), span);
                self.union_property_pattern(has_value, inner, union, nullable, span)
            }
            (None, Some(value)) => {
                self.union_property_pattern(value, null.clone(), union, nullable, span)
            }
            (None, None) => return None,
        };
        Some(if itself_null {
            BoundPattern::new(
                BoundPatternKind::Or(Box::new(null), Box::new(contents)),
                span,
            )
        } else {
            contents
        })
    }

    fn bind_pattern_plain(&mut self, node: &SyntaxNode, input: &Type) -> BoundPattern {
        let span = node.span();
        let at = |kind| BoundPattern::new(kind, span);
        match node.kind() {
            SyntaxKind::DiscardPattern => at(BoundPatternKind::Discard),
            SyntaxKind::ParenthesizedPattern => {
                match node.children().find(|child| child.kind().is_pattern_node()) {
                    Some(inner) => self.bind_pattern(&inner, input),
                    None => at(BoundPatternKind::Unsupported(node.kind())),
                }
            }
            SyntaxKind::ConstantPattern => match node.children().next() {
                Some(value) => {
                    let value = self.bind_expression(&value);
                    // `x is new()` makes one of what is being matched.
                    let value = if matches!(value.kind, BoundExpressionKind::UnboundCreation(_)) {
                        self.convert(value, input)
                    } else {
                        value
                    };
                    self.require_constant(&value, input);
                    let value = self.constant_as_decimal(value, input);
                    match self.span_string_test(&value, input, span) {
                        Some(test) => at(test),
                        None => at(BoundPatternKind::Constant(value)),
                    }
                }
                None => at(BoundPatternKind::Unsupported(node.kind())),
            },
            SyntaxKind::RelationalPattern => {
                let operator = node
                    .child_tokens()
                    .next()
                    .and_then(|token| relational_operator(token.kind()));
                let value = node
                    .children()
                    .next()
                    .map(|value| self.bind_expression(&value));
                match (operator, value) {
                    (Some(operator), Some(value)) => {
                        self.require_constant(&value, input);
                        let value = self.constant_as_decimal(value, input);
                        at(BoundPatternKind::Relational { operator, value })
                    }
                    _ => at(BoundPatternKind::Unsupported(node.kind())),
                }
            }
            SyntaxKind::TypePattern => {
                let Some(written) = node.children().find(|child| child.kind().is_type_node())
                else {
                    return at(BoundPatternKind::Unsupported(node.kind()));
                };
                // `Code.A` and `IDisposable` are the same syntax, and only
                // what the name means tells them apart: the parser cannot, and
                // C# says a name that is not a type is a constant.
                if !self.names_a_type(&written) {
                    let value = self.bind_expression(&written);
                    self.require_constant(&value, input);
                    let value = self.constant_as_decimal(value, input);
                    return at(BoundPatternKind::Constant(value));
                }
                let ty = self.resolve(&written);
                at(BoundPatternKind::Type(ty))
            }
            SyntaxKind::DeclarationPattern => {
                let ty = node
                    .children()
                    .find(|child| child.kind().is_type_node())
                    .map_or(Type::Error, |ty| self.resolve(&ty));
                let local = self.declare_designation(node, &ty);
                at(BoundPatternKind::Declaration { ty, local })
            }
            // `x is var (a, b)` takes the value apart exactly as a
            // deconstruction does, and always matches.
            SyntaxKind::VarPattern
                if node
                    .child_of_kind(SyntaxKind::ParenthesizedVariableDesignation)
                    .is_some() =>
            {
                // On a `T?` it takes the `T` apart: reaching the designation
                // has already established that there is one.
                let matched = self
                    .binder
                    .nullable_underlying(input)
                    .unwrap_or_else(|| input.clone());
                // `c is var ()` takes nothing out: it is `c is ()`, which
                // asks that there be a `c` and calls its `Deconstruct()`.
                let empty = node
                    .child_of_kind(SyntaxKind::ParenthesizedVariableDesignation)
                    .is_some_and(|designation| {
                        !designation.children().any(|part| {
                            matches!(
                                part.kind(),
                                SyntaxKind::SingleVariableDesignation
                                    | SyntaxKind::DiscardDesignation
                                    | SyntaxKind::ParenthesizedVariableDesignation
                            )
                        })
                    });
                if empty {
                    let deconstruct = self.find_deconstruct(&matched, 0).map(|found| found.method);
                    return at(BoundPatternKind::Recursive(Box::new(
                        BoundRecursivePattern {
                            ty: None,
                            properties: Vec::new(),
                            deconstruct,
                            positional: Vec::new(),
                            local: None,
                        },
                    )));
                }
                let local = self.declare_synthetic_local("matched", matched.clone());
                let value = BoundExpression::new(
                    BoundExpressionKind::Local(local),
                    matched.clone(),
                    node.span(),
                );
                match self.deconstruct_into(node, value, node.span()) {
                    Some(deconstruction) => at(BoundPatternKind::VarDeconstruct {
                        ty: matched,
                        local,
                        deconstruction: Box::new(deconstruction),
                    }),
                    None => at(BoundPatternKind::Unsupported(node.kind())),
                }
            }
            SyntaxKind::VarPattern => {
                // `var x` takes the type of whatever it is matched against.
                match self.declare_designation(node, input) {
                    Some(local) => at(BoundPatternKind::Var { local }),
                    None => at(BoundPatternKind::Discard),
                }
            }
            SyntaxKind::AndPattern => {
                let mut chain = Vec::new();
                and_chain(node, &mut chain);
                self.bind_and_chain(&chain, input, span)
            }
            SyntaxKind::OrPattern => {
                let mut parts = node
                    .children()
                    .filter(|child| child.kind().is_pattern_node());
                let left = parts.next().map(|left| self.bind_pattern(&left, input));
                // What the left of an `and` has established is what the right
                // is matched against: after `> 0` on an `int?` there is an
                // `int`, and `var length` is one (§12.4.? narrowing).
                let narrowed = match (&left, node.kind()) {
                    (Some(left), SyntaxKind::AndPattern) => self.narrowed_by(left, input),
                    _ => input.clone(),
                };
                let right = parts
                    .next()
                    .map(|right| self.bind_pattern(&right, &narrowed));
                match (left, right) {
                    (Some(left), Some(right)) => {
                        let (left, right) = (Box::new(left), Box::new(right));
                        at(if node.kind() == SyntaxKind::AndPattern {
                            BoundPatternKind::And(left, right)
                        } else {
                            BoundPatternKind::Or(left, right)
                        })
                    }
                    _ => at(BoundPatternKind::Unsupported(node.kind())),
                }
            }
            SyntaxKind::NotPattern => {
                match node.children().find(|child| child.kind().is_pattern_node()) {
                    Some(inner) => {
                        let inner = self.bind_pattern(&inner, input);
                        at(BoundPatternKind::Not(Box::new(inner)))
                    }
                    None => at(BoundPatternKind::Unsupported(node.kind())),
                }
            }
            SyntaxKind::RecursivePattern => self.bind_recursive_pattern(node, input),
            SyntaxKind::ListPattern => self.bind_list_pattern(node, input),
            _ => {
                // List and slice patterns are not modelled yet; their
                // variables are still declared so that the names inside them
                // resolve.
                self.declare_pattern_variables(node);
                at(BoundPatternKind::Unsupported(node.kind()))
            }
        }
    }

    /// `v is [1, var x, ..]`: how many elements there are, and what each one
    /// has to be.
    ///
    /// An array says its length with an instruction and is indexed with one;
    /// anything else has to have a `Length` or a `Count` and an indexer:
    /// one taking an `Index`, or else one taking an `int`, which is the
    /// implicit support C# 11 gives a countable type (§12.21.4). A `..`
    /// with a pattern in it cuts the slice out — `GetSubArray` on an array,
    /// an indexer taking a `Range`, or else `Slice(start, length)`
    /// (`Substring` on a string) — and matches the pattern against that.
    fn bind_list_pattern(&mut self, node: &SyntaxNode, input: &Type) -> BoundPattern {
        let span = node.span();
        let at = |kind| BoundPattern::new(kind, span);
        let matched = self
            .binder
            .nullable_underlying(input)
            .unwrap_or_else(|| input.clone());
        let index_type = self.framework_type("System.Index");
        let (length, indexer, element, by_index) = match &matched {
            Type::Array { element, rank } if *rank == 1 => (None, None, (**element).clone(), false),
            other => {
                let Some(symbol) = other.symbol() else {
                    self.declare_pattern_variables(node);
                    return at(BoundPatternKind::Unsupported(node.kind()));
                };
                let count = ["Length", "Count"]
                    .into_iter()
                    .find_map(|name| self.binder.lookup_member(symbol, name).first().copied());
                let real = index_type.as_ref().and_then(|index| {
                    self.binder
                        .lookup_member(symbol, "this[]")
                        .into_iter()
                        .find(|member| self.takes_one(*member, index))
                });
                let indexer = real.or_else(|| {
                    ["this[]", "get_Item"].into_iter().find_map(|name| {
                        self.binder
                            .lookup_member(symbol, name)
                            .into_iter()
                            .find(|member| self.takes_one_int(*member))
                    })
                });
                let (Some(count), Some(indexer)) = (count, indexer) else {
                    self.declare_pattern_variables(node);
                    return at(BoundPatternKind::Unsupported(node.kind()));
                };
                let element = self.member_type(indexer, other);
                (Some(count), Some(indexer), element, real.is_some())
            }
        };

        let mut before = Vec::new();
        let mut after = Vec::new();
        let mut slice = false;
        let mut sliced = None;
        for child in node.children() {
            if child.kind() == SyntaxKind::SlicePattern {
                slice = true;
                // `.. _` matches whatever is there without cutting it out.
                sliced = child.children().find(|inner| {
                    inner.kind().is_pattern_node() && inner.kind() != SyntaxKind::DiscardPattern
                });
                continue;
            }
            if !child.kind().is_pattern_node() {
                continue;
            }
            let bound = self.bind_pattern(&child, &element);
            if slice {
                after.push(bound);
            } else {
                before.push(bound);
            }
        }
        let indexes = match (by_index, &index_type) {
            (true, Some(index)) => {
                let written = before.len();
                let mut indexes = Vec::new();
                for at in 0..written {
                    indexes.push(self.index_value(index, at, false, span));
                }
                for back in (1..=after.len()).rev() {
                    indexes.push(self.index_value(index, back, true, span));
                }
                indexes
            }
            _ => Vec::new(),
        };
        let slice_pattern = match sliced {
            Some(inner) => {
                match self.list_slice(&matched, &element, before.len(), after.len(), span) {
                    Some((list, count, value)) => {
                        let pattern = self.bind_pattern(&inner, &value.ty);
                        Some(Box::new(BoundListSlice {
                            list,
                            count,
                            value,
                            pattern,
                        }))
                    }
                    None => {
                        self.declare_pattern_variables(&inner);
                        return at(BoundPatternKind::Unsupported(SyntaxKind::SlicePattern));
                    }
                }
            }
            None => None,
        };
        let local = self.declare_designation(node, &matched);
        at(BoundPatternKind::List(Box::new(BoundListPattern {
            length,
            indexer,
            matched,
            element,
            before,
            after,
            slice,
            indexes,
            slice_pattern,
            local,
        })))
    }

    /// `span is "str"` on a `Span<char>` or a `ReadOnlySpan<char>` (C# 11):
    /// what the characters are is compared, with
    /// `MemoryExtensions.SequenceEqual(span, "str".AsSpan())`, as Roslyn
    /// lowers it. `None` for any other input or constant.
    pub(super) fn span_string_test(
        &mut self,
        value: &BoundExpression,
        input: &Type,
        span: TextSpan,
    ) -> Option<BoundPatternKind> {
        let Some(ConstantValue::String(_)) = self.binder.folded(value) else {
            return None;
        };
        let Type::Named {
            symbol,
            type_arguments,
        } = input
        else {
            return None;
        };
        let character = self.special(SpecialType::Char);
        let name = self.binder.compilation().symbols().qualified_name(*symbol);
        if !matches!(name.as_str(), "System.Span`1" | "System.ReadOnlySpan`1")
            || type_arguments[..] != [character.clone()]
        {
            return None;
        }
        let extensions = self.framework_type("System.MemoryExtensions")?;
        let local = self.declare_synthetic_local("span", input.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(local), input.clone(), span);
        let text = self.call_static_with(&extensions, "AsSpan", vec![value.clone()], &[], span)?;
        let test = self.call_static_with(
            &extensions,
            "SequenceEqual",
            vec![read, text],
            &[character],
            span,
        )?;
        Some(BoundPatternKind::SpanString {
            local,
            test: Box::new(test),
        })
    }

    /// `new Index(value, fromEnd)`, a constant position of a list pattern.
    fn index_value(
        &mut self,
        index: &Type,
        value: usize,
        from_end: bool,
        span: TextSpan,
    ) -> BoundExpression {
        let int = self.special(SpecialType::Int32);
        let boolean = self.special(SpecialType::Boolean);
        let arguments = vec![
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(value as i32)),
                int,
                span,
            ),
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Boolean(from_end)),
                boolean,
                span,
            ),
        ];
        self.make(index, arguments, span)
            .unwrap_or_else(|| BoundExpression::error(span))
    }

    /// What `..` cuts out of a list with `start` elements listed before it
    /// and `end` after: the locals it is cut from (the list and its count)
    /// and the expression that cuts it, or `None` where the type has no way
    /// to be sliced.
    fn list_slice(
        &mut self,
        matched: &Type,
        element: &Type,
        start: usize,
        end: usize,
        span: TextSpan,
    ) -> Option<(LocalId, LocalId, BoundExpression)> {
        let int = self.special(SpecialType::Int32);
        let list = self.declare_synthetic_local("list", matched.clone());
        let count = self.declare_synthetic_local("count", int.clone());
        let read_list =
            BoundExpression::new(BoundExpressionKind::Local(list), matched.clone(), span);
        let range = |this: &mut Self| -> Option<BoundExpression> {
            let range = this.framework_type("System.Range")?;
            let index = this.framework_type("System.Index")?;
            let from = this.index_value(&index, start, false, span);
            let to = this.index_value(&index, end, true, span);
            this.make(&range, vec![from, to], span)
        };
        if let Type::Array { .. } = matched {
            let helpers = self.framework_type("System.Runtime.CompilerServices.RuntimeHelpers")?;
            let range = range(self)?;
            let value = self.call_static_with(
                &helpers,
                "GetSubArray",
                vec![read_list, range],
                std::slice::from_ref(element),
                span,
            )?;
            return Some((list, count, value));
        }
        // A real `this[Range]` first, as for the elements.
        let symbol = matched.symbol()?;
        if let Some(range_type) = self.framework_type("System.Range")
            && let Some(indexer) = self
                .binder
                .lookup_member(symbol, "this[]")
                .into_iter()
                .find(|member| self.takes_one(*member, &range_type))
        {
            let range = range(self)?;
            let ty = self.member_type(indexer, matched);
            let value = BoundExpression::new(
                BoundExpressionKind::IndexerAccess {
                    receiver: Box::new(read_list),
                    indexer,
                    arguments: vec![range],
                },
                ty,
                span,
            );
            return Some((list, count, value));
        }
        // `Slice(start, count - start - end)`, or a string's `Substring`.
        let literal = |value: usize| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(value as i32)),
                int.clone(),
                span,
            )
        };
        let taken = BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Subtract,
                left: Box::new(BoundExpression::new(
                    BoundExpressionKind::Local(count),
                    int.clone(),
                    span,
                )),
                right: Box::new(literal(start + end)),
            },
            int.clone(),
            span,
        );
        let value = self.slice(read_list, literal(start), taken, span)?;
        Some((list, count, value))
    }

    /// Whether a member is an indexer taking one argument of this type.
    fn takes_one(&self, member: SymbolId, wanted: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(member).as_property() else {
            return false;
        };
        let [parameter] = detail.parameters[..] else {
            return false;
        };
        let mut sink = Diagnostics::new();
        self.binder.type_of(parameter, &mut sink) == *wanted
    }

    /// Whether a member is an accessor taking one `int`, which is what a list
    /// pattern indexes with.
    fn takes_one_int(&self, member: SymbolId) -> bool {
        let symbols = self.binder.compilation().symbols();
        // `this[int]` is a property with a parameter, and `get_Item` is the
        // method it reads through; either one answers.
        let parameters = match &symbols.get(member).detail {
            crate::symbol::Detail::Method(detail) => detail.parameters.clone(),
            crate::symbol::Detail::Property(detail) if detail.is_indexer => {
                detail.parameters.clone()
            }
            _ => return false,
        };
        if parameters.len() != 1 {
            return false;
        }
        let mut sink = Diagnostics::new();
        let ty = self.binder.type_of(parameters[0], &mut sink);
        self.binder.special_of(ty.value()) == Some(SpecialType::Int32)
    }

    /// One entry of a property clause: the member it reads and the pattern
    /// its value has to match.    /// One entry of a property clause: the member it reads and the pattern
    /// its value has to match.
    ///
    /// `{ Parent.Width: 1 }` is `{ Parent: { Width: 1 } }` written shorter —
    /// C# 10 calls it an extended property pattern — so a chain of names
    /// becomes a chain of recursive patterns, built from the inside out.
    fn bind_property_chain(
        &mut self,
        names: &[String],
        matched: &Type,
        inner: &SyntaxNode,
        part: &SyntaxNode,
    ) -> Option<ChainEntry> {
        // `{ S1.Value: 1 }` on an `S1?` reads `S1`'s `Value`, as `{ S1: {
        // Value: 1 } }` does: a property pattern on a `T?` is one on its `T`,
        // not on the `Nullable<T>` with a `Value` of its own.
        let underlying = self.binder.nullable_underlying(matched);
        let matched = underlying.as_ref().unwrap_or(matched);
        // A tuple's members are its `ValueTuple`'s, and an element name is
        // another way of saying which field.
        let (matched, name) = match matched {
            Type::Tuple(elements) => {
                let at = elements
                    .iter()
                    .position(|element| element.name.as_deref() == Some(names[0].as_str()));
                let field = at.map_or_else(|| names[0].clone(), |at| format!("Item{}", at + 1));
                (self.tuple_as_named(elements), field)
            }
            // `source is TSource[] { Length: 0 }` reads what every array has
            // from `System.Array`, which is the only place it is declared.
            Type::Array { .. } => (
                self.framework_type("System.Array")
                    .unwrap_or_else(|| matched.clone()),
                names[0].clone(),
            ),
            other => (other.clone(), names[0].clone()),
        };
        let member = matched
            .symbol()
            .and_then(|symbol| self.binder.lookup_member(symbol, &name).first().copied())
            .or_else(|| self.extension_property(&matched, &name));
        let Some(member) = member else {
            if !matched.is_error() {
                let container = self.display(&matched);
                self.report(
                    ErrorCode::ErrNoSuchMember,
                    part.span(),
                    &[&container, &name],
                );
            }
            self.declare_pattern_variables(inner);
            return None;
        };
        // `{ Parent.Width: 1 }` names two members; this call is about the one
        // `names` starts at, which is the same distance from the end of the
        // written names.
        let spans = property_pattern_name_spans(part);
        if let Some(span) = spans.get(spans.len().saturating_sub(names.len())) {
            self.body.symbols.insert(*span, member);
        }
        // `{ Value: P }` on a union is `P` matched against what the union
        // holds, however it is read: `Value: string` asks `TryGetValue`
        // where there is one, and `Value: null` asks `HasValue` (C# 15).
        if names.len() == 1
            && let Some(members) = self.matchable_union(&matched)
            && members.value == Some(member)
        {
            let pattern = self.bind_union_pattern(inner, &matched, &matched, false, &members);
            return Some(ChainEntry::OnSelf(pattern));
        }
        let member_type = self.member_type(member, &matched);
        let pattern = match names.len() {
            1 => self.bind_pattern(inner, &member_type),
            _ => {
                let rest = self.bind_property_chain(&names[1..], &member_type, inner, part);
                // A `T?` is tested for a value and read as its `T`, as
                // `{ S1: { Value: 1 } }` would be.
                let held = self.binder.nullable_underlying(&member_type);
                let mut properties = Vec::new();
                let mut on_self = None;
                match rest {
                    Some(ChainEntry::Member(member, pattern)) => properties.push((member, pattern)),
                    Some(ChainEntry::OnSelf(pattern)) => on_self = Some(pattern),
                    None => {}
                }
                let reached = BoundPattern::new(
                    BoundPatternKind::Recursive(Box::new(BoundRecursivePattern {
                        ty: held.or_else(|| on_self.is_some().then(|| member_type.clone())),
                        properties,
                        deconstruct: None,
                        positional: Vec::new(),
                        local: None,
                    })),
                    part.span(),
                );
                match on_self {
                    Some(pattern) => BoundPattern::new(
                        BoundPatternKind::And(Box::new(reached), Box::new(pattern)),
                        part.span(),
                    ),
                    None => reached,
                }
            }
        };
        Some(ChainEntry::Member(member, pattern))
    }

    /// `Shape { Width: > 2 }` and `p is (1, var b)`.
    ///
    /// A type written in front narrows what everything inside is read on; a
    /// property clause reads members; a positional clause takes the value
    /// apart, through `Deconstruct` or, for a tuple, through its own fields.
    fn bind_recursive_pattern(&mut self, node: &SyntaxNode, input: &Type) -> BoundPattern {
        let span = node.span();
        // `[.., { } last] all` is a list pattern that names what it matched:
        // the parser hangs the designation off a node around the list, and
        // the list is what is bound, with the name added to it.
        if let Some(list) = node.child_of_kind(SyntaxKind::ListPattern) {
            let mut bound = self.bind_list_pattern(&list, input);
            let matched = self
                .binder
                .nullable_underlying(input)
                .unwrap_or_else(|| input.clone());
            let named = self.declare_designation(node, &matched);
            if let BoundPatternKind::List(list) = &mut bound.kind {
                list.local = list.local.or(named);
            }
            return BoundPattern::new(bound.kind, span);
        }
        let written = node
            .children()
            .find(|child| child.kind().is_type_node())
            .filter(|written| self.names_a_type(written));
        // `x is { }` on a `T?` matches the `T`: a pattern that reaches inside
        // has already established there is one, and what it reads members off
        // is the value rather than the nullable around it.
        let ty = written
            .as_ref()
            .map(|written| self.resolve(written))
            .or_else(|| self.binder.nullable_underlying(input));
        let matched = ty.clone().unwrap_or_else(|| input.clone());

        let mut properties = Vec::new();
        // What a union is matched for beyond its members: `{ Value: P }`.
        let mut on_self: Vec<BoundPattern> = Vec::new();
        if let Some(clause) = node.child_of_kind(SyntaxKind::PropertyPatternClause) {
            for part in clause.children() {
                let names = property_pattern_names(&part);
                let Some(inner) = part.children().find(|child| child.kind().is_pattern_node())
                else {
                    continue;
                };
                if names.is_empty() {
                    continue;
                }
                match self.bind_property_chain(&names, &matched, &inner, &part) {
                    Some(ChainEntry::Member(member, pattern)) => properties.push((member, pattern)),
                    Some(ChainEntry::OnSelf(pattern)) => on_self.push(pattern),
                    None => {}
                }
            }
        }

        let mut deconstruct = None;
        let mut positional = Vec::new();
        if let Some(clause) = node.child_of_kind(SyntaxKind::PositionalPatternClause) {
            let parts: Vec<SyntaxNode> = clause
                .children()
                .filter_map(|part| part.children().find(|child| child.kind().is_pattern_node()))
                .collect();
            // `o is (3, 4)` on an `object` with nothing to call is matched
            // through `ITuple` (Roslyn's `ShouldUseITupleForRecursivePattern`):
            // one of that length whose items match, which is the list
            // pattern `[3, 4]` over its `Length` and `this[int]`.
            if written.is_none()
                && properties.is_empty()
                && node
                    .child_of_kind(SyntaxKind::PropertyPatternClause)
                    .is_none()
                && node
                    .child_of_kind(SyntaxKind::SingleVariableDesignation)
                    .is_none()
                && self.binder.tuple_elements(&matched).is_none()
                && self.find_deconstruct(&matched, parts.len()).is_none()
                && let Some(tuple) = self.ituple_for(&matched)
            {
                return self.bind_ituple_pattern(&parts, &tuple, span);
            }
            // A tuple has nothing to call: its parts are its own elements.
            let types: Option<Vec<Type>> = match &matched {
                Type::Tuple(elements) if elements.len() == parts.len() => {
                    Some(elements.iter().map(|element| element.ty.clone()).collect())
                }
                // `ValueTuple<int, int>` is the tuple `(int, int)`, and takes
                // its parts apart the same way, though it declares no
                // `Deconstruct` to call.
                Type::Named { .. }
                    if self
                        .binder
                        .tuple_elements(&matched)
                        .is_some_and(|elements| elements.len() == parts.len()) =>
                {
                    self.binder.tuple_elements(&matched)
                }
                // An instance `Deconstruct`, or an extension one in scope
                // that needs nothing from the parts to be chosen.
                other => self
                    .find_deconstruct(other, parts.len())
                    .filter(|found| found.type_arguments.is_empty())
                    .map(|found| {
                        deconstruct = Some(found.method);
                        found.parameters
                    }),
            };
            let types = types.unwrap_or_else(|| vec![Type::Error; parts.len()]);
            for (part, ty) in parts.iter().zip(types) {
                positional.push(self.bind_pattern(part, &ty));
            }
        }

        let local = self.declare_designation(node, &matched);
        let recursive = BoundPattern::new(
            BoundPatternKind::Recursive(Box::new(BoundRecursivePattern {
                ty,
                properties,
                deconstruct,
                positional,
                local,
            })),
            span,
        );
        on_self.into_iter().fold(recursive, |whole, pattern| {
            BoundPattern::new(
                BoundPatternKind::And(Box::new(whole), Box::new(pattern)),
                span,
            )
        })
    }

    /// `System.Runtime.CompilerServices.ITuple`, where a positional pattern on
    /// a value of this type may match through it: an `object`, a `dynamic`,
    /// an `ITuple`, or something that implements it.
    fn ituple_for(&self, matched: &Type) -> Option<Type> {
        let symbol = self
            .binder
            .compilation()
            .type_by_metadata_name("System.Runtime.CompilerServices.ITuple")?;
        let tuple = Type::named(symbol);
        let object = self.binder.object_type();
        let fits = matches!(matched, Type::Dynamic)
            || object.as_ref() == Some(matched)
            || *matched == tuple
            || (matched.symbol().is_some()
                && self.binder.converts_implicitly(matched, &tuple)
                && !matched.is_error());
        fits.then_some(tuple)
    }

    /// `(p1, p2)` through `ITuple`: `ITuple and [p1, p2]`, each item an
    /// `object` read with the indexer, after the length is checked.
    fn bind_ituple_pattern(
        &mut self,
        parts: &[SyntaxNode],
        tuple: &Type,
        span: TextSpan,
    ) -> BoundPattern {
        let object = self.binder.object_type().unwrap_or(Type::Error);
        let symbol = tuple.symbol();
        let length =
            symbol.and_then(|symbol| self.binder.lookup_member(symbol, "Length").first().copied());
        let indexer =
            symbol.and_then(|symbol| self.binder.lookup_member(symbol, "this[]").first().copied());
        let before: Vec<BoundPattern> = parts
            .iter()
            .map(|part| self.bind_pattern(part, &object))
            .collect();
        let list = BoundPattern::new(
            BoundPatternKind::List(Box::new(BoundListPattern {
                length,
                indexer,
                matched: tuple.clone(),
                element: object,
                before,
                after: Vec::new(),
                slice: false,
                indexes: Vec::new(),
                slice_pattern: None,
                local: None,
            })),
            span,
        );
        BoundPattern::new(
            BoundPatternKind::And(
                Box::new(BoundPattern::new(
                    BoundPatternKind::Type(tuple.clone()),
                    span,
                )),
                Box::new(list),
            ),
            span,
        )
    }

    /// The type a value is known to have once a pattern has matched it.
    fn narrowed_by(&self, pattern: &BoundPattern, input: &Type) -> Type {
        match &pattern.kind {
            BoundPatternKind::Type(ty) => ty.clone(),
            BoundPatternKind::Declaration { ty, .. } => ty.clone(),
            BoundPatternKind::Recursive(recursive) => recursive
                .ty
                .clone()
                .or_else(|| self.binder.nullable_underlying(input))
                .unwrap_or_else(|| input.clone()),
            // `"11"` on an `object` leaves a `string`, and `<= 10U` a `uint`:
            // a constant the input is no value type for is tested with its
            // own type, which is what the right of an `and` is matched
            // against. `42` on a `long` leaves a `long`.
            BoundPatternKind::Relational { value, .. } | BoundPatternKind::Constant(value)
                if !matches!(value.ty, Type::Null) =>
            {
                let underlying = self
                    .binder
                    .nullable_underlying(input)
                    .unwrap_or_else(|| input.clone());
                let reference_input = matches!(underlying, Type::TypeParameter(_) | Type::Dynamic)
                    || underlying.is_reference_type(self.binder.compilation().symbols());
                if reference_input && !value.ty.is_error() && value.ty != underlying {
                    value.ty.clone()
                } else {
                    underlying
                }
            }
            // `(1 or 2)` leaves what both sides leave, where they agree on a
            // type the others convert to. Every alternative beneath the
            // `or`s counts, however they nest: `Derived1 or Derived2 or
            // Base` leaves a `Base`, though its first two leave nothing
            // between themselves (Roslyn's `leastSpecificType`).
            BoundPatternKind::Or(..) => {
                let mut candidates = Vec::new();
                self.or_alternatives(pattern, input, &mut candidates);
                self.least_specific(&candidates)
                    .unwrap_or_else(|| input.clone())
            }
            BoundPatternKind::And(left, right) => {
                let after_left = self.narrowed_by(left, input);
                self.narrowed_by(right, &after_left)
            }
            _ => input.clone(),
        }
    }

    /// What each alternative of an `or` leaves, the `or`s beneath it taken
    /// apart too.
    fn or_alternatives(&self, pattern: &BoundPattern, input: &Type, into: &mut Vec<Type>) {
        match &pattern.kind {
            BoundPatternKind::Or(left, right) => {
                self.or_alternatives(left, input, into);
                self.or_alternatives(right, input, into);
            }
            _ => into.push(self.narrowed_by(pattern, input)),
        }
    }

    /// The one of the types every other reaches by identity, reference or
    /// boxing, if there is one.
    fn least_specific(&self, candidates: &[Type]) -> Option<Type> {
        let (first, rest) = candidates.split_first()?;
        let mut best = first.clone();
        for candidate in rest {
            if let Some(less) = self.less_specific(&best, candidate) {
                best = less;
            }
        }
        for candidate in candidates {
            self.less_specific(candidate, &best)?;
        }
        Some(best)
    }

    /// The less specific of two types, where one reaches the other by
    /// identity, reference or boxing — not by a number widening, and not by
    /// an operator.
    fn less_specific(&self, best: &Type, candidate: &Type) -> Option<Type> {
        if best == candidate || self.binder.same_but_for_dynamic(best, candidate) {
            return Some(best.clone());
        }
        let symbols = self.binder.compilation().symbols();
        let reaches = |from: &Type, to: &Type| {
            (to.is_reference_type(symbols) || matches!(to, Type::TypeParameter(_)))
                && self.binder.converts_implicitly(from, to)
                && self.binder.implicit_operator(from, to).is_none()
        };
        if reaches(best, candidate) {
            Some(candidate.clone())
        } else if reaches(candidate, best) {
            Some(best.clone())
        } else {
            None
        }
    }

    /// Declares the name a pattern's designation introduces, if it has one.
    fn declare_designation(&mut self, pattern: &SyntaxNode, ty: &Type) -> Option<LocalId> {
        let designation = pattern.child_of_kind(SyntaxKind::SingleVariableDesignation)?;
        let token = designation
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
        Some(self.declare_local(token.value_text(), ty.clone(), token.span()))
    }

    pub(super) fn bind_case_label(&mut self, node: &SyntaxNode, input: &Type) -> BoundSwitchLabel {
        let pattern = node
            .children()
            .find(|child| child.kind().is_pattern_node())
            .map_or_else(
                || BoundPattern::new(BoundPatternKind::Discard, node.span()),
                |pattern| self.bind_pattern(&pattern, input),
            );
        let when = self.bind_when_clause(node);
        BoundSwitchLabel::Case(Box::new(BoundCaseLabel { pattern, when }))
    }

    /// The `when` clause of a label or an arm, which runs after the pattern
    /// matched and so sees the names it bound.
    fn bind_when_clause(&mut self, node: &SyntaxNode) -> Option<BoundExpression> {
        let clause = node.child_of_kind(SyntaxKind::WhenClause)?;
        let condition = clause
            .children()
            .find(|child| child.kind().is_expression())?;
        let bound = self.bind_expression(&condition);
        if matches!(bound.ty, Type::Dynamic) {
            return Some(self.as_condition(&condition, bound));
        }
        self.check_condition(&condition, &bound.ty.clone());
        Some(bound)
    }

    /// CS8509 and CS8524: a switch expression over an enum, a `bool` or an
    /// integer whose arms leave a value out, reported at its `switch`
    /// keyword. Only arms of constants (joined by `or`), `_` and `var` are
    /// judged; a switch with any other pattern unguarded is left alone, as
    /// is a nullable input. An arm with a `when` clause covers nothing.
    fn check_exhaustive(&mut self, node: &SyntaxNode, input: &Type, arms: &[BoundSwitchArm]) {
        /// The constants a pattern matches, or `None` where it matches
        /// everything or something this does not judge.
        fn constants(
            pattern: &BoundPattern,
            binder: &crate::binder::Binder<'_>,
            into: &mut Vec<i128>,
        ) -> Option<bool> {
            match &pattern.kind {
                BoundPatternKind::Discard | BoundPatternKind::Var { .. } => Some(true),
                BoundPatternKind::Constant(value) => {
                    into.push(as_integer(&binder.folded(value)?)?);
                    Some(false)
                }
                BoundPatternKind::Or(left, right) => {
                    let left = constants(left, binder, into)?;
                    let right = constants(right, binder, into)?;
                    Some(left || right)
                }
                _ => None,
            }
        }
        fn as_integer(value: &ConstantValue) -> Option<i128> {
            Some(match *value {
                ConstantValue::Boolean(value) => i128::from(value),
                ConstantValue::Char(value) => i128::from(u32::from(value)),
                ConstantValue::Int32(value) => i128::from(value),
                ConstantValue::UInt32(value) => i128::from(value),
                ConstantValue::Int64(value) => i128::from(value),
                ConstantValue::UInt64(value) => i128::from(value),
                _ => return None,
            })
        }
        let Some(switch) = node.child_token_of_kind(SyntaxKind::SwitchKeyword) else {
            return;
        };
        let Some(symbol) = input.symbol() else {
            return;
        };
        let mut covered = Vec::new();
        for arm in arms {
            if arm.when.is_some() {
                continue;
            }
            match constants(&arm.pattern, self.binder, &mut covered) {
                Some(true) => return,
                Some(false) => {}
                None => return,
            }
        }
        let symbols = self.binder.compilation().symbols();
        let entry = symbols.get(symbol);
        let (code, example) = if entry.type_kind() == Some(TypeKind::Enum) {
            let named: Vec<(SymbolId, i128)> = entry
                .members
                .iter()
                .filter(|&&member| symbols.get(member).kind == SymbolKind::Field)
                .filter_map(|&member| {
                    Some((member, as_integer(&self.binder.constant_value(member)?)?))
                })
                .collect();
            if let Some((member, _)) = named.iter().find(|(_, value)| !covered.contains(value)) {
                (
                    ErrorCode::WrnSwitchExpressionNotExhaustive,
                    format!(
                        "{}.{}",
                        symbols.qualified_name(symbol),
                        symbols.get(*member).name
                    ),
                )
            } else {
                let unnamed = (0..)
                    .find(|value| !covered.contains(value))
                    .unwrap_or_default();
                (
                    ErrorCode::WrnSwitchExpressionNotExhaustiveWithUnnamedEnumValue,
                    format!("({}){unnamed}", symbols.qualified_name(symbol)),
                )
            }
        } else if *input == self.special(SpecialType::Boolean) {
            match [1, 0].into_iter().find(|value| !covered.contains(value)) {
                Some(value) => (
                    ErrorCode::WrnSwitchExpressionNotExhaustive,
                    if value == 1 { "true" } else { "false" }.to_string(),
                ),
                None => return,
            }
        } else if [
            SpecialType::Int16,
            SpecialType::UInt16,
            SpecialType::Int32,
            SpecialType::UInt32,
            SpecialType::Int64,
            SpecialType::UInt64,
        ]
        .into_iter()
        .any(|special| *input == self.special(special))
        {
            // A byte is left out above: its 256 values can all be written.
            let missing = (0..)
                .find(|value| !covered.contains(value))
                .unwrap_or_default();
            (
                ErrorCode::WrnSwitchExpressionNotExhaustive,
                missing.to_string(),
            )
        } else {
            return;
        };
        self.report(code, switch.span(), &[&example]);
    }

    pub(super) fn bind_switch_expression(
        &mut self,
        node: &SyntaxNode,
        target: Option<&Type>,
    ) -> BoundExpression {
        let span = node.span();
        let values: Vec<SyntaxNode> = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::SwitchExpressionArm)
            .filter_map(|arm| {
                arm.children()
                    .filter(|part| part.kind().is_expression())
                    .last()
            })
            .collect();
        // `new()` or a lambda beside an arm with a type of its own is made
        // of that type (the switch's natural type is the arms' best common
        // type, which a typeless arm has no say in): `1 => new C(), int n =>
        // new() { n = n }` is a `C`, and `0 => (Func<int, int>)(x => x), _ =>
        // y => y * 2` a `Func<int, int>` — as `?:` has it.
        let typeless_beside_a_type = values
            .iter()
            .filter(|value| self.written_typeless(value))
            .all(|value| {
                value.kind() == SyntaxKind::ImplicitObjectCreationExpression || is_lambda(value)
            })
            && values.iter().any(|value| {
                !self.written_typeless(value) && value.kind() != SyntaxKind::ThrowExpression
            });
        // Nothing has said what this is yet, and the arms cannot say it
        // themselves: `attribute switch { A => isPossibleA, _ => throw ... }`
        // is a method group either way round. Wait for whatever it is given
        // to, the way a lambda written on its own waits.
        if target.is_none()
            && !typeless_beside_a_type
            && values.iter().any(|value| self.written_typeless(value))
        {
            return BoundExpression::new(
                BoundExpressionKind::UnboundSwitch(span),
                Type::Error,
                span,
            );
        }
        let governing = node
            .children()
            .find(|child| child.kind().is_expression())
            .map(|child| self.bind_expression(&child));
        let Some(governing) = governing else {
            return BoundExpression::error(span);
        };
        let input = governing.ty.clone();

        let mut arms = Vec::new();
        // The scope of each arm whose `new()` waits for the type the other
        // arms give: its variables are what the initializer names.
        let mut waiting: Vec<(usize, std::collections::HashMap<String, LocalId>)> = Vec::new();
        for child in node.children() {
            if child.kind() != SyntaxKind::SwitchExpressionArm {
                continue;
            }
            // An arm's pattern variables are in scope for its `when` clause
            // and its value, and nowhere else.
            self.push_scope();
            let pattern = child
                .children()
                .find(|part| part.kind().is_pattern_node())
                .map_or_else(
                    || BoundPattern::new(BoundPatternKind::Discard, child.span()),
                    |pattern| self.bind_pattern(&pattern, &input),
                );
            let when = self.bind_when_clause(&child);
            // The arm's value is the last expression in it; a `when` clause
            // holds one too, and it comes first.
            let mut value = child
                .children()
                .filter(|part| part.kind().is_expression())
                .last()
                .map_or_else(
                    || BoundExpression::error(child.span()),
                    |value| self.bind_expression(&value),
                );
            // `ICollection<T> collection => new(collection)` names the
            // pattern's variable in a value that has no type until the
            // target gives it one: where the target is known, the value is
            // converted here, while the variable is still in scope.
            if let Some(target) = target
                && typeless(&value)
            {
                value = self.convert(value, target);
            } else if typeless(&value)
                && let Some(scope) = self.scopes.last()
            {
                waiting.push((arms.len(), scope.clone()));
            }
            self.pop_scope();
            arms.push(BoundSwitchArm {
                pattern,
                when,
                value,
            });
        }
        self.check_exhaustive(node, &input, &arms);

        // The type is the one every arm converts to, found the way a
        // conditional finds it: keep the candidate the others reach. Where
        // something asked for a type, that is the answer and no arm gets a
        // say.
        let mut ty = target.cloned().unwrap_or(Type::Error);
        if target.is_none() {
            for arm in &arms {
                if arm.value.ty.is_error() {
                    continue;
                }
                // Once an arm is `dynamic` the arms are: every type converts
                // to it, and it converts back to every one, so an arm after
                // it would otherwise take its place.
                if ty.is_error()
                    || (!matches!(ty, Type::Dynamic)
                        && self.binder.converts_implicitly(&ty, &arm.value.ty))
                {
                    ty = arm.value.ty.clone();
                }
            }
            // `{ IsReturnOnly: true } => Level.ReturnOnly, _ => null` is a
            // `Level?`: a `null` arm beside a value type makes the whole
            // thing the nullable of it, the way `?:` does (§12.18).
            if arms.iter().any(|arm| matches!(arm.value.ty, Type::Null))
                && !ty.is_error()
                && !matches!(ty, Type::Null)
                && !self.binder.held_by_reference(&ty)
                && self.binder.nullable_underlying(&ty).is_none()
            {
                ty = self.nullable_of(ty);
            }
            // No arm's type takes all the others — `0 => left, 1 =>
            // operatorToken` is an `ExpressionSyntax` beside a `SyntaxToken`
            // — so the arms cannot say what this is (§12.6.3.15), and it
            // waits for what it is given to, as one with typeless arms does.
            let agreed = arms.iter().all(|arm| {
                arm.value.ty.is_error()
                    || matches!(arm.value.ty, Type::Null)
                    || typeless(&arm.value)
                    || arm.value.ty == ty
                    || self.binder.converts_implicitly(&arm.value.ty, &ty)
                    || self.constant_fits(&arm.value, &ty)
            });
            if !agreed && !ty.is_error() {
                self.branch_types.insert(
                    span,
                    arms.iter()
                        .filter(|arm| !typeless(&arm.value))
                        .map(|arm| arm.value.ty.clone())
                        .collect(),
                );
                return BoundExpression::new(
                    BoundExpressionKind::UnboundSwitch(span),
                    Type::Error,
                    span,
                );
            }
        }
        if !waiting.is_empty() {
            // No arm has a type the `new()` can be made of: the whole thing
            // waits for a target after all.
            if matches!(ty, Type::Error | Type::Null) {
                return BoundExpression::new(
                    BoundExpressionKind::UnboundSwitch(span),
                    Type::Error,
                    span,
                );
            }
            for (at, scope) in waiting {
                let value = std::mem::replace(&mut arms[at].value, BoundExpression::error(span));
                self.scopes.push(scope);
                self.siblings.push(false);
                arms[at].value = self.convert(value, &ty);
                self.pop_scope();
            }
        }
        // An arm that is a method group has no type of its own and no syntax
        // that says so. Where the arms cannot decide between them, they are
        // left as they are for whatever the whole thing is given to.
        if target.is_none()
            && matches!(ty, Type::Error | Type::Null)
            && arms.iter().any(|arm| typeless(&arm.value))
        {
            return BoundExpression::new(
                BoundExpressionKind::Switch {
                    governing: Box::new(governing),
                    arms,
                },
                Type::Error,
                span,
            );
        }
        let mut converted = Vec::with_capacity(arms.len());
        for arm in arms {
            // Given a type, each arm has to reach it (the switch expression
            // conversion): `Source1 x = b switch { false => s1, true => s2 }`
            // is an error at the `s2`, not a cast that fails when it runs.
            if target.is_some()
                && let Some(written) = values.iter().find(|value| value.span() == arm.value.span)
            {
                self.check_assignable(written, &arm.value, &ty);
            }
            let value = self.convert(arm.value, &ty);
            converted.push(BoundSwitchArm {
                pattern: arm.pattern,
                when: arm.when,
                value,
            });
        }

        BoundExpression::new(
            BoundExpressionKind::Switch {
                governing: Box::new(governing),
                arms: converted,
            },
            ty,
            span,
        )
    }

    /// Declares the variables a pattern introduces: `o is Shape s` puts `s` in
    /// scope for the rest of the enclosing statement.
    fn declare_pattern_variables(&mut self, pattern: &SyntaxNode) {
        match pattern.kind() {
            SyntaxKind::DeclarationPattern
            | SyntaxKind::VarPattern
            | SyntaxKind::RecursivePattern => {
                let ty = pattern
                    .children()
                    .find(|child| child.kind().is_type_node())
                    .map_or(Type::Error, |node| self.resolve(&node));
                for child in pattern.children() {
                    if child.kind() == SyntaxKind::SingleVariableDesignation
                        && let Some(token) = child
                            .child_tokens()
                            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    {
                        self.declare_local(token.value_text(), ty.clone(), token.span());
                    } else if child.kind().is_pattern_node() {
                        self.declare_pattern_variables(&child);
                    }
                }
            }
            // A list pattern, a slice, a subpattern: not modelled, but the
            // names inside still have to resolve, and they can be any depth
            // down through nodes that are not patterns themselves.
            _ => {
                for child in pattern.children() {
                    self.declare_pattern_variables(&child);
                }
            }
        }
    }
}

/// The operator a relational pattern's token stands for: `> 3` compares.
const fn relational_operator(token: SyntaxKind) -> Option<BinaryOperator> {
    Some(match token {
        SyntaxKind::LessThanToken => BinaryOperator::LessThan,
        SyntaxKind::LessThanEqualsToken => BinaryOperator::LessThanOrEqual,
        SyntaxKind::GreaterThanToken => BinaryOperator::GreaterThan,
        SyntaxKind::GreaterThanEqualsToken => BinaryOperator::GreaterThanOrEqual,
        SyntaxKind::EqualsEqualsToken => BinaryOperator::Equality,
        SyntaxKind::ExclamationEqualsToken => BinaryOperator::Inequality,
        _ => return None,
    })
}

/// The names in front of the `:` of one property-pattern entry.
///
/// `{ Width: 1 }` has one and `{ Parent.Width: 1 }` has two, which the parser
/// gives as a member access rather than as a name.
fn property_pattern_names(part: &SyntaxNode) -> Vec<String> {
    if let Some(colon) = part.child_of_kind(SyntaxKind::NameColon) {
        return colon
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| vec![token.value_text().to_string()])
            .unwrap_or_default();
    }
    let Some(colon) = part.child_of_kind(SyntaxKind::ExpressionColon) else {
        return Vec::new();
    };
    let Some(target) = colon.children().next() else {
        return Vec::new();
    };
    let mut names = Vec::new();
    collect_dotted_names(&target, &mut names);
    names
}

/// Where the names of [`property_pattern_names`] are, in the same order.
fn property_pattern_name_spans(part: &SyntaxNode) -> Vec<TextSpan> {
    let colon = part
        .child_of_kind(SyntaxKind::NameColon)
        .or_else(|| part.child_of_kind(SyntaxKind::ExpressionColon));
    colon
        .map(|colon| {
            colon
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                .map(|token| token.span())
                .collect()
        })
        .unwrap_or_default()
}

/// The identifiers of `a.b.c`, in order.
fn collect_dotted_names(node: &SyntaxNode, into: &mut Vec<String>) {
    match node.kind() {
        SyntaxKind::IdentifierName => into.extend(identifier_text(node)),
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::QualifiedName => {
            for child in node.children() {
                collect_dotted_names(&child, into);
            }
        }
        _ => {}
    }
}

/// The parts of `a and b and c`, left to right: the parser nests them to
/// the left, and a parenthesized part stays one.
fn and_chain(node: &SyntaxNode, into: &mut Vec<SyntaxNode>) {
    let parts: Vec<SyntaxNode> = node
        .children()
        .filter(|child| child.kind().is_pattern_node())
        .collect();
    for part in parts {
        // `(a and b) and c` is `a and b and c`: what narrows the value
        // narrows it for what follows, whichever way the parentheses go.
        let grouped = match part.kind() {
            SyntaxKind::AndPattern => Some(part.clone()),
            SyntaxKind::ParenthesizedPattern => part
                .children()
                .find(|child| child.kind().is_pattern_node())
                .filter(|inner| inner.kind() == SyntaxKind::AndPattern),
            _ => None,
        };
        match grouped {
            Some(inner) => and_chain(&inner, into),
            None => into.push(part),
        }
    }
}

/// A lambda or an anonymous method, in parentheses or not.
fn is_lambda(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::SimpleLambdaExpression
        | SyntaxKind::ParenthesizedLambdaExpression
        | SyntaxKind::AnonymousMethodExpression => true,
        SyntaxKind::ParenthesizedExpression => node
            .children()
            .find(|child| child.kind().is_expression())
            .is_some_and(|inner| is_lambda(&inner)),
        _ => false,
    }
}
