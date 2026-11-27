//! Assignment: `=` and compound assignment, and what may be written.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::operators::{operator_method_name, operator_token_text};
use super::{BodyBinder, compound_operator, identifier_text, typeless};
use crate::binder::Diagnostics;
use crate::bound::{BoundExpression, BoundExpressionKind, ConstantValue, ConversionKind};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{MethodKind, Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// Whether an override that declares no setter overrides a property
    /// that has one: `override long P { get; }` over a `get; set;` property
    /// can still be assigned, through the setter it inherits.
    fn overrides_a_setter(&self, property: SymbolId) -> bool {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        let mut current = property;
        for _ in 0..16 {
            let symbol = symbols.get(current);
            if !symbol.modifiers.contains(Modifiers::OVERRIDE) {
                return false;
            }
            let Some(arity) = symbol.as_property().map(|detail| detail.parameters.len()) else {
                return false;
            };
            let Some(base) = symbol
                .container
                .and_then(|container| self.binder.base_class_of(container))
                .and_then(|base| base.symbol())
            else {
                return false;
            };
            // What it overrides is the nearest property of its name up the
            // bases that it could: a base's private one is passed over.
            let overridden = self
                .binder
                .lookup_member_where(base, &symbol.name, &|candidate| {
                    symbols.get(candidate).accessibility != crate::symbol::Accessibility::Private
                        && symbols
                            .get(candidate)
                            .as_property()
                            .is_some_and(|detail| detail.parameters.len() == arity)
                });
            let Some(overridden) = overridden.first().copied() else {
                return false;
            };
            let Some(detail) = symbols.get(overridden).as_property() else {
                return false;
            };
            let settable = if compilation.is_from_metadata(overridden) {
                detail.setter.is_some()
            } else {
                detail.has_set || detail.has_init
            };
            if settable {
                return true;
            }
            current = overridden;
        }
        false
    }

    pub(super) fn bind_assignment(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let mut children = node.children();
        let Some(target_node) = children.next() else {
            return BoundExpression::error(span);
        };
        // `var (a, b) = point;` is not an assignment at all: it declares the
        // variables and calls `Deconstruct`.
        if matches!(
            target_node.kind(),
            SyntaxKind::DeclarationExpression | SyntaxKind::TupleExpression
        ) && let Some(value_node) = node.children().nth(1)
        {
            if let Some(call) = self.bind_deconstruction(&target_node, &value_node, span) {
                return call;
            }
            // `var (x, y) = "";` that could not be taken apart declared
            // its variables and said why; it is no call of a `var`.
            if target_node.kind() == SyntaxKind::DeclarationExpression {
                return BoundExpression::error(span);
            }
        }

        // `_ = Compute();` throws the value away: there is nothing to assign
        // to, and the point is that the expression still runs. A real `_` in
        // scope is an ordinary variable and wins.
        if target_node.kind() == SyntaxKind::IdentifierName
            && identifier_text(&target_node).as_deref() == Some("_")
            && self.lookup_local("_").is_none()
            && self
                .context
                .enclosing_type()
                .is_none_or(|ty| self.binder.lookup_member(ty, "_").is_empty())
        {
            let Some(value_node) = children.next() else {
                return BoundExpression::error(span);
            };
            let value = self.bind_expression(&value_node);
            // An assignment is a value, never the variable it read: `(_ =
            // v).Increment()` on a struct `v` increments a copy.
            if self.is_variable(&value) && !self.binder.held_by_reference(&value.ty) {
                let ty = value.ty.clone();
                return BoundExpression::new(
                    BoundExpressionKind::Conversion {
                        operand: Box::new(value),
                        conversion: ConversionKind::Identity,
                        written: false,
                    },
                    ty,
                    span,
                );
            }
            return value;
        }
        let target = self.bind_expression(&target_node);
        let Some(value_node) = children.next() else {
            return target;
        };
        let value = self.bind_expression(&value_node);

        // `a?.b = c` (C# 14) assigns only where `a` is not null, and is the
        // value assigned — nullable where that is a value type, as every
        // `?.` is (§12.8.8).
        // The access may come wrapped into its nullable: the target is what
        // is under that.
        let target = match target.kind {
            BoundExpressionKind::Conversion { operand, .. }
                if matches!(operand.kind, BoundExpressionKind::ConditionalAccess { .. }) =>
            {
                *operand
            }
            _ => target,
        };
        if matches!(target.kind, BoundExpressionKind::ConditionalAccess { .. }) {
            let innermost = assigned_through(&target).ty.clone();
            self.check_assignable(&value_node, &value, &innermost);
            let value = self.convert(value, &innermost);
            return self.assign_through(target, value, span);
        }

        let rebinds = matches!(value.kind, BoundExpressionKind::RefArgument { .. });
        self.check_writable(&target, &target_node, rebinds);
        self.check_assignable(&value_node, &value, &target.ty.clone());
        let ty = target.ty.clone();
        let value = self.convert(value, &ty);
        BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(target),
                value: Box::new(value),
            },
            ty,
            span,
        )
    }

    /// What is wrong with the left side of `target = value`: a property with
    /// no setter (CS0200), a `readonly` field outside a constructor (CS0191,
    /// CS0198), or something that is not a variable at all (CS0131).
    ///
    /// Inside a constructor and in an initializer a get-only property and a
    /// `readonly` field may both be written, and which type's constructor
    /// that is takes more than this asks: there, nothing is said.
    fn check_writable(
        &mut self,
        target: &BoundExpression,
        target_node: &SyntaxNode,
        rebinds: bool,
    ) {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        let constructing = self.in_initializer
            || self.member.is_none_or(|member| {
                symbols.get(member).as_method().is_some_and(|detail| {
                    matches!(
                        detail.method_kind,
                        MethodKind::Constructor
                            | MethodKind::StaticConstructor
                            | MethodKind::PropertySet
                    )
                }) || symbols.get(member).kind == SymbolKind::Field
            });
        let at = target_node.span();
        match &target.kind {
            BoundExpressionKind::Property { property, .. }
            | BoundExpressionKind::IndexerAccess {
                indexer: property, ..
            } => {
                let Some(detail) = symbols.get(*property).as_property() else {
                    return;
                };
                let settable = if compilation.is_from_metadata(*property) {
                    detail.setter.is_some()
                } else {
                    detail.has_set || detail.has_init
                };
                let by_ref = matches!(
                    self.binder.type_of(*property, &mut Diagnostics::new()),
                    Type::ByRef(_) | Type::Error
                );
                if settable
                    || by_ref
                    || constructing
                    || detail.backing_field.is_some()
                    || self.overrides_a_setter(*property)
                {
                    return;
                }
                let receiver_type = match &target.kind {
                    BoundExpressionKind::Property {
                        receiver: Some(receiver),
                        ..
                    } => receiver.ty.clone(),
                    BoundExpressionKind::IndexerAccess { receiver, .. } => receiver.ty.clone(),
                    _ => Type::Error,
                };
                let display = crate::checks::member_display(
                    compilation,
                    *property,
                    &self.substitution_for(*property, &receiver_type),
                    None,
                );
                self.report(ErrorCode::ErrAssgReadonlyProp, at, &[&display]);
            }
            BoundExpressionKind::Field { field, .. } => {
                let modifiers = symbols.get(*field).modifiers;
                if symbols.get(*field).kind != SymbolKind::Field {
                    return;
                }
                // `readonly ref T F` may not be pointed elsewhere, but what
                // it points at is written through it like any `ref`; only
                // `ref readonly` says that may not be written either.
                let mut sink = Diagnostics::new();
                if !rebinds && matches!(self.binder.type_of(*field, &mut sink), Type::ByRef(_)) {
                    let points_at_readonly = compilation.is_ref_readonly_field(*field);
                    if points_at_readonly {
                        self.report(ErrorCode::ErrAssgReadonly, at, &[]);
                    }
                    return;
                }
                if modifiers.contains(Modifiers::CONST) {
                    self.report(ErrorCode::ErrAssgLvalueExpected, at, &[]);
                } else if modifiers.contains(Modifiers::READONLY)
                    && !constructing
                    && !compilation.options().writes_readonly_fields
                {
                    let code = if modifiers.contains(Modifiers::STATIC) {
                        ErrorCode::ErrAssgReadonlyStatic
                    } else {
                        ErrorCode::ErrAssgReadonly
                    };
                    self.report(code, at, &[]);
                }
            }
            BoundExpressionKind::Literal(_)
            | BoundExpressionKind::Binary { .. }
            | BoundExpressionKind::ObjectCreation { .. }
            | BoundExpressionKind::InterpolatedString(_)
            | BoundExpressionKind::TypeTest { .. }
            | BoundExpressionKind::IsPattern { .. } => {
                self.report(ErrorCode::ErrAssgLvalueExpected, at, &[]);
            }
            BoundExpressionKind::Call { method, .. }
                if !matches!(
                    self.binder.type_of(*method, &mut Diagnostics::new()),
                    Type::ByRef(_) | Type::Error
                ) =>
            {
                self.report(ErrorCode::ErrAssgLvalueExpected, at, &[]);
            }
            _ => {}
        }
    }

    /// The assignment `a?.b?.c = v` makes: each `?.` on the way keeps its
    /// test, and the store goes on the innermost access (C# 14).
    fn assign_through(
        &mut self,
        target: BoundExpression,
        value: BoundExpression,
        span: TextSpan,
    ) -> BoundExpression {
        self.write_through(target, span, &mut |_, target| {
            let ty = target.ty.clone();
            BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(target),
                    value: Box::new(value.clone()),
                },
                ty,
                span,
            )
        })
    }

    /// What `a?.b?.c op= v` makes: each `?.` on the way keeps its test, and
    /// `write` makes the store on the innermost access.
    fn write_through(
        &mut self,
        target: BoundExpression,
        span: TextSpan,
        write: &mut dyn FnMut(&mut Self, BoundExpression) -> BoundExpression,
    ) -> BoundExpression {
        let target = match target.kind {
            BoundExpressionKind::Conversion { operand, .. }
                if matches!(operand.kind, BoundExpressionKind::ConditionalAccess { .. }) =>
            {
                *operand
            }
            _ => target,
        };
        match target.kind {
            BoundExpressionKind::ConditionalAccess { receiver, access } => {
                let assigned = self.write_through(*access, span, write);
                let ty = assigned.ty.clone();
                let result = if self.wraps_in_nullable(&ty) {
                    self.nullable_of(ty)
                } else {
                    ty
                };
                BoundExpression::new(
                    BoundExpressionKind::ConditionalAccess {
                        receiver,
                        access: Box::new(assigned),
                    },
                    result,
                    span,
                )
            }
            _ => write(self, target),
        }
    }

    /// Whether an event is used as the field behind it here: a field-like
    /// event is one only inside the type that declares it (§15.8.2), and an
    /// event out of metadata has no field at all.
    pub(super) fn event_is_a_field_here(&self, event: SymbolId) -> bool {
        let compilation = self.binder.compilation();
        if compilation.is_from_metadata(event) {
            return false;
        }
        // An event with `add` and `remove` blocks has no field at all.
        if compilation
            .declaration_node(event)
            .is_none_or(|node| node.kind() != SyntaxKind::VariableDeclarator)
        {
            return false;
        }
        let symbols = compilation.symbols();
        let Some(declaring) = symbols.get(event).container else {
            return false;
        };
        // `event Action E;` in an interface is abstract (C# 8): an instance
        // has nowhere to keep a delegate in, and `E += h` inside the
        // interface calls `add_E` as it would from outside.
        if symbols.get(declaring).type_kind() == Some(TypeKind::Interface)
            && !symbols.get(event).modifiers.contains(Modifiers::STATIC)
        {
            return false;
        }
        // Inside a `readonly` member of a struct the field may not be
        // written: `E += h` there calls the accessor, on a copy.
        let readonly_here = self.member.is_some_and(|member| {
            let symbol = symbols.get(member);
            symbol.modifiers.contains(Modifiers::READONLY)
                || symbol.container.is_some_and(|container| {
                    matches!(
                        symbols.get(container).kind,
                        SymbolKind::Property | SymbolKind::NamedType
                    ) && symbols
                        .get(container)
                        .modifiers
                        .contains(Modifiers::READONLY)
                })
        });
        if readonly_here && symbols.get(declaring).type_kind() == Some(TypeKind::Struct) {
            return false;
        }
        self.context.enclosing_types().contains(&declaring)
    }

    /// A place that is read and then written, with what locates it — the
    /// object a property or field is on, an indexer's receiver and indices,
    /// an array and its indices — kept in temporaries: the assignments that
    /// fill them, and the place reading them. `None` where the place is on
    /// a struct that is not a variable, whose copy would take the write.
    fn kept_place(
        &mut self,
        target: &BoundExpression,
    ) -> Option<(Vec<BoundExpression>, BoundExpression)> {
        let mut prelude = Vec::new();
        let mut keep = |this: &mut Self, value: &mut BoundExpression| {
            if matches!(
                value.kind,
                BoundExpressionKind::Local(_)
                    | BoundExpressionKind::Parameter(_)
                    | BoundExpressionKind::This
                    | BoundExpressionKind::Base
                    | BoundExpressionKind::Literal(_)
                    | BoundExpressionKind::TypeExpression(_)
            ) {
                return;
            }
            let ty = value.ty.clone();
            let span = value.span;
            let held = this.declare_synthetic_local("place", ty.clone());
            let read = BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
            let taken = std::mem::replace(value, read.clone());
            prelude.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read),
                    value: Box::new(taken),
                },
                ty,
                span,
            ));
        };
        let symbols = self.binder.compilation().symbols();
        let reference =
            |ty: &Type| ty.is_reference_type(symbols) || matches!(ty, Type::Array { .. });
        let mut place = target.clone();
        match &mut place.kind {
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                ..
            }
            | BoundExpressionKind::Property {
                receiver: Some(receiver),
                ..
            } => {
                if !reference(&receiver.ty) {
                    return None;
                }
                keep(self, receiver);
            }
            BoundExpressionKind::IndexerAccess {
                receiver,
                arguments,
                ..
            } => {
                if !reference(&receiver.ty) {
                    return None;
                }
                keep(self, receiver);
                for argument in arguments.iter_mut() {
                    if matches!(argument.kind, BoundExpressionKind::RefArgument { .. }) {
                        return None;
                    }
                    keep(self, argument);
                }
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                keep(self, array);
                for index in indices.iter_mut() {
                    keep(self, index);
                }
            }
            _ => return None,
        }
        Some((prelude, place))
    }

    /// Whether the target of an assignment is a place that can be assigned:
    /// a variable, an element, or a member of one or of a reference. What
    /// is not (a member of a value that is only a value, `default(T).P`) is
    /// said to be so before anything about the operator is.
    fn is_variable_place(&self, target: &BoundExpression) -> bool {
        let symbols = self.binder.compilation().symbols();
        let held = |receiver: &Option<Box<BoundExpression>>| {
            receiver.as_deref().is_none_or(|receiver| {
                self.is_variable_place(receiver) || receiver.ty.is_reference_type(symbols)
            })
        };
        match &target.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::ArrayAccess { .. } => true,
            BoundExpressionKind::Field { receiver, .. }
            | BoundExpressionKind::Property { receiver, .. } => held(receiver),
            BoundExpressionKind::IndexerAccess { receiver, .. } => {
                self.is_variable_place(receiver) || receiver.ty.is_reference_type(symbols)
            }
            _ => false,
        }
    }

    /// Whether a type is `decimal`, whose operators are metadata methods that the
    /// language nevertheless treats as predefined.
    /// Whether a type is one of the numbers, `char` and the native integers.
    pub(super) fn is_plain_number(&self, ty: &Type) -> bool {
        self.compound_operand_kind(ty) == Some(CompoundOperand::Number)
    }

    fn is_decimal(&self, ty: &Type) -> bool {
        self.binder.special_of(ty) == Some(SpecialType::Decimal)
    }

    /// Which kind of predefined type a compound assignment is certain about:
    /// the numbers, `char`, `nint` and `nuint`, `bool`, `string`, `object` and
    /// enums. Anything else (a type with operators of its own, a nullable, a
    /// pointer, a delegate) keeps every operator it may find.
    fn compound_operand_kind(&self, ty: &Type) -> Option<CompoundOperand> {
        if let Some(special) = self.binder.special_of(ty) {
            return match special {
                SpecialType::Boolean => Some(CompoundOperand::Boolean),
                SpecialType::String => Some(CompoundOperand::Text),
                SpecialType::Object => Some(CompoundOperand::Object),
                special if special.is_numeric() => Some(CompoundOperand::Number),
                _ => None,
            };
        }
        if self.binder.native_int(ty).is_some() {
            return Some(CompoundOperand::Number);
        }
        self.binder
            .enum_underlying(ty)
            .map(|_| CompoundOperand::Enumeration)
    }

    /// The predefined operator `x op y` takes on two operands of the plain
    /// predefined types (§12.4.5): the candidates both operands reach, and
    /// the one of them every other candidate is worse than. `None` where an
    /// operand is something this does not know the operators of.
    pub(super) fn predefined_operation(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<PredefinedOperation> {
        let left_kind = self.compound_operand_kind(&left.ty)?;
        let right_kind = self.compound_operand_kind(&right.ty)?;
        let shift = matches!(
            operator,
            BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::UnsignedRightShift
        );
        if left_kind == CompoundOperand::Text || right_kind == CompoundOperand::Text {
            return Some(if operator == BinaryOperator::Add {
                PredefinedOperation::Result(self.special(SpecialType::String))
            } else {
                PredefinedOperation::Inapplicable
            });
        }
        if left_kind == CompoundOperand::Object || right_kind == CompoundOperand::Object {
            return Some(PredefinedOperation::Inapplicable);
        }
        if left_kind == CompoundOperand::Boolean || right_kind == CompoundOperand::Boolean {
            return Some(
                if left_kind == right_kind
                    && matches!(
                        operator,
                        BinaryOperator::BitwiseAnd
                            | BinaryOperator::BitwiseOr
                            | BinaryOperator::ExclusiveOr
                    )
                {
                    PredefinedOperation::Result(self.special(SpecialType::Boolean))
                } else {
                    PredefinedOperation::Inapplicable
                },
            );
        }
        if left_kind == CompoundOperand::Enumeration || right_kind == CompoundOperand::Enumeration {
            // An enum has the `+`, `-` and the bit operators only, which
            // the binary operator already works out.
            return match operator {
                BinaryOperator::Add
                | BinaryOperator::Subtract
                | BinaryOperator::BitwiseAnd
                | BinaryOperator::BitwiseOr
                | BinaryOperator::ExclusiveOr => {
                    let floor = self.body.diagnostics.len();
                    let combined = self.bind_binary_on(operator, left.clone(), right.clone(), span);
                    if self.body.diagnostics.len() != floor {
                        Some(PredefinedOperation::Reported)
                    } else if combined.ty.is_error() {
                        None
                    } else {
                        Some(PredefinedOperation::Result(combined.ty))
                    }
                }
                _ => Some(PredefinedOperation::Inapplicable),
            };
        }
        let int = self.special(SpecialType::Int32);
        let native = |this: &Self, name: &str| {
            this.binder
                .compilation()
                .type_by_metadata_name(name)
                .map(Type::named)
        };
        let mut candidates = vec![
            int.clone(),
            self.special(SpecialType::UInt32),
            self.special(SpecialType::Int64),
            self.special(SpecialType::UInt64),
            native(self, "System.IntPtr")?,
            native(self, "System.UIntPtr")?,
        ];
        let arithmetic = matches!(
            operator,
            BinaryOperator::Add
                | BinaryOperator::Subtract
                | BinaryOperator::Multiply
                | BinaryOperator::Divide
                | BinaryOperator::Modulo
        );
        if arithmetic {
            candidates.push(self.special(SpecialType::Single));
            candidates.push(self.special(SpecialType::Double));
            candidates.push(self.special(SpecialType::Decimal));
        }
        let reaches = |this: &Self, operand: &BoundExpression, to: &Type| {
            this.binder.converts_implicitly(&operand.ty, to) || this.constant_fits(operand, to)
        };
        // The count of a shift is an `int` whatever the candidate.
        if shift && !reaches(self, right, &int) {
            return Some(PredefinedOperation::Inapplicable);
        }
        let applicable: Vec<Type> = candidates
            .into_iter()
            .filter(|candidate| {
                reaches(self, left, candidate) && (shift || reaches(self, right, candidate))
            })
            .collect();
        let signed = |this: &Self, ty: &Type| {
            this.binder.native_int(ty) == Some(false)
                || matches!(
                    this.binder.special_of(ty),
                    Some(
                        SpecialType::SByte
                            | SpecialType::Int16
                            | SpecialType::Int32
                            | SpecialType::Int64
                    )
                )
        };
        let unsigned = |this: &Self, ty: &Type| {
            this.binder.native_int(ty) == Some(true)
                || matches!(
                    this.binder.special_of(ty),
                    Some(
                        SpecialType::Byte
                            | SpecialType::UInt16
                            | SpecialType::UInt32
                            | SpecialType::UInt64
                    )
                )
        };
        let better = |this: &Self, one: &Type, other: &Type| {
            (this.binder.converts_implicitly(one, other)
                && !this.binder.converts_implicitly(other, one))
                || (signed(this, one) && unsigned(this, other))
        };
        let best = applicable.iter().find(|candidate| {
            applicable
                .iter()
                .all(|other| other == *candidate || better(self, candidate, other))
        });
        Some(match (best, applicable.is_empty()) {
            (Some(best), _) => PredefinedOperation::Result(best.clone()),
            (None, true) => PredefinedOperation::Inapplicable,
            (None, false) => PredefinedOperation::Ambiguous,
        })
    }

    /// `x op= y` on the plain predefined types: CS0019 and CS0034 where no
    /// operator takes the operands, and CS0266 or CS0029 where the result
    /// does not fit `x`. It has to convert implicitly, or, for a predefined
    /// operator, explicitly with `y` converting implicitly to the type of
    /// `x` (or a shift) (§12.21.4). Where an operand is not one of the
    /// plain predefined types the rule is not applied. Whether it reported.
    fn check_compound_result(
        &mut self,
        operator: BinaryOperator,
        target: &BoundExpression,
        value: &BoundExpression,
        span: TextSpan,
    ) -> bool {
        let stored = &target.ty;
        // An extension block (C# 14) may give any type an operator, an
        // `operator +=` too, and where one is in scope nothing is certain.
        if let Some(name) = operator_method_name(operator)
            && (!self
                .binder
                .extension_members_in_scope(&self.context, name)
                .is_empty()
                || !self
                    .binder
                    .extension_members_in_scope(&self.context, &format!("{name}Assignment"))
                    .is_empty())
        {
            return false;
        }
        // A `switch` expression goes to the type on the left arm by arm, as
        // it would in `x = y`: `b |= k switch { K.A => 1, _ => 0 }` asks no
        // cast of a `byte`, though the arms alone would make an `int`.
        if matches!(value.kind, BoundExpressionKind::Switch { .. }) {
            return false;
        }
        if !self.is_variable_place(target)
            || typeless(value)
            || matches!(value.ty, Type::Null | Type::Error | Type::Dynamic)
            || stored.is_error()
            || value.ty.is_error()
            || (!self.is_decimal(stored)
                && !self.is_decimal(&value.ty)
                && self
                    .user_defined_operator(operator, target, value, span)
                    .is_some())
        {
            return false;
        }
        // A nullable operand lifts the operator (§12.4.8): the plain
        // types are what the rules are asked about, and the result is a
        // nullable again.
        let bare = |this: &Self, operand: &BoundExpression| {
            let ty = this
                .binder
                .nullable_underlying(&operand.ty)
                .unwrap_or_else(|| operand.ty.clone());
            BoundExpression::new(operand.kind.clone(), ty, operand.span)
        };
        let (target_bare, value_bare) = (bare(self, target), bare(self, value));
        let lifted_left = target_bare.ty != *stored;
        let lifted_right = value_bare.ty != value.ty;
        let Some(operation) = self.predefined_operation(operator, &target_bare, &value_bare, span)
        else {
            return false;
        };
        let text = format!("{}=", operator_token_text(operator));
        let result = match operation {
            PredefinedOperation::Result(result) => result,
            PredefinedOperation::Reported => return true,
            PredefinedOperation::Inapplicable | PredefinedOperation::Ambiguous => {
                let code = if matches!(operation, PredefinedOperation::Ambiguous) {
                    ErrorCode::ErrAmbigBinaryOps
                } else {
                    ErrorCode::ErrBadBinaryOps
                };
                let (shown_left, shown_right) = (self.display(stored), self.display(&value.ty));
                self.report(code, span, &[&text, &shown_left, &shown_right]);
                return true;
            }
        };
        // `string + int?` is a concatenation, which nothing lifts.
        let lifted = (lifted_left || lifted_right)
            && self.binder.special_of(&result) != Some(SpecialType::String);
        let stored_bare = &target_bare.ty;
        let fits = |this: &Self, result: &Type| {
            this.binder.converts_implicitly(result, stored_bare) && (lifted_left || !lifted)
        };
        if fits(self, &result) {
            return false;
        }
        let number_like = |kind: Option<CompoundOperand>| {
            matches!(
                kind,
                Some(CompoundOperand::Number | CompoundOperand::Enumeration)
            )
        };
        let shift = matches!(
            operator,
            BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::UnsignedRightShift
        );
        let explicit = number_like(self.compound_operand_kind(stored_bare))
            && number_like(self.compound_operand_kind(&result));
        let shown_result = if lifted {
            let wrapped = self.nullable_of(result.clone());
            self.display(&wrapped)
        } else {
            self.display(&result)
        };
        let shown_stored = self.display(stored);
        if explicit {
            if lifted_left || !lifted {
                if shift
                    || self.binder.converts_implicitly(&value_bare.ty, stored_bare)
                    || self.constant_fits(&value_bare, stored_bare)
                {
                    return false;
                }
                // An `int` constant outside the small integer on the left
                // is said to be that, not to need a cast.
                if !lifted
                    && let Some(ConstantValue::Int32(constant)) = self.binder.folded(value)
                    && matches!(
                        self.binder.special_of(stored_bare),
                        Some(
                            SpecialType::SByte
                                | SpecialType::Byte
                                | SpecialType::Int16
                                | SpecialType::UInt16
                                | SpecialType::UInt32
                        )
                    )
                    && self.binder.special_of(&value.ty) == Some(SpecialType::Int32)
                {
                    let text = constant.to_string();
                    self.report(ErrorCode::ErrConstOutOfRange, span, &[&text, &shown_stored]);
                    return true;
                }
            }
            self.report(
                ErrorCode::ErrNoImplicitConvCast,
                span,
                &[&shown_result, &shown_stored],
            );
        } else {
            self.report(
                ErrorCode::ErrNoImplicitConv,
                span,
                &[&shown_result, &shown_stored],
            );
        }
        true
    }

    pub(super) fn bind_compound_assignment(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(operator) = compound_operator(node.kind()) else {
            return BoundExpression::error(span);
        };
        let mut children = node.children();
        let Some(target_node) = children.next() else {
            return BoundExpression::error(span);
        };
        let target = self.bind_expression(&target_node);
        let Some(value_node) = children.next() else {
            return target;
        };
        let value = self.bind_expression(&value_node);
        // `n ??= 0` on an `int`, which is never null.
        if operator == BinaryOperator::Coalesce && self.wraps_in_nullable(&target.ty) {
            let (shown_left, shown_right) = (self.display(&target.ty), self.display(&value.ty));
            self.report(
                ErrorCode::ErrBadBinaryOps,
                span,
                &["??=", &shown_left, &shown_right],
            );
            return BoundExpression::error(span);
        }
        // `a?.b += c` (C# 14) does the whole compound assignment where `a`
        // is not null, and nothing otherwise.
        let target = match target.kind {
            BoundExpressionKind::Conversion { operand, .. }
                if matches!(operand.kind, BoundExpressionKind::ConditionalAccess { .. }) =>
            {
                *operand
            }
            kind => BoundExpression::new(kind, target.ty, target.span),
        };
        if matches!(target.kind, BoundExpressionKind::ConditionalAccess { .. }) {
            return self.write_through(target, span, &mut |this, target| {
                let stored = target.ty.clone();
                let value = if operator == BinaryOperator::Coalesce {
                    this.convert(value.clone(), &stored)
                } else {
                    value.clone()
                };
                let ty = match this.binder.nullable_underlying(&stored) {
                    Some(inner) if operator == BinaryOperator::Coalesce => inner,
                    _ => stored,
                };
                BoundExpression::new(
                    BoundExpressionKind::CompoundAssignment {
                        target: Box::new(target),
                        operator,
                        value: Box::new(value),
                    },
                    ty,
                    span,
                )
            });
        }
        let stored = target.ty.clone();
        // `x.E += h` on an event of another type, or of a referenced
        // assembly, is a call to its `add_E` (§12.21.5): only inside the
        // type that declares a field-like event is the event its field.
        if let BoundExpressionKind::Field { receiver, field } = &target.kind
            && matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract)
            && self.kind_of(*field) == SymbolKind::Event
            && !self.event_is_a_field_here(*field)
        {
            let (receiver, event) = (receiver.clone(), *field);
            let handler = self.convert(value, &stored);
            return BoundExpression::new(
                BoundExpressionKind::EventAssignment {
                    receiver,
                    event,
                    add: operator == BinaryOperator::Add,
                    handler: Box::new(handler),
                },
                Type::Void,
                span,
            );
        }
        // `x op= d` and `d op= y` are an operation the runtime binds, and a
        // store of what it gives back (§12.21.4).
        if operator != BinaryOperator::Coalesce
            && (matches!(stored, Type::Dynamic) || matches!(value.ty, Type::Dynamic))
        {
            return BoundExpression::new(
                BoundExpressionKind::CompoundAssignment {
                    target: Box::new(target),
                    operator,
                    value: Box::new(value),
                },
                stored,
                span,
            );
        }
        // `a += b` on predefined types is `a = (T)(a + b)` only where the
        // cast is one the language writes for the programmer (§12.21.4).
        if operator != BinaryOperator::Coalesce
            && self.check_compound_result(operator, &target, &value, span)
        {
            return BoundExpression::new(
                BoundExpressionKind::CompoundAssignment {
                    target: Box::new(target),
                    operator,
                    value: Box::new(value),
                },
                stored,
                span,
            );
        }
        // `c ??= 3` on an `int?` writes an `int?`: what is stored is always
        // the variable's own type, whatever the right-hand side was written
        // as. The arithmetic operators convert in the emitter, where the
        // result of the operation is what gets stored; this one stores the
        // right-hand side itself. What the whole thing *is*, though, is the
        // `int` (§12.21.4): either side of the `??` is one by then.
        let mut ty = stored.clone();
        // `handler += Method` names a method group, and the delegate on the
        // left is what says which method and what delegate it becomes.
        let is_delegate = stored.symbol().is_some_and(|symbol| {
            self.binder.compilation().symbols().get(symbol).type_kind() == Some(TypeKind::Delegate)
        });
        let value =
            if is_delegate && matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract) {
                self.convert(value, &stored)
            } else if operator == BinaryOperator::Coalesce {
                // `a ??= default` on an `int?` is the `int` zero, not the
                // null that `default` of the variable's own type would be:
                // Roslyn tries the underlying type first.
                let mut value = value;
                if let Some(underlying) = self.binder.nullable_underlying(&stored)
                    && matches!(value.kind, BoundExpressionKind::Default(Type::Error))
                {
                    value = self.convert(value, &underlying);
                    ty = underlying;
                } else if let Some(underlying) = self.binder.nullable_underlying(&stored)
                    && !typeless(&value)
                    && !matches!(value.ty, Type::Null | Type::Error)
                    && self.binder.nullable_underlying(&value.ty).is_none()
                    && (self.binder.converts_implicitly(&value.ty, &underlying)
                        || self.constant_fits(&value, &underlying))
                {
                    ty = underlying;
                }
                self.convert(value, &stored)
            } else {
                value
            };
        // `s += t` where the type declares the `+`: `s = s + t` through
        // that operator (§12.21.4), written out for a target that costs
        // nothing to read twice — a variable, a parameter, a field of
        // `this`, or a field of any of those, however deep: `placement.
        // Position += offset` on a `ref` local of a struct holding a
        // `Vector3`. Anything dearer keeps the built-in form.
        fn cheap(place: &BoundExpression) -> bool {
            match &place.kind {
                BoundExpressionKind::Local(_)
                | BoundExpressionKind::Parameter(_)
                | BoundExpressionKind::This => true,
                BoundExpressionKind::Field { receiver, .. } => {
                    receiver.as_deref().is_none_or(cheap)
                }
                _ => false,
            }
        }
        let plain_place = cheap(&target);
        if plain_place
            && !is_delegate
            && operator != BinaryOperator::Coalesce
            && let Some(call) = self.user_defined_operator(operator, &target, &value, span)
        {
            let result = self.convert(call, &stored);
            return BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(target),
                    value: Box::new(result),
                },
                stored,
                span,
            );
        }
        // A dearer place — `holder.Value += x`, `items[i] += x` — is read
        // and written through temporaries that hold what locates it, each
        // evaluated once and in order.
        if !plain_place
            && !is_delegate
            && operator != BinaryOperator::Coalesce
            && self
                .user_defined_operator(operator, &target, &value, span)
                .is_some()
            && let Some((mut prelude, place)) = self.kept_place(&target)
            && let Some(call) = self.user_defined_operator(operator, &place, &value, span)
        {
            let result = self.convert(call, &stored);
            prelude.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(place),
                    value: Box::new(result),
                },
                stored.clone(),
                span,
            ));
            return BoundExpression::new(BoundExpressionKind::Sequence(prelude), stored, span);
        }
        // `n += a` on an `int?` is `n = (int?)(n + a)` with the `+` lifted
        // (§12.21.4): null in, null out.
        if plain_place
            && !is_delegate
            && operator != BinaryOperator::Coalesce
            && self.binder.nullable_underlying(&stored).is_some()
            && !typeless(&value)
        {
            let combined = self.bind_binary_on(operator, target.clone(), value, span);
            if !combined.ty.is_error() {
                let result = self.convert(combined, &stored);
                return BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(target),
                        value: Box::new(result),
                    },
                    stored,
                    span,
                );
            }
            return combined;
        }
        // `y += 5` on an `IntHolder?` that converts to and from `int`: the
        // predefined `+` through the conversions, and the result converted
        // back to what is stored, explicitly if it has to be (§12.21.4). A
        // dearer place — `collider.includeLayers |= mask` on Unity's
        // `LayerMask`, a property — is read and written through
        // temporaries, as for an operator the type declares.
        let converts = !is_delegate
            && operator != BinaryOperator::Coalesce
            && (!self.predefined_conversions_of(&stored).is_empty()
                || !self.predefined_conversions_of(&value.ty).is_empty());
        let located = if !converts {
            None
        } else if plain_place {
            Some((Vec::new(), target.clone()))
        } else {
            self.kept_place(&target)
        };
        if let Some((prelude, place)) = located
            && let Some(result) = self.binary_through_conversions(operator, &place, &value, span)
            && !result.ty.is_error()
        {
            let target = place;
            let base = |body: &Self, ty: &Type| {
                body.binder
                    .nullable_underlying(ty)
                    .unwrap_or_else(|| ty.clone())
            };
            let (from, to) = (base(self, &result.ty), base(self, &stored));
            let predefined = |body: &Self, ty: &Type| {
                body.binder.special_of(ty).is_some() || body.binder.enum_underlying(ty).is_some()
            };
            let back = if result.ty == stored {
                Some(result)
            } else if predefined(self, &from) && predefined(self, &to) {
                // `x -= t` on an `E` computes in the underlying type and
                // casts back, as any compound assignment on an enum does.
                let span = result.span;
                self.classify(&result.ty, &stored).map(|conversion| {
                    BoundExpression::new(
                        BoundExpressionKind::Conversion {
                            operand: Box::new(result),
                            conversion,
                            written: true,
                        },
                        stored.clone(),
                        span,
                    )
                })
            } else {
                self.binder
                    .implicit_operator(&from, &to)
                    .or_else(|| self.binder.explicit_operator(&from, &to))
                    .map(|operator| {
                        if self.binder.nullable_underlying(&stored).is_none()
                            && self.binder.nullable_underlying(&result.ty).is_some()
                        {
                            let span = result.span;
                            let unwrapped = BoundExpression::new(
                                BoundExpressionKind::Conversion {
                                    operand: Box::new(result),
                                    conversion: ConversionKind::NullableUnwrap,
                                    written: false,
                                },
                                from.clone(),
                                span,
                            );
                            self.operator_call(operator, unwrapped, stored.clone())
                        } else {
                            self.convert_through_operator(result, operator, &stored)
                        }
                    })
            };
            if let Some(back) = back {
                let assignment = BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(target),
                        value: Box::new(back),
                    },
                    stored.clone(),
                    span,
                );
                if prelude.is_empty() {
                    return assignment;
                }
                let mut steps = prelude;
                steps.push(assignment);
                return BoundExpression::new(BoundExpressionKind::Sequence(steps), stored, span);
            }
        }
        BoundExpression::new(
            BoundExpressionKind::CompoundAssignment {
                target: Box::new(target),
                operator,
                value: Box::new(value),
            },
            ty,
            span,
        )
    }
}

/// The innermost access of a `?.` chain: what `a?.b?.c` finally reads or
/// writes, under whatever nullable wrapping each step added.
fn assigned_through(target: &BoundExpression) -> &BoundExpression {
    match &target.kind {
        BoundExpressionKind::ConditionalAccess { access, .. } => assigned_through(access),
        BoundExpressionKind::Conversion { operand, .. }
            if matches!(operand.kind, BoundExpressionKind::ConditionalAccess { .. }) =>
        {
            assigned_through(operand)
        }
        _ => target,
    }
}

/// What a predefined operator makes of two operands.
pub(super) enum PredefinedOperation {
    Result(Type),
    Inapplicable,
    Ambiguous,
    /// Working it out reported the mistake already.
    Reported,
}

/// What kind of predefined type one side of a compound assignment is.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CompoundOperand {
    Number,
    Boolean,
    Text,
    Object,
    Enumeration,
}
