//! Operators: unary, binary, `++` and `--`, user-defined and lifted ones.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, Evidence, binary_operator, retype_default_beside, typeless};
use crate::binder::Diagnostics;
use crate::bound::{BoundExpression, BoundExpressionKind, ConstantValue, IncrementOperator};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// Whether arithmetic at `span` traps on overflow: the innermost
    /// `checked` or `unchecked` around it says so, and outside any the
    /// compilation does (`/checked`). The regions are recorded as they are
    /// entered, so an expression being bound already sees the ones around
    /// it.
    pub(super) fn in_checked_context(&self, span: TextSpan) -> bool {
        self.body
            .checked_regions
            .iter()
            .filter(|(region, _)| region.start() <= span.start() && span.end() <= region.end())
            .min_by_key(|(region, _)| region.length())
            .map_or_else(
                || self.binder.compilation().options().check_overflow,
                |(_, checked)| *checked,
            )
    }

    /// Whether the innermost `checked` or `unchecked` around `span` is an
    /// `unchecked`: the one thing that lets a constant overflow (§12.23).
    /// What `/checked` says does not come into it.
    fn explicitly_unchecked(&self, span: TextSpan) -> bool {
        self.body
            .checked_regions
            .iter()
            .filter(|(region, _)| region.start() <= span.start() && span.end() <= region.end())
            .min_by_key(|(region, _)| region.length())
            .is_some_and(|(_, checked)| !*checked)
    }

    /// CS0220 and CS0020: integer arithmetic on constants that overflows the
    /// type it is worked out in, outside `unchecked`, and `/` or `%` of a
    /// constant by a constant zero. Both are found when the compiler works
    /// the value out, so both are errors however the code is reached, and
    /// neither is one where an operand is not a constant: `x / 0` throws
    /// when it runs.
    ///
    /// `bound` is what a binary operator or a unary minus was bound to;
    /// anything but a predefined integer operator on two constants is left
    /// alone.
    pub(super) fn check_constant_arithmetic(&mut self, bound: &BoundExpression) {
        use crate::bound::UnaryOperator;
        use crate::constant::{Integers, as_exact, integer_range, integers};
        let ty = self
            .binder
            .enum_underlying(&bound.ty)
            .unwrap_or_else(|| bound.ty.clone());
        let special = self.binder.special_of(&ty);
        let Some((low, high)) = integer_range(special) else {
            return;
        };
        let exact = match &bound.kind {
            BoundExpressionKind::Binary {
                operator,
                left,
                right,
            } if matches!(
                operator,
                BinaryOperator::Add
                    | BinaryOperator::Subtract
                    | BinaryOperator::Multiply
                    | BinaryOperator::Divide
                    | BinaryOperator::Modulo
            ) =>
            {
                // The right first: in a long `a + b + c` it is the leaf, and
                // a chain that is not constant is turned down at once.
                let Some(right) = self.binder.folded(right).as_ref().and_then(as_exact) else {
                    return;
                };
                let Some(left) = self.binder.folded(left).as_ref().and_then(as_exact) else {
                    return;
                };
                match integers(*operator, left, right, special) {
                    Some(Integers::Value(exact)) => exact,
                    Some(Integers::DivisionByZero) => {
                        if !self.reported_within(bound.span) {
                            self.report(ErrorCode::ErrIntDivByZero, bound.span, &[]);
                        }
                        return;
                    }
                    None => return,
                }
            }
            BoundExpressionKind::Unary {
                operator: UnaryOperator::Minus,
                operand,
            } => {
                let Some(operand) = self.binder.folded(operand).as_ref().and_then(as_exact) else {
                    return;
                };
                -operand
            }
            _ => return,
        };
        if (exact < low || exact > high)
            && !self.explicitly_unchecked(bound.span)
            && !self.reported_within(bound.span)
        {
            self.report(ErrorCode::ErrCheckedOverflow, bound.span, &[]);
        }
    }

    /// Whether a part of the expression at `span` has overflowed or divided
    /// by zero already: it has no value then, and what is worked out from it
    /// is not a second mistake.
    pub(super) fn reported_within(&self, span: TextSpan) -> bool {
        self.body.diagnostics.iter().any(|(tree, diagnostic)| {
            *tree == self.tree
                && matches!(
                    diagnostic.code(),
                    ErrorCode::ErrCheckedOverflow | ErrorCode::ErrIntDivByZero
                )
                && span.start() <= diagnostic.span().start()
                && diagnostic.span().end() <= span.end()
        })
    }

    /// CS0221: a constant cast to an integral type it does not fit, outside
    /// `unchecked`. Constants are checked whatever `/checked` says: only an
    /// `unchecked` around the cast lets `(int)2147483648L` wrap.
    pub(super) fn check_constant_cast(
        &mut self,
        constant: &crate::bound::ConstantValue,
        ty: &Type,
        span: TextSpan,
    ) {
        use crate::bound::ConstantValue;
        if self.explicitly_unchecked(span) {
            return;
        }
        let target = self
            .binder
            .enum_underlying(ty)
            .unwrap_or_else(|| ty.clone());
        let range: (i128, i128) = match self.binder.special_of(&target) {
            Some(SpecialType::SByte) => (i8::MIN.into(), i8::MAX.into()),
            Some(SpecialType::Byte) => (u8::MIN.into(), u8::MAX.into()),
            Some(SpecialType::Int16) => (i16::MIN.into(), i16::MAX.into()),
            Some(SpecialType::UInt16 | SpecialType::Char) => (u16::MIN.into(), u16::MAX.into()),
            Some(SpecialType::Int32) => (i32::MIN.into(), i32::MAX.into()),
            Some(SpecialType::UInt32) => (u32::MIN.into(), u32::MAX.into()),
            Some(SpecialType::Int64) => (i64::MIN.into(), i64::MAX.into()),
            Some(SpecialType::UInt64) => (u64::MIN.into(), u64::MAX.into()),
            _ => return,
        };
        let (fits, text) = match constant {
            ConstantValue::Int32(value) => {
                let value = i128::from(*value);
                (range.0 <= value && value <= range.1, value.to_string())
            }
            ConstantValue::UInt32(value) => {
                let value = i128::from(*value);
                (range.0 <= value && value <= range.1, value.to_string())
            }
            ConstantValue::Int64(value) => {
                let value = i128::from(*value);
                (range.0 <= value && value <= range.1, value.to_string())
            }
            ConstantValue::UInt64(value) => {
                let value = i128::from(*value);
                (range.0 <= value && value <= range.1, value.to_string())
            }
            ConstantValue::Char(value) => {
                let value = i128::from(u32::from(*value));
                (range.0 <= value && value <= range.1, value.to_string())
            }
            // A floating constant is truncated toward zero, and has to land
            // inside the range; NaN and the infinities land nowhere. The
            // top of the range is compared as the power of two past it:
            // `long.MaxValue` itself is no `double`, and the one that
            // stands for it is 2^63, which is out.
            ConstantValue::Single(value) => {
                let value = f64::from(*value).trunc();
                (
                    value.is_finite() && range.0 as f64 <= value && value < (range.1 + 1) as f64,
                    value.to_string(),
                )
            }
            ConstantValue::Double(value) => {
                let truncated = value.trunc();
                (
                    truncated.is_finite()
                        && range.0 as f64 <= truncated
                        && truncated < (range.1 + 1) as f64,
                    value.to_string(),
                )
            }
            _ => return,
        };
        if !fits {
            let shown = self.display(ty);
            self.report(ErrorCode::ErrConstOutOfRangeChecked, span, &[&text, &shown]);
        }
    }

    /// The operator methods named `name` that a type (and its bases)
    /// offers for an operation at `span`. In a checked context an operator
    /// with a checked form (C# 11) is looked up by both names, and a regular
    /// operator gives way to a checked one its own type declares with the
    /// same signature — Roslyn's `DoOperatorsPair` — so `checked(a - b)`
    /// calls `operator checked -` where there is one and the regular `-`
    /// where there is not.
    pub(super) fn operator_candidates(
        &self,
        symbol: SymbolId,
        name: &str,
        span: TextSpan,
    ) -> Vec<SymbolId> {
        let methods = |name: &str| -> Vec<SymbolId> {
            self.binder
                .lookup_member(symbol, name)
                .into_iter()
                .filter(|candidate| self.kind_of(*candidate) == SymbolKind::Method)
                .collect()
        };
        let regular = methods(name);
        let Some(checked_name) =
            crate::declare::checked_operator_name(name).filter(|_| self.in_checked_context(span))
        else {
            return regular;
        };
        let mut candidates = methods(checked_name);
        if candidates.is_empty() {
            return regular;
        }
        let symbols = self.binder.compilation().symbols();
        let signature = |method: SymbolId| {
            let mut sink = Diagnostics::new();
            let parameters: Vec<Type> = symbols
                .get(method)
                .as_method()
                .map(|detail| {
                    detail
                        .parameters
                        .iter()
                        .map(|parameter| self.binder.type_of(*parameter, &mut sink))
                        .collect()
                })
                .unwrap_or_default();
            let returns = self.binder.type_of(method, &mut sink);
            (symbols.get(method).container, parameters, returns)
        };
        let paired: Vec<_> = candidates
            .iter()
            .map(|checked| signature(*checked))
            .collect();
        candidates.extend(
            regular
                .into_iter()
                .filter(|operator| !paired.contains(&signature(*operator))),
        );
        candidates
    }

    /// `a++` on a type with no `++` of its own that converts to a number
    /// and back (§12.9.6): the predefined `++` of that number, with the
    /// conversions on either side, written out through temporaries.
    pub(super) fn increment_through_conversion(
        &mut self,
        target: &BoundExpression,
        operator: IncrementOperator,
        prefix: bool,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let ty = target.ty.clone();
        let symbols = self.binder.compilation().symbols();
        if ty.is_error()
            || ty.symbol().is_none()
            || self.binder.special_of(&ty).is_some()
            || self.binder.enum_underlying(&ty).is_some()
            || self.binder.nullable_underlying(&ty).is_some()
            || matches!(ty, Type::TypeParameter(_) | Type::Pointer(_))
        {
            return None;
        }
        let plain = matches!(
            target.kind,
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
        ) || matches!(
            &target.kind,
            BoundExpressionKind::Field { receiver, field }
                if symbols.get(*field).kind == SymbolKind::Field
                    && receiver.as_ref().is_none_or(|receiver| matches!(receiver.kind, BoundExpressionKind::This))
        );
        if !plain {
            return None;
        }
        let specials = [
            SpecialType::SByte,
            SpecialType::Byte,
            SpecialType::Int16,
            SpecialType::UInt16,
            SpecialType::Int32,
            SpecialType::UInt32,
            SpecialType::Int64,
            SpecialType::UInt64,
            SpecialType::Char,
            SpecialType::Single,
            SpecialType::Double,
            SpecialType::Decimal,
        ];
        // The numbers themselves, then their nullables, whose `++` is the
        // lifted one: a type that converts to an `int?` and back steps
        // through it, and stays null where it was.
        let numbers: Vec<Type> = specials
            .iter()
            .map(|special| self.special(*special))
            .chain(
                specials
                    .iter()
                    .map(|special| self.nullable_of(self.special(*special))),
            )
            .collect();
        let (number, to_number, back) = numbers.into_iter().find_map(|number| {
            let to_number = self.binder.implicit_operator(&ty, &number)?;
            let back = self
                .binder
                .implicit_operator(&number, &ty)
                .or_else(|| self.binder.explicit_operator(&number, &ty))?;
            Some((number, to_number, back))
        })?;
        let step = self.declare_synthetic_local("step", number.clone());
        let local =
            |ty: &Type, id| BoundExpression::new(BoundExpressionKind::Local(id), ty.clone(), span);
        let assign = |to: BoundExpression, value: BoundExpression| {
            let ty = to.ty.clone();
            BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(to),
                    value: Box::new(value),
                },
                ty,
                span,
            )
        };
        let mut steps = Vec::new();
        let old = (!prefix).then(|| self.declare_synthetic_local("old", ty.clone()));
        let source = match old {
            Some(old) => {
                steps.push(assign(local(&ty, old), target.clone()));
                local(&ty, old)
            }
            None => target.clone(),
        };
        let converted = self.operator_call(to_number, source, number.clone());
        steps.push(assign(local(&number, step), converted));
        steps.push(BoundExpression::new(
            BoundExpressionKind::Increment {
                target: Box::new(local(&number, step)),
                operator,
                prefix: true,
                method: None,
            },
            number.clone(),
            span,
        ));
        let back = self.operator_call(back, local(&number, step), ty.clone());
        steps.push(assign(target.clone(), back));
        if let Some(old) = old {
            steps.push(local(&ty, old));
        }
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            ty,
            span,
        ))
    }

    /// The `op_` method an operator means on a type that declares one.
    ///
    /// C# looks on both operand types, because `a + b` may be defined by
    /// either. `&&` and `||` are not among them: they decide whether to
    /// evaluate their right operand at all, which a method call cannot.
    pub(super) fn user_defined_operator(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let name = operator_method_name(operator)?;
        // Two operands of types the language has operators of its own for
        // find nothing below but an extension block's: said before anything
        // is copied, since a long `a + b + c` asks this at every `+`.
        let built_in = |ty: &Type| {
            let ty = self
                .binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone());
            self.binder
                .special_of(&ty)
                .is_some_and(|special| special != SpecialType::Decimal)
        };
        if built_in(&left.ty)
            && built_in(&right.ty)
            && self
                .binder
                .extension_members_in_scope(&self.context, name)
                .is_empty()
        {
            return None;
        }
        // An `nint` or an `nuint` is a number, with the language's own
        // operators (C# 11): where one of those takes the operands, the
        // `op_Addition(IntPtr, int)` the type declares for older compilers
        // is not asked. They give the same value until `checked` says the
        // sum must fit, which only the language's own `+` checks.
        let native = |ty: &Type| {
            let ty = self
                .binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone());
            self.binder.native_int(&ty)
        };
        let number = |ty: &Type| {
            let ty = self
                .binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone());
            self.binder.native_int(&ty).is_some()
                || self
                    .binder
                    .special_of(&ty)
                    .is_some_and(SpecialType::is_numeric)
        };
        if let (left_native, right_native) = (native(&left.ty), native(&right.ty))
            && (left_native.is_some() || right_native.is_some())
            && (self
                .binder
                .binary_result(operator, &left.ty, &right.ty)
                .is_some()
                // Two numbers the language's operators do not take, `nuint`
                // and `long`, are an error rather than the older `op_` call.
                || (number(&left.ty) && number(&right.ty))
                // A non-negative `int` constant is an `nuint` (§10.2.11).
                || (left_native == Some(true)
                    && right_native.is_none()
                    && self.constant_fits(right, &left.ty))
                || (right_native == Some(true)
                    && left_native.is_none()
                    && self.constant_fits(left, &right.ty)))
        {
            return None;
        }
        let arguments = vec![left.ty.clone(), right.ty.clone()];
        let symbols = self.binder.compilation().symbols();

        // Each candidate with the operand type it was found on: that type is
        // the receiver its signature is read through, and
        // `Vector128<ulong> + Vector128<ulong>` calls an operator declared on
        // `Vector128<T>` whose parameters are only `Vector128<ulong>` once
        // the construction has said what `T` is.
        // `x == y` on two `T?`s looks for `T`'s operators (§12.4.6): the
        // wrapper declares none of its own, and `TypeWithAnnotations`
        // declares its `==` over two `TypeWithAnnotations?` for that very
        // call.
        // A tuple's operators are its `ValueTuple`'s.
        let operands: Vec<Type> = [&left.ty, &right.ty]
            .into_iter()
            .map(|ty| {
                let ty = self
                    .binder
                    .nullable_underlying(ty)
                    .unwrap_or_else(|| ty.clone());
                match &ty {
                    Type::Tuple(elements) => self.tuple_as_named(elements),
                    _ => ty,
                }
            })
            .collect();
        // What the operands are beyond their types counts as it does for a
        // call: `k == $"frog"` reaches an operator taking an `IFormattable`.
        let evidence = self.evidence(&[left.clone(), right.clone()]);
        let is_interface = |ty: &Type| {
            ty.symbol()
                .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Interface))
        };
        // The operators of classes and structs come first (C# 8): an
        // interface's are looked at only where none of those applies, so
        // that an interface declaring one changes no `a op b` that already
        // meant something.
        let mut resolved = None;
        let mut any = false;
        for interfaces in [false, true] {
            let mut candidates: Vec<(SymbolId, Type)> = Vec::new();
            for ty in operands.iter().filter(|ty| is_interface(ty) == interfaces) {
                let Some(symbol) = ty.symbol() else { continue };
                // Not on a type the language has operators of its own for:
                // those are built in, and going through a method would
                // change what `1 + 2` means. Everything else in the core
                // library is an ordinary type that happens to live there —
                // `Half`, `TimeSpan`, `IntPtr` — and `<` on one is the
                // `op_LessThan` it declares. `decimal` is the exception: the
                // language has operators for it, but the runtime has none.
                // Every one of them is a method on `System.Decimal`, and
                // emitting `add` on two of them is a program the runtime
                // refuses.
                if self
                    .binder
                    .special_of(ty)
                    .is_some_and(|special| special != SpecialType::Decimal)
                {
                    continue;
                }
                // A class's own, the checked ones first in a checked
                // context (C# 11).
                let found = if interfaces {
                    self.interface_operators(symbol, name, &arguments, &evidence, ty)
                } else {
                    self.operator_candidates(symbol, name, span)
                };
                for candidate in found {
                    if symbols.get(candidate).kind == SymbolKind::Method
                        && !candidates.iter().any(|(found, _)| *found == candidate)
                    {
                        candidates.push((candidate, ty.clone()));
                    }
                }
            }
            any |= !candidates.is_empty();
            resolved = self.resolve_operator(&candidates, &operands, &arguments, &evidence);
            if resolved.is_some() {
                break;
            }
        }
        // An operator an extension block (C# 14) gave one of the operand
        // types, where the types declare none of their own.
        let predefined_first = self.predefined_conversions_of(&left.ty).is_empty()
            && self.predefined_conversions_of(&right.ty).is_empty();
        // The language's own operators come first: where one takes the
        // operands, no block's is asked.
        if !any
            && (predefined_first
                || self
                    .binary_through_conversions(operator, left, right, span)
                    .is_none())
        {
            if self.predefined_binary_applies(operator, &left.ty, &right.ty) {
                return None;
            }
            let (resolved, _, given) =
                self.resolve_extension_operator(name, &[left.clone(), right.clone()], span)?;
            return Some(self.extension_operator_call(resolved, given, span));
        }
        let (method, receiver) = resolved?;
        let ty = self.member_type(method, &receiver);
        let arguments = self.convert_arguments(
            method,
            vec![left.clone(), right.clone()],
            &receiver,
            &HashMap::new(),
            span,
        );
        // The operator of a constructed type is a member of that
        // construction, which stands as the receiver of the call so that
        // the emitter names it (`Wrapper<T>.op_Equality`).
        let container = self.binder.compilation().symbols().get(method).container;
        let through = container
            .filter(|container| receiver.symbol() == Some(*container))
            .map(|container| {
                Box::new(BoundExpression::new(
                    BoundExpressionKind::TypeExpression(container),
                    receiver.clone(),
                    span,
                ))
            });
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: through,
                method,
                type_arguments: Vec::new(),
                arguments,
                virtual_call: false,
            },
            ty,
            span,
        ))
    }

    /// Whether the language has an operator of its own for the two types: an
    /// extension block's is asked only where it has none. Equality is the
    /// language's only for the built-in types and for two references, one of
    /// which converts to the other.
    fn predefined_binary_applies(
        &self,
        operator: BinaryOperator,
        left: &Type,
        right: &Type,
    ) -> bool {
        // An operand with no type of its own, a lambda, is no operand of the
        // language's operators.
        if left.is_error() || right.is_error() {
            return false;
        }
        if !matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) {
            return self.binder.binary_result(operator, left, right).is_some();
        }
        let symbols = self.binder.compilation().symbols();
        let builtin = |ty: &Type| {
            let ty = self
                .binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone());
            self.binder.special_of(&ty).is_some()
                || self.binder.enum_underlying(&ty).is_some()
                || matches!(ty, Type::Pointer(_))
        };
        // `x == null` is the language's on a reference or a nullable.
        let nullable_or_reference = |ty: &Type| {
            ty.is_reference_type(symbols) || self.binder.nullable_underlying(ty).is_some()
        };
        if (matches!(left, Type::Null) && nullable_or_reference(right))
            || (matches!(right, Type::Null) && nullable_or_reference(left))
        {
            return true;
        }
        let value_builtin = |ty: &Type| builtin(ty) && !ty.is_reference_type(symbols);
        if builtin(left) && builtin(right) {
            return self.binder.binary_result(operator, left, right).is_some();
        }
        // A number or a pointer is equal only to what converts to one.
        if value_builtin(left) || value_builtin(right) {
            return false;
        }
        let reference = |ty: &Type| matches!(ty, Type::Null) || ty.is_reference_type(symbols);
        reference(left)
            && reference(right)
            && (self.binder.converts_implicitly(left, right)
                || self.binder.converts_implicitly(right, left))
    }

    /// The operator overload resolution picks among `candidates`, each found
    /// on an operand's type, with the type it was found on: the left
    /// operand's are tried before the right's.
    fn resolve_operator(
        &self,
        candidates: &[(SymbolId, Type)],
        operands: &[Type],
        arguments: &[Type],
        evidence: &Evidence,
    ) -> Option<(SymbolId, Type)> {
        operands.iter().find_map(|receiver| {
            let group: Vec<SymbolId> = candidates
                .iter()
                .filter(|(_, found_on)| found_on == receiver)
                .map(|(candidate, _)| *candidate)
                .collect();
            if group.is_empty() {
                return None;
            }
            self.resolve_overload(&group, arguments, evidence, receiver)
                .map(|method| (method, receiver.clone()))
        })
    }

    /// The operators `name` an interface offers an operation on it (C# 8):
    /// its own where one of them applies, and otherwise those of each
    /// interface it derives from that has one that applies, less those of an
    /// interface a more derived one of them hides. `I5 : I1, I2` with `I2 :
    /// I1` and the same `-` in both is `I2`'s.
    fn interface_operators(
        &self,
        interface: SymbolId,
        name: &str,
        arguments: &[Type],
        evidence: &Evidence,
        receiver: &Type,
    ) -> Vec<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let declared = |ty: SymbolId| -> Vec<SymbolId> {
            symbols
                .lookup(ty, name)
                .iter()
                .copied()
                .filter(|member| symbols.get(*member).kind == SymbolKind::Method)
                .collect()
        };
        let applies = |group: &[SymbolId]| {
            !group.is_empty()
                && self
                    .resolve_overload(group, arguments, evidence, receiver)
                    .is_some()
        };
        let own = declared(interface);
        if applies(&own) {
            return own;
        }
        let applicable: Vec<SymbolId> = self
            .base_interfaces(interface)
            .into_iter()
            .filter(|base| applies(&declared(*base)))
            .collect();
        applicable
            .iter()
            .filter(|base| {
                !applicable
                    .iter()
                    .any(|other| other != *base && self.base_interfaces(*other).contains(base))
            })
            .flat_map(|base| declared(*base))
            .collect()
    }

    /// `-x`, `+x`, `~x` or `!x` where the operand's type declares the
    /// operator: a call to it, with the type standing as the receiver so
    /// that a constructed type's operator is named through the
    /// construction.
    pub(super) fn user_defined_unary(
        &mut self,
        name: &str,
        operand: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let ty = operand.ty.clone();
        // A `T?` has the operators its `T` declares, taking the `T?` where
        // one does and lifted over it otherwise (§12.4.8).
        let underlying = self.binder.nullable_underlying(&ty);
        let declaring = underlying.clone().unwrap_or_else(|| ty.clone());
        let symbol = declaring.symbol()?;
        // The built-in types have their operators built in, bar the ones
        // that have none of this kind: `+o` on an `object` is for an
        // extension block's.
        if (self.binder.special_of(&declaring).is_some()
            && !matches!(
                self.binder.special_of(&declaring),
                Some(SpecialType::Object | SpecialType::String)
            ))
            || self.binder.enum_underlying(&declaring).is_some()
        {
            return None;
        }
        let candidates = self.operator_candidates(symbol, name, span);
        // An operator an extension block (C# 14) gave the operand's type,
        // where the type declares none of its own. The language's own
        // operators, reached through a conversion of the operand, come
        // before an extension block's.
        if candidates.is_empty() {
            if !self.predefined_conversions_of(&ty).is_empty() {
                return None;
            }
            if let Some((resolved, _, given)) =
                self.resolve_extension_operator(name, std::slice::from_ref(operand), span)
            {
                return Some(self.extension_operator_call(resolved, given, span));
            }
            // On a `T?` it is `T`'s operator, lifted.
            let inner = underlying?;
            let probe =
                BoundExpression::new(BoundExpressionKind::Default(inner.clone()), inner, span);
            let (resolved, _, _) = self.resolve_extension_operator(name, &[probe], span)?;
            let result = self
                .member_type(resolved.method, &Type::Void)
                .substitute(&resolved.substitution);
            let lifted = if self.wraps_in_nullable(&result) {
                self.nullable_of(result)
            } else {
                result
            };
            return self.lift_conversion(operand.clone(), &lifted, |this, value| {
                this.extension_operator_call(resolved, vec![value], span)
            });
        }
        let direct = self.resolve_overload(
            &candidates,
            std::slice::from_ref(&ty),
            &Evidence::default(),
            &declaring,
        );
        let lifted = underlying.and_then(|inner| {
            self.resolve_overload(
                &candidates,
                std::slice::from_ref(&inner),
                &Evidence::default(),
                &declaring,
            )
        });
        // The operator over the `T` lifted to `T?` is a candidate beside
        // the one written for `T?`, and a higher `[OverloadResolutionPriority]`
        // on it puts the other out.
        let method = match (direct, lifted) {
            (Some(direct), Some(lifted))
                if direct != lifted && self.highest_priority(&[direct, lifted]) == [lifted] =>
            {
                lifted
            }
            (Some(direct), _) => {
                return Some(self.unary_call(direct, operand.clone(), &declaring, span));
            }
            (None, lifted) => lifted?,
        };
        let result = self.member_type(method, &declaring);
        let lifted = if self.wraps_in_nullable(&result) {
            self.nullable_of(result)
        } else {
            result
        };
        self.lift_conversion(operand.clone(), &lifted, |this, value| {
            this.unary_call(method, value, &declaring, span)
        })
    }

    /// A call to a unary operator method, with its declaring type standing
    /// as the receiver so that a constructed type's operator is named
    /// through the construction.
    fn unary_call(
        &mut self,
        method: SymbolId,
        operand: BoundExpression,
        declaring: &Type,
        span: TextSpan,
    ) -> BoundExpression {
        let result = self.member_type(method, declaring);
        let arguments =
            self.convert_arguments(method, vec![operand], declaring, &HashMap::new(), span);
        let container = self.binder.compilation().symbols().get(method).container;
        let receiver = container
            .filter(|container| declaring.symbol() == Some(*container))
            .map(|container| {
                Box::new(BoundExpression::new(
                    BoundExpressionKind::TypeExpression(container),
                    declaring.clone(),
                    span,
                ))
            });
        BoundExpression::new(
            BoundExpressionKind::Call {
                receiver,
                method,
                type_arguments: Vec::new(),
                arguments,
                virtual_call: false,
            },
            result,
            span,
        )
    }

    /// The operand of a `+` whose other side is a `string`, brought to
    /// `string` by the user-defined implicit conversion it has to it: the
    /// concatenation then takes two strings (§12.10.5), not a string and an
    /// object. Anything else is left as it is.
    pub(super) fn convert_operand_to_string(&mut self, value: BoundExpression) -> BoundExpression {
        let string = self.special(SpecialType::String);
        // A type with a `+` of its own is asked that first.
        let declares_addition = value
            .ty
            .symbol()
            .is_some_and(|symbol| !self.binder.lookup_member(symbol, "op_Addition").is_empty());
        if value.ty == string
            || value.ty.is_error()
            || matches!(value.ty, Type::Null)
            || self.binder.special_of(&value.ty).is_some()
            || declares_addition
        {
            return value;
        }
        match self.binder.implicit_operator(&value.ty, &string) {
            Some(operator) => self.operator_call(operator, value, string),
            None => value,
        }
    }

    /// `h + 1` where `h` converts to a number (§12.4.5): the predefined
    /// operators are candidates too, reached through the operand's
    /// user-defined conversions, and the first pair of types that an
    /// operator takes is the one used.
    pub(super) fn binary_through_conversions(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if matches!(
            operator,
            BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr | BinaryOperator::Coalesce
        ) || left.ty.is_error()
            || right.ty.is_error()
        {
            return None;
        }
        let options = |body: &Self, value: &BoundExpression| {
            let mut options: Vec<(Type, Option<SymbolId>)> = vec![(value.ty.clone(), None)];
            options.extend(
                body.predefined_conversions_of(&value.ty)
                    .into_iter()
                    .map(|(ty, operator)| (ty, Some(operator))),
            );
            options
        };
        let mut lefts = options(self, left);
        let mut rights = options(self, right);
        if lefts.len() == 1 && rights.len() == 1 {
            return None;
        }
        let base = |body: &Self, ty: &Type| {
            body.binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone())
        };
        // A conversion to the other operand's own type is tried first: `x -
        // t` on an `E` where `t` converts to both `E` and `short` is `E -
        // E`, as Roslyn picks it.
        // Beside a `T?` the operator is the lifted one, which takes a `T?`:
        // `qa + s` on an `int?` converts `s` by its operator giving an
        // `int?` where it has both, the one giving the target exactly.
        let (left_base, right_base) = (base(self, &left.ty), base(self, &right.ty));
        let nullable = |body: &Self, ty: &Type| body.binder.nullable_underlying(ty).is_some();
        let (left_lifted, right_lifted) = (nullable(self, &left.ty), nullable(self, &right.ty));
        rights.sort_by_key(|(ty, _)| {
            (
                base(self, ty) != left_base,
                nullable(self, ty) != left_lifted,
            )
        });
        lefts.sort_by_key(|(ty, _)| {
            (
                base(self, ty) != right_base,
                nullable(self, ty) != right_lifted,
            )
        });
        let predefined = |body: &Self, ty: &Type| {
            let inner = base(body, ty);
            body.binder.special_of(&inner).is_some()
                || body.binder.enum_underlying(&inner).is_some()
        };
        for (left_type, left_operator) in &lefts {
            for (right_type, right_operator) in &rights {
                if left_operator.is_none() && right_operator.is_none() {
                    continue;
                }
                if !predefined(self, left_type) || !predefined(self, right_type) {
                    continue;
                }
                let takes = self
                    .binder
                    .binary_result(operator, &base(self, left_type), &base(self, right_type))
                    .is_some_and(|ty| !ty.is_error());
                if !takes {
                    continue;
                }
                let left = match left_operator {
                    Some(conversion) => {
                        self.convert_through_operator(left.clone(), *conversion, left_type)
                    }
                    None => left.clone(),
                };
                let right = match right_operator {
                    Some(conversion) => {
                        self.convert_through_operator(right.clone(), *conversion, right_type)
                    }
                    None => right.clone(),
                };
                return Some(self.bind_binary_on(operator, left, right, span));
            }
        }
        None
    }

    /// Whether one side is the `null` literal and the other a struct with no
    /// `==` at all, or a tuple: there is no operator to lift then (§12.4.8),
    /// so nothing compares the two (CS0019) — where a number, an enum or a
    /// struct that declares `==` has the lifted one.
    fn compares_a_struct_without_equality_with_null(
        &self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
    ) -> bool {
        let value = match (&left.ty, &right.ty) {
            (Type::Null, Type::Null) => return false,
            (Type::Null, _) => right,
            (_, Type::Null) => left,
            _ => return false,
        };
        let ty = &value.ty;
        if matches!(ty, Type::Tuple(_)) {
            return true;
        }
        let symbols = self.binder.compilation().symbols();
        let Type::Named { symbol, .. } = ty else {
            return false;
        };
        if symbols.get(*symbol).type_kind() != Some(crate::symbol::TypeKind::Struct)
            || self.binder.nullable_underlying(ty).is_some()
            || self
                .binder
                .special_of(ty)
                .is_some_and(|special| special.is_numeric() || special == SpecialType::Boolean)
        {
            return false;
        }
        // `nint` and `nuint` have the predefined operators too.
        let compilation = self.binder.compilation();
        if ["System.IntPtr", "System.UIntPtr"]
            .iter()
            .any(|name| compilation.type_by_metadata_name(name) == Some(*symbol))
        {
            return false;
        }
        let name = if operator == BinaryOperator::Equality {
            "op_Equality"
        } else {
            "op_Inequality"
        };
        self.binder.lookup_member(*symbol, name).is_empty()
    }

    /// Whether one side is the `null` literal and the other a value of a
    /// type that is never null — a struct, an enum, a number — with no
    /// `==` of its own that could take a null: the comparison is the lifted
    /// one, and settled before it runs.
    fn compares_a_value_with_null(&self, left: &BoundExpression, right: &BoundExpression) -> bool {
        let value = match (&left.ty, &right.ty) {
            (Type::Null, Type::Null) => return false,
            (Type::Null, _) => right,
            (_, Type::Null) => left,
            _ => return false,
        };
        let ty = &value.ty;
        let symbols = self.binder.compilation().symbols();
        if ty.is_error()
            || matches!(
                ty,
                Type::TypeParameter(_)
                    | Type::Pointer(_)
                    | Type::FunctionPointer(_)
                    | Type::Dynamic
            )
            || ty.is_reference_type(symbols)
            || self.binder.nullable_underlying(ty).is_some()
            || !matches!(ty, Type::Named { .. } | Type::Tuple(_))
        {
            return false;
        }
        // A struct whose own `==` takes something a null reaches decides
        // for itself.
        let Some(symbol) = ty.symbol() else {
            return true;
        };
        ["op_Equality", "op_Inequality"].iter().all(|name| {
            self.binder
                .lookup_member(symbol, name)
                .iter()
                .all(|operator| {
                    symbols.get(*operator).as_method().is_none_or(|detail| {
                        detail.parameters.iter().all(|parameter| {
                            let mut sink = Diagnostics::new();
                            let taken = self.binder.type_of(*parameter, &mut sink);
                            !taken.is_reference_type(symbols)
                                && self.binder.nullable_underlying(&taken).is_none()
                        })
                    })
                })
        })
    }

    /// `x && y` and `x || y` on a type that declares `&` or `|` and `false`
    /// or `true` (§12.14.3): `T.false(x) ? x : T.&(x, y)`, and `T.true(x) ?
    /// x : T.|(x, y)`, with `x` read once.
    fn user_defined_conditional_logic(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let (bitwise, test) = match operator {
            BinaryOperator::LogicalAnd => (BinaryOperator::BitwiseAnd, "op_False"),
            BinaryOperator::LogicalOr => (BinaryOperator::BitwiseOr, "op_True"),
            _ => return None,
        };
        // `s && s` on an `S1?` where `S1` declares `&(S1?, S1?)` and
        // `false(S1?)` is one too: the operators take the nullable itself.
        let underlying = self.binder.nullable_underlying(&left.ty);
        if left.ty.is_error()
            || left.ty.symbol().is_none()
            || self
                .binder
                .special_of(underlying.as_ref().unwrap_or(&left.ty))
                .is_some_and(|special| {
                    !matches!(special, SpecialType::Object | SpecialType::String)
                })
        {
            return None;
        }
        // Probed on values of the operand's type, so that nothing is bound
        // twice; the real operands go in below.
        let probe = BoundExpression::new(
            BoundExpressionKind::Default(left.ty.clone()),
            left.ty.clone(),
            span,
        );
        // `&(S1, S1)` lifted is an `&` of two `S1?`s, where `false(S1?)`
        // takes what it gives back.
        let combined = self
            .user_defined_operator(bitwise, &probe, right, span)
            .or_else(|| self.lift_user_defined_binary(bitwise, &probe, right, span))?;
        // The operator's operands and result are one type, and the operand
        // is tested as that type: `d && d` on a `D` derived from the `C`
        // that declares `&(C, C)` asks `C`'s `false` of `(C)d`.
        let left = &if combined.ty == left.ty {
            left.clone()
        } else if self.binder.converts_implicitly(&left.ty, &combined.ty)
            && matches!(
                &combined.kind,
                BoundExpressionKind::Call { arguments, .. }
                    if arguments.iter().all(|argument| argument.ty == combined.ty)
            )
        {
            self.convert(left.clone(), &combined.ty)
        } else {
            return None;
        };
        let probe = BoundExpression::new(
            BoundExpressionKind::Default(left.ty.clone()),
            left.ty.clone(),
            span,
        );
        self.user_defined_unary(test, &probe, span)?;
        let simple = matches!(
            left.kind,
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
        );
        let (tested, read) = if simple {
            (left.clone(), left.clone())
        } else {
            let held = self.declare_synthetic_local("left", left.ty.clone());
            let read =
                BoundExpression::new(BoundExpressionKind::Local(held), left.ty.clone(), span);
            let assigned = BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(left.clone()),
                },
                left.ty.clone(),
                span,
            );
            (assigned, read)
        };
        let condition = self.user_defined_unary(test, &tested, span)?;
        let boolean = self.special(SpecialType::Boolean);
        let condition = self.convert(condition, &boolean);
        let combined = self
            .user_defined_operator(bitwise, &read, right, span)
            .or_else(|| self.lift_user_defined_binary(bitwise, &read, right, span))?;
        let ty = left.ty.clone();
        Some(BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(condition),
                consequence: Box::new(read),
                alternative: Box::new(combined),
            },
            ty,
            span,
        ))
    }

    /// A constant operand taken to the unsigned type the other one has.
    ///
    /// Only the unsigned types need this. Everywhere else the wider of the two
    /// holds both, so promotion by type alone already answers; `uint` and
    /// `ulong` are the two that a signed type does not reach, and a constant
    /// that fits is exactly the case the language carves out.
    fn meet_constant(&mut self, value: BoundExpression, other: &Type) -> BoundExpression {
        // The same goes for an enum and the `0` in `elementType >= 0`, which
        // §10.2.4 makes a value of the enum: the comparison is between two of
        // them, not between an enum and a number. A `T?` on the other side
        // asks the same of its `T`, and the lifting is done afterwards.
        let other = self
            .binder
            .nullable_underlying(other)
            .unwrap_or_else(|| other.clone());
        if !matches!(
            self.binder.special_of(&other),
            Some(SpecialType::UInt32 | SpecialType::UInt64)
        ) && self.binder.enum_underlying(&other).is_none()
        {
            return value;
        }
        if self.binder.converts_implicitly(&value.ty, &other) || !self.constant_fits(&value, &other)
        {
            return value;
        }
        self.convert(value, &other)
    }

    /// Whether `ReadOnlySpan<T>` declares a `+` of its own, which a `+` of
    /// UTF-8 literals calls rather than joining them.
    fn span_declares_addition(&self) -> bool {
        self.binder
            .compilation()
            .type_by_metadata_name("System.ReadOnlySpan`1")
            .is_some_and(|span| !self.binder.lookup_member(span, "op_Addition").is_empty())
    }

    pub(super) fn bind_binary(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(operator) = binary_operator(node.kind()) else {
            return BoundExpression::error(span);
        };
        // `"1"u8 + "2"u8` is the one UTF-8 literal `"12"u8` (C# 11), and so
        // is any `+` of them, parenthesized or not. It is a built-in
        // operator, so a `+` the span type declares comes first.
        if node.kind() == SyntaxKind::AddExpression
            && let Some(text) = utf8_literal_text(node)
            && !self.span_declares_addition()
        {
            return self.utf8_span(&text, span);
        }
        let mut children = node.children();
        let left = children
            .next()
            .map(|operand| self.bind_expression(&operand));
        let right = children
            .next()
            .map(|operand| self.bind_expression(&operand));
        let (Some(left), Some(right)) = (left, right) else {
            return BoundExpression::error(span);
        };
        // `t == default` compares a tuple with the default of its type,
        // which the tuple comparison then takes apart like any other.
        let (left, right) = if operator == BinaryOperator::Coalesce {
            (left, right)
        } else {
            retype_default_beside(left, right)
        };
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) && let Some(compared) = self.bind_tuple_equality(operator, &left, &right, span)
        {
            return compared;
        }
        self.bind_binary_on(operator, left, right, span)
    }

    /// Whether `enumeration` is an enum (or a `T?` of one) and `other` a
    /// number that does not reach the enum's underlying type.
    fn enum_operand_misses(&self, enumeration: &BoundExpression, other: &BoundExpression) -> bool {
        let strip = |ty: &Type| {
            self.binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone())
        };
        let (enum_type, other_type) = (strip(&enumeration.ty), strip(&other.ty));
        let Some(underlying) = self.binder.enum_underlying(&enum_type) else {
            return false;
        };
        self.binder.enum_underlying(&other_type).is_none()
            && self
                .binder
                .special_of(&other_type)
                .is_some_and(|special| special.is_numeric())
            && !self.binder.converts_implicitly(&other_type, &underlying)
            && !self.constant_fits(other, &underlying)
            // A constant zero of any integral type is a value of every enum
            // (§10.2.4), so `(long)0 - e` is `E - E`.
            && !matches!(
                self.binder.folded(other),
                Some(
                    ConstantValue::Int32(0)
                        | ConstantValue::Int64(0)
                        | ConstantValue::UInt32(0)
                        | ConstantValue::UInt64(0)
                )
            )
    }

    /// `left <operator> right` once both operands are bound.
    /// What a `null` operand of `operator` is where the type of the other
    /// operand, `beside`, declares the operator: the parameter at the null's
    /// position, `at`, a value type made nullable for the lifted form.
    fn null_operand_type(
        &self,
        operator: BinaryOperator,
        beside: &Type,
        at: usize,
    ) -> Option<Type> {
        let name = operator_method_name(operator)?;
        let base = self
            .binder
            .nullable_underlying(beside)
            .unwrap_or_else(|| beside.clone());
        let symbol = base.symbol()?;
        if self.binder.special_of(&base).is_some() || self.binder.enum_underlying(&base).is_some() {
            return None;
        }
        let other = 1 - at;
        let mut found = None;
        for candidate in self.binder.lookup_member(symbol, name) {
            let parameters = self
                .binder
                .compilation()
                .symbols()
                .get(candidate)
                .as_method()
                .map(|detail| detail.parameters.clone())
                .unwrap_or_default();
            if parameters.len() != 2 {
                continue;
            }
            let own = self.member_type(parameters[other], &base);
            if own != base && self.binder.nullable_underlying(&own).as_ref() != Some(&base) {
                continue;
            }
            let wanted = self.member_type(parameters[at], &base);
            // Two operators that take different things there leave it to
            // overload resolution.
            if found.as_ref().is_some_and(|found: &Type| *found != wanted) {
                return None;
            }
            found = Some(wanted);
        }
        let found = found?;
        Some(if self.wraps_in_nullable(&found) {
            self.nullable_of(found)
        } else {
            found
        })
    }

    pub(super) fn bind_binary_on(
        &mut self,
        operator: BinaryOperator,
        left: BoundExpression,
        right: BoundExpression,
        span: TextSpan,
    ) -> BoundExpression {
        // `null > null` and `null + null` pick the lifted `int?` operator,
        // the best of the predefined ones both nulls reach (CS0464 warns it
        // is always false, or null).
        let (left, right) = if matches!(left.ty, Type::Null)
            && matches!(right.ty, Type::Null)
            && !matches!(
                operator,
                BinaryOperator::Equality
                    | BinaryOperator::Inequality
                    | BinaryOperator::Coalesce
                    | BinaryOperator::LogicalAnd
                    | BinaryOperator::LogicalOr
            ) {
            let int = self.special(SpecialType::Int32);
            let nullable = self.nullable_of(int);
            (
                self.convert(left, &nullable),
                self.convert(right, &nullable),
            )
        } else {
            (left, right)
        };
        // `$"a" + $"b"` is still an interpolated string to whatever it is
        // given to (C# 10): a handler is appended all the pieces of both, and
        // nothing is joined before something says it is a string.
        if operator == BinaryOperator::Add
            && left.is_interpolated_string()
            && right.is_interpolated_string()
        {
            let string = left.ty.clone();
            return BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                string,
                span,
            );
        }
        // `token != default` compares a `SyntaxToken` with the default
        // `SyntaxToken`: a bare `default` is a value of whatever it is put
        // beside (§12.18), and only then can the struct's operator take it.
        let (left, right) = if operator == BinaryOperator::Coalesce {
            // `x ?? default` on an `int?` is an `int`, which the coalesce
            // itself settles below.
            (left, right)
        } else {
            retype_default_beside(left, right)
        };
        // `(() => { }) == null` and `Main == (() => { })` compare delegates:
        // a lambda or a method group is a value of its natural type there
        // (C# 10).
        let (left, right) = if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) {
            let mut natural = |operand: BoundExpression| match operand.kind {
                BoundExpressionKind::UnboundLambda(_) | BoundExpressionKind::MethodGroup { .. } => {
                    match self.natural_function_type(&operand) {
                        Some(ty) => self.convert(operand, &ty),
                        None => operand,
                    }
                }
                _ => operand,
            };
            let left = natural(left);
            (left, natural(right))
        } else {
            (left, right)
        };
        // `handlers + (x => Log(x))` and `handlers - Remove` combine a
        // delegate with a lambda or a method group, which is a value of the
        // delegate's type there (§12.12.9): the one operand with a type
        // says what the other is. Two such operands say nothing to each
        // other, and a lambda that takes another number of parameters than
        // the delegate cannot be it.
        let (left, right) = if matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract) {
            let function = |value: &BoundExpression| {
                matches!(
                    value.kind,
                    BoundExpressionKind::UnboundLambda(_) | BoundExpressionKind::MethodGroup { .. }
                )
            };
            let delegate = |this: &Self, value: &BoundExpression| {
                !value.ty.is_error()
                    && value.ty.symbol().is_some_and(|symbol| {
                        this.binder.compilation().symbols().get(symbol).type_kind()
                            == Some(crate::TypeKind::Delegate)
                    })
            };
            // Roslyn names an operand that has no type by what it is.
            let described = |this: &Self, value: &BoundExpression| match &value.kind {
                BoundExpressionKind::MethodGroup { .. } => "method group".to_string(),
                BoundExpressionKind::UnboundLambda(at)
                    if this.syntax_at(*at).is_some_and(|node| {
                        node.kind() == SyntaxKind::AnonymousMethodExpression
                    }) =>
                {
                    "anonymous method".to_string()
                }
                BoundExpressionKind::UnboundLambda(_) => "lambda expression".to_string(),
                _ => this.display(&value.ty),
            };
            let (at_left, at_right) = (function(&left), function(&right));
            let takes_the_other =
                at_left != at_right && delegate(self, if at_left { &right } else { &left });
            let unfit = if at_left && at_right {
                true
            } else if takes_the_other {
                let (value, other) = if at_left {
                    (&left, &right)
                } else {
                    (&right, &left)
                };
                matches!(value.kind, BoundExpressionKind::UnboundLambda(_))
                    && !self.lambda_fits(value, &other.ty)
            } else {
                false
            };
            if unfit {
                let text = operator_token_text(operator).to_string();
                let (shown_left, shown_right) = (described(self, &left), described(self, &right));
                self.report(
                    ErrorCode::ErrBadBinaryOps,
                    span,
                    &[&text, &shown_left, &shown_right],
                );
                return BoundExpression::error(span);
            }
            if takes_the_other {
                let (value, other) = if at_left {
                    (left, right)
                } else {
                    (right, left)
                };
                let converted = self.convert(value, &other.ty);
                if at_left {
                    (converted, other)
                } else {
                    (other, converted)
                }
            } else {
                (left, right)
            }
        } else {
            (left, right)
        };
        if matches!(left.ty, Type::Dynamic) || matches!(right.ty, Type::Dynamic) {
            return self.bind_dynamic_binary(operator, left, right, span);
        }
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) && self.compares_a_struct_without_equality_with_null(operator, &left, &right)
        {
            let text = operator_token_text(operator).to_string();
            let (shown_left, shown_right) = (self.display(&left.ty), self.display(&right.ty));
            self.report(
                ErrorCode::ErrBadBinaryOps,
                span,
                &[&text, &shown_left, &shown_right],
            );
            return BoundExpression::error(span);
        }
        // `i == null` on an `int` is the lifted `int? == int?`, which is
        // false whatever `i` holds (CS0472 warns so): the value is still
        // worked out, for what it does, and the answer is the constant.
        if matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) && self.compares_a_value_with_null(&left, &right)
        {
            let value = if matches!(left.ty, Type::Null) {
                right
            } else {
                left
            };
            let answer = BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Boolean(
                    operator == BinaryOperator::Inequality,
                )),
                self.special(SpecialType::Boolean),
                span,
            );
            return BoundExpression::new(
                BoundExpressionKind::Sequence(vec![value, answer]),
                self.special(SpecialType::Boolean),
                span,
            );
        }
        // `e - n` on an enum over `short` with an `int` `n`: the enum's
        // operators take its underlying type (§12.10.5), and an `int` does
        // not become a `short` unless it is a constant that fits.
        if matches!(operator, BinaryOperator::Add | BinaryOperator::Subtract)
            && (self.enum_operand_misses(&left, &right) || self.enum_operand_misses(&right, &left))
        {
            let text = operator_token_text(operator).to_string();
            let (shown_left, shown_right) = (self.display(&left.ty), self.display(&right.ty));
            self.report(
                ErrorCode::ErrBadBinaryOps,
                span,
                &[&text, &shown_left, &shown_right],
            );
            return BoundExpression::error(span);
        }
        // `n ?? 0` on an `int`: a value that cannot be null has nothing to
        // coalesce (§12.15).
        if operator == BinaryOperator::Coalesce && self.wraps_in_nullable(&left.ty) {
            let (shown_left, shown_right) = (self.display(&left.ty), self.display(&right.ty));
            self.report(
                ErrorCode::ErrBadBinaryOps,
                span,
                &["??", &shown_left, &shown_right],
            );
            return BoundExpression::error(span);
        }
        // `true & null` and `n - null` lift the operator (§12.4.8): the
        // `null` is a `T?` of whatever value type is beside it, and so is
        // the answer. Equality with `null` is a test of its own.
        let (left, right) = if matches!(
            operator,
            BinaryOperator::Coalesce
                | BinaryOperator::Equality
                | BinaryOperator::Inequality
                | BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
        ) {
            (left, right)
        } else {
            // `sx * null` where `SX` declares `*(SX, SY)` is the lifted
            // operator's: the `null` is an `SY?`, not an `SX?`.
            let declared = [
                self.null_operand_type(operator, &right.ty, 0),
                self.null_operand_type(operator, &left.ty, 1),
            ];
            let lifted_null = |this: &Self, value: &BoundExpression, beside: &Type, at: usize| {
                if !matches!(value.ty, Type::Null) || beside.is_error() {
                    return None;
                }
                let lifted = if let Some(declared) = declared[at].clone() {
                    declared
                } else if this.binder.nullable_underlying(beside).is_some() {
                    beside.clone()
                } else if this.wraps_in_nullable(beside) {
                    this.nullable_of(beside.clone())
                } else {
                    return None;
                };
                Some(BoundExpression::new(
                    BoundExpressionKind::Default(lifted.clone()),
                    lifted,
                    value.span,
                ))
            };
            match (
                lifted_null(self, &left, &right.ty, 0),
                lifted_null(self, &right, &left.ty, 1),
            ) {
                (Some(left), None) => (left, right),
                (None, Some(right)) => (left, right),
                _ => (left, right),
            }
        };

        // `alignment - 1` where `alignment` is a `uint` is a `uint`, not a
        // `long`: §12.4.5 picks the operator both operands reach, and a
        // constant `int` reaches `uint` without a cast. Promoting on types
        // alone meets at `long`, and then `~(alignment - 1)` is a `long` that
        // the `uint` it is assigned to refuses.
        let (left, right) = match operator {
            // `a ?? b` has no common operand type, and the right of a shift is
            // a count that stays an `int`.
            BinaryOperator::Coalesce
            | BinaryOperator::LeftShift
            | BinaryOperator::RightShift
            | BinaryOperator::UnsignedRightShift => (left, right),
            // `kind + 0` adds the underlying type to the enum (§12.10.5),
            // and the `0` stays a number: made an enum, it would leave `E +
            // E`, which is no operator at all.
            BinaryOperator::Add | BinaryOperator::Subtract => {
                let is_zero = |body: &Self, value: &BoundExpression| {
                    body.binder.enum_underlying(&value.ty).is_none()
                        && matches!(
                            body.binder.folded(value),
                            Some(
                                ConstantValue::Int32(0)
                                    | ConstantValue::Int64(0)
                                    | ConstantValue::UInt32(0)
                                    | ConstantValue::UInt64(0)
                            )
                        )
                };
                // `e - 0` is `E - E` too, which gives the `U`: both `E - U`
                // and `E - E` take it, and Roslyn picks the second — unless
                // the zero already is a `U`, which `E - U` then takes exactly.
                let right = if let Some(underlying) = self.binder.enum_underlying(&left.ty) {
                    if operator == BinaryOperator::Subtract
                        && is_zero(self, &right)
                        && right.ty != underlying
                    {
                        self.convert(right, &left.ty)
                    } else {
                        right
                    }
                } else if self
                    .binder
                    .nullable_underlying(&left.ty)
                    .and_then(|inner| self.binder.enum_underlying(&inner))
                    .is_some_and(|underlying| {
                        right.ty == underlying
                            || (operator == BinaryOperator::Add && is_zero(self, &right))
                    })
                {
                    // `x - (short)0` on an `E?` over `short` is the lifted
                    // `E - U`, which takes the `short` exactly.
                    right
                } else {
                    self.meet_constant(right, &left.ty)
                };
                // There is no `U - E`: `0 - e` is `E - E`, the constant zero
                // being a value of every enum (§10.2.4), and gives the `U`.
                let zero = is_zero(self, &left);
                let left = if self.binder.enum_underlying(&right.ty).is_some() {
                    if operator == BinaryOperator::Subtract
                        && zero
                        && self.binder.enum_underlying(&left.ty).is_none()
                    {
                        self.convert(left, &right.ty)
                    } else {
                        left
                    }
                } else if operator == BinaryOperator::Add
                    && zero
                    && self
                        .binder
                        .nullable_underlying(&right.ty)
                        .is_some_and(|inner| self.binder.enum_underlying(&inner).is_some())
                {
                    // `0 + e` on an `E?` adds the `0` to the enum, as it
                    // does on an `E`.
                    left
                } else {
                    self.meet_constant(left, &right.ty)
                };
                (left, right)
            }
            _ => {
                let right = self.meet_constant(right, &left.ty);
                let left = self.meet_constant(left, &right.ty);
                (left, right)
            }
        };

        // `a ?? b` gives `b` something to be: an `int?` on the left makes the
        // right an `int`, and `default` there is `0` rather than a value with
        // no type at all. The same goes for a lambda, a `new(...)` and a
        // collection expression, none of which has a type until something
        // asks for one.
        // §12.15 also lets the left widen instead: `alias ?? (Symbol)type` is
        // a `Symbol`, because that is what the alias reaches and the right
        // already is.
        let mut widened = None;
        let right = if operator == BinaryOperator::Coalesce {
            let target = self
                .binder
                .nullable_underlying(&left.ty)
                .unwrap_or_else(|| left.ty.clone());
            if !typeless(&right)
                && !right.ty.is_error()
                && !matches!(right.ty, Type::Null)
                && !self.binder.converts_implicitly(&right.ty, &target)
                && !self.constant_fits(&right, &target)
                && self.binder.converts_implicitly(&target, &right.ty)
            {
                widened = Some(right.ty.clone());
                right
            } else {
                self.convert(right, &target)
            }
        } else {
            right
        };
        // `syntaxOpt ?? (SyntaxNodeOrToken)token` reaches the right's type
        // through an operator the left's type declares, and that call has
        // to be made on the left once it is known not to be null: the left
        // is held, tested, and converted or replaced.
        // An `S?` on the left whose `S` reaches the right's type is the same
        // shape (§12.15): `s ?? -1` is `s.HasValue ? (int)s.Value : -1`.
        if let Some(result) = widened.clone()
            && let Some(underlying) = self.binder.nullable_underlying(&left.ty)
        {
            let held = self.declare_synthetic_local("left", left.ty.clone());
            let left_type = left.ty.clone();
            let read = |ty: &Type| {
                BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span)
            };
            let assigned = BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read(&left_type)),
                    value: Box::new(left),
                },
                left_type.clone(),
                span,
            );
            let condition = BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::Inequality,
                    left: Box::new(assigned),
                    right: Box::new(BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Null),
                        Type::Null,
                        span,
                    )),
                },
                self.special(SpecialType::Boolean),
                span,
            );
            if let Some(value) =
                self.call_on(read(&left_type), "GetValueOrDefault", Vec::new(), span)
            {
                let value = BoundExpression::new(value.kind, underlying.clone(), span);
                let converted = match self.user_defined_conversion(&underlying, &result) {
                    Some(operator) => self.operator_call(operator, value, result.clone()),
                    None => self.convert(value, &result),
                };
                return BoundExpression::new(
                    BoundExpressionKind::Conditional {
                        condition: Box::new(condition),
                        consequence: Box::new(converted),
                        alternative: Box::new(right),
                    },
                    result,
                    span,
                );
            }
            return BoundExpression::error(span);
        }
        if let Some(result) = widened.clone()
            && self.binder.nullable_underlying(&left.ty).is_none()
            && !matches!(left.ty, Type::Null)
            && let Some(operator) = self.user_defined_conversion(&left.ty, &result)
        {
            let held = self.declare_synthetic_local("left", left.ty.clone());
            let left_type = left.ty.clone();
            let assigned = BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(BoundExpression::new(
                        BoundExpressionKind::Local(held),
                        left_type.clone(),
                        span,
                    )),
                    value: Box::new(left),
                },
                left_type.clone(),
                span,
            );
            let condition = BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::Inequality,
                    left: Box::new(assigned),
                    right: Box::new(BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Null),
                        Type::Null,
                        span,
                    )),
                },
                self.special(SpecialType::Boolean),
                span,
            );
            let read = BoundExpression::new(BoundExpressionKind::Local(held), left_type, span);
            let converted = self.operator_call(operator, read, result.clone());
            return BoundExpression::new(
                BoundExpressionKind::Conditional {
                    condition: Box::new(condition),
                    consequence: Box::new(converted),
                    alternative: Box::new(right),
                },
                result,
                span,
            );
        }
        // The same on a `T?` whose `T` declares the conversion: `point ??
        // -1` converts the point inside where there is one (§12.15).
        if let Some(result) = widened.clone()
            && let Some(inner) = self.binder.nullable_underlying(&left.ty)
            && let Some(conversion) = self.user_defined_conversion(&inner, &result)
            && let Some(symbol) = left.ty.symbol()
            && let Some(has_value) = self
                .binder
                .lookup_member(symbol, "HasValue")
                .into_iter()
                .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)
        {
            let held = self.declare_synthetic_local("left", left.ty.clone());
            let left_type = left.ty.clone();
            let read =
                BoundExpression::new(BoundExpressionKind::Local(held), left_type.clone(), span);
            let store = BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(left),
                },
                left_type,
                span,
            );
            let boolean = self.special(SpecialType::Boolean);
            let present =
                self.member_access(has_value, Some(Box::new(read.clone())), boolean, span);
            if let Some(value) = self.call_on(read, "GetValueOrDefault", Vec::new(), span) {
                let converted = self.operator_call(conversion, value, result.clone());
                let chosen = BoundExpression::new(
                    BoundExpressionKind::Conditional {
                        condition: Box::new(present),
                        consequence: Box::new(converted),
                        alternative: Box::new(right),
                    },
                    result.clone(),
                    span,
                );
                return BoundExpression::new(
                    BoundExpressionKind::Sequence(vec![store, chosen]),
                    result,
                    span,
                );
            }
            return BoundExpression::error(span);
        }

        // `"S" + test` where `Test` converts to `string` is `string +
        // string`, not `string + object` (§12.10.5): the conversion to
        // `string` is the better one, and it runs before the concatenation.
        let (left, right) = if operator == BinaryOperator::Add {
            let string = self.special(SpecialType::String);
            let convert_to_string =
                |body: &mut Self, value: BoundExpression| body.convert_operand_to_string(value);
            if left.ty == string {
                let right = convert_to_string(self, right);
                (left, right)
            } else if right.ty == string {
                let left = convert_to_string(self, left);
                (left, right)
            } else {
                (left, right)
            }
        } else {
            (left, right)
        };

        let (left, right) = self.native_constant_operands(operator, left, right);

        // A type can say what an operator means on it, and when it does that
        // wins: `p == q` on a record compares what the records hold rather
        // than which objects they are.
        if let Some(call) = self.user_defined_operator(operator, &left, &right, span) {
            return call;
        }
        if let Some(conditional) =
            self.user_defined_conditional_logic(operator, &left, &right, span)
        {
            return conditional;
        }

        // §12.4.8: every operator on a value type has a lifted form on `T?`,
        // which is what `annotations?.Length > 0` asks for.
        if let Some(lifted) = self.lift_user_defined_equality(operator, &left, &right, span) {
            return lifted;
        }
        if let Some(lifted) = self.lift_user_defined_binary(operator, &left, &right, span) {
            return lifted;
        }
        if let Some(lifted) = self.lift_binary(operator, &left, &right, span) {
            return lifted;
        }
        if let Some(lifted) = self.lift_user_defined_operands(operator, &left, &right, span) {
            return lifted;
        }
        // `==` says `bool` of any two operands, since references compare by
        // identity; a struct has no such `==` of the language's, only what
        // its conversions reach (§12.12.1): `mask == other` on Unity's
        // `LayerMask` is `(int)mask == (int)other`.
        let plain_struct = |body: &Self, ty: &Type| {
            body.binder.special_of(ty).is_none()
                && body.binder.nullable_underlying(ty).is_none()
                && ty.symbol().is_some_and(|symbol| {
                    body.binder.compilation().symbols().get(symbol).type_kind()
                        == Some(crate::TypeKind::Struct)
                })
        };
        let equality = matches!(
            operator,
            BinaryOperator::Equality | BinaryOperator::Inequality
        ) && (plain_struct(self, &left.ty) || plain_struct(self, &right.ty));
        if (equality
            || self
                .binder
                .binary_result(operator, &left.ty, &right.ty)
                .is_none())
            && let Some(through) = self.binary_through_conversions(operator, &left, &right, span)
        {
            return through;
        }

        // `p - null`: the `null` is a pointer of the other's type, and the
        // difference of two pointers is a `long`.
        let (left, right) = match (operator, &left.ty, &right.ty) {
            (BinaryOperator::Subtract, Type::Pointer(_), Type::Null) => {
                let pointer = left.ty.clone();
                (left, self.convert(right, &pointer))
            }
            (BinaryOperator::Subtract, Type::Null, Type::Pointer(_)) => {
                let pointer = right.ty.clone();
                (self.convert(left, &pointer), right)
            }
            _ => (left, right),
        };
        match self.binder.binary_result(operator, &left.ty, &right.ty) {
            Some(ty) => {
                let ty = widened.take().unwrap_or(ty);
                // Both operands are brought to the type the operator works
                // in, which for a comparison is not the type of the result:
                // `i < n` compares two `int`s and produces a `bool`.
                let operand_type = match operator {
                    // The right operand of a shift is a count, not a value of
                    // the same type.
                    BinaryOperator::LeftShift
                    | BinaryOperator::RightShift
                    | BinaryOperator::UnsignedRightShift => Some(left.ty.clone()),
                    BinaryOperator::Equality
                    | BinaryOperator::Inequality
                    | BinaryOperator::LessThan
                    | BinaryOperator::GreaterThan
                    | BinaryOperator::LessThanOrEqual
                    | BinaryOperator::GreaterThanOrEqual => Some(
                        if let Some(native) = self.binder.native_result(&left.ty, &right.ty, false)
                        {
                            native
                        } else if self.binder.converts_implicitly(&left.ty, &right.ty) {
                            right.ty.clone()
                        } else {
                            left.ty.clone()
                        },
                    ),
                    // `a ?? b` keeps its operands as they are, and so does
                    // string concatenation: `"n = " + 1` does not convert the
                    // `1` to a string, it hands it to `String.Concat` as it is.
                    BinaryOperator::Coalesce => None,
                    // `p + 1` is a pointer and an offset, which are not the
                    // same type and never become one.
                    _ if matches!(left.ty, Type::Pointer(_))
                        || matches!(right.ty, Type::Pointer(_)) =>
                    {
                        None
                    }
                    BinaryOperator::Add
                        if self.binder.compilation().special_type(SpecialType::String)
                            == ty.symbol() =>
                    {
                        None
                    }
                    _ => Some(ty.clone()),
                };
                let shifts = matches!(
                    operator,
                    BinaryOperator::LeftShift
                        | BinaryOperator::RightShift
                        | BinaryOperator::UnsignedRightShift
                );
                let (left, right) = match &operand_type {
                    // A shift's count is an `int` whatever is shifted
                    // (§12.11): `v >> 1` on a `ulong` does not widen the `1`.
                    Some(operand_type) if shifts => {
                        let int = self.special(SpecialType::Int32);
                        (self.convert(left, operand_type), self.convert(right, &int))
                    }
                    Some(operand_type) => (
                        self.convert(left, operand_type),
                        self.convert(right, operand_type),
                    ),
                    None => (left, right),
                };
                BoundExpression::new(
                    BoundExpressionKind::Binary {
                        operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    ty,
                    span,
                )
            }
            None => {
                let text = operator_token_text(operator).to_string();
                // An `nint` or an `nuint` with a number it has no operator
                // with: the operators left are the `float`, `double` and
                // `decimal` ones, and none of those is the best, which Roslyn
                // calls ambiguous. Bitwise operators and shifts have no
                // such candidates and are plain mismatches.
                let number = |ty: &Type| {
                    self.binder.native_int(ty).is_some()
                        || self
                            .binder
                            .special_of(ty)
                            .is_some_and(SpecialType::is_numeric)
                };
                let ambiguous = (self.binder.native_int(&left.ty).is_some()
                    || self.binder.native_int(&right.ty).is_some())
                    && number(&left.ty)
                    && number(&right.ty)
                    && !matches!(
                        operator,
                        BinaryOperator::BitwiseAnd
                            | BinaryOperator::BitwiseOr
                            | BinaryOperator::ExclusiveOr
                            | BinaryOperator::LeftShift
                            | BinaryOperator::RightShift
                            | BinaryOperator::UnsignedRightShift
                    );
                // `long + ulong` is the same: the `float`, `double` and
                // `decimal` operators take both, and none is the best.
                let bare = |this: &Self, operand: &BoundExpression| {
                    let ty = this
                        .binder
                        .nullable_underlying(&operand.ty)
                        .unwrap_or_else(|| operand.ty.clone());
                    BoundExpression::new(operand.kind.clone(), ty, operand.span)
                };
                let (bare_left, bare_right) = (bare(self, &left), bare(self, &right));
                let ambiguous = ambiguous
                    || (self.is_plain_number(&bare_left.ty)
                        && self.is_plain_number(&bare_right.ty)
                        && matches!(
                            self.predefined_operation(operator, &bare_left, &bare_right, span),
                            Some(super::assignment::PredefinedOperation::Ambiguous)
                        ));
                // Roslyn names them as they are written.
                let shown = |this: &Self, ty: &Type| match this.binder.native_int(ty) {
                    Some(false) => "nint".to_string(),
                    Some(true) => "nuint".to_string(),
                    None => this.display(ty),
                };
                let (left, right) = (shown(self, &left.ty), shown(self, &right.ty));
                let code = if ambiguous {
                    ErrorCode::ErrAmbigBinaryOps
                } else {
                    ErrorCode::ErrBadBinaryOps
                };
                self.report(code, span, &[&text, &left, &right]);
                BoundExpression::error(span)
            }
        }
    }

    /// `s > 1` or `a + b` where a side is a `T?` and the operator is one
    /// the underlying types declare (§12.4.8): called on what the sides
    /// hold where each has something, and otherwise `false` for a
    /// comparison and null for anything else. Equality has rules of its
    /// own, in [`lift_user_defined_equality`](Self::lift_user_defined_equality).
    /// §12.4.8: a type's operator over non-nullable value types has a
    /// lifted form over their nullables, which is a candidate too. `x + x`
    /// on a `B` with `operator +(B, int)` and a conversion from `B` to `int?`
    /// only (no `int`) is that operator lifted: the `B` wraps into a `B?`,
    /// the other converts to an `int?`, and nothing is added where either is
    /// null.
    fn lift_user_defined_operands(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if matches!(
            operator,
            BinaryOperator::Equality
                | BinaryOperator::Inequality
                | BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::Coalesce
        ) || left.ty.is_error()
            || right.ty.is_error()
            || matches!(left.ty, Type::Null)
            || matches!(right.ty, Type::Null)
        {
            return None;
        }
        let name = operator_method_name(operator)?;
        for operand in [&left.ty, &right.ty] {
            let owner = self
                .binder
                .nullable_underlying(operand)
                .unwrap_or_else(|| operand.clone());
            let Some(symbol) = owner.symbol() else {
                continue;
            };
            if self.binder.special_of(&owner).is_some()
                || self.binder.enum_underlying(&owner).is_some()
            {
                continue;
            }
            for candidate in self.binder.lookup_member(symbol, name) {
                if self.kind_of(candidate) != SymbolKind::Method {
                    continue;
                }
                let parameters: Vec<SymbolId> = self
                    .binder
                    .compilation()
                    .symbols()
                    .get(candidate)
                    .as_method()
                    .map(|detail| detail.parameters.clone())
                    .unwrap_or_default();
                let [first, second] = parameters[..] else {
                    continue;
                };
                let (first, second) = (
                    self.member_type(first, &owner),
                    self.member_type(second, &owner),
                );
                let result = self.member_type(candidate, &owner);
                if !self.wraps_in_nullable(&first)
                    || !self.wraps_in_nullable(&second)
                    || !self.wraps_in_nullable(&result)
                {
                    continue;
                }
                // The normal form is the user-defined operator's own business.
                if self.binder.converts_implicitly(&left.ty, &first)
                    && self.binder.converts_implicitly(&right.ty, &second)
                {
                    return None;
                }
                let (first, second) = (self.nullable_of(first), self.nullable_of(second));
                if self.binder.converts_implicitly(&left.ty, &first)
                    && self.binder.converts_implicitly(&right.ty, &second)
                {
                    let left = self.convert(left.clone(), &first);
                    let right = self.convert(right.clone(), &second);
                    return self.lift_user_defined_binary(operator, &left, &right, span);
                }
            }
        }
        None
    }

    fn lift_user_defined_binary(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if matches!(
            operator,
            BinaryOperator::Equality
                | BinaryOperator::Inequality
                | BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::Coalesce
        ) || matches!(left.ty, Type::Null)
            || matches!(right.ty, Type::Null)
        {
            return None;
        }
        let left_base = self.binder.nullable_underlying(&left.ty);
        let right_base = self.binder.nullable_underlying(&right.ty);
        if left_base.is_none() && right_base.is_none() {
            return None;
        }
        // Only where the operator is a type's own: the built-in ones lift
        // in `lift_binary`.
        let declares = |ty: &Type| {
            ty.symbol().is_some()
                && self.binder.special_of(ty).is_none()
                && self.binder.enum_underlying(ty).is_none()
        };
        let underlying = [
            left_base.clone().unwrap_or_else(|| left.ty.clone()),
            right_base.clone().unwrap_or_else(|| right.ty.clone()),
        ];
        if !underlying.iter().any(declares) {
            return None;
        }
        let boolean = self.special(SpecialType::Boolean);
        let mut steps = Vec::new();
        let mut values = Vec::new();
        let mut present: Option<BoundExpression> = None;
        for (side, base) in [(left, &left_base), (right, &right_base)] {
            let local = self.declare_synthetic_local("side", side.ty.clone());
            let read =
                BoundExpression::new(BoundExpressionKind::Local(local), side.ty.clone(), span);
            steps.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(side.clone()),
                },
                side.ty.clone(),
                span,
            ));
            if base.is_some() {
                let symbol = side.ty.symbol()?;
                let has_value = self
                    .binder
                    .lookup_member(symbol, "HasValue")
                    .into_iter()
                    .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)?;
                let has = self.member_access(
                    has_value,
                    Some(Box::new(read.clone())),
                    boolean.clone(),
                    span,
                );
                present = Some(match present {
                    None => has,
                    Some(before) => BoundExpression::new(
                        BoundExpressionKind::Binary {
                            operator: BinaryOperator::LogicalAnd,
                            left: Box::new(before),
                            right: Box::new(has),
                        },
                        boolean.clone(),
                        span,
                    ),
                });
                values.push(self.call_on(read, "GetValueOrDefault", Vec::new(), span)?);
            } else {
                values.push(read);
            }
        }
        let [left_value, right_value]: [BoundExpression; 2] = values.try_into().ok()?;
        let call = self.user_defined_operator(operator, &left_value, &right_value, span)?;
        let comparison = matches!(
            operator,
            BinaryOperator::LessThan
                | BinaryOperator::GreaterThan
                | BinaryOperator::LessThanOrEqual
                | BinaryOperator::GreaterThanOrEqual
        );
        let (result, otherwise) = if comparison && self.binder.is_boolean(&call.ty) {
            let no = BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Boolean(false)),
                boolean.clone(),
                span,
            );
            (call.ty.clone(), no)
        } else {
            let result = if self.wraps_in_nullable(&call.ty) {
                self.nullable_of(call.ty.clone())
            } else {
                call.ty.clone()
            };
            let none = BoundExpression::new(
                BoundExpressionKind::Default(result.clone()),
                result.clone(),
                span,
            );
            (result, none)
        };
        let call = self.convert(call, &result);
        let chosen = BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(present?),
                consequence: Box::new(call),
                alternative: Box::new(otherwise),
            },
            result.clone(),
            span,
        );
        steps.push(chosen);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            result,
            span,
        ))
    }

    /// `x == y` where either is a `T?` and `T` has an `==` of its own
    /// (§12.4.8): equal where both are empty, unequal where one is, and the
    /// struct's own answer where neither is. Written out with the two sides
    /// held in locals, since each is read more than once.
    fn lift_user_defined_equality(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        // `Some(true)` for `==`, `Some(false)` for `!=`, and `None` for an
        // ordering, which is false whenever either side is missing.
        let equality = match operator {
            BinaryOperator::Equality => Some(true),
            BinaryOperator::Inequality => Some(false),
            BinaryOperator::LessThan
            | BinaryOperator::GreaterThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThanOrEqual => None,
            _ => return None,
        };
        if matches!(left.ty, Type::Null) || matches!(right.ty, Type::Null) {
            return None;
        }
        let left_base = self.binder.nullable_underlying(&left.ty);
        let right_base = self.binder.nullable_underlying(&right.ty);
        if left_base.is_none() && right_base.is_none() {
            return None;
        }
        let inner = left_base.unwrap_or_else(|| left.ty.clone());
        if right_base.unwrap_or_else(|| right.ty.clone()) != inner {
            return None;
        }
        let symbol = inner.symbol()?;
        // `decimal` is special but its operators are methods like anyone's:
        // `x != 0.0m` on a `decimal?` is `op_Inequality` lifted, not a
        // comparison of the bits.
        if self
            .binder
            .special_of(&inner)
            .is_some_and(|special| special != SpecialType::Decimal)
        {
            return None;
        }
        let name = operator_method_name(operator)?;
        let method = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .find(|candidate| {
                let symbols = self.binder.compilation().symbols();
                symbols.get(*candidate).as_method().is_some_and(|detail| {
                    detail.parameters.len() == 2
                        && detail
                            .parameters
                            .iter()
                            .all(|parameter| self.member_type(*parameter, &inner) == inner)
                })
            })?;
        let boolean = self.special(SpecialType::Boolean);
        let lifted = self.nullable_of(inner.clone());
        let nullable = lifted.symbol()?;
        let has_value = self
            .binder
            .lookup_member(nullable, "HasValue")
            .into_iter()
            .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)?;

        let mut steps = Vec::new();
        let mut held = Vec::new();
        for (side, stem) in [(left, "left"), (right, "right")] {
            let value = self.convert(side.clone(), &lifted);
            let local = self.declare_synthetic_local(stem, lifted.clone());
            let read =
                BoundExpression::new(BoundExpressionKind::Local(local), lifted.clone(), span);
            steps.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(value),
                },
                lifted.clone(),
                span,
            ));
            held.push(read);
        }
        let present = |read: &BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::Property {
                    receiver: Some(Box::new(read.clone())),
                    property: has_value,
                },
                boolean.clone(),
                span,
            )
        };
        let literal = |value: bool| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Boolean(value)),
                boolean.clone(),
                span,
            )
        };
        let mut values = Vec::new();
        for read in &held {
            values.push(self.call_on(read.clone(), "GetValueOrDefault", Vec::new(), span)?);
        }
        let compared = BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments: Vec::new(),
                arguments: values,
                virtual_call: false,
            },
            boolean.clone(),
            span,
        );
        let Some(equality) = equality else {
            // An ordering: both present, ask the struct; otherwise false
            // (§12.4.8).
            let both_present = BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::LogicalAnd,
                    left: Box::new(present(&held[0])),
                    right: Box::new(present(&held[1])),
                },
                boolean.clone(),
                span,
            );
            steps.push(BoundExpression::new(
                BoundExpressionKind::Conditional {
                    condition: Box::new(both_present),
                    consequence: Box::new(compared),
                    alternative: Box::new(literal(false)),
                },
                boolean.clone(),
                span,
            ));
            return Some(BoundExpression::new(
                BoundExpressionKind::Sequence(steps),
                boolean,
                span,
            ));
        };
        // Both present: ask the struct. Both missing: equal. One missing:
        // unequal.
        let when_present = BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(present(&held[0])),
                consequence: Box::new(compared),
                alternative: Box::new(literal(equality)),
            },
            boolean.clone(),
            span,
        );
        let same_presence = BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Equality,
                left: Box::new(present(&held[0])),
                right: Box::new(present(&held[1])),
            },
            boolean.clone(),
            span,
        );
        steps.push(BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(same_presence),
                consequence: Box::new(when_present),
                alternative: Box::new(literal(!equality)),
            },
            boolean.clone(),
            span,
        ));
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            boolean,
            span,
        ))
    }

    /// `&` and `|` on `bool?` (§12.13.5): three-valued, so a `false` on
    /// either side of `&` is `false` whatever the other is, and a `true` on
    /// either side of `|` is `true`. Written out over the two sides held in
    /// locals — for `&`, `l ? r : l.HasValue ? l : r ? l : r`, reading each
    /// side's value or default; `|` is the mirror.
    fn lift_boolean_logic(
        &mut self,
        and: bool,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let boolean = self.special(SpecialType::Boolean);
        let lifted = self.nullable_of(boolean.clone());
        let nullable = lifted.symbol()?;
        let has_value = self
            .binder
            .lookup_member(nullable, "HasValue")
            .into_iter()
            .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)?;
        let mut steps = Vec::new();
        let mut held = Vec::new();
        for (side, stem) in [(left, "left"), (right, "right")] {
            let value = self.convert(side.clone(), &lifted);
            let local = self.declare_synthetic_local(stem, lifted.clone());
            let read =
                BoundExpression::new(BoundExpressionKind::Local(local), lifted.clone(), span);
            steps.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(value),
                },
                lifted.clone(),
                span,
            ));
            held.push(read);
        }
        let (l, r) = (held[0].clone(), held[1].clone());
        let l_value = self.call_on(l.clone(), "GetValueOrDefault", Vec::new(), span)?;
        let r_value = self.call_on(r.clone(), "GetValueOrDefault", Vec::new(), span)?;
        let l_has = self.member_access(has_value, Some(Box::new(l.clone())), boolean, span);
        let choose = |condition: BoundExpression, yes: BoundExpression, no: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::Conditional {
                    condition: Box::new(condition),
                    consequence: Box::new(yes),
                    alternative: Box::new(no),
                },
                lifted.clone(),
                span,
            )
        };
        let result = if and {
            let unknown = choose(r_value, l.clone(), r.clone());
            let otherwise = choose(l_has, l.clone(), unknown);
            choose(l_value, r, otherwise)
        } else {
            let unknown = choose(r_value, r.clone(), l.clone());
            let otherwise = choose(l_has, r, unknown);
            choose(l_value, l, otherwise)
        };
        steps.push(result);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            lifted,
            span,
        ))
    }

    /// `u > 0` and `u + 1L` on an `nuint`: a non-negative `int` constant is
    /// an `nuint` (§10.2.11) and a non-negative `long` one is a `ulong`,
    /// where the operator would otherwise have nothing to take. No other
    /// `int` is an `nuint`.
    fn native_constant_operands(
        &mut self,
        operator: BinaryOperator,
        left: BoundExpression,
        right: BoundExpression,
    ) -> (BoundExpression, BoundExpression) {
        if matches!(
            operator,
            BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::UnsignedRightShift
                | BinaryOperator::LogicalAnd
                | BinaryOperator::LogicalOr
                | BinaryOperator::Coalesce
        ) {
            return (left, right);
        }
        let unsigned_native = |this: &Self, ty: &Type| {
            let ty = this
                .binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone());
            this.binder.native_int(&ty) == Some(true)
        };
        let ulong = self.special(SpecialType::UInt64);
        let adjust = |this: &mut Self, constant: BoundExpression, native: &Type| {
            let native = this
                .binder
                .nullable_underlying(native)
                .unwrap_or_else(|| native.clone());
            if this.binder.nullable_underlying(&constant.ty).is_some()
                || this.binder.native_int(&constant.ty).is_some()
                || !this.binder.special_of(&constant.ty).is_some_and(|special| {
                    matches!(special, SpecialType::Int32 | SpecialType::Int64)
                })
            {
                return constant;
            }
            if this.constant_fits(&constant, &native) {
                return this.convert(constant, &native);
            }
            if this.binder.special_of(&constant.ty) == Some(SpecialType::Int64)
                && this.constant_fits(&constant, &ulong)
            {
                return this.convert(constant, &ulong);
            }
            constant
        };
        if unsigned_native(self, &left.ty) && !unsigned_native(self, &right.ty) {
            let right = adjust(self, right, &left.ty);
            (left, right)
        } else if unsigned_native(self, &right.ty) && !unsigned_native(self, &left.ty) {
            let left = adjust(self, left, &right.ty);
            (left, right)
        } else {
            (left, right)
        }
    }

    fn lift_binary(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if matches!(
            operator,
            BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr | BinaryOperator::Coalesce
        ) {
            return None;
        }
        // A null literal is compared by asking whether the other side has a
        // value at all, which needs no lifting. Any other operator takes it
        // as the `T?` of the other side (`true & null` is a `bool?`).
        let null_left = matches!(left.ty, Type::Null);
        let null_right = matches!(right.ty, Type::Null);
        if null_left && null_right {
            return None;
        }
        if (null_left || null_right)
            && matches!(
                operator,
                BinaryOperator::Equality | BinaryOperator::Inequality
            )
        {
            return None;
        }
        let symbols = self.binder.compilation().symbols();
        let value_typed = |ty: &Type| {
            !ty.is_error()
                && !matches!(ty, Type::Null | Type::TypeParameter(_))
                && !ty.is_reference_type(symbols)
        };
        if (null_left && !value_typed(&right.ty)) || (null_right && !value_typed(&left.ty)) {
            return None;
        }
        let left_base = self.binder.nullable_underlying(&left.ty);
        let right_base = self.binder.nullable_underlying(&right.ty);
        if left_base.is_none() && right_base.is_none() && !null_left && !null_right {
            return None;
        }
        let left_base = left_base.unwrap_or_else(|| left.ty.clone());
        let right_base = right_base.unwrap_or_else(|| right.ty.clone());
        if matches!(
            operator,
            BinaryOperator::BitwiseAnd | BinaryOperator::BitwiseOr
        ) && self.binder.is_boolean(&left_base)
            && self.binder.is_boolean(&right_base)
        {
            return self.lift_boolean_logic(
                operator == BinaryOperator::BitwiseAnd,
                left,
                right,
                span,
            );
        }
        let (left_base, right_base) = if null_left {
            (right_base.clone(), right_base)
        } else if null_right {
            (left_base.clone(), left_base)
        } else {
            (left_base, right_base)
        };
        let result = self
            .binder
            .binary_result(operator, &left_base, &right_base)?;
        // `flag? + " "` is string concatenation, which takes the `bool?` as
        // an object and has nothing to lift: only a value-typed answer does.
        if result.is_reference_type(self.binder.compilation().symbols()) {
            return None;
        }
        let shift = matches!(
            operator,
            BinaryOperator::LeftShift
                | BinaryOperator::RightShift
                | BinaryOperator::UnsignedRightShift
        );
        let comparison = matches!(
            operator,
            BinaryOperator::Equality
                | BinaryOperator::Inequality
                | BinaryOperator::LessThan
                | BinaryOperator::GreaterThan
                | BinaryOperator::LessThanOrEqual
                | BinaryOperator::GreaterThanOrEqual
        );
        // Both sides work in one type, which for a comparison is not the
        // type of the answer: `(byte?)b > 0` compares two `int`s and gives a
        // `bool`. The right of a shift is a count and stays what it is.
        let operand = if shift {
            left_base.clone()
        } else if comparison {
            if let Some(native) = self.binder.native_result(&left_base, &right_base, false) {
                native
            } else if self.binder.converts_implicitly(&left_base, &right_base) {
                right_base.clone()
            } else {
                left_base.clone()
            }
        } else {
            result.clone()
        };
        let lifted = self.nullable_of(operand);
        let converted_left = self.convert(left.clone(), &lifted);
        let count = self.nullable_of(right_base);
        let converted_right = self.convert(right.clone(), if shift { &count } else { &lifted });
        if converted_left.ty.is_error() || converted_right.ty.is_error() {
            return None;
        }
        let ty = if comparison {
            let boolean = self
                .binder
                .compilation()
                .special_type(SpecialType::Boolean)?;
            Type::named(boolean)
        } else {
            self.nullable_of(result)
        };
        Some(BoundExpression::new(
            BoundExpressionKind::Binary {
                operator,
                left: Box::new(converted_left),
                right: Box::new(converted_right),
            },
            ty,
            span,
        ))
    }
}

/// The text of a UTF-8 string literal, or of a `+` of them: what `"1"u8 +
/// ("2"u8 + "3"u8)` is one literal of.
fn utf8_literal_text(node: &SyntaxNode) -> Option<String> {
    match node.kind() {
        SyntaxKind::Utf8StringLiteralExpression => match node.child_tokens().next()?.value() {
            rustlyn_syntax::TokenValue::String(text) => Some(text.to_string()),
            _ => None,
        },
        // `checked(...)` and `unchecked(...)` change nothing a literal is.
        SyntaxKind::ParenthesizedExpression
        | SyntaxKind::CheckedExpression
        | SyntaxKind::UncheckedExpression => {
            utf8_literal_text(&node.children().find(|child| child.kind().is_expression())?)
        }
        SyntaxKind::AddExpression => {
            let mut operands = node.children().filter(|child| child.kind().is_expression());
            let (left, right) = (operands.next()?, operands.next()?);
            // The right first: in `a + b + c` it is the leaf, and a chain of
            // anything but UTF-8 literals is turned down without walking the
            // whole of it again at every `+`.
            let right = utf8_literal_text(&right)?;
            Some(utf8_literal_text(&left)? + &right)
        }
        _ => None,
    }
}

/// The name metadata gives an operator, which is how a type declares one and
/// how a call finds it.
pub(super) const fn operator_method_name(operator: BinaryOperator) -> Option<&'static str> {
    Some(match operator {
        BinaryOperator::Add => "op_Addition",
        BinaryOperator::Subtract => "op_Subtraction",
        BinaryOperator::Multiply => "op_Multiply",
        BinaryOperator::Divide => "op_Division",
        BinaryOperator::Modulo => "op_Modulus",
        BinaryOperator::BitwiseAnd => "op_BitwiseAnd",
        BinaryOperator::BitwiseOr => "op_BitwiseOr",
        BinaryOperator::ExclusiveOr => "op_ExclusiveOr",
        BinaryOperator::LeftShift => "op_LeftShift",
        BinaryOperator::RightShift => "op_RightShift",
        BinaryOperator::UnsignedRightShift => "op_UnsignedRightShift",
        BinaryOperator::Equality => "op_Equality",
        BinaryOperator::Inequality => "op_Inequality",
        BinaryOperator::LessThan => "op_LessThan",
        BinaryOperator::GreaterThan => "op_GreaterThan",
        BinaryOperator::LessThanOrEqual => "op_LessThanOrEqual",
        BinaryOperator::GreaterThanOrEqual => "op_GreaterThanOrEqual",
        // `&&`, `||` and `??` choose whether to evaluate their right operand,
        // which is not something a call can do.
        BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr | BinaryOperator::Coalesce => {
            return None;
        }
    })
}

/// How an operator is spelled, for a diagnostic about it.
pub(super) fn operator_token_text(operator: BinaryOperator) -> &'static str {
    match operator {
        BinaryOperator::Add => "+",
        BinaryOperator::Subtract => "-",
        BinaryOperator::Multiply => "*",
        BinaryOperator::Divide => "/",
        BinaryOperator::Modulo => "%",
        BinaryOperator::LeftShift => "<<",
        BinaryOperator::RightShift => ">>",
        BinaryOperator::UnsignedRightShift => ">>>",
        BinaryOperator::BitwiseAnd => "&",
        BinaryOperator::BitwiseOr => "|",
        BinaryOperator::ExclusiveOr => "^",
        BinaryOperator::LogicalAnd => "&&",
        BinaryOperator::LogicalOr => "||",
        BinaryOperator::Equality => "==",
        BinaryOperator::Inequality => "!=",
        BinaryOperator::LessThan => "<",
        BinaryOperator::GreaterThan => ">",
        BinaryOperator::LessThanOrEqual => "<=",
        BinaryOperator::GreaterThanOrEqual => ">=",
        BinaryOperator::Coalesce => "??",
    }
}
