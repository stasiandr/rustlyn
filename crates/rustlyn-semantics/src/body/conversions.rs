//! Conversions (§10): implicit and explicit, user-defined and lifted, of
//! tuples and of constants.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::SyntaxKind;

use super::{BodyBinder, Resolved};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundSwitchArm, ConstantValue, ConversionKind,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, RefKind, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// The `implicit operator` of the target that a constant reaches by an
    /// implicit constant conversion (§10.2.11) of its parameter's type, with
    /// that type: `1` is an `int`, and an `implicit operator C(byte)` still
    /// takes it.
    pub(super) fn constant_operator(
        &self,
        value: &BoundExpression,
        to: &Type,
    ) -> Option<(SymbolId, Type)> {
        self.binder.folded(value)?;
        let inner = self.binder.nullable_underlying(to);
        let target = inner.as_ref().unwrap_or(to);
        let symbol = target.symbol()?;
        if self.binder.special_of(target).is_some() {
            return None;
        }
        let symbols = self.binder.compilation().symbols();
        self.binder
            .lookup_member(symbol, "op_Implicit")
            .into_iter()
            .find_map(|operator| {
                let detail = symbols.get(operator).as_method()?;
                let [parameter] = detail.parameters[..] else {
                    return None;
                };
                let takes = self.member_type(parameter, target);
                let gives = self.member_type(operator, target);
                (gives == *target
                    && takes != value.ty
                    && self.binder.special_of(&takes).is_some()
                    && self.constant_fits(value, &takes))
                .then_some((operator, takes))
            })
    }

    /// `C x = (1, "qq")` with an `implicit operator C((byte, string))`: the
    /// literal reaches the operator's tuple element by element, a constant
    /// as the constant it is, and the operator the rest of the way — the
    /// conversion into what an operator takes is asked of the expression
    /// (§10.5.4), not of the `(int, string)` it would be on its own.
    pub(super) fn tuple_literal_operator(
        &self,
        value: &BoundExpression,
        to: &Type,
    ) -> Option<(SymbolId, Type)> {
        let elements = self.tuple_literal_elements(value)?;
        self.tuple_literal_operator_of(&elements, to)
    }

    /// The same, for a literal overload resolution has taken apart.
    pub(super) fn tuple_literal_operator_of(
        &self,
        elements: &[super::TupleLiteralElement],
        to: &Type,
    ) -> Option<(SymbolId, Type)> {
        // `Nullable<T>`'s own operators are no user-defined conversion
        // (§10.5.4 looks in the type underneath); a tuple into a `T?` is
        // made as the `T` and wrapped.
        if self.binder.special_of(to).is_some() || self.binder.nullable_underlying(to).is_some() {
            return None;
        }
        let symbol = to.symbol()?;
        let symbols = self.binder.compilation().symbols();
        self.binder
            .lookup_member(symbol, "op_Implicit")
            .into_iter()
            .find_map(|operator| {
                let detail = symbols.get(operator).as_method()?;
                let [parameter] = detail.parameters[..] else {
                    return None;
                };
                let takes = self.member_type(parameter, to);
                let gives = self.member_type(operator, to);
                (gives == *to && self.tuple_literal_reaches(elements, &takes))
                    .then_some((operator, takes))
            })
    }

    /// Whether a cast would take `from` to `to` where nothing implicit does,
    /// which turns CS0029 into CS0266 and its "are you missing a cast?".
    ///
    /// Only the plain cases: between numbers and enums, out of a nullable,
    /// down a hierarchy (the reverse of an implicit reference or boxing
    /// conversion), and through an `explicit operator`.
    pub(super) fn converts_explicitly(&self, from: &Type, to: &Type) -> bool {
        let numeric_or_enum = |ty: &Type| {
            self.binder
                .special_of(ty)
                .is_some_and(crate::corlib::SpecialType::is_numeric)
                || self.binder.enum_underlying(ty).is_some()
        };
        let from_value = self
            .binder
            .nullable_underlying(from)
            .unwrap_or_else(|| from.clone());
        let to_value = self
            .binder
            .nullable_underlying(to)
            .unwrap_or_else(|| to.clone());
        (numeric_or_enum(&from_value) && numeric_or_enum(&to_value))
            || (self.binder.nullable_underlying(from).is_some()
                && self.binder.converts_implicitly(&from_value, to))
            || (!matches!(from, Type::Null) && self.binder.converts_implicitly(to, from))
            || self.binder.explicit_operator(from, to).is_some()
    }

    /// Whether a constant reaches a narrower type without a cast.
    ///
    /// `byte b = 1;` is legal and `byte b = i;` is not, for the same `1`: §10.2
    /// lets a *constant* whose value fits cross a narrowing conversion, because
    /// the compiler can see that nothing is lost. It is the rule that makes
    /// every small integer literal usable without a suffix or a cast.
    pub(super) fn constant_fits(&self, value: &BoundExpression, to: &Type) -> bool {
        // `(byte, byte) a = (1, 2)`: a tuple literal reaches a tuple type
        // element by element (§10.2.13), and each constant in it is asked
        // the same question about the element it is for.
        if let BoundExpressionKind::TupleCreation(values) = &value.kind {
            let inner = self
                .binder
                .nullable_underlying(to)
                .unwrap_or_else(|| to.clone());
            if let Some(elements) = self.tuple_element_types(&inner)
                && elements.len() == values.len()
            {
                return values.iter().zip(&elements).all(|(element, wanted)| {
                    element.ty.is_error()
                        || self.binder.converts_implicitly(&element.ty, wanted)
                        || self.constant_fits(element, wanted)
                        || (element.is_interpolated_string() && self.is_handler_type(wanted))
                });
            }
        }
        let Some(constant) = self.binder.folded(value) else {
            return false;
        };
        self.constant_reaches(&constant, &value.ty, to)
    }

    /// The same rule asked about a value that has already been folded.
    ///
    /// Overload resolution needs it as well as assignment does: `WriteByte(1)`
    /// has no candidate taking an `int`, and whether the call is applicable at
    /// all turns on the literal's value rather than on its type.
    ///
    /// Which is also why the type the constant is written as matters and not
    /// only its value. §10.2.11 gives the rule to a constant *of type `int`*
    /// (and `long` reaching `ulong`), nothing else: `Colour.Green` is a
    /// constant whose value is 4 and it does not convert to `int`, so
    /// `WriteLine(Colour.Green)` still goes to the overload taking an
    /// `object` and still prints a name.
    pub(super) fn constant_reaches(
        &self,
        constant: &ConstantValue,
        from: &Type,
        to: &Type,
    ) -> bool {
        // `byte? small = 3;` is the same question about the `byte` inside:
        // §10.2.4 is lifted like every other conversion.
        if let Some(inner) = self.binder.nullable_underlying(to) {
            return self.constant_reaches(constant, from, &inner);
        }
        // A constant zero is a value of every enum, whether or not the enum
        // names it: `ParseQueryExpression(0)` says the first precedence, and
        // `Level none = 0;` is how a flags enum is emptied (§10.2.4).
        // Roslyn takes any numeric zero, `0.0` included, as native C# did.
        let zero = match constant {
            ConstantValue::Int32(value) => *value == 0,
            ConstantValue::Int64(value) => *value == 0,
            ConstantValue::UInt32(value) => *value == 0,
            ConstantValue::UInt64(value) => *value == 0,
            ConstantValue::Single(value) => *value == 0.0,
            ConstantValue::Double(value) => *value == 0.0,
            _ => false,
        };
        if zero
            && self
                .binder
                .special_of(from)
                .is_some_and(SpecialType::is_numeric)
            && to.symbol().is_some_and(|symbol| {
                self.binder.compilation().symbols().get(symbol).type_kind() == Some(TypeKind::Enum)
            })
        {
            return true;
        }
        // A non-negative `int` constant reaches an `nuint` (§10.2.11, C# 9):
        // `Add(3, 4)` passes two of them.
        let unsigned_native = to.symbol().is_some_and(|symbol| {
            self.binder
                .compilation()
                .type_by_metadata_name("System.UIntPtr")
                == Some(symbol)
        });
        if unsigned_native {
            return match (constant, self.binder.special_of(from)) {
                (ConstantValue::Int32(value), Some(SpecialType::Int32)) => *value >= 0,
                _ => false,
            };
        }
        let (Some(written), Some(wanted)) =
            (self.binder.special_of(from), self.binder.special_of(to))
        else {
            return false;
        };
        // A `long` constant reaches `ulong` alone: `M(0L)` is not `M(uint)`.
        if written == SpecialType::Int64 && wanted != SpecialType::UInt64 {
            return false;
        }
        let wide = match (constant, written) {
            // `const long Bits = 8;` keeps the `8` it was written with, and
            // is a `long` constant all the same.
            (ConstantValue::Int32(value), SpecialType::Int32 | SpecialType::Int64) => {
                i128::from(*value)
            }
            (ConstantValue::Int64(value), SpecialType::Int64) => i128::from(*value),
            _ => return false,
        };
        let (low, high) = match wanted {
            SpecialType::SByte => (i128::from(i8::MIN), i128::from(i8::MAX)),
            SpecialType::Byte => (0, i128::from(u8::MAX)),
            SpecialType::Int16 => (i128::from(i16::MIN), i128::from(i16::MAX)),
            SpecialType::UInt16 => (0, i128::from(u16::MAX)),
            SpecialType::UInt32 => (0, i128::from(u32::MAX)),
            SpecialType::UInt64 => (0, i128::from(u64::MAX)),
            _ => return false,
        };
        (low..=high).contains(&wide)
    }

    /// Wraps `value` in the conversion that reaching `target` needs.
    ///
    /// A backend cannot work this out from the two types alone: `int` to
    /// `object` boxes, `int` to `long` widens, and `string` to `object` does
    /// nothing at all, and only the binder knows which rule applied.
    pub(super) fn convert(&mut self, value: BoundExpression, target: &Type) -> BoundExpression {
        // Arguments a call stores ahead of itself are stored by the first one
        // it evaluates (`in_written_order`), and a method group or a `new()`
        // that is that one is still converted as itself, after the stores.
        if let BoundExpressionKind::Sequence(items) = &value.kind
            && items.last().is_some_and(|last| {
                matches!(
                    last.kind,
                    BoundExpressionKind::MethodGroup { .. }
                        | BoundExpressionKind::UnboundLambda(_)
                        | BoundExpressionKind::UnboundCreation(_)
                        | BoundExpressionKind::UnboundCollection(_)
                        | BoundExpressionKind::UnboundConditional(_)
                        | BoundExpressionKind::UnboundSwitch(_)
                )
            })
        {
            let span = value.span;
            let BoundExpressionKind::Sequence(mut items) = value.kind else {
                unreachable!("matched above");
            };
            let last = items.pop().expect("matched above");
            let converted = self.convert(last, target);
            let ty = converted.ty.clone();
            items.push(converted);
            return BoundExpression::new(BoundExpressionKind::Sequence(items), ty, span);
        }
        // `dynamic` into anything but `object` is the runtime binder's to do.
        if matches!(value.ty, Type::Dynamic)
            && !matches!(target, Type::Dynamic | Type::Error | Type::Void)
            && self.binder.object_type().as_ref() != Some(target)
        {
            return Self::dynamic_conversion(value, target, false);
        }
        // `object` and `dynamic` are one type to the runtime, and so are
        // `List<object>` and `List<dynamic>`: nothing converts, and a `ref`
        // to one is a `ref` to the other.
        // So are `ref (int, object)` and `ref (int, dynamic)`, however the
        // tuple is spelled.
        if value.ty != *target
            && !value.ty.is_error()
            && !target.is_error()
            && (self.binder.same_but_for_dynamic(&value.ty, target)
                || ((crate::conversions::contains_dynamic(&value.ty)
                    || crate::conversions::contains_dynamic(target))
                    && self.binder.identity_converts(&value.ty, target)))
        {
            if matches!(value.ty, Type::Dynamic) {
                self.dynamic_relabelled.insert(value.span);
            }
            return BoundExpression::new(value.kind, target.clone(), value.span);
        }
        // `null` into a struct union is a union conversion through the case
        // type null reaches (C# 15): there is no null of the struct itself.
        if matches!(value.ty, Type::Null)
            && self.binder.nullable_underlying(target).is_none()
            && !target.is_reference_type(self.binder.compilation().symbols())
            && self.binder.is_union_type(target)
            && let Some(made) = self.union_conversion(value.clone(), target)
        {
            return made;
        }
        // A bare `default` is whatever it is being given to. That is the whole
        // of what it means, and until something says, it has no type at all.
        if matches!(value.kind, BoundExpressionKind::Default(_))
            && value.ty.is_error()
            && !target.is_error()
        {
            self.body.types.insert(value.span, target.clone());
            return BoundExpression::new(
                BoundExpressionKind::Default(target.clone()),
                target.clone(),
                value.span,
            );
        }
        // `null` given to a struct with an operator from a reference type
        // is that operator called with `null`: what it makes of nothing is
        // its own business. A span's makes the empty span, which `default`
        // below is just as well.
        if matches!(value.ty, Type::Null)
            && self.binder.nullable_underlying(target).is_none()
            && !target.is_reference_type(self.binder.compilation().symbols())
            && !self.is_span_type(target)
            && let Some(operator) = self.binder.null_operator(target)
        {
            return self.operator_call(operator, value, target.clone());
        }
        // `null` given to a value type is that type's default — the empty
        // `Nullable<T>`, nearly always. There is no reference to load: a
        // struct is not one, and `ldnull` where a struct is wanted is not a
        // program at all.
        if matches!(value.ty, Type::Null)
            && !matches!(target, Type::Null | Type::Error | Type::Array { .. })
            && !target.is_reference_type(self.binder.compilation().symbols())
        {
            self.body.types.insert(value.span, target.clone());
            // A `null` compared with a `T` stays a `null` that was written:
            // `default(T) == null` is a question about a value of `T`, and a
            // `default(T)` standing for the `null` could not be told from the
            // one the program wrote.
            if matches!(target, Type::TypeParameter(_)) {
                let span = value.span;
                return BoundExpression::new(
                    BoundExpressionKind::Conversion {
                        operand: Box::new(value),
                        conversion: ConversionKind::Identity,
                        written: false,
                    },
                    target.clone(),
                    span,
                );
            }
            return BoundExpression::new(
                BoundExpressionKind::Default(target.clone()),
                target.clone(),
                value.span,
            );
        }
        // A lambda or a method group given to a type with an `op_Implicit`
        // from a delegate becomes that delegate, and then goes through it.
        if matches!(
            value.kind,
            BoundExpressionKind::MethodGroup { .. } | BoundExpressionKind::UnboundLambda(_)
        ) && !target.is_error()
            && !self.is_function_target(target)
            && let Some((operator, parameter)) =
                self.function_conversion_operator(&value, target, false)
        {
            let converted = self.convert(value, &parameter);
            return self.operator_call(operator, converted, target.clone());
        }
        // A lambda or a method group given to `object`, `Delegate` or
        // `Expression` is first the delegate it is on its own (§10.7.3 of
        // C# 10), and then that delegate converted.
        if matches!(
            value.kind,
            BoundExpressionKind::MethodGroup { .. } | BoundExpressionKind::UnboundLambda(_)
        ) && !target.is_error()
            && !self.is_function_target(target)
            && let Some(natural) = self.natural_conversion_through(&value, target)
        {
            let converted = self.convert(value, &natural);
            if converted.is_error() {
                return converted;
            }
            return self.convert(converted, target);
        }
        if let Some(converted) = self.convert_span(&value, target) {
            return converted;
        }
        // `null` given to a pointer is the address zero: a conversion the
        // backend has to see, since it is no reference.
        if matches!(value.ty, Type::Null)
            && matches!(target, Type::Pointer(_) | Type::FunctionPointer(_))
        {
            let span = value.span;
            return BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(value),
                    conversion: ConversionKind::Identity,
                    written: false,
                },
                target.clone(),
                span,
            );
        }
        // `&M` has no type of its own: the function pointer it is given to
        // says which overload it is the address of.
        if let (BoundExpressionKind::AddressOf { operand }, Type::FunctionPointer(signature)) =
            (&value.kind, target)
            && matches!(operand.kind, BoundExpressionKind::MethodGroup { .. })
        {
            let signature = signature.clone();
            return self.convert_address_of(value, &signature, target);
        }
        // A method group is the one value whose conversion is not a cast: it
        // becomes a delegate holding the overload that matches.
        if matches!(value.kind, BoundExpressionKind::MethodGroup { .. }) {
            return self.convert_method_group(value, target);
        }
        // An interpolated string given to an interpolated string handler is
        // made into one (C# 10), and so is an addition of them; given to a
        // `FormattableString` one keeps its holes apart from its text
        // (§12.8.3).
        if value.is_interpolated_string() && self.is_handler_type(target) {
            return self.handler_conversion(value, target, Vec::new());
        }
        if matches!(value.kind, BoundExpressionKind::InterpolatedString(_))
            && self.is_formattable(target)
        {
            return self.formattable(value, target);
        }
        // A lambda is the other: its body is bound here, against the
        // parameters the delegate names.
        if let BoundExpressionKind::UnboundLambda(at) = value.kind {
            let Some(node) = self.syntax_at(at) else {
                return BoundExpression::error(value.span);
            };
            let bound = self.bind_lambda_body(&node, target);
            // The span was recorded as having no type when the lambda was
            // first met, because at that point it had none. It has one now.
            self.body.types.insert(at, bound.ty.clone());
            return bound;
        }
        // `new(a, b)` is a creation of whatever it is being converted to.
        if let BoundExpressionKind::UnboundCreation(at) = value.kind {
            let node = self.syntax_at(at);
            return match node {
                // `Alignment? a = new(direction, width)` makes an `Alignment`
                // and wraps it: a `Nullable<T>` has no such constructor.
                Some(node) => {
                    let inner = self.binder.nullable_underlying(target);
                    let made =
                        self.bind_object_creation(&node, Some(inner.as_ref().unwrap_or(target)));
                    self.body.types.insert(at, made.ty.clone());
                    if inner.is_some() {
                        self.convert(made, target)
                    } else {
                        made
                    }
                }
                None => BoundExpression::error(value.span),
            };
        }
        // `ulong f = n switch { 0 => 1, _ => 2 }` is an `int` by its arms
        // and a `ulong` by the switch expression conversion (§12.6.3.?):
        // where every arm reaches the target on its own, the whole thing is
        // bound again with the target, arm by arm.
        if let BoundExpressionKind::Switch { arms, .. } = &value.kind
            && !value.ty.is_error()
            && !target.is_error()
            && value.ty != *target
            && !self.binder.converts_implicitly(&value.ty, target)
            && arms.iter().all(|arm| {
                arm.value.ty.is_error()
                    || matches!(arm.value.ty, Type::Null)
                    || self.binder.converts_implicitly(&arm.value.ty, target)
                    || self.constant_fits(&arm.value, target)
                    || (arm.value.is_interpolated_string() && self.is_handler_type(target))
            })
            && let Some(node) = self.syntax_at(value.span)
            && node.kind() == SyntaxKind::SwitchExpression
        {
            let made = self.bind_switch_expression(&node, Some(target));
            self.body.types.insert(value.span, made.ty.clone());
            return made;
        }
        // `flag ? a => a : b => b` types both its branches from what the
        // whole thing is being converted to.
        // A `switch` expression whose arms have no type of their own takes
        // the one it is given, arm by arm.
        if let BoundExpressionKind::UnboundSwitch(at) = value.kind {
            let node = self.syntax_at(at);
            return match node {
                Some(node) => {
                    let made = self.bind_switch_expression(&node, Some(target));
                    self.body.types.insert(at, made.ty.clone());
                    made
                }
                None => BoundExpression::error(value.span),
            };
        }
        if let BoundExpressionKind::UnboundConditional(at) = value.kind {
            let node = self.syntax_at(at);
            return match node {
                Some(node) => {
                    let made = self.bind_conditional(&node, Some(target));
                    self.body.types.insert(at, made.ty.clone());
                    made
                }
                None => BoundExpression::error(value.span),
            };
        }
        // A conditional whose branches could not decide what it is: each one is
        // converted to what the whole thing was given to instead.
        if value.ty.is_error() && matches!(value.kind, BoundExpressionKind::Conditional { .. }) {
            let (span, kind) = (value.span, value.kind);
            let BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } = kind
            else {
                unreachable!("the kind was just matched")
            };
            let consequence = self.convert(*consequence, target);
            let alternative = self.convert(*alternative, target);
            return BoundExpression::new(
                BoundExpressionKind::Conditional {
                    condition,
                    consequence: Box::new(consequence),
                    alternative: Box::new(alternative),
                },
                target.clone(),
                span,
            );
        }
        // A `switch` expression whose arms could not decide either.
        if value.ty.is_error() && matches!(value.kind, BoundExpressionKind::Switch { .. }) {
            let (span, kind) = (value.span, value.kind);
            let BoundExpressionKind::Switch { governing, arms } = kind else {
                unreachable!("the kind was just matched")
            };
            let mut converted = Vec::with_capacity(arms.len());
            for arm in arms {
                let value = self.convert(arm.value, target);
                converted.push(BoundSwitchArm {
                    pattern: arm.pattern,
                    when: arm.when,
                    value,
                });
            }
            return BoundExpression::new(
                BoundExpressionKind::Switch {
                    governing,
                    arms: converted,
                },
                target.clone(),
                span,
            );
        }
        // `stackalloc T[n]` given to a `Span<T>` is the span over that memory
        // (§12.8.22): the same allocation, wrapped.
        if let BoundExpressionKind::StackAlloc { element, span, .. } = &value.kind
            && span.is_none()
            && self.is_span_of(target, element)
        {
            let position = value.span;
            let BoundExpressionKind::StackAlloc {
                element,
                count,
                elements,
                ..
            } = value.kind
            else {
                unreachable!("matched a stackalloc above");
            };
            // What is made is always a `Span<T>`, and a `ReadOnlySpan<T>` is
            // what the `Span<T>` converts to (Roslyn's
            // `BoundConvertedStackAllocExpression`): a `ReadOnlySpan<T>`
            // need not have a constructor taking a pointer.
            let span_type = self
                .binder
                .compilation()
                .type_by_metadata_name("System.Span`1")
                .map(|span| Type::Named {
                    symbol: span,
                    type_arguments: vec![element.clone()],
                })
                .filter(|span| span != target);
            let made_as = span_type.clone().unwrap_or_else(|| target.clone());
            let made = BoundExpression::new(
                BoundExpressionKind::StackAlloc {
                    element,
                    count,
                    elements,
                    span: Some(made_as.clone()),
                },
                made_as,
                position,
            );
            return if span_type.is_some() {
                self.convert(made, target)
            } else {
                made
            };
        }
        // `[a, b]` is made into whatever it is being converted to.
        if let BoundExpressionKind::UnboundCollection(at) = value.kind {
            let node = self.syntax_at(at);
            return match node {
                Some(node) => {
                    let made = self.bind_collection(&node, target);
                    self.body.types.insert(at, made.ty.clone());
                    made
                }
                None => BoundExpression::error(value.span),
            };
        }
        // `(1, flag ? [x] : [])` into an `(int, ImmutableArray<T>)` converts
        // each element to the element beside it (§10.2.13), which is how an
        // element with no type of its own gets one.
        // A `ValueTuple<…>` spelled out is the tuple type it is: its elements
        // are taken the same way, past seven through the nested rest.
        if let BoundExpressionKind::TupleCreation(values) = &value.kind
            && !matches!(target, Type::Tuple(_))
            && !target.is_error()
            && let Some(flat) = self.flat_tuple_element_types(target)
            && flat.len() == values.len()
            && holds_typeless(values)
        {
            let spelled = Type::Tuple(
                flat.into_iter()
                    .map(|ty| crate::types::TupleElement { name: None, ty })
                    .collect(),
            );
            let converted = self.convert(value, &spelled);
            return self.convert(converted, target);
        }
        if let (BoundExpressionKind::TupleCreation(values), Type::Tuple(elements)) =
            (&value.kind, target)
            && values.len() == elements.len()
            && !target.is_error()
            && value.ty != *target
        {
            let span = value.span;
            let BoundExpressionKind::TupleCreation(values) = value.kind else {
                unreachable!("matched a tuple creation above");
            };
            let converted: Vec<BoundExpression> = values
                .into_iter()
                .zip(elements)
                .map(|(element, wanted)| self.convert(element, &wanted.ty))
                .collect();
            return BoundExpression::new(
                BoundExpressionKind::TupleCreation(converted),
                target.clone(),
                span,
            );
        }
        if target.is_error() || value.ty.is_error() || value.ty == *target {
            return value;
        }
        // An inline array into a `Span<T>` or a `ReadOnlySpan<T>` is the span
        // over its elements (C# 12).
        if let Some((element, length)) = self.binder.inline_array_of(&value.ty)
            && self.binder.is_span_of(target, &element)
        {
            let readonly = target.symbol()
                != self
                    .binder
                    .compilation()
                    .type_by_metadata_name("System.Span`1")
                || !self.is_writable_place(&value);
            let span = value.span;
            return self
                .inline_array_span(value, &element, length, readonly, span)
                .unwrap_or_else(|| BoundExpression::error(span));
        }
        // `(1, 2)` into a `(byte, int)?` is a `(byte, int)` first, and then
        // one wrapped: the literal converts element by element to the type
        // inside, which then converts as a whole.
        if let Some(inner) = self.binder.nullable_underlying(target)
            && self.tuple_element_types(&inner).is_some()
            && self.binder.nullable_underlying(&value.ty).is_none()
            && (matches!(value.kind, BoundExpressionKind::TupleCreation(_))
                || self.tuple_element_types(&value.ty).is_some())
            && value.ty != inner
        {
            let converted = self.convert(value, &inner);
            if converted.ty == inner {
                return self.convert(converted, target);
            }
            let span = converted.span;
            let found = self.display(&converted.ty);
            let wanted = self.display(target);
            self.report(ErrorCode::ErrNoImplicitConv, span, &[&found, &wanted]);
            return BoundExpression::error(span);
        }
        // `5` into a `decimal?` is a `decimal` first — a call, since the
        // runtime has no conversion of its own to one — and then wrapped.
        if let Some(inner) = self.binder.nullable_underlying(target)
            && self.binder.nullable_underlying(&value.ty).is_none()
            && !matches!(value.ty, Type::Null)
            && value.ty != inner
            && self.binder.special_of(&inner) == Some(SpecialType::Decimal)
            && self.binder.special_of(&value.ty).is_some()
        {
            let converted = self.convert(value, &inner);
            return self.convert(converted, target);
        }
        // A tuple into a tuple of other element types is made anew, element
        // by element (§10.2.13), and each element converts as it would on
        // its own — through an operator its type declares, too.
        if let Some(converted) = self.convert_tuple_value(value.clone(), target, false) {
            return converted;
        }
        // `IntHolder? y = 3` converts the `3` through `IntHolder`'s
        // operator and wraps what it gives (§10.6.2); from an `int?` the
        // conversion is lifted, below.
        if let Some(inner) = self.binder.nullable_underlying(target)
            && inner != value.ty
            && !matches!(value.ty, Type::Null)
            && self.binder.nullable_underlying(&value.ty).is_none()
            && self.user_defined_conversion(&value.ty, target).is_none()
            && let Some(operator) = self.user_defined_conversion(&value.ty, &inner)
        {
            let call = self.operator_call(operator, value, inner);
            return self.convert(call, target);
        }
        // `C1 x = (1, null)`: a literal with no type of its own brings no
        // operators of its own either (§10.5.4), and only the target's are
        // asked — a `ValueTuple` declaring one to `C1` does not.
        if lacks_a_natural_type(&value)
            && let Some((operator, takes)) = self.tuple_literal_operator(&value, target)
        {
            let value = self.convert(value, &takes);
            return self.operator_call(operator, value, target.clone());
        }
        // A conversion the program wrote itself is a call, not a cast: the
        // type said how values reach it, and that code has to run.
        if let Some(operator) = self.user_defined_conversion(&value.ty, target) {
            return self.operator_call(operator, value, target.clone());
        }
        if let Some(lifted) = self.lift_user_defined_conversion(value.clone(), target, false) {
            return lifted;
        }
        // `C x = 1` with an `implicit operator C(byte)`: the constant
        // reaches the `byte`, and the operator the rest of the way.
        if let Some((operator, takes)) = self.constant_operator(&value, target) {
            let value = self.convert(value, &takes);
            return self.operator_call(operator, value, target.clone());
        }
        if let Some((operator, takes)) = self.tuple_literal_operator(&value, target) {
            let value = self.convert(value, &takes);
            return self.operator_call(operator, value, target.clone());
        }
        // `Pet pet = dog;` makes the union from its case (C# 15), where
        // nothing of the language's own and no operator reaches it.
        if !self
            .binder
            .converts_implicitly_but_by_union(&value.ty, target)
            && !(matches!(value.ty, Type::Null)
                && (self.binder.nullable_underlying(target).is_some()
                    || target.is_reference_type(self.binder.compilation().symbols())))
            && let Some(made) = self.union_conversion(value.clone(), target)
        {
            return made;
        }
        // `$"dog"` reaches an operator taking a `FormattableString` or an
        // `IFormattable` through the interpolated string conversion first.
        if matches!(value.kind, BoundExpressionKind::InterpolatedString(_)) {
            for name in ["System.FormattableString", "System.IFormattable"] {
                let Some(formattable) = self.framework_type(name) else {
                    continue;
                };
                if let Some(operator) = self.user_defined_conversion(&formattable, target) {
                    let value = self.convert(value, &formattable);
                    return self.operator_call(operator, value, target.clone());
                }
            }
        }
        // `(int)elementType` on an `UnmanagedType?` reads the value out and
        // then converts it (§10.3.2): two steps, and the first may throw.
        // Only a value type on the other side goes through the value; an
        // `object` or an interface takes the `T?` boxed as it is.
        if let Some(inner) = self.binder.nullable_underlying(&value.ty)
            && self.binder.nullable_underlying(target).is_none()
            && inner != *target
            && !matches!(target, Type::TypeParameter(_))
            && !target.is_reference_type(self.binder.compilation().symbols())
        {
            let span = value.span;
            let unwrapped = BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(value),
                    conversion: ConversionKind::NullableUnwrap,
                    written: false,
                },
                inner,
                span,
            );
            return self.convert(unwrapped, target);
        }
        let Some(conversion) = self.classify(&value.ty, target) else {
            return value;
        };
        let span = value.span;
        BoundExpression::new(
            BoundExpressionKind::Conversion {
                operand: Box::new(value),
                conversion,
                written: false,
            },
            target.clone(),
            span,
        )
    }

    /// A union conversion (C# 15): the union's constructor, or its
    /// provider's `Create`, that overload resolution picks for the value,
    /// called with it. A `U?` gets the `U` made and wrapped.
    fn union_conversion(
        &mut self,
        value: BoundExpression,
        target: &Type,
    ) -> Option<BoundExpression> {
        let (union, nullable) = match self.binder.nullable_underlying(target) {
            Some(inner) => (inner, true),
            None => (target.clone(), false),
        };
        let members = self.binder.union_members(&union)?;
        let span = value.span;
        let candidates: Vec<SymbolId> = members
            .creations
            .iter()
            .map(|(member, _)| *member)
            .collect();
        if candidates.is_empty() {
            return None;
        }
        // A `Create` of a provider is written in the union's terms: its
        // `T` is the union's.
        let symbols = self.binder.compilation().symbols();
        let through = match (&union, symbols.get(candidates[0]).container) {
            (
                Type::Named {
                    symbol,
                    type_arguments,
                },
                Some(container),
            ) if container != *symbol => Type::Named {
                symbol: container,
                type_arguments: type_arguments.clone(),
            },
            _ => union.clone(),
        };
        let arguments = vec![value];
        let types: Vec<Type> = arguments
            .iter()
            .map(|argument| argument.ty.clone())
            .collect();
        let Resolved {
            method,
            substitution,
            ..
        } = self.resolve_call(
            &candidates,
            &types,
            &self.evidence(&arguments),
            &through,
            &[],
        )?;
        let arguments = self.convert_arguments(method, arguments, &through, &substitution, span);
        let constructor = symbols.get(method).name == ".ctor";
        let made = BoundExpression::new(
            if constructor {
                BoundExpressionKind::ObjectCreation {
                    constructor: Some(method),
                    arguments,
                    initializers: Vec::new(),
                }
            } else {
                BoundExpressionKind::Call {
                    // A provider's `Create` is reached through the union
                    // that implements it.
                    receiver: Some(Box::new(BoundExpression::new(
                        BoundExpressionKind::TypeExpression(union.symbol()?),
                        union.clone(),
                        span,
                    ))),
                    method,
                    type_arguments: Vec::new(),
                    arguments,
                    virtual_call: false,
                }
            },
            union.clone(),
            span,
        );
        Some(if nullable {
            self.convert(made, target)
        } else {
            made
        })
    }

    /// A call to a conversion operator on `value`, giving `target`.
    ///
    /// The operand goes the way any argument does: converted to what the
    /// operator takes, and by reference where it takes `in` — `implicit
    /// operator SyntaxListBuilder(in SeparatedSyntaxListBuilder<T>)` wants
    /// the builder's address, not a copy.
    /// An implicit span conversion (C# 14), made of the operators and
    /// methods the span types have: an array or a string through the span's
    /// `op_Implicit`, a `Span<T>` into a `ReadOnlySpan<T>` through its own,
    /// and a `ReadOnlySpan<Derived>` into a `ReadOnlySpan<Base>` through
    /// `ReadOnlySpan<Base>.CastUp<Derived>` — which is how Roslyn lowers them.
    /// `None` where there is no such conversion, or where the value already
    /// has the type.
    fn convert_span(&mut self, value: &BoundExpression, target: &Type) -> Option<BoundExpression> {
        if value.ty == *target
            || !self.binder.first_class_spans()
            || !self.binder.implicit_span_conversion(&value.ty, target)
        {
            return None;
        }
        let (_, wanted) = self.binder.span_parts(target)?;
        let span = value.span;
        // First to a span of the value's own element; then, where that is
        // not the element wanted, up to it.
        let (own, element) = match &value.ty {
            Type::Array { element, .. } => {
                // `ReadOnlySpan<object>` from a `string[]` is made from the
                // array as an `object[]`, which it already is.
                let element = if self.binder.span_parts(target)?.0 {
                    wanted.clone()
                } else {
                    (**element).clone()
                };
                let array = Type::Array {
                    element: Box::new(element.clone()),
                    rank: 1,
                };
                let spanned = Type::Named {
                    symbol: target.symbol()?,
                    type_arguments: vec![element.clone()],
                };
                let operator = self.binder.implicit_operator(&array, &spanned)?;
                (
                    self.operator_call(operator, value.clone(), spanned),
                    element,
                )
            }
            ty if self.binder.span_parts(ty).is_some() => {
                let (readonly, element) = self.binder.span_parts(ty)?;
                if readonly {
                    (value.clone(), element)
                } else {
                    let spanned = Type::Named {
                        symbol: target.symbol()?,
                        type_arguments: vec![element.clone()],
                    };
                    let operator = self.binder.implicit_operator(ty, &spanned)?;
                    (
                        self.operator_call(operator, value.clone(), spanned),
                        element,
                    )
                }
            }
            ty => {
                // `string` into `ReadOnlySpan<char>`.
                let operator = self.binder.implicit_operator(ty, target)?;
                return Some(self.operator_call(operator, value.clone(), target.clone()));
            }
        };
        if element == wanted || self.binder.same_but_for_dynamic(&element, &wanted) {
            return Some(BoundExpression::new(own.kind, target.clone(), span));
        }
        let definition = target.symbol()?;
        let cast_up = self
            .binder
            .compilation()
            .symbols()
            .lookup(definition, "CastUp")
            .first()
            .copied()?;
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(BoundExpression::new(
                    BoundExpressionKind::TypeExpression(definition),
                    target.clone(),
                    span,
                ))),
                method: cast_up,
                type_arguments: vec![element],
                arguments: vec![own],
                virtual_call: false,
            },
            target.clone(),
            span,
        ))
    }

    pub(super) fn operator_call(
        &mut self,
        operator: SymbolId,
        value: BoundExpression,
        target: Type,
    ) -> BoundExpression {
        let span = value.span;
        // The operator is declared by one of the two types, and where that
        // type is generic its parameter is written in the type's own terms:
        // `ReadOnlySpan<T>.op_Implicit(T[])` takes a `char[]` only once
        // `ReadOnlySpan<char>` says what `T` is.
        let symbols = self.binder.compilation().symbols();
        let container = symbols.get(operator).container;
        // A tuple's operators are its `ValueTuple`'s, and named through it.
        let named = |ty: &Type| match ty {
            Type::Tuple(elements) => self.tuple_as_named(elements),
            _ => self.binder.nullable_underlying(ty).map_or_else(
                || ty.clone(),
                |inner| match &inner {
                    Type::Tuple(elements) => self.tuple_as_named(elements),
                    _ => ty.clone(),
                },
            ),
        };
        let (target_named, value_named) = (named(&target), named(&value.ty));
        // A type parameter's operator is its constraint's (C# 11): through
        // `IConv<T>`, the operator's `T` is the `T` at hand.
        let constraint = |ty: &Type| match ty {
            Type::TypeParameter(parameter) => self
                .binder
                .base_types_of(*parameter)
                .iter()
                .find(|base| container.is_some() && base.symbol() == container)
                .cloned(),
            _ => None,
        };
        let through = if container.is_some() && container == target_named.symbol() {
            target_named
        } else if container.is_some() && container == value_named.symbol() {
            value_named
        } else if let Some(constraint) = constraint(&value.ty).or_else(|| constraint(&target)) {
            constraint
        } else if let Some(base) =
            container.and_then(|container| self.binder.constructed_from(&value_named, container))
        {
            // An operator of the source's base class, as the source
            // constructs it: `Pref<bool>` reaches `UserSetting<bool>`'s.
            base
        } else {
            Type::Void
        };
        let parameter = symbols
            .get(operator)
            .as_method()
            .and_then(|detail| detail.parameters.first().copied());
        let ref_kind = parameter
            .and_then(|parameter| symbols.get(parameter).as_parameter())
            .map_or(RefKind::None, |detail| detail.ref_kind);
        // The operand is widened to what the operator takes by the
        // language's own conversions and no other: `(Wide)narrowValue`
        // reaches `op_Explicit(int)` from a `short`, and asking for a
        // user-defined conversion here would ask for this one again.
        let wanted = parameter.map(|parameter| self.member_type(parameter, &through));
        let value = match wanted {
            // A tuple reaches the operator's tuple element by element.
            Some(wanted)
                if wanted != value.ty
                    && !wanted.is_error()
                    && (matches!(value.kind, BoundExpressionKind::TupleCreation(_))
                        || self.flat_tuple_element_types(&value.ty).is_some())
                    && self.is_tuple_or_nullable_tuple(&wanted) =>
            {
                self.convert(value, &wanted)
            }
            Some(wanted) if wanted != value.ty && !wanted.is_error() => {
                match self.classify(&value.ty, &wanted) {
                    Some(conversion) => BoundExpression::new(
                        BoundExpressionKind::Conversion {
                            operand: Box::new(value),
                            conversion,
                            written: false,
                        },
                        wanted,
                        span,
                    ),
                    None => value,
                }
            }
            _ => value,
        };
        let argument = if ref_kind == RefKind::In {
            let ty = value.ty.clone();
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::In,
                    operand: Box::new(value),
                },
                ty,
                span,
            )
        } else {
            value
        };
        // The operator of a constructed type is a member of that
        // construction: `Wrapper<int>.op_Equality` is not a method anything
        // can call by its definition alone, so the type stands as the
        // receiver, the way it does for any static call written through it.
        let receiver = container
            .filter(|_| through != Type::Void && through.symbol().is_some())
            .map(|container| {
                Box::new(BoundExpression::new(
                    BoundExpressionKind::TypeExpression(container),
                    through.clone(),
                    span,
                ))
            });
        // The call gives what the operator returns; the rest of the way to
        // the target — `int` into `long?` after `op_Explicit(Test)` — is the
        // language's own conversion, written out so that every backend, an
        // expression tree included, sees both steps.
        let returns = self.member_type(operator, &through);
        let call = BoundExpression::new(
            BoundExpressionKind::Call {
                receiver,
                method: operator,
                type_arguments: Vec::new(),
                arguments: vec![argument],
                virtual_call: false,
            },
            if returns.is_error() {
                target.clone()
            } else {
                returns.clone()
            },
            span,
        );
        if returns.is_error() || returns == target {
            return call;
        }
        if self.flat_tuple_element_types(&returns).is_some()
            && self.is_tuple_or_nullable_tuple(&target)
        {
            return self.convert(call, &target);
        }
        // `op_Implicit` to an array, and then the span conversion (C# 14).
        if let Some(spanned) = self.convert_span(&call, &target) {
            return spanned;
        }
        match self.classify(&returns, &target) {
            Some(conversion) => BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(call),
                    conversion,
                    written: false,
                },
                target,
                span,
            ),
            None => BoundExpression::new(call.kind, target, span),
        }
    }

    /// A cast that reaches a user-defined operator only by unwrapping a
    /// `T?` on one side of it (§10.5.5): `(C)i` on an `int?` where `C`
    /// converts from `int` reads `i.Value` and calls the operator, and
    /// `(C)s` where an operator gives a `C?` calls it and reads the `Value`.
    fn cast_through_nullable(
        &mut self,
        value: &BoundExpression,
        target: &Type,
    ) -> Option<BoundExpression> {
        if value.ty.is_error() || target.is_error() || value.ty == *target {
            return None;
        }
        if self.binder.implicit_operator(&value.ty, target).is_some()
            || self.binder.converts_implicitly(&value.ty, target)
        {
            return None;
        }
        let operator_for = |body: &Self, from: &Type, to: &Type| {
            body.binder
                .implicit_operator(from, to)
                .or_else(|| body.binder.explicit_operator(from, to))
        };
        let symbols = self.binder.compilation().symbols();
        let span = value.span;
        if let Some(inner) = self.binder.nullable_underlying(&value.ty)
            && self.binder.nullable_underlying(target).is_none()
            && self.binder.special_of(target) != Some(SpecialType::Object)
            && !matches!(target, Type::TypeParameter(_))
            && let Some(operator) = operator_for(self, &inner, target)
        {
            let unwrapped = BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(value.clone()),
                    conversion: ConversionKind::NullableUnwrap,
                    written: false,
                },
                inner,
                span,
            );
            return Some(self.operator_call(operator, unwrapped, target.clone()));
        }
        if self.binder.nullable_underlying(target).is_none()
            && !target.is_reference_type(symbols)
            && !matches!(target, Type::TypeParameter(_) | Type::Pointer(_))
            && self.binder.special_of(target).is_none()
        {
            let lifted = self.nullable_of(target.clone());
            // The operator is `C`'s own, declared as giving a `C?`.
            let declared = target.symbol().and_then(|owner| {
                ["op_Implicit", "op_Explicit"].into_iter().find_map(|name| {
                    self.binder
                        .lookup_member(owner, name)
                        .into_iter()
                        .find(|operator| {
                            let takes = self
                                .binder
                                .compilation()
                                .symbols()
                                .get(*operator)
                                .as_method()
                                .and_then(|detail| detail.parameters.first().copied());
                            takes.is_some_and(|parameter| {
                                let taken = self.member_type(parameter, target);
                                taken == value.ty
                                    || self.binder.converts_implicitly(&value.ty, &taken)
                            }) && self.member_type(*operator, target) == lifted
                        })
                })
            });
            if let Some(operator) = declared {
                let call = self.operator_call(operator, value.clone(), lifted.clone());
                return Some(BoundExpression::new(
                    BoundExpressionKind::Conversion {
                        operand: Box::new(call),
                        conversion: ConversionKind::NullableUnwrap,
                        written: true,
                    },
                    target.clone(),
                    span,
                ));
            }
        }
        None
    }

    /// The `op_Implicit` this conversion needs, where the language's own
    /// conversions do not reach.
    ///
    /// Asked only when nothing standard applies: a numeric widening and a
    /// reference conversion are instructions, and a user-defined one is a
    /// call, so it matters which of them a `Conversion` node means.
    pub(super) fn user_defined_conversion(&self, from: &Type, to: &Type) -> Option<SymbolId> {
        if self.binder.special_of(to) == Some(SpecialType::Object) {
            return None;
        }
        if from.is_reference_type(self.binder.compilation().symbols())
            == to.is_reference_type(self.binder.compilation().symbols())
            && self.binder.inherits_from_public(from, to)
        {
            return None;
        }
        if let (Some(from_special), Some(to_special)) =
            (self.binder.special_of(from), self.binder.special_of(to))
            && from_special.is_numeric()
            && to_special.is_numeric()
        {
            return None;
        }
        self.binder.implicit_operator(from, to)
    }

    /// The element types of a tuple type, written `(A, B)` or read out of
    /// metadata as a `ValueTuple<A, B>`.
    pub(super) fn tuple_element_types(&self, ty: &Type) -> Option<Vec<Type>> {
        match ty {
            Type::Tuple(elements) => {
                Some(elements.iter().map(|element| element.ty.clone()).collect())
            }
            Type::Named {
                symbol,
                type_arguments,
            } if !type_arguments.is_empty() => {
                let symbols = self.binder.compilation().symbols();
                let named = symbols.get(*symbol);
                let in_system = named
                    .container
                    .is_some_and(|container| symbols.get(container).name == "System");
                (named.name == "ValueTuple" && in_system).then(|| type_arguments.clone())
            }
            _ => None,
        }
    }

    /// The element types of a tuple type, all of them: a long tuple read
    /// as a `ValueTuple<…, ValueTuple<…>>` has its `Rest` taken apart too.
    pub(super) fn flat_tuple_element_types(&self, ty: &Type) -> Option<Vec<Type>> {
        if let Type::Tuple(elements) = ty {
            return Some(elements.iter().map(|element| element.ty.clone()).collect());
        }
        let mut elements = self.tuple_element_types(ty)?;
        if elements.len() == 8 {
            let rest = elements.pop()?;
            elements.extend(self.flat_tuple_element_types(&rest)?);
        }
        Some(elements)
    }

    /// Whether a type is a tuple, or a `T?` of one.
    fn is_tuple_or_nullable_tuple(&self, ty: &Type) -> bool {
        let inner = self
            .binder
            .nullable_underlying(ty)
            .unwrap_or_else(|| ty.clone());
        self.flat_tuple_element_types(&inner).is_some()
    }

    /// A tuple value into a tuple type of other element types: held in a
    /// local, and a new tuple made of its elements converted one by one —
    /// implicitly, or as a cast would where `explicit` says the program
    /// wrote one. `None` where either side is not a tuple of that many
    /// elements, or where nothing but the names differ.
    fn convert_tuple_value(
        &mut self,
        value: BoundExpression,
        target: &Type,
        explicit: bool,
    ) -> Option<BoundExpression> {
        if matches!(value.kind, BoundExpressionKind::TupleCreation(_)) {
            return None;
        }
        // `(int, C)?` into a `(int, (object, C))?`: lifted, element by
        // element inside.
        if let (Some(from), Some(to)) = (
            self.binder.nullable_underlying(&value.ty),
            self.binder.nullable_underlying(target),
        ) && from != to
            && self.flat_tuple_element_types(&from).is_some()
            && self.flat_tuple_element_types(&to).is_some()
        {
            return self.lift_conversion(value, target, |this, inner| {
                if explicit {
                    this.convert_explicitly(inner, &to)
                } else {
                    this.convert(inner, &to)
                }
            });
        }
        // `((D, D)?)xt` on a `(C, C)`: the tuple is converted element by
        // element, and what that makes is wrapped.
        if self.binder.nullable_underlying(&value.ty).is_none()
            && let Some(to) = self.binder.nullable_underlying(target)
            && self.flat_tuple_element_types(&to).is_some()
        {
            let inner = self.convert_tuple_value(value, &to, explicit)?;
            let span = inner.span;
            return Some(BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(inner),
                    conversion: ConversionKind::NullableWrap,
                    written: false,
                },
                target.clone(),
                span,
            ));
        }
        let from = self.flat_tuple_element_types(&value.ty)?;
        let to = self.flat_tuple_element_types(target)?;
        if from.len() != to.len() || from == to || to.iter().any(Type::is_error) {
            return None;
        }
        let span = value.span;
        let tuple = value.ty.clone();
        let held = self.declare_synthetic_local("tuple", tuple.clone());
        let store = BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(BoundExpression::new(
                    BoundExpressionKind::Local(held),
                    tuple.clone(),
                    span,
                )),
                value: Box::new(value),
            },
            tuple.clone(),
            span,
        );
        let mut elements = Vec::with_capacity(to.len());
        for (at, (from, to)) in from.into_iter().zip(to).enumerate() {
            let element = self.tuple_element(held, &tuple, at, from, span);
            elements.push(if explicit {
                self.convert_explicitly(element, &to)
            } else {
                self.convert(element, &to)
            });
        }
        let made = BoundExpression::new(
            BoundExpressionKind::TupleCreation(elements),
            target.clone(),
            span,
        );
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(vec![store, made]),
            target.clone(),
            span,
        ))
    }

    /// What a cast does (§12.9.7): an explicit conversion, which may be one a
    /// type declares with `explicit operator`. A tuple is cast element by
    /// element, each as though it had been cast on its own.
    pub(super) fn convert_explicitly(
        &mut self,
        value: BoundExpression,
        ty: &Type,
    ) -> BoundExpression {
        let span = value.span;
        // `(ReadOnlySpan<object>)strings` is the implicit span conversion,
        // written out, and `(CustomHandler)$"..."` the handler conversion.
        if let Some(spanned) = self.convert_span(&value, ty) {
            return spanned;
        }
        if value.is_interpolated_string() && self.is_handler_type(ty) {
            return self.handler_conversion(value, ty, Vec::new());
        }
        if let (BoundExpressionKind::TupleCreation(_), Some(to)) =
            (&value.kind, self.flat_tuple_element_types(ty))
            && let BoundExpressionKind::TupleCreation(values) = &value.kind
            && values.len() == to.len()
        {
            let BoundExpressionKind::TupleCreation(values) = value.kind else {
                unreachable!("matched a tuple creation above");
            };
            let elements = values
                .into_iter()
                .zip(to)
                .map(|(element, to)| self.convert_explicitly(element, &to))
                .collect();
            return BoundExpression::new(
                BoundExpressionKind::TupleCreation(elements),
                ty.clone(),
                span,
            );
        }
        // A tuple that no tuple conversion reaches is one error, on the
        // cast, and not one for each element that fails to convert.
        let impossible = self.cast_span.is_some() && self.conversion_is_impossible(&value.ty, ty);
        let reported = if impossible {
            self.cast_span.take()
        } else {
            None
        };
        let converted = self.convert_tuple_value(value.clone(), ty, true);
        if let Some(cast) = reported {
            self.cast_span = Some(cast);
            if converted.is_some() {
                let (from, to) = (self.display(&value.ty), self.display(ty));
                self.report(ErrorCode::ErrNoExplicitConv, cast, &[&from, &to]);
            }
        }
        if let Some(converted) = converted {
            return converted;
        }
        // A pointer and a native integer convert to each other by a
        // conversion the language has (C# 11's `nint` is `IntPtr`), not by
        // the `op_Explicit`s `IntPtr` declares for older compilers.
        let native = |ty: &Type| {
            ty.symbol().is_some_and(|symbol| {
                matches!(
                    self.binder
                        .compilation()
                        .symbols()
                        .qualified_name(symbol)
                        .as_str(),
                    "System.IntPtr" | "System.UIntPtr"
                )
            })
        };
        let pointer = |ty: &Type| matches!(ty, Type::Pointer(_) | Type::FunctionPointer(_));
        // So do a native integer and a number (§10.3.2, C# 11): `(long)n` on
        // an `nuint` is the bits it has, where `UIntPtr`'s operator to
        // `uint` — the one found first — throws past four thousand million.
        // A `decimal` is reached by `System.Decimal`'s own operators, as
        // from any integer.
        let number = |ty: &Type| {
            self.binder
                .special_of(ty)
                .is_some_and(|special| special.is_numeric() && special != SpecialType::Decimal)
                || self.binder.enum_underlying(ty).is_some()
        };
        let built_in = (pointer(&value.ty) && native(ty))
            || (native(&value.ty) && pointer(ty))
            || (native(&value.ty) && (number(ty) || native(ty)))
            || (number(&value.ty) && native(ty));
        let checked = self.in_checked_context(self.cast_span.unwrap_or(value.span));
        if !built_in
            && let Some(operator) = self.binder.explicit_operator_in(&value.ty, ty, checked)
        {
            // An implicit operator is in the running too, but the one taking
            // exactly what is cast is the most specific (§10.5.5): `(Str)1`
            // reaches `explicit operator Str(int)` over `implicit operator
            // Str(double)`.
            let exact = |body: &Self, operator: SymbolId| {
                let symbols = body.binder.compilation().symbols();
                symbols
                    .get(operator)
                    .as_method()
                    .and_then(|detail| detail.parameters.first().copied())
                    .is_some_and(|parameter| {
                        let mut sink = Diagnostics::new();
                        body.binder.type_of(parameter, &mut sink) == value.ty
                    })
            };
            // Among operators taking exactly what is cast, the one giving
            // exactly the target is: `(long)c` reaches `explicit operator
            // long(C)` over `implicit operator int(C)` and a widening.
            let gives_exactly = |body: &Self, operator: SymbolId| {
                let mut sink = Diagnostics::new();
                body.binder.type_of(operator, &mut sink) == *ty
            };
            let implicit_user = self.binder.implicit_operator(&value.ty, ty);
            // A union conversion gives way to an operator the cast names
            // (C# 15).
            if !self.binder.converts_implicitly(&value.ty, ty)
                || (implicit_user.is_none()
                    && !self.binder.converts_implicitly_but_by_union(&value.ty, ty))
                || (implicit_user.is_some_and(|implicit| !exact(self, implicit))
                    && exact(self, operator))
                || (implicit_user.is_some_and(|implicit| {
                    exact(self, implicit) && !gives_exactly(self, implicit)
                }) && exact(self, operator)
                    && gives_exactly(self, operator))
            {
                return self.operator_call(operator, value, ty.clone());
            }
        }
        if !self.binder.converts_implicitly(&value.ty, ty) {
            if let Some(lifted) = self.lift_user_defined_conversion(value.clone(), ty, true) {
                return lifted;
            }
            // `(S)i` on an `int?` with an operator from `decimal`: the value
            // is taken out first — which throws where there is none — and
            // then converted as an `int` would be.
            if let Some(inner) = self.binder.nullable_underlying(&value.ty)
                && self.binder.nullable_underlying(ty).is_none()
                && !ty.is_reference_type(self.binder.compilation().symbols())
                && self
                    .binder
                    .explicit_operator_in(
                        &inner,
                        ty,
                        self.in_checked_context(self.cast_span.unwrap_or(value.span)),
                    )
                    .is_some()
            {
                let span = value.span;
                let unwrapped = BoundExpression::new(
                    BoundExpressionKind::Conversion {
                        operand: Box::new(value),
                        conversion: ConversionKind::NullableUnwrap,
                        written: false,
                    },
                    inner,
                    span,
                );
                return self.convert_explicitly(unwrapped, ty);
            }
        }
        if let Some(call) = self.cast_through_nullable(&value, ty) {
            return call;
        }
        // A cast down to a derived class is a standard conversion, and a
        // standard conversion is never passed over for a user-defined one
        // (§10.5.5).
        let symbols = self.binder.compilation().symbols();
        if value.ty.is_reference_type(symbols)
            && ty.is_reference_type(symbols)
            && value.ty != *ty
            && self.binder.inherits_from_public(ty, &value.ty)
            && let Some(conversion) = self.classify(&value.ty, ty)
        {
            return BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(value),
                    conversion,
                    written: true,
                },
                ty.clone(),
                span,
            );
        }
        // `(Union)x` from a type the union derives from or implements is
        // the unboxing or the reference conversion it always was, not a
        // union conversion (C# 15).
        if !self.binder.converts_implicitly_but_by_union(&value.ty, ty)
            && self.binder.union_converts(&value.ty, ty)
            && self.binder.converts_implicitly_but_by_union(ty, &value.ty)
            && let Some(conversion) = self.classify(&value.ty, ty)
        {
            return BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(value),
                    conversion,
                    written: true,
                },
                ty.clone(),
                span,
            );
        }
        // Nothing above took it: where it is certain that nothing can, the
        // cast is CS0030. It was bound as whatever the two types' shapes
        // suggested — `(string)5` as a boxing — and compiled.
        // An interpolated string is a `string` that also becomes a
        // `FormattableString` or a handler: what converts is the
        // expression, not its type.
        if let Some(cast) = self.cast_span
            && !value.is_interpolated_string()
            && self.conversion_is_impossible(&value.ty, ty)
        {
            let (from, to) = (self.display(&value.ty), self.display(ty));
            self.report(ErrorCode::ErrNoExplicitConv, cast, &[&from, &to]);
        }
        let converted = self.convert(value, ty);
        // The source wrote this one, so it is what the expression gives
        // rather than what something asked for: `(string)o` is a `string`,
        // not an `object`.
        let kind = match converted.kind {
            BoundExpressionKind::Conversion {
                operand,
                conversion,
                ..
            } => BoundExpressionKind::Conversion {
                operand,
                conversion,
                written: true,
            },
            kind => kind,
        };
        BoundExpression::new(kind, ty.clone(), span)
    }

    /// Whether it is certain that no conversion, implicit or explicit, takes
    /// a `from` to a `to` (CS0030).
    ///
    /// Certain, not likely: a cast the language has is never called
    /// impossible here, and one it has not may be let through. So only the
    /// plain shapes are judged, and only where no conversion operator could
    /// be in play: none is declared by either type or anything it derives
    /// from.
    ///
    /// - Two classes neither of which derives from the other, a struct and a
    ///   class that is not one every struct boxes to, two structs that are
    ///   not both numbers.
    /// - An interface and a sealed class, a delegate, a struct or an enum
    ///   that does not implement it. A class that is not sealed may have an
    ///   heir that does (§10.3.5), and an interface of a generic family the
    ///   type implements another of may convert by variance, so neither is
    ///   judged. Nor is a type whose interfaces are not all known: the
    ///   synthesised core library gives `int` and `Enum` none.
    /// - Two delegate types of different declarations: only the instances
    ///   of one generic delegate convert to one another, by variance.
    /// - Arrays: of different ranks, of elements one of which is a value
    ///   type and the two are not one type, or of reference types that
    ///   convert in neither direction; and an array and a class, a delegate,
    ///   a struct or an enum that is not one an array always converts to.
    ///   Arrays and interfaces are left alone: a vector is an `IList<T>`,
    ///   and more.
    /// - Tuples: of different arities, or with an element pair that nothing
    ///   converts.
    ///
    /// Pointers, type parameters and `dynamic` each have rules of their own,
    /// and are left alone.
    fn conversion_is_impossible(&self, from: &Type, to: &Type) -> bool {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        // `(int)b` on a `bool?` is as impossible as on a `bool`: a nullable
        // converts as what it holds does (§10.6.1).
        let strip = |ty: &Type| {
            self.binder
                .nullable_underlying(ty)
                .unwrap_or_else(|| ty.clone())
        };
        let (from, to) = (strip(from), strip(to));
        if from == to {
            return false;
        }
        // Tuples convert element by element, whatever they are called:
        // `(int, string)` is a `ValueTuple<int, string>`, written another
        // way, and nothing else about one differs from a struct but this.
        let is_value_tuple = |ty: &Type| {
            ty.symbol().is_some_and(|symbol| {
                symbols
                    .qualified_name(symbol)
                    .starts_with("System.ValueTuple`")
            })
        };
        match (
            self.binder.tuple_elements(&from),
            self.binder.tuple_elements(&to),
        ) {
            (Some(from), Some(to)) => {
                return from.len() != to.len()
                    || from
                        .iter()
                        .zip(&to)
                        .any(|(from, to)| self.conversion_is_impossible(from, to));
            }
            // A `ValueTuple` that cannot be read as a tuple is one that is
            // not understood.
            (None, _) if is_value_tuple(&from) => return false,
            (_, None) if is_value_tuple(&to) => return false,
            _ => {}
        }
        let as_struct = |ty: &Type| match ty {
            Type::Tuple(elements) => self.binder.value_tuple_of(
                &elements
                    .iter()
                    .map(|element| element.ty.clone())
                    .collect::<Vec<_>>(),
            ),
            other => Some(other.clone()),
        };
        let (Some(from), Some(to)) = (as_struct(&from), as_struct(&to)) else {
            return false;
        };
        // Named types said in full: no type parameter, nothing that did not
        // bind, no `dynamic` anywhere inside.
        fn closed(ty: &Type) -> bool {
            match ty {
                Type::Named { type_arguments, .. } => type_arguments.iter().all(closed),
                _ => false,
            }
        }
        // The same, and arrays of them.
        fn known(ty: &Type) -> bool {
            match ty {
                Type::Array { element, .. } => known(element),
                other => closed(other),
            }
        }
        fn mentions_tuple(ty: &Type) -> bool {
            match ty {
                Type::Tuple(_) => true,
                Type::Array { element, .. } => mentions_tuple(element),
                Type::Named { type_arguments, .. } => type_arguments.iter().any(mentions_tuple),
                _ => false,
            }
        }
        if from == to
            || !known(&from)
            || !known(&to)
            || self.binder.converts_implicitly(&from, &to)
            || self.binder.converts_implicitly(&to, &from)
            || self.binder.inline_array_of(&from).is_some()
            || self.binder.is_union_type(&from)
            || self.binder.is_union_type(&to)
        {
            return false;
        }
        // Arrays of one rank convert when what they hold does: an explicit
        // reference conversion between reference types, and nothing between
        // value types that are not one type (§10.3.5). No operator is in
        // play: neither is a type that could declare one.
        if let (
            Type::Array {
                element: from_element,
                rank: from_rank,
            },
            Type::Array {
                element: to_element,
                rank: to_rank,
            },
        ) = (&from, &to)
        {
            if from_rank != to_rank {
                return true;
            }
            if from_element.is_reference_type(symbols) && to_element.is_reference_type(symbols) {
                return self.conversion_is_impossible(from_element, to_element);
            }
            // `(int, int)` and `ValueTuple<int, int>` are one type.
            return !mentions_tuple(from_element) && !mentions_tuple(to_element);
        }
        // For an array and something else, the something else.
        let (from_symbol, to_symbol) = match (&from, &to) {
            (Type::Array { .. }, other) | (other, Type::Array { .. }) => {
                let Some(symbol) = other.symbol() else {
                    return false;
                };
                (symbol, symbol)
            }
            _ => {
                let (Some(from_symbol), Some(to_symbol)) = (from.symbol(), to.symbol()) else {
                    return false;
                };
                (from_symbol, to_symbol)
            }
        };
        // What every value type boxes to, and the classes arrays and
        // delegates derive from.
        let universal = |symbol: SymbolId| {
            matches!(
                symbols.qualified_name(symbol).as_str(),
                "System.Object"
                    | "System.ValueType"
                    | "System.Enum"
                    | "System.Array"
                    | "System.Delegate"
                    | "System.MulticastDelegate"
                    | "System.Void"
                    | "System.TypedReference"
            )
        };
        if universal(from_symbol) || universal(to_symbol) {
            return false;
        }
        // What a type is, as far as a cast between two of them cares;
        // anything else is not judged.
        #[derive(PartialEq, Clone, Copy)]
        enum Shape {
            Class,
            Value,
            Delegate,
            Interface,
        }
        let shape = |symbol: SymbolId| {
            let detail = symbols.get(symbol);
            if detail
                .as_named_type()
                .is_some_and(|named| named.anonymous || named.ref_like)
            {
                return None;
            }
            match detail.type_kind()? {
                TypeKind::Class | TypeKind::Record => Some(Shape::Class),
                TypeKind::Struct | TypeKind::RecordStruct | TypeKind::Enum => Some(Shape::Value),
                TypeKind::Delegate => Some(Shape::Delegate),
                TypeKind::Interface => Some(Shape::Interface),
            }
        };
        let (Some(from_shape), Some(to_shape)) = (shape(from_symbol), shape(to_symbol)) else {
            return false;
        };
        // Numbers, characters, enums and native integers convert among
        // themselves (§10.3.2, §10.3.3).
        let number = |ty: &Type| {
            self.binder
                .special_of(ty)
                .is_some_and(SpecialType::is_numeric)
                || self.binder.enum_underlying(ty).is_some()
                || self.binder.native_int(ty).is_some()
        };
        if number(&from) && number(&to) {
            return false;
        }
        // A conversion operator is looked for in both types and in what
        // they derive from, and reaches further by a standard conversion
        // before it and after (§10.5.5): one whose parameter is related to
        // what is cast, and whose result to what it is cast to. `string`
        // declares one to `ReadOnlySpan<char>`, which has nothing to say
        // about `(string)5`; where one could have, this does not say what
        // it reaches.
        let related = |first: &Type, second: &Type| {
            first == second
                || self.binder.converts_implicitly(first, second)
                || self.binder.converts_implicitly(second, first)
        };
        let operator_in_play = |declaring: &Type| {
            let Some(symbol) = declaring.symbol() else {
                return true;
            };
            ["op_Implicit", "op_Explicit", "op_CheckedExplicit"]
                .into_iter()
                .flat_map(|name| self.binder.lookup_member(symbol, name))
                .any(|operator| {
                    let Some(parameter) = symbols
                        .get(operator)
                        .as_method()
                        .and_then(|detail| detail.parameters.first().copied())
                    else {
                        return true;
                    };
                    let takes = self.member_type(parameter, declaring);
                    let gives = self.member_type(operator, declaring);
                    !closed(&strip(&takes))
                        || !closed(&strip(&gives))
                        || (related(&from, &strip(&takes)) && related(&strip(&gives), &to))
                })
        };
        let declares_conversion = |ty: &Type| {
            let mut current = Some(ty.clone());
            let mut depth = 0;
            while let Some(declaring) = current {
                // A base said in terms of its heir's type parameters is one
                // whose operators cannot be read here.
                if depth > 32 || !closed(&declaring) || operator_in_play(&declaring) {
                    return true;
                }
                current = declaring
                    .symbol()
                    .and_then(|symbol| self.binder.base_class_of(symbol));
                depth += 1;
            }
            false
        };
        let from_array = matches!(from, Type::Array { .. });
        if from_array || matches!(to, Type::Array { .. }) {
            // An array reaches `object` and `Array`, which are universal
            // above, and the interfaces a vector implements, which are not
            // judged; no class, delegate, struct or enum is one.
            let (other, other_shape) = if from_array {
                (&to, to_shape)
            } else {
                (&from, from_shape)
            };
            return other_shape != Shape::Interface && !declares_conversion(other);
        }
        // Two interfaces convert, one way or the other, whatever they are.
        if from_shape == Shape::Interface && to_shape == Shape::Interface {
            return false;
        }
        if from_shape == Shape::Interface || to_shape == Shape::Interface {
            let (other, other_shape, interface) = if from_shape == Shape::Interface {
                (&to, to_shape, &from)
            } else {
                (&from, from_shape, &to)
            };
            // A class that is not sealed may have an heir that implements
            // it (§10.3.5); a struct, an enum and a delegate have none.
            let sealed = other_shape != Shape::Class
                || other.symbol().is_some_and(|symbol| {
                    symbols.get(symbol).modifiers.contains(Modifiers::SEALED)
                });
            return sealed
                && self.implements_nothing_like(other, interface)
                && !declares_conversion(&from)
                && !declares_conversion(&to);
        }
        // Delegates convert to one another only where they are one generic
        // declaration, by variance.
        if from_shape == Shape::Delegate && to_shape == Shape::Delegate && from_symbol == to_symbol
        {
            return false;
        }
        if declares_conversion(&from) || declares_conversion(&to) {
            return false;
        }
        // Two classes (or delegates) are related or not, which the two
        // questions above answered; a struct reaches no class but the
        // universal ones, and no other struct at all.
        true
    }

    /// Whether it is certain that `ty` implements no interface of the
    /// family `to` is one of: an instance of it converts to `to`, or from
    /// it, by identity or by variance, and nothing else does.
    ///
    /// Certain only where everything `ty` derives from has its interfaces
    /// listed, which the synthesised core library's types do not: its `int`
    /// lists none, nor does its `Enum`. `object` and `ValueType` list none
    /// in the real one either.
    fn implements_nothing_like(&self, ty: &Type, to: &Type) -> bool {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        let synthesised = |symbol: SymbolId| {
            compilation.is_from_corlib(symbol) && !compilation.is_from_metadata(symbol)
        };
        let Some(wanted) = to.symbol() else {
            return false;
        };
        if synthesised(wanted) || self.binder.co_class(wanted).is_some() {
            return false;
        }
        let mut pending = vec![ty.clone()];
        let mut seen = Vec::new();
        while let Some(next) = pending.pop() {
            let Some(symbol) = next.symbol() else {
                return false;
            };
            if seen.contains(&symbol) {
                continue;
            }
            seen.push(symbol);
            if symbol == wanted || seen.len() > 256 {
                return false;
            }
            if synthesised(symbol)
                && !matches!(
                    symbols.qualified_name(symbol).as_str(),
                    "System.Object" | "System.ValueType"
                )
            {
                return false;
            }
            pending.extend(self.binder.direct_bases(&next));
        }
        true
    }

    pub(super) fn classify(&self, from: &Type, to: &Type) -> Option<ConversionKind> {
        let symbols = self.binder.compilation().symbols();
        if matches!(from, Type::Null) {
            return None;
        }
        // `int` into an `int?` makes one holding the value, and back out of it
        // reads the value: neither is a widening, and treating them as one
        // emits nothing at all.
        if self.binder.nullable_underlying(to).is_some()
            && self.binder.nullable_underlying(from).is_none()
        {
            // `3` into a `byte?` converts the number first and then wraps it:
            // one conversion in the source is two on the way out.
            return Some(ConversionKind::NullableWrap);
        }
        if self
            .binder
            .nullable_underlying(from)
            .is_some_and(|inner| inner == *to)
        {
            return Some(ConversionKind::NullableUnwrap);
        }
        // `byte?` into an `int?` converts what is inside and keeps the null,
        // which is neither of the two above.
        if self.binder.nullable_underlying(from).is_some()
            && self.binder.nullable_underlying(to).is_some()
        {
            return Some(ConversionKind::NullableLift);
        }
        // Two function pointers are the same address whatever their
        // signatures say.
        if matches!(
            (from, to),
            (Type::FunctionPointer(_), Type::FunctionPointer(_))
        ) {
            return Some(ConversionKind::Identity);
        }
        // A pointer is a native integer to convert to and from (§23.5):
        // `(byte*)_pointer` on an `IntPtr` is a `conv.u`, not a box.
        if matches!(from, Type::Pointer(_) | Type::FunctionPointer(_))
            || matches!(to, Type::Pointer(_) | Type::FunctionPointer(_))
        {
            return Some(ConversionKind::Numeric);
        }
        // A tuple into a tuple of other element types is made anew, element
        // by element (§10.2.13); one of the same element types is the same
        // `ValueTuple` under other names, and nothing at all.
        if let (Some(from_elements), Some(to_elements)) = (
            self.flat_tuple_element_types(from),
            self.flat_tuple_element_types(to),
        ) && from_elements.len() == to_elements.len()
        {
            return Some(if from_elements == to_elements {
                ConversionKind::Identity
            } else {
                ConversionKind::TupleElements
            });
        }
        // A type parameter's value is boxed to reach anything else, and
        // unboxed to become another: `T` into `object` is a `box` even where
        // `T : class`, and `TSource` into `TDestination` is both in turn.
        match (from, to) {
            (Type::TypeParameter(_), Type::TypeParameter(_)) => {
                return Some(ConversionKind::Unboxing);
            }
            (Type::TypeParameter(_), _) if to.is_reference_type(symbols) => {
                return Some(ConversionKind::Boxing);
            }
            (_, Type::TypeParameter(_)) if from.is_reference_type(symbols) => {
                return Some(ConversionKind::Unboxing);
            }
            // Between a type parameter and a value type the value is boxed
            // and taken out as the other (§10.3.8): `(int)t` is `box !!T;
            // unbox.any int32`, which throws where `T` is no `int`. As a
            // number conversion it read a `string` as its address.
            (Type::TypeParameter(_), _) | (_, Type::TypeParameter(_)) => {
                return Some(ConversionKind::Unboxing);
            }
            _ => {}
        }
        let from_reference = from.is_reference_type(symbols);
        let to_reference = to.is_reference_type(symbols);
        match (from_reference, to_reference) {
            (false, false) => Some(ConversionKind::Numeric),
            (false, true) => Some(ConversionKind::Boxing),
            (true, false) => Some(ConversionKind::Unboxing),
            // Down the chain — `(ITypeSymbol)symbol` — is checked at run
            // time; only up it is free (§10.3.5).
            (true, true) if self.binder.converts_implicitly(from, to) => {
                Some(ConversionKind::ImplicitReference)
            }
            (true, true) => Some(ConversionKind::ExplicitReference),
        }
    }

    /// Whether a `?.` yielding this type has to say `T?` instead.
    ///
    /// Only a value type that is not already one: a reference has its own
    /// null, and `T?` has one too.
    pub(super) fn wraps_in_nullable(&self, ty: &Type) -> bool {
        // A tuple is a `ValueTuple`, and `method?.Bodies` on a `(Block,
        // Arrow)` property is a `(Block, Arrow)?`.
        if matches!(ty, Type::Tuple(_)) {
            return true;
        }
        let Some(symbol) = ty.symbol() else {
            return false;
        };
        let symbols = self.binder.compilation().symbols();
        // A `ref struct` has no `T?`: `x?.M()` returning one is a statement
        // whose value nothing reads.
        let ref_like = symbols
            .get(symbol)
            .as_named_type()
            .is_some_and(|detail| detail.ref_like);
        matches!(
            symbols.get(symbol).type_kind(),
            Some(TypeKind::Struct | TypeKind::Enum | TypeKind::RecordStruct)
        ) && !ref_like
            && self.binder.nullable_underlying(ty).is_none()
    }

    /// `T?`, where there is a `Nullable<T>` to make one of.
    pub(super) fn nullable_of(&self, ty: Type) -> Type {
        match self
            .binder
            .compilation()
            .type_by_metadata_name("System.Nullable`1")
        {
            Some(symbol) => Type::Named {
                symbol,
                type_arguments: vec![ty],
            },
            None => ty,
        }
    }

    /// `S?` into a `T?` through an operator from `S` to `T` (§10.6.2): the
    /// lifted form, which gives null for null and calls the operator on
    /// what is there otherwise. A reference type or a `T?` of one keeps the
    /// operator's result as it is. `None` where no such operator exists.
    fn lift_user_defined_conversion(
        &mut self,
        value: BoundExpression,
        target: &Type,
        explicit: bool,
    ) -> Option<BoundExpression> {
        let source = self.binder.nullable_underlying(&value.ty)?;
        let symbols = self.binder.compilation().symbols();
        let wanted = match self.binder.nullable_underlying(target) {
            Some(inner) => inner,
            None if target.is_reference_type(symbols) => target.clone(),
            None => return None,
        };
        if self.binder.special_of(&source).is_some() && self.binder.special_of(&wanted).is_some() {
            return None;
        }
        // An operator giving the `T?` itself is lifted too, and is the most
        // specific one (Roslyn lifts it though its result is no
        // non-nullable value type): `Conv?` into a `double?` through
        // `implicit operator double?(Conv)` is what that returns, and not
        // `implicit operator int(Conv)` widened.
        if wanted != *target
            && let Some(operator) = self.binder.implicit_operator(&source, target)
            && self.member_type(operator, &source) == *target
        {
            let result = target.clone();
            return self.lift_conversion(value, &result, |this, inner| {
                this.operator_call(operator, inner, result.clone())
            });
        }
        let operator = if explicit {
            let checked = self.in_checked_context(self.cast_span.unwrap_or(value.span));
            self.binder
                .explicit_operator_in(&source, &wanted, checked)
                .or_else(|| self.binder.implicit_operator(&source, &wanted))
        } else {
            self.user_defined_conversion(&source, &wanted)
        }?;
        let result = target.clone();
        self.lift_conversion(value, &result, |this, inner| {
            this.operator_call(operator, inner, wanted)
        })
    }

    /// `convert` applied to what a `T?` holds, as a lifted conversion does
    /// it: null where there is nothing, and otherwise the conversion of the
    /// value, wrapped where the result is a value type that can be. The
    /// operand is held in a local, since it is read twice.
    pub(super) fn lift_conversion(
        &mut self,
        value: BoundExpression,
        result: &Type,
        convert: impl FnOnce(&mut Self, BoundExpression) -> BoundExpression,
    ) -> Option<BoundExpression> {
        let span = value.span;
        let nullable = value.ty.clone();
        let symbol = nullable.symbol()?;
        let has_value = self
            .binder
            .lookup_member(symbol, "HasValue")
            .into_iter()
            .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)?;
        let local = self.declare_synthetic_local("lifted", nullable.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(local), nullable.clone(), span);
        let store = BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(value),
            },
            nullable,
            span,
        );
        let boolean = self.special(SpecialType::Boolean);
        let present = self.member_access(has_value, Some(Box::new(read.clone())), boolean, span);
        let inner = self.call_on(read, "GetValueOrDefault", Vec::new(), span)?;
        let converted = convert(self, inner);
        let converted = self.convert(converted, result);
        let chosen = BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(present),
                consequence: Box::new(converted),
                alternative: Box::new(BoundExpression::new(
                    BoundExpressionKind::Default(result.clone()),
                    result.clone(),
                    span,
                )),
            },
            result.clone(),
            span,
        );
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(vec![store, chosen]),
            result.clone(),
            span,
        ))
    }

    /// The predefined types a user-defined type converts to implicitly,
    /// through operators it declares: `IntHolder` with `implicit operator
    /// int(IntHolder)` offers an `int`, and an `IntHolder?` the lifted
    /// `int?`. Each comes with the operator that makes it.
    pub(super) fn predefined_conversions_of(&self, ty: &Type) -> Vec<(Type, SymbolId)> {
        let underlying = self.binder.nullable_underlying(ty);
        let base = underlying.clone().unwrap_or_else(|| ty.clone());
        let Some(symbol) = base.symbol() else {
            return Vec::new();
        };
        if base.is_error()
            || self.binder.special_of(&base).is_some()
            || self.binder.enum_underlying(&base).is_some()
        {
            return Vec::new();
        }
        let symbols = self.binder.compilation().symbols();
        let mut found = Vec::new();
        for operator in self.binder.lookup_member(symbol, "op_Implicit") {
            let Some(parameter) = symbols
                .get(operator)
                .as_method()
                .and_then(|detail| detail.parameters.first().copied())
            else {
                continue;
            };
            if self.member_type(parameter, &base) != base {
                continue;
            }
            let gives = self.member_type(operator, &base);
            let inner = self
                .binder
                .nullable_underlying(&gives)
                .unwrap_or_else(|| gives.clone());
            if self.binder.special_of(&inner).is_none()
                && self.binder.enum_underlying(&inner).is_none()
            {
                continue;
            }
            let target = if underlying.is_some()
                && self.binder.nullable_underlying(&gives).is_none()
                && !gives.is_reference_type(symbols)
            {
                self.nullable_of(gives)
            } else {
                gives
            };
            found.push((target, operator));
        }
        found
    }

    /// A value converted through a user-defined operator, lifted where the
    /// value is a `T?` and the operator takes the `T`: null stays null, and
    /// anything else is converted and wrapped (§10.6.2).
    pub(super) fn convert_through_operator(
        &mut self,
        value: BoundExpression,
        operator: SymbolId,
        target: &Type,
    ) -> BoundExpression {
        let span = value.span;
        let Some(inner) = self.binder.nullable_underlying(&value.ty) else {
            return self.operator_call(operator, value, target.clone());
        };
        let symbols = self.binder.compilation().symbols();
        let takes_nullable = symbols
            .get(operator)
            .as_method()
            .and_then(|detail| detail.parameters.first().copied())
            .is_some_and(|parameter| {
                let mut sink = Diagnostics::new();
                self.binder
                    .nullable_underlying(&self.binder.type_of(parameter, &mut sink))
                    .is_some()
            });
        if takes_nullable {
            return self.operator_call(operator, value, target.clone());
        }
        // A reference type is null where the value was; a value type is
        // wrapped into its `T?`.
        let result = if self.binder.nullable_underlying(target).is_some()
            || target.is_reference_type(self.binder.compilation().symbols())
        {
            target.clone()
        } else {
            self.nullable_of(target.clone())
        };
        let value_type = value.ty.clone();
        let held = self.declare_synthetic_local("lifted", value_type.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(held), value_type.clone(), span);
        let assigned = BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(value),
            },
            value_type,
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
        let Some(inside) = self.call_on(read, "GetValueOrDefault", Vec::new(), span) else {
            return BoundExpression::error(span);
        };
        let inside = BoundExpression::new(inside.kind, inner, span);
        let wanted = self
            .binder
            .nullable_underlying(&result)
            .unwrap_or_else(|| result.clone());
        let converted = self.operator_call(operator, inside, wanted);
        let converted = self.convert(converted, &result);
        BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(condition),
                consequence: Box::new(converted),
                alternative: Box::new(BoundExpression::new(
                    BoundExpressionKind::Default(result.clone()),
                    result.clone(),
                    span,
                )),
            },
            result,
            span,
        )
    }
}

/// Whether a tuple literal holds an element with no type of its own yet: a
/// lambda, a method group, or a tuple literal that does.
fn holds_typeless(values: &[BoundExpression]) -> bool {
    values.iter().any(|value| match &value.kind {
        BoundExpressionKind::UnboundLambda(_) | BoundExpressionKind::MethodGroup { .. } => true,
        BoundExpressionKind::TupleCreation(inner) => holds_typeless(inner),
        _ => false,
    })
}

/// Whether a tuple literal has no type of its own: one of its elements has
/// none, as `null` has not.
fn lacks_a_natural_type(value: &BoundExpression) -> bool {
    let BoundExpressionKind::TupleCreation(values) = &value.kind else {
        return false;
    };
    values.iter().any(|element| {
        matches!(element.ty, Type::Null)
            || super::typeless(element)
            || lacks_a_natural_type(element)
    })
}
