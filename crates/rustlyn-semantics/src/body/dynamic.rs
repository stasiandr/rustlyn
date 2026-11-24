//! Binding what is done to a `dynamic` value (§12.3.3).
//!
//! An operation whose receiver or one of whose operands is `dynamic` is not
//! resolved here: the member, the overload, the operator are for the runtime
//! binder to pick once it sees the values. What binding does is record what
//! was written — the name, the arguments and how each was passed — as a
//! [`BoundDynamic`], whose type is `dynamic` (the result of a conversion is
//! the type converted to, that of `new C(d)` is `C`).

use rustlyn_text::TextSpan;

use super::BodyBinder;
use crate::bound::{
    BoundDynamic, BoundExpression, BoundExpressionKind, DynamicOperation, DynamicUnary,
};
use crate::conversions::BinaryOperator;
use crate::types::Type;

impl BodyBinder<'_> {
    /// An operation for the runtime binder.
    pub(super) fn dynamic_operation(
        operation: DynamicOperation,
        receiver: Option<BoundExpression>,
        arguments: Vec<BoundExpression>,
        names: Vec<Option<String>>,
        ty: Type,
        span: TextSpan,
    ) -> BoundExpression {
        BoundExpression::new(
            BoundExpressionKind::Dynamic(Box::new(BoundDynamic {
                operation,
                receiver,
                arguments,
                names,
            })),
            ty,
            span,
        )
    }

    /// Whether any argument is `dynamic`, which makes a call one the runtime
    /// binds (§12.6.4.1: "dynamic binding" of an invocation).
    pub(super) fn has_dynamic_argument(arguments: &[BoundExpression]) -> bool {
        // One passed by reference does not make the call dynamic (Roslyn's
        // `HasDynamicArgument`): `F1(ref d.Length)` calls `F1(ref dynamic)`,
        // with what the member read put somewhere to refer to.
        arguments.iter().any(|argument| {
            !matches!(argument.kind, BoundExpressionKind::RefArgument { .. })
                && matches!(argument.ty, Type::Dynamic)
        })
    }

    /// `value` converted to `target` by the runtime binder: the implicit
    /// conversion of `dynamic` to any type (§10.2.10), or a cast of one.
    pub(super) fn dynamic_conversion(
        value: BoundExpression,
        target: &Type,
        explicit: bool,
    ) -> BoundExpression {
        let span = value.span;
        Self::dynamic_operation(
            DynamicOperation::Convert { explicit },
            Some(value),
            Vec::new(),
            Vec::new(),
            target.clone(),
            span,
        )
    }

    /// `receiver.name`, read.
    pub(super) fn dynamic_member(
        receiver: BoundExpression,
        name: &str,
        span: TextSpan,
    ) -> BoundExpression {
        Self::dynamic_operation(
            DynamicOperation::GetMember(name.to_string()),
            Some(receiver),
            Vec::new(),
            Vec::new(),
            Type::Dynamic,
            span,
        )
    }

    /// `left op right` where either side is `dynamic`.
    pub(super) fn dynamic_binary(
        operator: BinaryOperator,
        left: BoundExpression,
        right: BoundExpression,
        compound: bool,
        span: TextSpan,
    ) -> BoundExpression {
        Self::dynamic_operation(
            DynamicOperation::Binary { operator, compound },
            Some(left),
            vec![right],
            vec![None],
            Type::Dynamic,
            span,
        )
    }

    /// `left op right` where either side is `dynamic` (§12.4.7.3 binds
    /// the operator at run time).
    ///
    /// `&&` and `||` still evaluate the right only when the left does not
    /// decide: `left && right` is `IsFalse(left) ? left : left & right`, with
    /// the `&` told it is the logical one, which is how Roslyn has it.
    pub(super) fn bind_dynamic_binary(
        &mut self,
        operator: BinaryOperator,
        left: BoundExpression,
        right: BoundExpression,
        span: TextSpan,
    ) -> BoundExpression {
        match operator {
            BinaryOperator::Coalesce => {
                let left = self.convert(left, &Type::Dynamic);
                let right = self.convert(right, &Type::Dynamic);
                BoundExpression::new(
                    BoundExpressionKind::Binary {
                        operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    Type::Dynamic,
                    span,
                )
            }
            BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr => {
                let and = operator == BinaryOperator::LogicalAnd;
                let held = self.declare_synthetic_local("left", left.ty.clone());
                let left_type = left.ty.clone();
                let read =
                    BoundExpression::new(BoundExpressionKind::Local(held), left_type.clone(), span);
                let stored = BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(read.clone()),
                        value: Box::new(left),
                    },
                    left_type.clone(),
                    span,
                );
                let test = if matches!(left_type, Type::Dynamic) {
                    let test = if and {
                        DynamicUnary::IsFalse
                    } else {
                        DynamicUnary::IsTrue
                    };
                    self.dynamic_unary(test, stored, span)
                } else if let Some(operator) = self.truth_operator(&left_type, and) {
                    // A left that is no `bool` is asked by its own `false`
                    // (for `&&`) or `true` (for `||`) operator (§12.14.3),
                    // which may take it as a `T?`.
                    let boolean = self.special(crate::corlib::SpecialType::Boolean);
                    self.operator_call(operator, stored, boolean)
                } else {
                    let boolean = self.special(crate::corlib::SpecialType::Boolean);
                    let stored = self.convert(stored, &boolean);
                    if and {
                        BoundExpression::new(
                            BoundExpressionKind::Unary {
                                operator: crate::bound::UnaryOperator::LogicalNot,
                                operand: Box::new(stored),
                            },
                            boolean,
                            span,
                        )
                    } else {
                        stored
                    }
                };
                let decided = self.convert(read.clone(), &Type::Dynamic);
                let operation = Self::dynamic_binary(operator, read, right, false, span);
                BoundExpression::new(
                    BoundExpressionKind::Conditional {
                        condition: Box::new(test),
                        consequence: Box::new(decided),
                        alternative: Box::new(operation),
                    },
                    Type::Dynamic,
                    span,
                )
            }
            _ => Self::dynamic_binary(operator, left, right, false, span),
        }
    }

    /// The `false` operator (`and`) or the `true` one of a type that does
    /// not convert to `bool` itself, which `x && d` asks about `x`.
    fn truth_operator(&self, ty: &Type, and: bool) -> Option<crate::SymbolId> {
        let boolean = self.special(crate::corlib::SpecialType::Boolean);
        if self.binder.converts_implicitly(ty, &boolean) {
            return None;
        }
        let underlying = self
            .binder
            .nullable_underlying(ty)
            .unwrap_or_else(|| ty.clone());
        let name = if and { "op_False" } else { "op_True" };
        let symbols = self.binder.compilation().symbols();
        self.binder
            .lookup_member(underlying.symbol()?, name)
            .into_iter()
            .find(|operator| {
                symbols
                    .get(*operator)
                    .as_method()
                    .is_some_and(|detail| detail.parameters.len() == 1)
            })
    }

    /// `op operand` on a `dynamic` operand; `IsTrue` and `IsFalse` give back
    /// a `bool`.
    pub(super) fn dynamic_unary(
        &self,
        operator: DynamicUnary,
        operand: BoundExpression,
        span: TextSpan,
    ) -> BoundExpression {
        let ty = match operator {
            DynamicUnary::IsTrue | DynamicUnary::IsFalse => {
                self.special(crate::corlib::SpecialType::Boolean)
            }
            _ => Type::Dynamic,
        };
        Self::dynamic_operation(
            DynamicOperation::Unary(operator),
            Some(operand),
            Vec::new(),
            Vec::new(),
            ty,
            span,
        )
    }
}
