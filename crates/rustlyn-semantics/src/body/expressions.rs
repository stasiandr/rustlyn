//! Binding expressions: the dispatch on the kind of expression, literals,
//! interpolated strings, conditionals and `await`.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode, TokenValue};
use rustlyn_text::TextSpan;

use super::{BodyBinder, binary_operator, compound_operator, identifier_text, typeless};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundAwaiting, BoundExpression, BoundExpressionKind, BoundPattern, BoundPatternKind,
    ConstantValue, DynamicUnary, IncrementOperator, UnaryOperator,
};
use crate::corlib::SpecialType;
use crate::decimal::{Decimal, DecimalError};
use crate::symbol::{Modifiers, RefKind, SymbolKind};
use crate::types::{TupleElement, Type};

impl BodyBinder<'_> {
    pub(super) fn bind_conditional(
        &mut self,
        node: &SyntaxNode,
        target: Option<&Type>,
    ) -> BoundExpression {
        let span = node.span();
        let at = |kind, ty| BoundExpression::new(kind, ty, span);
        let mut children = node.children();
        let condition_node = children.next();
        let (Some(first), Some(second)) = (children.next(), children.next()) else {
            self.bind_condition(condition_node.as_ref());
            return BoundExpression::error(span);
        };
        // Nothing has said what this is yet, and the branches cannot say it
        // themselves. Wait for whatever it is given to, the way a lambda
        // written on its own waits.
        if target.is_none() && (self.written_typeless(&first) || self.written_typeless(&second)) {
            // One branch with a type says what the other is: `stores is null
            // ? [] : stores.ToImmutable()` is an `ImmutableArray<T>`, since
            // the `[]` reaches that and the conditional has that as its
            // natural type (§12.18). Two typeless branches wait.
            if self.written_typeless(&first) != self.written_typeless(&second) {
                let floor = self.speculation_floor();
                let condition = self.bind_condition(condition_node.as_ref());
                let typed_first = !self.written_typeless(&first);
                let (typed_node, other_node) = if typed_first {
                    (&first, &second)
                } else {
                    (&second, &first)
                };
                let typed = self.bind_expression(typed_node);
                let ty = typed.ty.clone();
                // `null` says nothing either: `input ? null : () => Run()`
                // is the delegate it is given to, and waits for that.
                if matches!(ty, Type::Null) {
                    self.unwind_speculation(floor);
                    return at(BoundExpressionKind::UnboundConditional(span), Type::Error);
                }
                let other = self.bind_expression(other_node);
                let other = if ty.is_error() || matches!(ty, Type::Null) || typeless(&typed) {
                    other
                } else {
                    self.convert(other, &ty)
                };
                let (consequence, alternative) = if typed_first {
                    (typed, other)
                } else {
                    (other, typed)
                };
                return at(
                    BoundExpressionKind::Conditional {
                        condition: Box::new(condition),
                        consequence: Box::new(consequence),
                        alternative: Box::new(alternative),
                    },
                    ty,
                );
            }
            return at(BoundExpressionKind::UnboundConditional(span), Type::Error);
        }
        let condition = self.bind_condition(condition_node.as_ref());
        if let Some(target) = target {
            let consequence = self.bind_expression(&first);
            let consequence = self.convert(consequence, target);
            let alternative = self.bind_expression(&second);
            let alternative = self.convert(alternative, target);
            return at(
                BoundExpressionKind::Conditional {
                    condition: Box::new(condition),
                    consequence: Box::new(consequence),
                    alternative: Box::new(alternative),
                },
                target.clone(),
            );
        }
        let consequence = self.bind_expression(&first);
        let alternative = self.bind_expression(&second);

        // `info == null ? default : ResultType` is the type of the branch
        // that has one: a bare `default` is a value of whatever it is put
        // beside (§12.18), the way `null` is.
        let is_default = |value: &BoundExpression| {
            matches!(value.kind, BoundExpressionKind::Default(Type::Error))
        };
        let (consequence, alternative) = match (is_default(&consequence), is_default(&alternative))
        {
            (true, false) if !alternative.ty.is_error() && !typeless(&alternative) => {
                let ty = alternative.ty.clone();
                (
                    BoundExpression::new(
                        BoundExpressionKind::Default(ty.clone()),
                        ty,
                        first.span(),
                    ),
                    alternative,
                )
            }
            (false, true) if !consequence.ty.is_error() && !typeless(&consequence) => {
                let ty = consequence.ty.clone();
                (
                    consequence,
                    BoundExpression::new(
                        BoundExpressionKind::Default(ty.clone()),
                        ty,
                        second.span(),
                    ),
                )
            }
            _ => (consequence, alternative),
        };

        // The result is whichever branch the other converts to. With
        // `null` on one side and a value type on the other there is no
        // such branch: what both reach is the nullable of it, which is
        // what the surrounding code asked for by writing `null` at
        // all. A struct `null` reaches through an operator of its own is
        // the branch: `n > 8 ? new ArraySegment<byte>(…) : null` is an
        // `ArraySegment<byte>`, the null made by its operator from `byte[]`.
        let ty = match (&consequence.ty, &alternative.ty) {
            // `dynamic` and any other type are `dynamic`, whichever comes
            // first: `flag ? text : dyn` converts both ways, and the
            // `dynamic` is the better of the two (§12.18).
            (Type::Dynamic, other) | (other, Type::Dynamic)
                if !other.is_error() && !typeless(&consequence) && !typeless(&alternative) =>
            {
                Type::Dynamic
            }
            (Type::Null, other) | (other, Type::Null)
                if !self.binder.held_by_reference(other)
                    && !matches!(other, Type::Null | Type::Error)
                    && self.binder.nullable_underlying(other).is_none()
                    && self.binder.null_operator(other).is_none() =>
            {
                self.nullable_of(other.clone())
            }
            // A lambda or a method group beside a branch with a type is a
            // value of that type: `b ? d : (string s) => int.Parse(s)` is
            // the delegate `d` is. Asked first: a group's own type is no
            // type, which any other converts to — `input ? Out :
            // (Func<int, Slot>)In` is a `Func<int, Slot>`.
            _ if typeless(&alternative)
                && !typeless(&consequence)
                && !matches!(consequence.ty, Type::Error | Type::Null) =>
            {
                consequence.ty.clone()
            }
            _ if typeless(&consequence)
                && !typeless(&alternative)
                && !matches!(alternative.ty, Type::Error | Type::Null) =>
            {
                alternative.ty.clone()
            }
            _ if self
                .binder
                .converts_implicitly(&alternative.ty, &consequence.ty) =>
            {
                consequence.ty.clone()
            }
            // A constant reaches types nothing else does: the `0` in
            // `Private | (isStatic ? Static : 0)` is a value of the enum on
            // the other side, and the whole thing is that enum (§10.2.4).
            _ if self.constant_fits(&alternative, &consequence.ty) => consequence.ty.clone(),
            _ if self.constant_fits(&consequence, &alternative.ty) => alternative.ty.clone(),
            _ if self
                .binder
                .converts_implicitly(&consequence.ty, &alternative.ty) =>
            {
                alternative.ty.clone()
            }
            _ if consequence.ty.is_error()
                || alternative.ty.is_error()
                || typeless(&consequence)
                || typeless(&alternative) =>
            {
                alternative.ty.clone()
            }
            // Neither branch's type takes the other — `simple ? new
            // Simple(...) : new Complex(...)` — so the conditional is typed
            // by what it is given to (§12.18), and waits for that.
            _ => {
                self.branch_types
                    .insert(span, vec![consequence.ty.clone(), alternative.ty.clone()]);
                return at(BoundExpressionKind::UnboundConditional(span), Type::Error);
            }
        };
        // A method group has no type of its own and no syntax that says so:
        // `flag ? null : holder.Close` reads like two values. Where the
        // branches cannot decide between them, they are left as they are for
        // whatever the conditional is given to to decide.
        if (typeless(&consequence) || typeless(&alternative))
            && matches!(ty, Type::Error | Type::Null)
        {
            return at(
                BoundExpressionKind::Conditional {
                    condition: Box::new(condition),
                    consequence: Box::new(consequence),
                    alternative: Box::new(alternative),
                },
                Type::Error,
            );
        }
        let consequence = self.convert(consequence, &ty);
        let alternative = self.convert(alternative, &ty);
        at(
            BoundExpressionKind::Conditional {
                condition: Box::new(condition),
                consequence: Box::new(consequence),
                alternative: Box::new(alternative),
            },
            ty,
        )
    }

    /// Binds what should be a `bool`, reporting it if it is not.
    pub(super) fn bind_condition(&mut self, node: Option<&SyntaxNode>) -> BoundExpression {
        let Some(node) = node else {
            return BoundExpression::error(TextSpan::default());
        };
        let bound = self.bind_expression(node);
        self.as_condition(node, bound)
    }

    /// A condition as the `bool` it is tested as (§12.24): itself where it
    /// is one, and otherwise through an implicit conversion its type
    /// declares to `bool`, or failing that its `operator true`.
    pub(super) fn as_condition(
        &mut self,
        node: &SyntaxNode,
        bound: BoundExpression,
    ) -> BoundExpression {
        // A `dynamic` condition asks the runtime binder whether it is true:
        // an `if`'s, a `for`'s, a `when`'s alike.
        if matches!(bound.ty, Type::Dynamic) {
            let span = bound.span;
            return self.dynamic_unary(DynamicUnary::IsTrue, bound, span);
        }
        let boolean = self.special(SpecialType::Boolean);
        // `if (default)` is `if (false)`: a bare `default` is the `bool` the
        // condition takes.
        if bound.ty.is_error() && matches!(bound.kind, BoundExpressionKind::Default(_)) {
            return self.convert(bound, &boolean);
        }
        if !bound.ty.is_error()
            && !self.binder.is_boolean(&bound.ty)
            && bound.ty.symbol().is_some()
            && self.binder.special_of(&bound.ty).is_none()
            // `if (s)` on an `S1?` asks `S1`'s `true(S1?)`; a `bool?` is no
            // condition at all.
            && self
                .binder
                .nullable_underlying(&bound.ty)
                .is_none_or(|inner| self.binder.special_of(&inner).is_none())
        {
            if let Some(operator) = self.user_defined_conversion(&bound.ty, &boolean) {
                return self.operator_call(operator, bound, boolean);
            }
            if let Some(call) = self.user_defined_unary("op_True", &bound, bound.span)
                && self.binder.is_boolean(&call.ty)
            {
                return call;
            }
        }
        self.check_condition(node, &bound.ty.clone());
        bound
    }

    /// The operand of a predefined `-`, `+` or `~` whose type declares no
    /// such operator but an implicit conversion to a type that has one
    /// (§12.4.4): `~mask` on Unity's `LayerMask` is `~(int)mask`. The
    /// predefined operators are tried from the best down — `int` before
    /// `long` before `double` — and the first the operand converts to
    /// wins; an operand of any other type is left as it is.
    fn predefined_unary_operand(
        &mut self,
        operator: UnaryOperator,
        operand: BoundExpression,
    ) -> BoundExpression {
        let symbols = self.binder.compilation().symbols();
        let converts = !operand.ty.is_error()
            && self.binder.special_of(&operand.ty).is_none()
            && self.binder.nullable_underlying(&operand.ty).is_none()
            && operand.ty.symbol().is_some_and(|symbol| {
                symbols.get(symbol).type_kind() != Some(crate::TypeKind::Enum)
            });
        if !converts {
            return operand;
        }
        let candidates: &[SpecialType] = match operator {
            UnaryOperator::Minus => &[
                SpecialType::Int32,
                SpecialType::Int64,
                SpecialType::Single,
                SpecialType::Double,
                SpecialType::Decimal,
            ],
            UnaryOperator::Plus => &[
                SpecialType::Int32,
                SpecialType::UInt32,
                SpecialType::Int64,
                SpecialType::UInt64,
                SpecialType::Single,
                SpecialType::Double,
                SpecialType::Decimal,
            ],
            _ => &[
                SpecialType::Int32,
                SpecialType::UInt32,
                SpecialType::Int64,
                SpecialType::UInt64,
            ],
        };
        for special in candidates {
            let target = self.special(*special);
            if let Some(conversion) = self.user_defined_conversion(&operand.ty, &target) {
                return self.operator_call(conversion, operand, target);
            }
        }
        operand
    }

    pub(super) fn check_condition(&mut self, node: &SyntaxNode, ty: &Type) {
        if !self.binder.is_boolean(ty) {
            let (found, boolean) = (self.display(ty), "bool".to_string());
            self.report(
                ErrorCode::ErrNoImplicitConv,
                node.span(),
                &[&found, &boolean],
            );
        }
    }

    /// A `decimal` constant, as C# writes one: `new decimal(lo, mid, hi,
    /// negative, scale)`.
    pub(super) fn decimal_expression(
        &mut self,
        lo: u32,
        mid: u32,
        high: u32,
        negative: bool,
        scale: u8,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let decimal = self.special(SpecialType::Decimal);
        let int = self.special(SpecialType::Int32);
        let boolean = self.special(SpecialType::Boolean);
        let byte = self.special(SpecialType::Byte);
        let literal = |value, ty: &Type| {
            BoundExpression::new(BoundExpressionKind::Literal(value), ty.clone(), span)
        };
        let parts = vec![
            literal(ConstantValue::Int32(lo as i32), &int),
            literal(ConstantValue::Int32(mid as i32), &int),
            literal(ConstantValue::Int32(high as i32), &int),
            literal(ConstantValue::Boolean(negative), &boolean),
            literal(ConstantValue::Int32(i32::from(scale)), &byte),
        ];
        self.make(&decimal, parts, span)
    }

    /// A `decimal` operation on constants as the constant it gives, worked
    /// out the way .NET works it out (see `decimal.rs`), as Roslyn works it
    /// out: `10 / 4m` is `2.5`, `(decimal)3.5` is `3.5`, `1m * -0m` is
    /// `-0m`, `(int)3.7m` is `3`, and `(double)(-0m)` is `-0.0`. An answer
    /// the type cannot hold is an error (CS0463, CS0031) and one divided by
    /// zero is another (CS0020); where this cannot say what .NET says, the
    /// operation is left for run time.
    pub(super) fn fold_decimal(&mut self, expression: BoundExpression) -> BoundExpression {
        use crate::conversions::BinaryOperator as Op;
        let span = expression.span;
        // An operator on `decimal`s is bound as one, or as the call of the
        // `op_Multiply` or `op_Addition` `System.Decimal` declares.
        if let Some((operator, left, right)) =
            decimal_arithmetic(self.binder.compilation().symbols(), &expression)
            && self.binder.special_of(&left.ty) == Some(SpecialType::Decimal)
            && self.binder.special_of(&right.ty) == Some(SpecialType::Decimal)
        {
            let (Some(b), Some(a)) = (self.decimal_operand(right), self.decimal_operand(left))
            else {
                return expression;
            };
            let ordering = a.compare(&b);
            let result = match operator {
                Op::Add => a.add(b),
                Op::Subtract => a.sub(b),
                Op::Multiply => a.mul(b),
                Op::Divide => a.div(b),
                Op::Modulo => a.rem(b),
                Op::Equality
                | Op::Inequality
                | Op::LessThan
                | Op::LessThanOrEqual
                | Op::GreaterThan
                | Op::GreaterThanOrEqual => {
                    let holds = match operator {
                        Op::Equality => ordering.is_eq(),
                        Op::Inequality => ordering.is_ne(),
                        Op::LessThan => ordering.is_lt(),
                        Op::LessThanOrEqual => ordering.is_le(),
                        Op::GreaterThan => ordering.is_gt(),
                        _ => ordering.is_ge(),
                    };
                    return BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Boolean(holds)),
                        expression.ty.clone(),
                        span,
                    );
                }
                _ => return expression,
            };
            return match result {
                Ok(value) => self.decimal_literal(value, span).unwrap_or(expression),
                Err(DecimalError::Overflow) => {
                    self.report(ErrorCode::ErrDecimalConstantFailed, span, &[]);
                    expression
                }
                Err(DecimalError::DivideByZero) => {
                    self.report(ErrorCode::ErrIntDivByZero, span, &[]);
                    expression
                }
                Err(DecimalError::Unsure) => expression,
            };
        }
        // The conversion may be bound as one, or as the `op_Explicit`
        // `System.Decimal` declares for it.
        let Some(operand) =
            decimal_conversion_operand(self.binder.compilation().symbols(), &expression)
        else {
            return expression;
        };
        let from = self.binder.special_of(&operand.ty);
        let to = self.binder.special_of(&expression.ty);
        if from == Some(SpecialType::Decimal) && to != Some(SpecialType::Decimal) {
            let Some(value) = self.decimal_operand(operand) else {
                return expression;
            };
            let constant = match to {
                Some(SpecialType::Double) => ConstantValue::Double(value.to_f64()),
                Some(SpecialType::Single) => ConstantValue::Single(value.to_f32()),
                Some(
                    special @ (SpecialType::SByte
                    | SpecialType::Byte
                    | SpecialType::Int16
                    | SpecialType::UInt16
                    | SpecialType::Char
                    | SpecialType::Int32
                    | SpecialType::UInt32
                    | SpecialType::Int64
                    | SpecialType::UInt64),
                ) => match integer_constant(special, value.truncated()) {
                    Some(constant) => constant,
                    None => {
                        let text = format!("{}M", value.text());
                        let ty = self.display(&expression.ty);
                        self.report(ErrorCode::ErrConstOutOfRange, span, &[&text, &ty]);
                        return expression;
                    }
                },
                _ => return expression,
            };
            return BoundExpression::new(
                BoundExpressionKind::Literal(constant),
                expression.ty.clone(),
                span,
            );
        }
        if to == Some(SpecialType::Decimal) && from != Some(SpecialType::Decimal) {
            let Some(folded) = self.binder.folded(operand) else {
                return expression;
            };
            let value = match (from, &folded) {
                (Some(SpecialType::Double), ConstantValue::Double(value)) => {
                    Decimal::from_f64(*value).ok_or_else(|| value.to_string())
                }
                (Some(SpecialType::Double), ConstantValue::Single(value)) => {
                    Decimal::from_f64(f64::from(*value)).ok_or_else(|| value.to_string())
                }
                (Some(SpecialType::Single), ConstantValue::Single(value)) => {
                    Decimal::from_f32(*value).ok_or_else(|| value.to_string())
                }
                (Some(SpecialType::Single), ConstantValue::Double(value)) => {
                    Decimal::from_f32(*value as f32).ok_or_else(|| value.to_string())
                }
                (Some(SpecialType::Single | SpecialType::Double), _) => return expression,
                // An integer of any width, a character, or an enum: a whole
                // number a `decimal` holds exactly.
                _ => match crate::constant::as_exact(&folded).and_then(Decimal::from_integer) {
                    Some(value) => Ok(value),
                    None => return expression,
                },
            };
            return match value {
                Ok(value) => self.decimal_literal(value, span).unwrap_or(expression),
                Err(text) => {
                    let ty = self.display(&expression.ty);
                    self.report(ErrorCode::ErrConstOutOfRange, span, &[&text, &ty]);
                    expression
                }
            };
        }
        expression
    }

    /// The `decimal` a bound expression is, where it is a constant.
    fn decimal_operand(&self, value: &BoundExpression) -> Option<Decimal> {
        match self.binder.decimal_constant(value)? {
            crate::bound::SpecialConstant::Decimal {
                scale,
                negative,
                hi,
                mid,
                lo,
            } => Decimal::from_parts(lo, mid, hi, negative, scale),
            crate::bound::SpecialConstant::DateTime(_) => None,
        }
    }

    /// A `decimal` constant as the expression that makes it.
    fn decimal_literal(&mut self, value: Decimal, span: TextSpan) -> Option<BoundExpression> {
        self.decimal_expression(
            value.lo,
            value.mid,
            value.hi,
            value.negative,
            value.scale,
            span,
        )
    }

    /// A `decimal` or `DateTime` constant as the expression that makes it.
    pub(super) fn special_constant_expression(
        &mut self,
        value: crate::bound::SpecialConstant,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        match value {
            crate::bound::SpecialConstant::Decimal {
                scale,
                negative,
                hi,
                mid,
                lo,
            } => self.decimal_expression(lo, mid, hi, negative, scale, span),
            crate::bound::SpecialConstant::DateTime(ticks) => {
                let date = self.framework_type("System.DateTime")?;
                let long = self.special(SpecialType::Int64);
                let ticks = BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Int64(ticks)),
                    long,
                    span,
                );
                self.make(&date, vec![ticks], span)
            }
        }
    }

    /// Binds an expression, recording its type against its span on the way out.
    pub fn bind_expression(&mut self, node: &SyntaxNode) -> BoundExpression {
        let bound = self.bind_expression_core(node);
        self.body.types.insert(node.span(), bound.ty.clone());
        self.note_symbol(node, &bound);
        self.recover_lambdas_in(node);
        bound
    }

    /// Records which declared symbol the name in `node` settled on.
    ///
    /// Only the name is recorded, not the expression around it: an outer
    /// expression over the same name — the call around a method group —
    /// finishes binding after the inner one and overwrites it with the
    /// sharper answer, which is the overload rather than every candidate.
    fn note_symbol(&mut self, node: &SyntaxNode, bound: &BoundExpression) {
        let mut kind = &bound.kind;
        while let BoundExpressionKind::Conversion { operand, .. } = kind {
            kind = &operand.kind;
        }
        let symbol = match kind {
            BoundExpressionKind::Parameter(symbol)
            | BoundExpressionKind::TypeExpression(symbol)
            | BoundExpressionKind::NamespaceExpression(symbol)
            | BoundExpressionKind::Field { field: symbol, .. }
            | BoundExpressionKind::Property {
                property: symbol, ..
            }
            | BoundExpressionKind::DelegateCreation { method: symbol, .. }
            | BoundExpressionKind::Call { method: symbol, .. }
            | BoundExpressionKind::EventAssignment { event: symbol, .. } => *symbol,
            BoundExpressionKind::MethodGroup { candidates, .. } => match candidates.first() {
                Some(symbol) => *symbol,
                None => return,
            },
            // An array's length is read by an instruction of its own, but the
            // name written is `System.Array.Length`.
            BoundExpressionKind::ArrayLength { .. } => {
                let compilation = self.binder.compilation();
                let Some(array) = compilation.type_by_metadata_name("System.Array") else {
                    return;
                };
                match self.binder.lookup_member(array, "Length").first() {
                    Some(length) => *length,
                    None => return,
                }
            }
            BoundExpressionKind::ObjectCreation { constructor, .. } => {
                match (constructor, &bound.ty) {
                    (Some(constructor), _) => *constructor,
                    (None, Type::Named { symbol, .. }) => *symbol,
                    _ => return,
                }
            }
            _ => return,
        };
        if let Some(span) = name_token_span(node) {
            self.body.symbols.insert(span, symbol);
        }
    }

    fn bind_expression_core(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let at = |kind, ty| BoundExpression::new(kind, ty, span);

        match node.kind() {
            SyntaxKind::NumericLiteralExpression
            | SyntaxKind::StringLiteralExpression
            | SyntaxKind::CharacterLiteralExpression
            | SyntaxKind::Utf8StringLiteralExpression => self.bind_literal(node),
            SyntaxKind::InterpolatedStringExpression => self.bind_interpolated_string(node),
            SyntaxKind::TrueLiteralExpression => at(
                BoundExpressionKind::Literal(ConstantValue::Boolean(true)),
                self.special(SpecialType::Boolean),
            ),
            SyntaxKind::FalseLiteralExpression => at(
                BoundExpressionKind::Literal(ConstantValue::Boolean(false)),
                self.special(SpecialType::Boolean),
            ),
            SyntaxKind::NullLiteralExpression => at(
                BoundExpressionKind::Literal(ConstantValue::Null),
                Type::Null,
            ),
            SyntaxKind::ThisExpression => {
                self.note_this_capture();
                at(BoundExpressionKind::This, self.this_type())
            }
            // `base.F()` in a lambda reads `this` as much as `this.F()` does.
            SyntaxKind::BaseExpression => {
                self.note_this_capture();
                at(
                    BoundExpressionKind::Base,
                    self.this_type()
                        .symbol()
                        .and_then(|symbol| self.binder.base_class_of(symbol))
                        .unwrap_or(Type::Error),
                )
            }
            SyntaxKind::ParenthesizedExpression => node.children().next().map_or_else(
                || BoundExpression::error(span),
                |inner| self.bind_expression(&inner),
            ),
            SyntaxKind::IdentifierName | SyntaxKind::GenericName => self.bind_name(node),
            // `info with { Receiver = null }` is a copy of `info` with those
            // members set: the names are the receiver's members, tuple
            // elements included, and the whole thing is the receiver's type.
            SyntaxKind::WithExpression => {
                let Some(receiver) = node
                    .children()
                    .find(|child| child.kind().is_expression())
                    .map(|receiver| self.bind_expression(&receiver))
                else {
                    return BoundExpression::error(span);
                };
                if let Some(made) = self.bind_anonymous_with(node, &receiver) {
                    return made;
                }
                let initializers = node
                    .child_of_kind(SyntaxKind::WithInitializerExpression)
                    .map(|initializer| self.bind_initializers(&initializer, &receiver.ty))
                    .unwrap_or_default();
                let ty = receiver.ty.clone();
                at(
                    BoundExpressionKind::With {
                        receiver: Box::new(receiver),
                        initializers,
                    },
                    ty,
                )
            }
            // `int.TryParse(...)` reaches a static member through a keyword.
            SyntaxKind::PredefinedType => {
                let ty = self.resolve(node);
                match ty.symbol() {
                    Some(symbol) => at(BoundExpressionKind::TypeExpression(symbol), ty),
                    None => BoundExpression::error(span),
                }
            }
            SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::PointerMemberAccessExpression
            | SyntaxKind::QualifiedName => {
                self.bind_member_access(node)
            }
            // `NT::Program` in `NT::Program.M2` names a type through an alias.
            SyntaxKind::AliasQualifiedName => {
                let mut sink = Diagnostics::new();
                let ty = self.binder.resolve_type(node, &self.context, &mut sink);
                match ty {
                    Type::Named { symbol, .. } => at(BoundExpressionKind::TypeExpression(symbol), ty),
                    _ => BoundExpression::new(
                        BoundExpressionKind::Unsupported(node.kind()),
                        Type::Error,
                        span,
                    ),
                }
            }
            SyntaxKind::ConditionalAccessExpression => self.bind_conditional_access(node),
            // `ref a[0]` on the right of a `ref` local: the value is where the
            // thing is, not what it holds.
            SyntaxKind::RefExpression => {
                match node.children().find(|child| child.kind().is_expression()) {
                    Some(operand) => {
                        let operand = self.bind_expression(&operand);
                        let ty = operand.ty.clone();
                        at(
                            BoundExpressionKind::RefArgument {
                                kind: RefKind::Ref,
                                operand: Box::new(operand),
                            },
                            ty,
                        )
                    }
                    None => BoundExpression::error(span),
                }
            }
            // `[a, b]` has no type until something says what collection it
            // is, exactly as a lambda has none until a delegate does.
            SyntaxKind::CollectionExpression => {
                // An `out var x` of its `with(...)` is in scope in the
                // elements, which are read before any collection is made:
                // `[with(out var x), x]`.
                for declaration in node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::WithElement)
                    .flat_map(|element| element.descendants().collect::<Vec<_>>())
                    .filter(|inner| {
                        inner.kind() == SyntaxKind::DeclarationExpression
                            && inner
                                .parent()
                                .is_some_and(|argument| argument.kind() == SyntaxKind::Argument)
                    })
                {
                    self.bind_out_declaration(&declaration);
                }
                self.note_collection_elements(node);
                at(BoundExpressionKind::UnboundCollection(span), Type::Error)
            }
            SyntaxKind::QueryExpression => self.bind_query(node),
            // `(a, b)` on the right of an `=` is a value with a type of its
            // own, which an overload and a lambda's return both have to see.
            // Neither backend makes one.
            SyntaxKind::TupleExpression => {
                let mut elements = Vec::new();
                let mut values = Vec::new();
                for argument in node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::Argument)
                {
                    let name = argument
                        .child_of_kind(SyntaxKind::NameColon)
                        .and_then(|colon| {
                            colon
                                .child_tokens()
                                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                                .map(|token| token.value_text().to_string())
                        });
                    let written = argument
                        .children()
                        .find(|child| child.kind().is_expression());
                    // `(syntax, location)` names its elements `syntax` and
                    // `location`: where nothing was written, a simple name or
                    // the name after a `.` is taken as one.
                    let name = name.or_else(|| written.as_ref().and_then(inferred_element_name));
                    let value = written.map(|value| self.bind_expression(&value));
                    elements.push(TupleElement {
                        name,
                        ty: value.as_ref().map_or(Type::Error, |value| value.ty.clone()),
                    });
                    values.push(value.unwrap_or_else(|| BoundExpression::error(span)));
                }
                at(
                    BoundExpressionKind::TupleCreation(values),
                    Type::Tuple(elements),
                )
            }
            // `*p` is what the pointer points at, and `&x` is where `x` is.
            SyntaxKind::PointerIndirectionExpression => {
                let Some(operand) = node
                    .children()
                    .find(|child| child.kind().is_expression())
                    .map(|operand| self.bind_expression(&operand))
                else {
                    return BoundExpression::error(span);
                };
                let ty = match &operand.ty {
                    Type::Pointer(element) => (**element).clone(),
                    _ => Type::Error,
                };
                at(
                    BoundExpressionKind::Dereference {
                        operand: Box::new(operand),
                    },
                    ty,
                )
            }
            SyntaxKind::AddressOfExpression => {
                let Some(operand) = node
                    .children()
                    .find(|child| child.kind().is_expression())
                    .map(|operand| self.bind_expression(&operand))
                else {
                    return BoundExpression::error(span);
                };
                let ty = if operand.ty.is_error() {
                    Type::Error
                } else {
                    Type::Pointer(Box::new(operand.ty.clone()))
                };
                at(
                    BoundExpressionKind::AddressOf {
                        operand: Box::new(operand),
                    },
                    ty,
                )
            }
            SyntaxKind::StackAllocArrayCreationExpression
            | SyntaxKind::ImplicitStackAllocArrayCreationExpression => self.bind_stackalloc(node),
            SyntaxKind::AwaitExpression => self.bind_await(node),
            SyntaxKind::MemberBindingExpression => {
                let Some(right) = node.children().next() else {
                    return BoundExpression::error(span);
                };
                let Some(name) = identifier_text(&right) else {
                    return BoundExpression::error(span);
                };
                let receiver = self.accessed_value(span);
                self.member_on(receiver, &right, &name, span)
            }
            // `a?[i]` indexes the receiver of the `?.`, which is already bound
            // and waiting, the way `a?.M` reads a member of it.
            SyntaxKind::ElementBindingExpression => {
                let receiver = self.accessed_value(span);
                let indices = node
                    .child_of_kind(SyntaxKind::BracketedArgumentList)
                    .map(|list| self.bind_argument_list(&list))
                    .unwrap_or_default();
                self.element_access_on(receiver, indices, node.kind(), span)
            }
            SyntaxKind::InvocationExpression => self.bind_invocation(node),
            SyntaxKind::ObjectCreationExpression => self.bind_object_creation(node, None),
            // `new(a, b)` says everything but what is being made, and that
            // comes from whatever it is being given to.
            SyntaxKind::ImplicitObjectCreationExpression => {
                // Its arguments are bound once that is known, but an `out
                // var x` among them is in scope from here on: `M(new(out var
                // x), x)` reads it before the creation is bound. Declared
                // now, the binding later finds the same local.
                for declaration in node.descendants().filter(|inner| {
                    inner.kind() == SyntaxKind::DeclarationExpression
                        && inner
                            .parent()
                            .is_some_and(|argument| argument.kind() == SyntaxKind::Argument)
                }) {
                    self.bind_out_declaration(&declaration);
                }
                // So is a pattern variable: `M(new(a is var x), x)`. Its
                // value does not depend on what the creation is given to, so
                // it is bound here and again then, to the same local.
                for pattern in node.descendants().filter(|inner| {
                    inner.kind() == SyntaxKind::IsPatternExpression
                        && !inner
                            .ancestors()
                            .take_while(|outer| outer.span() != node.span())
                            .any(|outer| {
                                matches!(
                                    outer.kind(),
                                    SyntaxKind::ParenthesizedLambdaExpression
                                        | SyntaxKind::SimpleLambdaExpression
                                        | SyntaxKind::AnonymousMethodExpression
                                )
                            })
                }) {
                    let floor = self.body.diagnostics.len();
                    self.bind_expression(&pattern);
                    self.body.diagnostics.truncate(floor);
                }
                at(BoundExpressionKind::UnboundCreation(span), Type::Error)
            }
            SyntaxKind::ArrayCreationExpression
            | SyntaxKind::ImplicitArrayCreationExpression
            // `int[] a = { 1, 2 };` writes no `new`, and means the same as if
            // it had.
            | SyntaxKind::ArrayInitializerExpression => self.bind_array_creation(node),
            SyntaxKind::CastExpression => {
                let mut children = node.children();
                let ty = children
                    .next()
                    .map_or(Type::Error, |target| self.resolve(&target));
                match children.next() {
                    Some(operand) => {
                        let value = self.bind_expression(&operand);
                        // `(C)(() => x)` reaches an `op_Explicit` taking a
                        // delegate the lambda becomes.
                        if let Some((operator, parameter)) =
                            self.function_conversion_operator(&value, &ty, true)
                        {
                            let converted = self.convert(value, &parameter);
                            return self.operator_call(operator, converted, ty);
                        }
                        // A cast of a `dynamic` value is an explicit
                        // conversion the runtime binder makes.
                        if matches!(value.ty, Type::Dynamic)
                            && !matches!(ty, Type::Dynamic | Type::Error)
                            && self.binder.object_type().as_ref() != Some(&ty)
                        {
                            return Self::dynamic_conversion(value, &ty, true);
                        }
                        // §10.5.3: a cast may use an `op_Explicit`, and
                        // nothing else may. `(ExtendedSpecialType)i` is a
                        // call to one and `i` on its own is an `int`.
                        let constant = self.binder.folded(&value);
                        let outer = self.cast_span.replace(span);
                        let converted = self.convert_explicitly(value, &ty);
                        self.cast_span = outer;
                        if let Some(constant) = &constant {
                            self.check_constant_cast(constant, &ty, span);
                        }
                        // `((S)v).Increment()` calls the method on a copy: a
                        // cast is a value even where it changes nothing, and
                        // the variable under it is not what it is.
                        let converted = if matches!(
                            converted.kind,
                            BoundExpressionKind::Local(_)
                                | BoundExpressionKind::Parameter(_)
                                | BoundExpressionKind::Field { .. }
                                | BoundExpressionKind::ArrayAccess { .. }
                        ) && !converted.ty.is_error()
                            && !matches!(converted.ty, Type::TypeParameter(_))
                            && !self.binder.held_by_reference(&converted.ty)
                        {
                            let converted_type = converted.ty.clone();
                            BoundExpression::new(
                                BoundExpressionKind::Conversion {
                                    operand: Box::new(converted),
                                    conversion: crate::bound::ConversionKind::Identity,
                                    written: true,
                                },
                                converted_type,
                                span,
                            )
                        } else {
                            converted
                        };
                        self.fold_decimal(BoundExpression::new(converted.kind, ty, span))
                    }
                    None => BoundExpression::error(span),
                }
            }
            SyntaxKind::ElementAccessExpression => self.bind_element_access(node),
            // `^k` is `new Index(k, fromEnd: true)`, and `a..b` is a `Range`
            // of two of those. Both are ordinary values; what makes them look
            // like syntax is only that they are usually written inside `[]`.
            SyntaxKind::IndexExpression => self.bind_from_end(node),
            SyntaxKind::RangeExpression => self.bind_range(node),
            SyntaxKind::ConditionalExpression => self.bind_conditional(node, None),
            SyntaxKind::AnonymousObjectCreationExpression => self.bind_anonymous_object(node),
            // `checked(e)`, `unchecked(e)` and `e!` are the expression inside
            // them. The first two change how arithmetic overflows, which this
            // does not do either way; the third says something to a nullable
            // analysis there is none of.
            SyntaxKind::CheckedExpression
            | SyntaxKind::UncheckedExpression
            | SyntaxKind::SuppressNullableWarningExpression => {
                if node.kind() != SyntaxKind::SuppressNullableWarningExpression {
                    self.body
                        .checked_regions
                        .push((span, node.kind() == SyntaxKind::CheckedExpression));
                }
                match node.children().find(|child| child.kind().is_expression()) {
                    Some(inner) => self.bind_expression(&inner),
                    None => BoundExpression::error(span),
                }
            }
            // `sizeof(T)` is how many bytes a `T` takes, which only the
            // runtime knows for anything but the types the language names.
            // `__makeref`, `__refvalue` and `__reftype`: a `TypedReference`
            // made, read as the variable it refers to, and asked its type.
            SyntaxKind::MakeRefExpression => {
                let Some(operand) = node.children().find(|child| child.kind().is_expression())
                else {
                    return BoundExpression::error(span);
                };
                let operand = self.bind_expression(&operand);
                let ty = self.typed_reference();
                at(BoundExpressionKind::MakeRef(Box::new(operand)), ty)
            }
            SyntaxKind::RefValueExpression | SyntaxKind::RefTypeExpression => {
                let Some(operand) = node.children().find(|child| child.kind().is_expression())
                else {
                    return BoundExpression::error(span);
                };
                let operand = self.bind_expression(&operand);
                let reference = self.typed_reference();
                let operand = Box::new(self.convert(operand, &reference));
                if node.kind() == SyntaxKind::RefTypeExpression {
                    let ty = self
                        .binder
                        .compilation()
                        .type_by_metadata_name("System.Type")
                        .map_or(Type::Error, Type::named);
                    return at(BoundExpressionKind::RefType(operand), ty);
                }
                let ty = node
                    .children()
                    .filter(|child| child.kind().is_type_node())
                    .last()
                    .map_or(Type::Error, |target| self.resolve(&target));
                at(BoundExpressionKind::RefValue(operand), ty)
            }
            SyntaxKind::SizeOfExpression => {
                let target = node
                    .children()
                    .next()
                    .map_or(Type::Error, |target| self.resolve(&target));
                at(
                    BoundExpressionKind::SizeOf(target),
                    self.binder
                        .compilation()
                        .special_type(SpecialType::Int32)
                        .map_or(Type::Error, Type::named),
                )
            }
            // `x ?? throw new E()` throws instead of producing a value, so it
            // fits wherever a value was wanted.
            SyntaxKind::ThrowExpression => {
                let thrown = node
                    .children()
                    .find(|child| child.kind().is_expression())
                    .map(|inner| self.bind_thrown(&inner));
                at(
                    BoundExpressionKind::Throw(thrown.map(Box::new)),
                    Type::Error,
                )
            }
            SyntaxKind::TypeOfExpression => {
                let written = node.children().next();
                let mut target = written
                    .as_ref()
                    .map_or(Type::Error, |target| self.resolve(target));
                // `typeof(Nullable<>)` names the generic type itself, with no
                // arguments at all (§12.8.18): not a construction of errors.
                if written.is_some_and(|target| {
                    target
                        .descendants()
                        .any(|part| part.kind() == SyntaxKind::OmittedTypeArgument)
                }) && let Type::Named { symbol, .. } = &target
                {
                    target = Type::named(*symbol);
                }
                at(
                    BoundExpressionKind::TypeOf(target),
                    self.binder
                        .compilation()
                        .type_by_metadata_name("System.Type")
                        .map_or(Type::Error, Type::named),
                )
            }
            // `__arglist(a, b)` is what a call passes a varargs method past
            // its parameters; it has no type, and overload resolution sees it
            // as the `void` a varargs method's extra parameter takes.
            // `__arglist` alone is a varargs method's handle on them.
            SyntaxKind::ArgListExpression => match node.child_of_kind(SyntaxKind::ArgumentList) {
                Some(list) => {
                    let values = self.bind_argument_list(&list);
                    at(BoundExpressionKind::ArgList(values), Type::Void)
                }
                None => {
                    let handle = self
                        .framework_type("System.RuntimeArgumentHandle")
                        .unwrap_or(Type::Error);
                    at(BoundExpressionKind::ArgListHandle, handle)
                }
            },
            SyntaxKind::DefaultExpression | SyntaxKind::DefaultLiteralExpression => {
                let ty = node
                    .children()
                    .next()
                    .map_or(Type::Error, |target| self.resolve(&target));
                at(BoundExpressionKind::Default(ty.clone()), ty)
            }
            kind if binary_operator(kind).is_some() => {
                let bound = self.bind_binary(node);
                self.check_constant_arithmetic(&bound);
                self.fold_decimal(bound)
            }
            kind if compound_operator(kind).is_some() => self.bind_compound_assignment(node),
            SyntaxKind::SimpleAssignmentExpression => self.bind_assignment(node),
            SyntaxKind::UnaryMinusExpression
            | SyntaxKind::UnaryPlusExpression
            | SyntaxKind::BitwiseNotExpression => {
                let operator = match node.kind() {
                    SyntaxKind::UnaryMinusExpression => UnaryOperator::Minus,
                    SyntaxKind::UnaryPlusExpression => UnaryOperator::Plus,
                    _ => UnaryOperator::BitwiseNot,
                };
                match node.children().next() {
                    Some(operand) => {
                        let written = operand.clone();
                        let operand = self.bind_expression(&operand);
                        if matches!(operand.ty, Type::Dynamic) {
                            let dynamic = match operator {
                                UnaryOperator::Minus => DynamicUnary::Minus,
                                UnaryOperator::Plus => DynamicUnary::Plus,
                                _ => DynamicUnary::BitwiseNot,
                            };
                            return self.dynamic_unary(dynamic, operand, span);
                        }
                        // `-2147483648` is an `int` and `-9223372036854775808`
                        // a `long` (§6.4.5.3): the literal alone would not fit
                        // either, and would be a `uint` or `ulong` negated.
                        if operator == UnaryOperator::Minus
                            && written.kind() == SyntaxKind::NumericLiteralExpression
                            && !written.text().to_ascii_lowercase().contains('u')
                        {
                            match operand.kind {
                                BoundExpressionKind::Literal(ConstantValue::UInt32(
                                    0x8000_0000,
                                )) => {
                                    return at(
                                        BoundExpressionKind::Literal(ConstantValue::Int32(
                                            i32::MIN,
                                        )),
                                        self.special(SpecialType::Int32),
                                    );
                                }
                                BoundExpressionKind::Literal(ConstantValue::UInt64(
                                    0x8000_0000_0000_0000,
                                )) => {
                                    return at(
                                        BoundExpressionKind::Literal(ConstantValue::Int64(
                                            i64::MIN,
                                        )),
                                        self.special(SpecialType::Int64),
                                    );
                                }
                                _ => {}
                            }
                        }
                        // `-(decimal.Zero)` and `-1.5m` are constants, folded
                        // as Roslyn folds them: the sign flipped, a zero's
                        // too — `(double)(-0m)` is `-0.0`. Only writing one
                        // out as a `decimal` loses it (see the emitter).
                        if matches!(operator, UnaryOperator::Minus | UnaryOperator::Plus)
                            && self.binder.special_of(&operand.ty) == Some(SpecialType::Decimal)
                            && let Some(crate::bound::SpecialConstant::Decimal {
                                scale,
                                negative,
                                hi,
                                mid,
                                lo,
                            }) = self.binder.decimal_constant(&operand)
                            && let Some(folded) = self.decimal_expression(
                                lo,
                                mid,
                                hi,
                                negative != (operator == UnaryOperator::Minus),
                                scale,
                                span,
                            )
                        {
                            return folded;
                        }
                        // A type can say what `-`, `+` or `~` means on it
                        // (§12.9.1), and then that is what it means.
                        let name = match operator {
                            UnaryOperator::Minus => "op_UnaryNegation",
                            UnaryOperator::Plus => "op_UnaryPlus",
                            _ => "op_OnesComplement",
                        };
                        if let Some(call) = self.user_defined_unary(name, &operand, span) {
                            return call;
                        }
                        // The operand is promoted first (§12.9.2–4): `-b` on a
                        // `byte` is an `int`, and `-u` on a `uint` a `long`,
                        // since no `uint` holds the answer.
                        let promoted = match self.binder.special_of(&operand.ty) {
                            Some(
                                SpecialType::SByte
                                | SpecialType::Byte
                                | SpecialType::Int16
                                | SpecialType::UInt16
                                | SpecialType::Char,
                            ) => Some(SpecialType::Int32),
                            Some(SpecialType::UInt32) if operator == UnaryOperator::Minus => {
                                Some(SpecialType::Int64)
                            }
                            _ => None,
                        };
                        let operand = match promoted {
                            Some(special) => {
                                let target = self.special(special);
                                self.convert(operand, &target)
                            }
                            None => self.predefined_unary_operand(operator, operand),
                        };
                        let ty = operand.ty.clone();
                        let bound = at(
                            BoundExpressionKind::Unary {
                                operator,
                                operand: Box::new(operand),
                            },
                            ty,
                        );
                        // `-int.MinValue` has no `int` to be (CS0220).
                        self.check_constant_arithmetic(&bound);
                        bound
                    }
                    None => BoundExpression::error(span),
                }
            }
            SyntaxKind::PreIncrementExpression
            | SyntaxKind::PreDecrementExpression
            | SyntaxKind::PostIncrementExpression
            | SyntaxKind::PostDecrementExpression => {
                let operator = if matches!(
                    node.kind(),
                    SyntaxKind::PreIncrementExpression | SyntaxKind::PostIncrementExpression
                ) {
                    IncrementOperator::Increment
                } else {
                    IncrementOperator::Decrement
                };
                let prefix = matches!(
                    node.kind(),
                    SyntaxKind::PreIncrementExpression | SyntaxKind::PreDecrementExpression
                );
                match node.children().next() {
                    Some(operand) => {
                        let target = self.bind_expression(&operand);
                        let ty = target.ty.clone();
                        // A type can say what `++` means on it, and then that
                        // is what it means.
                        let name = match operator {
                            IncrementOperator::Increment => "op_Increment",
                            IncrementOperator::Decrement => "op_Decrement",
                        };
                        // On an `S?` the operator of `S` is lifted (§12.4.8).
                        let operand = match self.binder.nullable_underlying(&ty) {
                            Some(inner) => BoundExpression::new(
                                BoundExpressionKind::Default(inner.clone()),
                                inner,
                                span,
                            ),
                            None => target.clone(),
                        };
                        let method = self
                            .user_defined_unary(name, &operand, span)
                            .and_then(|call| match call.kind {
                                BoundExpressionKind::Call { method, .. } => Some(method),
                                _ => None,
                            });
                        if method.is_none()
                            && let Some(lowered) =
                                self.increment_through_conversion(&target, operator, prefix, span)
                        {
                            return lowered;
                        }
                        at(
                            BoundExpressionKind::Increment {
                                target: Box::new(target),
                                operator,
                                prefix,
                                method,
                            },
                            ty,
                        )
                    }
                    None => BoundExpression::error(span),
                }
            }
            SyntaxKind::LogicalNotExpression => {
                // `!` lifts onto a `bool?` like any operator on a value type
                // (§12.4.8): `!maybe` is a `bool?` that is null where `maybe`
                // was.
                let Some(written) = node.children().next() else {
                    return BoundExpression::error(span);
                };
                let mut operand = self.bind_expression(&written);
                if matches!(operand.ty, Type::Dynamic) {
                    return self.dynamic_unary(DynamicUnary::LogicalNot, operand, span);
                }
                if let Some(call) = self.user_defined_unary("op_LogicalNot", &operand, span) {
                    return call;
                }
                let lifted = self
                    .binder
                    .nullable_underlying(&operand.ty)
                    .is_some_and(|inner| self.binder.is_boolean(&inner));
                let ty = if lifted {
                    operand.ty.clone()
                } else {
                    // The predefined `!(bool)` takes an operand an implicit
                    // conversion its type declares makes a `bool` (§12.4.4):
                    // `!animator` on a `UnityEngine.Object` calls its
                    // `operator bool`. `operator true` is no such conversion.
                    let boolean = self.special(SpecialType::Boolean);
                    let converted = if !operand.ty.is_error()
                        && !self.binder.is_boolean(&operand.ty)
                        && operand.ty.symbol().is_some()
                        && self.binder.special_of(&operand.ty).is_none()
                    {
                        self.user_defined_conversion(&operand.ty, &boolean)
                    } else {
                        None
                    };
                    match converted {
                        Some(conversion) => {
                            operand = self.operator_call(conversion, operand, boolean.clone());
                        }
                        None => self.check_condition(&written, &operand.ty.clone()),
                    }
                    boolean
                };
                at(
                    BoundExpressionKind::Unary {
                        operator: UnaryOperator::LogicalNot,
                        operand: Box::new(operand),
                    },
                    ty,
                )
            }
            SyntaxKind::IsExpression => {
                let mut children = node.children();
                let operand = children
                    .next()
                    .map(|operand| self.bind_expression(&operand));
                let Some(written) = children.next() else {
                    return BoundExpression::error(span);
                };
                let Some(operand) = operand else {
                    return BoundExpression::error(span);
                };
                let boolean = self.special(SpecialType::Boolean);
                // `x is Kind.Viable || y` parses as a type test, because a
                // name is a name and `||` is not something a pattern can go
                // on with. What the name means is what tells the two apart:
                // where it is not a type it is a constant, and the whole
                // thing was a pattern all along.
                if !self.names_a_type(&written) {
                    let value = self.bind_expression(&written);
                    let pattern =
                        match self.union_constant_test(&operand.ty.clone(), value, written.span()) {
                            Ok(pattern) => pattern,
                            Err(value) => BoundPattern::new(
                                BoundPatternKind::Constant(*value),
                                written.span(),
                            ),
                        };
                    return at(
                        BoundExpressionKind::IsPattern {
                            operand: Box::new(operand),
                            pattern: Box::new(pattern),
                        },
                        boolean,
                    );
                }
                let target = self.resolve(&written);
                // `Increment() is object` on a `void` call is always false
                // (CS0184), and the call still runs.
                if matches!(operand.ty, Type::Void) {
                    let never = BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Boolean(false)),
                        boolean.clone(),
                        span,
                    );
                    return at(BoundExpressionKind::Sequence(vec![operand, never]), boolean);
                }
                // On a union, `u is int` asks what it holds (C# 15).
                if let Some(pattern) = self.union_type_test(&operand.ty.clone(), &target, written.span())
                {
                    return at(
                        BoundExpressionKind::IsPattern {
                            operand: Box::new(operand),
                            pattern: Box::new(pattern),
                        },
                        boolean,
                    );
                }
                at(
                    BoundExpressionKind::TypeTest {
                        operand: Box::new(operand),
                        target,
                    },
                    boolean,
                )
            }
            SyntaxKind::IsPatternExpression => {
                let mut children = node.children();
                let operand = children
                    .next()
                    .map(|operand| self.bind_expression(&operand));
                let Some(operand) = operand else {
                    return BoundExpression::error(span);
                };
                let pattern = children
                    .next()
                    .map(|pattern| self.bind_pattern(&pattern, &operand.ty.clone()));
                let Some(pattern) = pattern else {
                    return BoundExpression::error(span);
                };
                at(
                    BoundExpressionKind::IsPattern {
                        operand: Box::new(operand),
                        pattern: Box::new(pattern),
                    },
                    self.special(SpecialType::Boolean),
                )
            }
            SyntaxKind::SwitchExpression => self.bind_switch_expression(node, None),
            SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression => self.bind_lambda(node),
            SyntaxKind::AsExpression => {
                let mut children = node.children();
                let operand = children
                    .next()
                    .map(|operand| self.bind_expression(&operand));
                let target = children
                    .next()
                    .map_or(Type::Error, |target| self.resolve(&target));
                match operand {
                    Some(operand) => at(
                        BoundExpressionKind::TryCast {
                            operand: Box::new(operand),
                            target: target.clone(),
                        },
                        target,
                    ),
                    None => BoundExpression::error(span),
                }
            }
            _ => {
                // Queries, switch expressions and the rest still have their
                // sub-expressions bound, so the names inside them resolve even
                // though the whole has no type yet.
                for child in node.children() {
                    if child.kind().is_expression() {
                        self.bind_expression(&child);
                    } else if child.kind() == SyntaxKind::Block {
                        self.bind_block(&child);
                    } else if child.kind().is_statement_node() {
                        self.bind_statement(&child);
                    } else {
                        self.bind_arguments_of(&child);
                    }
                }
                at(BoundExpressionKind::Unsupported(node.kind()), Type::Error)
            }
        }
    }

    fn bind_arguments_of(&mut self, node: &SyntaxNode) {
        for child in node.children() {
            if child.kind().is_expression() {
                self.bind_expression(&child);
            } else if child.kind() == SyntaxKind::Block {
                self.bind_block(&child);
            } else {
                self.bind_arguments_of(&child);
            }
        }
    }

    fn bind_literal(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(token) = node.child_tokens().next() else {
            return BoundExpression::error(span);
        };
        // `"abc"u8` is a `ReadOnlySpan<byte>` over the UTF-8 bytes (§12.8.3):
        // made here over an array of them.
        if matches!(
            token.kind(),
            SyntaxKind::Utf8StringLiteralToken
                | SyntaxKind::Utf8SingleLineRawStringLiteralToken
                | SyntaxKind::Utf8MultiLineRawStringLiteralToken
        ) && let TokenValue::String(text) = token.value()
        {
            let text = text.to_string();
            return self.utf8_span(&text, span);
        }
        let (value, special) = match token.value() {
            TokenValue::Int32(value) => (ConstantValue::Int32(*value), SpecialType::Int32),
            TokenValue::UInt32(value) => (ConstantValue::UInt32(*value), SpecialType::UInt32),
            TokenValue::Int64(value) => (ConstantValue::Int64(*value), SpecialType::Int64),
            TokenValue::UInt64(value) => (ConstantValue::UInt64(*value), SpecialType::UInt64),
            TokenValue::Single(value) => (ConstantValue::Single(*value), SpecialType::Single),
            TokenValue::Double(value) => (ConstantValue::Double(*value), SpecialType::Double),
            // A decimal constant is not a CLR primitive: it has no literal
            // form at all, and a compiler writes one as a call to the
            // constructor that takes its parts. `1.5m` is `new decimal(15, 0,
            // 0, false, 1)`, which is what C# emits too.
            TokenValue::Decimal(text) => {
                let decimal = self.special(SpecialType::Decimal);
                let Some((lo, mid, high, negative, scale)) = decimal_parts(text) else {
                    return BoundExpression::new(
                        BoundExpressionKind::Unsupported(node.kind()),
                        decimal,
                        span,
                    );
                };
                return self
                    .decimal_expression(lo, mid, high, negative, scale, span)
                    .unwrap_or_else(|| {
                        BoundExpression::new(
                            BoundExpressionKind::Unsupported(node.kind()),
                            decimal,
                            span,
                        )
                    });
            }
            // `'\uD800'` is a lone surrogate, which a Rust `char` cannot
            // hold: the token's value is a replacement character, and the
            // constant is the number its text spells, as `constant.rs` keeps
            // a surrogate `char`.
            TokenValue::Char(char::REPLACEMENT_CHARACTER)
                if let Some(unit) = lone_surrogate(token.text()) =>
            {
                (ConstantValue::Int32(i32::from(unit)), SpecialType::Char)
            }
            TokenValue::Char(value) => (ConstantValue::Char(*value), SpecialType::Char),
            TokenValue::String(value) => (
                ConstantValue::String(value.to_string()),
                SpecialType::String,
            ),
            TokenValue::None => return BoundExpression::error(span),
        };
        BoundExpression::new(
            BoundExpressionKind::Literal(value),
            self.special(special),
            span,
        )
    }

    /// `await e`, whose value is what waiting for `e` produces.
    ///
    /// C# finds that by pattern: `e.GetAwaiter()` gives an awaiter, and its
    /// `GetResult()` gives the value. Nothing about the type is special —
    /// which is why `await` works on anything shaped that way — and nothing
    /// here makes the waiting happen.
    fn bind_await(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(operand) = node.children().find(|child| child.kind().is_expression()) else {
            return BoundExpression::error(span);
        };
        let operand = self.bind_expression(&operand);
        self.check_await_context(node);
        let operand_type = operand.ty.clone();
        let awaited = self.awaited(operand, span);
        // Nothing to wait on: `await` of a `void` call is CS4008, of
        // anything else without a `GetAwaiter`, its own or an extension,
        // CS1061 as for the call `await` makes.
        if let BoundExpressionKind::Await { awaiting: None, .. } = &awaited.kind
            && !operand_type.is_error()
            && !matches!(operand_type, Type::Dynamic | Type::Null)
        {
            if matches!(operand_type, Type::Void) {
                self.report(ErrorCode::ErrBadAwaitArgVoidCall, span, &[]);
            } else {
                let shown = self.display(&operand_type);
                self.report(
                    ErrorCode::ErrNoSuchMemberOrExtension,
                    span,
                    &[&shown, "GetAwaiter"],
                );
            }
        }
        awaited
    }

    /// CS4014: a call that gives back something to wait for, made as a
    /// statement in an `async` function, which goes on without it — UniTask's
    /// `handle.WithCancellation(token);` as much as a `Task`. Outside one,
    /// only a call of a method declared `async` is: `StartLogin(token);` from
    /// a button handler. Reported over the whole call, as Roslyn does.
    pub(super) fn check_unawaited(&mut self, expression: &SyntaxNode, value: &BoundExpression) {
        let BoundExpressionKind::Call { method, .. } = &value.kind else {
            return;
        };
        if expression.kind() != SyntaxKind::InvocationExpression
            || value.ty.is_error()
            || matches!(value.ty, Type::Void | Type::Dynamic)
        {
            return;
        }
        // `async` is known of a method of the assembly being compiled only:
        // UniTask's `ContinueWith`, built into an assembly of its own, is
        // just a method that gives back a `UniTask` to its callers.
        let compilation = self.binder.compilation();
        let callee = compilation.symbols().get(*method);
        let calls_async = callee.modifiers.contains(Modifiers::ASYNC)
            && callee.locations.first().is_some_and(|location| {
                compilation.tree_assembly(location.tree) == compilation.tree_assembly(self.tree)
            });
        let in_async = expression
            .ancestors()
            .find(|ancestor| {
                matches!(
                    ancestor.kind(),
                    SyntaxKind::SimpleLambdaExpression
                        | SyntaxKind::ParenthesizedLambdaExpression
                        | SyntaxKind::AnonymousMethodExpression
                        | SyntaxKind::LocalFunctionStatement
                        | SyntaxKind::MethodDeclaration
                        | SyntaxKind::ConstructorDeclaration
                        | SyntaxKind::PropertyDeclaration
                        | SyntaxKind::AccessorList
                        | SyntaxKind::GlobalStatement
                )
            })
            .is_some_and(|function| {
                function
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::AsyncKeyword)
            });
        if !in_async && !calls_async {
            return;
        }
        let floor = self.speculation_floor();
        let awaitable = self.awaiting(&value.ty).is_some()
            || self.awaiting_by_extension(value, value.span).is_some();
        self.unwind_speculation(floor);
        if awaitable {
            self.report(ErrorCode::WrnUnobservedAwaitableExpression, value.span, &[]);
        }
    }

    /// CS4032, CS4033 and CS4034: an `await` in a method or lambda that is
    /// not `async`. The function it belongs to is the nearest one around it;
    /// top-level statements may always wait.
    fn check_await_context(&mut self, node: &SyntaxNode) {
        let Some(function) = node.ancestors().find(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
                    | SyntaxKind::LocalFunctionStatement
                    | SyntaxKind::MethodDeclaration
                    | SyntaxKind::GlobalStatement
                    | SyntaxKind::QueryExpression
                    | SyntaxKind::LockStatement
                    | SyntaxKind::ConstructorDeclaration
                    | SyntaxKind::DestructorDeclaration
                    | SyntaxKind::OperatorDeclaration
                    | SyntaxKind::ConversionOperatorDeclaration
                    | SyntaxKind::AccessorList
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::IndexerDeclaration
                    | SyntaxKind::FieldDeclaration
                    | SyntaxKind::EventFieldDeclaration
                    | SyntaxKind::Parameter
                    | SyntaxKind::Attribute
            )
        }) else {
            return;
        };
        let is_async = function
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::AsyncKeyword);
        if is_async {
            return;
        }
        let span = node.span();
        match function.kind() {
            SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression => {
                self.report(ErrorCode::ErrBadAwaitWithoutAsyncLambda, span, &[]);
            }
            SyntaxKind::LocalFunctionStatement | SyntaxKind::MethodDeclaration => {
                let Some(returns) = function
                    .children()
                    .find(|child| child.kind().is_type_node())
                else {
                    return;
                };
                let ty = self
                    .binder
                    .resolve_type(&returns, &self.context, &mut Diagnostics::new());
                match ty {
                    Type::Error => {}
                    Type::Void => {
                        self.report(ErrorCode::ErrBadAwaitWithoutVoidAsyncMethod, span, &[])
                    }
                    ty => {
                        let shown = self.display(&ty);
                        self.report(ErrorCode::ErrBadAwaitWithoutAsyncMethod, span, &[&shown]);
                    }
                }
            }
            // Top-level statements wait as they please; the rest have codes
            // of their own that this does not report.
            _ => {}
        }
    }

    /// `await operand`, for an operand already bound.
    ///
    /// A `dynamic` operand is waited on through the runtime binder, which
    /// finds its `GetAwaiter()` and the awaiter's `IsCompleted` and
    /// `GetResult()` as it runs; what it gives is `dynamic` too (§12.9.8.2).
    pub(super) fn awaited(&mut self, operand: BoundExpression, span: TextSpan) -> BoundExpression {
        if matches!(operand.ty, Type::Dynamic) {
            return BoundExpression::new(
                BoundExpressionKind::Await {
                    operand: Box::new(operand),
                    awaiting: None,
                },
                Type::Dynamic,
                span,
            );
        }
        let awaiting = self
            .awaiting(&operand.ty)
            .or_else(|| self.awaiting_by_extension(&operand, span));
        let ty = awaiting.as_ref().map_or(Type::Error, |awaiting| {
            self.member_type(awaiting.get_result, &awaiting.get_result_type)
        });
        BoundExpression::new(
            BoundExpressionKind::Await {
                operand: Box::new(operand),
                awaiting: awaiting.map(Box::new),
            },
            ty,
            span,
        )
    }

    /// The members `await` on this type goes through, where it has them.
    fn awaiting(&mut self, ty: &Type) -> Option<BoundAwaiting> {
        let (get_awaiter, get_awaiter_type) =
            self.member_through(ty, "GetAwaiter", SymbolKind::Method)?;
        let awaiter = self.member_type(get_awaiter, &get_awaiter_type);
        let (is_completed, is_completed_type) =
            self.member_through(&awaiter, "IsCompleted", SymbolKind::Property)?;
        let (get_result, get_result_type) =
            self.member_through(&awaiter, "GetResult", SymbolKind::Method)?;
        Some(BoundAwaiting {
            get_awaiter,
            get_awaiter_type,
            awaiter,
            is_completed,
            is_completed_type,
            get_result,
            get_result_type,
            extension: None,
        })
    }

    /// The same where `GetAwaiter` is an extension method in scope: the
    /// type has none of its own, and `operand.GetAwaiter()` still binds
    /// (§12.9.8.2) — `await` on an interface's struct boxes it on the way.
    fn awaiting_by_extension(
        &mut self,
        operand: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundAwaiting> {
        if operand.ty.is_error() || matches!(operand.ty, Type::Dynamic | Type::Void) {
            return None;
        }
        let call = self.extension_call_at("GetAwaiter", operand.clone(), span)?;
        let BoundExpressionKind::Call {
            method,
            type_arguments,
            arguments,
            ..
        } = call.kind
        else {
            return None;
        };
        let this = arguments.first()?.ty.clone();
        let awaiter = call.ty;
        let (is_completed, is_completed_type) =
            self.member_through(&awaiter, "IsCompleted", SymbolKind::Property)?;
        let (get_result, get_result_type) =
            self.member_through(&awaiter, "GetResult", SymbolKind::Method)?;
        Some(BoundAwaiting {
            get_awaiter: method,
            get_awaiter_type: Type::Void,
            awaiter,
            is_completed,
            is_completed_type,
            get_result,
            get_result_type,
            extension: Some((type_arguments, this)),
        })
    }

    /// `new ReadOnlySpan<byte>(new byte[] { …, 0 }, 0, length)` over a
    /// string's UTF-8 bytes, which is what a `u8` literal is. The array ends
    /// in a zero the span leaves out, as Roslyn's does, so that what it
    /// points at can be handed to native code as a C string; a
    /// `ReadOnlySpan<T>` without that constructor gets the bytes alone.
    pub(super) fn utf8_span(&mut self, text: &str, span: TextSpan) -> BoundExpression {
        let byte = self.special(SpecialType::Byte);
        let int = self.special(SpecialType::Int32);
        let Some(span_symbol) = self
            .binder
            .compilation()
            .type_by_metadata_name("System.ReadOnlySpan`1")
        else {
            return BoundExpression::error(span);
        };
        let span_type = Type::Named {
            symbol: span_symbol,
            type_arguments: vec![byte.clone()],
        };
        let array_type = Type::Array {
            element: Box::new(byte.clone()),
            rank: 1,
        };
        let sliced = {
            let symbols = self.binder.compilation().symbols();
            symbols
                .lookup(span_symbol, ".ctor")
                .iter()
                .copied()
                .find(|candidate| {
                    symbols.get(*candidate).as_method().is_some_and(|detail| {
                        let parameters: Vec<Type> = detail
                            .parameters
                            .iter()
                            .map(|parameter| self.member_type(*parameter, &span_type))
                            .collect();
                        parameters == [array_type.clone(), int.clone(), int.clone()]
                    })
                })
        };
        let terminated: Vec<u8> = match sliced {
            Some(_) => text.bytes().chain(std::iter::once(0)).collect(),
            None => text.bytes().collect(),
        };
        let elements: Vec<BoundExpression> = terminated
            .iter()
            .map(|value| {
                let literal = BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Int32(i32::from(*value))),
                    int.clone(),
                    span,
                );
                self.convert(literal, &byte)
            })
            .collect();
        let array = BoundExpression::new(
            BoundExpressionKind::ArrayCreation {
                element: byte,
                lengths: Vec::new(),
                elements,
            },
            array_type.clone(),
            span,
        );
        if let Some(constructor) = sliced {
            let number = |value: usize| {
                BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Int32(value as i32)),
                    int.clone(),
                    span,
                )
            };
            return BoundExpression::new(
                BoundExpressionKind::ObjectCreation {
                    constructor: Some(constructor),
                    arguments: vec![array, number(0), number(text.len())],
                    initializers: Vec::new(),
                },
                span_type,
                span,
            );
        }
        let Some(constructor) = self.enumerable_constructor(&span_type, &array_type) else {
            return BoundExpression::error(span);
        };
        BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor: Some(constructor),
                arguments: vec![array],
                initializers: Vec::new(),
            },
            span_type,
            span,
        )
    }
}

/// The name a tuple element takes from the expression that fills it.
///
/// §12.8.6: a simple name gives its own, a member access gives the name after
/// the dot, and anything else gives none.
pub(super) fn inferred_element_name(value: &SyntaxNode) -> Option<String> {
    match value.kind() {
        SyntaxKind::IdentifierName => identifier_text(value),
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression => {
            value.children().last().and_then(|right| {
                (right.kind() == SyntaxKind::IdentifierName)
                    .then(|| identifier_text(&right))
                    .flatten()
            })
        }
        _ => None,
    }
}

/// A decimal literal taken apart the way its constructor wants it.
///
/// A `decimal` is a 96-bit whole number, a sign and a scale — the number of
/// digits that belong after the point (§II.  of the runtime's own docs, and
/// `decimal(int, int, int, bool, byte)`). `1.5m` is 15 with a scale of one.
/// `None` where the digits do not fit in 96 bits even after the scale has
/// been spent, which is a literal no `decimal` can hold.
pub(super) fn decimal_parts(text: &str) -> Option<(u32, u32, u32, bool, u8)> {
    const LIMIT: u128 = (1u128 << 96) - 1;
    let text = text.trim_end_matches(['m', 'M']).replace('_', "");
    let (digits, exponent) = match text.find(['e', 'E']) {
        Some(at) => (&text[..at], text[at + 1..].parse::<i32>().ok()?),
        None => (&text[..], 0),
    };
    let (whole, fraction) = match digits.find('.') {
        Some(at) => (&digits[..at], &digits[at + 1..]),
        None => (digits, ""),
    };
    // The digits as written, however many there are: a literal may carry
    // more than any `decimal` holds, and what it cannot hold is rounded
    // away — to the nearest, and to even between two — after the digits
    // that are kept, not digit by digit.
    let mut digits: Vec<u8> = Vec::new();
    for digit in whole.chars().chain(fraction.chars()) {
        let value = u8::try_from(digit.to_digit(10)?).ok()?;
        if digits.is_empty() && value == 0 {
            continue;
        }
        digits.push(value);
    }
    let mut scale = i64::from(fraction.len() as i32) - i64::from(exponent);
    // The zeros an exponent stands for are counted, not written out one at a
    // time: `E-2859354M` was a million inserts at the front, and an exponent
    // near `i32::MAX` would be gigabytes of zeros (found by fuzzing,
    // `examples/fuzz.rs` in rustlyn-ide).
    //
    // A negative scale is digits the literal wrote as an exponent, which the
    // whole number has to carry instead. Past 29 digits no `decimal` holds
    // it: the first digit is not a zero.
    if scale < 0 {
        if !digits.is_empty() {
            if digits.len() as i64 - scale > 29 {
                return None;
            }
            digits.extend(std::iter::repeat_n(0, scale.unsigned_abs() as usize));
        }
        scale = 0;
    }
    // A value too small for 28 places still rounds at the 28th: the zeros
    // in front of its first digit are counted in. With two or more of them
    // the first digit is past the one that rounds, and the value is zero at
    // the 28th place; with one, that digit is the one that rounds.
    if !digits.is_empty() && scale - 28 > digits.len() as i64 {
        return Some((0, 0, 0, false, 28));
    }
    if !digits.is_empty() && scale - 28 == digits.len() as i64 {
        digits.insert(0, 0);
    }
    let value_of = |digits: &[u8]| -> Option<u128> {
        digits.iter().try_fold(0u128, |sum, digit| {
            sum.checked_mul(10)?.checked_add(u128::from(*digit))
        })
    };
    // 28 is as many digits after the point as a `decimal` has room for, and
    // 96 bits is as much number.
    let mut kept = digits.len();
    while kept > 0
        && scale > 0
        && (scale > 28 || value_of(&digits[..kept]).is_none_or(|value| value > LIMIT))
    {
        kept -= 1;
        scale -= 1;
    }
    let mut mantissa = value_of(&digits[..kept])?;
    if let Some(&first) = digits.get(kept) {
        let sticky = digits[kept + 1..].iter().any(|digit| *digit != 0);
        if first > 5 || (first == 5 && (sticky || mantissa % 2 == 1)) {
            mantissa += 1;
            if mantissa > LIMIT && scale > 0 {
                mantissa = mantissa.div_ceil(10);
                scale -= 1;
            }
        }
    }
    // A zero with more places than a `decimal` has keeps all it can:
    // `0E-100M` is zero at the 28th place.
    if mantissa == 0 && scale > 28 {
        scale = 28;
    }
    if mantissa > LIMIT || scale > 28 {
        return None;
    }
    Some((
        mantissa as u32,
        (mantissa >> 32) as u32,
        (mantissa >> 64) as u32,
        false,
        scale as u8,
    ))
}

/// The token that names what an expression refers to: `C` in `a.b.C`, in
/// `a.b.C()`, in `new N.C()` and in `x += C`.
fn name_token_span(node: &SyntaxNode) -> Option<TextSpan> {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| token.span()),
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName
        | SyntaxKind::MemberBindingExpression => name_token_span(&node.children().last()?),
        SyntaxKind::InvocationExpression
        | SyntaxKind::AddAssignmentExpression
        | SyntaxKind::SubtractAssignmentExpression => name_token_span(&node.children().next()?),
        SyntaxKind::ObjectCreationExpression => node
            .children()
            .find(|child| child.kind().is_type_node())
            .and_then(|ty| name_token_span(&ty)),
        _ => None,
    }
}

/// What a conversion out of a `decimal` converts: the operand of a
/// `Conversion`, or the argument of the `op_Explicit` (or `op_Implicit`)
/// it was bound to.
fn decimal_conversion_operand<'e>(
    symbols: &crate::symbol::Symbols,
    expression: &'e BoundExpression,
) -> Option<&'e BoundExpression> {
    match &expression.kind {
        BoundExpressionKind::Conversion { operand, .. } => Some(operand),
        BoundExpressionKind::Call {
            method, arguments, ..
        } if matches!(
            symbols.get(*method).name.as_str(),
            "op_Explicit" | "op_Implicit"
        ) =>
        {
            match &arguments[..] {
                [only] => Some(only),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The constant of an integer type a whole number is, where it fits.
fn integer_constant(special: SpecialType, whole: i128) -> Option<ConstantValue> {
    Some(match special {
        SpecialType::SByte => ConstantValue::Int32(i32::from(i8::try_from(whole).ok()?)),
        SpecialType::Byte => ConstantValue::Int32(i32::from(u8::try_from(whole).ok()?)),
        SpecialType::Int16 => ConstantValue::Int32(i32::from(i16::try_from(whole).ok()?)),
        SpecialType::UInt16 => ConstantValue::Int32(i32::from(u16::try_from(whole).ok()?)),
        SpecialType::Char => {
            let unit = u16::try_from(whole).ok()?;
            // A surrogate, which a Rust `char` cannot hold, stays its number.
            char::from_u32(u32::from(unit))
                .map_or(ConstantValue::Int32(i32::from(unit)), ConstantValue::Char)
        }
        SpecialType::Int32 => ConstantValue::Int32(i32::try_from(whole).ok()?),
        SpecialType::UInt32 => ConstantValue::UInt32(u32::try_from(whole).ok()?),
        SpecialType::Int64 => ConstantValue::Int64(i64::try_from(whole).ok()?),
        SpecialType::UInt64 => ConstantValue::UInt64(u64::try_from(whole).ok()?),
        _ => return None,
    })
}

/// An arithmetic operator on two operands, bound as the operator or as the
/// call of the method a type declares for it: `op_Addition(a, b)`.
fn decimal_arithmetic<'e>(
    symbols: &crate::symbol::Symbols,
    expression: &'e BoundExpression,
) -> Option<(
    crate::conversions::BinaryOperator,
    &'e BoundExpression,
    &'e BoundExpression,
)> {
    use crate::conversions::BinaryOperator;
    match &expression.kind {
        BoundExpressionKind::Binary {
            operator,
            left,
            right,
        } => Some((*operator, left, right)),
        BoundExpressionKind::Call {
            method, arguments, ..
        } => {
            let operator = match symbols.get(*method).name.as_str() {
                "op_Addition" => BinaryOperator::Add,
                "op_Subtraction" => BinaryOperator::Subtract,
                "op_Multiply" => BinaryOperator::Multiply,
                "op_Division" => BinaryOperator::Divide,
                "op_Modulus" => BinaryOperator::Modulo,
                "op_Equality" => BinaryOperator::Equality,
                "op_Inequality" => BinaryOperator::Inequality,
                "op_LessThan" => BinaryOperator::LessThan,
                "op_LessThanOrEqual" => BinaryOperator::LessThanOrEqual,
                "op_GreaterThan" => BinaryOperator::GreaterThan,
                "op_GreaterThanOrEqual" => BinaryOperator::GreaterThanOrEqual,
                _ => return None,
            };
            match &arguments[..] {
                [left, right] => Some((operator, left, right)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The surrogate a character literal such as `'\uD800'` or `'\xDFFF'`
/// spells, if it spells one.
fn lone_surrogate(text: &str) -> Option<u16> {
    let inner = text.strip_prefix('\'')?.strip_suffix('\'')?;
    let digits = inner
        .strip_prefix("\\u")
        .or_else(|| inner.strip_prefix("\\x"))?;
    let unit = u16::from_str_radix(digits, 16).ok()?;
    (0xD800..=0xDFFF).contains(&unit).then_some(unit)
}
