//! In-place operators (C# 14): `x += y`, `++x` and `x++` where the type of
//! `x` declares an instance operator that changes the variable itself.

use rustlyn_syntax::SyntaxNode;
use rustlyn_text::TextSpan;

use super::{BodyBinder, Resolved};
use crate::binder::Diagnostics;
use crate::bound::{BoundExpression, BoundExpressionKind, ConstantValue, IncrementOperator};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, RefKind, SymbolId};
use crate::types::Type;

/// The name an instance operator has in metadata for the compound
/// assignment that calls it.
pub(super) const fn compound_name(operator: BinaryOperator) -> Option<&'static str> {
    Some(match operator {
        BinaryOperator::Add => "op_AdditionAssignment",
        BinaryOperator::Subtract => "op_SubtractionAssignment",
        BinaryOperator::Multiply => "op_MultiplicationAssignment",
        BinaryOperator::Divide => "op_DivisionAssignment",
        BinaryOperator::Modulo => "op_ModulusAssignment",
        BinaryOperator::BitwiseAnd => "op_BitwiseAndAssignment",
        BinaryOperator::BitwiseOr => "op_BitwiseOrAssignment",
        BinaryOperator::ExclusiveOr => "op_ExclusiveOrAssignment",
        BinaryOperator::LeftShift => "op_LeftShiftAssignment",
        BinaryOperator::RightShift => "op_RightShiftAssignment",
        BinaryOperator::UnsignedRightShift => "op_UnsignedRightShiftAssignment",
        _ => return None,
    })
}

impl BodyBinder<'_> {
    /// The instance operator `name` that takes `arguments` on a variable of
    /// the type of `receiver`, and the arguments converted to what it takes.
    /// A checked context prefers the checked form where the type declares
    /// one with the same signature.
    fn in_place_operator(
        &mut self,
        name: &str,
        receiver: &BoundExpression,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<(SymbolId, Vec<BoundExpression>)> {
        if !self
            .language_version()
            .at_least(rustlyn_syntax::LanguageVersion::CSharp14)
        {
            return None;
        }
        let ty = receiver.ty.clone();
        let symbol = ty.symbol()?;
        // The numbers, and every other type the language has operators of
        // its own for, declare none of these.
        if self.binder.special_of(&ty).is_some()
            || self.binder.enum_underlying(&ty).is_some()
            || self.binder.native_int(&ty).is_some()
        {
            return None;
        }
        let symbols = self.binder.compilation().symbols();
        let mut candidates: Vec<SymbolId> = self
            .operator_candidates(symbol, name, span)
            .into_iter()
            .filter(|method| {
                let declared = symbols.get(*method);
                let mut sink = Diagnostics::new();
                !declared.modifiers.contains(Modifiers::STATIC)
                    && declared.as_method().is_some_and(|detail| {
                        detail.parameters.len() == arguments.len()
                            && detail.parameters.iter().all(|parameter| {
                                symbols
                                    .get(*parameter)
                                    .as_parameter()
                                    .is_some_and(|detail| {
                                        matches!(detail.ref_kind, RefKind::None | RefKind::In)
                                    })
                            })
                    })
                    && matches!(self.binder.type_of(*method, &mut sink), Type::Void)
            })
            .collect();
        if candidates.is_empty() {
            return None;
        }
        // A checked context lists the checked operators first, wherever they
        // are declared. The most derived type's come first for the ones it
        // hides to be put out: its regular `+=` stands for a base's checked
        // one.
        let container = |method: &SymbolId| symbols.get(*method).container;
        let depth = |method: &SymbolId| {
            candidates
                .iter()
                .filter(|other| {
                    matches!((container(method), container(other)), (Some(derived), Some(base))
                        if derived != base && self.binder.derives_from_definition(derived, base, 0))
                })
                .count()
        };
        let mut keyed: Vec<(usize, SymbolId)> = candidates
            .iter()
            .map(|method| (depth(method), *method))
            .collect();
        keyed.sort_by_key(|(depth, _)| std::cmp::Reverse(*depth));
        candidates = keyed.into_iter().map(|(_, method)| method).collect();
        let types: Vec<Type> = arguments.iter().map(|value| value.ty.clone()).collect();
        let evidence = self.evidence(&arguments);
        let Resolved {
            method,
            substitution,
            ..
        } = self.resolve_call(&candidates, &types, &evidence, &ty, &[])?;
        let arguments = self.convert_arguments(method, arguments, &ty, &substitution, span);
        Some((method, arguments))
    }

    /// Whether `target` is a variable the operator may be called on: the
    /// receiver of a call that changes it has to be the variable itself,
    /// which a property or an indexer of a class does not give.
    fn is_in_place_receiver(&self, target: &BoundExpression) -> bool {
        match &target.kind {
            // `this` of a class cannot be assigned.
            BoundExpressionKind::This => !target
                .ty
                .is_reference_type(self.binder.compilation().symbols()),
            _ => self.is_writable_place(target),
        }
    }

    /// `x op= y` where the type of `x` declares the instance operator: a
    /// call of it on `x`, which is the value of the expression when that is
    /// used.
    pub(super) fn bind_in_place_compound(
        &mut self,
        node: &SyntaxNode,
        operator: BinaryOperator,
        target: &BoundExpression,
        value: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let name = compound_name(operator)?;
        if !self.is_in_place_receiver(target) {
            return None;
        }
        let (method, arguments) =
            self.in_place_operator(name, target, vec![value.clone()], span)?;
        let used = self.result_is_used(node);
        self.in_place_result(used, target, method, arguments, span)
    }

    /// `++x`, `--x`, and `x++` and `x--` whose value is not used, where the
    /// type of `x` declares the instance operator. The value of a postfix
    /// operation is the old one, which only the static operator can give.
    pub(super) fn bind_in_place_increment(
        &mut self,
        node: &SyntaxNode,
        operator: IncrementOperator,
        prefix: bool,
        target: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let used = self.result_is_used(node);
        if !prefix && used {
            return None;
        }
        if !self.is_in_place_receiver(target) {
            return None;
        }
        let name = match operator {
            IncrementOperator::Increment => "op_IncrementAssignment",
            IncrementOperator::Decrement => "op_DecrementAssignment",
        };
        let (method, arguments) = self.in_place_operator(name, target, Vec::new(), span)?;
        self.in_place_result(used, target, method, arguments, span)
    }

    /// The call of an instance operator on `target`, and what the expression
    /// is when its value is used: the variable afterwards. A class is
    /// changed through the reference read before the arguments run; a struct
    /// is copied before they do, changed, and stored back, which is what
    /// keeps the arguments from seeing or undoing half of the change.
    fn in_place_result(
        &mut self,
        used: bool,
        target: &BoundExpression,
        method: SymbolId,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let ty = target.ty.clone();
        // Called as any method of an object is, which is what makes a null
        // receiver throw here and not inside the operator.
        let virtual_call = true;
        let call = |receiver: BoundExpression, arguments: Vec<BoundExpression>| {
            BoundExpression::new(
                BoundExpressionKind::Call {
                    receiver: Some(Box::new(receiver)),
                    method,
                    type_arguments: Vec::new(),
                    arguments,
                    virtual_call,
                },
                Type::Void,
                span,
            )
        };
        if !used {
            return Some(call(target.clone(), arguments));
        }
        let symbols = self.binder.compilation().symbols();
        let local = |this: &Self, id| {
            let _ = this;
            BoundExpression::new(BoundExpressionKind::Local(id), ty.clone(), span)
        };
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
        if ty.is_reference_type(symbols) {
            let held = self.declare_synthetic_local("target", ty.clone());
            let held = local(self, held);
            return Some(BoundExpression::new(
                BoundExpressionKind::Sequence(vec![
                    assign(held.clone(), target.clone()),
                    call(held.clone(), arguments),
                    held,
                ]),
                ty,
                span,
            ));
        }
        let (mut steps, place) = match self.stable_variable(target) {
            Some(stable) => stable,
            None => self.referenced_variable(target),
        };
        let held = self.declare_synthetic_local("target", ty.clone());
        let held = local(self, held);
        steps.push(assign(held.clone(), place.clone()));
        let either = matches!(&ty, Type::TypeParameter(parameter) if symbols
            .get(*parameter)
            .as_type_parameter()
            .is_some_and(|detail| !detail.value_type));
        if either {
            // A type parameter is stored back only where it is a struct: a
            // class's reference is the one the call changed, and the
            // arguments may have put another in the variable.
            let mut arguments = arguments;
            for argument in &mut arguments {
                let kept = self.declare_synthetic_local("argument", argument.ty.clone());
                let read = BoundExpression::new(
                    BoundExpressionKind::Local(kept),
                    argument.ty.clone(),
                    span,
                );
                let taken = std::mem::replace(argument, read.clone());
                steps.push(assign(read, taken));
            }
            let object = self.special(SpecialType::Object);
            let default =
                BoundExpression::new(BoundExpressionKind::Default(ty.clone()), ty.clone(), span);
            let boxed = self.convert(default, &object);
            let null = BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Null),
                Type::Null,
                span,
            );
            let is_struct = self.bind_binary_on(BinaryOperator::Inequality, boxed, null, span);
            let in_both = call(held.clone(), arguments);
            steps.push(BoundExpression::new(
                BoundExpressionKind::Conditional {
                    condition: Box::new(is_struct),
                    consequence: Box::new(BoundExpression::new(
                        BoundExpressionKind::Sequence(vec![
                            in_both.clone(),
                            assign(place, held.clone()),
                            held.clone(),
                        ]),
                        ty.clone(),
                        span,
                    )),
                    alternative: Box::new(BoundExpression::new(
                        BoundExpressionKind::Sequence(vec![in_both, held.clone()]),
                        ty.clone(),
                        span,
                    )),
                },
                ty.clone(),
                span,
            ));
        } else {
            steps.push(call(held.clone(), arguments));
            steps.push(assign(place, held.clone()));
        }
        steps.push(held);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            ty,
            span,
        ))
    }

    /// A variable read and written more than once, with what locates it —
    /// the object a field is on, an array and its indices — kept in
    /// temporaries: the assignments that fill them, and the variable
    /// reading them. A field of a struct variable is the struct's own.
    fn stable_variable(
        &mut self,
        target: &BoundExpression,
    ) -> Option<(Vec<BoundExpression>, BoundExpression)> {
        let mut prelude = Vec::new();
        let place = self.stable_part(target, &mut prelude)?;
        Some((prelude, place))
    }

    /// A variable a member hands back by reference — a `ref` indexer, a `ref`
    /// property, a call that returns `ref` — held by a `ref` local, so that
    /// the member is called once and the variable read and written where it
    /// was found.
    fn referenced_variable(
        &mut self,
        target: &BoundExpression,
    ) -> (Vec<BoundExpression>, BoundExpression) {
        let (ty, span) = (target.ty.clone(), target.span);
        let held = self.declare_synthetic_local("place", ty.clone());
        if let Some(slot) = self.body.locals.get_mut(held.0 as usize) {
            slot.by_ref = true;
        }
        let read = BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
        let bind = BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind: RefKind::Ref,
                        operand: Box::new(target.clone()),
                    },
                    ty,
                    span,
                )),
            },
            read.ty.clone(),
            span,
        );
        (vec![bind], read)
    }

    /// What locates a variable, held in a temporary unless it is already
    /// nothing but a read of one.
    fn keep_value(
        &mut self,
        value: &BoundExpression,
        prelude: &mut Vec<BoundExpression>,
    ) -> BoundExpression {
        if matches!(
            value.kind,
            BoundExpressionKind::Local(_)
                | BoundExpressionKind::Parameter(_)
                | BoundExpressionKind::This
                | BoundExpressionKind::Base
                | BoundExpressionKind::Literal(_)
                | BoundExpressionKind::TypeExpression(_)
        ) {
            return value.clone();
        }
        let (ty, span) = (value.ty.clone(), value.span);
        let held = self.declare_synthetic_local("place", ty.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
        prelude.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(value.clone()),
            },
            ty,
            span,
        ));
        read
    }

    fn stable_part(
        &mut self,
        place: &BoundExpression,
        prelude: &mut Vec<BoundExpression>,
    ) -> Option<BoundExpression> {
        let symbols = self.binder.compilation().symbols();
        let mut stable = place.clone();
        match &mut stable.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This => {}
            BoundExpressionKind::Field { receiver, .. } => {
                if let Some(held) = receiver {
                    if held.ty.is_reference_type(symbols) {
                        let kept = self.keep_value(held, prelude);
                        **held = kept;
                    } else {
                        let inner = self.stable_part(held, prelude)?;
                        **held = inner;
                    }
                }
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                let kept = self.keep_value(array, prelude);
                **array = kept;
                for index in indices.iter_mut() {
                    let kept = self.keep_value(index, prelude);
                    *index = kept;
                }
            }
            _ => return None,
        }
        Some(stable)
    }
}
