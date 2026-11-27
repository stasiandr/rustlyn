//! The instance operators an extension block (C# 14) gives a type.
//!
//! `extension(ref S s) { public void operator +=(int x) { … } }` changes the
//! variable in place: `s += 1` is a call of the method, which takes the
//! variable by reference where `S` is a struct, and `s++` is one with nothing
//! after the receiver. They come after everything the language and the types
//! themselves offer for the operation, and in each place an extension is in
//! scope from, before the static operator (`+`, `++`) of that place.

use rustlyn_text::TextSpan;

use super::BodyBinder;
use crate::bound::{BoundExpression, BoundExpressionKind, IncrementOperator};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{RefKind, SymbolId, SymbolKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// `target op= value` through an instance operator of an extension block,
    /// where nothing nearer takes the operation: the result is the variable
    /// after the call.
    pub(super) fn extension_compound_assignment(
        &mut self,
        operator: BinaryOperator,
        target: &BoundExpression,
        value: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let name = super::operators::operator_method_name(operator)?;
        let assignment = super::instance_operators::compound_name(operator)?;
        if !self.takes_extension_operator(target) || value.ty.is_error() {
            return None;
        }
        // The types' own operators, and the language's, are asked first: they
        // are on the operand types, or reach them through a conversion.
        if self.operand_has_operator(name, &target.ty, span)
            || self.operand_has_operator(name, &value.ty, span)
            || self
                .binder
                .binary_result(operator, &target.ty, &value.ty)
                .is_some()
            || !self.predefined_conversions_of(&target.ty).is_empty()
            || !self.predefined_conversions_of(&value.ty).is_empty()
        {
            return None;
        }
        let (prelude, place) = self.kept_variable(target)?;
        let (call, level) =
            self.extension_instance_call(assignment, &place, vec![value.clone()], span)?;
        if self
            .static_extension_level(name, &[&target.ty, &value.ty])
            .is_some_and(|nearer| nearer < level)
        {
            return None;
        }
        let stored = place.ty.clone();
        let mut steps = prelude;
        steps.push(call);
        steps.push(place);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            stored,
            span,
        ))
    }

    /// `target++` and `--target` through an instance operator of an
    /// extension block, where nothing nearer takes the operation.
    pub(super) fn extension_instance_increment(
        &mut self,
        operator: IncrementOperator,
        target: &BoundExpression,
        prefix: bool,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let (static_name, name) = match operator {
            IncrementOperator::Increment => ("op_Increment", "op_IncrementAssignment"),
            IncrementOperator::Decrement => ("op_Decrement", "op_DecrementAssignment"),
        };
        if !self.takes_extension_operator(target)
            || self.operand_has_operator(static_name, &target.ty, span)
            || !self.predefined_conversions_of(&target.ty).is_empty()
        {
            return None;
        }
        let (mut steps, place) = self.kept_variable(target)?;
        let (call, level) = self.extension_instance_call(name, &place, Vec::new(), span)?;
        if self
            .static_extension_level(static_name, &[&target.ty])
            .is_some_and(|nearer| nearer < level)
        {
            return None;
        }
        let stored = place.ty.clone();
        if prefix {
            steps.push(call);
            steps.push(place);
        } else {
            // The value of `x++` is what `x` was.
            let old = self.declare_synthetic_local("old", stored.clone());
            let local = BoundExpression::new(BoundExpressionKind::Local(old), stored.clone(), span);
            steps.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(local.clone()),
                    value: Box::new(place),
                },
                stored.clone(),
                span,
            ));
            steps.push(call);
            steps.push(local);
        }
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            stored,
            span,
        ))
    }

    /// The static operators called `name` that the extension blocks in scope
    /// declare. In a checked context (C# 11) the checked form of the
    /// operator is looked up too, and gives way to the regular one only
    /// where there is none of the same signature.
    pub(super) fn extension_operator_candidates(
        &self,
        name: &str,
        span: TextSpan,
    ) -> Vec<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let methods = |name: &str| -> Vec<SymbolId> {
            self.binder
                .extension_members_in_scope(&self.context, name)
                .into_iter()
                .filter(|candidate| {
                    symbols
                        .get(*candidate)
                        .as_method()
                        .is_some_and(|detail| !detail.takes_receiver)
                })
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
        let signature = |method: SymbolId| {
            let mut sink = crate::binder::Diagnostics::new();
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
            (symbols.get(method).container, parameters)
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

    /// The static operator of an extension block (C# 14) that `arguments` ask
    /// for, with how far out the place is that brings it into view: the
    /// nearest place that has an operator taking them decides. A block
    /// reaches an operand whose type converts to the one it extends.
    pub(super) fn resolve_extension_operator(
        &mut self,
        name: &str,
        arguments: &[BoundExpression],
        span: TextSpan,
    ) -> Option<(super::Resolved, usize, Vec<BoundExpression>)> {
        let symbols = self.binder.compilation().symbols();
        let mut by_level: Vec<(usize, Vec<SymbolId>)> = Vec::new();
        for candidate in self.extension_operator_candidates(name, span) {
            let Some(detail) = symbols.get(candidate).as_method() else {
                continue;
            };
            let Some(extended) = detail.extended else {
                continue;
            };
            let generics = self.block_generics(&detail.type_parameters);
            let reaches = arguments.iter().any(|argument| {
                // A block may extend `S?` itself, and an operand that is one
                // reaches the block of `S` as well.
                self.static_extension_fits_with(extended, &argument.ty, &generics)
                    || self
                        .binder
                        .nullable_underlying(&argument.ty)
                        .is_some_and(|ty| self.static_extension_fits_with(extended, &ty, &generics))
            });
            if !reaches {
                continue;
            }
            let level = self
                .binder
                .extension_level(&self.context, candidate)
                .unwrap_or(usize::MAX);
            match by_level.iter_mut().find(|(at, _)| *at == level) {
                Some((_, group)) => group.push(candidate),
                None => by_level.push((level, vec![candidate])),
            }
        }
        by_level.sort_by_key(|(level, _)| *level);
        by_level.into_iter().find_map(|(level, group)| {
            let mut given = arguments.to_vec();
            self.resolve_with_lambdas(&group, &mut given, &Type::Void, &[], false)
                .map(|resolved| (resolved, level, given))
        })
    }

    /// The call of an extension operator that overload resolution settled
    /// on, whose type arguments it inferred from the operands.
    pub(super) fn extension_operator_call(
        &mut self,
        resolved: super::Resolved,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        let super::Resolved {
            method,
            type_arguments,
            substitution,
        } = resolved;
        let ty = self
            .member_type(method, &Type::Void)
            .substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, &Type::Void, &substitution, span);
        BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            ty,
            span,
        )
    }

    /// `target++` and `--target` through a static operator of an extension
    /// block: `target = op(target)`, whose value is the new one for a prefix
    /// operator and the old one for a postfix one.
    pub(super) fn extension_static_increment(
        &mut self,
        name: &str,
        target: &BoundExpression,
        prefix: bool,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let (mut steps, place) = self.kept_variable(target)?;
        let stored = place.ty.clone();
        let old = (!prefix).then(|| self.declare_synthetic_local("old", stored.clone()));
        let local =
            |old| BoundExpression::new(BoundExpressionKind::Local(old), stored.clone(), span);
        let operand = match old {
            Some(old) => {
                steps.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(local(old)),
                        value: Box::new(place.clone()),
                    },
                    stored.clone(),
                    span,
                ));
                local(old)
            }
            None => place.clone(),
        };
        let call = self.user_defined_unary(name, &operand, span)?;
        let call = self.convert(call, &stored);
        steps.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(place),
                value: Box::new(call),
            },
            stored.clone(),
            span,
        ));
        if let Some(old) = old {
            steps.push(local(old));
        }
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            stored,
            span,
        ))
    }

    /// Whether the operand is what an instance operator is asked of: a
    /// variable of a type that is not one of the language's own.
    fn takes_extension_operator(&self, target: &BoundExpression) -> bool {
        let ty = &target.ty;
        let variable = match &target.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::ArrayAccess { .. } => true,
            BoundExpressionKind::Field { field, receiver } => {
                self.kind_of(*field) == SymbolKind::Field
                    && receiver
                        .as_deref()
                        .is_none_or(|receiver| self.takes_extension_receiver(receiver))
            }
            _ => false,
        };
        variable
            && !ty.is_error()
            && ty.symbol().is_some()
            // The language's own types have operators of their own, but for
            // the two that have none of the kind.
            && self.binder.special_of(ty).is_none_or(|special| {
                matches!(special, SpecialType::Object | SpecialType::String)
            })
            && self.binder.enum_underlying(ty).is_none()
            && self.binder.nullable_underlying(ty).is_none()
    }

    /// Whether what a field is read from is itself a variable, or a
    /// reference.
    fn takes_extension_receiver(&self, receiver: &BoundExpression) -> bool {
        let symbols = self.binder.compilation().symbols();
        match &receiver.kind {
            BoundExpressionKind::TypeExpression(_) => true,
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::ArrayAccess { .. } => true,
            BoundExpressionKind::Field {
                receiver: inner,
                field,
            } => {
                receiver.ty.is_reference_type(symbols)
                    || (self.kind_of(*field) == SymbolKind::Field
                        && inner
                            .as_deref()
                            .is_none_or(|inner| self.takes_extension_receiver(inner)))
            }
            _ => receiver.ty.is_reference_type(symbols),
        }
    }

    /// Whether the type of an operand declares an operator of this name.
    fn operand_has_operator(&self, name: &str, ty: &Type, span: TextSpan) -> bool {
        let ty = self
            .binder
            .nullable_underlying(ty)
            .unwrap_or_else(|| ty.clone());
        ty.symbol()
            .is_some_and(|symbol| !self.operator_candidates(symbol, name, span).is_empty())
    }

    /// The target as a place that can be read after being written: itself
    /// where it costs nothing to evaluate twice, else what locates it kept
    /// in temporaries.
    fn kept_variable(
        &mut self,
        target: &BoundExpression,
    ) -> Option<(Vec<BoundExpression>, BoundExpression)> {
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
        if cheap(target) {
            return Some((Vec::new(), target.clone()));
        }
        self.kept_place(target)
    }

    /// How far out the nearest static operator of an extension block that
    /// takes one of these operand types is, where there is one.
    fn static_extension_level(&self, name: &str, operands: &[&Type]) -> Option<usize> {
        let symbols = self.binder.compilation().symbols();
        self.binder
            .extension_members_in_scope(&self.context, name)
            .into_iter()
            .filter_map(|candidate| {
                let detail = symbols.get(candidate).as_method()?;
                if detail.takes_receiver {
                    return None;
                }
                let extended = self.resolve_extended(detail.extended?);
                let takes = operands.iter().any(|operand| {
                    let operand = self
                        .binder
                        .nullable_underlying(operand)
                        .unwrap_or_else(|| (*operand).clone());
                    operand.symbol().is_some() && operand.symbol() == extended.symbol()
                });
                takes.then(|| self.binder.extension_level(&self.context, candidate))?
            })
            .min()
    }

    /// The call of the instance operator `name` (or its checked form, in a
    /// checked context) that the extension blocks in scope give `place`, and
    /// how far out the place is that brings it into view: the nearest place
    /// that has one that takes the arguments decides.
    fn extension_instance_call(
        &mut self,
        name: &str,
        place: &BoundExpression,
        rest: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<(BoundExpression, usize)> {
        let checked =
            crate::declare::checked_operator_name(name).filter(|_| self.in_checked_context(span));
        let symbols = self.binder.compilation().symbols();
        let mut found: Vec<(usize, bool, SymbolId)> = Vec::new();
        for (is_checked, written) in checked
            .map(|checked| (true, checked))
            .into_iter()
            .chain([(false, name)])
        {
            for candidate in self
                .binder
                .extension_members_in_scope(&self.context, written)
            {
                let Some(detail) = symbols.get(candidate).as_method() else {
                    continue;
                };
                if !detail.takes_receiver || detail.extended.is_none() {
                    continue;
                }
                if let Some(level) = self.binder.extension_level(&self.context, candidate) {
                    found.push((level, is_checked, candidate));
                }
            }
        }
        let mut levels: Vec<usize> = found.iter().map(|(level, ..)| *level).collect();
        levels.sort_unstable();
        levels.dedup();
        let by_reference = !place.ty.is_reference_type(symbols);
        for level in levels {
            // A checked operator is preferred to the regular one of the same
            // signature, and is asked first.
            for is_checked in [true, false] {
                let candidates: Vec<SymbolId> = found
                    .iter()
                    .filter(|(at, checked, _)| *at == level && *checked == is_checked)
                    .map(|(.., candidate)| *candidate)
                    .collect();
                if candidates.is_empty() {
                    continue;
                }
                let receiver = if by_reference {
                    BoundExpression::new(
                        BoundExpressionKind::RefArgument {
                            kind: RefKind::Ref,
                            operand: Box::new(place.clone()),
                        },
                        place.ty.clone(),
                        place.span,
                    )
                } else {
                    place.clone()
                };
                let mut arguments = vec![receiver];
                arguments.extend(rest.iter().cloned());
                let Some(super::Resolved {
                    method,
                    type_arguments,
                    substitution,
                }) = self.resolve_with_lambdas(&candidates, &mut arguments, &Type::Void, &[], true)
                else {
                    continue;
                };
                let ty = self
                    .member_type(method, &Type::Void)
                    .substitute(&substitution);
                let arguments =
                    self.convert_arguments(method, arguments, &Type::Void, &substitution, span);
                return Some((
                    BoundExpression::new(
                        BoundExpressionKind::Call {
                            receiver: None,
                            method,
                            type_arguments,
                            arguments,
                            virtual_call: false,
                        },
                        ty,
                        span,
                    ),
                    level,
                ));
            }
        }
        None
    }
}
