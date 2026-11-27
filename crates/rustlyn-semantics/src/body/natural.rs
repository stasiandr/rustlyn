//! The types lambdas and method groups have on their own (C# 10, §10.7.3).
//!
//! `var f = (int x) => x;` is a `Func<int, int>` and `object o = Main;` an
//! `Action`: where a lambda writes every parameter type, or a method group
//! has one signature, the expression has a *natural* delegate type, and a
//! conversion to `object`, `Delegate` or `Expression` goes through it.

use super::{BodyBinder, Diagnostics, LambdaProbe};
use crate::bound::{BoundExpression, BoundExpressionKind, ConstantValue};
use crate::delegates::{DelegateParameter, DelegateSignature};
use crate::symbol::{Location, Modifiers, RefKind, SymbolId, TypeKind};
use crate::types::Type;
use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};
use std::collections::HashMap;

impl BodyBinder<'_> {
    /// The natural type of a lambda or a method group, where it has one.
    ///
    /// Before C# 10 neither has one (Roslyn makes a `FunctionTypeSymbol`
    /// only where `IDS_FeatureInferredDelegateType` is enabled): a lambda
    /// converts to delegate types alone, and an overload taking `Delegate`
    /// or `object` does not apply to it.
    pub(super) fn natural_function_type(&mut self, value: &BoundExpression) -> Option<Type> {
        if !self.language_version().at_least(LanguageVersion::CSharp10) {
            return None;
        }
        match value.kind {
            BoundExpressionKind::UnboundLambda(_) => self.natural_delegate_type(value),
            BoundExpressionKind::MethodGroup { .. } => self.method_group_natural_type(value),
            _ => None,
        }
    }

    /// Whether `ty` is a delegate type, or an `Expression<TDelegate>`: what a
    /// lambda converts to directly, with no natural type in between.
    pub(super) fn is_function_target(&self, ty: &Type) -> bool {
        let inner = self.delegate_within(ty);
        let symbols = self.binder.compilation().symbols();
        inner
            .symbol()
            .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Delegate))
    }

    /// Whether a lambda or a method group converts to `ty` through its
    /// natural type (§10.2.14 of C# 10): `object`, `Delegate`,
    /// `MulticastDelegate` and the interfaces a delegate implements, or
    /// `Expression` and `LambdaExpression` for a lambda.
    pub(super) fn takes_a_function_type(&self, ty: &Type, lambda: bool) -> bool {
        if !self.language_version().at_least(LanguageVersion::CSharp10) {
            return false;
        }
        let Some(symbol) = ty.symbol() else {
            return false;
        };
        if !matches!(ty, Type::Named { type_arguments, .. } if type_arguments.is_empty()) {
            return false;
        }
        let name = self.binder.compilation().symbols().qualified_name(symbol);
        matches!(
            name.as_str(),
            "System.Object"
                | "System.Delegate"
                | "System.MulticastDelegate"
                | "System.ICloneable"
                | "System.Runtime.Serialization.ISerializable"
        ) || (lambda
            && matches!(
                name.as_str(),
                "System.Linq.Expressions.Expression" | "System.Linq.Expressions.LambdaExpression"
            ))
    }

    /// The type a lambda or a method group goes through on its way to a
    /// type that is not a delegate: `object o = () => 1;` makes a
    /// `Func<int>` and converts that, and `Expression e = () => 1;` an
    /// `Expression<Func<int>>`.
    pub(super) fn natural_conversion_through(
        &mut self,
        value: &BoundExpression,
        target: &Type,
    ) -> Option<Type> {
        let lambda = matches!(value.kind, BoundExpressionKind::UnboundLambda(_));
        if !self.takes_a_function_type(target, lambda) {
            return None;
        }
        let natural = self.natural_function_type(value)?;
        if lambda && self.is_expression_type(target) {
            let expression = self
                .binder
                .compilation()
                .type_by_metadata_name("System.Linq.Expressions.Expression`1")?;
            return Some(Type::Named {
                symbol: expression,
                type_arguments: vec![natural],
            });
        }
        Some(natural)
    }

    /// A type parameter an expression type constrains takes a lambda as a
    /// tree (C# 10): `F2<T>(T t) where T : Expression` handed `() => 1`
    /// infers an `Expression<Func<int>>`, not the `Func<int>` the lambda is
    /// on its own. The constraint is read through the receiver: `U : T` in
    /// `A<LambdaExpression>` is one.
    pub(super) fn infer_expression_trees(
        &self,
        parameters: &[SymbolId],
        substitution: &HashMap<SymbolId, Type>,
        inferred: &mut HashMap<SymbolId, Type>,
    ) {
        let Some(tree) = self
            .binder
            .compilation()
            .type_by_metadata_name("System.Linq.Expressions.Expression`1")
        else {
            return;
        };
        let symbols = self.binder.compilation().symbols();
        for parameter in parameters {
            let Some(argument) = inferred.get(parameter) else {
                continue;
            };
            let delegate = argument
                .symbol()
                .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Delegate));
            if !delegate {
                continue;
            }
            let constrained = self
                .binder
                .base_types_of(*parameter)
                .iter()
                .any(|constraint| {
                    let mut current = Some(constraint.substitute(substitution));
                    let mut depth = 0;
                    while let Some(ty) = current {
                        if self.is_expression_type(&ty) || ty.symbol() == Some(tree) {
                            return true;
                        }
                        depth += 1;
                        if depth > 16 {
                            return false;
                        }
                        current = ty
                            .symbol()
                            .and_then(|symbol| self.binder.base_class_of(symbol));
                    }
                    false
                });
            if constrained {
                let wrapped = Type::Named {
                    symbol: tree,
                    type_arguments: vec![argument.clone()],
                };
                inferred.insert(*parameter, wrapped);
            }
        }
    }

    fn is_expression_type(&self, ty: &Type) -> bool {
        ty.symbol().is_some_and(|symbol| {
            let name = self.binder.compilation().symbols().qualified_name(symbol);
            name == "System.Linq.Expressions.Expression"
                || name == "System.Linq.Expressions.LambdaExpression"
        })
    }

    /// The natural type of each lambda or method group among a call's
    /// arguments that some candidate takes as a bare type parameter of its
    /// own, which is what that type parameter is inferred from.
    pub(super) fn natural_types_for_inference(
        &mut self,
        candidates: &[SymbolId],
        arguments: &[BoundExpression],
        explicit: &[Type],
    ) -> Vec<Option<Type>> {
        if !explicit.is_empty() {
            return Vec::new();
        }
        let mut types = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.iter().enumerate() {
            let wanted = matches!(
                argument.kind,
                BoundExpressionKind::UnboundLambda(_) | BoundExpressionKind::MethodGroup { .. }
            ) && self.may_have_natural_type(argument)
                && candidates
                    .iter()
                    .any(|candidate| self.takes_a_bare_type_parameter(*candidate, index));
            if wanted {
                types.push(self.natural_function_type(argument));
                continue;
            }
            // `Test((() => 7, () => 8))` infers through the tuple's elements:
            // each lambda there stands for its natural type.
            if let BoundExpressionKind::TupleCreation(elements) = &argument.kind
                && let Type::Tuple(written) = &argument.ty
                && elements.iter().any(|element| {
                    matches!(
                        element.kind,
                        BoundExpressionKind::UnboundLambda(_)
                            | BoundExpressionKind::MethodGroup { .. }
                    )
                })
                && candidates
                    .iter()
                    .any(|candidate| self.takes_a_generic_parameter(*candidate, index))
            {
                let mut filled = written.clone();
                for (element, slot) in elements.iter().zip(filled.iter_mut()) {
                    if matches!(
                        element.kind,
                        BoundExpressionKind::UnboundLambda(_)
                            | BoundExpressionKind::MethodGroup { .. }
                    ) && self.may_have_natural_type(element)
                        && let Some(natural) = self.natural_function_type(element)
                    {
                        slot.ty = natural;
                    }
                }
                types.push(Some(Type::Tuple(filled)));
                continue;
            }
            types.push(None);
        }
        types
    }

    /// Whether a generic method's parameter at `index` mentions one of its
    /// own type parameters.
    fn takes_a_generic_parameter(&self, method: SymbolId, index: usize) -> bool {
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(method).as_method() else {
            return false;
        };
        let Some(parameter) = detail.parameters.get(index) else {
            return false;
        };
        let mut sink = Diagnostics::new();
        !detail.type_parameters.is_empty()
            && mentions_type_parameter(&self.binder.type_of(*parameter, &mut sink))
    }

    /// Whether a generic method's parameter at `index` is one of its own
    /// type parameters and nothing else.
    fn takes_a_bare_type_parameter(&self, method: SymbolId, index: usize) -> bool {
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(method).as_method() else {
            return false;
        };
        let Some(parameter) = detail.parameters.get(index) else {
            return false;
        };
        let mut sink = Diagnostics::new();
        matches!(
            self.binder.type_of(*parameter, &mut sink),
            Type::TypeParameter(symbol) if detail.type_parameters.contains(&symbol)
        )
    }

    /// The best common type of a set of expressions (§12.6.3.16): of the
    /// types they have — a lambda's and a method group's natural type among
    /// them — the one every other converts to.
    pub(super) fn best_common_type(&mut self, expressions: &[BoundExpression]) -> Option<Type> {
        // Each type, and whether it is a function type: a lambda's or a
        // method group's, which converts to any delegate of its signature
        // and not only to the `Func` or `Action` it stands for on its own.
        let mut candidates: Vec<(Type, bool)> = Vec::new();
        for expression in expressions {
            let (ty, function) = match expression.kind {
                BoundExpressionKind::UnboundLambda(_) | BoundExpressionKind::MethodGroup { .. } => {
                    (self.natural_function_type(expression), true)
                }
                _ if expression.ty.is_error() || matches!(expression.ty, Type::Null) => {
                    (None, false)
                }
                _ => (Some(expression.ty.clone()), false),
            };
            if let Some(ty) = ty
                && !candidates.iter().any(|(known, _)| *known == ty)
            {
                candidates.push((ty, function));
            }
        }
        let converts = |from: &(Type, bool), to: &Type| {
            self.binder.converts_implicitly(&from.0, to)
                || (from.1
                    && self.delegate_signature(to).is_some()
                    && self.delegate_signature(&from.0) == self.delegate_signature(to))
        };
        let mut best: Option<&(Type, bool)> = None;
        for candidate in &candidates {
            best = match best {
                None => Some(candidate),
                Some(current)
                    if converts(current, &candidate.0) && !converts(candidate, &current.0) =>
                {
                    Some(candidate)
                }
                Some(current) => Some(current),
            };
        }
        let best = best?;
        candidates
            .iter()
            .all(|candidate| candidate.0 == best.0 || converts(candidate, &best.0))
            .then(|| best.0.clone())
    }

    /// The delegate type a lambda has on its own (§10.7.3 of C# 10): its
    /// written parameters — with their `ref` kinds, default values and
    /// `params` — and the return type it wrote or its body gives back.
    ///
    /// `None` where a parameter has no type written: then the lambda has no
    /// type until something gives it one.
    pub(super) fn natural_delegate_type(&mut self, lambda: &BoundExpression) -> Option<Type> {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return None;
        };
        let node = self.syntax_at(span)?;
        let parameters = self.lambda_signature(&node)?;
        let returns = match self.lambda_written_return(&node) {
            Some(written) => written,
            // `(ref int x) => ref x` gives back a reference, which is part of
            // its type as much as a written `ref int` would be.
            None => {
                let inferred = self.inferred_lambda_return(lambda, &parameters)?;
                let by_ref = self.lambda_returns_ref(span) == Some(true)
                    && !matches!(inferred, Type::ByRef(_) | Type::Void);
                (
                    if by_ref {
                        Type::ByRef(Box::new(inferred))
                    } else {
                        inferred
                    },
                    false,
                )
            }
        };
        let signature = DelegateSignature {
            parameters,
            returns: returns.0,
            returns_readonly: returns.1,
        };
        self.binder
            .delegate_type_for(&signature, Some(Location::new(self.tree, span)))
    }

    /// What a lambda's body gives back, found by binding it against a
    /// delegate that returns nothing and, where an expression body has a
    /// value, against one that returns it.
    pub(super) fn inferred_lambda_return(
        &mut self,
        lambda: &BoundExpression,
        parameters: &[DelegateParameter],
    ) -> Option<Type> {
        // The probe takes every parameter by value and without a default: all
        // it is for is what the body returns, and a delegate of that shape
        // is an `Action` rather than a type made for the probe alone.
        let plain: Vec<DelegateParameter> = parameters
            .iter()
            .map(|parameter| DelegateParameter {
                ty: parameter.ty.clone(),
                ref_kind: RefKind::None,
                ref_readonly: false,
                unscoped: false,
                default: None,
                default_syntax: None,
                is_params: false,
                scoped: false,
            })
            .collect();
        let action = self.binder.delegate_type_for(
            &DelegateSignature {
                parameters: plain.clone(),
                returns: Type::Void,
                returns_readonly: false,
            },
            None,
        )?;
        // An `async` lambda's probe already gives the task around its body.
        let probe = self.probe_lambda(lambda, &action)?;
        let LambdaProbe {
            returns,
            yields_value,
            all_returns,
            ..
        } = probe;
        // Nothing returned is an `Action`'s body; a first `return null;`,
        // which against an `Action` has no type to give, is not that when
        // another `return` gives a value.
        if matches!(returns, Type::Void)
            && !yields_value
            && all_returns
                .iter()
                .all(|(ty, _, _)| matches!(ty, Type::Void | Type::Null))
        {
            return Some(Type::Void);
        }
        // An expression body whose value an `Action` dropped, or a `return`
        // of a lambda or a method group, which against an `Action` has no
        // type at all: bind it again against a `Func` to learn the value's
        // type.
        // `async () => 0` bound as an `Action` is a `Task` that dropped the
        // value, just as `() => 0` is nothing that dropped it.
        let is_async = self.is_async_lambda(lambda);
        let task = self
            .binder
            .compilation()
            .type_by_metadata_name("System.Threading.Tasks.Task");
        let dropped_into_task =
            is_async && yields_value && returns.symbol().is_some() && returns.symbol() == task;
        let returns = if matches!(returns, Type::Void)
            || dropped_into_task
            || all_returns.iter().any(|(ty, _, _)| ty.is_error())
        {
            let object = self.special(crate::corlib::SpecialType::Object);
            // An `async` one is asked for a `Task<object>`, whose result is
            // what its body gives back.
            let object = match self
                .binder
                .compilation()
                .type_by_metadata_name("System.Threading.Tasks.Task`1")
            {
                Some(generic) if is_async => Type::Named {
                    symbol: generic,
                    type_arguments: vec![object],
                },
                _ => object,
            };
            let func = self.binder.delegate_type_for(
                &DelegateSignature {
                    parameters: plain,
                    returns: object,
                    returns_readonly: false,
                },
                None,
            )?;
            let probe = self.probe_lambda(lambda, &func)?;
            self.best_returned(lambda, probe.returns, &probe.all_returns)
        } else {
            self.best_returned(lambda, returns, &all_returns)
        };
        if returns.is_error() || matches!(returns, Type::Void | Type::Null) {
            return None;
        }
        Some(returns)
    }

    /// The type a lambda returns where it returns more than one value: the
    /// best common type of them (§12.6.3.13), with the task an `async`
    /// lambda wraps around it.
    fn best_returned(
        &self,
        lambda: &BoundExpression,
        first: Type,
        all: &[(Type, rustlyn_text::TextSpan, bool)],
    ) -> Type {
        // A delegate made from a method group is a function only where the
        // group was written bare: `(StringIntDelegate)M` is a delegate of
        // the type its cast names.
        let candidates: Vec<(Type, bool)> = all
            .iter()
            .filter(|(ty, _, _)| !ty.is_error() && !matches!(ty, Type::Null | Type::Void))
            .map(|(ty, span, function)| {
                let cast = self.syntax_at(*span).is_some_and(|node| {
                    let mut node = node;
                    while node.kind() == SyntaxKind::ParenthesizedExpression {
                        match node.children().next() {
                            Some(inner) => node = inner,
                            None => break,
                        }
                    }
                    node.kind() == SyntaxKind::CastExpression
                });
                (ty.clone(), *function && !cast)
            })
            .collect();
        let candidates: Vec<&(Type, bool)> = candidates.iter().collect();
        // `if (b) return null; else return new object();`: the first return
        // has no type, and the one that has is the lambda's.
        if let [only] = candidates.as_slice()
            && matches!(first, Type::Null | Type::Void)
        {
            return self.wrapped_in_task(lambda, only.0.clone());
        }
        if candidates.len() < 2 {
            return first;
        }
        let converts = |from: &(Type, bool), to: &(Type, bool)| {
            from.0 == to.0
                || self.binder.converts_implicitly(&from.0, &to.0)
                || (from.1 && !to.1 && self.function_type_converts(&from.0, &to.0))
        };
        let mut best = candidates[0];
        for candidate in &candidates[1..] {
            if best.0 != candidate.0 && converts(best, candidate) && !converts(candidate, best) {
                best = candidate;
            }
        }
        if candidates.iter().all(|candidate| converts(candidate, best)) {
            self.wrapped_in_task(lambda, best.0.clone())
        } else {
            first
        }
    }

    /// Whether a lambda or a method group whose natural type is `natural`
    /// converts to the delegate type `target`: the same parameters, and a
    /// result that converts.
    fn function_type_converts(&self, natural: &Type, target: &Type) -> bool {
        if !self.is_function_target(target) {
            return false;
        }
        let (Some((taken, gives)), Some((wanted, returns))) = (
            self.delegate_signature(natural),
            self.delegate_signature(target),
        ) else {
            return false;
        };
        taken == wanted
            && (gives == returns
                || (!matches!(gives, Type::Void)
                    && !matches!(returns, Type::Void)
                    && self.binder.converts_implicitly(&gives, &returns)))
    }

    /// The parameters a lambda wrote, with their types, `ref` kinds,
    /// default values and `params`; `None` where any type is left out.
    fn lambda_signature(&mut self, node: &SyntaxNode) -> Option<Vec<DelegateParameter>> {
        match node.kind() {
            SyntaxKind::ParenthesizedLambdaExpression => {}
            // `delegate { }` with no parameter list converts to any delegate
            // and so has no type of its own; `delegate () { }` is an `Action`.
            SyntaxKind::AnonymousMethodExpression => {
                node.child_of_kind(SyntaxKind::ParameterList)?;
            }
            _ => return None,
        }
        let Some(list) = node.child_of_kind(SyntaxKind::ParameterList) else {
            return Some(Vec::new());
        };
        let context = self.binder.context_at(self.tree, node);
        let mut parameters = Vec::new();
        for parameter in list.children() {
            if parameter.kind() != SyntaxKind::Parameter {
                continue;
            }
            let written = parameter
                .children()
                .find(|child| child.kind().is_type_node())?;
            let mut sink = Diagnostics::new();
            let ty = match self.binder.resolve_type(&written, &context, &mut sink) {
                Type::Error => return None,
                ty => ty,
            };
            let ref_kind = written_ref_kind(&parameter);
            let is_params = parameter
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::ParamsKeyword);
            let written = parameter
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().find(|child| child.kind().is_expression()))
                .or_else(|| crate::declare::attributed_default(&parameter))
                // `[Optional, DecimalConstant(...)]` and `[Optional,
                // DateTimeConstant(...)]` give a default no constant holds:
                // the attribute is where it is written.
                .or_else(|| {
                    crate::declare::parameter_attribute(&parameter, "Optional")?;
                    crate::declare::parameter_attribute(&parameter, "DecimalConstant").or_else(
                        || crate::declare::parameter_attribute(&parameter, "DateTimeConstant"),
                    )
                });
            let (default, default_syntax) = match written {
                Some(expression) => {
                    let (constant, folded) = self.default_constant(&expression, &ty);
                    let key = self.default_key(&expression);
                    let syntax =
                        (!folded).then(|| (Location::new(self.tree, expression.span()), key));
                    (Some(constant), syntax)
                }
                None => (None, None),
            };
            let scoped = is_scoped(&parameter);
            parameters.push(DelegateParameter {
                ty,
                ref_kind,
                ref_readonly: written_ref_readonly(&parameter),
                unscoped: crate::declare::parameter_attribute(&parameter, "UnscopedRef").is_some(),
                default,
                default_syntax,
                is_params,
                scoped,
            });
        }
        Some(parameters)
    }

    /// What tells one default no constant holds from another: a `decimal`'s
    /// value however it is written (`100m`, `100.0m` and `[DecimalConstant(0,
    /// 0, 0, 0, 100)]` are one value), and otherwise the text.
    fn default_key(&mut self, expression: &SyntaxNode) -> String {
        let special = if expression.kind() == SyntaxKind::Attribute {
            self.attributed_special(self.tree, expression)
        } else {
            let (negated, literal) = match expression.kind() {
                SyntaxKind::UnaryMinusExpression => (true, expression.children().next()),
                _ => (false, Some(expression.clone())),
            };
            literal
                .filter(|literal| literal.kind() == SyntaxKind::NumericLiteralExpression)
                .and_then(|literal| super::expressions::decimal_parts(&literal.text().to_string()))
                .filter(|_| {
                    let text = expression.text().to_string();
                    text.trim_end().ends_with(['m', 'M'])
                })
                .map(
                    |(lo, mid, hi, negative, scale)| crate::bound::SpecialConstant::Decimal {
                        scale,
                        negative: negative != negated,
                        hi,
                        mid,
                        lo,
                    },
                )
        };
        match special {
            Some(crate::bound::SpecialConstant::Decimal {
                scale,
                negative,
                hi,
                mid,
                lo,
            }) => {
                let mut mantissa =
                    (u128::from(hi) << 64) | (u128::from(mid) << 32) | u128::from(lo);
                let mut scale = scale;
                while scale > 0 && mantissa % 10 == 0 {
                    mantissa /= 10;
                    scale -= 1;
                }
                let negative = negative && mantissa != 0;
                format!(
                    "decimal {}{mantissa}e-{scale}",
                    if negative { "-" } else { "" }
                )
            }
            Some(crate::bound::SpecialConstant::DateTime(ticks)) => format!("DateTime {ticks}"),
            None => expression.text().to_string(),
        }
    }

    /// The constant a default value written on a lambda parameter is, as a
    /// value of the parameter's type; a default that folds to nothing —
    /// `default(S)` — is the null metadata records for it.
    fn default_constant(&mut self, expression: &SyntaxNode, ty: &Type) -> (ConstantValue, bool) {
        let floor = self.speculation_floor();
        let value = self.bind_expression(expression);
        let value = self.convert(value, ty);
        let folded = self.binder.folded(&value);
        self.unwind_speculation(floor);
        match folded {
            Some(folded) => (self.binder.constant_as(folded, ty), true),
            None => (ConstantValue::Null, false),
        }
    }

    /// The return type a lambda wrote before its parameters, with whether it
    /// was `ref readonly`.
    fn lambda_written_return(&self, node: &SyntaxNode) -> Option<(Type, bool)> {
        if node.kind() != SyntaxKind::ParenthesizedLambdaExpression {
            return None;
        }
        let list = node.child_of_kind(SyntaxKind::ParameterList)?;
        let written = node.children().find(|child| {
            child.span().end() <= list.span().start()
                && child.kind().is_type_node()
                && child.kind() != SyntaxKind::AttributeList
        })?;
        let context = self.binder.context_at(self.tree, node);
        let mut sink = Diagnostics::new();
        let readonly = written.kind() == SyntaxKind::RefType
            && written
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::ReadOnlyKeyword);
        match self.binder.resolve_type(&written, &context, &mut sink) {
            Type::Error => None,
            resolved => Some((resolved, readonly)),
        }
    }

    /// Whether an argument is a lambda or a method group that has a type of
    /// its own, as far as can be told without binding a body: every
    /// parameter of a lambda written with its type, one signature in a
    /// group.
    pub(super) fn may_have_natural_type(&self, argument: &BoundExpression) -> bool {
        if !self.language_version().at_least(LanguageVersion::CSharp10) {
            return false;
        }
        match argument.kind {
            BoundExpressionKind::UnboundLambda(span) => {
                let Some(node) = self.syntax_at(span) else {
                    return false;
                };
                if !matches!(
                    node.kind(),
                    SyntaxKind::ParenthesizedLambdaExpression
                        | SyntaxKind::AnonymousMethodExpression
                ) {
                    return false;
                }
                node.child_of_kind(SyntaxKind::ParameterList)
                    .is_some_and(|list| {
                        list.children()
                            .filter(|child| child.kind() == SyntaxKind::Parameter)
                            .all(|parameter| {
                                parameter
                                    .children()
                                    .any(|child| child.kind().is_type_node())
                            })
                    })
            }
            BoundExpressionKind::MethodGroup { .. } => {
                self.unique_group_signature(argument).is_some()
            }
            _ => false,
        }
    }

    /// Whether the argument at `index` reaches `parameter` through its
    /// natural type.
    pub(super) fn natural_fits(
        &self,
        natural: &[bool],
        lambdas: &[Option<usize>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        natural.get(index).copied().unwrap_or(false)
            && self
                .takes_a_function_type(parameter, lambdas.get(index).copied().flatten().is_some())
    }

    /// The delegate type a method group has on its own (§10.7.3 of C# 10,
    /// with the C# 13 rules): the one signature its candidates share, the
    /// instance methods first and the extension methods only where there
    /// are none.
    pub(super) fn method_group_natural_type(&mut self, group: &BoundExpression) -> Option<Type> {
        let signature = self.unique_group_signature(group)?;
        self.binder
            .delegate_type_for(&signature, Some(Location::new(self.tree, group.span)))
    }

    /// The type arguments a method of a group takes, where they keep its
    /// constraints: `M<object>` is no `M<T>(this T, object) where T :
    /// struct`, and that method is no part of the group's type.
    fn fitting_type_arguments(
        &self,
        method: SymbolId,
        receiver: Option<&Type>,
        explicit: &[Type],
    ) -> Option<Vec<Type>> {
        let arguments = self.receiver_type_arguments(method, receiver, explicit)?;
        let parameters = self
            .binder
            .compilation()
            .symbols()
            .get(method)
            .as_method()?
            .type_parameters
            .clone();
        let inferred: HashMap<SymbolId, Type> = parameters
            .iter()
            .copied()
            .zip(arguments.iter().cloned())
            .collect();
        self.satisfies_constraints(&parameters, &inferred)
            .then_some(arguments)
    }

    /// The one signature the methods of a group share, if they do.
    fn unique_group_signature(&self, group: &BoundExpression) -> Option<DelegateSignature> {
        let BoundExpressionKind::MethodGroup {
            receiver,
            candidates,
        } = &group.kind
        else {
            return None;
        };
        let symbols = self.binder.compilation().symbols();
        let explicit = self.group_type_arguments(group.span);
        // A type written in front means the static methods; a value, the
        // instance ones and extension methods; nothing at all, whatever the
        // context allows.
        let wants_static = match receiver.as_deref() {
            Some(BoundExpression {
                kind: BoundExpressionKind::TypeExpression(_),
                ..
            }) => Some(true),
            Some(_) => Some(false),
            None if self.static_context() => Some(true),
            None => None,
        };
        let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
        let mut members: Vec<SymbolId> = Vec::new();
        let mut extensions: Vec<SymbolId> = Vec::new();
        for candidate in candidates {
            let symbol = symbols.get(*candidate);
            let Some(detail) = symbol.as_method() else {
                continue;
            };
            // An extension method's type arguments may come from the
            // receiver alone (C# 13); anything else takes what was written.
            if detail.is_extension && receiver.is_some() && wants_static == Some(false) {
                if detail.type_parameters.len() == explicit.len() || explicit.is_empty() {
                    extensions.push(*candidate);
                }
                continue;
            }
            if detail.type_parameters.len() != explicit.len() {
                continue;
            }
            let is_static = self.is_static(*candidate);
            if wants_static.is_some_and(|wanted| wanted != is_static) {
                continue;
            }
            if !self.accessible(*candidate) {
                continue;
            }
            members.push(*candidate);
        }
        // An override and the method it overrides are one member: the
        // override is the one seen, and says what its defaults are.
        let overridden: Vec<SymbolId> = members
            .iter()
            .filter(|member| {
                symbols
                    .get(**member)
                    .modifiers
                    .contains(Modifiers::OVERRIDE)
            })
            .map(|member| self.least_overridden(*member))
            .collect();
        let members: Vec<SymbolId> = members
            .into_iter()
            .filter(|member| {
                symbols.get(*member).modifiers.contains(Modifiers::OVERRIDE)
                    || !overridden.contains(member)
            })
            .collect();
        // Extension methods are looked for scope by scope (C# 13): the
        // nearest scope with a method the receiver can call is the only one
        // that counts, and its methods must agree.
        let from = if members.is_empty() {
            let name = extensions
                .first()
                .map(|first| symbols.get(*first).name.clone())
                .unwrap_or_default();
            let receiver_type = receiver_type.clone().unwrap_or(Type::Error);
            let levels = self.binder.extension_levels(&self.context, &name);
            let mut chosen = extensions.clone();
            for level in levels {
                let applicable: Vec<SymbolId> = level
                    .into_iter()
                    .filter(|method| extensions.contains(method))
                    .filter(|method| self.extension_takes_receiver(*method, &receiver_type))
                    .filter(|method| {
                        self.fitting_type_arguments(*method, Some(&receiver_type), &explicit)
                            .is_some()
                    })
                    .collect();
                if !applicable.is_empty() {
                    chosen = applicable;
                    break;
                }
            }
            chosen
        } else {
            members
        };
        let mut found: Option<DelegateSignature> = None;
        for candidate in from {
            let arguments =
                match self.fitting_type_arguments(candidate, receiver_type.as_ref(), &explicit) {
                    Some(arguments) => arguments,
                    None => continue,
                };
            let signature = self.method_signature(
                candidate,
                receiver_type.as_ref(),
                &arguments,
                receiver.is_some(),
            )?;
            match &found {
                None => found = Some(signature),
                Some(existing) if same_signature(existing, &signature) => {}
                Some(_) => return None,
            }
        }
        found
    }

    /// The method an override overrides, all the way down: the one that
    /// declared the slot (Roslyn's `GetLeastOverriddenMethod`).
    pub(super) fn least_overridden(&self, method: SymbolId) -> SymbolId {
        let symbols = self.binder.compilation().symbols();
        let mut current = method;
        for _ in 0..32 {
            let symbol = symbols.get(current);
            if !symbol.modifiers.contains(Modifiers::OVERRIDE) {
                break;
            }
            let Some(detail) = symbol.as_method() else {
                break;
            };
            let mut sink = Diagnostics::new();
            let shape: Vec<(RefKind, Type)> = detail
                .parameters
                .iter()
                .map(|parameter| {
                    (
                        symbols
                            .get(*parameter)
                            .as_parameter()
                            .map_or(RefKind::None, |detail| detail.ref_kind),
                        self.binder.type_of(*parameter, &mut sink),
                    )
                })
                .collect();
            let arity = detail.type_parameters.len();
            let name = symbol.name.clone();
            let mut base = symbol
                .container
                .and_then(|container| self.binder.base_class_of(container));
            let mut found = None;
            while let Some(ty) = base {
                let Some(owner) = ty.symbol() else {
                    break;
                };
                let substitution = self.binder.type_substitution(&ty);
                found =
                    symbols
                        .lookup(owner, &name)
                        .iter()
                        .copied()
                        .find(|candidate| {
                            let Some(other) = symbols.get(*candidate).as_method() else {
                                return false;
                            };
                            other.type_parameters.len() == arity
                                && other.parameters.len() == shape.len()
                                && other.parameters.iter().zip(&shape).all(
                                    |(parameter, (kind, ty))| {
                                        let written = self
                                            .binder
                                            .type_of(*parameter, &mut sink)
                                            .substitute(&substitution);
                                        symbols
                                            .get(*parameter)
                                            .as_parameter()
                                            .map_or(RefKind::None, |detail| detail.ref_kind)
                                            == *kind
                                            && (written == *ty || arity > 0)
                                    },
                                )
                        });
                if found.is_some() {
                    break;
                }
                base = self.binder.base_class_of(owner);
            }
            match found {
                Some(overridden) => current = overridden,
                None => break,
            }
        }
        current
    }

    /// The type arguments a method of a group is taken with: the ones
    /// written, or for a generic extension method written without any, the
    /// ones its receiver says — `None` where the receiver leaves one open.
    fn receiver_type_arguments(
        &self,
        method: SymbolId,
        receiver: Option<&Type>,
        explicit: &[Type],
    ) -> Option<Vec<Type>> {
        let symbols = self.binder.compilation().symbols();
        let detail = symbols.get(method).as_method()?;
        if !explicit.is_empty() || detail.type_parameters.is_empty() {
            return Some(explicit.to_vec());
        }
        let receiver = receiver?;
        let first = detail.parameters.first()?;
        let mut sink = Diagnostics::new();
        let taken = self.binder.type_of(*first, &mut sink);
        let mut inferred = std::collections::HashMap::new();
        self.infer_into(&taken, receiver, &detail.type_parameters, &mut inferred);
        detail
            .type_parameters
            .iter()
            .map(|parameter| inferred.get(parameter).cloned())
            .collect()
    }

    /// Whether an extension method's `this` parameter takes the receiver:
    /// by identity, reference or boxing, and for a generic method once its
    /// type parameters are inferred from the receiver.
    fn extension_takes_receiver(&self, method: SymbolId, receiver: &Type) -> bool {
        if receiver.is_error() {
            return true;
        }
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(method).as_method() else {
            return false;
        };
        let Some(first) = detail.parameters.first() else {
            return false;
        };
        let mut sink = Diagnostics::new();
        let taken = self.binder.type_of(*first, &mut sink);
        let taken = if detail.type_parameters.is_empty() {
            taken
        } else {
            let mut inferred = std::collections::HashMap::new();
            self.infer_into(&taken, receiver, &detail.type_parameters, &mut inferred);
            taken.substitute(&inferred)
        };
        self.binder.converts_implicitly(receiver, &taken)
    }

    /// A method's signature as a delegate would take it, seen through the
    /// receiver and with its type arguments put in.
    fn method_signature(
        &self,
        method: SymbolId,
        receiver: Option<&Type>,
        explicit: &[Type],
        closed: bool,
    ) -> Option<DelegateSignature> {
        let symbols = self.binder.compilation().symbols();
        let detail = symbols.get(method).as_method()?;
        let skip = usize::from(detail.is_extension && closed);
        let through = match (receiver, skip) {
            (Some(ty), 0) if !ty.is_error() => ty.clone(),
            _ => symbols
                .get(method)
                .container
                .map_or(Type::Error, |container| self.binder.self_type(container)),
        };
        let substitution: std::collections::HashMap<SymbolId, Type> = detail
            .type_parameters
            .iter()
            .copied()
            .zip(explicit.iter().cloned())
            .collect();
        let count = detail.parameters.len();
        // `params` is the least overridden method's to say; a default value
        // is the override's own.
        let original = self.least_overridden(method);
        let params_declared = symbols
            .get(original)
            .as_method()
            .and_then(|original| original.parameters.last())
            .and_then(|last| symbols.get(*last).as_parameter())
            .is_some_and(|last| last.is_params);
        let mut parameters = Vec::new();
        for (index, parameter) in detail.parameters.iter().enumerate().skip(skip) {
            let info = symbols.get(*parameter).as_parameter()?;
            // The default value of one of these parameters is what asks for
            // this signature: there is none to give.
            if self.binder.parameter_default_in_progress(*parameter) {
                return None;
            }
            let ty = self
                .member_type(*parameter, &through)
                .substitute(&substitution);
            let default = info.has_default.then(|| {
                self.binder
                    .parameter_default(*parameter)
                    .unwrap_or(ConstantValue::Null)
            });
            let scoped = self
                .binder
                .compilation()
                .declaration_node(*parameter)
                .is_some_and(|node| is_scoped(&node));
            parameters.push(DelegateParameter {
                ty,
                ref_kind: info.ref_kind,
                ref_readonly: info.ref_readonly,
                unscoped: info.unscoped_ref,
                default,
                default_syntax: None,
                is_params: params_declared && index + 1 == count,
                scoped,
            });
        }
        let mut sink = Diagnostics::new();
        let declared = self.binder.type_of(method, &mut sink);
        let value = self.member_type(method, &through).substitute(&substitution);
        let returns = match declared {
            Type::Void => Type::Void,
            Type::ByRef(_) => Type::ByRef(Box::new(value)),
            _ => value,
        };
        Some(DelegateSignature {
            parameters,
            returns,
            returns_readonly: detail.returns_readonly || self.declared_ref_readonly(method),
        })
    }

    /// Whether a method of the source was declared `ref readonly T M()`.
    fn declared_ref_readonly(&self, method: SymbolId) -> bool {
        let Some(node) = self.binder.compilation().declaration_node(method) else {
            return false;
        };
        node.children()
            .find(|child| child.kind().is_type_node() && child.kind() != SyntaxKind::AttributeList)
            .is_some_and(|ty| {
                ty.kind() == SyntaxKind::RefType
                    && ty
                        .child_tokens()
                        .any(|token| token.kind() == SyntaxKind::ReadOnlyKeyword)
            })
    }

    /// The user-defined conversion that takes a lambda or a method group to
    /// `target` through a delegate type (§10.5.4): an `op_Implicit` of the
    /// target, or also an `op_Explicit` where a cast asked for it, with the
    /// delegate type it takes.
    pub(super) fn function_conversion_operator(
        &self,
        value: &BoundExpression,
        target: &Type,
        explicit: bool,
    ) -> Option<(SymbolId, Type)> {
        let (lambda, group) = match &value.kind {
            BoundExpressionKind::UnboundLambda(_) => (true, None),
            BoundExpressionKind::MethodGroup {
                candidates,
                receiver,
            } => (false, Some((candidates.clone(), receiver.is_some()))),
            _ => return None,
        };
        let symbol = target.symbol()?;
        if self.binder.special_of(target).is_some() {
            return None;
        }
        let names: &[&str] = if explicit {
            &["op_Implicit", "op_Explicit"]
        } else {
            &["op_Implicit"]
        };
        for name in names {
            for operator in self.binder.lookup_member(symbol, name) {
                let symbols = self.binder.compilation().symbols();
                let Some(detail) = symbols.get(operator).as_method() else {
                    continue;
                };
                let [parameter] = detail.parameters.as_slice() else {
                    continue;
                };
                let returns = self.member_type(operator, target);
                if returns != *target {
                    continue;
                }
                let taken = self.member_type(*parameter, target);
                if !self.is_function_target(&taken) {
                    continue;
                }
                let fits = if lambda {
                    self.lambda_fits(value, &taken)
                } else {
                    let (candidates, closed) = group.as_ref()?;
                    self.group_fits(candidates, *closed, &taken)
                };
                if fits {
                    return Some((operator, taken));
                }
            }
        }
        None
    }

    /// Whether what a method of a group returns is what a delegate
    /// returning `wanted` may give back (§10.8): nothing for nothing, and
    /// otherwise the same type or one a reference conversion reaches. `int
    /// F2()` is no `Action`, and `void F1()` no `Func<int>`. Where either
    /// side still mentions a type parameter, inference has yet to say, and
    /// the method is not ruled out.
    pub(super) fn group_return_fits(
        &self,
        method: SymbolId,
        delegate: &Type,
        wanted: &Type,
    ) -> bool {
        let symbols = self.binder.compilation().symbols();
        // A `ref` return is a variable, and a variable of another type is no
        // conversion at all: `ref Derived1 M2()` is a `RefFunc<…, Derived1>`
        // and nothing else.
        let delegate = self.delegate_within(delegate);
        let by_ref = delegate
            .symbol()
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())
            .is_some_and(|invoke| {
                let mut sink = Diagnostics::new();
                matches!(self.binder.type_of(invoke, &mut sink), Type::ByRef(_))
            });
        let mut sink = Diagnostics::new();
        let method_by_ref = matches!(self.binder.type_of(method, &mut sink), Type::ByRef(_));
        if by_ref != method_by_ref {
            return false;
        }
        if symbols
            .get(method)
            .as_method()
            .is_none_or(|detail| !detail.type_parameters.is_empty())
        {
            return true;
        }
        let mut sink = Diagnostics::new();
        let returns = self.binder.type_of(method, &mut sink);
        let returns = returns.value();
        if mentions_type_parameter(returns) || mentions_type_parameter(wanted) {
            return true;
        }
        match (returns, wanted) {
            (Type::Void, Type::Void) => true,
            (Type::Void, _) | (_, Type::Void) => false,
            (returns, wanted) if by_ref => {
                returns == wanted || returns.is_error() || wanted.is_error()
            }
            (returns, wanted) => {
                returns == wanted
                    || returns.is_error()
                    || wanted.is_error()
                    || (returns.is_reference_type(symbols)
                        && self.binder.converts_implicitly(returns, wanted))
            }
        }
    }

    /// Whether a lambda returns by reference exactly where the delegate it
    /// would become does: its expression body, or the first `return` of its
    /// block, is written `ref` or not.
    pub(super) fn lambda_ref_return_fits(&self, lambda: &BoundExpression, target: &Type) -> bool {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return true;
        };
        let Some(node) = self.syntax_at(span) else {
            return true;
        };
        let target = self.delegate_within(target);
        let symbols = self.binder.compilation().symbols();
        let Some(invoke) = target
            .symbol()
            .filter(|symbol| symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate))
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())
        else {
            return true;
        };
        let mut sink = Diagnostics::new();
        let wanted = matches!(self.binder.type_of(invoke, &mut sink), Type::ByRef(_));
        let arrow = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::EqualsGreaterThanToken)
            .map_or(span.start(), |token| token.span().end());
        let Some(body) = node.children().find(|child| child.span().start() >= arrow) else {
            return true;
        };
        let written = if body.kind() == SyntaxKind::Block {
            let returned = body
                .descendants()
                .filter(|statement| statement.kind() == SyntaxKind::ReturnStatement)
                .find(|statement| {
                    // Not a `return` of a lambda or local function inside.
                    !statement
                        .ancestors()
                        .take_while(|up| up.span() != body.span())
                        .any(|up| {
                            matches!(
                                up.kind(),
                                SyntaxKind::ParenthesizedLambdaExpression
                                    | SyntaxKind::SimpleLambdaExpression
                                    | SyntaxKind::AnonymousMethodExpression
                                    | SyntaxKind::LocalFunctionStatement
                            )
                        })
                });
            let Some(value) = returned.and_then(|statement| statement.children().next()) else {
                return true;
            };
            value.kind() == SyntaxKind::RefExpression
        } else {
            body.kind() == SyntaxKind::RefExpression
        };
        written == wanted
    }

    /// The lambda a lambda with no parameters returns, where that is all its
    /// body does: `() => () => 1`, or `() => { return async () => 0; }`.
    /// One with parameters is left alone, since the lambda inside may read
    /// them and has nothing to read them from on its own.
    pub(super) fn returned_lambdas(&self, lambda: &BoundExpression) -> Vec<BoundExpression> {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return Vec::new();
        };
        let Some(node) = self.syntax_at(span) else {
            return Vec::new();
        };
        if node
            .child_of_kind(SyntaxKind::ParameterList)
            .is_none_or(|list| {
                list.children()
                    .any(|child| child.kind() == SyntaxKind::Parameter)
            })
        {
            return Vec::new();
        }
        let Some(arrow) = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::EqualsGreaterThanToken)
            .map(|token| token.span().end())
        else {
            return Vec::new();
        };
        let Some(body) = node.children().find(|child| child.span().start() >= arrow) else {
            return Vec::new();
        };
        // Every value the body returns: the expression of an expression
        // body, or of each `return` in a block that is not inside a lambda
        // or a local function of its own.
        let returned: Vec<SyntaxNode> = if body.kind() == SyntaxKind::Block {
            let mut found = Vec::new();
            collect_returns(&body, &mut found);
            found
        } else {
            vec![body]
        };
        if returned.is_empty() {
            return Vec::new();
        }
        if !returned.iter().all(|returned| {
            matches!(
                returned.kind(),
                SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
            )
        }) {
            return Vec::new();
        }
        returned
            .iter()
            .map(|returned| {
                BoundExpression::new(
                    BoundExpressionKind::UnboundLambda(returned.span()),
                    Type::Error,
                    returned.span(),
                )
            })
            .collect()
    }

    /// Whether the lambda a lambda returns has, on its own, the result the
    /// delegate it would be returned as gives back; `None` where there is no
    /// such lambda, or it has no type of its own.
    pub(super) fn nested_lambda_matches(
        &mut self,
        lambda: &BoundExpression,
        target: &Type,
    ) -> Option<bool> {
        let inners = self.returned_lambdas(lambda);
        if inners.is_empty() {
            return None;
        }
        // Before C# 10 a lambda has no type of its own, and so neither has
        // the result of one that returns it.
        if !self.language_version().at_least(LanguageVersion::CSharp10) {
            return Some(false);
        }
        let wanted = self.delegate_signature(target)?.1;
        // An `async` lambda returns the lambda through its task.
        let wanted = if self.is_async_lambda(lambda) {
            self.task_result(&wanted)
        } else {
            wanted
        };
        let wanted = self.delegate_signature(&wanted)?.1;
        let mut matches = true;
        for inner in &inners {
            let BoundExpressionKind::UnboundLambda(span) = inner.kind else {
                return None;
            };
            let node = self.syntax_at(span)?;
            if node
                .child_of_kind(SyntaxKind::ParameterList)
                .is_none_or(|list| {
                    list.children()
                        .any(|child| child.kind() == SyntaxKind::Parameter)
                })
            {
                return None;
            }
            let parameters: Vec<DelegateParameter> = Vec::new();
            let given = match self.lambda_written_return(&node) {
                Some((written, _)) => written,
                None => self.inferred_lambda_return(inner, &parameters)?,
            };
            matches &= given == wanted;
        }
        Some(matches)
    }

    /// Reports a lambda parameter whose `ref` kind is not the one the
    /// delegate's parameter has.
    pub(super) fn check_lambda_parameter_ref(
        &mut self,
        parameter: &SyntaxNode,
        index: usize,
        wanted: Option<RefKind>,
    ) {
        let Some(wanted) = wanted else {
            return;
        };
        let written = written_ref_kind(parameter);
        if written == wanted {
            return;
        }
        let keyword = |kind: RefKind| match kind {
            RefKind::Ref => "ref",
            RefKind::Out => "out",
            RefKind::In => "in",
            RefKind::None => "",
        };
        let number = (index + 1).to_string();
        if written == RefKind::None {
            self.report(
                rustlyn_diagnostics::ErrorCode::ErrBadParamRef,
                parameter.span(),
                &[&number, keyword(wanted)],
            );
        } else {
            self.report(
                rustlyn_diagnostics::ErrorCode::ErrBadParamExtraRef,
                parameter.span(),
                &[&number, keyword(written)],
            );
        }
    }

    /// The type arguments written on a method group: the `<string>` of
    /// `F1<string>`.
    pub(super) fn group_type_arguments(&self, span: rustlyn_text::TextSpan) -> Vec<Type> {
        let Some(node) = self.syntax_at(span) else {
            return Vec::new();
        };
        let name = match node.kind() {
            SyntaxKind::GenericName => Some(node.clone()),
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression => node
                .children()
                .last()
                .filter(|child| child.kind() == SyntaxKind::GenericName),
            _ => None,
        };
        let Some(list) = name.and_then(|name| name.child_of_kind(SyntaxKind::TypeArgumentList))
        else {
            return Vec::new();
        };
        let context = self.binder.context_at(self.tree, &node);
        list.children()
            .filter(|child| child.kind().is_type_node())
            .map(|child| {
                let mut sink = Diagnostics::new();
                self.binder.resolve_type(&child, &context, &mut sink)
            })
            .collect()
    }
}

/// Whether two methods of a group have one signature, as far as a delegate
/// can tell: the types, the `ref` kinds and what they return.
fn same_signature(left: &DelegateSignature, right: &DelegateSignature) -> bool {
    left.returns == right.returns
        && left.returns_readonly == right.returns_readonly
        && left.parameters.len() == right.parameters.len()
        && left
            .parameters
            .iter()
            .zip(&right.parameters)
            .all(|(left, right)| {
                left.ty == right.ty
                    && left.ref_kind == right.ref_kind
                    && left.is_params == right.is_params
            })
}

/// The `ref` kinds of the parameters a delegate's `Invoke` takes.
pub(super) fn invoke_parameters_ref_kinds(
    symbols: &crate::symbol::Symbols,
    invoke: SymbolId,
) -> Vec<RefKind> {
    symbols
        .get(invoke)
        .as_method()
        .map(|detail| {
            detail
                .parameters
                .iter()
                .map(|parameter| {
                    symbols
                        .get(*parameter)
                        .as_parameter()
                        .map_or(RefKind::None, |detail| detail.ref_kind)
                })
                .collect()
        })
        .unwrap_or_default()
}

/// The `ref` kind a lambda parameter was written with.
pub(super) fn written_ref_kind(parameter: &SyntaxNode) -> RefKind {
    let mut kind = RefKind::None;
    for token in parameter.child_tokens() {
        match token.kind() {
            SyntaxKind::RefKeyword if kind == RefKind::None => kind = RefKind::Ref,
            SyntaxKind::OutKeyword => kind = RefKind::Out,
            SyntaxKind::InKeyword | SyntaxKind::ReadOnlyKeyword => kind = RefKind::In,
            _ => {}
        }
    }
    kind
}

/// Whether a parameter is written `ref readonly` rather than `in`.
pub(super) fn written_ref_readonly(parameter: &SyntaxNode) -> bool {
    let mut tokens = parameter.child_tokens().map(|token| token.kind());
    tokens.any(|kind| kind == SyntaxKind::RefKeyword)
        && tokens.any(|kind| kind == SyntaxKind::ReadOnlyKeyword)
}

/// Whether a type mentions a type parameter anywhere.
fn mentions_type_parameter(ty: &Type) -> bool {
    match ty {
        Type::TypeParameter(_) => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(mentions_type_parameter),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            mentions_type_parameter(element)
        }
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| mentions_type_parameter(&element.ty)),
        Type::FunctionPointer(pointer) => pointer.types().any(mentions_type_parameter),
        Type::Error | Type::Null | Type::Void | Type::Dynamic => false,
    }
}

/// Whether a parameter was written `scoped`.
fn is_scoped(parameter: &SyntaxNode) -> bool {
    parameter
        .child_tokens()
        .any(|token| token.kind() == SyntaxKind::ScopedKeyword)
        || parameter
            .children()
            .any(|child| child.kind() == SyntaxKind::ScopedType)
}

/// The expressions of the `return` statements in a block, leaving out the
/// ones of the lambdas and local functions inside it.
fn collect_returns(node: &SyntaxNode, found: &mut Vec<SyntaxNode>) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::ReturnStatement => {
                if let Some(value) = child.children().next() {
                    found.push(value);
                }
            }
            SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::LocalFunctionStatement => {}
            _ => collect_returns(&child, found),
        }
    }
}
