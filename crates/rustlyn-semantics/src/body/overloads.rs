//! Overload resolution (§12.6.4) and type inference (§12.6.3).

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::inference::InferenceArgument;
use super::{
    AddressOfGroup, Betterness, BodyBinder, Bound, BranchFunction, Evidence, Interpolated,
    Resolved, Shape, TupleLiteralElement, arity_fits, generality,
};
use crate::binder::Diagnostics;
use crate::bound::{BoundExpression, BoundExpressionKind, ConstantValue};
use crate::corlib::SpecialType;
use crate::symbol::{RefKind, SymbolId, Variance};
use crate::types::Type;

impl BodyBinder<'_> {
    /// Picks the overload whose parameters the arguments fit.
    ///
    /// Parameters are seen through the receiver, so `List<string>.Add` takes a
    /// `string` rather than the `T` it is declared with. Applicability comes
    /// first, then the candidate with the most exact matches — a
    /// simplification of §12.6.4 that gets the common cases right.
    pub(super) fn resolve_overload(
        &self,
        candidates: &[SymbolId],
        arguments: &[Type],
        evidence: &Evidence,
        receiver: &Type,
    ) -> Option<SymbolId> {
        self.resolve_call(candidates, arguments, evidence, receiver, &[])
            .map(|resolved| resolved.method)
    }

    /// Everything about a call's arguments that their types do not say.
    pub(super) fn evidence(&self, arguments: &[BoundExpression]) -> Evidence {
        Evidence {
            constants: self.constants_of(arguments),
            lambdas: self.lambda_arities(arguments),
            lambda_refs: arguments
                .iter()
                .map(|argument| match argument.kind {
                    BoundExpressionKind::UnboundLambda(span) => self.lambda_returns_ref(span),
                    _ => None,
                })
                .collect(),
            lambda_safe: arguments
                .iter()
                .map(|argument| match argument.kind {
                    BoundExpressionKind::UnboundLambda(span) => !self.in_unsafe_context(span),
                    _ => false,
                })
                .collect(),
            refs: arguments
                .iter()
                .map(|argument| match &argument.kind {
                    BoundExpressionKind::RefArgument { kind, .. } => *kind,
                    _ => RefKind::None,
                })
                .collect(),
            groups: arguments
                .iter()
                .map(|argument| matches!(argument.kind, BoundExpressionKind::MethodGroup { .. }))
                .collect(),
            group_methods: arguments
                .iter()
                .map(|argument| match &argument.kind {
                    BoundExpressionKind::MethodGroup { candidates, .. } => candidates.clone(),
                    _ => Vec::new(),
                })
                .collect(),
            group_closed: arguments
                .iter()
                .map(|argument| {
                    matches!(
                        &argument.kind,
                        BoundExpressionKind::MethodGroup {
                            receiver: Some(_),
                            ..
                        }
                    )
                })
                .collect(),
            interpolated: arguments
                .iter()
                .map(|argument| {
                    argument.is_interpolated_string().then(|| Interpolated {
                        lone: matches!(argument.kind, BoundExpressionKind::InterpolatedString(_)),
                        constant: self.binder.folded(argument).is_some(),
                    })
                })
                .collect(),
            branches: arguments
                .iter()
                .map(|argument| match argument.kind {
                    BoundExpressionKind::UnboundConditional(at)
                    | BoundExpressionKind::UnboundSwitch(at) => self.branch_types.get(&at).cloned(),
                    _ => None,
                })
                .collect(),
            functions: arguments
                .iter()
                .map(|argument| self.branch_functions(argument))
                .collect(),
            collections: arguments
                .iter()
                .map(|argument| self.written_as_collection(argument))
                .collect(),
            elements: arguments
                .iter()
                .map(|argument| match argument.kind {
                    BoundExpressionKind::UnboundCollection(at) => {
                        self.collection_types.get(&at).cloned()
                    }
                    _ => None,
                })
                .collect(),
            extension: false,
            natural: arguments
                .iter()
                .map(|argument| self.may_have_natural_type(argument))
                .collect(),
            natural_types: Vec::new(),
            tuples: arguments
                .iter()
                .map(|argument| self.tuple_literal_elements(argument))
                .collect(),
            arms: arguments
                .iter()
                .map(|argument| self.switch_arm_elements(argument))
                .collect(),
            inference: arguments
                .iter()
                .map(|argument| self.inference_argument(argument))
                .collect(),
            addresses: arguments
                .iter()
                .map(|argument| match &argument.kind {
                    BoundExpressionKind::AddressOf { operand } => match &operand.kind {
                        BoundExpressionKind::MethodGroup {
                            receiver,
                            candidates,
                        } => Some(AddressOfGroup {
                            candidates: candidates.clone(),
                            receiver: receiver.as_ref().map(|receiver| receiver.ty.clone()),
                            explicit: self.group_type_arguments(operand.span),
                        }),
                        _ => None,
                    },
                    _ => None,
                })
                .collect(),
        }
    }

    /// Whether the argument at `index`, where it is `&M`, reaches the
    /// parameter: only a function pointer whose signature one of the group's
    /// methods fits.
    fn address_reaches(
        &self,
        addresses: &[Option<AddressOfGroup>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        let Some(Some(group)) = addresses.get(index) else {
            return true;
        };
        let Type::FunctionPointer(signature) = parameter else {
            return false;
        };
        self.address_target(
            &group.candidates,
            group.receiver.as_ref(),
            &group.explicit,
            signature,
        )
        .is_some()
    }

    /// The elements of a tuple literal, for overload resolution.
    pub(super) fn tuple_literal_elements(
        &self,
        argument: &BoundExpression,
    ) -> Option<Vec<TupleLiteralElement>> {
        let BoundExpressionKind::TupleCreation(values) = &argument.kind else {
            return None;
        };
        Some(
            values
                .iter()
                .map(|value| TupleLiteralElement {
                    ty: value.ty.clone(),
                    constant: self.binder.folded(value),
                    nested: self.tuple_literal_elements(value),
                    interpolated: value.is_interpolated_string().then(|| Interpolated {
                        lone: matches!(value.kind, BoundExpressionKind::InterpolatedString(_)),
                        constant: self.binder.folded(value).is_some(),
                    }),
                })
                .collect(),
        )
    }

    /// Whether a tuple literal reaches a parameter element by element
    /// (§10.2.13), each element by its type or as the constant it is; a
    /// `T?` of a tuple is reached by reaching the `T`.
    pub(super) fn tuple_literal_reaches(
        &self,
        elements: &[TupleLiteralElement],
        parameter: &Type,
    ) -> bool {
        let inner = self
            .binder
            .nullable_underlying(parameter)
            .unwrap_or_else(|| parameter.clone());
        let Some(wanted) = self.flat_tuple_element_types(&inner) else {
            return false;
        };
        wanted.len() == elements.len()
            && elements
                .iter()
                .zip(&wanted)
                .all(|(element, wanted)| self.element_reaches(element, wanted))
    }

    /// Whether one element of a tuple literal, or one arm of a `switch`,
    /// reaches a type: by its type, as the constant it is, as a tuple
    /// literal itself, or as an interpolated string.
    fn element_reaches(&self, element: &TupleLiteralElement, wanted: &Type) -> bool {
        self.binder.converts_implicitly(&element.ty, wanted)
            || element
                .constant
                .as_ref()
                .is_some_and(|constant| self.constant_reaches(constant, &element.ty, wanted))
            || element
                .nested
                .as_ref()
                .is_some_and(|nested| self.tuple_literal_reaches(nested, wanted))
            || self.interpolated_reaches(&[element.interpolated], 0, wanted)
    }

    /// The arms of a `switch` expression that has a type of its own, for
    /// overload resolution.
    fn switch_arm_elements(&self, argument: &BoundExpression) -> Option<Vec<TupleLiteralElement>> {
        let BoundExpressionKind::Switch { arms, .. } = &argument.kind else {
            return None;
        };
        if argument.ty.is_error() {
            return None;
        }
        Some(
            arms.iter()
                .map(|arm| TupleLiteralElement {
                    ty: arm.value.ty.clone(),
                    constant: self.binder.folded(&arm.value),
                    nested: self.tuple_literal_elements(&arm.value),
                    interpolated: arm.value.is_interpolated_string().then(|| Interpolated {
                        lone: matches!(arm.value.kind, BoundExpressionKind::InterpolatedString(_)),
                        constant: self.binder.folded(&arm.value).is_some(),
                    }),
                })
                .collect(),
        )
    }

    /// Whether the argument at `index` is a `switch` whose every arm
    /// reaches the parameter.
    fn arms_at(
        &self,
        arms: &[Option<Vec<TupleLiteralElement>>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        arms.get(index)
            .and_then(Option::as_ref)
            .is_some_and(|arms| {
                !arms.is_empty()
                    && arms
                        .iter()
                        .all(|arm| arm.ty.is_error() || self.element_reaches(arm, parameter))
            })
    }

    /// Whether the argument at `index` is a tuple literal the parameter
    /// takes.
    fn tuple_at(
        &self,
        tuples: &[Option<Vec<TupleLiteralElement>>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        tuples
            .get(index)
            .and_then(Option::as_ref)
            .is_some_and(|elements| {
                self.tuple_literal_reaches(elements, parameter)
                    || self
                        .tuple_literal_operator_of(elements, parameter)
                        .is_some()
            })
    }

    /// The same, for a call whose first argument is an extension receiver.
    /// Whether an argument is a collection expression, or a conditional
    /// whose branches are: `rightOpt is null ? [] : [rightOpt]` has no type
    /// yet either, and is no more one element of a `params` array than `[]`
    /// alone would be.
    fn written_as_collection(&self, argument: &BoundExpression) -> bool {
        match argument.kind {
            BoundExpressionKind::UnboundCollection(_) => true,
            BoundExpressionKind::UnboundConditional(span) => self
                .binder
                .tree_root(self.tree)
                .and_then(|root| root.find_node(span))
                .is_some_and(|node| branches_are_collections(&node)),
            _ => false,
        }
    }

    pub(super) fn evidence_for(&self, arguments: &[BoundExpression], extension: bool) -> Evidence {
        let mut evidence = self.evidence(arguments);
        evidence.extension = extension;
        evidence
    }

    /// What each argument folds to, for the arguments that fold to anything.
    fn constants_of(&self, arguments: &[BoundExpression]) -> Vec<Option<ConstantValue>> {
        arguments
            .iter()
            .map(|argument| self.binder.folded(argument))
            .collect()
    }

    /// The lambdas and method groups among the branches of a conditional
    /// argument, nested ones included; empty for anything else.
    fn branch_functions(&self, argument: &BoundExpression) -> Vec<BranchFunction> {
        let mut found = Vec::new();
        match &argument.kind {
            BoundExpressionKind::Conditional {
                consequence,
                alternative,
                ..
            } if argument.ty.is_error() => {
                for branch in [consequence, alternative] {
                    match &branch.kind {
                        BoundExpressionKind::UnboundLambda(span) => {
                            found.push(BranchFunction::Lambda(self.lambda_arity(*span)));
                        }
                        BoundExpressionKind::MethodGroup {
                            receiver,
                            candidates,
                        } => found.push(BranchFunction::Group(
                            candidates.clone(),
                            receiver.is_some(),
                        )),
                        _ => found.extend(self.branch_functions(branch)),
                    }
                }
            }
            // Two lambdas wait unbound, and are read off the syntax.
            BoundExpressionKind::UnboundConditional(span) => {
                let node = self
                    .binder
                    .tree_root(self.tree)
                    .and_then(|root| root.find_node(*span));
                for branch in node.iter().flat_map(|node| node.children().skip(1)) {
                    if matches!(
                        branch.kind(),
                        SyntaxKind::SimpleLambdaExpression
                            | SyntaxKind::ParenthesizedLambdaExpression
                            | SyntaxKind::AnonymousMethodExpression
                    ) {
                        found.push(BranchFunction::Lambda(self.lambda_arity(branch.span())));
                    }
                }
            }
            _ => {}
        }
        found
    }

    /// Whether every lambda and method group among a conditional argument's
    /// branches could become the parameter.
    fn functions_fit(
        &self,
        functions: &[Vec<BranchFunction>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        let symbols = self.binder.compilation().symbols();
        functions.get(index).is_none_or(|branches| {
            branches.iter().all(|branch| match branch {
                BranchFunction::Lambda(arity) => {
                    self.takes_a_function_here(parameter) && arity_fits(*arity, parameter, symbols)
                }
                BranchFunction::Group(methods, closed) => {
                    self.group_fits(methods, *closed, parameter)
                }
            })
        })
    }

    /// How many parameters each argument that is a lambda was written with.
    ///
    /// `None` for anything that is not a lambda, and for one whose syntax does
    /// not say. A lambda has no type of its own, so counting is all overload
    /// resolution has to tell two delegates apart.
    fn lambda_arities(&self, arguments: &[BoundExpression]) -> Vec<Option<usize>> {
        arguments
            .iter()
            .map(|argument| match argument.kind {
                BoundExpressionKind::UnboundLambda(span) => self.lambda_arity(span),
                _ => None,
            })
            .collect()
    }

    /// Whether the argument at `index` is a constant the parameter accepts.
    ///
    /// The list is as long as the call's arguments where the caller had the
    /// bound expressions to fold, and empty where it had only their types.
    fn constant_at(
        &self,
        constants: &[Option<ConstantValue>],
        index: usize,
        argument: &Type,
        parameter: &Type,
    ) -> bool {
        constants
            .get(index)
            .and_then(Option::as_ref)
            .is_some_and(|constant| self.constant_reaches(constant, argument, parameter))
    }

    /// Whether every branch of a typeless conditional or `switch` argument
    /// reaches the parameter; true for any other argument.
    /// Whether every plain element of a collection expression converts to
    /// what the candidate's collection holds: `Join(", ", [1, 2])` is not
    /// the `params string[]` form, whatever else it might be.
    fn elements_reach(
        &self,
        elements: &[Option<Vec<Type>>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        let Some(Some(types)) = elements.get(index) else {
            return true;
        };
        let Some(element) = self.collection_element(parameter) else {
            return true;
        };
        let symbols = self.binder.compilation().symbols();
        types.iter().all(|ty| {
            ty.is_error()
                || (matches!(ty, Type::Null)
                    && (element.is_reference_type(symbols)
                        || self.binder.nullable_underlying(&element).is_some()))
                || self.binder.converts_implicitly(ty, &element)
        })
    }

    fn branches_reach(
        &self,
        branches: &[Option<Vec<Type>>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        let Some(Some(types)) = branches.get(index) else {
            return true;
        };
        let symbols = self.binder.compilation().symbols();
        types.iter().all(|ty| {
            ty.is_error()
                || (matches!(ty, Type::Null)
                    && (parameter.is_reference_type(symbols)
                        || self.binder.nullable_underlying(parameter).is_some()))
                || self.binder.converts_implicitly(ty, parameter)
        })
    }

    /// Says why no overload took these arguments.
    ///
    /// "No overload takes two arguments" is the right thing to say when none
    /// of them takes two; where one does and an argument is the wrong type,
    /// saying which argument and which two types is the difference between a
    /// diagnostic you can act on and one you have to go and work out.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn report_no_overload(
        &mut self,
        candidates: &[SymbolId],
        name: &str,
        arguments: &[Type],
        argument_spans: &[TextSpan],
        receiver: &Type,
        explicit: &[Type],
        at: TextSpan,
        constructor_of: Option<&Type>,
    ) {
        // Among the ones that could take this many, the one that got furthest
        // before an argument stopped it: that is the overload the call was
        // most likely aimed at.
        let mismatch = candidates
            .iter()
            .filter_map(|candidate| {
                let shape = self.candidate_shape(*candidate, arguments, receiver, explicit, &[])?;
                if arguments.len() < shape.required || arguments.len() > shape.parameters.len() {
                    return None;
                }
                arguments
                    .iter()
                    .zip(&shape.parameters)
                    .position(|(argument, parameter)| {
                        !self.binder.converts_implicitly(argument, parameter)
                    })
                    .map(|at| (at, arguments[at].clone(), shape.parameters[at].clone()))
            })
            .max_by_key(|(at, _, _)| *at);
        if let Some((index, from, to)) = mismatch {
            let (position, from, to) = (
                (index + 1).to_string(),
                self.display(&from),
                self.display(&to),
            );
            // Roslyn puts it on the argument that does not convert.
            let place = argument_spans.get(index).copied().unwrap_or(at);
            self.report(ErrorCode::ErrBadArgType, place, &[&position, &from, &to]);
            return;
        }
        let symbols = self.binder.compilation().symbols();
        // How many arguments each candidate takes, as declared: the ones
        // without a default, and all of them unless the last is `params`.
        let counts: Vec<(SymbolId, usize, Option<usize>)> = candidates
            .iter()
            .filter_map(|candidate| {
                let detail = symbols.get(*candidate).as_method()?;
                let parameters: Vec<_> = detail
                    .parameters
                    .iter()
                    .filter_map(|parameter| symbols.get(*parameter).as_parameter())
                    .collect();
                let required = parameters
                    .iter()
                    .filter(|parameter| !parameter.has_default && !parameter.is_params)
                    .count();
                let most = (!parameters.iter().any(|parameter| parameter.is_params))
                    .then_some(parameters.len());
                Some((*candidate, required, most))
            })
            .collect();
        let fitting: Vec<SymbolId> = counts
            .iter()
            .filter(|(_, required, most)| {
                arguments.len() >= *required && most.is_none_or(|most| arguments.len() <= most)
            })
            .map(|(candidate, _, _)| *candidate)
            .collect();
        if !fitting.is_empty() {
            // Something takes this many, and it is not the count that is
            // wrong. Where every such candidate is generic and nothing said
            // what its type arguments are, it is inference that failed
            // (CS0411); otherwise an argument this binder could not type, and
            // better silent than wrong.
            let inferred_nothing = explicit.is_empty()
                && fitting.iter().all(|candidate| {
                    symbols
                        .get(*candidate)
                        .as_method()
                        .is_some_and(|detail| !detail.type_parameters.is_empty())
                        && self
                            .candidate_shape(*candidate, arguments, receiver, explicit, &[])
                            .is_none()
                });
            if inferred_nothing && !arguments.iter().any(Type::is_error) {
                let frame = self.substitution_for(fitting[0], receiver);
                let member = crate::checks::member_display(
                    self.binder.compilation(),
                    fitting[0],
                    &frame,
                    None,
                );
                self.report(ErrorCode::ErrCantInferMethTypeArgs, at, &[&member]);
            }
            return;
        }
        // One candidate, called with too few: which parameter has nothing.
        if let [(candidate, required, _)] = counts.as_slice()
            && arguments.len() < *required
            && let Some(parameter) = symbols
                .get(*candidate)
                .as_method()
                .and_then(|detail| detail.parameters.get(arguments.len()))
        {
            let parameter_name = symbols.get(*parameter).name.clone();
            let frame = self.substitution_for(*candidate, receiver);
            let member =
                crate::checks::member_display(self.binder.compilation(), *candidate, &frame, None);
            self.report(
                ErrorCode::ErrNoCorrespondingArgument,
                at,
                &[&parameter_name, &member],
            );
            return;
        }
        // An overload that does take this many, and that this code may not
        // call, is the one the call names (CS0122): `stream.Dispose(true)`
        // outside a `Stream` is not a `Dispose()` given one too many.
        if constructor_of.is_none()
            && let Some(hidden) = self.inaccessible_overload(receiver, name, arguments.len())
        {
            let display = crate::checks::member_display(
                self.binder.compilation(),
                hidden,
                &Default::default(),
                None,
            );
            self.report(ErrorCode::ErrBadAccess, at, &[&display]);
            return;
        }
        let count = arguments.len().to_string();
        match constructor_of {
            Some(ty) => {
                let ty = self.display(ty);
                self.report(ErrorCode::ErrBadCtorArgCount, at, &[&ty, &count]);
            }
            None => self.report(ErrorCode::ErrBadArgCount, at, &[name, &count]),
        }
    }

    /// A method called `name` on `receiver` or a class it derives from that
    /// takes `count` arguments and that the code here may not call.
    fn inaccessible_overload(&self, receiver: &Type, name: &str, count: usize) -> Option<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let mut current = receiver.symbol();
        let mut depth = 0;
        while let Some(ty) = current {
            let found = symbols.lookup(ty, name).iter().copied().find(|member| {
                symbols.get(*member).as_method().is_some_and(|detail| {
                    let parameters: Vec<_> = detail
                        .parameters
                        .iter()
                        .filter_map(|parameter| symbols.get(*parameter).as_parameter())
                        .collect();
                    let required = parameters
                        .iter()
                        .filter(|parameter| !parameter.has_default && !parameter.is_params)
                        .count();
                    let unbounded = parameters.iter().any(|parameter| parameter.is_params);
                    count >= required && (unbounded || count <= parameters.len())
                }) && !self.accessible(*member)
            });
            if found.is_some() || depth > 32 {
                return found;
            }
            current = self.binder.base_class_of(ty).and_then(|base| base.symbol());
            depth += 1;
        }
        None
    }

    /// The order a candidate's parameters are in as the call's arguments
    /// reach them, where names put the arguments out of declaration order:
    /// the parameter each argument goes to, then the ones none does, as
    /// declared. `Bar(x: 1, y: "")` reaches `Bar(string y, int x)` as
    /// `(int x, string y)`, and is compared with `Bar(int x, string y)` so.
    /// `None` where the order is the declared one, or no names are in play.
    pub(super) fn parameter_order(&self, candidate: SymbolId, count: usize) -> Option<Vec<usize>> {
        let order = {
            let stack = self.argument_names.borrow();
            let (candidates, names) = stack.last()?;
            if names.len() != count || !candidates.contains(&candidate) {
                return None;
            }
            self.named_order(candidate, names)?
        };
        (!order.iter().enumerate().all(|(at, index)| at == *index)).then_some(order)
    }

    /// The parameter of a candidate each named or positional argument goes
    /// to, followed by the parameters no argument does; `None` where the
    /// names cannot be read that way.
    pub(super) fn named_order(
        &self,
        candidate: SymbolId,
        names: &[Option<String>],
    ) -> Option<Vec<usize>> {
        let symbols = self.binder.compilation().symbols();
        let parameters = super::member_parameters(symbols, candidate)?;
        let mut order = Vec::with_capacity(parameters.len());
        for (position, name) in names.iter().enumerate() {
            let index = match name {
                Some(name) => parameters
                    .iter()
                    .position(|parameter| super::call_name(symbols, *parameter) == name)?,
                None => position,
            };
            if index >= parameters.len() || order.contains(&index) {
                return None;
            }
            order.push(index);
        }
        // A `params` parameter stays last, where its expanded form is.
        let last = parameters.len().checked_sub(1);
        if let Some(last) = last
            && symbols
                .get(parameters[last])
                .as_parameter()
                .is_some_and(|parameter| parameter.is_params)
            && order
                .iter()
                .position(|index| *index == last)
                .is_some_and(|at| at + 1 != parameters.len())
        {
            return None;
        }
        let rest: Vec<usize> = (0..parameters.len())
            .filter(|index| !order.contains(index))
            .collect();
        order.extend(rest);
        Some(order)
    }

    /// A candidate seen through the call it is a candidate for.
    ///
    /// The receiver says what the declaring type's parameters are, and the
    /// arguments say what the method's own are, so the parameter types a
    /// candidate *has here* are neither what it was declared with nor the
    /// same for two calls. `None` where the call cannot be made at all: the
    /// wrong number of type arguments, or a type parameter nothing settles.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn candidate_shape(
        &self,
        candidate: SymbolId,
        arguments: &[Type],
        receiver: &Type,
        explicit: &[Type],
        inference: &[InferenceArgument],
    ) -> Option<Shape> {
        let symbols = self.binder.compilation().symbols();
        // An indexer is a candidate as a method is, with no type parameters.
        let mut member_parameters: Vec<SymbolId> =
            super::member_parameters(symbols, candidate)?.to_vec();
        if let Some(order) = self.parameter_order(candidate, arguments.len()) {
            member_parameters = order
                .iter()
                .map(|index| member_parameters[*index])
                .collect();
        }
        let method_type_parameters: Vec<SymbolId> = symbols
            .get(candidate)
            .as_method()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        // Each candidate may be declared on a different type, and the
        // receiver says what that type's parameters are.
        let substitution = self.substitution_for(candidate, receiver);
        let declared: Vec<Type> = member_parameters
            .iter()
            .map(|id| {
                let mut sink = Diagnostics::new();
                self.binder
                    .type_of(*id, &mut sink)
                    .substitute(&substitution)
            })
            .collect();
        let type_parameters = method_type_parameters;
        let mut from_function = false;
        // Explicit type arguments settle it; otherwise each parameter is
        // matched against its argument until every one is accounted for.
        let method_substitution = if type_parameters.is_empty() {
            // `Allocate<MemberDeclarationSyntax>()` is not a call to the
            // `Allocate()` beside it: writing type arguments rules out every
            // candidate that has none to take.
            if !explicit.is_empty() {
                return None;
            }
            HashMap::new()
        } else if explicit.is_empty() {
            let inference: Vec<InferenceArgument> = if inference.len() == arguments.len() {
                inference.to_vec()
            } else {
                arguments
                    .iter()
                    .map(|argument| {
                        if argument.is_error() || matches!(argument, Type::Null | Type::Void) {
                            InferenceArgument::Untyped
                        } else {
                            InferenceArgument::Typed(argument.clone())
                        }
                    })
                    .collect()
            };
            let by_ref: Vec<bool> = member_parameters
                .iter()
                .map(|id| {
                    symbols.get(*id).as_parameter().is_some_and(|parameter| {
                        // An `in` parameter takes a value as readily as
                        // a variable, and infers from it as from one.
                        matches!(parameter.ref_kind, RefKind::Ref | RefKind::Out)
                    })
                })
                .collect();
            // The normal form first, and where that infers nothing the
            // expanded one: `Create(3, 7, 11)` hands its arguments one by one
            // to the element of a `params T[]` (§12.6.4.2).
            let found = self
                .infer_type_arguments(&type_parameters, &declared, &by_ref, &inference)
                .or_else(|| {
                    let element = self.params_element(candidate, &declared)?;
                    let fixed = declared.len().checked_sub(1)?;
                    if arguments.len() < fixed {
                        return None;
                    }
                    let mut expanded = declared[..fixed].to_vec();
                    expanded.resize(arguments.len().max(fixed), element);
                    let mut by_ref = by_ref[..fixed].to_vec();
                    by_ref.resize(expanded.len(), false);
                    self.infer_type_arguments(&type_parameters, &expanded, &by_ref, &inference)
                });
            let (mut inferred, function) = found?;
            from_function = function;
            if function {
                self.infer_expression_trees(&type_parameters, &substitution, &mut inferred);
            }
            // §12.6.4.2: a candidate whose inferred type arguments break
            // its constraints is not applicable. `Hash.Combine(ch, hash)`
            // on a `char` is the `Combine(int, int)` overload, not the
            // `Combine<T>(T, int) where T : class` beside it.
            if !self.satisfies_constraints(&type_parameters, &inferred) {
                return None;
            }
            inferred
        } else {
            if explicit.len() != type_parameters.len() {
                return None;
            }
            type_parameters
                .iter()
                .copied()
                .zip(explicit.iter().cloned())
                .collect()
        };
        // A varargs method takes one more argument than it has parameters:
        // the `__arglist(...)`, which nothing else takes (§II.23.2.2).
        let vararg = symbols
            .get(candidate)
            .as_method()
            .is_some_and(|detail| detail.is_vararg);
        Some(Shape {
            parameters: declared
                .iter()
                .map(|ty| ty.substitute(&method_substitution))
                .chain(vararg.then_some(Type::Void))
                .collect(),
            ref_kinds: member_parameters
                .iter()
                .map(|id| {
                    symbols
                        .get(*id)
                        .as_parameter()
                        .map_or(RefKind::None, |parameter| parameter.ref_kind)
                })
                .chain(vararg.then_some(RefKind::None))
                .collect(),
            type_arguments: type_parameters
                .iter()
                .map(|parameter| {
                    method_substitution
                        .get(parameter)
                        .cloned()
                        .unwrap_or(Type::Error)
                })
                .collect(),
            substitution: method_substitution,
            required: member_parameters
                .iter()
                .filter(|id| {
                    !symbols
                        .get(**id)
                        .as_parameter()
                        .is_some_and(|parameter| parameter.has_default || parameter.is_params)
                })
                .count()
                + usize::from(vararg),
            // Read off the declaration as written, where the type's own
            // parameters count as much as the method's: `C<S>(params
            // Func<Bar, S>[])` is less specific than `C(params Func<Bar,
            // Wrapper<int>>[])` even when `S` is `Wrapper<int>` (§12.6.4.5).
            generality: member_parameters
                .iter()
                .map(|id| {
                    let mut sink = Diagnostics::new();
                    let written = self.binder.type_of(*id, &mut sink);
                    let mut all = type_parameters.clone();
                    collect_type_parameters(&written, &mut all);
                    generality(&written, &all, 0)
                })
                .sum(),
            from_function,
        })
    }

    /// Whether inferred type arguments meet their parameters' constraints.
    ///
    /// Only what can be decided is decided: an argument that is itself a
    /// type parameter, or a constraint that still mentions one, is taken as
    /// satisfied, and only `class`, `struct` and the named constraints are
    /// checked.
    pub(super) fn satisfies_constraints(
        &self,
        parameters: &[SymbolId],
        inferred: &HashMap<SymbolId, Type>,
    ) -> bool {
        // A `ref struct` is no type argument (§8.8) unless the parameter
        // says `allows ref struct` (C# 13): `Write<T>(…, T)` is not
        // applicable to a `Span<object>`, whatever it would infer.
        let symbols = self.binder.compilation().symbols();
        let ref_like = |argument: &Type| {
            argument.symbol().is_some_and(|symbol| {
                symbols
                    .get(symbol)
                    .as_named_type()
                    .is_some_and(|detail| detail.ref_like)
            })
        };
        // Nor is a pointer (CS0306): `M<T>(T)` handed an `int*` is no
        // candidate, and a better one may take it by a conversion.
        if inferred
            .values()
            .any(|argument| matches!(argument, Type::Pointer(_) | Type::FunctionPointer(_)))
        {
            return false;
        }
        if inferred.iter().any(|(parameter, argument)| {
            ref_like(argument)
                && !symbols
                    .get(*parameter)
                    .as_type_parameter()
                    .is_some_and(|detail| detail.allows_ref_struct)
        }) {
            return false;
        }
        parameters.iter().all(|parameter| {
            let Some(argument) = inferred.get(parameter) else {
                return true;
            };
            // `ref collection` infers through the reference to what it
            // refers to.
            let argument = argument.value();
            if argument.is_error() || matches!(argument, Type::TypeParameter(_) | Type::Null) {
                return true;
            }
            let Some(detail) = symbols.get(*parameter).as_type_parameter() else {
                return true;
            };
            if detail.reference_type && !argument.is_reference_type(symbols) {
                return false;
            }
            if detail.value_type
                && (argument.is_reference_type(symbols)
                    || self.binder.nullable_underlying(argument).is_some())
            {
                return false;
            }
            self.binder
                .base_types_of(*parameter)
                .iter()
                .all(|constraint| {
                    let constraint = constraint.substitute(inferred);
                    constraint.is_error()
                        || matches!(constraint, Type::TypeParameter(_))
                        || mentions_any(&constraint, parameters)
                        || mentions_a_type_parameter(&constraint)
                        || self.binder.converts_implicitly(argument, &constraint)
                        // A `ref struct` does not box: it meets an interface
                        // constraint by implementing the interface.
                        || (ref_like(argument) && self.implements(argument, &constraint))
                })
        })
    }

    /// Whether a type lists an interface among its bases, directly or not.
    fn implements(&self, ty: &Type, interface: &Type) -> bool {
        let mut pending = vec![ty.clone()];
        let mut seen: Vec<Type> = Vec::new();
        while let Some(next) = pending.pop() {
            if next == *interface {
                return true;
            }
            if seen.contains(&next) || seen.len() > 64 {
                continue;
            }
            pending.extend(self.binder.direct_bases(&next));
            seen.push(next);
        }
        false
    }

    /// Picks an overload and works out what its type parameters stand for.
    ///
    /// A generic method is where overload resolution stops being a lookup:
    /// `Echo(3)` has to *infer* that `T` is `int` before it can tell whether
    /// the call is even applicable, and the answer has to survive into the
    /// bound tree, because a `MethodSpec` is exactly that list of types.
    /// Whether a member may be named from here: a private one belongs to
    /// its own type and to the types nested in it, and a protected one to
    /// those and the types derived from its own — `new A(1)` from outside
    /// `A` does not reach its `protected A(int)`.
    pub(super) fn can_reach(&self, candidate: SymbolId) -> bool {
        self.accessible(candidate)
    }

    /// Whether an extension method's receiver may be passed as its `this`
    /// parameter: a value type goes only to itself or, boxed, to a reference
    /// type — never through a numeric, enumeration or nullable conversion.
    pub(super) fn receiver_converts(&self, given: &Type, taken: &Type) -> bool {
        let taken = match taken {
            Type::ByRef(inner) => inner,
            other => other,
        };
        if given == taken {
            return true;
        }
        // `array.M()` reaches `M(this ReadOnlySpan<T>)` through an implicit
        // span conversion, which C# 14 made one of the receiver's.
        if self.binder.first_class_spans() && self.binder.implicit_span_conversion(given, taken) {
            return true;
        }
        let symbols = self.binder.compilation().symbols();
        let is_value = |ty: &Type| {
            !matches!(ty, Type::TypeParameter(_) | Type::Error | Type::Null)
                && !ty.is_reference_type(symbols)
        };
        let known = |ty: &Type| !matches!(ty, Type::TypeParameter(_) | Type::Error | Type::Null);
        // A reference reaches a value type by none of those: only a
        // user-defined conversion would take an array to a span.
        if known(given) && !is_value(given) && is_value(taken) {
            return false;
        }
        if !is_value(given) || !is_value(taken) {
            return true;
        }
        self.binder.special_of(given).is_none()
            && self.binder.enum_underlying(given).is_none()
            && self.binder.nullable_underlying(taken).is_none()
    }

    pub(super) fn resolve_call(
        &self,
        candidates: &[SymbolId],
        arguments: &[Type],
        evidence: &Evidence,
        receiver: &Type,
        explicit: &[Type],
    ) -> Option<Resolved> {
        let Evidence {
            constants,
            lambdas,
            lambda_refs,
            lambda_safe,
            refs,
            groups,
            group_methods,
            group_closed,
            interpolated,
            collections,
            elements,
            branches,
            functions,
            extension,
            natural,
            natural_types,
            tuples,
            arms,
            inference,
            addresses,
        } = evidence;
        // A lambda or a method group handed to a bare `T` infers `T` from its
        // natural type, where the caller worked one out.
        let inference: Vec<InferenceArgument> = inference
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                with_natural(argument, natural_types.get(index).cloned().flatten())
            })
            .collect();
        let symbols = self.binder.compilation().symbols();
        let ref_to_in = self.language_version().at_least(LanguageVersion::CSharp12);
        // Every candidate the arguments fit, with how well: a form that takes
        // them as written beats one that has to make an array out of them,
        // whatever either scores on exact matches. That is why
        // `Join(",", array)` passes the array rather than wrapping it.
        let mut applicable_set: Vec<(Betterness, Vec<Type>, Resolved)> = Vec::new();

        // §12.6.4.1: a member that cannot be named here is not a candidate.
        // `test.Equals(other)` from another class reaches the public
        // `Equals(object)` and not the private `Equals(BoundDagTest)` beside
        // it. Where nothing is reachable the set stands, and the error is
        // reported on the call rather than on a member that is not there.
        let reachable: Vec<SymbolId> = candidates
            .iter()
            .copied()
            .filter(|candidate| self.can_reach(*candidate))
            .collect();
        let candidates = if reachable.is_empty() {
            candidates
        } else {
            reachable.as_slice()
        };

        // A lambda or a method group handed to a bare `T` infers `T` from the
        // type it has on its own (C# 10): the arguments inference reads are
        // those types where there are any.
        let inferring: Vec<Type> = arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| match natural_types.get(index) {
                Some(Some(natural)) => natural.clone(),
                _ => argument.clone(),
            })
            .collect();
        for candidate in candidates {
            let Some(shape) =
                self.candidate_shape(*candidate, &inferring, receiver, explicit, &inference)
            else {
                continue;
            };
            let Shape {
                parameters,
                ref_kinds,
                type_arguments,
                substitution: method_substitution,
                required,
                generality,
                from_function,
            } = shape;
            // `ref` and `out` have to be written at the call site, so an
            // overload that takes one is not a candidate for a call that did
            // not write it — nor the other way round.
            // A method of a `[ComImport]` type may be handed a value where
            // it takes a `ref`: the call passes a copy (Roslyn's "omit ref").
            let omits_refs = self.omits_refs(*candidate);
            let mut ref_omitted = false;
            let mut refs_fit = true;
            for (index, written) in refs.iter().enumerate() {
                // `builder.AddIfNotNull(x)` reaches a `this ref
                // TemporaryArray<T>`: the receiver of an extension call goes
                // by reference without a `ref` at the call.
                let is_extension_receiver = index == 0 && *extension;
                let declared = ref_kinds.get(index).copied();
                if is_extension_receiver || ref_fits(*written, declared, ref_to_in) {
                    continue;
                }
                if omits_refs && *written == RefKind::None && declared == Some(RefKind::Ref) {
                    ref_omitted = true;
                    continue;
                }
                // `sb.Append($"{x}")` reaches `Append(ref AppendInterpolated
                // StringHandler)`: an interpolated string goes to a handler
                // struct's `ref` without one (C# 10), the handler made for
                // it being the variable.
                if *written == RefKind::None
                    && declared == Some(RefKind::Ref)
                    && interpolated.get(index).copied().flatten().is_some()
                    && parameters.get(index).is_some_and(|parameter| {
                        self.is_handler_type(parameter)
                            && !parameter.is_reference_type(self.binder.compilation().symbols())
                    })
                {
                    continue;
                }
                refs_fit = false;
                break;
            }
            if !refs_fit {
                continue;
            }
            // The receiver of an extension method reaches its `this`
            // parameter only by identity, reference or boxing (§12.8.10.3):
            // `0.Goo()` is not `Goo(this long)`, and a `DayOfWeek` is not
            // the `int` beneath it.
            if *extension
                && let (Some(given), Some(taken)) = (arguments.first(), parameters.first())
                && !self.receiver_converts(given, taken)
            {
                continue;
            }
            if arguments.len() < required {
                continue;
            }

            let mut exact = 0;
            let mut normal = true;
            let mut compared = parameters.clone();
            let applicable = arguments.len() <= parameters.len()
                && arguments.iter().zip(&parameters).enumerate().all(
                    |(index, (argument, parameter))| {
                        // An `__arglist(...)` goes to a varargs method's
                        // extra parameter and nowhere else.
                        if matches!(argument, Type::Void) != matches!(parameter, Type::Void) {
                            return false;
                        }
                        // A variable written `ref`, `out` or `in` is passed as
                        // itself, and only a parameter of its very type takes
                        // it (§12.6.4.2).
                        if refs.get(index).is_some_and(|kind| *kind != RefKind::None)
                            && !argument.is_error()
                            && !parameter.is_error()
                            && !self.identical(argument, parameter)
                            && !matches!(parameter, Type::TypeParameter(_))
                        {
                            return false;
                        }
                        if argument == parameter {
                            exact += 1;
                        }
                        // The receiver of an extension call converts only by
                        // identity, reference or boxing (§12.8.10.3): an
                        // interpolated string does not become the
                        // `FormattableString` a `this` parameter takes.
                        let receiver = *extension && index == 0;
                        // Nor does it widen as a number or wrap into a `T?`:
                        // `0.Goo()` does not reach `Goo(this long)`.
                        let symbols = self.binder.compilation().symbols();
                        if receiver
                            && argument != parameter
                            && !argument.is_error()
                            && !parameter.is_reference_type(symbols)
                            && !matches!(parameter, Type::TypeParameter(_))
                            && !matches!(argument, Type::TypeParameter(_))
                            && !argument.is_reference_type(symbols)
                            && !matches!(
                                argument,
                                Type::Null | Type::Array { .. } | Type::Pointer(_) | Type::Tuple(_)
                            )
                            // `foreach` over an `int?` asks with the `int`
                            // inside, and its extension takes the `int?`.
                            && self.binder.nullable_underlying(parameter).as_ref() != Some(argument)
                            // A tuple however it is spelled converts
                            // element by element.
                            && self.tuple_element_types(argument).is_none()
                            // A `Span<T>` reaches a `ReadOnlySpan<T>`
                            // receiver by an implicit span conversion (C# 14).
                            && !(self.binder.first_class_spans()
                                && self.binder.implicit_span_conversion(argument, parameter))
                        {
                            return false;
                        }
                        (self.binder.converts_implicitly(argument, parameter)
                            || self.tuple_at(tuples, index, parameter)
                            || (!receiver && self.arms_at(arms, index, parameter))
                            // The receiver of an extension method reaches
                            // its parameter by identity, reference or boxing
                            // only; an interpolated string there is a string.
                            || (!receiver
                                && (self.constant_at(constants, index, argument, parameter)
                                    || self.interpolated_reaches(interpolated, index, parameter))))
                            && (!collections.get(index).copied().unwrap_or(false)
                                || self.takes_a_collection(parameter))
                            && self.elements_reach(elements, index, parameter)
                            && self.branches_reach(branches, index, parameter)
                            && self.address_reaches(addresses, index, parameter)
                            && self.ref_return_fits(
                                lambda_refs.get(index).copied().flatten(),
                                parameter,
                            )
                            && !(lambda_safe.get(index).copied().unwrap_or(false)
                                && self.delegate_takes_pointer(parameter))
                            && (self.natural_fits(natural, lambdas, index, parameter)
                                || (arity_fits(
                                    lambdas.get(index).copied().flatten(),
                                    parameter,
                                    symbols,
                                ) && (lambdas.get(index).copied().flatten().is_none()
                                    || self.takes_a_function_here(parameter))
                                    && (!groups.get(index).copied().unwrap_or(false)
                                        || self.group_fits(
                                            group_methods.get(index).map_or(&[], Vec::as_slice),
                                            group_closed.get(index).copied().unwrap_or(false),
                                            parameter,
                                        ))))
                            && self.functions_fit(functions, index, parameter)
                    },
                );
            // A call that leaves out the `params` parameter altogether takes
            // it in its expanded form, with nothing in the array: `Write(s)`
            // is `Write(string)` before it is `Write(string, params
            // object[])` (§12.6.4.2).
            if applicable
                && arguments.len() < parameters.len()
                && self.params_element(*candidate, &parameters).is_some()
            {
                normal = false;
                // Compared as expanded, with nothing in the array.
                compared.truncate(parameters.len() - 1);
            }
            if !applicable {
                // `params object[] rest` also takes the arguments one by one,
                // and that form is tried only when passing them as an array
                // did not work: `Write(array)` passes the array.
                let Some(element) = self.params_element(*candidate, &parameters) else {
                    continue;
                };
                normal = false;
                let fixed = parameters.len() - 1;
                exact = 0;
                let expanded = arguments[..fixed.min(arguments.len())]
                    .iter()
                    .zip(&parameters)
                    .enumerate()
                    .all(|(index, (argument, parameter))| {
                        if argument == parameter {
                            exact += 1;
                        }
                        (self.binder.converts_implicitly(argument, parameter)
                            || self.constant_at(constants, index, argument, parameter)
                            || self.tuple_at(tuples, index, parameter)
                            || self.arms_at(arms, index, parameter)
                            // The receiver of an extension method reaches
                            // its parameter by identity, reference or boxing
                            // only; an interpolated string there is a string.
                            || (!(index == 0 && *extension)
                                && self.interpolated_reaches(interpolated, index, parameter)))
                            && (!collections.get(index).copied().unwrap_or(false)
                                || self.takes_a_collection(parameter))
                            && self.elements_reach(elements, index, parameter)
                            && self.branches_reach(branches, index, parameter)
                            && self.address_reaches(addresses, index, parameter)
                            && (self.natural_fits(natural, lambdas, index, parameter)
                                || (arity_fits(
                                    lambdas.get(index).copied().flatten(),
                                    parameter,
                                    symbols,
                                ) && (lambdas.get(index).copied().flatten().is_none()
                                    || self.takes_a_function_here(parameter))
                                    && (!groups.get(index).copied().unwrap_or(false)
                                        || self.group_fits(
                                            group_methods.get(index).map_or(&[], Vec::as_slice),
                                            group_closed.get(index).copied().unwrap_or(false),
                                            parameter,
                                        ))))
                    })
                    && arguments.len() >= fixed
                    && arguments[fixed..].iter().enumerate().all(|(at, argument)| {
                        // `Block([local], statement)` passes a collection
                        // where the expanded form wants one statement, and a
                        // collection expression is never one of those.
                        (self.binder.converts_implicitly(argument, &element)
                            || self.constant_at(constants, fixed + at, argument, &element)
                            || self.interpolated_reaches(interpolated, fixed + at, &element))
                            && (!collections.get(fixed + at).copied().unwrap_or(false)
                                || self.takes_a_collection(&element))
                            && self.branches_reach(branches, fixed + at, &element)
                    });
                if !expanded {
                    continue;
                }
                // Compared as expanded: each argument past the fixed ones
                // against the element type it converts to (§12.6.4.2).
                compared = parameters[..fixed].to_vec();
                compared.extend(std::iter::repeat_n(element, arguments.len() - fixed));
            }
            // A candidate whose inferred type arguments the call site could
            // not name is not applicable: `Goo<T>(I<T>)` over a class
            // implementing `I<Private>` gives way to `Goo<T>(J<T>)`.
            if !type_arguments.iter().all(|ty| self.type_accessible(ty)) {
                continue;
            }
            let function_type = parameters.iter().enumerate().any(|(index, parameter)| {
                natural.get(index).copied().unwrap_or(false)
                    && !self.is_function_target(parameter)
                    && self.natural_fits(natural, lambdas, index, parameter)
            }) || from_function;
            applicable_set.push((
                Betterness(
                    normal,
                    exact,
                    std::cmp::Reverse(generality),
                    function_type,
                    ref_omitted,
                ),
                compared,
                Resolved {
                    method: *candidate,
                    type_arguments,
                    substitution: method_substitution,
                },
            ));
        }

        // Only now, among the ones that fit, does it matter where they were
        // declared: a method a derived type contributes puts out the ones its
        // bases declare. Applicability comes first, which is why
        // `x.ToString()` still reaches `object`'s on a type that declares a
        // `ToString(string)` of its own.
        let kept = self
            .binder
            .reduce_overloads(applicable_set.iter().map(|(_, _, r)| r.method).collect());
        applicable_set.retain(|(_, _, resolved)| kept.contains(&resolved.method));
        self.keep_highest_priority(&mut applicable_set);
        applicable_set
            .into_iter()
            .reduce(|best, candidate| {
                if self.beats(&candidate, &best, arguments, &inference, refs, interpolated) {
                    candidate
                } else {
                    best
                }
            })
            .map(|(_, _, resolved)| resolved)
    }

    /// Whether a call to a method may leave out the `ref` of its `ref`
    /// parameters: an instance method of a `[ComImport]` type.
    pub(super) fn omits_refs(&self, method: SymbolId) -> bool {
        let symbols = self.binder.compilation().symbols();
        let symbol = symbols.get(method);
        !symbol.modifiers.contains(crate::symbol::Modifiers::STATIC)
            && symbol
                .container
                .is_some_and(|container| self.binder.is_com_import(container))
    }

    /// Whether the code here may name a type: every type in it is one it
    /// may access.
    fn type_accessible(&self, ty: &Type) -> bool {
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                self.accessible(*symbol) && type_arguments.iter().all(|it| self.type_accessible(it))
            }
            Type::Array { element, .. } | Type::ByRef(element) | Type::Pointer(element) => {
                self.type_accessible(element)
            }
            Type::Tuple(elements) => elements.iter().all(|it| self.type_accessible(&it.ty)),
            _ => true,
        }
    }

    /// C# 13: of the applicable members each type declares, only those with
    /// the highest `[OverloadResolutionPriority]` stay (Roslyn's
    /// `RemoveLowerPriorityMembers`), before any is compared with another.
    fn keep_highest_priority(&self, applicable: &mut Vec<(Betterness, Vec<Type>, Resolved)>) {
        if applicable.len() < 2
            || !self
                .language_version()
                .at_least(rustlyn_syntax::LanguageVersion::CSharp13)
        {
            return;
        }
        let compilation = self.binder.compilation();
        let priorities: Vec<i32> = applicable
            .iter()
            .map(|(_, _, resolved)| compilation.overload_resolution_priority(resolved.method))
            .collect();
        if priorities.iter().all(|priority| *priority == 0) {
            return;
        }
        let symbols = compilation.symbols();
        let container = |method: SymbolId| symbols.get(method).container;
        let mut highest: HashMap<Option<SymbolId>, i32> = HashMap::new();
        for ((_, _, resolved), priority) in applicable.iter().zip(&priorities) {
            let entry = highest
                .entry(container(resolved.method))
                .or_insert(i32::MIN);
            *entry = (*entry).max(*priority);
        }
        let mut index = 0;
        applicable.retain(|(_, _, resolved)| {
            let keep = highest.get(&container(resolved.method)) == Some(&priorities[index]);
            index += 1;
            keep
        });
    }

    /// Whether one candidate that fits is the better fit of two (§12.6.4.5),
    /// in the order Roslyn's `BetterFunctionMember` asks it.
    ///
    /// What each argument has to be converted into decides it: a candidate is
    /// better when no argument converts worse to its parameter and at least
    /// one converts better. Only where the arguments say nothing do the
    /// tie-breaking rules settle it: fewer defaults filled in, a parameter
    /// taken by value over one taken by `in`, a method that is not generic,
    /// the normal form over the expanded one, more declared parameters, no
    /// defaults at all, and the more specific parameter types.
    fn beats(
        &self,
        candidate: &(Betterness, Vec<Type>, Resolved),
        best: &(Betterness, Vec<Type>, Resolved),
        arguments: &[Type],
        inference: &[InferenceArgument],
        refs: &[RefKind],
        interpolated: &[Option<Interpolated>],
    ) -> bool {
        // A candidate a lambda or a method group reaches as a delegate beats
        // one it reaches only through its natural type (C# 10).
        if candidate.0.3 != best.0.3 {
            return !candidate.0.3;
        }
        // A candidate that needs no `ref` left out beats one that does.
        if candidate.0.4 != best.0.4 {
            return !candidate.0.4;
        }
        // How each candidate takes each argument, in the order the arguments
        // reach its parameters: an indexer's parameters are its own.
        let modes = |method: SymbolId| -> Vec<RefKind> {
            let symbols = self.binder.compilation().symbols();
            let declared = super::member_parameters(symbols, method).unwrap_or_default();
            let order: Vec<usize> = self
                .parameter_order(method, arguments.len())
                .unwrap_or_else(|| (0..declared.len()).collect());
            order
                .iter()
                .filter_map(|at| declared.get(*at))
                .map(|parameter| {
                    symbols
                        .get(*parameter)
                        .as_parameter()
                        .map_or(RefKind::None, |detail| detail.ref_kind)
                })
                .collect()
        };
        let (our_modes, their_modes) = (modes(candidate.2.method), modes(best.2.method));
        // Whether each parameter type is the other's, ignoring what the
        // arguments said: only then do the tie-breaking rules apply.
        let mut all_same = true;
        // What the arguments say, as Roslyn reads them: a lambda's say may be
        // dropped where it contradicts another argument's (bug 11961 — the
        // native compiler compared lambdas apart from everything else).
        let mut result: Option<bool> = None;
        let mut result_downgradable = false;
        let mut ignore_downgradable = false;
        let mut conflict = false;
        // Both leave out a `ref` (a COM call): an argument taken by value
        // is the better only where it goes in as it is, and two taken by
        // `ref` say nothing — the native compiler's rule, which Roslyn keeps.
        let consider_refs = candidate.0.4 && best.0.4;
        for (index, argument) in arguments.iter().enumerate() {
            let (Some(first), Some(second)) = (candidate.1.get(index), best.1.get(index)) else {
                continue;
            };
            // `ref x` is better passed to a `ref` parameter than to an `in`
            // one, which takes it only with a warning (C# 12).
            let by_ref = if refs.get(index) == Some(&RefKind::Ref) {
                match (our_modes.get(index), their_modes.get(index)) {
                    (Some(RefKind::Ref), Some(RefKind::In)) => Some(true),
                    (Some(RefKind::In), Some(RefKind::Ref)) => Some(false),
                    _ => None,
                }
            } else {
                None
            };
            if by_ref.is_none() && !self.identical(first, second) {
                all_same = false;
            }
            if conflict {
                continue;
            }
            let com_refs = consider_refs.then(|| {
                (
                    our_modes.get(index).copied().unwrap_or(RefKind::None),
                    their_modes.get(index).copied().unwrap_or(RefKind::None),
                )
            });
            let (better, downgradable) = match (by_ref, com_refs) {
                (Some(better), _) => (Some(better), false),
                _ if let Some(handler) =
                    self.handler_betterness(interpolated, index, first, second) =>
                {
                    (handler, false)
                }
                (None, Some((mine, theirs))) if mine != theirs => {
                    if mine == RefKind::None {
                        ((argument == first).then_some(true), false)
                    } else {
                        ((argument == second).then_some(false), false)
                    }
                }
                (None, Some((RefKind::Ref, RefKind::Ref))) => (None, false),
                _ => self.better_conversion_from(argument, inference.get(index), first, second),
            };
            let Some(better) = better else {
                continue;
            };
            match result {
                None => {
                    if !(ignore_downgradable && downgradable) {
                        result = Some(better);
                        result_downgradable = downgradable;
                    }
                }
                Some(known) if known != better => {
                    if result_downgradable {
                        if downgradable {
                            result = None;
                            result_downgradable = false;
                            ignore_downgradable = true;
                        } else {
                            result = Some(better);
                            result_downgradable = false;
                        }
                    } else if !downgradable {
                        result = None;
                        conflict = true;
                    }
                }
                Some(_) => result_downgradable &= downgradable,
            }
        }
        if let Some(better) = result {
            return better;
        }
        let symbols = self.binder.compilation().symbols();
        // An indexer is a property, and its parameters are its own.
        let parameters_of = |method: SymbolId| -> Vec<SymbolId> {
            let declared = super::member_parameters(symbols, method)
                .map(<[SymbolId]>::to_vec)
                .unwrap_or_default();
            match self.parameter_order(method, arguments.len()) {
                Some(order) => order.iter().map(|index| declared[*index]).collect(),
                None => declared,
            }
        };
        let (mine, other) = (
            parameters_of(candidate.2.method),
            parameters_of(best.2.method),
        );
        let normal = |entry: &(Betterness, Vec<Type>, Resolved)| entry.0.0;
        // How many parameters a candidate uses, the optional ones filled in
        // and the `params` one counted as many times as it is expanded.
        // A `params` parameter a named argument reaches is used, as
        // Roslyn's `GetParameterCounts` counts it: `Fn("a", p: "b")` uses all
        // three of `Fn(string x = "", string y = "", params object[] p)`.
        let used = |entry: &(Betterness, Vec<Type>, Resolved), declared: usize| {
            if normal(entry) {
                declared
            } else if arguments.len() < declared {
                let named_params = self
                    .parameter_order(entry.2.method, arguments.len())
                    .is_some_and(|order| order.contains(&(declared - 1)));
                if named_params { declared } else { declared - 1 }
            } else {
                arguments.len()
            }
        };
        let (mine_used, other_used) = (used(candidate, mine.len()), used(best, other.len()));

        if !all_same || mine_used != other_used {
            // Not part of the language: the native compiler compared the
            // parameters filled in by default too, and Roslyn keeps that.
            if mine_used != other_used {
                match (normal(candidate), normal(best)) {
                    (false, true) => return false,
                    (true, false) => return true,
                    _ => {}
                }
                // An argument written without `in` is better passed by value
                // whatever either has left to fill in with defaults.
                if let Some(value) = self.prefers_value(arguments, candidate, &mine, best, &other) {
                    return value;
                }
                if mine_used == arguments.len() {
                    return true;
                }
                if other_used == arguments.len() {
                    return false;
                }
            }
            return self.prefers_value(arguments, candidate, &mine, best, &other) == Some(true);
        }

        // A method that is not generic beats one that is.
        let arity = |method: SymbolId| {
            symbols
                .get(method)
                .as_method()
                .map_or(0, |detail| detail.type_parameters.len())
        };
        match (arity(candidate.2.method), arity(best.2.method)) {
            (0, theirs) if theirs > 0 => return true,
            (ours, 0) if ours > 0 => return false,
            _ => {}
        }
        // The normal form beats the expanded one.
        match (normal(candidate), normal(best)) {
            (true, false) => return true,
            (false, true) => return false,
            _ => {}
        }
        // Of two expanded forms, the one with more declared parameters.
        if !normal(candidate) && !normal(best) && mine.len() != other.len() {
            return mine.len() > other.len();
        }
        // One that needs no default filled in beats one that does.
        let has_all = |entry: &(Betterness, Vec<Type>, Resolved), declared: usize| {
            !normal(entry) || declared == arguments.len()
        };
        match (has_all(candidate, mine.len()), has_all(best, other.len())) {
            (true, false) => return true,
            (false, true) => return false,
            _ => {}
        }
        // The more specific parameter types, as declared.
        if let Some(better) =
            self.more_specific_parameters(arguments.len(), candidate, &mine, best, &other)
        {
            return better;
        }
        self.prefers_value(arguments, candidate, &mine, best, &other) == Some(true)
    }

    /// Whether two types are one, as far as overload resolution cares:
    /// `dynamic` is `object` and a tuple's names are no part of it.
    pub(super) fn identical(&self, first: &Type, second: &Type) -> bool {
        first == second
            || self.binder.same_but_for_dynamic(first, second)
            || ((contains_tuple(first) || contains_tuple(second))
                && self.as_value_tuples(first) == self.as_value_tuples(second))
    }

    /// A type with every tuple in it spelled as the `ValueTuple` it is.
    fn as_value_tuples(&self, ty: &Type) -> Type {
        match ty {
            Type::Tuple(elements) => {
                let named = self.tuple_as_named(elements);
                if matches!(named, Type::Tuple(_)) {
                    return named;
                }
                self.as_value_tuples(&named)
            }
            Type::Named {
                symbol,
                type_arguments,
            } => Type::Named {
                symbol: *symbol,
                type_arguments: type_arguments
                    .iter()
                    .map(|t| self.as_value_tuples(t))
                    .collect(),
            },
            Type::Array { element, rank } => Type::Array {
                element: Box::new(self.as_value_tuples(element)),
                rank: *rank,
            },
            _ => ty.clone(),
        }
    }

    /// The type of the parameter an argument goes to, as the method declares
    /// it: the element of a `params` collection taken expanded.
    fn declared_parameter_type(
        &self,
        method: SymbolId,
        parameters: &[SymbolId],
        normal: bool,
        index: usize,
    ) -> Option<Type> {
        let mut sink = Diagnostics::new();
        let declared: Vec<Type> = parameters
            .iter()
            .map(|id| self.binder.type_of(*id, &mut sink))
            .collect();
        if !normal && index + 1 >= declared.len() {
            return self.params_element(method, &declared);
        }
        declared.get(index).cloned()
    }

    /// Which candidate's parameter types are the more specific, as declared
    /// (§12.6.4.5): a type parameter is less specific than anything else,
    /// and a construction is more specific where its arguments are.
    fn more_specific_parameters(
        &self,
        count: usize,
        candidate: &(Betterness, Vec<Type>, Resolved),
        mine: &[SymbolId],
        best: &(Betterness, Vec<Type>, Resolved),
        other: &[SymbolId],
    ) -> Option<bool> {
        let mut result = None;
        for index in 0..count {
            let (Some(first), Some(second)) = (
                self.declared_parameter_type(candidate.2.method, mine, candidate.0.0, index),
                self.declared_parameter_type(best.2.method, other, best.0.0, index),
            ) else {
                continue;
            };
            match (self.more_specific(&first, &second), result) {
                (None, _) => {}
                (Some(found), None) => result = Some(found),
                (Some(found), Some(before)) if found != before => return None,
                _ => {}
            }
        }
        result
    }

    /// Whether the first of two types, identical but for type parameters, is
    /// the more specific (§12.6.4.5): `Some(false)` where the second is. A
    /// tuple is compared as the `ValueTuple` it is.
    fn more_specific(&self, first: &Type, second: &Type) -> Option<bool> {
        match (first, second) {
            (Type::TypeParameter(_), Type::TypeParameter(_)) => None,
            (Type::TypeParameter(_), _) => Some(false),
            (_, Type::TypeParameter(_)) => Some(true),
            (Type::Tuple(elements), other) => {
                self.more_specific(&self.tuple_as_named(elements), other)
            }
            (other, Type::Tuple(elements)) => {
                self.more_specific(other, &self.tuple_as_named(elements))
            }
            (Type::Array { element: a, .. }, Type::Array { element: b, .. })
            | (Type::Pointer(a), Type::Pointer(b))
            | (Type::ByRef(a), Type::ByRef(b)) => self.more_specific(a, b),
            (
                Type::Named {
                    type_arguments: a, ..
                },
                Type::Named {
                    type_arguments: b, ..
                },
            ) if a.len() == b.len() => {
                let mut result = None;
                for (first, second) in a.iter().zip(b) {
                    match (self.more_specific(first, second), result) {
                        (None, _) => {}
                        (Some(found), None) => result = Some(found),
                        (Some(found), Some(before)) if found != before => return None,
                        _ => {}
                    }
                }
                result
            }
            _ => None,
        }
    }

    /// Whether the first candidate takes by value what the other takes by
    /// `in` (or `ref readonly`), and never the other way round.
    fn prefers_value(
        &self,
        arguments: &[Type],
        candidate: &(Betterness, Vec<Type>, Resolved),
        mine: &[SymbolId],
        best: &(Betterness, Vec<Type>, Resolved),
        other: &[SymbolId],
    ) -> Option<bool> {
        let symbols = self.binder.compilation().symbols();
        let mode = |parameters: &[SymbolId], normal: bool, index: usize| {
            let at = if normal {
                index
            } else {
                index.min(parameters.len().saturating_sub(1))
            };
            parameters
                .get(at)
                .and_then(|id| symbols.get(*id).as_parameter())
                .map_or(RefKind::None, |detail| detail.ref_kind)
        };
        let readonly = |kind: RefKind| kind == RefKind::In;
        let mut preference = None;
        for index in 0..arguments.len() {
            let (first, second) = (
                mode(mine, candidate.0.0, index),
                mode(other, best.0.0, index),
            );
            if first == RefKind::None && readonly(second) {
                if preference == Some(false) {
                    return None;
                }
                preference = Some(true);
            } else if second == RefKind::None && readonly(first) {
                if preference == Some(true) {
                    return None;
                }
                preference = Some(false);
            }
        }
        preference
    }

    /// Which of two parameter types an argument converts to better, if
    /// either (§12.6.4.6), and whether that may give way to what another
    /// argument says: a lambda's answer may, where the two delegates take
    /// different parameters (Roslyn's deliberate deviation for bug 11961).
    fn better_conversion_from(
        &self,
        argument: &Type,
        inference: Option<&InferenceArgument>,
        first: &Type,
        second: &Type,
    ) -> (Option<bool>, bool) {
        if self.identical(first, second) {
            return (None, false);
        }
        if let Some(InferenceArgument::Lambda { span, .. }) = inference {
            let (exact_first, exact_second) = (
                self.lambda_matches_exactly(*span, first),
                self.lambda_matches_exactly(*span, second),
            );
            let better = if exact_first != exact_second {
                Some(exact_first)
            } else {
                self.better_target_type(first, second)
            };
            let downgradable = better.is_some() && self.lambda_may_give_way(*span, first, second);
            return (better, downgradable);
        }
        (self.better_target(argument, first, second), false)
    }

    /// Whether the argument at `index` is an interpolated string that
    /// reaches the parameter as one: a handler takes any, a
    /// `FormattableString` a lone one (§12.8.3).
    pub(super) fn interpolated_reaches(
        &self,
        interpolated: &[Option<Interpolated>],
        index: usize,
        parameter: &Type,
    ) -> bool {
        interpolated
            .get(index)
            .copied()
            .flatten()
            .is_some_and(|found| {
                self.is_handler_type(parameter) || (found.lone && self.is_formattable(parameter))
            })
    }

    /// What C# 10 says of two parameters an interpolated string that is no
    /// constant is given to (Roslyn's `BetterConversionFromExpression`): a
    /// handler is the better, whatever the other is, and two handlers are
    /// neither. `None` where the rule has nothing to say.
    fn handler_betterness(
        &self,
        interpolated: &[Option<Interpolated>],
        index: usize,
        first: &Type,
        second: &Type,
    ) -> Option<Option<bool>> {
        let found = interpolated.get(index).copied().flatten()?;
        if found.constant || !self.language_version().at_least(LanguageVersion::CSharp10) {
            return None;
        }
        match (self.is_handler_type(first), self.is_handler_type(second)) {
            (true, true) => Some(None),
            (true, false) => Some(Some(true)),
            (false, true) => Some(Some(false)),
            (false, false) => None,
        }
    }

    /// §12.6.4.5: a lambda exactly matches a delegate returning `Y` where
    /// the return type inferred for its body is `Y` itself.
    fn lambda_matches_exactly(&self, span: TextSpan, target: &Type) -> bool {
        let Some((_, gives)) = self.delegate_signature(target) else {
            return false;
        };
        if matches!(gives, Type::Void) {
            return false;
        }
        let Some(answer) = self.lambda_answer(span, target) else {
            return false;
        };
        // The fit says it: exact where what the body returns is the
        // delegate's return type, and a lambda it returns matches that
        // delegate's exactly in turn.
        answer.fit == super::Fit::Exact
    }

    /// Whether what a lambda says about two delegates may give way to what
    /// another argument says (Roslyn's `CanDowngradeConversionFromLambdaToNeither`).
    fn lambda_may_give_way(&self, span: TextSpan, first: &Type, second: &Type) -> bool {
        let (Some((taken_first, gives_first)), Some((taken_second, gives_second))) = (
            self.delegate_signature(first),
            self.delegate_signature(second),
        ) else {
            return false;
        };
        if taken_first.len() != taken_second.len()
            || taken_first
                .iter()
                .zip(&taken_second)
                .any(|(a, b)| !self.identical(a, b))
        {
            return true;
        }
        match (
            matches!(gives_first, Type::Void),
            matches!(gives_second, Type::Void),
        ) {
            (true, true) => return true,
            (true, false) | (false, true) => return false,
            _ => {}
        }
        if self.identical(&gives_first, &gives_second) {
            return true;
        }
        // Before C# 10 a lambda has no type of its own, and one that returns
        // only lambdas has no return type to infer.
        if !self.language_version().at_least(LanguageVersion::CSharp10)
            && self.returns_only_functions(span)
        {
            return true;
        }
        self.lambda_answer(span, first)
            .is_none_or(|answer| answer.returns.is_none())
    }

    /// Whether every value the lambda at `span` returns is a lambda or an
    /// anonymous method: `() => () => i`.
    fn returns_only_functions(&self, span: TextSpan) -> bool {
        let is_function = |node: &SyntaxNode| {
            matches!(
                node.kind(),
                SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
            )
        };
        let unparenthesized = |mut node: SyntaxNode| {
            while node.kind() == SyntaxKind::ParenthesizedExpression {
                let Some(inner) = node.children().next() else {
                    break;
                };
                node = inner;
            }
            node
        };
        let Some(lambda) = self.syntax_at(span) else {
            return false;
        };
        let Some(body) = lambda.children().last() else {
            return false;
        };
        if body.kind() != SyntaxKind::Block {
            return is_function(&unparenthesized(body));
        }
        // The returns of this lambda, not of one nested in it.
        let returned: Vec<SyntaxNode> = body
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ReturnStatement)
            .filter(|node| {
                node.ancestors()
                    .find(|ancestor| {
                        is_function(ancestor)
                            || ancestor.kind() == SyntaxKind::LocalFunctionStatement
                    })
                    .is_some_and(|owner| owner.span() == lambda.span())
            })
            .filter_map(|node| node.children().find(|child| child.kind().is_expression()))
            .collect();
        !returned.is_empty()
            && returned
                .into_iter()
                .all(|value| is_function(&unparenthesized(value)))
    }

    /// Which of two parameter types takes an argument better, if either does.
    fn better_target(&self, argument: &Type, first: &Type, second: &Type) -> Option<bool> {
        if first == second {
            return None;
        }
        // Nothing beats needing no conversion at all.
        if argument == first {
            return Some(true);
        }
        if argument == second {
            return Some(false);
        }
        // C# 14 (§12.6.4.6): an implicit span conversion from the argument
        // beats any other conversion.
        if self.binder.first_class_spans() {
            let spans = (
                self.binder.implicit_span_conversion(argument, first),
                self.binder.implicit_span_conversion(argument, second),
            );
            if spans.0 != spans.1 {
                return Some(spans.0);
            }
        }
        self.better_target_type(first, second)
    }

    /// The better conversion target of two types (§12.6.4.7): the one that
    /// converts to the other; of two tasks, the one whose result is; of two
    /// delegates, the one that returns something, or whose return is; and a
    /// signed integer over the unsigned ones it cannot hold.
    fn better_target_type(&self, first: &Type, second: &Type) -> Option<bool> {
        self.better_target_type_at(first, second, 0)
    }

    fn better_target_type_at(&self, first: &Type, second: &Type, depth: usize) -> Option<bool> {
        if depth > 32 || self.identical(first, second) {
            return None;
        }
        // C# 14: a `ReadOnlySpan<E>` is the better target than a `Span<E>`,
        // and otherwise two spans are only compared where both are
        // read-only — `Span<T>` reaching `ReadOnlySpan<T>` no longer makes
        // it the better one.
        if self.binder.first_class_spans() {
            let same = |one: &Type, other: &Type| {
                one == other || self.binder.same_but_for_dynamic(one, other)
            };
            match (
                self.binder.span_parts(first),
                self.binder.span_parts(second),
            ) {
                (Some((true, one)), Some((false, other))) if same(&one, &other) => {
                    return Some(true);
                }
                (Some((false, one)), Some((true, other))) if same(&one, &other) => {
                    return Some(false);
                }
                (Some((one, _)), Some((other, _))) if !(one && other) => return None,
                _ => {}
            }
        }
        let onwards = self.binder.converts_implicitly(first, second);
        let backwards = self.binder.converts_implicitly(second, first);
        if onwards != backwards {
            return Some(onwards);
        }
        if onwards {
            return None;
        }
        match (
            self.generic_task_result(first),
            self.generic_task_result(second),
        ) {
            (Some(first), Some(second)) => {
                return self.better_target_type_at(&first, &second, depth + 1);
            }
            // A task with a result over one without is what a value is over
            // `void`: `UniTask.Create<T>(Func<UniTask<T>>)` over
            // `Create(Func<UniTask>)` for `async () => await Check()`. A
            // `Task<T>` reaches a `Task` and is settled above; two task-like
            // structs reach nothing.
            (Some(_), None) if self.is_task_without_result(second) => return Some(true),
            (None, Some(_)) if self.is_task_without_result(first) => return Some(false),
            (Some(_), None) | (None, Some(_)) => return None,
            (None, None) => {}
        }
        match (
            self.delegate_signature(first),
            self.delegate_signature(second),
        ) {
            (Some((_, gives_first)), Some((_, gives_second))) => {
                return match (
                    matches!(gives_first, Type::Void),
                    matches!(gives_second, Type::Void),
                ) {
                    (false, true) => Some(true),
                    (true, false) => Some(false),
                    _ => self.better_target_type_at(&gives_first, &gives_second, depth + 1),
                };
            }
            (Some(_), None) | (None, Some(_)) => return None,
            (None, None) => {}
        }
        // §12.6.4.7: where neither type reaches the other, a signed type is
        // the better target than the unsigned ones it cannot hold. That is
        // what sends `Console.WriteLine(width)` on a `ushort` to the `int`
        // overload rather than to the `decimal` or `uint` ones.
        let (Some(first), Some(second)) = (
            self.binder.special_of(first),
            self.binder.special_of(second),
        ) else {
            return None;
        };
        if outranks(first, second) {
            return Some(true);
        }
        if outranks(second, first) {
            return Some(false);
        }
        None
    }

    /// Whether a type is a task an `async` body returns nothing through: a
    /// `Task`, a `ValueTask`, or a task-like type with no type argument.
    fn is_task_without_result(&self, ty: &Type) -> bool {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return false;
        };
        if !type_arguments.is_empty() {
            return false;
        }
        let name = self.binder.compilation().symbols().qualified_name(*symbol);
        matches!(
            name.as_str(),
            "System.Threading.Tasks.Task" | "System.Threading.Tasks.ValueTask"
        ) || self.binder.async_method_builder(*symbol).is_some()
    }

    /// The `T` of a `Task<T>` or a `ValueTask<T>`.
    fn generic_task_result(&self, ty: &Type) -> Option<Type> {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return None;
        };
        if type_arguments.len() != 1 {
            return None;
        }
        let name = self.binder.compilation().symbols().qualified_name(*symbol);
        // A task-like type of one argument, `UniTask<T>`, is one too.
        (matches!(
            name.as_str(),
            "System.Threading.Tasks.Task`1" | "System.Threading.Tasks.ValueTask`1"
        ) || self.binder.async_method_builder(*symbol).is_some())
        .then(|| type_arguments[0].clone())
    }
}

/// Matches a declared parameter type against the argument's, recording what
/// each of the method's type parameters must be.
///
/// This is type inference at its smallest: C# infers from the shape of the
/// types, and the shapes that can appear here are a bare parameter, an array
/// of one and a construction of one. The first binding wins — a second, worse
/// one would only be an inconsistency, and the applicability check below
/// catches it anyway.
impl BodyBinder<'_> {
    /// Works out what a method's type parameters must be, by matching each
    /// parameter's declared type against the argument given for it.
    ///
    /// This is §12.6.3 read narrowly: enough of it to settle `Echo(7)` and
    /// `numbers.Count()`, and none of the fixing and bounding that a second
    /// candidate would need.
    pub(super) fn infer_into(
        &self,
        parameter: &Type,
        argument: &Type,
        type_parameters: &[SymbolId],
        inferred: &mut HashMap<SymbolId, Type>,
    ) {
        self.infer_bound(parameter, argument, type_parameters, inferred, Bound::Lower);
    }

    /// The same, knowing which way the position constrains the answer.
    ///
    /// An argument for a bare `T` is a lower bound: `T` may be that or
    /// anything it reaches. One inside an invariant construction —
    /// the key of an `IReadOnlyDictionary<T, int>` — is exact, and one
    /// inside a contravariant one, an `IEqualityComparer<in T>`, is an upper
    /// bound that must not widen the answer (§12.6.3.15).
    fn infer_bound(
        &self,
        parameter: &Type,
        argument: &Type,
        type_parameters: &[SymbolId],
        inferred: &mut HashMap<SymbolId, Type>,
        bound: Bound,
    ) {
        // `(bool, T)` against a `(bool, int)`: a tuple is inferred element by
        // element, whichever of the two is written with parentheses and
        // whichever as a `ValueTuple<…>` (§12.6.3.9).
        // Past seven elements the shapes are compared as the nested
        // `ValueTuple<…, TRest>` both really are: a `TRest` is the rest
        // as a tuple, never its first element.
        let nested = |ty: &Type| match ty {
            Type::Tuple(elements) if elements.len() > 7 => self.tuple_as_named(elements),
            _ => ty.clone(),
        };
        let (parameter, argument) = (&nested(parameter), &nested(argument));
        if (matches!(parameter, Type::Tuple(_)) || matches!(argument, Type::Tuple(_)))
            && let (Some(wanted), Some(given)) = (
                self.tuple_element_types(parameter),
                self.tuple_element_types(argument),
            )
        {
            if wanted.len() == given.len() {
                for (wanted, given) in wanted.iter().zip(&given) {
                    self.infer_bound(wanted, given, type_parameters, inferred, bound);
                }
            }
            return;
        }
        match (parameter, argument) {
            (Type::TypeParameter(symbol), argument) if type_parameters.contains(symbol) => {
                // `null` has no type to infer from: `Echo(null)` says nothing
                // about `T`, and C# reports that rather than guessing `object`.
                //
                // An error does say something, though: that it has already
                // been reported. Refusing to infer from it makes the call
                // inapplicable and reports a second thing about the same
                // mistake — which is how one unresolved name turned into a
                // "no overload takes one argument" on every line that used
                // what it named.
                if matches!(argument, Type::Null) {
                    return;
                }
                // Two arguments for one `T` fix it to the type both reach
                // (§12.6.3.15): `Create(expressionStatement, tryFinally)` is
                // an `ImmutableArray<BoundStatement>`, whichever was written
                // first.
                match inferred.get(symbol) {
                    // `TryExtract(handle, out var data, s_extractor)`: the
                    // `out var` said nothing, and the extractor says what
                    // `T` is.
                    Some(existing) if existing.is_error() && !argument.is_error() => {
                        inferred.insert(*symbol, argument.clone());
                    }
                    Some(existing)
                        if bound != Bound::Upper
                            && !existing.is_error()
                            && !argument.is_error()
                            && existing != argument
                            && self.binder.converts_implicitly(existing, argument)
                            && (bound == Bound::Exact
                                || !self.binder.converts_implicitly(argument, existing)) =>
                    {
                        inferred.insert(*symbol, argument.clone());
                    }
                    // An upper bound over a value type stands: a tuple
                    // literal `(calls, @string)` gave `(…, NamedTypeSymbol)`,
                    // and the `Func<…, (…, TypeSymbol), …>` beside it takes
                    // no other tuple, variance being for references only.
                    // The literal converts to it element by element.
                    Some(existing)
                        if bound == Bound::Upper
                            && !existing.is_error()
                            && !argument.is_error()
                            && existing != argument
                            && self.tuple_element_types(existing).is_some()
                            && self.tuple_element_types(argument).is_some()
                            && self.binder.converts_implicitly(existing, argument) =>
                    {
                        inferred.insert(*symbol, argument.clone());
                    }
                    Some(_) => {}
                    None => {
                        inferred.insert(*symbol, argument.clone());
                    }
                }
            }
            (
                Type::Array { element, rank },
                Type::Array {
                    element: argument,
                    rank: argument_rank,
                },
            ) if rank == argument_rank => {
                self.infer_bound(element, argument, type_parameters, inferred, bound);
            }
            (Type::Pointer(element), Type::Pointer(argument)) => {
                self.infer_bound(element, argument, type_parameters, inferred, Bound::Exact);
            }
            (
                Type::Named {
                    symbol,
                    type_arguments,
                },
                argument,
            ) => {
                // `ReadOnlySpan<T>` against a `Span<int>` or an `int[]`, and
                // `Span<T>` against an `int[]`: the implicit span conversions
                // (C# 14, §12.6.3.10) infer the element, exactly for a
                // `Span<T>` and as a lower bound for a `ReadOnlySpan<T>`,
                // which reads only.
                if self.binder.first_class_spans()
                    && argument.symbol() != Some(*symbol)
                    && let Some((readonly, wanted)) = self.binder.span_parts(parameter)
                    && let Some(given) = self.span_inference(readonly, argument)
                {
                    let inner = if readonly { bound } else { Bound::Exact };
                    self.infer_bound(&wanted, &given, type_parameters, inferred, inner);
                    return;
                }
                // `IEnumerable<TSource>` against a `List<int>` or an `int[]`:
                // the argument is not that type, it *is* one, and the
                // construction it is says what `TSource` must be.
                if argument.symbol() != Some(*symbol) {
                    if let Some(constructed) = self.binder.constructed_from(argument, *symbol) {
                        self.infer_bound(parameter, &constructed, type_parameters, inferred, bound);
                    }
                    return;
                }
                let Type::Named {
                    type_arguments: argument_arguments,
                    ..
                } = argument
                else {
                    return;
                };
                if type_arguments.len() != argument_arguments.len() {
                    return;
                }
                let symbols = self.binder.compilation().symbols();
                let variances: Vec<Variance> = symbols
                    .get(*symbol)
                    .as_named_type()
                    .map(|detail| {
                        detail
                            .type_parameters
                            .iter()
                            .map(|parameter| {
                                symbols
                                    .get(*parameter)
                                    .as_type_parameter()
                                    .map_or(Variance::None, |detail| detail.variance)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                for (index, (parameter, argument)) in
                    type_arguments.iter().zip(argument_arguments).enumerate()
                {
                    let inner = match variances.get(index).copied().unwrap_or_default() {
                        Variance::Out => bound,
                        Variance::In => bound.flipped(),
                        Variance::None => Bound::Exact,
                    };
                    self.infer_bound(parameter, argument, type_parameters, inferred, inner);
                }
            }
            _ => {}
        }
    }
}

impl BodyBinder<'_> {
    /// What an argument gives a `Span<T>` or `ReadOnlySpan<T>` parameter
    /// through an implicit span conversion (C# 14): the element of an
    /// array, or of a `Span<U>` where a `ReadOnlySpan<T>` is taken.
    fn span_inference(&self, readonly: bool, argument: &Type) -> Option<Type> {
        match argument {
            Type::Array { element, rank: 1 } => Some((**element).clone()),
            _ => self
                .binder
                .span_parts(argument)
                .filter(|(given_readonly, _)| readonly && !given_readonly)
                .map(|(_, element)| element),
        }
    }
}

/// Whether an argument written this way reaches a parameter declared that way.
///
/// `ref` and `out` are written at both ends or at neither; `in` is the one
/// the caller may leave out, and may also write as `ref`. A parameter past
/// the end is a `params` one being expanded, which is never by reference.
/// Whether the first of two numeric types is the one §12.6.4.7 prefers.
///
/// Neither of these reaches the other, so nothing about the conversions tells
/// them apart. The rule the language settles it with is that a signed type is
/// the better target than the unsigned ones holding values it cannot.
fn outranks(first: SpecialType, second: SpecialType) -> bool {
    matches!(
        (first, second),
        (
            SpecialType::SByte,
            SpecialType::Byte | SpecialType::UInt16 | SpecialType::UInt32 | SpecialType::UInt64
        ) | (
            SpecialType::Int16,
            SpecialType::UInt16 | SpecialType::UInt32 | SpecialType::UInt64
        ) | (
            SpecialType::Int32,
            SpecialType::UInt32 | SpecialType::UInt64
        ) | (SpecialType::Int64, SpecialType::UInt64)
    )
}

/// An inference argument with the natural type a caller worked out for it:
/// a lambda's or a method group's own, or a tuple's with its elements'.
fn with_natural(argument: &InferenceArgument, natural: Option<Type>) -> InferenceArgument {
    let Some(natural) = natural else {
        return argument.clone();
    };
    match argument {
        InferenceArgument::Lambda {
            span,
            parameters,
            returns,
            arity,
            ..
        } => InferenceArgument::Lambda {
            span: *span,
            parameters: parameters.clone(),
            returns: returns.clone(),
            arity: *arity,
            natural: Some(natural),
        },
        InferenceArgument::Group {
            methods,
            receiver,
            explicit,
            ..
        } => InferenceArgument::Group {
            methods: methods.clone(),
            receiver: receiver.clone(),
            explicit: explicit.clone(),
            natural: Some(natural),
        },
        // A tuple literal holding a lambda has no type of its own (the
        // lambda's natural type is no element type): only its elements do.
        InferenceArgument::Tuple(elements, own) => match &natural {
            Type::Tuple(types) if types.len() == elements.len() => InferenceArgument::Tuple(
                elements
                    .iter()
                    .zip(types)
                    .map(|(element, ty)| match element {
                        InferenceArgument::Lambda { .. } | InferenceArgument::Group { .. } => {
                            with_natural(element, Some(ty.ty.clone()))
                        }
                        _ => element.clone(),
                    })
                    .collect(),
                own.clone(),
            ),
            _ => argument.clone(),
        },
        _ => argument.clone(),
    }
}

/// Whether a type is or holds a tuple.
fn contains_tuple(ty: &Type) -> bool {
    match ty {
        Type::Tuple(_) => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(contains_tuple),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            contains_tuple(element)
        }
        _ => false,
    }
}

/// Every type parameter a type mentions, added to `found`.
fn collect_type_parameters(ty: &Type, found: &mut Vec<SymbolId>) {
    match ty {
        Type::TypeParameter(symbol) => {
            if !found.contains(symbol) {
                found.push(*symbol);
            }
        }
        Type::Named { type_arguments, .. } => {
            for argument in type_arguments {
                collect_type_parameters(argument, found);
            }
        }
        Type::Array { element, .. } | Type::ByRef(element) | Type::Pointer(element) => {
            collect_type_parameters(element, found);
        }
        Type::Tuple(elements) => {
            for element in elements {
                collect_type_parameters(&element.ty, found);
            }
        }
        _ => {}
    }
}

/// Whether an expression as written has no type until something gives it one.
///
/// A lambda, a collection expression and a `new(...)` are all of them, and so
/// is a conditional whose own branches are.
/// Whether a conditional's branches are, each of them, collection expressions
/// or conditionals that are.
fn branches_are_collections(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::CollectionExpression => true,
        SyntaxKind::ParenthesizedExpression => node
            .children()
            .next()
            .is_some_and(|inner| branches_are_collections(&inner)),
        SyntaxKind::ConditionalExpression => {
            let mut branches = node.children().skip(1);
            let (Some(first), Some(second)) = (branches.next(), branches.next()) else {
                return false;
            };
            branches_are_collections(&first) && branches_are_collections(&second)
        }
        _ => false,
    }
}

///
/// An `in` parameter takes an argument written with `ref` only from C# 12
/// on, where `ref readonly` parameters came with that relaxation (Roslyn's
/// `IDS_FeatureRefReadonlyParameters`); before, such a call reaches an
/// extension method taking `ref` instead.
pub(super) fn ref_fits(written: RefKind, declared: Option<RefKind>, ref_to_in: bool) -> bool {
    match declared {
        Some(RefKind::In) => match written {
            RefKind::Out => false,
            RefKind::Ref => ref_to_in,
            RefKind::None | RefKind::In => true,
        },
        Some(declared) => written == declared,
        None => written == RefKind::None,
    }
}

/// Whether a type names any type parameter at all, whoever declares it.
fn mentions_a_type_parameter(ty: &Type) -> bool {
    match ty {
        Type::TypeParameter(_) => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(mentions_a_type_parameter),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            mentions_a_type_parameter(element)
        }
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| mentions_a_type_parameter(&element.ty)),
        _ => false,
    }
}

/// Whether a type names any of the given type parameters, however deep.
pub(super) fn mentions_any(ty: &Type, parameters: &[SymbolId]) -> bool {
    match ty {
        Type::TypeParameter(symbol) => parameters.contains(symbol),
        Type::Named { type_arguments, .. } => type_arguments
            .iter()
            .any(|argument| mentions_any(argument, parameters)),
        Type::Array { element, .. } => mentions_any(element, parameters),
        Type::Pointer(element) | Type::ByRef(element) => mentions_any(element, parameters),
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| mentions_any(&element.ty, parameters)),
        Type::FunctionPointer(pointer) => pointer.types().any(|ty| mentions_any(ty, parameters)),
        Type::Null | Type::Void | Type::Error | Type::Dynamic => false,
    }
}
