//! Method type inference (§12.6.3), after Roslyn's `MethodTypeInferrer`.
//!
//! Each type parameter collects bounds — exact, lower and upper — from the
//! arguments, and is fixed to the one candidate type all of them agree on.
//! The first phase reads what the arguments say by their types and by the
//! parameter types their lambdas wrote; the second alternates between fixing
//! the type parameters nothing else waits for and asking each lambda and
//! method group, whose delegate's parameters are now known, what it returns.
//!
//! Asking a lambda what it returns means binding its body, which this
//! `&self` code cannot do. It asks [`BodyBinder::lambda_answer`] instead,
//! which knows the answers a caller with `&mut self` worked out and writes
//! down the questions it could not answer, for that caller to work out and
//! ask again.

use std::collections::HashMap;

use rustlyn_text::TextSpan;

use super::{BodyBinder, Fit};
use crate::symbol::{RefKind, SymbolId, TypeKind, Variance};
use crate::types::{TupleElement, Type};

/// An argument, as much of it as inference reads.
#[derive(Clone, Debug)]
pub(super) enum InferenceArgument {
    /// An expression with a type of its own.
    Typed(Type),
    /// A lambda or an anonymous method.
    Lambda {
        span: TextSpan,
        /// The parameter types it wrote, where it wrote them.
        parameters: Option<Vec<Type>>,
        /// The return type it wrote, where it wrote one.
        returns: Option<Type>,
        /// How many parameters it has, where the syntax says.
        arity: Option<usize>,
        /// Its natural type (C# 10), for a parameter that is no delegate.
        natural: Option<Type>,
    },
    /// A method group.
    Group {
        methods: Vec<SymbolId>,
        /// The type of the receiver the group was named on, if any: what
        /// the methods of a generic type return is seen through it.
        receiver: Option<Type>,
        /// The type arguments written on it: `Load<Prefab>` returns a
        /// `Prefab`, which nothing it takes says.
        explicit: Vec<Type>,
        natural: Option<Type>,
    },
    /// A tuple literal, inferred through element by element, with the type
    /// it has on its own where every element has one.
    Tuple(Vec<InferenceArgument>, Option<Type>),
    /// A collection expression: what its elements say on their own
    /// (§12.6.3.7), each an argument for the element type of the parameter.
    Collection(Vec<InferenceArgument>),
    /// Nothing to infer from: `null`, `default`, an `out var`.
    Untyped,
}

/// What binding a lambda against one delegate showed.
#[derive(Clone, Debug)]
pub(super) struct LambdaAnswer {
    /// The return type inferred for the body (§12.6.3.13); `None` where it
    /// returns nothing or nothing could be inferred.
    pub(super) returns: Option<Type>,
    /// How well the body takes the delegate.
    pub(super) fit: Fit,
}

/// The lambda answers known to one overload resolution, and the questions
/// asked of it that had no answer yet.
#[derive(Default)]
pub(super) struct LambdaAnswers {
    pub(super) known: HashMap<(TextSpan, Type), LambdaAnswer>,
    pub(super) missing: Vec<(TextSpan, Type)>,
    /// Every delegate a lambda was bound against while this resolution
    /// was under way, in order, with whether its body took it; kept only
    /// for an editor's binding (see `guess_lambda_parameters`).
    pub(super) tried: Vec<(TextSpan, Type, bool)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Exact,
    Lower,
    Upper,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Dependency {
    Unknown,
    NotDependent,
    Direct,
    Indirect,
}

impl Dependency {
    const fn depends(self) -> bool {
        matches!(self, Self::Direct | Self::Indirect)
    }
}

/// A bound, with whether it is the natural type of a lambda or a method
/// group: those give way to any other bound (C# 10).
type Bounds = Vec<(Type, bool)>;

struct Inferrer<'s, 'a> {
    binder: &'s BodyBinder<'a>,
    parameters: &'s [SymbolId],
    formal: &'s [Type],
    by_ref: &'s [bool],
    arguments: &'s [InferenceArgument],
    fixed: Vec<Option<(Type, bool)>>,
    exact: Vec<Bounds>,
    lower: Vec<Bounds>,
    upper: Vec<Bounds>,
    dependencies: Vec<Vec<Dependency>>,
    dirty: bool,
}

impl BodyBinder<'_> {
    /// The answer for a lambda against a delegate, where the resolution
    /// under way knows it; otherwise the question is written down.
    pub(super) fn lambda_answer(&self, span: TextSpan, delegate: &Type) -> Option<LambdaAnswer> {
        let mut frames = self.lambda_answers.borrow_mut();
        let read = frames.len().checked_sub(1)?;
        self.answers_read.set(self.answers_read.get().min(read));
        let frame = frames.last_mut()?;
        let key = (span, delegate.clone());
        if let Some(answer) = frame.known.get(&key) {
            return Some(answer.clone());
        }
        if !frame.missing.contains(&key) {
            frame.missing.push(key);
        }
        None
    }

    /// Infers a generic method's type arguments from its arguments
    /// (§12.6.3): `None` where inference fails. The flag says whether a type
    /// argument came from a lambda's or a method group's natural type.
    pub(super) fn infer_type_arguments(
        &self,
        parameters: &[SymbolId],
        formal: &[Type],
        by_ref: &[bool],
        arguments: &[InferenceArgument],
    ) -> Option<(HashMap<SymbolId, Type>, bool)> {
        let count = parameters.len();
        let mut inferrer = Inferrer {
            binder: self,
            parameters,
            formal,
            by_ref,
            arguments,
            fixed: vec![None; count],
            exact: vec![Vec::new(); count],
            lower: vec![Vec::new(); count],
            upper: vec![Vec::new(); count],
            dependencies: Vec::new(),
            dirty: false,
        };
        inferrer.first_phase();
        if !inferrer.second_phase() {
            return None;
        }
        let mut from_function = false;
        let mut result = HashMap::new();
        for (parameter, fixed) in parameters.iter().zip(inferrer.fixed) {
            let (ty, function) = fixed?;
            from_function |= function;
            result.insert(*parameter, ty);
        }
        Some((result, from_function))
    }

    /// An argument as inference reads it, from what `&self` can see: a
    /// lambda's written parameter types and natural type need `&mut self`,
    /// and are filled in by the caller that has it.
    pub(super) fn inference_argument(
        &self,
        argument: &crate::bound::BoundExpression,
    ) -> InferenceArgument {
        use crate::bound::BoundExpressionKind as Kind;
        match &argument.kind {
            Kind::UnboundLambda(span) => InferenceArgument::Lambda {
                span: *span,
                parameters: self.written_lambda_parameters(*span),
                returns: self.written_lambda_return(*span),
                arity: self.lambda_arity(*span),
                natural: None,
            },
            Kind::MethodGroup {
                candidates,
                receiver,
                ..
            } => InferenceArgument::Group {
                methods: candidates.clone(),
                receiver: receiver.as_ref().map(|receiver| receiver.ty.clone()),
                explicit: self.group_type_arguments(argument.span),
                natural: None,
            },
            Kind::TupleCreation(values) => InferenceArgument::Tuple(
                values.iter().map(|v| self.inference_argument(v)).collect(),
                (!contains_error(&argument.ty)).then(|| argument.ty.clone()),
            ),
            Kind::UnboundCollection(at) => match self.collection_hints.get(at) {
                Some(elements) => InferenceArgument::Collection(elements.clone()),
                None => InferenceArgument::Untyped,
            },
            _ if argument.ty.is_error() || matches!(argument.ty, Type::Null | Type::Void) => {
                InferenceArgument::Untyped
            }
            _ => InferenceArgument::Typed(argument.ty.clone()),
        }
    }
}

impl Inferrer<'_, '_> {
    fn ordinal(&self, ty: &Type) -> Option<usize> {
        let Type::TypeParameter(symbol) = ty else {
            return None;
        };
        let index = self.parameters.iter().position(|p| p == symbol)?;
        self.fixed[index].is_none().then_some(index)
    }

    fn substitution(&self) -> HashMap<SymbolId, Type> {
        self.parameters
            .iter()
            .zip(&self.fixed)
            .filter_map(|(parameter, fixed)| fixed.as_ref().map(|(ty, _)| (*parameter, ty.clone())))
            .collect()
    }

    fn really_a_type(ty: &Type) -> bool {
        !ty.is_error() && !matches!(ty, Type::Void | Type::Null)
    }

    /// Adds a bound; one that is the same type but for its tuple element
    /// names merges with it, keeping only the names both agree on.
    fn add(bounds: &mut Bounds, ty: &Type, function: bool, object: Option<&Type>) {
        match bounds
            .iter_mut()
            .find(|(known, f)| same_type(known, ty, object) && *f == function)
        {
            Some(known) => known.0 = merge_names(&known.0, ty),
            None => bounds.push((ty.clone(), function)),
        }
    }

    // ---- first phase ----

    fn first_phase(&mut self) {
        let count = self.arguments.len().min(self.formal.len());
        for index in 0..count {
            let target = self.formal[index].clone();
            let kind = if self.by_ref.get(index).copied().unwrap_or(false)
                || matches!(target, Type::Pointer(_))
            {
                Kind::Exact
            } else {
                Kind::Lower
            };
            let argument = self.arguments[index].clone();
            self.explicit_inferences(&argument, &target, kind);
        }
    }

    fn explicit_inferences(&mut self, argument: &InferenceArgument, target: &Type, kind: Kind) {
        let delegate = self.binder.delegate_signature(target);
        match argument {
            InferenceArgument::Lambda {
                parameters,
                returns,
                natural,
                ..
            } => {
                if let Some((taken, gives)) = delegate {
                    // §12.6.3.8: the parameter types a lambda wrote are
                    // exactly its delegate's, and so is a written return.
                    if let Some(written) = parameters {
                        for (written, taken) in written.iter().zip(&taken) {
                            self.exact_inference(written, taken);
                        }
                    }
                    if let Some(written) = returns
                        && !matches!(gives, Type::Void)
                    {
                        self.exact_inference(written, &gives);
                    }
                } else if let Some(natural) = natural {
                    self.bound_inference(kind, natural, target, true);
                }
            }
            InferenceArgument::Group { natural, .. } => {
                if delegate.is_none()
                    && let Some(natural) = natural
                {
                    self.bound_inference(kind, natural, target, true);
                }
            }
            InferenceArgument::Tuple(elements, ty) => {
                if let Some(wanted) = self.binder.flat_tuple_element_types(target)
                    && wanted.len() == elements.len()
                {
                    for (element, wanted) in elements.iter().zip(&wanted) {
                        self.explicit_inferences(element, wanted, kind);
                    }
                } else if let Some(ty) = ty {
                    self.bound_inference(kind, ty, target, false);
                }
            }
            InferenceArgument::Typed(ty) => {
                if Self::really_a_type(ty) {
                    self.bound_inference(kind, ty, target, false);
                }
            }
            // `F([1, 2, 3])` for an `F<T>(IEnumerable<T>)`: each element is
            // a lower bound for the element type of the parameter.
            InferenceArgument::Collection(elements) => {
                if let Some(element) = self.binder.collection_element(target) {
                    for given in elements {
                        self.explicit_inferences(given, &element, Kind::Lower);
                    }
                }
            }
            InferenceArgument::Untyped => {}
        }
    }

    fn bound_inference(&mut self, kind: Kind, source: &Type, target: &Type, function: bool) {
        match kind {
            Kind::Exact => self.exact(source, target, function),
            Kind::Lower => self.lower_bound(source, target, function),
            Kind::Upper => self.upper_bound(source, target, function),
        }
    }

    // ---- second phase ----

    fn second_phase(&mut self) -> bool {
        self.initialize_dependencies();
        // Each round fixes at least one type parameter or fails, so this
        // ends; the bound is there for safety.
        for _ in 0..=self.parameters.len() + 1 {
            if self.fixed.iter().all(Option::is_some) {
                return true;
            }
            self.output_inferences();
            match self.fix_where(|this, index| !this.depends_on_any(index)) {
                Some(true) => continue,
                Some(false) => return false,
                None => {}
            }
            match self.fix_where(|this, index| this.any_depends_on(index)) {
                Some(true) => continue,
                Some(false) => return false,
                None => return false,
            }
        }
        self.fixed.iter().all(Option::is_some)
    }

    /// Fixes every unfixed type parameter with bounds that `predicate`
    /// picks: `None` where there is none, `Some(false)` where one could not
    /// be fixed.
    fn fix_where(&mut self, predicate: impl Fn(&mut Self, usize) -> bool) -> Option<bool> {
        let mut picked = Vec::new();
        for index in 0..self.parameters.len() {
            if self.fixed[index].is_none() && self.has_bound(index) && predicate(self, index) {
                picked.push(index);
            }
        }
        if picked.is_empty() {
            return None;
        }
        let mut ok = true;
        for index in picked {
            if !self.fix(index) {
                ok = false;
            }
        }
        Some(ok)
    }

    fn has_bound(&self, index: usize) -> bool {
        !self.exact[index].is_empty()
            || !self.lower[index].is_empty()
            || !self.upper[index].is_empty()
    }

    fn output_inferences(&mut self) {
        let count = self.arguments.len().min(self.formal.len());
        for index in 0..count {
            let argument = self.arguments[index].clone();
            let target = self.formal[index].clone();
            self.output_inferences_of(&argument, &target);
        }
    }

    fn output_inferences_of(&mut self, argument: &InferenceArgument, target: &Type) {
        if let InferenceArgument::Tuple(elements, _) = argument {
            if let Some(wanted) = self.binder.flat_tuple_element_types(target)
                && wanted.len() == elements.len()
            {
                for (element, wanted) in elements.iter().zip(&wanted) {
                    self.output_inferences_of(element, wanted);
                }
            }
            return;
        }
        if self.unfixed_in_output(argument, target) && !self.unfixed_in_input(argument, target) {
            self.output_type_inference(argument, target);
        }
    }

    /// The delegate a lambda or a method group would be handed as, with its
    /// parameter and return types; `None` for any other argument.
    fn function_signature(
        &self,
        argument: &InferenceArgument,
        target: &Type,
    ) -> Option<(Vec<Type>, Type)> {
        match argument {
            InferenceArgument::Lambda { .. } | InferenceArgument::Group { .. } => {
                self.binder.delegate_signature(target)
            }
            _ => None,
        }
    }

    fn input_contains(
        &self,
        argument: &InferenceArgument,
        target: &Type,
        parameter: usize,
    ) -> bool {
        self.function_signature(argument, target)
            .is_some_and(|(taken, _)| {
                taken
                    .iter()
                    .any(|ty| mentions(ty, self.parameters[parameter]))
            })
    }

    fn output_contains(
        &self,
        argument: &InferenceArgument,
        target: &Type,
        parameter: usize,
    ) -> bool {
        self.function_signature(argument, target)
            .is_some_and(|(_, gives)| mentions(&gives, self.parameters[parameter]))
    }

    fn unfixed_in_input(&self, argument: &InferenceArgument, target: &Type) -> bool {
        (0..self.parameters.len()).any(|index| {
            self.fixed[index].is_none() && self.input_contains(argument, target, index)
        })
    }

    fn unfixed_in_output(&self, argument: &InferenceArgument, target: &Type) -> bool {
        (0..self.parameters.len()).any(|index| {
            self.fixed[index].is_none() && self.output_contains(argument, target, index)
        })
    }

    fn output_type_inference(&mut self, argument: &InferenceArgument, target: &Type) {
        let Some((_, gives)) = self.binder.delegate_signature(target) else {
            return;
        };
        if matches!(gives, Type::Void) {
            return;
        }
        let fixed_target = target.substitute(&self.substitution());
        let Some((taken, _)) = self.binder.delegate_signature(&fixed_target) else {
            return;
        };
        match argument {
            InferenceArgument::Lambda {
                span,
                parameters,
                arity,
                ..
            } => {
                if arity.is_some_and(|arity| arity != taken.len()) {
                    return;
                }
                if let Some(written) = parameters
                    && (written.len() != taken.len()
                        || written
                            .iter()
                            .zip(&taken)
                            .any(|(written, taken)| !self.binder.identical(written, taken)))
                {
                    return;
                }
                let Some(answer) = self.binder.lambda_answer(*span, &fixed_target) else {
                    return;
                };
                if let Some(returns) = answer.returns
                    && Self::really_a_type(&returns)
                {
                    self.lower_bound(&returns, &gives, false);
                }
            }
            InferenceArgument::Group {
                methods,
                receiver,
                explicit,
                ..
            } => {
                if let Some(returns) =
                    self.binder
                        .group_member_return(methods, receiver.is_some(), &taken, explicit)
                {
                    let returns = match receiver {
                        Some(receiver) => {
                            returns.substitute(&self.binder.binder.type_substitution(receiver))
                        }
                        None => returns,
                    };
                    if Self::really_a_type(&returns) {
                        self.lower_bound(&returns, &gives, false);
                    }
                }
            }
            _ => {}
        }
    }

    // ---- dependencies ----

    fn depends_directly_on(&self, i: usize, j: usize) -> bool {
        let count = self.arguments.len().min(self.formal.len());
        (0..count).any(|index| {
            let (argument, target) = (&self.arguments[index], &self.formal[index]);
            self.input_contains(argument, target, j) && self.output_contains(argument, target, i)
        })
    }

    fn initialize_dependencies(&mut self) {
        let count = self.parameters.len();
        self.dependencies = vec![vec![Dependency::Unknown; count]; count];
        for i in 0..count {
            for j in 0..count {
                if self.depends_directly_on(i, j) {
                    self.dependencies[i][j] = Dependency::Direct;
                }
            }
        }
        self.deduce_all_dependencies();
    }

    fn deduce_all_dependencies(&mut self) {
        let count = self.parameters.len();
        loop {
            let mut progress = false;
            for i in 0..count {
                for j in 0..count {
                    if self.dependencies[i][j] == Dependency::Unknown
                        && (0..count).any(|k| {
                            self.dependencies[i][k].depends() && self.dependencies[k][j].depends()
                        })
                    {
                        self.dependencies[i][j] = Dependency::Indirect;
                        progress = true;
                    }
                }
            }
            if !progress {
                break;
            }
        }
        for row in &mut self.dependencies {
            for cell in row {
                if *cell == Dependency::Unknown {
                    *cell = Dependency::NotDependent;
                }
            }
        }
        self.dirty = false;
    }

    fn depends_on(&mut self, i: usize, j: usize) -> bool {
        if self.dirty {
            for row in &mut self.dependencies {
                for cell in row {
                    if *cell == Dependency::Indirect {
                        *cell = Dependency::Unknown;
                    }
                }
            }
            self.deduce_all_dependencies();
        }
        self.dependencies[i][j].depends()
    }

    fn depends_on_any(&mut self, i: usize) -> bool {
        (0..self.parameters.len()).any(|j| self.depends_on(i, j))
    }

    fn any_depends_on(&mut self, i: usize) -> bool {
        (0..self.parameters.len()).any(|j| self.depends_on(j, i))
    }

    // ---- exact, lower and upper bound inference ----

    /// A tuple as the `ValueTuple` it is, past seven elements.
    fn normalized(&self, ty: &Type) -> Type {
        match ty {
            Type::Tuple(elements) if elements.len() > 7 => self.binder.tuple_as_named(elements),
            _ => ty.clone(),
        }
    }

    fn tuple_pair(&self, source: &Type, target: &Type) -> Option<(Vec<Type>, Vec<Type>)> {
        if !matches!(source, Type::Tuple(_)) && !matches!(target, Type::Tuple(_)) {
            return None;
        }
        let (source, target) = (
            self.binder.tuple_element_types(source)?,
            self.binder.tuple_element_types(target)?,
        );
        (source.len() == target.len()).then_some((source, target))
    }

    fn exact_inference(&mut self, source: &Type, target: &Type) {
        self.exact(source, target, false);
    }

    fn exact(&mut self, source: &Type, target: &Type, function: bool) {
        let (source, target) = (&self.normalized(source), &self.normalized(target));
        if let (Some(source), Some(target)) = (
            self.binder.binder.nullable_underlying(source),
            self.binder.binder.nullable_underlying(target),
        ) {
            self.exact(&source, &target, function);
            return;
        }
        if let Some(index) = self.ordinal(target) {
            let object = self.binder.binder.object_type();
            Self::add(&mut self.exact[index], source, function, object.as_ref());
            return;
        }
        if self.span_inference(source, target, function, true) {
            return;
        }
        match (source, target) {
            (
                Type::Array { element, rank },
                Type::Array {
                    element: wanted,
                    rank: wanted_rank,
                },
            ) if rank == wanted_rank => self.exact(element, wanted, function),
            (Type::Pointer(source), Type::Pointer(target)) => self.exact(source, target, function),
            (Type::FunctionPointer(source), Type::FunctionPointer(target)) => {
                self.function_pointer_inference(source, target, Kind::Exact, function);
            }
            _ => {
                if let Some((source, target)) = self.tuple_pair(source, target) {
                    for (source, target) in source.iter().zip(&target) {
                        self.exact(source, target, function);
                    }
                } else if let (
                    Type::Named {
                        symbol,
                        type_arguments,
                    },
                    Type::Named {
                        symbol: wanted,
                        type_arguments: wanted_arguments,
                    },
                ) = (source, target)
                    && symbol == wanted
                    && type_arguments.len() == wanted_arguments.len()
                {
                    for (source, target) in type_arguments.iter().zip(wanted_arguments) {
                        self.exact(source, target, function);
                    }
                }
            }
        }
    }

    /// Inference between two function pointer types. A reference type a
    /// pointer returns varies with it (covariance) and one it takes against
    /// it (contravariance), as for delegates, and so does a function pointer
    /// of one; everything else, and every `ref` of either, has to be the same
    /// type.
    fn function_pointer_inference(
        &mut self,
        source: &crate::types::FunctionPointer,
        target: &crate::types::FunctionPointer,
        kind: Kind,
        function: bool,
    ) {
        if source.parameters.len() != target.parameters.len()
            || source.convention != target.convention
            || source.modifiers != target.modifiers
            || source.returns_ref != target.returns_ref
            || source
                .parameters
                .iter()
                .zip(&target.parameters)
                .any(|((source, _), (target, _))| source != target)
        {
            return;
        }
        let returned = if kind == Kind::Exact
            || source.returns_ref != RefKind::None
            || !(self.is_reference(&source.returns)
                || matches!(source.returns, Type::FunctionPointer(_)))
        {
            Kind::Exact
        } else {
            kind
        };
        self.bound_inference(returned, &source.returns, &target.returns, function);
        for ((source_ref, source), (target_ref, target)) in
            source.parameters.iter().zip(&target.parameters)
        {
            let taken = if kind == Kind::Exact
                || *source_ref != RefKind::None
                || source_ref != target_ref
                || !(self.is_reference(source) || matches!(source, Type::FunctionPointer(_)))
            {
                Kind::Exact
            } else if kind == Kind::Lower {
                Kind::Upper
            } else {
                Kind::Lower
            };
            self.bound_inference(taken, source, target, function);
        }
    }

    fn lower_bound(&mut self, source: &Type, target: &Type, function: bool) {
        let (source, target) = (&self.normalized(source), &self.normalized(target));
        if let (Some(source), Some(target)) = (
            self.binder.binder.nullable_underlying(source),
            self.binder.binder.nullable_underlying(target),
        ) {
            self.lower_bound(&source, &target, function);
            return;
        }
        if let Some(index) = self.ordinal(target) {
            let object = self.binder.binder.object_type();
            Self::add(&mut self.lower[index], source, function, object.as_ref());
            return;
        }
        if self.span_inference(source, target, function, false) {
            return;
        }
        // An array: its element against the target's, or against the
        // element of the generic collection interface a vector implements.
        if let Type::Array { element, rank } = source {
            if let Some(wanted) = self.matching_element(*rank, target) {
                if self.is_reference(element) {
                    self.lower_bound(element, &wanted, function);
                } else {
                    self.exact(element, &wanted, function);
                }
            }
            return;
        }
        if let Some((source, target)) = self.tuple_pair(source, target) {
            for (source, target) in source.iter().zip(&target) {
                self.lower_bound(source, target, function);
            }
            return;
        }
        if let (Type::FunctionPointer(source), Type::FunctionPointer(target)) = (source, target) {
            self.function_pointer_inference(source, target, Kind::Lower, function);
            return;
        }
        let Type::Named {
            symbol: definition,
            type_arguments,
        } = target
        else {
            return;
        };
        if type_arguments.is_empty() {
            return;
        }
        if let Type::Named {
            symbol,
            type_arguments: given,
        } = source
            && symbol == definition
        {
            if self.is_interface_or_delegate(*definition) {
                self.type_argument_inference(
                    *definition,
                    given,
                    type_arguments,
                    Kind::Lower,
                    function,
                );
            } else {
                for (source, target) in given.iter().zip(type_arguments) {
                    self.exact(source, target, function);
                }
            }
            return;
        }
        // The construction of the target's definition the source derives
        // from or implements: one class along the base chain, or the one
        // interface of that name it implements.
        let matches = self.constructions_of(source, *definition);
        let kind = self.type_kind(*definition);
        if kind == Some(TypeKind::Interface) {
            if let [only] = &matches[..]
                && let Type::Named {
                    type_arguments: given,
                    ..
                } = only
            {
                self.type_argument_inference(
                    *definition,
                    given,
                    type_arguments,
                    Kind::Lower,
                    function,
                );
            }
        } else if let Some(Type::Named {
            type_arguments: given,
            ..
        }) = matches.first()
        {
            for (source, target) in given.iter().zip(type_arguments) {
                self.exact(source, target, function);
            }
        }
    }

    /// C# 14 (§12.6.3.10): a `Span<V>` against an array or a `Span<U>`,
    /// and a `ReadOnlySpan<V>` against those or a `ReadOnlySpan<U>`, infer
    /// from `U` to `V` — exactly, unless the target is read-only, the
    /// inference a lower bound and `U` a reference type. Roslyn's
    /// `ExactSpanInference` and `LowerBoundSpanInference`.
    fn span_inference(
        &mut self,
        source: &Type,
        target: &Type,
        function: bool,
        exact: bool,
    ) -> bool {
        let binder = &self.binder.binder;
        if !binder.first_class_spans() {
            return false;
        }
        let Some((readonly, wanted)) = binder.span_parts(target) else {
            return false;
        };
        let given = match source {
            Type::Array { element, rank: 1 } => (**element).clone(),
            _ => match binder.span_parts(source) {
                Some((given_readonly, element)) if readonly || !given_readonly => element,
                _ => return false,
            },
        };
        if exact || !readonly || !self.is_reference(&given) {
            self.exact(&given, &wanted, function);
        } else {
            self.lower_bound(&given, &wanted, function);
        }
        true
    }

    fn upper_bound(&mut self, source: &Type, target: &Type, function: bool) {
        let (source, target) = (&self.normalized(source), &self.normalized(target));
        if let (Some(source), Some(target)) = (
            self.binder.binder.nullable_underlying(source),
            self.binder.binder.nullable_underlying(target),
        ) {
            self.upper_bound(&source, &target, function);
            return;
        }
        if let Some(index) = self.ordinal(target) {
            Self::add(&mut self.upper[index], source, function, None);
            return;
        }
        if let Type::Array { element, rank } = target {
            if let Some(given) = self.matching_element(*rank, source) {
                if self.is_reference(&given) {
                    self.upper_bound(&given, element, function);
                } else {
                    self.exact(&given, element, function);
                }
            }
            return;
        }
        if let Some((source, target)) = self.tuple_pair(source, target) {
            for (source, target) in source.iter().zip(&target) {
                self.exact(source, target, function);
            }
            return;
        }
        if let (Type::FunctionPointer(source), Type::FunctionPointer(target)) = (source, target) {
            self.function_pointer_inference(source, target, Kind::Upper, function);
            return;
        }
        let Type::Named {
            symbol: definition,
            type_arguments: given,
        } = source
        else {
            return;
        };
        if given.is_empty() {
            return;
        }
        if let Type::Named {
            symbol,
            type_arguments,
        } = target
            && symbol == definition
        {
            if self.is_interface_or_delegate(*definition) {
                self.type_argument_inference(
                    *definition,
                    given,
                    type_arguments,
                    Kind::Upper,
                    function,
                );
            } else {
                for (source, target) in given.iter().zip(type_arguments) {
                    self.exact(source, target, function);
                }
            }
            return;
        }
        let matches = self.constructions_of(target, *definition);
        let kind = self.type_kind(*definition);
        if kind == Some(TypeKind::Interface) {
            if let [only] = &matches[..]
                && let Type::Named { type_arguments, .. } = only
            {
                self.type_argument_inference(
                    *definition,
                    given,
                    type_arguments,
                    Kind::Upper,
                    function,
                );
            }
        } else if let Some(Type::Named { type_arguments, .. }) = matches.first() {
            for (source, target) in given.iter().zip(type_arguments) {
                self.exact(source, target, function);
            }
        }
    }

    /// Type arguments of one generic interface or delegate against another
    /// construction of it, each as its variance says: an `out` one keeps the
    /// direction, an `in` one reverses it, and an invariant or value-typed
    /// one is exact.
    fn type_argument_inference(
        &mut self,
        definition: SymbolId,
        source: &[Type],
        target: &[Type],
        kind: Kind,
        function: bool,
    ) {
        let variances = self.variances(definition);
        for (index, (source, target)) in source.iter().zip(target).enumerate() {
            let variance = variances.get(index).copied().unwrap_or(Variance::None);
            let reference = self.is_reference(source);
            match (reference, variance, kind) {
                (true, Variance::Out, Kind::Lower) | (true, Variance::In, Kind::Upper) => {
                    self.lower_bound(source, target, function);
                }
                (true, Variance::In, Kind::Lower) | (true, Variance::Out, Kind::Upper) => {
                    self.upper_bound(source, target, function);
                }
                _ => self.exact(source, target, function),
            }
        }
    }

    fn variances(&self, definition: SymbolId) -> Vec<Variance> {
        let symbols = self.binder.binder.compilation().symbols();
        symbols
            .get(definition)
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
            .unwrap_or_default()
    }

    fn type_kind(&self, symbol: SymbolId) -> Option<TypeKind> {
        self.binder
            .binder
            .compilation()
            .symbols()
            .get(symbol)
            .type_kind()
    }

    fn is_interface_or_delegate(&self, symbol: SymbolId) -> bool {
        matches!(
            self.type_kind(symbol),
            Some(TypeKind::Interface | TypeKind::Delegate)
        )
    }

    fn is_reference(&self, ty: &Type) -> bool {
        ty.is_reference_type(self.binder.binder.compilation().symbols())
    }

    /// The element type an array of this rank matches in `other`: another
    /// array's of the same rank, or the type argument of a generic
    /// collection interface a vector implements.
    fn matching_element(&self, rank: usize, other: &Type) -> Option<Type> {
        match other {
            Type::Array {
                element,
                rank: other_rank,
            } => (*other_rank == rank).then(|| (**element).clone()),
            Type::Named {
                symbol,
                type_arguments,
            } if rank == 1 && type_arguments.len() == 1 => {
                let name = self
                    .binder
                    .binder
                    .compilation()
                    .symbols()
                    .qualified_name(*symbol);
                matches!(
                    name.as_str(),
                    "System.Collections.Generic.IEnumerable`1"
                        | "System.Collections.Generic.ICollection`1"
                        | "System.Collections.Generic.IList`1"
                        | "System.Collections.Generic.IReadOnlyCollection`1"
                        | "System.Collections.Generic.IReadOnlyList`1"
                )
                .then(|| type_arguments[0].clone())
            }
            _ => None,
        }
    }

    /// Every construction of `definition` among the types `ty` derives from
    /// and implements, however far up, without repeats.
    fn constructions_of(&self, ty: &Type, definition: SymbolId) -> Vec<Type> {
        let mut found: Vec<Type> = Vec::new();
        let mut seen: Vec<Type> = Vec::new();
        let mut queue: Vec<Type> = self.binder.binder.direct_bases(ty);
        while let Some(next) = queue.pop() {
            if seen.contains(&next) || seen.len() > 256 {
                continue;
            }
            seen.push(next.clone());
            if next.symbol() == Some(definition) {
                if !found.contains(&next) {
                    found.push(next.clone());
                }
                continue;
            }
            queue.extend(self.binder.binder.direct_bases(&next));
        }
        found
    }

    // ---- fixing ----

    fn fix(&mut self, index: usize) -> bool {
        match self.fixed_type(index) {
            Some(fixed) => {
                self.fixed[index] = Some(fixed);
                for other in 0..self.parameters.len() {
                    if !self.dependencies.is_empty() {
                        self.dependencies[index][other] = Dependency::NotDependent;
                        self.dependencies[other][index] = Dependency::NotDependent;
                    }
                }
                self.dirty = true;
                true
            }
            None => false,
        }
    }

    /// §12.6.3.12: the candidates are the bounds; a lower bound rules out
    /// every candidate it does not convert to and an upper bound every one
    /// that does not convert to it; what is left must hold exactly one type
    /// every other one converts to.
    fn fixed_type(&self, index: usize) -> Option<(Type, bool)> {
        let (exact, lower, upper) = (&self.exact[index], &self.lower[index], &self.upper[index]);
        let has_function = lower.iter().any(|(_, f)| *f);
        let has_other = [exact, lower, upper]
            .iter()
            .any(|bounds| bounds.iter().any(|(_, f)| !*f));
        let keep = |(_, function): &&(Type, bool)| !(has_function && has_other && *function);
        let lower: Vec<&(Type, bool)> = lower.iter().filter(keep).collect();

        // `dynamic` and `object` are one candidate unless an upper bound
        // takes a side: then they are two, and `Func<object, dynamic>`
        // against `Func<T, T>` has none.
        let object = self
            .binder
            .binder
            .object_type()
            .filter(|_| upper.is_empty());
        let object = object.as_ref();
        let mut candidates: Vec<(Type, bool)> = Vec::new();
        let merge_in = |candidates: &mut Vec<(Type, bool)>, (ty, function): &(Type, bool)| {
            if let Some(known) = candidates
                .iter_mut()
                .find(|(known, _)| same_type(known, ty, object))
            {
                known.0 = merge_names(&known.0, ty);
            } else {
                candidates.push((ty.clone(), *function));
            }
        };
        if exact.is_empty() {
            for bound in &lower {
                merge_in(&mut candidates, bound);
            }
            for bound in upper {
                merge_in(&mut candidates, bound);
            }
        } else {
            for bound in exact {
                merge_in(&mut candidates, bound);
            }
            if candidates.len() >= 2 {
                return None;
            }
        }
        if candidates.is_empty() {
            return None;
        }
        let initial = candidates.clone();
        for (bound, _) in &lower {
            for (candidate, _) in &initial {
                if same_type(bound, candidate, object) {
                    continue;
                }
                if !self.converts(bound, candidate) {
                    candidates.retain(|(known, _)| !same_type(known, candidate, object));
                }
            }
        }
        for (bound, _) in upper {
            for (candidate, _) in &initial {
                if same_type(bound, candidate, object) {
                    continue;
                }
                if !self.converts(candidate, bound) {
                    candidates.retain(|(known, _)| !same_type(known, candidate, object));
                }
            }
        }
        let mut best: Option<(Type, bool)> = None;
        for candidate in &candidates {
            if candidates.iter().all(|other| {
                same_type(&other.0, &candidate.0, object) || self.converts(&other.0, &candidate.0)
            }) {
                if best.is_some() {
                    return None;
                }
                best = Some(candidate.clone());
            }
        }
        best
    }

    fn converts(&self, from: &Type, to: &Type) -> bool {
        if matches!(from, Type::Dynamic) && !matches!(to, Type::Dynamic) {
            return false;
        }
        self.binder.binder.converts_implicitly(from, to)
    }
}

/// Whether a type is, or is made of, an error.
fn contains_error(ty: &Type) -> bool {
    match ty {
        Type::Error | Type::Void => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(contains_error),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            contains_error(element)
        }
        Type::Tuple(elements) => elements.iter().any(|element| contains_error(&element.ty)),
        _ => false,
    }
}

/// Whether a type mentions the type parameter, however deep.
pub(super) fn mentions(ty: &Type, parameter: SymbolId) -> bool {
    match ty {
        Type::TypeParameter(symbol) => *symbol == parameter,
        Type::Named { type_arguments, .. } => type_arguments
            .iter()
            .any(|argument| mentions(argument, parameter)),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            mentions(element, parameter)
        }
        Type::Tuple(elements) => elements
            .iter()
            .any(|element| mentions(&element.ty, parameter)),
        _ => false,
    }
}

/// Whether two bounds are one type, as far as inference is concerned: the
/// same but for tuple element names and for `dynamic` standing where
/// `object` does, which the identity conversion makes no difference of.
fn same_type(first: &Type, second: &Type, object: Option<&Type>) -> bool {
    match (first, second) {
        (Type::Dynamic, other) | (other, Type::Dynamic) => {
            matches!(other, Type::Dynamic) || object == Some(other)
        }
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b)
                    .all(|(a, b)| same_type(&a.ty, &b.ty, object))
        }
        (
            Type::Named {
                symbol: a,
                type_arguments: x,
            },
            Type::Named {
                symbol: b,
                type_arguments: y,
            },
        ) => a == b && x.len() == y.len() && x.iter().zip(y).all(|(x, y)| same_type(x, y, object)),
        (
            Type::Array {
                element: a,
                rank: x,
            },
            Type::Array {
                element: b,
                rank: y,
            },
        ) => x == y && same_type(a, b, object),
        (Type::Pointer(a), Type::Pointer(b)) | (Type::ByRef(a), Type::ByRef(b)) => {
            same_type(a, b, object)
        }
        _ => first == second,
    }
}

/// Two candidates that are one type but for their tuple element names, as
/// one: a name both give stays, a name they disagree on goes.
fn merge_names(first: &Type, second: &Type) -> Type {
    match (first, second) {
        (Type::Tuple(a), Type::Tuple(b)) if a.len() == b.len() => Type::Tuple(
            a.iter()
                .zip(b)
                .map(|(a, b)| TupleElement {
                    name: if a.name == b.name {
                        a.name.clone()
                    } else {
                        None
                    },
                    ty: merge_names(&a.ty, &b.ty),
                })
                .collect(),
        ),
        (
            Type::Named {
                symbol,
                type_arguments: a,
            },
            Type::Named {
                type_arguments: b, ..
            },
        ) if a.len() == b.len() => Type::Named {
            symbol: *symbol,
            type_arguments: a.iter().zip(b).map(|(a, b)| merge_names(a, b)).collect(),
        },
        (Type::Array { element: a, rank }, Type::Array { element: b, .. }) => Type::Array {
            element: Box::new(merge_names(a, b)),
            rank: *rank,
        },
        (Type::Dynamic, _) | (_, Type::Dynamic) => Type::Dynamic,
        _ => first.clone(),
    }
}
