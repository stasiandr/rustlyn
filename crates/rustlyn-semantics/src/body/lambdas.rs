//! Lambdas, local functions and method groups: binding them against the
//! delegate they become, and letting them take part in overload resolution.

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::Evidence;
use super::inference::LambdaAnswer;
use super::natural::invoke_parameters_ref_kinds;
use super::{
    BodyBinder, Fit, LambdaFrame, LambdaProbe, Resolved, ThroughLambdas, arity_fits, generality,
};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundLambda, BoundLocalFunction, BoundStatement,
    BoundStatementKind,
};
use crate::symbol::{Modifiers, RefKind, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

/// What an editor's binding guesses a lambda of a call that resolved to
/// nothing takes and returns (see `guess_lambda_parameters`).
pub(super) struct LambdaGuess {
    /// Its parameter types, an error for each nothing said.
    parameters: Vec<Type>,
    /// What it returns, an error where nothing fixed it.
    returns: Type,
    /// How good a guess it is: whether the body took these parameters,
    /// then how many of them are known.
    score: (bool, usize),
}

impl BodyBinder<'_> {
    /// Picks the overload a delegate type asks for and wraps it up.
    ///
    /// The delegate's signature lives on its `Invoke`, in metadata and here
    /// alike, so the match is against that method's parameters.
    pub(super) fn convert_method_group(
        &mut self,
        value: BoundExpression,
        target: &Type,
    ) -> BoundExpression {
        let span = value.span;
        let BoundExpressionKind::MethodGroup {
            receiver,
            candidates,
        } = value.kind
        else {
            return value;
        };
        let symbols = self.binder.compilation().symbols();
        let invoke = target
            .symbol()
            .filter(|symbol| symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate))
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied());
        let Some(invoke) = invoke else {
            return BoundExpression::error(span);
        };
        let wanted: Vec<Type> = symbols
            .get(invoke)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default()
            .into_iter()
            .map(|parameter| self.member_type(parameter, target))
            .collect();

        let wanted_ref_kinds = invoke_parameters_ref_kinds(symbols, invoke);
        // Where no method of the group fits, the extension methods of that
        // name are looked at next, as for a call (§12.8.10.3).
        let group_type = value.ty.clone();
        let fallback = match (&receiver, candidates.first()) {
            (Some(on), Some(first))
                if !candidates.iter().any(|candidate| {
                    symbols
                        .get(*candidate)
                        .as_method()
                        .is_some_and(|detail| detail.is_extension)
                }) && !matches!(
                    on.kind,
                    BoundExpressionKind::TypeExpression(_) | BoundExpressionKind::Base
                ) =>
            {
                Some((on.clone(), symbols.get(*first).name.clone()))
            }
            _ => None,
        };
        let receiver_type = receiver.as_ref().map(|receiver| receiver.ty.clone());
        // `Program.M<int>` says what the method's type arguments are, and
        // only a method with that many is meant.
        let explicit = self.group_type_arguments(span);
        let mut exact: Vec<(SymbolId, Vec<Type>)> = Vec::new();
        let mut widened: Vec<(SymbolId, Vec<Type>, Vec<Type>)> = Vec::new();
        // A delegate that returns by reference takes a method returning a
        // reference to exactly its type, and nothing else (§10.8).
        let by_ref = |member: SymbolId| {
            let mut sink = Diagnostics::new();
            symbols.get(member).modifiers.contains(Modifiers::REF)
                || matches!(self.binder.type_of(member, &mut sink), Type::ByRef(_))
        };
        let wants_ref = by_ref(invoke);
        // The instance methods are asked first; the extension methods of the
        // group only where none of them serves (§12.8.10.3).
        let (instance, extension): (Vec<SymbolId>, Vec<SymbolId>) =
            candidates.iter().copied().partition(|candidate| {
                receiver.is_none()
                    || !symbols
                        .get(*candidate)
                        .as_method()
                        .is_some_and(|detail| detail.is_extension)
            });
        let mut from_extensions = false;
        for (pass, candidates) in [instance, extension].into_iter().enumerate() {
            if pass == 1 && (!exact.is_empty() || !widened.is_empty()) {
                break;
            }
            from_extensions = pass == 1;
            for candidate in candidates {
                let Some(detail) = symbols.get(candidate).as_method() else {
                    continue;
                };
                if wants_ref && !by_ref(candidate) {
                    continue;
                }
                let own = detail.type_parameters.clone();
                if !explicit.is_empty() && own.len() != explicit.len() {
                    continue;
                }
                // An extension method closed over its receiver takes the rest:
                // the delegate's parameters are the method's after the first.
                let skip = usize::from(detail.is_extension && receiver.is_some());
                if detail.parameters.len() != wanted.len() + skip {
                    continue;
                }
                // `F(in DateTime)` is no `Action<DateTime>`: the `ref` kinds have
                // to be the delegate's too, but for a `ref` of the delegate's
                // taken by an `in` or `ref readonly` (C# 12, with a warning).
                let ref_to_in = self.language_version().at_least(LanguageVersion::CSharp12);
                if detail
                    .parameters
                    .iter()
                    .skip(skip)
                    .zip(&wanted_ref_kinds)
                    .any(|(parameter, wanted)| {
                        symbols
                            .get(*parameter)
                            .as_parameter()
                            .is_some_and(|detail| {
                                !target_ref_kind_fits(detail.ref_kind, *wanted, ref_to_in)
                            })
                    })
                {
                    continue;
                }
                // The parameters as the receiver's construction reads them:
                // `HashSet<string>.Contains` takes a `string`, not the `T` it was
                // declared with.
                let through = match (&receiver_type, skip) {
                    (Some(ty), 0) if !ty.is_error() => ty.clone(),
                    _ => symbols
                        .get(candidate)
                        .container
                        .map_or(Type::Error, |container| self.binder.self_type(container)),
                };
                if wants_ref
                    && detail.type_parameters.is_empty()
                    && self.member_type(candidate, &through).value()
                        != self.member_type(invoke, target).value()
                {
                    continue;
                }
                let mut declared: Vec<Type> = detail
                    .parameters
                    .iter()
                    .skip(skip)
                    .map(|parameter| self.member_type(*parameter, &through))
                    .collect();
                // A generic method's type arguments come from the delegate:
                // `SkipBad<T>` handed to a `Skipper<Node>` is `SkipBad<Node>`
                // (§12.6.3 inference, from the delegate's parameters).
                let mut type_arguments = Vec::new();
                if !own.is_empty() {
                    let mut inferred: HashMap<SymbolId, Type> = HashMap::new();
                    if explicit.is_empty() {
                        // An extension method closed over its receiver infers
                        // from the receiver too: `principal.RemoveDetail` is a
                        // `RemoveDetail<Principal, …>`.
                        if skip == 1
                            && let (Some(receiver), Some(first)) =
                                (&receiver_type, detail.parameters.first())
                        {
                            let mut sink = Diagnostics::new();
                            let first = self.binder.type_of(*first, &mut sink);
                            self.infer_into(&first, receiver, &own, &mut inferred);
                        }
                        for (parameter, expected) in declared.iter().zip(&wanted) {
                            self.infer_into(parameter, expected, &own, &mut inferred);
                        }
                    } else {
                        inferred.extend(own.iter().copied().zip(explicit.iter().cloned()));
                    }
                    // `new Store<object, T?>(GetAttribute<T>)`: a type parameter
                    // that only the return type mentions is settled by what the
                    // delegate returns.
                    if own
                        .iter()
                        .any(|parameter| !inferred.contains_key(parameter))
                    {
                        let gives = self.member_type(candidate, &through);
                        let wants = self.member_type(invoke, target);
                        if !matches!(gives, Type::Void) && !matches!(wants, Type::Void) {
                            self.infer_into(&gives, &wants, &own, &mut inferred);
                        }
                    }
                    if own.iter().any(|parameter| {
                        inferred
                            .get(parameter)
                            .is_none_or(|argument| argument.is_error())
                    }) {
                        continue;
                    }
                    // `new object().M<int>` is no `M<T>() where T : class`.
                    if !self.satisfies_constraints(&own, &inferred) {
                        continue;
                    }
                    type_arguments = own
                        .iter()
                        .map(|parameter| inferred[parameter].clone())
                        .collect();
                    declared = declared
                        .into_iter()
                        .map(|parameter| parameter.substitute(&inferred))
                        .collect();
                }
                // `F<(int, dynamic)>` is an `Action<(int X, object Y)>`: the
                // names and the `dynamic` are the compiler's, not the type's.
                if declared == wanted
                    || declared.iter().zip(&wanted).all(|(declared, expected)| {
                        self.binder.identity_converts(declared, expected)
                    })
                {
                    exact.push((candidate, type_arguments));
                    continue;
                }
                // §10.8: the method may take more than the delegate hands it —
                // `ReferenceEquals(object, object)` serves a `Func<string, string,
                // bool>` — as long as each is a reference conversion.
                // A `T` a class constraint makes a reference is one too:
                // `(Action<T>)E.Target` with `T : C` reaches `Target(C)`.
                if declared.iter().zip(&wanted).all(|(declared, expected)| {
                    (self.binder.held_by_reference(declared)
                        && self.binder.held_by_reference(expected)
                        && self.binder.converts_implicitly(expected, declared))
                        || declared == expected
                }) {
                    widened.push((candidate, type_arguments, declared));
                }
            }
        }
        // Of several that take more than the delegate hands them, the one
        // taking the least (§12.6.4.5): `M(Derived1)` over `M(Base)` for a
        // delegate handing over a `Derived2`.
        let widened = widened
            .into_iter()
            .reduce(|best, candidate| {
                let narrower = candidate
                    .2
                    .iter()
                    .zip(&best.2)
                    .all(|(ours, theirs)| self.binder.converts_implicitly(ours, theirs));
                if narrower && candidate.2 != best.2 {
                    candidate
                } else {
                    best
                }
            })
            .map(|(method, type_arguments, _)| (method, type_arguments));
        // Of several that take exactly what the delegate hands them, a
        // derived type's own puts out what its bases declare — an override
        // counting as its base's — and one that is not generic comes first.
        // Extension methods come nearest scope first, and the nearest wins.
        if from_extensions {
            exact.truncate(1);
        }
        let kept = self
            .binder
            .reduce_overloads(exact.iter().map(|(method, _)| *method).collect());
        exact.retain(|(method, _)| kept.contains(method));
        let exact = exact
            .iter()
            .find(|(method, _)| {
                symbols
                    .get(*method)
                    .as_method()
                    .is_some_and(|detail| detail.type_parameters.is_empty())
            })
            .or(exact.first())
            .cloned();
        let Some((method, type_arguments)) = exact.or(widened) else {
            if let Some((on, name)) = fallback {
                let extensions: Vec<SymbolId> = self
                    .extensions_here(&name)
                    .into_iter()
                    .filter(|method| self.extension_takes(*method, &on.ty))
                    .collect();
                if !extensions.is_empty() {
                    let group = BoundExpression::new(
                        BoundExpressionKind::MethodGroup {
                            receiver: Some(on),
                            candidates: extensions,
                        },
                        group_type,
                        span,
                    );
                    return self.convert_method_group(group, target);
                }
            }
            return BoundExpression::error(span);
        };
        // A delegate closed over a value would close over a copy of it, and
        // an extension method on a value type gets none (CS1113): `x.Goo`
        // with `x` an `int` makes no delegate.
        if receiver.is_some()
            && let Some(detail) = symbols.get(method).as_method()
            && detail.is_extension
            && let Some(first) = detail.parameters.first()
        {
            let own = detail.type_parameters.clone();
            let substitution: std::collections::HashMap<SymbolId, Type> = own
                .iter()
                .copied()
                .zip(type_arguments.iter().cloned())
                .collect();
            let this_type = self
                .binder
                .type_of(*first, &mut Diagnostics::new())
                .substitute(&substitution);
            if !this_type.is_error()
                && !matches!(this_type, Type::TypeParameter(_))
                && !this_type.is_reference_type(symbols)
            {
                let (method_name, shown) = (
                    self.binder.compilation().symbols().qualified_name(method),
                    self.display(&this_type),
                );
                self.report(
                    rustlyn_diagnostics::ErrorCode::ErrValueTypeExtDelegate,
                    span,
                    &[&method_name, &shown],
                );
                return BoundExpression::error(span);
            }
        }
        // `base.F` names the base's method itself, not whatever overrides it.
        let virtual_dispatch = receiver
            .as_ref()
            .is_some_and(|receiver| !matches!(receiver.kind, BoundExpressionKind::Base))
            && self.is_virtual_call(method, None);
        // A method group written with nothing in front of it still needs the
        // receiver the delegate will be closed over: `Func<int, int> step =
        // Twice;` inside an instance method names an instance method, and a
        // delegate to one may not be made over a null.
        let receiver = match receiver {
            Some(receiver) => Some(receiver),
            None => self.implicit_receiver(method, span),
        };
        // The overload the delegate chose is what the group's name means
        // now, to an editor asking too: `del = Cubic.Out` for a three-
        // argument delegate is `Out(float, float, float)`, not the first
        // `Out` the lookup came to.
        // The name is the group's own, or the right of `Type.Name` — its
        // identifier, before any `<T>` written after it.
        if let Some(name) = self
            .syntax_at(span)
            .and_then(|group| match group.kind() {
                rustlyn_syntax::SyntaxKind::SimpleMemberAccessExpression => group.children().last(),
                _ => Some(group),
            })
            .and_then(|name| name.first_token())
            .filter(|token| token.kind() == rustlyn_syntax::SyntaxKind::IdentifierToken)
        {
            let symbols = self.binder.compilation().symbols();
            let is_method = |id: SymbolId| symbols.get(id).kind == SymbolKind::Method;
            if let Some(crate::bound::BoundSymbol::Declared(recorded)) =
                self.body.references.get(&name.span()).copied()
                && is_method(recorded)
            {
                self.body
                    .references
                    .insert(name.span(), crate::bound::BoundSymbol::Declared(method));
            }
            if let Some(&recorded) = self.body.symbols.get(&name.span())
                && is_method(recorded)
            {
                self.body.symbols.insert(name.span(), method);
            }
        }
        BoundExpression::new(
            BoundExpressionKind::DelegateCreation {
                method,
                receiver,
                virtual_dispatch,
                type_arguments,
            },
            target.clone(),
            span,
        )
    }

    /// `&M` given to a function pointer: the static method of the group
    /// whose signature the pointer's fits (§10.8 as C# 9 extends it to
    /// function pointers). `ref` kinds have to agree exactly; a parameter or
    /// a return passed by value may differ by a reference conversion, in the
    /// direction a call through the pointer would need.
    pub(super) fn convert_address_of(
        &mut self,
        value: BoundExpression,
        target: &crate::types::FunctionPointer,
        target_type: &Type,
    ) -> BoundExpression {
        let span = value.span;
        let BoundExpressionKind::AddressOf { operand } = value.kind else {
            return value;
        };
        let explicit = self.group_type_arguments(operand.span);
        let BoundExpressionKind::MethodGroup {
            receiver,
            candidates,
        } = operand.kind
        else {
            return BoundExpression::error(span);
        };
        let receiver = receiver.map(|receiver| receiver.ty);
        let Some((method, type_arguments)) =
            self.address_target(&candidates, receiver.as_ref(), &explicit, target)
        else {
            return BoundExpression::error(span);
        };
        BoundExpression::new(
            BoundExpressionKind::MethodAddress {
                method,
                type_arguments,
            },
            target_type.clone(),
            span,
        )
    }

    /// The method of a group, and its type arguments, that `&M` stands for
    /// when it is given to a function pointer of this signature, if any.
    pub(super) fn address_target(
        &self,
        candidates: &[SymbolId],
        receiver: Option<&Type>,
        explicit: &[Type],
        target: &crate::types::FunctionPointer,
    ) -> Option<(SymbolId, Vec<Type>)> {
        let symbols = self.binder.compilation().symbols();
        let wanted: Vec<Type> = target.parameters.iter().map(|(_, ty)| ty.clone()).collect();
        let converts = |from: &Type, to: &Type| {
            from == to
                || ((from.is_reference_type(symbols) && to.is_reference_type(symbols))
                    || matches!(
                        (from, to),
                        (Type::FunctionPointer(_), Type::FunctionPointer(_))
                    ))
                    && self.binder.converts_implicitly(from, to)
        };
        let mut exact: Option<(SymbolId, Vec<Type>)> = None;
        let mut widened: Vec<(SymbolId, Vec<Type>, Vec<Type>)> = Vec::new();
        for &candidate in candidates {
            let symbol = symbols.get(candidate);
            let Some(detail) = symbol.as_method() else {
                continue;
            };
            if !symbol.modifiers.contains(Modifiers::STATIC)
                || detail.parameters.len() != wanted.len()
            {
                continue;
            }
            let own = detail.type_parameters.clone();
            if !explicit.is_empty() && own.len() != explicit.len() {
                continue;
            }
            let ref_to_in = self.language_version().at_least(LanguageVersion::CSharp12);
            if detail
                .parameters
                .iter()
                .zip(&target.parameters)
                .any(|(parameter, (kind, _))| {
                    symbols.get(*parameter).as_parameter().is_none_or(|detail| {
                        !target_ref_kind_fits(detail.ref_kind, *kind, ref_to_in)
                    })
                })
            {
                continue;
            }
            let through = match receiver {
                Some(receiver) if !receiver.is_error() => receiver.clone(),
                _ => symbol
                    .container
                    .map_or(Type::Error, |container| self.binder.self_type(container)),
            };
            let gives = self.member_type(candidate, &through);
            let by_reference = symbol.modifiers.contains(Modifiers::REF)
                || matches!(gives, Type::ByRef(_))
                || matches!(
                    self.binder.type_of(candidate, &mut Diagnostics::new()),
                    Type::ByRef(_)
                );
            let returns_ref = match (by_reference, detail.returns_readonly) {
                (false, _) => RefKind::None,
                (true, true) => RefKind::In,
                (true, false) => RefKind::Ref,
            };
            if returns_ref != target.returns_ref {
                continue;
            }
            let mut gives = gives.value().clone();
            let mut declared: Vec<Type> = detail
                .parameters
                .iter()
                .map(|parameter| self.member_type(*parameter, &through))
                .collect();
            let mut type_arguments = Vec::new();
            if !own.is_empty() {
                let mut inferred: HashMap<SymbolId, Type> = HashMap::new();
                if explicit.is_empty() {
                    for (parameter, expected) in declared.iter().zip(&wanted) {
                        self.infer_into(parameter, expected, &own, &mut inferred);
                    }
                    if !matches!(gives, Type::Void) {
                        self.infer_into(&gives, &target.returns, &own, &mut inferred);
                    }
                } else {
                    inferred.extend(own.iter().copied().zip(explicit.iter().cloned()));
                }
                if own.iter().any(|parameter| {
                    inferred
                        .get(parameter)
                        .is_none_or(|argument| argument.is_error())
                }) {
                    continue;
                }
                type_arguments = own
                    .iter()
                    .map(|parameter| inferred[parameter].clone())
                    .collect();
                declared = declared
                    .into_iter()
                    .map(|parameter| parameter.substitute(&inferred))
                    .collect();
                gives = gives.substitute(&inferred);
            }
            let returns_fit = if returns_ref == RefKind::None {
                converts(&gives, &target.returns)
            } else {
                gives == target.returns
            };
            if !returns_fit {
                continue;
            }
            if declared == wanted && gives == target.returns {
                exact = Some((candidate, type_arguments));
                break;
            }
            if declared
                .iter()
                .zip(&target.parameters)
                .all(|(declared, (kind, expected))| {
                    declared == expected || (*kind == RefKind::None && converts(expected, declared))
                })
            {
                widened.push((candidate, type_arguments, declared));
            }
        }
        // Of several that take more than the pointer hands them, the one
        // taking the least, as for a delegate.
        let widened = widened
            .into_iter()
            .reduce(|best, candidate| {
                let narrower = candidate
                    .2
                    .iter()
                    .zip(&best.2)
                    .all(|(ours, theirs)| self.binder.converts_implicitly(ours, theirs));
                if narrower && candidate.2 != best.2 {
                    candidate
                } else {
                    best
                }
            })
            .map(|(method, type_arguments, _)| (method, type_arguments));
        exact.or(widened)
    }

    /// Binds a local function's body inside the body that holds it.
    ///
    /// Its parameters and return type are its own, so the member is swapped
    /// for the duration; its locals and its owner's live in one list, which
    /// is what lets a name written inside it find a variable written outside.
    pub(super) fn bind_local_function(&mut self, node: &SyntaxNode) {
        self.bind_attribute_names(node);
        let symbol = self.binder.declared_symbol_at(self.tree, node);
        let outer_member = self.member;
        let outer_context =
            std::mem::replace(&mut self.context, self.binder.context_at(self.tree, node));
        if symbol.is_some() {
            self.member = symbol;
        }
        // A `static` local function cannot reach the locals around it, so
        // they are not in scope inside it at all — and a name it declares is
        // its own, whatever the method holding it called something. Roslyn
        // leans on that: `resolveIncludePath` declares the very
        // `resolvedIncludePath` its caller returns.
        let outer_scopes = node
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::StaticKeyword)
            .then(|| self.detach_scopes());
        self.push_scope();
        // A frame, exactly as a lambda gets one: what it reads of the method
        // around it is what a backend has to keep alive for it, and the
        // machinery that notices a read is the same either way.
        let return_type = symbol.map_or(Type::Error, |member| {
            let mut sink = Diagnostics::new();
            let declared = self.binder.type_of(member, &mut sink).value().clone();
            // An `async` local function returns the `T` of its `Task<T>`,
            // exactly as an `async` method does.
            if self.is_async(member) {
                self.task_result(&declared)
            } else {
                declared
            }
        });
        let outer_synthetic = std::mem::replace(&mut self.synthetic_span, node.span());
        self.lambdas.push(LambdaFrame {
            floor: self.scopes.len() - 1,
            return_type,
            captured: Vec::new(),
            captured_parameters: Vec::new(),
            captures_this: false,
            calls: Vec::new(),
            iterator: None,
            declares: symbol,
        });
        let mut bound = None;
        for child in node.children() {
            match child.kind() {
                SyntaxKind::Block => {
                    bound = Some(self.bind_block(&child));
                }
                SyntaxKind::ArrowExpressionClause => {
                    if let Some(expression) = child.children().next() {
                        let value = self.bind_expression(&expression);
                        bound = Some(self.arrow_body(&expression, value));
                    }
                }
                _ => {}
            }
        }
        let frame = self.lambdas.pop();
        self.synthetic_span = outer_synthetic;
        self.pop_scope();
        if let Some(scopes) = outer_scopes {
            self.restore_scopes(scopes);
        }
        self.member = outer_member;
        self.context = outer_context;
        // An `extern` local function has no body to bind, and is still a
        // method the body calls: it goes on the list with nothing in it.
        let bound = bound.or_else(|| {
            symbol
                .filter(|symbol| {
                    self.binder
                        .compilation()
                        .symbols()
                        .get(*symbol)
                        .modifiers
                        .contains(Modifiers::EXTERN)
                })
                .map(|_| BoundStatement::new(BoundStatementKind::Empty, node.span()))
        });
        if let (Some(symbol), Some(body), Some(frame)) = (symbol, bound, frame) {
            self.body.local_functions.push(BoundLocalFunction {
                symbol,
                body,
                iterator: frame.iterator,
                captured: frame.captured,
                captured_parameters: frame.captured_parameters,
                captures_this: frame.captures_this,
                calls: frame.calls,
            });
        }
    }

    /// The names in the attributes of a local function or a lambda, and of
    /// its parameters: `[A(N)]` reads the constant `N` of the method
    /// around it, which no binder that sees the declaration alone can
    /// find. Only the names are looked up here; what the attribute makes of
    /// them is judged with every other attribute.
    pub(super) fn bind_attribute_names(&mut self, node: &SyntaxNode) {
        let mut lists: Vec<SyntaxNode> = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::AttributeList)
            .collect();
        for parameters in node
            .children()
            .filter(|child| child.kind() == SyntaxKind::ParameterList)
        {
            for parameter in parameters.children() {
                lists.extend(
                    parameter
                        .children()
                        .filter(|child| child.kind() == SyntaxKind::AttributeList),
                );
            }
        }
        if lists.is_empty() {
            return;
        }
        let floor = self.body.diagnostics.len();
        let outer = std::mem::replace(&mut self.in_attribute, true);
        for attribute in lists.iter().flat_map(|list| list.children()) {
            if attribute.kind() == SyntaxKind::Attribute {
                self.bind_attribute_node(&attribute);
            }
        }
        self.in_attribute = outer;
        let mut found = self.body.diagnostics.split_off(floor);
        found.retain(|(_, diagnostic)| {
            diagnostic.code() == rustlyn_diagnostics::ErrorCode::ErrNameNotInContext
        });
        self.body.diagnostics.extend(found);
    }

    /// The local function of this name in scope, if there is one.
    ///
    /// The search goes outwards through the functions that hold this one: a
    /// local function inside a local function can call its siblings and its
    /// uncles alike.
    ///
    /// Two blocks may each declare one of the same name — a `try` and its
    /// `catch` — and the one whose block holds the use is the one meant.
    pub(super) fn local_function(&self, name: &str, at: TextSpan) -> Option<SymbolId> {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        let mut current = self.member;
        while let Some(member) = current {
            let found: Vec<SymbolId> = symbols
                .lookup(member, name)
                .iter()
                .copied()
                .filter(|id| {
                    symbols.get(*id).as_method().is_some_and(|detail| {
                        detail.method_kind == crate::symbol::MethodKind::LocalFunction
                    })
                })
                .collect();
            let scope_of = |id: SymbolId| {
                compilation
                    .declaration_node(id)
                    .and_then(|node| node.parent().map(SyntaxNode::span))
            };
            let within = found
                .iter()
                .copied()
                .filter_map(|id| {
                    scope_of(id)
                        .filter(|scope| scope.start() <= at.start() && at.end() <= scope.end())
                        .map(|scope| (scope.length(), id))
                })
                .min();
            if let Some((_, found)) = within {
                return Some(found);
            }
            if let Some(found) = found.first().copied() {
                return Some(found);
            }
            let container = symbols.get(member).container?;
            if symbols.get(container).kind != SymbolKind::Method {
                return None;
            }
            current = Some(container);
        }
        None
    }

    /// Settles an overload whose type parameters a lambda has to supply.
    ///
    /// `OrderBy(n => n)` cannot be resolved from its arguments: `TKey` appears
    /// only in what the lambda returns, and the lambda has no type until it is
    /// given one. So the rest of the arguments are inferred from first, the
    /// lambda is bound against the parameter that would then be its delegate,
    /// and what it turns out to return finishes the job — §12.6.3's output
    /// type inference, done for one candidate at a time.
    fn resolve_through_lambdas(
        &mut self,
        candidates: &[SymbolId],
        arguments: &mut [BoundExpression],
        receiver: &Type,
        explicit: &[Type],
    ) -> Option<Resolved> {
        self.settle_through_lambdas(candidates, arguments, receiver, explicit)
            .map(|(_, found)| self.commit_through_lambdas(found, arguments))
    }

    /// The candidate the lambdas settle on, and how well they fit it,
    /// without binding them for real: the best of the candidates, where a
    /// body that is wrong against every delegate is wrong in itself and is
    /// still reported against the first candidate it could have gone to.
    fn settle_through_lambdas(
        &mut self,
        candidates: &[SymbolId],
        arguments: &[BoundExpression],
        receiver: &Type,
        explicit: &[Type],
    ) -> Option<(Fit, ThroughLambdas)> {
        if !arguments
            .iter()
            .any(|argument| matches!(argument.kind, BoundExpressionKind::UnboundLambda(_)))
        {
            return None;
        }
        // The best so far, with how generic its declared parameters are:
        // two candidates that fit equally well are told apart by that, the
        // less generic being the more specific (§12.6.4.7). `Task.Run(async
        // () => 1)` fits both `Run<T>(Func<T>)` and `Run<T>(Func<Task<T>>)`
        // exactly, and the second is the one that makes a `Task<int>`.
        let mut best: Option<(Fit, usize, ThroughLambdas)> = None;
        for candidate in candidates {
            let symbols = self.binder.compilation().symbols();
            let substitution = self.substitution_for(*candidate, receiver);
            let Some(detail) = symbols.get(*candidate).as_method() else {
                continue;
            };
            let type_parameters = detail.type_parameters.clone();
            if type_parameters.is_empty() || !explicit.is_empty() {
                continue;
            }
            let declared: Vec<Type> = detail
                .parameters
                .clone()
                .into_iter()
                .map(|id| {
                    let mut sink = Diagnostics::new();
                    self.binder.type_of(id, &mut sink).substitute(&substitution)
                })
                .collect();
            // A `params` parameter a lambda is given for can only be in its
            // expanded form, a lambda never being an array: each argument
            // from there on is one element (§12.6.4.2).
            let mut declared = declared;
            if let Some(element) = self.params_element(*candidate, &declared) {
                let fixed = declared.len() - 1;
                let expanded = arguments.len() != declared.len()
                    || matches!(arguments[fixed].kind, BoundExpressionKind::UnboundLambda(_));
                if expanded && arguments.len() >= fixed {
                    declared.truncate(fixed);
                    declared.resize(arguments.len(), element);
                }
            }
            // Fewer arguments than parameters is what optional parameters
            // are for; `required` below says whether enough were given.
            if arguments.len() > declared.len() {
                continue;
            }

            // What the arguments that are not lambdas already say.
            let mut inferred = HashMap::new();
            for (parameter, argument) in declared.iter().zip(arguments.iter()) {
                if matches!(argument.kind, BoundExpressionKind::UnboundLambda(_)) {
                    continue;
                }
                // An `out var` has no type of its own yet either, and taking
                // one as the answer fixes the type argument as an error
                // before the lambda has been asked what it is.
                if argument.ty.is_error() {
                    continue;
                }
                self.infer_into(parameter, &argument.ty, &type_parameters, &mut inferred);
            }

            // §12.6.3.13: a lambda that writes its parameter types says what
            // the delegate's are, and through them what the method's type
            // arguments are. `(GreenNode _, BoxedMemberNames names) => names`
            // fixes two of three before the body is looked at, and without
            // them the body cannot be bound at all.
            for (index, argument) in arguments.iter().enumerate() {
                let BoundExpressionKind::UnboundLambda(span) = argument.kind else {
                    continue;
                };
                let Some(written) = self.written_lambda_parameters(span) else {
                    continue;
                };
                let target = declared[index].substitute(&inferred);
                let Some(taken) = self.delegate_parameters(&target) else {
                    continue;
                };
                if taken.len() != written.len() {
                    continue;
                }
                for (parameter, ty) in taken.iter().zip(&written) {
                    self.infer_into(parameter, ty, &type_parameters, &mut inferred);
                }
            }

            // Then each lambda, bound against the delegate the parameter has
            // become. The binding is thrown away afterwards: it was asked a
            // question, not kept.
            let floor = self.speculation_floor();
            for (index, argument) in arguments.iter().enumerate() {
                if !matches!(argument.kind, BoundExpressionKind::UnboundLambda(_)) {
                    continue;
                }
                let target = declared[index].substitute(&inferred);
                let Some(returns) = self.lambda_returns(argument, &target) else {
                    continue;
                };
                let Some(declared_return) = self.delegate_return(&target) else {
                    continue;
                };
                // An `async` lambda gives its delegate the task around what
                // its body returns, and `lambda_returns` says so: against a
                // `Func<Task<TResult>>` that fixes `TResult` to the body's
                // type, and against a `Func<TResult>` to the task itself.
                let returns = self.task_as_declared(returns, &declared_return);
                self.infer_into(&declared_return, &returns, &type_parameters, &mut inferred);
            }
            self.unwind_speculation(floor);

            if type_parameters
                .iter()
                .any(|parameter| inferred.get(parameter).is_none_or(Type::is_error))
            {
                continue;
            }
            let parameters: Vec<Type> =
                declared.iter().map(|ty| ty.substitute(&inferred)).collect();
            let required = detail
                .parameters
                .iter()
                .filter(|id| {
                    !self
                        .binder
                        .compilation()
                        .symbols()
                        .get(**id)
                        .as_parameter()
                        .is_some_and(|parameter| parameter.has_default || parameter.is_params)
                })
                .count();
            let applicable = arguments.len() >= required
                && arguments
                    .iter()
                    .zip(&parameters)
                    .all(|(argument, parameter)| {
                        // A lambda has no type yet, and an untyped expression
                        // converts to anything — so asking the usual question
                        // makes `OrderBy(kv => kv.Value)` fit the overload
                        // taking an `IComparer<T>`, which is not a delegate at
                        // all. What a lambda fits is the only thing that
                        // answers for one (§12.6.4.4).
                        if matches!(argument.kind, BoundExpressionKind::UnboundLambda(_)) {
                            return self.lambda_fits(argument, parameter);
                        }
                        self.binder.converts_implicitly(&argument.ty, parameter)
                            || self.constant_fits(argument, parameter)
                    });
            if !applicable {
                continue;
            }

            // Whether each lambda returns what its delegate now says: the
            // `Max<TSource>` taking a `Func<TSource, int>` is applicable by
            // count to `Max(info => info.State)`, and only binding the body
            // tells that an enum comes back. A candidate that merely drops a
            // value is kept in case nothing better turns up.
            let mut fit = Fit::Exact;
            for (index, argument) in arguments.iter().enumerate() {
                if matches!(argument.kind, BoundExpressionKind::UnboundLambda(_)) {
                    fit = fit.max(self.lambda_fit(argument, &parameters[index]));
                }
            }
            let how_generic: usize = declared
                .iter()
                .map(|ty| generality(ty, &type_parameters, 0))
                .sum();
            let found = ThroughLambdas {
                candidate: *candidate,
                type_parameters,
                parameters,
                inferred,
            };
            if best.as_ref().is_none_or(|(known, generic, _)| {
                fit < *known || (fit == *known && how_generic < *generic)
            }) {
                best = Some((fit, how_generic, found));
            }
        }
        best.map(|(fit, _, found)| (fit, found))
    }

    /// Settles on a candidate found through its lambdas: now that every type
    /// parameter is known, the lambdas are bound for real, against the
    /// delegates they actually have, so what they say inside is checked
    /// against the right types.
    fn commit_through_lambdas(
        &mut self,
        found: ThroughLambdas,
        arguments: &mut [BoundExpression],
    ) -> Resolved {
        let ThroughLambdas {
            candidate,
            type_parameters,
            parameters,
            inferred,
        } = found;
        for index in 0..arguments.len() {
            if !matches!(arguments[index].kind, BoundExpressionKind::UnboundLambda(_)) {
                continue;
            }
            let target = parameters[index].clone();
            let span = arguments[index].span;
            let argument = std::mem::replace(&mut arguments[index], BoundExpression::error(span));
            arguments[index] = self.convert(argument, &target);
        }
        let type_arguments: Vec<Type> = type_parameters
            .iter()
            .map(|parameter| inferred.get(parameter).cloned().unwrap_or(Type::Error))
            .collect();
        Resolved {
            method: candidate,
            type_arguments,
            substitution: inferred,
        }
    }

    /// What a lambda turns out to return, bound against `target`.
    fn lambda_returns(&mut self, lambda: &BoundExpression, target: &Type) -> Option<Type> {
        // Against an `Expression<TDelegate>` the body is bound as the
        // delegate's would be: the question is what it returns, not what it
        // is compiled into. A return type the lambda wrote is what it
        // returns, whatever the body's expression is, and the probe says so.
        let delegate = self.delegate_within(target);
        self.probe_lambda(lambda, delegate)
            .map(|probe| probe.returns)
    }

    /// What an `async` lambda gives its delegate: the `Task<int>` around the
    /// `int` its body returns, or a `Task` around nothing (§12.19.3). A
    /// lambda that is not `async` gives what it returns.
    pub(super) fn wrapped_in_task(&self, lambda: &BoundExpression, returns: Type) -> Type {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return returns;
        };
        let is_async = self.syntax_at(span).is_some_and(|node| {
            node.child_tokens()
                .any(|token| token.kind() == SyntaxKind::AsyncKeyword)
        });
        if !is_async {
            return returns;
        }
        let compilation = self.binder.compilation();
        match returns {
            Type::Void => compilation
                .type_by_metadata_name("System.Threading.Tasks.Task")
                .map_or(Type::Void, Type::named),
            result => compilation
                .type_by_metadata_name("System.Threading.Tasks.Task`1")
                .map_or(Type::Error, |symbol| Type::Named {
                    symbol,
                    type_arguments: vec![result],
                }),
        }
    }

    /// The task an `async` lambda gives back, as the kind the delegate
    /// declares: against a `Func<…, ValueTask<Outcome<TResult>>>` the body's
    /// `Outcome<VoidResult>` comes wrapped in a `ValueTask`, not a `Task`,
    /// or `TResult` would never be inferred (§12.19.3).
    fn task_as_declared(&self, returns: Type, declared: &Type) -> Type {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        let Some(declared_symbol) = declared.symbol() else {
            return returns;
        };
        let declared_name = symbols.qualified_name(declared_symbol);
        let Type::Named {
            symbol,
            type_arguments,
        } = &returns
        else {
            return returns;
        };
        let name = symbols.qualified_name(*symbol);
        let value_task = match (name.as_str(), declared_name.as_str()) {
            ("System.Threading.Tasks.Task", "System.Threading.Tasks.ValueTask") => {
                compilation.type_by_metadata_name("System.Threading.Tasks.ValueTask")
            }
            ("System.Threading.Tasks.Task`1", "System.Threading.Tasks.ValueTask`1") => {
                compilation.type_by_metadata_name("System.Threading.Tasks.ValueTask`1")
            }
            // Any other task-like type the delegate declares (§15.15.1),
            // with as many type arguments as the task the body made:
            // `UniTask.Create<T>(Func<UniTask<T>>)` infers `T` from a body
            // returning `bool` only if the lambda gives a `UniTask<bool>`.
            ("System.Threading.Tasks.Task" | "System.Threading.Tasks.Task`1", _)
                if self.binder.async_method_builder(declared_symbol).is_some()
                    && symbols
                        .get(declared_symbol)
                        .as_named_type()
                        .is_some_and(|detail| {
                            detail.type_parameters.len() == type_arguments.len()
                        }) =>
            {
                Some(declared_symbol)
            }
            _ => None,
        };
        match value_task {
            Some(symbol) => Type::Named {
                symbol,
                type_arguments: type_arguments.clone(),
            },
            None => returns,
        }
    }

    /// Whether a lambda written with this many parameters could be the
    /// delegate a parameter asks for.
    ///
    /// `new ObjectPool<T>(pool => ..., size)` has three constructors to
    /// choose between, and two of them take a `Factory` that is handed
    /// nothing. Counting is what rules them out: a lambda is convertible to a
    /// delegate only when the two agree on how many parameters there are.
    pub(super) fn lambda_fits(&self, lambda: &BoundExpression, target: &Type) -> bool {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return false;
        };
        arity_fits(
            self.lambda_arity(span),
            target,
            self.binder.compilation().symbols(),
        )
    }

    /// How many parameters a lambda was written with, or `None` where the
    /// syntax does not say.
    pub(super) fn lambda_arity(&self, span: TextSpan) -> Option<usize> {
        let node = self.syntax_at(span)?;
        match node.kind() {
            SyntaxKind::SimpleLambdaExpression => Some(1),
            SyntaxKind::ParenthesizedLambdaExpression | SyntaxKind::AnonymousMethodExpression => {
                let list = node.child_of_kind(SyntaxKind::ParameterList)?;
                Some(
                    list.children()
                        .filter(|child| child.kind() == SyntaxKind::Parameter)
                        .count(),
                )
            }
            _ => None,
        }
    }

    /// Whether a delegate's parameters mention a pointer type anywhere.
    pub(super) fn delegate_takes_pointer(&self, target: &Type) -> bool {
        fn mentions_pointer(ty: &Type) -> bool {
            match ty {
                Type::Pointer(_) => true,
                Type::Array { element, .. } | Type::ByRef(element) => mentions_pointer(element),
                Type::Named { type_arguments, .. } => type_arguments.iter().any(mentions_pointer),
                _ => false,
            }
        }
        self.delegate_signature(target)
            .is_some_and(|(taken, _)| taken.iter().any(mentions_pointer))
    }

    /// Whether a lambda's expression body is `ref x`; `None` for a block.
    pub(super) fn lambda_returns_ref(&self, span: TextSpan) -> Option<bool> {
        let node = self.syntax_at(span)?;
        let body = node.children().last()?;
        if body.kind() == SyntaxKind::Block || !body.kind().is_expression() {
            return None;
        }
        Some(body.kind() == SyntaxKind::RefExpression)
    }

    /// Whether a lambda that does, or does not, return by reference may
    /// become a delegate of this type: only one whose `Invoke` does the same.
    pub(super) fn ref_return_fits(&self, returns_ref: Option<bool>, target: &Type) -> bool {
        let Some(returns_ref) = returns_ref else {
            return true;
        };
        let symbols = self.binder.compilation().symbols();
        let Some(invoke) = target.symbol().and_then(|symbol| {
            (symbols.get(symbol).type_kind() == Some(TypeKind::Delegate))
                .then(|| symbols.lookup(symbol, "Invoke").first().copied())
                .flatten()
        }) else {
            return true;
        };
        let mut sink = Diagnostics::new();
        let by_ref = symbols.get(invoke).modifiers.contains(Modifiers::REF)
            || matches!(self.binder.type_of(invoke, &mut sink), Type::ByRef(_));
        by_ref == returns_ref
    }

    /// The types a lambda wrote for its parameters, where it wrote them all.
    ///
    /// `None` where the syntax leaves any of them out — `(a, b) => ...` says
    /// nothing about what it takes, and neither does `x => ...`.
    pub(super) fn written_lambda_parameters(&self, span: TextSpan) -> Option<Vec<Type>> {
        let node = self.syntax_at(span)?;
        if node.kind() != SyntaxKind::ParenthesizedLambdaExpression
            && node.kind() != SyntaxKind::AnonymousMethodExpression
        {
            return None;
        }
        let list = node.child_of_kind(SyntaxKind::ParameterList)?;
        let context = self.binder.context_at(self.tree, &node);
        let mut written = Vec::new();
        for parameter in list.children() {
            if parameter.kind() != SyntaxKind::Parameter {
                continue;
            }
            // A parameter is `<type> <name>`; with no type there is only the
            // name, and nothing here to say what it is.
            let ty = parameter
                .children()
                .find(|child| child.kind() != SyntaxKind::AttributeList)?;
            let mut sink = Diagnostics::new();
            match self.binder.resolve_type(&ty, &context, &mut sink) {
                Type::Error => return None,
                resolved => written.push(resolved),
            }
        }
        (!written.is_empty()).then_some(written)
    }

    /// The return type a lambda wrote before its parameters, where it did.
    pub(super) fn written_lambda_return(&self, span: TextSpan) -> Option<Type> {
        let node = self.syntax_at(span)?;
        if node.kind() != SyntaxKind::ParenthesizedLambdaExpression {
            return None;
        }
        let list = node.child_of_kind(SyntaxKind::ParameterList)?;
        let ty = node.children().find(|child| {
            child.span().end() <= list.span().start()
                && child.kind().is_type_node()
                && child.kind() != SyntaxKind::AttributeList
        })?;
        let context = self.binder.context_at(self.tree, &node);
        let mut sink = Diagnostics::new();
        match self.binder.resolve_type(&ty, &context, &mut sink) {
            Type::Error => None,
            resolved => Some(resolved),
        }
    }

    /// The types a delegate's `Invoke` takes, as this construction of it.
    /// The delegate a lambda is bound against: the type itself, or the
    /// `TDelegate` of an `Expression<TDelegate>`, whose lambda has the same
    /// parameters and result whatever it is compiled into (§12.19.3).
    ///
    /// Borrowed where it can be: a lambda nested inside others is converted to
    /// a delegate whose type argument is the delegate of the one inside it,
    /// and copying that at every lookup made the binding of a chain of them
    /// grow with its depth for each lookup.
    pub(super) fn delegate_within<'t>(&self, target: &'t Type) -> &'t Type {
        if let Type::Named {
            symbol,
            type_arguments,
        } = target
            && type_arguments.len() == 1
            && self.binder.compilation().symbols().qualified_name(*symbol)
                == "System.Linq.Expressions.Expression`1"
        {
            return &type_arguments[0];
        }
        target
    }

    fn delegate_parameters(&mut self, target: &Type) -> Option<Vec<Type>> {
        let target = self.delegate_within(target);
        let symbols = self.binder.compilation().symbols();
        let invoke = target
            .symbol()
            .filter(|symbol| symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate))
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())?;
        let parameters = symbols.get(invoke).as_method()?.parameters.clone();
        let substitution = self.binder.type_substitution(target);
        Some(
            parameters
                .into_iter()
                .map(|parameter| {
                    let mut sink = Diagnostics::new();
                    self.binder
                        .type_of(parameter, &mut sink)
                        .substitute(&substitution)
                })
                .collect(),
        )
    }

    /// What a delegate takes and gives back, as this construction of it.
    pub(super) fn delegate_signature(&self, target: &Type) -> Option<(Vec<Type>, Type)> {
        let target = self.delegate_within(target);
        let symbols = self.binder.compilation().symbols();
        let invoke = target
            .symbol()
            .filter(|symbol| symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate))
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())?;
        let substitution = self.binder.type_substitution(target);
        let taken = symbols
            .get(invoke)
            .as_method()?
            .parameters
            .iter()
            .map(|parameter| {
                let mut sink = Diagnostics::new();
                self.binder
                    .type_of(*parameter, &mut sink)
                    .substitute(&substitution)
            })
            .collect();
        Some((taken, self.member_type(invoke, target)))
    }

    /// The method of a group that a delegate taking `taken` would call: the
    /// one whose parameters those are, or — while what it takes is not known
    /// yet — the one with as many. A group none of whose methods takes what
    /// is known gives nothing to infer from: `Select(Create)` over
    /// `ITestResult`s is not the `(T, int)` overload because some `Create`
    /// has two parameters.
    fn group_member_shaped(
        &self,
        group: &[SymbolId],
        closed: bool,
        taken: &[Type],
    ) -> Option<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let shapes: Vec<(SymbolId, Vec<Type>)> = group
            .iter()
            .filter_map(|method| {
                let detail = symbols.get(*method).as_method()?;
                if !detail.type_parameters.is_empty() {
                    return None;
                }
                let skip = usize::from(closed && detail.is_extension);
                let parameters = detail
                    .parameters
                    .iter()
                    .skip(skip)
                    .map(|parameter| {
                        let mut sink = Diagnostics::new();
                        self.binder.type_of(*parameter, &mut sink)
                    })
                    .collect::<Vec<Type>>();
                (parameters.len() == taken.len()).then_some((*method, parameters))
            })
            .collect();
        shapes
            .iter()
            .find(|(_, parameters)| {
                taken
                    .iter()
                    .zip(parameters)
                    .all(|(given, wanted)| self.binder.converts_implicitly(given, wanted))
            })
            .or_else(|| {
                taken
                    .iter()
                    .any(|given| given.is_error() || self.mentions_foreign_type_parameter(given))
                    .then(|| shapes.first())
                    .flatten()
            })
            .map(|(method, _)| *method)
    }

    /// What the method of a group that a delegate taking `taken` would call
    /// gives back.
    ///
    /// A generic member of the group — `Split(source, separator, IdFn)` with
    /// `static T IdFn<T>(T x)` — has its own type parameters inferred from
    /// what the delegate takes first (§12.6.3.14), and gives back its return
    /// type with those filled in.
    pub(super) fn group_member_return(
        &self,
        group: &[SymbolId],
        closed: bool,
        taken: &[Type],
        explicit: &[Type],
    ) -> Option<Type> {
        if !explicit.is_empty() {
            return self.explicit_group_member_return(group, closed, taken, explicit);
        }
        if let Some(method) = self.group_member_shaped(group, closed, taken) {
            let mut sink = Diagnostics::new();
            return Some(self.binder.type_of(method, &mut sink).value().clone());
        }
        let symbols = self.binder.compilation().symbols();
        for method in group {
            let Some(detail) = symbols.get(*method).as_method() else {
                continue;
            };
            if detail.type_parameters.is_empty() {
                continue;
            }
            let skip = usize::from(closed && detail.is_extension);
            let parameters: Vec<Type> = detail
                .parameters
                .iter()
                .skip(skip)
                .map(|parameter| {
                    let mut sink = Diagnostics::new();
                    self.binder.type_of(*parameter, &mut sink).value().clone()
                })
                .collect();
            if parameters.len() != taken.len() {
                continue;
            }
            let mut inferred = HashMap::new();
            for (parameter, given) in parameters.iter().zip(taken) {
                self.infer_into(parameter, given, &detail.type_parameters, &mut inferred);
            }
            if detail
                .type_parameters
                .iter()
                .any(|parameter| !inferred.contains_key(parameter))
            {
                continue;
            }
            let mut sink = Diagnostics::new();
            return Some(
                self.binder
                    .type_of(*method, &mut sink)
                    .value()
                    .substitute(&inferred),
            );
        }
        None
    }

    /// What the method of a group written with type arguments returns,
    /// given what the delegate passes it: the one method with as many type
    /// parameters as were written and as many parameters as are passed,
    /// constructed with what was written.
    fn explicit_group_member_return(
        &self,
        group: &[SymbolId],
        closed: bool,
        taken: &[Type],
        explicit: &[Type],
    ) -> Option<Type> {
        let symbols = self.binder.compilation().symbols();
        let mut fitting = group.iter().filter_map(|method| {
            let detail = symbols.get(*method).as_method()?;
            let skip = usize::from(closed && detail.is_extension);
            (detail.type_parameters.len() == explicit.len()
                && detail.parameters.len().saturating_sub(skip) == taken.len())
            .then_some((*method, detail))
        });
        let (method, detail) = fitting.next()?;
        if fitting.next().is_some() {
            return None;
        }
        let substitution: HashMap<SymbolId, Type> = detail
            .type_parameters
            .iter()
            .copied()
            .zip(explicit.iter().cloned())
            .collect();
        let mut sink = Diagnostics::new();
        Some(
            self.binder
                .type_of(method, &mut sink)
                .value()
                .substitute(&substitution),
        )
    }

    /// Whether a method group could become the delegate a parameter asks for.
    ///
    /// `GetDiagnosticSink(queue.EnqueueLocal, ...)` has overloads taking
    /// delegates of three and of five parameters, and which `EnqueueLocal`
    /// was meant is settled by counting: a group becomes a delegate only
    /// through a method that takes as many arguments as the delegate does.
    pub(super) fn group_fits(&self, group: &[SymbolId], closed: bool, parameter: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        if !self.takes_a_function_here(parameter) {
            return false;
        }
        if group.is_empty() {
            return true;
        }
        let Some((taken, wanted_return)) = self.delegate_signature(parameter) else {
            return true;
        };
        // `ref` and `out` have to agree too: `F(ref object, object)` is no
        // `D(object, ref object)`, however the count matches.
        let wanted = self
            .delegate_within(parameter)
            .symbol()
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())
            .map(|invoke| invoke_parameters_ref_kinds(symbols, invoke));
        group.iter().any(|method| {
            symbols.get(*method).as_method().is_some_and(|detail| {
                let skip = usize::from(closed && detail.is_extension);
                detail.parameters.len() == taken.len() + skip
                    && wanted.as_ref().is_none_or(|wanted| {
                        detail.parameters.iter().skip(skip).zip(wanted).all(
                            |(parameter, wanted)| {
                                symbols
                                    .get(*parameter)
                                    .as_parameter()
                                    .is_none_or(|detail| detail.ref_kind == *wanted)
                            },
                        )
                    })
                    && self.group_return_fits(*method, parameter, &wanted_return)
                    // A method takes what a delegate hands it by identity or
                    // reference conversion (§10.8), and `dynamic` has only
                    // `object` for either: `F(string)` is no `In<dynamic>`.
                    && taken
                        .iter()
                        .zip(detail.parameters.iter().skip(skip))
                        .all(|(given, parameter)| {
                            !matches!(given, Type::Dynamic) || {
                                let mut sink = Diagnostics::new();
                                let wanted = self.binder.type_of(*parameter, &mut sink);
                                matches!(wanted, Type::Dynamic | Type::TypeParameter(_) | Type::Error)
                                    || self.binder.object_type().as_ref() == Some(&wanted)
                            }
                        })
            })
        })
    }

    /// How much of the body has been built, for undoing a speculative binding.
    pub(super) fn speculation_floor(&self) -> (usize, usize, usize, usize, usize) {
        (
            self.body.lambdas.len(),
            self.body.locals.len(),
            self.body.diagnostics.len(),
            self.body.local_functions.len(),
            self.local_references.len(),
        )
    }

    /// Throws away everything bound since `floor` was taken.
    ///
    /// A local function written inside one of those lambdas goes with them:
    /// what it captured is a local that no longer exists, and the real
    /// binding will record it again. The speculation happened inside
    /// whatever is still being bound, and a frame that noted a capture of
    /// one of these locals would otherwise keep pointing at a slot that is
    /// gone.
    ///
    /// So do the names it said were those locals: a slot freed here is the
    /// next local's, and a name left pointing at it would be read as that
    /// one — the parameter of a lambda bound to see what it returns turned
    /// into the range variable a query declared after it.
    pub(super) fn unwind_speculation(&mut self, floor: (usize, usize, usize, usize, usize)) {
        self.body.lambdas.truncate(floor.0);
        self.body.locals.truncate(floor.1);
        self.body.diagnostics.truncate(floor.2);
        self.body.local_functions.truncate(floor.3);
        while self.local_references.len() > floor.4 {
            let Some((span, before)) = self.local_references.pop() else {
                break;
            };
            match before {
                Some(before) => self.body.references.insert(span, before),
                None => self.body.references.remove(&span),
            };
        }
        for frame in &mut self.lambdas {
            frame.captured.retain(|local| (local.0 as usize) < floor.1);
        }
        // And the names a scope still open gave them: `1 is { } t ? () =>
        // Use(t) : null` binds its condition, declaring `t`, finds nothing
        // to type the conditional by, and throws the binding away — and the
        // real one would find `t` declared already, as a slot that is gone.
        for scope in &mut self.scopes {
            scope.retain(|_, local| (local.0 as usize) < floor.1);
        }
    }

    /// Binds a lambda against a delegate to see what comes back, and undoes
    /// the binding: what its body returns, whether an expression body has a
    /// value even where the delegate returns none, and whether the binding
    /// itself went wrong — a body that reports errors against one delegate
    /// and none against another has said which it was written for.
    ///
    /// The answer is kept, by the lambda, the delegate and the locals around
    /// it. A call's lambda is bound against each candidate's delegate, and
    /// more than once against one — for what it returns, for how well it
    /// fits — and a lambda inside it again for every binding of the one
    /// around it: `Task.Run(async () => { … Task.Run(async () => …` five
    /// deep took a second and each level took six times the last (found by
    /// fuzzing, `examples/fuzz.rs` in rustlyn-ide). What the body can see is
    /// the locals, and they are in the key; an answer that read what a
    /// resolution around the lambda had learned is not kept.
    pub(super) fn probe_lambda(
        &mut self,
        lambda: &BoundExpression,
        target: &Type,
    ) -> Option<LambdaProbe> {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return self.bind_to_probe(lambda, target);
        };
        let (first, second) = self.locals_fingerprint();
        let key = (span, target.clone(), first, second);
        let probe = match self.lambda_probes.get(&key) {
            Some(probe) => probe.clone(),
            None => {
                let depth = self.lambda_answers.borrow().len();
                let outer = self.answers_read.replace(usize::MAX);
                let probe = self.bind_to_probe(lambda, target);
                let read = self.answers_read.get();
                self.answers_read.set(outer.min(read));
                if read >= depth {
                    self.lambda_probes.insert(key, probe.clone());
                }
                probe
            }
        };
        if self.recover_lambdas
            && let Some(frame) = self.lambda_answers.borrow_mut().last_mut()
        {
            let took = probe.as_ref().is_some_and(|probe| !probe.errored);
            frame.tried.push((span, target.clone(), took));
        }
        probe
    }

    /// Two independent 64-bit hashes of every local as it stands: its
    /// name, type, place and how it is held.
    fn locals_fingerprint(&self) -> (u64, u64) {
        use std::hash::{Hash, Hasher};
        let mut first = std::collections::hash_map::DefaultHasher::new();
        let mut second = std::collections::hash_map::DefaultHasher::new();
        0x9e37_79b9_7f4a_7c15_u64.hash(&mut second);
        for local in &self.body.locals {
            for hasher in [&mut first, &mut second] {
                local.name.hash(hasher);
                local.ty.hash(hasher);
                local.span.hash(hasher);
                local.by_ref.hash(hasher);
                local.readonly_ref.hash(hasher);
            }
        }
        (first.finish(), second.finish())
    }

    /// Binds a lambda against a delegate for [`Self::probe_lambda`], and
    /// undoes the binding.
    fn bind_to_probe(&mut self, lambda: &BoundExpression, target: &Type) -> Option<LambdaProbe> {
        let floor = self.speculation_floor();
        let bound = self.convert(lambda.clone(), target);
        // The lambda's own index, not where the list ended before it was
        // bound: a lambda inside its body is recorded first.
        // A return type the lambda wrote is what it returns, whatever the
        // body's expression is: `static ParameterSymbol (p, t) => new
        // SignatureOnlyParameterSymbol(...)` gives the base type it named.
        let written = match lambda.kind {
            BoundExpressionKind::UnboundLambda(span) => self.written_lambda_return(span),
            _ => None,
        };
        let probed = if let BoundExpressionKind::Lambda(index) = bound.kind {
            let errored = self.body.diagnostics.len() > floor.2;
            let mut all_returns = Vec::new();
            if let Some(bound) = self.body.lambdas.get(index) {
                returned_types(&bound.body, &mut all_returns);
            }
            let (returns, yields_value) = match self.body.lambdas.get(index) {
                Some(bound) => (
                    written
                        .clone()
                        .or_else(|| returned_type(&bound.body))
                        .unwrap_or(Type::Void),
                    matches!(
                        &bound.body.kind,
                        BoundStatementKind::Expression(value)
                            if !matches!(value.ty, Type::Void | Type::Error)
                    ),
                ),
                None => (Type::Void, false),
            };
            Some(LambdaProbe {
                returns: self.wrapped_in_task(lambda, returns),
                yields_value,
                errored,
                all_returns,
            })
        } else {
            None
        };
        self.unwind_speculation(floor);
        probed
    }

    /// Whether the lambdas among the arguments return what the candidate's
    /// delegates say they should.
    ///
    /// Applicability by type says nothing about a lambda, and
    /// `Sum(kvp => kvp.Value.TotalSeconds)` fits the overload taking a
    /// `Func<T, int>` as far as counting goes: only binding the body against
    /// each delegate tells that it gives a `double`. `Task.Run(() => Work())`
    /// is the softer case — an `Action` takes the call and drops the
    /// result, which is allowed and worse than the `Func<T>` that keeps it
    /// (§12.6.4.7).
    pub(super) fn lambdas_fit(
        &mut self,
        resolved: &Resolved,
        arguments: &[BoundExpression],
        receiver: &Type,
        explicit: &[Type],
    ) -> Fit {
        let types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();
        let evidence = self.evidence(arguments);
        let Some(shape) = self.candidate_shape(
            resolved.method,
            &types,
            receiver,
            explicit,
            &evidence.inference,
        ) else {
            return Fit::Good;
        };
        // A lambda in the `params` position is never the array itself: it is
        // one element of the expanded form.
        let element = self.params_element(resolved.method, &shape.parameters);
        let fixed = shape.parameters.len().saturating_sub(1);
        let mut fit = Fit::Exact;
        for (index, argument) in arguments.iter().enumerate() {
            if !holds_a_lambda(std::slice::from_ref(argument)) {
                continue;
            }
            let target = match &element {
                Some(element) if index >= fixed => Some(element.clone()),
                _ => shape.parameters.get(index).cloned(),
            };
            let Some(target) = target else {
                continue;
            };
            fit = fit.max(self.expression_fit(argument, &target));
        }
        fit
    }

    /// How an argument takes its parameter, as far as the lambdas in it
    /// say: a lambda by its body, a tuple literal by its elements'.
    fn expression_fit(&mut self, argument: &BoundExpression, target: &Type) -> Fit {
        match &argument.kind {
            BoundExpressionKind::UnboundLambda(_) => self.lambda_fit(argument, target),
            BoundExpressionKind::TupleCreation(values) => {
                let inner = self
                    .binder
                    .nullable_underlying(target)
                    .unwrap_or_else(|| target.clone());
                let Some(wanted) = self
                    .tuple_element_types(&inner)
                    .filter(|wanted| wanted.len() == values.len())
                else {
                    return Fit::Exact;
                };
                values
                    .iter()
                    .zip(&wanted)
                    .map(|(value, wanted)| self.expression_fit(value, wanted))
                    .max()
                    .unwrap_or(Fit::Exact)
            }
            _ => Fit::Exact,
        }
    }

    /// Whether a type names a type parameter of neither the member being
    /// bound nor a type around it: one of a callee whose type arguments are
    /// still being inferred.
    pub(super) fn mentions_foreign_type_parameter(&self, ty: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        let enclosing = self.context.enclosing_types();
        let own = |parameter: SymbolId| {
            let Some(owner) = symbols.get(parameter).container else {
                return true;
            };
            let mut member = self.member;
            while let Some(current) = member {
                if current == owner {
                    return true;
                }
                member = symbols.get(current).container;
            }
            enclosing.contains(&owner)
        };
        match ty {
            Type::TypeParameter(parameter) => !own(*parameter),
            Type::Named { type_arguments, .. } => type_arguments
                .iter()
                .any(|argument| self.mentions_foreign_type_parameter(argument)),
            Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
                self.mentions_foreign_type_parameter(element)
            }
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| self.mentions_foreign_type_parameter(&element.ty)),
            _ => false,
        }
    }

    /// Whether a lambda was written `async`.
    pub(super) fn is_async_lambda(&self, argument: &BoundExpression) -> bool {
        let BoundExpressionKind::UnboundLambda(span) = argument.kind else {
            return false;
        };
        self.syntax_at(span).is_some_and(|node| {
            node.child_tokens()
                .any(|token| token.kind() == SyntaxKind::AsyncKeyword)
        })
    }

    /// How one lambda takes the delegate it would be handed as.
    fn lambda_fit(&mut self, argument: &BoundExpression, target: &Type) -> Fit {
        let fit = self.lambda_fit_by_body(argument, target);
        // `() => async () => 0` matches a `Func<Func<Task<int>>>` exactly
        // only where the lambda it returns does too (§12.6.4.5): that one is
        // compared by the type it has on its own, before anything converted
        // its result.
        if fit == Fit::Exact && self.nested_lambda_matches(argument, target) == Some(false) {
            return Fit::Good;
        }
        fit
    }

    fn lambda_fit_by_body(&mut self, argument: &BoundExpression, target: &Type) -> Fit {
        let BoundExpressionKind::UnboundLambda(_) = argument.kind else {
            return Fit::Good;
        };
        // `t => ref x` is only for a delegate that returns by reference, and
        // `t => x` only for one that does not.
        if !self.lambda_ref_return_fits(argument, target) {
            return Fit::Bad;
        }
        let Some(expected) = self.delegate_return(target) else {
            // `Report(Delegate d)` takes a lambda through the type it has on
            // its own (C# 10), which is a worse conversion than one to a
            // delegate type.
            if self.takes_a_function_type(target, true) && self.may_have_natural_type(argument) {
                return Fit::Good;
            }
            // `Max(info => info.Number)` has an overload taking an
            // `IComparer<T>`, which no lambda can become.
            return if self.takes_a_function_here(target) {
                Fit::Good
            } else {
                Fit::Bad
            };
        };
        // An `async` lambda given to a `Func<Task<T>>` returns a `T`, and
        // one given to an `Action` returns nothing: both sides are compared
        // with the task taken off.
        let is_async = self.is_async_lambda(argument);
        let expected = if is_async {
            self.task_result(&expected)
        } else {
            expected
        };
        let Some(LambdaProbe {
            returns,
            yields_value,
            errored,
            ..
        }) = self.probe_lambda(argument, target)
        else {
            return Fit::Good;
        };
        let returns = if is_async {
            self.task_result(&returns)
        } else {
            returns
        };
        if errored {
            return Fit::Bad;
        }
        match (&expected, &returns) {
            // `() => i++` given an `Action` is a statement that happens to
            // have a value, which is as good a body as any; `() => 1` only
            // drops what it computes.
            (Type::Void, Type::Void) if yields_value && !self.body_is_a_statement(argument) => {
                Fit::Weak
            }
            (Type::Void, Type::Void) => Fit::Exact,
            // `return x;` where nothing is wanted.
            (Type::Void, _) => Fit::Bad,
            // Nothing returned where something is wanted: perhaps every path
            // throws, so it is not ruled out.
            (_, Type::Void) => Fit::Weak,
            (expected, returns) => {
                if returns == expected {
                    Fit::Exact
                } else if expected.is_error()
                    || returns.is_error()
                    || self.binder.converts_implicitly(returns, expected)
                {
                    Fit::Good
                } else {
                    Fit::Bad
                }
            }
        }
    }

    /// Whether a lambda's expression body is one a statement may be: a
    /// call, an assignment, an increment, an `await` or a `new` (§13.7).
    fn body_is_a_statement(&self, lambda: &BoundExpression) -> bool {
        let BoundExpressionKind::UnboundLambda(span) = lambda.kind else {
            return false;
        };
        let Some(node) = self.syntax_at(span) else {
            return false;
        };
        // `() => (c.Clone())` is not one: the parentheses make it a value.
        let Some(body) = node
            .children()
            .filter(|child| child.kind().is_expression())
            .last()
        else {
            return false;
        };
        matches!(
            body.kind(),
            SyntaxKind::InvocationExpression
                | SyntaxKind::ObjectCreationExpression
                | SyntaxKind::ImplicitObjectCreationExpression
                | SyntaxKind::SimpleAssignmentExpression
                | SyntaxKind::AddAssignmentExpression
                | SyntaxKind::SubtractAssignmentExpression
                | SyntaxKind::MultiplyAssignmentExpression
                | SyntaxKind::DivideAssignmentExpression
                | SyntaxKind::ModuloAssignmentExpression
                | SyntaxKind::AndAssignmentExpression
                | SyntaxKind::ExclusiveOrAssignmentExpression
                | SyntaxKind::OrAssignmentExpression
                | SyntaxKind::LeftShiftAssignmentExpression
                | SyntaxKind::RightShiftAssignmentExpression
                | SyntaxKind::UnsignedRightShiftAssignmentExpression
                | SyntaxKind::CoalesceAssignmentExpression
                | SyntaxKind::PreIncrementExpression
                | SyntaxKind::PreDecrementExpression
                | SyntaxKind::PostIncrementExpression
                | SyntaxKind::PostDecrementExpression
                | SyntaxKind::AwaitExpression
        )
    }

    /// Overload resolution that listens to the lambdas among the arguments.
    ///
    /// The usual pass fits lambdas by parameter count alone. The candidate
    /// it picks is then asked whether its delegates take what the lambdas
    /// return; one that does not is set aside and the rest are asked again,
    /// and a candidate that merely drops a value is kept as the answer of
    /// last resort. When no candidate can be settled that way, a lambda's
    /// body is what says what the type arguments are.
    pub(super) fn resolve_with_lambdas(
        &mut self,
        candidates: &[SymbolId],
        arguments: &mut [BoundExpression],
        receiver: &Type,
        explicit: &[Type],
        extension: bool,
    ) -> Option<Resolved> {
        // What the lambdas are found to return is known to this resolution
        // alone: a lambda nested in one of them is bound again for each
        // delegate the outer one is tried against, and returns differently.
        self.lambda_answers
            .borrow_mut()
            .push(super::inference::LambdaAnswers::default());
        let resolved = self
            .resolve_with_lambdas_answering(candidates, arguments, receiver, explicit, extension);
        if resolved.is_none() && self.recover_lambdas {
            self.guess_lambda_parameters(candidates, arguments, receiver, explicit);
        }
        self.lambda_answers.borrow_mut().pop();
        resolved
    }

    /// What the lambdas of a call that resolved to nothing most likely
    /// take, for the editor's binding of them: the parameter types
    /// inference had fixed when it asked one what it returns. In
    /// `list.Select(e => e.)` nothing says what `Select` returns, yet `e` is
    /// an element of `list` all the same. As Roslyn's
    /// `BindForErrorRecovery`, a delegate the body took is preferred, then
    /// the one that says most, then the first one asked; a lambda nothing
    /// was asked of — no candidate takes as many arguments as were written —
    /// takes the delegate a candidate has in its place, as
    /// `BuildArgumentsForErrorRecovery` does. A parameter whose type is one
    /// of the callee's type parameters nothing fixed stays unknown, and the
    /// others are still what they are: `(context, state) =>` before the
    /// argument that says what `state` is still has its `context`.
    fn guess_lambda_parameters(
        &mut self,
        candidates: &[SymbolId],
        arguments: &[BoundExpression],
        receiver: &Type,
        explicit: &[Type],
    ) {
        let mut guesses: Vec<(TextSpan, LambdaGuess)> = Vec::new();
        {
            let frames = self.lambda_answers.borrow();
            let Some(frame) = frames.last() else {
                return;
            };
            for argument in arguments {
                let BoundExpressionKind::UnboundLambda(span) = argument.kind else {
                    continue;
                };
                // A delegate the body took first, then the one that says
                // most; the first of those asked. Only one with as many
                // parameters as the lambda wrote: `Select(x => x.)` is
                // tried against the `(x, index)` overloads too.
                let arity = self.lambda_arity(span);
                let mut best: Option<LambdaGuess> = None;
                for (tried, delegate, took) in &frame.tried {
                    if *tried != span {
                        continue;
                    }
                    let Some(guess) = self.guess_from(delegate, *took) else {
                        continue;
                    };
                    if arity.is_some_and(|arity| arity != guess.parameters.len()) {
                        continue;
                    }
                    if guess.score.1 > 0
                        && best.as_ref().is_none_or(|best| guess.score > best.score)
                    {
                        best = Some(guess);
                    }
                }
                if let Some(guess) = best {
                    guesses.push((span, guess));
                }
            }
        }
        for (index, argument) in arguments.iter().enumerate() {
            let BoundExpressionKind::UnboundLambda(span) = argument.kind else {
                continue;
            };
            if guesses.iter().any(|(guessed, _)| *guessed == span) {
                continue;
            }
            let arity = self.lambda_arity(span);
            let mut best: Option<LambdaGuess> = None;
            for &candidate in candidates {
                let Some(guess) = self
                    .delegate_in_place(candidate, index, arguments.len(), receiver, explicit)
                    .and_then(|delegate| self.guess_from(&delegate, false))
                else {
                    continue;
                };
                if arity.is_some_and(|arity| arity != guess.parameters.len()) {
                    continue;
                }
                if guess.score.1 > 0 && best.as_ref().is_none_or(|best| guess.score > best.score) {
                    best = Some(guess);
                }
            }
            if let Some(guess) = best {
                guesses.push((span, guess));
            }
        }
        // A call is resolved more than once — an extension method in each
        // scope of `using`s until one applies — and a later round knowing
        // less does not undo an earlier one: UniRx's `Select` took the
        // body, and LINQ's, tried after it, knows nothing of `x`.
        for (span, guess) in guesses {
            match self.lambda_guesses.entry(span) {
                Entry::Occupied(kept) if kept.get().score >= guess.score => {}
                Entry::Occupied(mut kept) => {
                    kept.insert(guess);
                }
                Entry::Vacant(place) => {
                    place.insert(guess);
                }
            }
        }
    }

    /// What a delegate a lambda might become says the lambda takes and
    /// returns, as far as it is known: a type parameter of the callee
    /// nothing fixed — `TState` where the argument that says is not written
    /// yet — stays unknown, and the rest are what they are.
    fn guess_from(&self, delegate: &Type, took: bool) -> Option<LambdaGuess> {
        let (taken, returns) = self.delegate_signature(delegate)?;
        let unknown = |ty: &Type| ty.is_error() || self.mentions_foreign_type_parameter(ty);
        let mut known = 0;
        let parameters = taken
            .into_iter()
            .map(|ty| {
                if unknown(&ty) {
                    Type::Error
                } else {
                    known += 1;
                    ty
                }
            })
            .collect();
        let returns = if unknown(&returns) {
            Type::Error
        } else {
            returns
        };
        Some(LambdaGuess {
            parameters,
            returns,
            score: (took, known),
        })
    }

    /// What the delegate a candidate takes in the place of argument `index`
    /// is handed, where nothing but the receiver and the type arguments
    /// written decide it.
    fn delegate_in_place(
        &self,
        candidate: SymbolId,
        index: usize,
        count: usize,
        receiver: &Type,
        explicit: &[Type],
    ) -> Option<Type> {
        let symbols = self.binder.compilation().symbols();
        let parameters = super::member_parameters(symbols, candidate)?;
        let at = match self.parameter_order(candidate, count) {
            Some(order) => *order.get(index)?,
            None => index,
        };
        let parameter = *parameters.get(at)?;
        // Type arguments written pick the candidates with as many.
        let type_parameters = symbols
            .get(candidate)
            .as_method()
            .map_or(0, |detail| detail.type_parameters.len());
        if !explicit.is_empty() && type_parameters != explicit.len() {
            return None;
        }
        let mut substitution = self.substitution_for(candidate, receiver);
        if let Some(detail) = symbols.get(candidate).as_method()
            && detail.type_parameters.len() == explicit.len()
        {
            substitution.extend(
                detail
                    .type_parameters
                    .iter()
                    .copied()
                    .zip(explicit.iter().cloned()),
            );
        }
        let mut sink = Diagnostics::new();
        Some(
            self.binder
                .type_of(parameter, &mut sink)
                .substitute(&substitution),
        )
    }

    /// Overload resolution that asks the lambdas among the arguments what
    /// they return against each delegate type inference tries them with,
    /// and resolves again with the answers until nothing is left to ask.
    pub(super) fn resolve_call_answering(
        &mut self,
        candidates: &[SymbolId],
        types: &[Type],
        evidence: &Evidence,
        receiver: &Type,
        explicit: &[Type],
    ) -> Option<Resolved> {
        for _ in 0..16 {
            let found = self.resolve_call(candidates, types, evidence, receiver, explicit);
            let missing = match self.lambda_answers.borrow_mut().last_mut() {
                Some(frame) => std::mem::take(&mut frame.missing),
                None => return found,
            };
            if missing.is_empty() {
                return found;
            }
            for (span, delegate) in missing {
                let answer = self.answer_lambda(span, &delegate);
                if let Some(frame) = self.lambda_answers.borrow_mut().last_mut() {
                    if self.recover_lambdas {
                        let took = matches!(answer.fit, Fit::Exact | Fit::Good);
                        frame.tried.push((span, delegate.clone(), took));
                    }
                    frame.known.insert((span, delegate), answer);
                }
            }
        }
        self.resolve_call(candidates, types, evidence, receiver, explicit)
    }

    /// Binds a lambda against a delegate, to see what it returns and how
    /// well it takes it; the binding itself is thrown away.
    fn answer_lambda(&mut self, span: TextSpan, delegate: &Type) -> LambdaAnswer {
        let lambda =
            BoundExpression::new(BoundExpressionKind::UnboundLambda(span), Type::Error, span);
        // Asked while the callee's type parameters in what the delegate
        // returns are still being inferred: what the body returns is found on
        // its own (§12.6.3.13), and how well it fits waits for the type
        // arguments. `() => null` beside `() => new A()` for two `Func<R>`
        // says nothing about `R`, and is no reason to drop the candidate.
        if let Some((taken, gives)) = self.delegate_signature(delegate)
            && self.mentions_foreign_type_parameter(&gives)
            && !taken
                .iter()
                .any(|ty| self.mentions_foreign_type_parameter(ty))
        {
            let parameters: Vec<crate::delegates::DelegateParameter> = taken
                .into_iter()
                .map(|ty| crate::delegates::DelegateParameter {
                    ty,
                    ref_kind: RefKind::None,
                    ref_readonly: false,
                    unscoped: false,
                    default: None,
                    default_syntax: None,
                    is_params: false,
                    scoped: false,
                })
                .collect();
            let floor = self.speculation_floor();
            let returns = match self.written_lambda_return(span) {
                Some(written) => Some(written),
                None => self.inferred_lambda_return(&lambda, &parameters),
            };
            self.unwind_speculation(floor);
            // The task an `async` body makes is the kind the delegate
            // declares, as below: `Func<UniTask<T>>` infers `T` only from a
            // `UniTask<bool>`, never from the `Task<bool>` a body is first
            // given.
            let returns = returns
                .filter(|returns| {
                    !matches!(returns, Type::Void | Type::Null) && !returns.is_error()
                })
                .map(|returns| self.task_as_declared(returns, &gives));
            return LambdaAnswer {
                returns,
                fit: Fit::Good,
            };
        }
        let floor = self.speculation_floor();
        // Before C# 10 a lambda that returns a lambda infers no return type:
        // the one it returns has no type of its own.
        let typeless = !self
            .language_version()
            .at_least(rustlyn_syntax::LanguageVersion::CSharp10)
            && !self.returned_lambdas(&lambda).is_empty();
        let returns = self.lambda_returns(&lambda, delegate).filter(|_| !typeless);
        let fit = self.lambda_fit(&lambda, delegate);
        self.unwind_speculation(floor);
        let declared = self.delegate_return(delegate);
        // `(a, b) => null` infers no return type: `null` has none to give.
        let returns = returns
            .filter(|returns| !matches!(returns, Type::Void | Type::Null) && !returns.is_error())
            .map(|returns| match &declared {
                Some(declared) => self.task_as_declared(returns, declared),
                None => returns,
            });
        LambdaAnswer { returns, fit }
    }

    fn resolve_with_lambdas_answering(
        &mut self,
        candidates: &[SymbolId],
        arguments: &mut [BoundExpression],
        receiver: &Type,
        explicit: &[Type],
        extension: bool,
    ) -> Option<Resolved> {
        let types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();
        let natural_types = self.natural_types_for_inference(candidates, arguments, explicit);
        let evidence_for = |this: &Self, arguments: &[BoundExpression]| {
            let mut evidence = this.evidence_for(arguments, extension);
            evidence.natural_types.clone_from(&natural_types);
            evidence
        };
        let evidence = evidence_for(self, arguments);
        let mut resolved =
            self.resolve_call_answering(candidates, &types, &evidence, receiver, explicit);
        if !holds_a_lambda(arguments) {
            return resolved;
        }
        // A type argument that came out an error was inferred from an
        // argument that has no type of its own yet — an `out var` beside a
        // lambda. That is not an answer, it is the question again, and the
        // pass below can settle it.
        let mut excluded: Vec<SymbolId> = Vec::new();
        // Nor is it applicable while that stays so: another candidate the
        // arguments do fit is still a choice. Before C# 10 a lambda has no
        // type of its own, so `F<T>(T t)` infers nothing from `() => i++`
        // and `F(Action)` beside it is the one that applies.
        while let Some(found) = resolved.take_if(|found| unsettled(found)) {
            excluded.push(found.method);
            let remaining: Vec<SymbolId> = candidates
                .iter()
                .copied()
                .filter(|candidate| !excluded.contains(candidate))
                .collect();
            if remaining.is_empty() {
                break;
            }
            resolved = self.resolve_call(
                &remaining,
                &types,
                &evidence_for(self, arguments),
                receiver,
                explicit,
            );
        }
        let mut weak: Option<Resolved> = None;
        // A body that is wrong against every delegate is wrong in itself, and
        // the first choice is still the one to report that against.
        let mut first: Option<Resolved> = None;
        while let Some(found) = resolved.take() {
            match self.lambdas_fit(&found, arguments, receiver, explicit) {
                // Which of the candidates the lambdas fit is better is
                // overload resolution's to say, and it has said it: a lambda
                // that exactly matches its delegate counts there (§12.6.4.5).
                Fit::Exact | Fit::Good => return Some(found),
                Fit::Weak => {
                    if weak.is_none() {
                        weak = Some(found.clone());
                    }
                }
                Fit::Bad => {}
            }
            if first.is_none() {
                first = Some(found.clone());
            }
            excluded.push(found.method);
            let remaining: Vec<SymbolId> = candidates
                .iter()
                .copied()
                .filter(|candidate| !excluded.contains(candidate))
                .collect();
            if remaining.is_empty() {
                break;
            }
            let evidence = evidence_for(self, arguments);
            resolved = self
                .resolve_call_answering(&remaining, &types, &evidence, receiver, explicit)
                .filter(|resolved| !unsettled(resolved));
        }
        self.resolve_through_lambdas(candidates, arguments, receiver, explicit)
            .or(weak)
            .or(first)
    }

    /// The type a delegate's `Invoke` gives back.
    fn delegate_return(&mut self, target: &Type) -> Option<Type> {
        let target = self.delegate_within(target);
        let symbols = self.binder.compilation().symbols();
        let invoke = target
            .symbol()
            .filter(|symbol| symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate))
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())?;
        Some(self.member_type(invoke, target))
    }

    /// Binds a lambda, with its parameters in scope for its body.
    /// A lambda, left unbound.
    ///
    /// `x => x * 2` cannot be bound on sight: what `x` is comes from the
    /// delegate it is converted to, and binding the body against a guess would
    /// mean binding it twice and answering differently each time. So the
    /// syntax is recorded and the conversion does the work.
    pub(super) fn bind_lambda(&mut self, node: &SyntaxNode) -> BoundExpression {
        self.bind_attribute_names(node);
        BoundExpression::new(
            BoundExpressionKind::UnboundLambda(node.span()),
            Type::Error,
            node.span(),
        )
    }

    /// Binds a lambda's body now that a delegate has said what it takes.
    ///
    /// The locals go on the enclosing member's list rather than a list of
    /// their own: one flat table per member is what the semantic model
    /// already promises, and a lambda's body is still that member's syntax.
    pub(super) fn bind_lambda_body(&mut self, node: &SyntaxNode, asked: &Type) -> BoundExpression {
        let span = node.span();
        // Against an `Expression<TDelegate>` the lambda is bound as the
        // delegate's would be (§12.19.3); what comes out is typed as the
        // tree, which is what the emitter describes rather than compiles.
        let inner = self.delegate_within(asked);
        let target = &inner;
        let symbols = self.binder.compilation().symbols();
        let Some(invoke) = target
            .symbol()
            .filter(|symbol| symbols.get(*symbol).type_kind() == Some(TypeKind::Delegate))
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())
        else {
            return BoundExpression::error(span);
        };
        let invoke_parameters = symbols
            .get(invoke)
            .as_method()
            .map(|detail| detail.parameters.clone())
            .unwrap_or_default();
        // A delegate that takes `ref` is the reason the lambda's parameter is
        // an address rather than a value: the method the lambda becomes has to
        // match `Invoke`, and the body has to read through it.
        let by_ref: Vec<bool> = invoke_parameters
            .iter()
            .map(|parameter| {
                symbols
                    .get(*parameter)
                    .as_parameter()
                    .is_some_and(|detail| detail.ref_kind != RefKind::None)
            })
            .collect();
        let wanted: Vec<Type> = invoke_parameters
            .into_iter()
            .map(|parameter| self.member_type(parameter, target))
            .collect();
        let return_type = self.member_type(invoke, target);
        // `async x => { return 1; }` given to a `Func<int, Task<int>>` returns
        // an `int`: the task is made around it.
        let is_async = node
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::AsyncKeyword);
        let task_type = is_async.then(|| return_type.clone());
        let return_type = if is_async {
            self.task_result(&return_type)
        } else {
            return_type
        };

        // A `static` lambda captures nothing, so nothing around it is in
        // scope: a name it declares is its own, whatever the method holding
        // it called something. Roslyn leans on that —
        // `static (text, arg) => { var (@this, data, ...) = arg; }` is
        // written inside a method that has a `@this` and a `data` of its own.
        let outer_scopes = node
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::StaticKeyword)
            .then(|| self.detach_scopes());
        self.push_scope();
        let outer_synthetic = std::mem::replace(&mut self.synthetic_span, node.span());
        self.lambdas.push(LambdaFrame {
            floor: self.scopes.len() - 1,
            return_type: return_type.clone(),
            captured: Vec::new(),
            captured_parameters: Vec::new(),
            captures_this: false,
            calls: Vec::new(),
            iterator: None,
            declares: None,
        });

        let ref_kinds: Vec<RefKind> = invoke_parameters_ref_kinds(symbols, invoke);
        // `(_, _) => _` declares two discards and no `_` at all (C# 9): the
        // `_` it reads is whatever is outside. One `_` alone is a name.
        let discards = lambda_parameters(node)
            .iter()
            .filter(|parameter| {
                parameter.child_tokens().any(|token| {
                    token.kind() == SyntaxKind::IdentifierToken && token.value_text() == "_"
                })
            })
            .count()
            > 1;
        let mut declared = Vec::new();
        for parameter in lambda_parameters(node) {
            let index = declared.len();
            // `(ref int x) => ...` is a lambda for a delegate that takes a
            // `ref`, and for no other (§12.19.4).
            self.check_lambda_parameter_ref(&parameter, index, ref_kinds.get(index).copied());
            // A parameter with no type written takes the delegate's.
            let ty = parameter
                .children()
                .find(|child| child.kind().is_type_node())
                .map_or_else(
                    || wanted.get(index).cloned().unwrap_or(Type::Error),
                    |written| self.resolve(&written),
                );
            let Some(token) = parameter
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            else {
                continue;
            };
            let name = if discards && token.value_text() == "_" {
                format!("<_{index}>")
            } else {
                token.value_text().to_string()
            };
            let local = self.declare_local(&name, ty, token.span());
            if by_ref.get(index).copied().unwrap_or(false)
                && let Some(slot) = self.body.locals.get_mut(local.0 as usize)
            {
                slot.by_ref = true;
            }
            declared.push(local);
        }
        // `delegate { return 9; }` writes no parameter list, and takes
        // whatever the delegate hands it, unnamed (§12.19.2).
        if node.kind() == SyntaxKind::AnonymousMethodExpression
            && node.child_of_kind(SyntaxKind::ParameterList).is_none()
        {
            for (index, ty) in wanted.iter().enumerate() {
                let local = self.declare_local(&format!("<p{index}>"), ty.clone(), span);
                if by_ref.get(index).copied().unwrap_or(false)
                    && let Some(slot) = self.body.locals.get_mut(local.0 as usize)
                {
                    slot.by_ref = true;
                }
                declared.push(local);
            }
        }
        if declared.len() != wanted.len() {
            self.lambdas.pop();
            self.synthetic_span = outer_synthetic;
            self.pop_scope();
            if let Some(outer) = outer_scopes {
                self.restore_scopes(outer);
            }
            return BoundExpression::error(span);
        }

        // The body is what follows the `=>`: `static int (a) => a + 1` writes
        // a type before its parameters, and that is not the body.
        let arrow = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::EqualsGreaterThanToken)
            .map_or(span.start(), |token| token.span().end());
        let body = node
            .children()
            .find(|child| {
                child.span().start() >= arrow
                    && (child.kind() == SyntaxKind::Block || child.kind().is_expression())
            })
            .map(|child| {
                if child.kind() == SyntaxKind::Block {
                    self.bind_block(&child)
                } else {
                    // An expression-bodied lambda returns its expression, or
                    // just runs it when the delegate returns nothing.
                    let value = self.bind_expression(&child);
                    let body = self.arrow_body(&child, value);
                    // A lambda it returns that nothing gave a delegate — the
                    // delegate returns a type no one knows yet — is still
                    // there to be asked about.
                    if self.recover_lambdas && (is_lambda(&child) || is_targetless(&child)) {
                        let reported = self.body.diagnostics.len();
                        self.recover_expression(&child);
                        self.body.diagnostics.truncate(reported);
                    }
                    body
                }
            });

        self.synthetic_span = outer_synthetic;
        let Some(frame) = self.lambdas.pop() else {
            if let Some(outer) = outer_scopes {
                self.restore_scopes(outer);
            }
            return BoundExpression::error(span);
        };
        self.pop_scope();
        if let Some(outer) = outer_scopes {
            self.restore_scopes(outer);
        }

        let Some(body) = body else {
            return BoundExpression::error(span);
        };
        // A delegate that returns by reference makes a method that does:
        // its body returns a variable of the type, and the method `T&`.
        let returns_ref = {
            let mut sink = Diagnostics::new();
            self.binder
                .compilation()
                .symbols()
                .get(invoke)
                .modifiers
                .contains(Modifiers::REF)
                || matches!(self.binder.type_of(invoke, &mut sink), Type::ByRef(_))
        };
        let return_type = if returns_ref && !matches!(return_type, Type::ByRef(_)) {
            Type::ByRef(Box::new(return_type))
        } else {
            return_type
        };
        let index = self.body.lambdas.len();
        self.body.lambdas.push(BoundLambda {
            span,
            parameters: declared,
            body,
            captured: frame.captured,
            captured_parameters: frame.captured_parameters,
            captures_this: frame.captures_this,
            calls: frame.calls,
            return_type,
            task_type,
        });
        BoundExpression::new(BoundExpressionKind::Lambda(index), asked.clone(), span)
    }
}

impl BodyBinder<'_> {
    /// The lambdas given to `node` — a call, a creation, an assignment —
    /// that its binding left without a delegate, bound for the editor: their
    /// parameters typed as written or as nothing known, their bodies bound
    /// as usual. Roslyn binds these so "for error recovery". Without it, a
    /// lambda handed to a call that does not resolve — a method of an
    /// assembly not referenced, `Assert.Throws(() => items.First(x =>
    /// x.Ok))` in a test whose framework is missing, a call half typed — had
    /// no parameters at all, and nothing inside could say what `x` was, not
    /// even the inner lambda whose own call resolves. What the binding
    /// reports is dropped: the call has said what is wrong with it.
    ///
    /// Only for an editor's binding (`recover_lambdas`): a lambda bound
    /// against no delegate is nothing a backend can compile.
    ///
    /// So with a `new(…)` or a collection expression nothing gave a type:
    /// what is inside is bound as it would be on its own, and the lambdas
    /// among it as above — `Add(new(key, [.. items.Where(x => x.` is all
    /// still there to ask about while the call is being typed.
    pub(super) fn recover_lambdas_in(&mut self, node: &SyntaxNode) {
        // A `new(…)` is bound with what it is given to, later: only if that
        // never comes is what is inside it bound so.
        if !self.recover_lambdas || node.kind() == SyntaxKind::ImplicitObjectCreationExpression {
            return;
        }
        for given in given_expressions(node) {
            if is_lambda(&given) || is_targetless(&given) {
                let reported = self.body.diagnostics.len();
                self.recover_expression(&given);
                self.body.diagnostics.truncate(reported);
            }
        }
    }

    /// One expression bound for the editor where its binding was left
    /// undone: a lambda without its delegate, a `new(…)` or `[…]` without
    /// the type it makes, anything else as usual.
    fn recover_expression(&mut self, expression: &SyntaxNode) {
        if is_lambda(expression) {
            if !self
                .body
                .lambdas
                .iter()
                .any(|bound| bound.span == expression.span())
            {
                self.bind_lambda_for_recovery(expression);
            }
            return;
        }
        if is_targetless(expression) {
            // Converted after all, and so bound with what it makes.
            if self
                .body
                .types
                .get(&expression.span())
                .is_some_and(|ty| !ty.is_error())
            {
                return;
            }
            let parts: Vec<SyntaxNode> = match expression.kind() {
                SyntaxKind::CollectionExpression => expression
                    .children()
                    .filter(|element| {
                        matches!(
                            element.kind(),
                            SyntaxKind::ExpressionElement | SyntaxKind::SpreadElement
                        )
                    })
                    .filter_map(|element| {
                        element
                            .children()
                            .find(|child| child.kind().is_expression())
                    })
                    .collect(),
                // An `out var` among the arguments was declared when the
                // creation was met.
                _ => given_expressions(expression)
                    .into_iter()
                    .filter(|argument| argument.kind() != SyntaxKind::DeclarationExpression)
                    .collect(),
            };
            for part in parts {
                self.recover_expression(&part);
            }
            return;
        }
        self.bind_expression(expression);
    }

    /// [`Self::bind_lambda_body`] with no delegate to say what the lambda
    /// takes and returns.
    fn bind_lambda_for_recovery(&mut self, node: &SyntaxNode) {
        let span = node.span();
        let outer_scopes = node
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::StaticKeyword)
            .then(|| self.detach_scopes());
        self.push_scope();
        let outer_synthetic = std::mem::replace(&mut self.synthetic_span, span);
        self.lambdas.push(LambdaFrame {
            floor: self.scopes.len() - 1,
            return_type: Type::Error,
            captured: Vec::new(),
            captured_parameters: Vec::new(),
            captures_this: false,
            calls: Vec::new(),
            iterator: None,
            declares: None,
        });
        let parameters = lambda_parameters(node);
        let guessed = self
            .lambda_guesses
            .remove(&span)
            .filter(|guessed| guessed.parameters.len() == parameters.len());
        let discards = parameters
            .iter()
            .filter(|parameter| {
                parameter.child_tokens().any(|token| {
                    token.kind() == SyntaxKind::IdentifierToken && token.value_text() == "_"
                })
            })
            .count()
            > 1;
        let mut declared = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            let ty = match parameter
                .children()
                .find(|child| child.kind().is_type_node())
            {
                Some(written) => self.resolve(&written),
                None => guessed
                    .as_ref()
                    .and_then(|guessed| guessed.parameters.get(index).cloned())
                    .unwrap_or(Type::Error),
            };
            let Some(token) = parameter
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            else {
                continue;
            };
            let name = if discards && token.value_text() == "_" {
                format!("<_{index}>")
            } else {
                token.value_text().to_string()
            };
            declared.push(self.declare_local(&name, ty, token.span()));
        }
        let arrow = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::EqualsGreaterThanToken)
            .map_or(span.start(), |token| token.span().end());
        let body = node
            .children()
            .find(|child| {
                child.span().start() >= arrow
                    && (child.kind() == SyntaxKind::Block || child.kind().is_expression())
            })
            .map(|child| {
                if child.kind() == SyntaxKind::Block {
                    self.bind_block(&child)
                } else if is_lambda(&child) || is_targetless(&child) {
                    // `h => (sender, e) => h(e)`: what this one returns is
                    // the delegate the guess returns, where it says, and
                    // bound as it would be on its own otherwise.
                    let reported = self.body.diagnostics.len();
                    if let Some(returns) = guessed
                        .as_ref()
                        .map(|guessed| &guessed.returns)
                        .filter(|returns| !returns.is_error())
                    {
                        let value = self.bind_expression(&child);
                        self.convert(value, returns);
                    }
                    self.recover_expression(&child);
                    self.body.diagnostics.truncate(reported);
                    BoundStatement::new(
                        BoundStatementKind::Expression(BoundExpression::error(child.span())),
                        child.span(),
                    )
                } else {
                    let value = self.bind_expression(&child);
                    BoundStatement::new(BoundStatementKind::Expression(value), child.span())
                }
            });
        self.synthetic_span = outer_synthetic;
        let frame = self.lambdas.pop();
        self.pop_scope();
        if let Some(outer) = outer_scopes {
            self.restore_scopes(outer);
        }
        let (Some(frame), Some(body)) = (frame, body) else {
            return;
        };
        self.body.lambdas.push(BoundLambda {
            span,
            parameters: declared,
            body,
            captured: frame.captured,
            captured_parameters: frame.captured_parameters,
            captures_this: frame.captures_this,
            calls: frame.calls,
            return_type: Type::Error,
            task_type: None,
        });
    }
}

fn is_lambda(node: &SyntaxNode) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
    )
}

/// Whether an expression has no type until what it is given to says.
fn is_targetless(node: &SyntaxNode) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::ImplicitObjectCreationExpression | SyntaxKind::CollectionExpression
    )
}

/// What `node` is given — its arguments, the right side of an assignment —
/// out of any parentheses.
fn given_expressions(node: &SyntaxNode) -> Vec<SyntaxNode> {
    fn unwrapped(node: &SyntaxNode) -> Option<SyntaxNode> {
        match node.kind() {
            SyntaxKind::ParenthesizedExpression | SyntaxKind::Argument => node
                .children()
                .find(|child| child.kind().is_expression())
                .and_then(|inner| unwrapped(&inner)),
            _ => node.kind().is_expression().then(|| node.clone()),
        }
    }
    match node.kind() {
        SyntaxKind::InvocationExpression
        | SyntaxKind::ObjectCreationExpression
        | SyntaxKind::ImplicitObjectCreationExpression
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::BaseConstructorInitializer
        | SyntaxKind::ThisConstructorInitializer => node
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::ArgumentList | SyntaxKind::BracketedArgumentList
                )
            })
            .flat_map(|list| list.children().collect::<Vec<_>>())
            .filter_map(|argument| unwrapped(&argument))
            .collect(),
        SyntaxKind::SimpleAssignmentExpression
        | SyntaxKind::AddAssignmentExpression
        | SyntaxKind::SubtractAssignmentExpression => node
            .children()
            .last()
            .and_then(|right| unwrapped(&right))
            .into_iter()
            .collect(),
        _ => Vec::new(),
    }
}

/// Whether any of these arguments is a lambda that has no type yet.
fn holds_a_lambda(arguments: &[BoundExpression]) -> bool {
    arguments.iter().any(|argument| match &argument.kind {
        BoundExpressionKind::UnboundLambda(_) => true,
        BoundExpressionKind::TupleCreation(values) => holds_a_lambda(values),
        _ => false,
    })
}

/// Whether a resolution left a type argument as an error, which is what
/// inferring one from something that has no type yet comes to.
fn unsettled(resolved: &Resolved) -> bool {
    resolved.type_arguments.iter().any(Type::is_error)
}

/// A lambda's parameters, however they were written: `x => ...` has one and no
/// list, `(int x, int y) => ...` has a list.
fn lambda_parameters(node: &SyntaxNode) -> Vec<SyntaxNode> {
    let mut parameters = Vec::new();
    for child in node.children() {
        match child.kind() {
            SyntaxKind::Parameter => parameters.push(child),
            SyntaxKind::ParameterList => parameters.extend(
                child
                    .children()
                    .filter(|parameter| parameter.kind() == SyntaxKind::Parameter),
            ),
            _ => {}
        }
    }
    parameters
}

/// The type of the first value a body returns, where it returns one.
///
/// A conversion is looked through: the lambda was bound against a delegate
/// whose return type is the very parameter being inferred, so the conversion
/// that was applied says what was *asked for* rather than what was given.
fn returned_type(statement: &BoundStatement) -> Option<Type> {
    match &statement.kind {
        BoundStatementKind::Return(Some(value)) => Some(natural_type(value)),
        BoundStatementKind::Block(statements) => statements.iter().find_map(returned_type),
        BoundStatementKind::If {
            consequence,
            alternative,
            ..
        } => returned_type(consequence).or_else(|| alternative.as_deref().and_then(returned_type)),
        BoundStatementKind::While { body, .. }
        | BoundStatementKind::DoWhile { body, .. }
        | BoundStatementKind::For { body, .. }
        | BoundStatementKind::ForEach { body, .. }
        | BoundStatementKind::Using { body, .. }
        | BoundStatementKind::Lock { body, .. }
        | BoundStatementKind::Fixed { body, .. } => returned_type(body),
        // `try { ... return result.ToImmutableAndFree(); } finally { ... }`
        // returns from inside the `try`, as a lambda around a pooled
        // builder does.
        BoundStatementKind::Try {
            body,
            catches,
            finally,
        } => returned_type(body)
            .or_else(|| catches.iter().find_map(|catch| returned_type(&catch.body)))
            .or_else(|| finally.as_deref().and_then(returned_type)),
        BoundStatementKind::Switch { sections, .. } => sections
            .iter()
            .find_map(|section| section.statements.iter().find_map(returned_type)),
        _ => None,
    }
}

/// The type of every value a body returns, looking through conversions as
/// [`returned_type`] does; a lambda nested in it returns for itself.
fn returned_types(statement: &BoundStatement, into: &mut Vec<(Type, TextSpan, bool)>) {
    match &statement.kind {
        BoundStatementKind::Return(Some(value)) => {
            into.push((natural_type(value), value.span, is_function_value(value)));
        }
        BoundStatementKind::Block(statements) => {
            for statement in statements {
                returned_types(statement, into);
            }
        }
        BoundStatementKind::If {
            consequence,
            alternative,
            ..
        } => {
            returned_types(consequence, into);
            if let Some(alternative) = alternative {
                returned_types(alternative, into);
            }
        }
        BoundStatementKind::While { body, .. }
        | BoundStatementKind::DoWhile { body, .. }
        | BoundStatementKind::For { body, .. }
        | BoundStatementKind::ForEach { body, .. }
        | BoundStatementKind::Using { body, .. }
        | BoundStatementKind::Lock { body, .. }
        | BoundStatementKind::Fixed { body, .. } => returned_types(body, into),
        BoundStatementKind::Try {
            body,
            catches,
            finally,
        } => {
            returned_types(body, into);
            for catch in catches {
                returned_types(&catch.body, into);
            }
            if let Some(finally) = finally {
                returned_types(finally, into);
            }
        }
        BoundStatementKind::Switch { sections, .. } => {
            for section in sections {
                for statement in &section.statements {
                    returned_types(statement, into);
                }
            }
        }
        _ => {}
    }
}

/// Whether a value was a lambda or a delegate made from a method group,
/// before the conversions the binder put around it.
fn is_function_value(value: &BoundExpression) -> bool {
    match &value.kind {
        BoundExpressionKind::Conversion {
            operand,
            written: false,
            ..
        } => is_function_value(operand),
        BoundExpressionKind::Lambda(_) | BoundExpressionKind::DelegateCreation { .. } => true,
        _ => false,
    }
}

/// An expression's type before whatever conversion was applied to it.
fn natural_type(value: &BoundExpression) -> Type {
    match &value.kind {
        BoundExpressionKind::Conversion {
            operand,
            written: false,
            ..
        } => natural_type(operand),
        // The implicit conversion of a `dynamic` value is the binder's too.
        BoundExpressionKind::Dynamic(dynamic)
            if matches!(
                dynamic.operation,
                crate::bound::DynamicOperation::Convert { explicit: false }
            ) =>
        {
            dynamic
                .receiver
                .as_ref()
                .map_or_else(|| value.ty.clone(), natural_type)
        }
        // A tuple literal given a tuple type converts element by element,
        // and has the type its elements have on their own.
        BoundExpressionKind::TupleCreation(values) => {
            let names: Vec<Option<String>> = match &value.ty {
                Type::Tuple(elements) if elements.len() == values.len() => elements
                    .iter()
                    .map(|element| element.name.clone())
                    .collect(),
                _ => vec![None; values.len()],
            };
            let elements: Vec<crate::types::TupleElement> = values
                .iter()
                .zip(names)
                .map(|(value, name)| crate::types::TupleElement {
                    name,
                    ty: natural_type(value),
                })
                .collect();
            if elements.iter().any(|element| element.ty.is_error()) {
                value.ty.clone()
            } else {
                Type::Tuple(elements)
            }
        }
        _ => value.ty.clone(),
    }
}

/// Whether a method's parameter of one `ref` kind answers a delegate's or a
/// function pointer's of another: the same kind, or from C# 12 on an `in`
/// (or `ref readonly`) for a `ref`, which it only reads.
fn target_ref_kind_fits(method: RefKind, target: RefKind, ref_to_in: bool) -> bool {
    method == target || (ref_to_in && method == RefKind::In && target == RefKind::Ref)
}
