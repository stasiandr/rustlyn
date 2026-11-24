//! Invocations: calls of methods, extension methods and delegates, and the
//! arguments they are given — named, defaulted, caller information.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::interpolation::HandlerCapture;
use super::{
    BodyBinder, Resolved, call_name, identifier_text, is_constructed, member_parameters,
    missing_member_code, passes_the_array,
};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundSymbol, ConstantValue, DynamicOperation, LocalSymbol,
};
use crate::corlib::SpecialType;
use crate::metadata::ComDefault;
use crate::symbol::{CallerInfo, MethodKind, Modifiers, RefKind, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    pub(super) fn bind_invocation(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let mut children = node.children();
        let Some(callee) = children.next() else {
            return BoundExpression::error(span);
        };
        // `nameof(x)` is spelled like a call and is not one: its argument is
        // never evaluated and never even has to mean anything a value could
        // have, so it is answered before the arguments are bound.
        if let Some(name) = self.bind_nameof(node, &callee, span) {
            return name;
        }
        let argument_list = children.find(|child| child.kind() == SyntaxKind::ArgumentList);
        let arguments = argument_list
            .as_ref()
            .map(|list| self.bind_argument_list(list))
            .unwrap_or_default();
        let argument_names = argument_list
            .as_ref()
            .map(Self::argument_names)
            .unwrap_or_default();

        // `Chosen(true)(4)`: a callee that is not a name cannot be a method
        // group, so whatever it is has to be a delegate or nothing.
        if !matches!(
            callee.kind(),
            SyntaxKind::IdentifierName
                | SyntaxKind::GenericName
                | SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::PointerMemberAccessExpression
                | SyntaxKind::MemberBindingExpression
        ) && callee.kind().is_expression()
        {
            let target = self.bind_expression(&callee);
            return if self.is_invocable(&target.ty) || matches!(target.ty, Type::Dynamic) {
                self.invoke_delegate(target, arguments, span)
            } else {
                BoundExpression::error(span)
            };
        }

        // Whether the call was written on something, and if so whether that
        // something is a type name. A static member is not reachable through
        // an instance and an instance member is not reachable through a type
        // (§12.8.7), which is what keeps `span.Equals(other, comparison)`
        // away from `object.Equals(object, object)`.
        // An array asked for a member of `System.Array` is looked at as one;
        // an extension method is still found on the array itself.
        let mut array_receiver: Option<Type> = None;
        let (container, name, name_node, receiver_type, receiver, names_a_type) = match callee
            .kind()
        {
            SyntaxKind::IdentifierName | SyntaxKind::GenericName => {
                let Some(name) = identifier_text(&callee) else {
                    return BoundExpression::error(span);
                };
                // `square(2)` where `square` is a delegate variable calls what
                // the variable holds, not a method of the enclosing type. In
                // metadata that is a call to the delegate's `Invoke`, and it
                // is one here too.
                if let Some(target) = self.delegate_in_scope(&callee) {
                    return self.invoke_delegate(target, arguments, span);
                }
                // A local function is named from inside its owner and from
                // nowhere else, so it is looked for before the type's members
                // — and it shadows a member of the same name, as C# says.
                if let Some(local) = self.local_function(&name, span) {
                    self.note_local_function_call(local);
                    let candidates = vec![local];
                    let ordered = self.reorder_named(
                        &candidates,
                        &argument_names,
                        arguments.clone(),
                        &Type::Error,
                    );
                    if let Some(call) =
                        self.bind_resolved_call(&candidates, &callee, &ordered, span)
                    {
                        return call;
                    }
                    // Nothing else of that name is in reach, so it is the
                    // local function the call was meant for, and why it
                    // does not take these arguments is the error.
                    if self.binder.static_imports(&self.context, &name).is_empty()
                        && self.declaring_enclosing(&name).is_none()
                    {
                        let types: Vec<Type> = ordered.iter().map(|a| a.ty.clone()).collect();
                        let spans: Vec<TextSpan> = ordered.iter().map(|a| a.span).collect();
                        let explicit = self.explicit_type_arguments(&callee);
                        self.report_no_overload(
                            &candidates,
                            &name,
                            &types,
                            &spans,
                            &Type::Void,
                            &explicit,
                            callee.span(),
                            None,
                        );
                        return BoundExpression::error(span);
                    }
                }
                // `using static Math;` makes `Abs(x)` a call in its own
                // right, with no type written in front of it — where no type
                // around the code declares a method of the name: those are
                // looked in first, and `Lerp(a, b, t)` inside `Easing` is its
                // own `Lerp` and not `Mathf.Lerp`, however well both take it.
                // A field is not called, so `Empty()` beside a field `Empty`
                // is still `Expression.Empty()`.
                let declared = self.declaring_enclosing(&name).is_some_and(|ty| {
                    let symbols = self.binder.compilation().symbols();
                    self.binder
                        .lookup_member(ty, &name)
                        .iter()
                        .any(|&member| symbols.get(member).kind == SymbolKind::Method)
                });
                let imported = if declared {
                    Vec::new()
                } else {
                    self.binder.static_imports(&self.context, &name)
                };
                if !imported.is_empty() {
                    let ordered = self.reorder_named(
                        &imported,
                        &argument_names,
                        arguments.clone(),
                        &Type::Error,
                    );
                    if let Some(call) = self.bind_resolved_call(&imported, &callee, &ordered, span)
                    {
                        return call;
                    }
                }
                let Some(enclosing) = self
                    .declaring_enclosing(&name)
                    .or_else(|| self.context.enclosing_type())
                else {
                    return BoundExpression::error(span);
                };
                (
                    enclosing,
                    name,
                    callee.clone(),
                    self.binder.self_type(enclosing),
                    None,
                    // Nothing was written to call it on, so both a static
                    // member and one of `this` are in reach.
                    None,
                )
            }
            // `a?.M()` calls `M` on the receiver of the `?.`, which is
            // already bound and waiting: the callee names only the member.
            SyntaxKind::MemberBindingExpression => {
                let Some(right) = callee.children().next() else {
                    return BoundExpression::error(span);
                };
                let Some(name) = identifier_text(&right) else {
                    return BoundExpression::error(span);
                };
                let mut receiver = self.accessed_value(span);
                // `d?.M()` on a `dynamic` value is bound when it runs.
                if matches!(receiver.ty, Type::Dynamic) {
                    let type_arguments = self.explicit_type_arguments(&right);
                    return Self::dynamic_operation(
                        DynamicOperation::InvokeMember {
                            name,
                            type_arguments,
                            simple_name: false,
                        },
                        Some(receiver),
                        arguments,
                        argument_names,
                        Type::Dynamic,
                        span,
                    );
                }
                // `array?.Length` is the array's own; `array?.First()` is an
                // extension method over it, as `array.First()` would be.
                if receiver.ty.symbol().is_none()
                    && let Some(array) = self.as_system_array(&receiver, &name)
                {
                    array_receiver = Some(receiver.ty.clone());
                    receiver = BoundExpression::new(receiver.kind, array, receiver.span);
                }
                let Some(symbol) = receiver.ty.symbol() else {
                    let explicit = self.explicit_type_arguments(&right);
                    if !receiver.ty.is_error()
                        && let Some(call) = self.bind_extension_call(
                            &name, &right, receiver, &arguments, &explicit, span,
                        )
                    {
                        return call;
                    }
                    return BoundExpression::error(span);
                };
                // `a?.Callback()` on a delegate field or a field-like event
                // calls what it holds.
                if let Some(found) = self.binder.lookup_member(symbol, &name).first().copied()
                    && (matches!(
                        self.kind_of(found),
                        SymbolKind::Field | SymbolKind::Property
                    ) || (self.kind_of(found) == SymbolKind::Event
                        && self.event_is_a_field_here(found)))
                {
                    let ty = self.member_type(found, &receiver.ty);
                    if self.is_invocable(&ty) {
                        // The call is to `Invoke`, which is what the name's
                        // symbol says; what the name itself is, is the
                        // member, as it is for a local or a parameter.
                        self.body
                            .references
                            .insert(right.span(), BoundSymbol::Declared(found));
                        let target = self.member_access(found, Some(Box::new(receiver)), ty, span);
                        return self.invoke_delegate(target, arguments, span);
                    }
                }
                let receiver_type = receiver.ty.clone();
                (
                    symbol,
                    name,
                    right,
                    receiver_type,
                    Some(Box::new(receiver)),
                    Some(false),
                )
            }
            SyntaxKind::SimpleMemberAccessExpression
            | SyntaxKind::PointerMemberAccessExpression => {
                let mut parts = callee.children();
                let (Some(left), Some(right)) = (parts.next(), parts.next()) else {
                    return BoundExpression::error(span);
                };
                let Some(name) = identifier_text(&right) else {
                    return BoundExpression::error(span);
                };
                if self.namespace_of(&left).is_some() {
                    return BoundExpression::error(span);
                }
                let mut receiver = self.bind_expression(&left);
                if callee.kind() == SyntaxKind::PointerMemberAccessExpression {
                    receiver = self.pointed_at(receiver);
                }
                // `d.M(...)` is a call the runtime binds.
                if matches!(receiver.ty, Type::Dynamic) {
                    let type_arguments = self.explicit_type_arguments(&right);
                    return Self::dynamic_operation(
                        DynamicOperation::InvokeMember {
                            name,
                            type_arguments,
                            simple_name: false,
                        },
                        Some(receiver),
                        arguments,
                        argument_names,
                        Type::Dynamic,
                        span,
                    );
                }
                if let Some(array) = self.as_system_array(&receiver, &name) {
                    array_receiver = Some(receiver.ty.clone());
                    receiver = BoundExpression::new(receiver.kind, array, receiver.span);
                }
                // `args.consumeItems(...)` on a tuple calls what an element
                // holds: the element is a field of the `ValueTuple`
                // underneath, under the name the runtime has for it.
                let mut name = name;
                if let Type::Tuple(elements) = &receiver.ty {
                    if let Some(at) = elements
                        .iter()
                        .position(|element| element.name.as_deref() == Some(name.as_str()))
                    {
                        name = format!("Item{}", at + 1);
                    }
                    let ty = self.tuple_as_named(elements);
                    receiver = BoundExpression::new(receiver.kind, ty, receiver.span);
                }
                let Some(symbol) = receiver.ty.symbol() else {
                    // An array has no symbol to look a member up on, and an
                    // extension method is not looked up on the receiver
                    // anyway: `numbers.Select(...)` is exactly this case.
                    // `items.Cast<string>()` writes the extension's type
                    // arguments, and they go with the call.
                    let explicit = self.explicit_type_arguments(&right);
                    if !receiver.ty.is_error()
                        && let Some(call) = self.bind_extension_call(
                            &name, &right, receiver, &arguments, &explicit, span,
                        )
                    {
                        return call;
                    }
                    return BoundExpression::error(span);
                };
                // `holder.Callback(1)` where `Callback` is a delegate field is
                // an invocation of what the field holds, not of a method.
                if let Some(found) = self.binder.lookup_member(symbol, &name).first().copied()
                    && (matches!(
                        self.kind_of(found),
                        SymbolKind::Field | SymbolKind::Property
                    ) || (self.kind_of(found) == SymbolKind::Event
                        && self.event_is_a_field_here(found)))
                {
                    let ty = self.member_type(found, &receiver.ty);
                    if self.is_invocable(&ty) {
                        // The call is to `Invoke`, which is what the name's
                        // symbol says; what the name itself is, is the
                        // member, as it is for a local or a parameter.
                        self.body
                            .references
                            .insert(right.span(), BoundSymbol::Declared(found));
                        let target = self.member_access(found, Some(Box::new(receiver)), ty, span);
                        return self.invoke_delegate(target, arguments, span);
                    }
                }
                let receiver_type = receiver.ty.clone();
                let names_a_type = matches!(receiver.kind, BoundExpressionKind::TypeExpression(_));
                // `Palette.Make()` where `Palette` is both a property and the
                // type it is of: §12.8.7.2 says the two spellings name the
                // same thing, so both a static member of the type and an
                // instance member of the value are in reach, and the lookup
                // decides which was meant.
                let both_ways = !names_a_type
                    && left.kind() == SyntaxKind::IdentifierName
                    && self.names_a_type(&left);
                let is_type = names_a_type && !is_constructed(&receiver.ty);
                let receiver = if is_type {
                    None
                } else {
                    Some(Box::new(receiver))
                };
                (
                    symbol,
                    name,
                    right,
                    receiver_type,
                    receiver,
                    (!both_ways).then_some(names_a_type),
                )
            }
            _ => {
                self.bind_expression(&callee);
                return BoundExpression::error(span);
            }
        };

        let symbols = self.binder.compilation().symbols();
        let mut candidates: Vec<_> = self
            .lookup_invocable_here(container, &name)
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .filter(|id| {
                names_a_type.is_none_or(|wanted| {
                    symbols.get(*id).modifiers.contains(Modifiers::STATIC) == wanted
                })
            })
            .collect();
        // `C.Make()` reaching a static method an extension block (C# 14)
        // gave `C`, where `C` has none of that name itself.
        if candidates.is_empty() && names_a_type == Some(true) {
            for candidate in self.binder.extension_members_in_scope(&self.context, &name) {
                let Some(extended) = symbols
                    .get(candidate)
                    .as_method()
                    .and_then(|detail| detail.extended)
                else {
                    continue;
                };
                if self.static_extension_fits(extended, &self.binder.self_type(container)) {
                    candidates.push(candidate);
                }
            }
        }
        // A `dynamic` argument leaves the overload to the runtime binder,
        // which is called with the receiver — `this` for a simple name in an
        // instance member, the type for a static one — and the arguments as
        // written (§12.6.4.1).
        if !candidates.is_empty() && Self::has_dynamic_argument(&arguments) {
            let simple_name = matches!(
                callee.kind(),
                SyntaxKind::IdentifierName | SyntaxKind::GenericName
            );
            // A field's initializer runs before any constructor, where `this`
            // is not to be read: the call is made on the type (Roslyn does
            // the same). So is one through a name that is both a type and a
            // value where the value cannot be had.
            let in_initializer = self.member.is_some_and(|member| {
                matches!(
                    self.kind_of(member),
                    SymbolKind::Field | SymbolKind::Property
                )
            });
            let site_receiver = match &receiver {
                Some(receiver) if names_a_type.is_none() && self.static_context() => {
                    BoundExpression::new(
                        BoundExpressionKind::TypeExpression(container),
                        receiver_type.clone(),
                        receiver.span,
                    )
                }
                Some(receiver) => (**receiver).clone(),
                // `this`, which a lambda around the call has to capture —
                // unless the methods are an enclosing type's, which `this`
                // does not have: `M(d)` in `A.B` calls `A.M` on the type.
                None if simple_name
                    && !self.static_context()
                    && !in_initializer
                    && self.this_type().symbol().is_some_and(|this| {
                        self.binder.derives_from_definition(this, container, 0)
                    }) =>
                {
                    self.note_this_capture();
                    BoundExpression::new(BoundExpressionKind::This, self.this_type(), span)
                }
                None => BoundExpression::new(
                    BoundExpressionKind::TypeExpression(container),
                    receiver_type.clone(),
                    span,
                ),
            };
            let implicit_this = matches!(site_receiver.kind, BoundExpressionKind::This);
            let type_arguments = self.explicit_type_arguments(&name_node);
            return Self::dynamic_operation(
                DynamicOperation::InvokeMember {
                    name,
                    type_arguments,
                    simple_name: simple_name && implicit_this,
                },
                Some(site_receiver),
                arguments,
                argument_names,
                Type::Dynamic,
                span,
            );
        }
        // `M(null)` written in a static method has no `this` to call an
        // instance `M` on, so only the static ones are candidates (C# 7.3).
        let candidates = if receiver.is_none()
            && matches!(
                callee.kind(),
                SyntaxKind::IdentifierName | SyntaxKind::GenericName
            )
            && self.static_context()
            && candidates
                .iter()
                .any(|id| symbols.get(*id).modifiers.contains(Modifiers::STATIC))
        {
            candidates
                .into_iter()
                .filter(|id| symbols.get(*id).modifiers.contains(Modifiers::STATIC))
                .collect()
        } else {
            candidates
        };
        let candidates = self.named_candidates(&candidates, &argument_names);
        // Where every candidate can read the names, each reads them into its
        // own parameters while the overloads are compared, and the arguments
        // are put in order for the one chosen (§12.6.2.2). `Bar(x: 1, y: "")`
        // is as much a call to `Bar(string y, int x)` as to `Bar(int x,
        // string y, params int[] z)`.
        let by_candidate = argument_names.iter().any(Option::is_some)
            && argument_names.len() == arguments.len()
            && !candidates.is_empty()
            && candidates
                .iter()
                .all(|candidate| self.named_order(*candidate, &argument_names).is_some());
        let arguments = if by_candidate {
            arguments
        } else {
            self.reorder_named(&candidates, &argument_names, arguments, &receiver_type)
        };
        let argument_types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();

        // `Echo<int>(7)` says what `T` is; `Echo(7)` leaves it to inference.
        let explicit = self.explicit_type_arguments(&name_node);

        let mut arguments = arguments;
        let resolved = if candidates.is_empty() {
            None
        } else if by_candidate {
            self.argument_names
                .borrow_mut()
                .push((candidates.clone(), argument_names.clone()));
            let resolved = self.resolve_with_lambdas(
                &candidates,
                &mut arguments,
                &receiver_type,
                &explicit,
                false,
            );
            self.argument_names.borrow_mut().pop();
            if let Some(chosen) = &resolved {
                arguments = self.reorder_named(
                    &[chosen.method],
                    &argument_names,
                    arguments,
                    &receiver_type,
                );
            }
            resolved
        } else {
            self.resolve_with_lambdas(
                &candidates,
                &mut arguments,
                &receiver_type,
                &explicit,
                false,
            )
        };

        // Nothing on the type answered. An extension method still might: it is
        // found by the name the call site wrote, among the static classes the
        // file imported, and only then checked against the receiver.
        if resolved.is_none()
            && let Some(receiver) = receiver.clone()
            && let Some(call) = self.bind_extension_call_named(
                &name,
                &name_node,
                match array_receiver {
                    Some(array) => BoundExpression::new(receiver.kind, array, receiver.span),
                    None => *receiver,
                },
                &arguments,
                &argument_names,
                &explicit,
                span,
            )
        {
            return call;
        }
        // Nor an extension method: an extension block's property (C# 14)
        // holding a delegate is invoked as one.
        // `object.M()` reads a static one through the type.
        let extension_receiver = receiver.clone().or_else(|| {
            (names_a_type == Some(true)).then(|| {
                Box::new(BoundExpression::new(
                    BoundExpressionKind::TypeExpression(container),
                    receiver_type.clone(),
                    span,
                ))
            })
        });
        if resolved.is_none()
            && candidates.is_empty()
            && let Some(receiver) = extension_receiver
            && let Some((target, _)) = self.extension_member_access(&receiver, &name, span)
            && self.is_invocable(&target.ty)
        {
            return self.invoke_delegate(target, arguments, span);
        }

        // `Nonesuch()` with nothing in front is a name nothing in scope has,
        // which is how Roslyn says it; the type it was looked for in is only
        // this binder's first guess.
        if candidates.is_empty()
            && matches!(
                callee.kind(),
                SyntaxKind::IdentifierName | SyntaxKind::GenericName
            )
            && self.binder.lookup_member(container, &name).is_empty()
        {
            if name_node.span().is_empty() {
                return BoundExpression::error(span);
            }
            // `e()` on a local or a parameter that holds no delegate: the
            // name is there, it is just not a method (CS0149) — unless its
            // type is already an error, which has been said.
            let variable = callee.kind() == SyntaxKind::IdentifierName
                && (self.lookup_local(&name).is_some()
                    || self
                        .member
                        .and_then(|member| self.lookup_parameter(member, &name))
                        .is_some());
            if variable {
                let value = self.bind_expression(&callee);
                if !value.ty.is_error() {
                    self.report(ErrorCode::ErrMethodNameExpected, callee.span(), &[]);
                }
                return BoundExpression::error(span);
            }
            self.report(ErrorCode::ErrNameNotInContext, name_node.span(), &[&name]);
            return BoundExpression::error(span);
        }
        // `Type.Instance()` and `value.Static()`: the method is there, on
        // the wrong side of the dot.
        if candidates.is_empty()
            && callee.kind() == SyntaxKind::SimpleMemberAccessExpression
            && let Some(wanted) = names_a_type
        {
            let symbols = self.binder.compilation().symbols();
            let other_side = self
                .binder
                .lookup_member(container, &name)
                .into_iter()
                .find(|id| {
                    self.kind_of(*id) == SymbolKind::Method
                        && symbols.get(*id).modifiers.contains(Modifiers::STATIC) != wanted
                });
            if let Some(method) = other_side {
                if wanted {
                    self.report_object_required(method, callee.span());
                } else {
                    let member = crate::checks::member_display(
                        self.binder.compilation(),
                        method,
                        &Default::default(),
                        None,
                    );
                    self.report(ErrorCode::ErrObjectProhibited, callee.span(), &[&member]);
                }
                return BoundExpression::error(span);
            }
        }
        if candidates.is_empty() {
            let container_name = if receiver_type.is_error() {
                self.binder
                    .compilation()
                    .symbols()
                    .qualified_name(container)
            } else {
                self.display(&receiver_type)
            };
            let code = receiver
                .as_deref()
                .map_or(ErrorCode::ErrNoSuchMember, missing_member_code);
            self.report(code, name_node.span(), &[&container_name, &name]);
            return BoundExpression::error(span);
        }

        match resolved {
            Some(resolved) => {
                let Resolved {
                    method,
                    type_arguments,
                    mut substitution,
                } = resolved;
                let introduced = method;
                let method = match &receiver {
                    Some(base) if matches!(base.kind, BoundExpressionKind::Base) => {
                        self.base_override(method, &base.ty)
                    }
                    _ => method,
                };
                // `Timer.Start()` beside a `Timer` field calls the static
                // `Start` through the type (§12.8.7.2): the name on the left
                // is the type, to an editor asking too.
                if callee.kind() == SyntaxKind::SimpleMemberAccessExpression
                    && let Some(left) = callee.children().next()
                    && left.kind() == SyntaxKind::IdentifierName
                    && let Some(ty) = receiver_type.symbol()
                {
                    let symbols = self.binder.compilation().symbols();
                    let is_static = symbols.get(method).modifiers.contains(Modifiers::STATIC)
                        && symbols
                            .get(method)
                            .as_method()
                            .is_some_and(|detail| !detail.is_extension);
                    if is_static
                        && let Some(BoundSymbol::Declared(named)) = self.body.symbol_at(left.span())
                        && named != ty
                        && symbols.get(named).name == symbols.get(ty).name
                    {
                        self.body
                            .references
                            .insert(left.span(), BoundSymbol::Declared(ty));
                        if self.body.symbols.contains_key(&left.span()) {
                            self.body.symbols.insert(left.span(), ty);
                        }
                    }
                }
                // The override `base.M<T>()` reaches has type parameters of
                // its own, which the call's type arguments stand for as much
                // as the introducing method's: an override two classes up
                // returns its `TResult`, not the base's.
                if method != introduced {
                    let symbols = self.binder.compilation().symbols();
                    if let (Some(theirs), Some(ours)) = (
                        symbols.get(introduced).as_method(),
                        symbols.get(method).as_method(),
                    ) {
                        for (their, our) in theirs.type_parameters.iter().zip(&ours.type_parameters)
                        {
                            if let Some(argument) = substitution.get(their).cloned() {
                                substitution.insert(*our, argument);
                            }
                        }
                    }
                }
                self.body
                    .references
                    .insert(name_node.span(), BoundSymbol::Declared(method));
                if !candidates
                    .iter()
                    .any(|candidate| self.accessible(*candidate))
                {
                    self.check_accessible(method, &name, name_node.span());
                }
                if receiver.is_none()
                    && matches!(
                        callee.kind(),
                        SyntaxKind::IdentifierName | SyntaxKind::GenericName
                    )
                    && self.needs_this(method)
                    && self.static_context()
                {
                    self.report_object_required(method, name_node.span());
                }
                let ty = self
                    .member_type(method, &receiver_type)
                    .substitute(&substitution);
                // An instance call written without a receiver is a call on
                // `this`, and the backend needs that receiver spelled out.
                let receiver = receiver.or_else(|| {
                    (callee.kind() != SyntaxKind::SimpleMemberAccessExpression)
                        .then(|| self.implicit_receiver(method, span))
                        .flatten()
                });
                // A type name that reaches a method through a generic base
                // stays: `MetadataDecoder.GetSignatureCountsOrThrow` is a
                // member of `MetadataDecoder<PEModuleSymbol, ...>`, and the
                // name is the only thing that says which construction.
                let receiver = receiver.or_else(|| {
                    let symbol = receiver_type.symbol()?;
                    (callee.kind() == SyntaxKind::SimpleMemberAccessExpression
                        && names_a_type == Some(true)
                        && self.inherited_from_generic(method, &receiver_type))
                    .then(|| {
                        Box::new(BoundExpression::new(
                            BoundExpressionKind::TypeExpression(symbol),
                            receiver_type.clone(),
                            callee.children().next().map_or(span, |left| left.span()),
                        ))
                    })
                });
                // `DiagnosticBag.GetInstance()` written where `DiagnosticBag`
                // is both the type and a property of it: §12.8.7.2 says the
                // two spellings name the same thing, and a static method is
                // reached through the type. What was written stays, as the
                // type it names — the backend still needs it to know which
                // construction — but nothing is evaluated for it.
                let is_static = self
                    .binder
                    .compilation()
                    .symbols()
                    .get(method)
                    .modifiers
                    .contains(Modifiers::STATIC);
                let receiver = receiver.map(|receiver| match receiver.ty.symbol() {
                    Some(symbol)
                        if is_static
                            && !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_)) =>
                    {
                        let (ty, span) = (receiver.ty.clone(), receiver.span);
                        Box::new(BoundExpression::new(
                            BoundExpressionKind::TypeExpression(symbol),
                            ty,
                            span,
                        ))
                    }
                    _ => receiver,
                });
                let arguments =
                    self.convert_arguments(method, arguments, &receiver_type, &substitution, span);
                let receiver = match receiver {
                    Some(receiver) => Some(Box::new(self.capture_receiver(*receiver))),
                    None => {
                        self.pending_receiver = None;
                        None
                    }
                };
                let virtual_call = self.is_virtual_call(method, callee.children().next().as_ref());
                BoundExpression::new(
                    BoundExpressionKind::Call {
                        receiver,
                        method,
                        type_arguments,
                        arguments,
                        virtual_call,
                    },
                    ty,
                    span,
                )
            }
            None => {
                let spans: Vec<TextSpan> = arguments.iter().map(|argument| argument.span).collect();
                self.report_no_overload(
                    &candidates,
                    &name,
                    &argument_types,
                    &spans,
                    &receiver_type,
                    &explicit,
                    name_node.span(),
                    None,
                );
                BoundExpression::error(span)
            }
        }
    }

    /// Whether an expression is a call to a method the file's preprocessor
    /// symbols write out of the program.
    ///
    /// `[Conditional("DEBUG")]` on a method means every call to it is kept
    /// only where `DEBUG` is defined. The method itself stays; the call does
    /// not, and neither do its arguments.
    pub(super) fn is_conditioned_out(&self, value: &BoundExpression) -> bool {
        // `Create()?.Test()` goes as a whole, `Create()` and all, where the
        // call it makes does: nothing is left to make it for.
        if let BoundExpressionKind::ConditionalAccess { access, .. } = &value.kind {
            return self.is_conditioned_out(access);
        }
        let BoundExpressionKind::Call { method, .. } = &value.kind else {
            return false;
        };
        let Some(conditions) = self.binder.conditional_symbols(*method) else {
            return false;
        };
        let Some(tree) = self.binder.compilation().trees().get(self.tree) else {
            return false;
        };
        // Several `[Conditional]` attributes on one method mean *any* of them
        // keeps the call, and each is asked where the call is: a `#define`
        // or `#undef` above it counts.
        !conditions
            .iter()
            .any(|condition| tree.is_defined_at(condition, value.span.start()))
    }

    /// The type arguments a call wrote for itself, where it wrote any.
    fn explicit_type_arguments(&mut self, name_node: &SyntaxNode) -> Vec<Type> {
        name_node
            .child_of_kind(SyntaxKind::TypeArgumentList)
            .map(|list| {
                list.children()
                    .filter(|child| child.kind().is_type_node())
                    .map(|argument| self.resolve(&argument))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Binds a call to a known set of candidates with no receiver.
    fn bind_resolved_call(
        &mut self,
        candidates: &[SymbolId],
        name_node: &SyntaxNode,
        arguments: &[BoundExpression],
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let types: Vec<Type> = arguments
            .iter()
            .map(|argument| argument.ty.clone())
            .collect();
        // `Read<Token>()` says what `T` is where no argument could: a local
        // function or an imported static is named the same way as any other
        // method, type arguments and all.
        let explicit = self.explicit_type_arguments(name_node);
        let Resolved {
            method,
            type_arguments,
            substitution,
        } = self.resolve_call(
            candidates,
            &types,
            &self.evidence(arguments),
            &Type::Void,
            &explicit,
        )?;
        self.body
            .references
            .insert(name_node.span(), BoundSymbol::Declared(method));
        let ty = self
            .member_type(method, &Type::Void)
            .substitute(&substitution);
        let arguments =
            self.convert_arguments(method, arguments.to_vec(), &Type::Void, &substitution, span);
        // An instance local function is an instance method in metadata, so
        // the call has to carry the `this` the source did not write.
        let receiver = self.implicit_receiver(method, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            ty,
            span,
        ))
    }

    /// `nameof(Foo.Bar)` as the string `"Bar"`.
    ///
    /// C# reads it as an ordinary invocation and then notices that nothing is
    /// called `nameof`; a real member with that name wins, which is why the
    /// lookup happens first. What comes out is the last identifier written,
    /// with no type arguments and no dots.
    fn bind_nameof(
        &mut self,
        node: &SyntaxNode,
        callee: &SyntaxNode,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if callee.kind() != SyntaxKind::IdentifierName
            || identifier_text(callee).as_deref() != Some("nameof")
        {
            return None;
        }
        // Only a `nameof` that can be called makes this a call (Roslyn's
        // `InvocableNameofInScope`): a method, or a value of a delegate type.
        // `char nameof;` beside it leaves `nameof(x)` the operator.
        let invocable = |this: &Self, ty: &Type| {
            matches!(ty, Type::Dynamic)
                || ty.symbol().is_some_and(|symbol| {
                    this.binder.compilation().symbols().get(symbol).type_kind()
                        == Some(TypeKind::Delegate)
                })
        };
        let local_invocable = self
            .lookup_local("nameof")
            .is_some_and(|local| invocable(self, &self.local_type(local)));
        let parameter_invocable = self
            .member
            .and_then(|member| self.lookup_parameter(member, "nameof"))
            .is_some_and(|parameter| {
                invocable(
                    self,
                    &self.binder.type_of(parameter, &mut Diagnostics::new()),
                )
            });
        let member_invocable = self.context.enclosing_type().is_some_and(|ty| {
            self.binder
                .lookup_member(ty, "nameof")
                .into_iter()
                .any(|member| {
                    let symbols = self.binder.compilation().symbols();
                    symbols.get(member).kind == SymbolKind::Method
                        || invocable(self, &self.binder.type_of(member, &mut Diagnostics::new()))
                })
        });
        if local_invocable || parameter_invocable || member_invocable {
            return None;
        }
        let arguments = node.child_of_kind(SyntaxKind::ArgumentList)?;
        let mut written = arguments.children();
        let argument = written.next()?;
        if written.next().is_some() {
            return None;
        }
        // The argument is never evaluated, but it does name something, and
        // an editor asks what. Binding it records that; whatever it would
        // report is not this program's error — `nameof(List<int>.Count)`
        // reads an instance member through a type, which only `nameof` may.
        if let Some(expression) = argument.children().next() {
            let reported = self.body.diagnostics.len();
            let outer = std::mem::replace(&mut self.in_nameof, true);
            let _ = self.bind_expression(&expression);
            self.in_nameof = outer;
            self.body.diagnostics.truncate(reported);
        }
        // The rightmost simple name: `A.B<C>.D` is `"D"`, and `B<C, D>` is
        // `"B"` — its arguments are no part of its name.
        let name = argument
            .children()
            .next()
            .and_then(|expression| nameof_name(&expression))
            .or_else(|| {
                argument
                    .descendant_tokens()
                    .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .last()
                    .map(|token| token.value_text().to_string())
            })?;
        Some(BoundExpression::new(
            BoundExpressionKind::Literal(ConstantValue::String(name)),
            self.special(SpecialType::String),
            span,
        ))
    }

    /// `text.Twice()` as `Extensions.Twice(text)`, when there is such a method
    /// in scope that the receiver fits.
    ///
    /// The result is an ordinary static call: the receiver becomes the first
    /// argument, which is exactly what the CLI sees, and what makes extension
    /// methods a compile-time convenience rather than a runtime feature.
    pub(super) fn bind_extension_call(
        &mut self,
        name: &str,
        name_node: &SyntaxNode,
        receiver: BoundExpression,
        arguments: &[BoundExpression],
        explicit: &[Type],
        span: TextSpan,
    ) -> Option<BoundExpression> {
        self.bind_extension_call_named(name, name_node, receiver, arguments, &[], explicit, span)
    }

    /// The same, with the names the call site wrote for its arguments.
    ///
    /// `method.CheckConstraints(args, ..., nullabilityOpt: null, ref
    /// useSite, ignoreOpt: set)` names two of its arguments and leaves an
    /// optional one between them unfilled; where they go is decided against
    /// the extension's own parameters, receiver first.
    #[allow(clippy::too_many_arguments)]
    fn bind_extension_call_named(
        &mut self,
        name: &str,
        name_node: &SyntaxNode,
        receiver: BoundExpression,
        arguments: &[BoundExpression],
        names: &[Option<String>],
        explicit: &[Type],
        span: TextSpan,
    ) -> Option<BoundExpression> {
        // Only the ones this code may call are candidates: a private one in
        // another static class is not.
        let accessible = self.extensions_here(name);
        let levels: Vec<Vec<SymbolId>> = self
            .binder
            .extension_levels(&self.context, name)
            .into_iter()
            .map(|level| {
                level
                    .into_iter()
                    .filter(|method| accessible.contains(method))
                    .collect::<Vec<_>>()
            })
            .filter(|level| !level.is_empty())
            .collect();
        let mut given: Vec<BoundExpression> = arguments.to_vec();
        given.insert(0, receiver);
        // The nearest set of candidates with one that applies is the set
        // the call is resolved in (§12.8.10.3).
        let last = levels.len().saturating_sub(1);
        let mut settled = None;
        for (at, candidates) in levels.iter().enumerate() {
            let floor = self.body.diagnostics.len();
            let mut arguments = given.clone();
            let mut candidates = candidates.clone();
            if names.iter().any(Option::is_some) && names.len() + 1 == arguments.len() {
                let mut names = names.to_vec();
                names.insert(0, None);
                candidates = self.named_candidates(&candidates, &names);
                arguments = self.reorder_named(&candidates, &names, arguments, &Type::Void);
            }
            let candidates = &candidates;
            let unbound = arguments.clone();
            let speculation = self.speculation_floor();
            // A static class has no type arguments of its own, so there is
            // nothing for the receiver to substitute into the signature.
            if let Some(resolved) =
                self.resolve_with_lambdas(candidates, &mut arguments, &Type::Void, explicit, true)
            {
                // A lambda no delegate here takes leaves the first choice
                // to report it against, which is no reason to stop looking:
                // UniTask's `Select(Func<T, UniTask>)` in an enclosing
                // namespace does not take `p => p.Name`, and LINQ's does.
                let rejected = at != last
                    && unbound.iter().any(|argument| {
                        matches!(argument.kind, BoundExpressionKind::UnboundLambda(_))
                    })
                    && self.lambdas_fit(&resolved, &unbound, &Type::Void, explicit)
                        == super::Fit::Bad;
                if !rejected {
                    settled = Some((resolved, arguments));
                    break;
                }
                // Nothing of the scope passed over stays: its lambdas,
                // bound against delegates the call does not take, would
                // each be emitted.
                self.unwind_speculation(speculation);
                continue;
            }
            // What a farther set is tried for is not an error of the nearer.
            if at != last {
                self.body.diagnostics.truncate(floor);
            }
        }
        let (
            Resolved {
                method,
                type_arguments,
                substitution,
            },
            arguments,
        ) = settled?;

        self.body
            .references
            .insert(name_node.span(), BoundSymbol::Declared(method));
        let ty = self
            .member_type(method, &Type::Void)
            .substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, &Type::Void, &substitution, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            ty,
            span,
        ))
    }

    /// `receiver.Name()` as a call to an extension method in scope, for a
    /// call the compiler makes rather than the source: no name node to note
    /// a reference under, and no arguments beyond the receiver.
    pub(super) fn extension_call_at(
        &mut self,
        name: &str,
        receiver: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        self.extension_call_with(name, receiver, Vec::new(), span)
    }

    /// The same with arguments after the receiver: the `Add` a collection
    /// initializer calls may be an extension (§12.8.17.4).
    fn extension_call_with(
        &mut self,
        name: &str,
        receiver: BoundExpression,
        rest: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let candidates = self.extensions_here(name);
        if candidates.is_empty() {
            return None;
        }
        let mut arguments = vec![receiver];
        arguments.extend(rest);
        let Resolved {
            method,
            type_arguments,
            substitution,
        } = self.resolve_with_lambdas(&candidates, &mut arguments, &Type::Void, &[], true)?;
        let ty = self
            .member_type(method, &Type::Void)
            .substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, &Type::Void, &substitution, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            ty,
            span,
        ))
    }

    /// Whether the call dispatches on the run-time type.
    ///
    /// `base.M()` names a virtual method and still calls it non-virtually,
    /// which is the whole point of `base`.
    pub(super) fn is_virtual_call(&self, method: SymbolId, receiver: Option<&SyntaxNode>) -> bool {
        if receiver.is_some_and(|node| node.kind() == SyntaxKind::BaseExpression) {
            return false;
        }
        let symbols = self.binder.compilation().symbols();
        let modifiers = symbols.get(method).modifiers;
        modifiers.contains(Modifiers::VIRTUAL)
            || modifiers.contains(Modifiers::OVERRIDE)
            || modifiers.contains(Modifiers::ABSTRACT)
            || symbols.get(method).container.is_some_and(|container| {
                symbols.get(container).type_kind() == Some(TypeKind::Interface)
            })
    }

    /// Converts each argument to the parameter it was matched with.
    pub(super) fn convert_arguments(
        &mut self,
        method: SymbolId,
        arguments: Vec<BoundExpression>,
        receiver: &Type,
        method_arguments: &HashMap<SymbolId, Type>,
        span: TextSpan,
    ) -> Vec<BoundExpression> {
        let mut substitution = self.substitution_for(method, receiver);
        substitution.extend(method_arguments.iter().map(|(k, v)| (*k, v.clone())));
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(method).as_method() else {
            return arguments;
        };
        let parameters: Vec<Type> = detail
            .parameters
            .iter()
            .map(|id| {
                let mut sink = Diagnostics::new();
                self.binder
                    .type_of(*id, &mut sink)
                    .substitute(&substitution)
            })
            .collect();
        // What a parameter left out defaults to, caller information
        // included, is read off the declaration the receiver's static type
        // sees: an override's, where it has one nearer than the method
        // resolution settled on (§12.6.4.1 settles on the least overridden).
        let declared: Vec<SymbolId> = {
            let nearest = self.base_override(method, receiver);
            symbols
                .get(nearest)
                .as_method()
                .filter(|near| near.parameters.len() == detail.parameters.len())
                .map_or_else(|| detail.parameters.clone(), |near| near.parameters.clone())
        };
        // `Write("{0}", a, b)` passes one array, and the call site wrote
        // three arguments: the array is the compiler's, and this is where it
        // is made. Everything downstream then sees an ordinary call.
        let arguments = match self.params_element(method, &parameters) {
            Some(element) if !passes_the_array(self.binder, &arguments, &parameters) => {
                let fixed = parameters.len() - 1;
                let mut fixed_arguments: Vec<BoundExpression> = arguments;
                let written = fixed_arguments.len();
                // The array is the *last* argument, so everything optional
                // before it is filled first. `new D(id, title, msg, category,
                // severity, enabled)` leaves two optionals and the array
                // after them: putting the array where the first optional goes
                // passes it as the wrong parameter and leaves the call one
                // argument short.
                while fixed_arguments.len() < fixed {
                    let at = fixed_arguments.len();
                    // Only what the call site wrote has text to quote: a
                    // default filled in above it does not.
                    let given: Vec<Option<TextSpan>> = fixed_arguments
                        .iter()
                        .enumerate()
                        .map(|(index, argument)| {
                            // A default a name skipped over was filled in
                            // already, and has no text at the call.
                            (index < written && written_at_call(argument.span, span))
                                .then_some(argument.span)
                        })
                        .collect();
                    let Some(filled) =
                        self.default_argument(declared[at], &parameters[at], span, &given)
                    else {
                        break;
                    };
                    fixed_arguments.push(filled);
                }
                let rest = fixed_arguments.split_off(fixed.min(fixed_arguments.len()));
                let rest: Vec<BoundExpression> = rest
                    .into_iter()
                    .map(|argument| self.convert(argument, &element))
                    .collect();
                let collection = match parameters.last() {
                    Some(target) if !matches!(target, Type::Array { .. }) => {
                        let target = target.clone();
                        self.collection_of(&target, &element, rest, span)
                    }
                    _ => BoundExpression::new(
                        BoundExpressionKind::ArrayCreation {
                            element: element.clone(),
                            lengths: Vec::new(),
                            elements: rest,
                        },
                        Type::Array {
                            element: Box::new(element),
                            rank: 1,
                        },
                        span,
                    ),
                };
                fixed_arguments.push(collection);
                fixed_arguments
            }
            _ => arguments,
        };
        // An optional parameter the call site left out is still a slot in the
        // signature, and the runtime counts arguments: filling it here means
        // no backend has to know that `M(a)` and `M(a, 2)` are the same call.
        let mut arguments = arguments;
        let written = arguments.len();
        while arguments.len() < parameters.len() {
            let at = arguments.len();
            let given: Vec<Option<TextSpan>> = arguments
                .iter()
                .enumerate()
                .map(|(index, argument)| {
                    // A default a name skipped over was filled in
                    // already, and has no text at the call.
                    (index < written && written_at_call(argument.span, span))
                        .then_some(argument.span)
                })
                .collect();
            let Some(filled) = self.default_argument(declared[at], &parameters[at], span, &given)
            else {
                break;
            };
            arguments.push(filled);
        }
        // `in` is a reference the call site need not write, and the callee's
        // signature says `T&` either way: what goes in is where the value is,
        // not a copy of it.
        // So is the receiver of a `this ref` extension: `builder.Add(x)`
        // reaches `Add(ref builder, x)` and writes no `ref`.
        // A `[ComImport]` type's method takes `x` for a `ref` parameter, as
        // the address of a copy of it.
        let takes_ref = detail.parameters.iter().any(|parameter| {
            symbols
                .get(*parameter)
                .as_parameter()
                .is_some_and(|detail| detail.ref_kind == RefKind::Ref)
        });
        let com = takes_ref
            && symbols
                .get(method)
                .container
                .is_some_and(|container| self.binder.is_com_import(container));
        let extension = detail.is_extension;
        let by_reference: Vec<(bool, RefKind)> = detail
            .parameters
            .iter()
            .enumerate()
            .map(|(index, id)| {
                symbols
                    .get(*id)
                    .as_parameter()
                    .map_or((false, RefKind::None), |parameter| {
                        match parameter.ref_kind {
                            RefKind::In => (true, RefKind::In),
                            RefKind::Ref if index == 0 && detail.is_extension => {
                                (true, RefKind::Ref)
                            }
                            RefKind::Ref if com => (true, RefKind::Ref),
                            _ => (false, RefKind::None),
                        }
                    })
            })
            .collect();
        // An interpolated string given to a handler may be made with the
        // other arguments and the receiver (C# 10): the rest are converted
        // first, and each handler is then made with them in reach.
        let mut converted: Vec<BoundExpression> = Vec::with_capacity(arguments.len());
        let mut handlers: Vec<(usize, BoundExpression, Type)> = Vec::new();
        for (index, argument) in arguments.into_iter().enumerate() {
            let argument = match parameters.get(index) {
                // `out var value` and `out _` have no type until the
                // overload is picked: this is where it is picked.
                Some(parameter) if is_untyped_out(&argument, &self.body.locals) => {
                    self.give_out_a_type(argument, parameter)
                }
                Some(parameter)
                    if ends_interpolated(&argument) && self.is_handler_type(parameter) =>
                {
                    let span = argument.span;
                    handlers.push((index, argument, parameter.clone()));
                    converted.push(BoundExpression::error(span));
                    continue;
                }
                Some(parameter) => self.convert(argument, parameter),
                None => argument,
            };
            let (wanted, kind) = by_reference
                .get(index)
                .copied()
                .unwrap_or((false, RefKind::None));
            if !wanted || matches!(argument.kind, BoundExpressionKind::RefArgument { .. }) {
                converted.push(argument);
                continue;
            }
            let (ty, span) = (argument.ty.clone(), argument.span);
            // The omitted `ref` of a COM call passes a copy: the variable
            // written is not the one the callee writes to.
            let argument = if com && kind == RefKind::Ref && !(index == 0 && extension) {
                BoundExpression::new(
                    BoundExpressionKind::Conversion {
                        operand: Box::new(argument),
                        conversion: crate::bound::ConversionKind::Identity,
                        written: false,
                    },
                    ty.clone(),
                    span,
                )
            } else {
                argument
            };
            converted.push(BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind,
                    operand: Box::new(argument),
                },
                ty,
                span,
            ));
        }
        let mut capture = HandlerCapture::default();
        for (index, argument, parameter) in handlers {
            let declared = detail.parameters.get(index).copied();
            let made = match declared {
                Some(declared) => self.handler_argument(
                    argument,
                    &parameter,
                    declared,
                    index,
                    &detail.parameters,
                    &mut converted,
                    &mut capture,
                    receiver,
                ),
                None => self.convert(argument, &parameter),
            };
            // A handler struct's `ref` or `in` parameter takes the handler
            // made for it as the variable, written without `ref`.
            let taken = declared
                .and_then(|declared| symbols.get(declared).as_parameter())
                .map_or(RefKind::None, |parameter| parameter.ref_kind);
            converted[index] = if matches!(taken, RefKind::Ref | RefKind::In) {
                let (ty, span) = (made.ty.clone(), made.span);
                BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind: taken,
                        operand: Box::new(made),
                    },
                    ty,
                    span,
                )
            } else {
                made
            };
        }
        self.pending_receiver = capture.receiver;
        converted
    }

    /// Whether an argument is a variable an `in` parameter can be handed
    /// by reference: a field, an array element, or what a method returning
    /// a reference refers to.
    fn is_referenceable(&self, argument: &BoundExpression) -> bool {
        match &argument.kind {
            BoundExpressionKind::Call { method, .. } => {
                let mut sink = crate::Diagnostics::new();
                matches!(self.binder.type_of(*method, &mut sink), Type::ByRef(_))
            }
            BoundExpressionKind::Field { .. } | BoundExpressionKind::ArrayAccess { .. } => true,
            _ => false,
        }
    }

    /// Fills in the type of an `out` variable that was written without one.
    pub(super) fn give_out_a_type(
        &mut self,
        argument: BoundExpression,
        ty: &Type,
    ) -> BoundExpression {
        let span = argument.span;
        let (kind, local) = match argument.kind {
            BoundExpressionKind::RefArgument { kind, operand } => match operand.kind {
                BoundExpressionKind::Local(local) => (Some(kind), local),
                _ => return BoundExpression::new(BoundExpressionKind::Error, Type::Error, span),
            },
            BoundExpressionKind::Local(local) => (None, local),
            _ => return argument,
        };
        if let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
            slot.ty = ty.clone();
        }
        // The `var value` that was written has a type now, and whoever asks
        // the model about that piece of syntax should be told it.
        self.body.types.insert(span, ty.clone());
        let operand = BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span);
        match kind {
            Some(kind) => BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind,
                    operand: Box::new(operand),
                },
                ty.clone(),
                span,
            ),
            None => operand,
        }
    }

    /// If `node` names something holding a delegate, that something, bound.
    ///
    /// The name is resolved before it is bound, because a method of the same
    /// name has to win: `Square(2)` calls the method, whatever a delegate of
    /// that name would do.
    fn delegate_in_scope(&mut self, node: &SyntaxNode) -> Option<BoundExpression> {
        let name = identifier_text(node)?;
        let holds_a_delegate = if self.lookup_local(&name).is_some() {
            true
        } else if let Some(member) = self.member
            && self.lookup_parameter(member, &name).is_some()
        {
            true
        } else {
            // A field, a property or a field-like event of the enclosing type
            // will do; a method will not, being a method group and not a value.
            // A nested type sees what the types around it declare: `F1()` in
            // a class nested in an interface raises the interface's event.
            let found = self
                .context
                .enclosing_types()
                .into_iter()
                .find_map(|enclosing| {
                    self.binder.lookup_member(enclosing, &name).first().copied()
                })?;
            // A field-like event is its field inside the type declaring
            // it, and `E()` there calls what it holds.
            matches!(
                self.kind_of(found),
                SymbolKind::Field | SymbolKind::Property
            ) || (self.kind_of(found) == SymbolKind::Event && self.event_is_a_field_here(found))
        };
        if !holds_a_delegate {
            return None;
        }
        let holder = self.bind_expression(node);
        (self.is_invocable(&holder.ty) || matches!(holder.ty, Type::Dynamic)).then_some(holder)
    }

    /// Whether a value of the type is called by writing `(...)` after it: a
    /// delegate, or a function pointer.
    fn is_invocable(&self, ty: &Type) -> bool {
        self.is_delegate(ty) || matches!(ty, Type::FunctionPointer(_))
    }

    pub(super) fn is_delegate(&self, ty: &Type) -> bool {
        ty.symbol()
            .and_then(|symbol| self.kind_of_type(symbol))
            .is_some_and(|kind| kind == TypeKind::Delegate)
    }

    /// `f(x)` on a delegate, which is `f.Invoke(x)`.
    pub(super) fn invoke_delegate(
        &mut self,
        target: BoundExpression,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        // What a `dynamic` value holds, or a delegate given a `dynamic`
        // argument, is called through the runtime binder.
        if matches!(target.ty, Type::Dynamic) || Self::has_dynamic_argument(&arguments) {
            let names = vec![None; arguments.len()];
            return Self::dynamic_operation(
                DynamicOperation::Invoke,
                Some(target),
                arguments,
                names,
                Type::Dynamic,
                span,
            );
        }
        if let Type::FunctionPointer(signature) = &target.ty {
            return self.invoke_function_pointer(target.clone(), signature, arguments, span);
        }
        let symbols = self.binder.compilation().symbols();
        let Some(invoke) = target
            .ty
            .symbol()
            .and_then(|symbol| symbols.lookup(symbol, "Invoke").first().copied())
        else {
            return BoundExpression::error(span);
        };
        let ty = self.member_type(invoke, &target.ty);
        let receiver_type = target.ty.clone();
        let arguments =
            self.convert_arguments(invoke, arguments, &receiver_type, &HashMap::new(), span);
        BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(target)),
                method: invoke,
                type_arguments: Vec::new(),
                arguments,
                // `Invoke` is virtual, and the runtime provides its body.
                virtual_call: true,
            },
            ty,
            span,
        )
    }

    /// `f(a, b)` through a function pointer: each argument converted to the
    /// parameter the pointer's signature has in its place. There are no
    /// names, defaults or `params` to sort out, since there is no method.
    fn invoke_function_pointer(
        &mut self,
        target: BoundExpression,
        signature: &crate::types::FunctionPointer,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        if arguments.len() != signature.parameters.len() {
            return BoundExpression::error(span);
        }
        let arguments = arguments
            .into_iter()
            .zip(&signature.parameters)
            .map(|(argument, (kind, parameter))| {
                let converted = if is_untyped_out(&argument, &self.body.locals) {
                    self.give_out_a_type(argument, parameter)
                } else {
                    self.convert(argument, parameter)
                };
                // `in` is a reference the call site need not write.
                if *kind != RefKind::In
                    || matches!(converted.kind, BoundExpressionKind::RefArgument { .. })
                {
                    return converted;
                }
                let (ty, span) = (converted.ty.clone(), converted.span);
                BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind: RefKind::In,
                        operand: Box::new(converted),
                    },
                    ty,
                    span,
                )
            })
            .collect();
        let returns = signature.returns.clone();
        BoundExpression::new(
            BoundExpressionKind::FunctionPointerCall {
                pointer: Box::new(target),
                arguments,
            },
            returns,
            span,
        )
    }

    /// The names `foo(count: 2)` wrote, one per argument.
    pub(super) fn argument_names(list: &SyntaxNode) -> Vec<Option<String>> {
        list.children()
            .filter(|child| child.kind() == SyntaxKind::Argument)
            .map(|argument| {
                argument
                    .child_of_kind(SyntaxKind::NameColon)?
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| token.value_text().to_string())
            })
            .collect()
    }

    /// The candidates a call's argument names can be placed into at all
    /// (§12.6.2.2): each name is a parameter's, no parameter is given twice,
    /// and a named argument followed by a positional one stands in its own
    /// position. `M(3, a: 4)` rules out `M(int a, int b)` whatever the
    /// types say, and `new C(c: x, 2)` is not a call to `C(int i, object o)`.
    /// Where none fits, all are kept, for the error to be reported against.
    pub(super) fn named_candidates(
        &self,
        candidates: &[SymbolId],
        names: &[Option<String>],
    ) -> Vec<SymbolId> {
        if names.iter().all(Option::is_none) {
            return candidates.to_vec();
        }
        let symbols = self.binder.compilation().symbols();
        let last_positional = names.iter().rposition(Option::is_none);
        let fits = |candidate: SymbolId| {
            let Some(parameters) = member_parameters(symbols, candidate) else {
                return true;
            };
            let is_params = |index: usize| {
                index + 1 == parameters.len()
                    && symbols
                        .get(parameters[index])
                        .as_parameter()
                        .is_some_and(|parameter| parameter.is_params)
            };
            let mut taken = vec![false; parameters.len()];
            for (position, name) in names.iter().enumerate() {
                let index = match name {
                    Some(name) => {
                        let Some(index) = parameters
                            .iter()
                            .position(|parameter| call_name(symbols, *parameter) == name)
                        else {
                            return false;
                        };
                        if last_positional.is_some_and(|last| last > position) && index != position
                        {
                            return false;
                        }
                        index
                    }
                    None if position < parameters.len() => position,
                    None if !parameters.is_empty() && is_params(parameters.len() - 1) => {
                        continue;
                    }
                    None => return false,
                };
                if taken[index] && !is_params(index) {
                    return false;
                }
                taken[index] = true;
            }
            true
        };
        let kept: Vec<SymbolId> = candidates
            .iter()
            .copied()
            .filter(|candidate| fits(*candidate))
            .collect();
        if kept.is_empty() {
            candidates.to_vec()
        } else {
            kept
        }
    }

    /// Puts named arguments where the parameters they name are.
    ///
    /// `Add(right: 1, left: 10)` passes 10 first. Which parameter a name
    /// belongs to depends on the overload, so the first candidate that has
    /// all the names decides — overloads share parameter names, and one that
    /// does not would be a different call anyway.
    pub(super) fn reorder_named(
        &mut self,
        candidates: &[SymbolId],
        names: &[Option<String>],
        arguments: Vec<BoundExpression>,
        receiver: &Type,
    ) -> Vec<BoundExpression> {
        if names.iter().all(Option::is_none) || names.len() != arguments.len() {
            return arguments;
        }
        // A private overload of another class is not the one the names were
        // written for, however well they fit it.
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
        let span = arguments
            .first()
            .map_or(TextSpan::new(0, 0), |first| first.span);
        // A candidate that needs nothing filled in is the one the call site
        // meant. `M(a, b, out c, isOptional: d)` names the last parameter of a
        // four-parameter overload and the last of a six-parameter one; only
        // the first reading leaves no hole, and picking the other would hand
        // six arguments to a call that wrote four.
        // Four readings, best first. "Exact" means the names left no hole to
        // fill; "fits" means the arguments, once placed, are of the types the
        // candidate wants. `GetWellKnownTypeMember(compilation, member, bag,
        // syntax: node)` leaves no hole in the five-parameter overload whose
        // fourth parameter is `syntax` — and hands that overload a
        // `CSharpCompilation` where it wants a `WellKnownMember`. The
        // six-parameter one it was written for does leave a hole, and is the
        // one the arguments fit.
        for (exact, fits) in [(true, true), (false, true), (true, false), (false, false)] {
            for candidate in candidates {
                let symbols = self.binder.compilation().symbols();
                let Some(parameters) = member_parameters(symbols, *candidate).map(<[_]>::to_vec)
                else {
                    continue;
                };
                let mut slots: Vec<Option<BoundExpression>> = vec![None; parameters.len()];
                let mut sources: Vec<Option<usize>> = vec![None; parameters.len()];
                let mut placed = true;
                for (position, (name, argument)) in names.iter().zip(arguments.iter()).enumerate() {
                    let index = match name {
                        Some(name) => parameters
                            .iter()
                            .position(|id| call_name(symbols, *id) == name),
                        None => Some(position),
                    };
                    let Some(index) = index.filter(|index| *index < slots.len()) else {
                        placed = false;
                        break;
                    };
                    if slots[index].is_some() {
                        placed = false;
                        break;
                    }
                    slots[index] = Some(argument.clone());
                    sources[index] = Some(position);
                }
                if !placed {
                    continue;
                }
                // A name may skip over an optional parameter — `M(a, syntax: s)`
                // leaves the `location` between them out — and what it skipped is
                // filled in here, because everything downstream counts arguments.
                let last = slots
                    .iter()
                    .rposition(Option::is_some)
                    .map_or(0, |at| at + 1);
                let written: Vec<bool> = slots.iter().map(Option::is_some).collect();
                for index in 0..if exact { 0 } else { last } {
                    if slots[index].is_some() {
                        continue;
                    }
                    let wanted = self.member_type(parameters[index], receiver);
                    let given: Vec<Option<TextSpan>> = slots
                        .iter()
                        .zip(&written)
                        .map(|(slot, written)| {
                            slot.as_ref()
                                .filter(|_| *written)
                                .map(|argument| argument.span)
                        })
                        .collect();
                    let Some(filled) =
                        self.default_argument(parameters[index], &wanted, span, &given)
                    else {
                        placed = false;
                        break;
                    };
                    slots[index] = Some(filled);
                }
                if !placed || (exact && last != arguments.len()) {
                    continue;
                }
                sources.truncate(last);
                let placed: Vec<BoundExpression> = slots.into_iter().take(last).flatten().collect();
                if fits && !self.arguments_fit(*candidate, &placed, receiver) {
                    continue;
                }
                let by_reference: Vec<bool> = parameters
                    .iter()
                    .take(last)
                    .map(|id| {
                        symbols
                            .get(*id)
                            .as_parameter()
                            .is_some_and(|detail| detail.ref_kind == RefKind::In)
                    })
                    .collect();
                let handlers: Vec<bool> = parameters
                    .iter()
                    .take(last)
                    .map(|id| self.is_handler_type(&self.member_type(*id, receiver)))
                    .collect();
                // What each argument goes to, where that needs no inference:
                // a `new()` stored ahead of the call is made as it first.
                let type_parameters = symbols
                    .get(*candidate)
                    .as_method()
                    .map(|detail| detail.type_parameters.clone())
                    .unwrap_or_default();
                let wanted: Vec<Option<Type>> = parameters
                    .iter()
                    .take(last)
                    .map(|id| {
                        let ty = self.member_type(*id, receiver);
                        (!type_parameters
                            .iter()
                            .any(|parameter| super::inference::mentions(&ty, *parameter)))
                        .then_some(ty)
                    })
                    .collect();
                return self.in_written_order(placed, &sources, &by_reference, &handlers, &wanted);
            }
        }
        arguments
    }

    /// Arguments put in parameter order are still evaluated in the order
    /// they were written (§12.6.2.2): where the two differ, each one that
    /// could do or see something is stored ahead of the call into a local
    /// of its own, in written order — a `ref` one into a `ref` local — and
    /// the first argument evaluated does the storing. `sources` says where
    /// each argument was written, and is `None` for a default filled in.
    ///
    /// An argument with no type of its own — a `new()`, a collection
    /// expression — is made as the parameter's type before it is stored,
    /// where `wanted` says what that is; a lambda is not stored at all, and
    /// nor is it what does the storing: making one reads nothing.
    fn in_written_order(
        &mut self,
        mut placed: Vec<BoundExpression>,
        sources: &[Option<usize>],
        in_parameters: &[bool],
        handlers: &[bool],
        wanted: &[Option<Type>],
    ) -> Vec<BoundExpression> {
        let written: Vec<usize> = sources.iter().flatten().copied().collect();
        // An attribute's arguments are constants, which do nothing and see
        // nothing: `[Mark(b: new object[] { "a" }, a: true)]` is the blob of
        // its values in parameter order, and a local would not be one.
        if written.windows(2).all(|pair| pair[0] < pair[1])
            || placed.is_empty()
            || self.in_attribute
        {
            return placed;
        }
        let mut by_source: Vec<(usize, usize)> = sources
            .iter()
            .enumerate()
            .filter_map(|(slot, source)| source.map(|source| (source, slot)))
            .collect();
        by_source.sort_unstable();
        // Whether an argument evaluated after this one awaits: a reference
        // does not live across an `await`, so an `in` argument before one
        // is handed over as the value it had, as Roslyn spills it.
        let awaits: Vec<bool> = by_source
            .iter()
            .map(|(_, slot)| contains_await(&placed[*slot]))
            .collect();
        let mut stores = Vec::new();
        for (index, (_, slot)) in by_source.into_iter().enumerate() {
            let mut argument = placed[slot].clone();
            if is_target_typed(&argument) {
                match wanted.get(slot).cloned().flatten() {
                    Some(ty) => {
                        argument = self.convert(argument, &ty);
                        placed[slot] = argument.clone();
                    }
                    // Nothing to make it as yet: it stays where it is, and is
                    // converted with the rest.
                    None => continue,
                }
            }
            let await_follows = awaits[index + 1..].iter().any(|awaits| *awaits);
            // An interpolated string given to a handler is not a string to
            // keep: the handler it is made into, perhaps with the arguments
            // before it, is made where it stands.
            if safe_to_reorder(&argument, &self.body.locals)
                || (argument.is_interpolated_string()
                    && handlers.get(slot).copied().unwrap_or(false))
            {
                continue;
            }
            let span = argument.span;
            // An `in` parameter written without `in` still takes the variable
            // where there is one — `arg2: I(5)` with `I` returning a
            // reference — and it is that reference that is kept, not a copy
            // of what it pointed at when it was evaluated. Not where an
            // `await` comes between: a reference does not survive one, and
            // Roslyn spills the value there instead.
            let argument = if in_parameters.get(slot).copied().unwrap_or(false)
                && !await_follows
                && self.is_referenceable(&argument)
            {
                let ty = argument.ty.clone();
                BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind: RefKind::In,
                        operand: Box::new(argument),
                    },
                    ty,
                    span,
                )
            } else {
                argument
            };
            match argument.kind {
                // A group is not a value to keep: what it was written on is,
                // and the group made from that is converted at the call.
                BoundExpressionKind::MethodGroup {
                    receiver: Some(receiver),
                    candidates,
                } => {
                    let ty = receiver.ty.clone();
                    let held = self.declare_synthetic_local("argument", ty.clone());
                    let read =
                        BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
                    stores.push(BoundExpression::new(
                        BoundExpressionKind::Assignment {
                            target: Box::new(read.clone()),
                            value: receiver,
                        },
                        ty,
                        span,
                    ));
                    placed[slot] = BoundExpression::new(
                        BoundExpressionKind::MethodGroup {
                            receiver: Some(Box::new(read)),
                            candidates,
                        },
                        argument.ty,
                        span,
                    );
                }
                BoundExpressionKind::RefArgument { kind, operand } => {
                    let ty = operand.ty.clone();
                    let held = self.declare_synthetic_local("argument", ty.clone());
                    if let Some(local) = self.body.locals.get_mut(held.0 as usize) {
                        local.by_ref = true;
                    }
                    let read =
                        BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
                    stores.push(BoundExpression::new(
                        BoundExpressionKind::Assignment {
                            target: Box::new(read.clone()),
                            value: Box::new(BoundExpression::new(
                                BoundExpressionKind::RefArgument {
                                    kind: RefKind::Ref,
                                    operand,
                                },
                                ty.clone(),
                                span,
                            )),
                        },
                        ty,
                        span,
                    ));
                    placed[slot] = BoundExpression::new(
                        BoundExpressionKind::RefArgument {
                            kind,
                            operand: Box::new(read),
                        },
                        argument.ty,
                        span,
                    );
                }
                kind => {
                    let ty = argument.ty.clone();
                    let held = self.declare_synthetic_local("argument", ty.clone());
                    let read =
                        BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
                    stores.push(BoundExpression::new(
                        BoundExpressionKind::Assignment {
                            target: Box::new(read.clone()),
                            value: Box::new(BoundExpression::new(kind, ty.clone(), span)),
                        },
                        ty,
                        span,
                    ));
                    placed[slot] = read;
                }
            }
        }
        if stores.is_empty() {
            return placed;
        }
        // Whatever is evaluated first does the storing, but for a lambda: a
        // lambda reads what it captures when it is called, not when it is
        // made, and wrapped up it would no longer be a lambda to convert.
        let carrier = placed
            .iter()
            .position(|argument| !matches!(argument.kind, BoundExpressionKind::UnboundLambda(_)))
            .unwrap_or(0);
        let first = placed.remove(carrier);
        let span = first.span;
        let first = match first.kind {
            BoundExpressionKind::RefArgument { kind, operand } => {
                let ty = operand.ty.clone();
                stores.push(*operand);
                BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind,
                        operand: Box::new(BoundExpression::new(
                            BoundExpressionKind::Sequence(stores),
                            ty,
                            span,
                        )),
                    },
                    first.ty,
                    span,
                )
            }
            kind => {
                let ty = first.ty.clone();
                stores.push(BoundExpression::new(kind, ty.clone(), span));
                BoundExpression::new(BoundExpressionKind::Sequence(stores), ty, span)
            }
        };
        placed.insert(carrier, first);
        placed
    }

    /// Whether these arguments, in this order, are what a candidate takes.
    ///
    /// Only asked about a reordering: several are possible when a name skips
    /// an optional parameter, and the types are what tells them apart.
    fn arguments_fit(
        &self,
        candidate: SymbolId,
        arguments: &[BoundExpression],
        receiver: &Type,
    ) -> bool {
        let types: Vec<Type> = arguments
            .iter()
            .map(|argument| argument.ty.clone())
            .collect();
        let Some(shape) = self.candidate_shape(candidate, &types, receiver, &[], &[]) else {
            return false;
        };
        // `b: in b` goes to an `in` parameter and not to a value one.
        let symbols = self.binder.compilation().symbols();
        let refs_fit = member_parameters(symbols, candidate).is_none_or(|parameters| {
            arguments
                .iter()
                .zip(parameters)
                .all(|(argument, parameter)| {
                    let written = match &argument.kind {
                        BoundExpressionKind::RefArgument { kind, .. } => *kind,
                        _ => RefKind::None,
                    };
                    let declared = symbols
                        .get(*parameter)
                        .as_parameter()
                        .map_or(RefKind::None, |detail| detail.ref_kind);
                    super::overloads::ref_fits(
                        written,
                        Some(declared),
                        self.language_version()
                            .at_least(rustlyn_syntax::LanguageVersion::CSharp12),
                    )
                })
        });
        refs_fit
            && types.len() <= shape.parameters.len()
            && types.iter().zip(&shape.parameters).enumerate().all(
                |(index, (argument, parameter))| {
                    (self.binder.converts_implicitly(argument, parameter)
                        || self.lambda_fits(&arguments[index], parameter)
                        || self.constant_fits(&arguments[index], parameter))
                        && (!matches!(
                            arguments[index].kind,
                            BoundExpressionKind::UnboundCollection(_)
                        ) || self.takes_a_collection(parameter))
                },
            )
    }

    /// Whether a collection expression can be made into a type: an array, a
    /// span, or something that is an `IEnumerable` — which is not a `string`,
    /// however much a `string` enumerates.
    pub(super) fn takes_a_collection(&self, ty: &Type) -> bool {
        match ty {
            Type::Array { rank, .. } => *rank == 1,
            Type::Named { symbol, .. } => {
                if self.binder.special_of(ty) == Some(SpecialType::String) {
                    return false;
                }
                let compilation = self.binder.compilation();
                let spans = ["System.Span`1", "System.ReadOnlySpan`1"]
                    .into_iter()
                    .filter_map(|name| compilation.type_by_metadata_name(name));
                if spans.into_iter().any(|span| span == *symbol) {
                    return true;
                }
                compilation
                    .type_by_metadata_name("System.Collections.IEnumerable")
                    .is_some_and(|enumerable| {
                        enumerable == *symbol
                            || self.binder.constructed_from(ty, enumerable).is_some()
                    })
            }
            _ => false,
        }
    }

    /// The value a parameter takes when the call site leaves it out.
    ///
    /// What was written after the `=` where the declaration is in source, and
    /// the type's own default where metadata only records that there is one.
    /// The written expression belongs to the declaration's file rather than to
    /// this one, and is bound there: `LexerMode lexerMode = LexerMode.Syntax`
    /// names a type the caller's file has never heard of, and reading it as
    /// `default` instead would quietly pass the wrong value.
    ///
    /// `wanted` is the parameter's type *as this call sees it*: `Optional<
    /// TLocalState> initialState = default` on a generic base is an
    /// `Optional<LocalState>` when called from the derived class, and a
    /// `default` spelled with the `TLocalState` would name a type parameter
    /// the caller does not have.
    pub(super) fn default_argument(
        &mut self,
        parameter: SymbolId,
        wanted: &Type,
        span: TextSpan,
        given: &[Option<TextSpan>],
    ) -> Option<BoundExpression> {
        let symbols = self.binder.compilation().symbols();
        let detail = symbols.get(parameter).as_parameter()?;
        if !detail.has_default {
            return None;
        }
        let mut sink = Diagnostics::new();
        let ty = if wanted.is_error() {
            self.binder.type_of(parameter, &mut sink)
        } else {
            wanted.clone()
        };
        // A caller-info attribute (§22.5.6) fills the argument from the call
        // site: the member it is in, its line, its file, or the text of
        // another argument.
        if let Some(info) = detail.caller_info.clone()
            && let Some(value) = self.caller_info_value(&info, parameter, span, given)
        {
            return Some(self.convert(value, &ty));
        }
        // The `Invoke` of a delegate type made for a lambda or a method group
        // carries the value itself: there is no syntax behind it to bind,
        // unless the value is no constant (a `decimal`), and then it is the
        // lambda's.
        let late_syntax = self
            .binder
            .compilation()
            .anonymous_delegate_default_syntax(parameter);
        // So does a parameter read from metadata, in its `Constant` row.
        if late_syntax.is_none()
            && let Some(value) = self
                .binder
                .compilation()
                .anonymous_delegate_default(parameter)
                .or_else(|| {
                    self.binder
                        .compilation()
                        .metadata_parameter_default(parameter)
                        .cloned()
                })
        {
            return Some(self.constant_argument(value, &ty, span));
        }
        let written = match late_syntax {
            Some(at) => self
                .binder
                .compilation()
                .trees()
                .get(at.tree)
                .and_then(|tree| tree.root().find_node(at.span))
                .map(|node| (at.tree, node)),
            // `[Optional, DefaultParameterValue(3)] int x` writes its value in
            // an attribute.
            None => self
                .binder
                .parameter_default_syntax(parameter)
                .map(|(tree, _, node)| (tree, node)),
        };
        // A parameter out of metadata has its default in a `Constant` row,
        // or — a `decimal` or a `DateTime`, which are no CLR primitives — in
        // a `[DecimalConstant]` or `[DateTimeConstant]`, which a source
        // parameter may carry too.
        let attributed = written
            .as_ref()
            .is_some_and(|(_, node)| node.kind() == SyntaxKind::Attribute);
        if written.is_none() || attributed {
            if let Some(value) = self
                .binder
                .compilation()
                .metadata_parameter_default(parameter)
                .cloned()
            {
                return Some(self.constant_argument(value, &ty, span));
            }
            let special = match &written {
                Some((tree, node)) if attributed => self.attributed_special(*tree, node),
                _ => self.binder.special_constant(parameter),
            };
            if let Some(special) = special
                && let Some(made) = self.special_constant_expression(special, span)
            {
                // The value converts to the parameter's type as a cast would
                // — `[DecimalConstant(..50)] int` is 50 — and one the
                // parameter cannot hold leaves it at its default:
                // `[DateTimeConstant] string s` is null.
                if self.binder.converts_implicitly(&made.ty, &ty) {
                    return Some(self.convert(made, &ty));
                }
                if self.converts_explicitly(&made.ty, &ty) {
                    return Some(self.convert_explicitly(made, &ty));
                }
                return Some(BoundExpression::new(
                    BoundExpressionKind::Default(ty.clone()),
                    ty,
                    span,
                ));
            }
        }
        // `[MarshalAs(UnmanagedType.Interface)] [Optional] object x` left out
        // is `null`, `[IUnknownConstant]` one an `UnknownWrapper` of it and
        // `[IDispatchConstant]` one a `DispatchWrapper` (Roslyn's
        // `GetDefaultParameterSpecialNoConversion`).
        // `dynamic` is an `object` here as everywhere in metadata.
        let object =
            matches!(ty, Type::Dynamic) || self.binder.special_of(&ty) == Some(SpecialType::Object);
        if written.is_none()
            && object
            && let Some(special) = self.com_optional_default(parameter, &ty, span)
        {
            return Some(special);
        }
        if written.is_none()
            && object
            && let Some(missing) = self.missing_value(span)
        {
            // `[Optional] object o` left out is `Missing.Value`, which is
            // what a COM caller means by leaving it out.
            return Some(self.convert(missing, &ty));
        }
        // `int Local(int j = Local())`: the default calls the function
        // whose default it is. It is not a constant (CS1736), and binding it
        // once more would never end.
        thread_local! {
            static DEFAULTING: std::cell::RefCell<Vec<SymbolId>> =
                const { std::cell::RefCell::new(Vec::new()) };
        }
        let written = written
            .filter(|_| !DEFAULTING.with_borrow(|parameters| parameters.contains(&parameter)));
        if let Some((tree, node)) = written {
            DEFAULTING.with_borrow_mut(|parameters| parameters.push(parameter));
            let bound = self.bind_default_value(parameter, tree, &node);
            DEFAULTING.with_borrow_mut(|parameters| parameters.pop());
            // `T? z = default(T?)` is written in the method's own terms; at
            // the call it is the default of what the parameter is there.
            let declared = self.binder.type_of(parameter, &mut Diagnostics::new());
            if matches!(bound.kind, BoundExpressionKind::Default(_))
                && bound.ty == declared
                && declared != ty
            {
                return Some(BoundExpression::new(
                    BoundExpressionKind::Default(ty.clone()),
                    ty,
                    bound.span,
                ));
            }
            if !bound.ty.is_error() {
                return Some(self.convert(bound, &ty));
            }
        }
        Some(BoundExpression::new(
            BoundExpressionKind::Default(ty.clone()),
            ty,
            span,
        ))
    }

    /// A constant default value as the argument it fills in: a null as the
    /// default of a value type, anything else as a literal of what the
    /// parameter (or the `Nullable<T>` it is) holds.
    fn constant_argument(
        &mut self,
        value: ConstantValue,
        ty: &Type,
        span: TextSpan,
    ) -> BoundExpression {
        let symbols = self.binder.compilation().symbols();
        let literal = match value {
            ConstantValue::Null if ty.is_reference_type(symbols) => BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Null),
                Type::Null,
                span,
            ),
            ConstantValue::Null => {
                BoundExpression::new(BoundExpressionKind::Default(ty.clone()), ty.clone(), span)
            }
            value => {
                let literal_type = self
                    .binder
                    .nullable_underlying(ty)
                    .unwrap_or_else(|| ty.clone());
                let value = self.binder.constant_as(value, &literal_type);
                BoundExpression::new(BoundExpressionKind::Literal(value), literal_type, span)
            }
        };
        self.convert(literal, ty)
    }

    /// The `decimal` or `DateTime` a `[DecimalConstant(...)]` or
    /// `[DateTimeConstant(...)]` written on a lambda's parameter gives it.
    pub(super) fn attributed_special(
        &mut self,
        tree: usize,
        attribute: &SyntaxNode,
    ) -> Option<crate::bound::SpecialConstant> {
        self.binder.attribute_special(tree, attribute, attribute)
    }

    /// A parameter's default value, bound where it was written.
    fn bind_default_value(
        &mut self,
        parameter: SymbolId,
        tree: usize,
        node: &SyntaxNode,
    ) -> BoundExpression {
        let floor = self.body.diagnostics.len();
        // Nothing of this body is in scope over there: not its locals, not
        // its file's usings, not the type it is written in.
        let context = self.binder.context_at(tree, node);
        // Nor is any lambda of this body around it: what the default
        // value names, it names in its own class, and reading a member
        // there is not this lambda capturing `this`.
        // A local function's default is written in this very body, and
        // may name one of its constants: `void F(int n = N)` under a
        // `const int N`. Its scopes stay.
        let symbols = self.binder.compilation().symbols();
        let local_function = symbols
            .get(parameter)
            .container
            .and_then(|function| symbols.get(function).as_method())
            .is_some_and(|detail| detail.method_kind == MethodKind::LocalFunction);
        let scopes = if local_function {
            self.scopes.clone()
        } else {
            Vec::new()
        };
        let outer = (
            std::mem::replace(&mut self.tree, tree),
            std::mem::replace(&mut self.context, context),
            std::mem::replace(&mut self.scopes, scopes),
            std::mem::replace(&mut self.capture_floor, self.lambdas.len()),
        );
        self.scopes.push(HashMap::new());
        let bound = self.bind_expression(node);
        (self.tree, self.context, self.scopes, self.capture_floor) = outer;
        self.body.diagnostics.truncate(floor);
        bound
    }

    /// What a COM attribute on an `[Optional] object` parameter written here
    /// says it is when left out: `null` for a `[MarshalAs]` of an interface,
    /// `IUnknown` or `IDispatch`, else the wrapper `[IUnknownConstant]` or
    /// `[IDispatchConstant]` asks for.
    fn com_optional_default(
        &mut self,
        parameter: SymbolId,
        ty: &Type,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let default = match self.binder.compilation().metadata_com_default(parameter) {
            Some(default) => default,
            None => self.written_com_default(parameter)?,
        };
        let null = BoundExpression::new(BoundExpressionKind::Default(ty.clone()), ty.clone(), span);
        let wrapper = match default {
            ComDefault::Null => return Some(null),
            ComDefault::UnknownWrapper => "System.Runtime.InteropServices.UnknownWrapper",
            ComDefault::DispatchWrapper => "System.Runtime.InteropServices.DispatchWrapper",
        };
        let wrapper = self.framework_type(wrapper)?;
        let made = self.make(&wrapper, vec![null], span)?;
        Some(self.convert(made, ty))
    }

    /// What the COM attributes written on a parameter in source make of it
    /// left out: a `[MarshalAs]` of an interface, `IUnknown` or `IDispatch`
    /// first, then `[IUnknownConstant]`, then `[IDispatchConstant]`.
    fn written_com_default(&mut self, parameter: SymbolId) -> Option<ComDefault> {
        let compilation = self.binder.compilation();
        let &(tree, at) = compilation.declaration_nodes(parameter).first()?;
        let node = compilation.trees().get(tree)?.root().find_node(at)?;
        if let Some(attribute) = crate::declare::parameter_attribute(&node, "MarshalAs")
            && let Some(bound) = self.binder.bind_attribute(tree, &node, &attribute)
            && let Some(kind) = bound.arguments.first().and_then(|value| self.binder.folded(value))
            // `UnmanagedType.IUnknown`, `IDispatch` and `Interface`.
            && matches!(kind, ConstantValue::Int32(25 | 26 | 28))
        {
            return Some(ComDefault::Null);
        }
        if crate::declare::parameter_attribute(&node, "IUnknownConstant").is_some() {
            Some(ComDefault::UnknownWrapper)
        } else if crate::declare::parameter_attribute(&node, "IDispatchConstant").is_some() {
            Some(ComDefault::DispatchWrapper)
        } else {
            None
        }
    }

    /// `System.Reflection.Missing.Value`, as an `object`.
    fn missing_value(&mut self, span: TextSpan) -> Option<BoundExpression> {
        let missing = self.framework_type("System.Reflection.Missing")?;
        let field = self
            .binder
            .lookup_member(missing.symbol()?, "Value")
            .into_iter()
            .find(|member| self.kind_of(*member) == SymbolKind::Field)?;
        let read = self.member_access(field, None, missing, span);
        let object = self.special(SpecialType::Object);
        Some(self.convert(read, &object))
    }

    /// What a caller-info attribute supplies at this call (§22.5.6).
    fn caller_info_value(
        &mut self,
        info: &CallerInfo,
        parameter: SymbolId,
        span: TextSpan,
        given: &[Option<TextSpan>],
    ) -> Option<BoundExpression> {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        let string = self.special(SpecialType::String);
        let int = self.special(SpecialType::Int32);
        // A call the compiler writes with nothing written behind it — the
        // base constructor run by a constructor that wrote no `: base(...)`
        // — takes no caller info (Roslyn's `enableCallerInfo`): the
        // parameters keep their defaults.
        if self.implicit_call {
            return None;
        }
        let (constant, ty) = match info {
            CallerInfo::MemberName => {
                // A local function is called from the member it is written
                // in, as a lambda is.
                let mut member = self.member?;
                while symbols
                    .get(member)
                    .as_method()
                    .is_some_and(|detail| detail.method_kind == MethodKind::LocalFunction)
                {
                    member = symbols.get(member).container?;
                }
                let symbol = symbols.get(member);
                // An attribute on a type is called from no member at all.
                if symbol.kind == SymbolKind::NamedType {
                    return None;
                }
                // An accessor's caller is its property or event; a
                // constructor is `.ctor`, as the runtime names it.
                let named = match symbol.container {
                    Some(container)
                        if matches!(
                            symbols.get(container).kind,
                            SymbolKind::Property | SymbolKind::Event
                        ) =>
                    {
                        container
                    }
                    _ => member,
                };
                let written = &symbols.get(named).name;
                // An indexer goes by its metadata name — `I.Item` where it
                // implements `I`'s explicitly — and any other explicit
                // implementation by its own name without the interface's:
                // `void I.Add()` is `Add` (Roslyn's `GetMemberCallerName`).
                let name = if written == "this[]" {
                    let interface = compilation
                        .declaration_node(named)
                        .and_then(|node| node.child_of_kind(SyntaxKind::ExplicitInterfaceSpecifier))
                        .map(|specifier| {
                            let text: String = specifier
                                .text()
                                .chars()
                                .filter(|ch| !ch.is_whitespace())
                                .collect();
                            text.trim_end_matches('.').to_string()
                        });
                    match interface {
                        Some(interface) => format!("{interface}.Item"),
                        None => self.binder.indexer_metadata_name(named),
                    }
                } else {
                    match written.rsplit_once('.') {
                        Some((interface, name)) if !interface.is_empty() => name.to_string(),
                        _ => written.clone(),
                    }
                };
                (ConstantValue::String(name), string)
            }
            CallerInfo::LineNumber => {
                let source = compilation.trees().get(self.tree)?.source().clone();
                let at = self.caller_position(span);
                let line = rustlyn_text::LineIndex::new(source.text()).line_of(at) + 1;
                (ConstantValue::Int32(line as i32), int)
            }
            CallerInfo::FilePath => {
                let source = compilation.trees().get(self.tree)?.source().clone();
                (ConstantValue::String(source.name().to_string()), string)
            }
            CallerInfo::ArgumentExpression(_) | CallerInfo::ArgumentConstant(_) => {
                let method = symbols.get(parameter).container?;
                let target = match info {
                    CallerInfo::ArgumentExpression(target) => target.clone(),
                    CallerInfo::ArgumentConstant(name) => {
                        // The constant is looked up from the declaring
                        // type outwards, as a name in the declaration is.
                        let mut ty = symbols.get(method).container;
                        if symbols.get(method).kind == SymbolKind::Method
                            && ty.is_some_and(|it| {
                                matches!(
                                    symbols.get(it).kind,
                                    SymbolKind::Property | SymbolKind::Event
                                )
                            })
                        {
                            ty = symbols.get(ty?).container;
                        }
                        let mut found = None;
                        while let Some(scope) = ty {
                            if symbols.get(scope).as_named_type().is_none() {
                                break;
                            }
                            if let Some(value) = self
                                .binder
                                .lookup_member(scope, name)
                                .into_iter()
                                .find_map(|member| self.binder.constant_value(member))
                            {
                                found = Some(value);
                                break;
                            }
                            ty = symbols.get(scope).container;
                        }
                        match found? {
                            ConstantValue::String(text) => text,
                            _ => return None,
                        }
                    }
                    _ => return None,
                };
                let holder = symbols.get(method);
                // An indexer's parameters are the property's; its accessors
                // carry them again, `value` last.
                let parameters = match holder.container {
                    _ if holder.kind == SymbolKind::Property => {
                        holder.as_property()?.parameters.clone()
                    }
                    Some(container) if symbols.get(container).kind == SymbolKind::Property => {
                        symbols.get(container).as_property()?.parameters.clone()
                    }
                    _ => holder.as_method()?.parameters.clone(),
                };
                let at = parameters
                    .iter()
                    .position(|candidate| symbols.get(*candidate).name == target)?;
                let at = given.get(at).copied().flatten()?;
                let source = compilation.trees().get(self.tree)?.source().clone();
                let text = source
                    .text()
                    .get(at.start() as usize..at.end() as usize)?
                    .trim()
                    .to_string();
                (ConstantValue::String(text), string)
            }
        };
        // A parameter the value cannot reach ignores the attribute (Roslyn
        // warns): `[CallerLineNumber] string s = "hello"` keeps its default.
        // A line reaches it as the constant `int.MaxValue` would, so a
        // `uint` takes one and a `short` does not.
        let mut sink = Diagnostics::new();
        let taken = self.binder.type_of(parameter, &mut sink);
        let largest_line = BoundExpression::new(
            BoundExpressionKind::Literal(ConstantValue::Int32(i32::MAX)),
            self.special(SpecialType::Int32),
            span,
        );
        let reaches = self.binder.converts_implicitly(&ty, &taken)
            || (matches!(info, CallerInfo::LineNumber)
                && self.constant_fits(&largest_line, &taken));
        if !taken.is_error() && !reaches {
            return None;
        }
        Some(BoundExpression::new(
            BoundExpressionKind::Literal(constant),
            ty,
            span,
        ))
    }

    /// Where a call is for `[CallerLineNumber]`: the `(` of its arguments,
    /// the `new` of a creation, the `[` of an element access, and the first
    /// token of anything else (Roslyn's `GetCallerLocation`) — `Log` on one
    /// line and its `(` two lines down is a call on the line of the `(`.
    fn caller_position(&self, span: TextSpan) -> u32 {
        let Some(node) = self.syntax_at(span) else {
            return span.start();
        };
        let token = match node.kind() {
            SyntaxKind::InvocationExpression
            | SyntaxKind::BaseConstructorInitializer
            | SyntaxKind::ThisConstructorInitializer
            | SyntaxKind::PrimaryConstructorBaseType => node
                .child_of_kind(SyntaxKind::ArgumentList)
                .and_then(|list| list.first_token()),
            SyntaxKind::ElementAccessExpression => node
                .child_of_kind(SyntaxKind::BracketedArgumentList)
                .and_then(|list| list.first_token()),
            SyntaxKind::ObjectCreationExpression | SyntaxKind::ImplicitObjectCreationExpression => {
                node.child_tokens()
                    .find(|token| token.kind() == SyntaxKind::NewKeyword)
            }
            _ => node.first_token(),
        };
        token.map_or(span.start(), |token| token.span().start())
    }

    pub(super) fn bind_argument_list(&mut self, list: &SyntaxNode) -> Vec<BoundExpression> {
        list.children()
            .filter(|child| child.kind() == SyntaxKind::Argument)
            .map(|argument| {
                let kind = argument_ref_kind(&argument);
                let bound = match argument
                    .children()
                    .find(|child| child.kind().is_expression())
                {
                    // `out var value` and `out int value` declare the variable
                    // here, where it is passed.
                    Some(expression) if expression.kind() == SyntaxKind::DeclarationExpression => {
                        self.bind_out_declaration(&expression)
                    }
                    // `out _` wants the value thrown away, and still needs
                    // somewhere for the callee to put it.
                    Some(expression)
                        if kind == RefKind::Out
                            && expression.kind() == SyntaxKind::IdentifierName
                            && identifier_text(&expression).as_deref() == Some("_")
                            && self.lookup_local("_").is_none() =>
                    {
                        let local = self.declare_synthetic_local("discard", Type::Error);
                        BoundExpression::new(
                            BoundExpressionKind::Local(local),
                            Type::Error,
                            expression.span(),
                        )
                    }
                    Some(expression) => self.bind_expression(&expression),
                    None => BoundExpression::error(argument.span()),
                };
                if kind == RefKind::None {
                    return bound;
                }
                // `ref x` passes `x` itself. The type stays `x`'s, because
                // that is what overload resolution compares against the
                // parameter; what changes is how the value gets there.
                let (ty, span) = (bound.ty.clone(), bound.span);
                BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind,
                        operand: Box::new(bound),
                    },
                    ty,
                    span,
                )
            })
            .collect()
    }

    pub(super) fn bind_out_declaration(&mut self, node: &SyntaxNode) -> BoundExpression {
        let type_node = node.children().find(|child| child.kind().is_type_node());
        let inferred = type_node.as_ref().is_some_and(super::declares_var);
        let ty = match &type_node {
            Some(node) if !inferred => self.resolve(node),
            // `out var` takes its type from the parameter, which needs the
            // overload to be picked first; that is not done yet.
            _ => Type::Error,
        };
        let mut local = None;
        if let Some(designation) = node.child_of_kind(SyntaxKind::SingleVariableDesignation)
            && let Some(token) = designation
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        {
            local = Some(self.declare_local(token.value_text(), ty.clone(), token.span()));
        } else if node.child_of_kind(SyntaxKind::DiscardDesignation).is_some() {
            // `out var _` and `out int _` want the value thrown away, and
            // still need somewhere for the callee to put it.
            local = Some(self.declare_synthetic_local("discard", ty.clone()));
        }
        self.body.types.insert(node.span(), ty.clone());
        let kind = local.map_or(
            BoundExpressionKind::Unsupported(node.kind()),
            BoundExpressionKind::Local,
        );
        BoundExpression::new(kind, ty, node.span())
    }

    pub(super) fn bind_add_call(
        &mut self,
        ty: &Type,
        receiver: BoundExpression,
        argument: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        self.bind_member_call(ty, "Add", receiver, vec![argument], span)
    }

    /// A call to a named member of `ty` on a receiver, with the overload
    /// picked the way any call's is.
    pub(super) fn bind_member_call(
        &mut self,
        ty: &Type,
        name: &str,
        receiver: BoundExpression,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        self.bind_member_call_with(ty, name, receiver, arguments, &[], span)
    }

    /// The same, with the type arguments the call wrote: `source.Cast<int>()`
    /// on a source whose own `Cast<E>` is the one a query's `from int x`
    /// calls.
    pub(super) fn bind_member_call_with(
        &mut self,
        ty: &Type,
        name: &str,
        receiver: BoundExpression,
        arguments: Vec<BoundExpression>,
        explicit: &[Type],
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = ty.symbol()?;
        // A static method is no member of an instance: a collection whose
        // `Add` is static is filled through an extension one.
        let instance = !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_));
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .filter(|id| {
                !instance
                    || !self
                        .binder
                        .compilation()
                        .symbols()
                        .get(*id)
                        .modifiers
                        .contains(Modifiers::STATIC)
            })
            .collect();
        if candidates.is_empty() {
            // `new C { 1 }` may reach an extension `Add` (§12.8.17.3).
            if let Some(call) = self.extension_call_with(name, receiver, arguments, span) {
                return Some(call);
            }
            let container = ty.display(self.binder.compilation().symbols());
            self.report(ErrorCode::ErrNoSuchMember, span, &[&container, name]);
            return None;
        }
        let types: Vec<Type> = arguments.iter().map(|value| value.ty.clone()).collect();
        // Where no member of the type takes the arguments, an extension may
        // (§12.8.10.3): a `Dictionary<K, V>` has an `Add` of two, and one of
        // its pairs reaches an `Add(this ICollection<T>, params T[])`.
        let Some(Resolved {
            method,
            type_arguments,
            substitution,
        }) = self.resolve_call(
            &candidates,
            &types,
            &self.evidence(&arguments),
            ty,
            explicit,
        )
        else {
            return self.extension_call_with(name, receiver, arguments, span);
        };
        let result = self.member_type(method, ty).substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, ty, &substitution, span);
        let receiver = self.capture_receiver(receiver);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(receiver)),
                method,
                type_arguments,
                arguments,
                virtual_call: self.is_virtual_call(method, None),
            },
            result,
            span,
        ))
    }

    /// `new T(...)`, with the constructor picked the way any call is.
    pub(super) fn make(
        &mut self,
        ty: &Type,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = ty.symbol()?;
        let candidates = self
            .binder
            .compilation()
            .symbols()
            .lookup(symbol, ".ctor")
            .to_vec();
        let mut arguments = arguments;
        let constructor = self
            .resolve_with_lambdas(&candidates, &mut arguments, ty, &[], false)?
            .method;
        let arguments = self.convert_arguments(constructor, arguments, ty, &HashMap::new(), span);
        Some(BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor: Some(constructor),
                arguments,
                initializers: Vec::new(),
            },
            ty.clone(),
            span,
        ))
    }

    /// `T.Name<A>(...)` on a framework type, with the type arguments written.
    pub(super) fn call_static_with(
        &mut self,
        ty: &Type,
        name: &str,
        arguments: Vec<BoundExpression>,
        explicit: &[Type],
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = ty.symbol()?;
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .collect();
        let types: Vec<Type> = arguments.iter().map(|value| value.ty.clone()).collect();
        let evidence = self.evidence(&arguments);
        let Resolved {
            method,
            type_arguments,
            substitution,
        } = self.resolve_call(&candidates, &types, &evidence, ty, explicit)?;
        let result = self.member_type(method, ty).substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, ty, &substitution, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            result,
            span,
        ))
    }

    /// `T.Name(...)` on a framework type.
    pub(super) fn call_static(
        &mut self,
        ty: &Type,
        name: &str,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = ty.symbol()?;
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .collect();
        let types: Vec<Type> = arguments.iter().map(|value| value.ty.clone()).collect();
        let evidence = self.evidence(&arguments);
        let Resolved {
            method,
            type_arguments,
            substitution,
        } = self.resolve_call(&candidates, &types, &evidence, ty, &[])?;
        let result = self.member_type(method, ty).substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, ty, &substitution, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            result,
            span,
        ))
    }

    /// `receiver.Name(...)`, where the receiver is a value already bound.
    pub(super) fn call_on(
        &mut self,
        receiver: BoundExpression,
        name: &str,
        arguments: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = receiver.ty.symbol()?;
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .collect();
        let types: Vec<Type> = arguments.iter().map(|value| value.ty.clone()).collect();
        let evidence = self.evidence(&arguments);
        let receiver_type = receiver.ty.clone();
        let Resolved {
            method,
            type_arguments,
            substitution,
        } = self.resolve_call(&candidates, &types, &evidence, &receiver_type, &[])?;
        let result = self
            .member_type(method, &receiver_type)
            .substitute(&substitution);
        let arguments =
            self.convert_arguments(method, arguments, &receiver_type, &substitution, span);
        let receiver = self.capture_receiver(receiver);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(receiver)),
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            result,
            span,
        ))
    }
}

fn argument_ref_kind(argument: &SyntaxNode) -> RefKind {
    for token in argument.child_tokens() {
        match token.kind() {
            SyntaxKind::RefKeyword => return RefKind::Ref,
            SyntaxKind::OutKeyword => return RefKind::Out,
            SyntaxKind::InKeyword => return RefKind::In,
            _ => {}
        }
    }
    RefKind::None
}

/// Whether an argument is an interpolated string, or the stores of the
/// arguments written before it that were put in their parameters' order
/// and then one: what a handler parameter makes a handler of.
fn ends_interpolated(argument: &BoundExpression) -> bool {
    match &argument.kind {
        BoundExpressionKind::Sequence(steps) => steps
            .last()
            .is_some_and(BoundExpression::is_interpolated_string),
        _ => argument.is_interpolated_string(),
    }
}

/// Whether an argument is an `out` variable still waiting for its type.
pub(super) fn is_untyped_out(argument: &BoundExpression, locals: &[LocalSymbol]) -> bool {
    if !argument.ty.is_error() {
        return false;
    }
    let local = match &argument.kind {
        BoundExpressionKind::Local(local) => *local,
        BoundExpressionKind::RefArgument { operand, .. } => match operand.kind {
            BoundExpressionKind::Local(local) => local,
            _ => return false,
        },
        _ => return false,
    };
    // Declared right there, `out var x`, or the slot an `out _` throws its
    // value into: a variable declared elsewhere whose type is not known —
    // of a call that did not resolve, of a lambda no delegate took — is not
    // given the parameter's.
    locals.get(local.0 as usize).is_some_and(|declared| {
        argument.span.contains_span(declared.span) || declared.name.starts_with("<discard>")
    })
}

/// Whether an argument has no type until the parameter it goes to gives it
/// one: a `new()`, a collection expression, a conditional or `switch` whose
/// branches agree on none.
fn is_target_typed(argument: &BoundExpression) -> bool {
    matches!(
        argument.kind,
        BoundExpressionKind::UnboundCreation(_)
            | BoundExpressionKind::UnboundCollection(_)
            | BoundExpressionKind::UnboundConditional(_)
            | BoundExpressionKind::UnboundSwitch(_)
    )
}

/// Whether an argument neither does nor sees anything that moving it past
/// another could change: a constant, a lambda, a variable passed by
/// reference that no later argument can point elsewhere.
fn safe_to_reorder(argument: &BoundExpression, locals: &[LocalSymbol]) -> bool {
    match &argument.kind {
        BoundExpressionKind::Literal(_)
        | BoundExpressionKind::Default(_)
        | BoundExpressionKind::Lambda(_)
        | BoundExpressionKind::UnboundLambda(_)
        | BoundExpressionKind::TypeOf(_)
        | BoundExpressionKind::SizeOf(_) => true,
        BoundExpressionKind::Conversion { operand, .. } => safe_to_reorder(operand, locals),
        // `onEnter: Enter` written after a later parameter: the group is not
        // a value until overload resolution has picked the delegate it
        // becomes, so it cannot be kept in a local ahead of the call; made
        // from a receiver that is only read, it does nothing to keep.
        BoundExpressionKind::MethodGroup { receiver, .. } => {
            receiver.as_deref().is_none_or(|receiver| {
                matches!(
                    receiver.kind,
                    BoundExpressionKind::This
                        | BoundExpressionKind::Base
                        | BoundExpressionKind::TypeExpression(_)
                        | BoundExpressionKind::Parameter(_)
                        | BoundExpressionKind::Local(_)
                )
            })
        }
        BoundExpressionKind::RefArgument { operand, .. } => match &operand.kind {
            BoundExpressionKind::Local(local) => {
                !locals.get(local.0 as usize).is_some_and(|slot| slot.by_ref)
            }
            _ => false,
        },
        _ => false,
    }
}

/// Whether an argument's span is text the call wrote, rather than a default
/// filled in for it, which carries the call's own span or its declaration's.
fn written_at_call(argument: TextSpan, call: TextSpan) -> bool {
    argument != call && call.start() <= argument.start() && argument.end() <= call.end()
}

/// Whether an `await` sits anywhere in an expression; a lambda is a body of
/// its own and does not count.
pub(super) fn contains_await(expression: &BoundExpression) -> bool {
    if matches!(expression.kind, BoundExpressionKind::Await { .. }) {
        return true;
    }
    let mut found = false;
    crate::definite::each_child_of(expression, &mut |child| {
        found = found || contains_await(child);
    });
    found
}

/// The name `nameof` gives what it is handed: the simple name at the right
/// of a dotted one, without the type arguments written on it.
fn nameof_name(node: &SyntaxNode) -> Option<String> {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| token.value_text().to_string()),
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName => nameof_name(&node.children().last()?),
        _ => None,
    }
}
