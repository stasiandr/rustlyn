//! Making objects: `new`, anonymous objects, arrays, collection expressions
//! and object and collection initializers.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::inference::InferenceArgument;
use super::{BodyBinder, ElementKind, Resolved, identifier_text, member_parameters};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundStatement, BoundStatementKind, BoundSymbol,
    ConstantValue, DynamicOperation,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// Notes the natural types of a collection expression's elements, where
    /// every element is plain enough to have one on its own: a literal, a
    /// name, a member, a cast. An element that needs a target — a lambda, a
    /// nested collection, a conditional — leaves nothing noted, and the
    /// expression is a candidate for any collection.
    pub(super) fn note_collection_elements(&mut self, node: &SyntaxNode) {
        if let Some((types, hints, constants, kinds)) = self.collection_evidence(node) {
            self.collection_types.insert(node.span(), types);
            self.collection_kinds.insert(node.span(), kinds);
            self.collection_constants.insert(node.span(), constants);
            self.collection_hints.insert(node.span(), hints);
        }
    }

    /// The types a collection expression's elements give on their own
    /// (§12.6.3.7): `None` where one of them cannot be looked at without a
    /// target. An element with no type of its own — `null`, `default` —
    /// gives nothing and stands in the way of nothing.
    ///
    /// The second list is what inference reads, which is more: a nested
    /// collection is inferred from element by element in turn, though it
    /// has no type to check applicability with.
    fn collection_evidence(&mut self, node: &SyntaxNode) -> Option<CollectionEvidence> {
        let mut types = Vec::new();
        let mut hints = Vec::new();
        // What each element folds to, for the ones that are constants: `[0,
        // 1]` reaches a `byte[]` though an `int` does not.
        let mut constants = Vec::new();
        let mut kinds = Vec::new();
        for element in node.children().filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::ExpressionElement | SyntaxKind::SpreadElement
            )
        }) {
            let expression = element
                .children()
                .find(|child| child.kind().is_expression())?;
            let evidence = self.element_evidence(&expression)?;
            // A spread gives what walking it gives (§12.8.24).
            if element.kind() == SyntaxKind::SpreadElement {
                let Evidenced::Typed(spread, ..) = evidence else {
                    return None;
                };
                match self.collection_element(&spread) {
                    Some(element) if !element.is_error() => {
                        types.push(element.clone());
                        constants.push(None);
                        kinds.push(ElementKind::Spread);
                        hints.push(InferenceArgument::Typed(element));
                    }
                    _ => return None,
                }
                continue;
            }
            match evidence {
                Evidenced::Typed(ty, constant, kind) => {
                    types.push(ty.clone());
                    constants.push(constant);
                    kinds.push(kind);
                    hints.push(if matches!(ty, Type::Null) {
                        InferenceArgument::Untyped
                    } else {
                        InferenceArgument::Typed(ty)
                    });
                }
                Evidenced::Nested(inner) => hints.push(InferenceArgument::Collection(inner)),
                Evidenced::Nothing => {}
            }
        }
        Some((types, hints, constants, kinds))
    }

    /// What one element says about the element type, if it can be asked
    /// without a target: `None` for one that cannot be asked.
    fn element_evidence(&mut self, expression: &SyntaxNode) -> Option<Evidenced> {
        match expression.kind() {
            SyntaxKind::DefaultLiteralExpression => return Some(Evidenced::Nothing),
            SyntaxKind::CollectionExpression => {
                let (_, inner, _, _) = self.collection_evidence(expression)?;
                return Some(Evidenced::Nested(inner));
            }
            SyntaxKind::TupleExpression => {
                let plain = expression.children().all(|argument| {
                    argument
                        .children()
                        .find(|child| child.kind().is_expression())
                        .is_some_and(|value| {
                            is_plain_element(&value) || value.kind() == SyntaxKind::TupleExpression
                        })
                });
                if !plain {
                    return None;
                }
            }
            _ if !is_plain_element(expression) => return None,
            _ => {}
        }
        // Bound again once the target is known, so nothing said here is
        // kept: not a diagnostic, and not a type it had no way to have.
        let floor = self.body.diagnostics.len();
        let bound = self.bind_expression(expression);
        self.body.diagnostics.truncate(floor);
        if bound.ty.is_error() {
            return None;
        }
        let constant = self.binder.folded(&bound);
        let kind = if constant.is_none() && bound.is_interpolated_string() {
            ElementKind::Interpolated
        } else {
            ElementKind::Plain
        };
        Some(Evidenced::Typed(bound.ty, constant, kind))
    }

    /// What `{ X = 1, Y = 2 }` or `{ 1, 2 }` does to the object just made.
    ///
    /// The names on the left are members of the created type and of nothing
    /// else: `X` here is `X` of the new object, whatever `X` means outside.
    /// The elements of a collection initializer are arguments to its `Add`,
    /// which is why a type needs one to be initialized that way.
    pub(super) fn bind_initializers(
        &mut self,
        list: &SyntaxNode,
        ty: &Type,
    ) -> Vec<BoundExpression> {
        self.bind_initializers_on(list, ty, None)
    }

    /// The same, applied to `receiver` where one is given rather than to the
    /// object being made: `Items = { a, b }` inside an object initializer
    /// adds to what `Items` already holds (§12.8.17.3), and `Point = { X = 1
    /// }` writes into it.
    /// An index of `[index] = { a, b }`, which reads the element once per
    /// thing it initializes and the index once in all: kept in a local of
    /// its own first, where it could do or see something.
    fn hold_index(
        &mut self,
        index: BoundExpression,
        bound: &mut Vec<BoundExpression>,
    ) -> BoundExpression {
        if matches!(
            index.kind,
            BoundExpressionKind::Literal(_)
                | BoundExpressionKind::Default(_)
                | BoundExpressionKind::Local(_)
                | BoundExpressionKind::Parameter(_)
                | BoundExpressionKind::RefArgument { .. }
        ) || index.ty.is_error()
        {
            return index;
        }
        let (ty, at) = (index.ty.clone(), index.span);
        let held = self.declare_synthetic_local("index", ty.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), at);
        bound.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(index),
            },
            ty,
            at,
        ));
        read
    }

    fn bind_initializers_on(
        &mut self,
        list: &SyntaxNode,
        ty: &Type,
        receiver: Option<&BoundExpression>,
    ) -> Vec<BoundExpression> {
        let placeholder = |span| match receiver {
            Some(receiver) => BoundExpression::new(receiver.kind.clone(), ty.clone(), span),
            None => BoundExpression::new(BoundExpressionKind::CreatedObject, ty.clone(), span),
        };
        let mut bound = Vec::new();
        for element in list.children() {
            let span = element.span();
            if list.kind() == SyntaxKind::CollectionInitializerExpression {
                // `{ { "a", 1 } }` passes both values to one `Add`
                // (§12.8.17.4); a plain element is a one-argument call.
                let arguments: Vec<BoundExpression> =
                    if element.kind() == SyntaxKind::ComplexElementInitializerExpression {
                        element
                            .children()
                            .filter(|child| child.kind().is_expression())
                            .map(|child| self.bind_expression(&child))
                            .collect()
                    } else {
                        vec![self.bind_expression(&element)]
                    };
                // An element of a `dynamic` value is added to by the runtime
                // binder.
                if matches!(ty, Type::Dynamic) {
                    let names = vec![None; arguments.len()];
                    bound.push(Self::dynamic_operation(
                        DynamicOperation::InvokeMember {
                            name: "Add".to_string(),
                            type_arguments: Vec::new(),
                            simple_name: false,
                        },
                        Some(placeholder(span)),
                        arguments,
                        names,
                        Type::Dynamic,
                        span,
                    ));
                    continue;
                }
                // An `Add` the type does not have may be an extension in
                // scope, `ref this` ones on a struct included.
                if let Some(call) =
                    self.bind_member_call(ty, "Add", placeholder(span), arguments, span)
                {
                    bound.push(call);
                }
                continue;
            }
            // `X = value`, where `X` is a member rather than a name in scope.
            let mut parts = element.children();
            let (Some(name_node), Some(value_node)) = (parts.next(), parts.next()) else {
                self.bind_expression(&element);
                continue;
            };
            // `["a"] = 1` writes through the indexer of what is being made
            // (§12.8.17.3).
            if name_node.kind() == SyntaxKind::ImplicitElementAccess {
                let list = name_node.child_of_kind(SyntaxKind::BracketedArgumentList);
                let indices = list
                    .as_ref()
                    .map(|list| self.bind_argument_list(list))
                    .unwrap_or_default();
                // `[y: a, x: b]` names the indexer's parameters, as a call may.
                let names = list.as_ref().map(Self::argument_names).unwrap_or_default();
                // `[Index] = { a, b }` reads the element once per thing it
                // initializes, and `Index` once in all: each index that could
                // do or see something is kept in a local of its own first.
                let nested = matches!(
                    value_node.kind(),
                    SyntaxKind::CollectionInitializerExpression
                        | SyntaxKind::ObjectInitializerExpression
                );
                // An interpolated string is kept once it is what the
                // indexer takes: a handler, made once for all of them. Only
                // that is kept after the conversion — a `params` array is
                // made anew for each read, around the elements kept before.
                let handed = nested && indices.iter().any(BoundExpression::is_interpolated_string);
                let indices = if nested {
                    indices
                        .into_iter()
                        .map(|index| {
                            if index.is_interpolated_string() {
                                index
                            } else {
                                self.hold_index(index, &mut bound)
                            }
                        })
                        .collect()
                } else {
                    indices
                };
                let target = self.element_access_named(
                    placeholder(name_node.span()),
                    indices,
                    names,
                    name_node.kind(),
                    name_node.span(),
                );
                let target = match target.kind {
                    BoundExpressionKind::IndexerAccess {
                        receiver,
                        indexer,
                        arguments,
                    } if handed => {
                        let arguments = arguments
                            .into_iter()
                            .map(|argument| {
                                if matches!(argument.kind, BoundExpressionKind::Sequence(_)) {
                                    self.hold_index(argument, &mut bound)
                                } else {
                                    argument
                                }
                            })
                            .collect();
                        BoundExpression::new(
                            BoundExpressionKind::IndexerAccess {
                                receiver,
                                indexer,
                                arguments,
                            },
                            target.ty,
                            target.span,
                        )
                    }
                    kind => BoundExpression::new(kind, target.ty, target.span),
                };
                // `[i] = { ... }` initializes what the indexer gives back
                // rather than assigning it.
                if matches!(
                    value_node.kind(),
                    SyntaxKind::CollectionInitializerExpression
                        | SyntaxKind::ObjectInitializerExpression
                ) {
                    let element_type = target.ty.clone();
                    bound.extend(self.bind_initializers_on(
                        &value_node,
                        &element_type,
                        Some(&target),
                    ));
                    continue;
                }
                let value = self.bind_expression(&value_node);
                let value = self.convert(value, &target.ty.clone());
                bound.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(target),
                        value: Box::new(value),
                    },
                    ty.clone(),
                    span,
                ));
                continue;
            }
            let Some(name) = identifier_text(&name_node) else {
                self.bind_expression(&element);
                continue;
            };
            // A member of a `dynamic` value is written, or initialized, by the
            // runtime binder.
            if matches!(ty, Type::Dynamic) {
                let member = Self::dynamic_member(placeholder(span), &name, span);
                if matches!(
                    value_node.kind(),
                    SyntaxKind::CollectionInitializerExpression
                        | SyntaxKind::ObjectInitializerExpression
                ) {
                    bound.extend(self.bind_initializers_on(
                        &value_node,
                        &Type::Dynamic,
                        Some(&member),
                    ));
                    continue;
                }
                let value = self.bind_expression(&value_node);
                let value = self.convert(value, &Type::Dynamic);
                bound.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(member),
                        value: Box::new(value),
                    },
                    Type::Dynamic,
                    span,
                ));
                continue;
            }
            // `Items = { a, b }` and `Point = { X = 1 }`: the initializer is
            // applied to the member, which is read, not assigned.
            if matches!(
                value_node.kind(),
                SyntaxKind::CollectionInitializerExpression
                    | SyntaxKind::ObjectInitializerExpression
            ) {
                let (holder, member_name) = match ty {
                    Type::Tuple(elements) => {
                        let at = elements
                            .iter()
                            .position(|element| element.name.as_deref() == Some(name.as_str()));
                        (
                            self.tuple_as_named(elements),
                            at.map_or_else(|| name.clone(), |at| format!("Item{}", at + 1)),
                        )
                    }
                    other => (other.clone(), name.clone()),
                };
                let found = holder.symbol().and_then(|symbol| {
                    self.binder
                        .lookup_member(symbol, &member_name)
                        .into_iter()
                        .find(|candidate| {
                            matches!(
                                self.kind_of(*candidate),
                                SymbolKind::Field | SymbolKind::Property
                            ) || (self.kind_of(*candidate) == SymbolKind::Event
                                && self.event_is_a_field_here(*candidate))
                        })
                });
                // `P = { F = 1 }` initializes what a property an extension
                // block (C# 14) gave the type holds, where it has no member
                // of that name.
                let extension = if found.is_none() {
                    self.extension_member_access(&placeholder(span), &name, span)
                        .filter(|(target, _)| {
                            matches!(target.kind, BoundExpressionKind::Property { .. })
                        })
                } else {
                    None
                };
                let Some(member) = found.or(extension.as_ref().map(|(_, property)| *property))
                else {
                    let container = holder.display(self.binder.compilation().symbols());
                    self.report(
                        ErrorCode::ErrNoSuchMember,
                        name_node.span(),
                        &[&container, &name],
                    );
                    continue;
                };
                self.body
                    .references
                    .insert(name_node.span(), BoundSymbol::Declared(member));
                self.body.symbols.insert(name_node.span(), member);
                let (read, member_type) = match extension {
                    Some((target, _)) => {
                        let ty = target.ty.clone();
                        (target, ty)
                    }
                    None => {
                        let member_type = self.member_type(member, &holder);
                        let created = placeholder(span);
                        let read = self.member_access(
                            member,
                            Some(Box::new(created)),
                            member_type.clone(),
                            span,
                        );
                        (read, member_type)
                    }
                };
                bound.extend(self.bind_initializers_on(&value_node, &member_type, Some(&read)));
                continue;
            }
            let value = self.bind_expression(&value_node);
            // `t with { Item8 = 43 }` on a long tuple writes `t.Rest.Item1`,
            // where the eighth element and on live.
            if matches!(ty, Type::Tuple(_))
                && name
                    .strip_prefix("Item")
                    .and_then(|number| number.parse::<usize>().ok())
                    .is_some_and(|number| number > 7)
            {
                let target = self.member_on(placeholder(span), &name_node, &name, span);
                if !target.ty.is_error() {
                    let target_type = target.ty.clone();
                    self.check_assignable(&value_node, &value, &target_type);
                    let value = self.convert(value, &target_type);
                    bound.push(BoundExpression::new(
                        BoundExpressionKind::Assignment {
                            target: Box::new(target),
                            value: Box::new(value),
                        },
                        ty.clone(),
                        span,
                    ));
                }
                continue;
            }
            // `using LockTypeInfo = (MethodSymbol EnterScopeMethod, ...)` and
            // then `new LockTypeInfo { EnterScopeMethod = m }`: a tuple's
            // members are its `ValueTuple`'s, and an element name is another
            // way of saying which field.
            let (ty, name) = match ty {
                Type::Tuple(elements) => {
                    let at = elements
                        .iter()
                        .position(|element| element.name.as_deref() == Some(name.as_str()));
                    (
                        self.tuple_as_named(elements),
                        at.map_or(name, |at| format!("Item{}", at + 1)),
                    )
                }
                other => (other.clone(), name),
            };
            let ty = &ty;
            let found = ty
                .symbol()
                .and_then(|symbol| self.binder.lookup_member(symbol, &name).first().copied());
            // `new S { Prop = v }` sets an extension block's property (C#
            // 14) where the type has no member of that name.
            if found.is_none()
                && let Some((target, property)) =
                    self.extension_member_access(&placeholder(span), &name, span)
                && matches!(target.kind, BoundExpressionKind::Property { .. })
            {
                self.body
                    .references
                    .insert(name_node.span(), BoundSymbol::Declared(property));
                self.body.symbols.insert(name_node.span(), property);
                let value = self.convert(value, &target.ty.clone());
                bound.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(target),
                        value: Box::new(value),
                    },
                    ty.clone(),
                    span,
                ));
                continue;
            }
            let Some(member) = found else {
                let container = ty.display(self.binder.compilation().symbols());
                self.report(
                    ErrorCode::ErrNoSuchMember,
                    name_node.span(),
                    &[&container, &name],
                );
                continue;
            };
            // The name is what the member access `x.Field` would have
            // written, and is recorded as one: the symbol it settled on too.
            self.body
                .references
                .insert(name_node.span(), BoundSymbol::Declared(member));
            self.body.symbols.insert(name_node.span(), member);
            let member_type = self.member_type(member, ty);
            self.check_assignable(&value_node, &value, &member_type);
            let value = self.convert(value, &member_type);
            // The object being made, as the type the member was found on: a
            // tuple's field belongs to its `ValueTuple<...>`, and the
            // backend names the field through the receiver's type — a long
            // tuple's through the nested `ValueTuple<..., ValueTuple<...>>`.
            let created = BoundExpression::new(placeholder(span).kind, ty.clone(), span);
            let target = self.member_access(member, Some(Box::new(created)), member_type, span);
            bound.push(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(target),
                    value: Box::new(value),
                },
                ty.clone(),
                span,
            ));
        }
        bound
    }

    /// `collection.Add(element)`, for one element of a collection initializer.
    /// `[a, b, ..rest]`, now that something has said what it is.
    ///
    /// An array is filled element by element. Anything else is made and then
    /// told to `Add` each one, which is what a collection initializer does and
    /// what the language says a collection expression means where the type has
    /// no builder of its own.
    /// A constructor of `target` taking one argument an array of the
    /// elements converts to: `HashSet<T>(IEnumerable<T>)`.
    pub(super) fn enumerable_constructor(&self, target: &Type, array: &Type) -> Option<SymbolId> {
        let symbol = target.symbol()?;
        let symbols = self.binder.compilation().symbols();
        symbols
            .lookup(symbol, ".ctor")
            .iter()
            .copied()
            .find(|candidate| {
                symbols.get(*candidate).as_method().is_some_and(|detail| {
                    detail.parameters.len() == 1
                        && !symbols
                            .get(detail.parameters[0])
                            .as_parameter()
                            .is_some_and(|parameter| parameter.is_params)
                        && {
                            let wanted = self.member_type(detail.parameters[0], target);
                            self.binder.converts_implicitly(array, &wanted)
                        }
                })
            })
    }

    pub(super) fn bind_collection(&mut self, node: &SyntaxNode, target: &Type) -> BoundExpression {
        let span = node.span();
        if let Some(list) = self.mutable_interface_list(target) {
            let made = self.bind_collection(node, &list);
            return self.convert(made, target);
        }
        // `S? s = [1, 2]` makes the `S` and wraps it.
        if let Some(inner) = self.binder.nullable_underlying(target) {
            let made = self.bind_collection(node, &inner);
            return self.convert(made, target);
        }
        let spread = node
            .children()
            .any(|child| child.kind() == SyntaxKind::SpreadElement);
        // Each element is wrapped: `[a, ..rest]` is an `ExpressionElement`
        // and a `SpreadElement`, and what either holds is one expression.
        let written: Vec<SyntaxNode> = node
            .children()
            .filter_map(|child| child.children().find(|inner| inner.kind().is_expression()))
            .collect();
        // `..rest` has to be walked at run time, and how many elements it
        // adds is not known until then — so the elements go into a list,
        // which grows, and the array is what the list turns out to hold.
        if spread {
            // A type made with `new()` and filled with `Add` walks each
            // spread in place (§12.8.24): unless an array is accepted, or
            // the type names a builder, that is how it is made.
            let array_accepted = self.collection_element(target).is_some_and(|element| {
                let array = Type::Array {
                    element: Box::new(element),
                    rank: 1,
                };
                self.binder.converts_implicitly(&array, target)
            });
            if !array_accepted
                && !self.has_collection_builder(target)
                && self.is_collection_initializer_type(target)
                && let Some(construction) = self.collection_construction(node, target)
            {
                // A `List<T>` is the one this does by its own rules: its
                // elements go in converted, and a length every spread knows
                // sizes it (see `bind_collection_through_add`).
                let list_element = (Self::collection_arguments(node).is_none()
                    && self.capacity_constructor(target).is_some())
                .then(|| self.collection_element(target))
                .flatten();
                return self
                    .bind_collection_through_add(node, target, construction, list_element.as_ref())
                    .unwrap_or_else(|| {
                        BoundExpression::new(
                            BoundExpressionKind::Unsupported(node.kind()),
                            target.clone(),
                            span,
                        )
                    });
            }
            let leading = if self.has_collection_builder(target) {
                self.builder_arguments(node)
            } else {
                Vec::new()
            };
            if let Some(element) = self.collection_element(target)
                && let Some(array) = self.spread_into_array(node, &element, span)
            {
                if self.binder.converts_implicitly(&array.ty, target) {
                    return self.convert(array, target);
                }
                // `HashSet<Type> h = [..xs, t]`: a collection with no
                // builder is made from the array through a constructor that
                // takes an `IEnumerable<T>`, which every collection of the
                // core library has (§12.8.24).
                let through_constructor = self.enumerable_constructor(target, &array.ty);
                if let Some(built) =
                    self.bind_through_builder(target, &element, leading, array.clone(), span)
                {
                    return built;
                }
                if let Some(constructor) = through_constructor {
                    let argument = self.convert_arguments(
                        constructor,
                        vec![array],
                        target,
                        &HashMap::new(),
                        span,
                    );
                    return BoundExpression::new(
                        BoundExpressionKind::ObjectCreation {
                            constructor: Some(constructor),
                            arguments: argument,
                            initializers: Vec::new(),
                        },
                        target.clone(),
                        span,
                    );
                }
            } else {
                for value in &written {
                    self.bind_expression(value);
                }
            }
            return BoundExpression::new(
                BoundExpressionKind::Unsupported(node.kind()),
                target.clone(),
                span,
            );
        }

        // An array is the shape a collection expression takes most naturally,
        // and more than an array type wants one: `ReadOnlySpan<T>` and
        // `Span<T>` each have an implicit operator from `T[]`, and every one
        // of `IEnumerable<T>`, `IReadOnlyList<T>`, `IList<T>` and their kin is
        // an interface arrays implement. So the question is not whether the
        // target *is* an array but whether an array of its element type would
        // be accepted, which the conversion rules already answer.
        let as_array = match target {
            Type::Array { element, rank: 1 } => Some((**element).clone()),
            Type::Named { type_arguments, .. } if type_arguments.len() == 1 => {
                let element = type_arguments[0].clone();
                let array = Type::Array {
                    element: Box::new(element.clone()),
                    rank: 1,
                };
                self.binder
                    .converts_implicitly(&array, target)
                    .then_some(element)
            }
            _ => None,
        };
        if let Some(element) = as_array {
            let elements: Vec<BoundExpression> = written
                .iter()
                .map(|value| {
                    let bound = self.bind_expression(value);
                    self.convert(bound, &element)
                })
                .collect();
            let array = BoundExpression::new(
                BoundExpressionKind::ArrayCreation {
                    element: element.clone(),
                    lengths: Vec::new(),
                    elements,
                },
                Type::Array {
                    element: Box::new(element),
                    rank: 1,
                },
                span,
            );
            return self.convert(array, target);
        }

        // A type may say how a collection expression becomes one of it:
        // `ImmutableArray<T>` carries `[CollectionBuilder(typeof(ImmutableArray),
        // "Create")]`, and nothing else in its metadata says that
        // `ImmutableArray.Create` is the way in.
        if let Some(element) = self.collection_element(target)
            && self.has_collection_builder(target)
        {
            let leading = self.builder_arguments(node);
            let elements: Vec<BoundExpression> = written
                .iter()
                .map(|value| {
                    let bound = self.bind_expression(value);
                    self.convert(bound, &element)
                })
                .collect();
            let array = BoundExpression::new(
                BoundExpressionKind::ArrayCreation {
                    element: element.clone(),
                    lengths: Vec::new(),
                    elements,
                },
                Type::Array {
                    element: Box::new(element.clone()),
                    rank: 1,
                },
                span,
            );
            if let Some(built) = self.bind_through_builder(target, &element, leading, array, span) {
                return built;
            }
        }

        // Everything else is made and filled: the constructor first, then one
        // `Add` per element, against the object being created. That only works
        // for a type you can write `new` for — `ReadOnlySpan<byte>` and
        // `IEnumerable<T>` are collection types a collection expression may
        // name, and neither is built that way. The elements still bind, so
        // what is written about them is still checked; the shape of the thing
        // they go into is what this does not know.
        let construction = if Self::collection_arguments(node).is_some() {
            self.collection_construction(node, target)
        } else {
            target.symbol().and_then(|symbol| {
                self.binder
                    .compilation()
                    .symbols()
                    .lookup(symbol, ".ctor")
                    .iter()
                    .copied()
                    .find(|id| {
                        self.binder
                            .compilation()
                            .symbols()
                            .get(*id)
                            .as_method()
                            .is_some_and(|detail| detail.parameters.is_empty())
                    })
                    .map(|constructor| (constructor, Vec::new()))
            })
        };
        let Some((constructor, arguments)) = construction else {
            for value in &written {
                self.bind_expression(value);
            }
            return BoundExpression::new(
                BoundExpressionKind::Unsupported(node.kind()),
                target.clone(),
                span,
            );
        };
        // A `List<T>` is made as big as the elements it is given.
        let (constructor, arguments) = match self.capacity_constructor(target) {
            Some(with_capacity)
                if Self::collection_arguments(node).is_none() && !written.is_empty() =>
            {
                let count = BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Int32(written.len() as i32)),
                    self.special(SpecialType::Int32),
                    span,
                );
                (with_capacity, vec![count])
            }
            _ => (constructor, arguments),
        };
        let mut initializers = Vec::new();
        for value in &written {
            let bound = self.bind_expression(value);
            let created =
                BoundExpression::new(BoundExpressionKind::CreatedObject, target.clone(), span);
            if let Some(call) = self.bind_add_call(target, created, bound, span)
                && !self.is_conditioned_out(&call)
            {
                initializers.push(call);
            }
        }
        BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor: Some(constructor),
                arguments,
                initializers,
            },
            target.clone(),
            span,
        )
    }

    /// Whether a type names who builds it: `[CollectionBuilder(...)]` in
    /// metadata or in source.
    fn has_collection_builder(&self, target: &Type) -> bool {
        target.symbol().is_some_and(|symbol| {
            self.binder
                .compilation()
                .collection_builder(symbol)
                .is_some()
                || self.source_collection_builder(symbol).is_some()
        })
    }

    /// Whether a type is one a collection initializer can fill (§12.8.17.3):
    /// a class or a struct that is enumerable.
    fn is_collection_initializer_type(&self, target: &Type) -> bool {
        let Some(symbol) = target.symbol() else {
            return false;
        };
        let symbols = self.binder.compilation().symbols();
        if matches!(
            symbols
                .get(symbol)
                .as_named_type()
                .map(|detail| detail.type_kind),
            Some(Some(TypeKind::Interface)) | None
        ) {
            return false;
        }
        self.binder
            .compilation()
            .type_by_metadata_name("System.Collections.IEnumerable")
            .is_some_and(|enumerable| {
                self.binder
                    .converts_implicitly(target, &Type::named(enumerable))
            })
    }

    /// The constructor that makes an empty one of a type a collection
    /// initializer can fill: one that takes nothing.
    fn collection_initializer_constructor(&self, target: &Type) -> Option<SymbolId> {
        if !self.is_collection_initializer_type(target) {
            return None;
        }
        let symbol = target.symbol()?;
        let symbols = self.binder.compilation().symbols();
        symbols.lookup(symbol, ".ctor").iter().copied().find(|id| {
            symbols
                .get(*id)
                .as_method()
                .is_some_and(|detail| detail.parameters.is_empty())
        })
    }

    /// The arguments of a `with(...)` a builder is called with, ahead of
    /// the elements: bound where they stand, before any element is.
    fn builder_arguments(&mut self, node: &SyntaxNode) -> Vec<BoundExpression> {
        Self::collection_arguments(node)
            .map(|list| self.bind_argument_list(&list))
            .unwrap_or_default()
    }

    /// `with(...)` among a collection expression's elements (C# 15): the
    /// argument list the collection is made with.
    fn collection_arguments(node: &SyntaxNode) -> Option<SyntaxNode> {
        node.children()
            .find(|child| child.kind() == SyntaxKind::WithElement)
            .and_then(|element| element.child_of_kind(SyntaxKind::ArgumentList))
    }

    /// The constructor a collection expression makes its collection with,
    /// and what it passes: the arguments of its `with(...)`, bound as any
    /// constructor call's are, or nothing.
    fn collection_construction(
        &mut self,
        node: &SyntaxNode,
        target: &Type,
    ) -> Option<(SymbolId, Vec<BoundExpression>)> {
        let Some(list) = Self::collection_arguments(node) else {
            return Some((self.collection_initializer_constructor(target)?, Vec::new()));
        };
        if !self.is_collection_initializer_type(target) {
            return None;
        }
        let symbol = target.symbol()?;
        let arguments = self.bind_argument_list(&list);
        let candidates = self
            .binder
            .compilation()
            .symbols()
            .lookup(symbol, ".ctor")
            .to_vec();
        let names = Self::argument_names(&list);
        let candidates = self.named_candidates(&candidates, &names);
        let mut arguments = self.reorder_named(&candidates, &names, arguments, target);
        let constructor = self
            .resolve_with_lambdas(&candidates, &mut arguments, target, &[], false)?
            .method;
        let arguments =
            self.convert_arguments(constructor, arguments, target, &HashMap::new(), list.span());
        Some((constructor, arguments))
    }

    /// `IList<T>` or `ICollection<T>`, which a collection expression makes
    /// as a `List<T>` (§12.8.24): the array the read-only interfaces take
    /// could not be added to.
    fn mutable_interface_list(&self, target: &Type) -> Option<Type> {
        let Type::Named {
            symbol,
            type_arguments,
        } = target
        else {
            return None;
        };
        let compilation = self.binder.compilation();
        let mutable = [
            "System.Collections.Generic.IList`1",
            "System.Collections.Generic.ICollection`1",
        ]
        .iter()
        .any(|name| compilation.type_by_metadata_name(name) == Some(*symbol));
        if !mutable || type_arguments.len() != 1 {
            return None;
        }
        let list = compilation.type_by_metadata_name("System.Collections.Generic.List`1")?;
        Some(Type::Named {
            symbol: list,
            type_arguments: type_arguments.clone(),
        })
    }

    /// `[a, ..rest]` as the collection initializer means it, with the
    /// spreads walked where they stand:
    ///
    /// ```text
    /// made = new T(); made.Add(a); foreach (var x in rest) made.Add(x); made
    /// ```
    ///
    /// A walk is statements, so each spread is a
    /// [`SpillSequence`](BoundExpressionKind::SpillSequence) among the
    /// steps; the collection is a local all of them name, rather than the
    /// object being created, since the walk runs as statements of its own.
    fn bind_collection_through_add(
        &mut self,
        node: &SyntaxNode,
        target: &Type,
        (constructor, arguments): (SymbolId, Vec<BoundExpression>),
        element: Option<&Type>,
    ) -> Option<BoundExpression> {
        let span = node.span();
        let made = self.declare_synthetic_local("collection", target.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(made), target.clone(), span);
        // Every element is bound before any is walked, in the order written.
        let mut parts: Vec<(SyntaxNode, bool, BoundExpression)> = Vec::new();
        for child in node.children() {
            let Some(value) = child.children().find(|inner| inner.kind().is_expression()) else {
                continue;
            };
            let bound = self.bind_expression(&value);
            let spread = child.kind() == SyntaxKind::SpreadElement;
            parts.push((child, spread, bound));
        }
        // `[..xs]` is the list `new List<T>(xs)` makes (Roslyn calls
        // `ToList`) where `xs` reaches `IEnumerable<T>` by reference, which
        // copies a collection that knows its size at once.
        if self.capacity_constructor(target).is_some()
            && let Some(element) = element
            && let [(_, true, value)] = &parts[..]
            && let Some(enumerable) = self
                .binder
                .compilation()
                .type_by_metadata_name("System.Collections.Generic.IEnumerable`1")
        {
            let wanted = Type::Named {
                symbol: enumerable,
                type_arguments: vec![element.clone()],
            };
            let symbols = self.binder.compilation().symbols();
            if value.ty.is_reference_type(symbols)
                && !matches!(value.ty, Type::Dynamic)
                && !self.walks_by_struct_enumerator(&value.ty, element)
                && self.binder.converts_implicitly(&value.ty, &wanted)
                && let Some(copying) = self.enumerable_constructor(target, &wanted)
            {
                let arguments = vec![self.convert(value.clone(), &wanted)];
                return Some(BoundExpression::new(
                    BoundExpressionKind::ObjectCreation {
                        constructor: Some(copying),
                        arguments,
                        initializers: Vec::new(),
                    },
                    target.clone(),
                    span,
                ));
            }
        }
        let mut steps = Vec::new();
        let mut constructor = constructor;
        let mut arguments = arguments;
        // Where the elements end up in an array or a list, and every spread
        // can say how many it holds, the elements up to the last spread are
        // all evaluated first, then the counts are read and the collection
        // is made at its final size, and only then is anything added or
        // walked (Roslyn's known length, which is used up to three elements).
        let last = parts.iter().rposition(|part| part.1);
        let with_capacity = if element.is_some() && last.is_some_and(|last| last < 3) {
            self.capacity_constructor(target)
        } else {
            None
        };
        let mut counted = false;
        if let (Some(with_capacity), Some(last), Some(element)) = (with_capacity, last, element) {
            let int = self.special(SpecialType::Int32);
            let mut held: Vec<BoundExpression> = Vec::new();
            let mut lengths: Vec<BoundExpression> = Vec::new();
            let mut countable = true;
            // The counts are read from what was held, so a spread no one can
            // count is found before anything is evaluated for nothing.
            for (_, spread, bound) in parts.iter().take(last + 1) {
                if *spread && self.spread_count(bound, span).is_none() {
                    countable = false;
                }
            }
            if countable {
                for (_, spread, bound) in parts.iter_mut().take(last + 1) {
                    let value = if *spread {
                        bound.clone()
                    } else {
                        self.convert(bound.clone(), element)
                    };
                    let local = self.declare_synthetic_local("element", value.ty.clone());
                    let held_read = BoundExpression::new(
                        BoundExpressionKind::Local(local),
                        value.ty.clone(),
                        span,
                    );
                    steps.push(BoundExpression::new(
                        BoundExpressionKind::Assignment {
                            target: Box::new(held_read.clone()),
                            value: Box::new(value),
                        },
                        held_read.ty.clone(),
                        span,
                    ));
                    if *spread && let Some(count) = self.spread_count(&held_read, span) {
                        lengths.push(count);
                    }
                    held.push(held_read.clone());
                    *bound = held_read;
                }
                // What is not a spread is one element apiece, those after the
                // last spread too.
                let fixed = parts.iter().filter(|part| !part.1).count();
                let mut total = BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Int32(fixed as i32)),
                    int.clone(),
                    span,
                );
                for count in lengths {
                    total = BoundExpression::new(
                        BoundExpressionKind::Binary {
                            operator: BinaryOperator::Add,
                            left: Box::new(total),
                            right: Box::new(count),
                        },
                        int.clone(),
                        span,
                    );
                }
                constructor = with_capacity;
                arguments = vec![total];
                counted = true;
            }
        }
        steps.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(BoundExpression::new(
                    BoundExpressionKind::ObjectCreation {
                        constructor: Some(constructor),
                        arguments,
                        initializers: Vec::new(),
                    },
                    target.clone(),
                    span,
                )),
            },
            target.clone(),
            span,
        ));
        for (child, spread, bound) in parts {
            if spread {
                let at = child.span();
                let walk = self.foreach_over(bound, at, |this, item| {
                    let item = match element {
                        Some(element) => this.convert(item, element),
                        None => item,
                    };
                    let add = this.bind_add_call(target, read.clone(), item, at)?;
                    // An `Add` marked `[Conditional]` for a symbol that is
                    // not defined is no call: the walk still happens.
                    let kind = if this.is_conditioned_out(&add) {
                        BoundStatementKind::Empty
                    } else {
                        BoundStatementKind::Expression(add)
                    };
                    Some(BoundStatement::new(kind, at))
                })?;
                steps.push(BoundExpression::new(
                    BoundExpressionKind::SpillSequence {
                        statements: vec![walk],
                        value: Box::new(BoundExpression::new(
                            BoundExpressionKind::Sequence(Vec::new()),
                            Type::Void,
                            at,
                        )),
                    },
                    Type::Void,
                    at,
                ));
            } else {
                // What was held is converted already.
                let bound = match element {
                    Some(element) if !counted => self.convert(bound, element),
                    _ => bound,
                };
                let add = self.bind_add_call(target, read.clone(), bound, span)?;
                if !self.is_conditioned_out(&add) {
                    steps.push(add);
                }
            }
        }
        steps.push(read);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            target.clone(),
            span,
        ))
    }

    /// Whether a type is walked by an enumerator that is a struct and it is
    /// no `ICollection<T>`, which copying through `IEnumerable<T>` would
    /// box where walking it by hand does not.
    fn walks_by_struct_enumerator(&self, ty: &Type, element: &Type) -> bool {
        let Some(symbol) = ty.symbol() else {
            return false;
        };
        let symbols = self.binder.compilation().symbols();
        let by_struct = self
            .binder
            .lookup_member(symbol, "GetEnumerator")
            .into_iter()
            .filter(|method| symbols.get(*method).kind == SymbolKind::Method)
            .any(|method| !self.member_type(method, ty).is_reference_type(symbols));
        if !by_struct {
            return false;
        }
        let collection = self
            .binder
            .compilation()
            .type_by_metadata_name("System.Collections.Generic.ICollection`1")
            .map(|symbol| Type::Named {
                symbol,
                type_arguments: vec![element.clone()],
            });
        !collection.is_some_and(|collection| self.binder.converts_implicitly(ty, &collection))
    }

    /// How many elements a spread adds, where that is known before walking
    /// it: an inline array's length is the attribute's, whatever a `Length`
    /// of its own says; otherwise the `Length` or `Count` it carries.
    fn spread_count(&mut self, value: &BoundExpression, span: TextSpan) -> Option<BoundExpression> {
        if let Some((_, length)) = self.binder.inline_array_of(&value.ty) {
            return Some(BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(length)),
                self.special(SpecialType::Int32),
                span,
            ));
        }
        self.length_of(value, span)
    }

    /// The constructor of a `List<T>` that takes how many elements it will
    /// hold.
    fn capacity_constructor(&self, target: &Type) -> Option<SymbolId> {
        let symbol = target.symbol()?;
        let compilation = self.binder.compilation();
        if compilation.type_by_metadata_name("System.Collections.Generic.List`1") != Some(symbol) {
            return None;
        }
        let symbols = compilation.symbols();
        let int = self.special(SpecialType::Int32);
        symbols.lookup(symbol, ".ctor").iter().copied().find(|id| {
            symbols.get(*id).as_method().is_some_and(|detail| {
                let mut sink = Diagnostics::new();
                detail.parameters.len() == 1
                    && self.binder.type_of(detail.parameters[0], &mut sink) == int
            })
        })
    }

    /// A collection expression made by the builder its type names.
    ///
    /// The builder's method takes a `ReadOnlySpan<T>`, and an array of `T`
    /// reaches one: `[a, b]` is an array handed to `ImmutableArray.Create`,
    /// and overload resolution picks whichever of its overloads the array
    /// fits.
    fn bind_through_builder(
        &mut self,
        target: &Type,
        element: &Type,
        leading: Vec<BoundExpression>,
        array: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = target.symbol()?;
        // A type out of metadata says who builds it in its `Constant` table;
        // one declared here says so in its attribute list.
        let (builder, method) = match self.binder.compilation().collection_builder(symbol) {
            Some((builder, method)) => {
                let method = method.to_string();
                let builder = self.binder.compilation().type_by_metadata_name(builder)?;
                (builder, method)
            }
            None => self.source_collection_builder(symbol)?,
        };
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(builder, &method)
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .collect();
        if candidates.is_empty() {
            return None;
        }
        // `ImmutableArray.Create<T>` is told what `T` is; `SyntaxTokenList
        // .Create` has nothing to be told.
        let generic = candidates.iter().any(|candidate| {
            self.binder
                .compilation()
                .symbols()
                .get(*candidate)
                .as_method()
                .is_some_and(|detail| !detail.type_parameters.is_empty())
        });
        let explicit = if generic {
            vec![element.clone()]
        } else {
            Vec::new()
        };
        // `[with(a, b), x]` passes `a` and `b` ahead of the elements.
        let mut arguments = leading;
        arguments.push(array);
        let types: Vec<Type> = arguments.iter().map(|value| value.ty.clone()).collect();
        let Resolved {
            method,
            type_arguments,
            substitution,
        } = self.resolve_call(
            &candidates,
            &types,
            &self.evidence(&arguments),
            &Type::Void,
            &explicit,
        )?;
        let arguments = self.convert_arguments(method, arguments, &Type::Void, &substitution, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments,
                arguments,
                virtual_call: false,
            },
            target.clone(),
            span,
        ))
    }

    /// `[CollectionBuilder(typeof(SyntaxTokenList), "Create")]` read off a
    /// type declared in source: the builder type and the method's name.
    ///
    /// The `typeof` is resolved where the attribute was written, since that
    /// is where its name means what the writer meant, not where the
    /// collection expression happens to be.
    pub(super) fn source_collection_builder(&self, symbol: SymbolId) -> Option<(SymbolId, String)> {
        let compilation = self.binder.compilation();
        for &(tree, span) in compilation.declaration_nodes(symbol) {
            let Some(node) = compilation
                .trees()
                .get(tree)
                .and_then(|syntax| syntax.root().find_node(span))
            else {
                continue;
            };
            let attributes = node
                .children()
                .filter(|child| child.kind() == SyntaxKind::AttributeList)
                .flat_map(|list| list.children().collect::<Vec<_>>())
                .filter(|child| child.kind() == SyntaxKind::Attribute);
            for attribute in attributes {
                let names_builder = attribute
                    .children()
                    .next()
                    .and_then(|name| {
                        identifier_text(&name).or_else(|| {
                            name.children()
                                .last()
                                .and_then(|last| identifier_text(&last))
                        })
                    })
                    .is_some_and(|name| {
                        name == "CollectionBuilder" || name == "CollectionBuilderAttribute"
                    });
                if !names_builder {
                    continue;
                }
                let Some(arguments) = attribute.child_of_kind(SyntaxKind::AttributeArgumentList)
                else {
                    continue;
                };
                let mut builder = None;
                let mut method = None;
                for argument in arguments
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::AttributeArgument)
                {
                    let Some(expression) = argument
                        .children()
                        .find(|child| child.kind().is_expression())
                    else {
                        continue;
                    };
                    match expression.kind() {
                        SyntaxKind::TypeOfExpression => {
                            let context = self.binder.context_at(tree, &node);
                            let mut there = Self::new(self.binder, tree, context, None, false);
                            builder = expression
                                .children()
                                .find(|child| child.kind().is_type_node())
                                .and_then(|ty| there.resolve(&ty).symbol());
                        }
                        SyntaxKind::StringLiteralExpression => {
                            // The token's text, quotes and all: what is
                            // between them is the name.
                            method = expression
                                .child_tokens()
                                .next()
                                .map(|token| token.value_text().trim_matches('"').to_string());
                        }
                        // `nameof(MyCollectionBuilder.Create)` is the last
                        // name it was given.
                        SyntaxKind::InvocationExpression
                            if expression
                                .children()
                                .next()
                                .and_then(|callee| identifier_text(&callee))
                                .as_deref()
                                == Some("nameof") =>
                        {
                            method = expression
                                .descendants()
                                .filter(|inner| inner.kind() == SyntaxKind::IdentifierName)
                                .last()
                                .and_then(|name| identifier_text(&name));
                        }
                        _ => {}
                    }
                }
                return Some((builder?, method?));
            }
        }
        None
    }

    /// What one element of a collection expression's target is.
    ///
    /// An array says so itself; anything else with one type argument is taken
    /// at its word, which is what every collection in the framework means by
    /// its single parameter. A type with none — `SyntaxTokenList` — is asked
    /// what it enumerates.
    /// The element a `params` parameter takes one by one: an array's, or —
    /// for a `params` collection (C# 13) — the collection's.
    pub(super) fn params_element(&self, method: SymbolId, parameters: &[Type]) -> Option<Type> {
        let symbols = self.binder.compilation().symbols();
        if let Some(element) = params_array_element(symbols, method, parameters) {
            return Some(element);
        }
        let last = member_parameters(symbols, method)?.last().copied()?;
        if !symbols.get(last).as_parameter()?.is_params {
            return None;
        }
        self.collection_element(parameters.last()?)
    }

    /// A collection of `target`'s type holding `elements`, already bound and
    /// converted to the element type: what a `params` collection (C# 13)
    /// is made of. An array where one is accepted, the type's builder where
    /// it names one, and otherwise its constructor and one `Add` apiece.
    pub(super) fn collection_of(
        &mut self,
        target: &Type,
        element: &Type,
        elements: Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        // `Add(params MyCollection c)` on `MyCollection` itself: making the
        // collection means making one more of it to pass to `Add`, without
        // end. The language forbids it (CS9223); binding must at least stop.
        thread_local! {
            static BUILDING: std::cell::RefCell<Vec<Type>> =
                const { std::cell::RefCell::new(Vec::new()) };
        }
        if BUILDING.with_borrow(|building| building.iter().filter(|ty| *ty == target).count() > 1) {
            return BoundExpression::error(span);
        }
        BUILDING.with_borrow_mut(|building| building.push(target.clone()));
        let built = self.collection_of_uncached(target, element, elements, span);
        BUILDING.with_borrow_mut(|building| building.pop());
        built
    }

    fn collection_of_uncached(
        &mut self,
        target: &Type,
        element: &Type,
        elements: Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        let array_type = Type::Array {
            element: Box::new(element.clone()),
            rank: 1,
        };
        let array = BoundExpression::new(
            BoundExpressionKind::ArrayCreation {
                element: element.clone(),
                lengths: Vec::new(),
                elements: elements.clone(),
            },
            array_type.clone(),
            span,
        );
        if self.binder.converts_implicitly(&array_type, target) {
            return self.convert(array, target);
        }
        if let Some(built) = self.bind_through_builder(target, element, Vec::new(), array, span) {
            return built;
        }
        let constructor = target.symbol().and_then(|symbol| {
            let symbols = self.binder.compilation().symbols();
            symbols.lookup(symbol, ".ctor").iter().copied().find(|id| {
                symbols
                    .get(*id)
                    .as_method()
                    .is_some_and(|detail| detail.parameters.is_empty())
            })
        });
        let Some(constructor) = constructor else {
            return BoundExpression::new(
                BoundExpressionKind::Unsupported(SyntaxKind::CollectionExpression),
                target.clone(),
                span,
            );
        };
        let mut initializers = Vec::new();
        for value in elements {
            let created =
                BoundExpression::new(BoundExpressionKind::CreatedObject, target.clone(), span);
            if let Some(call) = self.bind_add_call(target, created, value, span)
                && !self.is_conditioned_out(&call)
            {
                initializers.push(call);
            }
        }
        BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor: Some(constructor),
                arguments: Vec::new(),
                initializers,
            },
            target.clone(),
            span,
        )
    }

    pub(super) fn collection_element(&self, target: &Type) -> Option<Type> {
        match target {
            Type::Array { element, rank: 1 } => Some((**element).clone()),
            Type::Named { type_arguments, .. } => match &type_arguments[..] {
                [element] => Some(element.clone()),
                [] => {
                    let enumerable = self
                        .binder
                        .compilation()
                        .type_by_metadata_name("System.Collections.Generic.IEnumerable`1")?;
                    match self.binder.constructed_from(target, enumerable)? {
                        Type::Named { type_arguments, .. } => type_arguments.into_iter().next(),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// `[a, ..rest, b]` as an array, by way of a list that grows.
    ///
    /// How many elements a spread adds is not known until it is walked, so
    /// there is nothing to size an array with. A `List<T>` has no such
    /// trouble: each element is an `Add`, each spread a walk that adds what
    /// it meets, converted to `T` on the way in, and what the list turns out
    /// to hold is the array. C# does the same where it cannot count the
    /// elements first.
    fn spread_into_array(
        &mut self,
        node: &SyntaxNode,
        element: &Type,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = self
            .binder
            .compilation()
            .type_by_metadata_name("System.Collections.Generic.List`1")?;
        let list = Type::Named {
            symbol,
            type_arguments: vec![element.clone()],
        };
        let symbols = self.binder.compilation().symbols();
        let constructor = symbols.lookup(symbol, ".ctor").iter().copied().find(|id| {
            symbols
                .get(*id)
                .as_method()
                .is_some_and(|detail| detail.parameters.is_empty())
        })?;
        let made = self.bind_collection_through_add(
            node,
            &list,
            (constructor, Vec::new()),
            Some(element),
        )?;
        self.bind_member_call(&list, "ToArray", made, Vec::new(), span)
    }

    /// `new { i = key, d }`: the class declared for this shape, constructed
    /// with the values' types and made with the values (§12.8.17.7).
    pub(super) fn bind_anonymous_object(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let names = crate::declare::anonymous_member_names(node);
        // `new { }` has no members, and a class of its own all the same.
        let values: Vec<BoundExpression> = node
            .child_of_kind(SyntaxKind::ObjectInitializerExpression)
            .map(|initializer| initializer.children().collect::<Vec<_>>())
            .unwrap_or_default()
            .into_iter()
            .filter(|child| child.kind() == SyntaxKind::AnonymousObjectMemberDeclarator)
            .filter_map(|declarator| {
                declarator
                    .children()
                    .find(|child| child.kind().is_expression())
            })
            .map(|expression| self.bind_expression(&expression))
            .collect();
        let Some(symbol) = self
            .binder
            .compilation()
            .anonymous_type(&names)
            .filter(|_| names.len() == values.len())
        else {
            return BoundExpression::new(
                BoundExpressionKind::Unsupported(node.kind()),
                Type::Error,
                span,
            );
        };
        // A `null` member has no type to hand the class; `object` is what
        // C# gives it too, with a warning this does not report.
        let object = self.special(SpecialType::Object);
        let type_arguments: Vec<Type> = values
            .iter()
            .map(|value| match &value.ty {
                Type::Null => object.clone(),
                ty => ty.clone(),
            })
            .collect();
        let ty = Type::Named {
            symbol,
            type_arguments,
        };
        let constructor = self
            .binder
            .compilation()
            .symbols()
            .lookup(symbol, ".ctor")
            .first()
            .copied();
        let arguments = match constructor {
            Some(constructor) => {
                self.convert_arguments(constructor, values, &ty, &HashMap::new(), span)
            }
            None => values,
        };
        BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor,
                arguments,
                initializers: Vec::new(),
            },
            ty,
            span,
        )
    }

    /// `a with { B = 3 }` on an anonymous type (C# 10): a new one made by
    /// its constructor, each member given its new value or the receiver's.
    /// The receiver is evaluated first, then the new values in the order
    /// written, and only then is anything read off the receiver.
    pub(super) fn bind_anonymous_with(
        &mut self,
        node: &SyntaxNode,
        receiver: &BoundExpression,
    ) -> Option<BoundExpression> {
        let span = node.span();
        let symbol = receiver.ty.symbol()?;
        let names = self.binder.compilation().anonymous_names(symbol)?.to_vec();
        let constructor = self
            .binder
            .compilation()
            .symbols()
            .lookup(symbol, ".ctor")
            .first()
            .copied()?;
        let ty = receiver.ty.clone();
        let held = self.declare_synthetic_local("anonymous", ty.clone());
        let read =
            |ty: &Type| BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
        let mut steps = vec![BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read(&ty)),
                value: Box::new(receiver.clone()),
            },
            ty.clone(),
            span,
        )];
        let mut given: HashMap<String, BoundExpression> = HashMap::new();
        if let Some(initializer) = node.child_of_kind(SyntaxKind::WithInitializerExpression) {
            for assignment in initializer
                .children()
                .filter(|child| child.kind() == SyntaxKind::SimpleAssignmentExpression)
            {
                let mut parts = assignment.children();
                let (Some(name), Some(value)) = (parts.next(), parts.next()) else {
                    continue;
                };
                let Some(name) = identifier_text(&name) else {
                    continue;
                };
                let Some(member) = self
                    .binder
                    .lookup_member(symbol, &name)
                    .into_iter()
                    .find(|member| self.kind_of(*member) == SymbolKind::Property)
                else {
                    self.bind_expression(&value);
                    continue;
                };
                let member_type = self.member_type(member, &ty);
                let bound = self.bind_expression(&value);
                let bound = self.convert(bound, &member_type);
                let local = self.declare_synthetic_local("with", member_type.clone());
                let local_read = BoundExpression::new(
                    BoundExpressionKind::Local(local),
                    member_type.clone(),
                    span,
                );
                steps.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(local_read.clone()),
                        value: Box::new(bound),
                    },
                    member_type,
                    span,
                ));
                given.insert(name, local_read);
            }
        }
        let mut arguments = Vec::new();
        for name in &names {
            let value = match given.remove(name) {
                Some(value) => value,
                None => {
                    let member = self
                        .binder
                        .lookup_member(symbol, name)
                        .into_iter()
                        .find(|member| self.kind_of(*member) == SymbolKind::Property)?;
                    let member_type = self.member_type(member, &ty);
                    BoundExpression::new(
                        BoundExpressionKind::Property {
                            receiver: Some(Box::new(read(&ty))),
                            property: member,
                        },
                        member_type,
                        span,
                    )
                }
            };
            arguments.push(value);
        }
        let arguments = self.convert_arguments(constructor, arguments, &ty, &HashMap::new(), span);
        steps.push(BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor: Some(constructor),
                arguments,
                initializers: Vec::new(),
            },
            ty.clone(),
            span,
        ));
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            ty,
            span,
        ))
    }

    pub(super) fn bind_object_creation(
        &mut self,
        node: &SyntaxNode,
        target: Option<&Type>,
    ) -> BoundExpression {
        let ty = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map_or_else(
                || target.cloned().unwrap_or(Type::Error),
                |written| self.resolve(&written),
            );
        // `new IWorksheet()` on a `[ComImport, CoClass(typeof(Worksheet))]`
        // interface makes a `Worksheet`, which is then an `IWorksheet`
        // (Roslyn's `BindComImportCoClassCreationExpression`).
        if let Type::Named { symbol, .. } = &ty
            && let Some(class) = self.binder.co_class(*symbol)
        {
            let created = self.bind_object_creation_of(node, class);
            return self.convert_explicitly(created, &ty);
        }
        self.bind_object_creation_of(node, ty)
    }

    /// `new T(...)` for the type it makes.
    fn bind_object_creation_of(&mut self, node: &SyntaxNode, ty: Type) -> BoundExpression {
        let span = node.span();
        let arguments = node
            .child_of_kind(SyntaxKind::ArgumentList)
            .map(|list| self.bind_argument_list(&list))
            .unwrap_or_default();

        // `return new(a, b);` where a tuple is wanted makes the tuple: its
        // constructor is the `ValueTuple`'s, and the elements are the
        // arguments converted to their types.
        if node.children().all(|child| !child.kind().is_type_node())
            && let Some(elements) = self.tuple_element_types(&ty)
            && elements.len() == arguments.len()
        {
            let values: Vec<BoundExpression> = arguments
                .into_iter()
                .zip(elements)
                .map(|(argument, element)| self.convert(argument, &element))
                .collect();
            return BoundExpression::new(BoundExpressionKind::TupleCreation(values), ty, span);
        }

        // `new Op(Square)` is not a constructor call at all: a delegate's
        // constructor takes a target and a function pointer, which no source
        // ever writes. It is the same conversion `Op f = Square;` does.
        if ty
            .symbol()
            .is_some_and(|symbol| self.kind_of_type(symbol) == Some(TypeKind::Delegate))
            && arguments.len() == 1
        {
            let argument = arguments
                .into_iter()
                .next()
                .unwrap_or_else(|| BoundExpression::error(span));
            // `new Action(ref M)` and `new Action(out a)` are accepted, and
            // the `ref` or `out` means nothing, as it never has.
            let argument = match argument.kind {
                BoundExpressionKind::RefArgument { operand, .. } => *operand,
                _ => argument,
            };
            // `new UnityAction(h)` with `h` an `Action` is a new delegate
            // calling `h.Invoke` (§12.8.17.5), of the type written: no
            // conversion takes one delegate type to another.
            if !matches!(
                argument.kind,
                BoundExpressionKind::MethodGroup { .. }
                    | BoundExpressionKind::UnboundLambda(_)
                    | BoundExpressionKind::Lambda(_)
            ) && argument
                .ty
                .symbol()
                .is_some_and(|symbol| self.kind_of_type(symbol) == Some(TypeKind::Delegate))
                && let Some(invoke) = argument.ty.symbol().and_then(|symbol| {
                    self.binder
                        .compilation()
                        .symbols()
                        .lookup(symbol, "Invoke")
                        .first()
                        .copied()
                })
            {
                return BoundExpression::new(
                    BoundExpressionKind::DelegateCreation {
                        method: invoke,
                        receiver: Some(Box::new(argument)),
                        virtual_dispatch: false,
                        type_arguments: Vec::new(),
                        written_new: true,
                    },
                    ty,
                    span,
                );
            }
            let mut converted = self.convert(argument, &ty);
            if let BoundExpressionKind::DelegateCreation { written_new, .. } = &mut converted.kind {
                *written_new = true;
            }
            return converted;
        }

        // The constructor is an overload like any other, looked up under the
        // name metadata gives it.
        let candidates: Vec<_> = ty
            .symbol()
            .map(|symbol| {
                self.binder
                    .compilation()
                    .symbols()
                    .lookup(symbol, ".ctor")
                    .to_vec()
            })
            .unwrap_or_default();
        let names = node
            .child_of_kind(SyntaxKind::ArgumentList)
            .map(|list| Self::argument_names(&list))
            .unwrap_or_default();
        // A `dynamic` argument leaves the constructor to the runtime binder
        // too (§12.8.17.2).
        // The initializer is applied to what the call site made, held in a
        // variable of the class's own type: its members are found here, not
        // at run time.
        let initializer = node.children().find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::ObjectInitializerExpression
                    | SyntaxKind::CollectionInitializerExpression
            )
        });
        if !candidates.is_empty() && Self::has_dynamic_argument(&arguments) {
            let created = Self::dynamic_operation(
                DynamicOperation::InvokeConstructor,
                None,
                arguments,
                names,
                ty.clone(),
                span,
            );
            let Some(initializer) = initializer else {
                return created;
            };
            let held = self.declare_synthetic_local("created", ty.clone());
            let read = BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
            let mut steps = vec![BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(created),
                },
                ty.clone(),
                span,
            )];
            steps.extend(self.bind_initializers_on(&initializer, &ty, Some(&read)));
            steps.push(read);
            return BoundExpression::new(BoundExpressionKind::Sequence(steps), ty, span);
        }
        let candidates = self.named_candidates(&candidates, &names);
        let mut arguments = self.reorder_named(&candidates, &names, arguments, &ty);
        // Resolution may rewrite lambdas among the arguments; whether two
        // constructors are ambiguous is judged on them as written.
        let written_arguments =
            (candidates.len() > 1 && names.iter().all(Option::is_none)).then(|| arguments.clone());
        let constructor = if candidates.is_empty()
            || (arguments.is_empty() && self.implicit_struct_constructor(&ty, &candidates))
        {
            None
        } else {
            self.resolve_with_lambdas(&candidates, &mut arguments, &ty, &[], false)
                .map(|resolved| resolved.method)
        };
        if let (Some(constructor), Some(written)) = (constructor, &written_arguments) {
            // Blamed on the type's name, or on `new` where there is none.
            let at = node
                .children()
                .find(|child| child.kind().is_type_node())
                .map_or(node.span(), |name| name.span());
            self.report_if_ambiguous(constructor, &candidates, written, &ty, &[], false, at);
        }
        // Resolution keeps to the constructors this code may call wherever
        // one of them takes the arguments; one it may not call is chosen
        // only where none does, and that is CS0122: `new Single()` outside a
        // class whose constructor is private. Blamed like an ambiguity.
        // A type that cannot be made at all is CS0144 and nothing more: the
        // constructor an abstract class is given is protected.
        let hidden = match constructor {
            _ if self.cannot_be_made(&ty) => None,
            Some(constructor) => (!self.accessible(constructor)).then_some(constructor),
            // None that may be called takes these; one that may not might.
            None => {
                let hidden: Vec<SymbolId> = candidates
                    .iter()
                    .copied()
                    .filter(|candidate| !self.accessible(*candidate))
                    .collect();
                if hidden.is_empty() || hidden.len() == candidates.len() {
                    None
                } else {
                    let mut given = arguments.clone();
                    self.resolve_with_lambdas(&hidden, &mut given, &ty, &[], false)
                        .map(|resolved| resolved.method)
                }
            }
        };
        let constructor_missing = constructor.is_none() && hidden.is_some();
        if let Some(constructor) = hidden {
            let at = node
                .children()
                .find(|child| child.kind().is_type_node())
                .map_or_else(
                    || {
                        node.child_tokens()
                            .find(|token| token.kind() == SyntaxKind::NewKeyword)
                            .map_or(node.span(), |token| token.span())
                    },
                    |name| name.span(),
                );
            let frame = self.substitution_for(constructor, &ty);
            let display =
                crate::checks::member_display(self.binder.compilation(), constructor, &frame, None);
            self.report(ErrorCode::ErrBadAccess, at, &[&display]);
        }
        let written = node.children().find(|child| child.kind().is_type_node());
        if let Some(written) = &written
            && !constructor_missing
        {
            self.check_creation(node, written, &ty, &candidates, constructor, &arguments);
        }
        let arguments = match constructor {
            Some(constructor) => {
                self.convert_arguments(constructor, arguments, &ty, &HashMap::new(), node.span())
            }
            None => arguments,
        };

        let initializers = node
            .children()
            .find(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::ObjectInitializerExpression
                        | SyntaxKind::CollectionInitializerExpression
                )
            })
            .map(|list| self.bind_initializers(&list, &ty))
            .unwrap_or_default();

        BoundExpression::new(
            BoundExpressionKind::ObjectCreation {
                constructor,
                arguments,
                initializers,
            },
            ty,
            span,
        )
    }

    /// Whether `new` of this type is CS0144: an interface, or an abstract
    /// class.
    fn cannot_be_made(&self, ty: &Type) -> bool {
        let Some(symbol) = ty.symbol() else {
            return false;
        };
        if !matches!(ty, Type::Named { .. }) {
            return false;
        }
        let found = self.binder.compilation().symbols().get(symbol);
        match found.type_kind() {
            Some(TypeKind::Interface) => true,
            Some(TypeKind::Class | TypeKind::Record) => {
                found.modifiers.contains(Modifiers::ABSTRACT)
                    && !found.modifiers.contains(Modifiers::STATIC)
            }
            _ => false,
        }
    }

    /// What is wrong with a `new T(...)` that made nothing: `T` cannot be
    /// made at all (CS0144), or no constructor of it takes these arguments.
    fn check_creation(
        &mut self,
        node: &SyntaxNode,
        written: &SyntaxNode,
        ty: &Type,
        candidates: &[SymbolId],
        constructor: Option<SymbolId>,
        arguments: &[BoundExpression],
    ) {
        let Some(symbol) = ty.symbol() else { return };
        if !matches!(ty, Type::Named { .. }) {
            return;
        }
        let symbols = self.binder.compilation().symbols();
        let found = symbols.get(symbol);
        if self.cannot_be_made(ty) {
            let name = self.display(ty);
            self.report(ErrorCode::ErrNoNewAbstract, node.span(), &[&name]);
            return;
        }
        if constructor.is_some()
            || candidates.is_empty()
            || (arguments.is_empty() && self.implicit_struct_constructor(ty, candidates))
            || arguments.iter().any(|argument| argument.ty.is_error())
        {
            return;
        }
        let types: Vec<Type> = arguments
            .iter()
            .map(|argument| argument.ty.clone())
            .collect();
        let spans: Vec<TextSpan> = arguments.iter().map(|argument| argument.span).collect();
        let name = found.name.clone();
        self.report_no_overload(
            candidates,
            &name,
            &types,
            &spans,
            ty,
            &[],
            written.span(),
            Some(ty),
        );
    }

    pub(super) fn bind_array_creation(&mut self, node: &SyntaxNode) -> BoundExpression {
        self.bind_array_creation_as(node, None)
    }

    /// The same, for a bare `{ ... }` whose type the declaration around it
    /// supplies.
    pub(super) fn bind_array_creation_as(
        &mut self,
        node: &SyntaxNode,
        target: Option<&Type>,
    ) -> BoundExpression {
        let span = node.span();
        // `object[] args = { vals };` has no type beside its braces, and
        // the `vals` inside them is a value, not the array's type.
        let array_type = if node.kind() == SyntaxKind::ArrayInitializerExpression {
            None
        } else {
            node.children().find(|child| child.kind().is_type_node())
        };
        let ty = array_type.as_ref().map_or_else(
            || target.cloned().unwrap_or(Type::Error),
            |written| self.resolve(written),
        );

        let initializer = if node.kind() == SyntaxKind::ArrayInitializerExpression {
            Some(node.clone())
        } else {
            node.child_of_kind(SyntaxKind::ArrayInitializerExpression)
        };
        // `new byte[,] { { 1, 2 }, { 3, 4 } }` writes one brace per dimension.
        // The sizes are what the nesting says, and the values are read across
        // the rows, which is the order the runtime stores them in.
        let rank = match &ty {
            Type::Array { rank, .. } => *rank,
            // `string[,] table = { { "", "M" }, { "S", "SM" } }` writes no
            // type beside the braces; the nesting says how many dimensions
            // there are, since a row of an array with one is never braces.
            _ => initializer.as_ref().map_or(1, initializer_depth),
        };
        let mut sizes: Vec<usize> = Vec::new();
        let written: Vec<SyntaxNode> = initializer
            .map(|list| flatten_initializer(&list, rank, 0, &mut sizes))
            .unwrap_or_default();
        let elements: Vec<BoundExpression> = written
            .iter()
            .map(|element| self.bind_expression(element))
            .collect();

        // `new[] { 1, 2 }` has no type of its own; the elements say what it
        // is: the best common type of them (§12.6.3.16).
        let declared_element = matches!(ty, Type::Array { .. });
        let element_type = match &ty {
            Type::Array { element, .. } => (**element).clone(),
            _ => self.best_common_type(&elements).unwrap_or_else(|| {
                elements
                    .first()
                    .map_or(Type::Error, |first| first.ty.clone())
            }),
        };
        let ty = match ty {
            Type::Array { .. } => ty,
            _ => Type::Array {
                element: Box::new(element_type.clone()),
                rank,
            },
        };

        // A rank specifier holds the length, unless it was left out because an
        // initializer says how many there are.
        let mut lengths: Vec<BoundExpression> = array_type
            .and_then(|target| target.child_of_kind(SyntaxKind::ArrayRankSpecifier))
            .map(|specifier| {
                specifier
                    .children()
                    .filter(|child| {
                        child.kind().is_expression()
                            && child.kind() != SyntaxKind::OmittedArraySizeExpression
                    })
                    .map(|length| {
                        // `new int[new()]` and `new int[default]` are an
                        // `int` of zero.
                        let bound = self.bind_expression(&length);
                        if matches!(bound.kind, BoundExpressionKind::UnboundCreation(_))
                            || (bound.ty.is_error()
                                && matches!(bound.kind, BoundExpressionKind::Default(_)))
                        {
                            let int = self.special(SpecialType::Int32);
                            self.convert(bound, &int)
                        } else if matches!(bound.ty, Type::Dynamic) {
                            // A `dynamic` size is converted at run time, as
                            // an array index: `new int[d]` takes a `long`
                            // that fits.
                            let int = self.special(SpecialType::Int32);
                            Self::dynamic_array_index(bound, &int)
                        } else {
                            bound
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();
        // An initializer for an array of more than one dimension says the
        // sizes itself, and a backend needs them: nothing else says where a
        // row ends.
        if lengths.is_empty() && sizes.len() == rank && rank > 1 {
            let int = self.special(SpecialType::Int32);
            lengths = sizes
                .iter()
                .map(|size| {
                    BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Int32(*size as i32)),
                        int.clone(),
                        span,
                    )
                })
                .collect();
        }

        // Each value is an assignment to an element of the type the array
        // is written with; `new[] { ... }` takes its type from the values.
        if declared_element {
            for (element, node) in elements.iter().zip(&written) {
                // A type or a namespace named where a value is wanted has
                // been said so, and a `stackalloc` takes the type of what
                // it is put in.
                if node.kind() != SyntaxKind::ArrayInitializerExpression
                    && !matches!(
                        element.kind,
                        BoundExpressionKind::TypeExpression(_)
                            | BoundExpressionKind::NamespaceExpression(_)
                            | BoundExpressionKind::StackAlloc { .. }
                    )
                {
                    self.check_assignable(node, element, &element_type);
                }
            }
        }
        let elements = elements
            .into_iter()
            .map(|element| self.convert(element, &element_type))
            .collect();

        BoundExpression::new(
            BoundExpressionKind::ArrayCreation {
                element: element_type,
                lengths,
                elements,
            },
            ty,
            span,
        )
    }
}

/// Whether an element of a collection expression has a type of its own
/// that binding it without a target can say: a literal, a name, a member
/// access, or a cast or parenthesis around one.
fn is_plain_element(expression: &SyntaxNode) -> bool {
    match expression.kind() {
        SyntaxKind::NumericLiteralExpression
        | SyntaxKind::StringLiteralExpression
        | SyntaxKind::InterpolatedStringExpression
        | SyntaxKind::CharacterLiteralExpression
        | SyntaxKind::TrueLiteralExpression
        | SyntaxKind::FalseLiteralExpression
        | SyntaxKind::NullLiteralExpression
        | SyntaxKind::IdentifierName
        | SyntaxKind::SimpleMemberAccessExpression => true,
        // A cast's first child is the type, which is written like a name;
        // the operand is what comes last.
        SyntaxKind::CastExpression
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::UnaryMinusExpression => expression
            .children()
            .filter(|child| child.kind().is_expression())
            .last()
            .is_some_and(|child| is_plain_element(&child)),
        _ => false,
    }
}

/// Whether an argument was written `ref`, `out` or `in`.
/// The values an array initializer holds, read across its rows.
///
/// `{ { 1, 2 }, { 3, 4 } }` is one brace per dimension, and the sizes are
/// what the nesting says: the first row decides how wide every row is, which
/// is what the language requires of the rest.
/// How many dimensions a bare initializer writes: one per level of braces.
fn initializer_depth(list: &SyntaxNode) -> usize {
    1 + list
        .children()
        .find(|child| child.kind().is_expression())
        .filter(|child| child.kind() == SyntaxKind::ComplexElementInitializerExpression)
        .map_or(0, |row| initializer_depth(&row))
}

fn flatten_initializer(
    list: &SyntaxNode,
    depth: usize,
    level: usize,
    sizes: &mut Vec<usize>,
) -> Vec<SyntaxNode> {
    let rows: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind().is_expression())
        .collect();
    // The first row of a level is the one that says how wide the level is.
    if sizes.len() == level {
        sizes.push(rows.len());
    }
    if depth <= 1 {
        return rows;
    }
    rows.iter()
        .flat_map(|row| flatten_initializer(row, depth - 1, level + 1, sizes))
        .collect()
}

/// The element type of a method's trailing `params` array, if it has one.
fn params_array_element(
    symbols: &crate::symbol::Symbols,
    method: SymbolId,
    parameters: &[Type],
) -> Option<Type> {
    let last = member_parameters(symbols, method)?.last().copied()?;
    if !symbols.get(last).as_parameter()?.is_params {
        return None;
    }
    match parameters.last()? {
        Type::Array { element, rank } if *rank == 1 => Some(element.as_ref().clone()),
        _ => None,
    }
}

/// The types a collection expression's elements give, what inference reads of
/// them, what each folds to, and what kind each is.
type CollectionEvidence = (
    Vec<Type>,
    Vec<InferenceArgument>,
    Vec<Option<ConstantValue>>,
    Vec<ElementKind>,
);

/// What an element of a collection expression says about the element type.
enum Evidenced {
    /// Nothing: `null`, `default`, `[]`.
    Nothing,
    /// Its own type, what it folds to where it is a constant, and its kind.
    Typed(Type, Option<ConstantValue>, ElementKind),
    /// A nested collection, which inference reads element by element and
    /// which has no type of its own.
    Nested(Vec<InferenceArgument>),
}
