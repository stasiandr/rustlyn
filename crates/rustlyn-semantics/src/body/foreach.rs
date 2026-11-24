//! `foreach` and `await foreach`: how a collection is walked (§13.9.5), and
//! the members of the enumeration pattern.

use std::collections::HashMap;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{AsyncEnumeration, BodyBinder, Resolved, Walked};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundEnumeration, BoundExpression, BoundExpressionKind, BoundStatement, BoundStatementKind,
    ConstantValue, IncrementOperator, LocalId,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    pub(super) fn bind_foreach(&mut self, node: &SyntaxNode) -> BoundStatementKind {
        self.push_scope();

        // `foreach (var item in items)` has an `IdentifierName` on both sides
        // of the `in`, so position decides: the collection is the last thing
        // before the body.
        let collection = node
            .children()
            .filter(|child| !child.kind().is_statement_node())
            .last();
        let mut collection = collection
            .as_ref()
            .map(|expression| self.bind_expression(expression));
        // An inline array is walked as the span over its elements — except
        // by a body that awaits or yields, since a span may not outlast
        // either. That loop reaches each element afresh from the buffer
        // (§12.8.12.3), the way Roslyn walks every inline array: what the
        // buffer is reached through is kept, and the buffer is not.
        let mut walked_inline = None;
        let suspending = node
            .children()
            .find(|child| child.kind().is_statement_node())
            .is_some_and(|body| suspends_within(&body));
        if suspending
            && let Some((element, length)) = collection
                .as_ref()
                .and_then(|value| self.binder.inline_array_of(&value.ty))
            && let Some(value) = collection.take()
        {
            let readonly = !self.is_writable_place(&value);
            let span = value.span;
            let mut prefix = Vec::new();
            let place = self.stable_place(value, &mut prefix);
            collection = self.inline_array_span(place.clone(), &element, length, readonly, span);
            walked_inline = Some((prefix, place, element, length, readonly));
        } else if let Some(value) = collection.take() {
            collection = Some(match self.binder.inline_array_of(&value.ty) {
                Some((element, length)) => {
                    let readonly = !self.is_writable_place(&value);
                    let span = value.span;
                    self.inline_array_span(value, &element, length, readonly, span)
                        .unwrap_or_else(|| BoundExpression::error(span))
                }
                None => value,
            });
        }
        // A `dynamic` collection is walked as the `IEnumerable` the runtime
        // binder converts it to, and what it yields is `dynamic` (§13.9.5).
        let walks_dynamic = collection
            .as_ref()
            .is_some_and(|value| matches!(value.ty, Type::Dynamic));
        if walks_dynamic
            && let Some(value) = collection.take()
            && let Some(enumerable) = self.framework_type("System.Collections.IEnumerable")
        {
            collection = Some(self.convert(value, &enumerable));
        }
        let collection_type = collection.as_ref().map_or(Type::Error, |c| c.ty.clone());
        let collection_span = (
            collection
                .as_ref()
                .map_or_else(|| TextSpan::new(0, 0), |c| c.span),
            node.span(),
        );

        // `await foreach` asks for an asynchronous enumerator instead, and
        // awaits each step of it. It does not go to a backend as a loop of
        // its own kind: it is the `while` and `try` it means, written here.
        let awaited = node
            .child_tokens()
            .any(|token| token.kind() == SyntaxKind::AwaitKeyword);
        let mut asynchronous = None;
        if awaited && !collection_type.is_error() {
            let Some(value) = collection.take() else {
                unreachable!("a typed collection was bound");
            };
            match self.async_enumeration_of(value, &collection_type) {
                Some(found) => asynchronous = Some(found),
                None => {
                    self.pop_scope();
                    return BoundStatementKind::Unsupported(node.kind());
                }
            }
        }

        // An array is walked by index; anything else has to be asked for an
        // enumerator, and the element type comes from what that yields. A
        // `SyntaxList<T>?` is walked as the `SyntaxList<T>` inside it: the
        // loop reads its `Value`, which is a `T` or a throw.
        // An extension `GetEnumerator(this int? self)` takes the nullable as
        // it is, though, and is asked first.
        let as_written = match self.binder.nullable_underlying(&collection_type) {
            Some(_) if asynchronous.is_none() => {
                self.enumeration_of(&collection_type, collection_span)
            }
            _ => None,
        };
        let collection_type = if as_written.is_some() {
            collection_type
        } else {
            self.binder
                .nullable_underlying(&collection_type)
                .unwrap_or(collection_type)
        };
        let enumeration = match &collection_type {
            _ if as_written.is_some() => as_written,
            _ if asynchronous.is_some() => None,
            // `foreach (var q in table)` over a `string[,]` walks every
            // dimension by index too, one loop inside another.
            Type::Array { .. } | Type::Error => None,
            other => self.enumeration_of(other, collection_span),
        };
        let enumeration = if walks_dynamic {
            enumeration.map(|(found, _)| (found, Type::Dynamic))
        } else {
            enumeration
        };

        // `foreach (var (a, b) in pairs)` walks the collection into a
        // variable nobody named and takes that apart on each turn.
        // `foreach (var (a, b) in pairs)` and `foreach ((var a, var b) in
        // pairs)` are the same thing written two ways, and both take the
        // element apart on each turn.
        // Only before the `in`: `foreach (var i in (1, 2, 3))` walks a tuple.
        let in_keyword = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::InKeyword)
            .map_or(usize::MAX, |token| token.span().start() as usize);
        let deconstructed = node.children().find(|child| {
            (child.span().end() as usize) <= in_keyword
                && match child.kind() {
                    SyntaxKind::DeclarationExpression => child
                        .child_of_kind(SyntaxKind::ParenthesizedVariableDesignation)
                        .is_some(),
                    SyntaxKind::TupleExpression => true,
                    _ => false,
                }
        });

        // With a `(a, b)` on the left there is no element type written, and
        // the collection itself is an `IdentifierName` — which is type syntax
        // too, and would be resolved as one.
        let type_node = node
            .children()
            .find(|child| child.kind().is_type_node())
            .filter(|_| deconstructed.is_none())
            // `foreach (scoped var r in ...)`: the type is inside.
            .map(|node| match node.kind() {
                SyntaxKind::ScopedType => node
                    .children()
                    .find(|child| child.kind().is_type_node())
                    .unwrap_or(node),
                _ => node,
            });
        // `foreach (ref int x in span)` makes each element a variable of its
        // own name rather than a copy.
        let by_ref = type_node
            .as_ref()
            .is_some_and(|node| node.kind() == SyntaxKind::RefType);
        let readonly_ref = type_node.as_ref().is_some_and(|node| {
            node.kind() == SyntaxKind::RefType
                && node
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::ReadOnlyKeyword)
        });
        let type_node = type_node.map(|node| match node.kind() {
            SyntaxKind::RefType => node
                .children()
                .find(|child| child.kind().is_type_node())
                .unwrap_or(node),
            _ => node,
        });
        let declared_var = type_node.as_ref().is_some_and(|node| node.text() == "var");
        let element = if declared_var {
            match (&enumeration, &asynchronous) {
                // `foreach (var x in grid)` over a `double[,]` is a
                // `double`, cast back from what `IEnumerable` gives.
                (Some(_), _) if matches!(collection_type, Type::Array { .. }) => {
                    self.element_type_of(&collection_type)
                }
                (Some((_, element)), _) => element.clone(),
                (None, Some(asynchronous)) => asynchronous.element.clone(),
                (None, None) => self.element_type_of(&collection_type),
            }
        } else {
            type_node
                .as_ref()
                .map_or(Type::Error, |node| self.resolve(node))
        };

        // What the walk hands out, before anything converts it.
        let walked_element = match (&enumeration, &asynchronous) {
            // A rectangular array is walked as an `Array`, and each element
            // is still of the array's element type.
            _ if matches!(collection_type, Type::Array { .. }) => {
                self.element_type_of(&collection_type)
            }
            (Some((_, element)), _) => element.clone(),
            (None, Some(asynchronous)) => asynchronous.element.clone(),
            (None, None) => self.element_type_of(&collection_type),
        };
        // `foreach (S1 y in ints)` where `S1` declares an operator from
        // `int`: the element is converted by it on each turn, as a cast
        // would (§13.9.5), into the variable the body sees.
        // `await foreach` converts what it is handed on its own.
        let through_operator = deconstructed.is_none()
            && asynchronous.is_none()
            && !declared_var
            && !by_ref
            && !element.is_error()
            && !walked_element.is_error()
            && element != walked_element
            && self.iterates_through_operator(&walked_element, &element);
        let (local, taking_apart) = match &deconstructed {
            None if through_operator => {
                let item = self.declare_synthetic_local("item", walked_element.clone());
                let span = node.span();
                let variable = node
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| {
                        let local =
                            self.declare_local(token.value_text(), element.clone(), token.span());
                        if let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
                            slot.readonly = true;
                        }
                        local
                    });
                let taking = variable.map(|variable| {
                    let read = BoundExpression::new(
                        BoundExpressionKind::Local(item),
                        walked_element.clone(),
                        span,
                    );
                    let converted = self.convert_explicitly(read, &element);
                    BoundStatementKind::Expression(BoundExpression::new(
                        BoundExpressionKind::Assignment {
                            target: Box::new(BoundExpression::new(
                                BoundExpressionKind::Local(variable),
                                element.clone(),
                                span,
                            )),
                            value: Box::new(converted),
                        },
                        element.clone(),
                        span,
                    ))
                });
                (Some(item), taking)
            }
            Some(target) => {
                let element = match (&enumeration, &asynchronous) {
                    // A rectangular array is walked as an `Array`, and each
                    // element is still of the array's element type.
                    _ if matches!(collection_type, Type::Array { .. }) => {
                        self.element_type_of(&collection_type)
                    }
                    (Some((_, element)), _) => element.clone(),
                    (None, Some(asynchronous)) => asynchronous.element.clone(),
                    (None, None) => self.element_type_of(&collection_type),
                };
                let local = self.declare_synthetic_local("item", element.clone());
                let value =
                    BoundExpression::new(BoundExpressionKind::Local(local), element, target.span());
                let call = self.deconstruct_into(target, value, target.span());
                (Some(local), call.map(BoundStatementKind::Expression))
            }
            None => (
                node.child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| {
                        let local =
                            self.declare_local(token.value_text(), element.clone(), token.span());
                        // The iteration variable is read-only (§13.9.5); a
                        // `ref` one refers to what the enumerator hands out.
                        if let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
                            if by_ref {
                                slot.by_ref = true;
                                slot.readonly_ref = readonly_ref;
                            } else {
                                slot.readonly = true;
                            }
                        }
                        local
                    }),
                None,
            ),
        };

        let body = node
            .children()
            .find(|child| child.kind().is_statement_node())
            .map(|child| Box::new(self.bind_statement(&child)));
        // The variables are taken apart before anything the body does.
        let body = match (taking_apart, body) {
            (Some(taking_apart), Some(body)) => {
                let span = body.span;
                Some(Box::new(BoundStatement::new(
                    BoundStatementKind::Block(vec![BoundStatement::new(taking_apart, span), *body]),
                    span,
                )))
            }
            (_, body) => body,
        };
        self.pop_scope();

        if let Some(asynchronous) = asynchronous {
            return match (local, body) {
                (Some(local), Some(body)) => {
                    self.lower_await_foreach(asynchronous, local, element, *body, node.span())
                }
                _ => BoundStatementKind::Unsupported(node.kind()),
            };
        }

        if let Some((prefix, place, element, length, readonly)) = walked_inline {
            let walked = Walked::Inline {
                place,
                element,
                length,
                readonly,
            };
            return match (local, body) {
                (Some(local), Some(body)) => self.walk_by_index(prefix, walked, local, *body),
                _ => BoundStatementKind::Unsupported(node.kind()),
            };
        }
        // A span is walked by index too, which is also what lets its
        // elements be `ref` variables.
        if self.is_span_type(&collection_type) {
            return match (local, collection, body) {
                (Some(local), Some(collection), Some(body)) => {
                    self.walk_by_index(Vec::new(), Walked::Span(collection), local, *body)
                }
                _ => BoundStatementKind::Unsupported(node.kind()),
            };
        }

        // An array walk keeps what it is walking and where it has got to; both
        // are variables of this body like any other, which is what lets an
        // iterator hoist them along with the rest.
        let walk = match &collection_type {
            Type::Array { .. } => Some((
                self.declare_synthetic_local("walked", collection_type.clone()),
                self.declare_synthetic_local("at", self.special(SpecialType::Int32)),
            )),
            _ => None,
        };
        let dimensions: Vec<(LocalId, LocalId)> = match &collection_type {
            Type::Array { rank, .. } if *rank > 1 => (0..*rank)
                .map(|_| {
                    let int = self.special(SpecialType::Int32);
                    (
                        self.declare_synthetic_local("at", int.clone()),
                        self.declare_synthetic_local("upper", int),
                    )
                })
                .collect(),
            _ => Vec::new(),
        };
        // Such an array is walked by its indices, not through `IEnumerable`.
        let enumeration = if dimensions.is_empty() {
            enumeration
        } else {
            None
        };
        // An extension `GetEnumerator` takes the collection as its first
        // argument, converted to what that parameter is: `this object`
        // boxes a struct collection.
        let collection = match (&enumeration, collection) {
            (Some((found, _)), Some(value)) => Some(self.enumerated_as(found, value)),
            (_, collection) => collection,
        };
        match (local, collection, body) {
            (Some(local), Some(collection), Some(body)) => BoundStatementKind::ForEach {
                local,
                collection,
                body,
                enumeration: enumeration.map(|(enumeration, _)| Box::new(enumeration)),
                walk,
                dimensions,
            },
            _ => BoundStatementKind::Unsupported(node.kind()),
        }
    }

    /// The collection as its `GetEnumerator` takes it: an extension's takes
    /// it as its first argument, converted to what that parameter is — `this
    /// object` boxes a struct collection.
    fn enumerated_as(
        &mut self,
        found: &BoundEnumeration,
        value: BoundExpression,
    ) -> BoundExpression {
        if found.extension.is_none() {
            return value;
        }
        let symbols = self.binder.compilation().symbols();
        let first = symbols
            .get(found.get_enumerator)
            .as_method()
            .and_then(|detail| {
                let parameter = *detail.parameters.first()?;
                let substitution: HashMap<SymbolId, Type> = detail
                    .type_parameters
                    .iter()
                    .copied()
                    .zip(found.extension.clone().unwrap_or_default())
                    .collect();
                let mut sink = Diagnostics::new();
                Some(
                    self.binder
                        .type_of(parameter, &mut sink)
                        .substitute(&substitution),
                )
            });
        match first {
            Some(wanted) if wanted != value.ty && !wanted.is_error() => {
                self.convert(value, &wanted)
            }
            _ => value,
        }
    }

    /// A `foreach` nobody wrote, over a collection already bound: `..items`
    /// in a collection filled through `Add` walks `items` and gives each
    /// element to `body`, which is handed a read of it. `None` where the
    /// collection cannot be walked.
    pub(super) fn foreach_over(
        &mut self,
        collection: BoundExpression,
        span: TextSpan,
        body: impl FnOnce(&mut Self, BoundExpression) -> Option<BoundStatement>,
    ) -> Option<BoundStatement> {
        // A `dynamic` collection is walked as the `IEnumerable` the runtime
        // binder converts it to, and what it yields is `dynamic` (§13.9.5).
        let walks_dynamic = matches!(collection.ty, Type::Dynamic);
        let collection = if walks_dynamic {
            let enumerable = self.framework_type("System.Collections.IEnumerable")?;
            self.convert(collection, &enumerable)
        } else {
            collection
        };
        // An inline array is walked as the span over its elements.
        let collection = match self.binder.inline_array_of(&collection.ty) {
            Some((element, length)) => {
                let readonly = !self.is_writable_place(&collection);
                let at = collection.span;
                self.inline_array_span(collection, &element, length, readonly, at)?
            }
            None => collection,
        };
        let collection_type = collection.ty.clone();
        let item = |this: &mut Self, element: Type| {
            let local = this.declare_synthetic_local("item", element.clone());
            (
                local,
                BoundExpression::new(BoundExpressionKind::Local(local), element, span),
            )
        };
        if self.is_span_type(&collection_type) {
            let (local, read) = item(self, self.element_type_of(&collection_type));
            let body = body(self, read)?;
            let kind = self.walk_by_index(Vec::new(), Walked::Span(collection), local, body);
            return Some(BoundStatement::new(kind, span));
        }
        if let Type::Array { rank: 1, .. } = &collection_type {
            let walk = Some((
                self.declare_synthetic_local("walked", collection_type.clone()),
                self.declare_synthetic_local("at", self.special(SpecialType::Int32)),
            ));
            let (local, read) = item(self, self.element_type_of(&collection_type));
            let body = body(self, read)?;
            return Some(BoundStatement::new(
                BoundStatementKind::ForEach {
                    local,
                    collection,
                    body: Box::new(body),
                    enumeration: None,
                    walk,
                    dimensions: Vec::new(),
                },
                span,
            ));
        }
        let walked_as = match &collection_type {
            // A rectangular array is walked as the `System.Array` it is.
            Type::Array { .. } => Type::named(
                self.binder
                    .compilation()
                    .type_by_metadata_name("System.Array")?,
            ),
            other => other.clone(),
        };
        let (found, element) = self.enumeration_of(&walked_as, (collection.span, span))?;
        let element = match &collection_type {
            _ if walks_dynamic => Type::Dynamic,
            Type::Array { .. } => self.element_type_of(&collection_type),
            _ => element,
        };
        let collection = self.enumerated_as(&found, collection);
        let (local, read) = item(self, element);
        let body = body(self, read)?;
        Some(BoundStatement::new(
            BoundStatementKind::ForEach {
                local,
                collection,
                body: Box::new(body),
                enumeration: Some(Box::new(found)),
                walk: None,
                dimensions: Vec::new(),
            },
            span,
        ))
    }

    /// `foreach` over an inline array or a span as the `for` it means
    /// (Roslyn lowers both so), each element reached by index on its turn:
    ///
    /// ```text
    /// for (int at = 0; at < length; at++) { var x = walked[at]; body }
    /// ```
    ///
    /// An inline array walked across `await`s or `yield`s is reached through
    /// a span made afresh each turn; anything else is walked through the
    /// span kept in a local of its own.
    fn walk_by_index(
        &mut self,
        mut prefix: Vec<BoundStatement>,
        walked: Walked,
        local: LocalId,
        body: BoundStatement,
    ) -> BoundStatementKind {
        let span = body.span;
        let int = self.special(SpecialType::Int32);
        let at = self.declare_synthetic_local("at", int.clone());
        let read_at = BoundExpression::new(BoundExpressionKind::Local(at), int.clone(), span);
        let literal = |value: i32| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(value)),
                int.clone(),
                span,
            )
        };
        let (over, length) = match walked {
            Walked::Inline {
                place,
                element,
                length,
                readonly,
            } => {
                let Some(over) = self.inline_array_span(place, &element, length, readonly, span)
                else {
                    return BoundStatementKind::Unsupported(SyntaxKind::ForEachStatement);
                };
                (over, literal(length))
            }
            Walked::Span(collection) => {
                let ty = collection.ty.clone();
                let held = self.declare_synthetic_local("span", ty.clone());
                prefix.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: held,
                        initializer: Some(collection),
                    },
                    span,
                ));
                let read = BoundExpression::new(BoundExpressionKind::Local(held), ty, span);
                let Some(length) = self.length_of(&read, span) else {
                    return BoundStatementKind::Unsupported(SyntaxKind::ForEachStatement);
                };
                (read, length)
            }
        };
        let item = self.element_access_on(
            over,
            vec![read_at.clone()],
            SyntaxKind::ElementAccessExpression,
            span,
        );
        let (declared, by_ref) = self
            .body
            .locals
            .get(local.0 as usize)
            .map_or((Type::Error, false), |slot| (slot.ty.clone(), slot.by_ref));
        let item = if by_ref {
            item
        } else {
            self.convert(item, &declared)
        };
        let mut initializers = prefix;
        initializers.push(BoundStatement::new(
            BoundStatementKind::LocalDeclaration {
                local: at,
                initializer: Some(literal(0)),
            },
            span,
        ));
        let condition = BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::LessThan,
                left: Box::new(read_at.clone()),
                right: Box::new(length),
            },
            self.special(SpecialType::Boolean),
            span,
        );
        let step = BoundExpression::new(
            BoundExpressionKind::Increment {
                target: Box::new(read_at),
                operator: IncrementOperator::Increment,
                prefix: true,
                method: None,
            },
            int,
            span,
        );
        let turn = BoundStatement::new(
            BoundStatementKind::Block(vec![
                BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local,
                        initializer: Some(item),
                    },
                    span,
                ),
                body,
            ]),
            span,
        );
        BoundStatementKind::For {
            initializers,
            condition: Some(condition),
            incrementors: vec![step],
            body: Box::new(turn),
        }
    }

    /// A variable that can be reached again and again without evaluating
    /// anything twice: what it is reached through is kept in locals first
    /// (the object a field is read from, an array and its index), and a
    /// value that is not a variable at all is copied into one.
    fn stable_place(
        &mut self,
        place: BoundExpression,
        prefix: &mut Vec<BoundStatement>,
    ) -> BoundExpression {
        let span = place.span;
        let ty = place.ty.clone();
        match place.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::Field { receiver: None, .. } => place,
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                field,
            } => {
                let symbols = self.binder.compilation().symbols();
                let receiver = if receiver.ty.is_reference_type(symbols) {
                    self.stable_value(*receiver, prefix)
                } else {
                    self.stable_place(*receiver, prefix)
                };
                BoundExpression::new(
                    BoundExpressionKind::Field {
                        receiver: Some(Box::new(receiver)),
                        field,
                    },
                    ty,
                    span,
                )
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                let array = self.stable_value(*array, prefix);
                let indices = indices
                    .into_iter()
                    .map(|index| self.stable_value(index, prefix))
                    .collect();
                BoundExpression::new(
                    BoundExpressionKind::ArrayAccess {
                        array: Box::new(array),
                        indices,
                    },
                    ty,
                    span,
                )
            }
            kind => {
                let place = BoundExpression::new(kind, ty, span);
                let variable = self.is_variable(&place);
                let held = self.declare_synthetic_local("buffer", place.ty.clone());
                if variable && let Some(slot) = self.body.locals.get_mut(held.0 as usize) {
                    slot.by_ref = true;
                }
                prefix.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local: held,
                        initializer: Some(place.clone()),
                    },
                    span,
                ));
                BoundExpression::new(BoundExpressionKind::Local(held), place.ty, span)
            }
        }
    }

    /// A value kept in a local, unless reading it again gives the same.
    fn stable_value(
        &mut self,
        value: BoundExpression,
        prefix: &mut Vec<BoundStatement>,
    ) -> BoundExpression {
        if matches!(
            value.kind,
            BoundExpressionKind::This | BoundExpressionKind::Literal(_)
        ) {
            return value;
        }
        let span = value.span;
        let ty = value.ty.clone();
        let held = self.declare_synthetic_local("held", ty.clone());
        prefix.push(BoundStatement::new(
            BoundStatementKind::LocalDeclaration {
                local: held,
                initializer: Some(value),
            },
            span,
        ));
        BoundExpression::new(BoundExpressionKind::Local(held), ty, span)
    }

    /// Works out how to walk a collection, and what it yields.
    ///
    /// C# does not require `IEnumerable`: it looks for `GetEnumerator` by
    /// name, then for `MoveNext` and `Current` on whatever that returns. The
    /// interface is only how the collections in the library happen to provide
    /// them, which is why this searches a type *and everything it inherits*
    /// rather than testing for an interface.
    /// What `await foreach` needs (§13.9.5): the asynchronous enumerator of
    /// the collection, an awaited `MoveNextAsync`, `Current`, and an awaited
    /// `DisposeAsync` where the enumerator has one.
    ///
    /// Found in Roslyn's order: a `T?` is walked as the `T` it holds, read
    /// through `Value`; then a public `GetAsyncEnumerator` of the type,
    /// callable with nothing; then the `IAsyncEnumerable<T>` it implements,
    /// its token left to its default; then an extension (C# 9). The
    /// enumerator is disposed the way `await using` would dispose it, where
    /// it can be.
    fn async_enumeration_of(
        &mut self,
        collection: BoundExpression,
        collection_type: &Type,
    ) -> Option<AsyncEnumeration> {
        let span = collection.span;
        // An extension is asked about the collection as it was written.
        let written = collection.clone();
        let (collection, collection_type) = match self.binder.nullable_underlying(collection_type) {
            Some(inside) => {
                let value = self
                    .binder
                    .lookup_member(collection_type.symbol()?, "Value")
                    .into_iter()
                    .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)?;
                let read =
                    self.member_access(value, Some(Box::new(collection)), inside.clone(), span);
                (read, inside)
            }
            None => (collection, collection_type.clone()),
        };
        let get_enumerator = match self.pattern_call(
            collection.clone(),
            &collection_type,
            "GetAsyncEnumerator",
            span,
            true,
        ) {
            Some(call) => call,
            None => match self.async_enumerable_call(collection, &collection_type, span) {
                Some(call) => call,
                None => self.extension_call_at("GetAsyncEnumerator", written, span)?,
            },
        };
        let enumerator_type = get_enumerator.ty.clone();
        if enumerator_type.is_error() {
            return None;
        }
        let enumerator = self.declare_synthetic_local("asyncEnumerator", enumerator_type.clone());
        let read = BoundExpression::new(
            BoundExpressionKind::Local(enumerator),
            enumerator_type.clone(),
            span,
        );
        let move_next = self.pattern_call(read, &enumerator_type, "MoveNextAsync", span, true)?;
        let move_next = self.awaited(move_next, span);
        let (current, current_through) =
            self.member_through(&enumerator_type, "Current", SymbolKind::Property)?;
        let element = self.member_type(current, &current_through);
        let dispose = self.disposal_if_any(enumerator, span);
        Some(AsyncEnumeration {
            enumerator,
            get_enumerator,
            move_next,
            current,
            element,
            dispose,
        })
    }

    /// `((IAsyncEnumerable<T>)collection).GetAsyncEnumerator()`, where the
    /// collection's type is or implements `IAsyncEnumerable<T>` — once: two
    /// constructions of it leave nothing to choose between — with the token
    /// it takes left to its default.
    fn async_enumerable_call(
        &mut self,
        collection: BoundExpression,
        collection_type: &Type,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let definition = self
            .binder
            .compilation()
            .type_by_metadata_name("System.Collections.Generic.IAsyncEnumerable`1")?;
        let constructed = self.binder.constructed_from(collection_type, definition)?;
        let method = self
            .binder
            .lookup_member(definition, "GetAsyncEnumerator")
            .into_iter()
            .find(|candidate| self.kind_of(*candidate) == SymbolKind::Method)?;
        let result = self.member_type(method, &constructed);
        let arguments =
            self.convert_arguments(method, Vec::new(), &constructed, &HashMap::new(), span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(collection)),
                method,
                type_arguments: Vec::new(),
                arguments,
                virtual_call: true,
            },
            result,
            span,
        ))
    }

    /// `await foreach (var x in e) body` as the statements it means:
    ///
    /// ```text
    /// var enumerator = e.GetAsyncEnumerator();
    /// try {
    ///     while (await enumerator.MoveNextAsync()) { var x = enumerator.Current; body }
    /// } finally { await enumerator.DisposeAsync(); }
    /// ```
    fn lower_await_foreach(
        &mut self,
        enumeration: AsyncEnumeration,
        local: LocalId,
        element: Type,
        body: BoundStatement,
        span: TextSpan,
    ) -> BoundStatementKind {
        let AsyncEnumeration {
            enumerator,
            get_enumerator,
            move_next,
            current,
            element: yielded,
            dispose,
        } = enumeration;
        let enumerator_type = get_enumerator.ty.clone();
        let read = |ty: &Type| {
            BoundExpression::new(BoundExpressionKind::Local(enumerator), ty.clone(), span)
        };
        let start = BoundStatement::new(
            BoundStatementKind::Expression(BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read(&enumerator_type)),
                    value: Box::new(get_enumerator),
                },
                enumerator_type.clone(),
                span,
            )),
            span,
        );
        let value = BoundExpression::new(
            BoundExpressionKind::Property {
                receiver: Some(Box::new(read(&enumerator_type))),
                property: current,
            },
            yielded,
            span,
        );
        // The element is converted to the variable the way `foreach`
        // converts it (§13.9.5): explicitly, where it has to be.
        let value = if element.is_error() {
            value
        } else {
            self.convert_explicitly(value, &element)
        };
        let body_span = body.span;
        let step = BoundStatement::new(
            BoundStatementKind::LocalDeclaration {
                local,
                initializer: Some(value),
            },
            span,
        );
        let repeat = BoundStatement::new(
            BoundStatementKind::While {
                condition: move_next,
                body: Box::new(BoundStatement::new(
                    BoundStatementKind::Block(vec![step, body]),
                    body_span,
                )),
            },
            span,
        );
        let guarded = match dispose {
            Some(dispose) => BoundStatement::new(
                BoundStatementKind::Try {
                    body: Box::new(repeat),
                    catches: Vec::new(),
                    finally: Some(dispose),
                },
                span,
            ),
            None => repeat,
        };
        BoundStatementKind::Block(vec![start, guarded])
    }

    /// `at` is where the collection is written, and the statement it is
    /// written in: an extension `GetEnumerator` quotes the collection for a
    /// `[CallerArgumentExpression]`.
    pub(super) fn enumeration_of(
        &mut self,
        collection: &Type,
        at: (TextSpan, TextSpan),
    ) -> Option<(BoundEnumeration, Type)> {
        // Only a `GetEnumerator` that takes nothing is the pattern's (§13.9.5):
        // one with parameters leaves the type without, and an extension
        // method may still answer.
        let parameterless =
            self.member_through_where(collection, "GetEnumerator", SymbolKind::Method, |method| {
                self.is_pattern_method(method)
            });
        // One that gives nothing is no pattern, and hides whatever a base
        // declares: `new void GetEnumerator()` beside an explicit
        // `IEnumerable.GetEnumerator` walks the collection through the
        // interface (Roslyn warns that the pattern's signature is wrong).
        let parameterless = match parameterless {
            Some((method, through)) if matches!(self.member_type(method, &through), Type::Void) => {
                [
                    "System.Collections.Generic.IEnumerable`1",
                    "System.Collections.IEnumerable",
                ]
                .iter()
                .find_map(|interface| {
                    self.member_through_where(
                        collection,
                        "GetEnumerator",
                        SymbolKind::Method,
                        |method| {
                            let symbols = self.binder.compilation().symbols();
                            symbols.get(method).container.is_some_and(|container| {
                                symbols.qualified_name(container) == *interface
                            })
                        },
                    )
                })
            }
            other => other,
        };
        let mut extension_parts = (Type::Void, Vec::new());
        let (get_enumerator, through, enumerator_type, extension) = match parameterless {
            Some((get_enumerator, through)) => {
                let enumerator_type = self.member_type(get_enumerator, &through);
                (get_enumerator, through, enumerator_type, None)
            }
            // `foreach (var x in c)` where nothing on `c`'s type is
            // called `GetEnumerator` but an extension method is (C# 9).
            None => {
                let candidates = self.extensions_here("GetEnumerator");
                if candidates.is_empty() {
                    return None;
                }
                let (written, span) = at;
                let mut arguments = vec![BoundExpression::new(
                    BoundExpressionKind::Default(collection.clone()),
                    collection.clone(),
                    written,
                )];
                let Resolved {
                    method,
                    type_arguments,
                    substitution,
                } =
                    self.resolve_with_lambdas(&candidates, &mut arguments, &Type::Void, &[], true)?;
                let enumerator_type = self
                    .member_type(method, &Type::Void)
                    .substitute(&substitution);
                let mut arguments =
                    self.convert_arguments(method, arguments, &Type::Void, &substitution, span);
                let this = if arguments.is_empty() {
                    collection.clone()
                } else {
                    arguments.remove(0).ty
                };
                extension_parts = (this, arguments);
                (method, Type::Void, enumerator_type, Some(type_arguments))
            }
        };
        let (move_next, move_next_type) =
            self.member_through(&enumerator_type, "MoveNext", SymbolKind::Method)?;
        let (current, current_through) =
            self.member_through(&enumerator_type, "Current", SymbolKind::Property)?;
        let element = self.member_type(current, &current_through);
        let current_through = current_through.clone();
        // The enumerator needs somewhere to live for as long as the loop does.
        let enumerator = self.declare_synthetic_local("enumerator", enumerator_type.clone());

        // An enumerator that is an `IDisposable` is disposed through it,
        // however the loop is left, and one whose type does not say so is
        // asked at run time where a value of it still might be one: a class
        // that is not sealed, or an interface (§13.9.5.4). A `ref struct`,
        // which can be no `IDisposable`, is disposed by a `Dispose` of its
        // own it can be called with, the defaults of any optional parameters
        // given (C# 8). Anything else is not disposed at all, whatever it
        // has (Roslyn's `GetDisposalInfoForEnumerator`).
        let symbols = self.binder.compilation().symbols();
        let declared = enumerator_type.symbol().map(|symbol| symbols.get(symbol));
        let unsealed = declared.is_some_and(|declared| {
            matches!(
                declared.type_kind(),
                Some(TypeKind::Class | TypeKind::Record | TypeKind::Interface)
            ) && !declared.modifiers.contains(Modifiers::SEALED)
        });
        let ref_like = declared
            .and_then(|declared| declared.as_named_type())
            .is_some_and(|detail| detail.ref_like);
        let disposable = self.framework_type("System.IDisposable");
        let implements = disposable.as_ref().is_some_and(|disposable| {
            self.binder
                .converts_implicitly(&enumerator_type, disposable)
        });
        let mut dispose = None;
        let mut dispose_arguments = Vec::new();
        let mut dispose_checked = false;
        if (implements || unsealed)
            && let Some(disposable) = &disposable
        {
            dispose = self.member_through(disposable, "Dispose", SymbolKind::Method);
            dispose_checked = !implements;
        } else if ref_like {
            let read = BoundExpression::new(
                BoundExpressionKind::Local(enumerator),
                enumerator_type.clone(),
                at.1,
            );
            if let Some(call) = self.pattern_call(read, &enumerator_type, "Dispose", at.1, false)
                && let BoundExpressionKind::Call {
                    method, arguments, ..
                } = call.kind
                && matches!(call.ty, Type::Void)
            {
                dispose = Some((method, enumerator_type.clone()));
                dispose_arguments = arguments;
            }
        }

        Some((
            BoundEnumeration {
                enumerator,
                collection_type: through,
                get_enumerator,
                enumerator_type,
                move_next,
                move_next_type,
                current,
                current_type: current_through,
                element_type: element.clone(),
                dispose: dispose.as_ref().map(|(symbol, _)| *symbol),
                dispose_arguments,
                dispose_type: dispose.map(|(_, through)| through),
                dispose_checked,
                extension,
                extension_this: extension_parts.0,
                extension_arguments: extension_parts.1,
            },
            element,
        ))
    }

    /// Finds a member by name on a type or anything it inherits, and answers
    /// with the *constructed* type that declares it.
    ///
    /// The construction is the point: `List<string>` inherits
    /// `IEnumerable<T>.GetEnumerator` as `IEnumerable<string>`'s, and calling
    /// it needs to say which.
    /// Whether the element a loop walks reaches the iteration variable only
    /// through an operator a program declared, implicit or explicit.
    fn iterates_through_operator(&self, element: &Type, variable: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        if self.binder.special_of(variable) == Some(SpecialType::Object)
            || self.binder.nullable_underlying(element).is_some()
            || self.binder.nullable_underlying(variable).is_some()
            || matches!(element, Type::Dynamic | Type::TypeParameter(_))
            || matches!(variable, Type::Dynamic | Type::TypeParameter(_))
            || self.binder.inherits_from_public(element, variable)
            || self.binder.inherits_from_public(variable, element)
            || (element.is_reference_type(symbols)
                && variable.is_reference_type(symbols)
                && self.binder.converts_implicitly(variable, element))
        {
            return false;
        }
        if let (Some(from), Some(to)) = (
            self.binder.special_of(element),
            self.binder.special_of(variable),
        ) && from.is_numeric()
            && to.is_numeric()
        {
            return false;
        }
        self.binder.implicit_operator(element, variable).is_some()
            || self.binder.explicit_operator(element, variable).is_some()
    }

    /// Whether a `GetEnumerator` a type declares is the pattern's
    /// (§13.9.5): public, an instance method, and taking nothing. Anything
    /// else leaves the type without one, and an extension method may still
    /// answer.
    fn is_pattern_method(&self, method: SymbolId) -> bool {
        let symbols = self.binder.compilation().symbols();
        let symbol = symbols.get(method);
        matches!(symbol.accessibility, crate::symbol::Accessibility::Public)
            && !symbol.modifiers.contains(Modifiers::STATIC)
            && symbol
                .as_method()
                .is_some_and(|detail| detail.parameters.is_empty())
    }

    pub(super) fn member_through(
        &self,
        ty: &Type,
        name: &str,
        kind: SymbolKind,
    ) -> Option<(SymbolId, Type)> {
        self.member_through_where(ty, name, kind, |_| true)
    }

    /// The same, for the first member that also passes `accept`: a base's
    /// `GetEnumerator()` is still reached past a derived one that takes
    /// parameters, which overloads it rather than hiding it.
    fn member_through_where(
        &self,
        ty: &Type,
        name: &str,
        kind: SymbolKind,
        accept: impl Fn(SymbolId) -> bool,
    ) -> Option<(SymbolId, Type)> {
        let symbols = self.binder.compilation().symbols();
        let mut queue = vec![ty.clone()];
        let mut seen = std::collections::HashSet::new();
        while !queue.is_empty() {
            let current = queue.remove(0);
            let Some(symbol) = current.symbol() else {
                continue;
            };
            if !seen.insert(symbol) {
                continue;
            }
            if let Some(found) = symbols
                .lookup(symbol, name)
                .iter()
                .copied()
                .find(|candidate| symbols.get(*candidate).kind == kind && accept(*candidate))
            {
                return Some((found, current));
            }
            let substitution = self.substitution(&current);
            for base in self.binder.base_types_of(symbol) {
                queue.push(base.substitute(&substitution));
            }
        }
        None
    }

    /// What `foreach` gets out of a collection.
    pub(super) fn element_type_of(&self, collection: &Type) -> Type {
        match collection {
            Type::Array { element, .. } => (**element).clone(),
            // A generic collection's element is its first type argument, which
            // is right for every collection in the core library.
            Type::Named { type_arguments, .. } if !type_arguments.is_empty() => {
                type_arguments[0].clone()
            }
            _ => Type::Error,
        }
    }
}

/// Whether a statement awaits or yields anywhere a machine would suspend it:
/// in itself, and not in a lambda or a local function inside it, which are
/// machines (or plain methods) of their own.
fn suspends_within(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::AwaitExpression | SyntaxKind::YieldReturnStatement => true,
        SyntaxKind::SimpleLambdaExpression
        | SyntaxKind::ParenthesizedLambdaExpression
        | SyntaxKind::AnonymousMethodExpression
        | SyntaxKind::LocalFunctionStatement => false,
        // `await foreach` and `await using` await without an `await`
        // expression.
        SyntaxKind::ForEachStatement
        | SyntaxKind::UsingStatement
        | SyntaxKind::LocalDeclarationStatement
            if node
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::AwaitKeyword) =>
        {
            true
        }
        _ => node.children().any(|child| suspends_within(&child)),
    }
}
