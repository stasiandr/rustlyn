//! Element access: arrays, indexers (extension ones included), `^i` and
//! `a..b`, and what counts as a variable.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::calls::is_untyped_out;
use super::interpolation::HandlerCapture;
use super::{BodyBinder, member_parameters, passes_the_array};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, ConstantValue, ConversionKind, DynamicOperation,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Detail, MethodKind, Modifiers, RefKind, SymbolId, SymbolKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// `^k`, which is an `Index` counted from the end.
    pub(super) fn bind_from_end(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(index) = self.framework_type("System.Index") else {
            return BoundExpression::new(
                BoundExpressionKind::Unsupported(node.kind()),
                Type::Error,
                span,
            );
        };
        let int = self.special(SpecialType::Int32);
        let boolean = self.special(SpecialType::Boolean);
        let from_end = BoundExpression::new(
            BoundExpressionKind::Literal(ConstantValue::Boolean(true)),
            boolean,
            span,
        );
        let Some(operand) = node.children().find(|child| child.kind().is_expression()) else {
            return BoundExpression::error(span);
        };
        let bound = self.bind_expression(&operand);
        // `^n` on an `int?` is an `Index?` (§12.9.6 lifted), null where `n`
        // is, as Roslyn lowers it — with its two shortcuts: an operand that
        // never has a value is `default(int)` (so `^new int?()` is `^0`, not
        // null), and one that always has one is that value.
        if self.binder.nullable_underlying(&bound.ty).is_some() {
            let lifted = self.nullable_of(index.clone());
            let operand = match self.nullable_shortcut(bound) {
                Ok(value) => value,
                Err(nullable) => {
                    return self
                        .lift_conversion(*nullable, &lifted, |this, inner| {
                            let inner = this.convert(inner, &int);
                            this.make(&index, vec![inner, from_end.clone()], span)
                                .unwrap_or_else(|| BoundExpression::error(span))
                        })
                        .unwrap_or_else(|| BoundExpression::error(span));
                }
            };
            let value = self.convert(operand, &int);
            let made = self
                .make(&index, vec![value, from_end], span)
                .unwrap_or_else(|| BoundExpression::error(span));
            return self.convert(made, &lifted);
        }
        let value = self.convert(bound, &int);
        self.make(&index, vec![value, from_end], span)
            .unwrap_or_else(|| BoundExpression::error(span))
    }

    /// Roslyn's two shortcuts for a nullable operand of `^` and `..`: one
    /// that never has a value (`null`, `default`, `new T?()`) is the
    /// underlying type's default, and one that always has one (`T` made
    /// nullable, `new T?(v)`) is that value; `Err` gives back any other,
    /// which is lifted.
    fn nullable_shortcut(
        &mut self,
        value: BoundExpression,
    ) -> Result<BoundExpression, Box<BoundExpression>> {
        let Some(underlying) = self.binder.nullable_underlying(&value.ty) else {
            return Ok(value);
        };
        let never = match &value.kind {
            BoundExpressionKind::Default(_) => true,
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } => arguments.is_empty() && initializers.is_empty(),
            BoundExpressionKind::Conversion { operand, .. } => {
                matches!(operand.ty, Type::Null)
            }
            _ => matches!(value.constant(), Some(ConstantValue::Null)),
        };
        if never {
            return Ok(BoundExpression::new(
                BoundExpressionKind::Default(underlying.clone()),
                underlying,
                value.span,
            ));
        }
        match value.kind {
            BoundExpressionKind::Conversion {
                operand,
                conversion: ConversionKind::NullableWrap,
                ..
            } => Ok(*operand),
            BoundExpressionKind::ObjectCreation { arguments, .. } if arguments.len() == 1 => {
                Ok(arguments
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| BoundExpression::error(value.span)))
            }
            kind => Err(Box::new(BoundExpression::new(kind, value.ty, value.span))),
        }
    }

    /// `a..b`, `a..`, `..b` and `..`, which are all `Range`s.
    pub(super) fn bind_range(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let (Some(range), Some(index)) = (
            self.framework_type("System.Range"),
            self.framework_type("System.Index"),
        ) else {
            // No range to make, but what it would be made of is still there
            // to be asked about.
            for child in node.children().filter(|child| child.kind().is_expression()) {
                self.bind_expression(&child);
            }
            return BoundExpression::new(
                BoundExpressionKind::Unsupported(node.kind()),
                Type::Error,
                span,
            );
        };
        // The dots are a token, so which side is written is decided by where
        // each operand sits relative to them.
        let dots = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::DotDotToken)
            .map(|token| token.span().start());
        let mut start = None;
        let mut end = None;
        let lifted_index = self.nullable_of(index.clone());
        let mut lifting = false;
        for child in node.children().filter(|child| child.kind().is_expression()) {
            let before = dots.is_some_and(|dots| child.span().start() < dots);
            let bound = self.bind_expression(&child);
            // A nullable operand makes the range a `Range?`, null where
            // either side is (lifted), less Roslyn's shortcuts for one that
            // never or always has a value.
            let bound = if self.binder.nullable_underlying(&bound.ty).is_some() {
                let bound = self.convert(bound, &lifted_index);
                match self.nullable_shortcut(bound) {
                    Ok(value) => self.convert(value, &index),
                    Err(nullable) => {
                        lifting = true;
                        *nullable
                    }
                }
            } else {
                self.convert(bound, &index)
            };
            if before {
                start = Some(bound)
            } else {
                end = Some(bound)
            }
        }
        if lifting {
            return self
                .lift_range(&range, start, end, span)
                .unwrap_or_else(|| BoundExpression::error(span));
        }
        match (start, end) {
            (Some(start), Some(end)) => self.make(&range, vec![start, end], span),
            (Some(start), None) => self.call_static(&range, "StartAt", vec![start], span),
            (None, Some(end)) => self.call_static(&range, "EndAt", vec![end], span),
            (None, None) => range.symbol().and_then(|symbol| {
                let found = self.binder.lookup_member(symbol, "All").first().copied()?;
                Some(BoundExpression::new(
                    BoundExpressionKind::Property {
                        receiver: None,
                        property: found,
                    },
                    range.clone(),
                    span,
                ))
            }),
        }
        .unwrap_or_else(|| BoundExpression::error(span))
    }

    /// `a..b` with an `Index?` on either side: both are held, and the
    /// range is made of their values where both have one, and is null
    /// otherwise (§12.4.8).
    fn lift_range(
        &mut self,
        range: &Type,
        start: Option<BoundExpression>,
        end: Option<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let lifted = self.nullable_of(range.clone());
        let boolean = self.special(SpecialType::Boolean);
        let mut steps = Vec::new();
        let mut condition: Option<BoundExpression> = None;
        let mut operands = Vec::new();
        for operand in [start, end] {
            let Some(operand) = operand else {
                operands.push(None);
                continue;
            };
            let held = self.held(operand, &mut steps, span);
            if self.binder.nullable_underlying(&held.ty).is_some() {
                let has_value = self.property_of(held.clone(), "HasValue", span)?;
                condition = Some(match condition {
                    None => has_value,
                    Some(before) => BoundExpression::new(
                        BoundExpressionKind::Binary {
                            operator: BinaryOperator::LogicalAnd,
                            left: Box::new(before),
                            right: Box::new(has_value),
                        },
                        boolean.clone(),
                        span,
                    ),
                });
                operands.push(Some(self.call_on(
                    held,
                    "GetValueOrDefault",
                    Vec::new(),
                    span,
                )?));
            } else {
                operands.push(Some(held));
            }
        }
        let made = match (operands.remove(0), operands.remove(0)) {
            (Some(start), Some(end)) => self.make(range, vec![start, end], span)?,
            (Some(start), None) => self.call_static(range, "StartAt", vec![start], span)?,
            (None, Some(end)) => self.call_static(range, "EndAt", vec![end], span)?,
            (None, None) => return None,
        };
        let made = self.convert(made, &lifted);
        let conditional = BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(condition?),
                consequence: Box::new(made),
                alternative: Box::new(BoundExpression::new(
                    BoundExpressionKind::Default(lifted.clone()),
                    lifted.clone(),
                    span,
                )),
            },
            lifted.clone(),
            span,
        );
        steps.push(conditional);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            lifted,
            span,
        ))
    }

    /// An array receiver seen as the `System.Array` it derives from.
    ///
    /// `int[,]` has no symbol of its own, and the members it has that are not
    /// `Length` — `GetLength`, `Rank`, `Clone` — are `System.Array`'s. The
    /// receiver itself does not change: the runtime lets an array stand
    /// wherever an `Array` is wanted. `None` where `System.Array` has no such
    /// member either, so that `numbers.Select(...)` still reaches the
    /// extension method it was written for.
    pub(super) fn as_system_array(&self, receiver: &BoundExpression, name: &str) -> Option<Type> {
        if !matches!(receiver.ty, Type::Array { .. }) {
            return None;
        }
        let array = self.framework_type("System.Array")?;
        let symbol = array.symbol()?;
        // Its static ones do not count: `_arities.BinarySearch(arity)` on an
        // `int[]` is an extension method, not `Array.BinarySearch` called on
        // a value.
        self.binder
            .lookup_member(symbol, name)
            .iter()
            .any(|member| !self.is_static(*member))
            .then_some(array)
    }

    /// Whether an expression is a variable something can be written through:
    /// a local, a parameter not passed `in`, a field of one (or of a
    /// reference), an array element, what a pointer points at. Anything else
    /// is a value, and a span over it has to be over a copy.
    pub(super) fn is_writable_place(&self, expression: &BoundExpression) -> bool {
        self.is_place(expression, true)
    }

    /// Whether an expression is a variable at all, read-only ones included:
    /// an `in` parameter, a `readonly` field. A span over one of those is
    /// over the variable itself, and sees what is written to it later.
    pub(super) fn is_variable(&self, expression: &BoundExpression) -> bool {
        self.is_place(expression, false)
    }

    fn is_place(&self, expression: &BoundExpression, writable: bool) -> bool {
        let symbols = self.binder.compilation().symbols();
        // A member that hands back a reference (`ref T this[int]` of a span,
        // `ref T M()`) names the variable it points at.
        let returns_reference = |member: SymbolId| {
            let symbol = symbols.get(member);
            let readonly = match &symbol.detail {
                Detail::Method(detail) => detail.returns_readonly,
                Detail::Property(detail) => detail.returns_readonly,
                _ => true,
            };
            let mut sink = Diagnostics::new();
            (!readonly || !writable)
                && (symbol.modifiers.contains(Modifiers::REF)
                    || matches!(self.binder.type_of(member, &mut sink), Type::ByRef(_)))
        };
        match &expression.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::ArrayAccess { .. }
            | BoundExpressionKind::Dereference { .. }
            | BoundExpressionKind::This => true,
            BoundExpressionKind::Parameter(parameter) => symbols
                .get(*parameter)
                .as_parameter()
                .is_some_and(|detail| !writable || detail.ref_kind != RefKind::In),
            BoundExpressionKind::Field { receiver, field } => {
                // A `readonly` field is written in the constructor of its
                // type, and nowhere else.
                let container = symbols.get(*field).container;
                let in_own_constructor = self.member.is_some_and(|member| {
                    symbols.get(member).container == container
                        && symbols.get(member).as_method().is_some_and(|detail| {
                            matches!(
                                detail.method_kind,
                                MethodKind::Constructor | MethodKind::StaticConstructor
                            )
                        })
                });
                (!writable
                    || !symbols.get(*field).modifiers.contains(Modifiers::READONLY)
                    || in_own_constructor)
                    && receiver.as_ref().is_none_or(|receiver| {
                        receiver.ty.is_reference_type(symbols) || self.is_place(receiver, writable)
                    })
            }
            BoundExpressionKind::IndexerAccess { indexer, .. } => returns_reference(*indexer),
            BoundExpressionKind::Property { property, .. } => returns_reference(*property),
            BoundExpressionKind::Call { method, .. } => returns_reference(*method),
            BoundExpressionKind::Sequence(steps) => steps
                .last()
                .is_some_and(|last| self.is_place(last, writable)),
            _ => false,
        }
    }

    /// Whether an expression is a reference a member handed back, `ref` or
    /// `ref readonly`.
    pub(super) fn is_returned_reference(&self, expression: &BoundExpression) -> bool {
        let member = match &expression.kind {
            BoundExpressionKind::IndexerAccess { indexer, .. } => *indexer,
            BoundExpressionKind::Property { property, .. } => *property,
            BoundExpressionKind::Call { method, .. } => *method,
            _ => return false,
        };
        let mut sink = Diagnostics::new();
        self.binder
            .compilation()
            .symbols()
            .get(member)
            .modifiers
            .contains(Modifiers::REF)
            || matches!(self.binder.type_of(member, &mut sink), Type::ByRef(_))
    }

    pub(super) fn bind_element_access(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(target) = node.children().next() else {
            return BoundExpression::error(span);
        };
        let receiver = self.bind_expression(&target);
        let list = node.child_of_kind(SyntaxKind::BracketedArgumentList);
        let indices = list
            .as_ref()
            .map(|list| self.bind_argument_list(list))
            .unwrap_or_default();
        let mut names = list.as_ref().map(Self::argument_names).unwrap_or_default();
        // `ia.P[i]`: a property with parameters of a `[ComImport]` type that
        // is not its indexer is an indexed property (Roslyn's
        // `IsIndexedProperty`), reached as an indexer is, under its name.
        if let BoundExpressionKind::Property {
            receiver: Some(inner),
            property,
        } = &receiver.kind
            && self.is_indexed_property(*property)
        {
            let (inner, property) = ((**inner).clone(), *property);
            let ty = inner.ty.clone();
            names.resize(indices.len(), None);
            return self.indexer_access(inner, &ty, &[property], indices, &names, span);
        }
        self.element_access_named(receiver, indices, names, node.kind(), span)
    }

    /// Whether a property is an indexed property: one with parameters,
    /// declared by a `[ComImport]` type, that is not `this[...]`.
    pub(super) fn is_indexed_property(&self, property: SymbolId) -> bool {
        let symbols = self.binder.compilation().symbols();
        let symbol = symbols.get(property);
        symbol
            .as_property()
            .is_some_and(|detail| !detail.is_indexer && !detail.parameters.is_empty())
            && symbol
                .container
                .is_some_and(|container| self.binder.is_com_import(container))
    }

    /// `receiver[indices]`, once both are bound: an array element, a pointer
    /// offset, or an indexer of the receiver's type.
    pub(super) fn element_access_on(
        &mut self,
        receiver: BoundExpression,
        indices: Vec<BoundExpression>,
        kind: SyntaxKind,
        span: TextSpan,
    ) -> BoundExpression {
        let names = vec![None; indices.len()];
        self.element_access_named(receiver, indices, names, kind, span)
    }

    /// The same, with the name each index was given: the runtime binder
    /// reads them, and a statically bound indexer takes each index where its
    /// name says.
    pub(super) fn element_access_named(
        &mut self,
        receiver: BoundExpression,
        indices: Vec<BoundExpression>,
        mut names: Vec<Option<String>>,
        kind: SyntaxKind,
        span: TextSpan,
    ) -> BoundExpression {
        names.resize(indices.len(), None);
        // `a[^1]` and `a[1..3]` are not indexing by an `Index` or a `Range`
        // unless the type says it can be: everything else is counted, and the
        // language turns the one into the other. The receiver is evaluated
        // once, which is what the local is for. An inline array is indexed
        // through the span over it whatever members it declares (§12.8.12.3),
        // and the span counts.
        if let [only] = &indices[..]
            && self.binder.inline_array_of(&receiver.ty).is_none()
            && !matches!(only.kind, BoundExpressionKind::UnboundCreation(_))
            && let Some(lowered) = self.bind_counted_access(&receiver, only, span)
        {
            return lowered;
        }

        // `d[i]`, and `c[d]` on a type with an indexer, are the runtime
        // binder's to resolve (§12.8.12.3).
        // A span and an inline array cannot be boxed for the runtime binder
        // to look at: their indexers take the index converted to an `int`.
        let unboxable = self.binder.inline_array_of(&receiver.ty).is_some()
            || receiver.ty.symbol().is_some_and(|symbol| {
                self.binder
                    .compilation()
                    .symbols()
                    .get(symbol)
                    .as_named_type()
                    .is_some_and(|detail| detail.ref_like)
            });
        if matches!(receiver.ty, Type::Dynamic)
            || (!matches!(receiver.ty, Type::Array { .. } | Type::Pointer(_))
                && !unboxable
                && Self::has_dynamic_argument(&indices))
        {
            return Self::dynamic_operation(
                DynamicOperation::GetIndex,
                Some(receiver),
                indices,
                names,
                Type::Dynamic,
                span,
            );
        }
        match receiver.ty.clone() {
            Type::Array { element, .. } => {
                // A `dynamic` index is converted to an `int` when it is used,
                // as an array index, and a bare `default` is the `int` zero.
                let int = self.special(SpecialType::Int32);
                let indices = indices
                    .into_iter()
                    .map(|index| {
                        if matches!(index.ty, Type::Dynamic) {
                            Self::dynamic_array_index(index, &int)
                        } else if index.ty.is_error()
                            && matches!(index.kind, BoundExpressionKind::Default(_))
                        {
                            self.convert(index, &int)
                        } else {
                            index
                        }
                    })
                    .collect();
                BoundExpression::new(
                    BoundExpressionKind::ArrayAccess {
                        array: Box::new(receiver),
                        indices,
                    },
                    *element,
                    span,
                )
            }
            // `p[i]` is `*(p + i)`, which is what the language says it is
            // and not an indexer on anything.
            Type::Pointer(element) => {
                // Reading through a pointer is what makes code unsafe; with
                // the memory safety rules of C# 15 naming a pointer type is
                // not (CS9360 at the `[`).
                if !self.in_unsafe_context(span) {
                    if self.language_version().at_least(LanguageVersion::Preview) {
                        let bracket = self
                            .syntax_at(span)
                            .and_then(|node| node.child_of_kind(SyntaxKind::BracketedArgumentList))
                            .and_then(|list| list.first_token())
                            .map_or(span, |token| token.span());
                        self.report(ErrorCode::ErrUnsafeOperation, bracket, &[]);
                    } else {
                        // Before, it is the pointer itself that is unsafe.
                        self.report(ErrorCode::ErrUnsafeNeeded, receiver.span, &[]);
                    }
                }
                let pointer = receiver.ty.clone();
                let Some(index) = indices.into_iter().next() else {
                    return BoundExpression::error(span);
                };
                let _ = kind;
                let moved = BoundExpression::new(
                    BoundExpressionKind::Binary {
                        operator: BinaryOperator::Add,
                        left: Box::new(receiver),
                        right: Box::new(index),
                    },
                    pointer,
                    span,
                );
                BoundExpression::new(
                    BoundExpressionKind::Dereference {
                        operand: Box::new(moved),
                    },
                    *element,
                    span,
                )
            }
            Type::Error => BoundExpression::error(span),
            // A tuple's indexer is its `ValueTuple`'s, where a program
            // declares one.
            Type::Tuple(elements) => {
                let named = self.tuple_as_named(&elements);
                if named.symbol().is_none() {
                    return BoundExpression::error(span);
                }
                let receiver = BoundExpression::new(receiver.kind, named, receiver.span);
                self.element_access_on(receiver, indices, kind, span)
            }
            other => {
                // `buffer[i]` on an inline array reads the span over its
                // elements: bounds are checked, `^1` and ranges work, and
                // writing through it writes the element.
                // Only one index that is an `int`, an `Index` or a `Range`
                // (or reaches one implicitly) is the inline array's: `b[(nint)0]`
                // is an indexer the struct declares, where it declares one.
                let inline_index = |this: &Self| {
                    let [index] = indices.as_slice() else {
                        return false;
                    };
                    if names.iter().any(Option::is_some) {
                        return false;
                    }
                    let int = this.special(SpecialType::Int32);
                    this.binder.converts_implicitly(&index.ty, &int)
                        || this.constant_fits(index, &int)
                        || ["System.Index", "System.Range"].iter().any(|name| {
                            this.framework_type(name)
                                .is_some_and(|ty| this.binder.converts_implicitly(&index.ty, &ty))
                        })
                };
                let declares_indexer = other
                    .symbol()
                    .is_some_and(|symbol| !self.binder.lookup_member(symbol, "this[]").is_empty());
                if let Some((element, length)) = self.binder.inline_array_of(&other)
                    && (inline_index(self) || !declares_indexer)
                {
                    let readonly = !self.is_writable_place(&receiver);
                    let Some(over) =
                        self.inline_array_span(receiver, &element, length, readonly, span)
                    else {
                        return BoundExpression::error(span);
                    };
                    return self.element_access_on(over, indices, kind, span);
                }
                let Some(symbol) = other.symbol() else {
                    let found = self.display(&other);
                    self.report(ErrorCode::ErrBadIndexLHS, span, &[&found]);
                    return BoundExpression::error(span);
                };
                let indexers = self.binder.lookup_member(symbol, "this[]");
                self.indexer_access(receiver, &other, &indexers, indices, &names, span)
            }
        }
    }

    /// `receiver[indices]` through one of `indexers`, which are the
    /// indexers of `other`, the receiver's type — or an indexed property
    /// of a `[ComImport]` type, `ia.P[i]`, which is reached the same way.
    fn indexer_access(
        &mut self,
        receiver: BoundExpression,
        other: &Type,
        indexers: &[SymbolId],
        indices: Vec<BoundExpression>,
        names: &[Option<String>],
        span: TextSpan,
    ) -> BoundExpression {
        let other = other.clone();
        // `p[inP: 2]` names a parameter, as a call may: only an indexer that
        // has it is meant, and the indices go where the names say.
        let indexers = self.named_candidates(indexers, names);
        let mut indices = self.reorder_named(&indexers, names, indices, &other);
        let picked = self.pick_indexer(&indexers, &indices, &other);
        // An indexer the type has wins where it takes the indices; only where
        // none does is an extension block's (C# 14) looked for, which takes
        // the receiver as its first parameter.
        let mut skip = 0;
        let mut inferred: HashMap<SymbolId, Type> = HashMap::new();
        let mut chosen = picked.map(|(indexer, _)| indexer);
        if !picked.is_some_and(|(_, fits)| fits)
            && let Some((indexer, found, ordered)) =
                self.extension_indexer(&receiver, &indices, names, false)
        {
            chosen = Some(indexer);
            inferred = found;
            indices = ordered;
            skip = 1;
        }
        match chosen {
            Some(indexer) => {
                // CS0121 where two indexers fit the indices and neither is
                // better, as two methods do.
                if skip == 0 && names.iter().all(Option::is_none) {
                    self.report_if_ambiguous(
                        indexer,
                        &indexers,
                        &indices,
                        &other,
                        &[],
                        false,
                        span,
                    );
                }
                let ty = if skip == 1 {
                    let mut sink = Diagnostics::new();
                    self.binder
                        .type_of(indexer, &mut sink)
                        .value()
                        .substitute(&inferred)
                } else {
                    self.member_type(indexer, &other)
                };
                // `token[2]` on a `this[object key]` boxes the `2`:
                // each index converts to the parameter it is for.
                let parameters: Vec<SymbolId> = self
                    .binder
                    .compilation()
                    .symbols()
                    .get(indexer)
                    .as_property()
                    .map(|detail| detail.parameters.iter().copied().skip(skip).collect())
                    .unwrap_or_default();
                // An extension block's indexer takes its receiver as its first
                // parameter, which a handler may be made with by name.
                let all_parameters: Vec<SymbolId> = self
                    .binder
                    .compilation()
                    .symbols()
                    .get(indexer)
                    .as_property()
                    .map(|detail| detail.parameters.clone())
                    .unwrap_or_default();
                let mut receiver = receiver;
                if skip == 1 {
                    receiver = self.extension_receiver(receiver, indexer, &inferred);
                }
                let indices = self.pack_params_indices(indexer, indices, &other, skip, span);
                let indices: Vec<BoundExpression> = if parameters.len() >= indices.len() {
                    let given: Vec<Option<TextSpan>> =
                        indices.iter().map(|index| Some(index.span)).collect();
                    // An interpolated string given to a handler may be
                    // made with the indices before it and the receiver
                    // (C# 10), as a call's arguments may.
                    let mut converted: Vec<BoundExpression> = Vec::with_capacity(indices.len() + 1);
                    if skip == 1 {
                        converted.push(receiver.clone());
                    }
                    let mut capture = HandlerCapture::default();
                    for (index, parameter) in indices.into_iter().zip(parameters.iter().copied()) {
                        let wanted = self.member_type(parameter, &other).substitute(&inferred);
                        let made =
                            if index.is_interpolated_string() && self.is_handler_type(&wanted) {
                                let at = converted.len();
                                self.handler_argument(
                                    index,
                                    &wanted,
                                    parameter,
                                    at,
                                    if skip == 1 {
                                        &all_parameters
                                    } else {
                                        &parameters
                                    },
                                    &mut converted,
                                    &mut capture,
                                    &other,
                                )
                            } else if is_untyped_out(&index, &self.body.locals) {
                                // `ia[out var x]`: the variable is of the
                                // type the parameter says.
                                self.give_out_a_type(index, &wanted)
                            } else {
                                self.convert(index, &wanted)
                            };
                        converted.push(made);
                    }
                    self.pending_receiver = capture.receiver;
                    // The receiver, which a handler may have kept.
                    if skip == 1 {
                        receiver = converted.remove(0);
                    }
                    // The parameters left unwritten take their
                    // defaults, caller information included — the
                    // ones of the accessor that is called, which an
                    // override that left it out inherits.
                    let written_only = self.is_assigned_to(span);
                    let owner = self.accessor_owner(indexer, written_only);
                    let symbols = self.binder.compilation().symbols();
                    // An indexer read from metadata has its defaults
                    // on each accessor, and the two may differ: a
                    // write takes the setter's.
                    let accessor = symbols
                        .get(owner)
                        .as_property()
                        .filter(|_| self.binder.compilation().is_from_metadata(owner))
                        .and_then(|detail| {
                            if written_only {
                                detail.setter
                            } else {
                                detail.getter
                            }
                        })
                        .and_then(|accessor| symbols.get(accessor).as_method())
                        .map(|detail| detail.parameters.clone())
                        .filter(|found| found.len() >= parameters.len())
                        .map(|found| found[..parameters.len()].to_vec());
                    let defaults = accessor
                        .or_else(|| {
                            symbols
                                .get(owner)
                                .as_property()
                                .map(|detail| {
                                    detail.parameters.iter().copied().skip(skip).collect()
                                })
                                .filter(|found: &Vec<SymbolId>| found.len() == parameters.len())
                        })
                        .unwrap_or_else(|| parameters.clone());
                    for parameter in defaults.iter().skip(converted.len()) {
                        let wanted = self.member_type(*parameter, &other).substitute(&inferred);
                        match self.default_argument(*parameter, &wanted, span, &given) {
                            Some(filled) => converted.push(filled),
                            None => break,
                        }
                    }
                    // `this[in int x]` takes the address of its
                    // argument, as a method's `in` does, and the
                    // call site writes no `in` — a default filled
                    // in above included. A `[ComImport]` type's
                    // `ref` parameter takes the address of a copy
                    // where no `ref` was written.
                    let com = self.omits_refs(indexer);
                    let symbols = self.binder.compilation().symbols();
                    converted
                        .into_iter()
                        .zip(parameters.iter().copied())
                        .map(|(argument, parameter)| {
                            let takes = symbols
                                .get(parameter)
                                .as_parameter()
                                .map_or(RefKind::None, |detail| detail.ref_kind);
                            if matches!(argument.kind, BoundExpressionKind::RefArgument { .. }) {
                                return argument;
                            }
                            let (ty, span) = (argument.ty.clone(), argument.span);
                            let operand = match takes {
                                RefKind::In => argument,
                                RefKind::Ref if com => BoundExpression::new(
                                    BoundExpressionKind::Conversion {
                                        operand: Box::new(argument),
                                        conversion: ConversionKind::Identity,
                                        written: false,
                                    },
                                    ty.clone(),
                                    span,
                                ),
                                _ => return argument,
                            };
                            BoundExpression::new(
                                BoundExpressionKind::RefArgument {
                                    kind: takes,
                                    operand: Box::new(operand),
                                },
                                ty,
                                span,
                            )
                        })
                        .collect()
                } else {
                    indices
                };
                let receiver = self.capture_receiver(receiver);
                BoundExpression::new(
                    BoundExpressionKind::IndexerAccess {
                        receiver: Box::new(receiver),
                        indexer,
                        arguments: indices,
                    },
                    ty,
                    span,
                )
            }
            None => {
                let found = self.display(&other);
                self.report(ErrorCode::ErrBadIndexLHS, span, &[&found]);
                BoundExpression::error(span)
            }
        }
    }

    /// The indexer the indices fit: `DefinitionIndex<T>` has a `this[int]`
    /// that gives a `T` and a `this[T]` that gives an `int`, and only the
    /// arguments say which was meant. The first declared is the fallback,
    /// so that a call that fits none is still reported against something.
    fn pick_indexer(
        &self,
        indexers: &[SymbolId],
        indices: &[BoundExpression],
        receiver: &Type,
    ) -> Option<(SymbolId, bool)> {
        // Overload resolution picks among indexers as among methods
        // (§12.8.12.3), `in` and tie-breaks and all.
        let types: Vec<Type> = indices.iter().map(|index| index.ty.clone()).collect();
        let evidence = self.evidence(indices);
        if let Some(indexer) = self.resolve_overload(indexers, &types, &evidence, receiver) {
            // Resolution reaches the slot an override fills, the one first
            // declared; the override nearest the receiver is the one whose
            // defaults the call takes (the list is nearest first).
            let symbols = self.binder.compilation().symbols();
            let signature = |candidate: SymbolId| -> Vec<Type> {
                symbols
                    .get(candidate)
                    .as_property()
                    .map(|detail| {
                        detail
                            .parameters
                            .iter()
                            .map(|parameter| self.member_type(*parameter, receiver))
                            .collect()
                    })
                    .unwrap_or_default()
            };
            let wanted = signature(indexer);
            let nearest = indexers.iter().copied().find(|candidate| {
                *candidate == indexer
                    || (symbols
                        .get(*candidate)
                        .modifiers
                        .contains(Modifiers::OVERRIDE)
                        && signature(*candidate) == wanted)
            });
            return Some((nearest.unwrap_or(indexer), true));
        }
        let symbols = self.binder.compilation().symbols();
        let mut best: Option<((bool, usize, usize), SymbolId)> = None;
        for indexer in indexers {
            let Some(parameters) = symbols
                .get(*indexer)
                .as_property()
                .map(|detail| detail.parameters.clone())
            else {
                continue;
            };
            // An index written without `in` is better passed by value, and
            // one written with it better to an `in` parameter (§12.6.4.5).
            let passing = parameters
                .iter()
                .zip(indices)
                .filter(|(parameter, index)| {
                    let takes_in = symbols
                        .get(**parameter)
                        .as_parameter()
                        .is_some_and(|detail| detail.ref_kind == RefKind::In);
                    takes_in == matches!(index.kind, BoundExpressionKind::RefArgument { .. })
                })
                .count();
            // Trailing parameters with defaults may go unwritten, as a
            // method's may.
            let optional = |parameter: &SymbolId| {
                symbols
                    .get(*parameter)
                    .as_parameter()
                    .is_some_and(|detail| detail.has_default)
            };
            let fits_one = |index: &BoundExpression, wanted: &Type| {
                // A lambda converts to a delegate type, or through the type
                // it has on its own (C# 10) to `Delegate` or `Expression`.
                if matches!(index.kind, BoundExpressionKind::UnboundLambda(_)) {
                    return self.is_function_target(wanted)
                        || (self.takes_a_function_type(wanted, true)
                            && self.may_have_natural_type(index));
                }
                self.binder.converts_implicitly(&index.ty, wanted)
                    || self.constant_fits(index, wanted)
                    // `[new()]` is whatever the parameter wants.
                    || matches!(index.kind, BoundExpressionKind::UnboundCreation(_))
            };
            let ref_kind = |parameter: &SymbolId| {
                symbols
                    .get(*parameter)
                    .as_parameter()
                    .map_or(RefKind::None, |detail| detail.ref_kind)
            };
            let written = |index: &BoundExpression| match &index.kind {
                BoundExpressionKind::RefArgument { kind, .. } => *kind,
                _ => RefKind::None,
            };
            // `p[x]` fits `this[in int]` too.
            let mut exact = 0;
            let normal = parameters.len() >= indices.len()
                && parameters[indices.len()..].iter().all(optional)
                && parameters.iter().zip(indices).all(|(parameter, index)| {
                    let wanted = self.member_type(*parameter, receiver);
                    if wanted == index.ty {
                        exact += 1;
                    }
                    super::overloads::ref_fits(
                        written(index),
                        Some(ref_kind(parameter)),
                        self.language_version()
                            .at_least(rustlyn_syntax::LanguageVersion::CSharp12),
                    ) && fits_one(index, &wanted)
                });
            // `this[params int[] values]` takes its indices one by one too,
            // and in that form ranks below any indexer taking them as they
            // are (§12.6.4.2).
            let fits = normal || {
                let types: Vec<Type> = parameters
                    .iter()
                    .map(|parameter| self.member_type(*parameter, receiver))
                    .collect();
                exact = 0;
                self.params_element(*indexer, &types)
                    .is_some_and(|element| {
                        let fixed = types.len() - 1;
                        indices.len() >= fixed
                            && types.iter().zip(&indices[..fixed]).all(|(wanted, index)| {
                                if *wanted == index.ty {
                                    exact += 1;
                                }
                                fits_one(index, wanted)
                            })
                            && indices[fixed..]
                                .iter()
                                .all(|index| fits_one(index, &element))
                    })
            };
            let score = (normal, exact, passing);
            if fits && best.is_none_or(|(known, _)| score > known) {
                best = Some((score, *indexer));
            }
        }
        best.map(|(_, indexer)| (indexer, true))
            .or_else(|| indexers.first().map(|first| (*first, false)))
    }

    /// The receiver of an extension block's (C# 14) indexer or property, as
    /// the block takes it: boxed where the block extends a reference type,
    /// or made a span where it extends one.
    pub(super) fn extension_receiver(
        &mut self,
        receiver: BoundExpression,
        member: SymbolId,
        inferred: &HashMap<SymbolId, Type>,
    ) -> BoundExpression {
        let Some(first) = self
            .binder
            .compilation()
            .symbols()
            .get(member)
            .as_property()
            .and_then(|detail| detail.parameters.first().copied())
        else {
            return receiver;
        };
        let mut sink = Diagnostics::new();
        let taken = self.binder.type_of(first, &mut sink).substitute(inferred);
        if receiver.ty == taken || taken.is_error() {
            return receiver;
        }
        let symbols = self.binder.compilation().symbols();
        let boxes = !matches!(
            receiver.ty,
            Type::TypeParameter(_) | Type::Error | Type::Null
        ) && !receiver.ty.is_reference_type(symbols)
            && !matches!(taken, Type::TypeParameter(_))
            && taken.is_reference_type(symbols);
        if self.binder.span_parts(&taken).is_some() || boxes {
            return self.convert(receiver, &taken);
        }
        receiver
    }

    /// Whether the expression at `span` is the target of a simple
    /// assignment, which writes it without reading it.
    fn is_assigned_to(&self, span: TextSpan) -> bool {
        let Some(node) = self.syntax_at(span) else {
            return false;
        };
        node.parent().is_some_and(|parent| {
            parent.kind() == SyntaxKind::SimpleAssignmentExpression
                && parent
                    .children()
                    .next()
                    .is_some_and(|left| left.span() == span)
        })
    }

    /// The property whose getter (or setter) a call through `property`
    /// reaches: its own, or, where an override left that accessor out, the
    /// one it overrides.
    fn accessor_owner(&self, property: SymbolId, setter: bool) -> SymbolId {
        let symbols = self.binder.compilation().symbols();
        let mut current = property;
        for _ in 0..16 {
            let symbol = symbols.get(current);
            let Some(detail) = symbol.as_property() else {
                return current;
            };
            let present = if setter {
                detail.has_set || detail.has_init
            } else {
                detail.has_get
            };
            if present || !symbol.modifiers.contains(Modifiers::OVERRIDE) {
                return current;
            }
            let count = detail.parameters.len();
            let Some(base) = symbol
                .container
                .and_then(|container| self.binder.base_class_of(container))
                .and_then(|base| base.symbol())
            else {
                return current;
            };
            let Some(found) = self
                .binder
                .lookup_member(base, &symbol.name)
                .into_iter()
                .find(|candidate| {
                    symbols
                        .get(*candidate)
                        .as_property()
                        .is_some_and(|detail| detail.parameters.len() == count)
                })
            else {
                return current;
            };
            current = found;
        }
        current
    }

    /// The indices given for a `params` indexer in its expanded form, with
    /// the ones past its fixed parameters made into the collection it takes.
    fn pack_params_indices(
        &mut self,
        indexer: SymbolId,
        indices: Vec<BoundExpression>,
        receiver: &Type,
        skip: usize,
        span: TextSpan,
    ) -> Vec<BoundExpression> {
        let parameters: Vec<Type> = member_parameters(self.binder.compilation().symbols(), indexer)
            .unwrap_or_default()
            .iter()
            .skip(skip)
            .copied()
            .map(|parameter| self.member_type(parameter, receiver))
            .collect();
        let Some(element) = self.params_element(indexer, &parameters) else {
            return indices;
        };
        if passes_the_array(self.binder, &indices, &parameters) {
            return indices;
        }
        let fixed = parameters.len() - 1;
        if indices.len() < fixed {
            return indices;
        }
        let mut indices = indices;
        let rest: Vec<BoundExpression> = indices
            .split_off(fixed)
            .into_iter()
            .map(|index| self.convert(index, &element))
            .collect();
        let collection = self.collection_of(&parameters[fixed], &element, rest, span);
        indices.push(collection);
        indices
    }

    /// `a[^1]` and `a[1..3]` where the type counts rather than taking an
    /// `Index` or a `Range` of its own.
    ///
    /// The language says what `^1` means only in terms of a length, so the
    /// receiver has to be asked for one — and asked once, which is why it
    /// goes into a local of its own first.
    fn bind_counted_access(
        &mut self,
        receiver: &BoundExpression,
        index: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let wanted = self.framework_type("System.Index")?;
        let range = self.framework_type("System.Range");
        let is_index = index.ty == wanted;
        let is_range = range.as_ref() == Some(&index.ty);
        if !is_index && !is_range {
            return None;
        }
        // A type that takes one directly needs no help.
        if self.takes_directly(&receiver.ty, &index.ty) {
            return None;
        }
        // So does an extension block's (C# 14) indexer that takes it — but not
        // for an array, whose own element access and slicing come first.
        // And what the type itself counts and indexes or slices with comes
        // before it.
        // The pattern is exact: an indexer of one `int` and no more, a
        // `Slice` of two. `this[int i, object o = null]` is not it, and the
        // block's indexer is what `c[^1]` means then.
        let own_pattern = self.length_through(receiver, span, false).is_some()
            && if is_index {
                self.takes_only_ints(&receiver.ty, &["this[]"], 1)
            } else {
                self.takes_only_ints(&receiver.ty, &["Substring", "Slice"], 2)
            };
        if !own_pattern
            && !matches!(receiver.ty, Type::Array { .. })
            && self
                .extension_indexer(receiver, std::slice::from_ref(index), &[None], false)
                .is_some()
        {
            return None;
        }
        let held = self.declare_synthetic_local("indexed", receiver.ty.clone());
        let local =
            BoundExpression::new(BoundExpressionKind::Local(held), receiver.ty.clone(), span);
        let keep = BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(local.clone()),
                value: Box::new(receiver.clone()),
            },
            receiver.ty.clone(),
            span,
        );
        let length = self.length_through(&local, span, true)?;
        // `f[^1]` on a variable — a `ref T` parameter above all — indexes the
        // variable itself: a copy of a struct would not see what `Length`
        // did to it, nor would the struct see what the indexer does.
        // A struct field is a variable too: `s[1..2]` on a static `S s`
        // slices the field itself, and what `Slice` does to it stays.
        let writable_field = matches!(&receiver.kind, BoundExpressionKind::Field { field, .. }
            if !self
                .binder
                .compilation()
                .symbols()
                .get(*field)
                .modifiers
                .contains(Modifiers::READONLY));
        let variable = (matches!(
            receiver.kind,
            BoundExpressionKind::Local(_)
                | BoundExpressionKind::Parameter(_)
                | BoundExpressionKind::This
        ) || writable_field)
            && ((matches!(receiver.ty, Type::TypeParameter(_))
            // A `T : class` is a reference, and what is indexed is the
            // instance the variable held before the index was worked out:
            // `item[^F(ref item)]` reads `item` first.
            && !self.binder.held_by_reference(&receiver.ty))
                || (!receiver
                    .ty
                    .is_reference_type(self.binder.compilation().symbols())
                    && receiver.ty.symbol().is_some()));
        if is_index && variable {
            let length = self.length_through(receiver, span, true)?;
            let offset = self.call_on(index.clone(), "GetOffset", vec![length], span)?;
            return self.index_by(receiver.clone(), offset, span, true);
        }
        if is_index {
            // `i.GetOffset(length)` is what the language says `a[i]` is. The
            // receiver is stored on the way in, and the element is then
            // read through the local — or written through it: `list[^1] =
            // x` assigns to whatever the indexing names, so the indexing
            // itself is what comes out, not a sequence that ends in it.
            let offset = self.call_on(index.clone(), "GetOffset", vec![length], span)?;
            let stored = BoundExpression::new(
                BoundExpressionKind::Sequence(vec![keep, local.clone()]),
                local.ty.clone(),
                span,
            );
            return self.index_by(stored, offset, span, true);
        }
        // `item[range]` on a variable of a struct, or of a `T` that may be
        // one, slices the variable itself once the range is worked out: its
        // `Length` and `Slice` see what the range did to it. A `T` that
        // turns out a class slices the instance it held first.
        let generic_either = matches!(receiver.ty, Type::TypeParameter(_))
            && !self.binder.held_by_reference(&receiver.ty);
        if variable
            && !matches!(local.ty, Type::Array { .. })
            && (writable_field
                || matches!(
                    receiver.kind,
                    BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
                ))
        {
            let mut steps = Vec::new();
            let struct_parameter = matches!(&receiver.ty, Type::TypeParameter(parameter)
                if self
                    .binder
                    .compilation()
                    .symbols()
                    .get(*parameter)
                    .as_type_parameter()
                    .is_some_and(|detail| detail.value_type));
            let through = if generic_either && !struct_parameter {
                self.keep_generic(receiver.clone(), &mut steps)
            } else {
                receiver.clone()
            };
            let length = self.length_through(&through, span, true)?;
            let (offset, count) = self.offset_and_count(index, length, &mut steps, span)?;
            let sliced = self.slice_through(through, offset, count, span, true)?;
            let ty = sliced.ty.clone();
            steps.push(sliced);
            return Some(BoundExpression::new(
                BoundExpressionKind::Sequence(steps),
                ty,
                span,
            ));
        }
        if let Type::Array { element, .. } = local.ty.clone() {
            // Nothing in the language makes a sub-array; the runtime does,
            // and it takes the `Range` as it stands.
            let helpers = self.framework_type("System.Runtime.CompilerServices.RuntimeHelpers")?;
            let taken = self.call_static_with(
                &helpers,
                "GetSubArray",
                vec![local, index.clone()],
                &[(*element).clone()],
                span,
            )?;
            Some(BoundExpression::new(
                BoundExpressionKind::Sequence(vec![keep, taken.clone()]),
                taken.ty,
                span,
            ))
        } else {
            // A `Range` gives an offset and a count, and what is taken with
            // them depends on what is being sliced.
            let mut steps = vec![keep];
            let (offset, count) = self.offset_and_count(index, length, &mut steps, span)?;
            let sliced = self.slice_through(local, offset, count, span, true)?;
            steps.push(sliced.clone());
            Some(BoundExpression::new(
                BoundExpressionKind::Sequence(steps),
                sliced.ty,
                span,
            ))
        }
    }

    /// Where a `Range` starts in a list of `length` elements and how many it
    /// takes: `range.Start.GetOffset(length)` and the `End`'s offset less
    /// that, as Roslyn works them out — which asks nothing of the `Range`
    /// but its two `Index`es, whatever else a `Range` declared in source
    /// has. The range and the length are held in locals, each evaluated
    /// once, by the steps pushed.
    fn offset_and_count(
        &mut self,
        range: &BoundExpression,
        length: BoundExpression,
        steps: &mut Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<(BoundExpression, BoundExpression)> {
        let int = self.special(SpecialType::Int32);
        let range = self.held(range.clone(), steps, span);
        let length = self.held(length, steps, span);
        let start = self.property_of(range.clone(), "Start", span)?;
        let start = self.call_on(start, "GetOffset", vec![length.clone()], span)?;
        let start = self.held(start, steps, span);
        let end = self.property_of(range, "End", span)?;
        let end = self.call_on(end, "GetOffset", vec![length], span)?;
        let count = BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Subtract,
                left: Box::new(end),
                right: Box::new(start.clone()),
            },
            int,
            span,
        );
        Some((start, count))
    }

    /// A value put in a local of its own by a step pushed, read back.
    fn held(
        &mut self,
        value: BoundExpression,
        steps: &mut Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        let ty = value.ty.clone();
        let local = self.declare_synthetic_local("held", ty.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span);
        steps.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(value),
            },
            ty,
            span,
        ));
        read
    }

    /// `value.Name`, a property read by name.
    fn property_of(
        &mut self,
        value: BoundExpression,
        name: &str,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let symbol = value.ty.symbol()?;
        let property = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .find(|member| self.kind_of(*member) == SymbolKind::Property)?;
        let ty = self.member_type(property, &value.ty);
        Some(BoundExpression::new(
            BoundExpressionKind::Property {
                receiver: Some(Box::new(value)),
                property,
            },
            ty,
            span,
        ))
    }

    /// Whether the type has a member of one of these names that takes
    /// exactly `count` parameters, each an `int`: the indexer or the `Slice`
    /// the language reads `x[^1]` and `x[a..b]` through.
    fn takes_only_ints(&self, receiver: &Type, names: &[&str], count: usize) -> bool {
        let Some(symbol) = receiver.symbol() else {
            return false;
        };
        let symbols = self.binder.compilation().symbols();
        let int = self.special(SpecialType::Int32);
        names.iter().any(|name| {
            self.binder
                .lookup_member(symbol, name)
                .into_iter()
                .any(|member| {
                    let parameters = match symbols.get(member).kind {
                        SymbolKind::Method => symbols
                            .get(member)
                            .as_method()
                            .map(|detail| detail.parameters.clone()),
                        _ => symbols
                            .get(member)
                            .as_property()
                            .map(|detail| detail.parameters.clone()),
                    };
                    parameters.is_some_and(|parameters| {
                        parameters.len() == count
                            && parameters.iter().all(|parameter| {
                                self.binder.type_of(*parameter, &mut Diagnostics::new()) == int
                            })
                    })
                })
        })
    }

    /// Whether a type has an indexer that takes this type as it stands.
    fn takes_directly(&self, receiver: &Type, index: &Type) -> bool {
        let Some(symbol) = receiver.symbol() else {
            return false;
        };
        self.binder
            .lookup_member(symbol, "this[]")
            .into_iter()
            .any(|indexer| {
                self.binder
                    .compilation()
                    .symbols()
                    .get(indexer)
                    .as_property()
                    .is_some_and(|detail| {
                        // `this[Index i, int j = 0]` takes one as well: the
                        // parameters after the first may be left out.
                        let Some((first, rest)) = detail.parameters.split_first() else {
                            return false;
                        };
                        let symbols = self.binder.compilation().symbols();
                        let optional = rest.iter().all(|parameter| {
                            symbols
                                .get(*parameter)
                                .as_parameter()
                                .is_some_and(|detail| detail.has_default || detail.is_params)
                        });
                        let mut sink = Diagnostics::new();
                        optional && self.binder.type_of(*first, &mut sink) == *index
                    })
            })
    }

    /// How many elements a value has: an array's length, or the `Length` or
    /// `Count` a countable type carries.
    pub(super) fn length_of(
        &mut self,
        value: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        self.length_through(value, span, false)
    }

    /// The same, where a `Length` or `Count` an extension block (C# 14)
    /// declared counts too, if `extensions` is set.
    fn length_through(
        &mut self,
        value: &BoundExpression,
        span: TextSpan,
        extensions: bool,
    ) -> Option<BoundExpression> {
        if matches!(value.ty, Type::Array { .. }) {
            return Some(BoundExpression::new(
                BoundExpressionKind::ArrayLength {
                    array: Box::new(value.clone()),
                },
                self.special(SpecialType::Int32),
                span,
            ));
        }
        let symbol = value.ty.symbol();
        for name in ["Length", "Count"] {
            if let Some(found) =
                symbol.and_then(|symbol| self.binder.lookup_member(symbol, name).first().copied())
                && self.kind_of(found) == SymbolKind::Property
            {
                let ty = self.member_type(found, &value.ty);
                return Some(BoundExpression::new(
                    BoundExpressionKind::Property {
                        receiver: Some(Box::new(value.clone())),
                        property: found,
                    },
                    ty,
                    span,
                ));
            }
        }
        if !extensions {
            return None;
        }
        let int = self.special(SpecialType::Int32);
        for name in ["Length", "Count"] {
            let Some((access, property, tied)) =
                self.extension_member_access_checked(value, name, span)
            else {
                continue;
            };
            // The first of the two names that is there is the one asked, and
            // it has to be one that can be read here.
            let readable = self
                .binder
                .compilation()
                .symbols()
                .get(property)
                .as_property()
                .is_some_and(|detail| {
                    detail.has_get
                        && detail.get_accessibility != Some(crate::symbol::Accessibility::Private)
                });
            // A `ref` one is no count the language can read.
            let mut sink = Diagnostics::new();
            let by_reference = matches!(self.binder.type_of(property, &mut sink), Type::ByRef(_));
            return (access.ty == int
                && !tied
                && !by_reference
                && readable
                && self.accessible(property))
            .then_some(access);
        }
        None
    }

    /// `receiver[offset]`, however this receiver is indexed.
    fn index_by(
        &mut self,
        receiver: BoundExpression,
        offset: BoundExpression,
        span: TextSpan,
        extensions: bool,
    ) -> Option<BoundExpression> {
        if let Type::Array { element, .. } = receiver.ty.clone() {
            return Some(BoundExpression::new(
                BoundExpressionKind::ArrayAccess {
                    array: Box::new(receiver),
                    indices: vec![offset],
                },
                *element,
                span,
            ));
        }
        let members = receiver
            .ty
            .symbol()
            .map(|symbol| self.binder.lookup_member(symbol, "this[]"))
            .unwrap_or_default();
        // Only where no indexer the type has takes the offset is an
        // extension block's looked for.
        if extensions
            && !self
                .pick_indexer(&members, std::slice::from_ref(&offset), &receiver.ty)
                .is_some_and(|(_, fits)| fits)
        {
            // It has to be one the language can name: a single `int`, no
            // more, that this code may reach.
            let found =
                self.extension_indexer(&receiver, std::slice::from_ref(&offset), &[None], true);
            let symbols = self.binder.compilation().symbols();
            let usable = found.as_ref().is_some_and(|(indexer, _, _)| {
                let parameters = symbols
                    .get(*indexer)
                    .as_property()
                    .map(|detail| detail.parameters.clone())
                    .unwrap_or_default();
                let int = self.special(SpecialType::Int32);
                let mut sink = Diagnostics::new();
                parameters.len() == 2
                    && self.binder.type_of(parameters[1], &mut sink) == int
                    && self.accessible(*indexer)
            });
            if !usable {
                return None;
            }
            let ty = receiver.ty.clone();
            return Some(self.indexer_access(receiver, &ty, &[], vec![offset], &[None], span));
        }
        let indexer = members.first().copied()?;
        let ty = self.member_type(indexer, &receiver.ty);
        Some(BoundExpression::new(
            BoundExpressionKind::IndexerAccess {
                receiver: Box::new(receiver),
                indexer,
                arguments: vec![offset],
            },
            ty,
            span,
        ))
    }

    /// What `a[1..3]` gives back: a sub-array, a substring, or whatever the
    /// type's own `Slice` makes.
    pub(super) fn slice(
        &mut self,
        receiver: BoundExpression,
        offset: BoundExpression,
        count: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        self.slice_through(receiver, offset, count, span, false)
    }

    /// The same, where a `Slice` an extension method or block (C# 14)
    /// declared counts too, if `extensions` is set.
    fn slice_through(
        &mut self,
        receiver: BoundExpression,
        offset: BoundExpression,
        count: BoundExpression,
        span: TextSpan,
        extensions: bool,
    ) -> Option<BoundExpression> {
        for name in ["Substring", "Slice"] {
            if let Some(call) = self.call_on(
                receiver.clone(),
                name,
                vec![offset.clone(), count.clone()],
                span,
            ) {
                return Some(call);
            }
        }
        if extensions {
            let call = self.extension_call_with("Slice", receiver, vec![offset, count], span)?;
            // A `Slice` the language can use takes two `int`s and gives
            // something back.
            let BoundExpressionKind::Call { method, .. } = &call.kind else {
                return None;
            };
            let symbols = self.binder.compilation().symbols();
            let int = self.special(SpecialType::Int32);
            let parameters = symbols
                .get(*method)
                .as_method()
                .map(|detail| detail.parameters.clone())
                .unwrap_or_default();
            let mut sink = Diagnostics::new();
            let shaped = parameters.len() == 3
                && parameters[1..]
                    .iter()
                    .all(|parameter| self.binder.type_of(*parameter, &mut sink) == int)
                && call.ty != Type::Void;
            return shaped.then_some(call);
        }
        None
    }
}
