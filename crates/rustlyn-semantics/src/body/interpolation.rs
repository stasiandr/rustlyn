//! Interpolated strings (§12.8.3): binding one as it is written, and what it
//! becomes once something says what it is for — a `FormattableString`, an
//! interpolated string handler (C# 10), or a `string` joined the way Roslyn
//! joins one.
//!
//! An interpolated string is bound as its pieces, the way Roslyn binds its
//! `BoundUnconvertedInterpolatedString`: nothing about how it is put
//! together is decided until it is converted. A conversion to a handler type
//! makes the handler there and then. Whatever is still a string once the
//! body is bound is joined by [`BodyBinder::lower_interpolated_strings`],
//! which walks the finished tree: only then is it certain that nothing will
//! give it another type.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, Resolved};
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundPattern, BoundPatternKind, BoundStatement,
    BoundStatementKind, BoundSwitchLabel, ConstantValue, DynamicOperation, LocalId,
    composite_clauses,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, RefKind, SymbolId, SymbolKind};
use crate::types::Type;

/// The handler a string-typed interpolated string is built with, where the
/// framework (or the program) has one.
const DEFAULT_HANDLER: &str = "System.Runtime.CompilerServices.DefaultInterpolatedStringHandler";

impl BodyBinder<'_> {
    /// `$"a{b,5:N2}"` as written: its text as the string constants it
    /// stands for, and each hole's value beside the alignment and format it
    /// was given.
    pub(super) fn bind_interpolated_string(&mut self, node: &SyntaxNode) -> BoundExpression {
        let string = self.special(SpecialType::String);
        let mut parts = Vec::new();
        for content in interpolation_contents(node) {
            match content {
                Content::Text(text, span) => parts.push(BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::String(text)),
                    string.clone(),
                    span,
                )),
                Content::Hole(hole, spelling) => {
                    if let Some(insert) = self.bind_hole(&hole, spelling) {
                        parts.push(insert);
                    }
                }
            }
        }
        BoundExpression::new(
            BoundExpressionKind::InterpolatedString(parts),
            string,
            node.span(),
        )
    }

    /// One `{value,alignment:format}`.
    ///
    /// A value with no type of its own is an `object`, which is what a hole
    /// takes when it is joined into a string — `{(t is null ? "null" : t)}`
    /// has branches that agree on nothing else. A handler may take it as
    /// something else: a conditional, a `switch` or a `new()` is kept as it
    /// was written too, for its `AppendFormatted` to give a type of its own.
    fn bind_hole(&mut self, hole: &SyntaxNode, spelling: Spelling) -> Option<BoundExpression> {
        let mut value = None;
        let mut alignment = None;
        let mut format = None;
        for part in hole.children() {
            match part.kind() {
                SyntaxKind::InterpolationAlignmentClause => alignment = self.alignment_of(&part),
                SyntaxKind::InterpolationFormatClause => format = Some(format_of(&part, spelling)),
                // `is_expression` rather than `is_expression_node`: the hole
                // of `$"{a}"` holds a name, and a name is not an expression
                // node.
                kind if kind.is_expression() && value.is_none() => {
                    value = Some(self.bind_expression(&part));
                }
                _ => {}
            }
        }
        let value = value?;
        let object = self.special(SpecialType::Object);
        let value = match value.kind {
            // A bare `default` is an object's.
            BoundExpressionKind::Default(Type::Error) => BoundExpression::new(
                BoundExpressionKind::Default(object.clone()),
                object,
                value.span,
            ),
            BoundExpressionKind::UnboundConditional(_)
            | BoundExpressionKind::UnboundSwitch(_)
            | BoundExpressionKind::UnboundCreation(_) => {
                let written = value.clone();
                let converted = self.convert(value, &object);
                self.typeless_holes.insert(converted.span, written);
                converted
            }
            BoundExpressionKind::UnboundLambda(_) => self.convert(value, &object),
            _ => value,
        };
        let ty = value.ty.clone();
        Some(BoundExpression::new(
            BoundExpressionKind::StringInsert {
                value: Box::new(value),
                alignment,
                format,
            },
            ty,
            hole.span(),
        ))
    }

    /// The `,n` of a hole, folded: the alignment is a constant (§12.8.3),
    /// `-(3+4)` as well as `-7`.
    fn alignment_of(&mut self, clause: &SyntaxNode) -> Option<i32> {
        let expression = clause
            .children()
            .find(|child| child.kind().is_expression())?;
        let floor = self.body.diagnostics.len();
        let bound = self.bind_expression(&expression);
        self.body.diagnostics.truncate(floor);
        match self.binder.folded(&bound)? {
            ConstantValue::Int32(value) => Some(value),
            ConstantValue::UInt32(value) => i32::try_from(value).ok(),
            ConstantValue::Int64(value) => i32::try_from(value).ok(),
            ConstantValue::UInt64(value) => i32::try_from(value).ok(),
            ConstantValue::Char(value) => i32::try_from(u32::from(value)).ok(),
            _ => None,
        }
    }

    /// Whether a type is one an interpolated string converts to with its
    /// holes kept apart from its text (§12.8.3).
    pub(super) fn is_formattable(&self, ty: &Type) -> bool {
        ty.symbol().is_some_and(|symbol| {
            matches!(
                self.binder
                    .compilation()
                    .symbols()
                    .qualified_name(symbol)
                    .as_str(),
                "System.FormattableString" | "System.IFormattable"
            )
        })
    }

    /// Whether a type is an interpolated string handler (C# 10): one declared
    /// `[InterpolatedStringHandler]`, in source or in metadata, which an
    /// interpolated string converts to by making one and appending to it.
    pub(super) fn is_handler_type(&self, ty: &Type) -> bool {
        let Type::Named { symbol, .. } = ty else {
            return false;
        };
        self.binder
            .compilation()
            .symbols()
            .get(*symbol)
            .as_named_type()
            .is_some_and(|detail| detail.interpolated_string_handler)
    }

    /// `$"{value:G9}"` given to a `FormattableString`: the text with its
    /// holes numbered, and the values beside it, handed to
    /// `FormattableStringFactory.Create` — which is what the conversion
    /// means, and what a C# compiler emits for it.
    pub(super) fn formattable(&mut self, value: BoundExpression, target: &Type) -> BoundExpression {
        let span = value.span;
        let BoundExpressionKind::InterpolatedString(parts) = value.kind else {
            return value;
        };
        let (format, holes) = composite_format(parts);
        let string = self.special(SpecialType::String);
        let object = self.special(SpecialType::Object);
        let Some(factory) =
            self.framework_type("System.Runtime.CompilerServices.FormattableStringFactory")
        else {
            return BoundExpression::error(span);
        };
        let Some(factory_symbol) = factory.symbol() else {
            return BoundExpression::error(span);
        };
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(factory_symbol, "Create")
            .into_iter()
            .filter(|id| self.kind_of(*id) == SymbolKind::Method)
            .collect();
        let mut arguments = vec![BoundExpression::new(
            BoundExpressionKind::Literal(ConstantValue::String(format)),
            string,
            span,
        )];
        for hole in holes {
            let boxed = self.convert(hole, &object);
            arguments.push(boxed);
        }
        let types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();
        let evidence = self.evidence(&arguments);
        let Some(method) = self.resolve_overload(&candidates, &types, &evidence, &factory) else {
            return BoundExpression::error(span);
        };
        let arguments = self.convert_arguments(method, arguments, &factory, &HashMap::new(), span);
        let ty = self.member_type(method, &factory);
        let call = BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: None,
                method,
                type_arguments: Vec::new(),
                arguments,
                virtual_call: false,
            },
            ty.clone(),
            span,
        );
        if ty == *target {
            call
        } else {
            self.convert(call, target)
        }
    }

    /// `$"a{b}"` given to an interpolated string handler (C# 10): the handler
    /// made with the length of the text and the number of holes — then
    /// `extra`, what a parameter's `[InterpolatedStringHandlerArgument]`
    /// names, and a trailing `out bool` where a constructor takes one — each
    /// piece appended to it in order, and the handler itself as the value.
    ///
    /// An `Append` that returns `bool` says whether to go on, and so does
    /// the `out bool`: a `false` leaves the rest of the pieces unevaluated.
    pub(super) fn handler_conversion(
        &mut self,
        value: BoundExpression,
        handler: &Type,
        extra: Vec<BoundExpression>,
    ) -> BoundExpression {
        let span = value.span;
        let pieces = pieces_of(value);
        let floor = self.body.diagnostics.len();
        let Some((mut steps, local)) = self.build_handler(handler, pieces, extra, true, span)
        else {
            // What was wrong was said where it was found, if anywhere.
            if self.body.diagnostics.len() == floor {
                let shown = self.display(handler);
                self.report(ErrorCode::ErrNoImplicitConv, span, &["string", &shown]);
            }
            return BoundExpression::error(span);
        };
        steps.push(BoundExpression::new(
            BoundExpressionKind::Local(local),
            handler.clone(),
            span,
        ));
        BoundExpression::new(BoundExpressionKind::Sequence(steps), handler.clone(), span)
    }

    /// An interpolated string given to a parameter of handler type: the
    /// handler made with what the parameter's
    /// `[InterpolatedStringHandlerArgument]` names (Roslyn's
    /// `bindInterpolatedStringHandlerInMemberCall`) — arguments before it,
    /// by their parameters' names, and `""` for the receiver.
    ///
    /// Each named argument is evaluated once, where it stands, into a
    /// temporary that both the handler and the call are then given; `in`,
    /// `ref` and `out` ones by reference, as their parameter takes them. The
    /// receiver is kept the same way by the call that has one, which
    /// [`capture_receiver`](Self::capture_receiver) does once the arguments
    /// are converted: `capture` says whether it was named.
    ///
    /// Arguments written in another order than their parameters' come as
    /// the stores that keep their written order, then the string: the
    /// arguments after this one's parameter are already kept by them, or
    /// read the same wherever they are read, and are read as they are.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn handler_argument(
        &mut self,
        argument: BoundExpression,
        handler: &Type,
        parameter: SymbolId,
        at: usize,
        parameters: &[SymbolId],
        converted: &mut [BoundExpression],
        capture: &mut HandlerCapture,
        receiver: &Type,
    ) -> BoundExpression {
        let span = argument.span;
        let (mut stores, argument) = match argument.kind {
            BoundExpressionKind::Sequence(mut steps)
                if steps
                    .last()
                    .is_some_and(BoundExpression::is_interpolated_string) =>
            {
                let last = steps.pop().unwrap_or_else(|| BoundExpression::error(span));
                (steps, last)
            }
            kind => (Vec::new(), BoundExpression::new(kind, argument.ty, span)),
        };
        let symbols = self.binder.compilation().symbols();
        let names = symbols
            .get(parameter)
            .as_parameter()
            .and_then(|detail| detail.handler_arguments.clone())
            .unwrap_or_default();
        let mut extra = Vec::with_capacity(names.len());
        for name in &names {
            if name.is_empty() {
                let local = match capture.receiver {
                    Some(local) => local,
                    None => {
                        let local = self.declare_synthetic_local("receiver", receiver.clone());
                        capture.receiver = Some(local);
                        local
                    }
                };
                extra.push(BoundExpression::new(
                    BoundExpressionKind::Local(local),
                    receiver.clone(),
                    span,
                ));
                continue;
            }
            let Some(named) = parameters
                .iter()
                .position(|candidate| super::call_name(symbols, *candidate) == name.as_str())
            else {
                continue;
            };
            let ref_kind = symbols
                .get(parameters[named])
                .as_parameter()
                .map_or(RefKind::None, |detail| detail.ref_kind);
            let Some(stored) = converted.get_mut(named) else {
                continue;
            };
            if named > at {
                extra.push(match &stored.kind {
                    BoundExpressionKind::RefArgument { operand, .. }
                        if ref_kind != RefKind::None =>
                    {
                        BoundExpression::new(
                            BoundExpressionKind::RefArgument {
                                kind: ref_kind,
                                operand: operand.clone(),
                            },
                            stored.ty.clone(),
                            stored.span,
                        )
                    }
                    _ => stored.clone(),
                });
                continue;
            }
            extra.push(self.keep_handler_argument(named, stored, ref_kind, capture));
        }
        let made = self.handler_conversion(argument, handler, extra);
        if stores.is_empty() {
            return made;
        }
        let ty = made.ty.clone();
        stores.push(made);
        BoundExpression::new(BoundExpressionKind::Sequence(stores), ty, span)
    }

    /// An argument a handler is made with: kept in a temporary where it is
    /// evaluated — `stored` becomes the store, whose value is what was
    /// stored — and read from it for the handler, by reference where the
    /// parameter takes one. A constant is the same wherever it is read.
    fn keep_handler_argument(
        &mut self,
        at: usize,
        stored: &mut BoundExpression,
        ref_kind: RefKind,
        capture: &mut HandlerCapture,
    ) -> BoundExpression {
        let (ty, span) = (stored.ty.clone(), stored.span);
        let read = |local: LocalId| {
            BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span)
        };
        let by_reference = |local: LocalId, kind: RefKind| {
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind,
                    operand: Box::new(read(local)),
                },
                ty.clone(),
                span,
            )
        };
        if let Some(local) = capture.arguments.get(&at).copied() {
            return if ref_kind == RefKind::None {
                read(local)
            } else {
                by_reference(local, ref_kind)
            };
        }
        if ref_kind == RefKind::None
            && matches!(
                stored.kind,
                BoundExpressionKind::Literal(_) | BoundExpressionKind::Default(_)
            )
        {
            return stored.clone();
        }
        // A local or a parameter passed by reference is the same variable
        // wherever it is named, and an `out` one is not yet assigned to be
        // read into a temporary.
        if let BoundExpressionKind::RefArgument { kind, operand } = &stored.kind
            && matches!(
                operand.kind,
                BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
            )
        {
            return BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: if ref_kind == RefKind::None {
                        *kind
                    } else {
                        ref_kind
                    },
                    operand: operand.clone(),
                },
                ty,
                span,
            );
        }
        let local = self.declare_synthetic_local("argument", ty.clone());
        capture.arguments.insert(at, local);
        let original = std::mem::replace(stored, BoundExpression::error(span));
        match original.kind {
            BoundExpressionKind::RefArgument { kind, operand } => {
                if let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
                    slot.by_ref = true;
                }
                // Pointed at the variable as the argument is passed: an
                // `out` one is only written, and not read to get there.
                let store = BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(read(local)),
                        value: Box::new(BoundExpression::new(
                            BoundExpressionKind::RefArgument { kind, operand },
                            ty.clone(),
                            span,
                        )),
                    },
                    ty.clone(),
                    span,
                );
                *stored = BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind,
                        operand: Box::new(BoundExpression::new(
                            BoundExpressionKind::Sequence(vec![store, read(local)]),
                            ty.clone(),
                            span,
                        )),
                    },
                    ty.clone(),
                    span,
                );
                by_reference(
                    local,
                    if ref_kind == RefKind::None {
                        kind
                    } else {
                        ref_kind
                    },
                )
            }
            kind => {
                *stored = BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(read(local)),
                        value: Box::new(BoundExpression::new(kind, ty.clone(), span)),
                    },
                    ty.clone(),
                    span,
                );
                read(local)
            }
        }
    }

    /// The receiver of a call whose handler argument was made with it
    /// (`[InterpolatedStringHandlerArgument("")]`), kept in the temporary
    /// converting the arguments asked for: evaluated once, into it, and read
    /// from it by the call and the handler alike. A struct that is a
    /// variable is kept by reference, so that the call still reaches the
    /// variable; anything else by value. Where no handler asked, the
    /// receiver as it is.
    pub(super) fn capture_receiver(&mut self, receiver: BoundExpression) -> BoundExpression {
        let Some(local) = self.pending_receiver.take() else {
            return receiver;
        };
        let (ty, span) = (receiver.ty.clone(), receiver.span);
        let symbols = self.binder.compilation().symbols();
        let by_reference = !ty.is_reference_type(symbols) && self.is_writable_place(&receiver);
        // A `T` that may be a class is kept by reference only where it
        // turns out to be a struct: a class's reference is copied, and the
        // call made on what the variable held before the arguments ran —
        // `c2.M(c2 = default, $"...")` still calls `M` on the old `c2`
        // (Roslyn's `ReferToTempIfReferenceTypeReceiver`).
        let either = match &ty {
            Type::TypeParameter(parameter) => symbols
                .get(*parameter)
                .as_type_parameter()
                .is_some_and(|detail| !detail.value_type),
            _ => false,
        };
        if by_reference && either {
            return self.capture_either_receiver(receiver, local);
        }
        let value = if by_reference {
            if let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
                slot.by_ref = true;
            }
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Ref,
                    operand: Box::new(receiver),
                },
                ty.clone(),
                span,
            )
        } else {
            receiver
        };
        let read = BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span);
        let store = BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(value),
            },
            ty.clone(),
            span,
        );
        BoundExpression::new(BoundExpressionKind::Sequence(vec![store, read]), ty, span)
    }

    /// A receiver of a `T` that may be a struct or a class, kept in `local`:
    /// `ref T held = ref receiver; local = ref (default(T) != null ? ref
    /// held : ref (copy = held))` — the variable itself for a struct, a copy
    /// of the reference for a class.
    fn capture_either_receiver(
        &mut self,
        receiver: BoundExpression,
        local: LocalId,
    ) -> BoundExpression {
        let (ty, span) = (receiver.ty.clone(), receiver.span);
        let object = self.special(SpecialType::Object);
        let boolean = self.special(SpecialType::Boolean);
        let held = self.declare_synthetic_local("receiver", ty.clone());
        let copy = self.declare_synthetic_local("receiver", ty.clone());
        for by_ref in [held, local] {
            if let Some(slot) = self.body.locals.get_mut(by_ref.0 as usize) {
                slot.by_ref = true;
            }
        }
        let read = |local: LocalId| {
            BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span)
        };
        let refer = |operand: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Ref,
                    operand: Box::new(operand),
                },
                ty.clone(),
                span,
            )
        };
        let assign = |target: BoundExpression, value: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(target),
                    value: Box::new(value),
                },
                ty.clone(),
                span,
            )
        };
        // `(object)default(T) != null` holds exactly where `T` is a struct.
        let boxed_default = BoundExpression::new(
            BoundExpressionKind::Conversion {
                operand: Box::new(BoundExpression::new(
                    BoundExpressionKind::Default(ty.clone()),
                    ty.clone(),
                    span,
                )),
                conversion: crate::bound::ConversionKind::Boxing,
                written: false,
            },
            object.clone(),
            span,
        );
        let is_struct = BoundExpression::new(
            BoundExpressionKind::Binary {
                operator: BinaryOperator::Inequality,
                left: Box::new(boxed_default),
                right: Box::new(BoundExpression::new(
                    BoundExpressionKind::Literal(ConstantValue::Null),
                    object,
                    span,
                )),
            },
            boolean,
            span,
        );
        let copied = BoundExpression::new(
            BoundExpressionKind::Sequence(vec![assign(read(copy), read(held)), read(copy)]),
            ty.clone(),
            span,
        );
        let chosen = BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(is_struct),
                consequence: Box::new(refer(read(held))),
                alternative: Box::new(refer(copied)),
            },
            ty.clone(),
            span,
        );
        let steps = vec![
            assign(read(held), refer(receiver)),
            assign(read(local), refer(chosen)),
            read(local),
        ];
        BoundExpression::new(BoundExpressionKind::Sequence(steps), ty, span)
    }

    /// Makes a handler of type `handler` for `pieces` and appends them to it
    /// (Roslyn's `BindUnconvertedInterpolatedPartsToHandlerType`, lowered):
    /// the expressions that do it, in order, and the local the handler is
    /// kept in. `None` where no constructor or no `Append` takes what it is
    /// given.
    ///
    /// `retarget` gives a hole that had no type of its own back its written
    /// form, for its `AppendFormatted` to type; only while the statement is
    /// still being bound, since that binds the hole again.
    fn build_handler(
        &mut self,
        handler: &Type,
        pieces: Vec<BoundExpression>,
        extra: Vec<BoundExpression>,
        retarget: bool,
        span: TextSpan,
    ) -> Option<(Vec<BoundExpression>, LocalId)> {
        let int = self.special(SpecialType::Int32);
        let boolean = self.special(SpecialType::Boolean);
        let string = self.special(SpecialType::String);
        // The length is the text's in UTF-16 code units, which is what a
        // .NET string counts.
        let literal_length: usize = pieces
            .iter()
            .map(|piece| match &piece.kind {
                BoundExpressionKind::Literal(ConstantValue::String(text)) => {
                    text.encode_utf16().count()
                }
                _ => 0,
            })
            .sum();
        let formatted_count = pieces
            .iter()
            .filter(|piece| matches!(piece.kind, BoundExpressionKind::StringInsert { .. }))
            .count();
        let count = |value: usize| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(
                    i32::try_from(value).unwrap_or(i32::MAX),
                )),
                int.clone(),
                span,
            )
        };
        let mut arguments = vec![count(literal_length), count(formatted_count)];
        arguments.extend(extra);
        // A constructor with a trailing `out bool` is looked for first, and
        // one without it only where there is none, as Roslyn does.
        let proceed = self.declare_synthetic_local("proceed", boolean.clone());
        let read_proceed =
            || BoundExpression::new(BoundExpressionKind::Local(proceed), boolean.clone(), span);
        let mut with_out = arguments.clone();
        with_out.push(BoundExpression::new(
            BoundExpressionKind::RefArgument {
                kind: RefKind::Out,
                operand: Box::new(read_proceed()),
            },
            boolean.clone(),
            span,
        ));
        // The call is written as widely as what it is given: a
        // `[CallerArgumentExpression]` of the constructor quotes the
        // arguments the attribute named where they were written.
        let at_call = arguments
            .iter()
            .fold(span, |whole, argument| whole.union(argument.span));
        let floor = self.body.diagnostics.len();
        let (construction, proceeds) = match self.make(handler, with_out, at_call) {
            Some(made) => (made, true),
            None => {
                self.body.diagnostics.truncate(floor);
                match self.make(handler, arguments.clone(), at_call) {
                    Some(made) => (made, false),
                    None => {
                        // Neither form fits: said of the one without the
                        // `out bool`, as Roslyn says it where both fail.
                        let symbol = handler.symbol()?;
                        let constructors = self
                            .binder
                            .compilation()
                            .symbols()
                            .lookup(symbol, ".ctor")
                            .to_vec();
                        let types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();
                        let spans: Vec<TextSpan> = arguments.iter().map(|a| a.span).collect();
                        let name = self.display(handler);
                        self.report_no_overload(
                            &constructors,
                            &name,
                            &types,
                            &spans,
                            handler,
                            &[],
                            at_call,
                            Some(handler),
                        );
                        return None;
                    }
                }
            }
        };
        let local = self.declare_synthetic_local("handler", handler.clone());
        let receiver =
            || BoundExpression::new(BoundExpressionKind::Local(local), handler.clone(), span);
        let mut appends = Vec::with_capacity(pieces.len());
        for piece in pieces {
            let at = piece.span;
            let (name, arguments, names) = match piece.kind {
                BoundExpressionKind::Literal(ConstantValue::String(text)) => (
                    "AppendLiteral",
                    vec![BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::String(text)),
                        string.clone(),
                        at,
                    )],
                    vec![None],
                ),
                BoundExpressionKind::StringInsert {
                    value,
                    alignment,
                    format,
                } => {
                    // A hole that had no type of its own takes the one its
                    // `AppendFormatted` gives it.
                    let value = match self.typeless_holes.get(&value.span) {
                        Some(written) if retarget => written.clone(),
                        _ => *value,
                    };
                    let mut arguments = vec![value];
                    let mut names = vec![None];
                    if let Some(alignment) = alignment {
                        arguments.push(BoundExpression::new(
                            BoundExpressionKind::Literal(ConstantValue::Int32(alignment)),
                            int.clone(),
                            at,
                        ));
                        names.push(Some("alignment".to_string()));
                    }
                    if let Some(format) = format {
                        arguments.push(BoundExpression::new(
                            BoundExpressionKind::Literal(ConstantValue::String(format)),
                            string.clone(),
                            at,
                        ));
                        names.push(Some("format".to_string()));
                    }
                    ("AppendFormatted", arguments, names)
                }
                _ => return None,
            };
            appends.push(self.call_named_on(receiver(), name, arguments, &names, at)?);
        }
        // Whether the pieces are appended conditionally is settled by the
        // first `Append` bound here: the rest are to agree with it, and one
        // the runtime binds is taken to (to return nothing, where none is
        // bound here). What that one gives is then read as a `bool`.
        let bool_returns = appends
            .iter()
            .find(|append| !matches!(append.ty, Type::Dynamic))
            .is_some_and(|append| self.binder.special_of(&append.ty) == Some(SpecialType::Boolean));
        let appends: Vec<BoundExpression> = if bool_returns {
            appends
                .into_iter()
                .map(|append| {
                    if matches!(append.ty, Type::Dynamic) {
                        Self::dynamic_conversion(append, &boolean, false)
                    } else {
                        append
                    }
                })
                .collect()
        } else {
            appends
        };
        let and = |left: BoundExpression, right: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::LogicalAnd,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                boolean.clone(),
                span,
            )
        };
        let mut steps = vec![BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(receiver()),
                value: Box::new(construction),
            },
            handler.clone(),
            span,
        )];
        if bool_returns {
            // `proceed && h.AppendLiteral("a") && h.AppendFormatted(b)`.
            let mut chain = proceeds.then(read_proceed);
            for append in appends {
                chain = Some(match chain {
                    Some(left) => and(left, append),
                    None => append,
                });
            }
            steps.extend(chain);
        } else if proceeds && !appends.is_empty() {
            // `proceed && (h.AppendLiteral("a"), h.AppendFormatted(b), true)`:
            // Roslyn's `if (proceed) { ... }`, as an expression.
            let mut guarded = appends;
            guarded.push(BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Boolean(true)),
                boolean.clone(),
                span,
            ));
            let guarded = BoundExpression::new(
                BoundExpressionKind::Sequence(guarded),
                boolean.clone(),
                span,
            );
            steps.push(and(read_proceed(), guarded));
        } else {
            steps.extend(appends);
        }
        Some((steps, local))
    }

    /// `receiver.name(arguments)` with the names the arguments were given,
    /// the overload picked the way any call's is: what a handler's `Append`
    /// calls are (§12.8.3 of C# 10), `alignment:` and `format:` by name.
    fn call_named_on(
        &mut self,
        receiver: BoundExpression,
        name: &str,
        arguments: Vec<BoundExpression>,
        names: &[Option<String>],
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let ty = receiver.ty.clone();
        let symbol = ty.symbol()?;
        let symbols = self.binder.compilation().symbols();
        let candidates: Vec<SymbolId> = self
            .binder
            .lookup_member(symbol, name)
            .into_iter()
            .filter(|id| {
                symbols.get(*id).kind == SymbolKind::Method
                    && !symbols.get(*id).modifiers.contains(Modifiers::STATIC)
            })
            .collect();
        if candidates.is_empty() {
            let shown = self.display(&ty);
            self.report(ErrorCode::ErrNoSuchMemberOrExtension, span, &[&shown, name]);
            return None;
        }
        // A `dynamic` hole leaves the overload to the runtime binder, as any
        // call's does (§12.6.4.1).
        if Self::has_dynamic_argument(&arguments) {
            return Some(Self::dynamic_operation(
                DynamicOperation::InvokeMember {
                    name: name.to_string(),
                    type_arguments: Vec::new(),
                    simple_name: false,
                },
                Some(receiver),
                arguments,
                names.to_vec(),
                Type::Dynamic,
                span,
            ));
        }
        let candidates = self.named_candidates(&candidates, names);
        let named = names.iter().any(Option::is_some);
        let by_candidate = named
            && candidates
                .iter()
                .all(|candidate| self.named_order(*candidate, names).is_some());
        let mut arguments = if by_candidate {
            arguments
        } else {
            self.reorder_named(&candidates, names, arguments, &ty)
        };
        let resolved = if by_candidate {
            self.argument_names
                .borrow_mut()
                .push((candidates.clone(), names.to_vec()));
            let resolved = self.resolve_with_lambdas(&candidates, &mut arguments, &ty, &[], false);
            self.argument_names.borrow_mut().pop();
            if let Some(resolved) = &resolved {
                arguments = self.reorder_named(&[resolved.method], names, arguments, &ty);
            }
            resolved
        } else {
            self.resolve_with_lambdas(&candidates, &mut arguments, &ty, &[], false)
        };
        let Some(Resolved {
            method,
            type_arguments,
            substitution,
        }) = resolved
        else {
            let types: Vec<Type> = arguments.iter().map(|a| a.ty.clone()).collect();
            let spans: Vec<TextSpan> = arguments.iter().map(|a| a.span).collect();
            self.report_no_overload(&candidates, name, &types, &spans, &ty, &[], span, None);
            return None;
        };
        let result = self.member_type(method, &ty).substitute(&substitution);
        let arguments = self.convert_arguments(method, arguments, &ty, &substitution, span);
        let receiver = self.capture_receiver(receiver);
        let virtual_call = self.is_virtual_call(method, None);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(receiver)),
                method,
                type_arguments,
                arguments,
                virtual_call,
            },
            result,
            span,
        ))
    }

    /// Joins what is left of the body's interpolated strings into the
    /// strings they stand for, now that nothing can give them another type.
    ///
    /// Every body, lambda and local function is walked. In a lambda that an
    /// expression tree describes a string stays one, for the description to
    /// write as the `string.Format` it means: a tree has no handler.
    pub(super) fn lower_interpolated_strings(&mut self) {
        let mut seen = vec![false; self.body.lambdas.len()];
        let mut statements = std::mem::take(&mut self.body.statements);
        for statement in &mut statements {
            self.lower_in_statement(statement, Place::default(), &mut seen);
        }
        self.body.statements = statements;
        for index in 0..self.body.local_functions.len() {
            let span = self.body.local_functions[index].body.span;
            let mut body = std::mem::replace(
                &mut self.body.local_functions[index].body,
                BoundStatement::new(BoundStatementKind::Empty, span),
            );
            self.lower_in_statement(&mut body, Place::default(), &mut seen);
            self.body.local_functions[index].body = body;
        }
        // A lambda nothing holds any more — one overload resolution bound
        // against a delegate it then did not pick — is still emitted.
        for index in 0..seen.len() {
            self.lower_in_lambda(index, Place::default(), &mut seen);
        }
    }

    fn lower_in_lambda(&mut self, index: usize, place: Place, seen: &mut [bool]) {
        match seen.get_mut(index) {
            Some(done) if !*done => *done = true,
            _ => return,
        }
        let span = self.body.lambdas[index].span;
        let mut body = std::mem::replace(
            &mut self.body.lambdas[index].body,
            BoundStatement::new(BoundStatementKind::Empty, span),
        );
        self.lower_in_statement(&mut body, place, seen);
        self.body.lambdas[index].body = body;
    }

    fn lower_in_statement(
        &mut self,
        statement: &mut BoundStatement,
        place: Place,
        seen: &mut [bool],
    ) {
        match &mut statement.kind {
            BoundStatementKind::Unsupported(_)
            | BoundStatementKind::Empty
            | BoundStatementKind::Break(_)
            | BoundStatementKind::Continue(_)
            | BoundStatementKind::GotoCase(_)
            | BoundStatementKind::Label(_)
            | BoundStatementKind::Goto(_)
            | BoundStatementKind::YieldBreak
            | BoundStatementKind::Return(None)
            | BoundStatementKind::Throw(None) => {}
            BoundStatementKind::Block(statements) => {
                for inner in statements {
                    self.lower_in_statement(inner, place, seen);
                }
            }
            BoundStatementKind::LocalDeclaration { initializer, .. } => {
                if let Some(value) = initializer {
                    self.lower_in_expression(value, place, seen);
                }
            }
            BoundStatementKind::Expression(value)
            | BoundStatementKind::Return(Some(value))
            | BoundStatementKind::YieldReturn(value)
            | BoundStatementKind::Throw(Some(value)) => {
                self.lower_in_expression(value, place, seen);
            }
            BoundStatementKind::If {
                condition,
                consequence,
                alternative,
            } => {
                self.lower_in_expression(condition, place, seen);
                self.lower_in_statement(consequence, place, seen);
                if let Some(alternative) = alternative {
                    self.lower_in_statement(alternative, place, seen);
                }
            }
            BoundStatementKind::While { condition, body }
            | BoundStatementKind::DoWhile { body, condition } => {
                self.lower_in_expression(condition, place, seen);
                self.lower_in_statement(body, place, seen);
            }
            BoundStatementKind::For {
                initializers,
                condition,
                incrementors,
                body,
            } => {
                for initializer in initializers {
                    self.lower_in_statement(initializer, place, seen);
                }
                if let Some(condition) = condition {
                    self.lower_in_expression(condition, place, seen);
                }
                for incrementor in incrementors {
                    self.lower_in_expression(incrementor, place, seen);
                }
                self.lower_in_statement(body, place, seen);
            }
            BoundStatementKind::ForEach {
                collection,
                body,
                enumeration,
                ..
            } => {
                self.lower_in_expression(collection, place, seen);
                if let Some(enumeration) = enumeration {
                    for argument in &mut enumeration.extension_arguments {
                        self.lower_in_expression(argument, place, seen);
                    }
                }
                self.lower_in_statement(body, place, seen);
            }
            BoundStatementKind::ConstructorInitializer { arguments, .. } => {
                for argument in arguments {
                    self.lower_in_expression(argument, place, seen);
                }
            }
            BoundStatementKind::Switch {
                governing,
                sections,
            } => {
                self.lower_in_expression(governing, place, seen);
                for section in sections {
                    for label in &mut section.labels {
                        if let BoundSwitchLabel::Case(case) = label {
                            self.lower_in_pattern(&mut case.pattern, place, seen);
                            if let Some(when) = &mut case.when {
                                self.lower_in_expression(when, place, seen);
                            }
                        }
                    }
                    for inner in &mut section.statements {
                        self.lower_in_statement(inner, place, seen);
                    }
                }
            }
            BoundStatementKind::Try {
                body,
                catches,
                finally,
            } => {
                self.lower_in_statement(body, place, seen);
                for catch in catches {
                    if let Some(filter) = &mut catch.filter {
                        self.lower_in_expression(filter, place, seen);
                    }
                    self.lower_in_statement(&mut catch.body, place, seen);
                }
                if let Some(finally) = finally {
                    self.lower_in_statement(finally, place, seen);
                }
            }
            BoundStatementKind::Using { resources, body } => {
                for resource in resources {
                    self.lower_in_expression(&mut resource.value, place, seen);
                }
                self.lower_in_statement(body, place, seen);
            }
            BoundStatementKind::Lock { value, body, .. } => {
                self.lower_in_expression(value, place, seen);
                self.lower_in_statement(body, place, seen);
            }
            BoundStatementKind::Fixed { declarations, body } => {
                for declaration in declarations {
                    self.lower_in_statement(declaration, place, seen);
                }
                self.lower_in_statement(body, place, seen);
            }
        }
    }

    fn lower_in_pattern(&mut self, pattern: &mut BoundPattern, place: Place, seen: &mut [bool]) {
        match &mut pattern.kind {
            BoundPatternKind::Unsupported(_)
            | BoundPatternKind::Discard
            | BoundPatternKind::Var { .. }
            | BoundPatternKind::Type(_)
            | BoundPatternKind::Declaration { .. } => {}
            BoundPatternKind::VarDeconstruct { deconstruction, .. } => {
                self.lower_in_expression(deconstruction, place, seen);
            }
            BoundPatternKind::Constant(value) | BoundPatternKind::Relational { value, .. } => {
                self.lower_in_expression(value, place, seen);
            }
            BoundPatternKind::Recursive(recursive) => {
                for (_, inner) in &mut recursive.properties {
                    self.lower_in_pattern(inner, place, seen);
                }
                for inner in &mut recursive.positional {
                    self.lower_in_pattern(inner, place, seen);
                }
            }
            BoundPatternKind::List(list) => {
                for index in &mut list.indexes {
                    self.lower_in_expression(index, place, seen);
                }
                for inner in list.before.iter_mut().chain(list.after.iter_mut()) {
                    self.lower_in_pattern(inner, place, seen);
                }
                if let Some(slice) = &mut list.slice_pattern {
                    self.lower_in_expression(&mut slice.value, place, seen);
                    self.lower_in_pattern(&mut slice.pattern, place, seen);
                }
            }
            BoundPatternKind::SpanString { test, .. } => {
                self.lower_in_expression(test, place, seen);
            }
            BoundPatternKind::And(left, right) | BoundPatternKind::Or(left, right) => {
                self.lower_in_pattern(left, place, seen);
                self.lower_in_pattern(right, place, seen);
            }
            BoundPatternKind::Not(inner) | BoundPatternKind::UnionCase { inner, .. } => {
                self.lower_in_pattern(inner, place, seen);
            }
        }
    }

    fn lower_in_expression(
        &mut self,
        expression: &mut BoundExpression,
        place: Place,
        seen: &mut [bool],
    ) {
        if expression.is_interpolated_string() {
            self.lower_in_holes(expression, place, seen);
            let span = expression.span;
            let value = std::mem::replace(expression, BoundExpression::error(span));
            let outer = std::mem::replace(&mut self.synthetic_span, span);
            *expression = self.interpolated_as_string(value, place);
            self.synthetic_span = outer;
            return;
        }
        match &mut expression.kind {
            BoundExpressionKind::Error
            | BoundExpressionKind::Unsupported(_)
            | BoundExpressionKind::Literal(_)
            | BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::Base
            | BoundExpressionKind::StackValue
            | BoundExpressionKind::TypeExpression(_)
            | BoundExpressionKind::NamespaceExpression(_)
            | BoundExpressionKind::UnboundLambda(_)
            | BoundExpressionKind::UnboundCollection(_)
            | BoundExpressionKind::UnboundCreation(_)
            | BoundExpressionKind::UnboundConditional(_)
            | BoundExpressionKind::UnboundSwitch(_)
            | BoundExpressionKind::ArgListHandle
            | BoundExpressionKind::SizeOf(_)
            | BoundExpressionKind::MethodAddress { .. }
            | BoundExpressionKind::AccessedValue
            | BoundExpressionKind::CreatedObject
            | BoundExpressionKind::TypeOf(_)
            | BoundExpressionKind::Default(_)
            | BoundExpressionKind::InterpolatedString(_) => {}
            BoundExpressionKind::Lambda(index) => {
                let index = *index;
                let place = Place {
                    in_tree: place.in_tree || self.is_expression_tree(&expression.ty),
                };
                self.lower_in_lambda(index, place, seen);
            }
            BoundExpressionKind::Field { receiver, .. }
            | BoundExpressionKind::Property { receiver, .. }
            | BoundExpressionKind::MethodGroup { receiver, .. }
            | BoundExpressionKind::DelegateCreation { receiver, .. } => {
                if let Some(receiver) = receiver {
                    self.lower_in_expression(receiver, place, seen);
                }
            }
            BoundExpressionKind::RefArgument { operand, .. }
            | BoundExpressionKind::Dereference { operand }
            | BoundExpressionKind::AddressOf { operand }
            | BoundExpressionKind::Unary { operand, .. }
            | BoundExpressionKind::Conversion { operand, .. }
            | BoundExpressionKind::TypeTest { operand, .. }
            | BoundExpressionKind::TryCast { operand, .. }
            | BoundExpressionKind::Await { operand, .. }
            | BoundExpressionKind::MakeRef(operand)
            | BoundExpressionKind::RefValue(operand)
            | BoundExpressionKind::RefType(operand) => {
                self.lower_in_expression(operand, place, seen);
            }
            BoundExpressionKind::StringInsert { value, .. } => {
                self.lower_in_expression(value, place, seen);
            }
            BoundExpressionKind::ArgList(values)
            | BoundExpressionKind::TupleCreation(values)
            | BoundExpressionKind::Sequence(values) => {
                for value in values {
                    self.lower_in_expression(value, place, seen);
                }
            }
            BoundExpressionKind::Call {
                receiver,
                arguments,
                ..
            } => {
                if let Some(receiver) = receiver {
                    self.lower_in_expression(receiver, place, seen);
                }
                for argument in arguments {
                    self.lower_in_expression(argument, place, seen);
                }
            }
            BoundExpressionKind::ObjectCreation {
                arguments,
                initializers,
                ..
            } => {
                for argument in arguments.iter_mut().chain(initializers.iter_mut()) {
                    self.lower_in_expression(argument, place, seen);
                }
            }
            BoundExpressionKind::With {
                receiver,
                initializers,
            } => {
                self.lower_in_expression(receiver, place, seen);
                for initializer in initializers {
                    self.lower_in_expression(initializer, place, seen);
                }
            }
            BoundExpressionKind::FunctionPointerCall { pointer, arguments } => {
                self.lower_in_expression(pointer, place, seen);
                for argument in arguments {
                    self.lower_in_expression(argument, place, seen);
                }
            }
            BoundExpressionKind::StackAlloc {
                count, elements, ..
            } => {
                self.lower_in_expression(count, place, seen);
                for element in elements {
                    self.lower_in_expression(element, place, seen);
                }
            }
            BoundExpressionKind::Throw(value) => {
                if let Some(value) = value {
                    self.lower_in_expression(value, place, seen);
                }
            }
            BoundExpressionKind::ConditionalAccess { receiver, access } => {
                self.lower_in_expression(receiver, place, seen);
                self.lower_in_expression(access, place, seen);
            }
            BoundExpressionKind::ArrayCreation {
                lengths, elements, ..
            } => {
                for value in lengths.iter_mut().chain(elements.iter_mut()) {
                    self.lower_in_expression(value, place, seen);
                }
            }
            BoundExpressionKind::ArrayAccess { array, indices } => {
                self.lower_in_expression(array, place, seen);
                for index in indices {
                    self.lower_in_expression(index, place, seen);
                }
            }
            BoundExpressionKind::ArrayLength { array } => {
                self.lower_in_expression(array, place, seen);
            }
            BoundExpressionKind::IndexerAccess {
                receiver,
                arguments,
                ..
            } => {
                self.lower_in_expression(receiver, place, seen);
                for argument in arguments {
                    self.lower_in_expression(argument, place, seen);
                }
            }
            BoundExpressionKind::Binary { left, right, .. } => {
                self.lower_in_expression(left, place, seen);
                self.lower_in_expression(right, place, seen);
            }
            BoundExpressionKind::Conditional {
                condition,
                consequence,
                alternative,
            } => {
                self.lower_in_expression(condition, place, seen);
                self.lower_in_expression(consequence, place, seen);
                self.lower_in_expression(alternative, place, seen);
            }
            BoundExpressionKind::Assignment { target, value }
            | BoundExpressionKind::CompoundAssignment { target, value, .. } => {
                self.lower_in_expression(target, place, seen);
                self.lower_in_expression(value, place, seen);
            }
            BoundExpressionKind::EventAssignment {
                receiver, handler, ..
            } => {
                if let Some(receiver) = receiver {
                    self.lower_in_expression(receiver, place, seen);
                }
                self.lower_in_expression(handler, place, seen);
            }
            BoundExpressionKind::SpillSequence { statements, value } => {
                for statement in statements {
                    self.lower_in_statement(statement, place, seen);
                }
                self.lower_in_expression(value, place, seen);
            }
            BoundExpressionKind::Increment { target, .. } => {
                self.lower_in_expression(target, place, seen);
            }
            BoundExpressionKind::IsPattern { operand, pattern } => {
                self.lower_in_expression(operand, place, seen);
                self.lower_in_pattern(pattern, place, seen);
            }
            BoundExpressionKind::Switch { governing, arms } => {
                self.lower_in_expression(governing, place, seen);
                for arm in arms {
                    self.lower_in_pattern(&mut arm.pattern, place, seen);
                    if let Some(when) = &mut arm.when {
                        self.lower_in_expression(when, place, seen);
                    }
                    self.lower_in_expression(&mut arm.value, place, seen);
                }
            }
            BoundExpressionKind::Dynamic(dynamic) => {
                if let Some(receiver) = &mut dynamic.receiver {
                    self.lower_in_expression(receiver, place, seen);
                }
                for argument in &mut dynamic.arguments {
                    self.lower_in_expression(argument, place, seen);
                }
            }
        }
    }

    /// Lowers what the holes of an interpolated string, or of an addition
    /// of them, hold: a hole may hold another interpolated string, or a
    /// lambda.
    fn lower_in_holes(
        &mut self,
        expression: &mut BoundExpression,
        place: Place,
        seen: &mut [bool],
    ) {
        match &mut expression.kind {
            BoundExpressionKind::InterpolatedString(parts) => {
                for part in parts {
                    if let BoundExpressionKind::StringInsert { value, .. } = &mut part.kind {
                        self.lower_in_expression(value, place, seen);
                    }
                }
            }
            BoundExpressionKind::Binary { left, right, .. } => {
                self.lower_in_holes(left, place, seen);
                self.lower_in_holes(right, place, seen);
            }
            _ => {}
        }
    }

    /// Whether a type is `Expression<TDelegate>`: a lambda converted to it
    /// is described rather than compiled.
    fn is_expression_tree(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named { symbol, type_arguments }
            if type_arguments.len() == 1
                && self.binder.compilation().symbols().qualified_name(*symbol)
                    == "System.Linq.Expressions.Expression`1")
    }

    /// An interpolated string, or an addition of them, given to a `string`:
    /// joined the way Roslyn joins one (`BindUnconvertedInterpolatedString
    /// ToString` and its lowering), in the first of these ways that applies.
    ///
    /// 1. A constant is the string it folds to.
    /// 2. Four pieces or fewer, each a string written with no alignment or
    ///    format, are `string.Concat`: no intermediate anything.
    /// 3. `DefaultInterpolatedStringHandler`, where there is one, the holes
    ///    wait for no `await` (it is a `ref struct`) and are not `dynamic`,
    ///    and the string is not in an expression tree: appended piece by
    ///    piece, then `ToStringAndClear()`. Which `AppendFormatted` a hole
    ///    gets — no boxing of a struct, a `ToString` only as it is appended
    ///    — is observable, and is why this is not `string.Format`.
    /// 4. Nothing but strings, however many, is `string.Concat` still.
    /// 5. Anything else is `string.Format` of the text with its holes
    ///    numbered.
    ///
    /// An addition goes the same way as a whole where the default handler
    /// takes all of it; otherwise each of its strings is joined on its own
    /// and the results added, as Roslyn binds it then.
    fn interpolated_as_string(&mut self, value: BoundExpression, place: Place) -> BoundExpression {
        let span = value.span;
        let string = self.special(SpecialType::String);
        if let Some(constant @ ConstantValue::String(_)) = self.binder.folded(&value) {
            return BoundExpression::new(BoundExpressionKind::Literal(constant), string, span);
        }
        if place.in_tree {
            // A tree has no interpolation of its own, nor any way to make a
            // handler: what it describes is the `string.Format` Roslyn
            // writes there, whatever the holes are, and the describing
            // writes it.
            return value;
        }
        let pieces = pieces_of(value.clone());
        let all_strings = pieces.iter().all(|piece| self.is_string_piece(piece));
        let simple = pieces.len() <= 4 && all_strings;
        let handler_takes_it = !simple
            && pieces.iter().all(|piece| match &piece.kind {
                BoundExpressionKind::StringInsert { value, .. } => {
                    !matches!(value.ty, Type::Dynamic) && !super::calls::contains_await(value)
                }
                _ => true,
            });
        if handler_takes_it && let Some(built) = self.default_handler_string(pieces.clone(), span) {
            return built;
        }
        if let BoundExpressionKind::Binary {
            operator: BinaryOperator::Add,
            left,
            right,
        } = value.kind
        {
            let left = self.interpolated_as_string(*left, place);
            let right = self.interpolated_as_string(*right, place);
            return BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::Add,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                string,
                span,
            );
        }
        let joined = if all_strings {
            self.concatenation(pieces, span)
        } else {
            self.format_call(pieces, span)
        };
        joined.unwrap_or(value)
    }

    /// Whether a piece is text, or a hole of a `string` with no alignment or
    /// format: what `string.Concat` takes as it is.
    fn is_string_piece(&self, piece: &BoundExpression) -> bool {
        match &piece.kind {
            BoundExpressionKind::Literal(ConstantValue::String(_)) => true,
            BoundExpressionKind::StringInsert {
                value,
                alignment: None,
                format: None,
            } => self.binder.special_of(&value.ty) == Some(SpecialType::String),
            _ => false,
        }
    }

    /// Pieces that are all strings, joined: one alone is itself — a hole
    /// with `?? ""`, since the string is never `null` — and more are
    /// `string.Concat` of them.
    fn concatenation(
        &mut self,
        pieces: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let string = self.special(SpecialType::String);
        let values: Vec<BoundExpression> = pieces
            .into_iter()
            .map(|piece| match piece.kind {
                BoundExpressionKind::StringInsert { value, .. } => *value,
                _ => piece,
            })
            .collect();
        match <[BoundExpression; 1]>::try_from(values) {
            Ok([value]) => Some(match value.kind {
                BoundExpressionKind::Literal(_) => value,
                _ => BoundExpression::new(
                    BoundExpressionKind::Binary {
                        operator: BinaryOperator::Coalesce,
                        left: Box::new(value),
                        right: Box::new(BoundExpression::new(
                            BoundExpressionKind::Literal(ConstantValue::String(String::new())),
                            string.clone(),
                            span,
                        )),
                    },
                    string,
                    span,
                ),
            }),
            Err(values) if values.is_empty() => Some(BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::String(String::new())),
                string,
                span,
            )),
            Err(values) => self.call_static(&string, "Concat", values, span),
        }
    }

    /// `string.Format` of the pieces' text with the holes numbered in it,
    /// and the holes' values as `object`s.
    fn format_call(
        &mut self,
        pieces: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let string = self.special(SpecialType::String);
        let object = self.special(SpecialType::Object);
        let (format, holes) = composite_format(pieces);
        let mut arguments = vec![BoundExpression::new(
            BoundExpressionKind::Literal(ConstantValue::String(format)),
            string.clone(),
            span,
        )];
        for hole in holes {
            let boxed = self.convert(hole, &object);
            arguments.push(boxed);
        }
        let floor = self.body.diagnostics.len();
        let call = self.call_static(&string, "Format", arguments, span);
        if call.is_none() {
            self.body.diagnostics.truncate(floor);
        }
        call
    }

    /// The pieces appended to a `DefaultInterpolatedStringHandler`, and its
    /// `ToStringAndClear()`, where the handler and everything it is asked
    /// for are there.
    fn default_handler_string(
        &mut self,
        pieces: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let handler = self.framework_type(DEFAULT_HANDLER)?;
        let string = self.special(SpecialType::String);
        let floor = self.body.diagnostics.len();
        let built = self
            .build_handler(&handler, pieces, Vec::new(), false, span)
            .and_then(|(mut steps, local)| {
                let receiver =
                    BoundExpression::new(BoundExpressionKind::Local(local), handler.clone(), span);
                let finished =
                    self.call_named_on(receiver, "ToStringAndClear", Vec::new(), &[], span)?;
                steps.push(finished);
                Some(BoundExpression::new(
                    BoundExpressionKind::Sequence(steps),
                    string,
                    span,
                ))
            });
        if built.is_none() {
            self.body.diagnostics.truncate(floor);
        }
        built
    }
}

/// The temporaries interpolated string handlers were made with, while the
/// arguments of one call are converted in order (§12.8.3 of C# 10).
#[derive(Default)]
pub(super) struct HandlerCapture {
    /// The arguments kept, by position: one named twice is kept once.
    arguments: HashMap<usize, LocalId>,
    /// The one the call's receiver is to be kept in, where a handler named
    /// it.
    pub(super) receiver: Option<LocalId>,
}

/// Where an expression being lowered stands.
#[derive(Clone, Copy, Default)]
struct Place {
    /// Inside a lambda an expression tree describes.
    in_tree: bool,
}

/// The pieces of an interpolated string, or of an addition of them, left to
/// right: text as string constants, holes as [`StringInsert`]s.
///
/// [`StringInsert`]: BoundExpressionKind::StringInsert
fn pieces_of(value: BoundExpression) -> Vec<BoundExpression> {
    match value.kind {
        BoundExpressionKind::InterpolatedString(parts) => parts,
        BoundExpressionKind::Binary { left, right, .. } => {
            let mut pieces = pieces_of(*left);
            pieces.extend(pieces_of(*right));
            pieces
        }
        _ => Vec::new(),
    }
}

/// The text of an interpolated string with its holes numbered, and the
/// values for the holes beside it: what `string.Format` and
/// `FormattableStringFactory.Create` both take. A brace of the text is
/// doubled in it, which is how a composite format spells one.
fn composite_format(pieces: Vec<BoundExpression>) -> (String, Vec<BoundExpression>) {
    let mut format = String::new();
    let mut holes = Vec::new();
    for piece in pieces {
        match piece.kind {
            BoundExpressionKind::StringInsert {
                value,
                alignment,
                format: clause,
            } => {
                format.push('{');
                format.push_str(&holes.len().to_string());
                format.push_str(&composite_clauses(alignment, clause.as_deref()));
                format.push('}');
                holes.push(*value);
            }
            BoundExpressionKind::Literal(ConstantValue::String(text)) => {
                for ch in text.chars() {
                    format.push(ch);
                    if matches!(ch, '{' | '}') {
                        format.push(ch);
                    }
                }
            }
            _ => {}
        }
    }
    (format, holes)
}

/// How an interpolated string was written, which decides how its text reads.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Spelling {
    /// `$"..."`: escapes, and a doubled brace for a brace.
    Regular,
    /// `$@"..."`: a doubled quote for a quote, and a doubled brace for a
    /// brace.
    Verbatim,
    /// `$"""..."""` on one line: the text as it stands.
    SingleLineRaw,
    /// `$"""` over several lines: the text less the lines of the fences, and
    /// less the closing fence's indentation where a line starts with it.
    MultiLineRaw,
}

/// A piece of an interpolated string as written.
enum Content {
    /// The text between two holes, as the string it stands for.
    Text(String, TextSpan),
    /// A hole, and how the string around it was written, which its format
    /// is read by.
    Hole(SyntaxNode, Spelling),
}

/// The pieces of an interpolated string in order, as Roslyn's parser hands
/// them to its binder: each run of text between holes once, as the string it
/// stands for, and the holes.
///
/// The lexer may cut one run into several tokens — a run of quotes or braces
/// ends one — so a run is joined before it is read. A multi-line raw
/// string's first and last lines are its fences', and go; a run left with no
/// text is no piece at all, where one whose lines were only indentation is a
/// piece of no text, as in Roslyn.
fn interpolation_contents(node: &SyntaxNode) -> Vec<Content> {
    let spelling = match node.first_token().map(|token| token.kind()) {
        Some(SyntaxKind::InterpolatedVerbatimStringStartToken) => Spelling::Verbatim,
        Some(SyntaxKind::InterpolatedSingleLineRawStringStartToken) => Spelling::SingleLineRaw,
        Some(SyntaxKind::InterpolatedMultiLineRawStringStartToken) => Spelling::MultiLineRaw,
        _ => Spelling::Regular,
    };
    let mut runs: Vec<Result<(String, TextSpan), SyntaxNode>> = Vec::new();
    for child in node.children() {
        match child.kind() {
            SyntaxKind::InterpolatedStringText => {
                let (text, span) = (child.text(), child.span());
                match runs.last_mut() {
                    Some(Ok((run, whole))) => {
                        run.push_str(&text);
                        *whole = whole.union(span);
                    }
                    _ => runs.push(Ok((text, span))),
                }
            }
            SyntaxKind::Interpolation => runs.push(Err(child)),
            _ => {}
        }
    }
    let indentation = if spelling == Spelling::MultiLineRaw {
        trim_raw_fences(&mut runs)
    } else {
        String::new()
    };
    let mut contents = Vec::with_capacity(runs.len());
    for (index, run) in runs.into_iter().enumerate() {
        match run {
            Err(hole) => contents.push(Content::Hole(hole, spelling)),
            Ok((text, _)) if text.is_empty() => {}
            Ok((text, span)) => {
                let value = match spelling {
                    Spelling::Regular => unescape(&text, true),
                    Spelling::Verbatim => unverbatim(&text, true),
                    Spelling::SingleLineRaw => text,
                    Spelling::MultiLineRaw => dedent(&text, &indentation, index == 0),
                };
                contents.push(Content::Text(value, span));
            }
        }
    }
    contents
}

/// Takes a multi-line raw string's fences' lines off its text — up to the
/// first line break, which ends the opening fence's line, and from the last
/// one on, which starts the closing fence's — and gives back what the
/// closing fence is indented by.
fn trim_raw_fences(runs: &mut [Result<(String, TextSpan), SyntaxNode>]) -> String {
    let indentation = match runs.last() {
        Some(Ok((text, _))) => text
            .rfind('\n')
            .map_or_else(String::new, |at| text[at + 1..].to_string()),
        _ => String::new(),
    };
    let count = runs.len();
    for (index, run) in runs.iter_mut().enumerate() {
        let Ok((text, _)) = run else {
            continue;
        };
        let start = if index == 0 {
            text.find('\n').map_or(text.len(), |at| at + 1)
        } else {
            0
        };
        let end = if index + 1 == count {
            text.rfind('\n').map_or(text.len(), |at| {
                if text[..at].ends_with('\r') {
                    at - 1
                } else {
                    at
                }
            })
        } else {
            text.len()
        };
        *text = text
            .get(start..end.max(start))
            .unwrap_or_default()
            .to_string();
    }
    indentation
}

/// A multi-line raw string's run with the closing fence's indentation taken
/// off each line it starts. A run after a hole goes on the hole's line up to
/// its first line break, and that much is kept whole; a line indented less —
/// a blank one — loses what it has.
fn dedent(text: &str, indentation: &str, first: bool) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    if !first {
        match rest.find('\n') {
            Some(at) => {
                out.push_str(&rest[..=at]);
                rest = &rest[at + 1..];
            }
            None => return rest.to_string(),
        }
    }
    let width = indentation.chars().count();
    while !rest.is_empty() {
        let skip: usize = rest
            .chars()
            .take(width)
            .take_while(|ch| ch.is_whitespace() && !matches!(ch, '\n' | '\r'))
            .map(char::len_utf8)
            .sum();
        rest = &rest[skip..];
        match rest.find('\n') {
            Some(at) => {
                out.push_str(&rest[..=at]);
                rest = &rest[at + 1..];
            }
            None => {
                out.push_str(rest);
                rest = "";
            }
        }
    }
    out
}

/// The text of a regular interpolated string as it reads: its escapes
/// decoded, and — where `braces` — a doubled brace as one.
fn unescape(text: &str, braces: bool) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    // `\x` takes up to four hex digits; `\u` four and `\U` eight exactly.
    let hex = |chars: &mut std::iter::Peekable<std::str::Chars<'_>>, most: usize, exact: bool| {
        let mut value = 0u32;
        let mut digits = 0;
        while digits < most {
            let Some(digit) = chars.peek().and_then(|ch| ch.to_digit(16)) else {
                break;
            };
            chars.next();
            value = value * 16 + digit;
            digits += 1;
        }
        (digits > 0 && (!exact || digits == most)).then_some(value)
    };
    while let Some(ch) = chars.next() {
        match ch {
            '\\' => match chars.next() {
                Some('\'') => out.push('\''),
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('0') => out.push('\0'),
                Some('a') => out.push('\u{7}'),
                Some('b') => out.push('\u{8}'),
                Some('e') => out.push('\u{1B}'),
                Some('f') => out.push('\u{C}'),
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some('v') => out.push('\u{B}'),
                Some(kind @ ('x' | 'u' | 'U')) => {
                    let value = match kind {
                        'x' => hex(&mut chars, 4, false),
                        'u' => hex(&mut chars, 4, true),
                        _ => hex(&mut chars, 8, true),
                    };
                    let Some(value) = value else {
                        continue;
                    };
                    // A surrogate pair spells one character; a lone
                    // surrogate cannot be held here, and stands as the
                    // replacement character.
                    if (0xD800..=0xDBFF).contains(&value) {
                        let mut ahead = chars.clone();
                        if ahead.next() == Some('\\')
                            && ahead.next() == Some('u')
                            && let Some(low) = hex(&mut ahead, 4, true)
                            && (0xDC00..=0xDFFF).contains(&low)
                        {
                            chars = ahead;
                            let combined = 0x1_0000 + ((value - 0xD800) << 10) + (low - 0xDC00);
                            out.push(
                                char::from_u32(combined).unwrap_or(char::REPLACEMENT_CHARACTER),
                            );
                            continue;
                        }
                    }
                    out.push(char::from_u32(value).unwrap_or(char::REPLACEMENT_CHARACTER));
                }
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            },
            '{' | '}' if braces && chars.peek() == Some(&ch) => {
                chars.next();
                out.push(ch);
            }
            _ => out.push(ch),
        }
    }
    out
}

/// The text of a verbatim interpolated string as it reads: a doubled quote
/// as one, and — where `braces` — a doubled brace as one.
fn unverbatim(text: &str, braces: bool) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        let doubled = ch == '"' || (braces && matches!(ch, '{' | '}'));
        if doubled && chars.peek() == Some(&ch) {
            chars.next();
        }
        out.push(ch);
    }
    out
}

/// The format of a hole, after its colon, as the text it stands for: the
/// escapes of a regular string are read in it, and a verbatim one's doubled
/// quote (Roslyn reads it as a string literal of the same kind).
fn format_of(clause: &SyntaxNode, spelling: Spelling) -> String {
    let text = clause.text();
    let written = text.split_once(':').map_or(text.as_str(), |(_, rest)| rest);
    match spelling {
        Spelling::Regular => unescape(written, false),
        Spelling::Verbatim => unverbatim(written, false),
        Spelling::SingleLineRaw | Spelling::MultiLineRaw => written.to_string(),
    }
}
