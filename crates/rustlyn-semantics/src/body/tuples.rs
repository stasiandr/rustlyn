//! Deconstruction and tuples: `var (a, b) = x`, `Deconstruct`, and `==` on
//! tuples.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, FoundDeconstruct, TupleSide, retype_default_beside, typeless};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundPattern, BoundPatternKind, BoundSymbol,
    ConstantValue, LocalId, UnaryOperator,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, RefKind, SymbolId, SymbolKind};
use crate::types::{TupleElement, Type};

/// One place on the left of a deconstruction, found before anything on
/// either side is evaluated.
enum Target {
    /// `var x` or `int x`: a variable the deconstruction brings into being,
    /// declared once the part it is given says what a `var` one is. The
    /// branches of a conditional are taken apart into the same variables, so
    /// the local, once there is one, is kept.
    Declare {
        designation: SyntaxNode,
        written: Option<Type>,
        local: Option<LocalId>,
    },
    /// `_`, or `int _`: nothing is written, but a written type still converts
    /// the part — `(int _, var x) = (c, 1)` runs `c`'s conversion.
    Discard { written: Option<Type> },
    /// A variable that is already there, bound, with whatever its receiver
    /// and indices evaluate already evaluated.
    Place(BoundExpression),
    /// `var ((a, b), c)` and `((a, b), c)`: a part that is itself taken
    /// apart.
    Nested {
        syntax: SyntaxNode,
        targets: Vec<Target>,
    },
}

/// What a deconstruction does, by the phase C# does it in (Roslyn's
/// `DeconstructionSideEffects`): each phase runs whole, across every level
/// of a nested deconstruction, before the next one starts.
#[derive(Default)]
struct Phases {
    /// The right-hand side, as far as its tuple literals reach: their
    /// elements, in order.
    init: Vec<BoundExpression>,
    /// Every `Deconstruct` called, and every tuple value held to be read
    /// field by field.
    deconstructions: Vec<BoundExpression>,
    /// Every part converted to the type of its place.
    conversions: Vec<BoundExpression>,
    /// Every part stored in its place.
    assignments: Vec<BoundExpression>,
}

impl BodyBinder<'_> {
    /// `var (a, b) = point;`, `(x, y) = (y, x);`, and every mix of the two.
    ///
    /// C# evaluates a deconstruction in phases (Roslyn's
    /// `RewriteDeconstruction`), each across the whole of it however deep it
    /// nests: the left-hand side's receivers and indices, and what a
    /// `ref`-returning member there hands back; then the right-hand side and
    /// every `Deconstruct` it is taken apart by; then every conversion of a
    /// part to its place; and only then every assignment. `(a.X, b.Y) = c`,
    /// whose `Deconstruct` hands out two values that convert to `int`, runs
    /// `a`, `b`, `c`, `Deconstruct`, both conversions, and then both setters.
    /// What comes out of the binder is that order, spelled as the calls,
    /// temporaries and assignments it takes, so that no backend has to know
    /// deconstruction exists.
    pub(super) fn bind_deconstruction(
        &mut self,
        target: &SyntaxNode,
        value_node: &SyntaxNode,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        // The left is bound and its places evaluated first: `(M(out var
        // x).P, x) = (1, x)` calls `M` before it reads `x`. A reference to a
        // place does not survive an `await`, and with one anywhere in the
        // deconstruction what the place is reached through is kept instead.
        let references = !awaits_in(target) && !awaits_in(value_node);
        let mut effects = Vec::new();
        let targets = self.deconstruction_targets(target, &mut effects, references);
        let value = self.bind_expression(value_node);
        self.deconstruct_after(target, targets, value, effects, span)
    }

    /// The same, for a value that is already bound: `foreach (var (a, b) in
    /// pairs)` takes apart something nobody named. The result is worth the
    /// tuple of what the places were given, which is what `var t = (a, b) =
    /// pair` holds; [`Self::deconstruct_into`] is the same without it.
    pub(super) fn deconstruct_value(
        &mut self,
        target: &SyntaxNode,
        value: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let mut effects = Vec::new();
        let targets = self.deconstruction_targets(target, &mut effects, true);
        self.deconstruct_after(target, targets, value, effects, span)
    }

    /// A deconstruction whose places are found and whose value is bound:
    /// what finding the places evaluated, and then the rest.
    fn deconstruct_after(
        &mut self,
        target: &SyntaxNode,
        targets: Option<Vec<Target>>,
        value: BoundExpression,
        mut effects: Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let taken_apart =
            targets.and_then(|mut targets| self.take_apart(target, &mut targets, value, span));
        let Some(taken_apart) = taken_apart else {
            // `var (x, y) = "";` cannot be taken apart, and that has been
            // said; `x` and `y` are still declared, so that what reads them
            // further on is not told they do not exist.
            self.declare_left_behind(target);
            return None;
        };
        // `var u = ((x, y) = t);` holds a `(x, y)`: the left names the
        // elements of the value as a tuple literal written there would.
        let mut ty = taken_apart.ty.clone();
        if target.kind() == SyntaxKind::TupleExpression
            && let Type::Tuple(elements) = &mut ty
        {
            let arguments: Vec<SyntaxNode> = target
                .children()
                .filter(|child| child.kind() == SyntaxKind::Argument)
                .collect();
            if arguments.len() == elements.len() {
                for (element, argument) in elements.iter_mut().zip(&arguments) {
                    if element.name.is_none() {
                        element.name = argument
                            .children()
                            .find(|child| child.kind().is_expression())
                            .as_ref()
                            .and_then(super::expressions::inferred_element_name);
                    }
                }
            }
        }
        effects.push(taken_apart);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(effects),
            ty,
            span,
        ))
    }

    /// The variables a deconstruction that could not be done was to
    /// declare, declared as errors where it did not get to them.
    fn declare_left_behind(&mut self, target: &SyntaxNode) {
        for designation in target
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::SingleVariableDesignation)
        {
            let Some(token) = designation
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            else {
                continue;
            };
            if !self
                .body
                .locals
                .iter()
                .any(|local| local.span == token.span())
            {
                self.declare_local(token.value_text(), Type::Error, token.span());
            }
        }
    }

    /// The places on the left of a deconstruction, in its shape: a variable
    /// to declare, a discard, a place bound and made to stay the place it is
    /// now, or a part taken apart again. The two kinds mix freely: `(var
    /// first, rest) = pair;` declares `first` and assigns to a `rest` that
    /// was already in scope.
    fn deconstruction_targets(
        &mut self,
        target: &SyntaxNode,
        effects: &mut Vec<BoundExpression>,
        references: bool,
    ) -> Option<Vec<Target>> {
        let mut targets = Vec::new();
        match target.kind() {
            // `var (a, b)`: a declaration expression on the left of an `=`,
            // or the pattern of an `is`. Both hold the same designation, and
            // both mean the same thing. A nested designation is the same
            // shape one level down.
            SyntaxKind::DeclarationExpression
            | SyntaxKind::VarPattern
            | SyntaxKind::ParenthesizedVariableDesignation => {
                let designation = if target.kind() == SyntaxKind::ParenthesizedVariableDesignation {
                    target.clone()
                } else {
                    target.child_of_kind(SyntaxKind::ParenthesizedVariableDesignation)?
                };
                for part in designation.children() {
                    match part.kind() {
                        SyntaxKind::SingleVariableDesignation => targets.push(Target::Declare {
                            designation: part,
                            written: None,
                            local: None,
                        }),
                        SyntaxKind::DiscardDesignation => {
                            targets.push(Target::Discard { written: None });
                        }
                        SyntaxKind::ParenthesizedVariableDesignation => {
                            let nested = self.deconstruction_targets(&part, effects, references)?;
                            targets.push(Target::Nested {
                                syntax: part,
                                targets: nested,
                            });
                        }
                        _ => {}
                    }
                }
            }
            SyntaxKind::TupleExpression => {
                for argument in target.children() {
                    if argument.kind() != SyntaxKind::Argument {
                        continue;
                    }
                    let inner = argument
                        .children()
                        .find(|child| child.kind().is_expression())?;
                    match inner.kind() {
                        // `(var (a, b), c)` and `((a, b), c)` nest a
                        // deconstruction inside the tuple.
                        SyntaxKind::DeclarationExpression
                            if inner
                                .child_of_kind(SyntaxKind::ParenthesizedVariableDesignation)
                                .is_some() =>
                        {
                            let nested =
                                self.deconstruction_targets(&inner, effects, references)?;
                            targets.push(Target::Nested {
                                syntax: inner,
                                targets: nested,
                            });
                        }
                        SyntaxKind::TupleExpression => {
                            let nested =
                                self.deconstruction_targets(&inner, effects, references)?;
                            targets.push(Target::Nested {
                                syntax: inner,
                                targets: nested,
                            });
                        }
                        // `int x` says what `x` is; `var x` leaves it to the
                        // part it is given.
                        SyntaxKind::DeclarationExpression => {
                            let designation = inner.children().find(|child| {
                                matches!(
                                    child.kind(),
                                    SyntaxKind::SingleVariableDesignation
                                        | SyntaxKind::DiscardDesignation
                                )
                            })?;
                            let written = inner
                                .children()
                                .find(|child| child.kind().is_type_node())
                                .filter(|node| !super::declares_var(node))
                                .map(|node| self.resolve(&node));
                            if designation.kind() == SyntaxKind::DiscardDesignation {
                                targets.push(Target::Discard { written });
                            } else {
                                targets.push(Target::Declare {
                                    designation,
                                    written,
                                    local: None,
                                });
                            }
                        }
                        // A bare `_` is a discard as well, unless something in
                        // scope answers to that name.
                        SyntaxKind::IdentifierName
                            if inner.text().trim() == "_" && self.lookup_local("_").is_none() =>
                        {
                            targets.push(Target::Discard { written: None });
                        }
                        // Binding it is the whole point: the name has to
                        // resolve like any other.
                        _ => {
                            let place = self.bind_expression(&inner);
                            targets
                                .push(Target::Place(self.hold_place(place, effects, references)));
                        }
                    }
                }
            }
            _ => return None,
        }
        (!targets.is_empty()).then_some(targets)
    }

    /// A value taken apart into places already found: a conditional branch
    /// by branch, anything else in phases.
    fn take_apart(
        &mut self,
        syntax: &SyntaxNode,
        targets: &mut [Target],
        value: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if is_value_conditional(&value) {
            return self.take_apart_branches(syntax, targets, value, span);
        }
        // `(x, y) = (1, 2)`: a tuple literal on the right is converted
        // element by element to the places it goes to first (Roslyn's
        // `FixTupleLiteral`), so that an element's conversion is part of
        // evaluating it. Anything else converts only once taken apart.
        let value = self.fix_tuple_literal(targets, value);
        self.take_apart_in_phases(syntax, targets, value, span)
    }

    /// `(x, y) = flag ? (1, 2) : default` takes each branch apart on its own
    /// into the same places, which were evaluated once, before either
    /// (Roslyn's `RewriteDeconstruction`): the tuple literal of the branch
    /// taken is never made into a tuple, and its elements convert only once
    /// all of them are evaluated. It is worth what that branch is.
    fn take_apart_branches(
        &mut self,
        syntax: &SyntaxNode,
        targets: &mut [Target],
        value: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let BoundExpressionKind::Conditional {
            condition,
            consequence,
            alternative,
        } = value.kind
        else {
            return self.take_apart_in_phases(syntax, targets, value, span);
        };
        let consequence = self.take_apart_branches(syntax, targets, *consequence, span)?;
        let alternative = self.take_apart_branches(syntax, targets, *alternative, span)?;
        let ty = consequence.ty.clone();
        Some(BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition,
                consequence: Box::new(consequence),
                alternative: Box::new(alternative),
            },
            ty,
            span,
        ))
    }

    /// The phases one after another, and then the tuple the deconstruction
    /// is worth.
    fn take_apart_in_phases(
        &mut self,
        syntax: &SyntaxNode,
        targets: &mut [Target],
        value: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let mut phases = Phases::default();
        let worth = self.deconstruct_parts(syntax, targets, value, &mut phases, true, span)?;
        let Phases {
            mut init,
            deconstructions,
            conversions,
            assignments,
        } = phases;
        init.extend(deconstructions);
        init.extend(conversions);
        init.extend(assignments);
        let ty = worth.ty.clone();
        init.push(worth);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(init),
            ty,
            span,
        ))
    }

    /// One level of a deconstruction: the parts `value` falls into, each
    /// converted and assigned to its place or taken apart again, with what
    /// that takes added to the phase it belongs to. The value is worth the
    /// tuple of what the places were given (§12.21.2).
    ///
    /// `early` says whether the right-hand side is still being evaluated:
    /// the elements of a tuple literal are, until a `Deconstruct` or a whole
    /// tuple is reached, and what that hands out is past the first phase —
    /// `((a, b), c) = (Pair(), F())` calls `F` before `Pair`, as Roslyn does.
    fn deconstruct_parts(
        &mut self,
        syntax: &SyntaxNode,
        targets: &mut [Target],
        value: BoundExpression,
        phases: &mut Phases,
        mut early: bool,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let (value_span, value_ty) = (value.span, value.ty.clone());
        let parts = match value.kind {
            BoundExpressionKind::TupleCreation(elements) => elements,
            kind => {
                let value = BoundExpression::new(kind, value_ty.clone(), value_span);
                if let Some(types) = self.binder.tuple_elements(&value_ty) {
                    // A tuple element is a field: the tuple is held, and each
                    // part read out of it.
                    if types.len() != targets.len() {
                        return None;
                    }
                    early = false;
                    if matches!(value.kind, BoundExpressionKind::Default(_)) {
                        types
                            .into_iter()
                            .map(|ty| {
                                BoundExpression::new(
                                    BoundExpressionKind::Default(ty.clone()),
                                    ty,
                                    span,
                                )
                            })
                            .collect()
                    } else {
                        let held = self.declare_synthetic_local("tuple", value_ty.clone());
                        phases.deconstructions.push(BoundExpression::new(
                            BoundExpressionKind::Assignment {
                                target: Box::new(BoundExpression::new(
                                    BoundExpressionKind::Local(held),
                                    value_ty.clone(),
                                    span,
                                )),
                                value: Box::new(value),
                            },
                            value_ty.clone(),
                            span,
                        ));
                        types
                            .into_iter()
                            .enumerate()
                            .map(|(at, ty)| self.tuple_element(held, &value_ty, at, ty, span))
                            .collect()
                    }
                } else {
                    let found = self.deconstruct_of(&value, targets)?;
                    // `Deconstruct` is called on what the value was when it
                    // was evaluated, and what it hands out is past the first
                    // phase.
                    let receiver = if early {
                        self.evaluate_early(value, &mut phases.init)
                    } else {
                        self.evaluate_early(value, &mut phases.deconstructions)
                    };
                    early = false;
                    let (call, parts) = self.deconstruct_call(syntax, found, receiver, span);
                    phases.deconstructions.push(call);
                    parts
                }
            }
        };
        if parts.len() != targets.len() {
            return None;
        }
        let mut values = Vec::with_capacity(parts.len());
        for (target, part) in targets.iter_mut().zip(parts) {
            if let Target::Nested { syntax, targets } = target {
                let syntax = syntax.clone();
                values.push(self.deconstruct_parts(&syntax, targets, part, phases, early, span)?);
                continue;
            }
            // A part of the right-hand side still being evaluated is
            // evaluated now, into a temporary where reading it later could
            // read something else: `(a, b) = (b, a)` swaps.
            let part = if early {
                self.evaluate_early(part, &mut phases.init)
            } else {
                part
            };
            let (place, ty) = self.place_of(target, &part)?;
            let converted = if part.ty == ty || ty.is_error() || part.ty.is_error() {
                part
            } else {
                let converted = self.convert(part, &ty);
                self.evaluate_early(converted, &mut phases.conversions)
            };
            if let Some(place) = place {
                phases.assignments.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(place),
                        value: Box::new(converted.clone()),
                    },
                    ty,
                    span,
                ));
            }
            values.push(converted);
        }
        Some(self.tuple_of(values, span))
    }

    /// Where a part goes, and the type it is converted to on the way: the
    /// place's, the one written, or for a `var` the part's own — which is
    /// when a variable the deconstruction declares comes into being.
    fn place_of(
        &mut self,
        target: &mut Target,
        part: &BoundExpression,
    ) -> Option<(Option<BoundExpression>, Type)> {
        match target {
            Target::Place(place) => Some((Some(place.clone()), place.ty.clone())),
            Target::Discard { written } => {
                Some((None, written.clone().unwrap_or_else(|| part.ty.clone())))
            }
            Target::Declare {
                designation,
                written,
                local,
            } => {
                let declared = match *local {
                    Some(declared) => declared,
                    None => {
                        let token = designation
                            .child_tokens()
                            .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
                        let ty = match written {
                            Some(ty) => ty.clone(),
                            // `var (x, y) = (null, 1)`: nothing says what `x`
                            // is.
                            None if matches!(part.ty, Type::Null) || typeless(part) => {
                                self.report(
                                    ErrorCode::ErrTypeInferenceFailedForImplicitlyTypedDeconstructionVariable,
                                    token.span(),
                                    &[token.value_text()],
                                );
                                Type::Error
                            }
                            None => part.ty.clone(),
                        };
                        let declared =
                            self.declare_local(token.value_text(), ty.clone(), token.span());
                        self.body.types.insert(designation.span(), ty);
                        *local = Some(declared);
                        declared
                    }
                };
                let ty = self.body.locals[declared.0 as usize].ty.clone();
                Some((
                    Some(BoundExpression::new(
                        BoundExpressionKind::Local(declared),
                        ty.clone(),
                        designation.span(),
                    )),
                    ty,
                ))
            }
            Target::Nested { .. } => None,
        }
    }

    /// A tuple literal converted, element by element, to the types of the
    /// places it goes to where they have one (Roslyn's `FixTupleLiteral`):
    /// `(x, y) = (new D1(), new D2())` converts each `D` as it is made,
    /// before the next one is, and `(s, _) = (null, 1)` gives the `null` a
    /// type — as `(E, _) = (Handler, 1)` makes the method group the delegate
    /// `E` is. A `var` or a `_` takes the element as it is.
    fn fix_tuple_literal(&mut self, targets: &[Target], value: BoundExpression) -> BoundExpression {
        let (span, ty) = (value.span, value.ty.clone());
        let elements = match value.kind {
            BoundExpressionKind::TupleCreation(elements) if elements.len() == targets.len() => {
                elements
            }
            kind => return BoundExpression::new(kind, ty, span),
        };
        let fixed: Vec<BoundExpression> = elements
            .into_iter()
            .zip(targets)
            .map(|(element, target)| {
                let wanted = match target {
                    Target::Nested { targets, .. } => {
                        return self.fix_tuple_literal(targets, element);
                    }
                    Target::Place(place) => Some(&place.ty),
                    Target::Declare { written, .. } | Target::Discard { written } => {
                        written.as_ref()
                    }
                };
                match wanted {
                    Some(wanted) if !wanted.is_error() => self.convert(element, wanted),
                    _ => element,
                }
            })
            .collect();
        let ty = Type::Tuple(
            fixed
                .iter()
                .map(|element| TupleElement {
                    name: None,
                    ty: element.ty.clone(),
                })
                .collect(),
        );
        BoundExpression::new(BoundExpressionKind::TupleCreation(fixed), ty, span)
    }

    /// The `Deconstruct` that takes `value` apart into as many parts as
    /// there are places, or, where there is none, `None` and why (CS8129,
    /// and CS8130 on each `var` whose type was to come from it).
    fn deconstruct_of(
        &mut self,
        value: &BoundExpression,
        targets: &[Target],
    ) -> Option<FoundDeconstruct> {
        if let Some(found) = self.find_deconstruct(&value.ty, targets.len()) {
            return Some(found);
        }
        if !value.ty.is_error() && !typeless(value) {
            let shown = value.ty.display(self.binder.compilation().symbols());
            self.report(
                ErrorCode::ErrMissingDeconstruct,
                value.span,
                &[&shown, &targets.len().to_string()],
            );
            for target in targets {
                if let Target::Declare {
                    designation,
                    written: None,
                    ..
                } = target
                    && let Some(token) = designation
                        .child_tokens()
                        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                {
                    self.report(
                        ErrorCode::ErrTypeInferenceFailedForImplicitlyTypedDeconstructionVariable,
                        token.span(),
                        &[token.value_text()],
                    );
                }
            }
        }
        None
    }

    /// `receiver.Deconstruct(out a, out b)`, or the extension's call with the
    /// receiver first, each part landing in a temporary of its parameter's
    /// type: the call, and a read of each temporary. A part of another type
    /// than its place's is converted afterwards — `(x, y) = c` with a `long
    /// x` and an `out int` — and an indexer or a property is no place an
    /// `out` can point at anyway.
    fn deconstruct_call(
        &mut self,
        syntax: &SyntaxNode,
        found: FoundDeconstruct,
        receiver: BoundExpression,
        span: TextSpan,
    ) -> (BoundExpression, Vec<BoundExpression>) {
        let deconstruct = found.method;
        let mut arguments = Vec::with_capacity(found.parameters.len() + 1);
        let mut parts = Vec::with_capacity(found.parameters.len());
        for declared in found.parameters {
            let part = self.declare_synthetic_local("part", declared.clone());
            let read =
                BoundExpression::new(BoundExpressionKind::Local(part), declared.clone(), span);
            arguments.push(BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Out,
                    operand: Box::new(read.clone()),
                },
                declared,
                span,
            ));
            parts.push(read);
        }
        self.body
            .references
            .insert(syntax.span(), BoundSymbol::Declared(deconstruct));
        let call = if let Some(receiver_type) = found.receiver {
            // An extension's receiver is its first argument.
            let receiver = self.convert(receiver, &receiver_type);
            // `this in C value` and `this ref C value` take the receiver by
            // reference.
            let symbols = self.binder.compilation().symbols();
            let ref_kind = symbols
                .get(deconstruct)
                .as_method()
                .and_then(|detail| detail.parameters.first().copied())
                .and_then(|parameter| symbols.get(parameter).as_parameter())
                .map_or(RefKind::None, |detail| detail.ref_kind);
            let receiver = if ref_kind == RefKind::None {
                receiver
            } else {
                let ty = receiver.ty.clone();
                BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind: ref_kind,
                        operand: Box::new(receiver),
                    },
                    ty,
                    span,
                )
            };
            arguments.insert(0, receiver);
            BoundExpression::new(
                BoundExpressionKind::Call {
                    receiver: None,
                    method: deconstruct,
                    type_arguments: found.type_arguments,
                    arguments,
                    virtual_call: false,
                },
                Type::Void,
                span,
            )
        } else {
            BoundExpression::new(
                BoundExpressionKind::Call {
                    receiver: Some(Box::new(receiver)),
                    method: deconstruct,
                    type_arguments: Vec::new(),
                    arguments,
                    virtual_call: self.is_virtual_call(deconstruct, None),
                },
                Type::Void,
                span,
            )
        };
        (call, parts)
    }

    /// A value of the right-hand side evaluated now, into a temporary unless
    /// reading it later is sure to read the same (Roslyn's
    /// `EvaluateSideEffectingArgumentToTemp`): a constant, a `default`, the
    /// `this` of a class. A variable is read now too, since the
    /// deconstruction may be what assigns it.
    fn evaluate_early(
        &mut self,
        value: BoundExpression,
        into: &mut Vec<BoundExpression>,
    ) -> BoundExpression {
        let settled = match &value.kind {
            BoundExpressionKind::Literal(_)
            | BoundExpressionKind::Default(_)
            | BoundExpressionKind::Base
            | BoundExpressionKind::TypeExpression(_) => true,
            // A struct's `this` is a variable, and `Deconstruct` on it would
            // run on the struct itself rather than on what it was.
            BoundExpressionKind::This => value
                .ty
                .is_reference_type(self.binder.compilation().symbols()),
            _ => {
                typeless(&value)
                    || value.ty.is_error()
                    || matches!(value.ty, Type::Null | Type::Void)
            }
        };
        if settled {
            value
        } else {
            self.hold("part", value, into)
        }
    }

    /// A place on the left of a deconstruction, made to stay the place it is
    /// now whatever the right-hand side does to what it is reached through
    /// (Roslyn's `TransformCompoundAssignmentLHS`): the receiver of a field,
    /// a property or an indexer is held, and so are an indexer's arguments;
    /// an array element, a field of a struct found through one, and what a
    /// `ref`-returning member hands back are held as a reference, found now.
    /// `(a[i], i) = (1, 2)` writes the element `i` was.
    fn hold_place(
        &mut self,
        place: BoundExpression,
        spilled: &mut Vec<BoundExpression>,
        references: bool,
    ) -> BoundExpression {
        let (span, ty) = (place.span, place.ty.clone());
        // `(P, P) = c` on a `static ref int P` calls the getter twice before
        // `Deconstruct` runs, and writes through the references it gave.
        if references && self.is_returned_reference(&place) {
            return self.hold_reference(place, spilled);
        }
        match place.kind {
            // What comes before the last step is part of finding the place.
            BoundExpressionKind::Sequence(mut steps) if !steps.is_empty() => {
                let last = steps.pop().expect("not empty");
                spilled.extend(steps);
                self.hold_place(last, spilled, references)
            }
            BoundExpressionKind::Property {
                receiver: Some(receiver),
                property,
            } if !self.is_static(property) => {
                let receiver = self.hold_receiver(*receiver, spilled, references);
                BoundExpression::new(
                    BoundExpressionKind::Property {
                        receiver: Some(Box::new(receiver)),
                        property,
                    },
                    ty,
                    span,
                )
            }
            // An indexer's receiver and its indices are evaluated before the
            // right-hand side as well: `(item[^1], _) = (F(ref item), 0)`
            // reads the `Length` it counts from first.
            BoundExpressionKind::IndexerAccess {
                receiver,
                indexer,
                arguments,
            } => {
                let variable = (*receiver).clone();
                let generic = self.kept_generic(&receiver);
                let kept = self.hold_receiver(*receiver, spilled, references);
                let arguments = arguments
                    .into_iter()
                    .map(|mut argument| {
                        if generic {
                            counted_from(&mut argument, &variable, &kept, self);
                        }
                        if self.reads_the_same(&argument)
                            || matches!(argument.kind, BoundExpressionKind::RefArgument { .. })
                        {
                            argument
                        } else {
                            self.hold("argument", argument, spilled)
                        }
                    })
                    .collect();
                BoundExpression::new(
                    BoundExpressionKind::IndexerAccess {
                        receiver: Box::new(kept),
                        indexer,
                        arguments,
                    },
                    ty,
                    span,
                )
            }
            // A field of a class is reached through the reference held now;
            // a field of a struct is part of the variable the struct is,
            // which is held by reference where finding it could come out
            // differently later: `(a[i].F, i) = (1, 2)`.
            BoundExpressionKind::Field {
                receiver: Some(receiver),
                field,
            } if !self.is_static(field) => {
                if self.binder.held_by_reference(&receiver.ty) || self.kept_generic(&receiver) {
                    let receiver = self.hold_receiver(*receiver, spilled, references);
                    BoundExpression::new(
                        BoundExpressionKind::Field {
                            receiver: Some(Box::new(receiver)),
                            field,
                        },
                        ty,
                        span,
                    )
                } else {
                    let fixed = self.fixed_location(&receiver);
                    let place = BoundExpression::new(
                        BoundExpressionKind::Field {
                            receiver: Some(receiver),
                            field,
                        },
                        ty,
                        span,
                    );
                    if references && !fixed {
                        self.hold_reference(place, spilled)
                    } else {
                        place
                    }
                }
            }
            // An element of an array whose element type is sealed is held by
            // reference; where the array may hold a type more derived than
            // it says, taking the element's address checks the type, and the
            // array and its indices are held instead.
            BoundExpressionKind::ArrayAccess { array, indices } => {
                if references && self.is_invariant_array(&array.ty) {
                    let place = BoundExpression::new(
                        BoundExpressionKind::ArrayAccess { array, indices },
                        ty,
                        span,
                    );
                    return self.hold_reference(place, spilled);
                }
                let array = if self.reads_the_same(&array) {
                    *array
                } else {
                    self.hold("receiver", *array, spilled)
                };
                let indices = indices
                    .into_iter()
                    .map(|index| {
                        if self.reads_the_same(&index) {
                            index
                        } else {
                            self.hold("argument", index, spilled)
                        }
                    })
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
            // `*p` is where `p` points now.
            BoundExpressionKind::Dereference { .. } | BoundExpressionKind::RefValue(_)
                if references =>
            {
                let place = BoundExpression::new(place.kind, ty, span);
                self.hold_reference(place, spilled)
            }
            kind => BoundExpression::new(kind, ty, span),
        }
    }

    /// The receiver of a member on the left of a deconstruction, as it is
    /// now: a reference, copied into a temporary; a variable of a type
    /// parameter, kept as [`Self::keep_generic`] keeps it; a struct
    /// variable reached through anything that could change, held by
    /// reference. `this`, a struct local or parameter, and a static member
    /// are where they are whatever happens.
    fn hold_receiver(
        &mut self,
        receiver: BoundExpression,
        spilled: &mut Vec<BoundExpression>,
        references: bool,
    ) -> BoundExpression {
        if self.kept_generic(&receiver) {
            return self.keep_generic(receiver, spilled);
        }
        if self.reads_the_same(&receiver) {
            return receiver;
        }
        if self.binder.held_by_reference(&receiver.ty) {
            return self.hold("receiver", receiver, spilled);
        }
        if references && !self.fixed_location(&receiver) && self.is_variable(&receiver) {
            return self.hold_reference(receiver, spilled);
        }
        receiver
    }

    /// Whether reading an expression later reads what reading it now does:
    /// a constant, `this` or `base` of a class, a type, a temporary the
    /// binder made and nothing else writes.
    fn reads_the_same(&self, value: &BoundExpression) -> bool {
        match &value.kind {
            BoundExpressionKind::Literal(_)
            | BoundExpressionKind::Default(_)
            | BoundExpressionKind::TypeOf(_)
            | BoundExpressionKind::SizeOf(_)
            | BoundExpressionKind::Base
            | BoundExpressionKind::TypeExpression(_)
            | BoundExpressionKind::NamespaceExpression(_) => true,
            BoundExpressionKind::This => value
                .ty
                .is_reference_type(self.binder.compilation().symbols()),
            BoundExpressionKind::Local(local) => self
                .body
                .locals
                .get(local.0 as usize)
                .is_some_and(|slot| slot.name.starts_with('<') && !slot.by_ref),
            _ => false,
        }
    }

    /// Whether a variable of a struct type stays where it is whatever runs
    /// meanwhile: a local, a parameter, `this`, a static field, or a field
    /// of one of those.
    fn fixed_location(&self, variable: &BoundExpression) -> bool {
        match &variable.kind {
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::Base => true,
            BoundExpressionKind::Field { receiver, field } => {
                self.is_static(*field)
                    || receiver.as_deref().is_none_or(|receiver| {
                        !self.binder.held_by_reference(&receiver.ty)
                            && self.fixed_location(receiver)
                    })
            }
            _ => false,
        }
    }

    /// Whether an array holds exactly the element type it says (Roslyn's
    /// `IsInvariantArray`): a sealed one, or a value type, which no array
    /// covariance reaches.
    fn is_invariant_array(&self, array: &Type) -> bool {
        let Type::Array { element, .. } = array else {
            return false;
        };
        let symbols = self.binder.compilation().symbols();
        match &**element {
            Type::TypeParameter(parameter) => symbols
                .get(*parameter)
                .as_type_parameter()
                .is_some_and(|detail| detail.value_type),
            Type::Named { symbol, .. } => {
                !element.is_reference_type(symbols)
                    || symbols.get(*symbol).modifiers.contains(Modifiers::SEALED)
            }
            Type::Tuple(_) | Type::Pointer(_) | Type::FunctionPointer(_) => true,
            _ => false,
        }
    }

    /// Whether a receiver is a variable of a type parameter that is not
    /// known to be a struct.
    fn kept_generic(&self, receiver: &BoundExpression) -> bool {
        matches!(
            receiver.kind,
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
        ) && matches!(&receiver.ty, Type::TypeParameter(parameter)
            if !self
                .binder
                .compilation()
                .symbols()
                .get(*parameter)
                .as_type_parameter()
                .is_some_and(|detail| detail.value_type))
    }

    /// A variable of a type parameter kept as it is now: copied, and where
    /// the parameter may be a struct, read through `default(T) is null ?
    /// ref copy : ref variable`.
    pub(super) fn keep_generic(
        &mut self,
        variable: BoundExpression,
        spilled: &mut Vec<BoundExpression>,
    ) -> BoundExpression {
        let (span, ty) = (variable.span, variable.ty.clone());
        let copy = self.hold("receiver", variable.clone(), spilled);
        if self.binder.held_by_reference(&ty) {
            return copy;
        }
        let by_reference = |operand: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Ref,
                    operand: Box::new(operand),
                },
                ty.clone(),
                span,
            )
        };
        let default_is_null = BoundExpression::new(
            BoundExpressionKind::IsPattern {
                operand: Box::new(BoundExpression::new(
                    BoundExpressionKind::Default(ty.clone()),
                    ty.clone(),
                    span,
                )),
                pattern: Box::new(BoundPattern::new(
                    BoundPatternKind::Constant(BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Null),
                        Type::Null,
                        span,
                    )),
                    span,
                )),
            },
            self.special(SpecialType::Boolean),
            span,
        );
        BoundExpression::new(
            BoundExpressionKind::Conditional {
                condition: Box::new(default_is_null),
                consequence: Box::new(by_reference(copy)),
                alternative: Box::new(by_reference(variable)),
            },
            ty,
            span,
        )
    }

    /// A value evaluated into a local now, and a read of that local.
    fn hold(
        &mut self,
        stem: &str,
        value: BoundExpression,
        spilled: &mut Vec<BoundExpression>,
    ) -> BoundExpression {
        let (span, ty) = (value.span, value.ty.clone());
        let local = self.declare_synthetic_local(stem, ty.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span);
        spilled.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(value),
            },
            ty,
            span,
        ));
        read
    }

    /// A variable found now and held by reference: `ref T held = ref
    /// variable`, and a read of `held`, which reads and writes the variable.
    fn hold_reference(
        &mut self,
        variable: BoundExpression,
        spilled: &mut Vec<BoundExpression>,
    ) -> BoundExpression {
        let (span, ty) = (variable.span, variable.ty.clone());
        let local = self.declare_synthetic_local("place", ty.clone());
        if let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
            slot.by_ref = true;
        }
        let read = BoundExpression::new(BoundExpressionKind::Local(local), ty.clone(), span);
        spilled.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(BoundExpression::new(
                    BoundExpressionKind::RefArgument {
                        kind: RefKind::Ref,
                        operand: Box::new(variable),
                    },
                    ty.clone(),
                    span,
                )),
            },
            ty,
            span,
        ));
        read
    }

    /// A deconstruction done for what it does, with nothing made of what it
    /// is worth: the statement `(a, b) = (b, a);` swaps and builds no tuple.
    pub(super) fn deconstruct_into(
        &mut self,
        target: &SyntaxNode,
        value: BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let taken_apart = self.deconstruct_value(target, value, span)?;
        Some(deconstruction_unused(taken_apart))
    }

    /// The tuple a deconstruction is worth, made of what each slot was given
    /// (§12.21.2): its elements are typed as the places are.
    fn tuple_of(&self, values: Vec<BoundExpression>, span: TextSpan) -> BoundExpression {
        let elements: Vec<TupleElement> = values
            .iter()
            .map(|value| TupleElement {
                name: None,
                ty: value.ty.clone(),
            })
            .collect();
        BoundExpression::new(
            BoundExpressionKind::TupleCreation(values),
            Type::Tuple(elements),
            span,
        )
    }

    /// The `Deconstruct` that takes a value of this type apart into `count`
    /// parts (§12.7): an instance method with that many `out` parameters,
    /// and failing one, an extension method in scope with a receiver
    /// before them. A generic one is a candidate only where the receiver
    /// says what all its type parameters are; the parts cannot.
    pub(super) fn find_deconstruct(&self, ty: &Type, count: usize) -> Option<FoundDeconstruct> {
        let symbols = self.binder.compilation().symbols();
        let all_out = |parameters: &[SymbolId]| {
            parameters.iter().all(|parameter| {
                symbols
                    .get(*parameter)
                    .as_parameter()
                    .is_some_and(|detail| detail.ref_kind == RefKind::Out)
            })
        };
        if let Some(symbol) = ty.symbol() {
            let own = self
                .binder
                .lookup_member(symbol, "Deconstruct")
                .into_iter()
                .find(|id| {
                    // `Deconstruct(out int a, out string b, __arglist)` is
                    // not one: a deconstruction passes no `__arglist`.
                    symbols.get(*id).as_method().is_some_and(|detail| {
                        detail.parameters.len() == count
                            && detail.type_parameters.is_empty()
                            && !detail.is_vararg
                            && all_out(&detail.parameters)
                            && !symbols.get(*id).modifiers.contains(Modifiers::STATIC)
                    })
                });
            if let Some(method) = own {
                let parameters = symbols
                    .get(method)
                    .as_method()?
                    .parameters
                    .iter()
                    .map(|parameter| self.member_type(*parameter, ty))
                    .collect();
                return Some(FoundDeconstruct {
                    method,
                    parameters,
                    receiver: None,
                    type_arguments: Vec::new(),
                });
            }
        }
        let mut found: Option<FoundDeconstruct> = None;
        for candidate in self
            .binder
            .extensions_in_scope(&self.context, "Deconstruct")
        {
            let Some(detail) = symbols.get(candidate).as_method() else {
                continue;
            };
            let Some((first, rest)) = detail.parameters.split_first() else {
                continue;
            };
            if rest.len() != count || !all_out(rest) {
                continue;
            }
            let mut sink = Diagnostics::new();
            let declared = self.binder.type_of(*first, &mut sink);
            let mut inferred = HashMap::new();
            self.infer_into(&declared, ty, &detail.type_parameters, &mut inferred);
            if detail
                .type_parameters
                .iter()
                .any(|parameter| !inferred.contains_key(parameter))
            {
                continue;
            }
            let receiver = declared.substitute(&inferred);
            if !self.binder.converts_implicitly(ty, &receiver) {
                continue;
            }
            // Two that fit are ambiguous; the first stands, as it would
            // after the error Roslyn reports.
            if found.is_some() {
                continue;
            }
            found = Some(FoundDeconstruct {
                method: candidate,
                parameters: rest
                    .iter()
                    .map(|parameter| {
                        let mut sink = Diagnostics::new();
                        self.binder
                            .type_of(*parameter, &mut sink)
                            .value()
                            .substitute(&inferred)
                    })
                    .collect(),
                receiver: Some(receiver),
                type_arguments: detail
                    .type_parameters
                    .iter()
                    .map(|parameter| inferred[parameter].clone())
                    .collect(),
            });
        }
        found
    }

    /// One element of a tuple held in a local: `held.ItemN`.
    pub(super) fn tuple_element(
        &mut self,
        held: LocalId,
        tuple: &Type,
        at: usize,
        ty: Type,
        span: TextSpan,
    ) -> BoundExpression {
        // The element's field, through `Rest` where the tuple is longer
        // than seven; a tuple written `(int, int)` and one read out of
        // metadata as a `ValueTuple<int, int>` are the same type.
        let side = TupleSide::Value {
            read: Box::new(BoundExpression::new(
                BoundExpressionKind::Local(held),
                tuple.clone(),
                span,
            )),
            elements: Vec::new(),
            has_value: None,
        };
        let element = self.tuple_side_element(&side, at, span);
        if element.ty.is_error() || ty.is_error() || element.ty == ty {
            return element;
        }
        BoundExpression::new(element.kind, ty, span)
    }

    /// The `ValueTuple<...>` a tuple type really is.
    ///
    /// Element names live on the tuple type and nowhere else; what the runtime
    /// holds is a `ValueTuple` of the element types, and every member a tuple
    /// has is one of its.
    pub(super) fn tuple_as_named(&self, elements: &[TupleElement]) -> Type {
        // Past seven the rest nest: `(1, …, 9)` is a
        // `ValueTuple<T1, …, T7, ValueTuple<T8, T9>>` (§8.3.11).
        let (head, rest) = if elements.len() > 7 {
            (&elements[..7], Some(self.tuple_as_named(&elements[7..])))
        } else {
            (elements, None)
        };
        let name = format!(
            "System.ValueTuple`{}",
            head.len() + usize::from(rest.is_some())
        );
        self.binder
            .compilation()
            .type_by_metadata_name(&name)
            .map_or(Type::Error, |symbol| Type::Named {
                symbol,
                type_arguments: head
                    .iter()
                    .map(|element| element.ty.clone())
                    .chain(rest)
                    .collect(),
            })
    }

    /// The lifted form of an operator, where one side is a `T?`.
    ///
    /// §12.4.8: an operator on a value type has a lifted form taking `T?` and
    /// giving `R?`, which is null where either side is. A comparison is the
    /// exception: it gives a `bool`, false where either side is null, and
    /// `==` calls two nulls equal.
    ///
    /// `None` where nothing is lifted, or where the two sides do not already
    /// agree on the type underneath: a widening between two different `T?`s
    /// is a conversion this does not do yet.
    /// Whether an operand takes part in a tuple comparison (§12.12.10): a
    /// tuple literal, a value of a tuple type, or a nullable one.
    fn is_tuple_operand(&self, operand: &BoundExpression) -> bool {
        if matches!(operand.kind, BoundExpressionKind::TupleCreation(_)) {
            return true;
        }
        let inner = self
            .binder
            .nullable_underlying(&operand.ty)
            .unwrap_or_else(|| operand.ty.clone());
        self.tuple_element_types(&inner).is_some()
    }

    /// `(a, b) == (c, d)`, and `t1 != t2` on two tuples: element by element,
    /// both sides evaluated once and in order first (§12.12.10). A nullable
    /// tuple compares equal to another only where both are present, or both
    /// missing.
    pub(super) fn bind_tuple_equality(
        &mut self,
        operator: BinaryOperator,
        left: &BoundExpression,
        right: &BoundExpression,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        if matches!(left.ty, Type::Null) || matches!(right.ty, Type::Null) {
            return None;
        }
        if !self.is_tuple_operand(left) && !self.is_tuple_operand(right) {
            return None;
        }
        let mut steps = Vec::new();
        let left = self.tuple_side(left.clone(), &mut steps, span)?;
        let right = self.tuple_side(right.clone(), &mut steps, span)?;
        if left.arity() != right.arity() {
            return None;
        }
        let boolean = self.special(SpecialType::Boolean);
        let equal = operator == BinaryOperator::Equality;
        let mut elementwise: Option<BoundExpression> = None;
        for index in 0..left.arity() {
            let l = self.tuple_side_element(&left, index, span);
            let r = self.tuple_side_element(&right, index, span);
            let compared = match self.bind_tuple_equality(operator, &l, &r, span) {
                Some(compared) => compared,
                None => {
                    let (l, r) = retype_default_beside(l, r);
                    // A method group or a lambda has no type of its own, and
                    // takes the delegate type beside it (§12.12.11); beside
                    // anything else an operator the types declare decides.
                    let (l, r) = if typeless(&l) && !typeless(&r) && self.is_delegate(&r.ty) {
                        let ty = r.ty.clone();
                        (self.convert(l, &ty), r)
                    } else if typeless(&r) && !typeless(&l) && self.is_delegate(&l.ty) {
                        let ty = l.ty.clone();
                        (l, self.convert(r, &ty))
                    } else {
                        (l, r)
                    };
                    self.bind_binary_on(operator, l, r, span)
                }
            };
            let compared = self.convert(compared, &boolean);
            elementwise = Some(match elementwise {
                None => compared,
                Some(sofar) => BoundExpression::new(
                    BoundExpressionKind::Binary {
                        operator: if equal {
                            BinaryOperator::LogicalAnd
                        } else {
                            BinaryOperator::LogicalOr
                        },
                        left: Box::new(sofar),
                        right: Box::new(compared),
                    },
                    boolean.clone(),
                    span,
                ),
            });
        }
        let elementwise = elementwise?;
        let literal = |value: bool| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Boolean(value)),
                boolean.clone(),
                span,
            )
        };
        let binary = |operator: BinaryOperator, l: BoundExpression, r: BoundExpression| {
            BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator,
                    left: Box::new(l),
                    right: Box::new(r),
                },
                boolean.clone(),
                span,
            )
        };
        let result = match (left.has_value(), right.has_value()) {
            (None, None) => elementwise,
            (l, r) => {
                // `(lHas == rHas) && (!lHas || elements)`: the elements are
                // only looked at where both sides have them.
                let l_has = l.cloned().unwrap_or_else(|| literal(true));
                let r_has = r.cloned().unwrap_or_else(|| literal(true));
                let not_l = BoundExpression::new(
                    BoundExpressionKind::Unary {
                        operator: UnaryOperator::LogicalNot,
                        operand: Box::new(l_has.clone()),
                    },
                    boolean.clone(),
                    span,
                );
                if equal {
                    binary(
                        BinaryOperator::LogicalAnd,
                        binary(BinaryOperator::Equality, l_has, r_has),
                        binary(BinaryOperator::LogicalOr, not_l, elementwise),
                    )
                } else {
                    binary(
                        BinaryOperator::LogicalOr,
                        binary(BinaryOperator::Inequality, l_has.clone(), r_has),
                        binary(BinaryOperator::LogicalAnd, l_has, elementwise),
                    )
                }
            }
        };
        if steps.is_empty() {
            return Some(result);
        }
        steps.push(result);
        Some(BoundExpression::new(
            BoundExpressionKind::Sequence(steps),
            boolean,
            span,
        ))
    }

    /// One operand of a tuple comparison, taken apart: a literal's elements
    /// (evaluated into temporaries where they do anything), or a value held
    /// in a temporary and read field by field.
    fn tuple_side(
        &mut self,
        operand: BoundExpression,
        steps: &mut Vec<BoundExpression>,
        span: TextSpan,
    ) -> Option<TupleSide> {
        if let BoundExpressionKind::TupleCreation(values) = operand.kind {
            let values = values
                .into_iter()
                .map(|value| self.spill_tuple_element(value, steps, span))
                .collect();
            return Some(TupleSide::Literal(values));
        }
        let nullable = self.binder.nullable_underlying(&operand.ty);
        let inner = nullable.clone().unwrap_or_else(|| operand.ty.clone());
        let elements = self.tuple_element_types(&inner)?;
        let held = self.declare_synthetic_local("tuple", operand.ty.clone());
        let read = BoundExpression::new(BoundExpressionKind::Local(held), operand.ty.clone(), span);
        steps.push(BoundExpression::new(
            BoundExpressionKind::Assignment {
                target: Box::new(read.clone()),
                value: Box::new(operand),
            },
            inner.clone(),
            span,
        ));
        let (read, has_value) = match nullable {
            Some(_) => {
                let symbol = read.ty.symbol()?;
                let has_value = self
                    .binder
                    .lookup_member(symbol, "HasValue")
                    .into_iter()
                    .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)?;
                let boolean = self.special(SpecialType::Boolean);
                let has_value =
                    self.member_access(has_value, Some(Box::new(read.clone())), boolean, span);
                let value = self.call_on(read, "GetValueOrDefault", Vec::new(), span)?;
                (value, Some(has_value))
            }
            None => (read, None),
        };
        Some(TupleSide::Value {
            read: Box::new(read),
            elements,
            has_value: has_value.map(Box::new),
        })
    }

    /// A tuple literal's element, evaluated before any comparison happens:
    /// into a temporary unless reading it twice would make no difference.
    fn spill_tuple_element(
        &mut self,
        value: BoundExpression,
        steps: &mut Vec<BoundExpression>,
        span: TextSpan,
    ) -> BoundExpression {
        match value.kind {
            BoundExpressionKind::TupleCreation(values) => {
                let values = values
                    .into_iter()
                    .map(|value| self.spill_tuple_element(value, steps, span))
                    .collect();
                BoundExpression::new(BoundExpressionKind::TupleCreation(values), value.ty, span)
            }
            BoundExpressionKind::Literal(_)
            | BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::Default(_) => value,
            // An interpolated string is a `string` or an `IFormattable` by
            // what it is compared with; one with nothing to evaluate stays
            // as written, so that the comparison can still choose.
            BoundExpressionKind::InterpolatedString(ref pieces)
                if pieces
                    .iter()
                    .all(|piece| matches!(piece.kind, BoundExpressionKind::Literal(_))) =>
            {
                value
            }
            _ if typeless(&value) || value.ty.is_error() || matches!(value.ty, Type::Null) => value,
            _ => {
                let held = self.declare_synthetic_local("element", value.ty.clone());
                let read =
                    BoundExpression::new(BoundExpressionKind::Local(held), value.ty.clone(), span);
                steps.push(BoundExpression::new(
                    BoundExpressionKind::Assignment {
                        target: Box::new(read.clone()),
                        value: Box::new(value),
                    },
                    read.ty.clone(),
                    span,
                ));
                read
            }
        }
    }

    /// The `index`th element of one side: the literal's expression, or the
    /// `Item{n}` field of the held value (`Rest.Item{n-7}` past the seventh).
    fn tuple_side_element(
        &mut self,
        side: &TupleSide,
        index: usize,
        span: TextSpan,
    ) -> BoundExpression {
        match side {
            TupleSide::Literal(values) => values[index].clone(),
            TupleSide::Value { read, .. } => {
                let mut receiver = (**read).clone();
                let mut index = index;
                loop {
                    let named = match &receiver.ty {
                        Type::Tuple(elements) => self.tuple_as_named(elements),
                        other => other.clone(),
                    };
                    receiver = BoundExpression::new(receiver.kind, named.clone(), span);
                    let name = if index >= 7 {
                        "Rest".to_string()
                    } else {
                        format!("Item{}", index + 1)
                    };
                    let field = named.symbol().and_then(|symbol| {
                        self.binder
                            .lookup_member(symbol, &name)
                            .into_iter()
                            .find(|candidate| self.kind_of(*candidate) == SymbolKind::Field)
                    });
                    let Some(field) = field else {
                        return BoundExpression::error(span);
                    };
                    let ty = self.member_type(field, &named);
                    receiver = self.member_access(field, Some(Box::new(receiver)), ty, span);
                    if index < 7 {
                        return receiver;
                    }
                    index -= 7;
                }
            }
        }
    }
}

/// A deconstruction's steps without the tuple it is worth: each step is kept
/// for what it does, and the tuple, the last step of the phases, reads only
/// what the steps before it wrote and goes. The branches of a conditional
/// each make theirs, and are kept as they are.
pub(super) fn deconstruction_unused(taken_apart: BoundExpression) -> BoundExpression {
    let span = taken_apart.span;
    let mut flat = Vec::new();
    let mut pending = vec![taken_apart];
    // Depth first and in order: the places' evaluation, then the phases.
    while let Some(step) = pending.pop() {
        match step.kind {
            BoundExpressionKind::Sequence(steps) => pending.extend(steps.into_iter().rev()),
            BoundExpressionKind::TupleCreation(_)
            | BoundExpressionKind::Local(_)
            | BoundExpressionKind::Literal(_)
            | BoundExpressionKind::Default(_) => {}
            kind => flat.push(BoundExpression::new(kind, step.ty, step.span)),
        }
    }
    BoundExpression::new(BoundExpressionKind::Sequence(flat), Type::Void, span)
}

/// Whether a value is `c ? a : b` for its value, rather than a reference
/// either branch hands back.
fn is_value_conditional(value: &BoundExpression) -> bool {
    matches!(&value.kind, BoundExpressionKind::Conditional { consequence, alternative, .. }
        if !matches!(consequence.kind, BoundExpressionKind::RefArgument { .. })
            && !matches!(alternative.kind, BoundExpressionKind::RefArgument { .. }))
}

/// Whether evaluating an expression waits on an `await`: one inside a lambda
/// or a local function is that function's own.
fn awaits_in(node: &SyntaxNode) -> bool {
    node.kind() == SyntaxKind::AwaitExpression
        || node.children().any(|child| {
            !matches!(
                child.kind(),
                SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
                    | SyntaxKind::LocalFunctionStatement
            ) && awaits_in(&child)
        })
}

/// Points the `Length` or `Count` an `Index` or a `Range` counts from
/// (`i.GetOffset(item.Length)`) at the receiver kept for `item`.
fn counted_from(
    expression: &mut BoundExpression,
    variable: &BoundExpression,
    kept: &BoundExpression,
    body: &BodyBinder<'_>,
) {
    let symbols = body.binder.compilation().symbols();
    match &mut expression.kind {
        BoundExpressionKind::Call {
            receiver,
            method,
            arguments,
            ..
        } => {
            if matches!(
                symbols.get(*method).name.as_str(),
                "GetOffset" | "GetOffsetAndLength"
            ) {
                for argument in arguments.iter_mut() {
                    if let BoundExpressionKind::Property {
                        receiver: Some(of),
                        property,
                    } = &mut argument.kind
                        && matches!(symbols.get(*property).name.as_str(), "Length" | "Count")
                        && match (&of.kind, &variable.kind) {
                            (BoundExpressionKind::Local(a), BoundExpressionKind::Local(b)) => {
                                a == b
                            }
                            (
                                BoundExpressionKind::Parameter(a),
                                BoundExpressionKind::Parameter(b),
                            ) => a == b,
                            _ => false,
                        }
                    {
                        **of = kept.clone();
                    }
                }
            }
            if let Some(receiver) = receiver {
                counted_from(receiver, variable, kept, body);
            }
        }
        BoundExpressionKind::Conversion { operand, .. } => {
            counted_from(operand, variable, kept, body);
        }
        _ => {}
    }
}
