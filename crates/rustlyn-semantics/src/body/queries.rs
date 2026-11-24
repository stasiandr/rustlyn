//! Query expressions (§12.20): the method calls a query is shorthand for.

use std::collections::HashMap;

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::overloads::mentions_any;
use super::{BodyBinder, LambdaFrame, Range};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundLambda, BoundStatement, BoundStatementKind,
    BoundSymbol, LocalId,
};
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, SymbolId, TypeKind};
use crate::types::{TupleElement, Type};

/// A method a query clause may be translated into, as its source sees it.
struct QueryCandidate {
    /// Its parameters' types, with the source's type arguments put in; an
    /// extension method's receiver is left out.
    parameters: Vec<Type>,
    /// Its own type parameters.
    type_parameters: Vec<SymbolId>,
    /// What the source says of them: an extension method's, inferred from
    /// its receiver.
    inferred: HashMap<SymbolId, Type>,
}

impl BodyBinder<'_> {
    /// `from x in xs where p select f`: the calls C# translates it into, or,
    /// where they cannot be found, the range variables and what the clauses
    /// mean without them.
    ///
    /// §12.20 says a query is shorthand for `xs.Where(x => p).Select(x => f)`
    /// and that the translation is syntactic — Roslyn rewrites the tree and
    /// binds the rewrite. [`Self::translate_query`] binds the calls without
    /// the rewrite; a query it cannot translate still has its range
    /// variables brought into scope with the types their collections give
    /// them and every clause bound against them, which is what the code
    /// around it needs to make sense, and is emitted by neither backend.
    pub(super) fn bind_query(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        self.push_scope();
        let translated = self.translate_query(node);
        // A clause this does not translate yet still has its expressions
        // bound, so that every name in the query resolves for whoever asks the
        // semantic model about it.
        let bound = match translated {
            Some(bound) => bound,
            None => {
                let mut current = Type::Error;
                for child in node.children() {
                    match child.kind() {
                        SyntaxKind::FromClause => current = self.bind_from_clause(&child),
                        SyntaxKind::QueryBody => current = self.bind_query_body(&child),
                        _ => {}
                    }
                }
                BoundExpression::new(BoundExpressionKind::Unsupported(node.kind()), current, span)
            }
        };
        self.pop_scope();
        bound
    }

    /// The method calls a query is shorthand for (§12.20).
    ///
    /// `from x in e where p select v` is `e.Where(x => p).Select(x => v)` and
    /// nothing else: the language defines the query form as a rewriting into
    /// calls, found by name on whatever the source turns out to be, whose
    /// lambdas' parameters are typed by the methods found. Each lambda here
    /// is bound once, against the types those methods say its range
    /// variables have, and handed to the call as the delegate the method
    /// takes.
    fn translate_query(&mut self, node: &SyntaxNode) -> Option<BoundExpression> {
        let from = node
            .children()
            .find(|child| child.kind() == SyntaxKind::FromClause)?;
        let body = node
            .children()
            .find(|child| child.kind() == SyntaxKind::QueryBody)?;
        let name = from
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
        let (name, name_span) = (name.value_text().to_string(), name.span());

        let mut current = self.bind_expression(&range_source(&from)?);
        // `from int n in xs` reads each element as that type, which is what
        // `Cast<T>` is for.
        if let Some(written) = written_element_type(&from).filter(|w| w.text().trim() != "var") {
            let ty = self.resolve(&written);
            current = self.query_call(current, "Cast", Vec::new(), vec![ty], &from)?;
        }
        // What the range variable is comes from the method the first clause
        // is translated into (§12.20.3): what its delegate is handed, as the
        // source sees it. `from x in y where x > 0` on a `Y` with a
        // `Where(Func<int, bool>)` ranges over `int`s, and one on a
        // `List1<T>` with a `Select<U>(Func1<T, U>)` over its `T`s. For a
        // sequence that is its element, whatever the method.
        let mut element = self.enumerated_element(&current.ty);
        if element.is_error() {
            element = self
                .clause_parameter_type(&current, &body, &name)
                .unwrap_or_else(|| self.element_type_of(&current.ty));
        }
        if element.is_error() {
            return None;
        }
        let ranges = vec![Range {
            name,
            span: name_span,
            ty: element,
        }];
        self.translate_query_body(&body, current, ranges)
    }

    /// The clauses of a query body, each one call on what came before.
    ///
    /// A second range variable — `let`, a second `from` — has nowhere to
    /// live between calls but the element itself, so from then on the
    /// element is a tuple of every variable in scope, named after them, and
    /// each clause's lambda takes it apart before doing its work (§12.20.3.6
    /// calls this a transparent identifier).
    fn translate_query_body(
        &mut self,
        body: &SyntaxNode,
        mut current: BoundExpression,
        mut ranges: Vec<Range>,
    ) -> Option<BoundExpression> {
        let mut clauses = body.children().peekable();
        let mut first = true;
        while let Some(clause) = clauses.next() {
            let follows_a_clause = !std::mem::replace(&mut first, false);
            match clause.kind() {
                SyntaxKind::WhereClause => {
                    let condition = clause.children().find(|c| c.kind().is_expression())?;
                    let boolean = self.special(SpecialType::Boolean);
                    let lambda = self.ranged_lambda(
                        &ranges,
                        None,
                        condition.span(),
                        Some(boolean),
                        |this, _, _| Some(this.bind_expression(&condition)),
                    )?;
                    current =
                        self.query_call(current, "Where", vec![lambda], Vec::new(), &clause)?;
                }
                SyntaxKind::OrderByClause => {
                    let mut ordered = false;
                    for ordering in clause.children() {
                        let key = ordering.children().find(|c| c.kind().is_expression())?;
                        let descending = ordering
                            .child_tokens()
                            .any(|token| token.kind() == SyntaxKind::DescendingKeyword);
                        let lambda =
                            self.ranged_lambda(&ranges, None, key.span(), None, |this, _, _| {
                                Some(this.bind_expression(&key))
                            })?;
                        let method = match (ordered, descending) {
                            (false, false) => "OrderBy",
                            (false, true) => "OrderByDescending",
                            (true, false) => "ThenBy",
                            (true, true) => "ThenByDescending",
                        };
                        current =
                            self.query_call(current, method, vec![lambda], Vec::new(), &ordering)?;
                        ordered = true;
                    }
                }
                SyntaxKind::SelectClause => {
                    let selected = clause.children().find(|c| c.kind().is_expression())?;
                    // `select x` of the one range variable after another
                    // clause selects nothing new, and is left out
                    // (§12.20.3.3): `from x in e where p select x` is
                    // `e.Where(x => p)`, which a `Where` that gives back
                    // anything at all may be.
                    if follows_a_clause
                        && let [single] = ranges.as_slice()
                        && selected.kind() == SyntaxKind::IdentifierName
                        && selected.text().trim() == single.name
                    {
                        // Still the range variable to an editor asking.
                        if let Some(local) = self
                            .body
                            .locals
                            .iter()
                            .rposition(|local| local.span == single.span)
                            .and_then(|at| u32::try_from(at).ok())
                        {
                            self.body
                                .references
                                .insert(selected.span(), BoundSymbol::Local(LocalId(local)));
                        }
                        continue;
                    }
                    let lambda =
                        self.ranged_lambda(&ranges, None, selected.span(), None, |this, _, _| {
                            Some(this.bind_expression(&selected))
                        })?;
                    current =
                        self.query_call(current, "Select", vec![lambda], Vec::new(), &clause)?;
                }
                // `let n = e` is a `Select` that keeps everything in scope
                // and adds `n`: the element becomes a tuple of them all.
                SyntaxKind::LetClause => {
                    let name = clause
                        .child_tokens()
                        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
                    let (name, name_span) = (name.value_text().to_string(), name.span());
                    let value = clause.children().find(|c| c.kind().is_expression())?;
                    let widened = ranges.clone();
                    let lambda = self.ranged_lambda(
                        &ranges,
                        None,
                        clause.span(),
                        None,
                        |this, locals, _| {
                            let added = this.bind_expression(&value);
                            let mut kept = widened.clone();
                            kept.push(Range {
                                name: name.clone(),
                                span: name_span,
                                ty: added.ty.clone(),
                            });
                            Some(Self::query_tuple(&kept, locals, added, clause.span()))
                        },
                    )?;
                    current =
                        self.query_call(current, "Select", vec![lambda], Vec::new(), &clause)?;
                    ranges = self.ranges_of(&current.ty, &ranges, Some((name, name_span)))?;
                }
                // A second `from` is a `SelectMany`: one lambda gives the
                // inner sequence, the other pairs each of its elements with
                // what was in scope.
                SyntaxKind::FromClause => {
                    let name = clause
                        .child_tokens()
                        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
                    let (name, name_span) = (name.value_text().to_string(), name.span());
                    let source = range_source(&clause)?;
                    let cast = written_element_type(&clause)
                        .filter(|written| written.text().trim() != "var")
                        .map(|written| self.resolve(&written));
                    let inner =
                        self.ranged_lambda(&ranges, None, source.span(), None, |this, _, _| {
                            let sequence = this.bind_expression(&source);
                            match &cast {
                                Some(ty) => this.query_call(
                                    sequence,
                                    "Cast",
                                    Vec::new(),
                                    vec![ty.clone()],
                                    &clause,
                                ),
                                None => Some(sequence),
                            }
                        })?;
                    let returned = self.lambda_return_of(&inner)?;
                    // The new range variable is what `SelectMany`'s result
                    // selector is handed second, with what the first lambda
                    // gives back inferring it: `Func1<T, List1<U>>` giving
                    // a `List1<int>` makes it an `int`. Of a sequence, its
                    // element.
                    let mut element = self.enumerated_element(&returned);
                    if element.is_error() {
                        element = self
                            .query_lambda_input(
                                &current,
                                "SelectMany",
                                2,
                                1,
                                2,
                                &[(0, returned.clone())],
                            )
                            .and_then(|taken| taken.get(1).cloned())
                            .unwrap_or_else(|| self.element_type_of(&returned));
                    }
                    if element.is_error() {
                        return None;
                    }
                    let added = Range {
                        name: name.clone(),
                        span: name_span,
                        ty: element,
                    };
                    let widened = ranges.clone();
                    let pairing = self.ranged_lambda(
                        &ranges,
                        Some(&added),
                        clause.span(),
                        None,
                        |this, locals, extra| {
                            let mut kept = widened.clone();
                            kept.push(added.clone());
                            let last = extra?;
                            let value = BoundExpression::new(
                                BoundExpressionKind::Local(last),
                                added.ty.clone(),
                                clause.span(),
                            );
                            let _ = this;
                            Some(Self::query_tuple(&kept, locals, value, clause.span()))
                        },
                    )?;
                    current = self.query_call(
                        current,
                        "SelectMany",
                        vec![inner, pairing],
                        Vec::new(),
                        &clause,
                    )?;
                    ranges = self.ranges_of(&current.ty, &ranges, Some((name, name_span)))?;
                }
                // `group e by k` is a `GroupBy`; what follows an `into` sees
                // each group as one range variable.
                SyntaxKind::GroupClause => {
                    let mut expressions = clause.children().filter(|c| c.kind().is_expression());
                    let (grouped, key) = (expressions.next()?, expressions.next()?);
                    // `group x by k` of the one range variable groups the
                    // elements themselves, and is `GroupBy(x => k)` alone
                    // (§12.20.3.5); the `x` is still bound, for whoever
                    // asks the model what it is.
                    let alone = matches!(ranges.as_slice(), [single]
                        if groups_the_range(&clause, &single.name));
                    let key_lambda =
                        self.ranged_lambda(&ranges, None, key.span(), None, |this, _, _| {
                            if alone {
                                this.bind_expression(&grouped);
                            }
                            Some(this.bind_expression(&key))
                        })?;
                    let mut arguments = vec![key_lambda];
                    if !alone {
                        arguments.push(self.ranged_lambda(
                            &ranges,
                            None,
                            grouped.span(),
                            None,
                            |this, _, _| Some(this.bind_expression(&grouped)),
                        )?);
                    }
                    current =
                        self.query_call(current, "GroupBy", arguments, Vec::new(), &clause)?;
                }
                SyntaxKind::QueryContinuation => {
                    let name = clause
                        .child_tokens()
                        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
                    let (name, name_span) = (name.value_text().to_string(), name.span());
                    let rest = clause
                        .children()
                        .find(|child| child.kind() == SyntaxKind::QueryBody)?;
                    // A query of its own over what came before, whose range
                    // variable is found the way the first one's is.
                    let mut element = self.enumerated_element(&current.ty);
                    if element.is_error() {
                        element = self
                            .clause_parameter_type(&current, &rest, &name)
                            .unwrap_or_else(|| self.element_type_of(&current.ty));
                    }
                    if element.is_error() {
                        return None;
                    }
                    let continued = vec![Range {
                        name,
                        span: name_span,
                        ty: element,
                    }];
                    return self.translate_query_body(&rest, current, continued);
                }
                // `join b in e on k1 equals k2` is a `Join` of what came
                // before with `e` by the two keys; with `into g` it is a
                // `GroupJoin`, and `g` holds every `b` a key matched. A
                // `select` right after it becomes the result selector;
                // anything else gets the pair handed on (§12.20.3.5).
                SyntaxKind::JoinClause => {
                    let name = clause
                        .child_tokens()
                        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
                    let (name, name_span) = (name.value_text().to_string(), name.span());
                    let source = range_source(&clause)?;
                    let keys: Vec<SyntaxNode> = clause
                        .children()
                        .filter(|child| {
                            child.kind().is_expression()
                                && child.span().start() > source.span().start()
                        })
                        .collect();
                    let [outer_key, inner_key] = keys.as_slice() else {
                        return None;
                    };
                    let mut inner = self.bind_expression(&source);
                    if let Some(written) = written_element_type(&clause)
                        .filter(|written| written.text().trim() != "var")
                    {
                        let ty = self.resolve(&written);
                        inner = self.query_call(inner, "Cast", Vec::new(), vec![ty], &clause)?;
                    }
                    // The joined variable is what the inner key selector is
                    // handed, the group what the result selector is handed
                    // second, both with the inner sequence inferring them:
                    // `Join<U, K, V>(List1<U> inner, …)` given a
                    // `List1<int>` joins `int`s. Of a sequence, its element,
                    // and a group of those.
                    let grouped = clause.child_of_kind(SyntaxKind::JoinIntoClause).is_some();
                    let method = if grouped { "GroupJoin" } else { "Join" };
                    let given = [(0, inner.ty.clone())];
                    let mut element = self.enumerated_element(&inner.ty);
                    if element.is_error() {
                        element = self
                            .query_lambda_input(&current, method, 4, 2, 1, &given)
                            .and_then(|taken| taken.first().cloned())
                            .unwrap_or_else(|| self.element_type_of(&inner.ty));
                    }
                    if element.is_error() {
                        return None;
                    }
                    let group = if grouped {
                        self.query_lambda_input(&current, method, 4, 3, 2, &given)
                            .and_then(|taken| taken.get(1).cloned())
                    } else {
                        None
                    };
                    let joined = Range {
                        name,
                        span: name_span,
                        ty: element.clone(),
                    };
                    let outer_lambda =
                        self.ranged_lambda(&ranges, None, outer_key.span(), None, |this, _, _| {
                            Some(this.bind_expression(outer_key))
                        })?;
                    let inner_lambda = self.ranged_lambda(
                        std::slice::from_ref(&joined),
                        None,
                        inner_key.span(),
                        None,
                        |this, _, _| Some(this.bind_expression(inner_key)),
                    )?;
                    let added = match clause.child_of_kind(SyntaxKind::JoinIntoClause) {
                        Some(into) => {
                            let name = into
                                .child_tokens()
                                .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
                            Range {
                                name: name.value_text().to_string(),
                                span: name.span(),
                                ty: group.unwrap_or_else(|| self.sequence_of(element)),
                            }
                        }
                        None => joined,
                    };
                    let selected = clauses
                        .peek()
                        .filter(|next| next.kind() == SyntaxKind::SelectClause)
                        .and_then(|next| next.children().find(|c| c.kind().is_expression()));
                    let widened = ranges.clone();
                    let result = match &selected {
                        Some(selected) => self.ranged_lambda(
                            &ranges,
                            Some(&added),
                            selected.span(),
                            None,
                            |this, _, _| Some(this.bind_expression(selected)),
                        )?,
                        None => self.ranged_lambda(
                            &ranges,
                            Some(&added),
                            clause.span(),
                            None,
                            |_, locals, extra| {
                                let mut kept = widened.clone();
                                kept.push(added.clone());
                                let value = BoundExpression::new(
                                    BoundExpressionKind::Local(extra?),
                                    added.ty.clone(),
                                    clause.span(),
                                );
                                Some(Self::query_tuple(&kept, locals, value, clause.span()))
                            },
                        )?,
                    };
                    current = self.query_call(
                        current,
                        method,
                        vec![inner, outer_lambda, inner_lambda, result],
                        Vec::new(),
                        &clause,
                    )?;
                    if selected.is_some() {
                        clauses.next();
                        // A continuation may still follow the `select`.
                        continue;
                    }
                    ranges =
                        self.ranges_of(&current.ty, &ranges, Some((added.name, added.span)))?;
                }
                _ => return None,
            }
        }
        Some(current)
    }

    /// What the lambda of the method a query's first clause is translated
    /// into is handed first: the range variable's type, for a source that
    /// is no sequence. A `join` hands it to its outer key selector, the
    /// second argument.
    fn clause_parameter_type(
        &mut self,
        source: &BoundExpression,
        body: &SyntaxNode,
        range: &str,
    ) -> Option<Type> {
        let clause = body.children().next()?;
        let (method, count, position) = match clause.kind() {
            SyntaxKind::WhereClause => ("Where", 1, 0),
            SyntaxKind::SelectClause | SyntaxKind::LetClause => ("Select", 1, 0),
            SyntaxKind::OrderByClause => {
                let descending = clause.children().next().is_some_and(|ordering| {
                    ordering
                        .child_tokens()
                        .any(|token| token.kind() == SyntaxKind::DescendingKeyword)
                });
                let method = if descending {
                    "OrderByDescending"
                } else {
                    "OrderBy"
                };
                (method, 1, 0)
            }
            SyntaxKind::FromClause => ("SelectMany", 2, 0),
            SyntaxKind::GroupClause => {
                let count = if groups_the_range(&clause, range) {
                    1
                } else {
                    2
                };
                ("GroupBy", count, 0)
            }
            SyntaxKind::JoinClause => {
                let method = if clause.child_of_kind(SyntaxKind::JoinIntoClause).is_some() {
                    "GroupJoin"
                } else {
                    "Join"
                };
                (method, 4, 1)
            }
            _ => return None,
        };
        self.query_lambda_input(source, method, count, position, 1, &[])?
            .into_iter()
            .next()
    }

    /// The methods of a source a clause may be translated into, found as
    /// `source.name(...)` finds them (§12.20.3 leaves every type in a query
    /// to them): the source's own, instance ones on a value and static ones
    /// on a type — `from a in Test select a` calls `Test.Select` — and
    /// failing those, the extension methods the source is a receiver for.
    fn query_candidates(
        &mut self,
        source: &BoundExpression,
        name: &str,
        count: usize,
    ) -> Vec<QueryCandidate> {
        let symbols = self.binder.compilation().symbols();
        let statics = matches!(source.kind, BoundExpressionKind::TypeExpression(_));
        let mut found = Vec::new();
        // The parameters after the clause's own may be left out: a
        // `[CallerLineNumber] int line = -1` behind `Where`'s predicate.
        let omissible = |parameter: &SymbolId| {
            symbols
                .get(*parameter)
                .as_parameter()
                .is_some_and(|detail| detail.has_default || detail.is_params)
        };
        if let Some(symbol) = source.ty.symbol() {
            for candidate in self.binder.lookup_member(symbol, name) {
                // `Where` may be a property or a field holding a delegate,
                // which the clause invokes (§12.20.3 is only a rewriting).
                if matches!(
                    self.kind_of(candidate),
                    crate::symbol::SymbolKind::Property | crate::symbol::SymbolKind::Field
                ) && symbols.get(candidate).modifiers.contains(Modifiers::STATIC) == statics
                {
                    let held = self.member_type(candidate, &source.ty);
                    if let Some((taken, _)) = self.delegate_signature(&held)
                        && taken.len() == count
                    {
                        found.push(QueryCandidate {
                            parameters: taken,
                            type_parameters: Vec::new(),
                            inferred: HashMap::new(),
                        });
                    }
                    continue;
                }
                let Some(detail) = symbols.get(candidate).as_method() else {
                    continue;
                };
                if detail.parameters.len() < count
                    || !detail.parameters[count..].iter().all(omissible)
                    || symbols.get(candidate).modifiers.contains(Modifiers::STATIC) != statics
                {
                    continue;
                }
                found.push(QueryCandidate {
                    parameters: detail.parameters[..count]
                        .iter()
                        .map(|parameter| self.member_type(*parameter, &source.ty))
                        .collect(),
                    type_parameters: detail.type_parameters.clone(),
                    inferred: HashMap::new(),
                });
            }
        }
        if !found.is_empty() || statics {
            return found;
        }
        for candidate in self.binder.extensions_in_scope(&self.context, name) {
            let Some(detail) = symbols.get(candidate).as_method() else {
                continue;
            };
            let Some((first, rest)) = detail.parameters.split_first() else {
                continue;
            };
            if rest.len() != count {
                continue;
            }
            let mut sink = Diagnostics::new();
            let declared = self.binder.type_of(*first, &mut sink).value().clone();
            let mut inferred = HashMap::new();
            self.infer_into(
                &declared,
                &source.ty,
                &detail.type_parameters,
                &mut inferred,
            );
            if !self
                .binder
                .converts_implicitly(&source.ty, &declared.substitute(&inferred))
            {
                continue;
            }
            found.push(QueryCandidate {
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
                type_parameters: detail.type_parameters.clone(),
                inferred,
            });
        }
        found
    }

    /// What the delegate a clause's method takes at `position` hands its
    /// lambda, as the candidates taking one of `arity` parameters there see
    /// it: the range variables' types. What is `given` at other positions
    /// infers the method's own type parameters first — the value itself, or
    /// what a lambda gives back at a delegate's: `Join`'s inner sequence says
    /// what its inner key selector is handed, and `SelectMany`'s first lambda
    /// what its result selector is. `None` unless the candidates agree.
    fn query_lambda_input(
        &mut self,
        source: &BoundExpression,
        name: &str,
        count: usize,
        position: usize,
        arity: usize,
        given: &[(usize, Type)],
    ) -> Option<Vec<Type>> {
        let mut answer: Option<Vec<Type>> = None;
        for candidate in self.query_candidates(source, name, count) {
            let mut inferred = candidate.inferred.clone();
            for (at, ty) in given {
                let Some(parameter) = candidate.parameters.get(*at) else {
                    continue;
                };
                match self.delegate_signature(parameter) {
                    Some((_, returns)) => {
                        self.infer_into(&returns, ty, &candidate.type_parameters, &mut inferred);
                    }
                    None => {
                        self.infer_into(parameter, ty, &candidate.type_parameters, &mut inferred);
                    }
                }
            }
            let Some(parameter) = candidate.parameters.get(position) else {
                continue;
            };
            let Some((taken, _)) = self.delegate_signature(&parameter.substitute(&inferred)) else {
                continue;
            };
            if taken.len() != arity
                || taken
                    .iter()
                    .any(|ty| mentions_any(ty, &candidate.type_parameters))
            {
                continue;
            }
            match &answer {
                None => answer = Some(taken),
                Some(agreed) if *agreed == taken => {}
                Some(_) => return None,
            }
        }
        answer
    }

    /// The arguments of a clause's call, each lambda given the delegate type
    /// the method takes there.
    ///
    /// A query's lambdas are bound against the range variables' types and
    /// made `System.Func`s; a method that takes a delegate of its own with
    /// the same signature — `Where(Func1<T, bool>)` — is handed that
    /// delegate instead, its type parameters inferred from the other
    /// arguments and from what the lambdas give back. Where the candidates
    /// do not all want the same, the lambdas are left to overload
    /// resolution as they are.
    fn as_declared_lambdas(
        &mut self,
        source: &BoundExpression,
        name: &str,
        mut arguments: Vec<BoundExpression>,
        explicit: &[Type],
    ) -> Vec<BoundExpression> {
        if !arguments
            .iter()
            .any(|argument| matches!(argument.kind, BoundExpressionKind::Lambda(_)))
        {
            return arguments;
        }
        let mut agreed: Option<Vec<Option<Type>>> = None;
        for candidate in self.query_candidates(source, name, arguments.len()) {
            let Some(wanted) = self.lambdas_wanted(&candidate, &arguments, explicit) else {
                continue;
            };
            match &agreed {
                None => agreed = Some(wanted),
                Some(existing) if *existing == wanted => {}
                Some(_) => return arguments,
            }
        }
        for (argument, wanted) in arguments.iter_mut().zip(agreed.unwrap_or_default()) {
            if let Some(ty) = wanted {
                argument.ty = ty;
            }
        }
        arguments
    }

    /// The delegate type each lambda among `arguments` would be handed to
    /// `candidate` as, where that is another than the one it has; `None`
    /// where the candidate does not take the lambdas as they are bound.
    fn lambdas_wanted(
        &mut self,
        candidate: &QueryCandidate,
        arguments: &[BoundExpression],
        explicit: &[Type],
    ) -> Option<Vec<Option<Type>>> {
        let mut inferred = candidate.inferred.clone();
        if !explicit.is_empty() {
            if explicit.len() != candidate.type_parameters.len() {
                return None;
            }
            inferred.extend(
                candidate
                    .type_parameters
                    .iter()
                    .copied()
                    .zip(explicit.iter().cloned()),
            );
        }
        for (parameter, argument) in candidate.parameters.iter().zip(arguments) {
            if !matches!(argument.kind, BoundExpressionKind::Lambda(_)) {
                self.infer_into(
                    parameter,
                    &argument.ty,
                    &candidate.type_parameters,
                    &mut inferred,
                );
            }
        }
        // In order, since what one lambda gives back can say what a later
        // one is handed: `SelectMany`'s `U`.
        let mut returned = Vec::with_capacity(arguments.len());
        for (parameter, argument) in candidate.parameters.iter().zip(arguments) {
            let BoundExpressionKind::Lambda(index) = argument.kind else {
                returned.push(None);
                continue;
            };
            let (taken, returns) = self.delegate_signature(&parameter.substitute(&inferred))?;
            let lambda = self.body.lambdas.get(index)?;
            let handed: Vec<Type> = lambda
                .parameters
                .iter()
                .map(|local| self.body.locals[local.0 as usize].ty.clone())
                .collect();
            let gives = lambda.return_type.clone();
            if taken != handed {
                return None;
            }
            self.infer_into(&returns, &gives, &candidate.type_parameters, &mut inferred);
            returned.push(Some(gives));
        }
        let symbols = self.binder.compilation().symbols();
        let mut wanted = Vec::with_capacity(arguments.len());
        for ((parameter, argument), gives) in
            candidate.parameters.iter().zip(arguments).zip(returned)
        {
            let Some(gives) = gives else {
                wanted.push(None);
                continue;
            };
            let ty = parameter.substitute(&inferred);
            let delegate = ty
                .symbol()
                .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Delegate));
            if !delegate || ty == argument.ty || mentions_any(&ty, &candidate.type_parameters) {
                wanted.push(None);
                continue;
            }
            let (_, returns) = self.delegate_signature(&ty)?;
            if returns != gives {
                return None;
            }
            wanted.push(Some(ty));
        }
        Some(wanted)
    }

    /// The tuple a clause hands on: every range variable in scope, and the
    /// one being added last.
    fn query_tuple(
        ranges: &[Range],
        locals: &[LocalId],
        added: BoundExpression,
        span: TextSpan,
    ) -> BoundExpression {
        let mut values: Vec<BoundExpression> = locals
            .iter()
            .zip(ranges)
            .map(|(local, range)| {
                BoundExpression::new(BoundExpressionKind::Local(*local), range.ty.clone(), span)
            })
            .collect();
        values.push(added);
        let ty = Type::Tuple(
            ranges
                .iter()
                .map(|range| TupleElement {
                    name: Some(range.name.clone()),
                    ty: range.ty.clone(),
                })
                .collect(),
        );
        BoundExpression::new(BoundExpressionKind::TupleCreation(values), ty, span)
    }

    /// The range variables after a clause that added one: what the sequence
    /// now holds is the tuple naming them, and the last is the new one.
    fn ranges_of(
        &mut self,
        sequence: &Type,
        before: &[Range],
        added: Option<(String, TextSpan)>,
    ) -> Option<Vec<Range>> {
        let element = self.element_of(sequence);
        let Type::Tuple(elements) = &element else {
            return None;
        };
        let (name, span) = added?;
        let mut ranges: Vec<Range> = before.to_vec();
        ranges.push(Range {
            name,
            span,
            ty: elements.last()?.ty.clone(),
        });
        if ranges.len() != elements.len() {
            return None;
        }
        for (range, element) in ranges.iter_mut().zip(elements) {
            range.ty = element.ty.clone();
        }
        Some(ranges)
    }

    /// What a query's lambda gives back, once it is bound.
    fn lambda_return_of(&self, lambda: &BoundExpression) -> Option<Type> {
        let BoundExpressionKind::Lambda(index) = lambda.kind else {
            return None;
        };
        Some(self.body.lambdas.get(index)?.return_type.clone())
    }

    /// The type a query's element has: the one range variable's, or the
    /// tuple of them all.
    fn query_element(ranges: &[Range]) -> Type {
        match ranges {
            [single] => single.ty.clone(),
            many => Type::Tuple(
                many.iter()
                    .map(|range| TupleElement {
                        name: Some(range.name.clone()),
                        ty: range.ty.clone(),
                    })
                    .collect(),
            ),
        }
    }

    /// The lambda a clause stands for: the range variables in, the clause's
    /// own value out.
    ///
    /// With one range variable the lambda takes it by name. With several it
    /// takes the tuple holding them and reads each back into a local of its
    /// own name first, so that the clause's expression binds as written.
    /// `extra` is a second parameter, for the lambda that pairs a second
    /// `from`'s element with what was in scope. `value` makes the body's
    /// value, given the locals of the range variables and of `extra`.
    fn ranged_lambda(
        &mut self,
        ranges: &[Range],
        extra: Option<&Range>,
        span: TextSpan,
        returns: Option<Type>,
        value: impl FnOnce(&mut Self, &[LocalId], Option<LocalId>) -> Option<BoundExpression>,
    ) -> Option<BoundExpression> {
        self.push_scope();
        let outer_synthetic = std::mem::replace(&mut self.synthetic_span, span);
        self.lambdas.push(LambdaFrame {
            floor: self.scopes.len() - 1,
            return_type: returns.clone().unwrap_or(Type::Error),
            captured: Vec::new(),
            captured_parameters: Vec::new(),
            captures_this: false,
            calls: Vec::new(),
            iterator: None,
            declares: None,
        });
        let input = Self::query_element(ranges);
        let mut parameters = Vec::new();
        let mut statements = Vec::new();
        let mut locals = Vec::new();
        if let [single] = ranges {
            let local = self.declare_local(&single.name, single.ty.clone(), single.span);
            self.body.types.insert(single.span, single.ty.clone());
            parameters.push(local);
            locals.push(local);
        } else {
            let holder = self.declare_local("<>h__TransparentIdentifier", input.clone(), span);
            parameters.push(holder);
            let named = match &input {
                Type::Tuple(elements) => self.tuple_as_named(elements),
                other => other.clone(),
            };
            for (index, range) in ranges.iter().enumerate() {
                let local = self.declare_local(&range.name, range.ty.clone(), range.span);
                self.body.types.insert(range.span, range.ty.clone());
                let field = named.symbol().and_then(|symbol| {
                    self.binder
                        .lookup_member(symbol, &format!("Item{}", index + 1))
                        .first()
                        .copied()
                });
                let receiver =
                    BoundExpression::new(BoundExpressionKind::Local(holder), named.clone(), span);
                let read = match field {
                    Some(field) => {
                        self.member_access(field, Some(Box::new(receiver)), range.ty.clone(), span)
                    }
                    None => BoundExpression::error(span),
                };
                statements.push(BoundStatement::new(
                    BoundStatementKind::LocalDeclaration {
                        local,
                        initializer: Some(read),
                    },
                    span,
                ));
                locals.push(local);
            }
        }
        let second = extra.map(|extra| {
            let local = self.declare_local(&extra.name, extra.ty.clone(), extra.span);
            self.body.types.insert(extra.span, extra.ty.clone());
            parameters.push(local);
            local
        });
        let value = value(self, &locals, second);
        let frame = self.lambdas.pop();
        self.synthetic_span = outer_synthetic;
        self.pop_scope();
        let (value, frame) = (value?, frame?);
        let return_type = returns.unwrap_or_else(|| value.ty.clone());
        let value = self.convert(value, &return_type);
        if return_type.is_error() {
            return None;
        }
        let function = self
            .binder
            .compilation()
            .type_by_metadata_name(match extra {
                Some(_) => "System.Func`3",
                None => "System.Func`2",
            })
            .map(|symbol| {
                let mut type_arguments = vec![input.clone()];
                type_arguments.extend(extra.map(|extra| extra.ty.clone()));
                type_arguments.push(return_type.clone());
                Type::Named {
                    symbol,
                    type_arguments,
                }
            })?;
        statements.push(BoundStatement::new(
            BoundStatementKind::Return(Some(value)),
            span,
        ));
        let body = if statements.len() == 1 {
            statements.pop()?
        } else {
            BoundStatement::new(BoundStatementKind::Block(statements), span)
        };
        let index = self.body.lambdas.len();
        self.body.lambdas.push(BoundLambda {
            span,
            parameters,
            body,
            captured: frame.captured,
            captured_parameters: frame.captured_parameters,
            captures_this: frame.captures_this,
            calls: frame.calls,
            return_type,
            task_type: None,
        });
        Some(BoundExpression::new(
            BoundExpressionKind::Lambda(index),
            function,
            span,
        ))
    }

    /// One call of the rewriting, found the way the source would have found it.
    ///
    /// A type that declares the method itself answers first; otherwise it is
    /// an extension method, which is how `IEnumerable<T>` has any of these.
    fn query_call(
        &mut self,
        receiver: BoundExpression,
        name: &str,
        arguments: Vec<BoundExpression>,
        explicit: Vec<Type>,
        at: &SyntaxNode,
    ) -> Option<BoundExpression> {
        let arguments = self.as_declared_lambdas(&receiver, name, arguments, &explicit);
        let ty = receiver.ty.clone();
        // The call is the clause's: `[CallerLineNumber]` on `Where` gets the
        // line of the `where`, not of the `from` the query starts with.
        let span = at.span();
        if let Some(symbol) = ty.symbol() {
            let members = self.binder.lookup_member(symbol, name);
            // `Where` held in a property or a field of a delegate type is
            // invoked, as `source.Where(...)` would invoke it.
            if let Some(member) = members.iter().copied().find(|member| {
                matches!(
                    self.kind_of(*member),
                    crate::symbol::SymbolKind::Property | crate::symbol::SymbolKind::Field
                )
            }) {
                let held = self.member_type(member, &ty);
                if self.is_delegate(&held) {
                    let access = self.member_access(member, Some(Box::new(receiver)), held, span);
                    return Some(self.invoke_delegate(access, arguments, span));
                }
            }
            if !members.is_empty() {
                return self.bind_member_call_with(&ty, name, receiver, arguments, &explicit, span);
            }
        }
        self.bind_extension_call(name, at, receiver, &arguments, &explicit, span)
    }

    /// `from x in xs`, which brings `x` into scope as one of what `xs` holds.
    fn bind_from_clause(&mut self, node: &SyntaxNode) -> Type {
        let written = written_element_type(node);
        let source = range_source(node).map(|source| self.bind_expression(&source));
        let source = source.map_or(Type::Error, |source| source.ty);
        let element = match &written {
            // `from int n in xs` says what the elements are to be read as.
            Some(written) if written.text().trim() != "var" => self.resolve(written),
            _ => self.element_of(&source),
        };
        self.declare_range_variable(node, element.clone());
        element
    }

    /// The clauses after the first `from`, in order, and the type the last of
    /// them makes.
    fn bind_query_body(&mut self, node: &SyntaxNode) -> Type {
        let mut result = Type::Error;
        for clause in node.children() {
            match clause.kind() {
                SyntaxKind::FromClause => {
                    self.bind_from_clause(&clause);
                }
                // `let y = e` is a range variable like any other, with the
                // type of whatever it was given.
                SyntaxKind::LetClause => {
                    let value = clause
                        .children()
                        .find(|child| child.kind().is_expression())
                        .map(|value| self.bind_expression(&value));
                    let ty = value.map_or(Type::Error, |value| value.ty);
                    self.declare_range_variable(&clause, ty);
                }
                SyntaxKind::WhereClause => {
                    for child in clause.children().filter(|c| c.kind().is_expression()) {
                        self.bind_expression(&child);
                    }
                }
                // Each ordering is a node of its own, holding the expression
                // to sort by and, sometimes, a direction.
                SyntaxKind::OrderByClause => {
                    for ordering in clause.children() {
                        for child in ordering.children().filter(|c| c.kind().is_expression()) {
                            self.bind_expression(&child);
                        }
                    }
                }
                SyntaxKind::JoinClause => self.bind_join_clause(&clause),
                SyntaxKind::SelectClause => {
                    let selected = clause
                        .children()
                        .find(|child| child.kind().is_expression())
                        .map(|value| self.bind_expression(&value));
                    result = self.sequence_of(selected.map_or(Type::Error, |value| value.ty));
                }
                // `group e by k` makes one `IGrouping<k, e>` per distinct key.
                SyntaxKind::GroupClause => {
                    let mut values = clause
                        .children()
                        .filter(|child| child.kind().is_expression());
                    let grouped = values
                        .next()
                        .map(|value| self.bind_expression(&value))
                        .map_or(Type::Error, |value| value.ty);
                    let key = values
                        .next()
                        .map(|value| self.bind_expression(&value))
                        .map_or(Type::Error, |value| value.ty);
                    let grouping = self
                        .binder
                        .compilation()
                        .type_by_metadata_name("System.Linq.IGrouping`2")
                        .map_or(Type::Error, |symbol| Type::Named {
                            symbol,
                            type_arguments: vec![key, grouped],
                        });
                    result = self.sequence_of(grouping);
                }
                // `into g` starts a fresh query over what came before, with
                // `g` standing for one of its elements.
                SyntaxKind::QueryContinuation => {
                    let element = self.element_of(&result);
                    self.declare_range_variable(&clause, element);
                    for child in clause.children() {
                        if child.kind() == SyntaxKind::QueryBody {
                            result = self.bind_query_body(&child);
                        }
                    }
                }
                _ => {}
            }
        }
        result
    }

    /// `join b in xs on a equals b into g`.
    fn bind_join_clause(&mut self, node: &SyntaxNode) {
        let written = written_element_type(node);
        let source_node = range_source(node);
        let source = source_node
            .as_ref()
            .map(|source| self.bind_expression(source))
            .map_or(Type::Error, |source| source.ty);
        let element = match &written {
            Some(written) if written.text().trim() != "var" => self.resolve(written),
            _ => self.element_of(&source),
        };
        self.declare_range_variable(node, element.clone());
        // The two keys, which are ordinary expressions on either side of the
        // `equals`, and are bound with the joined variable already in scope.
        let keys: Vec<SyntaxNode> = node
            .children()
            .filter(|child| {
                child.kind().is_expression()
                    && Some(child.span()) != source_node.as_ref().map(SyntaxNode::span)
            })
            .collect();
        for key in keys {
            self.bind_expression(&key);
        }
        if let Some(into) = node.child_of_kind(SyntaxKind::JoinIntoClause) {
            let sequence = self.sequence_of(element);
            self.declare_range_variable(&into, sequence);
        }
    }

    /// Brings the name a clause wrote into scope as a local.
    fn declare_range_variable(&mut self, clause: &SyntaxNode, ty: Type) {
        let Some(token) = clause
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        else {
            return;
        };
        self.declare_local(token.value_text(), ty.clone(), token.span());
        self.body.types.insert(token.span(), ty);
    }

    /// What one of a sequence holds.
    fn element_of(&mut self, sequence: &Type) -> Type {
        match self.enumeration_of(sequence, (TextSpan::new(0, 0), TextSpan::new(0, 0))) {
            Some((_, element)) => element,
            None => self.element_type_of(sequence),
        }
    }

    /// What one of a sequence holds, where it is one: what `foreach` would
    /// walk it as.
    fn enumerated_element(&mut self, sequence: &Type) -> Type {
        self.enumeration_of(sequence, (TextSpan::new(0, 0), TextSpan::new(0, 0)))
            .map_or(Type::Error, |(_, element)| element)
    }

    /// `IEnumerable<element>`, which is what every query produces.
    fn sequence_of(&self, element: Type) -> Type {
        self.binder
            .compilation()
            .type_by_metadata_name("System.Collections.Generic.IEnumerable`1")
            .map_or(Type::Error, |symbol| Type::Named {
                symbol,
                type_arguments: vec![element],
            })
    }
}

/// The type written in front of a range variable, where one was.
///
/// `from x in xs` and `from int x in xs` differ only in that: the name is an
/// identifier token either way and everything after it is an expression, and
/// an identifier is type syntax as much as expression syntax. What tells them
/// apart is position — a written type is the child that ends before the name
/// begins.
fn written_element_type(clause: &SyntaxNode) -> Option<SyntaxNode> {
    let name = clause
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
    clause
        .children()
        .find(|child| child.span().end() <= name.span().start())
}

/// The collection a range variable is drawn from: the first child after the
/// name it is bound to.
fn range_source(clause: &SyntaxNode) -> Option<SyntaxNode> {
    let name = clause
        .child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
    clause
        .children()
        .find(|child| child.span().start() >= name.span().end())
}

/// Whether `group v by k` groups the one range variable itself, `v` being
/// its name: the `GroupBy` then takes no element selector (§12.20.3.5).
fn groups_the_range(clause: &SyntaxNode, range: &str) -> bool {
    clause
        .children()
        .find(|child| child.kind().is_expression())
        .is_some_and(|grouped| {
            grouped.kind() == SyntaxKind::IdentifierName && grouped.text().trim() == range
        })
}
