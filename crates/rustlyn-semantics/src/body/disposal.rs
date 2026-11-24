//! What `await using` disposes of its resources with (§13.14): a
//! `DisposeAsync` the type has, found by pattern, or else the one of
//! `IAsyncDisposable`, awaited in the `finally` the statement means.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_text::TextSpan;

use super::BodyBinder;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundStatement, BoundStatementKind, BoundUsingResource,
    ConstantValue, ConversionKind,
};
use crate::conversions::BinaryOperator;
use crate::corlib::SpecialType;
use crate::symbol::{Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// The resources of an `await using`, each given the statement that
    /// disposes of it.
    ///
    /// A `dynamic` resource is disposed as the `IAsyncDisposable` the
    /// runtime binder converts it to, and the conversion happens as the
    /// resource is taken, not when it is let go (Roslyn converts it into a
    /// temporary right after the declaration): that temporary is a resource
    /// of its own, after the one it was converted from.
    pub(super) fn dispose_asynchronously(
        &mut self,
        resources: Vec<BoundUsingResource>,
        at: TextSpan,
    ) -> Vec<BoundUsingResource> {
        let mut disposed = Vec::with_capacity(resources.len());
        for mut resource in resources {
            let span = resource.value.span;
            let declared = self.body.locals[resource.local.0 as usize].ty.clone();
            let read = BoundExpression::new(
                BoundExpressionKind::Local(resource.local),
                declared.clone(),
                span,
            );
            if matches!(declared, Type::Dynamic) {
                let Some(disposable) = self.framework_type("System.IAsyncDisposable") else {
                    disposed.push(resource);
                    continue;
                };
                let converted = self.convert(read, &disposable);
                let held = self.declare_synthetic_local("disposable", disposable);
                disposed.push(resource);
                let awaited = self.async_disposal(held, span, at);
                disposed.push(BoundUsingResource {
                    local: held,
                    value: converted,
                    dispose: None,
                    awaited,
                });
                continue;
            }
            // `await using (null)` holds nothing, and there is nothing to
            // dispose or to look for.
            if !matches!(declared, Type::Null | Type::Error) {
                resource.awaited = self.async_disposal(resource.local, span, at);
            }
            disposed.push(resource);
        }
        disposed
    }

    /// `if (r != null) await r.DisposeAsync();` for the resource in `local`,
    /// or CS8410 where its type has no `DisposeAsync` either way.
    fn async_disposal(
        &mut self,
        local: crate::bound::LocalId,
        span: TextSpan,
        at: TextSpan,
    ) -> Option<Box<BoundStatement>> {
        let found = self.disposal_if_any(local, span);
        if found.is_none() {
            let declared = self.body.locals[local.0 as usize].ty.clone();
            let shown = self.display(&declared);
            self.report(ErrorCode::ErrNoConvToIAsyncDisp, at, &[&shown]);
        }
        found
    }

    /// `if (r != null) await r.DisposeAsync();` for what `local` holds, where
    /// its type has a `DisposeAsync`: one of its own it can be called with,
    /// or `IAsyncDisposable`'s. `await foreach` disposes its enumerator so,
    /// and one that has neither is not disposed at all.
    ///
    /// The test is what Roslyn writes: none for a struct, `HasValue` for a
    /// `T?` — whose `DisposeAsync` is then called on the value inside,
    /// `GetValueOrDefault()` — and a comparison with `null` for everything
    /// else, a type parameter boxed for it.
    pub(super) fn disposal_if_any(
        &mut self,
        local: crate::bound::LocalId,
        span: TextSpan,
    ) -> Option<Box<BoundStatement>> {
        let declared = self.body.locals[local.0 as usize].ty.clone();
        let read = BoundExpression::new(BoundExpressionKind::Local(local), declared.clone(), span);
        let inside = self.binder.nullable_underlying(&declared);
        let receiver = match &inside {
            Some(_) => self.call_on(read.clone(), "GetValueOrDefault", Vec::new(), span)?,
            None => read.clone(),
        };
        let call = match self.pattern_call(receiver.clone(), &declared, "DisposeAsync", span, false)
        {
            Some(call) => call,
            None => self.interface_dispose_async(receiver, &declared, span)?,
        };
        let awaited = self.awaited(call, span);
        let dispose = BoundStatement::new(BoundStatementKind::Expression(awaited), span);
        let boolean = self.special(SpecialType::Boolean);
        let condition = if inside.is_some() {
            let has_value = declared.symbol().and_then(|symbol| {
                self.binder
                    .lookup_member(symbol, "HasValue")
                    .into_iter()
                    .find(|candidate| self.kind_of(*candidate) == SymbolKind::Property)
            })?;
            Some(self.member_access(has_value, Some(Box::new(read)), boolean.clone(), span))
        } else if self.is_value_type(&declared) {
            None
        } else {
            // A type parameter is compared as the `object` it boxes to,
            // which is `null` only where it is a reference that is.
            let compared = match &declared {
                Type::TypeParameter(_) if !self.binder.held_by_reference(&declared) => {
                    let object = self.special(SpecialType::Object);
                    BoundExpression::new(
                        BoundExpressionKind::Conversion {
                            operand: Box::new(read),
                            conversion: ConversionKind::Boxing,
                            written: false,
                        },
                        object,
                        span,
                    )
                }
                _ => read,
            };
            Some(BoundExpression::new(
                BoundExpressionKind::Binary {
                    operator: BinaryOperator::Inequality,
                    left: Box::new(compared),
                    right: Box::new(BoundExpression::new(
                        BoundExpressionKind::Literal(ConstantValue::Null),
                        Type::Null,
                        span,
                    )),
                },
                boolean,
                span,
            ))
        };
        Some(Box::new(match condition {
            Some(condition) => BoundStatement::new(
                BoundStatementKind::If {
                    condition,
                    consequence: Box::new(dispose),
                    alternative: None,
                },
                span,
            ),
            None => dispose,
        }))
    }

    /// `receiver.Name()` where `declared` has a method of the name the code
    /// here can call with nothing — optional and `params` parameters take
    /// their defaults — which is how the patterns of `await using` (§13.14)
    /// and `await foreach` (§13.9.5) find `DisposeAsync`,
    /// `GetAsyncEnumerator` and `MoveNextAsync`. An extension method does not
    /// count, nor an interface's method implemented explicitly, nor a static
    /// one, and a member of the name that is not a method rules the pattern
    /// out. `await foreach` wants what it finds public too.
    pub(super) fn pattern_call(
        &mut self,
        receiver: BoundExpression,
        declared: &Type,
        name: &str,
        span: TextSpan,
        public: bool,
    ) -> Option<BoundExpression> {
        let symbol = declared.symbol()?;
        let found = self
            .binder
            .lookup_member_where(symbol, name, &|member| self.accessible(member));
        if found.is_empty()
            || found
                .iter()
                .any(|id| self.kind_of(*id) != SymbolKind::Method)
        {
            return None;
        }
        let symbols = self.binder.compilation().symbols();
        let candidates: Vec<SymbolId> = found
            .into_iter()
            .filter(|id| !symbols.get(*id).modifiers.contains(Modifiers::STATIC))
            .collect();
        if candidates.is_empty() {
            return None;
        }
        // A type parameter constrained to two interfaces that each declare
        // one has two, neither hiding the other: the lookup is ambiguous,
        // and the pattern gives way to `IAsyncDisposable` (Roslyn's
        // `PatternLookupResult.ResultHasErrors`).
        let mut interfaces: Vec<SymbolId> = candidates
            .iter()
            .filter_map(|id| symbols.get(*id).container)
            .collect();
        interfaces.sort_unstable_by_key(|id| id.0);
        interfaces.dedup();
        if interfaces.len() > 1
            && interfaces
                .iter()
                .all(|container| symbols.get(*container).type_kind() == Some(TypeKind::Interface))
        {
            return None;
        }
        let resolved = self.resolve_call(&candidates, &[], &self.evidence(&[]), declared, &[])?;
        let method = resolved.method;
        // A member of an interface is public whatever it was written with.
        let symbols = self.binder.compilation().symbols();
        let in_interface = symbols.get(method).container.is_some_and(|container| {
            symbols.get(container).type_kind() == Some(TypeKind::Interface)
        });
        if public
            && !in_interface
            && !matches!(
                symbols.get(method).accessibility,
                crate::symbol::Accessibility::Public
            )
        {
            return None;
        }
        let result = self
            .member_type(method, declared)
            .substitute(&resolved.substitution);
        let arguments =
            self.convert_arguments(method, Vec::new(), declared, &resolved.substitution, span);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(receiver)),
                method,
                type_arguments: resolved.type_arguments,
                arguments,
                virtual_call: self.is_virtual_call(method, None),
            },
            result,
            span,
        ))
    }

    /// Whether a value of the type can never be `null`: a struct, an enum,
    /// or a type parameter constrained to be one.
    fn is_value_type(&self, ty: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        match ty {
            Type::TypeParameter(symbol) => symbols
                .get(*symbol)
                .as_type_parameter()
                .is_some_and(|detail| detail.value_type),
            Type::Tuple(_) => true,
            Type::Named { symbol, .. } => matches!(
                symbols.get(*symbol).type_kind(),
                Some(TypeKind::Struct | TypeKind::Enum | TypeKind::RecordStruct)
            ),
            _ => false,
        }
    }

    /// `((IAsyncDisposable)receiver).DisposeAsync()`, where the resource's
    /// type converts to the interface: a struct is called through it
    /// without being boxed, as Roslyn calls it.
    fn interface_dispose_async(
        &mut self,
        receiver: BoundExpression,
        declared: &Type,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let disposable = self.framework_type("System.IAsyncDisposable")?;
        if !self.binder.converts_implicitly(declared, &disposable) {
            return None;
        }
        let method = self
            .binder
            .lookup_member(disposable.symbol()?, "DisposeAsync")
            .into_iter()
            .find(|candidate| self.kind_of(*candidate) == SymbolKind::Method)?;
        let result = self.member_type(method, &disposable);
        Some(BoundExpression::new(
            BoundExpressionKind::Call {
                receiver: Some(Box::new(receiver)),
                method,
                type_arguments: Vec::new(),
                arguments: Vec::new(),
                virtual_call: true,
            },
            result,
            span,
        ))
    }
}
