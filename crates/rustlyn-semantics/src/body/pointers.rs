//! Unsafe code and spans: `stackalloc`, `fixed`, `p->x`, and the spans over
//! inline arrays.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::BodyBinder;
use crate::bound::{
    BoundExpression, BoundExpressionKind, BoundStatement, BoundStatementKind, ConstantValue,
};
use crate::corlib::SpecialType;
use crate::symbol::{RefKind, SymbolKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// Binds `c ? a : b`, against a target type where there is one.
    ///
    /// Written on its own the two branches decide between them what the
    /// conditional is. Where neither has a type of its own — two lambdas, two
    /// collection expressions — there is nothing for them to decide with, and
    /// §12.18 hands the question to whatever the conditional is being
    /// converted to.
    /// `stackalloc T[n]`, `stackalloc T[] { ... }` and `stackalloc[] { ... }`:
    /// a `T*` to memory on the stack, holding `n` elements or the ones
    /// written. What it is given to may make it a `Span<T>` instead.
    pub(super) fn bind_stackalloc(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let int = self.special(SpecialType::Int32);
        // `stackalloc byte[n]` writes an array type whose rank holds the
        // count; `stackalloc[] { .. }` writes only the rank.
        let (element, rank) = match node.child_of_kind(SyntaxKind::ArrayType) {
            Some(array) => {
                let element = array
                    .children()
                    .find(|child| child.kind().is_type_node())
                    .map_or(Type::Error, |written| self.resolve(&written));
                (
                    Some(element),
                    array.child_of_kind(SyntaxKind::ArrayRankSpecifier),
                )
            }
            None => (None, node.child_of_kind(SyntaxKind::ArrayRankSpecifier)),
        };
        let written_count = rank
            .and_then(|rank| {
                rank.children()
                    .find(|child| child.kind().is_expression())
                    .filter(|child| child.kind() != SyntaxKind::OmittedArraySizeExpression)
            })
            .map(|count| {
                let count = self.bind_expression(&count);
                self.convert(count, &int)
            });
        let mut elements = Vec::new();
        if let Some(initializer) = node.child_of_kind(SyntaxKind::ArrayInitializerExpression) {
            for child in initializer.children() {
                if child.kind().is_expression() {
                    elements.push(self.bind_expression(&child));
                }
            }
        }
        let element = element
            .or_else(|| elements.first().map(|first| first.ty.clone()))
            .unwrap_or(Type::Error);
        let elements: Vec<BoundExpression> = elements
            .into_iter()
            .map(|value| self.convert(value, &element))
            .collect();
        let count = written_count.unwrap_or_else(|| {
            BoundExpression::new(
                BoundExpressionKind::Literal(ConstantValue::Int32(elements.len() as i32)),
                int.clone(),
                span,
            )
        });
        // Only the whole initializer of a local is a pointer; anywhere else
        // — an argument, a branch of a conditional — a `stackalloc` is the
        // `Span<T>` over what it allocates (§12.8.22).
        let initializes_a_local = node
            .parent()
            .filter(|parent| parent.kind() == SyntaxKind::EqualsValueClause)
            .and_then(|clause| clause.parent())
            .is_some_and(|declarator| declarator.kind() == SyntaxKind::VariableDeclarator);
        if !initializes_a_local {
            self.body.nested_stackallocs.push(span);
        }
        let span_type = (!initializes_a_local && !element.is_error())
            .then(|| self.framework_type("System.Span`1"))
            .flatten()
            .and_then(|span| {
                span.symbol().map(|symbol| Type::Named {
                    symbol,
                    type_arguments: vec![element.clone()],
                })
            });
        let ty = if element.is_error() {
            Type::Error
        } else if let Some(span_type) = &span_type {
            span_type.clone()
        } else {
            Type::Pointer(Box::new(element.clone()))
        };
        BoundExpression::new(
            BoundExpressionKind::StackAlloc {
                element,
                count: Box::new(count),
                elements,
                span: span_type,
            },
            ty,
            span,
        )
    }

    /// Whether a type is `Span<T>` or `ReadOnlySpan<T>` over anything.
    pub(super) fn is_span_type(&self, ty: &Type) -> bool {
        let Type::Named { symbol, .. } = ty else {
            return false;
        };
        let compilation = self.binder.compilation();
        ["System.Span`1", "System.ReadOnlySpan`1"]
            .into_iter()
            .filter_map(|name| compilation.type_by_metadata_name(name))
            .any(|span| span == *symbol)
    }

    /// Whether a type is `Span<T>` or `ReadOnlySpan<T>` over this element.
    pub(super) fn is_span_of(&self, ty: &Type, element: &Type) -> bool {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return false;
        };
        let compilation = self.binder.compilation();
        type_arguments.first() == Some(element)
            && ["System.Span`1", "System.ReadOnlySpan`1"]
                .into_iter()
                .filter_map(|name| compilation.type_by_metadata_name(name))
                .any(|span| span == *symbol)
    }

    /// `fixed (int* p = new Fixable())` where only an extension gives
    /// `Fixable` its `GetPinnableReference` (C# 14 extension blocks included):
    /// the reference that call returns is what is pinned. A type with a
    /// `GetPinnableReference` of its own is left as it is, for the backend
    /// to call.
    pub(super) fn pinnable_through_extension(
        &mut self,
        value: BoundExpression,
        pointer: &Type,
    ) -> BoundExpression {
        let own = !matches!(value.ty, Type::TypeParameter(_))
            && value.ty.symbol().is_some_and(|symbol| {
                self.binder
                    .lookup_member(symbol, "GetPinnableReference")
                    .into_iter()
                    .any(|member| {
                        self.binder
                            .compilation()
                            .symbols()
                            .get(member)
                            .as_method()
                            .is_some_and(|detail| detail.parameters.is_empty())
                    })
            });
        // An array and a string pin their own elements, whatever extension
        // methods say.
        if own
            || !matches!(value.ty, Type::Named { .. } | Type::TypeParameter(_))
            || self.binder.special_of(&value.ty) == Some(SpecialType::String)
        {
            return value;
        }
        let span = value.span;
        // A type parameter's constraint may give it one: the call goes
        // through the constraint, on the variable itself.
        if matches!(value.ty, Type::TypeParameter(_))
            && let Some((method, through)) =
                self.member_through(&value.ty, "GetPinnableReference", SymbolKind::Method)
            && self
                .binder
                .compilation()
                .symbols()
                .get(method)
                .as_method()
                .is_some_and(|detail| detail.parameters.is_empty())
        {
            let ty = self.member_type(method, &through);
            let call = BoundExpression::new(
                BoundExpressionKind::Call {
                    receiver: Some(Box::new(value)),
                    method,
                    type_arguments: Vec::new(),
                    arguments: Vec::new(),
                    virtual_call: true,
                },
                ty,
                span,
            );
            return BoundExpression::new(
                BoundExpressionKind::AddressOf {
                    operand: Box::new(call),
                },
                pointer.clone(),
                span,
            );
        }
        let Some(call) = self.extension_call_at("GetPinnableReference", value.clone(), span) else {
            return value;
        };
        BoundExpression::new(
            BoundExpressionKind::AddressOf {
                operand: Box::new(call),
            },
            pointer.clone(),
            span,
        )
    }

    /// `value.GetPinnableReference()`, which a `fixed` statement pins. A
    /// value that may be null is kept in a local first, where the statement
    /// can test it: a null one pins nothing, and the pointer is null.
    pub(super) fn pinnable_reference(
        &mut self,
        value: BoundExpression,
        statements: &mut Vec<BoundStatement>,
    ) -> Option<BoundExpression> {
        let span = value.span;
        let ty = value.ty.clone();
        let symbols = self.binder.compilation().symbols();
        let value_type = match &ty {
            Type::Named { symbol, .. } => {
                symbols
                    .get(*symbol)
                    .type_kind()
                    .is_some_and(|kind| !kind.is_reference_type())
                    && self.binder.nullable_underlying(&ty).is_none()
            }
            Type::TypeParameter(symbol) => symbols
                .get(*symbol)
                .as_type_parameter()
                .is_some_and(|detail| detail.value_type),
            _ => false,
        };
        // A variable is tested where it is, and called on where it is: a
        // `T` that turns out a struct is changed by the call in place.
        let variable = matches!(
            value.kind,
            BoundExpressionKind::Local(_) | BoundExpressionKind::Parameter(_)
        );
        let (subject, held) = if value_type || variable {
            (value, None)
        } else {
            let held = self.declare_synthetic_local("pinnable", ty.clone());
            let read = BoundExpression::new(BoundExpressionKind::Local(held), ty.clone(), span);
            (read, Some((held, value)))
        };
        let instance = ty.symbol().is_some_and(|symbol| {
            self.binder
                .lookup_member(symbol, "GetPinnableReference")
                .into_iter()
                .any(|id| {
                    self.kind_of(id) == SymbolKind::Method
                        && self
                            .binder
                            .compilation()
                            .symbols()
                            .get(id)
                            .as_method()
                            .is_some_and(|detail| {
                                detail.parameters.is_empty() && detail.type_parameters.is_empty()
                            })
                })
        });
        let call = if instance {
            self.bind_member_call(&ty, "GetPinnableReference", subject, Vec::new(), span)
        } else {
            self.extension_call_at("GetPinnableReference", subject, span)
        }?;
        if let Some((held, value)) = held {
            statements.push(BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local: held,
                    initializer: Some(value),
                },
                span,
            ));
        }
        Some(call)
    }

    /// `*p`, which is what `p->x` reaches `x` on (§24.6.3).
    pub(super) fn pointed_at(&mut self, pointer: BoundExpression) -> BoundExpression {
        let Type::Pointer(element) = &pointer.ty else {
            if !pointer.ty.is_error() {
                self.report(ErrorCode::ErrPtrExpected, pointer.span, &[]);
            }
            return BoundExpression::error(pointer.span);
        };
        let element = (**element).clone();
        let span = pointer.span;
        BoundExpression::new(
            BoundExpressionKind::Dereference {
                operand: Box::new(pointer),
            },
            element,
            span,
        )
    }

    /// Whether code at this span is in an unsafe context: inside an
    /// `unsafe` block, member or type (§24.2).
    pub(super) fn in_unsafe_context(&self, span: TextSpan) -> bool {
        let Some(node) = self.syntax_at(span) else {
            return false;
        };
        let mut current = Some(node);
        while let Some(node) = current {
            if node.kind() == SyntaxKind::UnsafeStatement
                || node
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::UnsafeKeyword)
            {
                return true;
            }
            current = node.parent().cloned();
        }
        false
    }

    /// The span over an inline array's elements (C# 12):
    /// `MemoryMarshal.CreateSpan(ref Unsafe.As<TBuffer, T>(ref buffer),
    /// length)`, or the read-only one. A buffer that is not a variable is
    /// copied into one first, since a span needs somewhere to point; a
    /// read-only variable is not copied, and its span is the read-only one.
    pub(super) fn inline_array_span(
        &mut self,
        buffer: BoundExpression,
        element: &Type,
        length: i32,
        readonly: bool,
        span: TextSpan,
    ) -> Option<BoundExpression> {
        let unsafe_type = self.framework_type("System.Runtime.CompilerServices.Unsafe")?;
        let marshal = self.framework_type("System.Runtime.InteropServices.MemoryMarshal")?;
        let buffer_type = buffer.ty.clone();
        // A read-only span may point into what a `ref readonly` member hands
        // back: that is a variable, just not one to write through.
        let (prefix, place) = if self.is_variable(&buffer)
            || (readonly && self.is_returned_reference(&buffer))
        {
            (None, buffer)
        } else {
            let held = self.declare_synthetic_local("buffer", buffer_type.clone());
            let read =
                BoundExpression::new(BoundExpressionKind::Local(held), buffer_type.clone(), span);
            let store = BoundExpression::new(
                BoundExpressionKind::Assignment {
                    target: Box::new(read.clone()),
                    value: Box::new(buffer),
                },
                buffer_type.clone(),
                span,
            );
            (Some(store), read)
        };
        let by_ref = |operand: BoundExpression| {
            let ty = operand.ty.clone();
            BoundExpression::new(
                BoundExpressionKind::RefArgument {
                    kind: RefKind::Ref,
                    operand: Box::new(operand),
                },
                ty,
                span,
            )
        };
        let first = self.call_static_with(
            &unsafe_type,
            "As",
            vec![by_ref(place)],
            &[buffer_type, element.clone()],
            span,
        )?;
        let first = BoundExpression::new(first.kind, element.clone(), span);
        let count = BoundExpression::new(
            BoundExpressionKind::Literal(ConstantValue::Int32(length)),
            self.special(SpecialType::Int32),
            span,
        );
        let name = if readonly {
            "CreateReadOnlySpan"
        } else {
            "CreateSpan"
        };
        let made = self.call_static_with(
            &marshal,
            name,
            vec![by_ref(first), count],
            std::slice::from_ref(element),
            span,
        )?;
        Some(match prefix {
            Some(store) => {
                let ty = made.ty.clone();
                BoundExpression::new(BoundExpressionKind::Sequence(vec![store, made]), ty, span)
            }
            None => made,
        })
    }
}
