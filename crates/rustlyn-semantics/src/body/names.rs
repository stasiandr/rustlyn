//! Names and member access: simple names, `a.b` and `a?.b`, the receiver a
//! member gets, accessibility and static access, and the members extension
//! blocks (C# 14) add.

use std::collections::HashMap;

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, identifier_text, is_constructed, missing_member_code};
use crate::binder::{Diagnostics, Resolution};
use crate::bound::{BoundExpression, BoundExpressionKind, BoundSymbol, ConversionKind};
use crate::corlib::SpecialType;
use crate::symbol::{Accessibility, Detail, MethodKind, Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    /// Whether a member is one only an instance has: not `static`, not a
    /// constant, not a type.
    pub(super) fn needs_this(&self, member: SymbolId) -> bool {
        let symbol = self.binder.compilation().symbols().get(member);
        matches!(
            symbol.kind,
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Method
        ) && !symbol.modifiers.contains(Modifiers::STATIC)
            && !symbol.modifiers.contains(Modifiers::CONST)
            && symbol
                .as_method()
                .is_none_or(|detail| detail.method_kind == MethodKind::Ordinary)
    }

    /// Whether the code being bound has no `this`: the body of a `static`
    /// member, where naming an instance member is CS0120.
    pub(super) fn static_context(&self) -> bool {
        self.member.is_some_and(|member| {
            let symbol = self.binder.compilation().symbols().get(member);
            symbol.modifiers.contains(Modifiers::STATIC)
                && matches!(
                    symbol.kind,
                    SymbolKind::Method | SymbolKind::Property | SymbolKind::Field
                )
                && !symbol.name.starts_with('<')
        })
    }

    /// Whether code in the types around this body may name `member`, as far
    /// as this binder can tell: a private member inside its own type (or one
    /// nested in it), a protected one inside a type derived from its own.
    /// Anything from the same compilation that is internal is; anything this
    /// cannot judge counts as accessible.
    pub(super) fn accessible(&self, member: SymbolId) -> bool {
        let compilation = self.binder.compilation();
        if !compilation.sees(member, self.context.tree()) {
            return false;
        }
        let symbols = compilation.symbols();
        let symbol = symbols.get(member);
        if !matches!(
            symbol.accessibility,
            Accessibility::Private | Accessibility::Protected | Accessibility::ProtectedAndInternal
        ) {
            return true;
        }
        let Some(owner) = symbol
            .container
            .filter(|owner| symbols.get(*owner).kind == SymbolKind::NamedType)
        else {
            return true;
        };
        let enclosing = self.context.enclosing_types();
        let inside = |ty: SymbolId| {
            enclosing.iter().any(|around| {
                let mut current = Some(*around);
                while let Some(id) = current {
                    if id == ty {
                        return true;
                    }
                    current = symbols
                        .get(id)
                        .container
                        .filter(|outer| symbols.get(*outer).kind == SymbolKind::NamedType);
                }
                false
            })
        };
        let derived = |ty: SymbolId| {
            // A protected member of an interface is for whatever implements
            // it or derives from it (C# 8), class or interface.
            if symbols.get(ty).type_kind() == Some(TypeKind::Interface) {
                return enclosing
                    .iter()
                    .any(|around| self.has_interface(*around, ty));
            }
            enclosing.iter().any(|around| {
                let mut current = Some(*around);
                let mut depth = 0;
                while let Some(id) = current {
                    if id == ty || depth > 32 {
                        return true;
                    }
                    current = self.binder.base_class_of(id).and_then(|base| base.symbol());
                    depth += 1;
                }
                false
            })
        };
        match symbol.accessibility {
            Accessibility::Private => inside(owner),
            Accessibility::Protected | Accessibility::ProtectedAndInternal => {
                compilation.is_from_metadata(member) || inside(owner) || derived(owner)
            }
            _ => true,
        }
    }

    /// Whether `ty` is `interface` or has it among its
    /// [`base_interfaces`](Self::base_interfaces).
    fn has_interface(&self, ty: SymbolId, interface: SymbolId) -> bool {
        ty == interface || self.base_interfaces(ty).contains(&interface)
    }

    /// Every interface `ty` lists, has through what it lists, or has through
    /// its base classes, each once and constructions aside: `class C : B`
    /// where `B : I3<int>` and `I3<T> : I1<T>` has `I3` and `I1`.
    pub(super) fn base_interfaces(&self, ty: SymbolId) -> Vec<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let mut found = Vec::new();
        let mut seen = vec![ty];
        let mut pending = vec![ty];
        while let Some(next) = pending.pop() {
            let bases: Vec<SymbolId> = self
                .binder
                .base_types_of(next)
                .iter()
                .filter_map(Type::symbol)
                .chain(
                    self.binder
                        .base_class_of(next)
                        .and_then(|base| base.symbol()),
                )
                .collect();
            for base in bases {
                if seen.contains(&base) || seen.len() > 64 {
                    continue;
                }
                seen.push(base);
                pending.push(base);
                if symbols.get(base).type_kind() == Some(TypeKind::Interface) {
                    found.push(base);
                }
            }
        }
        found
    }

    /// The members called `name` of `ty` that the code here may access,
    /// nearest first — an inaccessible one hides nothing — or, where it may
    /// access none, all of them, for the error to name.
    pub(super) fn lookup_member_here(&self, ty: SymbolId, name: &str) -> Vec<SymbolId> {
        let found = self
            .binder
            .lookup_member_where(ty, name, &|member| self.accessible(member));
        if found.is_empty() {
            self.unseen_removed(self.binder.lookup_member(ty, name))
        } else {
            found
        }
    }

    /// What a lookup found, less a reference's internal members this code
    /// is no friend of: to it they are not there at all, as they were not
    /// before friends' internals were read, and a name they would take
    /// goes on to the extension methods.
    fn unseen_removed(&self, mut found: Vec<SymbolId>) -> Vec<SymbolId> {
        let compilation = self.binder.compilation();
        let tree = self.context.tree();
        found.retain(|member| compilation.sees(*member, tree));
        found
    }

    /// The same for a name that is invoked, where only what can be invoked
    /// counts (§12.5): a method, or a field, property or event holding a
    /// delegate. A nested type or an `int` field of that name in a derived
    /// class hides nothing from `x.Name()`.
    pub(super) fn lookup_invocable_here(&self, ty: SymbolId, name: &str) -> Vec<SymbolId> {
        let found = self.binder.lookup_member_where(ty, name, &|member| {
            self.accessible(member) && self.invocable(member)
        });
        if found.is_empty() {
            self.unseen_removed(self.binder.lookup_member(ty, name))
        } else {
            found
        }
    }

    fn invocable(&self, member: SymbolId) -> bool {
        match self.binder.compilation().symbols().get(member).kind {
            SymbolKind::Method => true,
            SymbolKind::Field | SymbolKind::Property | SymbolKind::Event => {
                let mut sink = crate::Diagnostics::new();
                let ty = self.binder.type_of(member, &mut sink).value().clone();
                matches!(ty, Type::Dynamic | Type::Error) || self.is_delegate(&ty)
            }
            _ => false,
        }
    }

    /// The extension methods called `name` in scope here that this code may
    /// call: a private one in another static class is not a candidate.
    pub(super) fn extensions_here(&self, name: &str) -> Vec<SymbolId> {
        let mut found = self.binder.extensions_in_scope(&self.context, name);
        found.retain(|method| self.accessible(*method));
        found
    }

    /// CS0122: a member the code here may not name, where nothing else of
    /// that name up the hierarchy is one it may.
    pub(super) fn check_accessible(&mut self, member: SymbolId, name: &str, span: TextSpan) {
        let compilation = self.binder.compilation();
        let symbols = compilation.symbols();
        // A reference's member is accessible, but for an internal one of
        // an assembly that does not name this code's its friend.
        if (compilation.is_from_metadata(member) && compilation.sees(member, self.context.tree()))
            || !matches!(
                symbols.get(member).kind,
                SymbolKind::Field | SymbolKind::Property | SymbolKind::Method | SymbolKind::Event
            )
            || self.accessible(member)
        {
            return;
        }
        let Some(owner) = symbols.get(member).container else {
            return;
        };
        // An overload beside it that may be named is the one meant.
        if symbols
            .lookup(owner, name)
            .iter()
            .any(|other| self.accessible(*other))
        {
            return;
        }
        let mut current = self
            .binder
            .base_class_of(owner)
            .and_then(|base| base.symbol());
        let mut depth = 0;
        while let Some(ty) = current {
            if depth > 32
                || symbols
                    .lookup(ty, name)
                    .iter()
                    .any(|other| self.accessible(*other))
            {
                return;
            }
            current = self.binder.base_class_of(ty).and_then(|base| base.symbol());
            depth += 1;
        }
        let display = crate::checks::member_display(compilation, member, &Default::default(), None);
        self.report(ErrorCode::ErrBadAccess, span, &[&display]);
    }

    pub(super) fn report_object_required(&mut self, member: SymbolId, span: TextSpan) {
        let display = crate::checks::member_display(
            self.binder.compilation(),
            member,
            &Default::default(),
            None,
        );
        self.report(ErrorCode::ErrObjectRequired, span, &[&display]);
    }

    /// CS0120 and CS0176 for `left.Name`: an instance member reached through
    /// a type, or a static one through a value.
    ///
    /// `Color.Red`, where `Color` is both a property and its type, may do
    /// either (§12.8.7.2), so a name on the left that means both a type and
    /// a value is left alone.
    fn check_static_access(
        &mut self,
        found: SymbolId,
        receiver: &BoundExpression,
        right: &SyntaxNode,
    ) {
        let Some(access) = right
            .parent()
            .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
            .cloned()
        else {
            return;
        };
        let Some(left) = access.children().next() else {
            return;
        };
        let symbols = self.binder.compilation().symbols();
        let symbol = symbols.get(found);
        // An event read from metadata says whether it is static only on its
        // accessors, so events are left out.
        if !matches!(symbol.kind, SymbolKind::Field | SymbolKind::Property)
            || receiver.ty.is_error()
        {
            return;
        }
        let is_static = symbol.modifiers.contains(Modifiers::STATIC)
            || symbol.modifiers.contains(Modifiers::CONST);
        let wrong_side = match &receiver.kind {
            BoundExpressionKind::TypeExpression(_) => {
                !is_static && matches!(receiver.ty, Type::Named { .. })
            }
            BoundExpressionKind::Local(_)
            | BoundExpressionKind::Parameter(_)
            | BoundExpressionKind::This
            | BoundExpressionKind::Field { .. }
            | BoundExpressionKind::Property { .. }
            | BoundExpressionKind::Call { .. }
            | BoundExpressionKind::ObjectCreation { .. } => is_static,
            _ => false,
        };
        // Asked only once something is wrong: most accesses are fine, and
        // the question takes four lookups.
        if !wrong_side || self.means_a_value_and_a_type(&left) {
            return;
        }
        if is_static {
            let display = crate::checks::member_display(
                self.binder.compilation(),
                found,
                &Default::default(),
                None,
            );
            self.report(ErrorCode::ErrObjectProhibited, access.span(), &[&display]);
        } else {
            self.report_object_required(found, access.span());
        }
    }

    /// Whether a simple name means a value and a type at once, as `Color` in
    /// `Color.Red` does inside a type with a `Color Color` property.
    fn means_a_value_and_a_type(&self, left: &SyntaxNode) -> bool {
        left.kind() == SyntaxKind::IdentifierName
            && identifier_text(left).is_some_and(|name| {
                let value = self.lookup_local(&name).is_some()
                    || self
                        .member
                        .is_some_and(|member| self.lookup_parameter(member, &name).is_some())
                    || self.declaring_enclosing(&name).is_some();
                value
                    && self
                        .binder
                        .resolve_namespace_or_type(left, &self.context)
                        .is_some()
            })
    }

    pub(super) fn is_static(&self, symbol: SymbolId) -> bool {
        self.binder
            .compilation()
            .symbols()
            .get(symbol)
            .modifiers
            .contains(Modifiers::STATIC)
    }

    /// The enclosing type that declares `name`, innermost first.
    ///
    /// A type nested in another sees what the one around it declares, so the
    /// search does not stop at the innermost: `Parser` inside
    /// `DocumentationCommentId` writes `s_symbolListPool` and `EncodeName`
    /// with nothing in front of them, and both belong to the type it is
    /// nested in. Only the innermost one has a `this`, so anything found
    /// further out has to be reachable without one.
    pub(super) fn declaring_enclosing(&self, name: &str) -> Option<SymbolId> {
        let types = self.context.enclosing_types();
        for (depth, ty) in types.into_iter().enumerate() {
            let found = self.binder.lookup_member(ty, name);
            if found.is_empty() {
                continue;
            }
            if depth == 0
                || self.in_nameof
                || found.iter().any(|id| self.reachable_from_nested(*id))
            {
                return Some(ty);
            }
        }
        None
    }

    /// Whether a member of a type around this one can be named from inside it.
    ///
    /// The instance ones cannot: a nested type holds no reference to an
    /// instance of the type it is nested in, so there is no `this` for them
    /// to read. A `const` is static without saying so, and a nested type is
    /// not a member anything is read from at all.
    fn reachable_from_nested(&self, symbol: SymbolId) -> bool {
        let entry = self.binder.compilation().symbols().get(symbol);
        entry.kind == SymbolKind::NamedType
            || entry.modifiers.contains(Modifiers::STATIC)
            || entry.modifiers.contains(Modifiers::CONST)
    }

    /// The receiver a member of the enclosing type gets when none was written:
    /// `this` for an instance member, nothing for a static one.
    pub(super) fn implicit_receiver(
        &mut self,
        member: SymbolId,
        span: TextSpan,
    ) -> Option<Box<BoundExpression>> {
        if self.is_static(member) {
            // A static member of a generic type is a member of a
            // *construction* even when no receiver was written: inside
            // `Holder<T>` the `Count` you mean is `Holder<T>.Count`, and the
            // CLI has no way to name it without saying so.
            let symbols = self.binder.compilation().symbols();
            let container = symbols.get(member).container?;
            if symbols.get(container).kind != SymbolKind::NamedType
                || symbols
                    .get(container)
                    .as_named_type()
                    .is_none_or(|detail| detail.type_parameters.is_empty())
            {
                return None;
            }
            // Which construction, though, is the enclosing type's answer and
            // not the declaring type's. `Shared` written inside `Derived :
            // Base<string, int>` is `Base<string, int>.Shared`; naming it
            // `Base<T, U>.Shared` writes `!0` where `Derived` has no `!0`,
            // and the runtime refuses the whole body for it.
            //
            // Nor is the innermost type always the one that says: a class
            // nested in `Derived` reaches `Base<string, int>.Shared` through
            // `Derived`, not through anything it derives from itself.
            let mut enclosing = self.context.enclosing_type();
            let mut ty = None;
            while let Some(current) = enclosing {
                let from = self.binder.self_type(current);
                if let Some(found) = self.binder.constructed_from(&from, container) {
                    ty = Some(found);
                    break;
                }
                enclosing = symbols
                    .get(current)
                    .container
                    .filter(|outer| symbols.get(*outer).kind == SymbolKind::NamedType);
            }
            let ty = ty.unwrap_or_else(|| self.binder.self_type(container));
            return Some(Box::new(BoundExpression::new(
                BoundExpressionKind::TypeExpression(container),
                ty,
                span,
            )));
        }
        // An instance member reached without a receiver reads `this`, which a
        // lambda has to capture like anything else.
        self.note_this_capture();
        Some(Box::new(BoundExpression::new(
            BoundExpressionKind::This,
            self.this_type(),
            span,
        )))
    }

    /// The receiver of a static member, as the type it names.
    ///
    /// A static member is reached through a type and never through a value:
    /// keeping the value would leave one on the stack that nothing takes.
    fn as_type_where_static(
        &mut self,
        member: SymbolId,
        receiver: Box<BoundExpression>,
    ) -> Box<BoundExpression> {
        let symbols = self.binder.compilation().symbols();
        // A constant, an enum's member among them, is static without saying.
        let modifiers = symbols.get(member).modifiers;
        if !(modifiers.contains(Modifiers::STATIC) || modifiers.contains(Modifiers::CONST))
            || matches!(receiver.kind, BoundExpressionKind::TypeExpression(_))
        {
            return receiver;
        }
        match receiver.ty.symbol() {
            Some(symbol) => {
                let (ty, span) = (receiver.ty.clone(), receiver.span);
                // The name written means the type now, to an editor asking
                // too: `RenderType` of `RenderType.Custom` beside a
                // `RenderType` property is the enum.
                if let Some(BoundSymbol::Declared(named)) = self.body.references.get(&span).copied()
                    && symbols.get(named).name == symbols.get(symbol).name
                {
                    self.body
                        .references
                        .insert(span, BoundSymbol::Declared(symbol));
                }
                Box::new(BoundExpression::new(
                    BoundExpressionKind::TypeExpression(symbol),
                    ty,
                    span,
                ))
            }
            None => receiver,
        }
    }

    /// Builds the access to a member once it is known which one it is.
    /// The override `base.M` reaches.
    ///
    /// The lookup settles on the declaration that introduced a member, which
    /// is right for a dispatched call and wrong for one that is not: `base.
    /// MatchTypeToTypeId(...)` in a class whose base overrides an abstract
    /// method means the override, and calling the abstract one is not a
    /// program. The nearest override in the base's chain is the one.
    pub(super) fn base_override(&self, member: SymbolId, base: &Type) -> SymbolId {
        let symbols = self.binder.compilation().symbols();
        let symbol = symbols.get(member);
        let (name, kind) = (symbol.name.clone(), symbol.kind);
        if !matches!(kind, SymbolKind::Method | SymbolKind::Property) {
            return member;
        }
        let declared: Vec<Type> = symbol
            .as_method()
            .map(|detail| {
                detail
                    .parameters
                    .iter()
                    .map(|parameter| self.member_type(*parameter, base))
                    .collect()
            })
            .unwrap_or_default();
        let container = symbols.get(member).container;
        let mut current = base.symbol();
        for _ in 0..32 {
            let Some(ty) = current else {
                break;
            };
            if Some(ty) == container {
                break;
            }
            // An override's type parameters are its own: `M<T>(T x)` two
            // classes up takes the `T` of the method it overrides.
            let own = symbol
                .as_method()
                .map(|detail| detail.type_parameters.clone())
                .unwrap_or_default();
            let found =
                symbols.lookup(ty, &name).iter().copied().find(|candidate| {
                    let candidate_symbol = symbols.get(*candidate);
                    candidate_symbol.kind == kind
                        && candidate_symbol.modifiers.contains(Modifiers::OVERRIDE)
                        && candidate_symbol.as_method().is_none_or(|detail| {
                            let renamed: HashMap<SymbolId, Type> = detail
                                .type_parameters
                                .iter()
                                .zip(&own)
                                .map(|(theirs, ours)| (*theirs, Type::TypeParameter(*ours)))
                                .collect();
                            detail.type_parameters.len() == own.len()
                                && detail.parameters.len() == declared.len()
                                && detail.parameters.iter().zip(&declared).all(
                                    |(parameter, wanted)| {
                                        self.member_type(*parameter, base).substitute(&renamed)
                                            == *wanted
                                    },
                                )
                        })
                });
            if let Some(found) = found {
                return found;
            }
            current = self.binder.base_class_of(ty).and_then(|next| next.symbol());
        }
        member
    }

    pub(super) fn member_access(
        &mut self,
        member: SymbolId,
        receiver: Option<Box<BoundExpression>>,
        ty: Type,
        span: TextSpan,
    ) -> BoundExpression {
        // `CancellationToken.None` written where something of that type is in
        // scope under the same name: §12.8.7.2 says the two spellings name the
        // same thing, and a static member is reached through the type. What
        // was written stays, as the type it names — a static member of a
        // generic type still needs it to know which construction — but
        // nothing is evaluated for it.
        let receiver = receiver.map(|receiver| self.as_type_where_static(member, receiver));
        let member = match &receiver {
            Some(base) if matches!(base.kind, BoundExpressionKind::Base) => {
                self.base_override(member, &base.ty)
            }
            _ => member,
        };
        // Inside an enum's own initializers, its other members are values of
        // the underlying type (§19.4): `NullableReferenceType = ReferenceType
        // | 0x10` needs no cast, and folds to the number it is.
        if self.kind_of(member) == SymbolKind::Field
            && let Some(enumeration) = self.enclosing_enum_initializer()
            && self.binder.compilation().symbols().get(member).container == Some(enumeration)
            && let Some(underlying) = self.binder.enum_underlying(&ty)
        {
            let field = BoundExpression::new(
                BoundExpressionKind::Field {
                    receiver,
                    field: member,
                },
                ty,
                span,
            );
            return BoundExpression::new(
                BoundExpressionKind::Conversion {
                    operand: Box::new(field),
                    conversion: ConversionKind::Numeric,
                    written: false,
                },
                underlying,
                span,
            );
        }
        let kind = match self.kind_of(member) {
            // A field-like event is the delegate field it declares: read to
            // raise it, written to subscribe (§15.8.2).
            SymbolKind::Field | SymbolKind::Event => BoundExpressionKind::Field {
                receiver,
                field: member,
            },
            SymbolKind::Property => BoundExpressionKind::Property {
                receiver,
                property: member,
            },
            SymbolKind::NamedType => BoundExpressionKind::TypeExpression(member),
            SymbolKind::Namespace => BoundExpressionKind::NamespaceExpression(member),
            // A method name on its own is a method group, which is only a
            // value once it is converted to a delegate. It has no type until
            // then, because which overload it means depends on the delegate.
            SymbolKind::Method => {
                // A local function is never overloaded: another of its name
                // is in another block, and not part of the group.
                let local = self
                    .binder
                    .compilation()
                    .symbols()
                    .get(member)
                    .as_method()
                    .is_some_and(|detail| detail.method_kind == MethodKind::LocalFunction);
                let candidates = match self.compilation_member_group(member) {
                    _ if local => vec![member],
                    candidates if candidates.is_empty() => vec![member],
                    candidates => candidates,
                };
                return BoundExpression::new(
                    BoundExpressionKind::MethodGroup {
                        receiver,
                        candidates,
                    },
                    Type::Error,
                    span,
                );
            }
            _ => BoundExpressionKind::Unsupported(SyntaxKind::IdentifierName),
        };
        // `fixed int x[10]` read anywhere is a pointer to its first element
        // (§24.8.3): the field's own type is the element's.
        if let BoundExpressionKind::Field { field, .. } = &kind
            && self
                .binder
                .compilation()
                .symbols()
                .get(*field)
                .modifiers
                .contains(Modifiers::FIXED)
        {
            let pointer = Type::Pointer(Box::new(ty.clone()));
            let buffer = BoundExpression::new(kind, ty, span);
            return BoundExpression::new(
                BoundExpressionKind::AddressOf {
                    operand: Box::new(buffer),
                },
                pointer,
                span,
            );
        }
        BoundExpression::new(kind, ty, span)
    }

    /// The enum whose member initializer is being bound, if that is what
    /// this body is.
    fn enclosing_enum_initializer(&self) -> Option<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let member = self.member?;
        if symbols.get(member).kind != SymbolKind::Field {
            return None;
        }
        let container = symbols.get(member).container?;
        (symbols.get(container).type_kind() == Some(TypeKind::Enum)).then_some(container)
    }

    /// Every method of the same name on the same type, which is what a method
    /// group holds until a delegate picks one.
    fn compilation_member_group(&self, member: SymbolId) -> Vec<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let Some(container) = symbols.get(member).container else {
            return Vec::new();
        };
        let name = symbols.get(member).name.clone();
        self.binder
            .lookup_member(container, &name)
            .into_iter()
            .filter(|candidate| symbols.get(*candidate).kind == SymbolKind::Method)
            .collect()
    }

    /// A bare name: a local, a parameter, a member of the enclosing type, or a
    /// type.
    pub(super) fn bind_name(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let Some(name) = identifier_text(node) else {
            return BoundExpression::error(span);
        };

        // `field` in an accessor is the property's backing field (C# 14),
        // whatever else is called `field`: a member of that name is
        // `this.field` or `@field` from then on. Before C# 14 it is an
        // ordinary name.
        if name == "field"
            && !node.text().trim_start().starts_with('@')
            && self.language_version().at_least(LanguageVersion::CSharp14)
            && let Some(field) = self.backing_field_in_scope()
        {
            self.body
                .references
                .insert(span, BoundSymbol::Declared(field));
            let mut sink = Diagnostics::new();
            let ty = self.binder.type_of(field, &mut sink);
            let receiver = self.implicit_receiver(field, span);
            return self.member_access(field, receiver, ty, span);
        }

        // A local function's own parameter hides a local of the method around
        // it: `binary` inside `visit(BoundBinaryOperator binary)` is the
        // parameter, whatever the method holding it declared under that name.
        // A `const` local is its value wherever it is named: nothing is read,
        // so nothing is captured.
        if let Some((_, local)) = self.lookup_local_at(&name)
            && let Some(constant) = self.constant_locals.get(&local).cloned()
        {
            self.refer_to_local(span, local);
            return BoundExpression::new(
                BoundExpressionKind::Literal(constant),
                self.local_type(local),
                span,
            );
        }
        if !self.hidden_by_own_parameter(&name)
            && let Some(local) = self.resolve_local(&name)
        {
            self.refer_to_local(span, local);
            // `M(out var x, x)`: the type of `x` comes from the overload the
            // call picks, which the arguments decide, so none of them may
            // read it (CS8196).
            if self
                .body
                .locals
                .get(local.0 as usize)
                .is_some_and(|symbol| in_out_var_zone(node, symbol.span))
            {
                self.report(
                    ErrorCode::ErrImplicitlyTypedVariableUsedInForbiddenZone,
                    span,
                    &[&name],
                );
                return BoundExpression::error(span);
            }
            return BoundExpression::new(
                BoundExpressionKind::Local(local),
                self.local_type(local),
                span,
            );
        }

        if let Some(member) = self.member
            && !self.in_attribute
            && let Some(parameter) = self.lookup_parameter(member, &name)
        {
            // A primary constructor's parameter read from a method is the
            // field the constructor kept it in: the parameter is gone by
            // the time the method runs.
            let symbols = self.binder.compilation().symbols();
            let captured = symbols
                .get(parameter)
                .as_parameter()
                .and_then(|detail| detail.captured)
                .filter(|_| {
                    // A lambda in an initializer outlives the constructor
                    // too, and reads the field as a method would.
                    // So does one among the base constructor's arguments:
                    // the field is filled before the base is called.
                    // An initializer reads and writes the field as well:
                    // it is filled before any initializer runs.
                    symbols.get(parameter).container != Some(member) || !self.lambdas.is_empty()
                });
            if let Some(field) = captured {
                self.body
                    .references
                    .insert(span, BoundSymbol::Declared(parameter));
                let receiver = self.implicit_receiver(field, span);
                let mut sink = Diagnostics::new();
                let ty = self.binder.type_of(field, &mut sink);
                return BoundExpression::new(
                    BoundExpressionKind::Field { receiver, field },
                    ty,
                    span,
                );
            }
            self.note_parameter_capture(parameter);
            self.body
                .references
                .insert(span, BoundSymbol::Declared(parameter));
            let mut sink = Diagnostics::new();
            let ty = self.binder.type_of(parameter, &mut sink);
            return BoundExpression::new(BoundExpressionKind::Parameter(parameter), ty, span);
        }

        // A local function is a name in its own right, and one a method group
        // can be made of: Roslyn's parser hands `skipBadAttributeListTokens`
        // to a helper a good way above where it is declared.
        if let Some(found) = self.local_function(&name, span) {
            self.note_local_function_call(found);
            self.body
                .references
                .insert(span, BoundSymbol::Declared(found));
            let mut sink = Diagnostics::new();
            let ty = self.binder.type_of(found, &mut sink);
            return self.member_access(found, None, ty, span);
        }

        // A nested type that a type around this one declares is a name too,
        // but it is not read like a member: `Collection<TKey>` is a
        // *construction*, and taking it as a member here would lose the
        // `TKey`. The type path below knows how to keep it.
        if let Some(enclosing) = self.declaring_enclosing(&name)
            && let Some(found) = self.binder.lookup_member(enclosing, &name).first().copied()
            && self.kind_of(found) != SymbolKind::NamedType
        {
            self.body
                .references
                .insert(span, BoundSymbol::Declared(found));
            // The member may be inherited from a construction: inside an
            // `Embedded : Manager.CommonEmbedded`, the `Underlying` written
            // with no receiver is a `NamedTypeSymbolAdapter` and not the
            // `TSymbol` its declaration says.
            let receiver_type = self.binder.self_type(enclosing);
            let ty = self.member_type(found, &receiver_type);
            // A method group may hold a static overload the conversion
            // picks; only a field or property is blamed here.
            if self.kind_of(found) != SymbolKind::Method
                && self.needs_this(found)
                && self.static_context()
                && self
                    .binder
                    .resolve_namespace_or_type(node, &self.context)
                    .is_none()
            {
                self.report_object_required(found, span);
            }
            self.check_accessible(found, &name, span);
            let receiver = self.implicit_receiver(found, span);
            return self.member_access(found, receiver, ty, span);
        }

        // `using static Math;` makes `Abs` a name in its own right.
        if let Some(found) = self.binder.static_import(&self.context, &name) {
            self.body
                .references
                .insert(span, BoundSymbol::Declared(found));
            let mut sink = Diagnostics::new();
            let ty = self.binder.type_of(found, &mut sink);
            return self.member_access(found, None, ty, span);
        }

        // `using Aliases = ArrayBuilder<(string, string)>;` makes `Aliases`
        // a name for a *construction*, and `Aliases.GetInstance()` returns
        // one of those rather than an `ArrayBuilder<T>`: the alias is
        // resolved as the type it spells, arguments and all.
        if node.kind() == SyntaxKind::IdentifierName
            && let Some(Resolution::AliasTo(target)) =
                self.binder.lookup_resolution(&name, 0, &self.context)
            && names_a_construction(&target)
        {
            let alias_context = self.binder.alias_context(&name, &self.context);
            let mut sink = Diagnostics::new();
            let ty = self
                .binder
                .resolve_type(&target, &alias_context, &mut sink)
                .value()
                .clone();
            if let Some(symbol) = ty.symbol() {
                self.body
                    .references
                    .insert(span, BoundSymbol::Declared(symbol));
                return BoundExpression::new(BoundExpressionKind::TypeExpression(symbol), ty, span);
            }
        }

        // A type name is a legitimate answer: `Console` in `Console.Write`.
        if let Some(symbol) = self.binder.resolve_namespace_or_type(node, &self.context) {
            self.body
                .references
                .insert(span, BoundSymbol::Declared(symbol));
            if let Some(ambiguous) = self.binder.same_type_elsewhere(symbol, node, self.tree) {
                self.body.diagnostics.push((self.tree, ambiguous));
                return BoundExpression::error(span);
            }
            return match self.kind_of(symbol) {
                // `ImmutableArray<Symbol>.Empty` reaches a static member
                // *through a construction*, and the construction is what says
                // what `Empty` holds. Resolving the name as a type rather than
                // as a symbol is what keeps it.
                // So does the construction a base type was named with:
                // `E.A` in a class deriving from `B<int>` is a member of
                // `B<int>.E`, which the type resolver knows and the
                // arguments written after the name do not say.
                SymbolKind::NamedType => {
                    let resolved = self.resolve(node);
                    let ty = if resolved.symbol() == Some(symbol) {
                        resolved
                    } else {
                        self.constructed(symbol, node)
                    };
                    BoundExpression::new(BoundExpressionKind::TypeExpression(symbol), ty, span)
                }
                SymbolKind::Namespace => BoundExpression::new(
                    BoundExpressionKind::NamespaceExpression(symbol),
                    Type::Error,
                    span,
                ),
                // `T.Zero` where `T : INumberBase<T>` reaches a static
                // abstract member through the type parameter (§12.8.7.2).
                SymbolKind::TypeParameter => BoundExpression::new(
                    BoundExpressionKind::TypeExpression(symbol),
                    Type::TypeParameter(symbol),
                    span,
                ),
                _ => BoundExpression::error(span),
            };
        }

        // A name the parser made up where one was missing has been
        // complained about as a syntax error already.
        if !span.is_empty() {
            let code = if declared_further_on(node, &name) {
                ErrorCode::ErrVariableUsedBeforeDeclaration
            } else {
                ErrorCode::ErrNameNotInContext
            };
            self.report(code, span, &[&name]);
        }
        BoundExpression::error(span)
    }

    /// `left.Name`, where `left` may be a value or a type.
    /// A named type as the name wrote it, type arguments and all.
    ///
    /// `ImmutableArray<Symbol>.Empty` reaches a static member *through a
    /// construction*, and the construction is what says what `Empty` holds.
    /// Dropping it — which is what naming the symbol alone does — leaves every
    /// such member with its declared `T` instead of the type given for it.
    fn constructed(&mut self, symbol: SymbolId, name: &SyntaxNode) -> Type {
        let arguments: Vec<Type> = name
            .child_of_kind(SyntaxKind::TypeArgumentList)
            .map(|list| {
                list.children()
                    .filter(|child| child.kind().is_type_node())
                    .map(|argument| self.resolve(&argument))
                    .collect()
            })
            .unwrap_or_default();
        Type::Named {
            symbol,
            type_arguments: arguments,
        }
    }

    pub(super) fn bind_member_access(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let mut children = node.children();
        let (Some(left), Some(right)) = (children.next(), children.next()) else {
            return BoundExpression::error(span);
        };
        let Some(name) = identifier_text(&right) else {
            return BoundExpression::error(span);
        };

        // A namespace on the left is not a value, so it is looked through
        // rather than bound.
        if let Some(namespace) = self.namespace_of(&left) {
            return self.in_namespace(namespace, &right, &name, span);
        }

        // `NullableAnnotation.Oblivious` where `NullableAnnotation` is both
        // a property and the type it is of: binding the left reads the
        // property off `this`, which the lambdas around it note as a
        // capture, and then §12.8.7.2 settles on the type, which reads
        // nothing. What was noted for a receiver that went away is undone.
        let noted: Vec<bool> = self
            .lambdas
            .iter()
            .map(|frame| frame.captures_this)
            .collect();
        let receiver = self.bind_expression(&left);
        let receiver = if node.kind() == SyntaxKind::PointerMemberAccessExpression {
            self.pointed_at(receiver)
        } else {
            receiver
        };
        let was_value = !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_));
        let receiver_type = receiver.ty.symbol();
        let bound = self.member_on(receiver, &right, &name, span);
        if was_value && receiver_is_a_type(&bound) && noted.len() == self.lambdas.len() {
            for (frame, before) in self.lambdas.iter_mut().zip(noted) {
                frame.captures_this = before;
            }
        }
        // `RenderType.Custom` beside a `RenderType` property reads a static
        // member, a constant or an enum's member, through the type: the name
        // on the left is the type, to an editor asking too.
        let symbols = self.binder.compilation().symbols();
        let member = right
            .first_token()
            .and_then(|token| self.body.symbol_at(token.span()));
        if !bound.ty.is_error()
            && let Some(ty) = receiver_type
            && let Some(BoundSymbol::Declared(member)) = member
            && symbols.get(member).name == name
            && (symbols.get(member).modifiers.contains(Modifiers::STATIC)
                || symbols.get(member).modifiers.contains(Modifiers::CONST)
                || symbols.get(member).container == Some(ty)
                    && symbols.get(ty).type_kind() == Some(TypeKind::Enum))
            && let Some(named) = self
                .body
                .symbol_at(left.span())
                .and_then(|found| match found {
                    BoundSymbol::Declared(named) => Some(named),
                    BoundSymbol::Local(_) => None,
                })
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
        bound
    }

    /// What a namespace calls `name`: a type, or a namespace further in.
    fn in_namespace(
        &mut self,
        namespace: SymbolId,
        right: &SyntaxNode,
        name: &str,
        span: TextSpan,
    ) -> BoundExpression {
        let symbols = self.binder.compilation().symbols();
        // `ImmutableArray` and `ImmutableArray<T>` are two types with one
        // name, and the `<int>` after it is what says which:
        // `System.Collections.Immutable.ImmutableArray<int>.Empty` means the
        // generic one, and the static class beside it has no `Empty`.
        let arity = right
            .child_of_kind(SyntaxKind::TypeArgumentList)
            .map_or(0, |list| {
                list.children()
                    .filter(|child| child.kind().is_type_node())
                    .count()
            });
        // A reference's internal type is no candidate for code of an
        // assembly it is not a friend of.
        let compilation = self.binder.compilation();
        let tree = self.context.tree();
        let mut candidates: Vec<SymbolId> = symbols
            .lookup(namespace, name)
            .iter()
            .copied()
            .filter(|id| compilation.sees(*id, tree))
            .collect();
        // Of two references' types of one name, the one of a reference the
        // code's assembly has.
        candidates.sort_by_key(|id| compilation.references_assembly_of(*id, tree) == Some(false));
        let found = candidates
            .iter()
            .copied()
            .find(|id| {
                symbols
                    .get(*id)
                    .as_named_type()
                    .is_some_and(|detail| detail.arity == arity)
            })
            .or_else(|| candidates.first().copied());
        let Some(found) = found else {
            // `System.Nonesuch` is a name missing from a namespace, which
            // Roslyn words as a type or namespace that does not exist in it.
            let container = symbols.qualified_name(namespace);
            self.report(
                ErrorCode::ErrDottedTypeNameNotFoundInNS,
                right.span(),
                &[name, &container],
            );
            return BoundExpression::error(span);
        };
        self.body
            .references
            .insert(right.span(), BoundSymbol::Declared(found));
        if let Some(ambiguous) = self.binder.same_type_elsewhere(found, right, self.tree) {
            self.body.diagnostics.push((self.tree, ambiguous));
            return BoundExpression::error(span);
        }
        match self.kind_of(found) {
            SymbolKind::NamedType => BoundExpression::new(
                BoundExpressionKind::TypeExpression(found),
                self.constructed(found, right),
                span,
            ),
            SymbolKind::Namespace => BoundExpression::new(
                BoundExpressionKind::NamespaceExpression(found),
                Type::Error,
                span,
            ),
            _ => BoundExpression::error(span),
        }
    }

    /// `a?.B`, which is `B` of `a` unless `a` is null.
    ///
    /// The receiver is evaluated once — that is the whole reason `?.` exists
    /// rather than `a == null ? null : a.B` — so the access inside is written
    /// against a placeholder that stands for it.
    pub(super) fn bind_conditional_access(&mut self, node: &SyntaxNode) -> BoundExpression {
        let span = node.span();
        let mut children = node.children();
        let (Some(left), Some(right)) = (children.next(), children.next()) else {
            return BoundExpression::error(span);
        };
        let receiver = self.bind_expression(&left);
        // What is accessed is the receiver without its null: for an `int?`
        // that is the `int` underneath.
        let ty = self
            .binder
            .nullable_underlying(&receiver.ty)
            .unwrap_or_else(|| receiver.ty.clone());
        self.accessed.push(ty);
        let access = self.bind_expression(&right);
        self.accessed.pop();
        // `builder?.ToImmutable()` is an `ImmutableArray<T>?` and not an
        // `ImmutableArray<T>`: §12.8.8 gives the whole expression a null to
        // hand back when the receiver is one, and a struct has no null of its
        // own to be. Leaving it unwrapped makes `?? Empty` test a struct for
        // null, which is not a program at all.
        let result = access.ty.clone();
        // The result has to be a reference, a pointer (null is its zero) or
        // a `T?`. Where the access gives none of those — a type parameter
        // that may be either, a `ref struct` no `Nullable<T>` can hold —
        // there is no value to hand back, and the expression is `void`:
        // allowed where nothing reads it, CS8978 where something would.
        let result = if self.cannot_be_made_nullable(&result) {
            if self.conditional_result_used(node) {
                let symbols = self.binder.compilation().symbols();
                let display = result.display(symbols);
                self.report(ErrorCode::ErrCannotBeMadeNullable, access.span, &[&display]);
                return BoundExpression::error(span);
            }
            Type::Void
        } else if self.wraps_in_nullable(&result) {
            self.nullable_of(result)
        } else {
            result
        };
        BoundExpression::new(
            BoundExpressionKind::ConditionalAccess {
                receiver: Box::new(receiver),
                access: Box::new(access),
            },
            result,
            span,
        )
    }

    fn cannot_be_made_nullable(&self, ty: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        match ty {
            Type::TypeParameter(parameter) => {
                !symbols
                    .get(*parameter)
                    .as_type_parameter()
                    .is_some_and(|detail| detail.value_type)
                    && !self.binder.is_reference_type_parameter(*parameter)
            }
            Type::Named { symbol, .. } => symbols
                .get(*symbol)
                .as_named_type()
                .is_some_and(|detail| detail.ref_like),
            _ => false,
        }
    }

    /// Whether what a `?.` gives is read: not where it is a statement of its
    /// own, the body of a lambda or member returning nothing, or a `for`
    /// loop's step.
    fn conditional_result_used(&self, node: &SyntaxNode) -> bool {
        let Some(parent) = node.parent() else {
            return true;
        };
        let is_body = parent.children().last().is_some_and(|last| last == *node);
        match parent.kind() {
            SyntaxKind::ExpressionStatement => false,
            SyntaxKind::SimpleLambdaExpression | SyntaxKind::ParenthesizedLambdaExpression => {
                !is_body
                    || self
                        .lambdas
                        .last()
                        .is_none_or(|frame| !matches!(frame.return_type, Type::Void))
            }
            SyntaxKind::ArrowExpressionClause
                if parent
                    .parent()
                    .is_some_and(|owner| owner.kind() == SyntaxKind::LocalFunctionStatement) =>
            {
                self.lambdas
                    .last()
                    .is_none_or(|frame| !matches!(frame.return_type, Type::Void))
            }
            SyntaxKind::ArrowExpressionClause => {
                // An `async` member returning a `Task` returns nothing either.
                let returns_nothing = self.member.is_some_and(|member| {
                    let mut sink = crate::Diagnostics::new();
                    let returns = self.binder.type_of(member, &mut sink).value().clone();
                    matches!(returns, Type::Void)
                        || (self.is_async(member)
                            && returns.symbol().is_some_and(|symbol| {
                                self.binder.compilation().symbols().qualified_name(symbol)
                                    == "System.Threading.Tasks.Task"
                            }))
                });
                !returns_nothing
            }
            // Neither the initializers nor the incrementors of a `for` give
            // a value; the condition, between the two `;`, does.
            SyntaxKind::ForStatement => {
                let semicolons = parent
                    .child_tokens()
                    .filter(|token| {
                        token.kind() == SyntaxKind::SemicolonToken
                            && token.span().end() <= node.span().start()
                    })
                    .count();
                semicolons == 1
            }
            _ => true,
        }
    }

    /// The receiver of the `?.` being bound.
    pub(super) fn accessed_value(&self, span: TextSpan) -> BoundExpression {
        BoundExpression::new(
            BoundExpressionKind::AccessedValue,
            self.accessed.last().cloned().unwrap_or(Type::Error),
            span,
        )
    }

    /// The member `name` of an already-bound receiver.
    ///
    /// Split out because `a.B` and `a?.B` differ only in what the receiver is:
    /// one is the value, the other the value once it is known not to be null.
    pub(super) fn member_on(
        &mut self,
        mut receiver: BoundExpression,
        right: &SyntaxNode,
        name: &str,
        span: TextSpan,
    ) -> BoundExpression {
        // A namespace is not a value and has no type; what it has is members.
        // `System.Text.Encoding` reaches one that way — `System.Text` is a
        // namespace nothing can be read from, and `Encoding` is looked up
        // inside it rather than on it.
        if let BoundExpressionKind::NamespaceExpression(namespace) = receiver.kind {
            return self.in_namespace(namespace, right, name, span);
        }
        // A member of a `dynamic` value is found when the program runs.
        if matches!(receiver.ty, Type::Dynamic) {
            return Self::dynamic_member(receiver, name, span);
        }
        if receiver.ty.is_error()
            && !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_))
        {
            // `array.Length` has no synthesised array type to look up on, so
            // it is answered from the array type itself.
            if let Type::Array { .. } = receiver.ty {
                return BoundExpression::error(span);
            }
            return BoundExpression::error(span);
        }
        if let Type::Array { .. } = receiver.ty {
            if name == "Length" {
                return BoundExpression::new(
                    BoundExpressionKind::ArrayLength {
                        array: Box::new(receiver),
                    },
                    self.special(SpecialType::Int32),
                    span,
                );
            }
            // Everything else an array has, it has from `System.Array` — or
            // from an extension method: `items.Cast<string>()` is a method
            // group over the array, closed for the call to resolve.
            let Some(array) = self.as_system_array(&receiver, name) else {
                let extensions = self.extensions_here(name);
                if !extensions.is_empty() {
                    return BoundExpression::new(
                        BoundExpressionKind::MethodGroup {
                            receiver: Some(Box::new(receiver)),
                            candidates: extensions,
                        },
                        Type::Error,
                        span,
                    );
                }
                return BoundExpression::error(span);
            };
            receiver = BoundExpression::new(receiver.kind, array, receiver.span);
        }

        // A tuple is a `ValueTuple<...>` wearing better names: `pair.Item1` is
        // its first field, and `pair.count` is too where an element was named
        // that. The names are the language's alone — the runtime has only the
        // fields.
        let receiver = match &receiver.ty {
            Type::Tuple(elements) => {
                let at = elements
                    .iter()
                    .position(|element| element.name.as_deref() == Some(name));
                let field = at.map_or_else(|| name.to_string(), |at| format!("Item{}", at + 1));
                let ty = self.tuple_as_named(elements);
                let receiver = BoundExpression::new(receiver.kind, ty, receiver.span);
                return self.member_on(receiver, right, &field, span);
            }
            _ => receiver,
        };
        // `t.Item9` on a `ValueTuple<…, ValueTuple<…>>` is `t.Rest.Item2`:
        // the eighth element and on live in the nested tuple.
        if let Some(number) = name
            .strip_prefix("Item")
            .and_then(|rest| rest.parse::<usize>().ok())
            && number > 7
            && receiver.ty.symbol().is_some_and(|symbol| {
                let symbols = self.binder.compilation().symbols();
                symbols.get(symbol).name == "ValueTuple"
                    && symbols
                        .get(symbol)
                        .as_named_type()
                        .is_some_and(|detail| detail.arity == 8)
            })
        {
            let rest = self.member_on(receiver, right, "Rest", span);
            if rest.ty.is_error() {
                return rest;
            }
            return self.member_on(rest, right, &format!("Item{}", number - 7), span);
        }

        let Some(symbol) = receiver.ty.symbol() else {
            return BoundExpression::error(span);
        };

        // `Empty.Enumerator<T>` names the nested type of that arity, not the
        // `Enumerator` beside it.
        let arity = right
            .child_of_kind(SyntaxKind::TypeArgumentList)
            .map_or(0, |list| {
                list.children()
                    .filter(|child| child.kind().is_type_node())
                    .count()
            });
        let members = self.lookup_member_here(symbol, name);
        // A nested type hides only one of its own arity: `Derived2.Type<int>`
        // is the `Base2.Type<T>` it inherits beside its own `Type<T, U>`.
        let found = if arity > 0 {
            members
                .iter()
                .copied()
                .find(|id| {
                    self.binder
                        .compilation()
                        .symbols()
                        .get(*id)
                        .as_named_type()
                        .is_some_and(|detail| detail.arity == arity)
                })
                .or_else(|| self.binder.lookup_type_in_hierarchy(symbol, name, arity, 0))
        } else {
            None
        }
        .or_else(|| members.first().copied());
        // Methods a value cannot be called on — static ones, or ones it may
        // not reach from here — are no candidates for `value.M`, and when
        // nothing else of the name is, extension methods are looked for.
        let value_receiver = !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_));
        // `Color.M` where `Color` is a variable and its type both reaches the
        // static `M` as well (§12.8.7.2).
        let color_color = value_receiver
            && right
                .parent()
                .filter(|access| access.kind() == SyntaxKind::SimpleMemberAccessExpression)
                .and_then(|access| access.children().next())
                .is_some_and(|left| self.means_a_value_and_a_type(&left));
        let found = found.filter(|found| {
            !value_receiver
                || color_color
                || self.kind_of(*found) != SymbolKind::Method
                || members.iter().any(|member| {
                    self.kind_of(*member) != SymbolKind::Method
                        || (!self.is_static(*member) && self.accessible(*member))
                })
        });
        let Some(found) = found else {
            // A member of an extension block (C# 14): an instance property
            // of what the receiver is, or a static member of the type named.
            // An extension method for this receiver found by the same
            // name is reached first, as a group closed over the receiver.
            let methods_first = !matches!(receiver.kind, BoundExpressionKind::TypeExpression(_))
                && self
                    .binder
                    .extensions_in_scope(&self.context, name)
                    .into_iter()
                    .any(|method| self.extension_takes(method, &receiver.ty));
            if !methods_first
                && let Some(access) = self.extension_member_access(&receiver, name, span)
            {
                self.body
                    .references
                    .insert(right.span(), BoundSymbol::Declared(access.1));
                return access.0;
            }
            // An extension block's property (C# 14) is read through a
            // `get_Name(receiver)` the block declared as an extension method.
            if let Some(read) = self.bind_extension_call(
                &format!("get_{name}"),
                right,
                receiver.clone(),
                &[],
                &[],
                span,
            ) {
                return read;
            }
            // `types.All(symbol.IsContainingSymbolOfAllTypeParameters)` names
            // an extension method without calling it: a method group closed
            // over the receiver, which a delegate is made from.
            let extensions = self.extensions_here(name);
            if !extensions.is_empty() {
                return BoundExpression::new(
                    BoundExpressionKind::MethodGroup {
                        receiver: Some(Box::new(receiver)),
                        candidates: extensions,
                    },
                    Type::Error,
                    span,
                );
            }
            let container = self.display(&receiver.ty);
            let code = missing_member_code(&receiver);
            self.report(code, right.span(), &[&container, name]);
            return BoundExpression::error(span);
        };
        self.body
            .references
            .insert(right.span(), BoundSymbol::Declared(found));
        self.check_static_access(found, &receiver, right);
        self.check_accessible(found, name, right.span());
        let ty = if self.kind_of(found) == SymbolKind::NamedType {
            self.nested_construction(found, &receiver.ty, right)
        } else {
            self.member_type(found, &receiver.ty)
        };

        // `C.Field` names a static member: there is no value to pass on. A
        // *construction* is kept all the same — `Holder<int>.Count` is a
        // member of a construction, and nothing but the receiver says which.
        // So is a name that reaches a member through a generic base:
        // `MetadataDecoder.GetSignatureCountsOrThrow` is a member of
        // `MetadataDecoder<PEModuleSymbol, ...>`, and only the name knows
        // which construction that is.
        let receiver = match &receiver.kind {
            BoundExpressionKind::TypeExpression(_)
                if !is_constructed(&receiver.ty)
                    && !self.inherited_from_generic(found, &receiver.ty) =>
            {
                None
            }
            _ => Some(Box::new(receiver)),
        };
        let access = self.member_access(found, receiver, ty, span);
        // `value.M` names the extension methods of that name as well as the
        // instance ones, which a conversion to a delegate and a natural
        // type turn to where no instance method serves (§12.8.10.3).
        if let BoundExpressionKind::MethodGroup {
            receiver,
            mut candidates,
        } = access.kind
        {
            if value_receiver && receiver.is_some() {
                for extension in self.extensions_here(name) {
                    if !candidates.contains(&extension) {
                        candidates.push(extension);
                    }
                }
            }
            return BoundExpression::new(
                BoundExpressionKind::MethodGroup {
                    receiver,
                    candidates,
                },
                access.ty,
                access.span,
            );
        }
        access
    }

    /// Whether a member reached through a type belongs to a generic type
    /// other than the one named, which is then some construction of it.
    pub(super) fn inherited_from_generic(&self, member: SymbolId, through: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        let mut container = symbols.get(member).container;
        while let Some(id) = container {
            if symbols.get(id).kind == SymbolKind::NamedType {
                break;
            }
            container = symbols.get(id).container;
        }
        let Some(container) = container else {
            return false;
        };
        through.symbol() != Some(container)
            && symbols
                .get(container)
                .as_named_type()
                .is_some_and(|detail| !detail.type_parameters.is_empty())
    }

    /// A type nested in a construction, as a construction of its own.
    ///
    /// A nested type's parameters are the ones of the type around it followed
    /// by its own, so `Dict<TKey, TValue>.PrivateMarshal` is a construction
    /// with two arguments although nothing after its name says so — they are
    /// spelled to the left of the dot, and without them its members are
    /// written in terms of a `TKey` that belongs to the declaration rather
    /// than to this use of it.
    fn nested_construction(&mut self, found: SymbolId, outer: &Type, right: &SyntaxNode) -> Type {
        let own = match self.constructed(found, right) {
            Type::Named { type_arguments, .. } => type_arguments,
            other => return other,
        };
        let declared = self
            .binder
            .compilation()
            .symbols()
            .get(found)
            .as_named_type()
            .map_or(0, |detail| detail.type_parameters.len());
        if own.len() == declared {
            return Type::Named {
                symbol: found,
                type_arguments: own,
            };
        }
        let Type::Named { type_arguments, .. } = outer else {
            return Type::named(found);
        };
        let mut all = type_arguments.clone();
        all.extend(own);
        if all.len() == declared {
            return Type::Named {
                symbol: found,
                type_arguments: all,
            };
        }
        Type::named(found)
    }

    /// The namespace a name denotes, if it denotes one.
    pub(super) fn namespace_of(&self, node: &SyntaxNode) -> Option<SymbolId> {
        if !matches!(
            node.kind(),
            SyntaxKind::IdentifierName
                | SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::AliasQualifiedName
        ) {
            return None;
        }
        // A local, a parameter or a member of the same name shadows the
        // namespace: `Syntax.Identifier` inside a `LocalFunctionSymbol` reads
        // its own `Syntax` property, not the `Microsoft.CodeAnalysis.CSharp.Syntax`
        // the file is written in; `src.Length` reads the parameter `src`
        // whatever assembly declares a namespace `src`.
        if let Some(name) = identifier_text(node)
            && (self.lookup_local(&name).is_some()
                || self
                    .member
                    .is_some_and(|member| self.lookup_parameter(member, &name).is_some())
                || self.declaring_enclosing(&name).is_some())
        {
            return None;
        }
        let symbol = self
            .binder
            .resolve_namespace_or_type(&as_name_syntax(node)?, &self.context)?;
        (self.binder.compilation().symbols().get(symbol).kind == SymbolKind::Namespace)
            .then_some(symbol)
    }

    /// `x.P` or `C.P` reaching a property an extension block (C# 14)
    /// declared, or `C.M` a static method of one: the access, and what it
    /// reached. An instance property takes the receiver as its first
    /// parameter, which the receiver has to convert to.
    pub(super) fn extension_member_access(
        &mut self,
        receiver: &BoundExpression,
        name: &str,
        span: TextSpan,
    ) -> Option<(BoundExpression, SymbolId)> {
        let candidates = self.binder.extension_members_in_scope(&self.context, name);
        if candidates.is_empty() {
            return None;
        }
        let on_type = matches!(receiver.kind, BoundExpressionKind::TypeExpression(_));
        let symbols = self.binder.compilation().symbols();
        let mut statics = Vec::new();
        for candidate in candidates {
            let symbol = symbols.get(candidate);
            match &symbol.detail {
                Detail::Property(detail) if !detail.is_indexer => {
                    let extended = detail.extended?;
                    let mut inferred = HashMap::new();
                    let fits = if on_type {
                        detail.parameters.is_empty()
                            && self.static_extension_fits(extended, &receiver.ty)
                    } else {
                        detail.parameters.first().is_some_and(|parameter| {
                            self.receiver_fits(
                                *parameter,
                                &receiver.ty,
                                &detail.extension_generics,
                                &mut inferred,
                            )
                        })
                    };
                    if fits {
                        let mut sink = Diagnostics::new();
                        let ty = self
                            .binder
                            .type_of(candidate, &mut sink)
                            .substitute(&inferred);
                        let access = BoundExpression::new(
                            BoundExpressionKind::Property {
                                receiver: (!on_type).then(|| Box::new(receiver.clone())),
                                property: candidate,
                            },
                            ty,
                            span,
                        );
                        return Some((access, candidate));
                    }
                }
                Detail::Method(detail) if on_type => {
                    let Some(extended) = detail.extended else {
                        continue;
                    };
                    if self.static_extension_fits(extended, &receiver.ty) {
                        statics.push(candidate);
                    }
                }
                _ => {}
            }
        }
        let first = *statics.first()?;
        Some((
            BoundExpression::new(
                BoundExpressionKind::MethodGroup {
                    receiver: Some(Box::new(receiver.clone())),
                    candidates: statics,
                },
                Type::Error,
                span,
            ),
            first,
        ))
    }

    /// Whether a receiver of this type is what an extension block's
    /// receiver parameter takes, inferring the block's type parameters from
    /// it where it has any.
    fn receiver_fits(
        &self,
        parameter: SymbolId,
        receiver: &Type,
        generics: &[SymbolId],
        inferred: &mut HashMap<SymbolId, Type>,
    ) -> bool {
        let mut sink = Diagnostics::new();
        let taken = self.binder.type_of(parameter, &mut sink);
        if !generics.is_empty() {
            self.infer_into(&taken, receiver, generics, inferred);
            if !generics
                .iter()
                .all(|generic| inferred.contains_key(generic))
            {
                return false;
            }
        }
        let taken = taken.substitute(inferred);
        self.binder.converts_implicitly(receiver, &taken) || *receiver == taken
    }

    /// Whether an extension method's `this` parameter takes a receiver of
    /// this type — any receiver, where it is generic.
    pub(super) fn extension_takes(&self, method: SymbolId, receiver: &Type) -> bool {
        let symbols = self.binder.compilation().symbols();
        let Some(detail) = symbols.get(method).as_method() else {
            return false;
        };
        let Some(first) = detail.parameters.first() else {
            return false;
        };
        let mut sink = Diagnostics::new();
        let taken = self.binder.type_of(*first, &mut sink);
        !detail.type_parameters.is_empty() || self.binder.converts_implicitly(receiver, &taken)
    }

    /// The type an extension block extends, as its receiver wrote it.
    /// Whether a static member an extension block (C# 14) declared is
    /// reached through a type written as the receiver: the type is the one
    /// extended, or reaches it the way an extension receiver may — by
    /// reference or by boxing (`string.M()` for an `extension(object)`), or
    /// the block extends a type parameter, which any type may stand for.
    pub(super) fn static_extension_fits(
        &self,
        extended: crate::symbol::TypeSyntaxRef,
        receiver: &Type,
    ) -> bool {
        let extended = self.resolve_extended(extended);
        if extended.symbol() == receiver.symbol() && receiver.symbol().is_some() {
            return true;
        }
        match extended {
            Type::TypeParameter(_) => true,
            Type::Error => false,
            extended => {
                self.binder.converts_implicitly(receiver, &extended)
                    && self.receiver_converts(receiver, &extended)
            }
        }
    }

    pub(super) fn resolve_extended(&self, extended: crate::symbol::TypeSyntaxRef) -> Type {
        let mut sink = Diagnostics::new();
        self.binder.resolve_type_ref(extended, &mut sink)
    }

    /// `x[i]` reaching an indexer an extension block (C# 14) declared for
    /// what `x` is: the indexer, whose first parameter is the receiver.
    pub(super) fn extension_indexer(
        &self,
        receiver: &Type,
        indices: &[BoundExpression],
    ) -> Option<(SymbolId, HashMap<SymbolId, Type>)> {
        let symbols = self.binder.compilation().symbols();
        self.binder
            .extension_members_in_scope(&self.context, "this[]")
            .into_iter()
            .find_map(|candidate| {
                let detail = symbols.get(candidate).as_property()?;
                let mut inferred = HashMap::new();
                let fits = detail.parameters.len() == indices.len() + 1
                    && detail.parameters.first().is_some_and(|parameter| {
                        self.receiver_fits(
                            *parameter,
                            receiver,
                            &detail.extension_generics,
                            &mut inferred,
                        )
                    })
                    && detail.parameters[1..]
                        .iter()
                        .zip(indices)
                        .all(|(parameter, index)| {
                            let mut sink = Diagnostics::new();
                            let wanted = self
                                .binder
                                .type_of(*parameter, &mut sink)
                                .substitute(&inferred);
                            self.binder.converts_implicitly(&index.ty, &wanted)
                                || self.constant_fits(index, &wanted)
                        });
                fits.then_some((candidate, inferred))
            })
    }

    /// The property an extension block (C# 14) declared for `receiver`'s
    /// type, or a `get_Name(receiver)` extension method standing for one,
    /// if either is in scope.
    pub(super) fn extension_property(&self, receiver: &Type, name: &str) -> Option<SymbolId> {
        let symbols = self.binder.compilation().symbols();
        let declared = self
            .binder
            .extension_members_in_scope(&self.context, name)
            .into_iter()
            .find(|member| {
                symbols.get(*member).as_property().is_some_and(|detail| {
                    !detail.is_indexer
                        && detail.parameters.first().is_some_and(|parameter| {
                            let mut inferred = HashMap::new();
                            self.receiver_fits(
                                *parameter,
                                receiver,
                                &detail.extension_generics,
                                &mut inferred,
                            )
                        })
                })
            });
        if declared.is_some() {
            return declared;
        }
        self.binder
            .extensions_in_scope(&self.context, &format!("get_{name}"))
            .into_iter()
            .find(|method| {
                symbols
                    .get(*method)
                    .as_method()
                    .and_then(|detail| detail.parameters.first().copied())
                    .is_some_and(|parameter| {
                        let mut sink = Diagnostics::new();
                        let taken = self.binder.type_of(parameter, &mut sink);
                        self.binder.converts_implicitly(receiver, &taken)
                    })
            })
    }
}

/// The name syntax behind an expression, when the two coincide.
fn as_name_syntax(node: &SyntaxNode) -> Option<SyntaxNode> {
    matches!(
        node.kind(),
        SyntaxKind::IdentifierName
            | SyntaxKind::GenericName
            | SyntaxKind::QualifiedName
            | SyntaxKind::AliasQualifiedName
    )
    .then(|| node.clone())
    .or_else(|| {
        // `System.Collections` parses as member access in an expression, but
        // reads as a qualified name.
        (node.kind() == SyntaxKind::SimpleMemberAccessExpression).then(|| node.clone())
    })
}

/// Whether a member access ended up on a type rather than on a value.
fn receiver_is_a_type(expression: &BoundExpression) -> bool {
    let receiver = match &expression.kind {
        BoundExpressionKind::Field { receiver, .. }
        | BoundExpressionKind::Property { receiver, .. }
        | BoundExpressionKind::Call { receiver, .. } => receiver.as_deref(),
        _ => None,
    };
    receiver.is_some_and(|receiver| matches!(receiver.kind, BoundExpressionKind::TypeExpression(_)))
}

/// Whether a local called `name` is declared later in a block around
/// `node`: its scope is the whole block, so the name is that local's even
/// where it is not in effect yet (CS0841), and not a name nothing declares.
fn declared_further_on(node: &SyntaxNode, name: &str) -> bool {
    declared_by_a_later_statement(node, name)
        || designated_further_on(node, name)
        || declared_around(node, name)
}

/// Whether `node` is inside the declaration of the variable it names: `var
/// x = x.Next;`, whose type is what is being worked out, or `(var a, a) =
/// pair`, which declares `a` in the same breath as it assigns it.
fn declared_around(node: &SyntaxNode, name: &str) -> bool {
    let names = |token: &rustlyn_syntax::SyntaxToken| {
        token.kind() == SyntaxKind::IdentifierToken && token.value_text() == name
    };
    for ancestor in node.ancestors() {
        match ancestor.kind() {
            SyntaxKind::EqualsValueClause => {
                if let Some(declarator) = ancestor
                    .parent()
                    .filter(|parent| parent.kind() == SyntaxKind::VariableDeclarator)
                    && declarator.child_tokens().any(|token| names(&token))
                {
                    return true;
                }
            }
            SyntaxKind::SimpleAssignmentExpression => {
                let Some(target) = ancestor.children().next() else {
                    continue;
                };
                if target.kind() == SyntaxKind::TupleExpression
                    && target.span().contains_span(node.span())
                    && target.descendants().any(|designation| {
                        designation.kind() == SyntaxKind::SingleVariableDesignation
                            && designation.child_tokens().any(|token| names(&token))
                    })
                {
                    return true;
                }
            }
            kind if kind.is_statement_node() => return false,
            _ => {}
        }
    }
    false
}

/// Whether an `out var name` or a pattern's `name` further on declares the
/// variable in a scope that `node` is in: `M(x, out var x)` reads `x` before
/// the argument after it declares it.
fn designated_further_on(node: &SyntaxNode, name: &str) -> bool {
    let start = node.span().start();
    let Some(root) = node.ancestors().find(|ancestor| {
        matches!(
            ancestor.kind(),
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::DestructorDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::IndexerDeclaration
                | SyntaxKind::FieldDeclaration
                | SyntaxKind::EventDeclaration
                | SyntaxKind::CompilationUnit
        )
    }) else {
        return false;
    };
    root.descendants()
        .filter(|designation| {
            designation.kind() == SyntaxKind::SingleVariableDesignation
                && designation.span().start() > start
                && designation
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .is_some_and(|token| token.value_text() == name)
        })
        .any(|designation| {
            expression_variable_scope(&designation)
                .is_some_and(|scope| scope.span().contains_span(node.span()))
        })
}

/// The syntax an expression variable is in scope in (§7.7.1): the block
/// around the statement that declares it, or the statement itself where it
/// is a loop, a `using` or an embedded statement, or the one expression
/// that makes up a lambda's body, an initializer or an argument list.
fn expression_variable_scope(designation: &SyntaxNode) -> Option<SyntaxNode> {
    for ancestor in designation.ancestors() {
        let kind = ancestor.kind();
        match kind {
            SyntaxKind::Block
            | SyntaxKind::SwitchSection
            | SyntaxKind::SwitchExpressionArm
            | SyntaxKind::CatchClause
            | SyntaxKind::AttributeArgumentList
            | SyntaxKind::ArrowExpressionClause
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::CompilationUnit
            | SyntaxKind::WhileStatement
            | SyntaxKind::DoStatement
            | SyntaxKind::ForStatement
            | SyntaxKind::ForEachStatement
            | SyntaxKind::ForEachVariableStatement
            | SyntaxKind::UsingStatement
            | SyntaxKind::LockStatement
            | SyntaxKind::FixedStatement
            | SyntaxKind::SwitchStatement => return Some(ancestor),
            // What a constructor's `: base(...)` declares, its body sees.
            SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer => {
                return ancestor.parent().cloned();
            }
            // An initializer of anything but a local is a scope of its own.
            SyntaxKind::EqualsValueClause
                if !ancestor.ancestors().nth(1).is_some_and(|declaration| {
                    declaration.kind() == SyntaxKind::VariableDeclaration
                        && declaration.parent().is_some_and(|statement| {
                            statement.kind() == SyntaxKind::LocalDeclarationStatement
                        })
                }) =>
            {
                return Some(ancestor);
            }
            SyntaxKind::LocalFunctionStatement => return Some(ancestor),
            // A statement that is not in a block is a scope of its own: `if
            // (b) M(out var x);` declares `x` for that call and no further.
            _ if kind.is_statement_node()
                && !ancestor.parent().is_some_and(|parent| {
                    matches!(
                        parent.kind(),
                        SyntaxKind::Block
                            | SyntaxKind::SwitchSection
                            | SyntaxKind::GlobalStatement
                            | SyntaxKind::LabeledStatement
                    )
                }) =>
            {
                return Some(ancestor);
            }
            _ => {}
        }
    }
    None
}

fn declared_by_a_later_statement(node: &SyntaxNode, name: &str) -> bool {
    let start = node.span().start();
    for ancestor in node.ancestors() {
        if matches!(
            ancestor.kind(),
            SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::AccessorList
                | SyntaxKind::ClassDeclaration
                | SyntaxKind::StructDeclaration
        ) {
            return false;
        }
        if !matches!(
            ancestor.kind(),
            SyntaxKind::Block | SyntaxKind::SwitchSection | SyntaxKind::CompilationUnit
        ) {
            continue;
        }
        let later = statements_of(&ancestor)
            .filter(|statement| {
                statement.kind() == SyntaxKind::LocalDeclarationStatement
                    && statement.span().start() > start
            })
            .flat_map(|statement| statement.descendants())
            .filter(|declarator| declarator.kind() == SyntaxKind::VariableDeclarator)
            .any(|declarator| {
                declarator
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .is_some_and(|token| token.value_text() == name)
            });
        if later || ancestor.kind() == SyntaxKind::CompilationUnit {
            return later;
        }
    }
    false
}

/// The statements of a block or a switch section, or the top-level
/// statements of a file.
fn statements_of(scope: &SyntaxNode) -> impl Iterator<Item = SyntaxNode> {
    let top_level = scope.kind() == SyntaxKind::CompilationUnit;
    scope.children().filter_map(move |child| {
        if top_level {
            (child.kind() == SyntaxKind::GlobalStatement)
                .then(|| child.children().next())
                .flatten()
        } else {
            Some(child)
        }
    })
}

/// Whether type syntax spells a constructed generic type: `List<int>`, or a
/// qualified name ending in one.
fn names_a_construction(node: &SyntaxNode) -> bool {
    match node.kind() {
        SyntaxKind::GenericName => true,
        SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => node
            .children()
            .last()
            .is_some_and(|last| names_a_construction(&last)),
        _ => false,
    }
}

/// Whether `reference` sits in the argument list that declares, with
/// `out var`, the variable whose name is written at `declared`: the type of
/// that variable is not known until the call is resolved.
fn in_out_var_zone(reference: &SyntaxNode, declared: TextSpan) -> bool {
    let Some(root) = reference.ancestors().last() else {
        return false;
    };
    let Some(token) = root.find_token(declared.start()) else {
        return false;
    };
    let Some(declaration) = token
        .parent()
        .ancestors()
        .find(|node| node.kind() == SyntaxKind::DeclarationExpression)
    else {
        return false;
    };
    let is_var = declaration
        .children()
        .find(|child| child.kind().is_type_node())
        .is_some_and(|written| super::declares_var(&written));
    let Some(argument) = declaration.parent().filter(|parent| {
        parent.kind() == SyntaxKind::Argument
            && parent
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::OutKeyword)
    }) else {
        return false;
    };
    let Some(list) = argument
        .parent()
        .filter(|list| list.kind() == SyntaxKind::ArgumentList)
    else {
        return false;
    };
    is_var
        && reference.span().start() >= declaration.span().end()
        && reference.span().end() <= list.span().end()
}
