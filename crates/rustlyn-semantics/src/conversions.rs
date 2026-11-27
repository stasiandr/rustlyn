//! Implicit conversions, and the type a binary operator produces.
//!
//! These are the tables in §10 and §12 of the specification. They matter more
//! than they look: overload resolution is mostly the question "does this
//! argument convert to this parameter", asked once per candidate.

use crate::binder::{Binder, Diagnostics};
use crate::corlib::SpecialType;
use crate::symbol::{RefKind, SymbolId, TypeKind, Variance};
use crate::types::{FunctionPointer, Type};

impl Binder<'_> {
    /// The special type a type is, if it is one of the built-in ones.
    #[must_use]
    pub fn special_of(&self, ty: &Type) -> Option<SpecialType> {
        let symbol = ty.symbol()?;
        SpecialType::ALL
            .iter()
            .copied()
            .find(|special| self.compilation().special_type(*special) == Some(symbol))
    }

    /// Whether two types differ, if at all, only where one says `dynamic`
    /// and the other `object`.
    #[must_use]
    pub fn same_but_for_dynamic(&self, left: &Type, right: &Type) -> bool {
        if !contains_dynamic(left) && !contains_dynamic(right) {
            return left == right;
        }
        self.object_type()
            .is_some_and(|object| erase_dynamic(left, &object) == erase_dynamic(right, &object))
    }

    /// Whether two types are one type to the runtime, differing only in
    /// what the compiler reads off them: tuple element names, and `dynamic`
    /// for `object` (the identity conversion of §10.2.2).
    #[must_use]
    pub fn identity_converts(&self, left: &Type, right: &Type) -> bool {
        left == right || self.same_but_for_dynamic(&self.canonical(left), &self.canonical(right))
    }

    /// `object`, which `dynamic` is to the runtime.
    #[must_use]
    pub fn object_type(&self) -> Option<Type> {
        self.compilation()
            .special_type(SpecialType::Object)
            .map(Type::named)
    }

    /// Whether a value of type `from` can be used where `to` is expected,
    /// without a cast.
    #[must_use]
    pub fn converts_implicitly(&self, from: &Type, to: &Type) -> bool {
        // An error has already been reported about; letting it convert keeps
        // one mistake from turning into several.
        if from.is_error() || to.is_error() {
            return true;
        }
        if from == to {
            return true;
        }
        // The answer depends on the two types alone, and overload resolution
        // asks for the same pairs again and again.
        let key = (from.clone(), to.clone());
        if let Some(answer) = self.compilation().cached_implicit(&key) {
            return answer;
        }
        let answer = self.converts_implicitly_uncached(from, to) || self.union_converts(from, to);
        self.compilation().cache_implicit(key, answer);
        answer
    }

    /// Whether one function pointer type converts to another: the same
    /// convention and `ref` kinds, each by-value parameter the other way by
    /// identity or a reference conversion, and the return this way.
    fn function_pointer_converts(&self, from: &FunctionPointer, to: &FunctionPointer) -> bool {
        let symbols = self.compilation().symbols();
        let reaches = |from: &Type, to: &Type| {
            from == to
                || (matches!(
                    (from, to),
                    (Type::FunctionPointer(_), Type::FunctionPointer(_))
                ) || (from.is_reference_type(symbols) && to.is_reference_type(symbols)))
                    && self.converts_implicitly(from, to)
        };
        from.convention == to.convention
            && from.modifiers == to.modifiers
            && from.returns_ref == to.returns_ref
            && from.parameters.len() == to.parameters.len()
            && if from.returns_ref == RefKind::None {
                reaches(&from.returns, &to.returns)
            } else {
                from.returns == to.returns
            }
            && from.parameters.iter().zip(&to.parameters).all(
                |((from_kind, from_ty), (to_kind, to_ty))| {
                    from_kind == to_kind
                        && if *from_kind == RefKind::None {
                            reaches(to_ty, from_ty)
                        } else {
                            from_ty == to_ty
                        }
                },
            )
    }

    /// Whether a value converts implicitly by any conversion but a union
    /// conversion (C# 15), which gives way to every other.
    #[must_use]
    pub fn converts_implicitly_but_by_union(&self, from: &Type, to: &Type) -> bool {
        if from.is_error() || to.is_error() || from == to {
            return true;
        }
        // Into the `U?` of a union, what reaches the `U`.
        if let Some(inner) = self.nullable_underlying(to)
            && self.is_union_type(&inner)
        {
            return matches!(from, Type::Null)
                || self.nullable_underlying(from).as_ref() == Some(&inner)
                || self.converts_implicitly_but_by_union(from, &inner);
        }
        // Into a union itself, only what reaches any class or struct: a
        // null or a derived class, a `dynamic`, and an operator it declares.
        // Asking the general question would find the union conversion again
        // through one of its steps.
        if self.is_union_type(to) {
            let reference = to.is_reference_type(self.compilation().symbols());
            return matches!(from, Type::Dynamic)
                || (reference && matches!(from, Type::Null))
                || (reference && self.inherits_from(from, to, 0))
                || self.implicit_operator(from, to).is_some();
        }
        // Neither the type nor what it wraps is a union here, so no union
        // conversion could answer: the cached question is this one, and an
        // array initializer of millions of constants asks it for each.
        self.converts_implicitly(from, to)
    }

    fn converts_implicitly_uncached(&self, from: &Type, to: &Type) -> bool {
        // `dynamic` converts to anything, the runtime deciding how (§10.2.10);
        // anything that converts to `object` converts to `dynamic` (§10.2.8).
        // And `List<dynamic>` is `List<object>`: the two differ only in what
        // the compiler does with a value, never in what the value is.
        if matches!(from, Type::Dynamic) {
            return !matches!(to, Type::Void | Type::Pointer(_) | Type::ByRef(_));
        }
        if matches!(to, Type::Dynamic) {
            return self
                .object_type()
                .is_some_and(|object| self.converts_implicitly(from, &object));
        }
        if (contains_dynamic(from) || contains_dynamic(to))
            && let Some(object) = self.object_type()
        {
            let (from, to) = (erase_dynamic(from, &object), erase_dynamic(to, &object));
            return self.converts_implicitly(&from, &to);
        }
        // `(int a, string b)` and `(int, string)` are the same type: the
        // names are for the reader, and the runtime never sees them.
        if let (Type::Tuple(from), Type::Tuple(to)) = (from, to) {
            return from.len() == to.len()
                && from
                    .iter()
                    .zip(to)
                    .all(|(from, to)| self.converts_implicitly(&from.ty, &to.ty));
        }
        // A tuple *is* a `ValueTuple<...>`, written another way.
        if let Some(elements) = self.tuple_elements(from)
            && let Some(wanted) = self.tuple_elements(to)
        {
            return elements.len() == wanted.len()
                && elements
                    .iter()
                    .zip(&wanted)
                    .all(|(from, to)| self.converts_implicitly(from, to));
        }

        // A tuple is a struct like any other past its elements: it boxes to
        // `ValueType`, `object` and the interfaces its `ValueTuple` has.
        if let Type::Tuple(elements) = from
            && self.tuple_elements(to).is_none()
            && self.nullable_underlying(to).is_none()
            && let Some(named) = self.value_tuple_of(
                &elements
                    .iter()
                    .map(|element| element.ty.clone())
                    .collect::<Vec<_>>(),
            )
        {
            return self.converts_implicitly(&named, to);
        }

        // An array, a span or a string converts to a span (C# 14).
        if self.first_class_spans() && self.implicit_span_conversion(from, to) {
            return true;
        }
        // An inline array converts to a `Span<T>` or `ReadOnlySpan<T>` over
        // its elements (§10.2.?, C# 12).
        if let Some((element, _)) = self.inline_array_of(from)
            && self.is_span_of(to, &element)
        {
            return true;
        }

        // `BoundLiteral[]` reaches a `BoundExpression[]`: an array of a
        // reference type converts to an array of anything that type converts
        // to (§10.2.7). It is the one conversion the runtime does not check
        // on the way in, which is why writing to one can throw later.
        if let (
            Type::Array { element, rank },
            Type::Array {
                element: wanted,
                rank: wanted_rank,
            },
        ) = (from, to)
            && rank == wanted_rank
            && self.held_by_reference(element)
            && self.held_by_reference(wanted)
        {
            return self.converts_implicitly(element, wanted);
        }
        // A vector `S[]` is an `IList<T>` — and the other generic collection
        // interfaces an array implements — wherever `S` is a `T` by a
        // reference conversion (§10.2.8): a `Vector2[][]` is an
        // `IList<IList<Vector2>>`.
        if let (
            Type::Array { element, rank: 1 },
            Type::Named {
                symbol,
                type_arguments,
            },
        ) = (from, to)
            && let [wanted] = type_arguments.as_slice()
            && **element != *wanted
            && self.held_by_reference(element)
            && self.held_by_reference(wanted)
            && [
                "System.Collections.Generic.IList`1",
                "System.Collections.Generic.ICollection`1",
                "System.Collections.Generic.IEnumerable`1",
                "System.Collections.Generic.IReadOnlyList`1",
                "System.Collections.Generic.IReadOnlyCollection`1",
            ]
            .iter()
            .any(|name| self.compilation().type_by_metadata_name(name) == Some(*symbol))
            && self.converts_implicitly(element, wanted)
        {
            return true;
        }

        // A function pointer takes `null`, reaches `void*`, and reaches
        // another of the same shape whose parameters are more derived and
        // whose return is less (C# 9's function pointer conversions).
        match (from, to) {
            (Type::Null, Type::FunctionPointer(_)) => return true,
            (Type::FunctionPointer(source), Type::FunctionPointer(target)) => {
                return self.function_pointer_converts(source, target);
            }
            (Type::FunctionPointer(_), Type::Pointer(element)) => {
                return matches!(**element, Type::Void);
            }
            (Type::FunctionPointer(_), _) | (_, Type::FunctionPointer(_)) => return false,
            _ => {}
        }

        // `return null;` from a `TNode? M<TNode>() where TNode : SyntaxNode`:
        // a constraint naming a class makes the parameter a reference type
        // as surely as `class` does.
        if matches!(from, Type::Null) {
            return self.held_by_reference(to)
                || self.nullable_underlying(to).is_some()
                || self.takes_null_through_operator(to);
        }

        if self.canonical(from) == self.canonical(to) {
            return true;
        }

        // A `ref struct` never boxes (§16.2.3): not to `object`, not to
        // `ValueType`, not to an interface it implements. What it may reach
        // of a reference type is what an operator the program wrote makes.
        if self.is_ref_like(from) && to.is_reference_type(self.compilation().symbols()) {
            return self.implicit_operator(from, to).is_some_and(|operator| {
                let mut sink = Diagnostics::new();
                let made = self.type_of(operator, &mut sink);
                !self.is_ref_like(&made)
            });
        }

        // A `T?` boxes to any interface its `T` implements (§10.2.9): what
        // comes out is the boxed `T`, or null where there was nothing. So it
        // does to a type parameter its `T` depends on.
        if let Some(underlying) = self.nullable_underlying(from)
            && (matches!(to, Type::TypeParameter(_))
                || to.symbol().is_some_and(|symbol| {
                    self.compilation().symbols().get(symbol).type_kind()
                        == Some(TypeKind::Interface)
                }))
            && self.converts_implicitly(&underlying, to)
        {
            return true;
        }

        // Every pointer reaches `void*` (§23.5.1): `Unsafe.ReadUnaligned`
        // takes one, and is handed a `byte*`.
        if let (Type::Pointer(_), Type::Pointer(element)) = (from, to)
            && matches!(**element, Type::Void)
        {
            return true;
        }

        if let (Some(from_special), Some(to_special)) = (self.special_of(from), self.special_of(to))
            && implicit_numeric(from_special, to_special)
        {
            return true;
        }

        // `nint` sits between `int` and `long` (§10.2.3): an `int` reaches
        // it, and it reaches a `long`; `nuint` likewise for the unsigned.
        if let Some(unsigned) = self.native_int(to)
            && let Some(from_special) = self.special_of(from)
        {
            use SpecialType::{Byte, Char, Int16, Int32, SByte, UInt16, UInt32};
            let reaches: &[SpecialType] = if unsigned {
                &[Byte, UInt16, UInt32, Char]
            } else {
                &[SByte, Byte, Int16, UInt16, Int32, Char]
            };
            if reaches.contains(&from_special) {
                return true;
            }
        }
        if let Some(unsigned) = self.native_int(from)
            && let Some(to_special) = self.special_of(to)
        {
            use SpecialType::{Decimal, Double, Int64, Single, UInt64};
            let reached: &[SpecialType] = if unsigned {
                &[UInt64, Single, Double, Decimal]
            } else {
                &[Int64, Single, Double, Decimal]
            };
            if reached.contains(&to_special) {
                return true;
            }
        }

        // `int` to `int?`
        if let Some(underlying) = self.nullable_underlying(to)
            && self.converts_implicitly(from, &underlying)
        {
            return true;
        }

        // `byte?` to `int?`: §10.2.6 lifts a conversion between two value
        // types onto their nullable forms, and a null stays a null.
        if let (Some(inner), Some(wanted)) =
            (self.nullable_underlying(from), self.nullable_underlying(to))
            && self.converts_implicitly(&inner, &wanted)
        {
            return true;
        }

        // Anything at all to `object`, by boxing if it has to.
        if self.special_of(to) == Some(SpecialType::Object) {
            return true;
        }

        if self.inherits_from(from, to, 0) {
            return true;
        }

        // An `S?` boxes to whatever reference type `S` boxes to, null to a
        // null (§10.2.9): an `AssemblyOptions?` is an `Enum`.
        if let Some(inner) = self.nullable_underlying(from)
            && to.is_reference_type(self.compilation().symbols())
            && self.inherits_from(&inner, to, 0)
        {
            return true;
        }

        // `IEnumerable<out T>` means a `List<string>` is an
        // `IEnumerable<object>`, not only an `IEnumerable<string>`: the
        // construction `from` is of the wanted definition is found first, and
        // then each argument is compared the way its parameter's variance
        // says to.
        if let Type::Named {
            symbol: wanted,
            type_arguments,
        } = to
            && !type_arguments.is_empty()
            && let Some(Type::Named {
                type_arguments: mine,
                ..
            }) = self.constructed_from(from, *wanted)
            && mine.len() == type_arguments.len()
            && self.variance_allows(*wanted, &mine, type_arguments)
        {
            return true;
        }

        // Last: a conversion the program wrote itself — lifted, too, from an
        // `S?` where `S` has one: null gives null (§10.6.2).
        self.implicit_operator(from, to).is_some()
            || self.nullable_underlying(from).is_some_and(|inner| {
                let wanted = self.nullable_underlying(to).unwrap_or_else(|| to.clone());
                (self.nullable_underlying(to).is_some()
                    || to.is_reference_type(self.compilation().symbols()))
                    && inner.symbol().is_some()
                    && (self.implicit_operator(&inner, &wanted).is_some()
                        // An operator giving an `int?` is lifted too: `S?`
                        // reaches a `long?` through `operator int?(S)`.
                        || (wanted != *to && self.implicit_operator(&inner, to).is_some()))
            })
    }

    /// Whether one construction of a type converts to another.
    ///
    /// Only where the type said so: `out T` may widen, `in T` may narrow, and
    /// a parameter that said neither has to match exactly, because a value
    /// goes both in and out through it.
    /// Whether values of a type are held by reference, looking through what a
    /// type parameter's constraints promise.
    ///
    /// `where TSymbol : Symbol` makes `TSymbol` a reference type as surely as
    /// writing `class` does, and §10.2.11 lets a variance conversion vary only
    /// where both sides are: without this, a `Comparer` that is an
    /// `IEqualityComparer<Symbol>` is not an `IEqualityComparer<TSymbol>`.
    #[must_use]
    pub fn held_by_reference(&self, ty: &Type) -> bool {
        let symbols = self.compilation().symbols();
        if ty.is_reference_type(symbols) {
            return true;
        }
        let Type::TypeParameter(symbol) = ty else {
            return false;
        };
        let Some(detail) = symbols.get(*symbol).as_type_parameter() else {
            return false;
        };
        if detail.value_type {
            return false;
        }
        if detail.reference_type {
            return true;
        }
        if let Some(overridden) = self.overridden_type_parameter(*symbol) {
            return self.held_by_reference(&Type::TypeParameter(overridden));
        }
        // An interface constraint says nothing: a struct can implement one.
        self.base_types_of(*symbol).iter().any(|base| {
            base.symbol().is_some_and(|base| {
                matches!(
                    symbols.get(base).type_kind(),
                    Some(TypeKind::Class | TypeKind::Record | TypeKind::Delegate)
                )
            })
        })
    }

    fn variance_allows(&self, definition: SymbolId, mine: &[Type], wanted: &[Type]) -> bool {
        // `interface I<out T> : I<I<T>>` makes each question about `I<A>` a
        // question about `I<I<A>>`, without end. Roslyn gives up on such an
        // expansion and says there is no conversion; so does this, at a
        // depth no real program's variance nests to.
        thread_local! {
            static DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
        }
        let depth = DEPTH.get();
        if depth > 40 {
            return false;
        }
        DEPTH.set(depth + 1);
        let allowed = self.variance_allows_at(definition, mine, wanted);
        DEPTH.set(depth);
        allowed
    }

    fn variance_allows_at(&self, definition: SymbolId, mine: &[Type], wanted: &[Type]) -> bool {
        let symbols = self.compilation().symbols();
        let Some(parameters) = symbols
            .get(definition)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
        else {
            return false;
        };
        if parameters.len() != mine.len() {
            return false;
        }
        parameters
            .iter()
            .zip(mine.iter().zip(wanted))
            .all(|(parameter, (mine, wanted))| {
                if mine == wanted {
                    return true;
                }
                // Only a reference conversion is allowed to vary: an
                // `IEnumerable<int>` is not an `IEnumerable<object>`, because
                // boxing makes a different value rather than reading the same
                // one another way.
                if !self.held_by_reference(mine) || !self.held_by_reference(wanted) {
                    return false;
                }
                match symbols
                    .get(*parameter)
                    .as_type_parameter()
                    .map(|detail| detail.variance)
                {
                    Some(Variance::Out) => self.converts_implicitly(mine, wanted),
                    Some(Variance::In) => self.converts_implicitly(wanted, mine),
                    _ => false,
                }
            })
    }

    /// Whether a type is a `ref struct`.
    #[must_use]
    pub fn is_ref_like(&self, ty: &Type) -> bool {
        matches!(ty, Type::Named { .. })
            && ty.symbol().is_some_and(|symbol| {
                self.compilation()
                    .symbols()
                    .get(symbol)
                    .as_named_type()
                    .is_some_and(|detail| detail.ref_like)
            })
    }

    /// The `op_Implicit` that takes `from` and gives back `to`, if a type
    /// declares one.
    ///
    /// C# lets a type say how values reach it, and the call site says nothing:
    /// `GetSpecialType(SpecialType.System_Int32)` passes a `SpecialType` to a
    /// parameter of another type entirely, and works because that type
    /// declared the conversion. Both types are asked, because either may be
    /// the one that declared it.
    #[must_use]
    pub fn implicit_operator(&self, from: &Type, to: &Type) -> Option<SymbolId> {
        // Nothing declares a conversion from nothing, and a pair of built-in
        // types never needs one.
        if from.symbol().is_none() && to.symbol().is_none() {
            return None;
        }
        let key = (from.clone(), to.clone());
        if let Some(cached) = self.compilation().cached_conversion(&key) {
            return cached;
        }
        let found = self.operator_uncached(from, to, "op_Implicit");
        self.compilation().cache_conversion(key, found);
        found
    }

    /// Whether `null` reaches `to` through a conversion `to` declares from a
    /// reference type: `ReadOnlySpan<byte> span = null;` is the array
    /// conversion applied to a null array.
    fn takes_null_through_operator(&self, to: &Type) -> bool {
        self.null_operator(to).is_some()
    }

    /// The conversion `to` declares from a reference type, which `null`
    /// given to `to` goes through.
    #[must_use]
    pub fn null_operator(&self, to: &Type) -> Option<SymbolId> {
        let symbols = self.compilation().symbols();
        let target = to.symbol()?;
        symbols
            .lookup(target, "op_Implicit")
            .iter()
            .copied()
            .find(|&operator| {
                let Some(detail) = symbols.get(operator).as_method() else {
                    return false;
                };
                let [parameter] = detail.parameters.as_slice() else {
                    return false;
                };
                let mut sink = Diagnostics::new();
                let taken = self.type_of(*parameter, &mut sink);
                let given = self.type_of(operator, &mut sink);
                // A type parameter constrained to a class takes `null` as
                // surely as one constrained to `class`.
                self.held_by_reference(&taken) && given.symbol() == Some(target)
            })
    }

    /// The `op_Explicit` a written cast reaches, if a type declares one.
    ///
    /// §10.5.3: only a cast may use one, which is the whole difference
    /// between the two — `(ExtendedSpecialType)i` is a call and `i` on its
    /// own is not one.
    #[must_use]
    pub fn explicit_operator(&self, from: &Type, to: &Type) -> Option<SymbolId> {
        self.explicit_operator_in(from, to, false)
    }

    /// The same for a cast in a checked context, where an `explicit
    /// operator checked` (C# 11) is preferred to the regular operator of
    /// the same signature — which, having the same types, it is at every
    /// step of the search — and a regular one serves where there is none.
    #[must_use]
    pub fn explicit_operator_in(&self, from: &Type, to: &Type, checked: bool) -> Option<SymbolId> {
        if from.symbol().is_none() && to.symbol().is_none() {
            return None;
        }
        let names: &[&str] = if checked {
            &["op_CheckedExplicit", "op_Explicit"]
        } else {
            &["op_Explicit"]
        };
        // An operator giving the target itself first; only failing that, one
        // whose result a standard conversion carries the rest of the way
        // (§10.5.3), as `operator_uncached` does for one name.
        names
            .iter()
            .find_map(|name| self.operator_matching(from, to, name, false))
            .or_else(|| {
                names
                    .iter()
                    .find_map(|name| self.operator_matching(from, to, name, true))
            })
            // A cast may use an implicit operator too, with the explicit
            // conversions around it: `(S)i` reaches `implicit operator
            // S?(decimal)` and takes the `S` out of what it gives.
            .or_else(|| self.operator_matching_as(from, to, "op_Implicit", true, true))
    }

    fn operator_uncached(&self, from: &Type, to: &Type, name: &str) -> Option<SymbolId> {
        // An operator giving the target itself first; only failing that, one
        // whose result a standard conversion carries the rest of the way
        // (§10.5.3): `(long)test` reaches `explicit operator int(Test)`,
        // but `(int)test` must not reach an `explicit operator long`.
        self.operator_matching(from, to, name, false)
            .or_else(|| self.operator_matching(from, to, name, true))
    }

    /// Whether a standard conversion carries what an operator gives to the
    /// target: a numeric widening — or, for an explicit conversion, a
    /// narrowing too — and the wrapping into a `T?`.
    fn standard_after(&self, gives: &Type, to: &Type, explicit: bool) -> bool {
        let inner = self.nullable_underlying(to);
        let target = inner.as_ref().unwrap_or(to);
        if gives == target {
            return true;
        }
        // An operator giving an `S?` reaches an `S` by the unwrapping a
        // cast may do.
        if explicit && self.nullable_underlying(gives).as_ref() == Some(to) {
            return true;
        }
        // An operator giving an array reaches a span of it (C# 14): the span
        // conversion is a standard one.
        if self.first_class_spans() && self.implicit_span_conversion(gives, target) {
            return true;
        }
        // An operator giving an `int?` reaches a `long?` by the lifted
        // widening (§10.5.4): the second step is any standard implicit
        // conversion, and a nullable one is among them.
        let gives = match (&inner, self.nullable_underlying(gives)) {
            (Some(_), Some(given)) => given,
            _ => gives.clone(),
        };
        match (self.special_of(&gives), self.special_of(target)) {
            (Some(given), Some(wanted)) if given.is_numeric() && wanted.is_numeric() => {
                explicit || implicit_numeric(given, wanted)
            }
            _ => false,
        }
    }

    fn operator_matching(
        &self,
        from: &Type,
        to: &Type,
        name: &str,
        loose: bool,
    ) -> Option<SymbolId> {
        let explicit = matches!(name, "op_Explicit" | "op_CheckedExplicit");
        self.operator_matching_as(from, to, name, loose, explicit)
    }

    fn operator_matching_as(
        &self,
        from: &Type,
        to: &Type,
        name: &str,
        loose: bool,
        explicit: bool,
    ) -> Option<SymbolId> {
        let symbols = self.compilation().symbols();
        let inner_target = self.nullable_underlying(to);
        let mut found: Vec<(SymbolId, Type)> = Vec::new();
        for (side, owner_type) in [from, to].into_iter().enumerate() {
            // `Nullable<T>` declares an `op_Implicit` from `T`, but `int` into
            // an `int?` is not a user-defined conversion: the language lifts
            // it, and the backend writes a constructor call rather than a
            // call to that operator. Leaving it out here is what keeps the
            // two from being confused once the operator's `T` is substituted.
            // What a `T?` offers is what its `T` declares (§10.5.4): `AA? a =
            // tuple` goes through `AA`'s operator and wraps what it gives.
            let underlying = self.nullable_underlying(owner_type);
            let owner_type = underlying.as_ref().unwrap_or(owner_type);
            // A tuple's operators are its `ValueTuple`'s, which a program
            // may declare itself.
            let as_named = match owner_type {
                Type::Tuple(elements) => self.value_tuple_of(
                    &elements
                        .iter()
                        .map(|element| element.ty.clone())
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            };
            let owner_type = as_named.as_ref().unwrap_or(owner_type);
            // The operator is written in terms of the type's own parameters:
            // `SyntaxListBuilder<TNode>` declares one taking a
            // `SyntaxListBuilder<TNode>`, and the argument at hand is a
            // `SyntaxListBuilder<MemberDeclarationSyntax>`. Comparing the
            // declaration against the construction finds nothing until the
            // construction says what `TNode` stands for. A type parameter's
            // operators are its effective base class's (§10.5.3) — `if
            // (instance)` on a `T : UnityEngine.Object` is `Object`'s
            // `implicit operator bool` — and the static abstract ones of the
            // interfaces it is constrained to (C# 11), in terms of those
            // constructions: `(int)value` on a `T : IConv<T>` is
            // `IConv<T>.op_Explicit`.
            let owners: Vec<(SymbolId, std::collections::HashMap<SymbolId, Type>)> =
                match owner_type {
                    Type::TypeParameter(parameter) => self
                        .base_types_of(*parameter)
                        .iter()
                        .filter(|base| {
                            base.symbol().is_some_and(|base| {
                                matches!(
                                    symbols.get(base).type_kind(),
                                    Some(TypeKind::Interface | TypeKind::Class)
                                )
                            })
                        })
                        .filter_map(|base| Some((base.symbol()?, self.type_substitution(base))))
                        .collect(),
                    _ => {
                        let mut owners: Vec<(SymbolId, std::collections::HashMap<SymbolId, Type>)> =
                            owner_type
                                .symbol()
                                .map(|owner| (owner, self.type_substitution(owner_type)))
                                .into_iter()
                                .collect();
                        // The source's base classes declare operators for it
                        // too (§10.5.3), as it constructs them: a `Pref<bool> :
                        // UserSetting<bool>` reaches `UserSetting<T>`'s
                        // `implicit operator T` with `T` = `bool`.
                        let mut current = owner_type.clone();
                        let mut depth = 0;
                        while side == 0
                            && depth < 32
                            && let Some(symbol) = current.symbol()
                            && symbols.get(symbol).type_kind() == Some(TypeKind::Class)
                            && let Some(base) = self.base_class_of(symbol)
                        {
                            let base = base.substitute(&self.type_substitution(&current));
                            let Some(base_symbol) = base.symbol() else {
                                break;
                            };
                            if Some(base_symbol)
                                == self.compilation().special_type(crate::SpecialType::Object)
                            {
                                break;
                            }
                            owners.push((base_symbol, self.type_substitution(&base)));
                            current = base;
                            depth += 1;
                        }
                        owners
                    }
                };
            for (owner, substitution) in owners {
                for candidate in self.lookup_member(owner, name) {
                    let Some(detail) = symbols.get(candidate).as_method() else {
                        continue;
                    };
                    let [parameter] = detail.parameters[..] else {
                        continue;
                    };
                    let mut sink = crate::binder::Diagnostics::new();
                    let takes = self.type_of(parameter, &mut sink).substitute(&substitution);
                    let gives = self.type_of(candidate, &mut sink).substitute(&substitution);
                    // The operator does not have to name the type at hand. A
                    // `SyntaxNodeOrToken` takes a `SyntaxNode`, and an
                    // `ExpressionSyntax` is one — §10.5.3 lets a standard implicit
                    // conversion run on the way in, and another on the way out.
                    // A number widens on the way in too: `(ExtendedSpecialType)
                    // shortValue` reaches the operator taking an `int`.
                    let widens = match (self.special_of(from), self.special_of(&takes)) {
                        (Some(from_special), Some(takes_special)) => {
                            implicit_numeric(from_special, takes_special)
                        }
                        _ => false,
                    };
                    // A tuple reaches a tuple of what its elements convert to,
                    // on either side of the operator.
                    let tuples = |one: &Type, other: &Type| {
                        let inner = self
                            .nullable_underlying(other)
                            .unwrap_or_else(|| other.clone());
                        self.tuple_elements(one).is_some()
                            && self.tuple_elements(&inner).is_some()
                            && self.converts_implicitly(one, other)
                    };
                    // A cast may take a class down on either side of the
                    // operator (§10.5.5): `(F)d` reaches `explicit operator
                    // E(B)` on a `D : B`, and casts the `E` it gives to `F : E`.
                    let reference = |ty: &Type| ty.is_reference_type(symbols);
                    let down = |base: &Type, derived: &Type| {
                        explicit
                            && loose
                            && reference(base)
                            && reference(derived)
                            && self.inherits_from(derived, base, 0)
                    };
                    let gives_to = gives == *to
                        || inner_target.as_ref() == Some(&gives)
                        || self.inherits_from(&gives, to, 0)
                        || (loose && self.standard_after(&gives, to, explicit))
                        || (loose && tuples(&gives, to))
                        || down(&gives, to);
                    // `int` reaches an operator taking an `int?` by the wrapping
                    // that is a standard conversion too.
                    let wraps = self.nullable_underlying(from).is_none()
                        && self.nullable_underlying(&takes).is_some_and(|inner| {
                            inner == *from
                                || matches!(
                                    (self.special_of(from), self.special_of(&inner)),
                                    (Some(given), Some(wanted)) if implicit_numeric(given, wanted)
                                )
                        });
                    // `int?` reaches an operator taking a `long?` by the lifted
                    // widening, as a standard conversion.
                    let lifted_widens = match (
                        self.nullable_underlying(from),
                        self.nullable_underlying(&takes),
                    ) {
                        (Some(given), Some(wanted)) => matches!(
                            (self.special_of(&given), self.special_of(&wanted)),
                            (Some(given), Some(wanted)) if implicit_numeric(given, wanted)
                        ),
                        _ => false,
                    };
                    if (takes == *from
                        || widens
                        || wraps
                        || lifted_widens
                        || self.inherits_from(from, &takes, 0)
                        // Before C# 14 only: from then on an array reaches a
                        // span by the language's own span conversions, which
                        // leave the span's operators out.
                        || (!self.first_class_spans() && self.array_covariant(from, &takes))
                        || tuples(from, &takes)
                        || down(from, &takes))
                        && gives_to
                    {
                        found.push((candidate, gives));
                    }
                }
            }
        }
        self.most_specific_target(found, to)
    }

    /// Which of the operators that apply is the one (§10.5.4): the one
    /// giving the target itself — or, for a `T?`, the `T` under it — and
    /// else, for an implicit conversion, the one whose result every other
    /// result reaches by a standard conversion. With `operator int?(C)` and
    /// `operator long(C)` beside each other, a `long?` is the second and a
    /// `double?` is whichever result the other widens to. Where nothing
    /// stands out, the first one found stays.
    fn most_specific_target(&self, found: Vec<(SymbolId, Type)>, to: &Type) -> Option<SymbolId> {
        let inner = self.nullable_underlying(to);
        if let Some((operator, _)) = found
            .iter()
            .find(|(_, gives)| gives == to || inner.as_ref() == Some(gives))
        {
            return Some(*operator);
        }
        if found.len() > 1
            && let Some((operator, _)) = found.iter().find(|(_, gives)| {
                let bare = |ty: &Type| self.nullable_underlying(ty).unwrap_or_else(|| ty.clone());
                found.iter().all(|(_, other)| {
                    other == gives
                        || self.standard_after(&bare(other), &bare(gives), false)
                            && !self.standard_after(&bare(gives), &bare(other), false)
                })
            })
        {
            return Some(*operator);
        }
        found.first().map(|(operator, _)| *operator)
    }

    /// Whether an array converts to another by array covariance (§10.2.8),
    /// a standard implicit conversion that may lead into an operator:
    /// `string[][]` reaches `ReadOnlySpan<object[]>.op_Implicit(object[][])`.
    fn array_covariant(&self, from: &Type, to: &Type) -> bool {
        let symbols = self.compilation().symbols();
        match (from, to) {
            (
                Type::Array {
                    element: from_element,
                    rank: from_rank,
                },
                Type::Array {
                    element: to_element,
                    rank: to_rank,
                },
            ) if from_rank == to_rank => {
                from_element == to_element
                    || (from_element.is_reference_type(symbols)
                        && to_element.is_reference_type(symbols)
                        && (self.inherits_from(from_element, to_element, 0)
                            || self.array_covariant(from_element, to_element)))
            }
            _ => false,
        }
    }

    /// The construction of `definition` that `ty` is, if it is one.
    ///
    /// `List<int>` *is* an `IEnumerable<int>`, and that is the only way to
    /// learn what `TSource` is when the parameter says `IEnumerable<TSource>`
    /// and the argument says `List<int>`. C# calls it a lower-bound inference:
    /// look for the one base type or interface built from the same
    /// definition.
    #[must_use]
    pub fn constructed_from(&self, ty: &Type, definition: SymbolId) -> Option<Type> {
        self.constructed_from_at(ty, definition, 0)
    }

    fn constructed_from_at(&self, ty: &Type, definition: SymbolId, depth: usize) -> Option<Type> {
        self.constructed_through(ty, definition, depth, &mut Vec::new())
    }

    /// The walk behind [`Self::constructed_from_at`], which skips a type met
    /// again as [`Self::inherits_through`] does: the first construction
    /// found is the one a walk without skipping would find first.
    fn constructed_through(
        &self,
        ty: &Type,
        definition: SymbolId,
        depth: usize,
        seen: &mut Vec<(Type, usize)>,
    ) -> Option<Type> {
        if depth > 16 {
            return None;
        }
        if ty.symbol() == Some(definition) {
            return Some(ty.clone());
        }
        if !first_visit(seen, ty, depth) {
            return None;
        }
        self.direct_bases(ty)
            .iter()
            .find_map(|base| self.constructed_through(base, definition, depth + 1, seen))
    }

    /// What a *type* directly derives from and implements, with its own
    /// construction put through.
    ///
    /// A base type is declared in terms of the type's parameters: `List<T>`
    /// implements `IEnumerable<T>`, and what makes a `List<string>` an
    /// `IEnumerable<string>` is the substitution. The cases with no
    /// declaration behind them are here too — an array's interfaces, and the
    /// base every enum, struct and delegate has without writing one.
    #[must_use]
    pub fn direct_bases(&self, ty: &Type) -> Vec<Type> {
        if let Type::Array { element, rank } = ty {
            let mut bases = self.named("System.Array").into_iter().collect::<Vec<_>>();
            // Only a vector implements the generic collection interfaces; a
            // rectangular array is just an `Array`.
            if *rank == 1 {
                for name in [
                    "System.Collections.Generic.IList`1",
                    "System.Collections.Generic.ICollection`1",
                    "System.Collections.Generic.IEnumerable`1",
                    "System.Collections.Generic.IReadOnlyList`1",
                    "System.Collections.Generic.IReadOnlyCollection`1",
                ] {
                    if let Some(symbol) = self.compilation().type_by_metadata_name(name) {
                        bases.push(Type::Named {
                            symbol,
                            type_arguments: vec![element.as_ref().clone()],
                        });
                    }
                }
                if let Some(enumerable) = self.named("System.Collections.IEnumerable") {
                    bases.push(enumerable);
                }
            }
            return bases;
        }

        let Some(symbol) = ty.symbol() else {
            return Vec::new();
        };
        let substitution = self.type_substitution(ty);
        let mut bases: Vec<Type> = self
            .base_types_of(symbol)
            .iter()
            .map(|base| base.substitute(&substitution))
            .collect();

        // What the language gives a declaration that wrote no base at all.
        let symbols = self.compilation().symbols();
        let kind = symbols.get(symbol).type_kind();
        let implied = match kind {
            Some(TypeKind::Enum) => Some("System.Enum"),
            Some(TypeKind::Delegate) => Some("System.MulticastDelegate"),
            Some(TypeKind::Struct | TypeKind::RecordStruct) => Some("System.ValueType"),
            // A class that wrote no base derives from `System.Object`, and an
            // interface's members include its for the purpose of looking one
            // up: `IDisposable.ToString()` is a call anybody can write.
            _ => Some("System.Object"),
        };
        if let Some(implied) = implied
            && let Some(base) = self.named(implied)
            && base.symbol() != Some(symbol)
            && !bases.iter().any(|existing| {
                existing.symbol().is_some_and(|existing| {
                    symbols.get(existing).type_kind() != Some(TypeKind::Interface)
                })
            })
        {
            bases.push(base);
        }
        bases
    }

    /// A type by its metadata name, where the reference set has one.
    fn named(&self, name: &str) -> Option<Type> {
        self.compilation()
            .type_by_metadata_name(name)
            .map(Type::named)
    }

    /// The type an enum counts as: `int` unless the declaration said
    /// otherwise.
    ///
    /// An enum is a distinct type with the operators of the type underneath
    /// it, which is the whole point of `[Flags]`: `a | b` gives back the enum
    /// rather than the number it is stored as.
    #[must_use]
    pub fn enum_underlying(&self, ty: &Type) -> Option<Type> {
        let symbol = ty.symbol()?;
        let symbols = self.compilation().symbols();
        if symbols.get(symbol).type_kind() != Some(TypeKind::Enum) {
            return None;
        }
        if let Some(reference) = symbols
            .get(symbol)
            .as_named_type()
            .and_then(|detail| detail.enum_underlying)
        {
            let mut sink = Diagnostics::new();
            return Some(self.resolve_type_ref(reference, &mut sink));
        }
        // An enum out of metadata says what it is stored as with a field: the
        // instance one, which is called `value__` and is the enum's storage.
        if let Some(value) = symbols.lookup(symbol, "value__").first()
            && let Some(underlying) = self.compilation().metadata_type(*value)
        {
            return Some(underlying.clone());
        }
        self.compilation()
            .special_type(SpecialType::Int32)
            .map(Type::named)
    }

    /// Whether a type is `nint` or `nuint`, and which: the language gives
    /// them an integer's operators (C# 9), and the runtime spells them
    /// `IntPtr` and `UIntPtr`, which since C# 11 are the same types. Their
    /// own `<` is an explicit implementation of a generic-math interface,
    /// which no lookup by `op_LessThan` finds; the operators are built in.
    pub(crate) fn native_int(&self, ty: &Type) -> Option<bool> {
        let symbol = ty.symbol()?;
        match self.compilation().symbols().qualified_name(symbol).as_ref() {
            "System.IntPtr" => Some(false),
            "System.UIntPtr" => Some(true),
            _ => None,
        }
    }

    /// The type an operator works in where one operand is an `nint` or an
    /// `nuint`, found as the language does (§12.4.5): of the predefined
    /// operators, the ones both operands reach, and among those the one
    /// whose type reaches all the others. With nothing in the set that does,
    /// as for `nuint + long`, whose only candidates are `float`, `double` and
    /// `decimal`, there is no operator (an error, whether it is called
    /// ambiguous or not applicable).
    pub(crate) fn native_result(
        &self,
        left: &Type,
        right: &Type,
        integral_only: bool,
    ) -> Option<Type> {
        if self.native_int(left).is_none() && self.native_int(right).is_none() {
            return None;
        }
        let compilation = self.compilation();
        let named = |name: &str| compilation.type_by_metadata_name(name).map(Type::named);
        let special = |special| compilation.special_type(special).map(Type::named);
        let mut candidates = vec![
            named("System.IntPtr")?,
            named("System.UIntPtr")?,
            special(SpecialType::Int64)?,
            special(SpecialType::UInt64)?,
        ];
        if !integral_only {
            candidates.push(special(SpecialType::Single)?);
            candidates.push(special(SpecialType::Double)?);
            candidates.push(special(SpecialType::Decimal)?);
        }
        let applicable: Vec<&Type> = candidates
            .iter()
            .filter(|candidate| {
                self.converts_implicitly(left, candidate)
                    && self.converts_implicitly(right, candidate)
            })
            .collect();
        applicable
            .iter()
            .find(|best| {
                applicable
                    .iter()
                    .all(|other| ***best == **other || self.converts_implicitly(best, other))
            })
            .map(|best| (*best).clone())
    }

    /// Whether both sides are the same enum.
    fn same_enum(&self, left: &Type, right: &Type) -> bool {
        left == right && self.enum_underlying(left).is_some()
    }

    /// Whether spans are part of the language (C# 14): arrays, spans and
    /// strings convert to them implicitly, and overload resolution, type
    /// inference and extension receivers know it (Roslyn's
    /// `IDS_FeatureFirstClassSpan`).
    #[must_use]
    pub fn first_class_spans(&self) -> bool {
        self.compilation()
            .language_version()
            .at_least(rustlyn_syntax::LanguageVersion::CSharp14)
    }

    /// `Span<T>` or `ReadOnlySpan<T>`: whether it is the read-only one, and
    /// its `T`.
    #[must_use]
    pub fn span_parts(&self, ty: &Type) -> Option<(bool, Type)> {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return None;
        };
        let [element] = type_arguments.as_slice() else {
            return None;
        };
        let name = self.compilation().symbols().qualified_name(*symbol);
        match name.as_str() {
            "System.Span`1" => Some((false, element.clone())),
            "System.ReadOnlySpan`1" => Some((true, element.clone())),
            _ => None,
        }
    }

    /// Whether an implicit span conversion (C# 14, §10.2.1) takes `from`
    /// to `to`: an array to a `Span` of its element or a `ReadOnlySpan` of
    /// anything its element converts to by reference, a `Span` or
    /// `ReadOnlySpan` to a `ReadOnlySpan` the same way, and a `string` to a
    /// `ReadOnlySpan<char>`. It does not ask whether the language version
    /// has them: see [`Self::first_class_spans`].
    #[must_use]
    pub fn implicit_span_conversion(&self, from: &Type, to: &Type) -> bool {
        let Some((readonly, wanted)) = self.span_parts(to) else {
            return false;
        };
        // An identity or implicit reference conversion.
        let covariant = |given: &Type| {
            given == &wanted
                || (self.held_by_reference(given)
                    && self.held_by_reference(&wanted)
                    && self.converts_implicitly(given, &wanted))
        };
        match from {
            Type::Array { element, rank: 1 } => {
                if readonly {
                    covariant(element)
                } else {
                    **element == wanted
                }
            }
            _ => {
                if let Some((_, element)) = self.span_parts(from) {
                    return readonly && covariant(&element);
                }
                readonly
                    && self.special_of(from) == Some(SpecialType::String)
                    && self.special_of(&wanted) == Some(SpecialType::Char)
            }
        }
    }

    /// What a construction says its type's parameters are.
    /// Whether `ty` is `Span<element>` or `ReadOnlySpan<element>`.
    #[must_use]
    pub fn is_span_of(&self, ty: &Type, element: &Type) -> bool {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return false;
        };
        type_arguments.first() == Some(element)
            && ["System.Span`1", "System.ReadOnlySpan`1"]
                .into_iter()
                .filter_map(|name| self.compilation().type_by_metadata_name(name))
                .any(|span| span == *symbol)
    }

    #[must_use]
    pub fn type_substitution(&self, ty: &Type) -> std::collections::HashMap<SymbolId, Type> {
        // A tuple written `(int? blockBody, string arrowBody)` is a
        // `ValueTuple<int?, string>`, and its `Item2` is a `string` only
        // through that construction.
        if let Type::Tuple(elements) = ty {
            let name = format!("System.ValueTuple`{}", elements.len());
            let Some(symbol) = self.compilation().type_by_metadata_name(&name) else {
                return std::collections::HashMap::new();
            };
            let named = Type::Named {
                symbol,
                type_arguments: elements.iter().map(|element| element.ty.clone()).collect(),
            };
            return self.type_substitution(&named);
        }
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return std::collections::HashMap::new();
        };
        if type_arguments.is_empty() {
            return std::collections::HashMap::new();
        }
        self.compilation()
            .symbols()
            .get(*symbol)
            .as_named_type()
            .map(|detail| {
                detail
                    .type_parameters
                    .iter()
                    .copied()
                    .zip(type_arguments.iter().cloned())
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The `T` of a `Nullable<T>`.
    #[must_use]
    pub fn nullable_underlying(&self, ty: &Type) -> Option<Type> {
        let Type::Named {
            symbol,
            type_arguments,
        } = ty
        else {
            return None;
        };
        let nullable = self
            .compilation()
            .type_by_metadata_name("System.Nullable`1")?;
        (*symbol == nullable)
            .then(|| type_arguments.first().cloned())
            .flatten()
    }

    /// Whether `from` is `to`, or derives from it, or implements it.
    /// Whether `from` is `to`, derives from it, or implements it.
    #[must_use]
    pub fn inherits_from_public(&self, from: &Type, to: &Type) -> bool {
        let key = (from.clone(), to.clone());
        if let Some(answer) = self.compilation().cached_inheritance(&key) {
            return answer;
        }
        let answer = self.inherits_from(from, to, 0);
        self.compilation().cache_inheritance(key, answer);
        answer
    }

    fn inherits_from(&self, from: &Type, to: &Type, depth: usize) -> bool {
        self.inherits_through(from, to, depth, &mut Vec::new())
    }

    /// The walk behind [`Self::inherits_from`], remembering how deep each
    /// type was met. Interfaces make diamonds — a `List<T>` reaches
    /// `IEnumerable<T>` along four paths — and a type met again no shallower
    /// than before has nothing new to say: its walk from there was already
    /// made, with at least as much depth left, and found nothing.
    fn inherits_through(
        &self,
        from: &Type,
        to: &Type,
        depth: usize,
        seen: &mut Vec<(Type, usize)>,
    ) -> bool {
        if depth > 16 {
            return false;
        }
        if from == to {
            return true;
        }
        if !first_visit(seen, from, depth) {
            return false;
        }
        self.direct_bases(from)
            .iter()
            .any(|base| self.inherits_through(base, to, depth + 1, seen))
    }

    /// The type `left op right` produces, or `None` when the operator does not
    /// apply.
    #[must_use]
    /// The delegate type `d1 + d2` and `d1 - d2` give where both are of it,
    /// or one side is `null` (§12.10.5, §12.10.6).
    fn delegate_combination(&self, left: &Type, right: &Type) -> Option<Type> {
        let symbols = self.compilation().symbols();
        let is_delegate = |ty: &Type| {
            ty.symbol()
                .is_some_and(|symbol| symbols.get(symbol).type_kind() == Some(TypeKind::Delegate))
        };
        match (is_delegate(left), is_delegate(right)) {
            (true, true) if left == right => Some(left.clone()),
            (true, false) if matches!(right, Type::Null) => Some(left.clone()),
            (false, true) if matches!(left, Type::Null) => Some(right.clone()),
            _ => None,
        }
    }

    pub fn binary_result(
        &self,
        operator: BinaryOperator,
        left: &Type,
        right: &Type,
    ) -> Option<Type> {
        // `a ?? throw ...` is asked first: a `throw` produces nothing and so
        // has no type, and the guard below would make the whole thing an
        // error rather than the `a` it is.
        if operator == BinaryOperator::Coalesce && !left.is_error() {
            return Some(match self.nullable_underlying(left) {
                Some(underlying) => underlying,
                None if right.is_error() || matches!(right, Type::Null) => left.clone(),
                None => right.clone(),
            });
        }
        if left.is_error() || right.is_error() {
            return Some(Type::Error);
        }

        let boolean = || {
            self.compilation()
                .special_type(SpecialType::Boolean)
                .map_or(Type::Error, Type::named)
        };

        match operator {
            BinaryOperator::LogicalAnd | BinaryOperator::LogicalOr => Some(boolean()),
            BinaryOperator::Equality | BinaryOperator::Inequality => {
                // Two numbers meet in a predefined `==`, which for an `nint`
                // or an `nuint` there is not always one of: `n == 1UL`.
                let number = |ty: &Type| {
                    self.native_int(ty).is_some()
                        || self.special_of(ty).is_some_and(SpecialType::is_numeric)
                };
                if (self.native_int(left).is_some() || self.native_int(right).is_some())
                    && number(left)
                    && number(right)
                    && self.native_result(left, right, false).is_none()
                {
                    return None;
                }
                Some(boolean())
            }
            BinaryOperator::LessThan
            | BinaryOperator::GreaterThan
            | BinaryOperator::LessThanOrEqual
            | BinaryOperator::GreaterThanOrEqual => {
                if self.same_enum(left, right) || self.native_result(left, right, false).is_some() {
                    return Some(boolean());
                }
                // Two pointers compare as the addresses they are (§23.6.8),
                // and a function pointer is one, reaching `void*`.
                if matches!(left, Type::Pointer(_) | Type::FunctionPointer(_))
                    && matches!(right, Type::Pointer(_) | Type::FunctionPointer(_))
                {
                    return Some(boolean());
                }
                let (left, right) = (self.special_of(left)?, self.special_of(right)?);
                (left.is_numeric() && right.is_numeric()).then(boolean)
            }
            BinaryOperator::Add => {
                // `p + n` walks the pointer along by `n` elements, and so does
                // `n + p`; the result is the pointer.
                if let Some(result) = self.pointer_offset(left, right) {
                    return Some(result);
                }
                // `+` is also string concatenation, and a string on either side
                // is enough.
                let string = self.compilation().special_type(SpecialType::String);
                if left.symbol() == string || right.symbol() == string {
                    return Some(string.map_or(Type::Error, Type::named));
                }
                // `o + null` on an `object` is `object + string`: the
                // `null` becomes the string, and the result is one.
                let symbols = self.compilation().symbols();
                let reference = |ty: &Type| {
                    !matches!(ty, Type::Null | Type::TypeParameter(_) | Type::Pointer(_))
                        && ty.is_reference_type(symbols)
                        && ty.symbol().is_none_or(|symbol| {
                            symbols.get(symbol).type_kind() != Some(TypeKind::Delegate)
                        })
                };
                if (matches!(left, Type::Null) && reference(right))
                    || (matches!(right, Type::Null) && reference(left))
                {
                    return Some(string.map_or(Type::Error, Type::named));
                }
                // `E + 1` is an `E`; two enums cannot be added at all.
                if let Some(result) = self.enum_arithmetic(left, right) {
                    return Some(result);
                }
                // `d1 + d2` combines two delegates of one type (§12.10.5).
                if let Some(result) = self.delegate_combination(left, right) {
                    return Some(result);
                }
                self.numeric_result(left, right, false)
            }
            BinaryOperator::Subtract => {
                // `d1 - d2` takes one delegate's invocations out of another's.
                if let Some(result) = self.delegate_combination(left, right) {
                    return Some(result);
                }
                // `p - q` is how many elements apart they are, which the
                // language says is a `long`.
                if let (Type::Pointer(_), Type::Pointer(_)) = (left, right) {
                    return self
                        .compilation()
                        .special_type(SpecialType::Int64)
                        .map(Type::named);
                }
                if let Some(result) = self.pointer_offset(left, right) {
                    return Some(result);
                }
                // `E - E` is the number between them; `E - 1` is an `E`.
                if self.same_enum(left, right) {
                    return self.enum_underlying(left);
                }
                if let Some(result) = self.enum_arithmetic(left, right) {
                    return Some(result);
                }
                self.numeric_result(left, right, false)
            }
            BinaryOperator::Multiply | BinaryOperator::Divide | BinaryOperator::Modulo => {
                self.numeric_result(left, right, false)
            }
            BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseOr
            | BinaryOperator::ExclusiveOr => {
                if self.special_of(left) == Some(SpecialType::Boolean)
                    && self.special_of(right) == Some(SpecialType::Boolean)
                {
                    return Some(boolean());
                }
                // `a | b` on one enum gives back that enum, which is what
                // makes a set of flags a type rather than an int.
                if self.same_enum(left, right) {
                    return Some(left.clone());
                }
                self.numeric_result(left, right, true)
            }
            BinaryOperator::LeftShift
            | BinaryOperator::RightShift
            | BinaryOperator::UnsignedRightShift => {
                // `n << 1` on an `nint` stays an `nint`; the count is what
                // reaches an `int`, so `n << 1u` and `n << m` are errors.
                if self.native_int(left).is_some() {
                    let int = self.compilation().special_type(SpecialType::Int32)?;
                    return self
                        .converts_implicitly(right, &Type::named(int))
                        .then(|| left.clone());
                }
                if self.native_int(right).is_some() {
                    return None;
                }
                let left_special = self.special_of(left)?;
                left_special
                    .is_numeric()
                    .then(|| promote_shift(left_special))
                    .and_then(|special| self.compilation().special_type(special))
                    .map(Type::named)
            }
            // Handled above, before the guard that turns an error operand
            // into an error result.
            BinaryOperator::Coalesce => Some(right.clone()),
        }
    }

    /// The types a tuple holds, however it was spelled.
    ///
    /// `(int, string)` and `ValueTuple<int, string>` are one type with two
    /// spellings, and a signature read out of metadata only ever uses the
    /// second.
    /// A type with every `ValueTuple<...>` in it spelled as the tuple it is,
    /// so that `ArrayBuilder<ValueTuple<A, B>>` and `ArrayBuilder<(A, B)>`
    /// compare equal: they are one type with two spellings, and element
    /// names are not part of it (§8.3.11).
    fn canonical(&self, ty: &Type) -> Type {
        match ty {
            Type::Tuple(elements) => Type::Tuple(
                elements
                    .iter()
                    .map(|element| crate::types::TupleElement {
                        name: None,
                        ty: self.canonical(&element.ty),
                    })
                    .collect(),
            ),
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let arguments: Vec<Type> = type_arguments
                    .iter()
                    .map(|argument| self.canonical(argument))
                    .collect();
                if !arguments.is_empty()
                    && self
                        .compilation()
                        .symbols()
                        .qualified_name(*symbol)
                        .starts_with("System.ValueTuple`")
                {
                    return Type::Tuple(
                        arguments
                            .into_iter()
                            .map(|ty| crate::types::TupleElement { name: None, ty })
                            .collect(),
                    );
                }
                Type::Named {
                    symbol: *symbol,
                    type_arguments: arguments,
                }
            }
            Type::Array { element, rank } => Type::Array {
                element: Box::new(self.canonical(element)),
                rank: *rank,
            },
            Type::Pointer(element) => Type::Pointer(Box::new(self.canonical(element))),
            Type::ByRef(element) => Type::ByRef(Box::new(self.canonical(element))),
            other => other.clone(),
        }
    }

    #[must_use]
    pub fn tuple_elements(&self, ty: &Type) -> Option<Vec<Type>> {
        match ty {
            Type::Tuple(elements) => {
                Some(elements.iter().map(|element| element.ty.clone()).collect())
            }
            Type::Named {
                symbol,
                type_arguments,
            } if self
                .compilation()
                .symbols()
                .qualified_name(*symbol)
                .starts_with("System.ValueTuple`") =>
            {
                // Past seven the rest nest, and a `ValueTuple<…, ValueTuple<…>>`
                // has the elements of both.
                let mut elements = type_arguments.clone();
                if elements.len() == 8
                    && let Some(rest) = elements.pop()
                {
                    match self.tuple_elements(&rest) {
                        Some(more) => elements.extend(more),
                        None => elements.push(rest),
                    }
                }
                Some(elements)
            }
            _ => None,
        }
    }

    /// The `ValueTuple<…>` a tuple type is, nested past seven elements.
    #[must_use]
    pub fn value_tuple_of(&self, elements: &[Type]) -> Option<Type> {
        let (head, rest) = if elements.len() > 7 {
            (&elements[..7], Some(self.value_tuple_of(&elements[7..])?))
        } else {
            (elements, None)
        };
        let symbol = self.compilation().type_by_metadata_name(&format!(
            "System.ValueTuple`{}",
            head.len() + usize::from(rest.is_some())
        ))?;
        Some(Type::Named {
            symbol,
            type_arguments: head.iter().cloned().chain(rest).collect(),
        })
    }

    /// `p + n` and `n + p`, which give back the pointer.
    ///
    /// The offset is counted in elements rather than bytes, so the pointer
    /// keeps the type it had: that is the whole reason `byte*` and `ulong*`
    /// are different types.
    fn pointer_offset(&self, left: &Type, right: &Type) -> Option<Type> {
        let (pointer, other) = match (left, right) {
            (Type::Pointer(_), Type::Pointer(_)) => return None,
            (Type::Pointer(_), other) => (left, other),
            (other, Type::Pointer(_)) => (right, other),
            _ => return None,
        };
        // A native integer is an offset as a `long` or a `ulong` is, which
        // it converts to.
        if self.native_int(other).is_some() {
            return Some(pointer.clone());
        }
        self.special_of(other)?
            .is_numeric()
            .then(|| pointer.clone())
    }

    /// `E + n` and `n + E`, which give back the enum.
    fn enum_arithmetic(&self, left: &Type, right: &Type) -> Option<Type> {
        let (enumeration, other) = match (self.enum_underlying(left), self.enum_underlying(right)) {
            (Some(_), Some(_)) | (None, None) => return None,
            (Some(_), None) => (left, right),
            (None, Some(_)) => (right, left),
        };
        self.special_of(other)?
            .is_numeric()
            .then(|| enumeration.clone())
    }

    /// The type an arithmetic operator produces, following the promotions in
    /// §12.4.7: both operands move up to the wider type.
    fn numeric_result(&self, left: &Type, right: &Type, integral_only: bool) -> Option<Type> {
        if let Some(native) = self.native_result(left, right, integral_only) {
            return Some(native);
        }
        if self.native_int(left).is_some() || self.native_int(right).is_some() {
            return None;
        }
        let (left, right) = (self.special_of(left)?, self.special_of(right)?);
        if !left.is_numeric() || !right.is_numeric() {
            return None;
        }
        let promoted = promote(left, right)?;
        self.compilation().special_type(promoted).map(Type::named)
    }

    /// Whether a type can be the condition of an `if` or `while`.
    #[must_use]
    pub fn is_boolean(&self, ty: &Type) -> bool {
        ty.is_error() || self.special_of(ty) == Some(SpecialType::Boolean)
    }
}

/// The binary operators that have a result type worth computing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    LeftShift,
    RightShift,
    /// `>>>`, which shifts the bits and never the sign.
    UnsignedRightShift,
    BitwiseAnd,
    BitwiseOr,
    ExclusiveOr,
    LogicalAnd,
    LogicalOr,
    Equality,
    Inequality,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Coalesce,
}

/// Whether `dynamic` appears anywhere in a type.
pub(crate) fn contains_dynamic(ty: &Type) -> bool {
    match ty {
        Type::Dynamic => true,
        Type::Named { type_arguments, .. } => type_arguments.iter().any(contains_dynamic),
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            contains_dynamic(element)
        }
        Type::Tuple(elements) => elements.iter().any(|element| contains_dynamic(&element.ty)),
        Type::FunctionPointer(pointer) => pointer.types().any(contains_dynamic),
        Type::Error | Type::Null | Type::Void | Type::TypeParameter(_) => false,
    }
}

/// A type with `object` wherever it says `dynamic`, which is the type the
/// runtime sees.
pub(crate) fn erase_dynamic(ty: &Type, object: &Type) -> Type {
    match ty {
        Type::Dynamic => object.clone(),
        Type::Named {
            symbol,
            type_arguments,
        } => Type::Named {
            symbol: *symbol,
            type_arguments: type_arguments
                .iter()
                .map(|argument| erase_dynamic(argument, object))
                .collect(),
        },
        Type::Array { element, rank } => Type::Array {
            element: Box::new(erase_dynamic(element, object)),
            rank: *rank,
        },
        Type::Pointer(element) => Type::Pointer(Box::new(erase_dynamic(element, object))),
        Type::ByRef(element) => Type::ByRef(Box::new(erase_dynamic(element, object))),
        Type::FunctionPointer(pointer) => {
            Type::FunctionPointer(Box::new(pointer.map(|ty| erase_dynamic(ty, object))))
        }
        Type::Tuple(elements) => Type::Tuple(
            elements
                .iter()
                .map(|element| crate::types::TupleElement {
                    name: element.name.clone(),
                    ty: erase_dynamic(&element.ty, object),
                })
                .collect(),
        ),
        other => other.clone(),
    }
}

/// The implicit numeric conversions of §10.2.3.
fn implicit_numeric(from: SpecialType, to: SpecialType) -> bool {
    use SpecialType::{
        Byte, Char, Decimal, Double, Int16, Int32, Int64, SByte, Single, UInt16, UInt32, UInt64,
    };
    let widens_to: &[SpecialType] = match from {
        SByte => &[Int16, Int32, Int64, Single, Double, Decimal],
        Byte => &[
            Int16, UInt16, Int32, UInt32, Int64, UInt64, Single, Double, Decimal,
        ],
        Int16 => &[Int32, Int64, Single, Double, Decimal],
        UInt16 => &[Int32, UInt32, Int64, UInt64, Single, Double, Decimal],
        Int32 => &[Int64, Single, Double, Decimal],
        UInt32 => &[Int64, UInt64, Single, Double, Decimal],
        Int64 | UInt64 => &[Single, Double, Decimal],
        Char => &[
            UInt16, Int32, UInt32, Int64, UInt64, Single, Double, Decimal,
        ],
        Single => &[Double],
        _ => &[],
    };
    widens_to.contains(&to)
}

/// The wider of two numeric types, which both operands convert to.
fn promote(left: SpecialType, right: SpecialType) -> Option<SpecialType> {
    use SpecialType::{Decimal, Double, Int32, Int64, Single, UInt32, UInt64};
    let ladder = [Decimal, Double, Single, UInt64, Int64, UInt32];
    for wide in ladder {
        if left == wide || right == wide {
            // `uint` and a signed type meet at `long`, since neither holds the
            // other's range.
            if wide == UInt32 && (is_signed(left) || is_signed(right)) {
                return Some(Int64);
            }
            if wide == UInt64 && (is_signed(left) || is_signed(right)) {
                // No integer type holds both, and the specification makes this
                // an error rather than a promotion to float.
                return (left == UInt64 && right == UInt64).then_some(UInt64);
            }
            return Some(wide);
        }
    }
    // Everything narrower than `int` is computed as `int`.
    Some(Int32)
}

/// The type a shift produces, which depends only on its left operand.
const fn promote_shift(left: SpecialType) -> SpecialType {
    match left {
        SpecialType::Int64 | SpecialType::UInt64 | SpecialType::UInt32 => left,
        _ => SpecialType::Int32,
    }
}

const fn is_signed(special: SpecialType) -> bool {
    matches!(
        special,
        SpecialType::SByte | SpecialType::Int16 | SpecialType::Int32 | SpecialType::Int64
    )
}

/// Whether a walk over base types should go on from `ty`, met at `depth`:
/// not if it was met before at a depth no greater, since the walk from there
/// already covered everything this one could reach.
fn first_visit(seen: &mut Vec<(Type, usize)>, ty: &Type, depth: usize) -> bool {
    match seen.iter_mut().find(|(met, _)| met == ty) {
        Some((_, at)) if *at <= depth => false,
        Some((_, at)) => {
            *at = depth;
            true
        }
        None => {
            seen.push((ty.clone(), depth));
            true
        }
    }
}
