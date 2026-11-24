//! What `[Nullable]` says of a declared type: a byte for each place in it
//! that could hold a reference, in the order Roslyn's `AddNullableTransforms`
//! walks them.
//!
//! A place is `0` where the declaration is oblivious to nullability (no
//! `#nullable enable`) or the type there is a value type, `2` where it was
//! written with a `?`, and `1` otherwise. A value type that is not generic
//! takes no place at all, and neither does `Nullable<T>`, whose `T` does.
//! The type of a nested type's outer type's arguments come before its own,
//! an array's own place before its element's.
//!
//! The semantic model keeps no annotations: a `string?` is a `string` there.
//! They are read back off the syntax the declaration wrote, walked in step
//! with the type it resolved to; where there is no syntax, or it does not
//! line up (an alias, a type argument implied by an enclosing generic), a
//! place gets what its context gives an unwritten one.

use rustlyn_semantics::{Compilation, NullableContexts, Type, TypeKind, TypeSyntaxRef};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use crate::emitter::Emitter;

/// The `#nullable` directives of each tree of a compilation, read only
/// where a tree has any.
pub(crate) fn contexts_of(compilation: &Compilation) -> Vec<Option<NullableContexts>> {
    compilation
        .trees()
        .iter()
        .map(|tree| {
            tree.source()
                .text()
                .contains("#nullable")
                .then(|| NullableContexts::of(&tree.root()))
        })
        .collect()
}

/// Oblivious: written where annotations are off, or a value type.
pub(crate) const OBLIVIOUS: u8 = 0;
/// A reference that is not null.
pub(crate) const NOT_ANNOTATED: u8 = 1;
/// A reference that may be null: `string?`.
pub(crate) const ANNOTATED: u8 = 2;

/// Where in the syntax a place of the type is written: a node, or an array
/// type with some of its rank specifiers already walked.
#[derive(Clone)]
enum Written {
    Node(SyntaxNode),
    Ranks(SyntaxNode, usize),
    /// A type argument nothing wrote, implied by the enclosing generic type
    /// a nested one is named from inside: `T` in `Inner` for
    /// `Outer<T>.Inner`, which is oblivious.
    Implied,
}

impl Emitter<'_> {
    /// Whether annotations are on at a position of a tree.
    pub(crate) fn annotations_at(&self, tree: usize, position: u32) -> bool {
        let default = self.compilation.options().nullable_annotations;
        match self.nullable_contexts.get(tree) {
            Some(Some(contexts)) => contexts.annotations_at(position, default),
            _ => default,
        }
    }

    /// The places of a type a declaration wrote, read off the syntax it
    /// wrote it with; one written nowhere is oblivious.
    pub(crate) fn declared_flags(&self, ty: &Type, written: Option<&TypeSyntaxRef>) -> Vec<u8> {
        let Some(TypeSyntaxRef(location)) = written else {
            return self.nullable_flags(ty, None, false);
        };
        let node = self
            .compilation
            .trees()
            .get(location.tree)
            .and_then(|tree| tree.root().find_node(location.span));
        let enabled = self.annotations_at(location.tree, location.span.start());
        self.nullable_flags(ty, node.as_ref(), enabled)
    }

    /// The places of a type as `syntax` writes it, where annotations are on
    /// or not as `enabled` says.
    pub(crate) fn nullable_flags(
        &self,
        ty: &Type,
        syntax: Option<&SyntaxNode>,
        enabled: bool,
    ) -> Vec<u8> {
        let mut flags = Vec::new();
        self.flags_into(ty, syntax.cloned().map(Written::Node), enabled, &mut flags);
        flags
    }

    fn flags_into(&self, ty: &Type, written: Option<Written>, enabled: bool, out: &mut Vec<u8>) {
        let (written, enabled) = match written {
            Some(Written::Implied) => (None, false),
            other => (other, enabled),
        };
        let ty = match ty {
            Type::ByRef(inner) => inner.as_ref(),
            other => other,
        };
        // `ref T` and `scoped T` are no places of their own.
        let mut written = written;
        while let Some(Written::Node(node)) = &written
            && matches!(node.kind(), SyntaxKind::RefType | SyntaxKind::ScopedType)
        {
            written = type_child(node).map(Written::Node);
        }
        let nullable_value = self.nullable_underlying(ty);
        let mut annotated = false;
        if let Some(Written::Node(node)) = &written
            && node.kind() == SyntaxKind::NullableType
            && nullable_value.is_none()
        {
            annotated = true;
            written = type_child(node).map(Written::Node);
        }
        // A `?` annotates a reference type wherever it is written — outside
        // `#nullable enable` too, where csc warns and still records it.
        let flag = |value_type: bool| {
            if value_type {
                OBLIVIOUS
            } else if annotated {
                ANNOTATED
            } else if enabled {
                NOT_ANNOTATED
            } else {
                OBLIVIOUS
            }
        };
        match ty {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let value_type = self.is_value_type_symbol(*symbol);
                // `IsNonGenericValueType`: a generic value type takes a
                // place unless it is `Nullable<T>`.
                let placeless = if type_arguments.is_empty() {
                    value_type
                } else {
                    nullable_value.is_some()
                };
                if !placeless {
                    out.push(flag(value_type));
                }
                let arguments = match (&nullable_value, &written) {
                    // `int?` writes its `int` inside the `?`.
                    (Some(_), Some(Written::Node(node)))
                        if node.kind() == SyntaxKind::NullableType =>
                    {
                        vec![type_child(node).map(Written::Node)]
                    }
                    _ => aligned_arguments(written.as_ref(), type_arguments.len()),
                };
                for (argument, written) in type_arguments.iter().zip(arguments) {
                    self.flags_into(argument, written, enabled, out);
                }
            }
            Type::Tuple(elements) => {
                let written: Vec<Option<Written>> = match &written {
                    Some(Written::Node(node)) if node.kind() == SyntaxKind::TupleType => {
                        let elements: Vec<Option<Written>> = node
                            .children()
                            .filter(|child| child.kind() == SyntaxKind::TupleElement)
                            .map(|element| type_child(&element).map(Written::Node))
                            .collect();
                        if elements.len() == ty_len(ty) {
                            elements
                        } else {
                            vec![None; ty_len(ty)]
                        }
                    }
                    _ => vec![None; elements.len()],
                };
                let types: Vec<&Type> = elements.iter().map(|element| &element.ty).collect();
                self.tuple_flags_into(&types, written, enabled, out);
            }
            Type::Array { element, .. } => {
                out.push(flag(false));
                let inner = match written {
                    Some(Written::Node(node)) if node.kind() == SyntaxKind::ArrayType => {
                        element_written(&node, 0)
                    }
                    Some(Written::Ranks(node, walked)) => element_written(&node, walked),
                    _ => None,
                };
                self.flags_into(element, inner, enabled, out);
            }
            // A pointer is a value to Roslyn: its place is oblivious.
            Type::Pointer(pointee) => {
                out.push(OBLIVIOUS);
                let inner = match &written {
                    Some(Written::Node(node)) if node.kind() == SyntaxKind::PointerType => {
                        type_child(node).map(Written::Node)
                    }
                    _ => None,
                };
                self.flags_into(pointee, inner, enabled, out);
            }
            Type::FunctionPointer(pointer) => {
                out.push(OBLIVIOUS);
                let parameters: Vec<Option<Written>> = match &written {
                    Some(Written::Node(node)) if node.kind() == SyntaxKind::FunctionPointerType => {
                        node.descendants()
                            .filter(|child| child.kind() == SyntaxKind::FunctionPointerParameter)
                            .map(|parameter| type_child(&parameter).map(Written::Node))
                            .collect()
                    }
                    _ => Vec::new(),
                };
                // The return is written last and walked first.
                let count = pointer.parameters.len() + 1;
                let at = |index: usize| {
                    (parameters.len() == count)
                        .then(|| parameters[index].clone())
                        .flatten()
                };
                self.flags_into(&pointer.returns, at(count - 1), enabled, out);
                for (index, (_, parameter)) in pointer.parameters.iter().enumerate() {
                    self.flags_into(parameter, at(index), enabled, out);
                }
            }
            Type::TypeParameter(parameter) => {
                let value_type = self
                    .compilation
                    .symbols()
                    .get(*parameter)
                    .as_type_parameter()
                    .is_some_and(|detail| detail.value_type);
                out.push(flag(value_type));
            }
            Type::Dynamic => out.push(flag(false)),
            Type::Void | Type::Error | Type::Null | Type::ByRef(_) => {}
        }
    }

    /// A tuple is a `ValueTuple`: a generic struct, so a place of its own,
    /// then its first seven elements, then the rest as the eighth argument.
    fn tuple_flags_into(
        &self,
        types: &[&Type],
        written: Vec<Option<Written>>,
        enabled: bool,
        out: &mut Vec<u8>,
    ) {
        out.push(OBLIVIOUS);
        let here = types.len().min(7);
        for (ty, written) in types[..here].iter().zip(written.iter().cloned()) {
            self.flags_into(ty, written, enabled, out);
        }
        if types.len() > 7 {
            self.tuple_flags_into(&types[7..], written[7..].to_vec(), enabled, out);
        }
    }
}

fn ty_len(ty: &Type) -> usize {
    match ty {
        Type::Tuple(elements) => elements.len(),
        _ => 0,
    }
}

/// The type a wrapper node — `T?`, `T*`, `ref T`, a parameter, a tuple
/// element — writes inside it.
pub(crate) fn type_child(node: &SyntaxNode) -> Option<SyntaxNode> {
    node.children()
        .find(|child| child.kind().is_type_node() && child.kind() != SyntaxKind::ArrayRankSpecifier)
}

/// The element of an array type whose first `walked` rank specifiers have
/// been walked: the same node with one more walked, or its element type
/// once none are left.
fn element_written(node: &SyntaxNode, walked: usize) -> Option<Written> {
    let ranks = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::ArrayRankSpecifier)
        .count();
    if walked + 1 < ranks {
        Some(Written::Ranks(node.clone(), walked + 1))
    } else {
        type_child(node).map(Written::Node)
    }
}

/// The type arguments a name writes, one per argument of the type it
/// resolved to: every generic part of a qualified name, left to right, and
/// nothing for arguments it leaves implied — an enclosing generic type's,
/// which come first.
fn aligned_arguments(written: Option<&Written>, count: usize) -> Vec<Option<Written>> {
    let mut found = Vec::new();
    if let Some(Written::Node(node)) = written {
        collect_arguments(node, &mut found);
    }
    if found.len() > count {
        return vec![None; count];
    }
    // A name that writes fewer arguments than its type has leaves the
    // enclosing type's implied; with no name at all there is nothing to go
    // by.
    let implied = written.map(|_| Written::Implied);
    let mut aligned: Vec<Option<Written>> = vec![implied; count - found.len()];
    aligned.extend(found.into_iter().map(|node| Some(Written::Node(node))));
    aligned
}

fn collect_arguments(node: &SyntaxNode, found: &mut Vec<SyntaxNode>) {
    match node.kind() {
        SyntaxKind::QualifiedName | SyntaxKind::AliasQualifiedName => {
            for child in node.children() {
                collect_arguments(&child, found);
            }
        }
        SyntaxKind::GenericName => {
            if let Some(list) = node.child_of_kind(SyntaxKind::TypeArgumentList) {
                found.extend(list.children().filter(|child| child.kind().is_type_node()));
            }
        }
        _ => {}
    }
}

/// Roslyn's `MostCommonNullableValueBuilder`: how many of a scope's members
/// are oblivious, not annotated and annotated, each counted only where all
/// its places agree.
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct MostCommon {
    counts: [usize; 3],
}

impl MostCommon {
    /// A member whose type has these places.
    pub(crate) fn add_flags(&mut self, flags: &[u8]) {
        self.add(common_value(flags));
    }

    /// A member that says one value for all of itself, or none.
    pub(crate) fn add(&mut self, value: Option<u8>) {
        if let Some(value) = value {
            self.counts[usize::from(value.min(2))] += 1;
        }
    }

    /// The value most members agree on: annotated only where it beats both
    /// others, not annotated where it beats oblivious, and none where
    /// nothing was counted.
    pub(crate) fn value(&self) -> Option<u8> {
        let [oblivious, not_annotated, annotated] = self.counts;
        let (max, value) = if not_annotated > oblivious {
            (not_annotated, NOT_ANNOTATED)
        } else {
            (oblivious, OBLIVIOUS)
        };
        if annotated > max {
            return Some(ANNOTATED);
        }
        (max != 0).then_some(value)
    }
}

/// The one value all places have, where they agree; none for no places.
pub(crate) fn common_value(flags: &[u8]) -> Option<u8> {
    let (first, rest) = flags.split_first()?;
    rest.iter().all(|flag| flag == first).then_some(*first)
}

impl Emitter<'_> {
    /// Whether the references define the attributes nullable metadata is
    /// written with, as the framework does from .NET 8 on (older ones have
    /// the compiler embed its own, which this one does not).
    pub(crate) fn nullable_attributes_available(&self) -> bool {
        [
            "System.Runtime.CompilerServices.NullableAttribute",
            "System.Runtime.CompilerServices.NullableContextAttribute",
        ]
        .iter()
        .all(|name| self.compilation.type_by_metadata_name(name).is_some())
    }

    /// `[Nullable]` on a row for a type with these places, where the
    /// scope's context does not say it already (Roslyn's
    /// `SynthesizeNullableAttributeIfNecessary`): one byte where the places
    /// agree, all of them where they do not.
    pub(crate) fn mark_nullable(&mut self, parent: u32, flags: &[u8], context: Option<u8>) {
        if flags.is_empty() {
            return;
        }
        let byte = crate::signature::SigType::Primitive(crate::signature::ElementType::U1);
        let (argument, value) = match common_value(flags) {
            Some(value) => {
                if Some(value) == context || (context.is_none() && value == OBLIVIOUS) {
                    return;
                }
                (byte, vec![value])
            }
            None => {
                let mut value = (flags.len() as u32).to_le_bytes().to_vec();
                value.extend_from_slice(flags);
                (crate::signature::SigType::Array(Box::new(byte)), value)
            }
        };
        self.mark_with_argument(
            parent,
            "System.Runtime.CompilerServices.NullableAttribute",
            argument,
            &value,
        );
    }

    /// `[NullableContext(value)]` on a type's or a method's row.
    pub(crate) fn mark_nullable_context(&mut self, parent: u32, value: u8) {
        let byte = crate::signature::SigType::Primitive(crate::signature::ElementType::U1);
        self.mark_with_argument(
            parent,
            "System.Runtime.CompilerServices.NullableContextAttribute",
            byte,
            &[value],
        );
    }

    /// An attribute whose constructor takes one argument, already encoded.
    fn mark_with_argument(
        &mut self,
        parent: u32,
        qualified_type: &str,
        argument: crate::signature::SigType,
        encoded: &[u8],
    ) {
        let void = crate::signature::SigType::Primitive(crate::signature::ElementType::Void);
        let constructor = self.references.member_ref(
            &mut self.metadata,
            qualified_type,
            ".ctor",
            &crate::signature::method_signature(true, &void, &[argument]),
        );
        let mut blob = vec![0x01, 0x00];
        blob.extend_from_slice(encoded);
        blob.extend_from_slice(&[0x00, 0x00]);
        // A `CustomAttributeType` tagged 3 is a `MemberRef`.
        self.metadata
            .add_custom_attribute(parent, ((constructor.0 & 0x00FF_FFFF) << 3) | 3, &blob);
    }
}

impl Emitter<'_> {
    /// What `[Nullable]` says of a type parameter itself (Roslyn's
    /// `GetSynthesizedNullableAttributeValue`): `class` is not annotated and
    /// `class?` annotated, where annotations are on at the constraint;
    /// `notnull` is not annotated; one with no constraint at all, declared
    /// where annotations are on, may be null. Anything else — `struct`,
    /// a constraint type — is oblivious: the constraint types say the rest.
    pub(crate) fn type_parameter_nullable_value(
        &self,
        parameter: rustlyn_semantics::SymbolId,
    ) -> u8 {
        let symbols = self.compilation.symbols();
        let Some(detail) = symbols.get(parameter).as_type_parameter() else {
            return OBLIVIOUS;
        };
        let Some(location) = symbols.get(parameter).locations.first().copied() else {
            return OBLIVIOUS;
        };
        let clause = self.constraint_clause(parameter);
        if detail.reference_type {
            let class = clause.as_ref().and_then(|clause| {
                clause
                    .children()
                    .find(|constraint| constraint.kind() == SyntaxKind::ClassConstraint)
            });
            let Some(class) = class else {
                return OBLIVIOUS;
            };
            if class
                .child_tokens()
                .any(|token| token.kind() == SyntaxKind::QuestionToken)
            {
                return ANNOTATED;
            }
            return if self.annotations_at(location.tree, class.span().start()) {
                NOT_ANNOTATED
            } else {
                OBLIVIOUS
            };
        }
        let not_null = detail.constraints.iter().any(|constraint| {
            self.compilation
                .trees()
                .get(constraint.0.tree)
                .and_then(|tree| tree.root().find_node(constraint.0.span))
                .is_some_and(|node| {
                    node.kind() == SyntaxKind::IdentifierName && node.text().trim() == "notnull"
                })
        });
        if not_null {
            return NOT_ANNOTATED;
        }
        if !detail.value_type
            && detail.constraints.is_empty()
            && self.annotations_at(location.tree, location.span.start())
        {
            return ANNOTATED;
        }
        OBLIVIOUS
    }

    /// The `where` clause that constrains a type parameter, where one does.
    fn constraint_clause(&self, parameter: rustlyn_semantics::SymbolId) -> Option<SyntaxNode> {
        let symbols = self.compilation.symbols();
        let name = &symbols.get(parameter).name;
        let location = symbols.get(parameter).locations.first().copied()?;
        let node = self
            .compilation
            .trees()
            .get(location.tree)?
            .root()
            .find_node(location.span)?;
        // The parameter sits in a list inside the declaration that owns it,
        // which lists its clauses after.
        let list = std::iter::once(node.clone())
            .chain(node.ancestors())
            .find(|ancestor| ancestor.kind() == SyntaxKind::TypeParameterList)?;
        let owner = list.parent()?.clone();
        owner
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
            .find(|clause| {
                clause
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .is_some_and(|token| token.value_text() == name.as_str())
            })
    }
}

impl Emitter<'_> {
    /// The places of a field's, a property's, an event's or a parameter's
    /// type, or of a method's return, as the declaration wrote it.
    pub(crate) fn symbol_flags(&self, symbol: rustlyn_semantics::SymbolId) -> Vec<u8> {
        use rustlyn_semantics::Detail;
        if let Some(flags) = self.synthesized_record_flags(symbol) {
            return flags;
        }
        let symbols = self.compilation.symbols();
        let written = match &symbols.get(symbol).detail {
            Detail::Field(detail) => detail.ty.as_ref(),
            Detail::Property(detail) => detail.ty.as_ref(),
            Detail::Event(detail) => detail.ty.as_ref(),
            Detail::Parameter(detail) => detail.ty.as_ref(),
            Detail::Method(detail) => detail.return_type.as_ref(),
            _ => None,
        };
        self.declared_flags(&self.type_of(symbol), written)
    }

    /// The places the language gives a type a record's synthesized member
    /// has, whatever the `#nullable` context: a record class's
    /// `Equals(object? obj)`, `Equals(R? other)` and `==`'s and `!=`'s
    /// operands may be null; `ToString`'s string, `PrintMembers`' builder,
    /// `EqualityContract`, what `<Clone>$` gives and the copy constructor's
    /// `original` may not. A record struct's are oblivious.
    fn synthesized_record_flags(&self, symbol: rustlyn_semantics::SymbolId) -> Option<Vec<u8>> {
        use rustlyn_semantics::Detail;
        let symbols = self.compilation.symbols();
        let (synthesized, method) = match &symbols.get(symbol).detail {
            Detail::Parameter(detail) => {
                (detail.synthesized.is_some(), symbols.get(symbol).container?)
            }
            Detail::Method(detail) => (detail.synthesized_return.is_some(), symbol),
            Detail::Property(detail) => (detail.synthesized.is_some(), symbol),
            _ => return None,
        };
        if !synthesized {
            return None;
        }
        let record = symbols.get(method).container?;
        let ty = self.type_of(symbol);
        let mut flags = self.nullable_flags(&ty, None, false);
        match symbols.get(record).type_kind() {
            Some(TypeKind::Record) => {}
            Some(TypeKind::RecordStruct) => return Some(flags),
            _ => return None,
        }
        let annotated = matches!(
            symbols.get(method).name.as_str(),
            "Equals" | "op_Equality" | "op_Inequality"
        ) && matches!(symbols.get(symbol).detail, Detail::Parameter(_));
        let value_type = self.nullable_underlying(&ty).is_some()
            || matches!(&ty, Type::Named { symbol, .. } if self.is_value_type_symbol(*symbol));
        if let Some(first) = flags.first_mut()
            && !value_type
        {
            *first = if annotated { ANNOTATED } else { NOT_ANNOTATED };
        }
        Some(flags)
    }

    /// Whether a method is a record's copy constructor, which the language
    /// writes with no context of its own.
    fn is_record_copy_constructor(&self, method: rustlyn_semantics::SymbolId) -> bool {
        let symbols = self.compilation.symbols();
        symbols.get(method).name == ".ctor"
            && symbols.get(method).as_method().is_some_and(|detail| {
                detail.parameters.len() == 1
                    && symbols
                        .get(detail.parameters[0])
                        .as_parameter()
                        .is_some_and(|parameter| {
                            parameter.synthesized
                                == Some(rustlyn_semantics::SynthesizedType::Containing)
                        })
            })
    }

    /// What a type parameter adds to its owner's context: its own value,
    /// and each of its constraint types'.
    fn add_type_parameter(&self, builder: &mut MostCommon, parameter: rustlyn_semantics::SymbolId) {
        builder.add(Some(self.type_parameter_nullable_value(parameter)));
        for flags in self.constraint_flags(parameter) {
            builder.add_flags(&flags);
        }
    }

    /// The places of each of a type parameter's constraint types, in the
    /// order written; `notnull` and `unmanaged` are none.
    pub(crate) fn constraint_flags(&self, parameter: rustlyn_semantics::SymbolId) -> Vec<Vec<u8>> {
        let symbols = self.compilation.symbols();
        let Some(detail) = symbols.get(parameter).as_type_parameter() else {
            return Vec::new();
        };
        let mut all = Vec::new();
        for constraint in &detail.constraints {
            let node = self
                .compilation
                .trees()
                .get(constraint.0.tree)
                .and_then(|tree| tree.root().find_node(constraint.0.span));
            if node.as_ref().is_some_and(|node| {
                node.kind() == SyntaxKind::IdentifierName
                    && matches!(node.text().trim(), "notnull" | "unmanaged")
            }) {
                continue;
            }
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let ty = self.binder.resolve_type_ref(*constraint, &mut sink);
            all.push(self.declared_flags(&ty, Some(constraint)));
        }
        all
    }

    /// A method's own context (Roslyn's `ComputeNullableContextValue` for a
    /// method): what most of its type parameters, its return and its
    /// parameters agree on.
    pub(crate) fn method_nullable_context(
        &self,
        method: rustlyn_semantics::SymbolId,
    ) -> Option<u8> {
        if self.is_record_copy_constructor(method) {
            return None;
        }
        let symbols = self.compilation.symbols();
        let detail = symbols.get(method).as_method()?;
        let mut builder = MostCommon::default();
        for parameter in &detail.type_parameters {
            self.add_type_parameter(&mut builder, *parameter);
        }
        builder.add_flags(&self.symbol_flags(method));
        for parameter in &detail.parameters {
            builder.add_flags(&self.symbol_flags(*parameter));
        }
        builder.value()
    }

    /// The context of an accessor with no symbol of its own: a getter
    /// returns the property's type and takes an indexer's parameters, a
    /// setter takes those and the value.
    pub(crate) fn accessor_nullable_context(
        &self,
        property: rustlyn_semantics::SymbolId,
    ) -> Option<u8> {
        let mut builder = MostCommon::default();
        builder.add_flags(&self.symbol_flags(property));
        if let Some(detail) = self.compilation.symbols().get(property).as_property() {
            for parameter in &detail.parameters {
                builder.add_flags(&self.symbol_flags(*parameter));
            }
        }
        builder.value()
    }
}

impl Emitter<'_> {
    /// The places of what a type extends as its context counts them: its
    /// own place oblivious whatever was written (Roslyn builds it with
    /// `TypeWithAnnotations.Create`), its arguments as written. A type that
    /// names no base class extends `object`, `ValueType`, `Enum` or
    /// `MulticastDelegate`: one oblivious place. An interface extends
    /// nothing.
    pub(crate) fn base_flags(&self, ty: rustlyn_semantics::SymbolId) -> Option<Vec<u8>> {
        let symbols = self.compilation.symbols();
        let kind = symbols.get(ty).type_kind()?;
        if kind == TypeKind::Interface {
            return None;
        }
        let written = self.written_base(ty, |candidate| {
            candidate.symbol().is_some_and(|symbol| {
                matches!(
                    symbols.get(symbol).type_kind(),
                    Some(TypeKind::Class | TypeKind::Record)
                )
            })
        });
        let mut flags = match written {
            Some((base, reference)) => self.declared_flags(&base, Some(&reference)),
            None => vec![OBLIVIOUS],
        };
        if let Some(first) = flags.first_mut() {
            *first = OBLIVIOUS;
        }
        Some(flags)
    }

    /// The places of an interface a type implements, counted the way its
    /// base is: from what the base list wrote where it names it, and as an
    /// unwritten type where it is only implied by another.
    pub(crate) fn interface_flags(
        &self,
        ty: rustlyn_semantics::SymbolId,
        interface: &Type,
    ) -> Vec<u8> {
        let mut flags = match self.written_base(ty, |candidate| candidate == interface) {
            Some((resolved, reference)) => self.declared_flags(&resolved, Some(&reference)),
            // One the language adds (a record's `IEquatable<R>`) or that
            // another implies is oblivious throughout.
            None => self.nullable_flags(interface, None, false),
        };
        if let Some(first) = flags.first_mut() {
            *first = OBLIVIOUS;
        }
        flags
    }

    /// The first entry of a type's base list that resolves to a type `is`
    /// accepts, and that type.
    fn written_base(
        &self,
        ty: rustlyn_semantics::SymbolId,
        is: impl Fn(&Type) -> bool,
    ) -> Option<(Type, TypeSyntaxRef)> {
        let detail = self.compilation.symbols().get(ty).as_named_type()?;
        detail.base_types.iter().find_map(|reference| {
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let resolved = self.binder.resolve_type_ref(*reference, &mut sink);
            is(&resolved).then_some((resolved, *reference))
        })
    }

    /// A type's own context (Roslyn's `ComputeNullableContextValue` for a
    /// type): what most of its base, its interfaces, its own type
    /// parameters and its members agree on, each member counted as its
    /// kind counts — a method by its own context, a property, an event or
    /// a field by its type, a nested type by its own context — together
    /// with the accessors and the backing fields the language adds.
    pub(crate) fn type_nullable_context(&self, ty: rustlyn_semantics::SymbolId) -> Option<u8> {
        use rustlyn_semantics::SymbolKind;
        let symbols = self.compilation.symbols();
        let symbol = symbols.get(ty);
        symbol.type_kind()?;
        let mut builder = MostCommon::default();
        if let Some(flags) = self.base_flags(ty) {
            builder.add_flags(&flags);
        }
        for interface in self.implemented_interfaces(ty) {
            builder.add_flags(&self.interface_flags(ty, &interface));
        }
        let own: Vec<rustlyn_semantics::SymbolId> = symbol
            .as_named_type()
            .map(|detail| {
                detail
                    .type_parameters
                    .iter()
                    .copied()
                    .filter(|parameter| symbols.get(*parameter).container == Some(ty))
                    .collect()
            })
            .unwrap_or_default();
        for parameter in own {
            self.add_type_parameter(&mut builder, parameter);
        }
        for &member in &symbol.members {
            let detail = symbols.get(member);
            match detail.kind {
                SymbolKind::Field => {
                    if detail.name.ends_with(">k__BackingField") {
                        continue;
                    }
                    builder.add_flags(&self.symbol_flags(member));
                }
                SymbolKind::Property => {
                    let flags = self.symbol_flags(member);
                    builder.add_flags(&flags);
                    let Some(property) = detail.as_property() else {
                        continue;
                    };
                    let accessor = self.accessor_nullable_context(member);
                    if property.has_get {
                        builder.add(accessor);
                    }
                    if property.has_set || property.has_init {
                        builder.add(accessor);
                    }
                    if self.binder.is_automatic_property(member) {
                        builder.add_flags(&flags);
                    }
                }
                SymbolKind::Event => {
                    let flags = self.symbol_flags(member);
                    builder.add_flags(&flags);
                    // `add_E` and `remove_E` take the value and give back
                    // nothing. The field behind a field-like event is no
                    // member of the type's list, and does not count.
                    builder.add(common_value(&flags));
                    builder.add(common_value(&flags));
                }
                SymbolKind::Method => builder.add(self.method_nullable_context(member)),
                SymbolKind::NamedType => builder.add(self.type_nullable_context(member)),
                _ => {}
            }
        }
        // A record derived from another has `Equals(Base? other)` besides.
        if symbol.type_kind() == Some(TypeKind::Record) && self.record_base(ty).is_some() {
            builder.add(Some(ANNOTATED));
        }
        builder.value()
    }
}

/// A method's own context, the places of its return, and each parameter's.
type Signature = (Option<u8>, Vec<u8>, Vec<Vec<u8>>);

/// What nullable metadata a method's rows carry: its own context, the
/// context its signature is read in, and the places of its return and of
/// each parameter the plan writes.
#[derive(Clone, Debug, Default)]
pub(crate) struct NullableShape {
    /// `[NullableContext]` on the method, where its own context differs
    /// from its type's.
    pub(crate) context: Option<u8>,
    /// The context the return and the parameters are compared against.
    pub(crate) effective: Option<u8>,
    pub(crate) returns: Vec<u8>,
    pub(crate) parameters: Vec<Vec<u8>>,
}

impl Emitter<'_> {
    /// Whether the compilation writes nullable metadata at all: wherever
    /// the attributes exist. Code outside `#nullable enable` is oblivious
    /// and gets none, but a `?` written there still annotates, and a
    /// record's own members are annotated whatever the context.
    pub(crate) fn nullable_wanted(&self) -> bool {
        self.nullable_attributes_available()
    }

    /// A type's own context, worked out once.
    pub(crate) fn type_context(&mut self, ty: rustlyn_semantics::SymbolId) -> Option<u8> {
        if let Some(value) = self.nullable_type_contexts.get(&ty) {
            return *value;
        }
        let value = self.type_nullable_context(ty);
        self.nullable_type_contexts.insert(ty, value);
        value
    }

    /// The context a type's members are read in: its own, or the nearest
    /// enclosing type's.
    pub(crate) fn type_effective_context(&mut self, ty: rustlyn_semantics::SymbolId) -> Option<u8> {
        if let Some(value) = self.type_context(ty) {
            return Some(value);
        }
        let symbols = self.compilation.symbols();
        let container = symbols.get(ty).container.filter(|container| {
            symbols.get(*container).kind == rustlyn_semantics::SymbolKind::NamedType
        })?;
        self.type_effective_context(container)
    }

    /// `[NullableContext]` and `[Nullable]` for a type's own row: its
    /// context where it differs from the one around it, and what it
    /// extends.
    pub(crate) fn mark_type_nullable(&mut self, ty: rustlyn_semantics::SymbolId, parent: u32) {
        let local = self.type_context(ty);
        let symbols = self.compilation.symbols();
        let outer = symbols.get(ty).container.filter(|container| {
            symbols.get(*container).kind == rustlyn_semantics::SymbolKind::NamedType
        });
        let outer = outer.and_then(|outer| self.type_effective_context(outer));
        if let Some(value) = local
            && value != outer.unwrap_or(OBLIVIOUS)
        {
            self.mark_nullable_context(parent, value);
        }
        if let Some(flags) = self.base_flags(ty) {
            self.mark_nullable(parent, &flags, Some(local.unwrap_or(OBLIVIOUS)));
        }
    }

    /// The nullable metadata of a planned method, where it is one the
    /// source declared or the language adds to a declared member.
    pub(crate) fn method_nullable_shape(
        &mut self,
        ty: rustlyn_semantics::SymbolId,
        method: &crate::emitter::MethodPlan,
    ) -> Option<NullableShape> {
        use crate::emitter::MethodSource;
        use rustlyn_semantics::SymbolKind;
        let symbols = self.compilation.symbols();
        let indexer = |this: &Self, property: rustlyn_semantics::SymbolId| -> Vec<Vec<u8>> {
            this.compilation
                .symbols()
                .get(property)
                .as_property()
                .map(|detail| {
                    detail
                        .parameters
                        .iter()
                        .map(|p| this.symbol_flags(*p))
                        .collect()
                })
                .unwrap_or_default()
        };
        let (local, returns, parameters) = match &method.source {
            // An iterator or an `async` method is still the method written,
            // whatever its body became.
            // A record's `EqualityContract` getter stands for its property.
            MethodSource::RecordMember(property)
                if symbols.get(*property).kind == SymbolKind::Property =>
            {
                (
                    self.accessor_nullable_context(*property),
                    self.symbol_flags(*property),
                    Vec::new(),
                )
            }
            MethodSource::Declared(symbol)
            | MethodSource::RecordConstructor(symbol)
            | MethodSource::RecordMember(symbol)
            | MethodSource::IteratorStart(crate::emitter::MachineKey::Member(symbol))
            | MethodSource::AsyncStart(crate::emitter::MachineKey::Member(symbol)) => {
                let symbol = *symbol;
                let container = symbols.get(symbol).container?;
                match symbols.get(container).kind {
                    SymbolKind::Property => {
                        let flags = self.symbol_flags(container);
                        let mut parameters = indexer(self, container);
                        let getter = symbols.get(symbol).name.starts_with("get_")
                            || symbols
                                .get(container)
                                .as_property()
                                .is_some_and(|detail| detail.getter == Some(symbol));
                        let returns = if getter {
                            flags
                        } else {
                            parameters.push(flags);
                            Vec::new()
                        };
                        (
                            self.accessor_nullable_context(container),
                            returns,
                            parameters,
                        )
                    }
                    SymbolKind::Event => {
                        let flags = self.symbol_flags(container);
                        (common_value(&flags), Vec::new(), vec![flags])
                    }
                    _ => {
                        let detail = symbols.get(symbol).as_method()?;
                        let parameters = detail.parameters.clone();
                        (
                            self.method_nullable_context(symbol),
                            self.symbol_flags(symbol),
                            parameters.iter().map(|p| self.symbol_flags(*p)).collect(),
                        )
                    }
                }
            }
            MethodSource::PropertyGetter { property, .. } => (
                self.accessor_nullable_context(*property),
                self.symbol_flags(*property),
                indexer(self, *property),
            ),
            MethodSource::PropertySetter { property } => {
                let mut parameters = indexer(self, *property);
                parameters.push(self.symbol_flags(*property));
                (
                    self.accessor_nullable_context(*property),
                    Vec::new(),
                    parameters,
                )
            }
            MethodSource::EventAccessor { event, .. } => {
                let flags = self.symbol_flags(*event);
                (common_value(&flags), Vec::new(), vec![flags])
            }
            // A delegate's `BeginInvoke` takes `Invoke`'s parameters, a
            // callback and a state, and gives back an `IAsyncResult`; its
            // `EndInvoke` takes the `ref` and `out` ones and the result, and
            // gives back what `Invoke` does. What the language adds is
            // oblivious, and so is the object its constructor takes.
            MethodSource::DefaultConstructor
                if symbols.get(ty).type_kind() == Some(TypeKind::Delegate) =>
            {
                let returns_of_invoke = || {
                    symbols
                        .get(ty)
                        .members
                        .iter()
                        .copied()
                        .find(|member| symbols.get(*member).name == "Invoke")
                        .map(|invoke| self.symbol_flags(invoke))
                        .unwrap_or_default()
                };
                let (returns, parameters) = match self.cloned_parameters.get(&method.token) {
                    Some(originals) => {
                        let mut parameters: Vec<Vec<u8>> =
                            originals.iter().map(|p| self.symbol_flags(*p)).collect();
                        if method.name == "BeginInvoke" {
                            parameters.push(vec![OBLIVIOUS]);
                            parameters.push(vec![OBLIVIOUS]);
                            (vec![OBLIVIOUS], parameters)
                        } else {
                            parameters.push(vec![OBLIVIOUS]);
                            (returns_of_invoke(), parameters)
                        }
                    }
                    None => (Vec::new(), vec![vec![OBLIVIOUS], Vec::new()]),
                };
                let mut builder = MostCommon::default();
                builder.add_flags(&returns);
                for flags in &parameters {
                    builder.add_flags(flags);
                }
                (builder.value(), returns, parameters)
            }
            // A local function is a method the source declared, whatever
            // class it became a member of.
            MethodSource::LocalFunction { owner, index }
            | MethodSource::IteratorStart(crate::emitter::MachineKey::Function { owner, index })
            | MethodSource::AsyncStart(crate::emitter::MachineKey::Function { owner, index }) => {
                let function = self.body_of(*owner)?.local_functions.get(*index)?.symbol;
                let detail = self.compilation.symbols().get(function).as_method()?;
                let parameters = detail.parameters.clone();
                (
                    self.method_nullable_context(function),
                    self.symbol_flags(function),
                    parameters.iter().map(|p| self.symbol_flags(*p)).collect(),
                )
            }
            MethodSource::Lambda { owner, index }
            | MethodSource::AsyncStart(crate::emitter::MachineKey::Lambda { owner, index }) => {
                self.lambda_nullable_shape(*owner, *index)?
            }
            // `Equals(Base? other)`, sealed, in a record derived from
            // another.
            MethodSource::RecordBaseEquals => {
                let base = method
                    .parameters
                    .first()
                    .map_or(Type::Error, |parameter| parameter.ty.clone());
                let mut flags = self.nullable_flags(&base, None, false);
                if let Some(first) = flags.first_mut() {
                    *first = ANNOTATED;
                }
                (Some(ANNOTATED), Vec::new(), vec![flags])
            }
            _ => return None,
        };
        let around = self.type_effective_context(ty);
        let context = local.filter(|value| *value != around.unwrap_or(OBLIVIOUS));
        Some(NullableShape {
            context,
            effective: local.or(around),
            returns,
            parameters,
        })
    }

    /// Whether `[Nullable]` would go on a row for these places.
    pub(crate) fn nullable_needed(flags: &[u8], context: Option<u8>) -> bool {
        match common_value(flags) {
            None => !flags.is_empty(),
            Some(value) => Some(value) != context && !(context.is_none() && value == OBLIVIOUS),
        }
    }
}

impl Emitter<'_> {
    /// `[Nullable]` on a type parameter's row, where it is not oblivious
    /// and its owner's context does not say it, and on each of its
    /// constraint rows as their types were written.
    pub(crate) fn mark_type_parameter_nullable(
        &mut self,
        owner: u32,
        number: u16,
        parameter: rustlyn_semantics::SymbolId,
        constraints: &[Option<TypeSyntaxRef>],
        context: Option<u8>,
    ) {
        let value = self.type_parameter_nullable_value(parameter);
        if Self::nullable_needed(&[value], context) {
            let parent = self.metadata.generic_param_parent(owner, number);
            self.mark_nullable(parent, &[value], context);
        }
        for (index, reference) in constraints.iter().enumerate() {
            let Some(reference) = reference else {
                continue;
            };
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let ty = self.binder.resolve_type_ref(*reference, &mut sink);
            let flags = self.declared_flags(&ty, Some(reference));
            if Self::nullable_needed(&flags, context) {
                let parent = self
                    .metadata
                    .generic_param_constraint_parent(owner, number, index);
                self.mark_nullable(parent, &flags, context);
            }
        }
    }
}

impl Emitter<'_> {
    /// A lambda's own context, and the places of its return and of each of
    /// its parameters: as written where the lambda writes a type, else as
    /// the delegate type it converts to says where that is written — on the
    /// declaration it initializes — else as its context gives an unwritten
    /// type.
    fn lambda_nullable_shape(
        &mut self,
        owner: rustlyn_semantics::SymbolId,
        index: usize,
    ) -> Option<Signature> {
        let body = self.body_of(owner)?;
        let lambda = body.lambdas.get(index)?;
        let (tree, node) = self.lambda_node(owner, index)?;
        let enabled = self.annotations_at(tree, node.span().start());
        let delegate = body.types.get(&lambda.span).cloned();
        let (target_parameters, target_returns) = self
            .target_delegate_flags(&node, delegate.as_ref(), enabled)
            .unwrap_or_default();
        let written: Vec<SyntaxNode> = match node.child_of_kind(SyntaxKind::ParameterList) {
            Some(list) => list
                .children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
                .collect(),
            None => node
                .children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
                .collect(),
        };
        let mut parameters = Vec::with_capacity(lambda.parameters.len());
        for (at, local) in lambda.parameters.iter().enumerate() {
            let ty = &body.locals[local.0 as usize].ty;
            let explicit = written.get(at).and_then(type_child);
            let flags = match explicit {
                Some(explicit) => {
                    let enabled = self.annotations_at(tree, explicit.span().start());
                    self.nullable_flags(ty, Some(&explicit), enabled)
                }
                None => match target_parameters.get(at).cloned().flatten() {
                    Some(flags) => flags,
                    None => self.nullable_flags(ty, None, enabled),
                },
            };
            parameters.push(flags);
        }
        // `string? (object o) => ...` writes its return type ahead of its
        // parameters (C# 10).
        let explicit_return = node
            .children()
            .take_while(|child| child.kind() != SyntaxKind::ParameterList)
            .find(|child| child.kind().is_type_node());
        let returned = lambda
            .task_type
            .clone()
            .unwrap_or_else(|| lambda.return_type.clone());
        let returns = match explicit_return {
            Some(explicit) => {
                let enabled = self.annotations_at(tree, explicit.span().start());
                self.nullable_flags(&returned, Some(&explicit), enabled)
            }
            None => match target_returns.filter(|_| lambda.task_type.is_none()) {
                Some(flags) => flags,
                None => self.nullable_flags(&returned, None, enabled),
            },
        };
        let mut builder = MostCommon::default();
        builder.add_flags(&returns);
        for flags in &parameters {
            builder.add_flags(flags);
        }
        Some((builder.value(), returns, parameters))
    }

    /// The places of a delegate's `Invoke` parameters and return, as the
    /// type a lambda converts to is written where the lambda initializes a
    /// declaration: `Func<string?, string> f = s => ...` makes `s` a
    /// `string?`. A delegate declared here says them itself.
    #[allow(clippy::type_complexity)]
    fn target_delegate_flags(
        &self,
        lambda: &SyntaxNode,
        delegate: Option<&Type>,
        enabled: bool,
    ) -> Option<(Vec<Option<Vec<u8>>>, Option<Vec<u8>>)> {
        let delegate = delegate?;
        let Type::Named {
            symbol,
            type_arguments,
        } = delegate
        else {
            return None;
        };
        let symbols = self.compilation.symbols();
        let invoke = symbols
            .get(*symbol)
            .members
            .iter()
            .copied()
            .find(|member| symbols.get(*member).name == "Invoke")?;
        let invoke_parameters = symbols.get(invoke).as_method()?.parameters.clone();
        if type_arguments.is_empty() {
            // Its own declaration says what its parameters are.
            if self.compilation.is_from_metadata(*symbol) {
                return None;
            }
            return Some((
                invoke_parameters
                    .iter()
                    .map(|parameter| Some(self.symbol_flags(*parameter)))
                    .collect(),
                Some(self.symbol_flags(invoke)),
            ));
        }
        // The declaration the lambda initializes, and the type it wrote.
        let mut current = lambda.parent()?.clone();
        while current.kind() == SyntaxKind::ParenthesizedExpression {
            current = current.parent()?.clone();
        }
        if current.kind() != SyntaxKind::EqualsValueClause {
            return None;
        }
        let declaration = current.parent()?;
        let written = match declaration.kind() {
            SyntaxKind::VariableDeclarator => type_child(declaration.parent()?),
            SyntaxKind::PropertyDeclaration => type_child(declaration),
            _ => None,
        }?;
        if written.kind() == SyntaxKind::IdentifierName && written.text().trim() == "var" {
            return None;
        }
        let arguments = aligned_arguments(Some(&Written::Node(written)), type_arguments.len());
        let per_argument: Vec<Vec<u8>> = type_arguments
            .iter()
            .zip(arguments)
            .map(|(argument, written)| {
                let mut flags = Vec::new();
                self.flags_into(argument, written, enabled, &mut flags);
                flags
            })
            .collect();
        let delegate_parameters = symbols
            .get(*symbol)
            .as_named_type()?
            .type_parameters
            .clone();
        let place = |this: &Self, of: rustlyn_semantics::SymbolId| -> Option<Vec<u8>> {
            match this.type_of(of) {
                Type::TypeParameter(parameter) => delegate_parameters
                    .iter()
                    .position(|it| *it == parameter)
                    .and_then(|at| per_argument.get(at).cloned()),
                _ => None,
            }
        };
        let parameters = invoke_parameters
            .iter()
            .map(|parameter| place(self, *parameter))
            .collect();
        let returns = match self.type_of(invoke) {
            Type::Void => Some(Vec::new()),
            _ => place(self, invoke),
        };
        Some((parameters, returns))
    }
}
