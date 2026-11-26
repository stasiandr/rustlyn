//! The metadata tables and heaps of ECMA-335 §II.22–24.
//!
//! Metadata is four heaps of bytes and a set of tables whose columns index
//! into them. Two things about the encoding drive the shape of this module.
//! An index is two bytes or four depending on how big the thing it points at
//! turned out to be, so nothing can be written until every row exists. And a
//! row is found by its position, so the order rows are added in is part of the
//! output: a type's fields and methods are a *run* in the field and method
//! tables, and the type points at where its run starts.

use std::collections::HashMap;

use crate::il::Token;

/// Table numbers, as tokens and the valid-mask spell them.
pub(crate) mod table {
    pub(crate) const MODULE: u8 = 0x00;
    pub(crate) const TYPE_REF: u8 = 0x01;
    pub(crate) const TYPE_DEF: u8 = 0x02;
    pub(crate) const FIELD: u8 = 0x04;
    pub(crate) const METHOD_DEF: u8 = 0x06;
    pub(crate) const PARAM: u8 = 0x08;
    pub(crate) const INTERFACE_IMPL: u8 = 0x09;
    pub(crate) const CONSTANT: u8 = 0x0B;
    pub(crate) const CUSTOM_ATTRIBUTE: u8 = 0x0C;
    pub(crate) const FIELD_MARSHAL: u8 = 0x0D;
    pub(crate) const CLASS_LAYOUT: u8 = 0x0F;
    pub(crate) const FIELD_LAYOUT: u8 = 0x10;
    pub(crate) const EVENT_MAP: u8 = 0x12;
    pub(crate) const EVENT: u8 = 0x14;
    pub(crate) const PROPERTY_MAP: u8 = 0x15;
    pub(crate) const PROPERTY: u8 = 0x17;
    pub(crate) const METHOD_SEMANTICS: u8 = 0x18;
    pub(crate) const METHOD_IMPL: u8 = 0x19;
    pub(crate) const MODULE_REF: u8 = 0x1A;
    pub(crate) const IMPL_MAP: u8 = 0x1C;
    pub(crate) const FIELD_RVA: u8 = 0x1D;
    pub(crate) const TYPE_SPEC: u8 = 0x1B;
    pub(crate) const GENERIC_PARAM: u8 = 0x2A;
    pub(crate) const MANIFEST_RESOURCE: u8 = 0x28;
    pub(crate) const NESTED_CLASS: u8 = 0x29;
    pub(crate) const METHOD_SPEC: u8 = 0x2B;
    pub(crate) const GENERIC_PARAM_CONSTRAINT: u8 = 0x2C;
    pub(crate) const MEMBER_REF: u8 = 0x0A;
    pub(crate) const STAND_ALONE_SIG: u8 = 0x11;
    pub(crate) const ASSEMBLY: u8 = 0x20;
    pub(crate) const ASSEMBLY_REF: u8 = 0x23;
}

/// The `ParamAttributes` of §II.23.1.13 that this emitter sets.
pub(crate) mod param_attributes {
    pub(crate) const IN: u16 = 0x0001;
    pub(crate) const OUT: u16 = 0x0002;
    pub(crate) const OPTIONAL: u16 = 0x0010;
    pub(crate) const HAS_DEFAULT: u16 = 0x1000;
}

/// The `TypeAttributes` of §II.23.1.15 that this emitter sets.
pub(crate) mod type_attributes {
    pub(crate) const PUBLIC: u32 = 0x0000_0001;
    /// The visibility of a nested type is its own set of values, not the
    /// top-level ones: `Public` on a nested type would mean `NotPublic`.
    pub(crate) const NESTED_PUBLIC: u32 = 0x0000_0002;
    pub(crate) const NESTED_PRIVATE: u32 = 0x0000_0003;
    pub(crate) const NESTED_FAMILY: u32 = 0x0000_0004;
    pub(crate) const NESTED_ASSEMBLY: u32 = 0x0000_0005;
    pub(crate) const NESTED_FAM_AND_ASSEM: u32 = 0x0000_0006;
    pub(crate) const NESTED_FAM_OR_ASSEM: u32 = 0x0000_0007;
    pub(crate) const SEALED: u32 = 0x0000_0100;
    pub(crate) const INTERFACE: u32 = 0x0000_0020;
    pub(crate) const SEQUENTIAL_LAYOUT: u32 = 0x0000_0008;
    pub(crate) const EXPLICIT_LAYOUT: u32 = 0x0000_0010;
    pub(crate) const ABSTRACT: u32 = 0x0000_0080;
    pub(crate) const BEFORE_FIELD_INIT: u32 = 0x0010_0000;
    /// `[Serializable]`, which is a flag rather than an attribute.
    pub(crate) const SERIALIZABLE: u32 = 0x0000_2000;
    /// `[ComImport]`, which is one too.
    pub(crate) const IMPORT: u32 = 0x0000_1000;
    pub(crate) const AUTO_LAYOUT_ANSI_CLASS: u32 = 0x0000_0000;
}

/// The `MethodAttributes` of §II.23.1.10.
pub(crate) mod method_attributes {
    pub(crate) const PRIVATE: u16 = 0x0001;
    /// `protected internal` in C#: reachable from a derived type *or* from
    /// this assembly.
    pub(crate) const FAM_AND_ASSEM: u16 = 0x0002;
    /// `internal`, which is not `private`: everything in the assembly can
    /// reach it, and calling it from another file is the ordinary case.
    pub(crate) const ASSEMBLY: u16 = 0x0003;
    pub(crate) const FAMILY: u16 = 0x0004;
    pub(crate) const FAM_OR_ASSEM: u16 = 0x0005;
    pub(crate) const PUBLIC: u16 = 0x0006;
    pub(crate) const STATIC: u16 = 0x0010;
    pub(crate) const FINAL: u16 = 0x0020;
    pub(crate) const VIRTUAL: u16 = 0x0040;
    pub(crate) const HIDE_BY_SIG: u16 = 0x0080;
    pub(crate) const NEW_SLOT: u16 = 0x0100;
    /// `strict`: only a type that can see the method may override it, which
    /// is what `internal` means for a virtual one.
    pub(crate) const STRICT: u16 = 0x0200;
    pub(crate) const ABSTRACT: u16 = 0x0400;
    pub(crate) const SPECIAL_NAME: u16 = 0x0800;
    pub(crate) const RT_SPECIAL_NAME: u16 = 0x1000;
    /// The body is in an unmanaged library, named by an `ImplMap` row.
    pub(crate) const PINVOKE_IMPL: u16 = 0x2000;
}

/// The `MethodImplAttributes` of §II.23.1.10, as far as this needs them.
pub(crate) mod method_impl {
    /// The runtime provides the body. Every member of a delegate is one: there
    /// is no IL to write for `Invoke`, and writing some would be wrong.
    pub(crate) const RUNTIME: u16 = 0x0003;
    /// The JIT may not fold this body into its caller. A survey sets it on
    /// everything: a stack trace that names the method a stub was reached
    /// through, rather than whatever it was folded into, is the difference
    /// between a measurement and a guess.
    pub(crate) const NO_INLINING: u16 = 0x0008;
    /// The unmanaged signature is the managed one: no HRESULT is threaded
    /// through, which is what `DllImport` means unless told otherwise.
    pub(crate) const PRESERVE_SIG: u16 = 0x0080;
}

/// The `MethodSemanticsAttributes` of §II.23.1.12.
pub(crate) mod semantics {
    pub(crate) const SETTER: u16 = 0x0001;
    pub(crate) const GETTER: u16 = 0x0002;
    pub(crate) const ADD_ON: u16 = 0x0008;
    pub(crate) const REMOVE_ON: u16 = 0x0010;
}

/// The `FieldAttributes` of §II.23.1.5.
pub(crate) mod field_attributes {
    pub(crate) const PRIVATE: u16 = 0x0001;
    pub(crate) const FAM_AND_ASSEM: u16 = 0x0002;
    pub(crate) const ASSEMBLY: u16 = 0x0003;
    pub(crate) const FAMILY: u16 = 0x0004;
    pub(crate) const FAM_OR_ASSEM: u16 = 0x0005;
    pub(crate) const PUBLIC: u16 = 0x0006;
    pub(crate) const STATIC: u16 = 0x0010;
    pub(crate) const INIT_ONLY: u16 = 0x0020;
    pub(crate) const LITERAL: u16 = 0x0040;
    pub(crate) const SPECIAL_NAME: u16 = 0x0200;
    pub(crate) const RT_SPECIAL_NAME: u16 = 0x0400;
    pub(crate) const HAS_DEFAULT: u16 = 0x8000;
    pub(crate) const HAS_FIELD_RVA: u16 = 0x0100;
}

/// A heap of bytes that hands out offsets and never stores the same thing
/// twice.
#[derive(Debug)]
struct Heap {
    bytes: Vec<u8>,
    seen: HashMap<Vec<u8>, u32>,
}

impl Heap {
    /// A heap always opens with a single zero byte, which is the empty string
    /// and the empty blob.
    fn new() -> Self {
        Self {
            bytes: vec![0],
            seen: HashMap::new(),
        }
    }

    fn len(&self) -> u32 {
        self.bytes.len() as u32
    }
}

/// One row of `TypeDef`.
#[derive(Debug)]
struct TypeDefRow {
    flags: u32,
    name: u32,
    namespace: u32,
    extends: u32,
    /// One past the last row of the previous type; §II.22.37's "list" columns.
    first_field: u32,
    first_method: u32,
}

#[derive(Debug)]
struct MethodRow {
    /// Where the body sits inside the IL blob, or `None` for an abstract
    /// method, whose RVA is zero.
    body_offset: Option<u32>,
    /// How the body is provided. Zero is IL and managed; a delegate's members
    /// are `Runtime`, which says the runtime writes them.
    impl_flags: u16,
    flags: u16,
    name: u32,
    signature: u32,
    first_param: u32,
    /// Whether the first of its `Param` rows is the return's, sequence 0,
    /// which exists only to carry attributes of the return.
    returns_row: bool,
}

#[derive(Debug)]
struct FieldRow {
    flags: u16,
    name: u32,
    signature: u32,
}

#[derive(Debug)]
struct ParamRow {
    flags: u16,
    sequence: u16,
    name: u32,
}

#[derive(Debug)]
struct TypeRefRow {
    scope: u32,
    name: u32,
    namespace: u32,
}

#[derive(Debug)]
struct MemberRefRow {
    parent: u32,
    name: u32,
    signature: u32,
}

#[derive(Debug)]
struct AssemblyRefRow {
    version: [u16; 4],
    public_key: u32,
    name: u32,
}

/// Everything the metadata section will hold.
#[derive(Debug)]
pub(crate) struct Metadata {
    strings: Heap,
    user_strings: Heap,
    blobs: Heap,
    guid: [u8; 16],

    module_name: u32,
    type_refs: Vec<TypeRefRow>,
    type_defs: Vec<TypeDefRow>,
    fields: Vec<FieldRow>,
    methods: Vec<MethodRow>,
    params: Vec<ParamRow>,
    /// Which interfaces each type implements, as (`TypeDef` row,
    /// `TypeDefOrRef` coded index) pairs kept in type order, which is the
    /// order §II.22 requires the table to be sorted in.
    interface_impls: Vec<(u32, u32)>,
    /// The literal value of each constant field, as (`Field` row, element
    /// type, encoded value). Kept in field order, which is the order §II.22
    /// requires the `Constant` table to be sorted in.
    constants: Vec<(u32, u8, u32)>,
    /// (`HasCustomAttribute` coded parent, `CustomAttributeType` coded
    /// constructor, value blob) per attribute. Sorted on the way out, which
    /// is what §II.22 requires and what the runtime binary-searches on.
    custom_attributes: Vec<(u32, u32, u32)>,
    /// (`HasFieldMarshal` coded parent, native type blob) for a field or a
    /// parameter `[MarshalAs]` says how to marshal.
    field_marshals: Vec<(u32, u32)>,
    /// (packing size, class size, `TypeDef` row) for a type whose size the
    /// source fixed: the struct behind a fixed-size buffer.
    class_layouts: Vec<(u16, u32, u32)>,
    /// (offset, `Field` row) for a field placed by `[FieldOffset]`.
    field_layouts: Vec<(u32, u32)>,
    /// (RVA, `Field` row) for a field whose initial value is bytes in the
    /// image: the data an array initializer is copied out of.
    field_rvas: Vec<(u32, u32)>,
    /// (`TypeDef` row, first `Event` row) for each type that has any.
    event_maps: Vec<(u32, u32)>,
    /// (flags, name, `TypeDefOrRef` coded delegate type) per event.
    events: Vec<(u16, u32, u32)>,
    /// (`TypeDef` row, first `Property` row) for each type that has any.
    property_maps: Vec<(u32, u32)>,
    /// (flags, name, signature) per property.
    properties: Vec<(u16, u32, u32)>,
    /// (semantics, `MethodDef` row, `HasSemantics` coded parent) — which
    /// method is which accessor of which property.
    method_semantics: Vec<(u16, u32, u32)>,
    /// (`TypeDef` row, `MethodDefOrRef` body, `MethodDefOrRef` declaration) —
    /// which method of a type stands in for which method it inherits. This is
    /// the only thing that binds `string IFormattable.ToString(...)` to
    /// `IFormattable`: nothing in the name says so.
    method_impls: Vec<(u32, u32, u32)>,
    /// The unmanaged libraries `DllImport` names, by name.
    module_refs: Vec<u32>,
    /// One row per `DllImport`: mapping flags, the `MemberForwarded` coded
    /// index of the method, the entry point's name, the `ModuleRef` row.
    impl_maps: Vec<(u16, u32, u32, u32)>,
    /// Offset into the resources blob, flags, name.
    manifest_resources: Vec<(u32, u32, u32)>,
    /// The signature blob of each constructed type named anywhere.
    type_specs: Vec<u32>,
    /// (number, `TypeOrMethodDef` coded owner, name) per type parameter, kept
    /// in owner order, which is the order §II.22 requires.
    generic_params: Vec<(u16, u16, u32, u32)>,
    /// The type parameters attributes were put on, by owner and number: a
    /// `HasCustomAttribute` parent tagged 19 is an index into this until the
    /// `GenericParam` table is sorted and its rows are known.
    generic_param_keys: Vec<(u32, u16)>,
    /// A method instantiation: the `MethodDefOrRef` it constructs and the
    /// blob of what it was given.
    method_specs: Vec<(u32, u32)>,
    /// What a `where T : Base` says, as (owner, number, `TypeDefOrRef`).
    ///
    /// The parameter is named by owner and position rather than by row,
    /// because the `GenericParam` table is sorted on the way out and a row
    /// number handed out before that would point at the wrong parameter.
    generic_param_constraints: Vec<(u32, u16, u32)>,
    /// The constraints attributes were put on, by owner, number and which
    /// of the parameter's constraints: a `HasCustomAttribute` parent tagged
    /// 20 is an index into this until the table is sorted.
    constraint_keys: Vec<(u32, u16, usize)>,
    /// Which type each nested type sits in, as (`TypeDef` row, `TypeDef` row).
    nested_classes: Vec<(u32, u32)>,
    member_refs: Vec<MemberRefRow>,
    stand_alone_sigs: Vec<u32>,
    assembly_name: u32,
    /// What `[assembly: AssemblyVersion]`, `AssemblyCulture`,
    /// `AssemblyFlags` and `AssemblyAlgorithmId` say, which are columns of
    /// the `Assembly` row rather than attributes.
    assembly_version: [u16; 4],
    assembly_culture: u32,
    assembly_flags: u32,
    hash_algorithm: u32,
    /// Flags a pseudo-attribute adds to a row — `[SpecialName]`,
    /// `[Serializable]`, `[NonSerialized]` — by the `HasCustomAttribute`
    /// coded index the attribute was written for.
    row_flags: HashMap<u32, u32>,
    assembly_refs: Vec<AssemblyRefRow>,
}

impl Metadata {
    #[must_use]
    pub(crate) fn new(module_name: &str, assembly_name: &str) -> Self {
        let mut metadata = Self {
            strings: Heap::new(),
            user_strings: Heap::new(),
            blobs: Heap::new(),
            // A module identifier has to be *a* GUID; it does not have to be a
            // fresh one, and a fixed value makes the output reproducible.
            guid: *b"rustlyn-module\0\0",
            module_name: 0,
            type_refs: Vec::new(),
            type_defs: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            params: Vec::new(),
            interface_impls: Vec::new(),
            constants: Vec::new(),
            custom_attributes: Vec::new(),
            field_marshals: Vec::new(),
            class_layouts: Vec::new(),
            field_layouts: Vec::new(),
            field_rvas: Vec::new(),
            event_maps: Vec::new(),
            events: Vec::new(),
            property_maps: Vec::new(),
            properties: Vec::new(),
            method_semantics: Vec::new(),
            method_impls: Vec::new(),
            module_refs: Vec::new(),
            impl_maps: Vec::new(),
            manifest_resources: Vec::new(),
            type_specs: Vec::new(),
            generic_params: Vec::new(),
            generic_param_keys: Vec::new(),
            method_specs: Vec::new(),
            generic_param_constraints: Vec::new(),
            constraint_keys: Vec::new(),
            nested_classes: Vec::new(),
            member_refs: Vec::new(),
            stand_alone_sigs: Vec::new(),
            assembly_name: 0,
            assembly_version: [0; 4],
            assembly_culture: 0,
            assembly_flags: 0,
            // SHA1, which is what the column means, not a hash.
            hash_algorithm: 0x0000_8004,
            row_flags: HashMap::new(),
            assembly_refs: Vec::new(),
        };
        metadata.module_name = metadata.string(module_name);
        metadata.assembly_name = metadata.string(assembly_name);
        metadata
    }

    // -- heaps -------------------------------------------------------------

    /// Interns a name and returns its offset in `#Strings`.
    pub(crate) fn string(&mut self, text: &str) -> u32 {
        if text.is_empty() {
            return 0;
        }
        let key = text.as_bytes().to_vec();
        if let Some(offset) = self.strings.seen.get(&key) {
            return *offset;
        }
        let offset = self.strings.len();
        self.strings.bytes.extend_from_slice(text.as_bytes());
        self.strings.bytes.push(0);
        self.strings.seen.insert(key, offset);
        offset
    }

    /// Interns a blob and returns its offset in `#Blob`.
    pub(crate) fn blob(&mut self, bytes: &[u8]) -> u32 {
        if bytes.is_empty() {
            return 0;
        }
        if let Some(offset) = self.blobs.seen.get(bytes) {
            return *offset;
        }
        let offset = self.blobs.len();
        crate::signature::compress(&mut self.blobs.bytes, bytes.len() as u32);
        self.blobs.bytes.extend_from_slice(bytes);
        self.blobs.seen.insert(bytes.to_vec(), offset);
        offset
    }

    /// Interns a string literal and returns the `ldstr` token for it.
    ///
    /// `#US` holds UTF-16, and each entry ends with a byte saying whether any
    /// character needs more than the bottom eight bits — a hint for readers
    /// that want to know whether the text is ASCII without scanning it.
    pub(crate) fn user_string(&mut self, text: &str) -> Token {
        let units: Vec<u16> = text.encode_utf16().collect();
        let mut bytes = Vec::with_capacity(units.len() * 2 + 1);
        for unit in &units {
            bytes.extend_from_slice(&unit.to_le_bytes());
        }
        let special = units
            .iter()
            .any(|unit| *unit >= 0x100 || matches!(unit, 0x01..=0x08 | 0x0E..=0x1F | 0x27 | 0x2D));
        bytes.push(u8::from(special));

        if let Some(offset) = self.user_strings.seen.get(&bytes) {
            return Token(0x7000_0000 | *offset);
        }
        let offset = self.user_strings.len();
        crate::signature::compress(&mut self.user_strings.bytes, bytes.len() as u32);
        self.user_strings.bytes.extend_from_slice(&bytes);
        self.user_strings.seen.insert(bytes, offset);
        Token(0x7000_0000 | offset)
    }

    // -- rows --------------------------------------------------------------

    pub(crate) fn add_assembly_ref(
        &mut self,
        name: &str,
        version: [u16; 4],
        public_key: &[u8],
    ) -> Token {
        let name = self.string(name);
        let public_key = self.blob(public_key);
        self.assembly_refs.push(AssemblyRefRow {
            version,
            public_key,
            name,
        });
        Token::new(table::ASSEMBLY_REF, self.assembly_refs.len() as u32)
    }

    /// `scope` is a `ResolutionScope` coded index; for a type from another
    /// assembly that is `(assembly_ref_row << 2) | 2`.
    pub(crate) fn add_type_ref(&mut self, scope: u32, namespace: &str, name: &str) -> Token {
        let namespace = self.string(namespace);
        let name = self.string(name);
        self.type_refs.push(TypeRefRow {
            scope,
            name,
            namespace,
        });
        Token::new(table::TYPE_REF, self.type_refs.len() as u32)
    }

    /// Opens a type. Fields and methods added after this belong to it, until
    /// the next one is opened.
    pub(crate) fn add_type_def(
        &mut self,
        flags: u32,
        namespace: &str,
        name: &str,
        extends: u32,
    ) -> Token {
        let namespace = self.string(namespace);
        let name = self.string(name);
        self.type_defs.push(TypeDefRow {
            flags,
            name,
            namespace,
            extends,
            first_field: self.fields.len() as u32 + 1,
            first_method: self.methods.len() as u32 + 1,
        });
        Token::new(table::TYPE_DEF, self.type_defs.len() as u32)
    }

    /// Records that the most recently added type implements an interface.
    /// A type's listing of an interface; the row number, which an attribute
    /// on the listing names as its parent.
    pub(crate) fn add_interface_impl(&mut self, class: Token, interface: u32) -> u32 {
        self.interface_impls
            .push((class.0 & 0x00FF_FFFF, interface));
        self.interface_impls.len() as u32
    }

    /// Gives a field the literal value it was declared with.
    pub(crate) fn add_constant(&mut self, field: Token, element_type: u8, value: &[u8]) {
        let value = self.blob(value);
        // A `HasConstant` parent tagged 0 is a `Field`.
        self.constants
            .push(((field.0 & 0x00FF_FFFF) << 2, element_type, value));
    }

    /// The `Param` row of a method's parameter, counted from the method's
    /// first.
    #[must_use]
    pub(crate) fn param_token(&self, method: Token, index: usize) -> Token {
        let row = &self.methods[(method.0 & 0x00FF_FFFF) as usize - 1];
        Token::new(
            table::PARAM,
            row.first_param + u32::from(row.returns_row) + index as u32,
        )
    }

    /// Gives the method just added a `Param` row for its return, sequence 0,
    /// ahead of its parameters' rows: where `[return: X]` goes.
    pub(crate) fn add_return_param(&mut self, method: Token) -> Token {
        let row = &mut self.methods[(method.0 & 0x00FF_FFFF) as usize - 1];
        let first = row.first_param;
        row.returns_row = true;
        let name = self.string("");
        self.params.insert(
            first as usize - 1,
            ParamRow {
                flags: 0,
                sequence: 0,
                name,
            },
        );
        Token::new(table::PARAM, first)
    }

    /// Sets a parameter's `ParamAttributes`: `[out]`, optional, has default.
    pub(crate) fn set_param_flags(&mut self, param: Token, flags: u16) {
        self.params[(param.0 & 0x00FF_FFFF) as usize - 1].flags = flags;
    }

    /// The default value of an optional parameter: a `Constant` row whose
    /// `HasConstant` parent is the `Param`, tagged 1.
    pub(crate) fn add_param_constant(&mut self, param: Token, element_type: u8, value: &[u8]) {
        let value = self.blob(value);
        self.constants
            .push((((param.0 & 0x00FF_FFFF) << 2) | 1, element_type, value));
    }

    pub(crate) fn add_field(&mut self, flags: u16, name: &str, signature: &[u8]) -> Token {
        let name = self.string(name);
        let signature = self.blob(signature);
        self.fields.push(FieldRow {
            flags,
            name,
            signature,
        });
        Token::new(table::FIELD, self.fields.len() as u32)
    }

    /// Adds a method, with its parameters.
    ///
    /// `impl_flags` says who provides the body: zero is the IL blob, and
    /// `Runtime` is the runtime itself, which is how every member of a
    /// delegate is written.
    pub(crate) fn add_method(
        &mut self,
        flags: u16,
        impl_flags: u16,
        name: &str,
        signature: &[u8],
        body_offset: Option<u32>,
        parameters: &[String],
    ) -> Token {
        let name = self.string(name);
        let signature = self.blob(signature);
        let first_param = self.params.len() as u32 + 1;
        for (index, parameter) in parameters.iter().enumerate() {
            let name = self.string(parameter);
            self.params.push(ParamRow {
                flags: 0,
                sequence: index as u16 + 1,
                name,
            });
        }
        self.methods.push(MethodRow {
            body_offset,
            impl_flags,
            flags,
            name,
            signature,
            first_param,
            returns_row: false,
        });
        Token::new(table::METHOD_DEF, self.methods.len() as u32)
    }

    /// Points a method's row at another body. An incremental build writes a
    /// changed body after all the others and leaves the old one where it was,
    /// unreferenced, so that no other method moves.
    pub(crate) fn set_method_body(&mut self, method: Token, offset: u32) {
        let row = (method.0 & 0x00FF_FFFF) as usize;
        self.methods[row - 1].body_offset = Some(offset);
    }

    /// Opens every member to the assembly, for an editor's build that hot
    /// patches reach through `InternalsVisibleTo`: `private` becomes
    /// `internal`, and `protected` and `private protected` become `protected
    /// internal`, on fields, methods and nested types. Nothing outside the
    /// assembly sees more than before, and what Unity serializes — public
    /// fields and `[SerializeField]` ones — is the same. A private virtual
    /// method, an explicit interface implementation, is left as it is.
    pub(crate) fn widen_for_patches(&mut self, unity_owned: &std::collections::HashSet<u32>) {
        const ACCESS: u16 = 0x0007;
        let widened = |access: u16| match access {
            1 => 3,     // private -> assembly
            2 | 4 => 5, // famANDassem, family -> famORassem
            other => other,
        };
        // `initonly` goes too, so that a patch can give a static field the
        // value its changed initializer says and a patched constructor can
        // set a field from outside — but not from a public instance field,
        // which Unity's serializer and JSON libraries would then start
        // writing, nor from an instance field of what Unity serializes — a
        // Unity object, a `[Serializable]` type: an editor reloading keeps
        // the fields of its objects, read back expecting the ones it wrote,
        // and a build without `initonly` there has fields csc's has not.
        // `literal` stays.
        const INIT_ONLY: u16 = 0x0020;
        const STATIC: u16 = 0x0010;
        const PUBLIC: u16 = 6;
        let mut serializable_owned = std::collections::HashSet::new();
        for (index, ty) in self.type_defs.iter().enumerate() {
            // `[Serializable]` is a flag the type's row gets as it is
            // written (a pseudo-attribute's), not one it has yet.
            const TYPE_DEF_TAG: u32 = 3;
            if (ty.flags | self.extra_flags(TYPE_DEF_TAG, index)) & type_attributes::SERIALIZABLE
                == 0
            {
                continue;
            }
            let first = ty.first_field;
            let end = self
                .type_defs
                .get(index + 1)
                .map_or(self.fields.len() as u32 + 1, |next| next.first_field);
            serializable_owned.extend(first..end);
        }
        for (index, field) in self.fields.iter_mut().enumerate() {
            let row = index as u32 + 1;
            let instance = field.flags & STATIC == 0;
            let serialized = instance
                && (field.flags & ACCESS == PUBLIC
                    || unity_owned.contains(&row)
                    || serializable_owned.contains(&row));
            if !serialized {
                field.flags &= !INIT_ONLY;
            }
            field.flags = (field.flags & !ACCESS) | widened(field.flags & ACCESS);
        }
        for method in &mut self.methods {
            if method.flags & method_attributes::VIRTUAL != 0 && method.flags & ACCESS == 1 {
                continue;
            }
            method.flags = (method.flags & !ACCESS) | widened(method.flags & ACCESS);
        }
        const VISIBILITY: u32 = 0x0007;
        for ty in &mut self.type_defs {
            let nested = match ty.flags & VISIBILITY {
                3 => 5,     // nested private -> nested assembly
                4 | 6 => 7, // nested family, famANDassem -> famORassem
                other => other,
            };
            ty.flags = (ty.flags & !VISIBILITY) | nested;
        }
    }

    /// `parent` is a `MemberRefParent` coded index; for a type reference that
    /// is `(type_ref_row << 3) | 1`.
    pub(crate) fn add_member_ref(&mut self, parent: u32, name: &str, signature: &[u8]) -> Token {
        let name = self.string(name);
        let signature = self.blob(signature);
        self.member_refs.push(MemberRefRow {
            parent,
            name,
            signature,
        });
        Token::new(table::MEMBER_REF, self.member_refs.len() as u32)
    }

    /// Opens a type's run of events. Events added after this belong to it.
    pub(crate) fn add_event_map(&mut self, ty: Token) {
        self.event_maps
            .push((ty.0 & 0x00FF_FFFF, self.events.len() as u32 + 1));
    }

    /// An event: its name, its delegate type, and the `add_` and `remove_`
    /// methods that are its accessors (§II.22.13, §II.22.28).
    pub(crate) fn add_event(
        &mut self,
        name: &str,
        event_type: u32,
        add: Option<Token>,
        remove: Option<Token>,
    ) -> Token {
        let name = self.string(name);
        self.events.push((0, name, event_type));
        // A `HasSemantics` parent tagged 0 is an `Event`.
        let parent = (self.events.len() as u32) << 1;
        for (accessor, kind) in [(add, semantics::ADD_ON), (remove, semantics::REMOVE_ON)] {
            if let Some(accessor) = accessor {
                self.method_semantics
                    .push((kind, accessor.0 & 0x00FF_FFFF, parent));
            }
        }
        Token::new(table::EVENT, self.events.len() as u32)
    }

    /// Opens a type's run of properties. Properties added after this belong
    /// to it, the way fields and methods do.
    pub(crate) fn add_property_map(&mut self, ty: Token) {
        self.property_maps
            .push((ty.0 & 0x00FF_FFFF, self.properties.len() as u32 + 1));
    }

    /// Adds a property and ties its accessors to it.
    ///
    /// A property is metadata's way of saying that two methods belong
    /// together; the methods themselves are ordinary. Without these rows an
    /// assembly still runs, and another compiler reading it sees `get_X` and
    /// `set_X` rather than `X`.
    pub(crate) fn add_property(
        &mut self,
        name: &str,
        signature: &[u8],
        getter: Option<Token>,
        setter: Option<Token>,
    ) -> Token {
        let name = self.string(name);
        let signature = self.blob(signature);
        self.properties.push((0, name, signature));
        // A `HasSemantics` parent tagged 1 is a `Property`.
        let parent = ((self.properties.len() as u32) << 1) | 1;
        for (accessor, kind) in [(getter, semantics::GETTER), (setter, semantics::SETTER)] {
            if let Some(accessor) = accessor {
                self.method_semantics
                    .push((kind, accessor.0 & 0x00FF_FFFF, parent));
            }
        }
        Token::new(table::PROPERTY, self.properties.len() as u32)
    }

    /// Names a constructed type, so that an instruction can point at one.
    pub(crate) fn add_type_spec(&mut self, signature: &[u8]) -> Token {
        let signature = self.blob(signature);
        self.type_specs.push(signature);
        Token::new(table::TYPE_SPEC, self.type_specs.len() as u32)
    }

    /// Declares a type parameter of a type. `owner` is a `TypeOrMethodDef`
    /// coded index; for a type that is `(type_def_row << 1) | 0`.
    ///
    /// `flags` carries the variance in its low two bits (§II.23.1.7): without
    /// it the runtime does not know an `ISource<string>` is an
    /// `ISource<object>`, and an interface call through the wider one finds
    /// nothing to dispatch to.
    pub(crate) fn add_generic_param(&mut self, number: u16, flags: u16, owner: u32, name: &str) {
        let name = self.string(name);
        self.generic_params.push((number, flags, owner, name));
    }

    /// The `HasCustomAttribute` parent of an attribute on a type parameter:
    /// `class C<[A] T>`. The row is found when the tables are written.
    pub(crate) fn generic_param_parent(&mut self, owner: u32, number: u16) -> u32 {
        self.generic_param_keys.push((owner, number));
        ((self.generic_param_keys.len() as u32) << 5) | 19
    }

    /// The `HasCustomAttribute` parent of an attribute on the `index`th
    /// constraint of a type parameter. The row is found when the tables are
    /// written.
    pub(crate) fn generic_param_constraint_parent(
        &mut self,
        owner: u32,
        number: u16,
        index: usize,
    ) -> u32 {
        self.constraint_keys.push((owner, number, index));
        ((self.constraint_keys.len() as u32) << 5) | 20
    }

    /// `where T : Base`, which the runtime checks every construction against.
    pub(crate) fn add_generic_param_constraint(
        &mut self,
        owner: u32,
        number: u16,
        constraint: u32,
    ) {
        self.generic_param_constraints
            .push((owner, number, constraint));
    }

    /// Names a constructed *method*. `method` is a `MethodDefOrRef` coded
    /// index: `(row << 1) | 0` for a `MethodDef`, `| 1` for a `MemberRef`.
    pub(crate) fn add_method_spec(&mut self, method: u32, instantiation: &[u8]) -> Token {
        let instantiation = self.blob(instantiation);
        self.method_specs.push((method, instantiation));
        Token::new(table::METHOD_SPEC, self.method_specs.len() as u32)
    }

    /// Says that a method of a type stands in for one it inherits.
    ///
    /// Both methods are `MethodDefOrRef` coded indexes: `(row << 1) | 0` for a
    /// `MethodDef` and `| 1` for a `MemberRef`.
    pub(crate) fn add_method_impl(&mut self, class: Token, body: u32, declaration: u32) {
        self.method_impls
            .push((class.0 & 0x00FF_FFFF, body, declaration));
    }

    /// Records that one type is declared inside another. A nested type's own
    /// row says nothing about where it sits; this table is the only thing that
    /// does.
    /// The row naming an unmanaged library, made once per name.
    pub(crate) fn add_module_ref(&mut self, name: &str) -> u32 {
        let name = self.string(name);
        if let Some(at) = self.module_refs.iter().position(|it| *it == name) {
            return at as u32 + 1;
        }
        self.module_refs.push(name);
        self.module_refs.len() as u32
    }

    /// Says that a method's body is an entry point of an unmanaged library
    /// (§II.22.22).
    pub(crate) fn add_impl_map(&mut self, flags: u16, method: Token, entry: &str, module: u32) {
        let entry = self.string(entry);
        // `MemberForwarded` tags a `MethodDef` with 1.
        let forwarded = ((method.0 & 0x00FF_FFFF) << 1) | 1;
        self.impl_maps.push((flags, forwarded, entry, module));
    }

    /// An embedded resource: where it starts in the resources blob and what
    /// `GetManifestResourceStream` finds it under (§II.22.24). Public, and
    /// implemented in this file, which an `Implementation` of zero says.
    pub(crate) fn add_manifest_resource(&mut self, offset: u32, name: &str) {
        let name = self.string(name);
        self.manifest_resources.push((offset, 0x0001, name));
    }

    /// The version `[assembly: AssemblyVersion]` gives the assembly.
    pub(crate) fn set_assembly_version(&mut self, version: [u16; 4]) {
        self.assembly_version = version;
    }

    /// The culture `[assembly: AssemblyCulture]` gives the assembly.
    pub(crate) fn set_assembly_culture(&mut self, culture: &str) {
        self.assembly_culture = if culture.is_empty() {
            0
        } else {
            self.string(culture)
        };
    }

    /// The `AssemblyFlags` `[assembly: AssemblyFlags]` sets.
    pub(crate) fn set_assembly_flags(&mut self, flags: u32) {
        self.assembly_flags = flags;
    }

    /// The hash algorithm `[assembly: AssemblyAlgorithmId]` names.
    pub(crate) fn set_hash_algorithm(&mut self, algorithm: u32) {
        self.hash_algorithm = algorithm;
    }

    /// Adds flags to the row a `HasCustomAttribute` coded index names, as a
    /// pseudo-attribute written on it asks.
    pub(crate) fn add_row_flags(&mut self, parent: u32, flags: u32) {
        *self.row_flags.entry(parent).or_default() |= flags;
    }

    /// The flags pseudo-attributes add to one row, by the tag its
    /// `HasCustomAttribute` coded index has.
    fn extra_flags(&self, tag: u32, row: usize) -> u32 {
        self.row_flags
            .get(&(((row as u32 + 1) << 5) | tag))
            .copied()
            .unwrap_or(0)
    }

    /// How a field or a parameter is marshalled, `[MarshalAs]`'s descriptor
    /// (§II.23.4): a `FieldMarshal` row, whose presence is what sets the
    /// `HasFieldMarshal` flag on the row it names. The parent is given as
    /// the `HasCustomAttribute` coded index the attribute was written for.
    pub(crate) fn add_field_marshal(&mut self, parent: u32, descriptor: &[u8]) {
        // A `HasFieldMarshal` parent tagged 0 is a `Field`, 1 a `Param`.
        let parent = match parent & 0x1F {
            1 => (parent >> 5) << 1,
            4 => ((parent >> 5) << 1) | 1,
            _ => return,
        };
        let descriptor = self.blob(descriptor);
        self.field_marshals.push((parent, descriptor));
    }

    /// Fixes a type's size and packing: the struct behind `fixed byte
    /// Buffer[256]` is 256 bytes whatever its one field says.
    pub(crate) fn add_class_layout(&mut self, ty: Token, packing: u16, size: u32) {
        self.class_layouts.push((packing, size, ty.0 & 0x00FF_FFFF));
    }

    /// Places a field at a byte offset inside a type with explicit layout.
    pub(crate) fn add_field_layout(&mut self, field: Token, offset: u32) {
        self.field_layouts.push((offset, field.0 & 0x00FF_FFFF));
    }

    /// Says where in the image a field's initial bytes are.
    pub(crate) fn add_field_rva(&mut self, field: Token, rva: u32) {
        self.field_rvas.push((rva, field.0 & 0x00FF_FFFF));
    }

    pub(crate) fn add_nested_class(&mut self, nested: Token, enclosing: Token) {
        self.nested_classes
            .push((nested.0 & 0x00FF_FFFF, enclosing.0 & 0x00FF_FFFF));
    }

    /// An attribute on something, with its arguments already encoded.
    ///
    /// The parent is a `HasCustomAttribute` coded index and the constructor a
    /// `CustomAttributeType` one — the two widest coded indexes in the
    /// format, which is why neither is a plain token here.
    pub(crate) fn add_custom_attribute(&mut self, parent: u32, constructor: u32, value: &[u8]) {
        let value = self.blob(value);
        self.custom_attributes.push((parent, constructor, value));
    }

    pub(crate) fn add_stand_alone_sig(&mut self, signature: &[u8]) -> Token {
        let signature = self.blob(signature);
        self.stand_alone_sigs.push(signature);
        Token::new(table::STAND_ALONE_SIG, self.stand_alone_sigs.len() as u32)
    }

    // -- writing -----------------------------------------------------------

    /// Whether a heap needs four-byte offsets rather than two.
    fn heap_sizes(&self) -> u8 {
        let mut sizes = 0u8;
        if self.strings.len() > 0xFFFF {
            sizes |= 0x01;
        }
        // The GUID heap holds exactly one entry, so it is never large.
        if self.blobs.len() > 0xFFFF {
            sizes |= 0x04;
        }
        sizes
    }

    /// The tables and how many rows each has, in ascending table order.
    ///
    /// The order is not a convention: the row counts in the stream header and
    /// the rows themselves are both read in table order, with nothing to say
    /// which table is which, so a table out of place makes the whole stream
    /// unreadable from that point on.
    fn row_counts(&self) -> [(u8, u32); 31] {
        [
            (table::MODULE, 1),
            (table::TYPE_REF, self.type_refs.len() as u32),
            (table::TYPE_DEF, self.type_defs.len() as u32),
            (table::FIELD, self.fields.len() as u32),
            (table::METHOD_DEF, self.methods.len() as u32),
            (table::PARAM, self.params.len() as u32),
            (table::INTERFACE_IMPL, self.interface_impls.len() as u32),
            (table::MEMBER_REF, self.member_refs.len() as u32),
            (table::CONSTANT, self.constants.len() as u32),
            (table::CUSTOM_ATTRIBUTE, self.custom_attributes.len() as u32),
            (table::FIELD_MARSHAL, self.field_marshals.len() as u32),
            (table::CLASS_LAYOUT, self.class_layouts.len() as u32),
            (table::FIELD_LAYOUT, self.field_layouts.len() as u32),
            (table::STAND_ALONE_SIG, self.stand_alone_sigs.len() as u32),
            (table::EVENT_MAP, self.event_maps.len() as u32),
            (table::EVENT, self.events.len() as u32),
            (table::PROPERTY_MAP, self.property_maps.len() as u32),
            (table::PROPERTY, self.properties.len() as u32),
            (table::METHOD_SEMANTICS, self.method_semantics.len() as u32),
            (table::METHOD_IMPL, self.method_impls.len() as u32),
            (table::MODULE_REF, self.module_refs.len() as u32),
            (table::TYPE_SPEC, self.type_specs.len() as u32),
            (table::IMPL_MAP, self.impl_maps.len() as u32),
            (table::FIELD_RVA, self.field_rvas.len() as u32),
            (table::ASSEMBLY, 1),
            (table::ASSEMBLY_REF, self.assembly_refs.len() as u32),
            (
                table::MANIFEST_RESOURCE,
                self.manifest_resources.len() as u32,
            ),
            (table::NESTED_CLASS, self.nested_classes.len() as u32),
            (table::GENERIC_PARAM, self.generic_params.len() as u32),
            (table::METHOD_SPEC, self.method_specs.len() as u32),
            (
                table::GENERIC_PARAM_CONSTRAINT,
                self.generic_param_constraints.len() as u32,
            ),
        ]
    }

    fn rows_in(&self, table: u8) -> u32 {
        self.row_counts()
            .iter()
            .find(|(number, _)| *number == table)
            .map_or(0, |(_, rows)| *rows)
    }

    /// Serialises the whole metadata root: the header, the stream headers and
    /// the streams.
    ///
    /// `il_rva` is where the IL blob will land, which is the only thing the
    /// tables need that the metadata itself does not know.
    #[must_use]
    pub(crate) fn write(&self, il_rva: u32) -> Vec<u8> {
        let tables = self.write_tables(il_rva);

        // Every stream is four-byte aligned, and each header names the offset
        // from the start of the root.
        let streams: [(&str, &[u8]); 5] = [
            ("#~", &tables),
            ("#Strings", &self.strings.bytes),
            ("#US", &self.user_strings.bytes),
            ("#GUID", &self.guid),
            ("#Blob", &self.blobs.bytes),
        ];

        const VERSION: &[u8] = b"v4.0.30319\0\0";
        let header_size = 16 + VERSION.len() + 4;
        let headers_size: usize = streams
            .iter()
            .map(|(name, _)| 8 + align4(name.len() + 1))
            .sum();

        let mut root = Vec::new();
        root.extend_from_slice(&0x424A_5342u32.to_le_bytes()); // "BSJB"
        root.extend_from_slice(&1u16.to_le_bytes());
        root.extend_from_slice(&1u16.to_le_bytes());
        root.extend_from_slice(&0u32.to_le_bytes());
        root.extend_from_slice(&(VERSION.len() as u32).to_le_bytes());
        root.extend_from_slice(VERSION);
        root.extend_from_slice(&0u16.to_le_bytes()); // flags
        root.extend_from_slice(&(streams.len() as u16).to_le_bytes());

        let mut offset = (header_size + headers_size) as u32;
        for (name, bytes) in &streams {
            root.extend_from_slice(&offset.to_le_bytes());
            root.extend_from_slice(&(align4(bytes.len()) as u32).to_le_bytes());
            let mut name_bytes = name.as_bytes().to_vec();
            name_bytes.push(0);
            while name_bytes.len() % 4 != 0 {
                name_bytes.push(0);
            }
            root.extend_from_slice(&name_bytes);
            offset += align4(bytes.len()) as u32;
        }
        debug_assert_eq!(root.len(), header_size + headers_size);

        for (_, bytes) in &streams {
            root.extend_from_slice(bytes);
            while root.len() % 4 != 0 {
                root.push(0);
            }
        }
        root
    }

    fn write_tables(&self, il_rva: u32) -> Vec<u8> {
        let heap_sizes = self.heap_sizes();
        let string_wide = heap_sizes & 0x01 != 0;
        let blob_wide = heap_sizes & 0x04 != 0;

        let present = self.row_counts();
        debug_assert!(
            present.windows(2).all(|pair| pair[0].0 < pair[1].0),
            "the tables must be listed in ascending order",
        );
        let mut valid = 0u64;
        for (number, rows) in present {
            if rows > 0 {
                valid |= 1u64 << number;
            }
        }

        let mut stream = Vec::new();
        stream.extend_from_slice(&0u32.to_le_bytes()); // reserved
        stream.push(2); // major
        stream.push(0); // minor
        stream.push(heap_sizes);
        stream.push(1); // reserved
        stream.extend_from_slice(&valid.to_le_bytes());
        // `InterfaceImpl` is one of the tables the spec requires to be sorted,
        // and it is built in type order, which is that order.
        let sorted = (1u64 << table::INTERFACE_IMPL)
            | (1u64 << table::CONSTANT)
            | (1u64 << table::CUSTOM_ATTRIBUTE)
            | (1u64 << table::FIELD_MARSHAL)
            | (1u64 << table::CLASS_LAYOUT)
            | (1u64 << table::FIELD_LAYOUT)
            | (1u64 << table::EVENT_MAP)
            | (1u64 << table::PROPERTY_MAP)
            | (1u64 << table::METHOD_SEMANTICS)
            | (1u64 << table::METHOD_IMPL)
            | (1u64 << table::IMPL_MAP)
            | (1u64 << table::NESTED_CLASS)
            | (1u64 << table::GENERIC_PARAM)
            | (1u64 << table::GENERIC_PARAM_CONSTRAINT);
        stream.extend_from_slice(&sorted.to_le_bytes());
        for (_, rows) in present {
            if rows > 0 {
                stream.extend_from_slice(&rows.to_le_bytes());
            }
        }

        let mut out = Writer {
            bytes: stream,
            string_wide,
            blob_wide,
        };

        // Module: generation, name, mvid, encid, encbaseid.
        out.u16(0);
        out.string(self.module_name);
        out.index(1, 1); // the GUID heap's single entry
        out.index(0, 1);
        out.index(0, 1);

        // TypeRef: resolution scope, name, namespace.
        let scope_rows = self
            .rows_in(table::MODULE)
            .max(self.rows_in(table::MODULE_REF))
            .max(self.rows_in(table::ASSEMBLY_REF))
            .max(self.rows_in(table::TYPE_REF));
        for row in &self.type_refs {
            out.coded(row.scope, scope_rows, 2);
            out.string(row.name);
            out.string(row.namespace);
        }

        // TypeDef: flags, name, namespace, extends, fields, methods.
        let type_rows = self
            .rows_in(table::TYPE_DEF)
            .max(self.rows_in(table::TYPE_REF))
            .max(self.rows_in(table::TYPE_SPEC));
        for (at, row) in self.type_defs.iter().enumerate() {
            // A `HasCustomAttribute` parent tagged 3 is a `TypeDef`.
            out.u32(row.flags | self.extra_flags(3, at));
            out.string(row.name);
            out.string(row.namespace);
            out.coded(row.extends, type_rows, 2);
            out.index(self.rows_in(table::FIELD), row.first_field);
            out.index(self.rows_in(table::METHOD_DEF), row.first_method);
        }

        // A row `FieldMarshal` names says so in its flags: `HasFieldMarshal`
        // is 0x1000 on a field and 0x2000 on a parameter.
        let parents: std::collections::HashSet<u32> = self
            .field_marshals
            .iter()
            .map(|(parent, _)| *parent)
            .collect();
        let marshalled = |tag: u32, row: usize| parents.contains(&(((row as u32 + 1) << 1) | tag));

        // Field: flags, name, signature.
        for (at, row) in self.fields.iter().enumerate() {
            let extra = self.extra_flags(1, at) as u16;
            out.u16(row.flags | extra | if marshalled(0, at) { 0x1000 } else { 0 });
            out.string(row.name);
            out.blob(row.signature);
        }

        // MethodDef: rva, impl flags, flags, name, signature, params.
        for (at, row) in self.methods.iter().enumerate() {
            out.u32(row.body_offset.map_or(0, |offset| il_rva + offset));
            out.u16(row.impl_flags);
            out.u16(row.flags | self.extra_flags(0, at) as u16);
            out.string(row.name);
            out.blob(row.signature);
            out.index(self.rows_in(table::PARAM), row.first_param);
        }

        // Param: flags, sequence, name.
        for (at, row) in self.params.iter().enumerate() {
            out.u16(row.flags | if marshalled(1, at) { 0x2000 } else { 0 });
            out.u16(row.sequence);
            out.string(row.name);
        }

        // InterfaceImpl: class, interface.
        for (class, interface) in &self.interface_impls {
            out.index(self.rows_in(table::TYPE_DEF), *class);
            out.coded(*interface, type_rows, 2);
        }

        // MemberRef: class, name, signature. A `MemberRefParent` names a
        // `TypeDef`, `TypeRef`, `ModuleRef`, `MethodDef` or `TypeSpec`.
        let parent_rows = type_rows
            .max(self.rows_in(table::MODULE_REF))
            .max(self.rows_in(table::METHOD_DEF));
        for row in &self.member_refs {
            out.coded(row.parent, parent_rows, 3);
            out.string(row.name);
            out.blob(row.signature);
        }

        // Constant: type, padding, parent, value. A `HasConstant` parent
        // tagged 0 is a `Field`.
        let has_constant_rows = self
            .rows_in(table::FIELD)
            .max(self.rows_in(table::PARAM))
            .max(self.rows_in(table::PROPERTY));
        // The table is sorted by parent, which §II.22 requires; fields and
        // parameters are added in different passes, so the order is imposed
        // here.
        let mut constants = self.constants.clone();
        constants.sort_by_key(|(parent, _, _)| *parent);
        for (parent, element_type, value) in &constants {
            out.u16(u16::from(*element_type));
            out.coded(*parent, has_constant_rows, 2);
            out.blob(*value);
        }

        // CustomAttribute: parent, type, value. Sorted by parent, which
        // §II.22 requires and the runtime relies on to find a type's
        // attributes without reading the whole table.
        let has_custom_attribute_rows = [
            table::METHOD_DEF,
            table::FIELD,
            table::TYPE_REF,
            table::TYPE_DEF,
            table::PARAM,
            table::INTERFACE_IMPL,
            table::MEMBER_REF,
            table::MODULE,
            table::PROPERTY,
            table::EVENT,
            table::STAND_ALONE_SIG,
            table::MODULE_REF,
            table::TYPE_SPEC,
            table::ASSEMBLY,
            table::ASSEMBLY_REF,
            table::MANIFEST_RESOURCE,
            table::GENERIC_PARAM,
            table::GENERIC_PARAM_CONSTRAINT,
            table::METHOD_SPEC,
        ]
        .into_iter()
        .map(|table| self.rows_in(table))
        .max()
        .unwrap_or(0);
        let custom_attribute_type_rows = self
            .rows_in(table::METHOD_DEF)
            .max(self.rows_in(table::MEMBER_REF));
        // An attribute on a type parameter names it by owner and number
        // until here, where the rows are sorted as the table below is.
        let mut sorted_parameters = self.generic_params.clone();
        sorted_parameters.sort_by_key(|(number, _, owner, _)| (*owner, *number));
        // So does one on a constraint: the rows are sorted by parameter,
        // each parameter's in the order they were added.
        let mut constraint_rows: Vec<(usize, u32, u16, usize)> = Vec::new();
        {
            let mut seen: HashMap<(u32, u16), usize> = HashMap::new();
            for (owner, number, _) in &self.generic_param_constraints {
                let index = seen.entry((*owner, *number)).or_default();
                let row = sorted_parameters
                    .iter()
                    .position(|(at, _, of, _)| of == owner && at == number)
                    .unwrap_or(usize::MAX);
                constraint_rows.push((row, *owner, *number, *index));
                *index += 1;
            }
            constraint_rows.sort_by_key(|(row, _, _, _)| *row);
        }
        let mut attributes: Vec<(u32, u32, u32)> = self
            .custom_attributes
            .iter()
            .map(|(parent, constructor, value)| {
                if parent & 0x1F == 20 {
                    let row = self
                        .constraint_keys
                        .get(((parent >> 5) as usize).wrapping_sub(1))
                        .and_then(|(owner, number, index)| {
                            constraint_rows.iter().position(|(_, of, at, which)| {
                                of == owner && at == number && which == index
                            })
                        })
                        .map_or(0, |row| row as u32 + 1);
                    return ((row << 5) | 20, *constructor, *value);
                }
                if parent & 0x1F != 19 {
                    return (*parent, *constructor, *value);
                }
                let row = self
                    .generic_param_keys
                    .get(((parent >> 5) as usize).wrapping_sub(1))
                    .and_then(|(owner, number)| {
                        sorted_parameters
                            .iter()
                            .position(|(at, _, of, _)| of == owner && at == number)
                    })
                    .map_or(0, |row| row as u32 + 1);
                ((row << 5) | 19, *constructor, *value)
            })
            .collect();
        attributes.sort_by_key(|(parent, _, _)| *parent);
        for (parent, constructor, value) in &attributes {
            out.coded(*parent, has_custom_attribute_rows, 5);
            out.coded(*constructor, custom_attribute_type_rows, 3);
            out.blob(*value);
        }

        // FieldMarshal: parent, native type, sorted by parent.
        let has_field_marshal_rows = self.rows_in(table::FIELD).max(self.rows_in(table::PARAM));
        let mut marshals = self.field_marshals.clone();
        marshals.sort_by_key(|(parent, _)| *parent);
        for (parent, descriptor) in &marshals {
            out.coded(*parent, has_field_marshal_rows, 1);
            out.blob(*descriptor);
        }

        // ClassLayout: packing size, class size, parent, sorted by parent.
        let mut layouts = self.class_layouts.clone();
        layouts.sort_by_key(|(_, _, parent)| *parent);
        for (packing, size, parent) in &layouts {
            out.u16(*packing);
            out.u32(*size);
            out.index(self.rows_in(table::TYPE_DEF), *parent);
        }

        // FieldLayout: offset, field, sorted by field.
        let mut placed = self.field_layouts.clone();
        placed.sort_by_key(|(_, field)| *field);
        for (offset, field) in &placed {
            out.u32(*offset);
            out.index(self.rows_in(table::FIELD), *field);
        }

        // StandAloneSig: signature.
        for signature in &self.stand_alone_sigs {
            out.blob(*signature);
        }

        // EventMap: parent, event list.
        for (parent, first) in &self.event_maps {
            out.index(self.rows_in(table::TYPE_DEF), *parent);
            out.index(self.rows_in(table::EVENT), *first);
        }

        // Event: flags, name, type.
        for (at, (flags, name, event_type)) in self.events.iter().enumerate() {
            out.u16(*flags | self.extra_flags(10, at) as u16);
            out.string(*name);
            out.coded(*event_type, type_rows, 2);
        }

        // PropertyMap: parent, property list.
        for (parent, first) in &self.property_maps {
            out.index(self.rows_in(table::TYPE_DEF), *parent);
            out.index(self.rows_in(table::PROPERTY), *first);
        }

        // Property: flags, name, signature.
        for (at, (flags, name, signature)) in self.properties.iter().enumerate() {
            out.u16(*flags | self.extra_flags(9, at) as u16);
            out.string(*name);
            out.blob(*signature);
        }

        // MethodSemantics: semantics, method, association. `HasSemantics`
        // names `Event` and `Property` and nothing else — the method is a
        // plain row number beside it, and letting it into this width is what
        // shifts every table after `MethodSemantics` once methods pass 32768.
        let has_semantics_rows = self
            .rows_in(table::EVENT)
            .max(self.rows_in(table::PROPERTY));
        // Sorted by association (§II.22.28), which the runtime binary-searches
        // on: a type with both events and properties adds a property's rows
        // before an event's, whose coded index is the smaller.
        let mut method_semantics = self.method_semantics.clone();
        method_semantics.sort_by_key(|(_, _, parent)| *parent);
        for (kind, method, parent) in &method_semantics {
            out.u16(*kind);
            out.index(self.rows_in(table::METHOD_DEF), *method);
            out.coded(*parent, has_semantics_rows, 1);
        }

        // MethodImpl: class, body, declaration. Sorted by class, which is
        // what the spec requires and what the runtime binary-searches on.
        let method_def_or_ref_rows = self
            .rows_in(table::METHOD_DEF)
            .max(self.rows_in(table::MEMBER_REF));
        let mut method_impls = self.method_impls.clone();
        method_impls.sort_by_key(|(class, _, _)| *class);
        for (class, body, declaration) in &method_impls {
            out.index(self.rows_in(table::TYPE_DEF), *class);
            out.coded(*body, method_def_or_ref_rows, 1);
            out.coded(*declaration, method_def_or_ref_rows, 1);
        }

        // ModuleRef: name.
        for name in &self.module_refs {
            out.string(*name);
        }

        // TypeSpec: signature.
        for signature in &self.type_specs {
            out.blob(*signature);
        }

        // ImplMap: mapping flags, member forwarded, import name, import
        // scope. Sorted by the member, which the spec requires.
        let member_forwarded_rows = self
            .rows_in(table::FIELD)
            .max(self.rows_in(table::METHOD_DEF));
        let mut impl_maps = self.impl_maps.clone();
        impl_maps.sort_by_key(|(_, forwarded, _, _)| *forwarded);
        for (flags, forwarded, entry, module) in &impl_maps {
            out.u16(*flags);
            out.coded(*forwarded, member_forwarded_rows, 1);
            out.string(*entry);
            out.index(self.rows_in(table::MODULE_REF), *module);
        }

        // FieldRVA: RVA, field, sorted by field.
        let mut data = self.field_rvas.clone();
        data.sort_by_key(|(_, field)| *field);
        for (rva, field) in &data {
            out.u32(*rva);
            out.index(self.rows_in(table::FIELD), *field);
        }

        // Assembly: hash algorithm, version, flags, public key, name, culture.
        out.u32(self.hash_algorithm);
        for part in self.assembly_version {
            out.u16(part);
        }
        out.u32(self.assembly_flags);
        out.blob(0);
        out.string(self.assembly_name);
        out.string(self.assembly_culture);

        // AssemblyRef: version, flags, public key, name, culture, hash.
        for row in &self.assembly_refs {
            for part in row.version {
                out.u16(part);
            }
            out.u32(0);
            out.blob(row.public_key);
            out.string(row.name);
            out.string(0);
            out.blob(0);
        }

        // ManifestResource: offset, flags, name, implementation. The last
        // is an `Implementation` coded index over `File`, `AssemblyRef` and
        // `ExportedType`, and zero for a resource in this file.
        let implementation_rows = self.rows_in(table::ASSEMBLY_REF);
        for (offset, flags, name) in &self.manifest_resources {
            out.u32(*offset);
            out.u32(*flags);
            out.string(*name);
            out.coded(0, implementation_rows, 2);
        }

        // NestedClass: the nested type and the one it sits in, sorted by the
        // nested type, which §II.22 requires.
        let type_def_rows = self.rows_in(table::TYPE_DEF);
        let mut nested = self.nested_classes.clone();
        nested.sort_unstable();
        for (inner, outer) in &nested {
            out.index(type_def_rows, *inner);
            out.index(type_def_rows, *outer);
        }

        // GenericParam: number, flags, owner, name. A `TypeOrMethodDef` owner
        // tagged 0 is a `TypeDef`.
        let owner_rows = self
            .rows_in(table::TYPE_DEF)
            .max(self.rows_in(table::METHOD_DEF));
        // The table is one of those the spec requires sorted, and a type's
        // parameters and a method's are built at different times, so the order
        // is imposed here rather than assumed.
        let mut generic_params = self.generic_params.clone();
        generic_params.sort_by_key(|(number, _, owner, _)| (*owner, *number));
        for (number, flags, owner, name) in &generic_params {
            out.u16(*number);
            out.u16(*flags);
            out.coded(*owner, owner_rows, 1);
            out.string(*name);
        }

        // MethodSpec: the method and what it was instantiated with. A
        // `MethodDefOrRef` tagged 0 is a `MethodDef`.
        let method_rows = self
            .rows_in(table::METHOD_DEF)
            .max(self.rows_in(table::MEMBER_REF));
        for (method, instantiation) in &self.method_specs {
            out.coded(*method, method_rows, 1);
            out.blob(*instantiation);
        }

        // GenericParamConstraint: the parameter and what it is constrained to.
        // The parameter is found by owner and position, because the rows above
        // were just sorted and a row number from before that means nothing.
        // Looked up, not searched for: a search per constraint is the
        // square of how many type parameters a large project has.
        let parameter_rows: HashMap<(u32, u16), u32> = generic_params
            .iter()
            .enumerate()
            .rev()
            .map(|(row, (number, _, owner, _))| ((*owner, *number), row as u32 + 1))
            .collect();
        let mut constraints: Vec<(u32, u32)> = self
            .generic_param_constraints
            .iter()
            .filter_map(|(owner, number, constraint)| {
                let row = parameter_rows.get(&(*owner, *number))?;
                Some((*row, *constraint))
            })
            .collect();
        // Sorted by owner, which the runtime binary-searches on.
        constraints.sort_by_key(|(parameter, _)| *parameter);
        for (parameter, constraint) in &constraints {
            out.index(self.rows_in(table::GENERIC_PARAM), *parameter);
            // A `TypeDefOrRef`: as wide as the largest of `TypeDef`,
            // `TypeRef` and `TypeSpec` calls for — the same `type_rows` an
            // `extends` or an `InterfaceImpl` is written with. Written at
            // `TypeDef`'s width alone, a project with more constructed
            // types than declared ones (every `List<T>` it names is one)
            // wrote two bytes where a reader takes four, and every row
            // after the first was read out of place.
            out.coded(*constraint, type_rows, 2);
        }

        out.bytes
    }
}

/// Writes table columns at the widths the row counts call for.
struct Writer {
    bytes: Vec<u8>,
    string_wide: bool,
    blob_wide: bool,
}

impl Writer {
    fn u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn string(&mut self, offset: u32) {
        if self.string_wide {
            self.u32(offset);
        } else {
            self.u16(offset as u16);
        }
    }

    fn blob(&mut self, offset: u32) {
        if self.blob_wide {
            self.u32(offset);
        } else {
            self.u16(offset as u16);
        }
    }

    /// A simple index into a table: two bytes while the table is small.
    fn index(&mut self, rows: u32, value: u32) {
        if rows > 0xFFFF {
            self.u32(value);
        } else {
            self.u16(value as u16);
        }
    }

    /// A coded index, whose width depends on the largest table it can name and
    /// on how many bits the tag takes from it.
    fn coded(&mut self, value: u32, rows: u32, tag_bits: u32) {
        if rows >= (1u32 << (16 - tag_bits)) {
            self.u32(value);
        } else {
            self.u16(value as u16);
        }
    }
}

const fn align4(value: usize) -> usize {
    value.div_ceil(4) * 4
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_string_heap_starts_with_a_zero_and_interns() {
        let mut metadata = Metadata::new("A.dll", "A");
        let first = metadata.string("Program");
        let again = metadata.string("Program");
        assert_eq!(first, again);
        assert_eq!(metadata.strings.bytes[0], 0);
        assert_eq!(metadata.string(""), 0);
    }

    #[test]
    fn a_blob_carries_its_length() {
        let mut metadata = Metadata::new("A.dll", "A");
        let offset = metadata.blob(&[0x20, 0x00, 0x08]);
        let start = offset as usize;
        assert_eq!(metadata.blobs.bytes[start], 3);
        assert_eq!(&metadata.blobs.bytes[start + 1..start + 4], &[0x20, 0, 8]);
    }

    #[test]
    fn a_user_string_is_utf16_with_a_trailing_flag() {
        let mut metadata = Metadata::new("A.dll", "A");
        let token = metadata.user_string("hi");
        assert_eq!(token.0 & 0xFF00_0000, 0x7000_0000);
        let start = (token.0 & 0x00FF_FFFF) as usize;
        // Length 5: two characters of two bytes each, plus the flag.
        assert_eq!(metadata.user_strings.bytes[start], 5);
        assert_eq!(
            &metadata.user_strings.bytes[start + 1..start + 6],
            &[b'h', 0, b'i', 0, 0]
        );
    }

    #[test]
    fn a_string_needing_more_than_ascii_sets_the_flag() {
        let mut metadata = Metadata::new("A.dll", "A");
        let token = metadata.user_string("\u{41F}");
        let start = (token.0 & 0x00FF_FFFF) as usize;
        assert_eq!(metadata.user_strings.bytes[start + 3], 1);
    }

    #[test]
    fn a_type_points_at_where_its_members_start() {
        let mut metadata = Metadata::new("A.dll", "A");
        metadata.add_type_def(0, "", "First", 0);
        metadata.add_field(0, "a", &[0x06, 0x08]);
        metadata.add_method(0, 0, "M", &[0x00, 0x00, 0x01], Some(0), &[]);
        metadata.add_type_def(0, "", "Second", 0);
        assert_eq!(metadata.type_defs[0].first_field, 1);
        assert_eq!(metadata.type_defs[0].first_method, 1);
        assert_eq!(metadata.type_defs[1].first_field, 2);
        assert_eq!(metadata.type_defs[1].first_method, 2);
    }

    #[test]
    fn the_root_starts_with_its_signature_and_is_aligned() {
        let metadata = Metadata::new("A.dll", "A");
        let bytes = metadata.write(0x2050);
        assert_eq!(&bytes[..4], b"BSJB");
        assert_eq!(bytes.len() % 4, 0);
        // Five streams, named in the header after the version string.
        assert_eq!(u16::from_le_bytes([bytes[30], bytes[31]]), 5);
    }
}
