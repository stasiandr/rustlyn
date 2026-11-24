//! The shape of every metadata table, as §II.22 lays them out.
//!
//! This has to be complete rather than just cover what rustlyn emits. A row's
//! width depends on the widths of the columns before it, and a table's rows
//! are laid end to end with nothing between them — so reaching table 0x2A
//! means having correctly stepped over every table before it, including ones
//! nothing here models. A table whose shape is wrong does not fail: it shifts
//! everything after it, and the numbers that come out are plausible and wrong.

/// The tables, by the number the stream header orders them with.
pub mod table {
    pub const MODULE: u8 = 0x00;
    pub const TYPE_REF: u8 = 0x01;
    pub const TYPE_DEF: u8 = 0x02;
    pub const FIELD_PTR: u8 = 0x03;
    pub const FIELD: u8 = 0x04;
    pub const METHOD_PTR: u8 = 0x05;
    pub const METHOD_DEF: u8 = 0x06;
    pub const PARAM_PTR: u8 = 0x07;
    pub const PARAM: u8 = 0x08;
    pub const INTERFACE_IMPL: u8 = 0x09;
    pub const MEMBER_REF: u8 = 0x0A;
    pub const CONSTANT: u8 = 0x0B;
    pub const CUSTOM_ATTRIBUTE: u8 = 0x0C;
    pub const FIELD_MARSHAL: u8 = 0x0D;
    pub const DECL_SECURITY: u8 = 0x0E;
    pub const CLASS_LAYOUT: u8 = 0x0F;
    pub const FIELD_LAYOUT: u8 = 0x10;
    pub const STAND_ALONE_SIG: u8 = 0x11;
    pub const EVENT_MAP: u8 = 0x12;
    pub const EVENT_PTR: u8 = 0x13;
    pub const EVENT: u8 = 0x14;
    pub const PROPERTY_MAP: u8 = 0x15;
    pub const PROPERTY_PTR: u8 = 0x16;
    pub const PROPERTY: u8 = 0x17;
    pub const METHOD_SEMANTICS: u8 = 0x18;
    pub const METHOD_IMPL: u8 = 0x19;
    pub const MODULE_REF: u8 = 0x1A;
    pub const TYPE_SPEC: u8 = 0x1B;
    pub const IMPL_MAP: u8 = 0x1C;
    pub const FIELD_RVA: u8 = 0x1D;
    pub const ENC_LOG: u8 = 0x1E;
    pub const ENC_MAP: u8 = 0x1F;
    pub const ASSEMBLY: u8 = 0x20;
    pub const ASSEMBLY_PROCESSOR: u8 = 0x21;
    pub const ASSEMBLY_OS: u8 = 0x22;
    pub const ASSEMBLY_REF: u8 = 0x23;
    pub const ASSEMBLY_REF_PROCESSOR: u8 = 0x24;
    pub const ASSEMBLY_REF_OS: u8 = 0x25;
    pub const FILE: u8 = 0x26;
    pub const EXPORTED_TYPE: u8 = 0x27;
    pub const MANIFEST_RESOURCE: u8 = 0x28;
    pub const NESTED_CLASS: u8 = 0x29;
    pub const GENERIC_PARAM: u8 = 0x2A;
    pub const METHOD_SPEC: u8 = 0x2B;
    pub const GENERIC_PARAM_CONSTRAINT: u8 = 0x2C;
}

/// An index that can point into one of several tables, with the choice packed
/// into the low bits.
///
/// The number of tags decides how many bits are spent on them, and what is
/// left decides whether two bytes are enough for the row number.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Coded {
    pub tables: &'static [u8],
    pub bits: u32,
}

impl Coded {
    const fn new(tables: &'static [u8], bits: u32) -> Self {
        Self { tables, bits }
    }

    /// Which table a coded value points into, and which row.
    #[must_use]
    pub fn decode(self, value: u32) -> Option<(u8, u32)> {
        let tag = (value & ((1 << self.bits) - 1)) as usize;
        let row = value >> self.bits;
        self.tables.get(tag).map(|table| (*table, row))
    }
}

use table as t;

pub const TYPE_DEF_OR_REF: Coded = Coded::new(&[t::TYPE_DEF, t::TYPE_REF, t::TYPE_SPEC], 2);
pub const HAS_CONSTANT: Coded = Coded::new(&[t::FIELD, t::PARAM, t::PROPERTY], 2);
pub const HAS_CUSTOM_ATTRIBUTE: Coded = Coded::new(
    &[
        t::METHOD_DEF,
        t::FIELD,
        t::TYPE_REF,
        t::TYPE_DEF,
        t::PARAM,
        t::INTERFACE_IMPL,
        t::MEMBER_REF,
        t::MODULE,
        t::DECL_SECURITY,
        t::PROPERTY,
        t::EVENT,
        t::STAND_ALONE_SIG,
        t::MODULE_REF,
        t::TYPE_SPEC,
        t::ASSEMBLY,
        t::ASSEMBLY_REF,
        t::FILE,
        t::EXPORTED_TYPE,
        t::MANIFEST_RESOURCE,
        t::GENERIC_PARAM,
        t::GENERIC_PARAM_CONSTRAINT,
        t::METHOD_SPEC,
    ],
    5,
);
pub const HAS_FIELD_MARSHAL: Coded = Coded::new(&[t::FIELD, t::PARAM], 1);
pub const HAS_DECL_SECURITY: Coded = Coded::new(&[t::TYPE_DEF, t::METHOD_DEF, t::ASSEMBLY], 2);
pub const MEMBER_REF_PARENT: Coded = Coded::new(
    &[
        t::TYPE_DEF,
        t::TYPE_REF,
        t::MODULE_REF,
        t::METHOD_DEF,
        t::TYPE_SPEC,
    ],
    3,
);
pub const HAS_SEMANTICS: Coded = Coded::new(&[t::EVENT, t::PROPERTY], 1);
pub const METHOD_DEF_OR_REF: Coded = Coded::new(&[t::METHOD_DEF, t::MEMBER_REF], 1);
pub const MEMBER_FORWARDED: Coded = Coded::new(&[t::FIELD, t::METHOD_DEF], 1);
pub const IMPLEMENTATION: Coded = Coded::new(&[t::FILE, t::ASSEMBLY_REF, t::EXPORTED_TYPE], 2);
/// Two of its five tags are unused, and the spec still spends three bits.
pub const CUSTOM_ATTRIBUTE_TYPE: Coded = Coded::new(
    &[
        t::METHOD_DEF,
        t::METHOD_DEF,
        t::METHOD_DEF,
        t::MEMBER_REF,
        t::METHOD_DEF,
    ],
    3,
);
pub const RESOLUTION_SCOPE: Coded =
    Coded::new(&[t::MODULE, t::MODULE_REF, t::ASSEMBLY_REF, t::TYPE_REF], 2);
pub const TYPE_OR_METHOD_DEF: Coded = Coded::new(&[t::TYPE_DEF, t::METHOD_DEF], 1);

/// One column of a row.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Column {
    U8,
    U16,
    U32,
    /// An offset into `#Strings`, `#GUID` or `#Blob`, whose width the header
    /// says.
    String,
    Guid,
    Blob,
    /// A row number in one particular table.
    Row(u8),
    Coded(Coded),
}

/// The columns of a table, in order.
///
/// A table nothing here reads still needs its shape, because the tables are
/// laid end to end and a wrong width shifts every table after it.
#[must_use]
pub fn columns(number: u8) -> &'static [Column] {
    use Column as C;
    match number {
        t::MODULE => &[C::U16, C::String, C::Guid, C::Guid, C::Guid],
        t::TYPE_REF => &[C::Coded(RESOLUTION_SCOPE), C::String, C::String],
        t::TYPE_DEF => &[
            C::U32,
            C::String,
            C::String,
            C::Coded(TYPE_DEF_OR_REF),
            C::Row(t::FIELD),
            C::Row(t::METHOD_DEF),
        ],
        t::FIELD_PTR => &[C::Row(t::FIELD)],
        t::FIELD => &[C::U16, C::String, C::Blob],
        t::METHOD_PTR => &[C::Row(t::METHOD_DEF)],
        t::METHOD_DEF => &[C::U32, C::U16, C::U16, C::String, C::Blob, C::Row(t::PARAM)],
        t::PARAM_PTR => &[C::Row(t::PARAM)],
        t::PARAM => &[C::U16, C::U16, C::String],
        t::INTERFACE_IMPL => &[C::Row(t::TYPE_DEF), C::Coded(TYPE_DEF_OR_REF)],
        t::MEMBER_REF => &[C::Coded(MEMBER_REF_PARENT), C::String, C::Blob],
        // The type is one byte with one of padding after it.
        t::CONSTANT => &[C::U8, C::U8, C::Coded(HAS_CONSTANT), C::Blob],
        t::CUSTOM_ATTRIBUTE => &[
            C::Coded(HAS_CUSTOM_ATTRIBUTE),
            C::Coded(CUSTOM_ATTRIBUTE_TYPE),
            C::Blob,
        ],
        t::FIELD_MARSHAL => &[C::Coded(HAS_FIELD_MARSHAL), C::Blob],
        t::DECL_SECURITY => &[C::U16, C::Coded(HAS_DECL_SECURITY), C::Blob],
        t::CLASS_LAYOUT => &[C::U16, C::U32, C::Row(t::TYPE_DEF)],
        t::FIELD_LAYOUT => &[C::U32, C::Row(t::FIELD)],
        t::STAND_ALONE_SIG => &[C::Blob],
        t::EVENT_MAP => &[C::Row(t::TYPE_DEF), C::Row(t::EVENT)],
        t::EVENT_PTR => &[C::Row(t::EVENT)],
        t::EVENT => &[C::U16, C::String, C::Coded(TYPE_DEF_OR_REF)],
        t::PROPERTY_MAP => &[C::Row(t::TYPE_DEF), C::Row(t::PROPERTY)],
        t::PROPERTY_PTR => &[C::Row(t::PROPERTY)],
        t::PROPERTY => &[C::U16, C::String, C::Blob],
        t::METHOD_SEMANTICS => &[C::U16, C::Row(t::METHOD_DEF), C::Coded(HAS_SEMANTICS)],
        t::METHOD_IMPL => &[
            C::Row(t::TYPE_DEF),
            C::Coded(METHOD_DEF_OR_REF),
            C::Coded(METHOD_DEF_OR_REF),
        ],
        t::MODULE_REF => &[C::String],
        t::TYPE_SPEC => &[C::Blob],
        t::IMPL_MAP => &[
            C::U16,
            C::Coded(MEMBER_FORWARDED),
            C::String,
            C::Row(t::MODULE_REF),
        ],
        t::FIELD_RVA => &[C::U32, C::Row(t::FIELD)],
        t::ENC_LOG => &[C::U32, C::U32],
        t::ENC_MAP => &[C::U32],
        t::ASSEMBLY => &[
            C::U32,
            C::U16,
            C::U16,
            C::U16,
            C::U16,
            C::U32,
            C::Blob,
            C::String,
            C::String,
        ],
        t::ASSEMBLY_PROCESSOR => &[C::U32],
        t::ASSEMBLY_OS => &[C::U32, C::U32, C::U32],
        t::ASSEMBLY_REF => &[
            C::U16,
            C::U16,
            C::U16,
            C::U16,
            C::U32,
            C::Blob,
            C::String,
            C::String,
            C::Blob,
        ],
        t::ASSEMBLY_REF_PROCESSOR => &[C::U32, C::Row(t::ASSEMBLY_REF)],
        t::ASSEMBLY_REF_OS => &[C::U32, C::U32, C::U32, C::Row(t::ASSEMBLY_REF)],
        t::FILE => &[C::U32, C::String, C::Blob],
        t::EXPORTED_TYPE => &[
            C::U32,
            C::U32,
            C::String,
            C::String,
            C::Coded(IMPLEMENTATION),
        ],
        t::MANIFEST_RESOURCE => &[C::U32, C::U32, C::String, C::Coded(IMPLEMENTATION)],
        t::NESTED_CLASS => &[C::Row(t::TYPE_DEF), C::Row(t::TYPE_DEF)],
        t::GENERIC_PARAM => &[C::U16, C::U16, C::Coded(TYPE_OR_METHOD_DEF), C::String],
        t::METHOD_SPEC => &[C::Coded(METHOD_DEF_OR_REF), C::Blob],
        t::GENERIC_PARAM_CONSTRAINT => &[C::Row(t::GENERIC_PARAM), C::Coded(TYPE_DEF_OR_REF)],
        _ => &[],
    }
}

/// The name a table goes by, for anything that prints one.
#[must_use]
pub const fn name(number: u8) -> &'static str {
    match number {
        t::MODULE => "Module",
        t::TYPE_REF => "TypeRef",
        t::TYPE_DEF => "TypeDef",
        t::FIELD_PTR => "FieldPtr",
        t::FIELD => "Field",
        t::METHOD_PTR => "MethodPtr",
        t::METHOD_DEF => "MethodDef",
        t::PARAM_PTR => "ParamPtr",
        t::PARAM => "Param",
        t::INTERFACE_IMPL => "InterfaceImpl",
        t::MEMBER_REF => "MemberRef",
        t::CONSTANT => "Constant",
        t::CUSTOM_ATTRIBUTE => "CustomAttribute",
        t::FIELD_MARSHAL => "FieldMarshal",
        t::DECL_SECURITY => "DeclSecurity",
        t::CLASS_LAYOUT => "ClassLayout",
        t::FIELD_LAYOUT => "FieldLayout",
        t::STAND_ALONE_SIG => "StandAloneSig",
        t::EVENT_MAP => "EventMap",
        t::EVENT_PTR => "EventPtr",
        t::EVENT => "Event",
        t::PROPERTY_MAP => "PropertyMap",
        t::PROPERTY_PTR => "PropertyPtr",
        t::PROPERTY => "Property",
        t::METHOD_SEMANTICS => "MethodSemantics",
        t::METHOD_IMPL => "MethodImpl",
        t::MODULE_REF => "ModuleRef",
        t::TYPE_SPEC => "TypeSpec",
        t::IMPL_MAP => "ImplMap",
        t::FIELD_RVA => "FieldRVA",
        t::ENC_LOG => "EncLog",
        t::ENC_MAP => "EncMap",
        t::ASSEMBLY => "Assembly",
        t::ASSEMBLY_PROCESSOR => "AssemblyProcessor",
        t::ASSEMBLY_OS => "AssemblyOS",
        t::ASSEMBLY_REF => "AssemblyRef",
        t::ASSEMBLY_REF_PROCESSOR => "AssemblyRefProcessor",
        t::ASSEMBLY_REF_OS => "AssemblyRefOS",
        t::FILE => "File",
        t::EXPORTED_TYPE => "ExportedType",
        t::MANIFEST_RESOURCE => "ManifestResource",
        t::NESTED_CLASS => "NestedClass",
        t::GENERIC_PARAM => "GenericParam",
        t::METHOD_SPEC => "MethodSpec",
        t::GENERIC_PARAM_CONSTRAINT => "GenericParamConstraint",
        _ => "?",
    }
}
