//! Every IL opcode, with the name it goes by and the operand it carries.
//!
//! The operand widths are the load-bearing part. Reading IL is a walk with no
//! landmarks — nothing separates one instruction from the next but the length
//! of the one before — so an opcode whose operand size is wrong does not skip
//! an instruction, it lands in the middle of one and everything after is
//! garbage that still decodes.
//!
//! `0xFE` is a prefix rather than an opcode: what follows it is the second
//! half of a two-byte code, which is why an opcode here is a `u16`.

/// What follows an opcode in the instruction stream.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Operand {
    None,
    /// A one-byte local or argument number.
    Short,
    /// A two-byte one.
    Variable,
    Int8,
    Int32,
    Int64,
    Float32,
    Float64,
    /// A metadata token: a method, a field, a type, a string, a signature.
    Token,
    /// A branch offset, counted from the instruction after the branch.
    BranchShort,
    Branch,
    /// A count, then that many branch offsets.
    Switch,
}

impl Operand {
    /// How many bytes the operand takes, `switch` aside — its length depends
    /// on the count it starts with.
    #[must_use]
    pub const fn width(self) -> usize {
        match self {
            Self::None => 0,
            Self::Short | Self::Int8 | Self::BranchShort => 1,
            Self::Variable => 2,
            Self::Int32 | Self::Float32 | Self::Token | Self::Branch | Self::Switch => 4,
            Self::Int64 | Self::Float64 => 8,
        }
    }
}

/// The name and operand of an opcode, or `None` when it is not one.
#[must_use]
pub fn describe(opcode: u16) -> Option<(&'static str, Operand)> {
    use Operand as O;
    Some(match opcode {
        0x00 => ("nop", O::None),
        0x01 => ("break", O::None),
        0x02 => ("ldarg.0", O::None),
        0x03 => ("ldarg.1", O::None),
        0x04 => ("ldarg.2", O::None),
        0x05 => ("ldarg.3", O::None),
        0x06 => ("ldloc.0", O::None),
        0x07 => ("ldloc.1", O::None),
        0x08 => ("ldloc.2", O::None),
        0x09 => ("ldloc.3", O::None),
        0x0A => ("stloc.0", O::None),
        0x0B => ("stloc.1", O::None),
        0x0C => ("stloc.2", O::None),
        0x0D => ("stloc.3", O::None),
        0x0E => ("ldarg.s", O::Short),
        0x0F => ("ldarga.s", O::Short),
        0x10 => ("starg.s", O::Short),
        0x11 => ("ldloc.s", O::Short),
        0x12 => ("ldloca.s", O::Short),
        0x13 => ("stloc.s", O::Short),
        0x14 => ("ldnull", O::None),
        0x15 => ("ldc.i4.m1", O::None),
        0x16..=0x1E => (LDC_I4[(opcode - 0x16) as usize], O::None),
        0x1F => ("ldc.i4.s", O::Int8),
        0x20 => ("ldc.i4", O::Int32),
        0x21 => ("ldc.i8", O::Int64),
        0x22 => ("ldc.r4", O::Float32),
        0x23 => ("ldc.r8", O::Float64),
        0x25 => ("dup", O::None),
        0x26 => ("pop", O::None),
        0x27 => ("jmp", O::Token),
        0x28 => ("call", O::Token),
        0x29 => ("calli", O::Token),
        0x2A => ("ret", O::None),
        0x2B..=0x37 => (SHORT_BRANCHES[(opcode - 0x2B) as usize], O::BranchShort),
        0x38..=0x44 => (BRANCHES[(opcode - 0x38) as usize], O::Branch),
        0x45 => ("switch", O::Switch),
        0x46..=0x50 => (LOAD_INDIRECT[(opcode - 0x46) as usize], O::None),
        0x51..=0x57 => (STORE_INDIRECT[(opcode - 0x51) as usize], O::None),
        0x58..=0x66 => (ARITHMETIC[(opcode - 0x58) as usize], O::None),
        0x67..=0x6E => (CONVERSIONS[(opcode - 0x67) as usize], O::None),
        0x6F => ("callvirt", O::Token),
        0x70 => ("cpobj", O::Token),
        0x71 => ("ldobj", O::Token),
        0x72 => ("ldstr", O::Token),
        0x73 => ("newobj", O::Token),
        0x74 => ("castclass", O::Token),
        0x75 => ("isinst", O::Token),
        0x76 => ("conv.r.un", O::None),
        0x79 => ("unbox", O::Token),
        0x7A => ("throw", O::None),
        0x7B => ("ldfld", O::Token),
        0x7C => ("ldflda", O::Token),
        0x7D => ("stfld", O::Token),
        0x7E => ("ldsfld", O::Token),
        0x7F => ("ldsflda", O::Token),
        0x80 => ("stsfld", O::Token),
        0x81 => ("stobj", O::Token),
        0x82..=0x8B => (CHECKED_UNSIGNED[(opcode - 0x82) as usize], O::None),
        0x8C => ("box", O::Token),
        0x8D => ("newarr", O::Token),
        0x8E => ("ldlen", O::None),
        0x8F => ("ldelema", O::Token),
        0x90..=0x9A => (LOAD_ELEMENT[(opcode - 0x90) as usize], O::None),
        0x9B..=0xA2 => (STORE_ELEMENT[(opcode - 0x9B) as usize], O::None),
        0xA3 => ("ldelem", O::Token),
        0xA4 => ("stelem", O::Token),
        0xA5 => ("unbox.any", O::Token),
        0xB3..=0xBA => (CHECKED[(opcode - 0xB3) as usize], O::None),
        0xC2 => ("refanyval", O::Token),
        0xC3 => ("ckfinite", O::None),
        0xC6 => ("mkrefany", O::Token),
        0xD0 => ("ldtoken", O::Token),
        0xD1 => ("conv.u2", O::None),
        0xD2 => ("conv.u1", O::None),
        0xD3 => ("conv.i", O::None),
        0xD4 => ("conv.ovf.i", O::None),
        0xD5 => ("conv.ovf.u", O::None),
        0xD6 => ("add.ovf", O::None),
        0xD7 => ("add.ovf.un", O::None),
        0xD8 => ("mul.ovf", O::None),
        0xD9 => ("mul.ovf.un", O::None),
        0xDA => ("sub.ovf", O::None),
        0xDB => ("sub.ovf.un", O::None),
        0xDC => ("endfinally", O::None),
        0xDD => ("leave", O::Branch),
        0xDE => ("leave.s", O::BranchShort),
        0xDF => ("stind.i", O::None),
        0xE0 => ("conv.u", O::None),

        0xFE00 => ("arglist", O::None),
        0xFE01 => ("ceq", O::None),
        0xFE02 => ("cgt", O::None),
        0xFE03 => ("cgt.un", O::None),
        0xFE04 => ("clt", O::None),
        0xFE05 => ("clt.un", O::None),
        0xFE06 => ("ldftn", O::Token),
        0xFE07 => ("ldvirtftn", O::Token),
        0xFE09 => ("ldarg", O::Variable),
        0xFE0A => ("ldarga", O::Variable),
        0xFE0B => ("starg", O::Variable),
        0xFE0C => ("ldloc", O::Variable),
        0xFE0D => ("ldloca", O::Variable),
        0xFE0E => ("stloc", O::Variable),
        0xFE0F => ("localloc", O::None),
        0xFE11 => ("endfilter", O::None),
        0xFE12 => ("unaligned.", O::Short),
        0xFE13 => ("volatile.", O::None),
        0xFE14 => ("tail.", O::None),
        0xFE15 => ("initobj", O::Token),
        0xFE16 => ("constrained.", O::Token),
        0xFE17 => ("cpblk", O::None),
        0xFE18 => ("initblk", O::None),
        0xFE19 => ("no.", O::Short),
        0xFE1A => ("rethrow", O::None),
        0xFE1C => ("sizeof", O::Token),
        0xFE1D => ("refanytype", O::None),
        0xFE1E => ("readonly.", O::None),
        _ => return None,
    })
}

const LDC_I4: [&str; 9] = [
    "ldc.i4.0", "ldc.i4.1", "ldc.i4.2", "ldc.i4.3", "ldc.i4.4", "ldc.i4.5", "ldc.i4.6", "ldc.i4.7",
    "ldc.i4.8",
];
const SHORT_BRANCHES: [&str; 13] = [
    "br.s",
    "brfalse.s",
    "brtrue.s",
    "beq.s",
    "bge.s",
    "bgt.s",
    "ble.s",
    "blt.s",
    "bne.un.s",
    "bge.un.s",
    "bgt.un.s",
    "ble.un.s",
    "blt.un.s",
];
const BRANCHES: [&str; 13] = [
    "br", "brfalse", "brtrue", "beq", "bge", "bgt", "ble", "blt", "bne.un", "bge.un", "bgt.un",
    "ble.un", "blt.un",
];
const LOAD_INDIRECT: [&str; 11] = [
    "ldind.i1",
    "ldind.u1",
    "ldind.i2",
    "ldind.u2",
    "ldind.i4",
    "ldind.u4",
    "ldind.i8",
    "ldind.i",
    "ldind.r4",
    "ldind.r8",
    "ldind.ref",
];
const STORE_INDIRECT: [&str; 7] = [
    "stind.ref",
    "stind.i1",
    "stind.i2",
    "stind.i4",
    "stind.i8",
    "stind.r4",
    "stind.r8",
];
const ARITHMETIC: [&str; 15] = [
    "add", "sub", "mul", "div", "div.un", "rem", "rem.un", "and", "or", "xor", "shl", "shr",
    "shr.un", "neg", "not",
];
const CONVERSIONS: [&str; 8] = [
    "conv.i1", "conv.i2", "conv.i4", "conv.i8", "conv.r4", "conv.r8", "conv.u4", "conv.u8",
];
const CHECKED_UNSIGNED: [&str; 10] = [
    "conv.ovf.i1.un",
    "conv.ovf.i2.un",
    "conv.ovf.i4.un",
    "conv.ovf.i8.un",
    "conv.ovf.u1.un",
    "conv.ovf.u2.un",
    "conv.ovf.u4.un",
    "conv.ovf.u8.un",
    "conv.ovf.i.un",
    "conv.ovf.u.un",
];
const LOAD_ELEMENT: [&str; 11] = [
    "ldelem.i1",
    "ldelem.u1",
    "ldelem.i2",
    "ldelem.u2",
    "ldelem.i4",
    "ldelem.u4",
    "ldelem.i8",
    "ldelem.i",
    "ldelem.r4",
    "ldelem.r8",
    "ldelem.ref",
];
const STORE_ELEMENT: [&str; 8] = [
    "stelem.i",
    "stelem.i1",
    "stelem.i2",
    "stelem.i4",
    "stelem.i8",
    "stelem.r4",
    "stelem.r8",
    "stelem.ref",
];
const CHECKED: [&str; 8] = [
    "conv.ovf.i1",
    "conv.ovf.u1",
    "conv.ovf.i2",
    "conv.ovf.u2",
    "conv.ovf.i4",
    "conv.ovf.u4",
    "conv.ovf.i8",
    "conv.ovf.u8",
];
