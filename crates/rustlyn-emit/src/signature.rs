//! Signature blobs, as §II.23.2 encodes them.
//!
//! A signature is a compressed byte string rather than a string of names: a
//! method's is its calling convention, its parameter count and then one
//! element type per parameter with the return type first. Everything that
//! needs a type — a field, a local, an array — spells it the same way, which
//! is why the element-type writer is shared and the headers are not.

/// The element types of §II.23.1.16, as far as this emitter needs them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub(crate) enum ElementType {
    Void = 0x01,
    Boolean = 0x02,
    Char = 0x03,
    I1 = 0x04,
    U1 = 0x05,
    I2 = 0x06,
    U2 = 0x07,
    I4 = 0x08,
    U4 = 0x09,
    I8 = 0x0A,
    U8 = 0x0B,
    R4 = 0x0C,
    R8 = 0x0D,
    String = 0x0E,
    ValueType = 0x11,
    Class = 0x12,
    /// A type's own type parameter: `!0` inside `Box<T>`.
    Var = 0x13,
    /// A constructed type: `Box<int>`.
    GenericInst = 0x15,
    /// `System.TypedReference`, which `__makeref` makes.
    TypedByRef = 0x16,
    /// `native int`, which is what a delegate's constructor takes as its
    /// function pointer — and what `System.IntPtr` is written as.
    I = 0x18,
    /// `native unsigned int`: `System.UIntPtr`.
    U = 0x19,
    Object = 0x1C,
    SzArray = 0x1D,
    /// An array with a shape: a rank, and bounds it usually does not give.
    Array = 0x14,
    /// A method's type parameter: `!!0` inside `T Echo<T>(T)`. A type's and
    /// a method's are numbered separately, so they need different element
    /// types to tell them apart.
    MVar = 0x1E,
    /// `ref int` and `out int`: a reference to a variable rather than a copy
    /// of it. Both are the same thing here — `out` is a promise the compiler
    /// checks, not a difference the runtime sees.
    ByRef = 0x10,
    /// `T*`, which is a type only where the source said `unsafe`.
    Pointer = 0x0F,
    /// `delegate*<...>`: a method signature standing where a type goes.
    FnPtr = 0x1B,
    /// The constraint on a local that the garbage collector may not move
    /// what it points at, which is what `fixed` asks for (§II.23.2.9).
    Pinned = 0x45,
}

/// A type as a signature spells it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum SigType {
    Primitive(ElementType),
    /// A class or value type, by its `TypeDefOrRef` coded index.
    Named {
        value_type: bool,
        coded: u32,
    },
    /// A vector — a one-dimensional array with a zero lower bound, which is
    /// what `T[]` means in C#.
    Array(Box<SigType>),
    /// `T[,]` and beyond: an array with a rank and no bounds given.
    MultiArray(Box<SigType>, u32),
    /// A use of the enclosing type's type parameter, by position. A signature
    /// never names a type parameter: `Box<T>.Get` returns `!0`, and what `!0`
    /// is depends on the construction the caller wrote.
    TypeParameter(u32),
    /// A use of the enclosing *method's* type parameter, by position: `!!0`.
    MethodTypeParameter(u32),
    /// `ref T`, which is what a `ref` or `out` parameter takes.
    ByRef(Box<SigType>),
    /// `T*`: a pointer to somewhere, which nothing tracks the lifetime of.
    Pointer(Box<SigType>),
    /// A local the garbage collector may not move the target of: only a
    /// local's signature ever carries this, and only `fixed` writes one.
    Pinned(Box<SigType>),
    /// A type with a required custom modifier in front of it.
    ///
    /// `ref readonly T` is `T&` under a `modreq` naming `InAttribute`, and the
    /// modifier is part of the signature: a reference that leaves it out names
    /// a method the runtime does not have.
    Required {
        modifier: u32,
        inner: Box<SigType>,
    },
    /// A type with an optional custom modifier in front of it: what a
    /// function pointer's `unmanaged[SuppressGCTransition]` says, on its
    /// return type.
    Optional {
        modifier: u32,
        inner: Box<SigType>,
    },
    /// `delegate*<int, void>`: a whole method signature, calling convention
    /// first, as the type of a value.
    FunctionPointer {
        convention: u8,
        returns: Box<SigType>,
        parameters: Vec<SigType>,
    },
    /// `Box<int>`: the definition and what it was given.
    Constructed {
        value_type: bool,
        coded: u32,
        arguments: Vec<SigType>,
    },
}

impl SigType {
    pub(crate) fn write(&self, blob: &mut Vec<u8>) {
        match self {
            Self::Primitive(element) => blob.push(*element as u8),
            Self::Named { value_type, coded } => {
                blob.push(if *value_type {
                    ElementType::ValueType as u8
                } else {
                    ElementType::Class as u8
                });
                compress(blob, *coded);
            }
            Self::Array(element) => {
                blob.push(ElementType::SzArray as u8);
                element.write(blob);
            }
            // §II.23.2.13: the rank, then how many sizes are given and then
            // how many lower bounds are. C# gives no size: `new int[2, 3]`
            // says its sizes at run time, not in the type. It gives every
            // dimension the lower bound 0, as Roslyn writes it.
            Self::MultiArray(element, rank) => {
                blob.push(ElementType::Array as u8);
                element.write(blob);
                compress(blob, *rank);
                compress(blob, 0);
                compress(blob, *rank);
                for _ in 0..*rank {
                    compress(blob, 0);
                }
            }
            Self::TypeParameter(index) => {
                blob.push(ElementType::Var as u8);
                compress(blob, *index);
            }
            Self::MethodTypeParameter(index) => {
                blob.push(ElementType::MVar as u8);
                compress(blob, *index);
            }
            Self::ByRef(inner) => {
                blob.push(ElementType::ByRef as u8);
                inner.write(blob);
            }
            Self::Pointer(inner) => {
                blob.push(ElementType::Pointer as u8);
                inner.write(blob);
            }
            Self::Pinned(inner) => {
                blob.push(ElementType::Pinned as u8);
                inner.write(blob);
            }
            // §II.23.2.7: the modifier comes first, as a `TypeDefOrRef` coded
            // index, and the type it modifies follows.
            Self::Required { modifier, inner } => {
                blob.push(0x1F);
                compress(blob, *modifier);
                inner.write(blob);
            }
            Self::Optional { modifier, inner } => {
                blob.push(0x20);
                compress(blob, *modifier);
                inner.write(blob);
            }
            // §II.23.2.15: `FNPTR` and then the signature as a method's would
            // be written.
            Self::FunctionPointer {
                convention,
                returns,
                parameters,
            } => {
                blob.push(ElementType::FnPtr as u8);
                blob.extend(standalone_method_signature(
                    *convention,
                    returns,
                    parameters,
                ));
            }
            Self::Constructed {
                value_type,
                coded,
                arguments,
            } => {
                blob.push(ElementType::GenericInst as u8);
                blob.push(if *value_type {
                    ElementType::ValueType as u8
                } else {
                    ElementType::Class as u8
                });
                compress(blob, *coded);
                compress(blob, arguments.len() as u32);
                for argument in arguments {
                    argument.write(blob);
                }
            }
        }
    }
}

/// Writes an unsigned integer in the compressed form of §II.23.2.
///
/// One byte up to 0x7F, two up to 0x3FFF, four beyond that; the leading bits
/// say which, so a reader never needs to be told the width.
pub(crate) fn compress(blob: &mut Vec<u8>, value: u32) {
    if value <= 0x7F {
        blob.push(value as u8);
    } else if value <= 0x3FFF {
        blob.push(0x80 | (value >> 8) as u8);
        blob.push((value & 0xFF) as u8);
    } else {
        blob.push(0xC0 | (value >> 24) as u8);
        blob.push(((value >> 16) & 0xFF) as u8);
        blob.push(((value >> 8) & 0xFF) as u8);
        blob.push((value & 0xFF) as u8);
    }
}

/// `HASTHIS`, which an instance method's signature carries and a static one's
/// does not.
const HAS_THIS: u8 = 0x20;

/// `GENERIC`, which says the count that follows is the method's type
/// parameters and that its own parameter count comes after that.
const GENERIC: u8 = 0x10;

/// The signature of a method, as a `MethodDef` or `MemberRef` blob.
#[must_use]
pub(crate) fn method_signature(
    instance: bool,
    return_type: &SigType,
    parameters: &[SigType],
) -> Vec<u8> {
    generic_method_signature(instance, 0, return_type, parameters)
}

/// A method signature with a calling convention of its own: what a function
/// pointer's type spells, and what `calli` is handed as a `StandAloneSig`.
#[must_use]
pub(crate) fn standalone_method_signature(
    convention: u8,
    return_type: &SigType,
    parameters: &[SigType],
) -> Vec<u8> {
    let mut blob = vec![convention];
    compress(&mut blob, parameters.len() as u32);
    return_type.write(&mut blob);
    for parameter in parameters {
        parameter.write(&mut blob);
    }
    blob
}

/// The same, for a method that declares type parameters of its own.
#[must_use]
pub(crate) fn generic_method_signature(
    instance: bool,
    arity: u32,
    return_type: &SigType,
    parameters: &[SigType],
) -> Vec<u8> {
    let mut blob = Vec::new();
    blob.push((if instance { HAS_THIS } else { 0 }) | (if arity > 0 { GENERIC } else { 0 }));
    if arity > 0 {
        compress(&mut blob, arity);
    }
    compress(&mut blob, parameters.len() as u32);
    return_type.write(&mut blob);
    for parameter in parameters {
        parameter.write(&mut blob);
    }
    blob
}

/// `VARARG`: the calling convention of a method ending in `__arglist`.
const VARARG: u8 = 0x05;

/// `SENTINEL`: where a call site's own arguments to a varargs method start.
const SENTINEL: u8 = 0x41;

/// The signature of a varargs method, as its `MethodDef` has it, or as a
/// call site's `MemberRef` does: the fixed parameters, then — only at a call
/// site — a sentinel and the types of what the call passes beyond them
/// (§II.23.2.2).
#[must_use]
pub(crate) fn vararg_signature(
    instance: bool,
    return_type: &SigType,
    parameters: &[SigType],
    extra: &[SigType],
) -> Vec<u8> {
    let mut blob = vec![(if instance { HAS_THIS } else { 0 }) | VARARG];
    compress(&mut blob, (parameters.len() + extra.len()) as u32);
    return_type.write(&mut blob);
    for parameter in parameters {
        parameter.write(&mut blob);
    }
    if !extra.is_empty() {
        blob.push(SENTINEL);
        for argument in extra {
            argument.write(&mut blob);
        }
    }
    blob
}

/// The instantiation a `MethodSpec` carries: `Echo<int>` is `GENERICINST`
/// followed by the types the call settled on.
#[must_use]
pub(crate) fn method_spec_signature(arguments: &[SigType]) -> Vec<u8> {
    let mut blob = vec![0x0A];
    compress(&mut blob, arguments.len() as u32);
    for argument in arguments {
        argument.write(&mut blob);
    }
    blob
}

/// The signature of a field: the `FIELD` calling convention and one type.
#[must_use]
pub(crate) fn field_signature(ty: &SigType) -> Vec<u8> {
    let mut blob = vec![0x06];
    ty.write(&mut blob);
    blob
}

/// The signature of a property: the `PROPERTY` calling convention, how many
/// parameters it takes (none, unless it is an indexer) and its type.
#[must_use]
pub(crate) fn property_signature(instance: bool, ty: &SigType, parameters: &[SigType]) -> Vec<u8> {
    let mut blob = vec![0x08 | if instance { HAS_THIS } else { 0 }];
    // An indexer is a property with parameters, and this count is the only
    // place metadata says how many it has.
    compress(&mut blob, parameters.len() as u32);
    ty.write(&mut blob);
    for parameter in parameters {
        parameter.write(&mut blob);
    }
    blob
}

/// The signature of a method's locals, which a `StandAloneSig` row holds.
#[must_use]
pub(crate) fn local_signature(locals: &[SigType]) -> Vec<u8> {
    let mut blob = vec![0x07];
    compress(&mut blob, locals.len() as u32);
    for local in locals {
        local.write(&mut blob);
    }
    blob
}

/// A `TypeDefOrRef` coded index: two bits of tag under the row number.
///
/// 0 is `TypeDef`, 1 is `TypeRef`, 2 is `TypeSpec`.
#[must_use]
pub(crate) const fn type_def_or_ref(tag: u32, row: u32) -> u32 {
    (row << 2) | tag
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compression_follows_the_spec_examples() {
        // §II.23.2 gives these exact encodings.
        let mut blob = Vec::new();
        compress(&mut blob, 0x03);
        compress(&mut blob, 0x7F);
        assert_eq!(blob, vec![0x03, 0x7F]);

        let mut blob = Vec::new();
        compress(&mut blob, 0x80);
        compress(&mut blob, 0x2E57);
        assert_eq!(blob, vec![0x80, 0x80, 0xAE, 0x57]);

        let mut blob = Vec::new();
        compress(&mut blob, 0x3FFF);
        compress(&mut blob, 0x4000);
        assert_eq!(blob, vec![0xBF, 0xFF, 0xC0, 0x00, 0x40, 0x00]);
    }

    #[test]
    fn a_static_method_has_no_this() {
        let signature = method_signature(
            false,
            &SigType::Primitive(ElementType::Void),
            &[SigType::Primitive(ElementType::I4)],
        );
        assert_eq!(signature, vec![0x00, 0x01, 0x01, 0x08]);
    }

    #[test]
    fn an_instance_method_does() {
        let signature = method_signature(true, &SigType::Primitive(ElementType::I4), &[]);
        assert_eq!(signature, vec![0x20, 0x00, 0x08]);
    }

    #[test]
    fn an_array_wraps_its_element() {
        let mut blob = Vec::new();
        SigType::Array(Box::new(SigType::Primitive(ElementType::String))).write(&mut blob);
        assert_eq!(blob, vec![0x1D, 0x0E]);
    }

    #[test]
    fn a_constructed_type_carries_its_arguments() {
        let mut blob = Vec::new();
        // `Box<int>`, where `Box` is TypeDef row 2: coded index (2 << 2) | 0.
        SigType::Constructed {
            value_type: false,
            coded: 8,
            arguments: vec![SigType::Primitive(ElementType::I4)],
        }
        .write(&mut blob);
        assert_eq!(blob, vec![0x15, 0x12, 0x08, 0x01, 0x08]);
    }

    #[test]
    fn a_type_parameter_is_written_by_position() {
        let mut blob = Vec::new();
        SigType::TypeParameter(1).write(&mut blob);
        assert_eq!(blob, vec![0x13, 0x01]);
    }

    #[test]
    fn locals_carry_their_count() {
        let signature = local_signature(&[
            SigType::Primitive(ElementType::I4),
            SigType::Primitive(ElementType::String),
        ]);
        assert_eq!(signature, vec![0x07, 0x02, 0x08, 0x0E]);
    }
}
