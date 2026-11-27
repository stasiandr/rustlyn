//! Reading a signature blob back into something with a shape.
//!
//! A signature is a compressed byte string rather than a string of names: a
//! calling convention, a count, and then one element type per parameter with
//! the return type first. Everything that needs a type — a field, a local, an
//! array — spells it the same way, which is why the type reader is shared and
//! the headers are not.

use crate::{Error, Token};

/// A type, as a signature spells it.
///
/// This is the structural form rather than the resolved one: a `Class` knows
/// which token it names but not what that token is, because resolving one
/// needs the whole set of assemblies and a signature is read from just the
/// one.
#[derive(Clone, PartialEq, Debug)]
pub enum TypeSig {
    Void,
    Boolean,
    Char,
    SByte,
    Byte,
    Int16,
    UInt16,
    Int32,
    UInt32,
    Int64,
    UInt64,
    Single,
    Double,
    String,
    Object,
    /// `native int` and `native unsigned int`.
    IntPtr,
    UIntPtr,
    /// `typedref`, which only `__arglist` produces.
    TypedReference,
    Class(Token),
    ValueType(Token),
    /// `T[]`, which is what C# writes.
    Vector(Box<TypeSig>),
    /// An array with a rank and possibly bounds.
    Array {
        element: Box<TypeSig>,
        rank: u32,
    },
    Pointer(Box<TypeSig>),
    ByRef(Box<TypeSig>),
    /// A type's own type parameter, by position.
    Var(u32),
    /// A method's, by position.
    MVar(u32),
    /// `List<string>`: the definition and what it was given.
    Generic {
        definition: Box<TypeSig>,
        arguments: Vec<TypeSig>,
    },
    /// `delegate*<int, void>`: a method signature standing where a type goes.
    FunctionPointer(Box<FunctionPointerSig>),
    /// Something this reader does not model, with the element type that
    /// started it. Answering this beats guessing: a signature that is not
    /// understood is not the same as one that is `object`.
    Unknown(u8),
}

/// A method's signature.
#[derive(Clone, PartialEq, Debug)]
pub struct MethodSig {
    /// Whether it takes a `this`.
    pub instance: bool,
    /// How many type parameters of its own it declares.
    pub arity: u32,
    pub returns: TypeSig,
    /// The required custom modifiers written in front of the return type.
    ///
    /// `ref readonly T` is `T&` with a `modreq` naming `InAttribute`, and a
    /// reference to such a method that leaves the modifier out names a method
    /// the runtime does not have.
    pub returns_required: Vec<Token>,
    pub parameters: Vec<TypeSig>,
    /// The required custom modifiers written in front of each parameter.
    ///
    /// `in T` is `T&` with a `modreq` naming `InAttribute`, and that modifier
    /// is the only thing in metadata that tells it from a `ref T`.
    pub parameters_required: Vec<Vec<Token>>,
    /// Where the `params` of a vararg call begin, when there are any.
    pub sentinel: Option<usize>,
    /// Every custom modifier in front of the return type, `modreq` and
    /// `modopt` alike, in the order written: a reference to the method has
    /// to repeat them all, and an override has to copy them.
    pub returns_modifiers: Vec<CustomModifier>,
    /// The same for each parameter.
    pub parameters_modifiers: Vec<Vec<CustomModifier>>,
}

/// One `modreq` (required) or `modopt` in a signature, by the type it names.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CustomModifier {
    pub required: bool,
    pub token: Token,
}

/// What a function pointer type says: a method signature, its calling
/// convention byte, and the optional modifiers in front of its return type,
/// which is where `unmanaged[SuppressGCTransition]` writes its `CallConv*`
/// types.
#[derive(Clone, PartialEq, Debug)]
pub struct FunctionPointerSig {
    pub convention: u8,
    pub returns_optional: Vec<Token>,
    pub signature: MethodSig,
}

/// The `modreq`s of a run of modifiers.
fn required(modifiers: &[CustomModifier]) -> Vec<Token> {
    modifiers
        .iter()
        .filter(|modifier| modifier.required)
        .map(|modifier| modifier.token)
        .collect()
}

/// Walks a blob, with the one bit of decoding every reader of one needs.
#[derive(Clone, Debug)]
pub struct Blob<'a> {
    bytes: &'a [u8],
    at: usize,
    /// How many types deep the one being read is; see [`MAX_NESTING`].
    depth: u32,
}

/// How deep a type in a signature nests: `int*****[]` is six. Each level is
/// a call to itself, and a blob of nothing but `PTR` bytes — a megabyte of
/// them fits in a file — ran the reader out of stack. Real signatures nest a
/// handful deep.
const MAX_NESTING: u32 = 256;

impl<'a> Blob<'a> {
    #[must_use]
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            at: 0,
            depth: 0,
        }
    }

    #[must_use]
    pub const fn position(&self) -> usize {
        self.at
    }

    #[must_use]
    pub fn is_done(&self) -> bool {
        self.at >= self.bytes.len()
    }

    /// The next byte.
    pub fn byte(&mut self) -> Result<u8, Error> {
        let byte = *self.bytes.get(self.at).ok_or(Error::Truncated)?;
        self.at += 1;
        Ok(byte)
    }

    /// The next byte without taking it.
    #[must_use]
    pub fn peek(&self) -> Option<u8> {
        self.bytes.get(self.at).copied()
    }

    /// An unsigned integer in the compressed form of §II.23.2: one byte up to
    /// 0x7F, two up to 0x3FFF, four beyond, with the leading bits saying
    /// which.
    pub fn unsigned(&mut self) -> Result<u32, Error> {
        let first = self.byte()?;
        Ok(if first & 0x80 == 0 {
            u32::from(first)
        } else if first & 0x40 == 0 {
            (u32::from(first & 0x3F) << 8) | u32::from(self.byte()?)
        } else {
            (u32::from(first & 0x1F) << 24)
                | (u32::from(self.byte()?) << 16)
                | (u32::from(self.byte()?) << 8)
                | u32::from(self.byte()?)
        })
    }

    /// A signed integer, which the same compression rotates into place.
    pub fn signed(&mut self) -> Result<i32, Error> {
        let value = self.unsigned()?;
        // The sign is the low bit, and the width decides where it comes back.
        let rotated = (value >> 1) as i32;
        Ok(if value & 1 == 0 { rotated } else { !rotated })
    }

    /// A `TypeDefOrRef` coded index, which signatures write compressed rather
    /// than at the fixed width a table column uses.
    pub fn type_def_or_ref(&mut self) -> Result<Token, Error> {
        let value = self.unsigned()?;
        let table = match value & 3 {
            0 => crate::table::TYPE_DEF,
            1 => crate::table::TYPE_REF,
            _ => crate::table::TYPE_SPEC,
        };
        Ok(Token::new(table, value >> 2))
    }

    /// One type.
    ///
    /// # Errors
    ///
    /// Returns an error when the blob ends in the middle of a type.
    pub fn type_sig(&mut self) -> Result<TypeSig, Error> {
        if self.depth >= MAX_NESTING {
            return Err(Error::Malformed("a type nested too deep in a signature"));
        }
        self.depth += 1;
        let ty = self.type_sig_here();
        self.depth -= 1;
        ty
    }

    /// Room for `count` things still to be read: at most one per byte left,
    /// whatever the count says — it is a number in a file, and half a
    /// thousand million parameters asked for before the first is read is
    /// memory nobody has.
    fn room<T>(&self, count: usize) -> Vec<T> {
        Vec::with_capacity(count.min(self.bytes.len().saturating_sub(self.at)))
    }

    fn type_sig_here(&mut self) -> Result<TypeSig, Error> {
        // Custom modifiers sit in front of the type they modify and say
        // nothing this needs, so they are stepped over rather than kept.
        while let Some(0x1F | 0x20) = self.peek() {
            self.byte()?;
            self.unsigned()?;
        }
        let element = self.byte()?;
        Ok(match element {
            0x01 => TypeSig::Void,
            0x02 => TypeSig::Boolean,
            0x03 => TypeSig::Char,
            0x04 => TypeSig::SByte,
            0x05 => TypeSig::Byte,
            0x06 => TypeSig::Int16,
            0x07 => TypeSig::UInt16,
            0x08 => TypeSig::Int32,
            0x09 => TypeSig::UInt32,
            0x0A => TypeSig::Int64,
            0x0B => TypeSig::UInt64,
            0x0C => TypeSig::Single,
            0x0D => TypeSig::Double,
            0x0E => TypeSig::String,
            0x0F => TypeSig::Pointer(Box::new(self.type_sig()?)),
            0x10 => TypeSig::ByRef(Box::new(self.type_sig()?)),
            0x11 => TypeSig::ValueType(self.type_def_or_ref()?),
            0x12 => TypeSig::Class(self.type_def_or_ref()?),
            0x13 => TypeSig::Var(self.unsigned()?),
            0x14 => {
                let element = Box::new(self.type_sig()?);
                let rank = self.unsigned()?;
                // The sizes and the lower bounds are written out and say
                // nothing C# can express, so they are stepped over.
                let sizes = self.unsigned()?;
                for _ in 0..sizes {
                    self.unsigned()?;
                }
                let bounds = self.unsigned()?;
                for _ in 0..bounds {
                    self.signed()?;
                }
                TypeSig::Array { element, rank }
            }
            0x15 => {
                let definition = Box::new(self.type_sig()?);
                let count = self.unsigned()?;
                let mut arguments = self.room(count as usize);
                for _ in 0..count {
                    arguments.push(self.type_sig()?);
                }
                TypeSig::Generic {
                    definition,
                    arguments,
                }
            }
            0x16 => TypeSig::TypedReference,
            0x18 => TypeSig::IntPtr,
            0x19 => TypeSig::UIntPtr,
            0x1B => {
                // A function pointer carries a whole method signature; the
                // `modopt`s on its return say the calling convention beyond
                // what the first byte can.
                let convention = self.peek().ok_or(Error::Truncated)?;
                let signature = self.method_sig()?;
                let returns_optional = signature
                    .returns_modifiers
                    .iter()
                    .filter(|modifier| !modifier.required)
                    .map(|modifier| modifier.token)
                    .collect();
                TypeSig::FunctionPointer(Box::new(FunctionPointerSig {
                    convention: convention & 0x0F,
                    returns_optional,
                    signature,
                }))
            }
            0x1C => TypeSig::Object,
            0x1D => TypeSig::Vector(Box::new(self.type_sig()?)),
            0x1E => TypeSig::MVar(self.unsigned()?),
            0x45 => {
                // `PINNED`, which a local can be.
                self.type_sig()?
            }
            other => TypeSig::Unknown(other),
        })
    }

    /// The custom modifiers a field's type has in front of it, after the
    /// convention byte: `modreq(IsVolatile)` is what says a field is
    /// `volatile`.
    ///
    /// # Errors
    ///
    /// Returns an error when the blob ends in the middle of one.
    pub fn field_modifiers(&mut self) -> Result<Vec<CustomModifier>, Error> {
        self.byte()?;
        self.modifiers()
    }

    /// A method's signature: the calling convention, the counts, and the types.
    ///
    /// # Errors
    ///
    /// Returns an error when the blob ends in the middle of one.
    /// The custom modifiers in front of whatever comes next, consumed.
    fn modifiers(&mut self) -> Result<Vec<CustomModifier>, Error> {
        let mut modifiers = Vec::new();
        while let Some(kind @ (0x1F | 0x20)) = self.peek() {
            self.byte()?;
            let token = self.type_def_or_ref()?;
            modifiers.push(CustomModifier {
                required: kind == 0x1F,
                token,
            });
        }
        Ok(modifiers)
    }

    pub fn method_sig(&mut self) -> Result<MethodSig, Error> {
        let convention = self.byte()?;
        let arity = if convention & 0x10 != 0 {
            self.unsigned()?
        } else {
            0
        };
        let count = self.unsigned()? as usize;
        let returns_modifiers = self.modifiers()?;
        let returns = self.type_sig()?;
        let mut parameters = self.room(count);
        let mut parameters_modifiers = self.room(count);
        let mut sentinel = None;
        for _ in 0..count {
            // `SENTINEL` marks where a vararg call's extra arguments begin.
            if self.peek() == Some(0x41) {
                self.byte()?;
                sentinel = Some(parameters.len());
            }
            parameters_modifiers.push(self.modifiers()?);
            parameters.push(self.type_sig()?);
        }
        Ok(MethodSig {
            instance: convention & 0x20 != 0,
            arity,
            returns,
            returns_required: required(&returns_modifiers),
            parameters,
            parameters_required: parameters_modifiers
                .iter()
                .map(|each| required(each))
                .collect(),
            sentinel,
            returns_modifiers,
            parameters_modifiers,
        })
    }

    /// A field's signature, which is the `FIELD` convention and one type.
    ///
    /// # Errors
    ///
    /// Returns an error when the blob ends in the middle of one.
    pub fn field_sig(&mut self) -> Result<TypeSig, Error> {
        self.byte()?;
        self.type_sig()
    }

    /// A property's: the convention, how many parameters it takes and its
    /// type, then those parameters.
    ///
    /// # Errors
    ///
    /// Returns an error when the blob ends in the middle of one.
    pub fn property_sig(&mut self) -> Result<MethodSig, Error> {
        let convention = self.byte()?;
        let count = self.unsigned()? as usize;
        let returns_modifiers = self.modifiers()?;
        let returns = self.type_sig()?;
        let mut parameters = self.room(count);
        let mut parameters_modifiers = self.room(count);
        for _ in 0..count {
            parameters_modifiers.push(self.modifiers()?);
            parameters.push(self.type_sig()?);
        }
        Ok(MethodSig {
            instance: convention & 0x20 != 0,
            arity: 0,
            returns,
            returns_required: required(&returns_modifiers),
            parameters,
            parameters_required: parameters_modifiers
                .iter()
                .map(|each| required(each))
                .collect(),
            sentinel: None,
            returns_modifiers,
            parameters_modifiers,
        })
    }

    /// A method body's locals.
    ///
    /// # Errors
    ///
    /// Returns an error when the blob ends in the middle of one.
    pub fn locals_sig(&mut self) -> Result<Vec<TypeSig>, Error> {
        self.byte()?;
        let count = self.unsigned()? as usize;
        let mut locals = self.room(count);
        for _ in 0..count {
            locals.push(self.type_sig()?);
        }
        Ok(locals)
    }
}
