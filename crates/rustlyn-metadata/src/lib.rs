//! Reading the metadata out of a .NET assembly.
//!
//! This is `rustlyn-emit` run backwards. The emitter lays out a PE file, a
//! metadata root, four heaps and a stream of tables; this walks the same
//! shapes in the other direction, which makes the two a check on each other:
//! anything the emitter writes, this has to be able to read back and agree
//! about.
//!
//! It is also the thing standing between rustlyn and a real reference
//! assembly. The core library is synthesised from source today because there
//! is no way to read `System.Runtime.dll`; this is the start of that way.

pub mod body;
mod heaps;
pub mod opcodes;
mod pe;
mod reader;
pub mod signature;
pub mod tables;
pub mod verify;

pub use body::Body;
pub use heaps::Heaps;
pub use pe::{Image, Section};
pub use reader::{Assembly, Row, Table};
pub use signature::{Blob, CustomModifier, MethodSig, TypeSig};
pub use tables::{Coded, Column, table};

/// A metadata token: the table it points into and the row inside it.
///
/// Row numbers start at one, and zero means no row at all — which is how a
/// column says "nothing" without a flag to say so.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token(pub u32);

impl Token {
    #[must_use]
    pub const fn new(table: u8, row: u32) -> Self {
        Self(((table as u32) << 24) | row)
    }

    /// The table the token points into. A token read out of a file may
    /// name one that does not exist (there are sixty-four); nothing has rows
    /// there.
    #[must_use]
    pub const fn table(self) -> u8 {
        (self.0 >> 24) as u8
    }

    #[must_use]
    pub const fn row(self) -> u32 {
        self.0 & 0x00FF_FFFF
    }

    #[must_use]
    pub const fn is_nil(self) -> bool {
        self.row() == 0
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", tables::name(self.table()), self.row())
    }
}

/// Why an assembly could not be read.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// Not a PE file at all.
    NotAnImage,
    /// A PE file with no CLI header: a native executable.
    NotAnAssembly,
    /// The metadata root does not start with `BSJB`.
    NotMetadata,
    /// A stream the metadata needs is missing.
    MissingStream(&'static str),
    /// An address that is in no section.
    BadAddress(u32),
    /// The file ends where something was expected.
    Truncated,
    /// The file says something no assembly says: a table this does not know
    /// with rows in it, a type nested deeper than any is, a section of no
    /// size. A file that is damaged, or made to be.
    Malformed(&'static str),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotAnImage => f.write_str("not a PE image"),
            Self::NotAnAssembly => f.write_str("a PE image with no CLI header"),
            Self::NotMetadata => f.write_str("the metadata root is not `BSJB`"),
            Self::MissingStream(name) => write!(f, "the `{name}` stream is missing"),
            Self::BadAddress(rva) => write!(f, "the address {rva:#x} is in no section"),
            Self::Truncated => f.write_str("the file ends early"),
            Self::Malformed(what) => write!(f, "the file is malformed: {what}"),
        }
    }
}

impl std::error::Error for Error {}
