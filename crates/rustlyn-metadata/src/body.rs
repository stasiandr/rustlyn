//! Reading a method body: its header, its IL and its exception clauses.
//!
//! This is `il.rs` in the emitter run backwards. The header is tiny or fat,
//! and the fat one says where the locals signature is and whether an exception
//! table follows the code; the code itself is a walk with no landmarks, which
//! is what makes [`crate::opcodes`] the load-bearing part.

use crate::opcodes::{self, Operand};
use crate::{Error, Token};

/// What an instruction carries.
#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    None,
    /// A local or argument number.
    Variable(u16),
    Int(i64),
    Float(f64),
    Token(Token),
    /// Where a branch goes, as an offset into the body.
    Target(u32),
    /// `switch`, with one target per case.
    Targets(Vec<u32>),
}

/// One decoded instruction.
#[derive(Clone, PartialEq, Debug)]
pub struct Instruction {
    /// Where it starts, counted from the first byte of the code.
    pub offset: u32,
    pub opcode: u16,
    pub name: &'static str,
    pub value: Value,
}

impl Instruction {
    /// How wide the instruction is, prefix and operand included.
    #[must_use]
    pub fn width(&self) -> u32 {
        let opcode = if self.opcode > 0xFF { 2 } else { 1 };
        let operand = match &self.value {
            Value::Targets(targets) => 4 + 4 * targets.len(),
            _ => opcodes::describe(self.opcode).map_or(0, |(_, operand)| operand.width()),
        };
        opcode + operand as u32
    }
}

/// What a protected region does when it throws.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Handler {
    /// `catch (T)`, with the type it takes.
    Catch(Token),
    /// `catch (T) when (c)`, with where the filter's code starts.
    Filter(u32),
    Finally,
    Fault,
}

/// One protected region and the handler that guards it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Region {
    pub kind: Handler,
    pub try_offset: u32,
    pub try_length: u32,
    pub handler_offset: u32,
    pub handler_length: u32,
}

/// A method body, decoded.
#[derive(Clone, PartialEq, Debug)]
pub struct Body {
    pub max_stack: u16,
    /// The `StandAloneSig` holding the local types, when there are any.
    pub locals: Option<Token>,
    /// Whether the runtime has to zero the locals before the body runs.
    pub init_locals: bool,
    pub instructions: Vec<Instruction>,
    pub regions: Vec<Region>,
    /// The code itself, for anything that wants the bytes.
    pub code_size: u32,
}

impl Body {
    /// Reads a method body out of the bytes at its address.
    ///
    /// # Errors
    ///
    /// Returns an error when the body runs past the end of the file or its
    /// header is not one of the two shapes §II.25.4 allows.
    pub fn read(bytes: &[u8]) -> Result<Self, Error> {
        let first = *bytes.first().ok_or(Error::Truncated)?;
        // The low two bits say which header this is; a tiny one packs the code
        // size into the rest of the same byte.
        let (code_at, code_size, max_stack, locals, init_locals, more_sections) =
            if first & 0x03 == 0x02 {
                (1usize, u32::from(first >> 2), 8u16, None, false, false)
            } else {
                let flags = u16::from_le_bytes([bytes[0], *bytes.get(1).ok_or(Error::Truncated)?]);
                let header_size = ((flags >> 12) * 4) as usize;
                let read16 = |at: usize| -> Result<u16, Error> {
                    bytes
                        .get(at..at + 2)
                        .map(|s| u16::from_le_bytes([s[0], s[1]]))
                        .ok_or(Error::Truncated)
                };
                let read32 = |at: usize| -> Result<u32, Error> {
                    bytes
                        .get(at..at + 4)
                        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
                        .ok_or(Error::Truncated)
                };
                let signature = read32(8)?;
                (
                    header_size,
                    read32(4)?,
                    read16(2)?,
                    (signature != 0).then_some(Token(signature)),
                    flags & 0x0010 != 0,
                    flags & 0x0008 != 0,
                )
            };

        let code = bytes
            .get(code_at..code_at + code_size as usize)
            .ok_or(Error::Truncated)?;
        let instructions = decode(code)?;

        let mut regions = Vec::new();
        if more_sections {
            // The section starts on a four-byte boundary after the code.
            let mut at = (code_at + code_size as usize + 3) & !3;
            loop {
                let kind = *bytes.get(at).ok_or(Error::Truncated)?;
                let fat = kind & 0x40 != 0;
                let size = if fat {
                    u32::from(bytes[at + 1])
                        | (u32::from(bytes[at + 2]) << 8)
                        | (u32::from(bytes[at + 3]) << 16)
                } else {
                    u32::from(bytes[at + 1])
                };
                if kind & 0x01 != 0 {
                    read_clauses(bytes, at + 4, size, fat, &mut regions)?;
                }
                if kind & 0x80 == 0 {
                    break;
                }
                at += size as usize;
            }
        }

        Ok(Self {
            max_stack,
            locals,
            init_locals,
            instructions,
            regions,
            code_size,
        })
    }
}

/// The clauses of one exception table, fat or small.
fn read_clauses(
    bytes: &[u8],
    at: usize,
    size: u32,
    fat: bool,
    regions: &mut Vec<Region>,
) -> Result<(), Error> {
    let width = if fat { 24 } else { 12 };
    let count = (size as usize).saturating_sub(4) / width;
    for index in 0..count {
        let clause = at + index * width;
        let slice = bytes.get(clause..clause + width).ok_or(Error::Truncated)?;
        let (flags, try_offset, try_length, handler_offset, handler_length, extra) = if fat {
            let word = |at: usize| {
                u32::from_le_bytes([slice[at], slice[at + 1], slice[at + 2], slice[at + 3]])
            };
            (word(0), word(4), word(8), word(12), word(16), word(20))
        } else {
            let half = |at: usize| u32::from(u16::from_le_bytes([slice[at], slice[at + 1]]));
            let word = |at: usize| {
                u32::from_le_bytes([slice[at], slice[at + 1], slice[at + 2], slice[at + 3]])
            };
            (
                half(0),
                half(2),
                u32::from(slice[4]),
                half(5),
                u32::from(slice[7]),
                word(8),
            )
        };
        regions.push(Region {
            kind: match flags & 0x07 {
                0x01 => Handler::Filter(extra),
                0x02 => Handler::Finally,
                0x04 => Handler::Fault,
                _ => Handler::Catch(Token(extra)),
            },
            try_offset,
            try_length,
            handler_offset,
            handler_length,
        });
    }
    Ok(())
}

/// Walks the code, one instruction at a time.
///
/// # Errors
///
/// Returns an error when the code ends in the middle of an instruction, or
/// holds a byte that is no opcode — either way the walk cannot go on, because
/// the length of what it is standing on is what says where the next one is.
pub fn decode(code: &[u8]) -> Result<Vec<Instruction>, Error> {
    let mut instructions = Vec::new();
    let mut at = 0usize;
    while at < code.len() {
        let offset = at as u32;
        let first = code[at];
        at += 1;
        let opcode = if first == 0xFE {
            let second = *code.get(at).ok_or(Error::Truncated)?;
            at += 1;
            0xFE00 | u16::from(second)
        } else {
            u16::from(first)
        };
        let (name, operand) = opcodes::describe(opcode).ok_or(Error::Truncated)?;

        let take = |at: usize, width: usize| code.get(at..at + width).ok_or(Error::Truncated);
        let value = match operand {
            Operand::None => Value::None,
            Operand::Short => Value::Variable(u16::from(*code.get(at).ok_or(Error::Truncated)?)),
            Operand::Variable => {
                let slice = take(at, 2)?;
                Value::Variable(u16::from_le_bytes([slice[0], slice[1]]))
            }
            Operand::Int8 => Value::Int(i64::from(*code.get(at).ok_or(Error::Truncated)? as i8)),
            Operand::Int32 => {
                let slice = take(at, 4)?;
                Value::Int(i64::from(i32::from_le_bytes([
                    slice[0], slice[1], slice[2], slice[3],
                ])))
            }
            Operand::Int64 => {
                let slice = take(at, 8)?;
                Value::Int(i64::from_le_bytes(slice.try_into().unwrap_or([0; 8])))
            }
            Operand::Float32 => {
                let slice = take(at, 4)?;
                Value::Float(f64::from(f32::from_le_bytes([
                    slice[0], slice[1], slice[2], slice[3],
                ])))
            }
            Operand::Float64 => {
                let slice = take(at, 8)?;
                Value::Float(f64::from_le_bytes(slice.try_into().unwrap_or([0; 8])))
            }
            Operand::Token => {
                let slice = take(at, 4)?;
                Value::Token(Token(u32::from_le_bytes([
                    slice[0], slice[1], slice[2], slice[3],
                ])))
            }
            // A branch counts from the instruction *after* it, which is why
            // the target needs the width of the operand as well as its value.
            Operand::BranchShort => {
                let delta = i64::from(*code.get(at).ok_or(Error::Truncated)? as i8);
                Value::Target((at as i64 + 1 + delta) as u32)
            }
            Operand::Branch => {
                let slice = take(at, 4)?;
                let delta = i64::from(i32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]));
                Value::Target((at as i64 + 4 + delta) as u32)
            }
            Operand::Switch => {
                let slice = take(at, 4)?;
                let count = u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]) as usize;
                let after = at + 4 + count * 4;
                let mut targets = Vec::with_capacity(count);
                for index in 0..count {
                    let slice = take(at + 4 + index * 4, 4)?;
                    let delta =
                        i64::from(i32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]));
                    targets.push((after as i64 + delta) as u32);
                }
                Value::Targets(targets)
            }
        };

        at += match &value {
            Value::Targets(targets) => 4 + 4 * targets.len(),
            _ => operand.width(),
        };
        instructions.push(Instruction {
            offset,
            opcode,
            name,
            value,
        });
    }
    Ok(instructions)
}
