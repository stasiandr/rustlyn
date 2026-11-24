//! Reading the data an array initializer was compiled into.
//!
//! `new[] { 1, 2, 3 }` is compiled to a field with an address and no name
//! worth reading, and a call that copies its bytes into the array. The bytes
//! are the values, laid out as the element type lays them out.

use rustlyn_metadata::signature::TypeSig;
use rustlyn_metadata::table;

use crate::ir::Expr;
use crate::names::{FieldRef, Resolver};

/// How many bytes an element of an array initializer takes.
#[must_use]
pub fn element_width(resolver: Resolver<'_>, element: &TypeSig) -> Option<usize> {
    Some(match element {
        TypeSig::Boolean | TypeSig::Byte | TypeSig::SByte => 1,
        TypeSig::Char | TypeSig::Int16 | TypeSig::UInt16 => 2,
        TypeSig::Int32 | TypeSig::UInt32 | TypeSig::Single => 4,
        TypeSig::Int64 | TypeSig::UInt64 | TypeSig::Double => 8,
        // An enum is laid out as the type under it.
        TypeSig::ValueType(_) => element_width(resolver, &resolver.enum_underlying(element)?)?,
        _ => return None,
    })
}

/// The values a `FieldRVA` blob holds, as items of an array of the element
/// type, when the type is one whose layout is known.
#[must_use]
pub fn array_items(
    resolver: Resolver<'_>,
    field: &FieldRef,
    element: &TypeSig,
    count: i64,
) -> Option<Vec<Expr>> {
    if field.token.table() != table::FIELD || !(0..=1 << 18).contains(&count) {
        return None;
    }
    let rva = resolver.field_rva(field.token.row())?;
    let offset = resolver.assembly.image().offset_of(rva).ok()? as usize;
    let bytes = resolver.assembly.image().bytes().get(offset..)?;
    let width = element_width(resolver, element)?;
    let count = count as usize;
    let bytes = bytes.get(..count * width)?;
    let mut items = Vec::with_capacity(count);
    for chunk in bytes.chunks_exact(width) {
        let raw = |signed: bool| -> i64 {
            let mut buffer = [0u8; 8];
            buffer[..width].copy_from_slice(chunk);
            let value = u64::from_le_bytes(buffer);
            if signed {
                let shift = 64 - 8 * width as u32;
                ((value << shift) as i64) >> shift
            } else {
                value as i64
            }
        };
        items.push(match element {
            TypeSig::Boolean => Expr::Bool(chunk[0] != 0),
            TypeSig::Byte | TypeSig::UInt16 | TypeSig::UInt32 => Expr::Int(raw(false)),
            TypeSig::SByte | TypeSig::Int16 | TypeSig::Int32 => Expr::Int(raw(true)),
            TypeSig::Char => Expr::Char(raw(false) as u16),
            TypeSig::Int64 | TypeSig::UInt64 => Expr::Long(raw(true)),
            TypeSig::Single => Expr::Float(
                f64::from(f32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]])),
                true,
            ),
            TypeSig::Double => {
                let mut buffer = [0u8; 8];
                buffer.copy_from_slice(chunk);
                Expr::Float(f64::from_le_bytes(buffer), false)
            }
            _ => {
                let signed = matches!(
                    resolver.enum_underlying(element),
                    Some(TypeSig::SByte | TypeSig::Int16 | TypeSig::Int32 | TypeSig::Int64)
                );
                crate::stack::coerce_expr(resolver, Expr::Int(raw(signed)), element)
            }
        });
    }
    Some(items)
}
