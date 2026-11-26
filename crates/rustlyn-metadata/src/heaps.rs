//! The four heaps, and reading something out of one.
//!
//! `#Strings` and `#US` hold text, `#Blob` holds signatures and `#GUID` holds
//! the module's identity. An index into one is an offset rather than an
//! ordinal, which is why nothing here is a list: a heap is a wall of bytes and
//! an index points into the middle of it.

use crate::Error;

#[derive(Clone, Debug, Default)]
pub struct Heaps<'a> {
    pub strings: &'a [u8],
    pub user_strings: &'a [u8],
    pub blobs: &'a [u8],
    pub guids: &'a [u8],
}

impl<'a> Heaps<'a> {
    /// A name out of `#Strings`, which holds UTF-8 runs ended by a zero.
    #[must_use]
    pub fn string(&self, offset: u32) -> &'a str {
        let offset = offset as usize;
        let Some(rest) = self.strings.get(offset..) else {
            return "";
        };
        let end = rest
            .iter()
            .position(|byte| *byte == 0)
            .unwrap_or(rest.len());
        std::str::from_utf8(&rest[..end]).unwrap_or("")
    }

    /// A blob, whose length is written in front of it.
    ///
    /// # Errors
    ///
    /// Returns an error when the offset or the length runs past the heap.
    pub fn blob(&self, offset: u32) -> Result<&'a [u8], Error> {
        Self::counted(self.blobs, offset)
    }

    /// A literal out of `#US`, which holds UTF-16 with a trailing flag byte.
    ///
    /// # Errors
    ///
    /// Returns an error when the offset or the length runs past the heap.
    pub fn user_string(&self, offset: u32) -> Result<String, Error> {
        let bytes = Self::counted(self.user_strings, offset)?;
        // The last byte says whether any character needs more than a `char`
        // would hold; it is not part of the text.
        let text = if bytes.is_empty() {
            bytes
        } else {
            &bytes[..bytes.len() - 1]
        };
        let units: Vec<u16> = text
            .chunks_exact(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
            .collect();
        Ok(String::from_utf16_lossy(&units))
    }

    /// The module's GUID, which is the one entry `#GUID` usually holds.
    #[must_use]
    pub fn guid(&self, index: u32) -> Option<&'a [u8]> {
        if index == 0 {
            return None;
        }
        let at = (index as usize - 1).checked_mul(16)?;
        crate::pe::slice(self.guids, at, 16).ok()
    }

    /// A run of bytes with its length compressed in front, as §II.23.2 writes
    /// one.
    fn counted(heap: &'a [u8], offset: u32) -> Result<&'a [u8], Error> {
        let at = offset as usize;
        let first = *heap.get(at).ok_or(Error::Truncated)?;
        let (length, start) = if first & 0x80 == 0 {
            (u32::from(first & 0x7F), at + 1)
        } else if first & 0x40 == 0 {
            let second = *heap.get(at + 1).ok_or(Error::Truncated)?;
            ((u32::from(first & 0x3F) << 8) | u32::from(second), at + 2)
        } else {
            let rest = crate::pe::slice(heap, at + 1, 3)?;
            (
                (u32::from(first & 0x1F) << 24)
                    | (u32::from(rest[0]) << 16)
                    | (u32::from(rest[1]) << 8)
                    | u32::from(rest[2]),
                at + 4,
            )
        };
        crate::pe::slice(heap, start, length as usize)
    }
}
