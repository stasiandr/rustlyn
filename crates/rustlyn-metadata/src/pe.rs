//! Finding the metadata inside a PE file.
//!
//! A .NET assembly is a Windows executable with the metadata tucked into a
//! section, so reaching it means reading enough of the PE format to turn a
//! relative virtual address into a file offset. That is all this does: the
//! headers say where the sections are, the data directory says where the CLI
//! header is, and the CLI header says where the metadata is.

use crate::Error;

/// One section of the image, which is what maps addresses to file offsets.
#[derive(Clone, Debug)]
pub struct Section {
    pub name: String,
    pub virtual_address: u32,
    pub virtual_size: u32,
    pub raw_offset: u32,
    pub raw_size: u32,
}

/// The parts of a PE file this needs.
#[derive(Clone, Debug)]
pub struct Image<'a> {
    bytes: &'a [u8],
    sections: Vec<Section>,
    /// Where the CLI header sits, which is what makes this an assembly rather
    /// than any other executable.
    pub cli_header: u32,
}

impl<'a> Image<'a> {
    /// Reads the headers, far enough to find the metadata.
    ///
    /// # Errors
    ///
    /// Returns an error when the file is not a PE image, or is one with no CLI
    /// header — a native executable rather than a .NET assembly.
    pub fn read(bytes: &'a [u8]) -> Result<Self, Error> {
        // Every offset below is the file's own word for where something
        // is, and a damaged file says anything: the sums are checked, so
        // that one past the end of the address space is "the file ends
        // early" like any other.
        let at = |offset: usize| -> Result<u32, Error> {
            slice(bytes, offset, 4)
                .map(|slice| u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
        };
        let at16 = |offset: usize| -> Result<u16, Error> {
            slice(bytes, offset, 2).map(|slice| u16::from_le_bytes([slice[0], slice[1]]))
        };

        if bytes.get(..2) != Some(b"MZ") {
            return Err(Error::NotAnImage);
        }
        // The DOS stub ends with the offset of the PE signature.
        let pe = at(0x3C)? as usize;
        if slice(bytes, pe, 4).ok() != Some(b"PE\0\0") {
            return Err(Error::NotAnImage);
        }

        let sections = at16(pe + 6)? as usize;
        let optional = at16(pe + 20)? as usize;
        // The magic says PE32 or PE32+, which is the only thing that moves the
        // data directories.
        let magic = at16(pe + 24)?;
        let directories = pe + 24 + if magic == 0x20B { 112 } else { 96 };
        let cli_header = at(directories + 14 * 8)?;
        if cli_header == 0 {
            return Err(Error::NotAnAssembly);
        }

        let table = pe + 24 + optional;
        let mut parsed = Vec::new();
        for index in 0..sections {
            let at_section = table + 40 * index;
            let name = slice(bytes, at_section, 8)?;
            let name = String::from_utf8_lossy(name)
                .trim_end_matches('\0')
                .to_string();
            parsed.push(Section {
                name,
                virtual_size: at(at_section + 8)?,
                virtual_address: at(at_section + 12)?,
                raw_size: at(at_section + 16)?,
                raw_offset: at(at_section + 20)?,
            });
        }

        let mut image = Self {
            bytes,
            sections: parsed,
            cli_header: 0,
        };
        image.cli_header = image.offset_of(cli_header)?;
        Ok(image)
    }

    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub fn sections(&self) -> &[Section] {
        &self.sections
    }

    /// Where a relative virtual address lands in the file.
    ///
    /// # Errors
    ///
    /// Returns an error when the address is in no section, which means the
    /// file is malformed or the address was never one.
    pub fn offset_of(&self, rva: u32) -> Result<u32, Error> {
        self.sections
            .iter()
            .find(|section| {
                rva >= section.virtual_address
                    && u64::from(rva)
                        < u64::from(section.virtual_address) + u64::from(section.raw_size)
            })
            .and_then(|section| {
                section
                    .raw_offset
                    .checked_add(rva - section.virtual_address)
            })
            .ok_or(Error::BadAddress(rva))
    }

    /// The file from a relative virtual address on: what a method body is
    /// read out of, which has no length until its header says one.
    ///
    /// # Errors
    ///
    /// Returns an error when the address is in no section, or in one the
    /// file ends before.
    pub fn from_rva(&self, rva: u32) -> Result<&'a [u8], Error> {
        let offset = self.offset_of(rva)? as usize;
        self.bytes.get(offset..).ok_or(Error::Truncated)
    }

    /// A slice of the file at a relative virtual address.
    ///
    /// # Errors
    ///
    /// Returns an error when the address is in no section or the slice runs
    /// past the end of the file.
    pub fn at_rva(&self, rva: u32, length: usize) -> Result<&'a [u8], Error> {
        let offset = self.offset_of(rva)? as usize;
        slice(self.bytes, offset, length)
    }
}

/// `length` bytes at `offset`, or [`Error::Truncated`] where the file does
/// not have them — the sum checked, since both are whatever a file said.
pub(crate) fn slice(bytes: &[u8], offset: usize, length: usize) -> Result<&[u8], Error> {
    offset
        .checked_add(length)
        .and_then(|end| bytes.get(offset..end))
        .ok_or(Error::Truncated)
}
