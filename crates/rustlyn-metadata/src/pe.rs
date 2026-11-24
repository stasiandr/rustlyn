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
        let at = |offset: usize| -> Result<u32, Error> {
            bytes
                .get(offset..offset + 4)
                .map(|slice| u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
                .ok_or(Error::Truncated)
        };
        let at16 = |offset: usize| -> Result<u16, Error> {
            bytes
                .get(offset..offset + 2)
                .map(|slice| u16::from_le_bytes([slice[0], slice[1]]))
                .ok_or(Error::Truncated)
        };

        if bytes.get(..2) != Some(b"MZ") {
            return Err(Error::NotAnImage);
        }
        // The DOS stub ends with the offset of the PE signature.
        let pe = at(0x3C)? as usize;
        if bytes.get(pe..pe + 4) != Some(b"PE\0\0") {
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
        let mut parsed = Vec::with_capacity(sections);
        for index in 0..sections {
            let at_section = table + 40 * index;
            let name = bytes
                .get(at_section..at_section + 8)
                .ok_or(Error::Truncated)?;
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
                rva >= section.virtual_address && rva < section.virtual_address + section.raw_size
            })
            .map(|section| section.raw_offset + (rva - section.virtual_address))
            .ok_or(Error::BadAddress(rva))
    }

    /// A slice of the file at a relative virtual address.
    ///
    /// # Errors
    ///
    /// Returns an error when the address is in no section or the slice runs
    /// past the end of the file.
    pub fn at_rva(&self, rva: u32, length: usize) -> Result<&'a [u8], Error> {
        let offset = self.offset_of(rva)? as usize;
        self.bytes
            .get(offset..offset + length)
            .ok_or(Error::Truncated)
    }
}
