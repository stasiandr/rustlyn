//! The PE file a managed assembly lives inside.
//!
//! A .NET assembly is a Windows executable whose only real content is the CLI
//! header and what it points at. The native scaffolding around it — the DOS
//! stub, the section table, the data directories — exists because the format
//! demands it, not because the runtime reads much of it.
//!
//! Two numbers govern the layout and are the usual source of a file that
//! loads nowhere: a section's `VirtualAddress` is aligned to the section
//! alignment and its `PointerToRawData` to the file alignment, and the two are
//! different, so an address in the file is not an address in memory. Every
//! offset the metadata stores is a virtual one.

/// Where things are once the file is mapped.
const SECTION_ALIGNMENT: u32 = 0x2000;
const FILE_ALIGNMENT: u32 = 0x200;
/// The base a PE32 image prefers; the loader relocates if it has to.
const IMAGE_BASE: u32 = 0x0040_0000;
/// The first section starts on the page after the headers.
const TEXT_RVA: u32 = SECTION_ALIGNMENT;

/// What goes into the assembly, in the order the section will hold it.
#[derive(Debug)]
pub(crate) struct PeLayout {
    /// The bytes fields with an RVA start out as — what array initializers
    /// are copied out of — first in the section, where their addresses do
    /// not move with the IL after them.
    pub(crate) data: Vec<u8>,
    /// The IL bodies, concatenated and aligned.
    pub(crate) il: Vec<u8>,
    /// The embedded resources, each its length and then its bytes, which the
    /// CLI header's resources directory points at; empty for none.
    pub(crate) resources: Vec<u8>,
    /// The metadata root.
    pub(crate) metadata: Vec<u8>,
    /// The token of the method to start at, or zero for a library.
    pub(crate) entry_point: u32,
}

/// The virtual address the IL blob will have, after `data` bytes of field
/// data.
///
/// The emitter needs this before the metadata exists, because a `MethodDef`
/// row stores the address of its body; only the field data comes before the
/// IL in the section, so the address is known without laying anything out.
#[must_use]
pub(crate) const fn il_rva(data: usize) -> u32 {
    align(TEXT_RVA + data as u32, 8)
}

/// The virtual address of the field data at `offset`.
#[must_use]
pub(crate) const fn data_rva(offset: u32) -> u32 {
    TEXT_RVA + offset
}

/// Builds the whole file.
#[must_use]
pub(crate) fn write(layout: &PeLayout) -> Vec<u8> {
    let il_rva = il_rva(layout.data.len());
    let resources_rva = align(il_rva + layout.il.len() as u32, 8);
    let metadata_rva = align(resources_rva + layout.resources.len() as u32, 4);
    let cli_header_rva = align(metadata_rva + layout.metadata.len() as u32, 4);
    // The header is the last thing in the section, and the section runs on
    // for as much of a header as any loader reads (see [`CLI_HEADER_READ`]).
    let text_size = cli_header_rva + CLI_HEADER_READ - TEXT_RVA;

    // The section's contents, laid out at the same relative offsets they will
    // have in memory.
    let mut text = vec![0u8; text_size as usize];
    text[..layout.data.len()].copy_from_slice(&layout.data);
    let il_offset = (il_rva - TEXT_RVA) as usize;
    text[il_offset..il_offset + layout.il.len()].copy_from_slice(&layout.il);
    let resources_offset = (resources_rva - TEXT_RVA) as usize;
    text[resources_offset..resources_offset + layout.resources.len()]
        .copy_from_slice(&layout.resources);
    let metadata_offset = (metadata_rva - TEXT_RVA) as usize;
    text[metadata_offset..metadata_offset + layout.metadata.len()]
        .copy_from_slice(&layout.metadata);
    let cli_offset = (cli_header_rva - TEXT_RVA) as usize;
    let resources = if layout.resources.is_empty() {
        None
    } else {
        Some((resources_rva, layout.resources.len() as u32))
    };
    text[cli_offset..cli_offset + CLI_HEADER_SIZE as usize].copy_from_slice(&cli_header(
        metadata_rva,
        layout.metadata.len() as u32,
        layout.entry_point,
        resources,
    ));

    let raw_size = align(text_size, FILE_ALIGNMENT);
    let headers_size = align(HEADERS_SIZE, FILE_ALIGNMENT);

    let mut file = Vec::with_capacity((headers_size + raw_size) as usize);
    write_headers(
        &mut file,
        text_size,
        raw_size,
        headers_size,
        cli_header_rva,
        CLI_HEADER_SIZE,
        layout.entry_point == 0,
    );
    file.resize(headers_size as usize, 0);
    file.extend_from_slice(&text);
    file.resize((headers_size + raw_size) as usize, 0);
    file
}

const CLI_HEADER_SIZE: u32 = 72;

/// How much Mono reads where the CLI header is: its `MonoCLIHeader` still
/// has the fields an early draft of the format gave the header, 136 bytes in
/// all, and a header with fewer than that left in the file after it is an
/// image it will not open ("Invalid Image") — which, with the header last in
/// the section, was a matter of how the section's end fell against the file
/// alignment. What lies past the header's 72 bytes is zeroes.
const CLI_HEADER_READ: u32 = 136;

/// The size of everything before the first section, before alignment.
const HEADERS_SIZE: u32 = 0x80 + 4 + 20 + 224 + 40;

fn cli_header(
    metadata_rva: u32,
    metadata_size: u32,
    entry_point: u32,
    resources: Option<(u32, u32)>,
) -> Vec<u8> {
    let mut header = Vec::with_capacity(CLI_HEADER_SIZE as usize);
    header.extend_from_slice(&CLI_HEADER_SIZE.to_le_bytes());
    header.extend_from_slice(&2u16.to_le_bytes()); // major runtime version
    header.extend_from_slice(&5u16.to_le_bytes()); // minor
    header.extend_from_slice(&metadata_rva.to_le_bytes());
    header.extend_from_slice(&metadata_size.to_le_bytes());
    // COMIMAGE_FLAGS_ILONLY. Not 32-bit-required: the assembly runs on
    // whichever word size the host uses.
    header.extend_from_slice(&1u32.to_le_bytes());
    header.extend_from_slice(&entry_point.to_le_bytes());
    // Resources: where the embedded blobs are, or nothing.
    let (resources_rva, resources_size) = resources.unwrap_or((0, 0));
    header.extend_from_slice(&resources_rva.to_le_bytes());
    header.extend_from_slice(&resources_size.to_le_bytes());
    // Strong name, code manager, vtable fixups, export addresses, managed
    // native header: eight bytes each, all absent.
    header.resize(CLI_HEADER_SIZE as usize, 0);
    header
}

#[allow(clippy::too_many_arguments)]
fn write_headers(
    file: &mut Vec<u8>,
    text_virtual_size: u32,
    text_raw_size: u32,
    headers_size: u32,
    cli_header_rva: u32,
    cli_header_size: u32,
    library: bool,
) {
    // The DOS header, whose only live field is the offset of the PE one.
    file.extend_from_slice(b"MZ");
    file.resize(0x3C, 0);
    file.extend_from_slice(&0x80u32.to_le_bytes());
    file.resize(0x80, 0);

    file.extend_from_slice(b"PE\0\0");

    // COFF header.
    file.extend_from_slice(&0x014Cu16.to_le_bytes()); // i386, as IL-only files say
    file.extend_from_slice(&1u16.to_le_bytes()); // one section
    file.extend_from_slice(&0u32.to_le_bytes()); // timestamp: fixed, for reproducibility
    file.extend_from_slice(&0u32.to_le_bytes()); // symbol table
    file.extend_from_slice(&0u32.to_le_bytes()); // symbol count
    file.extend_from_slice(&224u16.to_le_bytes()); // optional header size
    // Executable, 32-bit word machine; and a DLL when there is nothing to
    // start at.
    let dll = if library { 0x2000 } else { 0 };
    file.extend_from_slice(&(0x0102u16 | dll).to_le_bytes());

    // Optional header, PE32.
    file.extend_from_slice(&0x010Bu16.to_le_bytes());
    file.push(48); // linker major
    file.push(0); // linker minor
    file.extend_from_slice(&text_raw_size.to_le_bytes()); // size of code
    file.extend_from_slice(&0u32.to_le_bytes()); // initialised data
    file.extend_from_slice(&0u32.to_le_bytes()); // uninitialised data
    // A .NET Framework image put a jump to `_CorExeMain` here and an import
    // directory naming `mscoree.dll` beside it. .NET Core loads an assembly
    // through its own host and never reads either; it does still validate an
    // import directory that is present, so the honest thing is to have none.
    file.extend_from_slice(&0u32.to_le_bytes());
    file.extend_from_slice(&TEXT_RVA.to_le_bytes()); // base of code
    file.extend_from_slice(&TEXT_RVA.to_le_bytes()); // base of data
    file.extend_from_slice(&IMAGE_BASE.to_le_bytes());
    file.extend_from_slice(&SECTION_ALIGNMENT.to_le_bytes());
    file.extend_from_slice(&FILE_ALIGNMENT.to_le_bytes());
    file.extend_from_slice(&4u16.to_le_bytes()); // os major
    file.extend_from_slice(&0u16.to_le_bytes());
    file.extend_from_slice(&0u16.to_le_bytes()); // image major
    file.extend_from_slice(&0u16.to_le_bytes());
    file.extend_from_slice(&4u16.to_le_bytes()); // subsystem major
    file.extend_from_slice(&0u16.to_le_bytes());
    file.extend_from_slice(&0u32.to_le_bytes()); // win32 version
    file.extend_from_slice(&(align(TEXT_RVA + text_virtual_size, SECTION_ALIGNMENT)).to_le_bytes());
    file.extend_from_slice(&headers_size.to_le_bytes());
    file.extend_from_slice(&0u32.to_le_bytes()); // checksum
    file.extend_from_slice(&3u16.to_le_bytes()); // console subsystem
    // High-entropy ASLR, dynamic base, NX, no SEH.
    file.extend_from_slice(&0x8560u16.to_le_bytes());
    file.extend_from_slice(&0x0010_0000u32.to_le_bytes()); // stack reserve
    file.extend_from_slice(&0x1000u32.to_le_bytes()); // stack commit
    file.extend_from_slice(&0x0010_0000u32.to_le_bytes()); // heap reserve
    file.extend_from_slice(&0x1000u32.to_le_bytes()); // heap commit
    file.extend_from_slice(&0u32.to_le_bytes()); // loader flags
    file.extend_from_slice(&16u32.to_le_bytes()); // data directory count

    // Data directories. Only the CLI header is used.
    let mut directories = [(0u32, 0u32); 16];
    directories[14] = (cli_header_rva, cli_header_size);
    for (rva, size) in directories {
        file.extend_from_slice(&rva.to_le_bytes());
        file.extend_from_slice(&size.to_le_bytes());
    }

    // The one section.
    let mut name = *b".text\0\0\0";
    name[5] = 0;
    file.extend_from_slice(&name);
    file.extend_from_slice(&text_virtual_size.to_le_bytes());
    file.extend_from_slice(&TEXT_RVA.to_le_bytes());
    file.extend_from_slice(&text_raw_size.to_le_bytes());
    file.extend_from_slice(&headers_size.to_le_bytes());
    file.extend_from_slice(&0u32.to_le_bytes()); // relocations
    file.extend_from_slice(&0u32.to_le_bytes()); // line numbers
    file.extend_from_slice(&0u16.to_le_bytes());
    file.extend_from_slice(&0u16.to_le_bytes());
    // Code, readable, executable.
    file.extend_from_slice(&0x6000_0020u32.to_le_bytes());
}

const fn align(value: u32, alignment: u32) -> u32 {
    value.div_ceil(alignment) * alignment
}

/// The `runtimeconfig.json` that `dotnet <assembly>.dll` looks for beside the
/// assembly. Without it the host does not know which runtime to load — and
/// which one is the one the references came from: an assembly built against
/// .NET 11 names `System.Runtime, Version=11.0.0.0`, which no older runtime
/// will hand over.
#[must_use]
pub(crate) fn runtime_config(major: u16) -> String {
    format!(
        r#"{{
  "runtimeOptions": {{
    "tfm": "net{major}.0",
    "framework": {{
      "name": "Microsoft.NETCore.App",
      "version": "{major}.0.0"
    }}
  }}
}}
"#
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Vec<u8> {
        write(&PeLayout {
            data: Vec::new(),
            il: vec![0x2A],
            resources: Vec::new(),
            metadata: b"BSJB".to_vec(),
            entry_point: 0x0600_0001,
        })
    }

    #[test]
    fn the_file_starts_with_mz_and_points_at_the_pe_header() {
        let file = sample();
        assert_eq!(&file[..2], b"MZ");
        let pe = u32::from_le_bytes(file[0x3C..0x40].try_into().unwrap()) as usize;
        assert_eq!(&file[pe..pe + 4], b"PE\0\0");
    }

    #[test]
    fn the_sizes_are_aligned_the_way_the_loader_expects() {
        let file = sample();
        assert_eq!(file.len() % FILE_ALIGNMENT as usize, 0);
        let pe = 0x80;
        let section = pe + 4 + 20 + 224;
        let raw_size = u32::from_le_bytes(file[section + 16..section + 20].try_into().unwrap());
        let raw_pointer = u32::from_le_bytes(file[section + 20..section + 24].try_into().unwrap());
        assert_eq!(raw_size % FILE_ALIGNMENT, 0);
        assert_eq!(raw_pointer % FILE_ALIGNMENT, 0);
        let virtual_address =
            u32::from_le_bytes(file[section + 12..section + 16].try_into().unwrap());
        assert_eq!(virtual_address % SECTION_ALIGNMENT, 0);
    }

    #[test]
    fn mono_can_read_its_whole_cli_header_from_the_file() {
        // Mono reads 136 bytes where the header is; whatever the metadata's
        // length, the file has to hold them, or it is an "Invalid Image".
        for padding in 0..8 {
            let file = write(&PeLayout {
                data: Vec::new(),
                il: vec![0x2A; 1 + padding],
                resources: Vec::new(),
                metadata: vec![0; 2520 + 4 * padding],
                entry_point: 0,
            });
            let pe = 0x80;
            let directories = pe + 4 + 20 + 96;
            let cli_rva = u32::from_le_bytes(
                file[directories + 14 * 8..directories + 14 * 8 + 4]
                    .try_into()
                    .unwrap(),
            );
            let section = pe + 4 + 20 + 224;
            let virtual_address =
                u32::from_le_bytes(file[section + 12..section + 16].try_into().unwrap());
            let raw_pointer =
                u32::from_le_bytes(file[section + 20..section + 24].try_into().unwrap());
            let offset = cli_rva - virtual_address + raw_pointer;
            assert!(offset + CLI_HEADER_READ <= file.len() as u32);
        }
    }

    #[test]
    fn the_cli_directory_finds_the_cli_header() {
        let file = sample();
        let pe = 0x80;
        let directories = pe + 4 + 20 + 96;
        let cli_rva = u32::from_le_bytes(
            file[directories + 14 * 8..directories + 14 * 8 + 4]
                .try_into()
                .unwrap(),
        );
        let section = pe + 4 + 20 + 224;
        let virtual_address =
            u32::from_le_bytes(file[section + 12..section + 16].try_into().unwrap());
        let raw_pointer = u32::from_le_bytes(file[section + 20..section + 24].try_into().unwrap());
        let offset = (cli_rva - virtual_address + raw_pointer) as usize;
        // The header opens with its own size.
        assert_eq!(
            u32::from_le_bytes(file[offset..offset + 4].try_into().unwrap()),
            CLI_HEADER_SIZE
        );
        // ...and carries the entry point token it was given.
        assert_eq!(
            u32::from_le_bytes(file[offset + 20..offset + 24].try_into().unwrap()),
            0x0600_0001
        );
    }

    #[test]
    fn the_il_lands_where_its_address_says() {
        let file = sample();
        let pe = 0x80;
        let section = pe + 4 + 20 + 224;
        let virtual_address =
            u32::from_le_bytes(file[section + 12..section + 16].try_into().unwrap());
        let raw_pointer = u32::from_le_bytes(file[section + 20..section + 24].try_into().unwrap());
        let offset = (il_rva(0) - virtual_address + raw_pointer) as usize;
        assert_eq!(file[offset], 0x2A);
    }
}
