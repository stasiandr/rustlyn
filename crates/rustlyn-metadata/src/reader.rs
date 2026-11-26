//! Walking the metadata root, the streams and the tables.
//!
//! The one thing worth knowing about the table stream: rows have no headers
//! and tables have no separators. The stream header says which tables are
//! present and how many rows each has, and everything after that is arithmetic
//! — a column's width depends on how many rows the table it points into has,
//! and a row's width is the sum of its columns'. Get one width wrong and every
//! table after it reads plausible nonsense.

use crate::heaps::Heaps;
use crate::pe::{Image, slice};
use crate::tables::{self, Column};
use crate::{Error, Token};

/// One table's rows, and how to step through them.
#[derive(Clone, Copy, Debug)]
pub struct Table<'a> {
    number: u8,
    rows: u32,
    row_size: usize,
    bytes: &'a [u8],
    widths: &'a Widths,
}

/// The widths every column kind takes in this particular assembly.
#[derive(Clone, Debug)]
struct Widths {
    string: usize,
    guid: usize,
    blob: usize,
    /// How many rows each table has, which is what decides an index's width.
    rows: [u32; 64],
}

impl Widths {
    /// A row number is two bytes while the table it names fits in two.
    const fn row_width(&self, table: u8) -> usize {
        if self.rows[table as usize] < (1 << 16) {
            2
        } else {
            4
        }
    }

    /// A coded index spends some bits on the tag, so it goes to four bytes
    /// sooner than a plain row number does.
    fn coded_width(&self, coded: tables::Coded) -> usize {
        let largest = coded
            .tables
            .iter()
            .map(|table| self.rows[*table as usize])
            .max()
            .unwrap_or(0);
        if u64::from(largest) < (1u64 << (16 - coded.bits)) {
            2
        } else {
            4
        }
    }

    fn width(&self, column: Column) -> usize {
        match column {
            Column::U8 => 1,
            Column::U16 => 2,
            Column::U32 => 4,
            Column::String => self.string,
            Column::Guid => self.guid,
            Column::Blob => self.blob,
            Column::Row(table) => self.row_width(table),
            Column::Coded(coded) => self.coded_width(coded),
        }
    }
}

/// One row, read on demand.
#[derive(Clone, Copy, Debug)]
pub struct Row<'a> {
    table: Table<'a>,
    bytes: &'a [u8],
}

impl<'a> Row<'a> {
    /// A column as a plain number, whatever its width.
    #[must_use]
    pub fn number(&self, column: usize) -> u32 {
        let columns = tables::columns(self.table.number);
        let mut at = 0usize;
        for (index, kind) in columns.iter().enumerate() {
            let width = self.table.widths.width(*kind);
            if index == column {
                return match self.bytes.get(at..at + width) {
                    Some([a]) => u32::from(*a),
                    Some([a, b]) => u32::from(u16::from_le_bytes([*a, *b])),
                    Some([a, b, c, d]) => u32::from_le_bytes([*a, *b, *c, *d]),
                    _ => 0,
                };
            }
            at += width;
        }
        0
    }

    /// A column that names a row of another table, as a token.
    #[must_use]
    pub fn token(&self, column: usize) -> Token {
        match tables::columns(self.table.number).get(column) {
            Some(Column::Row(table)) => Token::new(*table, self.number(column)),
            Some(Column::Coded(coded)) => coded
                .decode(self.number(column))
                .map_or(Token(0), |(table, row)| Token::new(table, row)),
            _ => Token(0),
        }
    }
}

/// An assembly's metadata, read.
#[derive(Clone, Debug)]
pub struct Assembly<'a> {
    image: Image<'a>,
    heaps: Heaps<'a>,
    widths: Widths,
    /// Where each present table's rows begin, inside the table stream.
    starts: [usize; 64],
    row_sizes: [usize; 64],
    stream: &'a [u8],
    /// Where the IL lives, so a method body can be found from its address.
    pub entry_point: Token,
}

impl<'a> Assembly<'a> {
    /// Reads an assembly out of the bytes of a file.
    ///
    /// # Errors
    ///
    /// Returns an error when the file is not a .NET assembly, or its metadata
    /// is malformed.
    pub fn read(bytes: &'a [u8]) -> Result<Self, Error> {
        let image = Image::read(bytes)?;
        let cli = image.cli_header as usize;
        let read32 = |at: usize| -> Result<u32, Error> {
            slice(bytes, at, 4)
                .map(|slice| u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
        };

        // The CLI header points at the metadata root and names the entry
        // point, which is the one token the runtime needs before any table.
        let metadata_rva = read32(cli + 8)?;
        let metadata_size = read32(cli + 12)? as usize;
        let entry_point = Token(read32(cli + 20)?);
        let root = image.offset_of(metadata_rva)? as usize;
        let metadata = slice(bytes, root, metadata_size)?;
        if metadata.get(..4) != Some(b"BSJB") {
            return Err(Error::NotMetadata);
        }
        // Everything from here on is read at a place the file names, and a
        // damaged file names places it does not have: each read says the
        // file ends early there instead of reading past the end.
        let word = |at: usize| -> Result<usize, Error> {
            slice(metadata, at, 4)
                .map(|slice| u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]) as usize)
        };

        // The root is a header, a version string of its own length, then one
        // header per stream.
        let version_length = word(12)?;
        let mut at = version_length.checked_add(16).ok_or(Error::Truncated)?;
        let streams = slice(metadata, at.checked_add(2).ok_or(Error::Truncated)?, 2)
            .map(|slice| u16::from_le_bytes([slice[0], slice[1]]))?;
        at += 4;

        let mut heaps = Heaps::default();
        let mut table_stream: &[u8] = &[];
        for _ in 0..streams {
            let offset = word(at)?;
            let size = word(at + 4)?;
            at += 8;
            let start = at;
            while metadata.get(at).is_some_and(|byte| *byte != 0) {
                at += 1;
            }
            let name = std::str::from_utf8(slice(metadata, start, at - start)?).unwrap_or("");
            // Each header is padded to a four-byte boundary.
            at = (at + 4) & !3;
            let body = slice(metadata, offset, size)?;
            match name {
                "#Strings" => heaps.strings = body,
                "#US" => heaps.user_strings = body,
                "#Blob" => heaps.blobs = body,
                "#GUID" => heaps.guids = body,
                // `#~` is the compressed form and `#-` the uncompressed one;
                // they differ in whether the `Ptr` tables are used, which the
                // reader does not care about.
                "#~" | "#-" => table_stream = body,
                _ => {}
            }
        }
        if table_stream.is_empty() {
            return Err(Error::MissingStream("#~"));
        }

        // The table stream's own header: the heap widths, then which tables
        // are present, then a row count for each.
        let heap_sizes = *table_stream.get(6).ok_or(Error::Truncated)?;
        let valid = u64::from_le_bytes(
            slice(table_stream, 8, 8)?
                .try_into()
                .map_err(|_| Error::Truncated)?,
        );
        let mut widths = Widths {
            string: if heap_sizes & 0x01 == 0 { 2 } else { 4 },
            guid: if heap_sizes & 0x02 == 0 { 2 } else { 4 },
            blob: if heap_sizes & 0x04 == 0 { 2 } else { 4 },
            rows: [0; 64],
        };
        let mut at = 24;
        for number in 0..64u8 {
            if valid >> number & 1 == 1 {
                widths.rows[number as usize] = u32::from_le_bytes(
                    slice(table_stream, at, 4)?
                        .try_into()
                        .map_err(|_| Error::Truncated)?,
                );
                at += 4;
            }
        }

        // Only now can a row size be worked out, because a column's width
        // depends on how many rows every table has.
        let mut row_sizes = [0usize; 64];
        let mut starts = [0usize; 64];
        for number in 0..64u8 {
            row_sizes[number as usize] = tables::columns(number)
                .iter()
                .map(|column| widths.width(*column))
                .sum();
        }
        for number in 0..64u8 {
            let rows = widths.rows[number as usize] as usize;
            // Rows of a table whose columns are not known cannot be stepped
            // over, so nothing after them can be found — and a row count is
            // a number anyone can write: four thousand million rows of no
            // width took as long to walk as that many of any.
            if rows > 0 && row_sizes[number as usize] == 0 {
                return Err(Error::Malformed("rows in a table that does not exist"));
            }
            starts[number as usize] = at;
            at = rows
                .checked_mul(row_sizes[number as usize])
                .and_then(|length| at.checked_add(length))
                .ok_or(Error::Truncated)?;
            // The rows the header counts are there to be read: a count past
            // the end of the stream is a table nobody could walk.
            if at > table_stream.len() {
                return Err(Error::Truncated);
            }
        }

        Ok(Self {
            image,
            heaps,
            widths,
            starts,
            row_sizes,
            stream: table_stream,
            entry_point,
        })
    }

    #[must_use]
    pub const fn heaps(&self) -> &Heaps<'a> {
        &self.heaps
    }

    #[must_use]
    pub const fn image(&self) -> &Image<'a> {
        &self.image
    }

    /// How many rows a table has: none, for a number that is no table's
    /// (a token read out of a file may carry any).
    #[must_use]
    pub fn rows(&self, number: u8) -> u32 {
        self.widths.rows.get(number as usize).copied().unwrap_or(0)
    }

    /// One table, ready to be stepped through; an empty one for a number
    /// that is no table's.
    #[must_use]
    pub fn table(&self, number: u8) -> Table<'_> {
        let index = number as usize;
        if index >= self.starts.len() {
            return Table {
                number,
                rows: 0,
                row_size: 0,
                bytes: &[],
                widths: &self.widths,
            };
        }
        let start = self.starts[index];
        let size = self.row_sizes[index];
        let length = size * self.widths.rows[index] as usize;
        Table {
            number,
            rows: self.widths.rows[index],
            row_size: size,
            bytes: self.stream.get(start..start + length).unwrap_or(&[]),
            widths: &self.widths,
        }
    }

    /// The row a token names, if it names one.
    #[must_use]
    pub fn row(&self, token: Token) -> Option<Row<'_>> {
        if token.is_nil() {
            return None;
        }
        self.table(token.table()).row(token.row())
    }
}

impl<'a> Table<'a> {
    #[must_use]
    pub const fn number(&self) -> u8 {
        self.number
    }

    #[must_use]
    pub const fn len(&self) -> u32 {
        self.rows
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.rows == 0
    }

    /// One row, numbered from one the way a token numbers it.
    #[must_use]
    pub fn row(&self, number: u32) -> Option<Row<'a>> {
        if number == 0 || number > self.rows {
            return None;
        }
        let at = (number as usize - 1) * self.row_size;
        Some(Row {
            table: *self,
            bytes: self.bytes.get(at..at + self.row_size)?,
        })
    }

    /// Every row, in order.
    pub fn iter(&self) -> impl Iterator<Item = Row<'a>> + use<'a> {
        let table = *self;
        (1..=self.rows).filter_map(move |number| table.row(number))
    }
}
