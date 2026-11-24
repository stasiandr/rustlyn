//! A small binary encoding for the things the cache keeps on disk.
//!
//! The workspace has no dependencies and this is not the place to start: what
//! goes to disk is our own data, read back by the same build that wrote it,
//! so the format only has to be unambiguous and fast. Every reader is
//! bounds-checked and returns `None` rather than panicking, because a cache
//! file is the one input that arrives already corrupted — a truncated write,
//! a half-finished copy, a file from an older build — and the answer to all
//! of those is to recompute, not to fall over.

/// Appends values to a byte buffer.
#[derive(Debug, Default)]
pub struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn finish(self) -> Vec<u8> {
        self.bytes
    }

    pub fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    pub fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    pub fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    pub fn u128(&mut self, value: u128) {
        self.bytes.extend_from_slice(&value.to_le_bytes());
    }

    pub fn bytes(&mut self, value: &[u8]) {
        self.u32(value.len() as u32);
        self.bytes.extend_from_slice(value);
    }

    pub fn str(&mut self, value: &str) {
        self.bytes(value.as_bytes());
    }

    /// Writes a length and then lets `each` write that many items.
    pub fn seq<T>(&mut self, items: &[T], mut each: impl FnMut(&mut Self, &T)) {
        self.u32(items.len() as u32);
        for item in items {
            each(self, item);
        }
    }
}

/// Reads values back, refusing to run off the end.
#[derive(Clone, Copy, Debug)]
pub struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    #[must_use]
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    #[must_use]
    pub const fn is_done(&self) -> bool {
        self.at >= self.bytes.len()
    }

    fn take(&mut self, count: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(count)?;
        let slice = self.bytes.get(self.at..end)?;
        self.at = end;
        Some(slice)
    }

    pub fn u8(&mut self) -> Option<u8> {
        self.take(1).map(|slice| slice[0])
    }

    pub fn u32(&mut self) -> Option<u32> {
        let slice = self.take(4)?;
        Some(u32::from_le_bytes(slice.try_into().ok()?))
    }

    pub fn u64(&mut self) -> Option<u64> {
        let slice = self.take(8)?;
        Some(u64::from_le_bytes(slice.try_into().ok()?))
    }

    pub fn u128(&mut self) -> Option<u128> {
        let slice = self.take(16)?;
        Some(u128::from_le_bytes(slice.try_into().ok()?))
    }

    pub fn bytes(&mut self) -> Option<&'a [u8]> {
        let length = self.u32()? as usize;
        self.take(length)
    }

    pub fn str(&mut self) -> Option<&'a str> {
        std::str::from_utf8(self.bytes()?).ok()
    }

    pub fn string(&mut self) -> Option<String> {
        self.str().map(ToOwned::to_owned)
    }

    /// Reads a length and then that many items.
    ///
    /// The length is capped against what is actually left in the buffer
    /// before anything is reserved: a corrupted length field would otherwise
    /// ask for gigabytes on the strength of four bytes that mean nothing.
    pub fn seq<T>(&mut self, mut each: impl FnMut(&mut Self) -> Option<T>) -> Option<Vec<T>> {
        let count = self.u32()? as usize;
        let remaining = self.bytes.len().saturating_sub(self.at);
        let mut items = Vec::with_capacity(count.min(remaining));
        for _ in 0..count {
            items.push(each(self)?);
        }
        Some(items)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_come_back_as_they_went_in() {
        let mut writer = Writer::new();
        writer.u8(7);
        writer.u32(70_000);
        writer.u64(1 << 40);
        writer.str("PlayerPawn");
        writer.seq(&["a", "bb", "ccc"], |w, s| w.str(s));
        let bytes = writer.finish();

        let mut reader = Reader::new(&bytes);
        assert_eq!(reader.u8(), Some(7));
        assert_eq!(reader.u32(), Some(70_000));
        assert_eq!(reader.u64(), Some(1 << 40));
        assert_eq!(reader.str(), Some("PlayerPawn"));
        assert_eq!(
            reader.seq(Reader::string),
            Some(vec!["a".to_owned(), "bb".to_owned(), "ccc".to_owned()])
        );
        assert!(reader.is_done());
    }

    #[test]
    fn a_truncated_buffer_gives_none_rather_than_panicking() {
        let mut writer = Writer::new();
        writer.str("a long enough string to survive being cut");
        let bytes = writer.finish();
        for length in 0..bytes.len() {
            let mut reader = Reader::new(&bytes[..length]);
            assert_eq!(
                reader.str(),
                None,
                "prefix of {length} bytes should not read"
            );
        }
    }

    #[test]
    fn a_corrupt_length_does_not_reserve_the_world() {
        // A count of four billion, with nothing behind it.
        let bytes = u32::MAX.to_le_bytes();
        let mut reader = Reader::new(&bytes);
        assert_eq!(reader.seq(Reader::u32), None);
    }

    #[test]
    fn invalid_utf8_is_refused() {
        let mut writer = Writer::new();
        writer.bytes(&[0xFF, 0xFE]);
        let bytes = writer.finish();
        assert_eq!(Reader::new(&bytes).str(), None);
    }
}
