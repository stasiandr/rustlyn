//! Not doing the same work twice.
//!
//! Every layer of this crate is a pure function of a file's bytes and a
//! handful of options, so every layer can be cached the same way. The ladder
//! a lookup walks is always:
//!
//! 1. **Stamp.** The entry in memory was taken under a length and a
//!    modification time. If the file still has them, the answer stands and
//!    nothing is read.
//! 2. **Hash.** The stamp moved, so the file is read and hashed. A branch
//!    switched back and forth rewrites times without changing bytes, and this
//!    is where that costs a read instead of a reparse.
//! 3. **Disk.** Nothing in memory, but a previous run may have left the answer
//!    in the cache directory, keyed by the hash of the bytes it was computed
//!    from. Opening a project a second time starts here.
//! 4. **Miss.** The caller is handed the bytes and computes.
//!
//! Memory is bounded by a byte budget rather than a count, because the things
//! kept here differ by four orders of magnitude in size — a line-state table
//! for a small file against the declarations of a whole project — and a count
//! would either hold too little of the small or far too much of the large.
//! Eviction is least-recently-used.

use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::fingerprint::{Fingerprint, Freshness, Stamp, hash};
use crate::wire::{Reader, Writer};

/// Which layer an entry belongs to. Part of the key, so the layers cannot
/// read each other's entries even when they are about the same file.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Layer {
    /// Line starts and lexer states: layer 2.
    Lines,
    /// The outline of one file: layer 3.
    Outline,
    /// One file's contribution to the project index: layer 4.
    FileSymbols,
    /// The surface of one assembly: layer 5.
    AssemblySurface,
    /// One decompiled type: layer 5.
    DecompiledType,
}

impl Layer {
    /// The directory name this layer's entries live in.
    const fn directory(self) -> &'static str {
        match self {
            Self::Lines => "lines",
            Self::Outline => "outline",
            Self::FileSymbols => "symbols",
            Self::AssemblySurface => "assembly",
            Self::DecompiledType => "decompiled",
        }
    }
}

/// What an entry is about: a layer, a file, and whatever options change the
/// answer for the same bytes.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Key {
    pub layer: Layer,
    pub path: PathBuf,
    /// A hash of the options the answer depends on — preprocessor symbols, a
    /// type name, the set of referenced assemblies. Two answers that differ
    /// only by options must not share a key.
    pub salt: u64,
}

impl Key {
    #[must_use]
    pub fn new(layer: Layer, path: impl Into<PathBuf>) -> Self {
        Self {
            layer,
            path: path.into(),
            salt: 0,
        }
    }

    #[must_use]
    pub fn salted(mut self, salt: u64) -> Self {
        self.salt = salt;
        self
    }

    /// The salt for a list of strings, for options that are one.
    #[must_use]
    pub fn salt_of(parts: &[&str]) -> u64 {
        let mut joined = Vec::new();
        for part in parts {
            joined.extend_from_slice(part.as_bytes());
            joined.push(0x1F); // a separator no identifier contains
        }
        hash(&joined)
    }
}

/// What a cache lookup found.
#[derive(Debug)]
pub enum Lookup<T> {
    /// The answer, still good. Nothing needs computing.
    Hit(Arc<T>),
    /// No usable answer. Here are the bytes it should be computed from, and
    /// the fingerprint to store it under.
    Miss(Vec<u8>, Fingerprint),
}

/// Something that can be kept on disk between runs.
///
/// Layers whose answers are cheap to recompute but expensive to encode can
/// skip this and use [`Cache::lookup_in_memory`] instead.
pub trait Cacheable: Sized {
    /// Bumped whenever the encoding changes, so a new build ignores the old
    /// build's files instead of misreading them.
    const VERSION: u32;

    fn encode(&self, writer: &mut Writer);
    fn decode(reader: &mut Reader<'_>) -> Option<Self>;

    /// Roughly how much memory this occupies, for the eviction budget. An
    /// estimate is fine; it decides when to evict, not correctness.
    fn weight(&self) -> usize;
}

struct Entry {
    value: Arc<dyn std::any::Any + Send + Sync>,
    print: Fingerprint,
    weight: usize,
    /// When this was last touched, by a counter rather than a clock: a clock
    /// can run backwards and does not tick fast enough to order two lookups.
    used: u64,
}

/// A cache shared by every layer.
#[derive(Debug)]
pub struct Cache {
    memory: Mutex<Memory>,
    /// Where entries survive between runs, or `None` to keep nothing.
    directory: Option<PathBuf>,
    clock: AtomicU64,
    hits: AtomicU64,
    rehashes: AtomicU64,
    disk_hits: AtomicU64,
    misses: AtomicU64,
}

#[derive(Default)]
struct Memory {
    entries: HashMap<Key, Entry>,
    weight: usize,
    budget: usize,
}

impl std::fmt::Debug for Memory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Memory")
            .field("entries", &self.entries.len())
            .field("weight", &self.weight)
            .field("budget", &self.budget)
            .finish()
    }
}

/// What the cache has been doing, for the status line and for tests.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Statistics {
    /// Answers taken from memory on the strength of the stamp alone.
    pub stamped: u64,
    /// Answers kept because the bytes hashed the same although the stamp moved.
    pub rehashed: u64,
    /// Answers read back from the cache directory.
    pub from_disk: u64,
    /// Answers that had to be computed.
    pub computed: u64,
    pub entries: usize,
    pub bytes: usize,
}

impl Cache {
    /// Where entries are kept between runs, if anywhere.
    #[must_use]
    pub fn directory(&self) -> Option<&Path> {
        self.directory.as_deref()
    }

    /// A cache holding up to `budget` bytes in memory and keeping entries in
    /// `directory` between runs.
    #[must_use]
    pub fn new(directory: Option<PathBuf>, budget: usize) -> Self {
        Self {
            memory: Mutex::new(Memory {
                budget,
                ..Memory::default()
            }),
            directory,
            clock: AtomicU64::new(0),
            hits: AtomicU64::new(0),
            rehashes: AtomicU64::new(0),
            disk_hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
        }
    }

    /// A cache that keeps nothing between runs — what tests and one-shot
    /// tools want.
    #[must_use]
    pub fn in_memory(budget: usize) -> Self {
        Self::new(None, budget)
    }

    #[must_use]
    pub fn statistics(&self) -> Statistics {
        let memory = self.memory.lock().unwrap_or_else(|e| e.into_inner());
        Statistics {
            stamped: self.hits.load(Ordering::Relaxed),
            rehashed: self.rehashes.load(Ordering::Relaxed),
            from_disk: self.disk_hits.load(Ordering::Relaxed),
            computed: self.misses.load(Ordering::Relaxed),
            entries: memory.entries.len(),
            bytes: memory.weight,
        }
    }

    /// Walks the ladder for a file on disk.
    ///
    /// On [`Lookup::Miss`] the caller computes the answer from the bytes it is
    /// handed and passes it to [`Self::store`] with the fingerprint.
    pub fn lookup<T>(&self, key: &Key, path: &Path) -> io::Result<Lookup<T>>
    where
        T: Cacheable + Send + Sync + 'static,
    {
        let current = Stamp::of(path);

        // 1. The stamp still matches what the entry was taken under.
        if let Some(current) = current
            && let Some(value) = self.fresh_in_memory::<T>(key, current, Freshness::Stamped)
        {
            self.hits.fetch_add(1, Ordering::Relaxed);
            return Ok(Lookup::Hit(value));
        }

        // 2. The stamp moved, so read and hash. This is the only read, and
        //    everything below reuses its bytes.
        let (print, bytes) = Fingerprint::of_file(path)?;

        if let Some(value) = self.rehash_in_memory::<T>(key, print) {
            self.rehashes.fetch_add(1, Ordering::Relaxed);
            return Ok(Lookup::Hit(value));
        }

        // 3. A previous run may have left it on disk under this content hash.
        if let Some(value) = self.read_from_disk::<T>(key, print) {
            self.disk_hits.fetch_add(1, Ordering::Relaxed);
            let value = self.put(key.clone(), print, value);
            return Ok(Lookup::Hit(value));
        }

        // 4. Nothing for it.
        self.misses.fetch_add(1, Ordering::Relaxed);
        Ok(Lookup::Miss(bytes, print))
    }

    /// The same ladder for bytes already in hand — an unsaved buffer, which no
    /// stamp describes, so this starts at the hash.
    pub fn lookup_bytes<T>(&self, key: &Key, bytes: &[u8]) -> Lookup<T>
    where
        T: Cacheable + Send + Sync + 'static,
    {
        let print = Fingerprint::of_bytes(bytes);
        if let Some(value) = self.rehash_in_memory::<T>(key, print) {
            self.hits.fetch_add(1, Ordering::Relaxed);
            return Lookup::Hit(value);
        }
        if let Some(value) = self.read_from_disk::<T>(key, print) {
            self.disk_hits.fetch_add(1, Ordering::Relaxed);
            let value = self.put(key.clone(), print, value);
            return Lookup::Hit(value);
        }
        self.misses.fetch_add(1, Ordering::Relaxed);
        Lookup::Miss(bytes.to_vec(), print)
    }

    /// Keeps `value` under `key`, in memory and on disk, and hands back the
    /// shared copy the caller should use.
    pub fn store<T>(&self, key: &Key, print: Fingerprint, value: T) -> Arc<T>
    where
        T: Cacheable + Send + Sync + 'static,
    {
        self.write_to_disk(key, print, &value);
        self.put(key.clone(), print, value)
    }

    /// Drops everything remembered about one file, across every layer.
    ///
    /// The layer is part of the key, so this has to sweep rather than remove.
    /// It is what a deleted file calls, which is rare enough that a sweep is
    /// cheaper than the second index it would take to avoid one.
    pub fn forget(&self, path: &Path) {
        let mut memory = self.memory.lock().unwrap_or_else(|e| e.into_inner());
        let doomed: Vec<Key> = memory
            .entries
            .keys()
            .filter(|key| key.path == path)
            .cloned()
            .collect();
        for key in doomed {
            if let Some(entry) = memory.entries.remove(&key) {
                memory.weight = memory.weight.saturating_sub(entry.weight);
            }
        }
    }

    /// Empties the cache in memory. The directory is left alone: its entries
    /// are keyed by content hash and are still true.
    pub fn clear(&self) {
        let mut memory = self.memory.lock().unwrap_or_else(|e| e.into_inner());
        memory.entries.clear();
        memory.weight = 0;
    }

    // MARK: - The rungs

    fn fresh_in_memory<T>(&self, key: &Key, current: Stamp, _why: Freshness) -> Option<Arc<T>>
    where
        T: Send + Sync + 'static,
    {
        let mut memory = self.memory.lock().unwrap_or_else(|e| e.into_inner());
        let used = self.clock.fetch_add(1, Ordering::Relaxed);
        let entry = memory.entries.get_mut(key)?;
        if !current.matches(entry.print.stamp) {
            return None;
        }
        entry.used = used;
        entry.value.clone().downcast::<T>().ok()
    }

    fn rehash_in_memory<T>(&self, key: &Key, print: Fingerprint) -> Option<Arc<T>>
    where
        T: Send + Sync + 'static,
    {
        let mut memory = self.memory.lock().unwrap_or_else(|e| e.into_inner());
        let used = self.clock.fetch_add(1, Ordering::Relaxed);
        let entry = memory.entries.get_mut(key)?;
        if entry.print.hash != print.hash || entry.print.stamp.len != print.stamp.len {
            return None;
        }
        // The content is the same but the file was touched. Re-stamp, so the
        // next lookup stops at the first rung and reads nothing.
        entry.print.stamp = print.stamp;
        entry.used = used;
        entry.value.clone().downcast::<T>().ok()
    }

    fn put<T>(&self, key: Key, print: Fingerprint, value: T) -> Arc<T>
    where
        T: Cacheable + Send + Sync + 'static,
    {
        let weight = value.weight();
        let shared = Arc::new(value);
        let mut memory = self.memory.lock().unwrap_or_else(|e| e.into_inner());
        let used = self.clock.fetch_add(1, Ordering::Relaxed);
        if let Some(previous) = memory.entries.insert(
            key,
            Entry {
                value: shared.clone(),
                print,
                weight,
                used,
            },
        ) {
            memory.weight = memory.weight.saturating_sub(previous.weight);
        }
        memory.weight += weight;
        memory.evict();
        shared
    }

    // MARK: - The directory

    fn file_for(&self, key: &Key, print: Fingerprint, version: u32) -> Option<PathBuf> {
        let directory = self.directory.as_ref()?;
        // The name is the content hash and the salt, not the path: two copies
        // of the same file share an entry, and a moved file keeps its own.
        Some(
            directory
                .join(key.layer.directory())
                .join(format!("{:016x}-{:016x}-{version}", print.hash, key.salt)),
        )
    }

    fn read_from_disk<T: Cacheable>(&self, key: &Key, print: Fingerprint) -> Option<T> {
        let file = self.file_for(key, print, T::VERSION)?;
        let bytes = std::fs::read(file).ok()?;
        let mut reader = Reader::new(&bytes);
        // The length the entry was computed from is written first: a hash
        // collision would otherwise hand back another file's answer.
        if reader.u64()? != print.stamp.len {
            return None;
        }
        T::decode(&mut reader)
    }

    fn write_to_disk<T: Cacheable>(&self, key: &Key, print: Fingerprint, value: &T) {
        let Some(file) = self.file_for(key, print, T::VERSION) else {
            return;
        };
        let Some(parent) = file.parent() else { return };
        if std::fs::create_dir_all(parent).is_err() {
            return;
        }
        let mut writer = Writer::new();
        writer.u64(print.stamp.len);
        value.encode(&mut writer);

        // Written beside the real name and renamed over it: a reader must
        // never see half a file, and two processes may be writing at once.
        let temporary = file.with_extension(format!("tmp{}", std::process::id()));
        if std::fs::write(&temporary, writer.finish()).is_ok()
            && std::fs::rename(&temporary, &file).is_err()
        {
            let _ = std::fs::remove_file(&temporary);
        }
    }
}

impl Memory {
    fn evict(&mut self) {
        if self.weight <= self.budget {
            return;
        }
        // Least recently used first. The number of entries is small enough
        // (thousands) that sorting on the rare overflow beats keeping an
        // intrusive list up to date on every hit.
        let mut order: Vec<(u64, Key)> = self
            .entries
            .iter()
            .map(|(key, entry)| (entry.used, key.clone()))
            .collect();
        order.sort_unstable_by_key(|(used, _)| *used);
        for (_, key) in order {
            if self.weight <= self.budget {
                break;
            }
            if let Some(entry) = self.entries.remove(&key) {
                self.weight = self.weight.saturating_sub(entry.weight);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(PartialEq, Eq, Debug)]
    struct Counted(String);

    impl Cacheable for Counted {
        const VERSION: u32 = 1;
        fn encode(&self, writer: &mut Writer) {
            writer.str(&self.0);
        }
        fn decode(reader: &mut Reader<'_>) -> Option<Self> {
            reader.string().map(Counted)
        }
        fn weight(&self) -> usize {
            self.0.len()
        }
    }

    /// A directory that cleans itself up, so tests leave nothing behind.
    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "rustlyn-ide-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).expect("a temporary directory");
            Self(path)
        }
        fn join(&self, name: &str) -> PathBuf {
            self.0.join(name)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn write(path: &Path, text: &str) {
        std::fs::write(path, text).expect("writing a test file");
    }

    #[test]
    fn a_second_lookup_costs_nothing() {
        let dir = TempDir::new("stamp");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let cache = Cache::in_memory(1 << 20);
        let key = Key::new(Layer::Outline, &file);

        let Lookup::Miss(bytes, print) = cache.lookup::<Counted>(&key, &file).expect("lookup")
        else {
            panic!("the first lookup must miss");
        };
        cache.store(&key, print, Counted(String::from_utf8(bytes).unwrap()));

        match cache.lookup::<Counted>(&key, &file).expect("lookup") {
            Lookup::Hit(value) => assert_eq!(value.0, "class A {}"),
            Lookup::Miss(..) => panic!("the second lookup must hit"),
        }
        assert_eq!(cache.statistics().stamped, 1);
        assert_eq!(cache.statistics().computed, 1);
    }

    #[test]
    fn touching_a_file_without_changing_it_does_not_recompute() {
        // This is the `git checkout` case: times move, bytes do not.
        let dir = TempDir::new("rehash");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let cache = Cache::in_memory(1 << 20);
        let key = Key::new(Layer::Outline, &file);

        let Lookup::Miss(_, print) = cache.lookup::<Counted>(&key, &file).expect("lookup") else {
            panic!("the first lookup must miss");
        };
        cache.store(&key, print, Counted("built once".into()));

        // Rewrite the same bytes: a new modification time, the same content.
        std::thread::sleep(std::time::Duration::from_millis(10));
        write(&file, "class A {}");

        match cache.lookup::<Counted>(&key, &file).expect("lookup") {
            Lookup::Hit(value) => assert_eq!(value.0, "built once"),
            Lookup::Miss(..) => panic!("the same bytes must not be recomputed"),
        }
        assert_eq!(cache.statistics().rehashed, 1);
        assert_eq!(cache.statistics().computed, 1);

        // And it was re-stamped, so the next lookup does not even hash.
        assert!(matches!(
            cache.lookup::<Counted>(&key, &file).expect("lookup"),
            Lookup::Hit(_)
        ));
        assert_eq!(cache.statistics().stamped, 1);
    }

    #[test]
    fn changing_a_file_does_recompute() {
        let dir = TempDir::new("stale");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let cache = Cache::in_memory(1 << 20);
        let key = Key::new(Layer::Outline, &file);

        let Lookup::Miss(_, print) = cache.lookup::<Counted>(&key, &file).expect("lookup") else {
            panic!("the first lookup must miss");
        };
        cache.store(&key, print, Counted("built once".into()));

        write(&file, "class B {}");
        assert!(matches!(
            cache.lookup::<Counted>(&key, &file).expect("lookup"),
            Lookup::Miss(..)
        ));
    }

    #[test]
    fn an_answer_survives_to_the_next_run() {
        let dir = TempDir::new("disk");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let store = dir.join("cache");
        let key = Key::new(Layer::Outline, &file);

        {
            let cache = Cache::new(Some(store.clone()), 1 << 20);
            let Lookup::Miss(_, print) = cache.lookup::<Counted>(&key, &file).expect("lookup")
            else {
                panic!("the first lookup must miss");
            };
            cache.store(&key, print, Counted("built once".into()));
        }

        // A new run: nothing in memory, everything on disk.
        let cache = Cache::new(Some(store), 1 << 20);
        match cache.lookup::<Counted>(&key, &file).expect("lookup") {
            Lookup::Hit(value) => assert_eq!(value.0, "built once"),
            Lookup::Miss(..) => panic!("the entry should have come back from disk"),
        }
        assert_eq!(cache.statistics().from_disk, 1);
    }

    #[test]
    fn options_that_change_the_answer_change_the_key() {
        let dir = TempDir::new("salt");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let cache = Cache::in_memory(1 << 20);
        let plain = Key::new(Layer::Outline, &file);
        let with_debug = Key::new(Layer::Outline, &file).salted(Key::salt_of(&["DEBUG"]));

        let Lookup::Miss(_, print) = cache.lookup::<Counted>(&plain, &file).expect("lookup") else {
            panic!("miss");
        };
        cache.store(&plain, print, Counted("no symbols".into()));

        assert!(
            matches!(
                cache.lookup::<Counted>(&with_debug, &file).expect("lookup"),
                Lookup::Miss(..)
            ),
            "a different salt must not read the other answer",
        );
    }

    #[test]
    fn a_corrupt_cache_file_is_recomputed_rather_than_believed() {
        let dir = TempDir::new("corrupt");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let store = dir.join("cache");
        let key = Key::new(Layer::Outline, &file);

        let cache = Cache::new(Some(store.clone()), 1 << 20);
        let Lookup::Miss(_, print) = cache.lookup::<Counted>(&key, &file).expect("lookup") else {
            panic!("miss");
        };
        cache.store(&key, print, Counted("built once".into()));
        cache.clear();

        // Truncate every file the cache wrote.
        for entry in std::fs::read_dir(store.join(Layer::Outline.directory())).expect("read_dir") {
            let path = entry.expect("entry").path();
            write(&path, "");
        }

        assert!(matches!(
            cache.lookup::<Counted>(&key, &file).expect("lookup"),
            Lookup::Miss(..)
        ));
    }

    #[test]
    fn the_budget_evicts_the_least_recently_used() {
        let dir = TempDir::new("evict");
        let cache = Cache::in_memory(20);
        let mut keys = Vec::new();
        for index in 0..4 {
            let file = dir.join(&format!("{index}.cs"));
            write(&file, "class A {}");
            let key = Key::new(Layer::Outline, &file);
            let Lookup::Miss(_, print) = cache.lookup::<Counted>(&key, &file).expect("lookup")
            else {
                panic!("miss");
            };
            // Ten bytes each, so the fourth must push the first out.
            cache.store(&key, print, Counted("0123456789".into()));
            keys.push((key, file));
        }
        let stats = cache.statistics();
        assert!(stats.bytes <= 20, "budget exceeded: {} bytes", stats.bytes);
        assert!(stats.entries <= 2, "too many entries: {}", stats.entries);
    }

    #[test]
    fn forgetting_a_file_drops_every_layer_of_it() {
        let dir = TempDir::new("forget");
        let file = dir.join("a.cs");
        write(&file, "class A {}");
        let cache = Cache::in_memory(1 << 20);
        for layer in [Layer::Outline, Layer::Lines, Layer::FileSymbols] {
            let key = Key::new(layer, &file);
            let Lookup::Miss(_, print) = cache.lookup::<Counted>(&key, &file).expect("lookup")
            else {
                panic!("miss");
            };
            cache.store(&key, print, Counted("x".into()));
        }
        assert_eq!(cache.statistics().entries, 3);
        cache.forget(&file);
        assert_eq!(cache.statistics().entries, 0);
    }

    #[test]
    fn an_unsaved_buffer_is_cached_by_its_bytes() {
        let cache = Cache::in_memory(1 << 20);
        let key = Key::new(Layer::Outline, "untitled.cs");

        let Lookup::Miss(_, print) = cache.lookup_bytes::<Counted>(&key, b"class A {}") else {
            panic!("miss");
        };
        cache.store(&key, print, Counted("built once".into()));

        assert!(matches!(
            cache.lookup_bytes::<Counted>(&key, b"class A {}"),
            Lookup::Hit(_)
        ));
        assert!(matches!(
            cache.lookup_bytes::<Counted>(&key, b"class B {}"),
            Lookup::Miss(..)
        ));
    }
}
