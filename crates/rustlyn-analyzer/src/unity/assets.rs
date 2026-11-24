//! GUID to asset and back.
//!
//! Everything Unity serializes — scenes, prefabs, materials — refers to other
//! assets only by the GUID from their `.meta`. Without this table
//! `{fileID: 11500000, guid: a79441f3…}` is noise; with it, it is a reference
//! to a particular script.
//!
//! Built from every `.meta` under `Assets/`, `Packages/` and
//! `Library/PackageCache/` — the last so that package scripts and resources
//! resolve. The walk ignores `.gitignore`: an asset git ignores is still on
//! disk, and references to it are real.

use std::collections::HashMap;
use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::guid::Guid;

/// The index; immutable once built.
#[derive(Debug, Clone, Default)]
pub struct AssetIndex {
    /// Entries in the order they came: of two with one GUID the first wins,
    /// and the cache on disk keeps the same order.
    entries: Vec<(Guid, String)>,
    /// Paths relative to the project root, as entry numbers.
    path_by_guid: HashMap<Guid, u32>,
    /// Entries sorted by path; of equal paths the last wins. A list of
    /// numbers rather than a map of strings: there are hundreds of thousands
    /// of paths, and a second copy of each would cost megabytes.
    by_path: Vec<u32>,
    /// Scripts by file name: `Team` → `Assets/Scripts/Team.cs`. That is how
    /// an enum declared in a file of its own is found.
    script_by_name: HashMap<String, u32>,
    /// The project's assemblies: plugins in `Assets`, package libraries. They
    /// turn up here because each has a `.meta` — no separate walk is needed.
    assembly_paths: Vec<String>,
}

/// Where to look for `.meta` files, in order of priority.
pub const SEARCH_ROOTS: [&str; 3] = ["Assets", "Packages", "Library/PackageCache"];

/// The file name without its extension.
pub fn display_name_of(path: &str) -> String {
    let name = path.rsplit('/').next().unwrap_or(path);
    Path::new(name)
        .file_stem()
        .map_or_else(|| name.to_string(), |s| s.to_string_lossy().into_owned())
}

impl AssetIndex {
    /// The order matters: of two with one GUID the first wins. A project
    /// asset beats a package, an embedded package beats a cached copy.
    pub fn new(entries: Vec<(Guid, String)>) -> AssetIndex {
        let mut path_by_guid = HashMap::with_capacity(entries.len());
        let mut script_by_name = HashMap::new();
        let mut assembly_paths = Vec::new();
        for (k, (guid, path)) in entries.iter().enumerate() {
            path_by_guid.entry(*guid).or_insert(k as u32);
            if path.ends_with(".cs") {
                script_by_name
                    .entry(display_name_of(path))
                    .or_insert(k as u32);
            } else if path.ends_with(".dll") {
                assembly_paths.push(path.clone());
            }
        }
        let mut by_path: Vec<u32> = (0..entries.len() as u32).collect();
        by_path.sort_by(|&a, &b| {
            entries[a as usize]
                .1
                .cmp(&entries[b as usize].1)
                .then(a.cmp(&b))
        });
        AssetIndex {
            entries,
            path_by_guid,
            by_path,
            script_by_name,
            assembly_paths,
        }
    }

    pub fn count(&self) -> usize {
        self.path_by_guid.len()
    }

    pub fn entries(&self) -> &[(Guid, String)] {
        &self.entries
    }

    pub fn assembly_paths(&self) -> &[String] {
        &self.assembly_paths
    }

    pub fn path(&self, guid: Guid) -> Option<&str> {
        self.path_by_guid
            .get(&guid)
            .map(|&k| self.entries[k as usize].1.as_str())
    }

    pub fn guid(&self, rel_path: &str) -> Option<Guid> {
        // The last of the entries with this path.
        let after = self
            .by_path
            .partition_point(|&k| self.entries[k as usize].1.as_str() <= rel_path);
        let k = *self.by_path.get(after.checked_sub(1)?)?;
        let (guid, path) = &self.entries[k as usize];
        (path == rel_path).then_some(*guid)
    }

    pub fn script_path(&self, name: &str) -> Option<&str> {
        self.script_by_name
            .get(name)
            .map(|&k| self.entries[k as usize].1.as_str())
    }

    /// The name Unity shows an asset under: the file name without its
    /// extension. For a script it is also the class name, which Unity
    /// requires to match.
    pub fn display_name(&self, guid: Guid) -> Option<String> {
        self.path(guid).map(display_name_of)
    }

    // MARK: - the cache on disk

    /// A line per entry: `GUID<TAB>path`. Neither a GUID nor a Unity asset
    /// path holds a tab or a line break.
    pub fn serialized(&self) -> String {
        let mut out = String::with_capacity(self.entries.len() * 64 + 16);
        out.push_str("unity-assets 1\n");
        for (guid, path) in &self.entries {
            out.push_str(&guid.to_string());
            out.push('\t');
            out.push_str(path);
            out.push('\n');
        }
        out
    }

    /// `None` for another format or a damaged file: then the index is built
    /// again.
    pub fn deserialize(text: &str) -> Option<AssetIndex> {
        let mut lines = text.split('\n').filter(|l| !l.is_empty());
        if lines.next()? != "unity-assets 1" {
            return None;
        }
        let mut entries = Vec::new();
        for line in lines {
            let (guid, path) = line.split_once('\t')?;
            entries.push((Guid::parse(guid)?, path.to_string()));
        }
        Some(AssetIndex::new(entries))
    }

    /// The same entries in the same order: a fresh walk found nothing new, so
    /// neither the cache nor anything open needs redoing.
    pub fn has_same_entries(&self, other: &AssetIndex) -> bool {
        self.entries == other.entries
    }

    // MARK: - building

    /// Synchronous: call it off the main thread.
    ///
    /// `base` is the last index, built starting at `since` (seconds since
    /// 1970): a `.meta` unchanged since is not read, its GUID taken from
    /// there. A walk with a `stat` per file costs a fraction of reading
    /// 140,000 files, and between runs only a handful change.
    pub fn build(
        root: &Path,
        base: Option<&AssetIndex>,
        since: Option<f64>,
        should_stop: &dyn Fn() -> bool,
    ) -> AssetIndex {
        let reuse = base.is_some() && since.is_some();
        let mut metas: Vec<(String, i64)> = Vec::new();
        for folder in SEARCH_ROOTS {
            if should_stop() {
                break;
            }
            collect_meta_files(&root.join(folder), folder, reuse, &mut metas);
        }
        if should_stop() {
            return AssetIndex::new(Vec::new());
        }

        // A couple of seconds' margin: the file's time and the last build's
        // start are written by different clocks at different precision.
        let cutoff = (since.unwrap_or(0.0) - 2.0) as i64;

        // Reading thousands of small files is bound by system calls, not the
        // disk, so it parallelizes almost linearly.
        const CHUNK: usize = 256;
        let chunk_count = metas.len().div_ceil(CHUNK);
        let parts: Vec<Mutex<Vec<(Guid, String)>>> =
            (0..chunk_count).map(|_| Mutex::new(Vec::new())).collect();
        let next = AtomicUsize::new(0);
        let threads = std::thread::available_parallelism()
            .map_or(4, |n| n.get())
            .min(chunk_count.max(1));
        std::thread::scope(|scope| {
            for _ in 0..threads {
                scope.spawn(|| {
                    loop {
                        let c = next.fetch_add(1, Ordering::Relaxed);
                        if c >= chunk_count {
                            break;
                        }
                        let mut local = Vec::with_capacity(CHUNK);
                        for (meta, modified) in
                            &metas[c * CHUNK..((c + 1) * CHUNK).min(metas.len())]
                        {
                            let asset = &meta[..meta.len() - 5]; // without ".meta"
                            if reuse
                                && *modified < cutoff
                                && let Some(guid) = base.and_then(|b| b.guid(asset))
                            {
                                local.push((guid, asset.to_string()));
                                continue;
                            }
                            if let Some(guid) = read_guid(&root.join(meta)) {
                                local.push((guid, asset.to_string()));
                            }
                        }
                        *parts[c].lock().unwrap() = local;
                    }
                });
            }
        });
        AssetIndex::new(
            parts
                .into_iter()
                .flat_map(|p| p.into_inner().unwrap())
                .collect(),
        )
    }
}

/// Every `.meta` in the subtree, as paths from the project root (`rel` is the
/// folder's own). Hidden folders and folders ending in `~` (`Samples~`,
/// `Documentation~`) Unity does not import, and neither do we walk them.
/// `stat` only when the modification time is wanted (`with_times`): then
/// each path has it in seconds, otherwise zero. Links are not followed;
/// without `stat` a link named `.meta` counts as a file, with it not — as
/// `fts` behaves.
fn collect_meta_files(dir: &Path, rel: &str, with_times: bool, out: &mut Vec<(String, i64)>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        let path = format!("{rel}/{name}");
        if kind.is_dir() {
            if name.starts_with('.') || name.ends_with('~') {
                continue;
            }
            collect_meta_files(&entry.path(), &path, with_times, out);
            continue;
        }
        if !path.ends_with(".meta") || (with_times && !kind.is_file()) {
            continue;
        }
        if !kind.is_file() && !kind.is_symlink() {
            continue;
        }
        let modified = if with_times {
            entry.metadata().map_or(i64::MAX, |m| mtime(&m))
        } else {
            0
        };
        out.push((path, modified));
    }
}

/// Seconds since 1970, like `st_mtime`; negative before 1970.
fn mtime(m: &fs::Metadata) -> i64 {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        m.mtime()
    }
    #[cfg(not(unix))]
    {
        let Ok(time) = m.modified() else {
            return i64::MAX;
        };
        match time.duration_since(std::time::UNIX_EPOCH) {
            Ok(after) => after.as_secs() as i64,
            Err(before) => -(before.duration().as_secs_f64().ceil() as i64),
        }
    }
}

/// The GUID of a `.meta`. It is always on the second line, so only the
/// start of the file is read, not the whole importer.
pub fn read_guid(path: &Path) -> Option<Guid> {
    let mut file = File::open(path).ok()?;
    let mut buffer = [0u8; 256];
    let n = file.read(&mut buffer).ok()?;
    if n == 0 {
        return None;
    }
    parse_meta(&buffer[..n])
}

/// Looks for the line `guid: <32 hex digits>` at the start of a `.meta`.
pub fn parse_meta(bytes: &[u8]) -> Option<Guid> {
    let key = b"guid: ";
    let mut line_start = 0;
    while line_start + key.len() + 32 <= bytes.len() {
        if bytes[line_start..].starts_with(key) {
            return Guid::parse_at(&bytes[line_start + key.len()..], 0);
        }
        let newline = bytes[line_start..].iter().position(|&b| b == b'\n')?;
        line_start += newline + 1;
    }
    None
}
