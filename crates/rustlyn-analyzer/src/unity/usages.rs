//! Where an asset is used — without Unity and without a language server.
//!
//! Every reference to an asset in a serialized file is its GUID, so the
//! search is a search for 32 bytes through every text asset of the project.
//! `memmem` over memory-mapped files gets through hundreds of megabytes of
//! scenes and prefabs in a fraction of a second; only files with hits are
//! parsed.

use std::collections::HashSet;
#[cfg(unix)]
use std::ffi::c_int;
use std::ffi::c_void;
use std::fs::File;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::guid::Guid;
use super::yaml::UnityFile;

/// One place an asset is referenced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hit {
    pub rel_path: String,
    /// The line, from zero.
    pub line: usize,
    /// The byte offset of the GUID in its line.
    pub column: usize,
    /// The byte offset of the GUID in the file.
    pub offset: usize,
    /// Where exactly: `Canvas / Button › PlayerInput`; `None` when the file is
    /// not a serialized Unity file.
    pub context: Option<String>,
}

/// The files Unity keeps references to assets in, by GUID. Compared with the
/// extension in lowercase.
pub const SEARCHABLE_EXTENSIONS: [&str; 36] = [
    "unity",
    "prefab",
    "asset",
    "mat",
    "anim",
    "controller",
    "overridecontroller",
    "playable",
    "mask",
    "physicmaterial",
    "physicsmaterial2d",
    "mixer",
    "rendertexture",
    "lighting",
    "spriteatlas",
    "spriteatlasv2",
    "terrainlayer",
    "signal",
    "preset",
    "guiskin",
    "fontsettings",
    "flare",
    "brush",
    "cubemap",
    "giparams",
    "scenetemplate",
    "shadergraph",
    "shadersubgraph",
    "vfx",
    "vfxoperator",
    "vfxblock",
    "asmdef",
    "asmref",
    "uxml",
    "uss",
    "tss",
];

/// Whether a file can hold references to assets.
#[must_use]
pub fn is_searchable(rel_path: &str) -> bool {
    Path::new(rel_path).extension().is_some_and(|ext| {
        SEARCHABLE_EXTENSIONS.contains(&ext.to_string_lossy().to_lowercase().as_str())
    })
}

/// Files larger than this are not parsed for context; they get a line number
/// only.
pub const MAX_CONTEXT_BYTES: usize = 64 * 1024 * 1024;

/// Synchronous and parallel: call it off the main thread.
///
/// Several hits inside one object fold into one: a nested prefab mentions its
/// source's GUID in each of dozens of overridden lines, and what matters is
/// that it was placed there.
pub fn find(
    guid: Guid,
    root: &Path,
    paths: &[String],
    resolve: &(dyn Fn(Guid) -> Option<String> + Sync),
    should_stop: &(dyn Fn() -> bool + Sync),
) -> Vec<Hit> {
    let needle = guid.to_string().into_bytes();
    let candidates: Vec<&String> = paths.iter().filter(|p| is_searchable(p)).collect();
    let per_file: Vec<Mutex<Vec<Hit>>> = (0..candidates.len())
        .map(|_| Mutex::new(Vec::new()))
        .collect();
    let next = AtomicUsize::new(0);
    let threads = std::thread::available_parallelism()
        .map_or(4, |n| n.get())
        .min(candidates.len().max(1));
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let k = next.fetch_add(1, Ordering::Relaxed);
                    if k >= candidates.len() {
                        break;
                    }
                    if should_stop() {
                        continue;
                    }
                    let rel = candidates[k];
                    let Some(mapped) = Mapped::open(&root.join(rel)) else {
                        continue;
                    };
                    *per_file[k].lock().unwrap() = hits(mapped.bytes(), &needle, rel, resolve);
                }
            });
        }
    });
    per_file
        .into_iter()
        .flat_map(|m| m.into_inner().unwrap())
        .collect()
}

/// The hits in one file's bytes; `needle` is the GUID as text.
pub fn hits(
    bytes: &[u8],
    needle: &[u8],
    rel_path: &str,
    resolve: &dyn Fn(Guid) -> Option<String>,
) -> Vec<Hit> {
    let offsets = occurrences(needle, bytes);
    if offsets.is_empty() {
        return Vec::new();
    }

    // Line numbers in one pass over the file; the hits are sorted.
    let mut positions = Vec::with_capacity(offsets.len());
    let (mut line, mut line_start, mut cursor) = (0, 0, 0);
    for &offset in &offsets {
        while cursor < offset {
            if bytes[cursor] == b'\n' {
                line += 1;
                line_start = cursor + 1;
            }
            cursor += 1;
        }
        positions.push((line, line_start, offset));
    }

    // Context only for Unity serialized files.
    let mut file = None;
    if bytes.len() <= MAX_CONTEXT_BYTES
        && bytes.len() >= 7
        && (bytes.starts_with(b"%YAML") || contains_header(bytes))
    {
        file = UnityFile::parse(bytes);
    }

    let mut result = Vec::new();
    let mut seen_objects = HashSet::new();
    for (line, line_start, offset) in positions {
        let mut context = None;
        if let Some(file) = &file
            && let Some(index) = file.object_index_containing_line(line)
        {
            if !seen_objects.insert(index) {
                continue;
            }
            context = Some(file.describe(index, resolve));
        }
        result.push(Hit {
            rel_path: rel_path.to_string(),
            line,
            column: offset - line_start,
            offset,
            context,
        });
    }
    result
}

fn contains_header(bytes: &[u8]) -> bool {
    !occurrences(b"--- !u!", &bytes[..bytes.len().min(512)]).is_empty()
}

#[cfg(unix)]
unsafe extern "C" {
    fn memmem(
        haystack: *const c_void,
        haystack_len: usize,
        needle: *const c_void,
        needle_len: usize,
    ) -> *mut c_void;
    fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: i64,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> c_int;
}

/// Every occurrence of `needle`. Without `memmem` (the Windows CRT has none),
/// by finding the first byte and comparing the rest: slower on the same
/// files, with the same result.
#[cfg(not(unix))]
pub fn occurrences(needle: &[u8], bytes: &[u8]) -> Vec<usize> {
    let mut result = Vec::new();
    if needle.is_empty() || bytes.len() < needle.len() {
        return result;
    }
    let last = bytes.len() - needle.len();
    let mut offset = 0;
    while offset <= last {
        let Some(step) = bytes[offset..=last].iter().position(|b| *b == needle[0]) else {
            break;
        };
        let position = offset + step;
        if &bytes[position..position + needle.len()] == needle {
            result.push(position);
            offset = position + needle.len();
        } else {
            offset = position + 1;
        }
    }
    result
}

/// Every occurrence of `needle`, through `memmem`, which libc vectorizes.
#[cfg(unix)]
pub fn occurrences(needle: &[u8], bytes: &[u8]) -> Vec<usize> {
    let mut result = Vec::new();
    if needle.is_empty() || bytes.len() < needle.len() {
        return result;
    }
    let mut offset = 0;
    while offset + needle.len() <= bytes.len() {
        let found = unsafe {
            memmem(
                bytes.as_ptr().add(offset) as *const c_void,
                bytes.len() - offset,
                needle.as_ptr() as *const c_void,
                needle.len(),
            )
        };
        if found.is_null() {
            break;
        }
        let position = found as usize - bytes.as_ptr() as usize;
        result.push(position);
        offset = position + needle.len();
    }
    result
}

/// A file mapped into memory, read-only.
#[derive(Debug)]
pub struct Mapped {
    pointer: *mut c_void,
    length: usize,
    /// An empty file, or one that would not map, read whole.
    fallback: Vec<u8>,
}

unsafe impl Send for Mapped {}
unsafe impl Sync for Mapped {}

impl Mapped {
    pub fn open(path: &Path) -> Option<Mapped> {
        let file = File::open(path).ok()?;
        let metadata = file.metadata().ok()?;
        if !metadata.is_file() {
            return None;
        }
        let length = metadata.len() as usize;
        if length == 0 {
            return Some(Mapped {
                pointer: std::ptr::null_mut(),
                length: 0,
                fallback: Vec::new(),
            });
        }
        #[cfg(unix)]
        {
            use std::os::fd::AsRawFd;
            const PROT_READ: c_int = 1;
            const MAP_PRIVATE: c_int = 2;
            let pointer = unsafe {
                mmap(
                    std::ptr::null_mut(),
                    length,
                    PROT_READ,
                    MAP_PRIVATE,
                    file.as_raw_fd(),
                    0,
                )
            };
            if pointer as isize != -1 && !pointer.is_null() {
                return Some(Mapped {
                    pointer,
                    length,
                    fallback: Vec::new(),
                });
            }
        }
        // Did not map (or on Windows, where there is no mapping): read whole.
        let mut bytes = Vec::with_capacity(length);
        let mut file = file;
        std::io::Read::read_to_end(&mut file, &mut bytes).ok()?;
        Some(Mapped {
            pointer: std::ptr::null_mut(),
            length: 0,
            fallback: bytes,
        })
    }

    pub fn bytes(&self) -> &[u8] {
        if self.pointer.is_null() {
            &self.fallback
        } else {
            unsafe { std::slice::from_raw_parts(self.pointer as *const u8, self.length) }
        }
    }
}

impl Drop for Mapped {
    fn drop(&mut self) {
        #[cfg(unix)]
        if !self.pointer.is_null() {
            unsafe { munmap(self.pointer, self.length) };
        }
    }
}
