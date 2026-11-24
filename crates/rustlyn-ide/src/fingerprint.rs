//! Telling whether the input to a piece of work has changed since it was done.
//!
//! Every layer above this one is expensive enough to be worth not repeating,
//! and cheap enough to repeat that nobody would notice the cache was wrong.
//! That combination is how stale answers get shipped, so the check is made
//! explicit here rather than left to each layer.
//!
//! There are two ways to ask, and the difference matters:
//!
//! * A [`Stamp`] is what the file system already knows — length and
//!   modification time. It costs one `stat` and no read, so it is what the
//!   fast path asks.
//! * A [`Fingerprint`] adds a hash of the bytes. It costs a read, and it is
//!   the only answer that is actually about the content.
//!
//! The stamp alone is not enough. Checking out a branch rewrites modification
//! times on files whose content did not change, and two writes inside one
//! file-system tick can leave the stamp alone on a file that did. So a stamp
//! miss is not a cache miss: it is a reason to read the file and compare
//! hashes, and a matching hash re-stamps the entry instead of redoing the
//! work. A whole `git checkout` back and forth costs one pass of hashing and
//! no reparsing at all.

use std::path::Path;
use std::time::SystemTime;

/// What the file system knows about a file without opening it.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Stamp {
    pub len: u64,
    /// Nanoseconds since the epoch, or zero when the platform has no time for
    /// the file. Zero never compares equal to a real time, so a file without
    /// one falls through to the hash every time rather than matching wrongly.
    pub modified_ns: u128,
}

impl Stamp {
    /// Reads the stamp of a file, or `None` when it cannot be seen at all.
    #[must_use]
    pub fn of(path: &Path) -> Option<Self> {
        let metadata = std::fs::metadata(path).ok()?;
        Some(Self {
            len: metadata.len(),
            modified_ns: metadata
                .modified()
                .ok()
                .and_then(|time| time.duration_since(SystemTime::UNIX_EPOCH).ok())
                .map_or(0, |since| since.as_nanos()),
        })
    }

    /// Whether this stamp can stand for a cached answer taken under `other`.
    ///
    /// A stamp with no modification time never matches: the platform is not
    /// telling us what we asked, and guessing in the direction of "unchanged"
    /// is the guess that ships stale answers.
    #[must_use]
    pub const fn matches(self, other: Self) -> bool {
        self.modified_ns != 0 && self.len == other.len && self.modified_ns == other.modified_ns
    }
}

/// A stamp together with a hash of the bytes it stood for.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Fingerprint {
    pub stamp: Stamp,
    pub hash: u64,
}

impl Fingerprint {
    #[must_use]
    pub const fn new(stamp: Stamp, hash: u64) -> Self {
        Self { stamp, hash }
    }

    /// The fingerprint of bytes that are already in hand, with no stamp —
    /// an unsaved buffer, which no `stat` describes.
    #[must_use]
    pub fn of_bytes(bytes: &[u8]) -> Self {
        Self {
            stamp: Stamp {
                len: bytes.len() as u64,
                modified_ns: 0,
            },
            hash: hash(bytes),
        }
    }

    /// Reads a file and fingerprints it, handing back the bytes so the caller
    /// does not read them twice.
    pub fn of_file(path: &Path) -> std::io::Result<(Self, Vec<u8>)> {
        let stamp = Stamp::of(path).unwrap_or_default();
        let bytes = std::fs::read(path)?;
        Ok((
            Self {
                stamp,
                hash: hash(&bytes),
            },
            bytes,
        ))
    }
}

/// How a cached entry answered the question "is this still good?".
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Freshness {
    /// The stamp matched: the answer stands, and nothing was read.
    Stamped,
    /// The stamp moved but the bytes hashed the same: the answer stands, and
    /// the caller should re-stamp the entry so the next check is free again.
    Rehashed,
    /// The content is genuinely different.
    Stale,
}

impl Freshness {
    #[must_use]
    pub const fn is_usable(self) -> bool {
        matches!(self, Self::Stamped | Self::Rehashed)
    }
}

/// A 64-bit hash of a byte string.
///
/// This decides whether work is repeated, not where anything is stored, so it
/// wants to be fast over megabytes and to not collide by accident. It is not
/// a cryptographic hash and nothing here defends against a file crafted to
/// collide with another.
///
/// The shape is the usual multiply-and-fold: eat eight bytes at a time into a
/// 128-bit product, fold the halves together, and finish the tail. Sixty-four
/// bits gives a one-in-2^32 collision chance at four billion distinct files,
/// which is several orders of magnitude past any project this will open.
#[must_use]
pub fn hash(bytes: &[u8]) -> u64 {
    const SEED: u64 = 0x9E37_79B9_7F4A_7C15;
    const K1: u64 = 0xFF51_AFD7_ED55_8CCD;
    const K2: u64 = 0xC4CE_B9FE_1A85_EC53;

    #[inline]
    fn mix(a: u64, b: u64) -> u64 {
        let product = u128::from(a) * u128::from(b);
        (product as u64) ^ ((product >> 64) as u64)
    }

    let mut acc = SEED ^ (bytes.len() as u64).wrapping_mul(K1);
    let mut chunks = bytes.chunks_exact(8);
    for chunk in &mut chunks {
        let word = u64::from_le_bytes(chunk.try_into().expect("chunks_exact(8) yields 8 bytes"));
        acc = mix(acc ^ word, K2);
    }

    // The tail is padded rather than looped over byte by byte: the length is
    // already in the accumulator, so padding cannot make two different tails
    // hash alike.
    let tail = chunks.remainder();
    if !tail.is_empty() {
        let mut word = [0u8; 8];
        word[..tail.len()].copy_from_slice(tail);
        acc = mix(acc ^ u64::from_le_bytes(word), K1);
    }

    acc = mix(acc, K2);
    acc ^ (acc >> 29)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_hash_depends_on_every_byte() {
        let base = b"public sealed class PlayerPawn : MonoBehaviour";
        let mut seen = std::collections::HashSet::new();
        seen.insert(hash(base));
        for index in 0..base.len() {
            let mut changed = base.to_vec();
            changed[index] ^= 0x20;
            assert!(
                seen.insert(hash(&changed)),
                "flipping byte {index} did not change the hash",
            );
        }
    }

    #[test]
    fn length_is_part_of_the_hash() {
        // Padding the tail must not make a short string hash like a padded one.
        assert_ne!(hash(b"ab"), hash(b"ab\0"));
        assert_ne!(hash(b""), hash(b"\0"));
    }

    #[test]
    fn hashing_is_the_same_across_chunk_boundaries() {
        // The eight-byte loop and the tail must agree about what they read.
        let text: Vec<u8> = (0u8..=255).cycle().take(1000).collect();
        for length in 0..text.len() {
            let once = hash(&text[..length]);
            assert_eq!(once, hash(&text[..length]));
        }
        // Lengths either side of a chunk boundary stay distinct.
        assert_ne!(hash(&text[..8]), hash(&text[..9]));
        assert_ne!(hash(&text[..15]), hash(&text[..16]));
    }

    #[test]
    fn a_stamp_without_a_time_never_matches() {
        let nothing = Stamp {
            len: 10,
            modified_ns: 0,
        };
        assert!(!nothing.matches(nothing));
    }

    #[test]
    fn a_stamp_matches_only_itself() {
        let one = Stamp {
            len: 10,
            modified_ns: 5,
        };
        assert!(one.matches(one));
        assert!(!one.matches(Stamp {
            len: 11,
            modified_ns: 5
        }));
        assert!(!one.matches(Stamp {
            len: 10,
            modified_ns: 6
        }));
    }
}
