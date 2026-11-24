//! Diffs: the unified format git and code review services print, and a line
//! diff of two texts computed here.
//!
//! Both speak the same [`Kind`] and zero-based line ranges, so changes from
//! either source can be shown the same way.

pub mod lines;
pub mod unified;

pub use lines::{Change, Kind, MAX_EDITS, changes, changes_of_lines};
pub use unified::{Block, UnifiedDiff};
