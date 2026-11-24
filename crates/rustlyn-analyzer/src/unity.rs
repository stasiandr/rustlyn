//! A Unity project without Unity.
//!
//! Everything Unity serializes — scenes, prefabs, materials — refers to other
//! assets only by the GUID in their `.meta` file. [`assets`] maps GUIDs to
//! paths and back, [`yaml`] reads the serialized text format object by
//! object, and [`usages`] finds where an asset is referenced across the
//! project. Which C# methods the engine calls by name is
//! [`rustlyn_ide::semantic::unity`].

pub mod assets;
pub mod guid;
pub mod usages;
pub mod yaml;

pub use assets::AssetIndex;
pub use guid::Guid;
pub use yaml::{CodeUnit, Reference, Span, UnityFile, UnityObject};

#[cfg(test)]
mod tests;
