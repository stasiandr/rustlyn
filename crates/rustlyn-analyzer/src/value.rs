//! How values move through code: the value graph — where a value comes
//! from, through the places that write it, to its sources.
//!
//! * [`flow`] — the text reading of one place: written or read, and what
//!   the right-hand side holds; [`ecs`] — the same for components written
//!   through ECS stashes.
//! * [`origin`] — which literals and library members are sources.
//! * [`compiler`] — what the graph asks the compiler ([`rustlyn_ide::Session`]
//!   answers), [`symbols`] — declarations by name, for what the compiler
//!   does not answer.
//! * [`analysis`] — the searches: writes, returns, callers, origins.
//! * [`graph`] — the graph itself, expanding lazily or at once;
//!   [`headless`] — printed as a tree or JSON, and a survey of a folder.
//! * [`edges`] — what a host adds through [`EdgeProvider`]s; [`wording`] —
//!   the graph's text as data, worded by a [`Wording`].
//!
//! Positions: the compiler's locations are lines and UTF-16 columns (as
//! [`rustlyn_ide::session::Location`] counts); a [`Site`]'s `offset` is a
//! UTF-8 byte offset. The text readers in [`flow`] work over UTF-16 code
//! units internally (TODO: bytes), the way the editor they were written for
//! counted.

pub mod analysis;
pub mod compiler;
pub mod document;
pub mod ecs;
pub mod edges;
pub mod flow;
pub mod graph;
pub mod headless;
pub mod origin;
pub mod project;
pub mod symbols;
pub mod text;
pub mod wording;

#[cfg(test)]
mod graph_cases;
#[cfg(test)]
pub(crate) mod testing;

pub use analysis::{Context, Decl, Root, Site, Source, SourceKind, Trigger};
pub use compiler::{Compiler, Inspector, InspectorHit, Target};
pub use edges::{EdgeProvider, Member};
pub use graph::{Graph, Job, Node, NodeKind, Outcome, Reach, State};
pub use project::{Project, Projects};
pub use symbols::{IndexSymbols, Symbol, SymbolKind, Symbols};
pub use wording::{English, Wording};

/// How many lines of a method after its first a place's method excerpt
/// spans at most.
pub const LINES_AFTER: usize = 90;

/// Members every value, string or collection (LINQ) has, to recognize them
/// when the compiler does not know the receiver's type — and to ignore a
/// call that "may" reach an override of `ToString` on any object.
pub const UNIVERSAL_MEMBERS: &[&str] = &[
    "ToString",
    "GetHashCode",
    "Equals",
    "GetType",
    "CompareTo",
    "Substring",
    "Trim",
    "TrimStart",
    "TrimEnd",
    "Split",
    "Replace",
    "ToLower",
    "ToUpper",
    "ToLowerInvariant",
    "ToUpperInvariant",
    "Contains",
    "StartsWith",
    "EndsWith",
    "IndexOf",
    "LastIndexOf",
    "PadLeft",
    "PadRight",
    "ToList",
    "ToArray",
    "ToDictionary",
    "ToHashSet",
    "First",
    "FirstOrDefault",
    "Last",
    "LastOrDefault",
    "Single",
    "SingleOrDefault",
    "Where",
    "Select",
    "SelectMany",
    "Any",
    "All",
    "Sum",
    "Min",
    "Max",
    "Average",
    "OrderBy",
    "OrderByDescending",
    "ThenBy",
    "Skip",
    "Take",
    "Distinct",
    "Concat",
    "Aggregate",
    "ElementAt",
    "ElementAtOrDefault",
    "GetValueOrDefault",
    "Length",
    "ToUniversalTime",
    "ToLocalTime",
    "AddSeconds",
    "AddMinutes",
    "AddHours",
    "AddDays",
    "AddMilliseconds",
    "Subtract",
];
