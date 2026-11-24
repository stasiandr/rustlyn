//! Emission: turning a bound tree into an assembly the CLR will run.
//!
//! The compiler's front end answers what a program means; this crate answers
//! what a machine should do about it. Between the two sits the bound tree,
//! which is the only input here — the syntax is never consulted again, so a
//! decision the binder made cannot be quietly remade with a different answer.
//!
//! The output is an ordinary .NET assembly: a PE file whose CLI header points
//! at ECMA-335 metadata, which points at the IL. `dotnet Program.dll` runs it,
//! which is the only test of an emitter worth trusting.

mod async_iterator;
mod async_machine;
mod codegen;
mod dynamic;
mod emitter;
mod expression_trees;
mod hoisting;
pub mod hot;
mod il;
mod iterator;
mod metadata;
mod nullable;
mod pe;
mod records;
mod references;
pub mod resources;
mod signature;
mod singleton;

pub use emitter::{
    Coverage, CoverageEntry, EmitError, Emitted, Incremental, IncrementalOptions, Rebuilt, Started,
    coverage, emit, emit_library, emit_with_main_type, emit_with_resources, incremental,
    incremental_with, survey, survey_with_resources,
};
pub use resources::Resource;
