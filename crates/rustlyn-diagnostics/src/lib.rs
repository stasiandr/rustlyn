//! Diagnostics shared by every stage of the compiler.
//!
//! Messages carry the same `CSxxxx` identifiers the Microsoft C# compiler uses,
//! so a Rustlyn diagnostic can be compared against `csc` output directly.

mod code;
mod diagnostic;

pub use code::{ErrorCode, Severity};
pub use diagnostic::{Diagnostic, DiagnosticBag, DiagnosticDisplay};
