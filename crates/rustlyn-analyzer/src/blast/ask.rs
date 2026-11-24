//! Questions to the compiler: on a deep stack, and a panic inside it is an
//! answer that is not there rather than the end of the report.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;

use rustlyn_ide::Refusal;

use crate::deep;

/// Asks on a deep-stack thread; a refusal and a panic are both `None`.
pub(crate) fn ask<T: Send>(body: impl FnOnce() -> Result<T, Refusal> + Send) -> Option<T> {
    catch_unwind(AssertUnwindSafe(|| deep::run(body)))
        .ok()
        .and_then(Result::ok)
}

/// A path as the compiler gives it, made absolute: a project file's path is
/// relative to the session's root, an assembly's is absolute already.
pub(crate) fn absolute(root: &str, path: &Path) -> String {
    if path.is_absolute() || path.to_string_lossy().starts_with('/') {
        return path.to_string_lossy().into_owned();
    }
    Path::new(root).join(path).to_string_lossy().into_owned()
}
