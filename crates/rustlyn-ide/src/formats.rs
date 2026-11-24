//! File formats the projects an editor opens are full of, read and written
//! with no dependencies: [`json`] for `project.assets.json`, `.asmdef` and
//! service answers, [`xml`] for MSBuild files and `NuGet.Config`.

pub mod json;
pub mod xml;
