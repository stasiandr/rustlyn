//! NuGet: package versions, `NuGet.Config`, the packages .NET projects
//! reference, whether a restore found them, and v3 feeds.
//!
//! Nothing here touches the network. [`client`] builds requests, pages
//! through answers and decides what counts as a failure; the request itself
//! goes to an [`http::Transport`] the caller supplies — whatever its platform
//! has for HTTP and TLS.

pub mod client;
pub mod config;
pub mod http;
pub mod projects;
pub mod restore;
pub mod url;
pub mod version;

mod text;

#[cfg(test)]
mod testing;

pub use client::{Feed, FeedFailure, NuGetClient, Package};
pub use config::Source;
pub use projects::{Project, Reference};
pub use restore::{Assets, Problem, Reason, Report};
pub use version::NuGetVersion;
