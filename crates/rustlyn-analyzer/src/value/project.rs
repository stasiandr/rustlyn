//! What the value graph needs of a project: its compiler, its symbols,
//! the unsaved texts of open files, a host's providers and the project
//! linked to it. The host brings them as data: the table of projects at
//! hand.

use std::collections::HashMap;
use std::sync::Arc;

use super::compiler::{Compiler, Inspector};
use super::edges::EdgeProvider;
use super::symbols::Symbols;

/// Where the graph writes what it did, for a host's log.
pub type Logger = Arc<dyn Fn(&str) + Send + Sync>;

/// A project as the graph sees it.
#[derive(Clone)]
pub struct Project {
    pub root: String,
    /// The linked project, by its root: values cross to it as messages
    /// (the other half of a client and a server).
    pub peer: Option<String>,
    /// The compiler; without it the graph does not expand in this project.
    pub compiler: Option<Arc<dyn Compiler>>,
    pub symbols: Option<Arc<dyn Symbols>>,
    /// The texts of open files with unsaved changes: the graph needs the
    /// text the compiler has.
    pub texts: HashMap<String, String>,
    /// Where to find the values of Unity inspector fields.
    pub inspector: Option<Arc<dyn Inspector>>,
    /// A host's edges.
    pub edges: Vec<Arc<dyn EdgeProvider>>,
    pub log: Option<Logger>,
}

impl std::fmt::Debug for Project {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Project")
            .field("root", &self.root)
            .field("peer", &self.peer)
            .field("compiler", &self.compiler.is_some())
            .field("symbols", &self.symbols.is_some())
            .field("edges", &self.edges.len())
            .finish_non_exhaustive()
    }
}

impl Project {
    #[must_use]
    pub fn new(root: impl Into<String>) -> Self {
        Self {
            root: root.into(),
            peer: None,
            compiler: None,
            symbols: None,
            texts: HashMap::new(),
            inspector: None,
            edges: Vec::new(),
            log: None,
        }
    }
}

/// The projects at hand: one's own (`home`) and those found by root — the
/// linked project, when it is open.
#[derive(Debug, Clone, Default)]
pub struct Projects {
    pub home: Option<String>,
    pub list: Vec<Project>,
}

impl Projects {
    /// A project by its root.
    #[must_use]
    pub fn lookup(&self, root: &str) -> Option<&Project> {
        self.list.iter().find(|p| p.root == root)
    }

    #[must_use]
    pub fn home(&self) -> Option<&Project> {
        self.home.as_deref().and_then(|h| self.lookup(h))
    }
}
