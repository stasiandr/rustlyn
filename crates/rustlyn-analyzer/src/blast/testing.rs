//! For tests: a project in a temporary folder, compiled by Rustlyn, and the
//! diff of two texts of one file.

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustlyn_ide::Session;

#[derive(Debug)]
pub(crate) struct Project(PathBuf);

impl Project {
    pub(crate) fn new(name: &str, files: &[(&str, &str)]) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "rustlyn-blast-{name}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("folder");
        // The root without links (`/var` → `/private/var`), as the session
        // sees it.
        let project = Self(path.canonicalize().expect("path"));
        for (name, text) in files {
            project.write(name, text);
        }
        project
    }

    pub(crate) fn root(&self) -> String {
        self.0.to_string_lossy().into_owned()
    }

    pub(crate) fn write(&self, name: &str, text: &str) {
        let path = self.0.join(name);
        std::fs::create_dir_all(path.parent().expect("folder")).expect("folder");
        std::fs::write(path, text).expect("file");
    }

    /// A compiled session over what is on disk now.
    pub(crate) fn session(&self) -> Session {
        crate::blast::project::compiled(&self.root(), None).expect("compiled")
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A diff in one hunk over the whole file: lines missing from the other
/// text are removed or added.
pub(crate) fn patch(path: &str, old: &str, new: &str) -> String {
    let o: Vec<&str> = old.lines().collect();
    let n: Vec<&str> = new.lines().collect();
    let mut text = format!(
        "--- a/{path}\n+++ b/{path}\n@@ -1,{} +1,{} @@\n",
        o.len(),
        n.len()
    );
    let (mut i, mut j) = (0, 0);
    while i < o.len() || j < n.len() {
        if i < o.len() && j < n.len() && o[i] == n[j] {
            text += &format!(" {}\n", o[i]);
            i += 1;
            j += 1;
        } else if i < o.len() && !n[j..].contains(&o[i]) {
            text += &format!("-{}\n", o[i]);
            i += 1;
        } else {
            text += &format!("+{}\n", n[j]);
            j += 1;
        }
    }
    text
}
