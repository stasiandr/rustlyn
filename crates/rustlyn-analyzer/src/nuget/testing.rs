//! A transport for tests, answering by address with no network.

use std::sync::Mutex;

use super::http::{Request, Response, Transport};

/// Answers by the first rule whose address matches (a trailing `*` matches
/// a prefix) and remembers the requests. No rule: no connection.
#[derive(Debug, Default)]
pub(crate) struct FakeTransport {
    rules: Vec<(String, Result<Response, String>)>,
    pub(crate) seen: Mutex<Vec<Request>>,
}

impl FakeTransport {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn reply(mut self, url: &str, status: i32, body: &str) -> Self {
        self.rules.push((
            url.into(),
            Ok(Response {
                status,
                headers: Vec::new(),
                body: body.as_bytes().to_vec(),
            }),
        ));
        self
    }

    pub(crate) fn fail(mut self, url: &str, message: &str) -> Self {
        self.rules.push((url.into(), Err(message.into())));
        self
    }

    pub(crate) fn urls(&self) -> Vec<String> {
        self.seen
            .lock()
            .unwrap()
            .iter()
            .map(|r| r.url.clone())
            .collect()
    }
}

impl Transport for FakeTransport {
    fn send(&self, request: &Request) -> Result<Response, String> {
        self.seen.lock().unwrap().push(request.clone());
        for (url, answer) in &self.rules {
            if request.url == *url
                || (url.ends_with('*') && request.url.starts_with(&url[..url.len() - 1]))
            {
                return answer.clone();
            }
        }
        Err(format!("no answer for {}", request.url))
    }
}

/// A test's temporary folder, removed with the value.
#[derive(Debug)]
pub(crate) struct TempDir {
    path: std::path::PathBuf,
}

impl TempDir {
    pub(crate) fn new(label: &str) -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "rustlyn-analyzer-nuget-{label}-{}-{n}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        Self { path }
    }

    pub(crate) fn path(&self) -> &std::path::Path {
        &self.path
    }

    pub(crate) fn put(&self, relative: &str, text: &str) {
        let file = self.path.join(relative);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, text).unwrap();
    }

    pub(crate) fn mkdir(&self, relative: &str) {
        std::fs::create_dir_all(self.path.join(relative)).unwrap();
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}
