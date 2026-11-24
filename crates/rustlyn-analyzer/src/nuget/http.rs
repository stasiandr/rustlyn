//! The boundary with the transport. Requests are built here and sent by the
//! caller, with whatever its platform has; the whole answer comes back —
//! status, headers, body — and what counts as a failure is decided here.
//!
//! A transport is called from worker threads and in parallel: NuGet feeds
//! are asked at the same time.

/// A request, as it is to be sent.
#[derive(Debug, Clone, PartialEq)]
pub struct Request {
    pub method: String,
    pub url: String,
    pub headers: Vec<(String, String)>,
    pub body: Option<Vec<u8>>,
    /// How long to wait for an answer, in seconds.
    pub timeout: f64,
}

impl Request {
    pub fn get(url: impl Into<String>, timeout: f64) -> Self {
        Self {
            method: "GET".into(),
            url: url.into(),
            headers: Vec::new(),
            body: None,
            timeout,
        }
    }

    #[must_use]
    pub fn header(mut self, name: &str, value: &str) -> Self {
        self.headers.push((name.to_string(), value.to_string()));
        self
    }

    /// A header's value, the name's case ignored.
    #[must_use]
    pub fn header_value(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(n, _)| n.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }
}

/// A server's answer, with whatever status. A `file://` address answers with
/// no HTTP status; the transport writes 200.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Response {
    pub status: i32,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

impl Response {
    /// A header's value, the name's case ignored.
    #[must_use]
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(n, _)| n.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }

    #[must_use]
    pub fn is_success(&self) -> bool {
        (200..300).contains(&self.status)
    }
}

/// Sends a request and waits for the answer. `Err` when there is no answer
/// at all — no connection, a timeout, a certificate — with text for a person.
pub trait Transport: Sync {
    fn send(&self, request: &Request) -> Result<Response, String>;
}

/// `user:password` as Basic authorization.
#[must_use]
pub fn basic_authorization(username: &str, password: &str) -> String {
    format!(
        "Basic {}",
        base64(format!("{username}:{password}").as_bytes())
    )
}

/// Standard base64 with padding.
#[must_use]
pub fn base64(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b = [
            chunk[0],
            chunk.get(1).copied().unwrap_or(0),
            chunk.get(2).copied().unwrap_or(0),
        ];
        let n = (u32::from(b[0]) << 16) | (u32::from(b[1]) << 8) | u32::from(b[2]);
        for k in 0..4 {
            if k <= chunk.len() {
                out.push(ALPHABET[((n >> (18 - 6 * k)) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_authorization_and_base64() {
        assert_eq!(
            basic_authorization("u.user", "secret"),
            "Basic dS51c2VyOnNlY3JldA=="
        );
        assert_eq!(basic_authorization("a", "b"), "Basic YTpi");
        assert_eq!(base64(b""), "");
        assert_eq!(base64(b"f"), "Zg==");
        assert_eq!(base64(b"fo"), "Zm8=");
        assert_eq!(base64(b"foo"), "Zm9v");
        assert_eq!(base64(b"foob"), "Zm9vYg==");
    }
}
