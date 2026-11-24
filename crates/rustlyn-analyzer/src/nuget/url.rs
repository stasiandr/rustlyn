//! Addresses: just what talking to a feed needs — the host, the path,
//! encoding a path segment and query parameters.

use std::fmt::Write as _;

/// The characters a path segment or a parameter leaves unencoded (RFC 3986
/// unreserved). A slash is encoded.
#[must_use]
pub fn is_unreserved(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'.' | b'_' | b'~')
}

/// Everything but the unreserved as `%XX` UTF-8 bytes: `group/app` →
/// `group%2Fapp`.
#[must_use]
pub fn encode_component(text: &str) -> String {
    encode_keeping(text, |c| c.is_ascii() && is_unreserved(c as u8))
}

/// Encodes everything `keep` does not keep, as UTF-8 bytes.
#[must_use]
pub fn encode_keeping(text: &str, keep: impl Fn(char) -> bool) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if keep(c) {
            out.push(c);
        } else {
            let mut buffer = [0u8; 4];
            for byte in c.encode_utf8(&mut buffer).bytes() {
                let _ = write!(out, "%{byte:02X}");
            }
        }
    }
    out
}

/// `%XX` back to bytes; anything broken as it is.
#[must_use]
pub fn decode_percent(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%'
            && i + 2 < bytes.len()
            && let (Some(h), Some(l)) = (hex(bytes[i + 1]), hex(bytes[i + 2]))
        {
            out.push(h * 16 + l);
            i += 3;
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8(out).unwrap_or_else(|_| text.to_string())
}

fn hex(byte: u8) -> Option<u8> {
    (byte as char).to_digit(16).map(|d| d as u8)
}

/// `address?k=v&…`, appending to any parameters already there.
#[must_use]
pub fn with_query(base: &str, items: &[(&str, &str)]) -> String {
    if items.is_empty() {
        return base.to_string();
    }
    let mut out = base.to_string();
    let joiner = if base.contains('?') {
        if base.ends_with('?') || base.ends_with('&') {
            ""
        } else {
            "&"
        }
    } else {
        "?"
    };
    out.push_str(joiner);
    for (i, (name, value)) in items.iter().enumerate() {
        if i > 0 {
            out.push('&');
        }
        out.push_str(&encode_component(name));
        out.push('=');
        out.push_str(&encode_component(value));
    }
    out
}

/// The parts of `scheme://[user[:password]@]host[:port]/path?query#fragment`.
/// An address taken apart.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parts {
    pub scheme: String,
    /// As in the address; case kept.
    pub host: String,
    /// Percent-decoded.
    pub path: String,
}

/// An address with a scheme. Spaces and other characters an address may not
/// hold make it `None`.
#[must_use]
pub fn parse(text: &str) -> Option<Parts> {
    if text.chars().any(|c| {
        c.is_whitespace()
            || c.is_control()
            || matches!(c, '<' | '>' | '"' | '{' | '}' | '|' | '\\' | '^' | '`')
    }) {
        return None;
    }
    let (scheme, rest) = text.split_once("://")?;
    if scheme.is_empty()
        || !scheme
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '+' | '-' | '.'))
    {
        return None;
    }
    let end = rest.find(['/', '?', '#']).unwrap_or(rest.len());
    let authority = &rest[..end];
    let tail = &rest[end..];
    let host_port = authority.rsplit_once('@').map_or(authority, |(_, h)| h);
    let host = if let Some(inner) = host_port.strip_prefix('[') {
        inner.split(']').next().unwrap_or("").to_string()
    } else {
        host_port.split(':').next().unwrap_or("").to_string()
    };
    let path_end = tail.find(['?', '#']).unwrap_or(tail.len());
    Some(Parts {
        scheme: scheme.to_string(),
        host,
        path: decode_percent(&tail[..path_end]),
    })
}

/// An address's host; an address with no scheme has none.
#[must_use]
pub fn host(text: &str) -> Option<String> {
    parse(text).map(|p| p.host).filter(|h| !h.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parts_and_encoding() {
        assert_eq!(encode_component("group/sub app"), "group%2Fsub%20app");
        let p = parse("ssh://git@gitlab.example.com:2222/group/sub/app.git").unwrap();
        assert_eq!(
            (p.host.as_str(), p.path.as_str()),
            ("gitlab.example.com", "/group/sub/app.git")
        );
        assert_eq!(
            host("https://oauth2:secret@GitLab.com/x"),
            Some("GitLab.com".into())
        );
        assert_eq!(host("api.nuget.org/v3"), None);
        assert_eq!(
            with_query("https://h/q?x=1", &[("q", "a b"), ("take", "1")]),
            "https://h/q?x=1&q=a%20b&take=1"
        );
        assert_eq!(decode_percent("a%2Fb%"), "a/b%");
    }
}
