//! A NuGet package version: `1.2.3`, `1.2.3.4`, `2.0.0-beta.1+sha`. Compared
//! as NuGet compares: numbers in order (missing ones are zeros), a release
//! above any of its prereleases, labels part by part on the dots — numeric
//! ones as numbers and below alphanumeric ones. Everything after `+` is
//! ignored.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use super::text::trim_spaces;

/// A parsed version, with the text it was written as.
#[derive(Debug, Clone)]
pub struct NuGetVersion {
    pub numbers: Vec<i64>,
    pub prerelease: Vec<String>,
    /// As written: the text that goes to `dotnet add … --version`.
    pub text: String,
}

impl NuGetVersion {
    #[must_use]
    pub fn parse(string: &str) -> Option<NuGetVersion> {
        let text = trim_spaces(string);
        let core = text.split('+').next().unwrap_or("");
        let (release, prerelease) = match core.split_once('-') {
            Some((release, rest)) => (release, Some(rest)),
            None => (core, None),
        };
        if release.is_empty() {
            return None;
        }
        let numbers: Option<Vec<i64>> = release.split('.').map(|n| n.parse::<i64>().ok()).collect();
        let numbers = numbers?;
        if numbers.is_empty() || numbers.len() > 4 {
            return None;
        }
        let prerelease: Vec<String> = prerelease
            .map(|p| {
                p.split('.')
                    .filter(|s| !s.is_empty())
                    .map(str::to_owned)
                    .collect()
            })
            .unwrap_or_default();
        if core.contains('-') && prerelease.is_empty() {
            return None;
        }
        Some(NuGetVersion {
            numbers,
            prerelease,
            text: text.to_string(),
        })
    }

    pub fn is_prerelease(&self) -> bool {
        !self.prerelease.is_empty()
    }

    /// What to offer as an update to `current`: the newest stable version, or
    /// the newest of all when `current` is a prerelease. `None` when there is
    /// nothing newer.
    pub fn update<'a>(
        current: &NuGetVersion,
        versions: &'a [NuGetVersion],
    ) -> Option<&'a NuGetVersion> {
        // Of equal ones, the first.
        let newest = versions
            .iter()
            .filter(|v| current.is_prerelease() || !v.is_prerelease())
            .fold(None, |best: Option<&NuGetVersion>, v| {
                if best.is_none_or(|b| v > b) {
                    Some(v)
                } else {
                    best
                }
            })?;
        (newest > current).then_some(newest)
    }

    /// Descending, without repeats (a repeat is an equal version: `1.0` and
    /// `1.0.0`; the first stays).
    pub fn sorted_unique(versions: impl IntoIterator<Item = NuGetVersion>) -> Vec<NuGetVersion> {
        let mut out: Vec<NuGetVersion> = Vec::new();
        for version in versions {
            if !out.contains(&version) {
                out.push(version);
            }
        }
        out.sort_by(|a, b| b.cmp(a));
        out
    }
}

impl std::fmt::Display for NuGetVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.text)
    }
}

impl PartialEq for NuGetVersion {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for NuGetVersion {}

impl Hash for NuGetVersion {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut trimmed = self.numbers.as_slice();
        while trimmed.len() > 1 && trimmed.last() == Some(&0) {
            trimmed = &trimmed[..trimmed.len() - 1];
        }
        trimmed.hash(state);
        for label in &self.prerelease {
            label.to_lowercase().hash(state);
        }
    }
}

impl PartialOrd for NuGetVersion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NuGetVersion {
    fn cmp(&self, b: &Self) -> Ordering {
        let a = self;
        for i in 0..a.numbers.len().max(b.numbers.len()) {
            let x = a.numbers.get(i).copied().unwrap_or(0);
            let y = b.numbers.get(i).copied().unwrap_or(0);
            if x != y {
                return x.cmp(&y);
            }
        }
        if a.prerelease.is_empty() != b.prerelease.is_empty() {
            return if a.prerelease.is_empty() {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }
        for i in 0..a.prerelease.len().max(b.prerelease.len()) {
            let (Some(x), Some(y)) = (a.prerelease.get(i), b.prerelease.get(i)) else {
                return if i >= a.prerelease.len() {
                    Ordering::Less
                } else {
                    Ordering::Greater
                };
            };
            match (x.parse::<i64>().ok(), y.parse::<i64>().ok()) {
                (Some(m), Some(n)) => {
                    if m != n {
                        return m.cmp(&n);
                    }
                }
                (Some(_), None) => return Ordering::Less,
                (None, Some(_)) => return Ordering::Greater,
                (None, None) => {
                    let order = x.to_lowercase().cmp(&y.to_lowercase());
                    if order != Ordering::Equal {
                        return order;
                    }
                }
            }
        }
        Ordering::Equal
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn v(s: &str) -> NuGetVersion {
        NuGetVersion::parse(s).unwrap()
    }

    #[test]
    fn ordering() {
        assert!(
            v("1.2.10") > v("1.2.9") && v("1.2") == v("1.2.0.0") && v("2.0.0") > v("2.0.0-rc.1"),
            "numbers in order, missing ones zero, a release above an rc"
        );
        assert!(
            v("1.0.0-beta.10") > v("1.0.0-beta.2")
                && v("1.0.0-beta") > v("1.0.0-alpha.5")
                && v("1.0.0-alpha") < v("1.0.0-alpha.1")
                && v("1.0.0-1") < v("1.0.0-a"),
            "prerelease labels: numbers as numbers, shorter is lower, a number below a letter"
        );
        assert!(
            v("1.0.0+abc") == v("1.0.0") && HashSet::from([v("1.0"), v("1.0.0")]).len() == 1,
            "build metadata does not count"
        );
        assert!(
            NuGetVersion::parse("").is_none()
                && NuGetVersion::parse("1.x").is_none()
                && NuGetVersion::parse("$(Ver)").is_none()
                && NuGetVersion::parse("1.0-").is_none(),
            "not a version"
        );
        assert!(
            NuGetVersion::parse("1.2.3.4.5").is_none(),
            "more than four numbers is not a version"
        );
        assert_eq!(
            v(" 1.0-Beta ").text,
            "1.0-Beta",
            "the text as written, without surrounding spaces"
        );
    }

    #[test]
    fn updates() {
        let all = [v("13.0.1"), v("13.0.3"), v("14.0.0-beta1"), v("12.0.0")];
        assert_eq!(
            NuGetVersion::update(&v("13.0.1"), &all),
            Some(&v("13.0.3")),
            "the update is the newest stable"
        );
        assert_eq!(
            NuGetVersion::update(&v("14.0.0-alpha"), &all),
            Some(&v("14.0.0-beta1")),
            "for a prerelease, prereleases too"
        );
        assert_eq!(
            NuGetVersion::update(&v("13.0.3"), &all),
            None,
            "nothing newer"
        );
        let texts: Vec<String> = NuGetVersion::sorted_unique([v("1.0"), v("2.0"), v("1.0.0")])
            .into_iter()
            .map(|v| v.text)
            .collect();
        assert_eq!(texts, ["2.0", "1.0"]);
    }
}
