//! The version of C# a file is written in, as `/langversion:` names it.

use std::fmt;
use std::str::FromStr;

/// A version of the language. The compiler holds a program to the rules of
/// the version it is compiled as — where the rules changed between
/// versions (which overload a lambda picks, which extension methods an
/// `in` argument reaches) it follows the older ones for an older version,
/// the way Roslyn checks `LanguageVersion` in binding.
///
/// Ordered by release, so `version >= LanguageVersion::CSharp10` asks
/// whether C# 10 rules apply.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LanguageVersion {
    CSharp1,
    CSharp2,
    CSharp3,
    CSharp4,
    CSharp5,
    CSharp6,
    CSharp7,
    CSharp7_1,
    CSharp7_2,
    CSharp7_3,
    CSharp8,
    CSharp9,
    CSharp10,
    CSharp11,
    CSharp12,
    CSharp13,
    CSharp14,
    CSharp15,
    /// The features not yet released.
    Preview,
}

impl LanguageVersion {
    /// The newest released version: what `default`, `latest` and
    /// `latestmajor` mean, and what a file is compiled as unless told
    /// otherwise.
    pub const LATEST: Self = Self::CSharp15;

    /// Whether this version has the rules of `version` — the check Roslyn
    /// spells `languageVersion >= MessageID.IDS_FeatureX.RequiredVersion()`.
    #[must_use]
    pub fn at_least(self, version: Self) -> bool {
        self >= version
    }
}

impl Default for LanguageVersion {
    fn default() -> Self {
        Self::LATEST
    }
}

/// The error of a `/langversion:` value no version answers to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnknownLanguageVersion(pub String);

impl fmt::Display for UnknownLanguageVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid language version '{}'", self.0)
    }
}

impl std::error::Error for UnknownLanguageVersion {}

impl FromStr for LanguageVersion {
    type Err = UnknownLanguageVersion;

    /// Reads a version the way the command line spells it: `7.3`, `10`,
    /// `10.0`, `ISO-2`, `latest`, `preview`, ...
    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let lowered = text.trim().to_ascii_lowercase();
        let version = match lowered.as_str() {
            "default" | "latest" | "latestmajor" => Self::LATEST,
            "preview" => Self::Preview,
            "1" | "1.0" | "iso-1" => Self::CSharp1,
            "2" | "2.0" | "iso-2" => Self::CSharp2,
            "3" | "3.0" => Self::CSharp3,
            "4" | "4.0" => Self::CSharp4,
            "5" | "5.0" => Self::CSharp5,
            "6" | "6.0" => Self::CSharp6,
            "7" | "7.0" => Self::CSharp7,
            "7.1" => Self::CSharp7_1,
            "7.2" => Self::CSharp7_2,
            "7.3" => Self::CSharp7_3,
            "8" | "8.0" => Self::CSharp8,
            "9" | "9.0" => Self::CSharp9,
            "10" | "10.0" => Self::CSharp10,
            "11" | "11.0" => Self::CSharp11,
            "12" | "12.0" => Self::CSharp12,
            "13" | "13.0" => Self::CSharp13,
            "14" | "14.0" => Self::CSharp14,
            "15" | "15.0" => Self::CSharp15,
            _ => return Err(UnknownLanguageVersion(text.to_string())),
        };
        Ok(version)
    }
}

impl fmt::Display for LanguageVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::CSharp1 => "1",
            Self::CSharp2 => "2",
            Self::CSharp3 => "3",
            Self::CSharp4 => "4",
            Self::CSharp5 => "5",
            Self::CSharp6 => "6",
            Self::CSharp7 => "7.0",
            Self::CSharp7_1 => "7.1",
            Self::CSharp7_2 => "7.2",
            Self::CSharp7_3 => "7.3",
            Self::CSharp8 => "8.0",
            Self::CSharp9 => "9.0",
            Self::CSharp10 => "10.0",
            Self::CSharp11 => "11.0",
            Self::CSharp12 => "12.0",
            Self::CSharp13 => "13.0",
            Self::CSharp14 => "14.0",
            Self::CSharp15 => "15.0",
            Self::Preview => "preview",
        };
        f.write_str(text)
    }
}

#[cfg(test)]
mod tests {
    use super::LanguageVersion;

    #[test]
    fn versions_read_the_way_the_command_line_spells_them() {
        assert_eq!("7.3".parse(), Ok(LanguageVersion::CSharp7_3));
        assert_eq!("10".parse(), Ok(LanguageVersion::CSharp10));
        assert_eq!("10.0".parse(), Ok(LanguageVersion::CSharp10));
        assert_eq!("Preview".parse(), Ok(LanguageVersion::Preview));
        assert_eq!("latest".parse(), Ok(LanguageVersion::LATEST));
        assert!("10.5".parse::<LanguageVersion>().is_err());
    }

    #[test]
    fn versions_are_ordered_by_release() {
        assert!(LanguageVersion::CSharp9 < LanguageVersion::CSharp10);
        assert!(LanguageVersion::CSharp7_3 < LanguageVersion::CSharp8);
        assert!(LanguageVersion::Preview.at_least(LanguageVersion::LATEST));
        assert!(!LanguageVersion::CSharp9.at_least(LanguageVersion::CSharp10));
    }
}
