//! What to look for: the APIs a change is asked about, the code that is the
//! project's own, the builds to read it as, and how far to follow.
//!
//! The engine knows nothing of any particular API. A caller names the sinks
//! — by namespace, type, folder or assembly — in a JSON file:
//!
//! ```json
//! {
//!   "name": "payments",
//!   "own": ["Assets/Game"],
//!   "configurations": [
//!     { "name": "android", "symbols": ["UNITY_ANDROID", "-UNITY_EDITOR"] }
//!   ],
//!   "sinks": [
//!     { "name": "Billing", "namespaces": ["Vendor.Billing"], "paths": ["Assets/Vendor/Billing"] }
//!   ],
//!   "watch": [
//!     { "name": "Billing package", "paths": ["Packages/manifest.json", "Assets/Vendor/Billing/**"] }
//!   ],
//!   "ignore": ["Game.Logging"],
//!   "limits": { "depth": 10, "data_hops": 2, "hub_callers": 10, "hub_writers": 10, "shared_readers": 3 }
//! }
//! ```

use rustlyn_ide::formats::json::Json;

/// A group of APIs under one name: an SDK, a subsystem.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Sink {
    pub name: String,
    /// Namespaces whose types and members are the sink, nested ones too.
    pub namespaces: Vec<String>,
    /// Type names, qualified or not.
    pub types: Vec<String>,
    /// Folders (relative to the root) whose source is the sink.
    pub paths: Vec<String>,
    /// Assemblies by file name, without the extension.
    pub assemblies: Vec<String>,
}

/// A build to read the project as.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Configuration {
    pub name: String,
    /// `NAME` defines, `-NAME` undefines, over the project's own symbols.
    pub symbols: Vec<String>,
}

/// Files that are not code and concern the sinks all the same: a package
/// manifest, a vendor folder, a settings asset.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Watch {
    pub name: String,
    /// Globs relative to the root: `*` within a folder, `**` across folders.
    pub paths: Vec<String>,
}

/// How far the walk goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Steps from a sink.
    pub depth: usize,
    /// Of those steps, how many may go through data: a field one member
    /// writes and another reads, an ECS component.
    pub data_hops: usize,
    /// A member with more callers than this is an API of the project's own:
    /// its callers are followed no further, and only their calling
    /// statements count.
    pub hub_callers: usize,
    /// The same for the writers of a field or a component.
    pub hub_writers: usize,
    /// A field or a component read by more members outside the cone than
    /// this is shared state, not the cone's own: who writes it is not
    /// followed.
    pub shared_readers: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            depth: 10,
            data_hops: 2,
            hub_callers: 10,
            hub_writers: 10,
            shared_readers: 3,
        }
    }
}

/// One question about a project: does a change lead to these sinks.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Config {
    pub name: String,
    /// Folders of the project's own code, relative to the root. Empty:
    /// every source file outside the sinks' folders.
    pub own: Vec<String>,
    /// Empty: the project as it compiles.
    pub configurations: Vec<Configuration>,
    pub sinks: Vec<Sink>,
    pub watch: Vec<Watch>,
    /// Qualified name prefixes of types and members the walk does not go
    /// through: a logger that happens to forward to a sink.
    pub ignore: Vec<String>,
    pub limits: Limits,
}

impl Config {
    /// Reads a configuration from JSON.
    ///
    /// # Errors
    ///
    /// When the text is not JSON, or names no sinks.
    pub fn parse(text: &str) -> Result<Self, String> {
        let json = Json::parse(text.as_bytes()).ok_or("not valid JSON")?;
        let strings = |from: &Json, key: &str| from.strings(key).unwrap_or_default();
        let folders = |from: &Json, key: &str| -> Vec<String> {
            strings(from, key)
                .into_iter()
                .map(|path| path.trim_matches('/').to_owned())
                .collect()
        };
        let sinks: Vec<Sink> = json
            .objects_in("sinks")
            .into_iter()
            .map(|sink| Sink {
                name: sink.str("name").unwrap_or_default().to_owned(),
                namespaces: strings(sink, "namespaces"),
                types: strings(sink, "types"),
                paths: folders(sink, "paths"),
                assemblies: strings(sink, "assemblies"),
            })
            .collect();
        if sinks.is_empty() {
            return Err("no sinks: name at least one under \"sinks\"".to_owned());
        }
        if let Some(sink) = sinks.iter().find(|sink| sink.name.is_empty()) {
            return Err(format!("a sink without a name: {sink:?}"));
        }
        let mut limits = Limits::default();
        if let Some(given) = json.object("limits") {
            let number = |key: &str, default: usize| {
                given
                    .int(key)
                    .and_then(|value| usize::try_from(value).ok())
                    .unwrap_or(default)
            };
            limits = Limits {
                depth: number("depth", limits.depth),
                data_hops: number("data_hops", limits.data_hops),
                hub_callers: number("hub_callers", limits.hub_callers),
                hub_writers: number("hub_writers", limits.hub_writers),
                shared_readers: number("shared_readers", limits.shared_readers),
            };
        }
        Ok(Self {
            name: json.str("name").unwrap_or("reach").to_owned(),
            own: folders(&json, "own"),
            configurations: json
                .objects_in("configurations")
                .into_iter()
                .map(|configuration| Configuration {
                    name: configuration.str("name").unwrap_or_default().to_owned(),
                    symbols: strings(configuration, "symbols"),
                })
                .collect(),
            sinks,
            watch: json
                .objects_in("watch")
                .into_iter()
                .map(|watch| Watch {
                    name: watch.str("name").unwrap_or_default().to_owned(),
                    paths: strings(watch, "paths"),
                })
                .collect(),
            ignore: strings(&json, "ignore"),
            limits,
        })
    }

    /// Whether `path` (relative to the root) is the project's own code.
    #[must_use]
    pub fn is_own(&self, path: &str) -> bool {
        if self.sink_of_path(path).is_some() {
            return false;
        }
        self.own.is_empty() || self.own.iter().any(|folder| under(path, folder))
    }

    /// The sink whose folder holds `path`.
    #[must_use]
    pub fn sink_of_path(&self, path: &str) -> Option<usize> {
        self.sinks
            .iter()
            .position(|sink| sink.paths.iter().any(|folder| under(path, folder)))
    }

    /// The sink a symbol belongs to, by where it is declared and what it is
    /// in. `container` is the qualified name of the type or namespace it is
    /// in; `is_type` says the symbol is itself a type.
    #[must_use]
    pub fn sink_of_symbol(&self, name: &str, container: &str, is_type: bool) -> Option<usize> {
        let qualified = if container.is_empty() {
            name.to_owned()
        } else {
            format!("{container}.{name}")
        };
        self.sinks.iter().position(|sink| {
            sink.namespaces
                .iter()
                .any(|namespace| container == namespace || inside(container, namespace))
                || sink.types.iter().any(|ty| {
                    let named = |candidate: &str| {
                        candidate == ty
                            || candidate
                                .strip_suffix(ty.as_str())
                                .is_some_and(|rest| rest.ends_with('.'))
                            || inside(candidate, ty)
                    };
                    named(container) || (is_type && named(&qualified))
                })
        })
    }

    /// The sink an assembly is, by its file name without the extension.
    #[must_use]
    pub fn sink_of_assembly(&self, stem: &str) -> Option<usize> {
        self.sinks.iter().position(|sink| {
            sink.assemblies
                .iter()
                .any(|assembly| assembly.eq_ignore_ascii_case(stem))
        })
    }

    /// Whether the walk leaves a qualified name alone.
    #[must_use]
    pub fn ignored(&self, qualified: &str) -> bool {
        self.ignore
            .iter()
            .any(|prefix| qualified == prefix || inside(qualified, prefix))
    }

    /// The watch entries whose globs match `path`.
    #[must_use]
    pub fn watched(&self, path: &str) -> Vec<&Watch> {
        self.watch
            .iter()
            .filter(|watch| watch.paths.iter().any(|glob| glob_matches(glob, path)))
            .collect()
    }
}

/// `name` is `outer` followed by `.` and more.
fn inside(name: &str, outer: &str) -> bool {
    name.strip_prefix(outer)
        .is_some_and(|rest| rest.starts_with('.'))
}

/// `path` is `folder` or in it.
fn under(path: &str, folder: &str) -> bool {
    folder.is_empty()
        || path
            .strip_prefix(folder)
            .is_some_and(|rest| rest.is_empty() || rest.starts_with('/'))
}

/// A glob over a `/`-separated path: `*` matches within a folder, `**`
/// across folders, `?` one character. A pattern with no wildcard also
/// matches everything under it, as a folder.
#[must_use]
pub fn glob_matches(glob: &str, path: &str) -> bool {
    fn matches(glob: &[u8], path: &[u8]) -> bool {
        match glob.split_first() {
            None => path.is_empty(),
            Some((b'*', rest)) if rest.first() == Some(&b'*') => {
                let rest = &rest[1..];
                let rest = rest.strip_prefix(b"/").unwrap_or(rest);
                (0..=path.len()).any(|at| matches(rest, &path[at..]))
            }
            Some((b'*', rest)) => (0..=path.len())
                .take_while(|&at| at == 0 || path[at - 1] != b'/')
                .any(|at| matches(rest, &path[at..])),
            Some((b'?', rest)) => path
                .split_first()
                .is_some_and(|(first, tail)| *first != b'/' && matches(rest, tail)),
            Some((first, rest)) => path
                .split_first()
                .is_some_and(|(head, tail)| head == first && matches(rest, tail)),
        }
    }
    let glob = glob.trim_matches('/');
    if !glob.contains(['*', '?']) {
        return under(path, glob);
    }
    matches(glob.as_bytes(), path.as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn globs() {
        assert!(glob_matches(
            "Packages/manifest.json",
            "Packages/manifest.json"
        ));
        assert!(glob_matches(
            "Assets/Vendor",
            "Assets/Vendor/Billing/Api.cs"
        ));
        assert!(!glob_matches("Assets/Vendor", "Assets/VendorTools/Api.cs"));
        assert!(glob_matches(
            "Assets/**/*.asset",
            "Assets/Data/Shop/Prices.asset"
        ));
        assert!(glob_matches("Assets/**/*.asset", "Assets/Prices.asset"));
        assert!(!glob_matches("Assets/*.asset", "Assets/Data/Prices.asset"));
        assert!(glob_matches(
            "**/google-services.json",
            "Assets/google-services.json"
        ));
        assert!(glob_matches(
            "Assets/Plugins/Android/**",
            "Assets/Plugins/Android/a/b.xml"
        ));
    }

    #[test]
    fn symbols_of_a_sink() {
        let config = Config::parse(
            r#"{"sinks": [{"name": "Billing", "namespaces": ["Vendor.Billing"], "types": ["Tracker"]}]}"#,
        )
        .unwrap();
        // A member of a type in the namespace, the type itself, a nested
        // namespace.
        assert_eq!(
            config.sink_of_symbol("Pay", "Vendor.Billing.Store", false),
            Some(0)
        );
        assert_eq!(
            config.sink_of_symbol("Store", "Vendor.Billing", true),
            Some(0)
        );
        assert_eq!(
            config.sink_of_symbol("Log", "Vendor.Billing.Internal.Trace", false),
            Some(0)
        );
        assert_eq!(
            config.sink_of_symbol("Pay", "Vendor.BillingTools.Store", false),
            None
        );
        // A type by its bare name, wherever it is, and its members.
        assert_eq!(
            config.sink_of_symbol("Tracker", "Other.Place", true),
            Some(0)
        );
        assert_eq!(
            config.sink_of_symbol("Start", "Other.Place.Tracker", false),
            Some(0)
        );
        assert_eq!(
            config.sink_of_symbol("Start", "Other.Place.MyTracker", false),
            None
        );
    }

    #[test]
    fn own_code_is_outside_the_sinks() {
        let config = Config::parse(
            r#"{"own": ["Assets"], "sinks": [{"name": "Billing", "paths": ["Assets/Vendor/Billing/"]}]}"#,
        )
        .unwrap();
        assert!(config.is_own("Assets/Game/Shop.cs"));
        assert!(!config.is_own("Assets/Vendor/Billing/Api.cs"));
        assert!(!config.is_own("Packages/x/Y.cs"));
        assert_eq!(config.sink_of_path("Assets/Vendor/Billing/Api.cs"), Some(0));
    }

    #[test]
    fn a_configuration_needs_sinks() {
        assert!(Config::parse("{}").is_err());
        assert!(Config::parse("not json").is_err());
    }
}
