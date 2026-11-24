//! A project's feeds over the v3 protocol: search and version lists across
//! all enabled feeds at once. Each client keeps the service indexes it has
//! read; projects can have their own `nuget.config`, so a tool showing
//! several keeps a client per project.

use std::sync::{Arc, Mutex};

use rustlyn_ide::formats::json::Json;

use super::config::Source;
use super::http::{Request, Transport, basic_authorization};
use super::text::{equal_ignoring_case, trim_blank};
use super::url;
use super::version::NuGetVersion;

/// A package found in the feeds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    pub id: String,
    pub version: String,
    pub description: String,
    pub authors: String,
    pub total_downloads: i64,
    pub verified: bool,
    pub project_url: Option<String>,
    pub icon_url: Option<String>,
    /// Every published version, newest first.
    pub versions: Vec<NuGetVersion>,
    /// The name of the feed it was found in.
    pub source: String,
    pub is_from_nuget_org: bool,
}

/// Why a feed did not answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeedFailure {
    /// 401 or 403: a user name and token are needed.
    Unauthorized(String),
    Status(String, i32),
    /// The feed's index has no search service.
    NoSearch(String),
    /// No answer at all; the text is the transport's.
    Network(String),
    /// An answer that is not JSON where JSON is needed.
    Unreadable(String),
}

impl FeedFailure {
    /// The name of the feed that failed.
    #[must_use]
    pub fn feed(&self) -> &str {
        match self {
            Self::Unauthorized(feed)
            | Self::Status(feed, _)
            | Self::NoSearch(feed)
            | Self::Unreadable(feed) => feed,
            Self::Network(_) => "",
        }
    }
}

impl std::fmt::Display for FeedFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unauthorized(feed) => write!(f, "{feed}: a user name and token are needed"),
            Self::Status(feed, status) => write!(f, "{feed}: the server answered {status}"),
            Self::NoSearch(feed) => write!(f, "{feed}: the feed has no search service"),
            Self::Network(message) => write!(f, "no answer: {message}"),
            Self::Unreadable(feed) => write!(f, "{feed}: the answer is not JSON"),
        }
    }
}

/// The service index of nuget.org.
pub const NUGET_ORG_INDEX: &str = "https://api.nuget.org/v3/index.json";
const FALLBACK_SEARCH: &str = "https://azuresearch-usnc.nuget.org/query";
const FALLBACK_PACKAGES: &str = "https://api.nuget.org/v3-flatcontainer/";
/// The `User-Agent` requests carry unless told otherwise.
pub const USER_AGENT: &str = "rustlyn";
/// How long to wait for a feed, in seconds.
const TIMEOUT: f64 = 20.0;

/// nuget.org as a source.
#[must_use]
pub fn nuget_org() -> Source {
    Source::new("nuget.org", NUGET_ORG_INDEX)
}

#[derive(Debug, Default)]
struct Services {
    search: Option<String>,
    packages: Option<String>,
    /// The index was read: services missing from it will stay missing.
    resolved: bool,
}

/// One v3 feed. Service addresses come from its `index.json`, as NuGet itself
/// takes them; for nuget.org there are known ones in case the index does not
/// answer. Credentials go as Basic authorization, as `dotnet` sends them.
#[derive(Debug)]
pub struct Feed {
    pub source: Source,
    /// The `User-Agent` of every request.
    pub user_agent: String,
    services: Mutex<Services>,
}

impl Feed {
    #[must_use]
    pub fn new(source: Source) -> Self {
        Feed {
            source,
            user_agent: USER_AGENT.to_string(),
            services: Mutex::new(Services::default()),
        }
    }

    /// The same feed introducing itself as `user_agent`.
    #[must_use]
    pub fn with_user_agent(mut self, user_agent: &str) -> Self {
        self.user_agent = user_agent.to_string();
        self
    }

    /// `take` results; `prerelease` includes prerelease versions.
    pub fn search(
        &self,
        t: &dyn Transport,
        query: &str,
        prerelease: bool,
        skip: usize,
        take: usize,
    ) -> Result<Vec<Package>, FeedFailure> {
        let Some(base) = self.services(t, false)?.0 else {
            return Err(FeedFailure::NoSearch(self.source.name.clone()));
        };
        let (skip, take) = (skip.to_string(), take.to_string());
        let address = url::with_query(
            &base,
            &[
                ("q", query),
                ("skip", &skip),
                ("take", &take),
                ("prerelease", if prerelease { "true" } else { "false" }),
                ("semVerLevel", "2.0.0"),
            ],
        );
        let data = self.fetch(t, &address)?;
        Ok(parse_search(&data, &self.source))
    }

    /// Exactly this package. nuget.org understands `packageid:`; other feeds
    /// search the text, and the result with the same name is taken.
    pub fn package(&self, t: &dyn Transport, id: &str) -> Result<Option<Package>, FeedFailure> {
        let exact = |list: Vec<Package>| list.into_iter().find(|p| equal_ignoring_case(&p.id, id));
        if let Some(found) = exact(self.search(t, &format!("packageid:{id}"), true, 0, 1)?) {
            return Ok(Some(found));
        }
        if self.source.is_nuget_org() {
            return Ok(None);
        }
        Ok(exact(self.search(t, id, true, 0, 20)?))
    }

    /// Every version of the package in the feed; empty when there is none.
    pub fn versions(&self, t: &dyn Transport, id: &str) -> Result<Vec<NuGetVersion>, FeedFailure> {
        let Some(base) = self.services(t, false)?.1 else {
            return Ok(Vec::new());
        };
        let address = format!(
            "{base}{}/index.json",
            url::encode_component(&id.to_lowercase())
        );
        let data = match self.fetch(t, &address) {
            Err(FeedFailure::Status(_, 404)) => return Ok(Vec::new()),
            other => other?,
        };
        let json =
            Json::parse(&data).ok_or_else(|| FeedFailure::Unreadable(self.source.name.clone()))?;
        let Some(list) = json.strings("versions") else {
            return Ok(Vec::new());
        };
        let mut versions: Vec<NuGetVersion> =
            list.iter().filter_map(|v| NuGetVersion::parse(v)).collect();
        versions.sort_by(|a, b| b.cmp(a));
        Ok(versions)
    }

    /// Whether the feed answers with these credentials. The index is not
    /// enough — some servers hand it out without a login and then refuse the
    /// search — so the search is asked.
    pub fn check(&self, t: &dyn Transport) -> Result<(), FeedFailure> {
        self.services.lock().unwrap().resolved = false;
        let (search, packages) = self.services(t, true)?;
        if search.is_some() {
            self.search(t, "", false, 0, 1)?;
        } else if packages.is_some() {
            self.versions(t, "rustlyn.source.check")?;
        }
        Ok(())
    }

    fn fetch(&self, t: &dyn Transport, address: &str) -> Result<Vec<u8>, FeedFailure> {
        let mut request = Request::get(address, TIMEOUT).header("User-Agent", &self.user_agent);
        if self.source.has_credentials()
            && let (Some(username), Some(password)) = (&self.source.username, &self.source.password)
        {
            request = request.header("Authorization", &basic_authorization(username, password));
        }
        let response = t.send(&request).map_err(FeedFailure::Network)?;
        if !response.is_success() {
            if response.status == 401 || response.status == 403 {
                return Err(FeedFailure::Unauthorized(self.source.name.clone()));
            }
            return Err(FeedFailure::Status(
                self.source.name.clone(),
                response.status,
            ));
        }
        Ok(response.body)
    }

    /// The search and package addresses. The index is read once; while it is
    /// being read another request may read it too.
    fn services(
        &self,
        t: &dyn Transport,
        strict: bool,
    ) -> Result<(Option<String>, Option<String>), FeedFailure> {
        let resolved = self.services.lock().unwrap().resolved;
        if !resolved {
            match self.fetch(t, &self.source.url) {
                Ok(data) => {
                    let (search, packages) = parse_service_index(&data);
                    let mut services = self.services.lock().unwrap();
                    services.search = search;
                    services.packages = packages;
                    services.resolved = true;
                }
                // Without its index nuget.org still answers at the known
                // addresses; another feed does not, and its error is better
                // shown.
                Err(error) => {
                    if strict || !self.source.is_nuget_org() {
                        return Err(error);
                    }
                }
            }
        }
        let services = self.services.lock().unwrap();
        if self.source.is_nuget_org() {
            return Ok((
                Some(
                    services
                        .search
                        .clone()
                        .unwrap_or_else(|| FALLBACK_SEARCH.into()),
                ),
                Some(
                    services
                        .packages
                        .clone()
                        .unwrap_or_else(|| FALLBACK_PACKAGES.into()),
                ),
            ));
        }
        Ok((services.search.clone(), services.packages.clone()))
    }
}

/// All the feeds of a project. Kept between calls: service indexes once read
/// are not asked for again.
#[derive(Debug)]
pub struct NuGetClient {
    feeds: Mutex<Vec<Arc<Feed>>>,
    user_agent: String,
}

impl Default for NuGetClient {
    fn default() -> Self {
        Self::with_user_agent(USER_AGENT)
    }
}

impl NuGetClient {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// A client whose requests introduce themselves as `user_agent`.
    #[must_use]
    pub fn with_user_agent(user_agent: &str) -> Self {
        NuGetClient {
            feeds: Mutex::new(vec![Arc::new(
                Feed::new(nuget_org()).with_user_agent(user_agent),
            )]),
            user_agent: user_agent.to_string(),
        }
    }

    /// The feeds from `NuGet.Config`; with none, nuget.org, as for `dotnet`.
    pub fn set_sources(&self, sources: &[Source]) {
        let wanted: Vec<Source> = if sources.is_empty() {
            vec![nuget_org()]
        } else {
            sources
                .iter()
                .filter(|s| s.is_enabled && s.is_remote())
                .cloned()
                .collect()
        };
        let mut feeds = self.feeds.lock().unwrap();
        let next = wanted
            .into_iter()
            .map(|source| {
                feeds
                    .iter()
                    .find(|f| f.source == source)
                    .cloned()
                    .unwrap_or_else(|| {
                        Arc::new(Feed::new(source).with_user_agent(&self.user_agent))
                    })
            })
            .collect();
        *feeds = next;
    }

    /// Own feeds first, nuget.org last: own packages are looked for there.
    fn ordered(&self) -> Vec<Arc<Feed>> {
        let feeds = self.feeds.lock().unwrap();
        feeds
            .iter()
            .filter(|f| !f.source.is_nuget_org())
            .chain(feeds.iter().filter(|f| f.source.is_nuget_org()))
            .cloned()
            .collect()
    }

    /// What all the feeds found: own feeds first, then nuget.org. A package
    /// from several feeds is one, its versions merged. Second, which feeds
    /// did not answer and why, in feed order.
    pub fn search(
        &self,
        t: &dyn Transport,
        query: &str,
        prerelease: bool,
        take: usize,
    ) -> (Vec<Package>, Vec<FeedFailure>) {
        let ordered = self.ordered();
        let results: Vec<Result<Vec<Package>, FeedFailure>> = std::thread::scope(|scope| {
            let handles: Vec<_> = ordered
                .iter()
                .map(|feed| scope.spawn(move || feed.search(t, query, prerelease, 0, take)))
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap_or_else(|_| Ok(Vec::new())))
                .collect()
        });
        let mut merged: Vec<Package> = Vec::new();
        let mut failures = Vec::new();
        for result in results {
            match result {
                Ok(packages) => {
                    for package in packages {
                        if let Some(existing) = merged
                            .iter_mut()
                            .find(|p| equal_ignoring_case(&p.id, &package.id))
                        {
                            let all = existing
                                .versions
                                .drain(..)
                                .chain(package.versions)
                                .collect::<Vec<_>>();
                            existing.versions = NuGetVersion::sorted_unique(all);
                        } else {
                            merged.push(package);
                        }
                    }
                }
                Err(failure) => failures.push(failure),
            }
        }
        (merged, failures)
    }

    /// Exactly this package, for installed ones: description and versions, from
    /// the first feed that has it.
    pub fn package(&self, t: &dyn Transport, id: &str) -> Option<Package> {
        self.ordered()
            .iter()
            .find_map(|feed| feed.package(t, id).ok().flatten())
    }

    /// Every version from every feed, prereleases and unlisted ones included.
    /// `None` when no feed answered.
    pub fn versions(&self, t: &dyn Transport, id: &str) -> Option<Vec<NuGetVersion>> {
        let feeds = self.feeds.lock().unwrap().clone();
        let found: Vec<Option<Vec<NuGetVersion>>> = std::thread::scope(|scope| {
            let handles: Vec<_> = feeds
                .iter()
                .map(|feed| scope.spawn(move || feed.versions(t, id).ok()))
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().ok().flatten())
                .collect()
        });
        let answered: Vec<Vec<NuGetVersion>> = found.into_iter().flatten().collect();
        (!answered.is_empty()).then(|| NuGetVersion::sorted_unique(answered.into_iter().flatten()))
    }
}

// MARK: reading

/// Service addresses from `index.json`: search and the package base. The base
/// ends in a slash: an id and `index.json` are appended to it.
#[must_use]
pub fn parse_service_index(data: &[u8]) -> (Option<String>, Option<String>) {
    let Some(resources) = Json::parse(data).and_then(|j| {
        j.objects("resources")
            .map(|r| r.into_iter().cloned().collect::<Vec<_>>())
    }) else {
        return (None, None);
    };
    let first = |prefix: &str| -> Option<String> {
        resources
            .iter()
            .filter(|r| r.str("@type").is_some_and(|t| t.starts_with(prefix)))
            .find_map(|r| r.str("@id").filter(|id| !id.is_empty()).map(str::to_owned))
    };
    let packages = first("PackageBaseAddress").map(|base| {
        if base.ends_with('/') {
            base
        } else {
            base + "/"
        }
    });
    (first("SearchQueryService"), packages)
}

/// The packages of a search answer.
#[must_use]
pub fn parse_search(data: &[u8], source: &Source) -> Vec<Package> {
    let Some(items) = Json::parse(data).and_then(|j| {
        j.objects("data")
            .map(|r| r.into_iter().cloned().collect::<Vec<_>>())
    }) else {
        return Vec::new();
    };
    items
        .iter()
        .filter_map(|item| {
            let (id, version) = (item.str("id")?, item.str("version")?);
            // `authors` is a string or an array of strings.
            let authors = item
                .strings("authors")
                .map(|a| a.join(", "))
                .or_else(|| item.str("authors").map(str::to_owned))
                .unwrap_or_default();
            let mut versions: Vec<NuGetVersion> = item
                .objects("versions")
                .unwrap_or_default()
                .into_iter()
                .filter_map(|v| v.str("version").and_then(NuGetVersion::parse))
                .collect();
            versions.sort_by(|a, b| b.cmp(a));
            let link = |key: &str| item.str(key).filter(|s| !s.is_empty()).map(str::to_owned);
            Some(Package {
                id: id.into(),
                version: version.into(),
                description: trim_blank(item.str("description").unwrap_or("")).to_string(),
                authors,
                total_downloads: item
                    .get("totalDownloads")
                    .and_then(Json::as_number_int)
                    .unwrap_or(0),
                verified: item.bool("verified").unwrap_or(false),
                project_url: link("projectUrl"),
                icon_url: link("iconUrl"),
                versions,
                source: source.name.clone(),
                is_from_nuget_org: source.is_nuget_org(),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nuget::testing::FakeTransport;

    const COMPANY_INDEX: &str = r#"{"resources": [{"@id": "https://git.example.com/nuget/query", "@type": "SearchQueryService"},
        {"@id": "https://git.example.com/nuget/download", "@type": "PackageBaseAddress/3.0.0"}]}"#;

    fn company() -> Source {
        let mut s = Source::new("Company", "https://git.example.com/nuget/index.json");
        s.username = Some("u".into());
        s.password = Some("p".into());
        s
    }

    #[test]
    fn service_index() {
        let (search, packages) = parse_service_index(COMPANY_INDEX.as_bytes());
        assert!(
            search.as_deref() == Some("https://git.example.com/nuget/query")
                && packages.as_deref() == Some("https://git.example.com/nuget/download/"),
            "a feed index: search, and the package base with a slash"
        );
        assert_eq!(parse_service_index(b"[]"), (None, None));
    }

    #[test]
    fn search_parsing() {
        let data = r#"{"data": [
            {"id": "Serilog", "version": "3.1.1", "description": " Logs \n", "authors": ["A", "B"], "totalDownloads": 1.5e9,
             "verified": true, "projectUrl": "https://serilog.net", "iconUrl": "", "versions": [{"version": "2.0.0"}, {"version": "3.1.1"}, {"version": "x"}]},
            {"id": "Bare", "version": "1.0", "authors": "Me"},
            {"version": "1.0"}]}"#;
        let found = parse_search(data.as_bytes(), &nuget_org());
        assert_eq!(found.len(), 2, "no id: skipped");
        let s = &found[0];
        assert!(
            s.description == "Logs"
                && s.authors == "A, B"
                && s.total_downloads == 1_500_000_000
                && s.verified
                && s.is_from_nuget_org
        );
        assert!(s.project_url.as_deref() == Some("https://serilog.net") && s.icon_url.is_none());
        assert_eq!(
            s.versions
                .iter()
                .map(|v| v.text.as_str())
                .collect::<Vec<_>>(),
            ["3.1.1", "2.0.0"],
            "versions newest first, non-versions dropped"
        );
        assert_eq!(found[1].authors, "Me", "authors as a string");
    }

    #[test]
    fn feeds_merge_and_fail() {
        let t = FakeTransport::new()
            .reply("https://git.example.com/nuget/index.json", 200, COMPANY_INDEX)
            .reply("https://git.example.com/nuget/query?q=log&skip=0&take=40&prerelease=false&semVerLevel=2.0.0", 200,
                r#"{"data": [{"id": "serilog", "version": "4.0.0-dev", "versions": [{"version": "4.0.0-dev"}, {"version": "3.1.1"}]}]}"#)
            .fail(NUGET_ORG_INDEX, "offline")
            .reply("https://azuresearch-usnc.nuget.org/query*", 200,
                r#"{"data": [{"id": "Serilog", "version": "3.1.1", "versions": [{"version": "3.1.1"}, {"version": "2.0"}]}]}"#)
            .reply("https://broken.example.com/index.json", 401, "");
        let client = NuGetClient::new();
        let mut broken = Source::new("Broken", "https://broken.example.com/index.json");
        broken.config_file = Some("/x".into());
        let folder = Source::new("Local", "/packages");
        client.set_sources(&[nuget_org(), company(), broken, folder]);
        let (packages, failures) = client.search(&t, "log", false, 40);
        assert_eq!(packages.len(), 1, "a package from two feeds is one");
        assert_eq!(packages[0].source, "Company", "own feeds first");
        let versions: Vec<&str> = packages[0]
            .versions
            .iter()
            .map(|v| v.text.as_str())
            .collect();
        assert_eq!(
            versions,
            ["4.0.0-dev", "3.1.1", "2.0"],
            "versions merge without repeats"
        );
        assert_eq!(
            failures,
            [FeedFailure::Unauthorized("Broken".into())],
            "nuget.org without its index answers at the known addresses"
        );
        let seen = t.seen.lock().unwrap();
        let company_request = seen
            .iter()
            .find(|r| r.url.starts_with("https://git.example.com/nuget/query"))
            .unwrap();
        assert_eq!(
            company_request.header_value("Authorization"),
            Some("Basic dTpw")
        );
        assert!(
            !seen.iter().any(|r| r.url.contains("/packages")),
            "a folder on disk is not a feed"
        );
    }

    #[test]
    fn versions_and_check() {
        let t = FakeTransport::new()
            .reply(
                "https://git.example.com/nuget/index.json",
                200,
                COMPANY_INDEX,
            )
            .reply(
                "https://git.example.com/nuget/download/my.pkg/index.json",
                200,
                r#"{"versions": ["1.0.0", "2.0.0-beta", "1.5"]}"#,
            )
            .reply(
                "https://git.example.com/nuget/download/none/index.json",
                404,
                "",
            )
            .reply("https://git.example.com/nuget/query*", 403, "");
        let client = NuGetClient::new();
        client.set_sources(&[company()]);
        let versions: Vec<String> = client
            .versions(&t, "My.Pkg")
            .unwrap()
            .into_iter()
            .map(|v| v.text)
            .collect();
        assert_eq!(versions, ["2.0.0-beta", "1.5", "1.0.0"]);
        assert_eq!(
            client.versions(&t, "none"),
            Some(Vec::new()),
            "404: no package, but the feed answered"
        );
        let index_reads = t
            .urls()
            .iter()
            .filter(|u| u.ends_with("nuget/index.json"))
            .count();
        assert_eq!(index_reads, 1, "the service index is read once");
        assert_eq!(
            Feed::new(company()).check(&t),
            Err(FeedFailure::Unauthorized("Company".into())),
            "the index without a login, the search not"
        );
        let offline = FakeTransport::new();
        assert_eq!(
            client.versions(&offline, "x"),
            None,
            "no feed answered: None"
        );
    }
}
