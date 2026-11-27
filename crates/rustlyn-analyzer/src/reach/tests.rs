//! Reach on a small project: a vendor SDK in its own folder, a stand-in for
//! Morpeh's stashes, and game code that leads to the SDK through calls,
//! fields and components — and game code that does not.

use std::collections::HashMap;

use super::packages::{LOCK, MANIFEST};
use super::{Config, FindingKind, Report, Request, Revision, Role, analyze};
use crate::blast::testing::{Project, patch};

const VENDOR: &str = "namespace Vendor.Ads {
    public interface IListener { void OnData(string data); }
    public static class Tracker {
        public static void Start() {}
        public static void Stop() {}
        public static void SetConsent(bool granted) {}
        public static void Send(string name) {}
        public static void Listen(IListener listener) {}
    }
}
";

const ECS: &str = "namespace Scellecs.Morpeh {
    public struct Entity {}
    public class Stash<T> where T : struct {
        public void Set(Entity entity, T value) {}
        public ref T Get(Entity entity) => throw null;
        public bool Has(Entity entity) => false;
        public void Remove(Entity entity) {}
    }
}
";

const CONSENT: &str = "using Scellecs.Morpeh;
using Vendor.Ads;
namespace Game {
    public struct TrackingStatus {
        public bool Enabled;
    }
    public struct Health {
        public int Value;
    }
    public class ConsentSystem {
        Stash<TrackingStatus> _status;
        Entity _entity;
        public void Apply(bool granted) {
            Tracker.SetConsent(granted);
            SetStatus(granted);
        }
        void SetStatus(bool granted) {
            _status.Set(_entity, new TrackingStatus { Enabled = granted });
        }
    }
    public class TrackingSystem {
        Stash<TrackingStatus> _status;
        Entity _entity;
        bool _tracking;
        public void OnUpdate() {
            if (!_status.Has(_entity)) return;
            ref var status = ref _status.Get(_entity);
            if (status.Enabled && !_tracking) {
                _tracking = true;
                Tracker.Start();
            }
            _status.Remove(_entity);
        }
    }
    public class ConsentPopup {
        ConsentSystem _consent = new ConsentSystem();
        public void OnAccept() {
            _consent.Apply(Decide());
        }
        bool Decide() {
            return true;
        }
    }
    public class Listener : IListener {
        public string Last;
        public void OnData(string data) {
            Last = data;
        }
    }
    public class Combat {
        Stash<Health> _health;
        Entity _entity;
        public int Hits;
        public void Hit() {
            ref var health = ref _health.Get(_entity);
            health.Value -= 1;
            Hits += 1;
        }
    }
}
";

const ANALYTICS: &str = "using Vendor.Ads;
namespace Game {
    public static class Analytics {
        public static void Track(string name) {
            Tracker.Send(name);
        }
    }
    public class Shop {
        public int Coins;
        public void Buy() {
            Coins -= 1;
            Analytics.Track(\"buy\");
        }
        public void Sell() {
            Coins += 1;
            Analytics.Track(\"sell\");
        }
    }
    public class Quests {
        public void Complete() {
            Analytics.Track(\"quest\");
        }
    }
}
";

const CONFIG: &str = r#"{
    "name": "ads",
    "own": ["Game"],
    "sinks": [{ "name": "Ads", "namespaces": ["Vendor.Ads"], "paths": ["Vendor"] }],
    "watch": [{ "name": "packages", "paths": ["Packages/manifest.json"] }],
    "limits": { "hub_callers": 2 }
}"#;

fn project(name: &str) -> Project {
    Project::new(
        name,
        &[
            ("Vendor/Tracker.cs", VENDOR),
            ("Lib/Ecs.cs", ECS),
            ("Game/Consent.cs", CONSENT),
            ("Game/Analytics.cs", ANALYTICS),
        ],
    )
}

fn run(project: &Project, config: &str, patch: Option<String>) -> Report {
    let request = Request {
        root: project.root(),
        patch,
        ..Request::default()
    };
    analyze(&request, &Config::parse(config).expect("config")).expect("analyzed")
}

/// The role a member has in the cone, by its name with parameter types.
fn role(report: &Report, name: &str) -> Option<Role> {
    report
        .cone
        .iter()
        .find(|listed| listed.name == name)
        .map(|listed| listed.role)
}

fn steps(report: &Report, name: &str) -> Vec<String> {
    report
        .cone
        .iter()
        .find(|listed| listed.name == name)
        .map(|listed| {
            listed
                .chain
                .iter()
                .map(|hop| format!("{} {}", hop.step, hop.target))
                .collect()
        })
        .unwrap_or_default()
}

/// A change of one text of `path` into another, judged.
fn change(name: &str, path: &str, old: &str, new: &str) -> Report {
    let project = project(name);
    project.write(path, new);
    run(&project, CONFIG, Some(patch(path, old, new)))
}

#[test]
fn the_cone_goes_through_calls_fields_and_components() {
    let project = project("cone");
    let report = run(&project, CONFIG, None);
    let text = report.cone_text(true);
    // Names the sink.
    assert_eq!(
        role(&report, "Game.ConsentSystem.Apply(bool)"),
        Some(Role::Path),
        "{text}"
    );
    assert_eq!(
        role(&report, "Game.TrackingSystem.OnUpdate()"),
        Some(Role::Path),
        "{text}"
    );
    // Calls what names it.
    assert_eq!(
        role(&report, "Game.ConsentPopup.OnAccept()"),
        Some(Role::Path),
        "{text}"
    );
    // The component one system writes and the other reads on its way to the
    // sink links the two, though neither calls the other.
    assert_eq!(
        role(&report, "Game.TrackingStatus"),
        Some(Role::Data),
        "{text}"
    );
    assert_eq!(
        role(&report, "Game.ConsentSystem.SetStatus(bool)"),
        Some(Role::Path),
        "{text}"
    );
    assert_eq!(
        steps(&report, "Game.ConsentSystem.SetStatus(bool)"),
        [
            "writes Game.TrackingStatus",
            "read_by Game.TrackingSystem.OnUpdate()",
            "uses Tracker.Start",
        ],
        "{text}"
    );
    // A field read on the way.
    assert_eq!(
        role(&report, "Game.TrackingSystem._tracking"),
        Some(Role::Data),
        "{text}"
    );
    // Called only from the cone.
    assert_eq!(
        role(&report, "Game.ConsentPopup.Decide()"),
        Some(Role::Helper),
        "{text}"
    );
    // Implements the sink's interface: the sink calls it.
    assert_eq!(
        role(&report, "Game.Listener.OnData(string)"),
        Some(Role::Path),
        "{text}"
    );
    // Game logic leads nowhere near it.
    assert_eq!(role(&report, "Game.Combat.Hit()"), None, "{text}");
    assert_eq!(role(&report, "Game.Health"), None, "{text}");
    assert!(!report.judged && !report.affects());
}

#[test]
fn a_hub_makes_its_callers_users() {
    let project = project("hub");
    let report = run(&project, CONFIG, None);
    let text = report.cone_text(true);
    // Three members call `Track`, and the limit is two: it is the project's
    // own API over the sink, and its callers only use it.
    assert_eq!(
        role(&report, "Game.Analytics.Track(string)"),
        Some(Role::Path),
        "{text}"
    );
    assert_eq!(role(&report, "Game.Shop.Buy()"), Some(Role::User), "{text}");
    assert_eq!(
        role(&report, "Game.Quests.Complete()"),
        Some(Role::User),
        "{text}"
    );
    // What a user reads is its own business.
    assert_eq!(role(&report, "Game.Shop.Coins"), None, "{text}");
    assert_eq!(report.hubs.len(), 1, "{text}");
    assert_eq!(report.hubs[0].name, "Game.Analytics.Track(string)");
    assert_eq!(report.hubs[0].users, 3);
}

#[test]
fn a_change_on_a_path_affects() {
    let new = CONSENT.replace("SetStatus(granted);", "SetStatus(!granted);");
    let report = change("path", "Game/Consent.cs", CONSENT, &new);
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.name, "Game.ConsentSystem.Apply(bool)");
    assert_eq!(finding.kind, FindingKind::Member);
    assert_eq!(finding.sinks, ["Ads"]);
    assert_eq!(report.unaffected, 0);
}

#[test]
fn a_change_of_game_logic_does_not() {
    let new = CONSENT.replace("health.Value -= 1;", "health.Value -= 2;");
    let report = change("logic", "Game/Consent.cs", CONSENT, &new);
    assert!(!report.affects(), "{}", report.text(true));
    assert!(report.findings.is_empty(), "{}", report.text(true));
    assert_eq!(report.unaffected, 1);
}

#[test]
fn a_component_field_is_part_of_the_way() {
    // A field nothing reads yet: the component it is in is on the way.
    let new = CONSENT.replace(
        "public bool Enabled;",
        "public bool Enabled;\n        public bool Forced;",
    );
    let report = change("field", "Game/Consent.cs", CONSENT, &new);
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.name, "Game.TrackingStatus.Forced");
    assert_eq!(finding.chain[0].step, "member_of");
    assert_eq!(finding.chain[0].target, "Game.TrackingStatus");
    // The other component is game logic's.
    let new = CONSENT.replace("public int Value;", "public long Value;");
    let report = change("other-field", "Game/Consent.cs", CONSENT, &new);
    assert!(!report.affects(), "{}", report.text(true));
}

#[test]
fn a_user_is_affected_where_it_uses_the_cone() {
    // The statement that calls the hub.
    let new = ANALYTICS.replace(
        "Analytics.Track(\"buy\");",
        "Analytics.Track(\"purchase\");",
    );
    let report = change("user-call", "Game/Analytics.cs", ANALYTICS, &new);
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings[0].name, "Game.Shop.Buy()");
    assert_eq!(report.findings[0].role, Some(Role::User));
    // Another statement of the same member: possibly, not for certain.
    let new = ANALYTICS.replace("Coins -= 1;", "Coins -= 2;");
    let report = change("user-else", "Game/Analytics.cs", ANALYTICS, &new);
    assert!(!report.affects(), "{}", report.text(true));
    assert_eq!(report.findings.len(), 1);
    assert!(!report.findings[0].certain);
    assert!(
        report.text(true).contains("? Game.Shop.Buy()"),
        "{}",
        report.text(true)
    );
    assert!(
        !report.text(false).contains("Game.Shop.Buy()"),
        "{}",
        report.text(false)
    );
}

#[test]
fn a_removed_call_is_found_by_its_name() {
    let old = CONSENT.replace("Hits += 1;", "Hits += 1;\n            Tracker.Stop();");
    let project = project("removed");
    let report = run(
        &project,
        CONFIG,
        Some(patch("Game/Consent.cs", &old, CONSENT)),
    );
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.kind, FindingKind::Removed);
    assert_eq!(finding.name, "Game.Combat.Hit()");
    assert_eq!(finding.chain[0].target, "Tracker");
    assert_eq!(report.unaffected, 0);
}

#[test]
fn a_removed_call_into_the_cone_is_found_by_its_name() {
    // Game logic stops calling the consent system: the call is not in the
    // new code, but the removed line names a member only the cone has.
    let old = CONSENT.replace(
        "Hits += 1;",
        "Hits += 1;\n            new ConsentSystem().Apply(false);",
    );
    let project = project("removed-member");
    let report = run(
        &project,
        CONFIG,
        Some(patch("Game/Consent.cs", &old, CONSENT)),
    );
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.name, "Game.Combat.Hit()");
    let steps: Vec<String> = finding
        .chain
        .iter()
        .map(|hop| format!("{} {}", hop.step, hop.target))
        .collect();
    assert_eq!(
        steps,
        [
            "removed Game.ConsentSystem.Apply(bool)",
            "uses Tracker.SetConsent"
        ]
    );
    assert_eq!(finding.sinks, ["Ads"]);
}

#[test]
fn a_new_call_is_found_in_the_new_code() {
    let new = CONSENT.replace("Hits += 1;", "Hits += 1;\n            Tracker.Stop();");
    let report = change("added", "Game/Consent.cs", CONSENT, &new);
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings[0].name, "Game.Combat.Hit()");
    assert_eq!(report.findings[0].chain[0].target, "Tracker.Stop");
}

#[test]
fn code_behind_a_symbol_is_read_with_it() {
    let device = CONSENT.replace(
        "Hits += 1;",
        "Hits += 1;\n#if DEVICE && !EDITOR\n            Tracker.Stop();\n#endif",
    );
    let project = project("symbols");
    project.write("Game/Consent.cs", &device);
    // As the project compiles, the call is not there.
    let report = run(&project, CONFIG, None);
    assert_eq!(
        role(&report, "Game.Combat.Hit()"),
        None,
        "{}",
        report.cone_text(true)
    );
    // Read as a device build, it is.
    let config = CONFIG.replace(
        "\"own\"",
        "\"configurations\": [{ \"name\": \"device\", \"symbols\": [\"DEVICE\", \"-EDITOR\"] }], \"own\"",
    );
    let report = run(&project, &config, None);
    assert_eq!(
        role(&report, "Game.Combat.Hit()"),
        Some(Role::Path),
        "{}",
        report.cone_text(true)
    );
    assert_eq!(report.cone[0].configurations, ["device"]);
}

#[test]
fn watched_files_and_the_sinks_own_source() {
    let project = project("watch");
    let diff = "--- a/Packages/manifest.json\n+++ b/Packages/manifest.json\n@@ -1,1 +1,1 @@\n-old\n+new\n\
                --- a/Vendor/Tracker.cs\n+++ b/Vendor/Tracker.cs\n@@ -3,1 +3,1 @@\n-    public static class Tracker {\n+    public static partial class Tracker {\n";
    let report = run(&project, CONFIG, Some(diff.to_owned()));
    assert!(report.affects(), "{}", report.text(true));
    let kinds: Vec<FindingKind> = report.findings.iter().map(|f| f.kind).collect();
    assert!(kinds.contains(&FindingKind::Watch), "{kinds:?}");
    assert!(kinds.contains(&FindingKind::Sink), "{kinds:?}");
}

#[test]
fn an_asset_with_the_data_of_a_script_the_cone_reads() {
    let settings = "using Vendor.Ads;
namespace Game {
    public class AdsSettings {
        public bool Enabled;
    }
    public class AdsStarter {
        public AdsSettings Settings;
        public void Start() {
            if (Settings.Enabled) Tracker.Start();
        }
    }
}
";
    let asset = "%YAML 1.1
--- !u!114 &11400000
MonoBehaviour:
  m_Script: {fileID: 11500000, guid: 0123456789abcdef0123456789abcdef, type: 3}
  Enabled: 1
--- !u!114 &11400001
MonoBehaviour:
  m_Script: {fileID: 11500000, guid: ffffffffffffffffffffffffffffffff, type: 3}
  Volume: 3
";
    let project = project("asset");
    project.write("Game/AdsSettings.cs", settings);
    project.write(
        "Game/AdsSettings.cs.meta",
        "fileFormatVersion: 2\nguid: 0123456789abcdef0123456789abcdef\n",
    );
    project.write("Data/Ads.asset", asset);
    let old = asset.replace("Enabled: 1", "Enabled: 0");
    let report = run(&project, CONFIG, Some(patch("Data/Ads.asset", &old, asset)));
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings[0].kind, FindingKind::Asset);
    assert_eq!(report.findings[0].name, "Game/AdsSettings.cs");
    // A change to another object of the same file is not about the sink.
    let old = asset.replace("Volume: 3", "Volume: 2");
    let report = run(&project, CONFIG, Some(patch("Data/Ads.asset", &old, asset)));
    assert!(!report.affects(), "{}", report.text(true));
}

#[test]
fn an_asset_is_judged_down_to_the_key() {
    // A settings object of many sections, of which the cone reads one
    // field of one.
    let settings = "using Vendor.Ads;
namespace Game {
    public class Section {
        public bool Enabled;
        public string Title;
    }
    public class AllSettings {
        public Section Ads;
        public Section Sound;
        public int[] Levels;
    }
    public class AdsStarter {
        public AllSettings Settings;
        public void Start() {
            if (Settings.Ads.Enabled) Tracker.Start();
        }
    }
}
";
    let asset = "%YAML 1.1
--- !u!114 &11400000
MonoBehaviour:
  m_Name: All
  m_Script: {fileID: 11500000, guid: 0123456789abcdef0123456789abcdef, type: 3}
  Ads:
    Enabled: 1
    Title: ads
  Sound:
    Enabled: 1
    Title: sound
  Levels:
  - 1
  - 2
";
    let judged = |name: &str, old_line: &str, new_line: &str| {
        let project = project(name);
        project.write("Game/AllSettings.cs", settings);
        project.write(
            "Game/AllSettings.cs.meta",
            "fileFormatVersion: 2\nguid: 0123456789abcdef0123456789abcdef\n",
        );
        project.write("Data/All.asset", asset);
        let old = asset.replacen(new_line, old_line, 1);
        assert_ne!(old, asset);
        run(&project, CONFIG, Some(patch("Data/All.asset", &old, asset)))
    };
    // The field the cone reads.
    let report = judged(
        "key-read",
        "  Ads:\n    Enabled: 0",
        "  Ads:\n    Enabled: 1",
    );
    assert!(report.affects(), "{}", report.text(true));
    // A field beside it in the same section; another section; the object's
    // own name.
    for (name, old, new) in [
        ("key-beside", "    Title: old", "    Title: ads"),
        ("key-section", "    Title: old", "    Title: sound"),
        ("key-list", "  - 5", "  - 2"),
        ("key-name", "  m_Name: Old", "  m_Name: All"),
    ] {
        let report = judged(name, old, new);
        assert!(!report.affects(), "{name}: {}", report.text(true));
    }
}

#[test]
fn the_report_as_json() {
    let new = CONSENT.replace("SetStatus(granted);", "SetStatus(!granted);");
    let report = change("json", "Game/Consent.cs", CONSENT, &new);
    let json = report.json(true);
    assert_eq!(json.int("version"), Some(1));
    assert_eq!(json.bool("affects"), Some(true));
    let findings = json.objects("findings").expect("findings");
    assert_eq!(
        findings[0].str("name"),
        Some("Game.ConsentSystem.Apply(bool)")
    );
    assert_eq!(findings[0].int("line"), Some(13));
    // The way on from the statement that changed: the call that sets the
    // component, the system that reads it, the sink.
    let chain = findings[0].objects("chain").expect("chain");
    let steps: Vec<&str> = chain.iter().filter_map(|hop| hop.str("step")).collect();
    assert_eq!(steps, ["calls", "writes", "read_by", "uses"]);
    assert_eq!(chain[3].str("sink"), Some("Ads"));
    assert_eq!(chain[3].str("target"), Some("Tracker.Start"));
    assert!(json.objects("cone").is_some_and(|cone| !cone.is_empty()));
}

/// Shared state, a call through an interface with two implementations, and
/// a utility the rest of the game calls too.
const SHARED: &str = "using Scellecs.Morpeh;
using Vendor.Ads;
namespace Game {
    public struct GamePhase {
        public int Value;
    }
    public interface IScreen {
        void Open();
    }
    public class AdsScreen : IScreen {
        Stash<GamePhase> _phase;
        Entity _entity;
        public void Open() {
            if (_phase.Has(_entity)) Tracker.Start();
            Util.Note();
        }
    }
    public class MapScreen : IScreen {
        public void Open() {
            Util.Note();
        }
    }
    public class Menu {
        IScreen _screen;
        public int Clicks;
        public void Click() {
            Clicks += 1;
            _screen.Open();
        }
    }
    public static class Util {
        public static void Note() {}
    }
    public class Loader {
        Stash<GamePhase> _phase;
        Entity _entity;
        public void Done() {
            _phase.Set(_entity, new GamePhase { Value = 1 });
        }
    }
    public class Hud { Stash<GamePhase> _phase; Entity _e; public bool A() { return _phase.Has(_e); } }
    public class Map { Stash<GamePhase> _phase; Entity _e; public bool A() { return _phase.Has(_e); } }
    public class Chat { Stash<GamePhase> _phase; Entity _e; public bool A() { return _phase.Has(_e); } }
    public class Shop2 { Stash<GamePhase> _phase; Entity _e; public bool A() { return _phase.Has(_e); } }
}
";

#[test]
fn shared_state_and_calls_through_a_base_end_the_walk() {
    let project = project("shared");
    project.write("Game/Shared.cs", SHARED);
    let report = run(&project, CONFIG, None);
    let text = report.cone_text(true);
    assert_eq!(
        role(&report, "Game.AdsScreen.Open()"),
        Some(Role::Path),
        "{text}"
    );
    // The component is read on the way, so a change to it counts...
    assert_eq!(role(&report, "Game.GamePhase"), Some(Role::Data), "{text}");
    // ...but four members outside the cone read it too: it is the game's
    // state, and who sets it sets it for everyone.
    assert_eq!(role(&report, "Game.Loader.Done()"), None, "{text}");
    // `IScreen.Open` has two implementations: the caller only uses
    // whichever it has, and the walk does not go on through it.
    assert_eq!(
        role(&report, "Game.Menu.Click()"),
        Some(Role::User),
        "{text}"
    );
    assert_eq!(role(&report, "Game.Menu.Clicks"), None, "{text}");
    // Called from outside the cone as well: nobody's helper.
    assert_eq!(role(&report, "Game.Util.Note()"), None, "{text}");
}

#[test]
fn only_the_slice_of_a_caller_matters() {
    let caller = "namespace Game {
    public class Flow {
        ConsentSystem _consent = new ConsentSystem();
        public int Steps;
        public bool Ready;
        public void Next(bool agreed) {
            Steps += 1;
            var granted = agreed && Ready;
            if (Steps > 100) return;
            Log(Steps);
            _consent.Apply(granted);
        }
        void Log(int value) {}
    }
}
";
    let judged = |name: &str, old: &str, new: &str| {
        let project = project(name);
        let changed = caller.replace(old, new);
        assert_ne!(changed, caller);
        project.write("Game/Flow.cs", &changed);
        run(
            &project,
            CONFIG,
            Some(patch("Game/Flow.cs", caller, &changed)),
        )
    };
    // The call itself, the local it passes, and the condition that leaves
    // before it: all on the way.
    for (name, old, new) in [
        ("slice-call", "Apply(granted)", "Apply(!granted)"),
        ("slice-local", "agreed && Ready", "agreed || Ready"),
        ("slice-exit", "Steps > 100", "Steps > 10"),
    ] {
        let report = judged(name, old, new);
        assert!(report.affects(), "{name}: {}", report.text(true));
        assert_eq!(report.findings[0].name, "Game.Flow.Next(bool)");
    }
    // A statement beside it: possibly, not for certain.
    let report = judged("slice-beside", "Log(Steps);", "Log(Steps + 1);");
    assert!(!report.affects(), "{}", report.text(true));
    assert_eq!(report.findings.len(), 1, "{}", report.text(true));
    assert!(!report.findings[0].certain);
    // What the slice reads is data of the cone; what the rest reads is not.
    let report = judged(
        "slice-none",
        "Log(Steps);",
        "Log(Steps);\n            Log(0);",
    );
    assert_eq!(role(&report, "Game.Flow.Ready"), Some(Role::Data));
    assert_eq!(role(&report, "Game.Flow.Log(int)"), None);
}

#[test]
fn a_past_change_is_judged_by_names() {
    // The code has moved on since the change: lines no longer match.
    let project = project("past");
    let now = format!("// A comment added since.\n{CONSENT}");
    project.write("Game/Consent.cs", &now);
    let revision = |id: &str, old: &str, new: &str| {
        let then = CONSENT.replace(old, new);
        assert_ne!(then, CONSENT);
        Revision {
            id: id.to_owned(),
            title: format!("change {id}"),
            patch: patch("Game/Consent.cs", CONSENT, &then),
            texts: HashMap::from([("Game/Consent.cs".to_owned(), then)]),
            ..Revision::default()
        }
    };
    let request = Request {
        root: project.root(),
        revisions: vec![
            revision("consent", "SetStatus(granted);", "SetStatus(!granted);"),
            revision("combat", "health.Value -= 1;", "health.Value -= 2;"),
            revision("popup", "return true;", "return false;"),
            revision(
                "call",
                "Hits += 1;",
                "Hits += 1;\n            Tracker.Stop();",
            ),
        ],
        ..Request::default()
    };
    let report = analyze(&request, &Config::parse(CONFIG).expect("config")).expect("analyzed");
    let text = report.text(true);
    let judged: Vec<(&str, bool)> = report
        .revisions
        .iter()
        .map(|revision| (revision.id.as_str(), revision.affects()))
        .collect();
    assert_eq!(
        judged,
        [
            ("consent", true),
            ("combat", false),
            ("popup", true),
            ("call", true)
        ],
        "{text}"
    );
    assert_eq!(
        report.revisions[0].findings[0].name,
        "Game.ConsentSystem.Apply(bool)"
    );
    assert_eq!(report.revisions[1].unaffected, 1, "{text}");
    // A helper of the cone, whole.
    assert_eq!(
        report.revisions[2].findings[0].name,
        "Game.ConsentPopup.Decide()"
    );
    // The call is not in today's code: found by the name the line had.
    assert_eq!(report.revisions[3].findings[0].kind, FindingKind::Removed);
    assert_eq!(report.revisions[3].findings[0].chain[0].step, "named");
    assert!(report.affects() && !report.judged);
    assert!(
        text.contains("● consent change consent — AFFECTS Ads"),
        "{text}"
    );
    assert!(
        text.contains("○ combat change combat — not affected"),
        "{text}"
    );
    let json = report.json(false);
    assert_eq!(json.objects("revisions").map(|list| list.len()), Some(4));
}

// MARK: - Unity packages and build files

const STORE: &str = "namespace Vendor.Iap {
    public static class Store {
        public static bool Ready() { return true; }
    }
}
";

const LABEL: &str = "namespace Vendor.Ui {
    public static class Label {
        public static string Text(string text) { return text; }
    }
}
";

/// Game code over three packages: it sells through the store and reports
/// to the ads SDK, and shows labels.
const PAY: &str = "using Vendor.Ads;
using Vendor.Iap;
using Vendor.Ui;
namespace Game {
    public class Payments {
        public void Purchase(string id) {
            if (!Store.Ready()) return;
            Tracker.Send(id);
        }
    }
    public class Hud {
        public string Title() {
            return Label.Text(\"hello\");
        }
    }
}
";

const PACKAGE_CONFIG: &str = r#"{
    "name": "ads",
    "own": ["Game"],
    "sinks": [{ "name": "Ads", "namespaces": ["Vendor.Ads"], "mentions": ["AppsFlyer"] }]
}"#;

const DEPENDENCIES: &str = "<dependencies>
  <androidPackages>
    <androidPackage spec=\"com.appsflyer:af-android-sdk:6.14.0\"/>
    <androidPackage spec=\"com.other:lib:1.0\"/>
  </androidPackages>
</dependencies>
";

/// The manifest: what the project asked for. `core` is only in the lock.
fn manifest() -> String {
    "{
  \"dependencies\": {
    \"com.vendor.ads\": \"1.0.0\",
    \"com.vendor.iap\": \"1.0.0\",
    \"com.vendor.ui\": \"1.0.0\",
    \"com.vendor.wrap\": \"1.0.0\"
  }
}
"
    .to_owned()
}

/// The lock: the three packages embedded in the project, `ads` over `core`,
/// and `wrap` over `ads`.
fn lock() -> String {
    let entry = |name: &str, version: &str, source: &str, dependencies: &str| {
        format!(
            "    \"com.vendor.{name}\": {{\n      \"version\": \"{version}\",\n      \"depth\": 0,\n      \"source\": \"{source}\",\n      \"dependencies\": {{{dependencies}}},\n      \"hash\": \"{name}-1\"\n    }}"
        )
    };
    let entries = [
        entry(
            "ads",
            "file:com.vendor.ads",
            "embedded",
            "\"com.vendor.core\": \"1.0.0\"",
        ),
        entry("iap", "file:com.vendor.iap", "embedded", ""),
        entry("ui", "file:com.vendor.ui", "embedded", ""),
        entry("core", "1.0.0", "registry", ""),
        entry("wrap", "1.0.0", "registry", "\"com.vendor.ads\": \"1.0.0\""),
    ];
    format!(
        "{{\n  \"dependencies\": {{\n{}\n  }}\n}}\n",
        entries.join(",\n")
    )
}

/// A project whose SDK is an embedded package, as are the code the game
/// uses to buy and a label widget.
fn package_project(name: &str) -> Project {
    Project::new(
        name,
        &[
            ("Packages/com.vendor.ads/Runtime/Tracker.cs", VENDOR),
            ("Packages/com.vendor.iap/Runtime/Store.cs", STORE),
            ("Packages/com.vendor.ui/Runtime/Label.cs", LABEL),
            (MANIFEST, &manifest()),
            (LOCK, &lock()),
            ("Game/Pay.cs", PAY),
        ],
    )
}

/// The manifest and the lock after `package` was bumped, as the texts and
/// as one patch.
fn bumped(package: &str) -> (String, String, String) {
    let name = package.strip_prefix("com.vendor.").unwrap_or(package);
    let manifest = manifest().replace(
        &format!("\"{package}\": \"1.0.0\""),
        &format!("\"{package}\": \"1.1.0\""),
    );
    let lock = lock().replace(&format!("\"{name}-1\""), &format!("\"{name}-2\""));
    let both = patch(MANIFEST, &self::manifest(), &manifest) + &patch(LOCK, &self::lock(), &lock);
    (manifest, lock, both)
}

/// What bumping one package of the project comes to.
fn bump(name: &str, package: &str) -> Report {
    let project = package_project(name);
    let (manifest, lock, patch) = bumped(package);
    project.write(MANIFEST, &manifest);
    project.write(LOCK, &lock);
    run(&project, PACKAGE_CONFIG, Some(patch))
}

fn hop_steps(finding: &super::Finding) -> Vec<String> {
    finding
        .chain
        .iter()
        .map(|hop| format!("{} {}", hop.step, hop.target))
        .collect()
}

#[test]
fn a_package_that_is_the_sinks_code() {
    let report = bump("pkg-ads", "com.vendor.ads");
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings.len(), 1, "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.kind, FindingKind::Package);
    assert_eq!(finding.name, "com.vendor.ads");
    assert_eq!(finding.path, MANIFEST);
    assert_eq!(finding.line, 2);
    assert_eq!(hop_steps(finding), ["package_of com.vendor.ads"]);
    assert_eq!(finding.chain[0].sink.as_deref(), Some("Ads"));
    assert_eq!(finding.sinks, ["Ads"]);
    assert_eq!(finding.count, 0);
    assert_eq!(report.unaffected, 0);
}

#[test]
fn a_package_the_sinks_package_depends_on() {
    // Only in the lock: its entry is found there.
    let report = bump("pkg-core", "com.vendor.core");
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.name, "com.vendor.core");
    assert_eq!(finding.path, LOCK);
    assert_eq!(hop_steps(finding), ["dependency_of com.vendor.ads"]);
    assert_eq!(finding.sinks, ["Ads"]);
}

#[test]
fn a_package_that_depends_on_the_sinks_package() {
    let report = bump("pkg-wrap", "com.vendor.wrap");
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.name, "com.vendor.wrap");
    assert_eq!(hop_steps(finding), ["depends_on com.vendor.ads"]);
    assert_eq!(finding.sinks, ["Ads"]);
}

#[test]
fn a_package_the_way_to_a_sink_uses() {
    let report = bump("pkg-iap", "com.vendor.iap");
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.kind, FindingKind::Package);
    assert_eq!(finding.count, 1);
    assert_eq!(
        hop_steps(finding),
        [
            "used_by Game.Payments.Purchase(string)",
            "uses Tracker.Send"
        ]
    );
    // The line of the use, in the member's file.
    assert_eq!(finding.chain[0].path, "Game/Pay.cs");
    assert_eq!(finding.chain[0].line, 6);
    assert_eq!(finding.chain[1].sink.as_deref(), Some("Ads"));
    assert_eq!(finding.sinks, ["Ads"]);
    let text = report.text(true);
    assert!(
        text.contains("used by 1 members on the way, such as Game.Payments.Purchase(string)"),
        "{text}"
    );
    let json = report.json(false);
    let findings = json.objects("findings").expect("findings");
    assert_eq!(findings[0].str("kind"), Some("package"));
    assert_eq!(findings[0].int("count"), Some(1));
}

#[test]
fn a_package_only_game_logic_uses_is_not_affected() {
    let report = bump("pkg-ui", "com.vendor.ui");
    assert!(!report.affects(), "{}", report.text(true));
    assert!(report.findings.is_empty(), "{}", report.text(true));
    // A package is counted as one, not as a member.
    assert_eq!(report.unaffected, 0);
    assert_eq!(report.unaffected_packages, 1);
}

#[test]
fn a_sink_named_only_by_its_packages() {
    // No code in the project names the sink: its packages are binaries.
    let config = r#"{
        "name": "ads",
        "own": ["Game"],
        "sinks": [{ "name": "Ads", "types": ["Nothing"], "packages": ["com.vendor.a*"] }]
    }"#;
    let project = package_project("pkg-named");
    let (manifest, lock, both) = bumped("com.vendor.ads");
    project.write(MANIFEST, &manifest);
    project.write(LOCK, &lock);
    let report = run(&project, config, Some(both));
    let finding = &report.findings[0];
    assert_eq!(
        hop_steps(finding),
        ["package_of com.vendor.ads"],
        "{}",
        report.text(true)
    );
    // What depends on it follows from the lock.
    let (manifest, lock, both) = bumped("com.vendor.core");
    project.write(MANIFEST, &manifest);
    project.write(LOCK, &lock);
    let report = run(&project, config, Some(both));
    assert_eq!(
        hop_steps(&report.findings[0]),
        ["dependency_of com.vendor.ads"],
        "{}",
        report.text(true)
    );
}

#[test]
fn a_manifest_that_is_not_json_is_reported() {
    let project = package_project("pkg-broken");
    let broken = "{ \"dependencies\": { \"com.vendor.ads\": \n";
    project.write(MANIFEST, broken);
    let report = run(
        &project,
        PACKAGE_CONFIG,
        Some(patch(MANIFEST, &manifest(), broken)),
    );
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.kind, FindingKind::Watch);
    assert_eq!(finding.name, "packages");
    assert_eq!(finding.path, MANIFEST);
}

#[test]
fn a_package_bump_in_a_past_revision() {
    let project = package_project("pkg-past");
    let revision = |id: &str, package: &str| {
        let (manifest, lock, patch) = bumped(package);
        Revision {
            id: id.to_owned(),
            title: format!("bump {package}"),
            patch,
            texts: HashMap::from([(MANIFEST.to_owned(), manifest), (LOCK.to_owned(), lock)]),
            ..Revision::default()
        }
    };
    let request = Request {
        root: project.root(),
        revisions: vec![
            revision("iap", "com.vendor.iap"),
            revision("ui", "com.vendor.ui"),
            revision("ads", "com.vendor.ads"),
        ],
        ..Request::default()
    };
    let report =
        analyze(&request, &Config::parse(PACKAGE_CONFIG).expect("config")).expect("analyzed");
    let text = report.text(true);
    let judged: Vec<bool> = report.revisions.iter().map(|r| r.affects()).collect();
    assert_eq!(judged, [true, false, true], "{text}");
    let finding = &report.revisions[0].findings[0];
    assert_eq!(finding.kind, FindingKind::Package);
    assert_eq!(finding.count, 1);
    assert_eq!(report.revisions[1].unaffected, 0, "{text}");
    assert_eq!(report.revisions[1].unaffected_packages, 1, "{text}");
    assert_eq!(report.revisions[2].findings[0].chain[0].step, "package_of");
}

#[test]
fn a_line_of_a_build_file_that_names_a_sink() {
    let path = "Game/Editor/AdsDependencies.xml";
    let judged = |name: &str, old: &str, new: &str| {
        let project = package_project(name);
        project.write(path, new);
        run(&project, PACKAGE_CONFIG, Some(patch(path, old, new)))
    };
    let bumped = DEPENDENCIES.replace("6.14.0", "6.15.0");
    // The line is replaced: added and removed both name it, once.
    let report = judged("mention-bump", DEPENDENCIES, &bumped);
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings.len(), 1, "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.kind, FindingKind::Mention);
    // As the configuration spells it, matched without regard to case.
    assert_eq!(finding.name, "AppsFlyer");
    assert_eq!(finding.path, path);
    assert_eq!(finding.line, 2);
    assert_eq!(finding.sinks, ["Ads"]);
    assert_eq!(finding.chain[0].step, "mentions");
    assert_eq!(
        finding.chain[0].target,
        "<androidPackage spec=\"com.appsflyer:af-android-sdk:6.15.0\"/>"
    );
    // Added.
    let without = DEPENDENCIES.replace(
        "    <androidPackage spec=\"com.appsflyer:af-android-sdk:6.14.0\"/>\n",
        "",
    );
    let report = judged("mention-added", &without, DEPENDENCIES);
    assert!(report.affects(), "{}", report.text(true));
    // Removed: the line is not in the new text.
    let report = judged("mention-removed", DEPENDENCIES, &without);
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings[0].kind, FindingKind::Mention);
    // A line that names nothing.
    let other = DEPENDENCIES.replace("com.other:lib:1.0", "com.other:lib:2.0");
    let report = judged("mention-none", DEPENDENCIES, &other);
    assert!(!report.affects(), "{}", report.text(true));
    assert!(report.findings.is_empty(), "{}", report.text(true));
}

#[test]
fn a_watched_file_changed_by_name_only_in_a_past_revision() {
    let project = project("others");
    let revision = |others: &[&str]| Revision {
        id: "abc".to_owned(),
        title: "binary".to_owned(),
        others: others.iter().map(|path| (*path).to_owned()).collect(),
        ..Revision::default()
    };
    let request = Request {
        root: project.root(),
        revisions: vec![
            revision(&["Packages/manifest.json"]),
            revision(&["Assets/a.png"]),
        ],
        ..Request::default()
    };
    let report = analyze(&request, &Config::parse(CONFIG).expect("config")).expect("analyzed");
    let text = report.text(true);
    assert!(report.revisions[0].affects(), "{text}");
    assert_eq!(report.revisions[0].findings[0].kind, FindingKind::Watch);
    assert_eq!(report.revisions[0].findings[0].name, "packages");
    assert!(!report.revisions[1].affects(), "{text}");
}

#[test]
fn the_cone_lists_its_packages() {
    let project = package_project("pkg-cone");
    let report = run(&project, PACKAGE_CONFIG, None);
    assert_eq!(
        report.packages.provided,
        [("Ads".to_owned(), vec!["com.vendor.ads".to_owned()])]
    );
    // The store is used on the way; the label is game logic's; the SDK's
    // own package is not listed as used.
    assert_eq!(report.packages.used.len(), 1, "{:?}", report.packages);
    assert_eq!(report.packages.used[0].name, "com.vendor.iap");
    assert_eq!(report.packages.used[0].members, 1);
    let text = report.cone_text(true);
    assert!(text.contains("Ads is provided by com.vendor.ads"), "{text}");
    assert!(text.contains("com.vendor.iap — 1 members"), "{text}");
    let json = report.json(true);
    let section = json.object("packages").expect("packages");
    let used = section.objects("used").expect("used");
    assert_eq!(used[0].str("name"), Some("com.vendor.iap"));
    assert_eq!(used[0].int("members"), Some(1));
    let provided = section.objects("provided").expect("provided");
    assert_eq!(provided[0].str("sink"), Some("Ads"));
    assert_eq!(
        provided[0].strings("packages"),
        Some(vec!["com.vendor.ads".to_owned()])
    );
}

/// Members that run code the sink is called from, and the code that runs
/// them without writing their names.
const BOX: &str = "using System;
using Vendor.Ads;
namespace Game {
    public class Box : IDisposable {
        public Box() { Tracker.Start(); }
        public int this[int i] { get { Tracker.Start(); return i; } set { Tracker.Stop(); } }
        public static Box operator +(Box a, Box b) { Tracker.Send(\"add\"); return a; }
        public static implicit operator int(Box b) { Tracker.Send(\"int\"); return 0; }
        public override string ToString() { Tracker.Send(\"str\"); return \"\"; }
        public void Dispose() { Tracker.Stop(); }
        int _p;
        public int P { get { return _p; } set { Tracker.SetConsent(true); } }
        public int Plain() { return 1; }
        public static Box operator -(Box a, Box b) { return a; }
        public bool Cheap() { return true; }
    }
    public class Calls {
        public Box NewTarget() { Box b = new(); return b; }
        public int IndexRead(Box b) { return b[1]; }
        public void IndexWrite(Box b) { b[1] = 2; }
        public Box Add(Box a, Box c) { return a + c; }
        public Box Sub(Box a, Box c) { return a - c; }
        public int Conv(Box b) { int i = b; return i; }
        public string Interp(Box b) { return $\"{b}\"; }
        public void Using(Box b) { using (b) { } }
        public void SetP(Box b) { b.P = 4; }
        public void Init() { var b = new Box { P = 3 }; }
        public int Plain(Box b) { return b.Plain(); }
        public string Name() { return nameof(Box.Cheap); }
        public Type Kind() { return typeof(Box); }
    }
}
";

/// A caller that runs a member of the cone through a construct — `new()`,
/// `m[i]`, `a + b`, a conversion, `$"{m}"`, `using`, an assignment of a
/// property whose setter has code — is on the way to the sink as much as
/// one that names it; one that only names it in `nameof` or `typeof`, or
/// that runs another operator, is not.
#[test]
fn a_construct_that_runs_a_member_of_the_cone_leads_to_the_sink() {
    let project = project("constructs");
    project.write("Game/Box.cs", BOX);
    let report = run(&project, CONFIG, None);
    let text = report.cone_text(true);
    for name in [
        "NewTarget()",
        "IndexRead(Game.Box)",
        "IndexWrite(Game.Box)",
        "Add(Game.Box, Game.Box)",
        "Conv(Game.Box)",
        "Interp(Game.Box)",
        "Using(Game.Box)",
        "SetP(Game.Box)",
        "Init()",
    ] {
        let found = role(&report, &format!("Game.Calls.{name}")).or_else(|| {
            role(
                &report,
                &format!("Game.Calls.{}", name.replace("Game.Box", "Box")),
            )
        });
        assert!(found.is_some(), "{name} is on the way: {text}");
    }
    for name in ["Sub", "Plain", "Name", "Kind"] {
        assert!(
            !report
                .cone
                .iter()
                .any(|listed| listed.name.starts_with(&format!("Game.Calls.{name}("))),
            "{name} is not on the way: {text}"
        );
    }
}

/// Two members written on one line are told apart: the change is to the one
/// it is in, not to the class that holds both.
#[test]
fn members_on_one_line_are_judged_each() {
    const ONE: &str = "using Vendor.Ads;\nnamespace Game {\n    public class One { void A() { Tracker.Start(); } void B() { int x = 1; } }\n}\n";
    let project = project("one-line");
    project.write("Game/One.cs", ONE);
    let new = ONE.replace("int x = 1;", "int x = 2;");
    project.write("Game/One.cs", &new);
    let report = run(&project, CONFIG, Some(patch("Game/One.cs", ONE, &new)));
    assert!(!report.affects(), "{}", report.text(true));
    assert_eq!(report.unaffected, 1, "{}", report.text(true));
    let new = ONE.replace("Tracker.Start();", "Tracker.Stop();");
    project.write("Game/One.cs", &new);
    let report = run(&project, CONFIG, Some(patch("Game/One.cs", ONE, &new)));
    assert!(report.affects(), "{}", report.text(true));
    assert_eq!(report.findings[0].name, "Game.One.A()");
}

/// A project whose constructor, method, property and base class are on the
/// way to a sink, and a `Work` that is not: what its removed lines name is
/// what they run.
const NAMING: &str = "using Vendor.Ads;
namespace Game {
    public class Gate {
        public Gate(string id) { Tracker.Start(); }
        public Gate(int n) { Tracker.Start(); }
        public static int Max = 1;
    }
    public class Door : Gate {
        public Door(int n) : base(n) { }
    }
    public class Tail {
        public Tail(string s) { Tracker.Start(); }
        public Tail(int n) : this(\"x\") { }
    }
    public class Opts {
        public int Level { get { Tracker.Stop(); return 1; } set { Tracker.Stop(); } }
    }
    public static class Boot {
        public static void Launch() { Tracker.Start(); }
    }
    public class Caller {
        public System.Action Hook;
        public void Work(object o, Gate g) {
            int before = 0;
            BODY
        }
    }
}
";

/// What removing `old` from `Work`, in favour of `new`, comes to.
fn removal(name: &str, old: &str, new: &str) -> Report {
    let before = NAMING.replace("BODY", old);
    let after = NAMING.replace("BODY", new);
    let project = project(name);
    project.write("Game/Naming.cs", &after);
    run(
        &project,
        CONFIG,
        Some(patch("Game/Naming.cs", &before, &after)),
    )
}

/// A removed line that only mentions a type does not run its constructor: a
/// test of the type, a cast, a declaration, a generic argument, `typeof`,
/// `nameof`, a string or a comment.
#[test]
fn a_removed_line_that_only_mentions_a_type_names_no_constructor() {
    let cases = [
        ("var b = o is Gate;", "var b = o is Gate && true;"),
        ("var b = o as Gate;", "var b = (o as Gate) == null;"),
        ("Gate h = g;", "var h = g;"),
        ("var x = (Gate)o;", "var x = o;"),
        ("var t = typeof(Gate);", "var t = typeof(string);"),
        ("var n = nameof(Gate);", "var n = \"Gate\";"),
        (
            "var l = new System.Collections.Generic.List<Gate>();",
            "var l = new System.Collections.Generic.List<int>();",
        ),
        ("Gate[] all = null;", "var all = 1;"),
        ("var s = \"new Gate(1)\";", "var s = \"\";"),
        ("// new Gate(2) was here", "// gone"),
        ("/* new Gate(3) */ before++;", "before++;"),
        ("var v = Gate.Max;", "var v = 1;"),
    ];
    for (k, (old, new)) in cases.into_iter().enumerate() {
        let report = removal(&format!("type-mention-{k}"), old, new);
        assert!(!report.affects(), "{old}: {}", report.text(true));
        assert!(report.findings.is_empty(), "{old}: {}", report.text(true));
    }
}

/// A removed line that runs something on the way to a sink names it, by the
/// syntax of what is gone.
#[test]
fn a_removed_line_that_runs_a_member_names_it() {
    let cases = [
        // A constructor, by `new`, a target type and an initializer.
        (
            "var x = new Gate(\"a\");",
            "var x = 1;",
            "Game.Gate.Gate(string)",
        ),
        (
            "var x = new Game.Gate(\"a\");",
            "var x = 1;",
            "Game.Gate.Gate(string)",
        ),
        (
            "Gate x = new(\"a\");",
            "var x = 1;",
            "Game.Gate.Gate(string)",
        ),
        (
            "var x = new Gate(\"a\") { };",
            "var x = 1;",
            "Game.Gate.Gate(string)",
        ),
        // A method call, a method group.
        ("Boot.Launch();", "before++;", "Game.Boot.Launch()"),
        ("Hook += Boot.Launch;", "before++;", "Game.Boot.Launch()"),
        // A property read, set by an object initializer.
        ("var l = new Opts().Level;", "var l = 0;", "Game.Opts.Level"),
        (
            "var p = new Opts { Level = 3 };",
            "var p = 1;",
            "Game.Opts.Level",
        ),
        (
            "Opts p = null; p.Level = 4;",
            "before++;",
            "Game.Opts.Level",
        ),
    ];
    for (k, (old, new, member)) in cases.into_iter().enumerate() {
        let report = removal(&format!("run-{k}"), old, new);
        assert!(report.affects(), "{old}: {}", report.text(true));
        let finding = &report.findings[0];
        assert_eq!(finding.kind, FindingKind::Removed, "{old}");
        assert!(finding.certain, "{old}");
        assert!(
            finding.chain.iter().any(|hop| hop.target == member),
            "{old}: {:?}",
            finding.chain
        );
    }
}

/// `: base(…)` and `: this(…)` run the constructors of the base and of the
/// type, when every one that may be meant is on the way to a sink.
#[test]
fn a_removed_constructor_chain_names_the_constructors_it_ran() {
    let first = project("chained");
    let old = NAMING.replace("BODY", "before++;");
    let new = old.replace("public Door(int n) : base(n) { }", "public Door(int n) { }");
    first.write("Game/Naming.cs", &new);
    let report = run(&first, CONFIG, Some(patch("Game/Naming.cs", &old, &new)));
    assert!(report.affects(), "{}", report.text(true));
    let finding = &report.findings[0];
    assert_eq!(finding.name, "Game.Door.Door(int)");
    assert!(
        finding
            .chain
            .iter()
            .any(|hop| hop.target.starts_with("Game.Gate.Gate(")),
        "{:?}",
        finding.chain
    );
    // The same of `: this(…)`.
    let second = project("chained-this");
    let new = old.replace(
        "public Tail(int n) : this(\"x\") { }",
        "public Tail(int n) { }",
    );
    second.write("Game/Naming.cs", &new);
    let report = run(&second, CONFIG, Some(patch("Game/Naming.cs", &old, &new)));
    assert!(report.affects(), "{}", report.text(true));
    assert!(
        report.findings[0]
            .chain
            .iter()
            .any(|hop| hop.target == "Game.Tail.Tail(string)"),
        "{:?}",
        report.findings[0].chain
    );
}

/// A name the cone shares with a member outside it says nothing of which
/// was run.
#[test]
fn a_removed_call_of_a_name_the_cone_shares_is_not_named() {
    let both = "namespace Game { public class Lamp { public void Launch() { } } }\n";
    let project = project("shared-name");
    project.write("Game/Lamp.cs", both);
    let old = NAMING.replace("BODY", "new Lamp().Launch();");
    let new = NAMING.replace("BODY", "before++;");
    project.write("Game/Naming.cs", &new);
    let report = run(&project, CONFIG, Some(patch("Game/Naming.cs", &old, &new)));
    assert!(!report.affects(), "{}", report.text(true));
}

/// A package alone changed: the headline counts packages, not members, and
/// says one where there is one.
#[test]
fn the_headline_counts_members_and_packages_apart() {
    let report = bump("headline-ui", "com.vendor.ui");
    let headline = report.headline();
    assert!(
        headline.contains("1 changed package does not lead there"),
        "{headline}"
    );
    assert!(!headline.contains("member"), "{headline}");
    assert_eq!(report.unaffected, 0);
    assert_eq!(report.unaffected_packages, 1);
    let json = report.json(false);
    assert_eq!(json.int("unaffected"), Some(0));
    assert_eq!(json.int("unaffected_packages"), Some(1));
}

#[test]
fn the_headline_words_one_and_many() {
    let new = CONSENT.replace("health.Value -= 1;", "health.Value -= 2;");
    let report = change("headline-member", "Game/Consent.cs", CONSENT, &new);
    let headline = report.headline();
    assert!(
        headline.contains("1 changed member does not lead there"),
        "{headline}"
    );
    let new = CONSENT.replace("SetStatus(granted);", "SetStatus(!granted);");
    let report = change("headline-finding", "Game/Consent.cs", CONSENT, &new);
    let headline = report.headline();
    assert!(headline.contains("— 1 finding;"), "{headline}");
    assert!(
        headline.contains("0 changed members do not lead there"),
        "{headline}"
    );
}
