//! Reach on a small project: a vendor SDK in its own folder, a stand-in for
//! Morpeh's stashes, and game code that leads to the SDK through calls,
//! fields and components — and game code that does not.

use std::collections::HashMap;

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
