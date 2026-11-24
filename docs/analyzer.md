# rustlyn-analyzer

`rustlyn-ide` answers the questions an editor asks about the file on screen,
within the time a keystroke allows. `rustlyn-analyzer` answers questions about
the whole project, which take longer: what a change reaches, where a value comes
from, how a method can fail, which scenes use a script, and which packages were
restored. These analyses run in the background, read the disk directly and may
take seconds.

The crate depends only on Rustlyn crates. It does no networking: NuGet requests
are built and their answers parsed, but the caller supplies the transport.
Results are structured data (enums and stable English codes, with an English
`Display`), so a front end can present or translate them however it likes.
Positions in the public API are UTF-8 byte offsets and zero-based lines, unless
an item says otherwise.

## Modules

| Module | What it does |
|---|---|
| `blast` | The blast radius of a change. It maps the changed lines of a patch onto members, then walks forward through the compiler to find who calls the changed code, who reads what it writes and who uses a changed type. It adds the Unity scenes and prefabs that use the touched scripts, then attaches risks to every node. |
| `reach` | Does a change lead to a given set of APIs. A caller names the *sinks* (an SDK's namespaces, a vendor folder, an assembly); the analysis works out the cone of own code that leads to them through calls, fields and ECS components, and judges a change against it, with the chain from the change to the sink. |
| `value` | The value graph: where a value comes from, through every place that writes it, down to its sources (literals, constants, configs, the Unity inspector, time, input). |
| `fail` | How a member can fail (throw, division by zero, null, index, a library call), where, through which calls and under which conditions, and whether those conditions can hold given the values its inputs get across the project. |
| `unity` | A Unity project read without Unity: asset GUIDs from `.meta` files, the serialized scene and prefab format, and where a script or asset is used. |
| `nuget` | Package versions, `NuGet.Config`, the packages each project references, whether a restore found them, and v3 feeds over a caller-supplied `nuget::http::Transport`. |
| `diff` | Unified diffs as git and code review services print them, and a Myers line diff. |
| `deep` | A pool of threads with a deep stack, for the compiler's recursion on deeply nested code. |

Thread-safety analysis (`RLN1001`–`RLN1003`) and the per-method failability
pass are part of `rustlyn-ide`'s diagnostics; `blast` and `fail` use them.

## Command-line tools

Build them with `cargo build --release -p rustlyn-analyzer`.

### rustlyn-blast

```
rustlyn-blast [ROOT] [--diff FILE|-] [--base REV] [--staged] [--depth N] [--nodes N] [--json] [--no-cache] [--timings]
rustlyn-blast --mcp
```

Without `--diff` it diffs the git working copy against `--base` (default `HEAD`).
The exit code is 0 when there are no high risks, 3 when there are, and 2 on an
error. `--json` prints a report for agents. `--mcp` runs the same analysis as a
Model Context Protocol server over stdio.

```
Change: 4 changed members in 1 files; 2 more reached, assets 1. Risk: high.
✎ Player.health [removed] Assets/Player.cs:3
   ⚠ high: the field's value is set in Assets/Hero.prefab: a rename or a type change without [FormerlySerializedAs] loses it
✎ Player.hp [new] Assets/Player.cs:3
✎ Player.Damage(int) [body] Assets/Player.cs:4
   ← Enemy.Attack() — calls Assets/Enemy.cs:4
      ⚠ high: always fails once it gets there: NullReferenceException when target == null
✎ Player.IsDead() [body] Assets/Player.cs:7
   ← Player.Update() — calls Assets/Player.cs:8
      ⚠ medium: Unity calls it every frame: an error or slow code shows at once
▣ Assets/Hero.prefab — has Assets/Player.cs (Hero › MonoBehaviour); sets field health
```

### rustlyn-reach

```
rustlyn-reach [ROOT] --config FILE [--diff FILE|-] [--base REV] [--merge-base REV] [--staged] [--possible] [--json] [--no-cache] [--timings]
rustlyn-reach [ROOT] --config FILE --commits RANGE [--commit REV] [--possible] [--json]
rustlyn-reach [ROOT] --config FILE --cone [--users] [--json]
```

A blast radius starts at a change and asks what it reaches. `rustlyn-reach`
starts at the other end: the configuration names *sinks* — the APIs of an SDK,
say — and the question is whether a change leads to them. A change to the code
that asks for consent does; a change to game logic does not.

```json
{
  "name": "ads",
  "own": ["Assets/Game"],
  "configurations": [
    { "name": "android", "symbols": ["UNITY_ANDROID", "-UNITY_EDITOR"] },
    { "name": "ios", "symbols": ["UNITY_IOS", "-UNITY_ANDROID", "-UNITY_EDITOR"] }
  ],
  "sinks": [
    { "name": "Ads", "namespaces": ["Vendor.Ads"], "paths": ["Assets/Vendor/Ads"] },
    { "name": "Consent", "types": ["ConsentManager"], "assemblies": ["Vendor.Consent"] }
  ],
  "watch": [
    { "name": "SDK packages", "paths": ["Packages/manifest.json", "Assets/Vendor/**"] }
  ],
  "ignore": ["Game.Logging"],
  "limits": { "depth": 10, "data_hops": 2, "hub_callers": 10, "hub_writers": 10, "shared_readers": 3 }
}
```

`own` is the code the cone is looked for in (everything outside the sinks'
folders when it is left out). A sink is named by namespaces, type names,
source folders or assemblies. Each configuration reads the project as one
build: `NAME` defines a preprocessor symbol everywhere, `-NAME` undefines it.
A Unity project's own compile is its editor's, and the code that talks to a
device SDK usually sits behind `#if UNITY_ANDROID && !UNITY_EDITOR`; the cone
is worked out for every configuration and a report says which ones a finding
holds for. `watch` lists files to report as they are: a package manifest, a
vendor folder. Without `--config` the file is `ROOT/.rustlyn/reach.json`.

The cone is walked backward from every place where own code names a sink:

* a member that names a sink is in it, all of it, and so are the members of a
  type that derives from a sink's type: the sink calls them;
* who calls a member of the cone is in it, by the *slice* of the calling
  statement — the statement, the conditions it runs under, the conditions
  under which an earlier `return` leaves before it, and the statements that
  give the locals those mention their values;
* a field, a property or an ECS component read on those lines is in it as
  data, and so is who writes it. Two systems that never call each other are
  linked by the component one sets and the other reads;
* a method called on those lines, and from the cone only, is in it whole.

Three things stop the walk before it reaches the whole project. A member with
more than `hub_callers` callers is the project's own API over the sink
(`Analytics.Track`): its callers are *users*, judged by the statement that
calls it and followed no further; so are the callers of a base or interface
member with several implementations. A field or component that more than
`shared_readers` members outside the cone read is shared state: it is in the
cone as data, but who writes it is not. And at most `data_hops` steps of a
path go through data.

A changed member of the cone is a finding for certain when the change is on
the lines that matter, and a possible one (`--possible`) otherwise:

```
Reach «ads»: AFFECTS Ads — 1 findings; 0 possibly, 3 changed members do not lead there.
✎ Game.ConsentSystem.SetStatus(bool) [path]  Assets/Game/Consent.cs:17
   → writes Game.TrackingStatus  Assets/Game/Consent.cs:18
   → read by Game.TrackingSystem.OnUpdate()  Assets/Game/Consent.cs:28
   → uses Tracker.Start [Ads]  Assets/Game/Consent.cs:30
```

Removed lines are read as text: a call that is gone is not in the new code to
be found, so a removed line that names a sink's type is reported by the name.
A changed scene, prefab or asset is reported when the change is in the
serialized data of a script whose fields the cone reads.

Without `--diff` the change is the git working copy against `--base`
(`HEAD`); `--merge-base master` takes the commit the branch left `master` at.
`--commits RANGE` judges every commit of a git range (first parents: a merge
is its whole branch) against the cone of the code as it is now — which of a
release's merges touched the SDKs. A file that has not changed since a commit
is judged by lines, as above; one that has is judged by names: the changed
members are found in today's code, and a member the cone holds a slice of is
affected for certain when the changed lines mention what the slice leads to.
`--commit REV` judges that one commit against its first parent, the same way;
it can be given more than once. The library does the same without the tool:
`reach::git::revision(root, "HEAD")` and `reach::git::revisions(root, range, progress)`
give the `Revision`s to put in a `Request`.

`--cone` prints the cone instead: every member with its way to a sink, then
the hubs. It is the way to check a configuration. `--json` is the report for
scripts and agents (schema `version: 1`). The exit code is 0 when the change
leads to no sink, 3 when it does, 2 on an error.

### rustlyn-graph

```
rustlyn-graph ROOT File.cs:line:column [--json] [--depth N] [--limit N] [--no-calls] [--arguments] [--expect CHAIN]…
rustlyn-graph ROOT Folder/ [--calls] [-v]
```

Given a position, it prints the value graph of the symbol there. Given a folder,
it surveys the folder's members and reports how many graphs could be built
cleanly. `--expect` checks that a chain of nodes is present, which is useful in
tests.

```
Wallet.balance [value] Shop.cs:5
   ← Wallet.Withdraw [code] Shop.cs:10  │ balance -= amount; — changes the old value
      ← amount [parameter] Shop.cs:7
         ← Shop.Buy [code] Shop.cs:20  │ void Buy() { wallet.Withdraw(price); } — calls Withdraw
            ← Shop.price [value] Shop.cs:18
               ← 15 [source: initial value]
   ← Wallet.balance [code] Shop.cs:5  │ int balance = Start; — initial value
      ← Wallet.Start [value] Shop.cs:4
         ← 100 [source: constant]
sources: constant 100 · initial value 15
```

### rustlyn-fail

```
rustlyn-fail ROOT File.cs[:line[:column]] [--all] [--no-cache]
```

```
Wallet.Withdraw — places that can fail: 2, possible: 1
1. InvalidOperationException «low» (throw) — unknown — not every input can be computed
   where: Shop.cs:9:31  throw new InvalidOperationException("low");
   when: amount >= 0 && amount > balance
   amount = 15 — the only call in the project: Shop.cs:20:18
2. ArgumentException «negative» (throw) — impossible
   where: Shop.cs:8:25  throw new ArgumentException("negative");
   when: amount < 0
   amount = 15 — the only call in the project: Shop.cs:20:18
```

## Extending the analyses

The engine knows C#, Unity and NuGet. It knows nothing about a particular
codebase's conventions, such as a network protocol, a config system or a
client/server pair. A host application adds those through traits:

- `blast::BlastStep` contributes findings and risks to a blast radius report,
  for example "this change alters the wire format of a network message". Steps
  are passed in `blast::Extensions` and appear in the JSON report under their
  own name.
- `blast::RiskModel` adds risk reasons to the nodes of the impact.
- `blast::Wording` words a report's codes, in English by default.
- `value::EdgeProvider` adds edges to the value graph. It supplies extra origins
  (for example "read from config X"), places where a value is set outside C#,
  places where a message arrives, and types bridged between projects. Providers
  live in `value::Project::edges`.
- `value::symbols::Symbols` is the name index the graph uses. `IndexSymbols`
  implements it over `rustlyn-ide`'s project index; a host can supply its own
  to see members that source generators add.

```rust
use rustlyn_analyzer::blast::{self, Extensions, Request};

let report = blast::analyze(&request, &session, &Extensions::default());
println!("{}", report.text());
```

## Limits

- Parts of `value` still work on UTF-16 text internally, which is why
  `Decl` and `Target` positions are UTF-16 columns, the same as
  `rustlyn-ide`'s `Location`.
- `reach` reads a body by its text, not its flow: a slice takes every
  assignment to a local, before the statement or after it. It does not follow
  a value through a call's arguments into the callee, and a delegate stored
  in a field and invoked elsewhere is a read of the field, not a call.
- Morpeh-style ECS stashes are recognised by `value::ecs` and `reach`. Other ECS frameworks
  need their own provider.
- Unity source generators are not run, so members they add are invisible
  unless the host's `Symbols` knows about them.
