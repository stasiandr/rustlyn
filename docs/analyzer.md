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
- Morpeh-style ECS stashes are recognised by `value::ecs`. Other ECS frameworks
  need their own provider.
- Unity source generators are not run, so members they add are invisible
  unless the host's `Symbols` knows about them.
