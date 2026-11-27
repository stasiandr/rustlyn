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

The thread diagnostics report a pair of accesses only where nothing can be shown to
order or exclude them. Two accesses overlap when one is in code started and not waited
for (`Task.Run`, `Task.Factory.StartNew`, a `Thread`, the thread pool, a timer, an
`async void` method or an async call that is a statement of its own, a `ContinueWith`
body) and the other is outside it, or when both are in the body of a `Parallel` call,
or in two delegates of one `Parallel.Invoke`, or in the task of a loop that starts one
for each iteration and waits for none inside the loop (`for (...) Task.Run(() => x++)`).
They do not overlap when the code before and after an `await` is one flow, when the
thread was waited for first (`await`, `Wait`, `Result`, `GetAwaiter().GetResult()`,
`Join`, `Task.WaitAll`, `Task.WhenAll` awaited or waited, a signalled gate, the wait
handle of a cancellation token whose source is cancelled, `RunSynchronously()`), when a
`ContinueWith` body follows its antecedent, or when both hold the same lock (`lock`,
`Monitor`, `SemaphoreSlim`, `Mutex`, `SpinLock`, `ReaderWriterLockSlim`). The wait may be
for a task a method of the file returns (`await Start()`, `Start().Wait()`, `var t =
Start(); t.Wait()`, where every `return` of the method is the task it started, or the
method is `async` and awaits what it started), or for tasks put into a local collection
that nothing else changes (`tasks.Add(Task.Run(..))`, `new[] { Task.Run(..) }`, then
`Task.WaitAll(tasks.ToArray())` or `await Task.WhenAll(tasks)`). A lock on one
side only, or two different locks, is still reported ("under different locks"). The
operand of `lock` is not an access of the field. `arr[i]` in a `Parallel.For` body with
the loop's own index is not a shared write, and neither are `arr[2 * i + 1]` and `int j
= i; arr[j]`, an index that is the loop's index moved or scaled by a constant and never
shared with another write to the same array in the body; `arr[0]`, `arr[i / 2]` and
`arr[i % 2]` are. A local that a local function writes is written by every iteration of
a `Parallel` body that calls the function. A lock held by a caller, and a protocol
between methods (a flag set before a start message, a volatile flag a loop spins on, a
`Barrier`), are not judged. Elements of an array that tasks of a loop write are not
reported, as which element each takes is not known, and neither is what those tasks
reach by calling a method, which may be the state of a different object in each
iteration. The module docs of `crates/rustlyn-ide/src/semantic/analyzers/threads.rs` list
each rule.

## Command-line tools

Build them with `cargo build --release -p rustlyn-analyzer`.

### rustlyn-blast

```
rustlyn-blast [ROOT] [--diff FILE|-] [--base REV] [--staged] [--depth N] [--nodes N] [--json] [--no-cache] [--timings]
rustlyn-blast --mcp
```

Without `--diff` it diffs the git working copy against `--base` (default `HEAD`).
The exit code is 0 when there are no high risks, 3 when there are, and 2 on an
error: a ROOT that is not a folder, a `--diff` file that cannot be read or has
no line of a diff in it, a failing `git`. An empty diff is not an error; it is a
change with no members. `--json` prints a report for agents. `--mcp` runs the
same analysis as a Model Context Protocol server over stdio: a `root` that is
not a folder and a `diff` that is not a diff are an error result (`isError`),
and a JSON-RPC batch (an array of requests) is answered with an array of
answers, as JSON-RPC 2.0 has it.

Sources are read as the compiler reads them: UTF-8, UTF-16 with a byte-order
mark, and — as `csc` does — any other bytes as Latin-1; a patch is read by line
the same way. A file that is not UTF-8 is analyzed, not skipped.

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

What counts as a caller. The walk asks the compiler's bound bodies who runs a
changed member, so a caller is a member whose code runs it, whether or not it
writes the member's name:

* a call, a method group made a delegate (`Func<int> f = o.M;`), a handler
  subscribed to an event (`e += o.M`);
* a constructor by `new C(…)`, by a target-typed `new(…)`, by `: base(…)` or
  `: this(…)`, and by an object initializer (`new C { P = 1 }` runs the
  constructor and the setter `P`), a collection initializer (`Add`), `with`
  (a record's own copy constructor and the `init` setters it names) and an
  attribute (the constructor it binds and the properties it sets by name; the
  member it is on is the caller);
* an indexer used as `m[i]`, its getter by a read, its setter by an assignment;
* operators: binary, unary, compound assignment, `++` and `--`, `true` and
  `false` (`if (m)`, `a && b`), implicit and explicit conversions, wherever a
  value of the one type is taken as the other (assigned, passed, cast);
* `foreach` (`GetEnumerator`, `MoveNext`, `Current` and the enumerator's
  `Dispose`), `using` and `await using` (`Dispose`, `DisposeAsync`), `await`
  (`GetAwaiter`, `IsCompleted`, `GetResult`), a deconstruction or a positional
  pattern (`Deconstruct`), a list pattern (`Length`, `Count`, the indexer), a
  query expression (`Select`, `Where`, …), `lock` on a `System.Threading.Lock`
  the project declares (the framework's own runs no member of the project);
* `ToString()` where the static type shows that the value is written as text:
  an interpolation hole, a string concatenation, an argument of
  `Console.WriteLine`, `string.Format`, `StringBuilder.Append` or `Debug.Log`.
  A value typed `object` or as an interface shows nothing, and is not a caller.

A name that is not a run is not a caller: `nameof(m.F)`, `typeof(T)` and a
documentation `cref`. Another type's member of the same name is another
member, and so is the overload the compiler did not bind. A call by name
through an interface or a base member is listed as `calls_base`, as before. A
construct that runs a base class's member on a value of the changed member's
type, or of a class it derives from, is listed the same way; one that runs an
interface's is every implementation's, and is not listed, nor is a use of a
base member on a value of an unrelated type (the `IDisposable.Dispose` of the
`IEnumerator<int>` a `foreach` disposes, for a collection that is no
enumerator).

A property's getter and setter are different code. When the changed lines are
all in the getter, the callers are the code that reads the property; when all
in the setter (or `init`), the code that assigns it; `p.P += 1` does both. A
change outside the accessors, or in both, reaches all of them. Two members
written on one line are told apart by where the change is on the line, and a
caller is the member the compiler names, not the innermost one on its line.

A change in code the build leaves out — an `#if` that is off for the project —
is not in the compiler's view. It is not dropped: the member is named from the
file's own structure (read with the symbols its conditions name turned on),
and it carries a medium risk, `not_built`: no callers are known, and nothing
checks it.

The search does not follow `dynamic`, reflection, or a method called by a name
in a string (`SendMessage("Hit")`, a `UnityEvent` set up in the editor; those a
scene or prefab calls by name are listed under assets).

The Unity field risk is about the value an asset stores. A prefab or scene that
sets a field keeps the value under the field's name and type. It is lost, and
the risk is high (`serialized_field`), when the field is renamed (the old name
is gone, with no `[FormerlySerializedAs("old")]` on a field that replaces it),
removed, given another type, or stops being serialized (`public` to private
without `[SerializeField]`, `static`, `const`, `readonly`, `[NonSerialized]`).
A changed default or an added attribute loses nothing: serialized instances
keep their own value, and the report says so as a low note
(`serialized_value_kept`). A scene or prefab that places the prefab and
overrides the field (`PrefabInstance`, `m_Modifications`, `propertyPath`) is
listed with the same finding.

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
    {
      "name": "Ads",
      "namespaces": ["Vendor.Ads"],
      "paths": ["Assets/Vendor/Ads"],
      "mentions": ["appsflyer"]
    },
    {
      "name": "Consent",
      "types": ["ConsentManager"],
      "assemblies": ["Vendor.Consent"],
      "packages": ["com.vendor.consent", "com.vendor.consent.*"]
    }
  ],
  "text_files": ["**/*Dependencies.xml", "**/*.gradle", "**/Podfile"],
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
holds for. `watch` lists files to report as they are: a vendor folder, a settings file.
A sink's `packages` are Unity package names (`*` is a glob) that are the sink
even when the code analysis cannot tell, as with a binary plugin; its
`mentions` are substrings, matched without regard to case, that make a changed
line of a native build file concern it. `text_files` are the globs of those
build files and default to `**/*Dependencies.xml`, `**/*.gradle`,
`**/gradle.properties`, `**/AndroidManifest.xml`, `**/Podfile` and
`**/*.podspec`. Without `--config` the file is `ROOT/.rustlyn/reach.json`.

The cone is walked backward from every place where own code names a sink:

* a member that names a sink is in it, all of it, and so are the members of a
  type that derives from a sink's type: the sink calls them;
* who calls a member of the cone is in it, by the *slice* of the calling
  statement — the statement, the conditions it runs under, the conditions
  under which an earlier `return` leaves before it, and the statements that
  give the locals those mention their values. A call is any use that runs the
  member, as for `rustlyn-blast`: an operator, a conversion, `m[i]`, `new()`,
  `foreach`, `using`, `await`, `$"{m}"`. A property whose getter or setter has
  code of its own is called by whoever reads or assigns it; the property is one
  member, so its getter and its setter are not told apart in the cone;
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

A change to `Packages/manifest.json` or `Packages/packages-lock.json` is judged
per package, not as one file: the packages added, removed or changed (by
version or hash) are compared between the old and the new text, and each is
judged by the first rule that holds, for every configuration. A package
concerns a sink (a `package` finding, certain) when

1. it provides a sink: own code names a sink declared in it, or the
   configuration names it (`package_of`);
2. a package that provides a sink depends on it, directly or not, by the lock
   (`dependency_of`);
3. it depends on a package that provides a sink (`depends_on`);
4. a member on a path to a sink, or a helper of one, uses it on the lines that
   matter (`used_by`, the member closest to a sink, then its way on; the
   finding says how many members use it).

Any other package is not affected and counts under `unaffected`. A package
owns the files of its folder: `Library/PackageCache/<name>@…/`, and the folder
of a lock entry that is `embedded` (`file:<folder>`) or `local` (`file:<path
relative to Packages>`). A manifest or a lock that is not JSON, before or after,
is reported whole as a certain `watch` finding named `packages`.

A changed line of one of the `text_files` — added or removed — that contains a
sink's `mentions` is a certain `mention` finding, once for each file and sink,
with the line as the way on (`mentions`).

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
`reach::git::revision(root, "HEAD", &config)` and
`reach::git::revisions(root, range, &config, progress)` give the `Revision`s to
put in a `Request`. Sources, assets, the two package files and the
`text_files` are diffed and their text kept; every other changed path is only
named in `Revision::others`, which is all a `watch` needs.

`--cone` prints the cone instead: every member with its way to a sink, then
the hubs, then the packages: for each sink the packages that provide it, and
the packages the cone uses on lines that matter with the number of members,
most used first. It is the way to check a configuration. `--json` is the report for
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

The writes of a member are the places that assign it by name: `=`, `+=`, `??=`,
`++`, a deconstruction, an object initializer, `with`, an `out` or `ref`
argument — also through a receiver (`ref this.T`, `out o.T`) — a `ref` local
that is another name for it (`ref int r = ref T; r = 5;`), the callers of a
`ref`-returning member (`Slot() = 5`), `Interlocked.Exchange`/`CompareExchange`/
`Add`/`And`/`Or` and `Volatile.Write`, the arguments of the callers of the
primary constructor whose parameter a member is initialized from (`class
C(int t) { public int T = t; }`), the same for a record's positional parameter
(`record R(int V)` with `new R(4)`), and the assignments an indexer's setter is
reached by (`this[0] = 5` for a `set { T = value; }`).

"No writes were found by name" is an assertion about names. Where a reference to
the place escapes into code the graph cannot follow — a method of an assembly it
does not model, a delegate, a reference stored away — the node says that the
value may be written through a reference there, and the list of writes is not
empty.

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

What each verdict says:

- **fails always, once it gets here** — every value the inputs can have leads
  to the failure, and nothing on the way there is open. It is not given for a
  failure behind a loop that may not run, a `catch` or a `catch` filter, a
  statement above that may return or throw, a label a `goto` may reach, a
  `goto case` into a `switch` section, or a call that runs a member a subtype
  may replace.
- **possible** — some values lead to it, and the way there may be closed.
- **impossible** — no value the inputs can have makes the conditions hold
  together. Two conditions on one input count together only for a value it has
  at both: a write to a parameter, a local or a field between them, and for a
  field a call, an `await`, a `yield` or a `lock`, make them about two values.
- **unknown** — an input has no known value, or a condition is of a kind the
  values cannot tell.

A parameter has what every call in the project passes until the body writes to
it; after that it has that or what the body gives it, and nothing is known
after `+=`, `++`, `ref` or `out`. Nothing is known of the parameters of a
member that calls reach without naming it, and the input's line in the report
says which way:

- it is virtual, an override or implements an interface member;
- the runtime or a framework calls it: `Main`, a static constructor, a method
  with an attribute other than the few that only tell the compiler or a tool
  something (`[Fact]`, `[OnDeserialized]`, `[HttpGet]`, `[ContextMenu]`), and in
  a Unity project a message such as `Update` or `OnTriggerEnter` of a type
  derived from the engine's;
- it is passed as a delegate, or a method of its name is in a method group the
  binder could not resolve;
- something calls it by name at run time: a `dynamic` call or access of that
  name on any receiver (`d.F(0)`, `F(d)` with a `dynamic` argument), or a
  lookup by name that is a constant string or `nameof` (`GetMethod("F")`,
  `InvokeMember`, `Delegate.CreateDelegate`, `Expression.Call`, Unity's
  `Invoke("F")` and `SendMessage("F")`). A field written by name
  (`GetField("f").SetValue`, a `dynamic` assignment) has no known values;
- a body that may call it does not compile.

A call whose member is a public one of a library may come from code outside
the project too; that is the limit stated below, and `impossible` is said of
the project as it is.

The `default` of a `switch` holds where no other label does; an arm of a
`switch` expression, where its pattern matches and no arm before it did. A call
of an `async` method that is not awaited does not throw, and a call of an
iterator runs none of its body.

A library call that throws on what it is given is judged by what the library
does. `int.Parse(s)` reads `s` by the current culture, which the program sets
and the analysis does not know: `-` is the sign in most cultures and
`U+061C -` in the Arabic ones, `1,000` is a thousand in one culture and not a
number in another. A verdict is certain only for a text every culture the
runtime ships reads the same way:

- digits, the white space `\t \n \v \f \r` and the space around them, and
  the NULs a string may end in: `" 5 "` and `"5\0"` parse, `"5 5"` and `""` do
  not;
- the range of an integer type (`OverflowException` where the digits are too
  many, and not `FormatException`), of `decimal` too;
- an ASCII letter, `.` or `,` in an integer, a letter in a `decimal`, a
  character no culture uses in a number (`_`, `(`, `$`): it does not parse;
- `bool.Parse` and `char.Parse`, which no culture reads.

A `+` or `-` in a text that would parse makes it *possible* (the cultures
differ), unless the provider is `CultureInfo.InvariantCulture` or
`NumberFormatInfo.InvariantInfo`, which sign with them. A `.`, `,`, `e`, `NaN` or `Infinity` in a `float`,
`double` or `decimal`, a character beyond ASCII that a culture may use as a
sign or a separator, and the overloads that take `NumberStyles` or a base are
*unknown*. `TryParse` never throws; `Convert.ToInt32(null)` is `0` where
`int.Parse(null)` throws `ArgumentNullException`. An `OverflowException` or an
`ArgumentNullException` of a parse is listed only where it can happen. `Parse`
of a `Guid`, `DateTime`, `TimeSpan`, `Version`, an enum or a `BigInteger` is
not modelled and lists nothing.

A condition is written as C# that means what it says. Where the failure is on
the way past a guard, the opposite is written: a comparison is turned round
(`a < b` to `a >= b`) only for integers, `char`, `decimal` and enums, where
that is exactly the opposite; for a `float`, a `double`, a nullable or a type
with an operator of its own it is `!(a < b)`. Operands that bind more loosely
than the comparison are put in parentheses, and conditions joined with `&&`
are, where one has a `||` or a `?:`.

Certain, beside the failures already followed: a member reached through a
`null` that is written (`((string)null).Length`, `default(string).Length`), a
`foreach` over what is known to be null, `dict[null]` read or written, a
collection made with a capacity below zero, `First()`, `Last()`, `Single()`
and `ElementAt()` of an empty array, of `Enumerable.Empty<T>()` and of a
collection made empty where it is used, `Pop`, `Peek` and `Dequeue` of an
empty stack or queue, `throw null`. A collection held in a local counts as
empty only where the local has been given it once and is not mentioned
between, in a loop that comes back to it, or in a lambda. Two comparisons of
one integer, as it is at one place, with constants that no value satisfies
together (`x > 0 && x < 0`, `i < 3` and `i == 5`) rule the failure out
whatever the integer is; comparisons of anything else are not combined.

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
- A use no name stands for is found where the compiler binds it to the
  member. Binding a body costs more than reading its text, so the search binds
  only the bodies that hold a construct that can reach the member (`foreach`
  and `using` for a `Dispose`, a `[` for an indexer, `new(` for a constructor)
  and that mention a name that can bring them a value of the member's type, of
  a type derived from it or of a base class of it: the type's name, or the
  name of a member declared with such a type or taking one. A value that reaches a body by no such name
  (a `dynamic`, a type argument inferred from a value the body gets from an
  assembly) is not found. `ToString` is followed only where the static type
  shows it, and `lock` only on a `System.Threading.Lock` the project declares.
- `reach` reads a body by its text, not its flow: a slice takes every
  assignment to a local, before the statement or after it. It does not follow
  a value through a call's arguments into the callee, and a delegate stored
  in a field and invoked elsewhere is a read of the field, not a call.
- `fail` takes the values a method is called with, and the values a field or
  property is given, from the project's own code: a public method that code
  outside the project calls, or a public field it sets, may get others, and
  `impossible` is said of the project as it is.
  A virtual or interface member's failures are not told from its overrides',
  an exception that a `catch` rethrows is not followed out of it, and what an
  iterator or a delegate runs is not followed.
  A name that is read at run time (`GetMethod(name)`), a method found by
  `Activator.CreateInstance` or `Type.GetMethods()`, and a method the Unity
  inspector wires to an event, are not seen: `impossible` rests on the calls
  that name the member.
  A column in `rustlyn-fail`'s output is counted in UTF-16 code units, as an
  editor and `csc` count them.
- Morpeh-style ECS stashes are recognised by `value::ecs` and `reach`. Other ECS frameworks
  need their own provider.
- Unity source generators are not run, so members they add are invisible
  unless the host's `Symbols` knows about them.
