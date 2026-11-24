# Compiling a Unity project's Assembly-CSharp with rustlyn

What was used to measure an edit's way from disk to a running Unity editor
through `examples/serve` instead of Unity's own compile. Run it on a copy of
the project, never on the one an editor is open on: the probe replaces
`Library/ScriptAssemblies/Assembly-CSharp.dll` and turns auto-refresh off.

1. Copy the project (on APFS `cp -Rc` makes the 50 GB `Library` free).
2. Put `PilotProbe.cs` and `PilotProbe.asmdef` in `Assets/PilotProbe/Editor/`.
   The probe is an editor assembly of its own that references nothing of the
   game, so it keeps working whatever Assembly-CSharp does.
3. Start Unity on the copy without a window:
   `Unity -batchmode -projectPath <copy> -logFile <copy>/Logs/batch.log`.
   The probe answers in `Temp/PilotProbe/log.txt`; write a command to
   `Temp/PilotProbe/cmd.txt` (`reload <dll>`, `verify`, `call <Type> <Method>`,
   `refresh`, `quit`).
4. Start `examples/serve` in the copy's root with the references, defines and
   sources of Unity's `Library/Bee/artifacts/*Dbg.dag/Assembly-CSharp.rsp`
   (and the generators' output, which csc writes with `-generatedfilesout`),
   reading its commands from `tail -F $RUSTLYN_SERVE_DIR/cmds.txt` and
   writing to `$RUSTLYN_SERVE_DIR/out.txt`.
5. `reload` the assembly it wrote, `verify` it, then edit a method, wait for
   the rebuild and the reload, and `call` the method (`RUSTLYN_SERVE_DIR` and
   `RUSTLYN_UNITY_PROJECT` point the scripts here at the two).

On a 37 000-file Assembly-CSharp (Unity 2022.3, Apple M5 Pro) an edit runs in
the editor 7.4 s after it is saved — 1.0 s compiling, 6.3 s reloading the
domain — against 53 s through Unity's compile.

## In Pilot

Pilot does all of the below itself, with its own compilation of the project
instead of the daemon (`rustlyn_ide::hot`, through `rln_hot_*`): Unity →
Hot Reload with the project open in Unity. It builds `gend`, `minigen`,
`PilotRuntime` and `libpilotpatch.dylib` once per Unity and these sources,
puts the probe in `Assets/PilotProbe/Editor` (or brings it up to date) and
waits for Unity to compile it, runs the generators, builds the project whole
and reloads the editor on it, and holds Unity's own reloads. Then each save
— in Pilot or on disk — is a patch, a reload where only a whole build carries
the edit, or a word in the editor's Pilot Hot Reload window and Pilot's
status bar. `PILOT_HOT_RELOAD=1` turns it on at launch;
`PILOT_HOT_RELOAD_SELFTEST="<path>|<anchor>"` then saves an edit through the
editor and takes it back. `pilot_fuzz.py` edits files on disk under a running
Pilot and checks what comes of each (`PILOT_FUZZ_PLAY=1`: in Play Mode).

## Hot patches

Unity's own share of a reload on that project is about 6 s whatever compiles
the code (the domain reload, then the asset database categorizing every asset
again), so an edit can be fast only without one. `examples/serve --hot <dir>`
builds the assembly with every member opened to the assembly and
`[InternalsVisibleTo("PilotPatch")]`, and after each change writes
`PilotPatch-<n>.dll`: the changed methods as static methods taking the
instance first, compiled against the assembly just built. The probe's
`hotpatch <dll>` loads it and writes a jump over the start of each old
method's compiled code (`pilotpatch.c`, native, because JIT memory on Apple
silicon cannot be executed while it is writable). An edit to a method body
runs in the editor 1.4 s after it is saved, with no reload.

The library goes beside the probe as an editor plugin, where Unity finds it
for the probe's `DllImport("pilotpatch")`:

    clang -O2 -dynamiclib -arch arm64 -arch x86_64 -o Assets/PilotProbe/Editor/libpilotpatch.dylib pilotpatch.c

While an editor patches it (`hold on`, with a heartbeat file the probe
checks), Unity's own compiles do not reload the domain: the build patches
are measured against stays. Play Mode that would wait for such a reload gets
it — the hold is let go after 3 s — and the patching editor puts its build
back when Play Mode ends.

A patch is cumulative: each one holds everything that differs from the
assembly the editor loaded, so an edit can be undone or changed again, and a
method once patched is patched in every later round. What it covers, each
measured from saving the file to the new code answering in the editor's
process (edits of every kind in a row on a running editor; all about
1.3–1.5 s):

- a changed body — of a method, an accessor, an operator, or `int P => e`;
- a method added, renamed, or given another signature or return type, as
  long as no file the edit did not touch names it (that file's code calls
  the old one); a generic method added;
- a field added: a class keeps it beside each instance, in a
  `ConditionalWeakTable` (`PilotRuntime.cs`); a static one is kept by name;
  an ECS component (`partial` struct) keeps it in a 32-byte tail every
  component is given in the editor's build (`tails.rs`). An object made
  before the patch gets the field's initializer — or what the constructor
  assigns it, with the constructor's parameters read back from where it
  kept them — the first time the field is read;
- a property added: `{ get; set; }` is kept as a field is, one with a getter
  is read through it;
- a constant or an enum member added: written where it is read;
- a type added, nested or not, with every part the generators write for it;
- `base.M()`: the patch calls a member on `PilotRuntime.Base.Of<B>(self)`,
  which rustlyn calls directly rather than through the vtable;
- whatever the source generators write for the edit: `minigen` runs them on
  the edited file alone (with the files its types name, and the ones that
  declare middlewares and injection resolvers, which every system reads),
  in 5–150 ms rather than the 8 s an incremental run over the assembly takes,
  and checked against the full run on 1000 random files with no difference.

Also patched, each checked on a running editor: a static field's changed
initializer and a changed static constructor, run once more when the patch
is applied (the editor's build keeps `initonly` only on a public instance
field, which serializers read, and on the instance fields of a Unity object or
a `[Serializable]` type: an editor reloading writes what its objects hold and
reads it back expecting the fields it wrote, and a build whose readonly
fields are not readonly has fields csc's has not — "The file 'MemoryStream'
is corrupted"); a field added to any struct that
holds a reference, not only to components — the tail is written into the
struct as the daemon reads its file, and what goes where in it is decided
at run time, so `int?` or `DateTime` fit as well as a number; a serialized
field given another type, whose first value is the old one's converted (a
`RectTransform` from a `GameObject`); and a system added to a feature: the
feature's constructor is patched — a struct's chains to nothing — so the
next world runs the system, while in the running one, where the field is
empty, a call through it is skipped (`?.`).

A reload is still needed for a field a JSON loader or another serializer
fills given another type, a class's constructor that does more than give
added fields their values, a change to a generic method or to a member of a
generic type, an interface added to a type, and anything Unity itself has
to see: a new `MonoBehaviour`, or a new serialized field in the Inspector.

How much of real editing that is: `history.py` replays a project's recent
commits each on its own parent — the C# exported from git, the generators
run over the whole assembly, the parent built whole, the commit's files
saved one after another as edits — and the daemon answers each with a patch
or a reload. On the last 300 commits of the project this was measured on,
263 touch Assembly-CSharp. 5 of them do not compile as committed here (one
calls a method that is not there; the others need what a package had
then), which leaves 258: 248 of them, 96%, would have been one patch. Of the 10
left, 8 need what a patch cannot honestly do — a component that turns from
a tag into data, whose storage the running world keeps (3), an interface
Unity checks on the live object (2), a reference added to a struct of
values alone, which would stop being one (2), a JSON model's field given
another type (1) — and 2 are a compiler bug: a type of the base seen as two
in the patch's compilation. A commit holds many saves, so 96% is a floor.

The source list the daemon is given has to hold every file csc compiles,
`AssemblyMonoScriptTypes.generated.cs` of Unity's own generator among them:
Unity finds the class of each script in a scene through the table it holds,
and without it components of the scene come up with their script missing.
The probe's `play` opens the build's first scene and enters Play Mode —
where the game's generic code is instantiated as it runs, which `verify`,
compiling each method once, does not reach.

## Watching a project (`hot.py`)

`hot.py` starts the daemon, waits for the editor, and sends whatever it
finds saved in one look as one round — a file that changes while it reads
is read once it has settled. Its answers, one line each: `✓` patched, `·`
nothing that runs changed (spacing, comments), `✗ does not compile` (a save
in the middle of typing — nothing of it is built, the next save is read
again; the daemon answers such a round `broken`), `⟳` built whole and
reloaded. A file deleted asks for Unity to be quit instead: reloaded in
place, an editor whose objects held the deleted types cannot read back
what it saved of them, with csc's build as much as Rustlyn's. An editor in
the background reloads only once it is in front (`RUSTLYN_WAKE_EDITOR`
brings it there, for scripts).

With `--gatherer` the daemon runs `gend` — the generators over the whole
assembly — for a round that adds or deletes a file or saves many (a branch
checked out): what one file's generators cannot see, such as a feature the
runner lists, is written again. gend keeps each generated file's name across
runs, and starts again when its generators throw. The daemon keeps its
source list in Unity's order (by path, case ignored): a partial type's
fields are laid out in the order of its files.

## Testing

- `fuzz.py` with `examples/mutate`: random files of the game edited as a
  person would — a log line, a number or string, a method, field, property,
  nested (generic) type, lambda, local function, coroutine or async method
  added and used, a condition turned round, a method copied, removed or
  given a parameter, spacing, a half-typed save — through the daemon into
  the editor and back, with a whole build JITted every so often;
  `RUSTLYN_FUZZ_PLAY` keeps the game running in Play Mode and reads the
  editor's log for what only broken code makes the runtime say;
  `RUSTLYN_NO_EDITOR` runs it on the daemon alone.
- `checkout.py`: older commits checked out under the running editor and
  back, files added and deleted.

