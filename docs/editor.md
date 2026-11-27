# Rustlyn in an editor

A compiler and an editor want different things from the same code. A compiler is asked
one question about all of the code, and the answer may take as long as it takes. An
editor is asked a question per frame, about what is on screen, and has sixteen
milliseconds. One analysis serves both only if it can stop early, start in the middle,
and avoid redoing work. `rustlyn-ide` is exactly that: the compiler's layers arranged so
that each answers before the next one starts working.

## Layers

1. **Open.** Bytes to text. No parsing, no lexing: the file is on screen before
   anything about it is decided.
2. **Colour.** The lexer, over the visible lines and only those. The obstacle is that a
   token's meaning depends on the text above it: `*/` closes a comment only inside a
   comment, and a line is live code only if its `#if` branch is taken. All of that fits
   in three fields, so it is a `LexerState` the lexer hands out and takes back, and the
   layer keeps one every five hundred lines. Colouring a window means resuming from the
   nearest checkpoint above and lexing down to it. On a 200,000-line file the first
   screen takes 149 µs, scrolling 257 µs, a full warm-up (in the background) 715 ms,
   and any jump after that 178 µs.
3. **Parse the file.** The parser, plus everything it knows about a declaration: type,
   parameters and how they are passed, bases, attributes. In one pass, because a second
   would be needed by the layer above.
4. **Project index.** The same declarations across all files, on all cores, and name
   resolution by the scope at the reference site, as C# does it but without binding
   anything. Where the scope does not decide, all candidates are returned: picking one
   for the reader would silently send them to the wrong place. 5,000 files and 100,000
   lines on four cores: 512 ms cold, 100 ms from the next launch, 84 ms after saving
   one file, 60 ns per name resolution.
5. **Decompile.** An assembly's surface from its tables immediately; one method's IL,
   with resolved names, when asked.
6. **Understand.** The whole project compiled against its real references, and the
   editor's questions about it: where the thing under the cursor is declared (the
   overload a call picked, the member `var` got from its value, a row in an assembly
   for an assembly member), where it is used (the symbol, not the word), and what can be
   written here (the members of the type left of the dot together with visible
   extensions, or everything in scope).

Every layer is a pure function of the file's bytes, so they all share one cache and one
question before working: did the inputs change? First `stat`: length and modification
time, without reading. If those moved, the file is read and hashed, and **a matching
hash counts as unchanged**: `git checkout` there and back rewrites timestamps on files
whose content is the same, and that should cost a read, not a reparse. Then the cache
directory from the previous run. Only then the work.

## What to compile

A compiler is told by its command line; nobody tells an editor, and language servers ask
MSBuild, hence their minute before the first answer. `project.rs` reads what MSBuild
would read itself: `.sln`/`.slnx`, `.csproj` in both formats (references from
`HintPath`, `DefineConstants`, target framework, old-style `<Compile>`, shared
`.projitems`), `obj/project.assets.json` with transitive NuGet packages,
`packs/Microsoft.NETCore.App.Ref` of the installed .NET, and the symbols and
`global using`s the SDK would add for `ImplicitUsings` and `<Using>` (with `Alias`,
`Static` and `Remove`), including from `Directory.Build.props` and
`Directory.Build.targets` above an SDK project and what they import through
`$(MSBuildThisFileDirectory)`. A condition like `'$(TargetFramework)' == '…'` is
compared with the project's framework; anything not understood counts as false. A Unity
project without project files is assembled from the editor it was opened with
(`Library/EditorInstance.json`), its packages and plugins. All of this takes
milliseconds; a miss is possible only where MSBuild would have computed something, and
it costs an unresolved name, not a broken project.

### Unity projects

A Unity project is compiled the way Unity last built it, not the way its `.csproj` files
say (they lag behind the branch). Assemblies and their files come from
`.asmdef`/`.asmref`, the predefined `Assembly-CSharp*`, and `Editor` and `Plugins`
folders; folders ending in `~` are skipped. Each assembly's symbols and references come
from its `.rsp` in `Library/Bee` (including engine DLLs and plugins that are in no
project); the language is C# 9. Package scripts from `Library/PackageCache` are compiled
for the assemblies Unity built; test assemblies without an `.rsp` are not.

It is all one compilation, but each assembly sees only what it references: other
projects; `internal` members of references only through `[InternalsVisibleTo]` (the
assembly name compared case-insensitively, as in .NET); of two DLLs with the same type,
the one in its `.rsp` (Burst carries its own copy of Cecil next to the shared one). A
type with the same name in two projects is not a duplicate. Unity's built copy of an
assembly (`Library/ScriptAssemblies/*.dll`) that is compiled here from source is not
treated as a reference. Warnings follow `-warn:`/`-nowarn:` from the `.rsp` or the
project's `<WarningLevel>`/`<NoWarn>`: Unity builds packages with `-warn:0`, so they
have no warnings. `[Obsolete]` is read from assemblies too.

On a large production Unity project (45,510 files including packages) there are no
false errors and 44 unresolved names, all of them members of `dynamic`; of the 5,505
warnings Unity's own compilation reports, 5,198 match, and none are extra.

### Unity source generators

Unity runs its source generators itself on every script compilation and leaves their
output for the compiler: in the folder named by `-generatedfilesout:` in the `.rsp` from
`Library/Bee`, and in `Temp/GeneratedCode`. Rustlyn adds all `.cs` files from there to
the compilation, so go to definition, references and completion work on them. Text
written for several assemblies is taken once, and never edited: `rln_is_generated` tells
the editor to open such a file read-only, no edit (rename, light bulb, Fix All) goes into
it, and something declared only there cannot be renamed, as in Roslyn. Freshness is
Unity's: new generated code appears after Unity recompiles scripts.

## The compilation

**One compilation per project**, declarations without bodies, built in the background
and replaced whole; trees of unchanged files carry over as they are. Bodies are bound on
demand, one at a time, and kept in a cache: a question about the method under the cursor
binds it once. For this `Compilation` is shared between threads (its caches are behind
locks, not in `RefCell`), and find references runs on all cores: first by spelling
(cheap, and discards almost everything), then binding only the bodies where the word
was found.

**An edited file** is queried with its current text, while the compilation is from the
last save. `Speculation` maps one onto the other: between edits the text is the same,
only shifted. Lines are re-matched after each change, changed lines are trimmed by their
common prefix and suffix, and everything enclosing the edit (the method, its class, the
namespace) is the same declaration as in the compiled tree, at a shifted offset. A
declaration whose end the edit moved (a field initializer or accessor cut off mid-word,
into which the following lines slid) is found by its start, so a setter keeps its
`value`. So the method being edited is bound on top of the compilation as is, however
many places in the file changed since the save: a just-declared variable already
completes, and a declaration below the edit is found where it is now. Syntax inside the
body (lambdas, which binding returns to by their nodes) is looked up in the tree of the
edited text, not the compiled one.

**A lambda in a call that does not resolve yet** is bound anyway, as Roslyn does "for
error recovery": in `list.Select(e => e.)` the body does not say what `Select` returns,
but `e` is the element of `list` as type inference saw it when it asked the lambda; in a
call missing arguments, it gets the delegate type the candidate expects in its place. A
parameter whose type only a not-yet-written argument would tell (`(context, state) =>`
before the `state` argument) stays untyped while the rest get theirs; a lambda returned
by a lambda (`h => (sender, e) =>`) becomes the delegate the outer one would return. A
type parameter of the method the call is written in is an ordinary type: the lambda does
not become it, and `Split(source, item =>` is not `Split(source, separator)`. Contents
of untyped `new(…)` and `[…]`, and `: base(…)` arguments, are bound the same way, so
`Add(new(key, [.. items.Where(x => x.` completes while typing. After a dot, completion
offers `object`'s members for a class with no base, what a type parameter's constraints
promise, and a tuple's `Item1`/`Equals`; the cursor between dots in `p.‸.Name` (a
deleted name, which the lexer sees as `..`) is still a member of `p`, as is `p.Ag` with
the next line slid into it (`p.Ag other = 1;` parses as a declaration).

On the Roslyn compiler sources (2,090 files, 700,000 lines, 167 .NET 10 assemblies):
compilation takes 4 s, a recompilation reusing trees 3 s, about 1.2 GB; go to
definition finds a target for 99.4% of identifiers (99.7% excluding `_`, `nameof` and
tuple element names at their declaration, which refer to nothing), 0.4 ms on average;
find references across the whole project averages 0.2 s, 1.3 s at worst; completion
after a dot is non-empty in 99.3% of cases, 3 ms on average. A third of the remaining
misses are namespaces from assemblies, which have no declaration to go to, and as many
again are `CodeAnalysisResources`, a class the build generates from `.resx` and that is
not in the sources. To run it yourself:

```sh
find src -name '*.cs' | cargo run --release -p rustlyn-ide --example semantic -- <project root>
```

**The compilation survives the process.** `rln_save_compilation` writes it to disk: the
symbol table, indexes, file texts, and what it was built against (the project, assembly
stamps, the Rustlyn build itself). `rln_load_compilation` reads it back without parsing
trees: declarations are already in the symbol table, and a file's tree is needed only
when asked about, at which point it is parsed from the same text under the same symbols,
hence with the same offsets. The first `rln_compile` after loading checks the project,
texts and assemblies and, if nothing changed, returns `unchanged` and keeps what was
loaded. On Roslyn: a 57 MB snapshot, 0.7 s to write, 0.8 s to read instead of 4 s to
compile, 8 ms to check. A snapshot from a different Rustlyn build is not read: the symbol
table format is not stable between builds.

## What the editor shows next to the code

* `rln_diagnostics`: the file's errors as it is in the editor: syntax of the edited
  text, what type declaration reported (carried across the edit), and what binding each
  body finds. On the Roslyn compilers, the same 310 diagnostics as a full `bind` run, at
  15 ms per file.
  Among the IDE analyzers are the thread diagnostics: RLN1001 (a field two threads touch
  with nothing between them), RLN1002 (Unity's main-thread API off the main thread) and
  RLN1003 (a local every `Parallel.For` iteration writes). They report only where two
  accesses can overlap: a task or thread started and not waited for, an `async void`
  method or an async call nobody awaits, two iterations of a parallel loop. The code
  after an `await` is the same flow as the code before it. A wait (`await`, `Wait`,
  `Result`, `Join`, `WaitAll`, `WhenAll`, a gate such as `ManualResetEventSlim` or a
  `TaskCompletionSource`) orders what follows it; a lock held on both sides excludes
  (`lock`, `Monitor`, `SemaphoreSlim`, `Mutex`, `SpinLock`, `ReaderWriterLockSlim`);
  `arr[i]` with the loop's own index is an element of its own. What the analysis cannot
  tell, such as a lock a caller holds or an ordering a protocol between methods gives, it
  does not report.
* `rln_signatures`: overloads of the call being typed, the matching one and the
  parameter under the cursor, including for a call that does not bind yet (then the
  methods are asked of the type left of the dot).
* `rln_documentation`: `///` from source or the XML file next to an assembly, as plain
  text, under the symbol's signature as it is at that spot: `int Key` for
  `IGrouping<int, Item>`, `Select<Item, string>` with inferred arguments, `var` as
  `Dictionary<string, int>`, an anonymous type as `new { string Title, int Twice }`.
  Members in after-dot completion are labelled the same way.
* `rln_selection_ranges`: ever larger pieces of syntax around the selection, with the
  contents of brackets, blocks and strings as separate steps; parse-only, so it works
  before compilation.

## Completion, as Roslyn's `CompletionService`

The context is determined by the token before the word being typed, not by the node the
parser put the half-written word in, and then that context's providers run. Keywords are
only those the grammar allows there (`await` in `async`, `break` in a loop, modifiers
not already written). After `new`, in a declaration, in `typeof(`, in a base list: types
only, with the expected type preselected (`List<int> xs = new` → `List<int>`); where an
enum is expected, `Color.Red`. No instance members in a static member; attributes
without the `Attribute` suffix in `[`; namespaces after `using`. `override` writes the
whole member with a `base` call, `partial` the unimplemented partial methods; in a call,
`name:` for unnamed parameters; in `new C { }`, members not yet assigned. Types and
extension methods from namespaces not imported come with a `using` inserted in order.
There are `///` tags, directives after `#`, snippets (`cw`, `prop`, `ctor`) and names
for a new variable from its type. All of this is `rln_completions_ex` (the older
`rln_completions` is unchanged); an item's description is `rln_completion_description`,
and whether to open the list on a typed character is `rln_completion_trigger`.

## Refactorings with a dialog

What Visual Studio does through a window is two functions here: one says what to show
(`rln_signature_info`: the method's parameters; `rln_dialog_members`: the type's
members, which are preselected, a suggested name, base types), the other does what was
chosen: change signature (`rln_change_signature`: the declaration, overrides and
implementations, `<param>` in documentation, and every call across the project:
positional and named arguments, `params`, extension `this`, `base(...)`), extract
interface and base class, pull members up, generate overrides, move static members to
another type. The answer is per-file edits, a new file being an edit to a file that does
not exist yet; a refusal is not an error but a reason in `refused`.

The light bulb has the same refactorings with default choices ("Extract interface...",
"Pull 'M' up to 'Base'", "Generate overrides..."), and next to them: introduce parameter
(three ways to keep calls working), inline method, "Make static", primary constructor,
`record`, tuples instead of anonymous types, `foreach` to LINQ and back, and the style
suggestions Roslyn shows as hidden hints: `??`, `??=`, `?.`, `throw` expressions,
pattern matching, `^1`, `[..]`, collection expressions, `out int x`, deconstruction. Each
is checked by the compiler: a test applies everything offered anywhere in three sample
files and compiles the result together with any created files.

## Everything Roslyn does for an editor, except building

Every service of Roslyn's language server, and of what Visual Studio does on top of it,
is here as an `rln_*` call. All work on the text as it is in the editor, and the
syntactic ones work before compilation.

| Roslyn | Rustlyn |
|---|---|
| Classification (syntactic and semantic) | `rln_classify`, `rln_semantic_tokens`: class, struct, interface, extension method, static member, reassigned variable, `[Obsolete]` |
| Diagnostics, IDE analyzers, `.editorconfig` | `rln_diagnostics`: compiler errors and warnings (CS0535, CS0161, CS1061, CS0168, `#pragma`…), IDE0001-IDE0090 and IDE1006 with "unnecessary"/"deprecated" tags, severity from `.editorconfig`; `rln_editorconfig` |
| Code fixes, refactorings, Fix All | `rln_code_actions`, `rln_fix_all`: add `using`, fix a typo, implement an interface or abstract class, generate method/property/field/constructor/type, populate `switch`, make `async`; introduce variable, extract method, inline, invert `if`, `var`, expression bodies, interpolation, `for`↔`foreach`, `switch` expression, constructor and `Equals`, encapsulate field, sort `using`s, move type to file, namespaces, arguments, initializers, patterns, LINQ… |
| Change Signature, Extract Interface/Base Class, Pull Members Up, Generate Overrides, Move Static Members | `rln_signature_info`, `rln_dialog_members` and `rln_change_signature`, `rln_extract_interface`, `rln_extract_base_class`, `rln_pull_members_up`, `rln_generate_overrides`, `rln_move_static_members` |
| Completion | `rln_completions_ex`, `rln_completion_description`, `rln_completion_trigger`, `rln_completion_filter` |
| Signature Help, Quick Info | `rln_signatures`, `rln_quick_info`, `rln_documentation` |
| Go to Definition / Type Definition / Base / Implementation, Find Derived | `rln_definition_in`, `rln_type_definition`, `rln_bases`, `rln_implementations_in`, `rln_derived_types` |
| Find All References, Document Highlights, CodeLens | `rln_references_detailed` (write/read, where, line; cascades over the member family), `rln_highlights` (keywords included), `rln_code_lens` (the same cascade over sources: a call through an interface or base method counts as a use of implementations and overrides) |
| Rename | `rln_prepare_rename`, `rln_rename`: the family of overrides and implementations, constructors, attributes, `nameof`, `cref`, file, conflicts with rebinding |
| Call Hierarchy, Type Hierarchy | `rln_call_hierarchy`, `rln_incoming_calls`, `rln_outgoing_calls`, `rln_type_hierarchy`, `rln_supertypes`, `rln_subtypes` |
| Navigate To, document symbols | `rln_search` (PatternMatcher: prefix, camel humps `GTD`, substring, fuzzy), `rln_outline` |
| Inlay Hints | `rln_inlay_hints`: parameter names with Roslyn's suppressions, types of `var`, lambdas, `new()` |
| Formatting, smart indent | `rln_format_document`, `rln_format_range`, `rln_format_on_type` (`;`, `}`, `{`, newline), `rln_indentation_for_new_line` |
| Block structure, brace matching, extend selection | `rln_block_structure`, `rln_brace_match`, `rln_selection_ranges` |
| `///` templates, comment/uncomment | `rln_doc_comment_on_typed`, `rln_doc_comment_on_enter`, `rln_insert_doc_comment`, `rln_toggle_line_comment`, `rln_toggle_block_comment` |
| Metadata as Source | `rln_assembly_text`, `rln_method_body` |

Where behaviour differs from Roslyn in details, the documentation of the module that
implements it says so.

## The C ABI

`rustlyn-ffi` is the boundary for code not written in Rust: a panic never crosses it, a
null is rejected rather than dereferenced, and whatever Rust allocated, Rust frees. A
list result comes in one piece, an array of structs next to a single UTF-8 blob, not one
allocation per string. The header
[`crates/rustlyn-ffi/include/rustlyn.h`](../crates/rustlyn-ffi/include/rustlyn.h) is
written by hand, because it is read more often than it is edited; it is checked by
[`crates/rustlyn-ffi/tests/run.sh`](../crates/rustlyn-ffi/tests/run.sh), a C program that
includes the header, links against the real library and calls through it. A test written
in Rust would only check the library against itself.

The host application this was built for is a native macOS code editor that uses
Rustlyn for highlighting, outline, the index, assemblies and, through `rln_compile`,
`rln_definition_in`, `rln_references` and `rln_completions`, everything it used to ask
Roslyn's language server for.

## Hot reload

`rustlyn-ide` also contains a hot-reload path for Unity projects: on each save it
compiles the changed code and sends a patch to a running Unity editor. The
`rustlyn-ide` examples `hot` and `stubs` drive it from the command line, and the
Unity-side pieces live in [`tools/unity`](../tools/unity).
