# What works

This page is the long form of "What it does" in the [top-level README](../README.md):
how each part of the compiler is checked against real code, and what each part
supports.

## Validation on Roslyn's own sources

### Parsing

The front end is full-fidelity: lexer, green/red tree and a parser for the whole
language.

```rust
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

let source = SourceText::new("Program.cs", "var x = a is > 0 and < 10;\n");
let tree = parse(source.clone());

assert!(!tree.has_errors());
assert_eq!(tree.text(), source.text()); // byte for byte
```

Checked on **18,224 source files of Roslyn itself**: the tree reproduces the source
verbatim in 100% of cases, and 99.7% of files parse with no diagnostics at all. The
rest is not C#: generated Razor with expressions split by `#line`, Visual Studio
templates with `$rootnamespace$` in place of a name, one Visual Basic file with a
`.cs` extension, deliberately broken preprocessor tests, and an `#error` in the branch
a build without `/define:` picks.

### Binding

Parsing answers "can we read it?". The next question is "do we understand it?", and
the binder sweep answers it on the same sources: the 2,242 files of the Roslyn
compiler itself (`Compilers/Core/Portable` with `Core/AnalyzerDriver`,
`Compilers/CSharp/Portable` with `CSharp/CSharpAnalyzerDriver`, and
`src/Dependencies`) bind against a real `Microsoft.NETCore.App` 10.0 in about half a
minute, and against .NET 11 rc1 (the version Roslyn itself targets) **none of them
produces a single diagnostic**. Against .NET 10 a few calls to API that does not exist
there remain (such as `LayoutKind.Extended`): a runtime version issue, not a binder
gap. A histogram of what actually breaks is a better plan than a list of missing
features ranked by guesswork.

It is 2,242 files rather than 2,240 because two have to be generated first.
`CodeAnalysisResources` and `CSharpResources` are classes that are not in the sources:
the real build produces them from `.resx` with a generator from a NuGet package, and
without them 287 references across the corpus hit a missing name. That is a missing
piece of the input, not a compiler gap, so it is put back rather than subtracted:

```sh
R=roslyn/src/Compilers
cargo run --release -p rustlyn-semantics --example resx -- Microsoft.CodeAnalysis \
  $R/Core/Portable/CodeAnalysisResources.resx > generated/CodeAnalysisResources.cs
cargo run --release -p rustlyn-semantics --example resx -- Microsoft.CodeAnalysis.CSharp \
  $R/CSharp/Portable/CSharpResources.resx > generated/CSharpResources.cs

# The same /define: symbols the SDK passes for net10.0: without them a file takes
# the branch nobody builds.
DEFINES='NET;NETCOREAPP;NET10_0;NET10_0_OR_GREATER;NET9_0_OR_GREATER;NET8_0_OR_GREATER;NET7_0_OR_GREATER;NET6_0_OR_GREATER;NET5_0_OR_GREATER;NETCOREAPP3_1_OR_GREATER;NETCOREAPP3_0_OR_GREATER;NETCOREAPP2_2_OR_GREATER;NETCOREAPP2_1_OR_GREATER;NETCOREAPP2_0_OR_GREATER;NETCOREAPP1_1_OR_GREATER;NETCOREAPP1_0_OR_GREATER'
corpus() {
  find $R/Core/Portable $R/Core/AnalyzerDriver $R/CSharp/Portable $R/CSharp/CSharpAnalyzerDriver \
       roslyn/src/Dependencies -name '*.cs'
  ls generated/*.cs
}

corpus | cargo run --release -p rustlyn-semantics --example bind -- \
    $DOTNET/shared/Microsoft.NETCore.App/10.0.12 --define "$DEFINES" --verbose
```

A diagnostic is the binder admitting it did not understand something. The other half
is expressions whose type came out `?` in a file that bound with no diagnostics: the
backend meets those as a type it cannot write down, and nothing in the diagnostic
histogram points at them.

```sh
corpus | cargo run --release -p rustlyn-semantics --example untyped -- \
    $DOTNET/shared/Microsoft.NETCore.App/10.0.12 --define "$DEFINES"
```

### Emitting IL

The same question for the back half of the compiler ("can we tell the machine what to
do with it?") has a separate answer: a file can bind with no diagnostics and still
produce no instructions. It is measured the same way:

```sh
corpus | cargo run --release -p rustlyn-emit --example coverage -- \
    $DOTNET/shared/Microsoft.NETCore.App/10.0.12 --define "$DEFINES"
```

The corpus has 61,228 method bodies (state machines counted separately), and
**99.99% of them compile to IL**: 2 do not (the run takes about a minute; `--dump path`
writes each failed body with its reason). Both are async enumerables: an `async`
iterator returning `IAsyncEnumerable<T>`, and an `async` lambda whose variable is
captured by a lambda inside it. The corpus is built against .NET 11 rc1, the version
Roslyn targets (.NET 10 lacks `LayoutKind.Extended` and a couple of neighbouring APIs).

### Roslyn compiled by Rustlyn

The `assemble` example puts the whole corpus into one `Roslyn.dll` (10.6 MB, three
bodies replaced by stubs that throw `NotImplementedException`), together with the
strings from `.resx`: `--resource Ns.Class=file.resx` embeds them as `.resources`, so
the `ResourceManager` inside Roslyn finds the diagnostic texts. The assembly loads, and
the compiler it contains **compiles and runs a program**: `CSharpCompilation.Create`
→ `GetDiagnostics` (zero errors, and where there are errors, with their text) → `Emit`
produces an assembly in which `C.M(41)` returns 42 and `C.Greet("roslyn")` returns
`hi roslyn`. A program with LINQ, lambdas, an iterator, a `switch` expression and
interpolation also compiles and runs.

This was reached by running the built Roslyn under .NET and fixing errors in our IL one
by one. ILVerify over `Roslyn.dll` went from 9,282 findings to about three hundred
(including the unsafe `XxHash`); the rest are mostly pointers, `null` for a type
parameter, and `conv.u` over a pinned reference, which csc itself also produces.

Beyond that the self-build reached a fixed point: the Roslyn built by Rustlyn compiles
all 2,243 files of its own source into `Roslyn2.dll`, which compiles the corpus again
into the same bytes (`Roslyn2 == Roslyn3`, zero lines of IL difference) and does so
deterministically. The driver is [`tools/selfhost/drive.cs`](../tools/selfhost/drive.cs).
See the [roadmap](roadmap.md) (milestones 122-136) for the steps.

## Trying it yourself

```sh
find /path/to/roslyn -name '*.cs' | cargo run --release -p rustlyn-syntax --example fidelity
cargo run -p rustlyn-syntax --example dump -- Program.cs          # parse tree
cargo run -p rustlyn-semantics --example symbols -- Program.cs    # symbol table
cargo run -p rustlyn-semantics --example typecheck -- Program.cs  # unresolved types
cargo run -p rustlyn-semantics --example typeof -- Program.cs     # type of every expression
cargo run -p rustlyn-semantics --example bound -- Program.cs      # bound tree
cargo run -p rustlyn-interpret --example run -- Program.cs        # run the program
cargo run -p rustlyn-emit --example build -- Program.cs out/      # build a .NET assembly
dotnet out/Program.dll                                            # and run it
cargo run -p rustlyn-emit --example build -- Program.cs out/ --source Other.cs \
    --langversion 9 --main N.Program --checked --define TRACE     # csc-style options
cargo run -p rustlyn-metadata --example dump -- out/Program.dll   # read its metadata
cargo run -p rustlyn-metadata --example disasm -- out/Program.dll # and its IL
cargo run -p rustlyn-decompile -- out/Program.dll [Type[::Method]] [--references $FW]  # and C# back from IL
cargo run -p rustlyn-semantics --example load -- $DOTNET/shared/Microsoft.NETCore.App/8.0.11
```

## Components

### Lexer

All C# tokens and operators (maximal munch, including `>>>=`), reserved and contextual
keywords, identifiers with `@` and `\uXXXX`, numeric literals in every base with
suffixes and type inference per §6.4.5.3, regular, verbatim, raw (`"""`) and
interpolated strings, surrogate pairs, the `u8` suffix, comments including doc
comments. An interpolated raw string is lexed into a token stream, so a hole can hold
another raw string: `$$"""{{s.Replace("""a""", """b""")}}"""`.

### Preprocessor

`#if`/`#elif`/`#else`/`#endif` with condition evaluation, `#define`/`#undef`,
`#region`, `#pragma`, `#nullable`, `#error`/`#warning`, `#!` and `#:` from C# 14
file-based programs. Disabled branches are kept as `DisabledTextTrivia`.

### Parser

Namespaces (block and file-scoped), classes, structs, interfaces, records, enums,
delegates, every kind of member, attributes, type parameters with constraints; all
control flow, local functions, deconstruction; the full expression precedence table,
lambdas, patterns, `switch` and `with` expressions, LINQ queries, collection
expressions, ranges, function pointers (`delegate* unmanaged[Cdecl]<int, void>`), the
C# 13 `allows ref struct` constraint, C# 14 extension blocks.

### Symbols

The declaration table: namespaces and partial types merge across files, arity is part
of a type's identity (`C`, ``C`1``, ``C`2``), members get metadata names (`.ctor`,
`op_Addition`, `this[]`), a delegate carries its signature on `Invoke`. Without
references, the core library (`System.Object` and the rest) is compiled from a
synthesized source by the same pass; with references, it is read from the real
assemblies (below).

### Bound tree

What the binder turns syntax into: every node already has a type, a symbol and a
conversion kind. `a.b(c)` in syntax is text; in the bound tree it is a specific
method, argument types, and boxing where needed. The backends no longer look at
syntax, so a binder decision cannot accidentally be made a second time differently.

### Binder

Name lookup through the scope chain with `using`, aliases and `global using`; types:
arrays, pointers, tuples, `Nullable<T>`, constructed generics with substitution
(`List<string>.this[int]` yields `string`); method bodies: locals with `var`
inference, pattern and `out` variables, lambda parameters, overload resolution,
implicit conversions and numeric promotions.

```rust
use rustlyn_semantics::Compilation;

let compilation = Compilation::from_source("class C { void M() { int x = \"text\"; } }");
let errors: Vec<_> = compilation
    .semantic_diagnostics()
    .iter()
    .map(|entry| compilation.render(entry))
    .collect();
assert_eq!(errors, ["Program.cs(1,30): error CS0029: Cannot implicitly convert type 'string' to 'int'"]);
```

### Language versions

`ParseOptions::with_language_version` (`/langversion:`, default latest, C# 15) and
`CompilationOptions` (`/main:`, `/checked`, `/optimize`, `/unsafe`). The binder follows
the named version wherever Roslyn checks `LanguageVersion`: before C# 10 lambdas and
method groups have no natural type; before C# 12 a `ref` argument does not go to an
`in` parameter; `[OverloadResolutionPriority]` is C# 13; `field` in an accessor is the
property's backing field from C# 14 (a plain name before); and from C# 14 spans are
part of the language: arrays, spans and strings convert implicitly to spans
(covariantly via `CastUp`), that conversion beats any other, `ReadOnlySpan<T>` beats
`Span<T>`, the span element is inferred from an array, and an extension method
receiver takes that conversion. `file` types are visible only in their file and are
named `<File>F<SHA-256 of path>__Name` in metadata.

### Interpreter

Walks the same bound tree as the code generator. That is the point of having two
backends: they agree because they were told the same thing, not because each was
carefully tuned to the same answers. A test runs the same program both ways and
compares outputs. Supported: classes, inheritance with virtual dispatch, constructors
with `: base(...)`, auto and computed properties, static fields, all control flow,
arrays and `List<T>`, strings and interpolation, recursion, exceptions with
`try/catch/finally`. It does not resolve names, members or overloads itself: it reads
the binder's decisions.

```rust
let output = rustlyn_interpret::run(r#"
    using System;
    class Program
    {
        static int Fib(int n) => n < 2 ? n : Fib(n - 1) + Fib(n - 2);
        static void Main() => Console.WriteLine($"fib(10) = {Fib(10)}");
    }
"#)?;
assert_eq!(output, "fib(10) = 55\n");
```

### Code generation

A real .NET assembly: PE file, CLI header, ECMA-335 metadata (`#~`/`#Strings`/`#US`/
`#GUID`/`#Blob` heaps, tables, signature blobs) and IL. Highlights:

* classes, structs, interfaces, enums; virtual and interface dispatch; field
  initializers, `: base(...)` and `: this(...)`, auto-properties with backing fields,
  static constructors;
* all control flow, both forms of `switch`, patterns; records with the value equality,
  `ToString`, `GetHashCode` and `Deconstruct` the language provides; user-defined
  operators;
* real `ref` and `out` (by-ref signatures, `ldind`/`stind`) for locals, parameters,
  fields and array elements; `try`/`catch`/`finally` with `when` filters, both forms
  of `using`;
* `foreach` over anything with `GetEnumerator`/`MoveNext`/`Current` found by name, as
  C# does, with the enumerator disposed in `finally` however the loop ends;
* generics: a signature never names a type parameter (`!0`), a constructed type gets a
  `TypeSpec`, a member of a constructed type a `MemberRef` under it with the
  *definition's* signature; generic methods are `!!0` in the signature and a
  `MethodSpec` at the call, with type arguments inferred (`Echo(3)` is `Echo<int>`);
* properties as two methods, each accessor with a body getting its own symbol (like
  Roslyn's `GetMethod`/`SetMethod`), so `set { ... }` sees `value` and user indexers
  work (`get_Item`/`set_Item`, with `string`'s accessor named `get_Chars` from its
  `DefaultMember`);
* lambdas bound only once the target delegate says what they take; delegates with no
  IL of their own (`Invoke` and `.ctor` are provided by the runtime), method group
  conversions, and `ldvirtftn` for virtual targets;
* `const` and enum members as metadata literals, so `Console.WriteLine(Colour.Green)`
  prints `Green`; `.maxstack` is computed, not guessed.

It is checked the only way that can be trusted, by running on real .NET:

```sh
cargo run -p rustlyn-emit --example build -- Program.cs out/
dotnet out/Program.dll
```

### Metadata reader

The same ECMA-335 that `rustlyn-emit` writes, read from the other end: PE headers, the
`#Strings`/`#US`/`#Blob`/`#GUID` heaps and every table in §II.22, including those the
emitter does not write, because rows are packed and a wrong width for one table shifts
every table after it. It reads its own output and real assemblies:
`System.Private.CoreLib.dll` (12 MB, 2,468 types, 33,838 methods) in half a second.
Whatever the emitter writes, the reader must read back and agree with; tests check this.

### Disassembler

Method bodies back into instructions: both header formats, every §VI opcode (including
the two-byte `0xFE`-prefixed ones) and the exception handler table. Operand widths are
load-bearing: IL has no separators, so a wrong width does not skip an instruction, it
lands in the middle of one, and everything after decodes wrongly. So the check is the
entire .NET 8 runtime. Signatures are read the same way and checked the same way:

```sh
cargo run --release -p rustlyn-metadata --example sweep -- .../shared/Microsoft.NETCore.App/*/*.dll
```

On the .NET 8 shared framework: 115,850 bodies, 2,555,335 instructions, 5,525 methods
without a body, 276,115 signatures, 0 that failed to decode.

### Decompiler

`rustlyn-decompile` is an ILSpy counterpart: meaningful C# from an assembly, not an IL
listing.

* The evaluation stack is replayed symbolically (each instruction leaves an expression,
  not a value). Blocks fold into `if`/`while`/`do`/`for`/`switch`/`try` from the shapes
  compilers lay out (a forward branch over a range is `if`, a backward one a loop, an
  exception table range is `try`).
* Idioms fold back: temporaries into expressions, `get_X` into properties,
  `op_Addition` into `+`, `string.Concat` with literals into `$"..."`, an enumerator
  loop with `Dispose` in `finally` into `foreach`, `Dispose` without a loop into
  `using`, `Monitor.Enter/Exit` into `lock`, `isinst` plus a null check into
  `o is T x`, `(x != null) ? x : y` into `x ?? y`, if/else assignments into a ternary,
  exception filters into `catch (T e) when (…)`, field stores before the base
  constructor call into field initializers, trivial accessors into `{ get; set; }`.
* Locals are named by type and by where the value came from (`num`, `text`,
  `enumerator`, `name` for an element of `names`) and declared at first assignment.
  `ref`/`out` are recovered from definition signatures. What does not fold into
  structure stays an honest `goto IL_xxxx` rather than a guess.
* Compiler-generated code folds back: closure classes into lambdas and local functions
  with captured variables (including nested ones and loop-variable captures), iterator
  and `async` state machines into `yield return`/`yield break` and `await` with the
  original `try`/`finally`/`using` around them, `<>9__` delegate caches into the
  delegate; the `<>c__DisplayClass`/`<M>d__N` types themselves are hidden.
* With `--references <dir>` (or `RUSTLYN_FRAMEWORK`) it looks into the assemblies the
  input references: extension calls print as `xs.Where(...)`, `out` is recovered for
  foreign methods too, default arguments are omitted, enum constants and `bool`
  arguments get names (`ConfigureAwait(continueOnCapturedContext: false)`).
* Modern C# folds too: records into `record Point(int X, int Y)` without the generated
  members, `<Clone>$` plus `init` into `p with { Y = 5 }`; `<name>P` fields into
  primary constructors; string `switch` from all three shapes Roslyn lowers it to
  (binary search on `ComputeStringHash`, switch on length and character, an
  `if (s == "a")` chain); `await` in `finally` back into `finally`, and with
  `DisposeAsync` into `await using` and `await foreach`; async iterators; pinned
  references into `fixed (char* p = s)`; `p + i * sizeof(T)` into `p[i]`; attributes
  with arguments (`[Header("Movement")]`, `[Range(0f, 1f)]`, `typeof`, enums);
  `required`, `static abstract`, `>>>`, `new T()`, `const decimal`.
* A type with its own `==` (like `UnityEngine.Object`) gets reference comparisons as
  `(object)a == b` and `x is null`; a name present in two used namespaces (`Object` in
  `System` and `UnityEngine`) is written in full, and only the needed `using`s remain.
  Debug builds (no `-optimize`, as the Unity editor produces) read as well as optimized
  ones.

It is tested on output from both Rustlyn and Roslyn (`tests/fixtures/roslyn_*.dll` in
`crates/rustlyn-decompile` are built by `csc`; the same source compiled by Rustlyn must
read the same). The two compilers lay out the same constructs differently (Roslyn jumps
to the loop condition at the end, Rustlyn tests it at the top; Roslyn branches directly,
Rustlyn materializes a `bool`), and the decompiler must recognize both. The entire
.NET 11 `System.Private.CoreLib` (12 MB, 462 thousand lines of C#) decompiles in
2 seconds without a crash.

Round trips are the other check. A corpus is built by `csc` in both modes, decompiled
and compiled again; the `roslyn_modern.cs` fixture keeps this in the tests. .NET 8
runtime assemblies are decompiled whole and compiled again against the implementation
assemblies: `System.Collections.Specialized`, `System.Collections.NonGeneric`,
`System.Collections.Concurrent`, `System.ComponentModel.Primitives`,
`System.ObjectModel`, `System.Memory`, `System.Text.Encodings.Web` and
`System.Web.HttpUtility` compile with no errors; `System.Collections`,
`System.Text.RegularExpressions` and `System.Threading.Channels` have one or two each.
For that the decompiler inserts the casts C# requires and IL does not write (on
assignment, return, arguments, tuples and indices, unsigned and `checked` operations,
enums, `bool`/`int`, pointers and `nint`, explicit interface implementation calls).

### Symbols from real assemblies

Tables instead of source: `System.Object` used to be three hundred lines of C# the
compiler knew by heart; now it is a row in a table in a file named in the references.
Types, fields, methods with parameters, properties with accessors, inheritance and
interfaces, and generic parameters are loaded. What a signature numbers rather than
names (`!0`, `!!0`) is resolved by scope: a nested type repeats the outer type's
parameters, so `Dictionary<K,V>.Enumerator` has two parameters in metadata and none in
C#.

```sh
cargo run --release -p rustlyn-semantics --example load -- .../shared/Microsoft.NETCore.App/8.0.11
```

On .NET 8.0.11: 168 assemblies in 161 ms; 3,874 types, 43,900 methods, 10,208
properties, 7,038 fields, 59,376 parameters.

Real programs compile against all `Microsoft.NETCore.App` assemblies and run on the
real runtime: structs, interfaces, generic methods, arrays, `List<string>`,
`Dictionary<string,int>`, `int.Parse`, `try`/`catch`/`finally` with a real
`InvalidOperationException`, lambdas as `Func<int,int>`, and LINQ (`Where`, `Count`,
`Sum`, `Max`, `First`, `ToArray`, found through `ExtensionAttribute` in metadata, with
`TSource` inferred from `List<int>` via `IEnumerable<T>`). `AssemblyRef` rows follow
what the metadata said, and a nested type's `TypeRef` points at its outer type.

The first thing this found: `foreach` over `List<T>` uses a *struct* enumerator. It has
no vtable and cannot be loaded as a reference; its methods are called by address
(`ldloca`, `call`), not `callvirt`. The synthesized corlib did not show this because its
enumerator was a class; the CLR accepted the wrong IL and crashed with a segfault rather
than an exception.

### Diagnostics

Real `CSxxxx` codes, formatted like `csc`:

```
Program.cs(3,13): error CS0594: Floating-point constant is outside the range of type 'double'
```

## Other code bases

* [`tools/cav`](../tools/cav/README.md): Roslyn's `CompileAndVerify` tests extracted
  into programs with expected output, each built by Rustlyn and run on .NET.
* [`tools/diag`](../tools/diag/README.md): Roslyn's `VerifyDiagnostics` tests, comparing
  reported diagnostics.
* [`tools/oss`](../tools/oss/README.md): open-source libraries (Newtonsoft.Json,
  Serilog, Dapper, NodaTime, MoreLINQ, Polly and others) compiled from source and used
  from small programs.

Current numbers for each are in the [roadmap](roadmap.md#whats-next).
